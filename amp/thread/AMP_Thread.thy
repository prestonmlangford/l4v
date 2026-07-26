(*
 * PolarFire verified multicore (AMP) — Phase 5.75: channel thread ownership
 * (T1–T4).
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * Phase 5.5 stated message integrity (M2, REQ-MSG-8) under a NAMED, unproven
 * locale assumption, `sender_quiescent`: "the sender issues no further write
 * to its own pending buffer". That assumption is a claim about arbitrary,
 * unverified APPLICATION code, because Phase 2's `frame_perm` is CORE
 * granularity — it cannot distinguish the channel driver thread from any
 * other thread on the same core. Every thread on the sending core holds the
 * sender's PermRW on the buffer for the system's whole lifetime, so nothing
 * in the model before this phase could rule out some unrelated thread
 * rewriting the message.
 *
 * This phase closes exactly that gap by narrowing write authority from the
 * CORE to one designated OWNING THREAD per channel endpoint, mirroring
 * seL4's own `BlockedOnSend`: a sender that blocks awaiting the ack is not
 * scheduled, so once the owner is the ONLY holder of the buffer's write
 * mapping, blocking it means nobody can write. See
 * ../../multicore-amp-plan.md section 5 (Phase 5.75).
 *
 * THE ONE TRAP IN THIS PHASE (recorded because it is easy to get backwards).
 * `sender_quiescent`'s hypothesis quantifies over CORE-level `amp_step_w`
 * steps. The new thread-level step relation `amp_step_t` REFINES
 * `amp_step_w` (every thread-authorised write is core-authorised), exactly
 * the same direction as Phase 5.5's own `amp_step_w`/`amp_step` refinement.
 * Proving a property for every `amp_step_t` therefore does NOT, by itself,
 * discharge a hypothesis quantified over every `amp_step_w` — the
 * implication runs the wrong way; a core-level step need not come from any
 * particular thread. Bridging the gap needs an explicit ATTRIBUTION fact:
 * every core-level write is actually taken by SOME thread on that core. This
 * is not a new fact about the world — it is what seL4's own `integrity`
 * theorem already gives, being indexed by a specific authorised subject —
 * but it is not re-derived from that theorem here, so it is named and
 * tracked as a new assumption, `A-THR`, exactly as the plan requires. This
 * phase DISCHARGES `sender_quiescent` (it becomes a theorem, not an
 * assumption) at the cost of INTRODUCING `A-THR` — a strictly better trade,
 * since `A-THR` is one architectural fact about seL4's own subject-indexed
 * integrity theorem, not a claim about arbitrary application code, but it is
 * a real entry in the TCB and must not be written up as "unconditional".
 *
 * SCOPE. As the plan is explicit about: this phase does not model DMA (a bus
 * master is not a thread), does not model the kernel's own writes (the claim
 * is about THREAD write authority, not raw physical reachability — aligned
 * with `amp_step` already being authority-derived), and does not touch the
 * timeout/ack-race window (Phase 6's D4). It also does not model the
 * sending thread's control flow or do any Hoare/rely-guarantee reasoning
 * about the driver's C — only the state-machine shape of "blocked while
 * pending" is needed.
 *
 * This theory is organized in the usual four zones (plan section 2.5).
 *)

theory AMP_Thread
imports "AMP_Message.AMP_Message"
begin

section \<open>Specification\<close>

subsection \<open>T1 — thread-granular write authority\<close>

(* A thread is named by a natural number, exactly parallel to core_id — this
   model never fixes how many threads exist, only which ones are named as
   channel owners below. *)
type_synonym thread_id = nat

(* The thread-ownership assignment layered on top of a boot partition:
   tp_core assigns every thread this phase talks about to the one core it
   runs on (a thread not in its domain simply isn't modelled); tp_send_owner
   and tp_recv_owner name, per declared channel, the ONE thread on the
   sending/receiving core that may actually touch the buffer — the
   channel-driver thread, in an implementation. Every other thread on the
   same core, however many there are, holds NO access to the buffer at all
   under thread_perm below: this is the narrowing T1 exists to state. *)
record thread_partition =
  tp_core       :: "thread_id \<rightharpoonup> core_id"
  tp_send_owner :: "amp_channel \<Rightarrow> thread_id"
  tp_recv_owner :: "amp_channel \<Rightarrow> thread_id"

(* Well-formedness of a thread assignment against a boot partition bp: every
   present core has at least one modelled thread (so the private-memory case
   of the union condition below always has a witness), and every declared
   channel's named owners actually run on that channel's declared endpoints
   (so "the sender's owning thread" and "the sending core" agree on which
   core is meant). *)
definition thread_partition_wf :: "amp_partition \<Rightarrow> thread_partition \<Rightarrow> bool" where
  "thread_partition_wf bp tp \<equiv>
     (\<forall>c r. ap_cores bp c = Some r \<longrightarrow> (\<exists>t. tp_core tp t = Some c)) \<and>
     (\<forall>ch \<in> ap_channels bp. tp_core tp (tp_send_owner tp ch) = Some (ch_from ch)
                            \<and> tp_core tp (tp_recv_owner tp ch) = Some (ch_to ch))"

(* The three NAMED conditions of thread_perm, mirroring Phase 2's
   owns_priv/maps_writer/maps_reader exactly and for the same reason (see
   AMP_Spatial's header): keeping the existentials opaque behind named
   predicates stops simp descending into them and exploding the search. *)

(* t is on some core that privately owns f: t inherits its core's private
   read-write access. This phase does not narrow PRIVATE memory to
   individual threads — only the channel buffer, which is this phase's
   entire point — so every thread on a core shares that core's full private
   access. *)
definition thread_owns_priv :: "amp_partition \<Rightarrow> thread_partition \<Rightarrow> thread_id \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "thread_owns_priv bp tp t f \<equiv> (\<exists>c. tp_core tp t = Some c \<and> owns_priv bp c f)"

(* t is THE declared write-owner of some channel whose buffer holds f. *)
definition thread_maps_writer :: "amp_partition \<Rightarrow> thread_partition \<Rightarrow> thread_id \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "thread_maps_writer bp tp t f \<equiv> (\<exists>ch \<in> ap_channels bp. f \<in> ch_buffer ch \<and> t = tp_send_owner tp ch)"

(* t is THE declared read-owner of some channel whose buffer holds f. *)
definition thread_maps_reader :: "amp_partition \<Rightarrow> thread_partition \<Rightarrow> thread_id \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "thread_maps_reader bp tp t f \<equiv> (\<exists>ch \<in> ap_channels bp. f \<in> ch_buffer ch \<and> t = tp_recv_owner tp ch)"

(* The permission a THREAD holds on a frame: read-write if it privately owns
   the frame (via its core) or is the declared send-owner of a channel whose
   buffer holds it; read-only if it is the declared recv-owner; none
   otherwise. On a channel buffer frame this is strictly narrower than
   frame_perm bp c f for c = the thread's core: every non-owner thread on the
   sending core gets PermNone there, where frame_perm would say PermRW for
   the core as a whole. That narrowing is the entire content of T1. *)
definition thread_perm :: "amp_partition \<Rightarrow> thread_partition \<Rightarrow> thread_id \<Rightarrow> obj_ref \<Rightarrow> access_perm" where
  "thread_perm bp tp t f =
     (if thread_owns_priv bp tp t f then PermRW
      else if thread_maps_writer bp tp t f then PermRW
      else if thread_maps_reader bp tp t f then PermR
      else PermNone)"

subsection \<open>T2 — a thread-level, permission-respecting step relation\<close>

(* amp_step_t t m m' bp tp: thread t takes a step whose every changed frame is
   one t actually holds write authority on, per thread_perm. This REFINES
   amp_step_w (proved below, amp_step_t_is_amp_step_w): every thread-write is
   in particular a core-write by the thread's own core. It does NOT go the
   other way — see the theory header's "one trap" note — so it is additive,
   not a replacement, and every fact about amp_step_w still applies to any
   amp_step_t step via this one lemma. *)
definition amp_step_t ::
  "thread_id \<Rightarrow> (obj_ref \<Rightarrow> 'v) \<Rightarrow> (obj_ref \<Rightarrow> 'v) \<Rightarrow> amp_partition \<Rightarrow> thread_partition \<Rightarrow> bool" where
  "amp_step_t t m m' bp tp \<equiv> \<forall>f \<in> changed_frames m m'. thread_perm bp tp t f = PermRW"

subsection \<open>T3 — thread status and the blocked-owner invariant\<close>

(* Whether a thread is free to run, or blocked awaiting its message being
   consumed on a specific channel it is the declared send-owner of. Mirrors
   seL4's own BlockedOnSend constructor of Structures_A's thread_state: a
   sending thread waiting on its message is not scheduled, and a thread that
   is not scheduled issues no further step at all — including a further
   write to the very buffer it just filled. *)
datatype thread_status = TRunning | TBlockedOnChannel amp_channel

(* The scheduling status of every thread this phase talks about. A total
   function (not a partial map, unlike xchan_map): a thread this development
   never names is simply never looked up, so totality costs nothing and
   avoids a spurious domain side-condition on every lemma that touches it. *)
type_synonym thread_status_map = "thread_id \<Rightarrow> thread_status"

(* owner_status ch tp xm: the scheduling status this phase derives for every
   thread, as a function of ch's OWN runtime status map xm rather than as
   independent state — exactly the plan's "set by send and cleared by
   recv/ack". Defining it this way makes "the owner is blocked while ch is
   pending" (owner_blocked_while_pending below) true BY CONSTRUCTION, not a
   further invariant this phase must separately establish and maintain
   across a trace — matching the phase's explicit scope boundary of not
   modelling the driver's control flow or a general scheduler. Every thread
   other than ch's own declared sender is left running: this phase models
   only the one blocking fact T4 actually consumes. *)
definition owner_status :: "amp_channel \<Rightarrow> thread_partition \<Rightarrow> xchan_map \<Rightarrow> thread_status_map" where
  "owner_status ch tp xm =
     (\<lambda>t. if t = tp_send_owner tp ch \<and> xm ch = Some XSendPending
          then TBlockedOnChannel ch else TRunning)"

(* amp_thread_step t m m' bp tp ts: thread t takes a permission-respecting
   step PROVIDED it is actually running under status map ts. A thread that
   is not running (in particular, one recorded TBlockedOnChannel) simply
   cannot instantiate this relation — there is no step for it to take, not
   merely a step that changes nothing. This is the "step relation that only
   lets running threads move" T3 calls for. *)
definition amp_thread_step ::
  "thread_id \<Rightarrow> (obj_ref \<Rightarrow> 'v) \<Rightarrow> (obj_ref \<Rightarrow> 'v) \<Rightarrow> amp_partition \<Rightarrow> thread_partition
     \<Rightarrow> thread_status_map \<Rightarrow> bool" where
  "amp_thread_step t m m' bp tp ts \<equiv> ts t = TRunning \<and> amp_step_t t m m' bp tp"

section \<open>Proof development (internal machinery)\<close>

subsection \<open>T1 helpers, mirroring AMP_Spatial's buffer-frame branch facts\<close>

(* A channel buffer frame is never any thread's private-ownership frame:
   buffers are disjoint from every core's private frames (Phase 1), so the
   thread_owns_priv branch of thread_perm can never fire there. Kills that
   branch for buffer_write_requires_owner below, exactly as
   buffer_not_owns_priv did at core granularity. *)
lemma buffer_not_thread_owns_priv:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
  shows "\<not> thread_owns_priv bp tp t f"
proof
  assume "thread_owns_priv bp tp t f"
  then obtain c where "tp_core tp t = Some c" and priv: "owns_priv bp c f"
    unfolding thread_owns_priv_def by blast
  then obtain r where "ap_cores bp c = Some r" and fr: "f \<in> cr_frames r"
    unfolding owns_priv_def by blast
  with amp_partition_wf_buffer_not_private[OF wf ch] f show False by blast
qed

(* Any thread other than ch's declared send-owner is NOT a writer for ch's
   buffer frame: the only channel whose buffer holds f is ch itself (buffers
   are pairwise disjoint, Phase 2's wf_buffer_unique), so thread_maps_writer
   can only be witnessed by ch's own tp_send_owner. This is T1 condition (i)
   from the plan, stated as its contrapositive. *)
lemma not_owner_not_thread_maps_writer:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
      and ne: "t \<noteq> tp_send_owner tp ch"
  shows "\<not> thread_maps_writer bp tp t f"
proof
  assume "thread_maps_writer bp tp t f"
  then obtain ch' where ch': "ch' \<in> ap_channels bp" and f': "f \<in> ch_buffer ch'"
                     and teq: "t = tp_send_owner tp ch'"
    unfolding thread_maps_writer_def by blast
  from wf_buffer_unique[OF wf ch' ch f' f] have "ch' = ch" .
  with teq ne show False by simp
qed

(* T1's headline destructor: on a declared channel's buffer frame, the ONLY
   thread ever holding write authority is that channel's declared
   send-owner. Combines the two facts above exactly as
   buffer_write_requires_sender combined its core-level counterparts in
   AMP_Message. This is the fact T4's discharge below actually reaches for. *)
lemma buffer_write_requires_owner:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
      and perm: "thread_perm bp tp t f = PermRW"
  shows "t = tp_send_owner tp ch"
proof -
  from perm have "thread_owns_priv bp tp t f \<or> thread_maps_writer bp tp t f"
    by (simp add: thread_perm_def split: if_splits)
  then show ?thesis
  proof
    assume "thread_owns_priv bp tp t f"
    with buffer_not_thread_owns_priv[OF wf ch f] show ?thesis by simp
  next
    assume "thread_maps_writer bp tp t f"
    then obtain ch' where ch': "ch' \<in> ap_channels bp" and f': "f \<in> ch_buffer ch'"
                       and teq: "t = tp_send_owner tp ch'"
      unfolding thread_maps_writer_def by blast
    from wf_buffer_unique[OF wf ch' ch f' f] have "ch' = ch" .
    with teq show ?thesis by simp
  qed
qed

subsection \<open>T1 condition (ii): a core's permission is the union of its threads'\<close>

(* One direction of the union condition, used directly by T2's refinement
   lemma below: if SOME thread on core c holds thread-level write authority
   on f, core c holds frame_perm PermRW there too. Either that thread's
   authority came from privately owning f (so c does too, directly), or from
   being some channel's declared send-owner (so c is that channel's ch_from,
   which is exactly maps_writer). *)
lemma thread_perm_implies_frame_perm:
  assumes wf: "amp_partition_wf bp" and twf: "thread_partition_wf bp tp"
      and core: "tp_core tp t = Some c" and tperm: "thread_perm bp tp t f = PermRW"
  shows "frame_perm bp c f = PermRW"
proof -
  from tperm have "thread_owns_priv bp tp t f \<or> thread_maps_writer bp tp t f"
    by (simp add: thread_perm_def split: if_splits)
  then show ?thesis
  proof
    assume "thread_owns_priv bp tp t f"
    then obtain c' where c'core: "tp_core tp t = Some c'" and priv: "owns_priv bp c' f"
      unfolding thread_owns_priv_def by blast
    with core have "c' = c" by simp
    with priv show ?thesis by (simp add: frame_perm_def)
  next
    assume "thread_maps_writer bp tp t f"
    then obtain ch where ch: "ch \<in> ap_channels bp" and f': "f \<in> ch_buffer ch"
                      and teq: "t = tp_send_owner tp ch"
      unfolding thread_maps_writer_def by blast
    from twf ch have towner: "tp_core tp (tp_send_owner tp ch) = Some (ch_from ch)"
      unfolding thread_partition_wf_def by blast
    with teq core have ceq: "c = ch_from ch" by simp
    have mw: "maps_writer bp c f" unfolding maps_writer_def using ch f' ceq by blast
    show ?thesis by (simp add: frame_perm_def buffer_not_owns_priv[OF wf ch f'] mw)
  qed
qed

section \<open>Results\<close>

subsection \<open>T1 — the union condition, in full\<close>

(* T1 condition (ii) as stated in the plan: a core's permission is EXACTLY
   the union of its threads' permissions. This is what lets every one of
   Phases 2-5's frame_perm-level theorems be reused unchanged once threads
   are in the picture: nothing about frame_perm itself needed to change,
   because it is recoverable from thread_perm plus thread_partition_wf. *)
theorem thread_perm_union_is_frame_perm:
  assumes wf: "amp_partition_wf bp" and twf: "thread_partition_wf bp tp"
  shows "frame_perm bp c f = PermRW \<longleftrightarrow> (\<exists>t. tp_core tp t = Some c \<and> thread_perm bp tp t f = PermRW)"
proof
  assume fp: "frame_perm bp c f = PermRW"
  then have "owns_priv bp c f \<or> maps_writer bp c f"
    by (simp add: frame_perm_def split: if_splits)
  then show "\<exists>t. tp_core tp t = Some c \<and> thread_perm bp tp t f = PermRW"
  proof
    assume priv: "owns_priv bp c f"
    from priv obtain r where cpres: "ap_cores bp c = Some r" unfolding owns_priv_def by blast
    from twf cpres obtain t where tcore: "tp_core tp t = Some c"
      unfolding thread_partition_wf_def by blast
    have "thread_owns_priv bp tp t f" unfolding thread_owns_priv_def using tcore priv by blast
    then have "thread_perm bp tp t f = PermRW" by (simp add: thread_perm_def)
    with tcore show ?thesis by blast
  next
    assume wr: "maps_writer bp c f"
    then obtain ch where ch: "ch \<in> ap_channels bp" and f': "f \<in> ch_buffer ch" and c': "c = ch_from ch"
      unfolding maps_writer_def by blast
    from twf ch have towner: "tp_core tp (tp_send_owner tp ch) = Some (ch_from ch)"
      unfolding thread_partition_wf_def by blast
    have "thread_maps_writer bp tp (tp_send_owner tp ch) f"
      unfolding thread_maps_writer_def using ch f' by blast
    then have "thread_perm bp tp (tp_send_owner tp ch) f = PermRW" by (simp add: thread_perm_def)
    with towner c' show ?thesis by blast
  qed
next
  assume "\<exists>t. tp_core tp t = Some c \<and> thread_perm bp tp t f = PermRW"
  then show "frame_perm bp c f = PermRW"
    using thread_perm_implies_frame_perm[OF wf twf] by blast
qed

subsection \<open>T2 — amp_step_t refines amp_step_w\<close>

(* T2's refinement lemma, as the plan specifies: every thread-authorised step
   is, in particular, a step its thread's own core is authorised to make.
   Additive to Phase 5.5 — amp_step_w and everything built on it is
   untouched; this only supplies a new, stronger way to establish it. *)
theorem amp_step_t_is_amp_step_w:
  assumes wf: "amp_partition_wf bp" and twf: "thread_partition_wf bp tp"
      and core: "tp_core tp t = Some c" and step: "amp_step_t t m m' bp tp"
  shows "amp_step_w c m m' bp"
  unfolding amp_step_w_def
proof (intro ballI)
  fix f assume f: "f \<in> changed_frames m m'"
  with step have "thread_perm bp tp t f = PermRW" by (simp add: amp_step_t_def)
  with thread_perm_implies_frame_perm[OF wf twf core] show "frame_perm bp c f = PermRW" by simp
qed

subsection \<open>T3 — the blocked-owner invariant\<close>

(* T3's headline fact: BY CONSTRUCTION of owner_status, ch's declared
   send-owner is blocked exactly when ch itself is pending. This is the fact
   T4's discharge below actually consumes; it needs no further proof beyond
   unfolding the definition, precisely because owner_status was defined to
   make it true rather than assumed as a separate invariant to maintain. *)
theorem owner_blocked_while_pending:
  assumes pending: "xm ch = Some XSendPending"
  shows "owner_status ch tp xm (tp_send_owner tp ch) = TBlockedOnChannel ch"
  using pending by (simp add: owner_status_def)

subsection \<open>T4 — discharging sender_quiescent\<close>

(* thread_ownership: the one genuinely NEW assumption this phase introduces,
   A-THR, packaged as a locale exactly the way Phase 5.5 packaged
   sender_quiescent (same phantom `'v itself` device, for the same reason —
   without it, lemmas inside this locale would get thread_attribution's and
   the goal's memory type as two UNRELATED schematic variables; see Phase
   5.5's theory header for the full explanation of the pitfall).

   thread_attribution says: whenever ch's declared sender CORE takes a
   permission-respecting step, that step is actually attributable to some
   thread running on that core, whose OWN thread-level authority already
   accounts for every frame the step changed. This is not a new fact about
   the world so much as a restatement, at this model's granularity, of what
   seL4's own `integrity` theorem already gives for free — a kernel step is
   always taken on behalf of one specific authorised subject. Discharging
   THIS locale against that real theorem is deferred integration work, named
   `A-THR` in the plan's TCB table; nothing here attempts it. There is
   deliberately no non-vacuity witness for this locale below, for exactly
   the reason Phase 5.5 gave for omitting one for sender_quiescent: any
   witness would either assume the very fact being checked (that a thread
   attribution happens) or be vacuous. *)
locale thread_ownership =
  fixes msg_type :: "'v itself"
    and bp :: amp_partition
    and ch :: amp_channel
    and tp :: thread_partition
  assumes wf: "amp_partition_wf bp"
      and ch_declared: "ch \<in> ap_channels bp"
      and twf: "thread_partition_wf bp tp"
      and thread_attribution:
        "\<And>(m :: obj_ref \<Rightarrow> 'v) m' xm. amp_step_w (ch_from ch) m m' bp
           \<Longrightarrow> \<exists>t. tp_core tp t = Some (ch_from ch)
                   \<and> amp_thread_step t m m' bp tp (owner_status ch tp xm)"
begin

(* T4, the discharge itself. Given a real permission-respecting step by ch's
   sender core while ch is pending: thread_attribution names some running
   thread t on that core actually responsible for it; owner_blocked_while_
   pending shows ch's OWNER is blocked at that very moment, so t cannot be
   the owner; buffer_write_requires_owner then rules out t touching ch's
   buffer at all, since only the owner ever may. This is exactly
   sender_quiescent's hypothesis — PROVED here, not assumed. *)
theorem sender_quiescent_discharged:
  assumes pending: "xm ch = Some XSendPending"
      and step: "amp_step_w (ch_from ch) (m :: obj_ref \<Rightarrow> 'v) m' bp"
  shows "\<forall>f \<in> ch_buffer ch. m' f = m f"
proof -
  from thread_attribution[OF step] obtain t
    where core: "tp_core tp t = Some (ch_from ch)"
      and tstep: "amp_thread_step t m m' bp tp (owner_status ch tp xm)" by blast
  from tstep have running: "owner_status ch tp xm t = TRunning"
                and tstep': "amp_step_t t m m' bp tp"
    by (simp_all add: amp_thread_step_def)
  have blocked: "owner_status ch tp xm (tp_send_owner tp ch) = TBlockedOnChannel ch"
    using pending by (simp add: owner_status_def)
  have not_owner: "t \<noteq> tp_send_owner tp ch"
  proof
    assume "t = tp_send_owner tp ch"
    with blocked running show False by simp
  qed
  show ?thesis
  proof (intro ballI)
    fix f assume f: "f \<in> ch_buffer ch"
    show "m' f = m f"
    proof (rule ccontr)
      assume "m' f \<noteq> m f"
      then have "f \<in> changed_frames m m'" by (simp add: changed_frames_def)
      with tstep' have perm: "thread_perm bp tp t f = PermRW" by (simp add: amp_step_t_def)
      from buffer_write_requires_owner[OF wf ch_declared f perm] have "t = tp_send_owner tp ch" .
      with not_owner show False by simp
    qed
  qed
qed

end

(* Interpreting sender_quiescent from inside thread_ownership: any model
   satisfying T1-T3 plus the one new A-THR assumption automatically
   satisfies Phase 5.5's sender_quiescent, so every fact sender_quiescent
   proves — in particular message_integrity, REQ-MSG-8 — becomes available
   with no further work, via Isabelle's own locale machinery. This IS the
   discharge the plan's exit test asks for: sender_quiescent is INTERPRETED
   here, never separately assumed again. *)
sublocale thread_ownership \<subseteq> sender_quiescent msg_type bp ch
proof unfold_locales
  show "amp_partition_wf bp" by (rule wf)
  show "ch \<in> ap_channels bp" by (rule ch_declared)
  show "\<And>(m :: obj_ref \<Rightarrow> 'v) m' xm. xm ch = Some XSendPending
          \<Longrightarrow> amp_step_w (ch_from ch) m m' bp \<Longrightarrow> \<forall>f \<in> ch_buffer ch. m' f = m f"
    using sender_quiescent_discharged .
qed

(* The headline restated: under thread_ownership (T1-T3 plus A-THR), the
   receiver reads exactly what the sender sent — with NO sender_quiescent
   hypothesis anywhere in this statement, because the sublocale above already
   discharged it. This is what AMP_Overview restates as the new form of
   REQ-MSG-8. *)
theorem (in thread_ownership) message_integrity_via_thread_ownership:
  assumes send: "xchan_send_msg ch (msg :: obj_ref \<Rightarrow> 'v) m m' xm0 xm1"
      and run:  "(quiescent_step bp xm1 ch)\<^sup>*\<^sup>* m' m''"
      and recv: "xchan_recv_ack ch xm1 xm2"
  shows "xchan_recv ch m'' = xchan_recv ch msg"
  using message_integrity[OF send run recv] .

section \<open>Examples\<close>

subsection \<open>A concrete thread ownership assignment for the example system\<close>

(* Two threads for the example two-core system: thread 10 runs on core 0 and
   is chan01's declared send-owner; thread 20 runs on core 1 and is its
   declared recv-owner. Elsewhere tp_send_owner/tp_recv_owner default to an
   arbitrary placeholder (0), never inspected since example2 declares only
   chan01. *)
definition example_tp :: thread_partition where
  "example_tp = \<lparr> tp_core = [10 \<mapsto> 0, 20 \<mapsto> 1],
                  tp_send_owner = (\<lambda>c. if c = chan01 then 10 else 0),
                  tp_recv_owner = (\<lambda>c. if c = chan01 then 20 else 0) \<rparr>"

(* Non-vacuity for T1: this assignment genuinely satisfies
   thread_partition_wf over example2 — both clauses (every present core has
   a modelled thread; each channel's declared owners run on its declared
   endpoints) are satisfiable requirements, not vacuous ones. *)
lemma example_tp_wf: "thread_partition_wf example2 example_tp"
proof (unfold thread_partition_wf_def, intro conjI allI impI)
  fix c r assume h: "ap_cores example2 c = Some r"
  from h have "c = 0 \<or> c = 1"
    by (auto simp: example2_def split: if_splits)
  then show "\<exists>t. tp_core example_tp t = Some c"
  proof
    assume ceq: "c = 0"
    show ?thesis unfolding ceq by (rule exI[of _ 10]) (simp add: example_tp_def)
  next
    assume ceq: "c = 1"
    show ?thesis unfolding ceq by (rule exI[of _ 20]) (simp add: example_tp_def)
  qed
next
  show "\<forall>ch \<in> ap_channels example2. tp_core example_tp (tp_send_owner example_tp ch) = Some (ch_from ch)
                                    \<and> tp_core example_tp (tp_recv_owner example_tp ch) = Some (ch_to ch)"
    by (auto simp: example2_def chan01_def example_tp_def)
qed

(* Non-vacuity for T3: thread 10 (chan01's owner) is running while chan01 is
   idle, and blocked exactly once chan01 becomes pending — the invariant T4
   relies on, exhibited concretely. Thread 20 (a different channel's
   business entirely here) stays running regardless. *)
lemma example_owner_status_tracks_chan01:
  "owner_status chan01 example_tp example_xchan0 10 = TRunning"
  "owner_status chan01 example_tp example_xchan0 20 = TRunning"
  "owner_status chan01 example_tp (example_xchan0(chan01 \<mapsto> XSendPending)) 10
     = TBlockedOnChannel chan01"
  by (simp_all add: owner_status_def example_tp_def example_xchan0_def)

(* Non-vacuity for T2: a step by chan01's owner thread (10), confined to
   chan01's one buffer frame, is a genuine amp_step_t — and, via
   amp_step_t_is_amp_step_w, a genuine amp_step_w for core 0, exactly as T2
   predicts. *)
lemma example_owner_step_is_amp_step_t:
  assumes m: "changed_frames m m' \<subseteq> {0x8000}"
  shows "amp_step_t 10 m m' example2 example_tp"
  using m
  by (auto simp: amp_step_t_def thread_perm_def thread_owns_priv_def
                 thread_maps_writer_def example_tp_def example2_def chan01_def)

(* The same concrete step, chained through T2's refinement lemma: since
   thread 10 is on core 0 (tp_core example_tp 10 = Some 0), its amp_step_t
   step above is, in particular, a genuine amp_step_w for core 0 — the
   thread-level fact refining to the core-level one T4's discharge needs. *)
lemma example_owner_step_is_amp_step_w:
  assumes m: "changed_frames m m' \<subseteq> {0x8000}"
  shows "amp_step_w 0 m m' example2"
proof -
  have core: "tp_core example_tp 10 = Some 0" by (simp add: example_tp_def)
  show ?thesis
    using amp_step_t_is_amp_step_w[OF example2_partition_wf example_tp_wf core
                                     example_owner_step_is_amp_step_t[OF m]] .
qed

end
