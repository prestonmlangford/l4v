(*
 * PolarFire verified multicore (AMP) — the guarantees.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * WHAT THIS FILE IS. This is the answer to "what does the AMP work actually
 * guarantee me, as someone writing software on top of it?" — stated as a list
 * of requirements, each one a plain-English paragraph immediately followed by
 * the machine-checked statement that discharges it. Read this file top to
 * bottom and you know what has been proved. You do not need to open any other
 * theory, or understand any proof, to trust the list.
 *
 * HOW TO TRUST IT. Every requirement below is derived here, in this file, from
 * theorems checked in the AMP sessions. Most are a one-step restatement of a
 * single theorem; a few compose two or three. Either way the derivation is real
 * Isabelle: if a cited theorem's name, statement, or hypotheses ever change
 * incompatibly, THIS FILE FAILS TO BUILD. The requirement list cannot silently
 * drift away from the proofs, and no requirement below can be false.
 *
 * WHAT IT DELIBERATELY OMITS. Intermediate results — refinement steps,
 * abstraction relations, internal consistency lemmas, proof scaffolding — are
 * not here even when they were hard to prove, because they are not claims about
 * the running system. A result earns a place below only if an application
 * developer would change a design decision on learning it.
 *
 * READ SECTION 4 BEFORE RELYING ON ANY OF THIS. It states, precisely, what is
 * NOT established. The requirements below are conditional guarantees, and their
 * conditions are load-bearing.
 *)

theory AMP_Overview
imports
  "AMP_Channel_C.AMP_Channel_C"    (* pulls in AMP_Channel_R, AMP_Channel_A, AMP_Spatial, AMP_Model *)
  "AMP_Channel_AC.AMP_Channel_AC"  (* the authority-graph layer, a sibling branch off AMP_Channel_A *)
  "AMP_Message.AMP_Message"        (* message content: integrity and confidentiality of VALUES *)
  "AMP_Thread.AMP_Thread"          (* thread ownership: narrows buffer authority to one thread per endpoint *)
  "AMP_Concurrency.AMP_Concurrency" (* the interleaved model, and its refinement to the atomic protocol *)
  "AMP_ADT.AMP_ADT"                (* the ledger layers: amp_step derived from seL4's own integrity theorem *)
begin

(* THE VOCABULARY, in one place, so the statements below read without lookups.

     amp_partition (bp)   the static boot configuration: which cores exist
                          (ap_cores), what private memory each owns
                          (cr_frames), and what channels are declared
                          (ap_channels). Fixed at boot; never changes.
     amp_channel (ch)     a declared one-way channel: a sender (ch_from), a
                          receiver (ch_to), and a shared buffer (ch_buffer).
     amp_partition_wf bp  the configuration is sane: cores' private memory is
                          pairwise disjoint, channels run between two distinct
                          present cores, buffers are not carved out of anyone's
                          private memory, and distinct channels use disjoint
                          buffers. EVERY guarantee below is conditional on this.
     frame_perm bp c f    the access core c holds on frame f: PermRW, PermR, or
                          PermNone. A function of bp alone.
     changed_frames m m'  the frames whose contents differ between two memories.
     amp_step c m m' bp   core c takes a step, writing only frames it owns.
                          Derived from seL4's integrity theorem; see REQ-DUR-5.
     ADT_A uop            l4v's model of the running seL4 system: a six-clause
                          automaton (ADT_AI.thy:282) over kernel calls,
                          user-mode steps and interrupt polls. A "step" below
                          always means a step of this.
     amp_gs_inv bp c gs   core c's kernel state realises the declared partition
                          and satisfies seL4's invs, pas_refined, valid_sched
                          and schact_is_rct. Assumed at boot (A-BOOT),
                          preserved by every step.
     gs_mem gs            system memory, read off an ADT_A state.
     xchan_send,          the channel protocol: send requires the channel idle
     xchan_recv_ack       and leaves it send-pending; recv/ack requires it
                          send-pending and leaves it idle.
     amp_auth_graph bp    who the boot config SAYS may send/receive on what.
     xchan_send_msg,      the channel protocol WITH a message value attached:
     xchan_recv           send additionally requires the buffer to hold msg
                          afterwards; recv reads the buffer back out as an
                          option-valued function (Some on buffer frames, None
                          elsewhere).
     observation bp c m   everything core c can see of memory m: Some (m f)
                          on every frame c holds any access to, None
                          elsewhere. Two memories giving c the same
                          observation are indistinguishable to it.
     quiescent_step       one step of SOME core, taken while ch sits
                          send-pending. Its reflexive-transitive closure is how
                          REQ-MSG-8 says "any amount of unrelated activity may
                          run while the message waits": arbitrary cores taking
                          arbitrary permission-respecting steps, constrained
                          only by the channel remaining pending throughout.
     thread_id, tp        a thread (thread_id, a bare identifier) and a
                          thread_partition tp assigning each modelled thread
                          to one core (tp_core) and naming, per declared
                          channel, the ONE thread on each endpoint core
                          allowed to touch the buffer (tp_send_owner,
                          tp_recv_owner) — every other thread on that same
                          core holds NO access to it at all.
     owner_status ch tp xm   the scheduling status this development derives
                          for ch's declared sender thread from ch's OWN
                          runtime status: blocked exactly while ch is
                          pending, running otherwise.
     A-THR (thread_attribution)   the one new assumption REQ-MSG-8 now rests
                          on: every core-level permission-respecting write is
                          actually taken by some thread running on that core
                          whose own thread-level authority already accounts
                          for it. Not a claim about arbitrary application
                          code, but an architectural fact about seL4's own
                          subject-indexed `integrity` theorem — one not yet
                          discharged against it.
                          See REQ-MSG-8 and section 4.1(c).
     cstep, csteps        one step, and one finite TRACE, of the system as it
                          actually runs: the two kernels' buffer copies
                          happening one frame at a time, with any other
                          thread's activity free to interleave ANYWHERE,
                          including in the middle of a copy. This is the
                          concurrent system the atomic protocol above is a
                          description OF; see REQ-DUR-4.
     cs_recv_val s        what the receiving APPLICATION holds: the buffer the
                          receiving kernel copied the message into, which
                          deliberately outlives the acknowledgement. REQ-MSG-11
                          is the claim about this.
     abs_mem, atrace      how a concurrent execution is read as a run of the
                          atomic protocol: abs_mem is memory as that protocol
                          sees it, and atrace maps a real execution's steps to
                          the protocol operations they perform (a copy-loop
                          iteration performs none). Both are COMPUTED from the
                          execution, not chosen — see REQ-DUR-4.
     asteps, alternates   a run of the atomic protocol (a sequence of
                          xchan_send_msg / xchan_recv_ack / other-thread
                          steps), and the property that its sends and
                          acknowledgements strictly alternate.
     A-AVL                the accepted availability gap: a sender blocks until
                          its message is acknowledged, with no timeout, so a
                          receiver that never acknowledges wedges it forever.
                          Not an assumption — a known-false property, disclosed
                          rather than assumed away. See section 4.2(e). *)


section \<open>1. Isolation — cores do not share resources except through declared channels\<close>

(* REQ-ISO-1. THE ONLY MEMORY TWO CORES CAN BOTH REACH IS A DECLARED CHANNEL
   BUFFER. Take any two distinct cores and intersect everything each of them can
   reach — private memory plus every channel they are an endpoint of. Whatever
   survives that intersection is inside some channel's buffer that the boot
   config declared. There is no other overlap: no accidental sharing, no
   incidental aliasing, nothing outside the declared channel set. This is the
   headline isolation property, stated over what the configuration grants. *)
theorem shared_resources_are_declared_channels_only:
  assumes wf:  "amp_partition_wf bp"
      and neq: "c1 \<noteq> c2"
  shows "owned_frames bp c1 \<inter> owned_frames bp c2 \<subseteq> (\<Union>ch \<in> ap_channels bp. ch_buffer ch)"
  using owned_overlap_subset_channels[OF wf neq] .

(* REQ-ISO-1', the same requirement stated over what the HARDWARE enforces
   rather than what the configuration grants: if two distinct cores both hold
   SOME access to a frame — read or write, it does not matter which — that frame
   is a declared channel's buffer. Equivalently: find any doubly-mapped frame in
   an AMP system and you have found a declared channel. This is the form to cite
   when the question is "can these two cores interfere through memory at all?",
   because it ranges over the MMU permission map, which is what actually runs. *)
theorem doubly_mapped_frames_are_channel_buffers:
  assumes wf:  "amp_partition_wf bp"
      and neq: "c1 \<noteq> c2"
      and a1:  "frame_perm bp c1 f \<noteq> PermNone"
      and a2:  "frame_perm bp c2 f \<noteq> PermNone"
  shows "\<exists>ch \<in> ap_channels bp. f \<in> ch_buffer ch"
proof -
  (* Two distinct cores cannot both hold f as private memory: the configuration
     makes private frame sets pairwise disjoint. *)
  have priv: "\<not> (owns_priv bp c1 f \<and> owns_priv bp c2 f)"
  proof
    assume "owns_priv bp c1 f \<and> owns_priv bp c2 f"
    then obtain r1 r2 where "ap_cores bp c1 = Some r1" and "f \<in> cr_frames r1"
                        and "ap_cores bp c2 = Some r2" and "f \<in> cr_frames r2"
      unfolding owns_priv_def by blast
    with amp_partition_wf_private_disjoint[OF wf _ _ neq] show False by blast
  qed
  (* So at least one of them holds f as a channel endpoint instead — and either
     of the two endpoint cases exhibits the declared channel we need. *)
  from a1 a2 priv show ?thesis
    by (auto simp: frame_perm_def maps_writer_def maps_reader_def split: if_splits)
qed

(* REQ-ISO-2. A RUNNING CORE CANNOT MODIFY ANOTHER CORE'S PRIVATE MEMORY. When
   core c takes a step, not one frame of any other core's private memory
   changes. This is the integrity guarantee in its most directly usable form:
   whatever core c's software does — correct, buggy, or actively hostile — it
   cannot corrupt another core's private state.

   "Takes a step" means a step of `ADT_A`, l4v's model of the running kernel —
   see REQ-DUR-5. Conditional on A-BOOT (section 4.1(b)). *)
theorem core_step_cannot_touch_another_cores_memory:
  assumes wf:    "amp_partition_wf bp"
      and inv:   "amp_gs_inv bp c gs"
      and step:  "(gs, gs') \<in> Step (ADT_A uop) u"
      and other: "ap_cores bp c' = Some r'"
      and neq:   "c \<noteq> c'"
  shows "changed_frames (gs_mem gs) (gs_mem gs') \<inter> cr_frames r' = {}"
  using amp_step_preserves_other_private
          [OF wf conjunct1[OF amp_step_of_ADT_A[OF wf inv step]] other neq] .

(* REQ-ISO-3. A CORE CANNOT EVEN HOLD WRITE ACCESS TO ANOTHER CORE'S PRIVATE
   MEMORY. Stronger, and different in kind, from ISO-2: that one says a step
   does not write another core's memory; this one says no core is ever in a
   position to. There is no mapping to abuse, no window to race, no privilege to
   escalate through — the write simply cannot be issued. Cross-core memory
   corruption is impossible by construction, not merely absent in practice. *)
theorem no_core_can_write_another_cores_memory:
  assumes wf:    "amp_partition_wf bp"
      and other: "ap_cores bp c' = Some r'"
      and f:     "f \<in> cr_frames r'"
      and neq:   "c \<noteq> c'"
  shows "frame_perm bp c f \<noteq> PermRW"
  using no_cross_writable[OF wf other f neq] .

(* REQ-ISO-4. A CHANNEL BUFFER IS REACHABLE ONLY BY ITS TWO DECLARED ENDPOINTS.
   Any core that is neither the declared sender nor the declared receiver of a
   channel has NO access to that channel's buffer — not write, not read, nothing
   at all. A third core cannot corrupt a message in flight and cannot observe
   one either. Note this holds regardless of the channel's runtime state: there
   is no moment during the protocol at which a buffer becomes momentarily
   visible to anyone else. *)
theorem channel_buffer_is_reachable_only_by_its_endpoints:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
      and c1: "c \<noteq> ch_from ch" and c2: "c \<noteq> ch_to ch"
  shows "frame_perm bp c f = PermNone"
  using buffer_perm_only_endpoints[OF wf ch f c1 c2] .

(* REQ-ISO-5. CHANNELS ARE ONE-WAY, AND THE HARDWARE ENFORCES THE DIRECTION. On
   a declared channel's buffer the sender holds read-write and the receiver
   holds read-only. The receiver cannot write back through the channel it
   receives on — not by convention or discipline, but because it has no write
   mapping. A protocol that needs replies needs a second declared channel in the
   opposite direction; it cannot be improvised on top of one. *)
theorem channel_direction_is_enforced:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
  shows "frame_perm bp (ch_from ch) f = PermRW \<and> frame_perm bp (ch_to ch) f = PermR"
  using buffer_perm_asymmetric[OF wf ch f] .

(* REQ-ISO-6. WHAT THE BOOT CONFIGURATION DECLARES IS EXACTLY WHAT THE HARDWARE
   ENFORCES. Both directions, on both kinds of access: a core has write access
   to a channel buffer IF AND ONLY IF the configuration declared it that
   channel's sender, and read access IF AND ONLY IF it declared it that
   channel's receiver. The "only if" halves say the system grants nothing beyond
   what you asked for; the "if" halves say it grants everything you did ask for,
   so a correctly configured channel is never silently dead. In practice this
   means the boot configuration is a complete and faithful description of the
   system's information flows — reading it tells you the whole story, and the
   proof is what licenses you to reason about the config instead of the MMU. *)
theorem enforced_access_matches_declared_configuration:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
  shows "frame_perm bp c f = PermRW \<longleftrightarrow> (c, XSend, ch) \<in> amp_auth_graph bp"
    and "frame_perm bp c f = PermR  \<longleftrightarrow> (c, XRecv, ch) \<in> amp_auth_graph bp"
proof -
  show "frame_perm bp c f = PermRW \<longleftrightarrow> (c, XSend, ch) \<in> amp_auth_graph bp"
    using amp_auth_graph_write_iff[OF wf ch f] .
  show "frame_perm bp c f = PermR \<longleftrightarrow> (c, XRecv, ch) \<in> amp_auth_graph bp"
    using amp_auth_graph_read_iff[OF wf ch f] .
qed


section \<open>2. Messaging — messages reach the right recipient, and are acknowledged\<close>

(* REQ-MSG-1. A MESSAGE LANDS ONLY WHERE IT WAS ADDRESSED. A send on channel ch
   changes memory inside ch's buffer and nowhere else: not another channel's
   buffer (so no message can be crossed onto the wrong channel), and not ANY
   core's private memory — not even the sender's own, since buffers are never
   carved out of private memory. Misdelivery is impossible, and the reason is
   worth internalising as a design property: a channel's destination is fixed at
   boot and there is no runtime routing decision anywhere in the system, so
   there is no addressing step that could go wrong. *)
theorem message_lands_only_in_its_own_channel_buffer:
  assumes wf:   "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp"
      and send: "xchan_send ch m m' xm xm'"
  shows "changed_frames m m' \<subseteq> ch_buffer ch"
    and "\<forall>ch' \<in> ap_channels bp. ch \<noteq> ch' \<longrightarrow> changed_frames m m' \<inter> ch_buffer ch' = {}"
    and "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> changed_frames m m' \<inter> cr_frames r' = {}"
proof -
  show "changed_frames m m' \<subseteq> ch_buffer ch" using send by (simp add: xchan_send_def)
next
  show "\<forall>ch' \<in> ap_channels bp. ch \<noteq> ch' \<longrightarrow> changed_frames m m' \<inter> ch_buffer ch' = {}"
  proof (intro ballI impI)
    fix ch' assume ch': "ch' \<in> ap_channels bp" and ne: "ch \<noteq> ch'"
    from wf_buffers_disjoint[OF wf ch ch' ne] have "ch_buffer ch \<inter> ch_buffer ch' = {}" .
    with send show "changed_frames m m' \<inter> ch_buffer ch' = {}"
      by (auto simp: xchan_send_def)
  qed
next
  show "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> changed_frames m m' \<inter> cr_frames r' = {}"
    using send amp_partition_wf_buffer_not_private[OF wf ch] by (auto simp: xchan_send_def)
qed

(* REQ-MSG-2. ONLY THE DECLARED RECIPIENT CAN READ THE MESSAGE. Combined with
   MSG-1 this is the delivery guarantee at full strength: the message lands in
   exactly one buffer, the declared receiver is the only core with read access
   to that buffer, and any other core holds no mapping there at all — so it
   cannot observe the message, whatever it does and whenever it tries. Stated in
   the configuration's own vocabulary as well: no core outside the declared
   receiver ever holds the receive authority for that channel. *)
theorem message_is_readable_only_by_its_declared_recipient:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
      and c1: "c \<noteq> ch_from ch" and c2: "c \<noteq> ch_to ch"
  shows "frame_perm bp c f = PermNone"
    and "(c, XRecv, ch) \<notin> amp_auth_graph bp"
    and "(c, XSend, ch) \<notin> amp_auth_graph bp"
  using amp_auth_graph_confined_to_endpoints[OF wf ch f c1 c2] by blast+

(* REQ-MSG-3. A PENDING MESSAGE IS NEVER OVERWRITTEN. While a message sits
   unconsumed on a channel, no send on that channel is possible at all — the
   operation has no enabled instance. A sender cannot clobber a message the
   receiver has not yet taken, so no message is ever silently lost to a faster
   sender. The flip side, which callers must design for: a send on a busy
   channel does not happen, so the sender needs a story for that case (retry,
   backpressure, drop) — the guarantee is no-loss, not no-blocking. *)
theorem pending_message_cannot_be_overwritten:
  assumes pending: "xm ch = Some XSendPending"
  shows "\<not> xchan_send ch m m' xm xm'"
  using pending by (simp add: xchan_send_def)

(* REQ-MSG-4. EVERY RECEIVED MESSAGE IS ACKNOWLEDGED. Receiving and
   acknowledging are one indivisible operation: it is enabled only when a
   message is genuinely pending, and it leaves the channel idle. There is no
   reachable state in which a message has been received but not acknowledged,
   because there is no operation that produces one — the "received, ack
   pending" state does not exist in the protocol. A receiver therefore cannot
   forget to acknowledge, cannot acknowledge twice, and cannot leave the
   channel wedged by failing to. *)
theorem every_received_message_is_acknowledged:
  assumes rc: "xchan_recv_ack ch xm xm'"
  shows "xm ch = Some XSendPending"    (* it was enabled only by a real pending message *)
    and "xm' ch = Some XIdle"          (* and it always completes the acknowledgement *)
  using rc by (simp_all add: xchan_recv_ack_def)

(* REQ-MSG-5. NOTHING IS ACKNOWLEDGED THAT WAS NOT SENT. The dual of MSG-4: on
   an idle channel, no receive/acknowledge is possible. A receiver cannot
   manufacture an acknowledgement for a message that was never sent, so an
   acknowledgement observed by the sender is always evidence of a real,
   completed delivery. *)
theorem no_acknowledgement_without_a_message:
  assumes idle: "xm ch = Some XIdle"
  shows "\<not> xchan_recv_ack ch xm xm'"
  using idle by (simp add: xchan_recv_ack_def)

(* REQ-MSG-6. A COMPLETED ROUND TRIP LEAVES NO RESIDUE. After a send followed by
   its receive/acknowledge, the channel state is not merely idle again — it is
   BIT-FOR-BIT the state it was in before the send, and so is every other
   channel's. There is no accumulating counter, no drift, no sequence number
   that eventually wraps, nothing whose Nth round trip differs from its first.
   A long-running system's channel state is therefore bounded and does not
   degrade, and any two round trips are genuinely interchangeable. *)
theorem completed_round_trip_leaves_no_residue:
  assumes send: "xchan_send ch m m' xm xm1"
      and recv: "xchan_recv_ack ch xm1 xm2"
  shows "xm2 = xm"
proof -
  from send have idle: "xm ch = Some XIdle" and u1: "xm1 = xm(ch \<mapsto> XSendPending)"
    by (simp_all add: xchan_send_def)
  from recv have "xm2 = xm1(ch \<mapsto> XIdle)" by (simp add: xchan_recv_ack_def)
  with u1 have "xm2 = xm(ch \<mapsto> XIdle)" by simp
  also have "xm(ch \<mapsto> XIdle) = xm" using idle by (rule fun_upd_idem)
  finally show ?thesis .
qed

(* REQ-MSG-7. CHANNELS DO NOT INTERFERE WITH EACH OTHER. An operation on one
   channel leaves every other channel's state exactly as it was. Traffic on one
   channel cannot perturb, stall, or corrupt the protocol state of another, so
   channels can be reasoned about — and tested — one at a time. Together with
   MSG-1's buffer-disjointness half, this is full independence of channels in
   both their memory and their protocol state. *)
theorem send_affects_only_its_own_channel:
  assumes send: "xchan_send ch m m' xm xm'"
  shows "\<forall>d. d \<noteq> ch \<longrightarrow> xm' d = xm d"
  using send by (auto simp: xchan_send_def)

(* REQ-MSG-7, receive/acknowledge half: consuming a message on one channel
   likewise leaves every other channel's protocol state untouched. Stated
   separately from the send half above because it is a distinct operation with
   a distinct enabling condition, not a corollary of it. *)
theorem recv_ack_affects_only_its_own_channel:
  assumes rc: "xchan_recv_ack ch xm xm'"
  shows "\<forall>d. d \<noteq> ch \<longrightarrow> xm' d = xm d"
  using rc by (auto simp: xchan_recv_ack_def)

(* REQ-MSG-8. THE RECEIVER READS EXACTLY THE MESSAGE THE SENDER SENT — GIVEN
   ONE NAMED, ARCHITECTURAL ASSUMPTION, NOT A CLAIM ABOUT APPLICATION CODE.
   Everything above this line concerns WHO can reach a message, never what
   its VALUE is; this is the first result about values. Send a message msg
   on ch; let any amount of unrelated kernel activity run while it sits
   pending; then recv/ack it. The value read back is bit-for-bit the value
   sent. What makes that believable is thread ownership: the buffer's write
   authority belongs not to the whole sending core but to ONE declared owning
   thread, and that thread is blocked, by construction, for exactly as long as
   the channel sits pending — so the only party permitted to disturb the
   message cannot be running. Carrying that argument from threads down to
   actual writes is what the `attribution` hypothesis (A-THR) does. It is an
   architectural assumption, not a claim about application code, but it IS
   undischarged: this theorem is conditional on it, not unconditional. Section
   4.1(c) states its status and what breaks if it fails. The parenthetical
   half remains unconditional and worth isolating: no core OTHER than the
   sender can ever alter the message in flight, regardless of any hypothesis
   here — that part follows from ISO-3/ISO-4 alone. *)
theorem the_receiver_reads_exactly_what_was_sent:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp"
      and twf: "thread_partition_wf bp tp"
      and attribution:
        "\<And>(m :: obj_ref \<Rightarrow> 'v) m' xm. amp_step_w (ch_from ch) m m' bp
           \<Longrightarrow> \<exists>t. tp_core tp t = Some (ch_from ch)
                   \<and> amp_thread_step t m m' bp tp (owner_status ch tp xm)"
      and send: "xchan_send_msg ch (msg :: obj_ref \<Rightarrow> 'v) m m' xm0 xm1"
      and run:  "(quiescent_step bp xm1 ch)\<^sup>*\<^sup>* m' m''"
      and recv: "xchan_recv_ack ch xm1 xm2"
  shows "xchan_recv ch m'' = xchan_recv ch msg"
proof -
  interpret thread_ownership "TYPE('v)" bp ch tp
  proof unfold_locales
    show "amp_partition_wf bp" by (rule wf)
    show "ch \<in> ap_channels bp" by (rule ch)
    show "thread_partition_wf bp tp" by (rule twf)
    show "\<And>(m :: obj_ref \<Rightarrow> 'v) m' xm. amp_step_w (ch_from ch) m m' bp
            \<Longrightarrow> \<exists>t. tp_core tp t = Some (ch_from ch)
                    \<and> amp_thread_step t m m' bp tp (owner_status ch tp xm)"
      using attribution .
  qed
  show ?thesis using send run recv by (rule message_integrity)
qed

(* REQ-MSG-9. NO CORE OUTSIDE THE CHANNEL LEARNS ANYTHING FROM A SEND — FOR
   ANY MESSAGE VALUE, UNCONDITIONALLY. Take any core c that is neither ch's
   declared sender nor its declared receiver. Whatever c can observe of
   memory (every frame it holds any access to at all) is EXACTLY the same
   before and after a send on ch, no matter what the message says. Unlike
   MSG-8, this needs no quiescence hypothesis and no locale: it costs nothing
   to establish because c holds no mapping to the buffer at all (ISO-4), so
   there is nothing for a changing value to be seen THROUGH. This is the
   storage-channel confidentiality half of message security — the first
   result in this file that is a genuine claim about VALUES rather than
   permissions, and the one that needed message content in the model before
   it could even be stated. Section 4.2(f) records the confidentiality
   claim this does NOT make. *)
theorem no_core_outside_the_channel_learns_anything_from_a_send:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp"
      and send: "xchan_send_msg ch msg m m' xm xm'"
      and c1: "c \<noteq> ch_from ch" and c2: "c \<noteq> ch_to ch"
  shows "observation bp c m = observation bp c m'"
  using xchan_send_msg_invisible_to_third_core[OF wf ch send c1 c2] .

(* REQ-MSG-10. THE ACKNOWLEDGEMENT IS A REAL, BUT BOUNDED, BACKWARD FLOW. The
   channel is one-way for DATA — REQ-ISO-5 already says the receiver holds no
   write mapping at all — but a working protocol still needs the receiver to
   tell the sender "consumed", and that IS a flow from receiver to sender.
   This states its exact size: recv/ack changes ch's own status entry to
   idle and nothing else — no other channel's status, and (definitionally,
   since recv/ack has no memory operand at all) no message content
   whatsoever. One bit, once per round trip, carrying no payload. This
   matters for how to read section 1: a claim that the two endpoints of a
   channel learn NOTHING from each other would be false, and any future
   cross-core confidentiality result (beyond this file) must be phrased to
   ALLOW this one declared bit, not to assert its absence. *)
theorem the_acknowledgement_carries_no_message_content:
  assumes rc: "xchan_recv_ack ch xm xm'"
  shows "xm' ch = Some XIdle"
    and "\<forall>d. d \<noteq> ch \<longrightarrow> xm' d = xm d"
  using xchan_recv_ack_reverse_flow_is_bounded_to_one_status_bit[OF rc] by blast+

(* REQ-MSG-11. THE RECEIVING APPLICATION ENDS UP HOLDING THE MESSAGE THAT WAS
   SENT, UNDER ANY INTERLEAVING — AND GOES ON HOLDING IT. MSG-8 is a claim
   about what is in the shared buffer at the moment of the acknowledgement.
   That is the right claim for a protocol, and the wrong one for an
   application, which does not read the shared buffer: it reads whatever the
   kernel put in ITS memory. This states the application's claim. Run the real
   system — the sending kernel copying the message into the buffer one frame
   at a time, the receiving kernel copying it back out one frame at a time,
   with ANY amount of other threads' activity interleaved anywhere, in any
   order — and at the acknowledgement the receiving application's own buffer
   holds the sent message, every frame of it, bit for bit. Two things are
   worth reading carefully. First, "any interleaving" is literal: nothing
   constrains the trace, and in particular nothing rules out other threads
   running in the middle of either copy. A partially written buffer is a state
   the model genuinely has; this says the receiver can never be looking at
   one. Second, the guarantee is about memory the APPLICATION still owns after
   the channel has gone idle and the sender has been released — so it is not
   invalidated by whatever the sender does next. That is why the channel copies
   rather than sharing a pointer: a zero-copy receiver could read the frame at
   any time, including after the acknowledgement, and no kernel-side property
   could bound that. See section 4.3(i) for the one thing this does NOT
   say. *)
theorem the_receiving_application_holds_the_message_that_was_sent:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp"
      and init: "conc_init ch s"
      and run: "csteps bp ch tp msg s ls s'"
      and ack: "cstep bp ch tp msg s' CRecvCommit s''"
  shows "\<forall>f \<in> ch_buffer ch. cs_recv_val s'' f = Some (msg f)"
  using delivered_message_is_intact[OF wf ch init run ack] .


section \<open>3. Durability — the guarantees survive operation, and reach the implementation\<close>

(* REQ-DUR-1. USING A CHANNEL CANNOT WEAKEN ISOLATION. Every isolation guarantee
   in section 1 still holds after a send, and after a receive/acknowledge. Note
   WHY, because it is a stronger fact than "the invariant is preserved": the
   access-control guarantees (ISO-3 through ISO-6) are properties of the static
   boot configuration alone, and no operation in the system touches that
   configuration. There is no capability to derive, mint, transfer, or revoke,
   so there is no mechanism by which access rights could change at run time and
   nothing that needs re-establishing after each step. Isolation is not an
   invariant the kernel maintains; it is a property of the configuration the
   kernel cannot reach. *)
theorem isolation_holds_across_every_channel_operation:
  assumes wf:   "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp"
      and send: "xchan_send ch m m' xm xm'"
      and rc:   "xchan_recv_ack ch' xn xn'"
  shows "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> ch_from ch \<noteq> c'
                 \<longrightarrow> changed_frames m m' \<inter> cr_frames r' = {}"
    and "\<forall>chx \<in> ap_channels bp. \<forall>f \<in> ch_buffer chx.
           frame_perm bp (ch_from chx) f = PermRW \<and> frame_perm bp (ch_to chx) f = PermR"
    and "\<forall>c' r' f. ap_cores bp c' = Some r' \<longrightarrow> f \<in> cr_frames r' \<longrightarrow> ch_to ch' \<noteq> c'
                   \<longrightarrow> frame_perm bp (ch_to ch') f \<noteq> PermRW"
  using xchan_send_preserves_partition[OF wf ch send]
        xchan_recv_ack_preserves_partition[OF wf rc]
  by blast+

(* REQ-DUR-2. THE GUARANTEES REACH THE IMPLEMENTATION, NOT JUST THE
   SPECIFICATION. The abstract protocol above is stated over a symbolic channel
   status. A real implementation stores a machine word and runs deterministic
   code. The same guarantees hold there: a design-level send on a properly idle
   channel still cannot touch another core's private memory. This is what
   licenses reasoning about the specification when what ships is the code. *)
theorem implementation_inherits_isolation:
  assumes wf:  "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp"
      and pre: "xm ch = Some xIdleR"
      and mem: "changed_frames m m' \<subseteq> ch_buffer ch"
  shows "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> ch_from ch \<noteq> c'
                 \<longrightarrow> changed_frames m m' \<inter> cr_frames r' = {}"
  using xchan_send_R_preserves_partition(1)[where xm = xm and ch = ch, OF wf ch pre mem] .

(* REQ-DUR-3. THE IMPLEMENTATION'S ROUND TRIP ALSO LEAVES NO RESIDUE. MSG-6
   restated at the word level, where it is the claim that actually matters for a
   long-running deployment: run the real send/receive-acknowledge pair against a
   word-tagged status field and the field returns to the exact word it held
   before. Bounded state, no drift, in the representation that ships. *)
theorem implementation_round_trip_leaves_no_residue:
  assumes pre: "(xm :: xchan_map_R) ch = Some xIdleR"
  shows "xchan_recv_ack_R ch (xchan_send_R ch xm) = xm"
proof -
  have "xchan_recv_ack_R ch (xchan_send_R ch xm) = xm(ch \<mapsto> xIdleR)"
    by (simp add: xchan_send_R_def xchan_recv_ack_R_def)
  also have "xm(ch \<mapsto> xIdleR) = xm" using pre by (rule fun_upd_idem)
  finally show ?thesis .
qed

(* REQ-DUR-4. THE GUARANTEES DESCRIBE A CONCURRENTLY EXECUTING SYSTEM, NOT AN
   ATOMIC IDEALISATION OF ONE. This is the requirement that licenses reading
   every messaging guarantee above as a statement about real hardware, and
   without it they would all be quietly conditional on an assumption nobody had
   written down.

   Sections 1 to 3 state the channel protocol as ATOMIC: a send is one
   indivisible operation, an acknowledgement is another. Real hardware does no
   such thing. The sending kernel copies a message into the shared buffer one
   frame at a time; the receiving kernel copies it back out one frame at a
   time; both cores keep running throughout, and any other thread may take a
   step between any two of those instructions. So there is a real question the
   requirement list above cannot answer on its own: is the atomic protocol a
   faithful description of that system, or a convenient fiction?

   It is faithful, and this is the proof. Take ANY execution of the real
   interleaved system — any number of round trips, any interleaving of the two
   copy loops with each other and with any other threads' activity, any length,
   any order. That execution performs a run of the ATOMIC protocol: each of the
   two status-word stores performs one whole abstract operation, every other
   thread's step is an ordinary permission-respecting step, and the copy-loop
   iterations perform nothing at all — they are invisible at the protocol
   level, which is precisely what "the send is atomic" means. The correspondence
   is COMPUTED from the execution rather than chosen for it, so there is no
   freedom hidden in the argument.

   The second conclusion is what makes this a statement about a running system
   rather than about one message: the sends and acknowledgements of any
   execution STRICTLY ALTERNATE, beginning with a send. Never two sends without
   an intervening acknowledgement; never an acknowledgement of something that
   was not sent. MSG-3 and MSG-5 said this about the abstract protocol; this
   says it about the machine.

   This result is here, rather than being omitted as internal refinement
   machinery, for one reason: it is a claim about the running system. An
   application developer who learns that the guarantee list describes only a
   serialised idealisation of the kernel would rightly change their design.
   See sections 4.1(a), 4.3(i) and 4.3(j) for the three things this does
   not extend to. *)
theorem the_guarantees_survive_concurrent_execution:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp"
      and nemp: "ch_buffer ch \<noteq> {}"
      and init: "conc_init ch s"
      and run: "csteps bp ch tp msg s ls s'"
  shows "asteps bp ch tp msg (abs_mem ch s) (cs_xm s) (atrace ls)
                             (abs_mem ch s') (cs_xm s')"
    and "alternates XIdle (atrace ls)"
  using every_run_refines_the_atomic_protocol[OF wf ch nemp init run]
        runs_alternate_send_and_ack[OF wf ch nemp init run] by blast+

(* REQ-DUR-5. A CORE'S STEP WRITES ONLY FRAMES IT OWNS. Section 1's isolation
   results all quantify over a core's steps. This says which executions those
   are: every way the seL4 kernel can run — a system call, user code executing,
   an interrupt arriving. The statement is over `ADT_A`, l4v's own model of the
   running kernel, so "a step" here and a step of the real system are the same
   thing.

   It is seL4's integrity theorem projected onto frames. The proof composes
   `call_kernel_integrity` (Syscall_AC.thy:1311) and `do_user_op_respects`
   (ADT_AC.thy:89) over a per-core PAS. The AMP work supplies the labelling and
   the projection onto frames and proves nothing about seL4 itself.

   The second conclusion is what extends this from one step to a whole run: the
   invariant the step required is re-established, so it applies again to the
   next step, and to every step after that.

   Conditional on A-BOOT (section 4.1(b)). A-THR is a separate assumption at a
   finer granularity, untouched by this; MSG-8 stays conditional on it. *)
theorem a_cores_step_writes_only_frames_it_owns:
  assumes wf:   "amp_partition_wf bp"
      and inv:  "amp_gs_inv bp c gs"
      and step: "(gs, gs') \<in> Step (ADT_A uop) u"
  shows "amp_step c (gs_mem gs) (gs_mem gs') bp \<and> amp_gs_inv bp c gs'"
  using amp_step_of_ADT_A[OF wf inv step] .


section \<open>4. What is NOT established\<close>

(* Every requirement above is conditional, and the conditions matter. Read this
   section as part of the guarantee, not as a caveat appended to it.

   It is arranged by what you would DO about each limit, because that differs
   sharply:

     4.1  ASSUMPTIONS THE GUARANTEES REST ON — things that must be true of the
          world and are not proved here. If one is false the results above are
          simply void, so each entry names its failure mode. Nothing you write
          on top can compensate.
     4.2  CLAIMS THE DESIGN DOES NOT MAKE — consequences of what was BUILT, not
          of what was left unproved. Closing one needs a different design, or a
          different development entirely; more verification will not do it.
     4.3  PROVED LESS THAN THE HEADING SUGGESTS — open proof work. The
          guarantee holds but is narrower than its name, and each entry says
          exactly how.

   THE ASSUMPTIONS IN ONE PLACE, so that "what must be true for any of this to
   hold?" is answerable without reading the rest of the section:

     A-HW      the boot loader establishes the declared partition        4.1(d)
     A-BOOT    the state it hands each core satisfies that core's
               per-core invariant, in seL4's own vocabulary              4.1(b)
     A-MEM     correctly-fenced RVWMO accesses behave sequentially
               consistently                                             4.1(a)
     A-COH     the channel buffer is cache-coherent across U54 harts     4.1(a)
     A-BIN     the compiler preserves fence ordering into the binary     4.1(a)
     A-THR     every permission-respecting write is taken by some thread
               whose own authority already accounts for it              4.1(c)
     A-IPI     inter-processor interrupts are eventually delivered       4.2(e)

   A-BOOT is the only assumption about the kernel's own execution. What a step
   WRITES is proved (REQ-DUR-5); what the boot loader HANDS OVER is assumed.

   A-COH, A-MEM and A-IPI are NEW relative to single-core seL4. This system is
   therefore not "as trustworthy as" the single-core kernel; it is trustworthy
   MODULO three additional hardware and toolchain assumptions, and any safety
   case built on it has to say so. One further property, A-AVL, is not assumed
   at all — it is known to be FALSE and accepted by design; see 4.2(e). *)


subsection \<open>4.1 Assumptions the guarantees rest on\<close>

(* (a) MODEL-TO-HARDWARE FIDELITY IS ASSUMED, NOT PROVED. THIS IS THE LARGEST
       GAP IN THIS FILE. Every result above concerns a formal model in which
       memory operations take effect in the order the model gives them. Four
       things carry that model to a real RISC-V multicore, and none is proved
       here:

         A-MEM  correctly-fenced RVWMO accesses behave sequentially
                consistently — a hardware fact, trusted the way seL4 already
                trusts its machine model;
         A-COH  the shared buffer is cache-coherent across the U54 harts;
         A-BIN  the compiler does not reorder or delete the fences on the way
                to the binary — the same unproven binary-level gap every
                result in this file inherits;
         and, separately unproved, that the shipped code actually EMITS the
                required fences around each copy loop.

       None of these appears as a hypothesis of any theorem above, because they
       justify the RELATIONSHIP between the model and the hardware rather than
       any step inside a proof — which is precisely why they have to be listed
       here instead. Read together they mean: GIVEN that real execution is
       faithfully represented by some trace of this model, the protocol is
       correct. That is a real and useful statement, and not an unconditional
       one. If false: a receiver can observe a stale or partially written
       buffer, and MSG-8 and MSG-11 then say nothing about what it holds. A
       missing or compiler-reordered fence is a bug that no proof in this file
       will catch; the defences against it are keeping the fenced sequence tiny
       and reviewing the compiled send/acknowledge path by hand.

   (b) THE BOOT STATE IS ASSUMED, IN SEL4'S OWN VOCABULARY (A-BOOT). The boot
       loader is assumed to hand core c a kernel state satisfying
       `amp_gs_inv bp c`: core c's kernel state realises the declared partition
       (`amp_config`) and satisfies seL4's own `invs`, `pas_refined`,
       `valid_sched` and `schact_is_rct`. It is assumed once, at boot;
       preservation across every step is proved (REQ-DUR-5).

       `amp_config` is stated over `ap_cores`, `ap_channels`, `cr_frames` and
       `ch_buffer` — the boot configuration's own vocabulary — so a proposed
       configuration can be checked against it. The `invs` half is inherited
       from l4v, where kernel initialisation is axiomatised
       (`akernel_init_invs`, KernelInit_AI.thy:16, under a header reading
       "Currently axiomatised").

       Two configuration restrictions come with it, both real constraints on a
       deployment. The configuration must map 4K pages: a frame capability
       confers authority over its whole page, so a 2M mapping would require
       every 4K frame inside it to be owned. And no capability conferring
       `Control` — Untyped, CNode, Thread, Domain, IRQControl, Zombie — may
       reach outside the core; in particular no untyped capability may cover a
       channel buffer.

       No witness is exhibited for it (section 5). If false: ISO-2 and
       everything downstream lose their basis, which is nearly everything in
       this file.

   (c) THREAD ATTRIBUTION IS ASSUMED (A-THR). Every core-level,
       permission-respecting write is actually taken by SOME thread running on
       that core, in a way thread ownership's own bookkeeping already accounts
       for. MSG-8's integrity result rests on this, and the interleaved model
       consumes it a second time: every other-thread step there is attributed
       to an explicitly named thread BY CONSTRUCTION, which is not a way of
       avoiding A-THR but is A-THR's content built into the shape of the model.
       The concurrency work therefore does not retire it.

       It is a good assumption to be left holding — an architectural fact about
       seL4's own subject-indexed `integrity` theorem (a kernel step is always
       taken on behalf of one specific authorised subject), rather than a claim
       about what arbitrary, unverified application code chooses to do. But it
       has not been re-derived from that theorem here, so MSG-8 is a CONDITIONAL
       guarantee and must not be read as anything else. If false: thread-granular
       ownership proves nothing about the writes that actually occur, and a
       receiver may read a torn message.

       Note the asymmetry — only INTEGRITY is conditional on this.
       Confidentiality (MSG-9) carries no assumption beyond ISO-4.

   (d) THE CONFIGURATION ITSELF IS ASSUMED, NOT VERIFIED (A-HW).
       `amp_partition_wf` is a hypothesis of nearly every result above, and
       nothing here proves it of YOUR configuration: section 5's witness shows
       only that well-formed configurations exist. Checking `amp_partition_wf`
       against a real deployment configuration is concrete, cheap, and currently
       unperformed.

       Two further things are assumed here and are not covered by A-BOOT. That
       the boot loader installs the mappings the configuration DESCRIBES:
       A-BOOT constrains where a core's page tables may reach, never that a
       declared frame is mapped at all, so a core handed no mappings satisfies
       A-BOOT and does no work. And that the hardware honours those mappings,
       which is outside every model in this file.

       A-HW is about `bp` and the machine; A-BOOT (4.1(b)) is about the kernel
       state handed to a core. Neither implies the other: a state can faithfully
       realise a nonsensical `bp`, and a sane `bp` can be handed to a kernel
       whose objects sit in another core's frames. Both are needed.

       If false: cores start with overlapping ownership, and isolation fails at
       the root. *)


subsection \<open>4.2 Claims the design does not make\<close>

(* (e) NO LIVENESS, AND AVAILABILITY IS KNOWN-BROKEN BY DESIGN (A-AVL).
       Nothing above says a message is ever delivered, that a receiver ever
       runs, that a sender ever gets its channel back, or that any operation
       terminates. "Every RECEIVED message is acknowledged" (MSG-4) is proved;
       "every SENT message is eventually received" is not, and cannot be
       without a model of scheduling and progress that this development does
       not have.

       Beyond that ordinary absence there is one specific, DELIBERATE decision
       that must not be discovered the hard way. A sender blocks until its
       message is acknowledged, and there is NO TIMEOUT — mirroring seL4's own
       `seL4_Send`, which likewise blocks indefinitely. A receiver that never
       acknowledges — crashed, malicious, or merely slow — therefore wedges the
       sending thread permanently. This is a real receiver-to-sender
       interference channel and a denial-of-service vector against the sender.
       It is NOT an assumption: it is a property known to be FALSE, accepted as
       the price of a protocol whose safety is provable, and named A-AVL so
       that nobody has to infer it. Read MSG-10's "bounded backward flow" with
       this in mind — the acknowledgement carries one bit of DATA, but the
       sender's PROGRESS is entirely at the receiver's discretion. Do not place
       a channel's send side on a core whose availability matters unless you
       also control the receiver. Removing this needs a different channel, not
       a further proof about this one; a wait-free design that does remove it
       exists on paper and is not built.

       A-IPI (inter-processor interrupts are eventually delivered) is filed
       here rather than in 4.1 for the same reason: its only failure mode is
       that a sender blocks forever, which is the availability property already
       conceded above. It costs nothing beyond what A-AVL already concedes.

   (f) NO CONFIDENTIALITY CLAIM BETWEEN THE TWO ENDPOINTS THEMSELVES. MSG-9
       covers cores OUTSIDE the channel, and covers them unconditionally. It
       says nothing about what a channel's own sender and receiver may learn
       about each other, and this file does not attempt such a claim. MSG-10
       records the obstacle any future attempt would have to account for rather
       than rule out: the acknowledgement is a genuine backward flow of one
       status bit per round trip.

   (g) NO TIMING OR SIDE-CHANNEL CLAIM. ISO-4, MSG-2 and MSG-9 rule out a third
       core reading a message, or learning its VALUE through the storage
       channel a buffer mapping would provide. None of them says anything about
       timing channels, cache-based side channels, shared-bus contention, or
       any other non-architectural flow — MSG-9's noninterference result is a
       storage-channel claim only, matching the scope single-core InfoFlow
       already commits to. Cross-core timing-channel confidentiality is out of
       scope permanently, not deferred.

   (h) NO SERIALISATION, FRAMING, OR PAYLOAD ENCODING. A message here is a
       function from buffer frames to values. Turning application data into one
       of those, and back, is outside this development entirely and always will
       be. *)


subsection \<open>4.3 Proved less than the heading suggests\<close>

(* (i) INTEGRITY IS PROVED; FRESHNESS IS NOT. The message content is a fixed
       parameter of the interleaved model, so the repeated round trips DUR-4
       covers all carry the SAME message. Every individual round trip is fully
       covered — MSG-11 holds for every message value, under every interleaving
       — but one specific fault is invisible to the model as it stands: a
       receiver delivering the PREVIOUS message's bytes instead of the current
       one's would satisfy every theorem above, because with one fixed message
       value the two ARE the same bytes. So "no torn or corrupt value is ever
       delivered" is established; "the value delivered is the one from the send
       being acknowledged" is not. Closing this means stating integrity against
       the buffer snapshot each send publishes rather than against a fixed
       parameter — a change to the integrity invariant, not a widened
       quantifier.

   (j) ONE CHANNEL PER EXECUTION. The interleaved model covers one channel's
       protocol, with arbitrary other-thread activity around it. Two channels'
       protocols genuinely racing is not modelled. MSG-7 (channels do not
       interfere) is the reason that is believed harmless, and it is an
       argument about the abstract operations rather than a proof about this
       particular composition.

   (k) THE C CODE IS NOT THE KERNEL'S. The AMP_Channel_C session checks two
       hand-written C functions against the design-level operations. That C
       exists nowhere in the real kernel translation unit; it is not spliced
       into kernel_all.c and it does not describe what runs on hardware. DUR-2
       and DUR-3 are stated at the DESIGN level, which is a genuine step below
       the specification but still above the shipped binary. Nothing else in
       this file depends on the C session's results, deliberately.

   WHAT SECTION 1 INHERITS, AND WHAT IT DOES NOT. The isolation results depend
   on none of the interleaving limits — neither (a)'s ordering assumptions nor
   (i) nor (j) — because they are properties of a STATIC configuration enforced
   per-access by each hart's own MMU, and no interleaving can break them. They
   do rest on (b) and (d), as does everything else here. *)


section \<open>5. Non-vacuity — the guarantees are not empty\<close>

(* Every theorem above is conditional on `amp_partition_wf`, and the messaging
   results are conditional on operations actually being enabled. If no
   configuration satisfied those hypotheses, the whole list would be true and
   worthless. It is not: a genuine two-core, one-channel system satisfies them,
   and a real round trip runs in it. *)

(* A real configuration is well-formed: two cores each privately owning two
   frames, one declared channel between them using a third, disjoint frame. *)
theorem a_real_configuration_is_wellformed: "amp_partition_wf example2"
  using example2_partition_wf .

(* A real round trip is enabled in it: core 0 sends into the channel buffer, and
   core 1's receive/acknowledge returns the channel to exactly its prior state
   (MSG-6, witnessed concretely rather than assumed reachable). *)
theorem a_real_round_trip_runs:
  assumes m: "changed_frames m m' \<subseteq> {0x8000}"
  shows "xchan_send chan01 m m' example_xchan0 (example_xchan0(chan01 \<mapsto> XSendPending))
       \<and> xchan_recv_ack chan01 (example_xchan0(chan01 \<mapsto> XSendPending)) example_xchan0"
  using m by (auto simp: xchan_send_def xchan_recv_ack_def example_xchan0_def chan01_def)

(* And the declared authority in that system is exactly the two edges you would
   expect — core 0 may send, core 1 may receive, and core 1 may NOT send back
   (ISO-5, witnessed concretely). *)
theorem a_real_configurations_authority_is_as_declared:
  "(0, XSend, chan01) \<in> amp_auth_graph example2"
  "(1, XRecv, chan01) \<in> amp_auth_graph example2"
  "(1, XSend, chan01) \<notin> amp_auth_graph example2"
  using example2_auth_graph_edges example2_core1_has_no_send_authority by blast+

(* And a real message value, sent on that same channel, is invisible to a
   bystander core outside it — witnessed concretely rather than only proved
   in the abstract, so MSG-9 is not true-but-empty either. *)
theorem a_real_messages_send_is_invisible_to_a_bystander:
  assumes send: "xchan_send_msg chan01 example_msg m m' xm xm'"
  shows "observation example2 99 m = observation example2 99 m'"
  using example2_send_is_invisible_to_a_bystander[OF send] .

(* And MSG-8's new hypothesis is satisfiable, not vacuous either: a genuine
   thread-ownership assignment over the example system exists (thread 10
   owns chan01's send side on core 0, thread 20 its receive side on core 1),
   so the thread_partition_wf premise thread ownership adds is not an empty
   requirement. (No witness is given, or should be, for the remaining
   thread_attribution/A-THR hypothesis itself — see section 4.1(c) and the
   AMP_Thread theory header for why any such witness would be vacuous.) *)
theorem a_real_thread_ownership_assignment_exists:
  "thread_partition_wf example2 example_tp"
  using example_tp_wf .

(* And DUR-4 is witnessed on a genuinely interleaved execution rather than a
   serialised one, which matters more here than for the requirements above: a
   refinement result whose only instances were sequential executions would be
   true and worthless. This is a real six-step execution of the example system
   — the sending kernel storing into the buffer, a THIRD thread taking a step
   in the middle of that copy, the send's status store, the receiving kernel's
   copy, and the acknowledgement — and it performs the three-operation protocol
   run you would expect: the interleaved thread's step, one whole send, one
   whole acknowledgement. Both copy loops have vanished at the protocol level,
   which is DUR-4's content made concrete. *)
theorem a_real_interleaved_execution_performs_a_protocol_run:
  "atrace [COwnerWrite 0x8000, COther 20, COwnerCommit,
           CRecvStart, CRecvCopy 0x8000, CRecvCommit]
   = [AOther 20, ASend, AAck]"
  "\<exists>s' :: nat conc_state.
     csteps example2 chan01 example_tp example_msg example_s0
       [COwnerWrite 0x8000, COther 20, COwnerCommit,
        CRecvStart, CRecvCopy 0x8000, CRecvCommit] s'
     \<and> asteps example2 chan01 example_tp example_msg
         (abs_mem chan01 example_s0) (cs_xm example_s0)
         [AOther 20, ASend, AAck] (abs_mem chan01 s') (cs_xm s')"
  using example_simulated_run by blast+

(* And DUR-5 constrains real memory. "The frames a step changes are among the
   frames it owns" is trivially true if no step ever changes anything, and
   trivially true if every frame is owned. Neither holds: a one-byte write into
   core 0's own private frame is a permitted step and does change a frame; the
   same write into core 1's private frame is not permitted. *)
theorem a_real_step_changes_memory_and_a_forbidden_one_is_refused:
  assumes own:   "underlying_memory (machine_state s) 0x1000 \<noteq> v"
      and other: "underlying_memory (machine_state s) 0x3000 \<noteq> w"
  shows "amp_step 0 (mem_proj s) (mem_proj (mem_upd s 0x1000 v)) example2
         \<and> changed_frames (mem_proj s) (mem_proj (mem_upd s 0x1000 v)) \<noteq> {}"
    and "\<not> amp_step 0 (mem_proj s) (mem_proj (mem_upd s 0x3000 w)) example2"
  using example2_amp_step_changes_own_frame[OF own]
        example2_amp_step_forbids_other_frame[OF other] by blast+

(* WHAT SECTION 5 DOES NOT WITNESS. Every witness above is for a hypothesis of
   some requirement, except one: there is none for A-BOOT. No concrete kernel
   state satisfying `amp_gs_inv` is exhibited, so nothing here rules out DUR-5
   and ISO-2 being conditional on something unsatisfiable.

   The gap is `invs` — seL4's own kernel invariant — not anything the AMP work
   introduced. l4v exhibits a state satisfying `invs` once, in
   `Example_Valid_State.thy` (1971 lines, a different labelling), and reaches
   its initial state through an axiomatised initialisation. The partition-shaped
   half of A-BOOT is witnessed in AMP_Invariant: core 0 owns the buffer it sends
   on, core 1 does not, and core 1 has read access to it — the asymmetry that
   makes the condition satisfiable by a channel-using system rather than only by
   a silent one. *)

end
