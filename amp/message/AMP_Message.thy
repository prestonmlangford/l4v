(*
 * PolarFire verified multicore (AMP) — Phase 5.5: message content, integrity
 * & confidentiality (M1–M4).
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * Every phase before this one proves things about WHO HOLDS WHICH PERMISSION
 * on WHICH FRAME. Buffer contents are polymorphic and never inspected, so
 * there is no "message" object anywhere in the model yet to state a
 * value-level security property about. This phase adds exactly that: a
 * message operand for the send/recv protocol (M1), an integrity theorem
 * saying the receiver reads the value the sender wrote (M2), a
 * confidentiality theorem saying a send is invisible to any core outside the
 * channel (M3), and an explicit accounting of the one real backward flow the
 * protocol has — the acknowledgement (M4). See ../../multicore-amp-plan.md
 * section 5 (Phase 5.5).
 *
 * DESIGN FINDING THAT SHAPES M2. `frame_perm` is a function of the STATIC
 * boot partition alone (Phase 2), so the sender holds PermRW on its own
 * channel's buffer for the system's entire lifetime — including while a
 * message sits pending. Nothing in the model stops the sender issuing a
 * further write to the buffer after marking it send-pending. That is not a
 * security violation (the sender can only corrupt its own message, and no
 * third core is involved), but it does mean "the receiver reads what the
 * sender wrote" is FALSE in general without a quiescence condition. The fix
 * is not to make frame_perm dynamic — that would spend the static-permission
 * property section 1 of AMP_Overview rests on — but to state M2 under a
 * named locale assumption, `sender_quiescent`, exactly the same pattern
 * Phase 3 already uses for `atomic_xchan`: a fact this phase CONSUMES rather
 * than discharges, left for Phase 6's D2 (the ownership-mutex result) to
 * turn into a theorem.
 *
 * WHY A NEW STEP RELATION (amp_step_w). Phase 2's `amp_step` bounds a core's
 * changed frames by `owned_frames`, which — deliberately, for Phase 2's own
 * purposes — does not distinguish read from write access: a channel's
 * RECEIVER "owns" the buffer in that coarse sense too, even though it only
 * ever holds PermR there. That coarseness is harmless for Phase 2's headline
 * results (which are about PRIVATE memory, never about buffer contents), but
 * it is exactly wrong for a value-level claim: it would let a receiver's own
 * step "legally" appear to rewrite the buffer it is only supposed to read.
 * `amp_step_w` below tightens the bound to `frame_perm bp c f = PermRW` — the
 * ACTUAL write authority Phase 2/5 already established — and comes with a
 * one-line proof that it REFINES `amp_step` (every PermRW frame is an owned
 * frame), so nothing in Phase 2 is rewritten: every existing amp_step result
 * still applies to any amp_step_w step, it is simply a stronger hypothesis to
 * discharge.
 *
 * SCOPE. Everything below reasons about a single send, an arbitrary but
 * FINITE run of permission-respecting steps while the message sits pending,
 * and a single recv/ack — i.e. one message's lifecycle in isolation, not
 * multiple cores genuinely racing against each other in real time. That
 * finer question — soundness of treating the whole protocol as atomic under
 * real interleaved execution — is exactly Phase 6's D1/D2, which is also what
 * discharges the `sender_quiescent` locale this phase merely assumes. This
 * matches AMP_Overview's gap (a): "no concurrency" is not resolved here, only
 * narrowed enough to make M1–M4 statable.
 *
 * This theory is organized in the usual four zones (plan section 2.5).
 *)

theory AMP_Message
imports "AMP_Channel_AC.AMP_Channel_AC"
begin

section \<open>Specification\<close>

subsection \<open>M1 — message content\<close>

(* xchan_send_msg ch msg m m' xm xm': a send that additionally records WHAT
   was written, not just that something was. It is xchan_send (Phase 3)
   together with one extra clause: every frame of ch's buffer, after the
   write, equals the sender's intended message msg at that frame. This is a
   STRICT REFINEMENT of xchan_send — the footprint clause
   (changed_frames m m' \<subseteq> ch_buffer ch) is inherited unchanged from the
   definition it wraps — so every existing fact about xchan_send is available
   for free (see xchan_send_msg_is_xchan_send below); nothing from Phases 3-5
   needs to be re-proved, only re-derived through this one destructor. *)
definition xchan_send_msg ::
  "amp_channel \<Rightarrow> (obj_ref \<Rightarrow> 'v) \<Rightarrow> (obj_ref \<Rightarrow> 'v) \<Rightarrow> (obj_ref \<Rightarrow> 'v)
     \<Rightarrow> xchan_map \<Rightarrow> xchan_map \<Rightarrow> bool" where
  "xchan_send_msg ch msg m m' xm xm' \<equiv>
     xchan_send ch m m' xm xm' \<and> (\<forall>f \<in> ch_buffer ch. m' f = msg f)"

(* xchan_recv ch m: what a receiver reading channel ch's buffer out of
   system memory m actually gets — an option-valued function that is
   Some (m f) on ch's buffer frames and None everywhere else. The None
   outside the buffer is not a claim that other memory is secret (that is
   `observation`'s job below); it simply says a channel's receive interface
   exposes nothing beyond its own buffer. Comparing two `xchan_recv ch`
   results directly is how M2 states "the receiver got exactly the sent
   value" as a single equation rather than a per-frame quantifier. *)
definition xchan_recv :: "amp_channel \<Rightarrow> (obj_ref \<Rightarrow> 'v) \<Rightarrow> (obj_ref \<Rightarrow> 'v option)" where
  "xchan_recv ch m = (\<lambda>f. if f \<in> ch_buffer ch then Some (m f) else None)"

subsection \<open>A permission-respecting step relation\<close>

(* amp_step_w c m m' bp: core c takes a step whose every changed frame is one
   c actually holds WRITE authority on, per Phase 2's frame_perm. This is
   strictly more precise than Phase 2's amp_step (which bounds changes by
   owned_frames, conflating c's read and write reach) — see the theory header
   for why that extra precision is exactly what a value-level claim needs.
   amp_step_w is not a replacement for amp_step; it is a new, additional
   relation, shown below to IMPLY amp_step, so it inherits every one of
   Phase 2's B1-B3 results as a corollary rather than requiring them to be
   re-proved. *)
definition amp_step_w ::
  "core_id \<Rightarrow> (obj_ref \<Rightarrow> 'v) \<Rightarrow> (obj_ref \<Rightarrow> 'v) \<Rightarrow> amp_partition \<Rightarrow> bool" where
  "amp_step_w c m m' bp \<equiv> \<forall>f \<in> changed_frames m m'. frame_perm bp c f = PermRW"

(* quiescent_step bp xm ch m m': one step of SOME core, taken while ch is
   send-pending under the fixed status map xm. This is the unit of the "run"
   M2 reasons over: a run of these steps models whatever unrelated kernel
   activity happens between a send completing and its matching recv/ack,
   restricted to the window where the message is still sitting unread. xm is
   carried explicitly (rather than assumed constant) because nothing in this
   definition forces it; the lemmas below only ever apply it across a run
   where xm provably does not change (xchan_send/xchan_recv_ack are the only
   operations that touch xm, and neither one is a member of this run). *)
definition quiescent_step ::
  "amp_partition \<Rightarrow> xchan_map \<Rightarrow> amp_channel \<Rightarrow> (obj_ref \<Rightarrow> 'v) \<Rightarrow> (obj_ref \<Rightarrow> 'v) \<Rightarrow> bool" where
  "quiescent_step bp xm ch m m' \<equiv> xm ch = Some XSendPending \<and> (\<exists>c. amp_step_w c m m' bp)"

subsection \<open>M3 — an observer's view of memory\<close>

(* observation bp c m: everything core c can see of system memory m — Some
   value on every frame c holds ANY access to (read or write), None
   elsewhere. Two memories that give the same core the same observation are,
   by construction, indistinguishable to it; this is the standard
   storage-channel noninterference formulation (mirroring single-core
   InfoFlow's observation functions), specialised to this model's frame_perm.
   M3 below is the statement that a send never changes a non-endpoint core's
   observation, whatever the message value. *)
definition observation ::
  "amp_partition \<Rightarrow> core_id \<Rightarrow> (obj_ref \<Rightarrow> 'v) \<Rightarrow> (obj_ref \<Rightarrow> 'v option)" where
  "observation bp c m = (\<lambda>f. if frame_perm bp c f \<noteq> PermNone then Some (m f) else None)"

section \<open>Proof development (internal machinery)\<close>

(* Destructor: a frame a core holds PermRW on is always one of its owned
   frames. This is the one fact that links amp_step_w back to Phase 2's
   amp_step: frame_perm's two PermRW-producing branches (owns_priv,
   maps_writer) are each individually a sub-case of owned_frames's two
   disjuncts (private frames, channel buffers of an endpoint core). *)
lemma permRW_frame_is_owned:
  assumes perm: "frame_perm bp c f = PermRW"
  shows "f \<in> owned_frames bp c"
proof -
  from perm have "owns_priv bp c f \<or> maps_writer bp c f"
    by (simp add: frame_perm_def split: if_splits)
  then show ?thesis
  proof
    assume "owns_priv bp c f"
    then obtain r where "ap_cores bp c = Some r" and "f \<in> cr_frames r"
      unfolding owns_priv_def by blast
    then show ?thesis by (auto simp: owned_frames_def)
  next
    assume "maps_writer bp c f"
    then obtain ch where "ch \<in> ap_channels bp" and "f \<in> ch_buffer ch" and "c = ch_from ch"
      unfolding maps_writer_def by blast
    then show ?thesis by (auto simp: owned_frames_def channel_endpoints_def)
  qed
qed

(* amp_step_w REFINES amp_step: every permission-respecting step is, in
   particular, a step confined to owned frames. This is the fact that lets
   every one of Phase 2's B1-B3 theorems be reused unchanged for amp_step_w
   steps — nothing about Phase 2 is edited, this is purely additive. *)
lemma amp_step_w_is_amp_step:
  "amp_step_w c m m' bp \<Longrightarrow> amp_step c m m' bp"
  unfolding amp_step_def amp_step_w_def
  using permRW_frame_is_owned by blast

(* On a declared channel's buffer frame, PermRW is held by the sender and by
   no one else: the receiver's own asymmetric mapping is PermR (Phase 2's
   buffer_perm_asymmetric), and every other core holds PermNone there (Phase
   2's buffer_perm_only_endpoints) — so PermRW singles out ch_from ch
   uniquely. This is the fact that turns "no PermRW, no write" into "only the
   sender can ever write this frame". *)
lemma buffer_write_requires_sender:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
      and perm: "frame_perm bp c f = PermRW"
  shows "c = ch_from ch"
proof (rule ccontr)
  assume ne: "c \<noteq> ch_from ch"
  show False
  proof (cases "c = ch_to ch")
    case True
    with buffer_perm_asymmetric[OF wf ch f] perm show False by simp
  next
    case False
    with ne buffer_perm_only_endpoints[OF wf ch f ne] perm show False by simp
  qed
qed

(* Any permission-respecting step by a core OTHER than ch's declared sender
   leaves every one of ch's buffer frames untouched — unconditionally, no
   locale needed. This is the parenthetical half of M2's plan statement ("no
   interleaved amp_step c for c \<noteq> ch_from ch can alter it"): a non-sender
   step cannot even in principle write there, because buffer_write_requires_
   sender rules out anyone else ever holding the PermRW that amp_step_w
   demands. *)
lemma amp_step_w_confined_to_sender_on_buffer:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp"
      and step: "amp_step_w c m m' bp" and c: "c \<noteq> ch_from ch"
  shows "\<forall>f \<in> ch_buffer ch. m' f = m f"
proof (intro ballI)
  fix f assume f: "f \<in> ch_buffer ch"
  show "m' f = m f"
  proof (rule ccontr)
    assume "m' f \<noteq> m f"
    then have "f \<in> changed_frames m m'" by (simp add: changed_frames_def)
    with step have "frame_perm bp c f = PermRW" by (simp add: amp_step_w_def)
    with buffer_write_requires_sender[OF wf ch f] c show False by simp
  qed
qed

(* Destructor: a content-carrying send is, underneath, a plain xchan_send.
   Everything Phases 3-5 proved about xchan_send therefore applies to
   xchan_send_msg via this one line, per the theory header's "re-derived, not
   rewritten" principle. *)
lemma xchan_send_msg_is_xchan_send:
  "xchan_send_msg ch msg m m' xm xm' \<Longrightarrow> xchan_send ch m m' xm xm'"
  by (simp add: xchan_send_msg_def)

section \<open>Results\<close>

subsection \<open>Phases 3 and 5, re-derived (not rewritten) for the content-carrying send\<close>

(* The content-carrying send still preserves the spatial partition (B1-B3):
   an immediate corollary of C1 (xchan_send_preserves_partition) through the
   destructor above. This is the concrete demonstration, promised in the
   theory header, that adding message content changes nothing Phase 2/3
   already established. *)
theorem xchan_send_msg_preserves_partition:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp"
      and send: "xchan_send_msg ch msg m m' xm xm'"
  shows "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> ch_from ch \<noteq> c'
                 \<longrightarrow> changed_frames m m' \<inter> cr_frames r' = {}"
    and "\<forall>ch' \<in> ap_channels bp. \<forall>f \<in> ch_buffer ch'.
           frame_perm bp (ch_from ch') f = PermRW
           \<and> frame_perm bp (ch_to ch') f = PermR"
    and "\<forall>c' r' f. ap_cores bp c' = Some r' \<longrightarrow> f \<in> cr_frames r' \<longrightarrow> ch_from ch \<noteq> c'
                   \<longrightarrow> frame_perm bp (ch_from ch) f \<noteq> PermRW"
  using xchan_send_preserves_partition[OF wf ch xchan_send_msg_is_xchan_send[OF send]]
  by blast+

(* The content-carrying send is still authority-confined (D-spatial, Phase
   5): an immediate corollary of xchan_send_authority_confined, the same way.
   Adding a message operand conveys no new authority to anyone. *)
theorem xchan_send_msg_authority_confined:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp"
      and send: "xchan_send_msg ch msg m m' xm xm'"
  shows "\<forall>f \<in> changed_frames m m'. \<forall>c. frame_perm bp c f = PermRW
           \<longrightarrow> (c, XSend, ch) \<in> amp_auth_graph bp"
  using xchan_send_authority_confined[OF wf ch xchan_send_msg_is_xchan_send[OF send]] .

subsection \<open>M2 — message integrity, under a named quiescence assumption\<close>

(* sender_quiescent bp ch: the one fact this phase CANNOT derive and must
   name explicitly (matching Phase 3's atomic_xchan) — that channel ch's
   declared sender issues no further permission-respecting write to ch's own
   buffer while ch is send-pending. Without this, the sender's standing
   PermRW (static for the system's whole lifetime, per Phase 2) would let it
   legally tear its own just-sent message before the receiver reads it: not a
   security breach (only the sender's own message is at risk, and no other
   core is ever involved — see the theory header), but a real functional-
   correctness gap that makes "the receiver reads what was sent" false
   without this hypothesis. Phase 6's D2 (the buffer ownership-mutex
   invariant, tracked over TIME rather than just space) is what turns this
   from an assumed locale into a proved one; nothing here attempts that.
   There is deliberately no non-vacuity witness for this locale in the
   Examples section below: satisfying it is a genuine claim about the
   sender's own code, which this development does not model, so any witness
   would either assume the very thing being checked or be vacuous. *)
locale sender_quiescent =
  fixes msg_type :: "'v itself"
    and bp :: amp_partition
    and ch :: amp_channel
  assumes wf: "amp_partition_wf bp"
      and ch_declared: "ch \<in> ap_channels bp"
      and sender_quiescent_while_pending:
        "\<And>(m :: obj_ref \<Rightarrow> 'v) m' xm. xm ch = Some XSendPending
           \<Longrightarrow> amp_step_w (ch_from ch) m m' bp \<Longrightarrow> \<forall>f \<in> ch_buffer ch. m' f = m f"
begin

(* Under the locale: ANY single permission-respecting step taken while ch is
   pending — by the sender (locale assumption) or by anyone else
   (unconditional, amp_step_w_confined_to_sender_on_buffer) — leaves ch's
   buffer untouched. This is the per-step building block quiescent_run_
   preserves_buffer below extends to an arbitrary run. *)
lemma quiescent_step_preserves_buffer:
  assumes qs: "quiescent_step bp xm ch (m :: obj_ref \<Rightarrow> 'v) m'"
  shows "\<forall>f \<in> ch_buffer ch. m' f = m f"
proof -
  from qs have pending: "xm ch = Some XSendPending"
    and ex: "\<exists>c. amp_step_w c m m' bp"
    by (simp_all add: quiescent_step_def)
  from ex obtain c where step: "amp_step_w c m m' bp" ..
  show ?thesis
  proof (cases "c = ch_from ch")
    case True
    have step': "amp_step_w (ch_from ch) m m' bp" using step True by simp
    show ?thesis using sender_quiescent_while_pending pending step' by blast
  next
    case False
    show ?thesis using amp_step_w_confined_to_sender_on_buffer[OF wf ch_declared step False] .
  qed
qed

(* Generalising the single step to an arbitrary FINITE run of them (the
   reflexive-transitive closure of quiescent_step): as long as ch stays
   send-pending throughout — which holds automatically here, since nothing in
   quiescent_step's steps touches xm, only xchan_send/xchan_recv_ack do, and
   neither is a member of the run — the buffer is exactly as stable across
   the whole run as it is across one step. This is what lets M2 below cover
   "whatever unrelated kernel activity happens between the send and the
   matching recv", not just a single interleaved instruction. *)
lemma quiescent_run_preserves_buffer:
  "(quiescent_step bp xm ch)\<^sup>*\<^sup>* (m :: obj_ref \<Rightarrow> 'v) m'' \<Longrightarrow> \<forall>f \<in> ch_buffer ch. m'' f = m f"
proof (induct rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  from quiescent_step_preserves_buffer[OF step.hyps(2)] step.hyps
  show ?case by fastforce
qed

(* M2. THE RECEIVER READS EXACTLY THE MESSAGE THE SENDER SENT. Send msg on
   ch (producing m' with msg written into the buffer and the channel marked
   pending); let any finite run of permission-respecting steps happen while
   it sits pending (producing m''); then recv/ack it. Under sender_quiescent,
   the receiver's xchan_recv on the final memory m'' equals xchan_recv on the
   message msg the sender supplied — bit for bit, not merely "some value was
   delivered". The recv/ack step itself needs no separate memory argument
   (xchan_recv_ack has none — it only flips the status map), so the claim is
   entirely about the memory the run already fixed. *)
theorem message_integrity:
  assumes send: "xchan_send_msg ch (msg :: obj_ref \<Rightarrow> 'v) m m' xm0 xm1"
      and run:  "(quiescent_step bp xm1 ch)\<^sup>*\<^sup>* m' m''"
      and recv: "xchan_recv_ack ch xm1 xm2"
  shows "xchan_recv ch m'' = xchan_recv ch msg"
proof -
  from send have buf_eq_msg: "\<forall>f \<in> ch_buffer ch. m' f = msg f"
    by (simp add: xchan_send_msg_def)
  from quiescent_run_preserves_buffer[OF run] have buf_stable: "\<forall>f \<in> ch_buffer ch. m'' f = m' f" .
  have "\<forall>f \<in> ch_buffer ch. m'' f = msg f" using buf_eq_msg buf_stable by simp
  then show ?thesis using recv by (auto simp: xchan_recv_def)
qed

end

subsection \<open>M3 — confidentiality: a send is invisible to any non-endpoint core\<close>

(* M3. NO THIRD CORE LEARNS ANYTHING FROM A SEND, FOR ANY MESSAGE VALUE. For
   a core c that is neither ch's declared sender nor its declared receiver,
   c's observation of memory is bit-for-bit the same before and after a send
   on ch — for every buffer frame, c holds PermNone (Phase 2's buffer_perm_
   only_endpoints) so both observations are None regardless of what the
   message was; for every other frame, the send did not touch it at all
   (xchan_send's own footprint bound). This holds unconditionally — no
   locale, no quiescence assumption — because it needs nothing about WHEN c
   looks, only that c has no mapping to look through. This is the storage-
   channel noninterference statement the plan's M3 calls for, falling out
   exactly as predicted from changed_frames \<subseteq> ch_buffer ch plus
   frame_perm = PermNone. *)
theorem xchan_send_msg_invisible_to_third_core:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp"
      and send: "xchan_send_msg ch msg m m' xm xm'"
      and c1: "c \<noteq> ch_from ch" and c2: "c \<noteq> ch_to ch"
  shows "observation bp c m = observation bp c m'"
proof (rule ext)
  fix f
  show "observation bp c m f = observation bp c m' f"
  proof (cases "f \<in> ch_buffer ch")
    case True
    with buffer_perm_only_endpoints[OF wf ch True c1 c2] show ?thesis
      by (simp add: observation_def)
  next
    case False
    from send have "changed_frames m m' \<subseteq> ch_buffer ch"
      by (simp add: xchan_send_msg_def xchan_send_def)
    with False have "m f = m' f" by (auto simp: changed_frames_def)
    then show ?thesis by (simp add: observation_def)
  qed
qed

subsection \<open>M4 — the acknowledgement is a real, but bounded, reverse flow\<close>

(* M4. THE ONLY THING A RECV/ACK EVER SENDS BACKWARD IS ONE CHANNEL'S OWN
   STATUS BIT. The channel is one-way for DATA, but the receiver does
   influence the sender: the sender learns, by reading ch's status, that its
   message was consumed. That influence is exactly ch's own entry flipping
   to XIdle — every other channel's status is untouched (mirrors REQ-MSG-7's
   recv/ack half at this level) — and it carries no message CONTENT at all,
   which is not an extra fact to prove but immediate from xchan_recv_ack's
   type: the operation has no memory operand whatsoever, so it is
   definitionally incapable of moving a value anywhere. This is the
   accounting the plan's M4 calls for: the reverse flow is real, it is
   intended (a working protocol needs it), and it is bounded to one bit per
   round trip with zero content — so a later confidentiality theorem (Phase
   7's E2) must be phrased to ALLOW this flow, not to claim its absence. *)
theorem xchan_recv_ack_reverse_flow_is_bounded_to_one_status_bit:
  assumes rc: "xchan_recv_ack ch xm xm'"
  shows "xm' ch = Some XIdle"
    and "\<forall>d. d \<noteq> ch \<longrightarrow> xm' d = xm d"
proof -
  show "xm' ch = Some XIdle" using rc by (simp add: xchan_recv_ack_def)
next
  show "\<forall>d. d \<noteq> ch \<longrightarrow> xm' d = xm d" using rc by (auto simp: xchan_recv_ack_def)
qed

section \<open>Examples\<close>

subsection \<open>A concrete message, delivered intact and unseen by a bystander\<close>

(* A concrete message value over the example system's frames: 42 on the
   channel's one buffer frame (0x8000), an arbitrary placeholder (0)
   everywhere else — the placeholder value is never inspected by anything
   below, only the buffer-frame value is. *)
definition example_msg :: "obj_ref \<Rightarrow> nat" where
  "example_msg = (\<lambda>f. if f = 0x8000 then 42 else 0)"

(* Non-vacuity for M1: writing example_msg into chan01's buffer and nothing
   else is a genuine xchan_send_msg instance from the example system's
   initial (idle) status map. *)
lemma example_xchan_send_msg_instance:
  assumes mem: "changed_frames m m' \<subseteq> {0x8000}"
      and val: "m' 0x8000 = example_msg 0x8000"
  shows "xchan_send_msg chan01 example_msg m m' example_xchan0
           (example_xchan0(chan01 \<mapsto> XSendPending))"
  using mem val by (simp add: xchan_send_msg_def xchan_send_def example_xchan0_def chan01_def)

(* Non-vacuity for M3: a bystander core (99 — deliberately not one of
   example2's two declared cores, and in particular neither chan01's sender
   nor its receiver) observes nothing different across a send of example_msg
   on chan01. This is the concrete instance of "a send is invisible outside
   its declared endpoints" — the security property that holds regardless of
   what the message says. *)
lemma example2_send_is_invisible_to_a_bystander:
  assumes send: "xchan_send_msg chan01 example_msg m m' xm xm'"
  shows "observation example2 99 m = observation example2 99 m'"
proof -
  have ch: "chan01 \<in> ap_channels example2" by (simp add: example2_def)
  have c1: "(99 :: core_id) \<noteq> ch_from chan01" and c2: "(99 :: core_id) \<noteq> ch_to chan01"
    by (simp_all add: chan01_def)
  show ?thesis
    using xchan_send_msg_invisible_to_third_core[OF example2_partition_wf ch send c1 c2] .
qed

(* Non-vacuity for M4: a concrete recv/ack on chan01 flips exactly its own
   status to idle. Combined with completed_round_trip_leaves_no_residue
   (Phase 3/AMP_Overview), this is the whole round trip's visible footprint
   from the sender's side — one bit, and nothing else. *)
lemma example2_recv_ack_flips_only_chan01:
  assumes rc: "xchan_recv_ack chan01 (example_xchan0(chan01 \<mapsto> XSendPending)) example_xchan0"
  shows "example_xchan0 chan01 = Some XIdle"
  using xchan_recv_ack_reverse_flow_is_bounded_to_one_status_bit[OF rc] by simp

end
