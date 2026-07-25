(*
 * PolarFire verified multicore (AMP) — Phase 3: channel object + abstract
 * operations (C1–C3).
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * Phase 3 adds the cross-core channel as a first-class object with runtime
 * state, and gives it abstract semantics mirroring seL4's IPC endpoints
 * (Ipc_AI): a send operation and a combined receive-and-acknowledge
 * operation, each specified as a single ATOMIC step. Both are shown to
 * preserve the spatial partition invariant (B1–B3) established in Phase 2 —
 * not by re-deriving spatial reasoning, but by observing that each op is a
 * special case of the `amp_step` relation Phase 2 already covers. See
 * ../../multicore-amp-plan.md section 5 (Phase 3).
 *
 * Two deliberate simplifications versus a literal reading of the plan's
 * sketch, recorded here so the design choice is visible:
 *
 *   - NO SEPARATE OBJECT RECORD. The plan describes "a datatype paralleling
 *     Structures_A endpoints ... with a swap-buffer index and an
 *     owning-core field." Structures_A endpoints need those fields because
 *     an endpoint is reached indirectly through an obj_ref into the kernel
 *     heap. A declared `amp_channel` (AMP_Model.thy) is not indirected that
 *     way — it already IS a value carrying its owning core (ch_from) and its
 *     buffer (ch_buffer). Adding a wrapper record with redundant copies of
 *     those fields would be pure duplication, so the runtime object is just
 *     a status per declared channel (xchan_map below).
 *
 *   - TWO RUNTIME STATES, NOT THREE. Structures_A's endpoint has three
 *     constructors (IdleEP | SendEP | RecvEP) because RecvEP holds a QUEUE of
 *     blocked receiving threads. A channel has exactly one fixed receiver, no
 *     queue, and Phase 3 specifies "receive" and "ack" as a SINGLE atomic
 *     step (xchan_recv_ack) per the plan's own atomicity assumption for this
 *     phase. There is consequently no intermediate "ack pending" state that
 *     is ever actually occupied yet — it becomes meaningful only once Phase 6
 *     stops assuming atomicity and studies the ack race (D4) by splitting
 *     receive and ack into two separate steps. Introduced there, not here.
 *
 * This theory is organized in the usual four zones (plan section 2.5):
 * SPECIFICATION, PROOF DEVELOPMENT (none needed this phase — the results
 * follow directly from Phase 2's), RESULTS (C1–C3), EXAMPLES.
 *)

theory AMP_Channel_A
imports "AMP_Spatial.AMP_Spatial"
begin

section \<open>Specification\<close>

subsection \<open>Channel runtime status\<close>

(* The runtime protocol state of one declared channel: XIdle (no message in
   flight, ready to send) or XSendPending (the sender has written the buffer
   and the receiver has not yet consumed it). This is the dynamic counterpart
   to the STATIC declaration in ap_channels — a channel can be declared (and
   hence well-formed, spatially) while carrying no message at all. *)
datatype xchan_status = XIdle | XSendPending

(* The runtime status of every declared channel in the system, keyed by the
   channel itself (channels are already distinguishable by their buffers
   under a well-formed partition, so no separate identifier is needed). This
   is genuinely new state beyond amp_state — the boot partition never
   changes, but which channels currently hold an unread message does. *)
type_synonym xchan_map = "amp_channel \<rightharpoonup> xchan_status"

subsection \<open>Well-formedness of the runtime status map\<close>

(* The runtime status map tracks exactly the declared channels of bp: no
   channel is missing a status, and no status exists for an undeclared
   channel. This is the channel-protocol analogue of the kernel's
   object-table consistency invariants (e.g. sym_refs linking every endpoint
   reference to a real object) — drastically simplified because channels here
   are static values, not allocated objects. *)
definition xchan_dom_wf :: "amp_partition \<Rightarrow> xchan_map \<Rightarrow> bool" where
  "xchan_dom_wf bp xm \<equiv> dom xm = ap_channels bp"

subsection \<open>Abstract channel operations\<close>

(* xchan_send ch m m' xm xm': the sender writes a message into channel ch's
   buffer. Preconditions: the channel must currently be idle. Effect: system
   memory changes only within ch's buffer (mirrors seL4's send_ipc writing
   only into the IPC buffer / registers of the transfer, nothing else), and
   the channel's status becomes XSendPending; every other channel's status is
   untouched (xm' agrees with xm off ch, by function update). Message CONTENT
   is left unmodelled, exactly as Phase 2 left memory contents polymorphic —
   the spatial argument never needs to know what was written, only where. *)
definition xchan_send ::
  "amp_channel \<Rightarrow> (obj_ref \<Rightarrow> 'v) \<Rightarrow> (obj_ref \<Rightarrow> 'v) \<Rightarrow> xchan_map \<Rightarrow> xchan_map \<Rightarrow> bool" where
  "xchan_send ch m m' xm xm' \<equiv>
     xm ch = Some XIdle \<and> changed_frames m m' \<subseteq> ch_buffer ch \<and> xm' = xm(ch \<mapsto> XSendPending)"

(* xchan_recv_ack ch xm xm': the receiver reads the pending message and the
   channel is released back to idle, in one atomic step (the plan's
   atomicity assumption for this phase; splitting this into a genuine
   two-step receive/ack protocol is Phase 6's D4). Precondition: a message
   must be pending. Effect: only the status map changes — reading a buffer
   changes no frame's contents, so there is deliberately no memory operand
   here at all. *)
definition xchan_recv_ack :: "amp_channel \<Rightarrow> xchan_map \<Rightarrow> xchan_map \<Rightarrow> bool" where
  "xchan_recv_ack ch xm xm' \<equiv> xm ch = Some XSendPending \<and> xm' = xm(ch \<mapsto> XIdle)"

section \<open>Results\<close>

subsection \<open>Well-definedness: neither op changes which channels are tracked\<close>

(* Half of C1's "send is well-defined": sending never adds or drops a tracked
   channel, so xchan_dom_wf is preserved across a send. *)
lemma xchan_send_dom_preserved: "xchan_send ch m m' xm xm' \<Longrightarrow> dom xm' = dom xm"
  by (auto simp: xchan_send_def)

(* Half of C2's "recv/ack is well-defined": likewise for recv_ack. *)
lemma xchan_recv_ack_dom_preserved: "xchan_recv_ack ch xm xm' \<Longrightarrow> dom xm' = dom xm"
  by (auto simp: xchan_recv_ack_def)

subsection \<open>C1 — send preserves the spatial partition\<close>

(* A send's memory write is confined to ch's buffer, which lies inside the
   sender's owned frames (ch_from ch is one of ch's two channel_endpoints).
   So xchan_send's effect on memory is, by construction, an amp_step by the
   sender — no new spatial argument is needed, only this containment. *)
lemma xchan_send_is_amp_step:
  assumes ch: "ch \<in> ap_channels bp" and send: "xchan_send ch m m' xm xm'"
  shows "amp_step (ch_from ch) m m' bp"
proof -
  have "ch_buffer ch \<subseteq> owned_frames bp (ch_from ch)"
    using ch by (auto simp: owned_frames_def channel_endpoints_def)
  with send show ?thesis by (auto simp: xchan_send_def amp_step_def)
qed

(* C1: sending on a declared channel never breaks the spatial partition
   (B1–B3). Since xchan_send's memory write is exactly an amp_step by the
   sender (above), Phase 2's packaged theorem applies unchanged. This is the
   structural analogue of Ipc_AI's "send_ipc preserves invariants" lemmas:
   channel sends are simply a named special case of the already-verified
   step relation, not a fresh proof obligation. *)
theorem xchan_send_preserves_partition:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp"
      and send: "xchan_send ch m m' xm xm'"
  shows "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> ch_from ch \<noteq> c'
                 \<longrightarrow> changed_frames m m' \<inter> cr_frames r' = {}"      (* B1 *)
    and "\<forall>ch' \<in> ap_channels bp. \<forall>f \<in> ch_buffer ch'.
           frame_perm bp (ch_from ch') f = PermRW
           \<and> frame_perm bp (ch_to ch') f = PermR"                     (* B2 *)
    and "\<forall>c' r' f. ap_cores bp c' = Some r' \<longrightarrow> f \<in> cr_frames r' \<longrightarrow> ch_from ch \<noteq> c'
                   \<longrightarrow> frame_perm bp (ch_from ch) f \<noteq> PermRW"          (* B3 *)
  using amp_step_preserves_partition[OF wf xchan_send_is_amp_step[OF ch send]]
  by blast+

subsection \<open>C2 — recv/ack needs no fresh spatial argument\<close>

(* xchan_recv_ack has no memory operand at all: by construction it only
   updates the status map, never system memory. A step that changes no frame
   is trivially an amp_step for EVERY core (changed_frames m m = {} is a
   subset of any owned_frames set), so B1–B3 hold across any such null step
   unconditionally — the "recv/ack likewise" half of the exit test is, if
   anything, simpler than send's, since it needs no channel-specific fact at
   all, only that recv_ack never touches memory. *)
lemma xchan_null_step_preserves_partition:
  assumes wf: "amp_partition_wf bp"
  shows "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> c \<noteq> c'
                 \<longrightarrow> changed_frames m m \<inter> cr_frames r' = {}"
    and "\<forall>ch \<in> ap_channels bp. \<forall>f \<in> ch_buffer ch.
           frame_perm bp (ch_from ch) f = PermRW \<and> frame_perm bp (ch_to ch) f = PermR"
    and "\<forall>c' r' f. ap_cores bp c' = Some r' \<longrightarrow> f \<in> cr_frames r' \<longrightarrow> c \<noteq> c'
                   \<longrightarrow> frame_perm bp c f \<noteq> PermRW"
proof -
  have step: "amp_step c m m bp" by (simp add: amp_step_def changed_frames_def)
  show "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> c \<noteq> c'
               \<longrightarrow> changed_frames m m \<inter> cr_frames r' = {}"
       "\<forall>ch \<in> ap_channels bp. \<forall>f \<in> ch_buffer ch.
          frame_perm bp (ch_from ch) f = PermRW \<and> frame_perm bp (ch_to ch) f = PermR"
       "\<forall>c' r' f. ap_cores bp c' = Some r' \<longrightarrow> f \<in> cr_frames r' \<longrightarrow> c \<noteq> c'
                  \<longrightarrow> frame_perm bp c f \<noteq> PermRW"
    using amp_step_preserves_partition[OF wf step] by blast+
qed

(* C2 proper, specialised to the receiving core of an actual xchan_recv_ack
   transition, so the exit test can point at a definition-specific theorem
   rather than only the general null-step fact above. *)
corollary xchan_recv_ack_preserves_partition:
  assumes wf: "amp_partition_wf bp" and rc: "xchan_recv_ack ch xm xm'"
  shows "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> ch_to ch \<noteq> c'
                 \<longrightarrow> changed_frames m m \<inter> cr_frames r' = {}"
    and "\<forall>ch' \<in> ap_channels bp. \<forall>f \<in> ch_buffer ch'.
           frame_perm bp (ch_from ch') f = PermRW \<and> frame_perm bp (ch_to ch') f = PermR"
    and "\<forall>c' r' f. ap_cores bp c' = Some r' \<longrightarrow> f \<in> cr_frames r' \<longrightarrow> ch_to ch \<noteq> c'
                   \<longrightarrow> frame_perm bp (ch_to ch) f \<noteq> PermRW"
proof -
  have step: "amp_step (ch_to ch) m m bp" by (simp add: amp_step_def changed_frames_def)
  show "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> ch_to ch \<noteq> c'
               \<longrightarrow> changed_frames m m \<inter> cr_frames r' = {}"
       "\<forall>ch' \<in> ap_channels bp. \<forall>f \<in> ch_buffer ch'.
          frame_perm bp (ch_from ch') f = PermRW \<and> frame_perm bp (ch_to ch') f = PermR"
       "\<forall>c' r' f. ap_cores bp c' = Some r' \<longrightarrow> f \<in> cr_frames r' \<longrightarrow> ch_to ch \<noteq> c'
                  \<longrightarrow> frame_perm bp (ch_to ch) f \<noteq> PermRW"
    using amp_step_preserves_partition[OF wf step] by blast+
qed

subsection \<open>C3 — the buffer mapping invariant (B2) holds throughout the protocol\<close>

(* C3: whichever state a channel is in — idle, or holding a pending message —
   the underlying MMU mapping intent (B2's writer/reader asymmetry) never
   changes, because frame_perm is a pure function of the STATIC boot
   partition bp, and neither xchan_send nor xchan_recv_ack ever touches bp
   (only the dynamic status map, or in send's case, buffer CONTENTS). So the
   "buffer swap" the channel protocol performs is a change of contents and
   status only; the permission map that governs who may read/write the
   buffer is fixed for the lifetime of the system, and Phase 2's B2 theorem
   may be reused unconditionally at every point in the send/recv-ack
   round trip rather than re-established at each step. *)
theorem xchan_protocol_preserves_buffer_mapping:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
  shows "frame_perm bp (ch_from ch) f = PermRW \<and> frame_perm bp (ch_to ch) f = PermR"
  using buffer_perm_asymmetric[OF wf ch f] .

section \<open>Examples\<close>

subsection \<open>A send/recv-ack round trip on the example channel\<close>

(* The runtime status map for the example two-core system (AMP_Model.thy),
   with its one declared channel chan01 initially idle. *)
definition example_xchan0 :: xchan_map where
  "example_xchan0 = [chan01 \<mapsto> XIdle]"

(* Non-vacuity: example_xchan0's domain matches example2's declared channels,
   so it is a legitimate initial runtime status map for the example system. *)
lemma example_xchan0_dom_wf: "xchan_dom_wf example2 example_xchan0"
  by (simp add: xchan_dom_wf_def example_xchan0_def example2_def)

(* Concrete send: writing into chan01's one buffer frame (0x8000) and nothing
   else is a valid xchan_send from example_xchan0, and — by C1 — it cannot
   touch core 1's private frames. This is the exit-test scenario: core 0
   sends a cross-core message and core 1's private memory is provably
   unaffected. *)
lemma example_xchan_send_isolates_core1:
  assumes m: "changed_frames m m' \<subseteq> {0x8000}"
  shows "changed_frames m m' \<inter> cr_frames core1_res = {}"
proof -
  have send: "xchan_send chan01 m m' example_xchan0 (example_xchan0(chan01 \<mapsto> XSendPending))"
    using m by (simp add: xchan_send_def example_xchan0_def chan01_def)
  have ch: "chan01 \<in> ap_channels example2" by (simp add: example2_def)
  have step: "amp_step 0 m m' example2"
    using xchan_send_is_amp_step[OF ch send] by (simp add: chan01_def)
  show ?thesis
    using amp_step_preserves_other_private[OF example2_partition_wf step,
                                           where c' = 1 and r' = core1_res]
    by (simp add: example2_def)
qed

(* Concrete recv_ack: once core 1 has consumed the message and the channel is
   released back to idle, the buffer's asymmetric mapping (core 0 read-write,
   core 1 read-only) still holds exactly as it did before the send — the
   round trip has left the permission map untouched. *)
lemma example_xchan_recv_ack_mapping_unchanged:
  assumes rc: "xchan_recv_ack chan01 (example_xchan0(chan01 \<mapsto> XSendPending)) example_xchan0"
  shows "frame_perm example2 0 0x8000 = PermRW \<and> frame_perm example2 1 0x8000 = PermR"
  using xchan_protocol_preserves_buffer_mapping[OF example2_partition_wf, where ch = chan01 and f = "0x8000"]
  by (simp add: example2_def chan01_def)

end
