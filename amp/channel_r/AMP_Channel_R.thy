(*
 * PolarFire verified multicore (AMP) — Phase 4: channel refinement, design
 * level (the "R" half — mirrors Ipc_R).
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * Phase 3 gave the channel ATOMIC ABSTRACT semantics (xchan_send,
 * xchan_recv_ack) as relations over a symbolic two-valued status
 * (xchan_status). This theory adds a DESIGN-LEVEL ("R", refinement)
 * counterpart closer to what an implementation actually stores and runs:
 * status is a machine word (0 = idle, nonzero = send-pending), and each op is
 * a total DETERMINISTIC function rather than a relation, the same shift the
 * real spec makes going from `Structures_A`'s `endpoint` datatype and
 * `send_ipc`'s nondeterministic monad to `Structures_H`'s word-tagged state
 * and `sendIPC`'s deterministic Haskell function (spec/haskell/src/SEL4/
 * Object/Endpoint.lhs). The headline results are REFINEMENT theorems
 * (`xchan_send_R_corres`, `xchan_recv_ack_R_corres`): every design-level step
 * that respects its precondition is shown, via an abstraction map
 * `xchan_map_abs`, to correspond to a genuine Phase 3 abstract step — the
 * same `corres`-shaped claim `sendIPC_corres`/`receiveIPC_corres` make in
 * `l4v/proof/refine/Ipc_R.thy`, just for this much smaller state. Chaining
 * corres with Phase 3's C1/C2 then gives the spatial partition guarantee at
 * the design level for free, with no fresh spatial argument. See
 * ../../multicore-amp-plan.md section 5 (Phase 4).
 *
 * SCOPE. This is deliberately a small VERTICAL SLICE, not a full mirror of
 * Ipc_R (4385 lines) or Ipc_C (6578 lines):
 *   - The channel moves a fixed-size buffer, never capabilities, so it needs
 *     none of Ipc_R's ~40-lemma capability-transfer machinery
 *     (transferCapsToSlots_corres and friends) — that bulk of Ipc_R simply
 *     does not apply here.
 *   - Message/buffer CONTENTS remain unmodelled, exactly as Phases 2–3 left
 *     them — this theory is about the STATUS state machine and its
 *     refinement, not about byte-level buffer semantics.
 *   - The C level (mirroring Ipc_C, session `AMP_Channel_C`) is intentionally
 *     NOT attempted here; it is a separate, later, independently-greenable
 *     session per plan section 3 ("one phase, one (or few) new sessions").
 *
 * This theory is organized in the usual four zones (plan section 2.5):
 * SPECIFICATION, PROOF DEVELOPMENT, RESULTS (the corres theorems and their
 * partition-preservation corollaries), EXAMPLES.
 *)

theory AMP_Channel_R
imports "AMP_Channel_A.AMP_Channel_A"
begin

section \<open>Specification\<close>

subsection \<open>Channel runtime status, at the design level\<close>

(* The design-level encoding of a channel's runtime status: a single machine
   word, exactly the shape a real status field would take in kernel state
   (the same type as obj_ref itself — see Machine_A.thy). Unlike Phase 3's
   xchan_status datatype (a genuine two-constructor sum type), this is an
   untyped tag whose MEANING is fixed only by convention (xIdleR/xSendPendingR
   below) — mirroring how Structures_H represents kernel-object state as
   concrete words/records rather than the richer algebraic types the abstract
   spec is free to use. *)
type_synonym xchan_status_R = machine_word

(* The idle tag: no message pending. Chosen as 0, the natural "false"/default
   word value, matching how boolean-ish status flags are conventionally
   encoded at the design/C level. *)
definition xIdleR :: xchan_status_R where
  "xIdleR = 0"

(* The send-pending tag: a message has been written and not yet consumed. Any
   value other than xIdleR is treated as send-pending by the abstraction map
   below, but 1 is the canonical witness used throughout this theory. *)
definition xSendPendingR :: xchan_status_R where
  "xSendPendingR = 1"

subsection \<open>The design-level runtime status map\<close>

(* The design-level counterpart of Phase 3's xchan_map: the runtime status of
   every declared channel, now word-tagged rather than datatype-tagged. Same
   domain discipline as Phase 3 (keyed by the channel value itself). *)
type_synonym xchan_map_R = "amp_channel \<rightharpoonup> xchan_status_R"

subsection \<open>Abstraction relation: design state maps down to abstract state\<close>

(* xchan_status_abs: the abstraction function a refinement proof needs to
   relate a concrete (design-level) value to the abstract value it represents.
   Total and simple by construction: 0 reads as XIdle, anything else reads as
   XSendPending — so every design-level word has SOME abstract meaning, even
   ones a well-behaved kernel would never actually produce. This mirrors how a
   real corres state relation is usually total on the concrete side (it must
   classify whatever the concrete state machine can reach), with well-formedness
   of what values actually occur established separately if needed (not needed
   here — send_R only ever writes xSendPendingR, recv_ack_R only ever writes
   xIdleR, so exactly {xIdleR, xSendPendingR} are reachable in practice). *)
definition xchan_status_abs :: "xchan_status_R \<Rightarrow> xchan_status" where
  "xchan_status_abs v \<equiv> if v = xIdleR then XIdle else XSendPending"

(* xchan_map_abs: lifts xchan_status_abs pointwise over the whole runtime
   status map, preserving Nones (an untracked channel design-side is untracked
   abstract-side too). This is the state relation every corres theorem below
   is phrased in terms of: two states (one xchan_map_R, one xchan_map)
   correspond exactly when the abstract one equals xchan_map_abs of the
   concrete one. *)
definition xchan_map_abs :: "xchan_map_R \<Rightarrow> xchan_map" where
  "xchan_map_abs xm \<equiv> \<lambda>ch. map_option xchan_status_abs (xm ch)"

subsection \<open>Design-level channel operations\<close>

(* xchan_send_R: the design-level send, a TOTAL deterministic function (not a
   relation) that writes the send-pending tag. Unlike Phase 3's xchan_send,
   this definition itself does not check the idle precondition — exactly as
   the real sendIPC (Endpoint.lhs) does not re-derive that its caller already
   established the relevant guard; the precondition is instead an EXPLICIT
   hypothesis of the refinement theorem below, the same division of labour
   `sendIPC_corres` uses against `send_ipc`'s guard in Ipc_R.thy. Buffer
   CONTENTS are, as throughout this project, left unmodelled — this operation
   is about the status transition only. *)
definition xchan_send_R :: "amp_channel \<Rightarrow> xchan_map_R \<Rightarrow> xchan_map_R" where
  "xchan_send_R ch xm \<equiv> xm(ch \<mapsto> xSendPendingR)"

(* xchan_recv_ack_R: the design-level recv/ack, symmetric to xchan_send_R —
   writes the idle tag back, with the send-pending precondition again left to
   the refinement theorem rather than checked here. *)
definition xchan_recv_ack_R :: "amp_channel \<Rightarrow> xchan_map_R \<Rightarrow> xchan_map_R" where
  "xchan_recv_ack_R ch xm \<equiv> xm(ch \<mapsto> xIdleR)"

section \<open>Proof development (internal machinery)\<close>

(* The one fact every corres proof below reduces to: abstracting a map after a
   function update is the same as abstracting first and then updating with the
   abstracted value. Routine, but stated once here rather than re-derived
   inline in every theorem that needs it. *)
lemma xchan_map_abs_upd:
  "xchan_map_abs (xm(ch \<mapsto> v)) = (xchan_map_abs xm)(ch \<mapsto> xchan_status_abs v)"
  by (auto simp: xchan_map_abs_def)

section \<open>Results\<close>

subsection \<open>C1 continued — design-level send refines the abstract send\<close>

(* xchan_send_R_corres: the refinement headline for send. Whenever the
   design-level map has ch tagged idle (the real precondition a caller must
   have established — mirrors send_ipc's guard) and the memory write is
   confined to ch's buffer (the same containment Phase 3's xchan_send
   requires), running xchan_send_R and viewing BOTH the before- and
   after-states through xchan_map_abs produces exactly a valid Phase 3
   xchan_send step. This is the corres-shaped claim: every design-level send
   is a genuine abstract send, once translated through the state relation. *)
theorem xchan_send_R_corres:
  assumes pre: "xm ch = Some xIdleR"
      and mem: "changed_frames m m' \<subseteq> ch_buffer ch"
  shows "xchan_send ch m m' (xchan_map_abs xm) (xchan_map_abs (xchan_send_R ch xm))"
proof -
  have idle: "xchan_map_abs xm ch = Some XIdle"
    using pre by (simp add: xchan_map_abs_def xchan_status_abs_def)
  have upd: "xchan_map_abs (xchan_send_R ch xm) = (xchan_map_abs xm)(ch \<mapsto> XSendPending)"
    by (simp add: xchan_send_R_def xchan_map_abs_upd xchan_status_abs_def xIdleR_def xSendPendingR_def)
  from idle upd mem show ?thesis by (simp add: xchan_send_def)
qed

subsection \<open>C2 continued — design-level recv/ack refines the abstract recv/ack\<close>

(* xchan_recv_ack_R_corres: the symmetric refinement headline for recv/ack.
   Whenever the design-level map has ch tagged send-pending, running
   xchan_recv_ack_R and translating through xchan_map_abs produces exactly a
   valid Phase 3 xchan_recv_ack step. *)
theorem xchan_recv_ack_R_corres:
  assumes pre: "xm ch = Some xSendPendingR"
  shows "xchan_recv_ack ch (xchan_map_abs xm) (xchan_map_abs (xchan_recv_ack_R ch xm))"
proof -
  have pending: "xchan_map_abs xm ch = Some XSendPending"
    using pre by (simp add: xchan_map_abs_def xchan_status_abs_def xIdleR_def xSendPendingR_def)
  have upd: "xchan_map_abs (xchan_recv_ack_R ch xm) = (xchan_map_abs xm)(ch \<mapsto> XIdle)"
    by (simp add: xchan_recv_ack_R_def xchan_map_abs_upd xchan_status_abs_def)
  from pending upd show ?thesis by (simp add: xchan_recv_ack_def)
qed

subsection \<open>The design level inherits the spatial partition guarantee for free\<close>

(* xchan_send_R_preserves_partition: chaining xchan_send_R_corres with Phase
   3's C1 (xchan_send_preserves_partition) gives B1–B3 at the design level
   with no new spatial reasoning at all — exactly the payoff refinement is
   for: prove the spatial argument once, abstractly, and every lower level
   that correctly refines it inherits the guarantee automatically. *)
corollary xchan_send_R_preserves_partition:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp"
      and pre: "xm ch = Some xIdleR" and mem: "changed_frames m m' \<subseteq> ch_buffer ch"
  shows "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> ch_from ch \<noteq> c'
                 \<longrightarrow> changed_frames m m' \<inter> cr_frames r' = {}"      (* B1 *)
    and "\<forall>ch' \<in> ap_channels bp. \<forall>f \<in> ch_buffer ch'.
           frame_perm bp (ch_from ch') f = PermRW
           \<and> frame_perm bp (ch_to ch') f = PermR"                     (* B2 *)
    and "\<forall>c' r' f. ap_cores bp c' = Some r' \<longrightarrow> f \<in> cr_frames r' \<longrightarrow> ch_from ch \<noteq> c'
                   \<longrightarrow> frame_perm bp (ch_from ch) f \<noteq> PermRW"          (* B3 *)
proof -
  have corres: "xchan_send ch m m' (xchan_map_abs xm) (xchan_map_abs (xchan_send_R ch xm))"
    using xchan_send_R_corres[where xm = xm and ch = ch, OF pre mem] .
  show "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> ch_from ch \<noteq> c'
               \<longrightarrow> changed_frames m m' \<inter> cr_frames r' = {}"
       "\<forall>ch' \<in> ap_channels bp. \<forall>f \<in> ch_buffer ch'.
          frame_perm bp (ch_from ch') f = PermRW
          \<and> frame_perm bp (ch_to ch') f = PermR"
       "\<forall>c' r' f. ap_cores bp c' = Some r' \<longrightarrow> f \<in> cr_frames r' \<longrightarrow> ch_from ch \<noteq> c'
                  \<longrightarrow> frame_perm bp (ch_from ch) f \<noteq> PermRW"
    using xchan_send_preserves_partition[OF wf ch corres] by blast+
qed

(* xchan_recv_ack_R_preserves_partition: the symmetric corollary for recv/ack,
   chaining xchan_recv_ack_R_corres with Phase 3's C2. *)
corollary xchan_recv_ack_R_preserves_partition:
  assumes wf: "amp_partition_wf bp" and pre: "(xm :: xchan_map_R) ch = Some xSendPendingR"
  shows "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> ch_to ch \<noteq> c'
                 \<longrightarrow> changed_frames m m \<inter> cr_frames r' = {}"
    and "\<forall>ch' \<in> ap_channels bp. \<forall>f \<in> ch_buffer ch'.
           frame_perm bp (ch_from ch') f = PermRW \<and> frame_perm bp (ch_to ch') f = PermR"
    and "\<forall>c' r' f. ap_cores bp c' = Some r' \<longrightarrow> f \<in> cr_frames r' \<longrightarrow> ch_to ch \<noteq> c'
                   \<longrightarrow> frame_perm bp (ch_to ch) f \<noteq> PermRW"
proof -
  have corres: "xchan_recv_ack ch (xchan_map_abs xm) (xchan_map_abs (xchan_recv_ack_R ch xm))"
    using xchan_recv_ack_R_corres[where xm = xm and ch = ch, OF pre] .
  show "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> ch_to ch \<noteq> c'
               \<longrightarrow> changed_frames m m \<inter> cr_frames r' = {}"
       "\<forall>ch' \<in> ap_channels bp. \<forall>f \<in> ch_buffer ch'.
          frame_perm bp (ch_from ch') f = PermRW \<and> frame_perm bp (ch_to ch') f = PermR"
       "\<forall>c' r' f. ap_cores bp c' = Some r' \<longrightarrow> f \<in> cr_frames r' \<longrightarrow> ch_to ch \<noteq> c'
                  \<longrightarrow> frame_perm bp (ch_to ch) f \<noteq> PermRW"
    using xchan_recv_ack_preserves_partition[OF wf corres] by blast+
qed

section \<open>Examples\<close>

subsection \<open>The example channel's design-level state, and one round trip\<close>

(* The design-level counterpart of Phase 3's example_xchan0: the same example
   channel (chan01, from AMP_Model.thy), initially idle, now word-tagged. *)
definition example_xchan0_R :: xchan_map_R where
  "example_xchan0_R = [chan01 \<mapsto> xIdleR]"

(* Non-vacuity / sanity: the design-level example state abstracts to exactly
   Phase 3's abstract example state, so the two examples genuinely describe
   the same starting point at different levels. *)
lemma example_xchan0_R_abs: "xchan_map_abs example_xchan0_R = example_xchan0"
  by (auto simp: xchan_map_abs_def example_xchan0_R_def example_xchan0_def xchan_status_abs_def xIdleR_def)

(* Concrete instance of C1 continued: sending on the example channel at the
   design level, writing only its one buffer frame, still cannot touch core
   1's private memory — the same exit-test scenario as Phase 3's
   example_xchan_send_isolates_core1, now witnessed one level down. *)
lemma example_xchan_send_R_isolates_core1:
  assumes m: "changed_frames m m' \<subseteq> {0x8000}"
  shows "changed_frames m m' \<inter> cr_frames core1_res = {}"
proof -
  have pre: "example_xchan0_R chan01 = Some xIdleR" by (simp add: example_xchan0_R_def)
  have mem: "changed_frames m m' \<subseteq> ch_buffer chan01" using m by (simp add: chan01_def)
  have corres0: "xchan_send chan01 m m' (xchan_map_abs example_xchan0_R) (xchan_map_abs (xchan_send_R chan01 example_xchan0_R))"
    using xchan_send_R_corres[where xm = example_xchan0_R and ch = chan01, OF pre mem] .
  have corres: "xchan_send chan01 m m' example_xchan0 (xchan_map_abs (xchan_send_R chan01 example_xchan0_R))"
    using corres0 by (simp add: example_xchan0_R_abs)
  have ch: "chan01 \<in> ap_channels example2" by (simp add: example2_def)
  have step: "amp_step 0 m m' example2"
    using xchan_send_is_amp_step[OF ch corres] by (simp add: chan01_def)
  show ?thesis
    using amp_step_preserves_other_private[OF example2_partition_wf step,
                                           where c' = 1 and r' = core1_res]
    by (simp add: example2_def)
qed

(* Concrete instance of C2 continued: once the design-level state has been
   moved to send-pending and recv_ack_R is run, the result abstracts back to
   exactly example_xchan0 — the round trip returns to idle at the design
   level exactly as it does abstractly (Phase 3's
   example_xchan_recv_ack_mapping_unchanged), witnessed via the corres
   theorem rather than recomputed independently. *)
lemma example_xchan_recv_ack_R_returns_to_idle:
  "xchan_map_abs (xchan_recv_ack_R chan01 (example_xchan0_R(chan01 \<mapsto> xSendPendingR))) = example_xchan0"
proof -
  have pre: "(example_xchan0_R(chan01 \<mapsto> xSendPendingR)) chan01 = Some xSendPendingR" by simp
  have corres: "xchan_recv_ack chan01
                  (xchan_map_abs (example_xchan0_R(chan01 \<mapsto> xSendPendingR)))
                  (xchan_map_abs (xchan_recv_ack_R chan01 (example_xchan0_R(chan01 \<mapsto> xSendPendingR))))"
    using xchan_recv_ack_R_corres[where xm = "example_xchan0_R(chan01 \<mapsto> xSendPendingR)" and ch = chan01, OF pre] .
  moreover have "xchan_map_abs (example_xchan0_R(chan01 \<mapsto> xSendPendingR)) = example_xchan0(chan01 \<mapsto> XSendPending)"
    by (simp add: xchan_map_abs_upd example_xchan0_R_abs xchan_status_abs_def xIdleR_def xSendPendingR_def)
  ultimately show ?thesis
    by (simp add: xchan_recv_ack_def example_xchan0_def)
qed

end
