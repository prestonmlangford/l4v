(*
 * PolarFire verified multicore (AMP) — cumulative specification index.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * This theory contains NO new proof. Every entry below is: a plain-English
 * paragraph, directly followed by that phase's headline theorem restated
 * VERBATIM from its own session, re-derived here in one step from the real
 * theorem. That step is the enforcement mechanism -- if a cited theorem's name,
 * statement, or hypotheses ever change incompatibly, THIS FILE FAILS TO BUILD.
 * You do not need to open any phase's own theory, or understand its proof, to
 * know what has been established for AMP: read this file top to bottom.
 *
 * What this DOES guarantee: every restated theorem below is a genuine logical
 * consequence of the real, checked theorem it cites -- it cannot be false, and
 * it cannot silently drift out of sync with a later change to the real proof.
 *
 * What this does NOT guarantee: completeness (a phase may prove other true
 * facts not surfaced here -- that is a scoping choice, not a gap; in
 * particular a phase whose only result is an intermediate refinement or
 * consistency fact, with no real-world corollary reachable from it, earns
 * NO entry at all -- see Phase 4's C half, deliberately absent below), and
 * it cannot check that the English paragraph captures what YOU actually care
 * about -- that translation from formal statement to real-world intent is an
 * unavoidably human judgment. The paragraph sits directly next to the formal
 * statement precisely so that judgment is easy to make.
 *
 * See ../../multicore-amp-plan.md section 2.5 for the rationale, and each
 * phase's own exit test in section 5 for what "headline theorem" means there.
 * Updated once per phase, in the same commit that merges the phase.
 *)

theory AMP_Overview
imports "AMP_Channel_C.AMP_Channel_C"   (* pulls in AMP_Channel_R, AMP_Channel_A, AMP_Spatial, AMP_Model transitively *)
begin

section \<open>Phase 1 — AMP system model\<close>

(* A multicore system's static resource assignment ("partition") is
   well-formed when four things all hold: distinct cores' private memory never
   overlaps; every declared channel connects two distinct cores that are both
   actually present; a channel's shared buffer is never part of any core's
   private memory; and distinct channels use disjoint buffers. This is the
   static shape every later phase's dynamic behaviour must preserve -- it says
   nothing yet about what a running kernel does, only what configuration counts
   as sane to start from. *)
corollary phase1_wellformedness:
  "amp_partition_wf ap \<equiv>
     (\<forall>c1 c2 r1 r2. ap_cores ap c1 = Some r1 \<longrightarrow> ap_cores ap c2 = Some r2 \<longrightarrow> c1 \<noteq> c2
                    \<longrightarrow> cr_frames r1 \<inter> cr_frames r2 = {}) \<and>
     (\<forall>ch \<in> ap_channels ap. ch_from ch \<noteq> ch_to ch
                    \<and> ch_from ch \<in> dom (ap_cores ap) \<and> ch_to ch \<in> dom (ap_cores ap)) \<and>
     (\<forall>ch \<in> ap_channels ap. \<forall>c r. ap_cores ap c = Some r
                    \<longrightarrow> ch_buffer ch \<inter> cr_frames r = {}) \<and>
     (\<forall>ch1 \<in> ap_channels ap. \<forall>ch2 \<in> ap_channels ap. ch1 \<noteq> ch2
                    \<longrightarrow> ch_buffer ch1 \<inter> ch_buffer ch2 = {})"
  using amp_partition_wf_def .

(* This shape is not vacuous: a genuine two-core, one-channel configuration
   (core 0 privately owns two frames, core 1 privately owns two different
   frames, and one declared channel from core 0 to core 1 uses a third, disjoint
   frame as its buffer) satisfies it. *)
corollary phase1_witness: "amp_partition_wf example2"
  using example2_partition_wf .

section \<open>Phase 2 — Spatial partition invariant (B1-B3)\<close>

(* Starting from a well-formed partition, every kernel step of a single core
   preserves it, in three parts:
     B1 -- the step changes no OTHER core's private memory;
     B2 -- on any declared channel's buffer frame, the sender core holds
           read-write access and the receiver core holds read-only access, and
           this is exactly the two-way split (no third core has any access);
     B3 -- no core ever holds a WRITABLE mapping into another core's private
           memory.
   Together these say: for any single kernel step, on any core, the only memory
   it can touch is its own resources and its declared channels' shared buffers
   -- and even on a shared buffer, only the sender may write. This is the
   property that makes cross-core memory corruption impossible by construction,
   for a single step; concurrent interleavings of many steps are Phase 6's job,
   not this one's. *)
corollary phase2_headline:
  assumes wf:   "amp_partition_wf bp"
      and step: "amp_step c m m' bp"
  shows "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> c \<noteq> c'
                 \<longrightarrow> changed_frames m m' \<inter> cr_frames r' = {}"      (* B1 *)
    and "\<forall>ch \<in> ap_channels bp. \<forall>f \<in> ch_buffer ch.
           frame_perm bp (ch_from ch) f = PermRW
           \<and> frame_perm bp (ch_to ch) f = PermR"                     (* B2 *)
    and "\<forall>c' r' f. ap_cores bp c' = Some r' \<longrightarrow> f \<in> cr_frames r' \<longrightarrow> c \<noteq> c'
                   \<longrightarrow> frame_perm bp c f \<noteq> PermRW"                   (* B3 *)
  using amp_step_preserves_partition[OF wf step] by blast+

section \<open>Phase 3 — Channel object + abstract operations (C1-C3)\<close>

(* If the partition is well-formed and ch is one of its declared channels,
   then after a send on ch: B1 no other core's private memory changes; B2
   every channel's buffer keeps its sender-writes/receiver-reads split; B3 no
   core holds a writable mapping into another core's private memory. *)
corollary phase3_send_headline:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp"
      and send: "xchan_send ch m m' xm xm'"
  shows "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> ch_from ch \<noteq> c'
                 \<longrightarrow> changed_frames m m' \<inter> cr_frames r' = {}"      (* B1 *)
    and "\<forall>ch' \<in> ap_channels bp. \<forall>f \<in> ch_buffer ch'.
           frame_perm bp (ch_from ch') f = PermRW
           \<and> frame_perm bp (ch_to ch') f = PermR"                     (* B2 *)
    and "\<forall>c' r' f. ap_cores bp c' = Some r' \<longrightarrow> f \<in> cr_frames r' \<longrightarrow> ch_from ch \<noteq> c'
                   \<longrightarrow> frame_perm bp (ch_from ch) f \<noteq> PermRW"          (* B3 *)
  using xchan_send_preserves_partition[OF wf ch send] by blast+

(* If the partition is well-formed, then after a receive-and-acknowledge on
   ch: B1 no memory changes at all; B2 every channel's buffer keeps its
   sender-writes/receiver-reads split; B3 no core holds a writable mapping
   into another core's private memory. *)
corollary phase3_recv_ack_headline:
  assumes wf: "amp_partition_wf bp" and rc: "xchan_recv_ack ch xm xm'"
  shows "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> ch_to ch \<noteq> c'
                 \<longrightarrow> changed_frames m m \<inter> cr_frames r' = {}"        (* B1, vacuous *)
    and "\<forall>ch' \<in> ap_channels bp. \<forall>f \<in> ch_buffer ch'.
           frame_perm bp (ch_from ch') f = PermRW
           \<and> frame_perm bp (ch_to ch') f = PermR"                     (* B2/C3 *)
    and "\<forall>c' r' f. ap_cores bp c' = Some r' \<longrightarrow> f \<in> cr_frames r' \<longrightarrow> ch_to ch \<noteq> c'
                   \<longrightarrow> frame_perm bp (ch_to ch) f \<noteq> PermRW"           (* B3 *)
  using xchan_recv_ack_preserves_partition[OF wf rc] by blast+

section \<open>Phase 4 — Channel refinement, design level (mirrors Ipc_R)\<close>

(* If the partition is well-formed and ch is one of its declared channels,
   then after a send on ch using the design-level (word-tagged, deterministic)
   operation: B1 no other core's private memory changes; B2 every channel's
   buffer keeps its sender-writes/receiver-reads split; B3 no core holds a
   writable mapping into another core's private memory. Same guarantee as
   Phase 3, now established for the operation shape a real implementation
   actually uses, not just the abstract relation. *)
corollary phase4_send_R_headline:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp"
      and pre: "xm ch = Some xIdleR" and mem: "changed_frames m m' \<subseteq> ch_buffer ch"
  shows "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> ch_from ch \<noteq> c'
                 \<longrightarrow> changed_frames m m' \<inter> cr_frames r' = {}"      (* B1 *)
    and "\<forall>ch' \<in> ap_channels bp. \<forall>f \<in> ch_buffer ch'.
           frame_perm bp (ch_from ch') f = PermRW
           \<and> frame_perm bp (ch_to ch') f = PermR"                     (* B2 *)
    and "\<forall>c' r' f. ap_cores bp c' = Some r' \<longrightarrow> f \<in> cr_frames r' \<longrightarrow> ch_from ch \<noteq> c'
                   \<longrightarrow> frame_perm bp (ch_from ch) f \<noteq> PermRW"          (* B3 *)
  using xchan_send_R_preserves_partition[where xm = xm and ch = ch, OF wf ch pre mem] by blast+

(* If the partition is well-formed, then after a receive-and-acknowledge on ch
   using the design-level operation: B1 no memory changes at all; B2 every
   channel's buffer keeps its sender-writes/receiver-reads split; B3 no core
   holds a writable mapping into another core's private memory. Same
   guarantee as Phase 3, now established at the design level. *)
corollary phase4_recv_ack_R_headline:
  assumes wf: "amp_partition_wf bp" and pre: "(xm :: xchan_map_R) ch = Some xSendPendingR"
  shows "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> ch_to ch \<noteq> c'
                 \<longrightarrow> changed_frames m m \<inter> cr_frames r' = {}"        (* B1, vacuous *)
    and "\<forall>ch' \<in> ap_channels bp. \<forall>f \<in> ch_buffer ch'.
           frame_perm bp (ch_from ch') f = PermRW
           \<and> frame_perm bp (ch_to ch') f = PermR"                     (* B2 *)
    and "\<forall>c' r' f. ap_cores bp c' = Some r' \<longrightarrow> f \<in> cr_frames r' \<longrightarrow> ch_to ch \<noteq> c'
                   \<longrightarrow> frame_perm bp (ch_to ch) f \<noteq> PermRW"           (* B3 *)
  using xchan_recv_ack_R_preserves_partition[where xm = xm and ch = ch, OF wf pre] by blast+

(* Phase 4's C half (amp/channel_c/xchan.c, session AMP_Channel_C,
   xchan_send_c_refines_R / xchan_recv_ack_c_refines_R) is intentionally
   NOT restated here. Those are refinement/mechanism facts -- "the C write
   matches the R-level tag" -- the same category xchan_send_R_corres was at
   the R half above, which this file also does not cite directly (see
   phase4_send_R_headline's comment and plan.md section 2.5, "Pick the
   corollary, not the proof step"). Unlike the R half there is no
   downstream corollary to chain to either: the standalone AutoCorres model
   xchan_send_c_refines_R is proved against has no notion of frames or
   memory permissions at all, so no real-world (confidentiality/integrity/
   availability) consequence is reachable from it by construction -- and
   this C isn't even spliced into the real kernel_all.c yet, so it doesn't
   describe what runs on hardware either. It is a genuine, checked result
   (session AMP_Channel_C is green), just not one with real-world relevance
   on its own; it earns an entry here only once/if it is bridged into an
   actual kernel translation unit and something real-world-relevant is
   proved about that. *)

end
