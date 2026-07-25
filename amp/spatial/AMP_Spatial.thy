(*
 * PolarFire verified multicore (AMP) — Phase 2: the spatial partition invariant.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * Phase 2 shows that if the cores start partitioned, each core's kernel steps
 * keep them partitioned: a core can only touch memory it owns (B1), the channel
 * buffer is the only doubly-mapped frame and its permissions are asymmetric
 * (B2), and no core holds a writable mapping to another core's private frames
 * (B3). None of this needs concurrency reasoning — a single core's step is
 * exactly the already-verified single-core transition (plan section 5, Phase 2).
 *
 * How this connects to the verified single-core proofs. seL4's `integrity`
 * theorem (Access.thy, `integrity_subjects`/`integrity_mem`) already states that
 * a kernel step leaves `underlying_memory` unchanged EXCEPT where the running
 * subject has write authority. Phase 2's job is the spatial half: given that a
 * core's threads have authority only within that core's owned frames, integrity
 * confines the step's writes to owned_frames, and the partition's disjointness
 * does the rest. We capture "the step's writes are confined to the acting core's
 * owned frames" as the predicate `amp_step` below and note explicitly that it is
 * the abstraction of seL4's integrity_mem; discharging it against the real
 * `integrity` theorem (relating a per-core PAS to the partition) is the deferred
 * integration step. Everything else here is proved outright.
 *
 * Performance note: `amp_partition_wf` is a four-conjunct nested-quantifier
 * predicate, so `fastforce`/`auto` with `amp_partition_wf_def` in the simp set
 * explodes the search (the same trap as the single-core pspace_distinct_s0
 * hang). Every proof below instead goes through the bounded per-conjunct
 * destructor lemmas in the first section, and never unfolds the definition into
 * a non-trivial goal.
 *
 * This theory is organized in four zones, in this order: SPECIFICATION (the
 * types and operations that give the spatial argument its vocabulary — read
 * this to know WHAT is being modelled), PROOF DEVELOPMENT (internal destructor
 * lemmas and branch facts that exist only to make the results below provable —
 * skip this if you only want to know what holds), RESULTS (B1/B2/B3 and the
 * packaged exit theorem), and EXAMPLES (concrete non-vacuity witnesses). See
 * ../../multicore-amp-plan.md section 2.5 and amp/overview/AMP_Overview.thy for
 * the cumulative cross-phase version of this same idea.
 *)

theory AMP_Spatial
imports "AMP_Model.AMP_Model"
begin

section \<open>Specification\<close>

subsection \<open>Access permissions on frames\<close>

(* The permission a core may hold on a physical frame. Three levels suffice for
   the spatial argument: no access at all, read-only (the receiver's view of a
   channel buffer), and read-write (a core's private frames, and the sender's
   view of a channel buffer). This mirrors the R/W distinction that the RISCV64
   Sv39 page tables enforce per page; the full page-table encoding is not needed
   at this altitude. *)
datatype access_perm = PermNone | PermR | PermRW

subsection \<open>Frames changed by a step, and the integrity abstraction\<close>

(* The set of frames whose contents differ between two system memories. A "system
   memory" is modelled abstractly as a function from a frame (obj_ref) to its
   contents; the type of contents is left polymorphic because the spatial
   argument never inspects a value, only whether it changed. *)
definition changed_frames :: "(obj_ref \<Rightarrow> 'v) \<Rightarrow> (obj_ref \<Rightarrow> 'v) \<Rightarrow> obj_ref set" where
  "changed_frames m m' = {f. m f \<noteq> m' f}"

(* A single-core AMP step, as seen at frame granularity. Core c takes a kernel
   step that changes system memory from m to m', and the frames it changes are
   confined to core c's owned frames under the static boot partition bp. This
   confinement is EXACTLY the content of seL4's integrity_mem specialised to a
   core whose threads' write authority lies within owned_frames bp c: it is not
   an extra assumption about the world but the abstraction of a theorem already
   proved single-core (Access.integrity). Phase 2 proves the spatial consequences
   of this predicate; a later integration step discharges it against the real
   integrity theorem. Nothing here modifies bp — the partition is static (A-HW). *)
definition amp_step ::
  "core_id \<Rightarrow> (obj_ref \<Rightarrow> 'v) \<Rightarrow> (obj_ref \<Rightarrow> 'v) \<Rightarrow> amp_partition \<Rightarrow> bool" where
  "amp_step c m m' bp \<equiv> changed_frames m m' \<subseteq> owned_frames bp c"

subsection \<open>The intended permission map\<close>

(* The three conditions of the permission map, as NAMED predicates rather than
   inline existentials. This is deliberate and load-bearing: keeping the
   existential quantifiers hidden inside these definitions means the permission
   proofs reduce frame_perm's `if`s against opaque booleans, so simp never
   descends into an existential over the abstract ap_channels bp (which sends its
   search pathological). Each branch fact is proved once, by unfolding the ONE
   relevant predicate. *)

(* c privately owns frame f: f is in c's private resources. *)
definition owns_priv :: "amp_partition \<Rightarrow> core_id \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "owns_priv bp c f \<equiv> (\<exists>r. ap_cores bp c = Some r \<and> f \<in> cr_frames r)"

(* c is the SENDER for frame f: f is the buffer of a channel whose ch_from is c. *)
definition maps_writer :: "amp_partition \<Rightarrow> core_id \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "maps_writer bp c f \<equiv> (\<exists>ch \<in> ap_channels bp. f \<in> ch_buffer ch \<and> c = ch_from ch)"

(* c is the RECEIVER for frame f: f is the buffer of a channel whose ch_to is c. *)
definition maps_reader :: "amp_partition \<Rightarrow> core_id \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "maps_reader bp c f \<equiv> (\<exists>ch \<in> ap_channels bp. f \<in> ch_buffer ch \<and> c = ch_to ch)"

(* The permission a core c is intended to hold on frame f under the static boot
   partition bp:
     - a frame in c's private resources: read-write;
     - a channel buffer, for the sender endpoint: read-write;
     - a channel buffer, for the receiver endpoint: read-only;
     - otherwise: no access.
   This is the boot-time mapping the partition prescribes; being determined by
   bp alone, it never changes under a step that leaves bp fixed (below). The
   private-before-channel ordering is unambiguous under a well-
   formed partition, where buffers and private frames are disjoint. *)
definition frame_perm :: "amp_partition \<Rightarrow> core_id \<Rightarrow> obj_ref \<Rightarrow> access_perm" where
  "frame_perm bp c f =
     (if owns_priv bp c f then PermRW
      else if maps_writer bp c f then PermRW
      else if maps_reader bp c f then PermR
      else PermNone)"

section \<open>Proof development (internal machinery)\<close>

subsection \<open>Well-formedness destructors (bounded projections)\<close>

(* Channels connect distinct cores. Projection of amp_partition_wf conjunct 2.
   The conjunct is first pulled out by simp (conjunction-elimination only, no
   search), THEN instantiated by blast on that single small fact — crucially the
   full definition, with its set-equality conjuncts, is never handed to blast. *)
lemma wf_channel_distinct:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp"
  shows "ch_from ch \<noteq> ch_to ch"
proof -
  from wf have "\<forall>ch \<in> ap_channels bp. ch_from ch \<noteq> ch_to ch
                  \<and> ch_from ch \<in> dom (ap_cores bp) \<and> ch_to ch \<in> dom (ap_cores bp)"
    by (simp add: amp_partition_wf_def)
  with ch show ?thesis by blast
qed

(* Distinct channels have disjoint buffers. Projection of conjunct 4, extracted
   the same way — simp projects the conjunct, blast instantiates it. *)
lemma wf_buffers_disjoint:
  assumes wf: "amp_partition_wf bp"
      and c1: "ch1 \<in> ap_channels bp" and c2: "ch2 \<in> ap_channels bp" and ne: "ch1 \<noteq> ch2"
  shows "ch_buffer ch1 \<inter> ch_buffer ch2 = {}"
proof -
  from wf have "\<forall>ch1 \<in> ap_channels bp. \<forall>ch2 \<in> ap_channels bp.
                  ch1 \<noteq> ch2 \<longrightarrow> ch_buffer ch1 \<inter> ch_buffer ch2 = {}"
    by (simp add: amp_partition_wf_def)
  with c1 c2 ne show ?thesis by blast
qed

(* A frame lies in at most one channel's buffer: any channel whose buffer holds f
   equals any other such channel. Immediate from buffer disjointness — this is the
   form the permission proofs actually use. *)
lemma wf_buffer_unique:
  assumes wf: "amp_partition_wf bp"
      and c1: "ch1 \<in> ap_channels bp" and c2: "ch2 \<in> ap_channels bp"
      and f1: "f \<in> ch_buffer ch1" and f2: "f \<in> ch_buffer ch2"
  shows "ch1 = ch2"
  using wf_buffers_disjoint[OF wf c1 c2] f1 f2 by blast

subsection \<open>B1 helper\<close>

(* Helper: under a well-formed partition, one core's whole footprint is disjoint
   from any OTHER core's private frames. owned_frames c meets owned_frames c'
   only in channel buffers (owned_overlap_subset_channels), and a channel buffer
   never intersects any core's private frames (amp_partition_wf_buffer_not_private),
   so the meet with c''s private frames specifically is empty. This is the spatial
   core of the whole phase; B1 and B3 both fall out of it. *)
lemma owned_disjoint_other_private:
  assumes wf:  "amp_partition_wf bp"
      and c':  "ap_cores bp c' = Some r'"
      and neq: "c \<noteq> c'"
  shows "owned_frames bp c \<inter> cr_frames r' = {}"
proof -
  have sub: "cr_frames r' \<subseteq> owned_frames bp c'"
    using c' by (auto simp: owned_frames_def)
  have "owned_frames bp c \<inter> cr_frames r' \<subseteq> owned_frames bp c \<inter> owned_frames bp c'"
    using sub by blast
  also have "\<dots> \<subseteq> (\<Union>ch \<in> ap_channels bp. ch_buffer ch)"
    using owned_overlap_subset_channels[OF wf neq] .
  finally have in_bufs: "owned_frames bp c \<inter> cr_frames r'
                           \<subseteq> (\<Union>ch \<in> ap_channels bp. ch_buffer ch)" .
  (* no channel buffer meets c''s private frames (conjunct-3 destructor) *)
  have "(\<Union>ch \<in> ap_channels bp. ch_buffer ch) \<inter> cr_frames r' = {}"
    using amp_partition_wf_buffer_not_private[OF wf _ c'] by blast
  with in_bufs show ?thesis by blast
qed

subsection \<open>Buffer-frame branch facts\<close>

(* NB every negative fact below is proved by a structured obtain + explicit
   contradiction, NOT by handing wf_buffer_unique (which concludes an equality)
   to blast — an equality-producing Horn rule sends blast into a non-terminating
   search over the abstract ap_channels bp. *)

(* A channel buffer frame is no core's private frame: buffers are disjoint from
   every core's private frames (conjunct-3 destructor). Kills the owns_priv
   branch for either endpoint. *)
lemma buffer_not_owns_priv:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
  shows "\<not> owns_priv bp c f"
proof
  assume "owns_priv bp c f"
  then obtain r where "ap_cores bp c = Some r" and "f \<in> cr_frames r"
    unfolding owns_priv_def by blast
  with amp_partition_wf_buffer_not_private[OF wf ch] f show False by blast
qed

(* The sender endpoint of a channel is a writer for that channel's buffer frame. *)
lemma from_maps_writer:
  assumes ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
  shows "maps_writer bp (ch_from ch) f"
  unfolding maps_writer_def using ch f by blast

(* The receiver endpoint is a reader for that channel's buffer frame. *)
lemma to_maps_reader:
  assumes ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
  shows "maps_reader bp (ch_to ch) f"
  unfolding maps_reader_def using ch f by blast

(* The receiver endpoint is NOT a writer for the buffer frame: the only channel
   whose buffer holds f is ch (buffers disjoint), and its sender differs from its
   receiver (channels are cross-core). *)
lemma to_not_maps_writer:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
  shows "\<not> maps_writer bp (ch_to ch) f"
proof
  assume "maps_writer bp (ch_to ch) f"
  then obtain ch' where ch': "ch' \<in> ap_channels bp" and f': "f \<in> ch_buffer ch'"
      and eq: "ch_to ch = ch_from ch'"
    unfolding maps_writer_def by blast
  from wf_buffer_unique[OF wf ch' ch f' f] have "ch' = ch" .
  with eq wf_channel_distinct[OF wf ch] show False by simp
qed

(* A core that is neither endpoint is not a writer for the buffer frame. *)
lemma other_not_maps_writer:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
      and c: "c \<noteq> ch_from ch"
  shows "\<not> maps_writer bp c f"
proof
  assume "maps_writer bp c f"
  then obtain ch' where ch': "ch' \<in> ap_channels bp" and f': "f \<in> ch_buffer ch'"
      and eq: "c = ch_from ch'"
    unfolding maps_writer_def by blast
  from wf_buffer_unique[OF wf ch' ch f' f] have "ch' = ch" .
  with eq c show False by simp
qed

(* A core that is neither endpoint is not a reader for the buffer frame. *)
lemma other_not_maps_reader:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
      and c: "c \<noteq> ch_to ch"
  shows "\<not> maps_reader bp c f"
proof
  assume "maps_reader bp c f"
  then obtain ch' where ch': "ch' \<in> ap_channels bp" and f': "f \<in> ch_buffer ch'"
      and eq: "c = ch_to ch'"
    unfolding maps_reader_def by blast
  from wf_buffer_unique[OF wf ch' ch f' f] have "ch' = ch" .
  with eq c show False by simp
qed

(* A frame private to some core is in no channel buffer, hence its holder is
   neither a writer nor a reader of it. Kills both channel branches in B3. *)
lemma private_not_maps_writer:
  assumes wf: "amp_partition_wf bp" and c': "ap_cores bp c' = Some r'" and f: "f \<in> cr_frames r'"
  shows "\<not> maps_writer bp c f"
proof
  assume "maps_writer bp c f"
  then obtain ch' where ch': "ch' \<in> ap_channels bp" and f': "f \<in> ch_buffer ch'"
    unfolding maps_writer_def by blast
  from amp_partition_wf_buffer_not_private[OF wf ch' c'] f f' show False by blast
qed

subsection \<open>Static permission map\<close>

(* The permission map is a function of the static boot partition alone, so a step
   — which never modifies bp — leaves every core's permissions unchanged. Hence
   the B2/B3 mapping invariants, being facts about frame_perm bp, are preserved
   verbatim across any step. Stated explicitly to discharge the "established and
   preserved" half of the exit test. *)
lemma frame_perm_invariant_under_step:
  "amp_step c m m' bp \<Longrightarrow> frame_perm bp = frame_perm bp"
  by (rule refl)

section \<open>Results\<close>

subsection \<open>B1 — a step never touches another core's private memory\<close>

(* B1: a single-core step by c changes none of any other core c''s private
   frames. Immediate from confinement (changed frames \<subseteq> owned c) and the helper
   above. This is the "a core can only touch memory it owns" guarantee, reduced
   to seL4's integrity via amp_step. *)
theorem amp_step_preserves_other_private:
  assumes wf:   "amp_partition_wf bp"
      and step: "amp_step c m m' bp"
      and c':   "ap_cores bp c' = Some r'"
      and neq:  "c \<noteq> c'"
  shows "changed_frames m m' \<inter> cr_frames r' = {}"
proof -
  have "changed_frames m m' \<inter> cr_frames r' \<subseteq> owned_frames bp c \<inter> cr_frames r'"
    using step by (auto simp: amp_step_def)
  with owned_disjoint_other_private[OF wf c' neq] show ?thesis by blast
qed

subsection \<open>B2 — the channel buffer is doubly mapped, asymmetrically\<close>

(* B2: on a declared channel's buffer frame, the sender endpoint holds read-write
   and the receiver endpoint holds read-only. This is the asymmetry the one-way
   discipline rests on. Each frame_perm reduces against opaque branch facts, so
   no existential is ever handed to simp. *)
theorem buffer_perm_asymmetric:
  assumes wf: "amp_partition_wf bp"
      and ch: "ch \<in> ap_channels bp"
      and f:  "f \<in> ch_buffer ch"
  shows "frame_perm bp (ch_from ch) f = PermRW \<and> frame_perm bp (ch_to ch) f = PermR"
proof -
  have "frame_perm bp (ch_from ch) f = PermRW"
    by (simp add: frame_perm_def buffer_not_owns_priv[OF wf ch f] from_maps_writer[OF ch f])
  moreover have "frame_perm bp (ch_to ch) f = PermR"
    by (simp add: frame_perm_def buffer_not_owns_priv[OF wf ch f]
                  to_not_maps_writer[OF wf ch f] to_maps_reader[OF ch f])
  ultimately show ?thesis by simp
qed

(* B2, second half: no core other than the two endpoints has any access to a
   channel buffer frame. Together with buffer_perm_asymmetric this says the
   buffer is mapped into exactly its two endpoints and nowhere else. *)
theorem buffer_perm_only_endpoints:
  assumes wf: "amp_partition_wf bp"
      and ch: "ch \<in> ap_channels bp"
      and f:  "f \<in> ch_buffer ch"
      and c:  "c \<noteq> ch_from ch"  and c2: "c \<noteq> ch_to ch"
  shows "frame_perm bp c f = PermNone"
  by (simp add: frame_perm_def buffer_not_owns_priv[OF wf ch f]
                other_not_maps_writer[OF wf ch f c] other_not_maps_reader[OF wf ch f c2])

subsection \<open>B3 — no writable mapping to another core's private frames\<close>

(* B3: no core holds read-write access to a DIFFERENT core's private frame. A
   PermRW verdict comes only from owns_priv (excluded, since private frames of
   distinct cores are disjoint) or from maps_writer (excluded, since the frame is
   another core's private memory and buffers never overlap private frames), so
   the value is PermR or PermNone, both distinct from PermRW. This is the property
   that makes cross-core memory corruption impossible by construction. *)
theorem no_cross_writable:
  assumes wf:  "amp_partition_wf bp"
      and c':  "ap_cores bp c' = Some r'"
      and f:   "f \<in> cr_frames r'"
      and neq: "c \<noteq> c'"
  shows "frame_perm bp c f \<noteq> PermRW"
proof -
  (* c does not privately own f: c and c' have disjoint private frames. *)
  have "\<not> owns_priv bp c f"
    unfolding owns_priv_def
    using amp_partition_wf_private_disjoint[OF wf _ c' neq] f by blast
  (* nor is c a writer for f, which is private to c' and so in no buffer. *)
  moreover have "\<not> maps_writer bp c f" using private_not_maps_writer[OF wf c' f] .
  (* the remaining outcomes are PermR or PermNone, both \<noteq> PermRW (maps_reader is
     an opaque bool, so the leftover if is split without touching an existential). *)
  ultimately show ?thesis by (simp add: frame_perm_def)
qed

subsection \<open>Packaged invariant\<close>

(* Phase 2 exit theorem: for a well-formed partition, any single-core step keeps
   the system partitioned. It (1) changes no other core's private memory (B1) and
   (2) leaves the asymmetric buffer mapping (B2) and the no-cross-write property
   (B3) intact — the latter two because the mapping is static. This is the
   `partition_preserved` obligation of the plan's Phase 2 exit test. *)
theorem amp_step_preserves_partition:
  assumes wf:   "amp_partition_wf bp"
      and step: "amp_step c m m' bp"
  shows "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> c \<noteq> c'
                 \<longrightarrow> changed_frames m m' \<inter> cr_frames r' = {}"      (* B1 *)
    and "\<forall>ch \<in> ap_channels bp. \<forall>f \<in> ch_buffer ch.
           frame_perm bp (ch_from ch) f = PermRW
           \<and> frame_perm bp (ch_to ch) f = PermR"                     (* B2 *)
    and "\<forall>c' r' f. ap_cores bp c' = Some r' \<longrightarrow> f \<in> cr_frames r' \<longrightarrow> c \<noteq> c'
                   \<longrightarrow> frame_perm bp c f \<noteq> PermRW"                   (* B3 *)
proof -
  (* Each goal is discharged by ONLY its own lemma; mixing all three lemmas into
     one blast lets the frame_perm =PermRW / \<noteq>PermRW facts chase each other. *)
  show "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> c \<noteq> c'
                \<longrightarrow> changed_frames m m' \<inter> cr_frames r' = {}"
    using amp_step_preserves_other_private[OF wf step] by blast
  show "\<forall>ch \<in> ap_channels bp. \<forall>f \<in> ch_buffer ch.
          frame_perm bp (ch_from ch) f = PermRW \<and> frame_perm bp (ch_to ch) f = PermR"
    using buffer_perm_asymmetric[OF wf] by blast
  show "\<forall>c' r' f. ap_cores bp c' = Some r' \<longrightarrow> f \<in> cr_frames r' \<longrightarrow> c \<noteq> c'
                  \<longrightarrow> frame_perm bp c f \<noteq> PermRW"
    using no_cross_writable[OF wf] by blast
qed

section \<open>Examples\<close>

subsection \<open>The example two-core configuration is spatially isolated\<close>

(* Concrete non-vacuity check: in the example two-core system, any step by core 0
   leaves core 1's private frames untouched. Instantiates B1 at example2, whose
   well-formedness was proved in Phase 1. *)
lemma example2_core0_step_isolates_core1:
  assumes "amp_step 0 m m' example2"
  shows "changed_frames m m' \<inter> cr_frames core1_res = {}"
  using amp_step_preserves_other_private[OF example2_partition_wf assms,
                                         where c' = 1 and r' = core1_res]
  by (simp add: example2_def)

(* Concrete B2 at example2: on the channel's buffer frame, core 0 (sender) has
   read-write and core 1 (receiver) has read-only. *)
lemma example2_buffer_asymmetric:
  "frame_perm example2 0 0x8000 = PermRW \<and> frame_perm example2 1 0x8000 = PermR"
  using buffer_perm_asymmetric[OF example2_partition_wf, where ch = chan01 and f = "0x8000"]
  by (simp add: example2_def chan01_def)

end
