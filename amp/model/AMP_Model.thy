(*
 * PolarFire verified multicore (AMP) — Phase 1: the AMP system model.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * This theory introduces the multicore SYSTEM as a spec-level composition of N
 * single-core abstract states, together with the static boot partition that
 * says which physical resources each core owns. There is deliberately NO
 * behaviour here (no kernel steps): Phase 1 is state and invariant SHAPE only.
 * The per-core `abstract_state` is imported UNCHANGED from ASpec — the existing
 * specification is single-core by construction and we keep it that way.
 *
 * See ../../multicore-amp-plan.md section 5 (Phase 1). The key definitions are:
 *   - core_id, core_resources, amp_channel, amp_partition, amp_state;
 *   - amp_partition_wf: the well-formedness predicate (cores' private frames are
 *     disjoint, and the only cross-core sharing is via declared channel buffers);
 *   - owned_frames and owned_overlap_subset_channels: the shape Phase 2 will
 *     prove is PRESERVED by each core's kernel steps.
 * Exit test: this session builds green and amp_partition_wf holds for the
 * example two-core configuration (example2_partition_wf below).
 *)

theory AMP_Model
imports "ASpec.Syscall_A"
begin

(* This theory is organized in four zones, in this order: SPECIFICATION (types,
   records, and the operations/predicates that give the AMP model its
   vocabulary — read this to know WHAT is being modelled), PROOF DEVELOPMENT
   (internal destructor lemmas that exist only to make the results below
   provable — skip this if you only want to know what holds), RESULTS (the
   phase's headline theorem), and EXAMPLES (a concrete non-vacuity witness).
   See ../../multicore-amp-plan.md section 2.5 and amp/overview/AMP_Overview.thy
   for the cumulative cross-phase version of this same idea. *)

section \<open>Specification\<close>

subsection \<open>Core identifiers and per-core resources\<close>

(* A core is named by a natural number. PolarFire has four U54 application
   cores, but nothing in the model fixes the count; core_id is left as nat so
   the same definitions serve any number of cores. Which core_ids are actually
   present in a system is recorded by the domain of the partition map below,
   not by this type. *)
type_synonym core_id = nat

(* The physical resources a single core owns privately. cr_frames is the set of
   physical frames (identified by their machine-word base address, the same
   obj_ref used throughout the abstract spec) that only this core may access;
   cr_irqs is the set of interrupt lines routed to this core. "Private" is the
   operative word: the well-formedness predicate below forbids these sets from
   overlapping another core's private frames. Shared memory is never listed
   here — it lives in a channel buffer instead. *)
record core_resources =
  cr_frames :: "obj_ref set"
  cr_irqs   :: "irq set"

subsection \<open>Declared cross-core channels\<close>

(* A declared one-way communication channel between two distinct cores. ch_from
   is the sender, ch_to the receiver, and ch_buffer is the set of physical
   frames making up the shared swap buffer through which the message travels.
   This buffer is the ONLY sanctioned overlap between two cores' address spaces;
   the asymmetric MMU permissions (writer-side W, reader-side R) that enforce
   the one-way discipline are added in Phase 2. A channel is meaningful only
   when it appears in a partition's ap_channels set. *)
record amp_channel =
  ch_from   :: core_id
  ch_to     :: core_id
  ch_buffer :: "obj_ref set"

(* The unordered pair of cores a channel connects. Used to phrase "sharing is
   allowed only between the two endpoints of some declared channel". *)
definition channel_endpoints :: "amp_channel \<Rightarrow> core_id set" where
  "channel_endpoints ch = {ch_from ch, ch_to ch}"

subsection \<open>The static boot partition\<close>

(* The static, boot-time assignment of resources to cores. ap_cores is a partial
   map from core_id to that core's private resources; its DOMAIN is exactly the
   set of cores that exist in this system (a core_id with no entry is simply not
   present). ap_channels is the set of declared cross-core channels. Everything
   here is fixed at boot and never changes at run time — it is the trusted
   configuration the boot loader is assumed to establish (assumption A-HW). *)
record amp_partition =
  ap_cores    :: "core_id \<rightharpoonup> core_resources"
  ap_channels :: "amp_channel set"

subsection \<open>The multicore system state\<close>

(* The whole AMP system: one single-core abstract_state per present core, plus
   the static partition. amp_cores has the SAME domain as ap_cores of amp_boot —
   an active core has both a resource assignment and a running kernel state. The
   per-core abstract_state is the unmodified single-core spec state, so each
   core individually is exactly the system that is already verified; the
   multicore content is entirely in how they are composed and partitioned. *)
record amp_state =
  amp_cores :: "core_id \<rightharpoonup> abstract_state"
  amp_boot  :: amp_partition

subsection \<open>Well-formedness of the partition\<close>

(* The core invariant SHAPE of the whole AMP effort, stated over the static
   partition. A partition is well-formed when all four hold:
     1. PRIVATE FRAMES ARE DISJOINT. Distinct present cores share no private
        frame — this is spatial isolation of private memory.
     2. CHANNELS ARE CROSS-CORE AND GROUNDED. Every declared channel runs
        between two DISTINCT cores, both of which are present in the partition.
     3. BUFFERS ARE NOT PRIVATE. A channel buffer overlaps no core's private
        frames — shared memory is a separate region, never carved out of
        anyone's private address space.
     4. BUFFERS ARE DISJOINT. Distinct channels use disjoint buffers, so a frame
        belongs to at most one channel.
   Together these make declared channel buffers the ONLY place two cores' memory
   can meet, which is exactly the property Phase 2 shows each kernel step keeps. *)
definition amp_partition_wf :: "amp_partition \<Rightarrow> bool" where
  "amp_partition_wf ap \<equiv>
     (\<forall>c1 c2 r1 r2. ap_cores ap c1 = Some r1 \<longrightarrow> ap_cores ap c2 = Some r2 \<longrightarrow> c1 \<noteq> c2
                    \<longrightarrow> cr_frames r1 \<inter> cr_frames r2 = {}) \<and>
     (\<forall>ch \<in> ap_channels ap. ch_from ch \<noteq> ch_to ch
                    \<and> ch_from ch \<in> dom (ap_cores ap) \<and> ch_to ch \<in> dom (ap_cores ap)) \<and>
     (\<forall>ch \<in> ap_channels ap. \<forall>c r. ap_cores ap c = Some r
                    \<longrightarrow> ch_buffer ch \<inter> cr_frames r = {}) \<and>
     (\<forall>ch1 \<in> ap_channels ap. \<forall>ch2 \<in> ap_channels ap. ch1 \<noteq> ch2
                    \<longrightarrow> ch_buffer ch1 \<inter> ch_buffer ch2 = {})"

subsection \<open>Owned frames\<close>

(* The full set of frames a core may reach: its private frames, plus the buffers
   of every declared channel it is an endpoint of. This is the footprint whose
   pairwise overlap the next theorem bounds, and the quantity Phase 2 shows is
   preserved by kernel steps. A core with no entry in the partition owns
   nothing. *)
definition owned_frames :: "amp_partition \<Rightarrow> core_id \<Rightarrow> obj_ref set" where
  "owned_frames ap c =
     (case ap_cores ap c of None \<Rightarrow> {} | Some r \<Rightarrow> cr_frames r)
     \<union> (\<Union>{ch_buffer ch | ch. ch \<in> ap_channels ap \<and> c \<in> channel_endpoints ch})"

section \<open>Proof development (internal machinery)\<close>

(* Destructor: the private-frame disjointness conjunct, in usable form. Phase 2's
   B1/B3 obligations reach for exactly this fact when arguing a core's step
   cannot touch another core's private memory. *)
lemma amp_partition_wf_private_disjoint:
  "amp_partition_wf ap \<Longrightarrow> ap_cores ap c1 = Some r1 \<Longrightarrow> ap_cores ap c2 = Some r2
   \<Longrightarrow> c1 \<noteq> c2 \<Longrightarrow> cr_frames r1 \<inter> cr_frames r2 = {}"
  by (simp add: amp_partition_wf_def)

(* Destructor: a channel buffer never intersects any core's private frames. This
   is what lets Phase 2 treat the shared buffer as a region separate from every
   core's private address space. *)
lemma amp_partition_wf_buffer_not_private:
  "amp_partition_wf ap \<Longrightarrow> ch \<in> ap_channels ap \<Longrightarrow> ap_cores ap c = Some r
   \<Longrightarrow> ch_buffer ch \<inter> cr_frames r = {}"
  by (simp add: amp_partition_wf_def)

section \<open>Results\<close>

(* The payoff of well-formedness: for two DISTINCT cores, the only frames they
   can both reach are declared channel buffers. Every other cross term is empty
   — private-vs-private by conjunct 1, private-vs-buffer and buffer-vs-private
   by conjunct 3 — leaving only buffer-vs-buffer, which is contained in the union
   of all channel buffers. This is the precise statement of "owned frame sets are
   disjoint except at declared channel buffers", and it is the property Phase 2
   must prove each per-core kernel step maintains. The c1 \<noteq> c2 hypothesis is
   essential: a core's footprint overlaps ITSELF in its private frames, which are
   not channel buffers, so the claim genuinely fails when the cores coincide. *)
lemma owned_overlap_subset_channels:
  assumes wf:  "amp_partition_wf ap"
      and neq: "c1 \<noteq> c2"
  shows "owned_frames ap c1 \<inter> owned_frames ap c2
           \<subseteq> (\<Union>ch \<in> ap_channels ap. ch_buffer ch)"
proof -
  from wf
  have c1disj: "\<forall>a b r s. ap_cores ap a = Some r \<longrightarrow> ap_cores ap b = Some s \<longrightarrow> a \<noteq> b
                          \<longrightarrow> cr_frames r \<inter> cr_frames s = {}"
    and c3buf:  "\<forall>ch \<in> ap_channels ap. \<forall>c r. ap_cores ap c = Some r
                          \<longrightarrow> ch_buffer ch \<inter> cr_frames r = {}"
    by (simp_all add: amp_partition_wf_def)
  show ?thesis
    using neq c1disj c3buf
    by (fastforce simp: owned_frames_def channel_endpoints_def split: option.splits)
qed

section \<open>Examples\<close>

subsection \<open>A well-formed two-core configuration\<close>

(* Private resources for the two example cores. Frames use arbitrary but
   distinct, page-separated witness addresses; the concrete numbers matter only
   in that they are pairwise distinct and disjoint from the channel buffer. *)
(* Core 0's private resources: two private frames and two IRQ lines. *)
definition core0_res :: core_resources where
  "core0_res = \<lparr> cr_frames = {0x1000, 0x2000}, cr_irqs = {1, 2} \<rparr>"

(* Core 1's private resources: two further frames and IRQ lines, chosen disjoint
   from core 0's so the two cores' private memory does not overlap. *)
definition core1_res :: core_resources where
  "core1_res = \<lparr> cr_frames = {0x3000, 0x4000}, cr_irqs = {3, 4} \<rparr>"

(* One declared channel from core 0 (writer) to core 1 (reader), with a single
   buffer frame chosen disjoint from every private frame above. *)
definition chan01 :: amp_channel where
  "chan01 = \<lparr> ch_from = 0, ch_to = 1, ch_buffer = {0x8000} \<rparr>"

(* The example two-core partition: cores 0 and 1 present, one channel between
   them. This is the witness for the Phase 1 exit test. *)
definition example2 :: amp_partition where
  "example2 = \<lparr> ap_cores = [0 \<mapsto> core0_res, 1 \<mapsto> core1_res],
                ap_channels = {chan01} \<rparr>"

(* Phase 1 exit test: the example configuration is well-formed. Discharging this
   confirms the well-formedness predicate is satisfiable by a genuine two-core
   system and that its four conjuncts are mutually consistent. *)
lemma example2_partition_wf: "amp_partition_wf example2"
  by (simp add: amp_partition_wf_def example2_def core0_res_def core1_res_def
                chan01_def channel_endpoints_def dom_def)

end
