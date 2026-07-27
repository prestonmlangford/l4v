(*
 * PolarFire verified multicore (AMP) -- the per-core invariant layer.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * WHAT THIS THEORY IS FOR.  `integrity_imp_amp_step` (AMP_Integrity.thy) turns
 * seL4's `integrity` into the AMP model's `amp_step`.  To USE it one must first
 * obtain `integrity`, which means discharging the preconditions of
 * `call_kernel_integrity` (Syscall_AC.thy:1311) and `do_user_op_respects`
 * (ADT_AC.thy:89).  The heaviest of those by far is `pas_refined`.
 *
 * THE PROBLEM `amp_config_pas_refined` SOLVES.  l4v establishes `pas_refined`
 * only for one concrete configuration at a time, by brute force:
 * `proof/access-control/RISCV64/ExampleSystem.thy` is 1148 lines and covers a
 * TWO-THREAD system, and `proof/infoflow/RISCV64/Example_Valid_State.thy` is
 * another 1971.  Repeating that for a real PolarFire partition is not a
 * realistic route, and doing it once would say nothing about the next
 * configuration.
 *
 * This theory takes the other route.  It states ONE condition on a kernel
 * state -- `amp_config` -- phrased in the vocabulary of the declared boot
 * partition (`ap_cores`, `ap_channels`, `cr_frames`, `ch_buffer`), and proves
 * that ANY state satisfying it satisfies `pas_refined` for that core's PAS.  A
 * boot configuration can then be checked against the partition it claims to
 * implement, rather than against `auth_graph_map` and `amp_policy`.
 *
 * That is available only because the PAS is core-granular.  At thread
 * granularity (what A-THR needs) the same conjuncts do not collapse, which is
 * the concrete reason A-THR is priced separately -- see multicore-amp-plan.md
 * W3b.
 *
 * WHAT IS AND IS NOT REDUCED, stated plainly (plan section 9).  Six conditions
 * become one, not zero.  Four of `amp_config`'s six clauses are genuinely
 * smaller than what they discharge -- they say "this address lies in a frame
 * this core owns", which is a property of the boot configuration and can be
 * checked against one.  The other two, `amp_objs_local` and `amp_vrefs_local`,
 * are NOT smaller than the `pas_refined` conjuncts they feed: they are the same
 * edge sets, restated over the partition instead of over `amp_policy`.  The
 * gain there is that they are checkable against a declared partition, and that
 * they are named conditions rather than an unfolded proof obligation; it is not
 * a derivation from something simpler.  Anyone reading this as "pas_refined is
 * proved" is reading it wrong.
 *
 * WHAT IS ASSUMED AT BOOT.  Nothing here.  `amp_config` is a hypothesis of
 * every result below; AMP_ADT.thy carries it into `core_inv` and assumes THAT
 * at boot, disclosed as A-HW restated in l4v's vocabulary.
 *
 * TWO CONFIGURATION RESTRICTIONS, recorded because both were found by reading
 * l4v rather than by a failing proof:
 *
 *   - PAGE SIZE.  `aobj_ref' (FrameCap ref cR sz dev as) = ptr_range ref
 *     (pageBitsForSize sz)` (ArchAccess.thy:53): a frame cap's object
 *     references span the WHOLE page, and `sbta_caps` emits an edge for each.
 *     `amp_label_of` labels every byte by its enclosing 4K frame, so a 2M or 1G
 *     page would require every one of its 4K frames to be owned.  Nothing below
 *     is false for large pages, but `amp_config` is only satisfiable for a
 *     configuration that maps 4K pages, and that is the intended AMP setup.
 *   - CONTROL CAPS.  `cap_auth_conferred` (Access.thy:118) confers `Control` on
 *     Untyped, CNode, Thread, Domain, IRQControl and Zombie caps, and
 *     `sbta_untyped` confers `Control` over an untyped cap's entire range.
 *     `policy_wellformed`'s first conjunct forbids the subject from holding
 *     `Control` over any label but its own, so `amp_objs_local` is violated by
 *     any such cap reaching outside the core -- in particular by an untyped cap
 *     covering a channel buffer.  This is a real, checkable boot condition.
 *
 * Organised in the usual four zones: SPECIFICATION, PROOF DEVELOPMENT,
 * RESULTS, EXAMPLES.
 *)

theory AMP_Invariant
imports "AMP_Integrity.AMP_Integrity"
begin

section \<open>Specification\<close>

subsection \<open>Addresses, in the partition's vocabulary\<close>

(* p lies in a frame core c holds PRIVATELY. This is the workhorse of
   `amp_config`: almost every clause says some address of the kernel state
   satisfies it. Stated over `frame_of p` rather than p because seL4 addresses
   objects by byte and the partition owns whole frames. *)
definition amp_private :: "amp_partition \<Rightarrow> core_id \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "amp_private bp c p \<equiv> \<exists>r. ap_cores bp c = Some r \<and> frame_of p \<in> cr_frames r"

(* p lies in the buffer of a declared channel whose RECEIVER is c. This is the
   one place an authority edge is permitted to leave the core's own label, and
   only carrying `Read` -- which is exactly the asymmetry Phase 2's `frame_perm`
   declares and Phase 5's `amp_auth_graph` records. *)
definition amp_inbuf :: "amp_partition \<Rightarrow> core_id \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "amp_inbuf bp c p \<equiv> \<exists>ch \<in> ap_channels bp. ch_to ch = c \<and> frame_of p \<in> ch_buffer ch"

(* p lies in the buffer of a declared channel whose SENDER is c. Such a frame
   carries core c's OWN label (`owner_core_buffer` attributes a buffer to its
   sender), so authority over it is a self-loop and needs no exception. *)
definition amp_outbuf :: "amp_partition \<Rightarrow> core_id \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "amp_outbuf bp c p \<equiv> \<exists>ch \<in> ap_channels bp. ch_from ch = c \<and> frame_of p \<in> ch_buffer ch"

(* Everything labelled `Core c`: the core's private frames plus the buffers it
   SENDS on.
 *
 * Distinguishing this from `amp_private` is load-bearing, not tidiness. An
 * earlier version of this theory required every vspace target to be
 * `amp_private`; since a channel buffer is never private (conjunct 3 of
 * `amp_partition_wf`), that made `amp_config` UNSATISFIABLE for any core that
 * sends on a channel -- the sender could not map its own buffer writable, so it
 * could not send, and `amp_config_pas_refined` would have been green and
 * vacuous. A green build cannot detect that; `example2_config_nonvacuous` below
 * is what does. *)
definition amp_own :: "amp_partition \<Rightarrow> core_id \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "amp_own bp c p \<equiv> amp_private bp c p \<or> amp_outbuf bp c p"

subsection \<open>The six configuration clauses\<close>

(* Each clause below is a named definition rather than a conjunct inlined into
   `amp_config`, for two reasons. It keeps the assumption ledger honest: if one
   ever has to be weakened, the plan's fallback table can name the clause rather
   than "a conjunct of amp_config". And it keeps the extraction in
   `amp_config_pas_refined` a flat conjunction of atoms -- unfolding six
   quantified clauses at once and letting a classical prover sort them out does
   not terminate, which cost a session to find out. *)

(* Clause 1. The core's interrupt CNodes are its own. Discharges
   `irq_map_wellformed`, whose target label is `pasIRQAbs` = Core c. *)
definition amp_irqnode_own :: "amp_partition \<Rightarrow> core_id \<Rightarrow> det_state \<Rightarrow> bool" where
  "amp_irqnode_own bp c s \<equiv> \<forall>irq. amp_private bp c (interrupt_irq_node s irq)"

(* Clause 2. Every TCB in this kernel is the core's own. Discharges
   `tcb_domain_map_wellformed` -- and hence, as a corollary, AMP_Integrity's
   `tcbs_labelled`, which is therefore NOT a separate assumption anywhere in
   this development (see `pas_refined_tcbs_labelled`). *)
definition amp_tcbs_own :: "amp_partition \<Rightarrow> core_id \<Rightarrow> det_state \<Rightarrow> bool" where
  "amp_tcbs_own bp c s \<equiv> \<forall>t d. (t, d) \<in> domains_of_state s \<longrightarrow> amp_private bp c t"

(* Clause 3. Every object holding a cap is in the core's private memory. Feeds
   the `Control`-to-IRQ and `Control`-to-ASID edges, which have no object-graph
   counterpart and so are not covered by clause 4. *)
definition amp_cslots_own :: "amp_partition \<Rightarrow> core_id \<Rightarrow> det_state \<Rightarrow> bool" where
  "amp_cslots_own bp c s \<equiv>
     \<forall>p sl cap. caps_of_state s (p, sl) = Some cap \<longrightarrow> amp_private bp c p"

(* Clause 4. Every authority edge the state exhibits starts inside the core and
   stays inside it -- except that it may carry `Read` into a buffer the core
   RECEIVES on. This is one of the two clauses that is a restatement rather than
   a reduction; see the theory header. *)
definition amp_objs_local :: "amp_partition \<Rightarrow> core_id \<Rightarrow> det_state \<Rightarrow> bool" where
  "amp_objs_local bp c s \<equiv>
     \<forall>p a p'. (p, a, p') \<in> state_objs_to_policy s
              \<longrightarrow> amp_own bp c p \<and> (amp_own bp c p' \<or> (a = Read \<and> amp_inbuf bp c p'))"

(* Clause 5. The core's ASID pools are its own. *)
definition amp_asidtab_own :: "amp_partition \<Rightarrow> core_id \<Rightarrow> det_state \<Rightarrow> bool" where
  "amp_asidtab_own bp c s \<equiv>
     \<forall>hi p. RISCV64_A.riscv_asid_table (arch_state s) hi = Some p \<longrightarrow> amp_private bp c p"

(* Clause 6. The same discipline as clause 4, for the page-table graph: a
   mapping either targets the core's own memory, or is a `Read` mapping of an
   inbound buffer. A receiver that mapped a channel buffer WRITABLE would
   violate this, and `pas_refined` with it, because `pte_ref2` (ArchAccess.thy:26)
   gives a leaf PTE exactly the auths of its rights -- so the asymmetric buffer
   permission is FORCED by seL4's own page-table machinery rather than assumed
   alongside it. *)
definition amp_vrefs_local :: "amp_partition \<Rightarrow> core_id \<Rightarrow> det_state \<Rightarrow> bool" where
  "amp_vrefs_local bp c s \<equiv>
     \<forall>p q i t a. (q, i, t, a) \<in> state_vrefs s p
                 \<longrightarrow> amp_own bp c q \<or> (a = Read \<and> amp_inbuf bp c q)"

subsection \<open>The configuration condition\<close>

(* A kernel state that realises the declared partition, for core c: the
   conjunction of the six clauses above, in the order the six `pas_refined`
   conjuncts consume them. *)
definition amp_config :: "amp_partition \<Rightarrow> core_id \<Rightarrow> det_state \<Rightarrow> bool" where
  "amp_config bp c s \<equiv>
     amp_irqnode_own bp c s \<and> amp_tcbs_own bp c s \<and> amp_cslots_own bp c s
   \<and> amp_objs_local bp c s \<and> amp_asidtab_own bp c s \<and> amp_vrefs_local bp c s"

section \<open>Proof development (internal machinery)\<close>

subsection \<open>Clause destructors\<close>

(* Clause 1, in usable form. *)
lemma amp_irqnode_ownD:
  "amp_irqnode_own bp c s \<Longrightarrow> amp_private bp c (interrupt_irq_node s irq)"
  by (simp add: amp_irqnode_own_def)

(* Clause 2, in usable form. *)
lemma amp_tcbs_ownD:
  "\<lbrakk> amp_tcbs_own bp c s; (t, d) \<in> domains_of_state s \<rbrakk> \<Longrightarrow> amp_private bp c t"
  unfolding amp_tcbs_own_def by blast

(* Clause 3, in usable form. Stated over an explicit slot pair because that is
   the shape `sbta_caps` and `sita_controlled` present. *)
lemma amp_cslots_ownD:
  "\<lbrakk> amp_cslots_own bp c s; caps_of_state s (p, sl) = Some cap \<rbrakk> \<Longrightarrow> amp_private bp c p"
  unfolding amp_cslots_own_def by blast

(* Clause 4, in usable form. *)
lemma amp_objs_localD:
  "\<lbrakk> amp_objs_local bp c s; (p, a, p') \<in> state_objs_to_policy s \<rbrakk>
   \<Longrightarrow> amp_own bp c p \<and> (amp_own bp c p' \<or> (a = Read \<and> amp_inbuf bp c p'))"
  by (simp add: amp_objs_local_def)

(* Clause 5, in usable form. *)
lemma amp_asidtab_ownD:
  "\<lbrakk> amp_asidtab_own bp c s; RISCV64_A.riscv_asid_table (arch_state s) hi = Some p \<rbrakk>
   \<Longrightarrow> amp_private bp c p"
  by (simp add: amp_asidtab_own_def)

(* Clause 6, in usable form. *)
lemma amp_vrefs_localD:
  "\<lbrakk> amp_vrefs_local bp c s; (q, i, t, a) \<in> state_vrefs s p \<rbrakk>
   \<Longrightarrow> amp_own bp c q \<or> (a = Read \<and> amp_inbuf bp c q)"
  by (simp add: amp_vrefs_local_def)

subsection \<open>From partition membership to labels\<close>

(* THE bridge of this theory: an address in one of core c's private frames
   carries label `Core c`. Everything below is this lemma applied six times.
   The partition's private-frame disjointness (conjunct 1 of
   `amp_partition_wf`) is what makes the owner unique. *)
lemma amp_private_label:
  assumes wf: "amp_partition_wf bp" and p: "amp_private bp c p"
  shows "amp_label_of bp p = Core c"
proof -
  from p obtain r where ac: "ap_cores bp c = Some r" and f: "frame_of p \<in> cr_frames r"
    by (auto simp: amp_private_def)
  from owner_core_priv[OF wf ac f] show ?thesis by (simp add: amp_label_of_def)
qed

(* An outbound buffer carries its sender's label -- which, for the sender, is
   the sender's own. This is why a core writing the buffer it sends on is a
   self-loop in `amp_policy` and needs no cross-label edge. *)
lemma amp_outbuf_label:
  assumes wf: "amp_partition_wf bp" and p: "amp_outbuf bp c p"
  shows "amp_label_of bp p = Core c"
proof -
  from p obtain ch where ch: "ch \<in> ap_channels bp" and fr: "ch_from ch = c"
                     and f: "frame_of p \<in> ch_buffer ch"
    by (auto simp: amp_outbuf_def)
  from owner_core_buffer[OF wf ch f] fr show ?thesis by (simp add: amp_label_of_def)
qed

(* The two together: everything the core owns carries the core's label. This is
   the hypothesis shape clauses 4 and 6 present. *)
lemma amp_own_label:
  assumes wf: "amp_partition_wf bp" and p: "amp_own bp c p"
  shows "amp_label_of bp p = Core c"
  using p amp_private_label[OF wf] amp_outbuf_label[OF wf] by (auto simp: amp_own_def)

(* The same for an inbound buffer, which carries its SENDER's label -- a
   DIFFERENT label from the receiver's. The returned channel is what witnesses
   membership of `amp_policy`'s only cross-label edge. *)
lemma amp_inbuf_label:
  assumes wf: "amp_partition_wf bp" and p: "amp_inbuf bp c p"
  shows "\<exists>ch \<in> ap_channels bp. ch_to ch = c \<and> amp_label_of bp p = Core (ch_from ch)"
proof -
  from p obtain ch where ch: "ch \<in> ap_channels bp" and to: "ch_to ch = c"
                     and f: "frame_of p \<in> ch_buffer ch"
    by (auto simp: amp_inbuf_def)
  from owner_core_buffer[OF wf ch f] have "amp_label_of bp p = Core (ch_from ch)"
    by (simp add: amp_label_of_def)
  with ch to show ?thesis by blast
qed

(* THE shape every conjunct below reduces to: an edge FROM the core, to
   something the core is entitled to. Either the target is the core's own -- a
   self-loop -- or the edge carries `Read` into a buffer the core receives on,
   which is `amp_policy`'s one cross-label edge. No third possibility exists,
   which is precisely the content of `pas_refined` for this PAS. *)
lemma amp_subject_edge_in_policy:
  assumes wf: "amp_partition_wf bp"
      and tgt: "amp_own bp c p' \<or> (a = Read \<and> amp_inbuf bp c p')"
  shows "(Core c, a, amp_label_of bp p') \<in> amp_policy bp"
  using tgt
proof
  assume "amp_own bp c p'"
  from amp_own_label[OF wf this] show ?thesis by (simp add: amp_policy_self)
next
  assume r: "a = Read \<and> amp_inbuf bp c p'"
  then obtain ch where ch: "ch \<in> ap_channels bp" and to: "ch_to ch = c"
                   and lb: "amp_label_of bp p' = Core (ch_from ch)"
    using amp_inbuf_label[OF wf] by blast
  from r to lb ch show ?thesis by (fastforce simp: amp_policy_def)
qed

(* The same for an edge whose subject is an ADDRESS rather than the core itself
   -- the object-graph case, where the subject's label has to be computed too. *)
lemma amp_edge_in_policy:
  assumes wf: "amp_partition_wf bp"
      and src: "amp_own bp c p"
      and tgt: "amp_own bp c p' \<or> (a = Read \<and> amp_inbuf bp c p')"
  shows "(amp_label_of bp p, a, amp_label_of bp p') \<in> amp_policy bp"
  using amp_subject_edge_in_policy[OF wf tgt] amp_own_label[OF wf src] by simp

section \<open>Results\<close>

subsection \<open>J2 -- the configuration condition implies pas_refined\<close>

(* THE RESULT OF THIS THEORY. Every state realising the declared partition
   satisfies seL4's `pas_refined` for that core's PAS -- for EVERY partition,
   not for one hand-built example.
 *
 * The six conjuncts of `pas_refined` (Access.thy:312) go as follows:
 *   - `pas_wellformed` needs nothing at all (AMP_Integrity's J1);
 *   - `irq_map_wellformed` and `tcb_domain_map_wellformed` are clauses 1 and 2
 *     carried through `amp_private_label`;
 *   - `state_objs_in_policy` is clause 4 through `amp_edge_in_policy`;
 *   - the ASID and IRQ policy inclusions are clauses 3, 5 and 6, one per
 *     introduction rule of `state_asids_to_policy_aux` and
 *     `state_irqs_to_policy_aux`.
 *
 * `state_objs_to_policy` and `state_vrefs` are never unfolded: the point is
 * that their shape does not matter, only that every edge they contain is one
 * the declared partition permits.
 *
 * What this does NOT do: it does not establish `amp_config` for any state. That
 * is assumed at boot (AMP_ADT.thy), disclosed as A-HW in l4v's vocabulary. *)
theorem amp_config_pas_refined:
  assumes wf: "amp_partition_wf bp" and cfg: "amp_config bp c s"
  shows "pas_refined (amp_pas bp c) s"
proof -
  from cfg have irqn: "amp_irqnode_own bp c s" and doms: "amp_tcbs_own bp c s"
            and cslots: "amp_cslots_own bp c s" and objs: "amp_objs_local bp c s"
            and asidtab: "amp_asidtab_own bp c s" and vrefs: "amp_vrefs_local bp c s"
    by (simp_all add: amp_config_def)
  show ?thesis
    unfolding pas_refined_def
  proof (intro conjI)
    show "pas_wellformed (amp_pas bp c)" by (rule amp_pas_wellformed)
  next
    show "irq_map_wellformed (amp_pas bp c) s"
      using amp_private_label[OF wf amp_irqnode_ownD[OF irqn]]
      by (simp add: irq_map_wellformed_aux_def amp_pas_def)
  next
    show "tcb_domain_map_wellformed (amp_pas bp c) s"
      using amp_private_label[OF wf amp_tcbs_ownD[OF doms]]
      by (clarsimp simp: tcb_domain_map_wellformed_aux_def amp_pas_def)
  next
    show "state_objs_in_policy (amp_pas bp c) s"
      apply (rule subsetI)
      apply (clarsimp simp: auth_graph_map_def amp_pas_def)
      apply (frule amp_objs_localD[OF objs])
      apply (blast intro: amp_edge_in_policy[OF wf])
      done
  next
    \<comment> \<open>three introduction rules, discharged by clauses 3, 6 and 5 in that order.
        The idiom (`rule subsetI, clarsimp, erule ....cases`) is copied from
        l4v's own ExampleSystem.thy:606 rather than reinvented.\<close>
    show "state_asids_to_policy (amp_pas bp c) s \<subseteq> pasPolicy (amp_pas bp c)"
      apply (rule subsetI, clarsimp simp: RISCV64.state_asids_to_policy_arch_def)
      apply (erule RISCV64.state_asids_to_policy_aux.cases)
        apply (fastforce simp: amp_pas_def amp_policy_self
                         dest: amp_cslots_ownD[OF cslots] amp_private_label[OF wf])
       apply (fastforce simp: amp_pas_def dest: amp_vrefs_localD[OF vrefs]
                       intro: amp_subject_edge_in_policy[OF wf])
      apply (fastforce simp: amp_pas_def amp_policy_self
                       dest: amp_asidtab_ownD[OF asidtab] amp_private_label[OF wf])
      done
  next
    \<comment> \<open>one introduction rule, discharged by clause 3: an IRQ-controlling cap's
        holder is the core's own object, and `pasIRQAbs` is constantly Core c.\<close>
    show "state_irqs_to_policy (amp_pas bp c) s \<subseteq> pasPolicy (amp_pas bp c)"
      apply (rule subsetI, clarsimp)
      apply (erule state_irqs_to_policy_aux.cases)
      apply (fastforce simp: amp_pas_def amp_policy_self
                       dest: amp_cslots_ownD[OF cslots] amp_private_label[OF wf])
      done
  qed
qed

subsection \<open>J2b -- the vspace clause IS Phase 2's frame_perm\<close>

(* Phase 2 DECLARES that a channel buffer is mapped read-write for its sender
   and read-only for its receiver (`buffer_perm_asymmetric`). That was a
   statement about the AMP model's own `frame_perm`, with nothing connecting it
   to a real page table. This theorem supplies the connection: under
   `amp_config`, a receiver's page tables CANNOT carry any authority over the
   buffer but `Read`, and the permission Phase 2 declares is the one that
   results.
 *
 * The asymmetry is therefore forced, not assumed. `pte_ref2`
 * (ArchAccess.thy:26) gives a leaf PTE exactly `vspace_cap_rights_to_auth` of
 * its rights, so a receiver that mapped the buffer writable would emit a
 * `(Core (ch_to ch), Write, Core (ch_from ch))` edge -- and `amp_policy` has no
 * such edge, so `pas_refined` would fail. seL4's own page-table machinery is
 * what enforces the one-way discipline; the AMP model merely names it.
 *
 * This is the same move `amp_pas_write_authority_iff` (AMP_Integrity) made for
 * Phase 5's authority graph, now for Phase 2's permission map. *)
theorem amp_vrefs_frame_perm:
  assumes wf: "amp_partition_wf bp"
      and vl: "amp_vrefs_local bp c s"
      and ch: "ch \<in> ap_channels bp" and to: "ch_to ch = c"
      and fb: "frame_of q \<in> ch_buffer ch"
      and vr: "(q, i, t, a) \<in> state_vrefs s p"
  shows "a = Read \<and> frame_perm bp c (frame_of q) = PermR"
proof -
  \<comment> \<open>the receiver does not OWN the buffer: it is not private (partition conjunct
      3), and it is not an outbound buffer either, since that would make the
      channel's sender and receiver the same core (conjunct 2)\<close>
  have npriv: "\<not> amp_private bp c q"
    using amp_partition_wf_buffer_not_private[OF wf ch] fb by (auto simp: amp_private_def)
  have nout: "\<not> amp_outbuf bp c q"
  proof
    assume "amp_outbuf bp c q"
    then obtain ch' where ch': "ch' \<in> ap_channels bp" and fr: "ch_from ch' = c"
                      and fb': "frame_of q \<in> ch_buffer ch'"
      by (auto simp: amp_outbuf_def)
    from wf_buffer_unique[OF wf ch' ch fb' fb] have "ch' = ch" .
    with fr to wf ch show False by (auto simp: amp_partition_wf_def)
  qed
  have nown: "\<not> amp_own bp c q" using npriv nout by (simp add: amp_own_def)
  from amp_vrefs_localD[OF vl vr] nown have "a = Read" by auto
  moreover from buffer_perm_asymmetric[OF wf ch fb] to
  have "frame_perm bp c (frame_of q) = PermR" by simp
  ultimately show ?thesis by simp
qed

subsection \<open>J3 -- the scheduler re-establishes schact_is_rct\<close>

(* `call_kernel_integrity` and `call_kernel_pas_refined` both require
   `schact_is_rct`, so the per-core invariant has to carry it -- and therefore
   something must re-establish it across a kernel entry. l4v does not have that
   lemma. It ASSUMES `schact_is_rct` in six places in `Syscall_AC`, and the only
   postcondition lemma about it anywhere is `set_thread_state_schact_is_rct`
   (DetSchedSchedule_AI.thy:605), which covers one primitive.
 *
 * It is nevertheless true and cheap, and it belongs here rather than in
 * `DetSchedSchedule_AI` -- the verified single-core proofs are not edited from
 * this development (plan section 9). *)

(* Every exit path of `schedule_choose_new_thread` ends in
   `set_scheduler_action resume_cur_thread`, so it establishes `schact_is_rct`
   from nothing at all. *)
lemma schedule_choose_new_thread_schact_is_rct:
  "\<lbrace>\<top>\<rbrace> schedule_choose_new_thread \<lbrace>\<lambda>_. schact_is_rct\<rbrace>"
  by (wpsimp simp: schedule_choose_new_thread_def set_scheduler_action_def schact_is_rct_def)

(* `schedule` has four exit paths (Schedule_A.thy:107-158) and needs NO
   precondition. Three of them end in `set_scheduler_action resume_cur_thread`,
   directly or through `schedule_choose_new_thread`. The fourth -- the
   `resume_cur_thread` branch -- changes no state at all, and was entered
   precisely because the scheduler action already was `resume_cur_thread`. *)
(* The operations `schedule` performs BEFORE its final `set_scheduler_action`
   leave the scheduler action alone. l4v has these as `[wp]` in the Refine
   session, which Access does not see. *)
crunch tcb_sched_action, guarded_switch_to, schedule_switch_thread_fastfail, thread_get
  for scheduler_action[wp]: "\<lambda>s :: det_state. P (scheduler_action s)"
  (wp: crunch_wps)

(* `schedule` re-establishes `resume_cur_thread` from nothing. Three of its four
   exit paths end in `set_scheduler_action resume_cur_thread`, directly or
   through `schedule_choose_new_thread`; the fourth changes no state and was
   entered precisely because the action already was `resume_cur_thread`. l4v
   states this as `schedule_sched_act_rct` (Refine.thy:252) but only in the
   Refine session. *)
lemma schedule_sched_act_rct:
  "\<lbrace>\<top>\<rbrace> schedule \<lbrace>\<lambda>rs (s :: det_state). scheduler_action s = resume_cur_thread\<rbrace>"
  unfolding schedule_def
  by (wpsimp wp: schedule_choose_new_thread_schact_is_rct[unfolded schact_is_rct_def]
                 gts_wp
           simp: set_scheduler_action_def)

(* The same, in the `schact_is_rct` vocabulary the access-control preconditions
   are stated in. *)
lemma schedule_schact_is_rct:
  "\<lbrace>\<top>\<rbrace> schedule \<lbrace>\<lambda>_. schact_is_rct :: det_state \<Rightarrow> bool\<rbrace>"
  unfolding schact_is_rct_def by (rule schedule_sched_act_rct)

(* Setting a thread to a RUNNABLE state leaves the scheduler action alone.
   Reproved here verbatim from l4v's Refine.thy:222, which is in the Refine
   session and therefore not in Access's cone; pulling in Refine for one lemma
   would be a far heavier dependency than repeating its script. *)
lemma set_thread_state_sched_act:
  "\<lbrace>(\<lambda>s. runnable state) and (\<lambda>s. P (scheduler_action s))\<rbrace>
   set_thread_state thread state
   \<lbrace>\<lambda>rs s. P (scheduler_action (s :: det_state))\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply wp
     apply (simp add: set_thread_state_act_def)
     apply wp
        apply (rule hoare_pre_cont)
       apply (rule_tac Q'="\<lambda>rv. (\<lambda>s. runnable ts) and (\<lambda>s. P (scheduler_action s))"
               in hoare_strengthen_post)
        apply wp
       apply force
      apply (wp gts_st_tcb_at)+
    apply (rule_tac Q'="\<lambda>rv. st_tcb_at ((=) state) thread and (\<lambda>s. runnable state)
                              and (\<lambda>s. P (scheduler_action s))"
            in hoare_strengthen_post)
     apply (simp add: st_tcb_at_def)
     apply (wp obj_set_prop_at)+
    apply (force simp: st_tcb_at_def obj_at_def)
   apply wp
  apply clarsimp
  done

(* `activate_thread` leaves the scheduler action alone: the only state it ever
   sets is `Running`, and the idle branch is `return ()` on RISCV64
   (Arch_A.thy:44). Also l4v's, from Refine.thy:245. *)
lemma activate_thread_sched_act:
  "\<lbrace>ct_in_state activatable and (\<lambda>s. P (scheduler_action s))\<rbrace>
   activate_thread
   \<lbrace>\<lambda>rs s. P (scheduler_action (s :: det_state))\<rbrace>"
  by (simp add: activate_thread_def set_thread_state_def
                RISCV64_A.arch_activate_idle_thread_def
      | (wp set_thread_state_sched_act gts_wp)+ | wpc)+

(* The instance this development needs. Note the `ct_in_state activatable`
   precondition: it is NOT free, which is why `call_kernel_schact_is_rct` below
   carries invariants rather than holding outright. `schedule` alone needs
   nothing, but the `activate_thread` that follows it does. *)
lemma activate_thread_schact_is_rct:
  "\<lbrace>ct_in_state activatable and schact_is_rct\<rbrace>
   activate_thread
   \<lbrace>\<lambda>_. schact_is_rct :: det_state \<Rightarrow> bool\<rbrace>"
  unfolding schact_is_rct_def
  by (rule activate_thread_sched_act[where P="\<lambda>a. a = resume_cur_thread"])

(* The lemma the invariant actually needs: a whole kernel entry re-establishes
   `schact_is_rct`.
 *
 * The preconditions are NOT decoration and the plan's estimate of this lemma
 * was wrong: finding (c) said `schedule_schact_is_rct` needs no precondition,
 * which is true and is proved above, but `call_kernel` is
 * `handle_event; schedule; activate_thread` -- and the trailing
 * `activate_thread` needs `ct_in_state activatable`, which is not free. The
 * invariants below are what establish it, and they are exactly l4v's own
 * preconditions on `call_kernel_sched_act_rct` (Refine.thy:258). `core_inv`
 * carries all of them anyway, so this costs the invariant nothing. *)
lemma call_kernel_schact_is_rct:
  "\<lbrace>einvs and (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_running s) and schact_is_rct\<rbrace>
   call_kernel ev
   \<lbrace>\<lambda>_. schact_is_rct :: det_state \<Rightarrow> bool\<rbrace>"
  unfolding call_kernel_def schact_is_rct_def
  by (wpsimp wp: activate_thread_sched_act
                 hoare_vcg_conj_lift[OF schedule_ct_activateable schedule_sched_act_rct]
           simp: active_from_running)

subsection \<open>tcbs_labelled is not a separate assumption\<close>

(* AMP_Integrity carries `tcbs_labelled` as a hypothesis of
   `integrity_imp_amp_step`, described there as "a fact about the state to be
   discharged with the per-core invariant". This is that discharge: it is
   `tcb_domain_map_wellformed`, a conjunct of `pas_refined`, so it comes free
   with the invariant and is preserved by l4v's own `call_kernel_pas_refined`
   (Syscall_AC.thy:1326) rather than needing preservation of its own. *)
lemma pas_refined_tcbs_labelled:
  assumes pr: "pas_refined (amp_pas bp c) s"
  shows "tcbs_labelled bp c s"
  unfolding tcbs_labelled_def
proof (intro allI impI)
  fix t tcb assume "get_tcb t s = Some tcb"
  hence "etcbs_of s t = Some (etcb_of tcb)"
    by (simp add: get_tcb_def etcbs_of'_def
           split: option.splits Structures_A.kernel_object.splits)
  hence "(t, etcb_domain (etcb_of tcb)) \<in> domains_of_state s"
    by (fastforce intro: domains_of_state_aux.domtcbs)
  with pr show "amp_label_of bp t = Core c"
    by (fastforce simp: pas_refined_def tcb_domain_map_wellformed_aux_def amp_pas_def)
qed

subsection \<open>J4 -- the per-core invariant\<close>

(* With `irqs = True` the reference state of `domain_sep_inv` is irrelevant: the
   second conjunct of its definition (DomainSepInv.thy:26) is discharged by
   `irqs` alone, leaving only "no DomainCap is held anywhere". Naming that
   directly keeps `core_inv` from mentioning a state twice, which no wp rule
   would match. `amp_pas` sets `pasMaySendIrqs = True`, so this is the only
   instance this development ever needs. *)
definition amp_no_domain_cap :: "det_state \<Rightarrow> bool" where
  "amp_no_domain_cap s \<equiv> \<forall>slot. \<not> cte_wp_at ((=) DomainCap) slot s"

(* The bridge to l4v's form, pointwise. *)
lemma domain_sep_inv_True_iff:
  "domain_sep_inv True st s = amp_no_domain_cap s"
  by (simp add: domain_sep_inv_def amp_no_domain_cap_def)

(* The same point-free, which is the shape needed to rewrite inside the `and`
   combinators l4v states its preconditions with. *)
lemma domain_sep_inv_True_eq:
  "domain_sep_inv True st = amp_no_domain_cap"
  by (rule ext) (rule domain_sep_inv_True_iff)

(* THE per-core invariant: everything `call_kernel_integrity` and
   `do_user_op_respects` require, bundled so it can be carried rather than
   re-established.
 *
 * It is indexed by MODE and EVENT, following l4v's own `full_invs_if`
 * (ADT_IF.thy:1376), and for the same reason: `ev \<noteq> Interrupt \<longrightarrow> ct_running` is
 * not a property of a state at all. It is true of a KernelMode state only
 * because of HOW that state was reached -- `global_automaton` enters KernelMode
 * either from UserMode carrying a real event with `ct_running`, or from
 * IdleMode carrying `Interrupt`. An invariant over states alone cannot express
 * that, which is why the mode and the pending event are parameters.
 *
 * Note what is NOT here. `guarded_pas_domain`, `is_subject \<circ> cur_thread` and
 * `pas_cur_domain` are all consequences of `pas_refined` plus `invs` under this
 * PAS (below), so carrying them would be redundant; `pasMayActivate` and
 * `pasMayEditReadyQueues` hold by construction of `amp_pas`. That leaves five
 * conjuncts, each with an l4v preservation lemma. *)
definition core_inv ::
  "amp_partition \<Rightarrow> core_id \<Rightarrow> mode \<Rightarrow> event option \<Rightarrow> det_state \<Rightarrow> bool" where
  "core_inv bp c m e s \<equiv>
     pas_refined (amp_pas bp c) s \<and> invs s \<and> valid_sched s \<and> valid_list s
   \<and> amp_no_domain_cap s \<and> schact_is_rct s
   \<and> (case m of
        UserMode \<Rightarrow> ct_running s
      | IdleMode \<Rightarrow> ct_idle s
      | KernelMode \<Rightarrow> (ct_active s \<or> ct_idle s)
                      \<and> (\<forall>ev. e = Some ev \<longrightarrow> ev \<noteq> Interrupt \<longrightarrow> ct_running s))"

(* The current thread is always the core's own. This is what makes
   `is_subject aag \<circ> cur_thread` -- a precondition of both integrity lemmas --
   free rather than carried: `invs` says the current thread is a TCB, and
   `pas_refined` says every TCB is this core's. *)
lemma pas_refined_is_subject_cur_thread:
  assumes pr: "pas_refined (amp_pas bp c) s" and iv: "invs s"
  shows "is_subject (amp_pas bp c) (cur_thread s)"
proof -
  from iv have "cur_tcb s" by (rule invs_cur)
  then obtain tcb where "get_tcb (cur_thread s) s = Some tcb"
    by (auto simp: cur_tcb_def tcb_at_def)
  with pas_refined_tcbs_labelled[OF pr] show ?thesis
    by (simp add: tcbs_labelled_def amp_pas_def)
qed

(* The same fact with the label written out, which is the form the composed
   preservation proof below leaves in its goal. *)
lemma pas_refined_cur_thread_label:
  "\<lbrakk> pas_refined (amp_pas bp c) s; invs s \<rbrakk> \<Longrightarrow> amp_label_of bp (cur_thread s) = Core c"
  using pas_refined_is_subject_cur_thread[of bp c s] by (simp add: amp_pas_def)

(* And therefore `guarded_pas_domain` too, since `pasDomainAbs` is constantly
   the core's own singleton. Another precondition that costs nothing under a
   core-granular PAS -- and one that would NOT be free at thread granularity,
   which is part of why A-THR is priced separately. *)
lemma pas_refined_guarded_pas_domain:
  "\<lbrakk> pas_refined (amp_pas bp c) s; invs s \<rbrakk> \<Longrightarrow> guarded_pas_domain (amp_pas bp c) s"
  using pas_refined_is_subject_cur_thread
  by (fastforce simp: guarded_pas_domain_def amp_pas_def)

(* Field projections of the per-core PAS, so that the composed preservation
   proof below never has to unfold the record. Unfolding it would put
   `amp_label_of bp (cur_thread s) = Core c` in the goal, at which point the
   derived `is_subject` and `guarded_pas_domain` lemmas no longer match. *)
lemma amp_pas_simps[simp]:
  "pasSubject (amp_pas bp c) = Core c"
  "pasObjectAbs (amp_pas bp c) = amp_label_of bp"
  "pasMaySendIrqs (amp_pas bp c)"
  "pasMayActivate (amp_pas bp c)"
  "pasMayEditReadyQueues (amp_pas bp c)"
  "pasDomainAbs (amp_pas bp c) d = {Core c}"
  by (simp_all add: amp_pas_def)

(* The core is always in its own domain, unconditionally: `pasDomainAbs` is
   constantly the core's own singleton. *)
lemma pas_cur_domain_amp_pas[simp]: "pas_cur_domain (amp_pas bp c) s"
  by simp

(* l4v's kernel-invariant lemma with its `and`-form postcondition flattened to a
   conjunction, so that ONE wp rule delivers both halves that `core_inv` needs. *)
lemma call_kernel_invs_ct:
  "\<lbrace>invs and (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_running s)\<rbrace>
   (call_kernel ev :: (unit, det_ext) s_monad)
   \<lbrace>\<lambda>_ s. invs s \<and> (ct_running s \<or> ct_idle s)\<rbrace>"
  using akernel_invs_det_ext[where e=ev] by (simp add: pred_conj_def)

(* `call_kernel_domain_sep_inv` at `irqs = True`, in the reference-state-free
   form `core_inv` carries. *)
lemma call_kernel_no_domain_cap:
  "\<lbrace>amp_no_domain_cap and invs and (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_active s)\<rbrace>
   (call_kernel ev :: (unit, det_ext) s_monad)
   \<lbrace>\<lambda>_. amp_no_domain_cap\<rbrace>"
  using call_kernel_domain_sep_inv[where irqs=True and st="undefined :: det_state" and ev=ev]
  by (simp add: domain_sep_inv_True_eq)

(* PRESERVATION across the kernel-call transition, the first of `ADT_A`'s three
   memory-touching kinds. Every conjunct has an l4v lemma and this theorem is
   their composition; nothing new is proved about the kernel here. The event
   hypothesis is exactly what `core_inv`'s mode index supplies, and the
   `ct_running \<or> ct_idle` conclusion is what decides the mode `kernel_call_A`
   moves to. *)
theorem call_kernel_core_inv:
  "\<lbrace>core_inv bp c KernelMode (Some ev)\<rbrace>
   (call_kernel ev :: (unit, det_ext) s_monad)
   \<lbrace>\<lambda>_ s. pas_refined (amp_pas bp c) s \<and> valid_sched s \<and> valid_list s
          \<and> amp_no_domain_cap s \<and> schact_is_rct s
          \<and> (invs s \<and> (ct_running s \<or> ct_idle s))\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule hoare_vcg_conj_lift[OF call_kernel_pas_refined
            hoare_vcg_conj_lift[OF call_kernel_valid_sched
              hoare_vcg_conj_lift[OF call_kernel_valid_list
                hoare_vcg_conj_lift[OF call_kernel_no_domain_cap
                  hoare_vcg_conj_lift[OF call_kernel_schact_is_rct
                                         call_kernel_invs_ct]]]]])
  apply (clarsimp simp: core_inv_def active_from_running pred_conj_def
                        domain_sep_inv_True_iff schact_is_rct_def
                        pas_refined_guarded_pas_domain)
  apply (simp add: pas_refined_cur_thread_label)
  done

(* PRESERVATION, user-mode transition. `do_user_op` writes user memory and
   returns a register context; it touches neither `kheap`, `cdt`,
   `caps_of_state` nor `arch_state`, so every capability-shaped conjunct of the
   invariant is preserved for free. l4v proves the `pas_refined` half only for
   the SPLIT operation `do_user_op_if` (ArchADT_IF.thy:63), inside InfoFlow;
   the crunch here is the same argument for the unsplit `do_user_op`, which
   keeps InfoFlow out of this session's dependencies. *)
crunch do_user_op
  for pas_refined[wp]: "pas_refined aag"
  and valid_list[wp]: valid_list
  and valid_sched[wp]: "valid_sched :: det_state \<Rightarrow> bool"
  and scheduler_action[wp]: "\<lambda>s :: det_state. P (scheduler_action s)"
  and no_domain_cap[wp]: amp_no_domain_cap
  (wp: crunch_wps select_wp simp: crunch_simps amp_no_domain_cap_def
   ignore: user_memory_update device_memory_update)

(* PRESERVATION, interrupt-poll transition. `check_active_irq` is
   `do_machine_op (getActiveIRQ ...)`, which touches only `irq_state` and
   `irq_masks`. l4v has this as `check_active_irq_invs` (Move_R.thy:238) in the
   Refine session; its whole proof is the one line repeated here. *)
crunch check_active_irq
  for pas_refined[wp]: "pas_refined aag"
  and valid_list[wp]: valid_list
  and valid_sched[wp]: "valid_sched :: det_state \<Rightarrow> bool"
  and scheduler_action[wp]: "\<lambda>s :: det_state. P (scheduler_action s)"
  and no_domain_cap[wp]: amp_no_domain_cap
  (wp: crunch_wps simp: crunch_simps amp_no_domain_cap_def)

(* `invs` needs the machine-op argument, so it is not a crunch. l4v's
   `check_active_irq_invs` (Move_R.thy:238) is this one line, carrying a much
   longer pre/postcondition that this development does not need. *)
lemma check_active_irq_invs_amp:
  "\<lbrace>invs\<rbrace> check_active_irq \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp simp: check_active_irq_def)

section \<open>Examples\<close>

subsection \<open>The configuration condition is satisfiable by a sending core\<close>

(* NON-VACUITY, the half a green build cannot detect, and the reason the
   distinction between `amp_own` and `amp_private` exists.
 *
 * `amp_config_pas_refined` is an implication. It would be equally green if
 * `amp_config` were unsatisfiable -- and an earlier version of this theory made
 * exactly that mistake, requiring every authority target to be `amp_private`.
 * Since a channel buffer is never private (conjunct 3 of `amp_partition_wf`),
 * that forbade the SENDER from holding any authority over the buffer it sends
 * on: no write, therefore no send, therefore no configuration of a
 * channel-using system satisfies the condition, therefore the theorem says
 * nothing. These three lemmas pin the corrected asymmetry down concretely. *)

(* Core 0 is example2's sender, and OWNS the buffer: an edge from core 0 to
   0x8000 is a self-loop, so clauses 4 and 6 permit it with ANY authority --
   Write included. This is the lemma that fails under the broken definition. *)
lemma example2_sender_owns_buffer: "amp_own example2 0 0x8000"
  by (fastforce simp: amp_own_def amp_outbuf_def example2_def chan01_def
                      frame_of_def mask_eq_decr_exp RISCV64.pageBits_def)

(* Core 1 is the receiver, and does NOT own the buffer -- so clauses 4 and 6
   confine it to the `Read` exception, which is the one-way discipline. *)
lemma example2_receiver_not_own_buffer: "\<not> amp_own example2 1 0x8000"
  by (auto simp: amp_own_def amp_private_def amp_outbuf_def example2_def core1_res_def
                 chan01_def frame_of_def mask_eq_decr_exp RISCV64.pageBits_def)

(* And the exception really is available to it: 0x8000 is an inbound buffer for
   core 1, so a `Read` edge to it is permitted. Without this the receiver could
   not read the message and the channel would be as vacuous as before. *)
lemma example2_receiver_inbuf: "amp_inbuf example2 1 0x8000"
  by (fastforce simp: amp_inbuf_def example2_def chan01_def
                      frame_of_def mask_eq_decr_exp RISCV64.pageBits_def)

end
