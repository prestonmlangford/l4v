(*
 * PolarFire verified multicore (AMP) -- the ADT step layer.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * WHAT THIS THEORY IS FOR.  `integrity_imp_amp_step` (AMP_Integrity.thy) turns
 * seL4's `integrity` into the AMP model's `amp_step`, and
 * `amp_config_pas_refined` / `core_inv` (AMP_Invariant.thy) supply the
 * preconditions of the two l4v lemmas that PRODUCE `integrity`.  What was still
 * missing is the last join: `call_kernel_integrity` and `do_user_op_respects`
 * are statements about two of the kernel's monadic operations, while the seL4
 * system is `ADT_A` -- a six-clause automaton (ADT_AI.thy:127) whose steps also
 * include interrupt polling and three different mode changes.
 *
 * This theory closes that gap.  `amp_step_of_ADT_A` below says: from a state
 * satisfying the per-core invariant, EVERY `ADT_A` step is an `amp_step` for
 * that core and re-establishes the invariant.  That is the form Phases 2-6 need,
 * because `amp_step` is what they carry as a hypothesis.
 *
 * THE THREE MEMORY-TOUCHING TRANSITION KINDS, and how each is discharged:
 *
 *   - `kernel_call_A`, i.e. `kernel_entry` (ADT_AI.thy:249).  This is NOT just
 *     `call_kernel`: it brackets it with a `thread_set` writing the user
 *     register context into the current thread's TCB, and a read-only
 *     `thread_get` reading it back.  The `thread_set` changes the state before
 *     `call_kernel_integrity`'s reference state is taken, so the two integrity
 *     facts have to be composed with `integrity_trans_start` (Access_AC.thy:1590)
 *     rather than simply chained.  It also has to preserve every conjunct of
 *     `core_inv`, which is what the `thread_set_ctxt_*` block below is for.
 *   - `do_user_op_A`, i.e. `do_user_op` (ADT_AI.thy:200).  `do_user_op_respects`
 *     already carries `integrity aag X st` in its PRECONDITION, so it composes
 *     directly with no transitivity step.
 *   - `check_active_irq_A`.  This one needs no integrity argument at all:
 *     `getActiveIRQ` (MachineOps.thy:132) touches only `irq_state`, so
 *     `underlying_memory` is unchanged, `changed_frames` is empty, and
 *     `amp_step` holds for ANY partition.  Proving the memory equality directly
 *     is both shorter and stronger than routing it through `integrity`.
 *
 * ONE CORRECTION TO THE PLAN, found by doing the work.  The plan priced the
 * `thread_set` bracket as covered by `thread_set_integrity_autarch` alone.  It
 * is not: the bracket also has to preserve `pas_refined`, and the version of
 * `thread_set_pas_refined` in the Access session (CNode_AC.thy:1343) assumes
 * `tcb_arch (f tcb) = tcb_arch tcb` -- which is exactly what writing the
 * register context violates.  l4v has a version without that assumption, but
 * only inside InfoFlow (ArchADT_IF.thy:302).  Its ten-line script is reproduced
 * below rather than taken as a dependency; see `thread_set_ctxt_pas_refined`.
 *
 * WHAT IS ASSUMED.  One thing, and it is named: `amp_gs_inv bp c` must hold of
 * the initial global state.  That is A-HW restated in l4v's vocabulary -- the
 * claim that the boot loader really does hand each core a state realising the
 * declared partition -- and it sits exactly where l4v puts its own
 * `akernel_init_invs` (KernelInit_AI.thy:16, header: "Currently axiomatised").
 * `amp_config_pas_refined` is what makes that assumption checkable against a
 * boot configuration rather than against `auth_graph_map`.  Nothing else here is
 * assumed: every lemma below is a hypothesis-carrying implication.
 *
 * Organised in the usual four zones: SPECIFICATION, PROOF DEVELOPMENT,
 * RESULTS, EXAMPLES.
 *)

theory AMP_ADT
imports "AMP_Invariant.AMP_Invariant"
begin

section \<open>Specification\<close>

subsection \<open>The per-core invariant and the memory projection, at ADT_A granularity\<close>

(* The per-core invariant of a whole `ADT_A` global state. `core_inv` is indexed
   by mode and pending event because `ev \<noteq> Interrupt \<longrightarrow> ct_running` is a fact about
   how a state was REACHED (AMP_Invariant.thy); a `global_state` carries exactly
   those two indices alongside the kernel state, so this is the shape in which
   the invariant can be both assumed and re-established by a step.

   Written with projections rather than a case pattern on purpose: the six
   clauses of `global_automaton` leave the user-context/kernel-state pair
   unsplit, and a case pattern here would force a spurious split in each. *)
definition amp_gs_inv :: "amp_partition \<Rightarrow> core_id \<Rightarrow> det_state global_state \<Rightarrow> bool" where
  "amp_gs_inv bp c gs \<equiv> core_inv bp c (fst (snd gs)) (snd (snd gs)) (snd (fst gs))"

(* The AMP model's system memory, read off an `ADT_A` global state: neither the
   register context nor the mode is memory, so this is just `mem_proj` of the
   kernel state component. *)
definition gs_mem :: "det_state global_state \<Rightarrow> obj_ref \<Rightarrow> (machine_word \<Rightarrow> word8)" where
  "gs_mem gs \<equiv> mem_proj (snd (fst gs))"

section \<open>Proof development (internal machinery)\<close>

subsection \<open>The register-context update performed at kernel entry\<close>

(* The TCB update `kernel_entry` performs before calling the kernel: it stores
   the user's register context into the current thread's arch TCB. Named here
   because a dozen preservation lemmas below are about exactly this function and
   nothing else. *)
abbreviation ctxt_upd :: "user_context \<Rightarrow> tcb \<Rightarrow> tcb" where
  "ctxt_upd tc \<equiv> (\<lambda>tcb. tcb \<lparr> tcb_arch := arch_tcb_context_set tc (tcb_arch tcb) \<rparr>)"

(* The update touches `tcb_arch` and nothing else. Each field equality below is
   a separate named lemma rather than a simp set because l4v's preservation
   lemmas take them as explicit assumptions, in exactly this form. *)
lemma ctxt_upd_tcb_state: "tcb_state (ctxt_upd tc tcb) = tcb_state tcb"
  by simp

(* As above, for the bound notification. *)
lemma ctxt_upd_bound_ntfn: "tcb_bound_notification (ctxt_upd tc tcb) = tcb_bound_notification tcb"
  by simp

(* As above, for the scheduling domain -- this is the one `pas_refined` needs,
   since `tcb_domain_map_wellformed` is a conjunct of it. *)
lemma ctxt_upd_domain: "tcb_domain (ctxt_upd tc tcb) = tcb_domain tcb"
  by simp

(* And the capability slots are untouched, which is what makes the update
   invisible to `caps_of_state` and hence to `domain_sep_inv` and to every
   capability-shaped conjunct of `pas_refined`. *)
lemma ctxt_upd_cap_cases:
  "\<forall>(getF, v) \<in> ran tcb_cap_cases. getF (ctxt_upd tc tcb) = getF tcb"
  by (clarsimp simp: tcb_cap_cases_def)

subsection \<open>What the register-context update preserves\<close>

(* On RISCV64 the hypervisor reference relation is empty for every object
   (`hyp_refs_of_simps`, ArchInvariants_AI.thy:942), so `state_hyp_refs_of` is
   the constantly-empty map and no operation can change it. This is the reason
   l4v's RISCV64 instance of `thread_set_pas_refined` can drop the `tcb_arch`
   assumption that the generic one carries. *)
lemma state_hyp_refs_of_empty: "state_hyp_refs_of (s :: det_state) = (\<lambda>p. {})"
  by (rule ext) (simp add: RISCV64.state_hyp_refs_of_def split: option.splits)

(* Hence any operation preserves it, this one included. *)
lemma thread_set_ctxt_hyp_refs:
  "thread_set (ctxt_upd tc) t \<lbrace>\<lambda>s :: det_state. P (state_hyp_refs_of s)\<rbrace>"
  by (simp add: state_hyp_refs_of_empty, rule hoare_vcg_prop)

(* `pas_refined` survives the update. l4v proves this for RISCV64 as
   `thread_set_pas_refined` (ArchADT_IF.thy:302) -- but inside InfoFlow, and
   the version in the Access session (CNode_AC.thy:1343) additionally assumes
   `tcb_arch (f tcb) = tcb_arch tcb`, which is exactly what this update
   violates. The proof script is reproduced here so that this development does
   not acquire an InfoFlow dependency for a ten-line argument. *)
lemma thread_set_ctxt_pas_refined:
  "thread_set (ctxt_upd tc) t \<lbrace>pas_refined aag\<rbrace>"
  by (wpsimp wp: tcb_domain_map_wellformed_lift_strong thread_set_state_vrefs
                 thread_set_edomains[OF ctxt_upd_domain]
           simp: pas_refined_def state_objs_to_policy_def
      | wps thread_set_caps_of_state_trivial[OF ctxt_upd_cap_cases]
            thread_set_thread_st_auth_trivT[OF ctxt_upd_tcb_state]
            thread_set_thread_bound_ntfns_trivT[OF ctxt_upd_bound_ntfn]
            thread_set_ctxt_hyp_refs)+

(* `invs` survives it. This is l4v's `thread_set_invs_trivial`
   (TcbAcc_AI.thy:463) with its nine side conditions discharged; the same
   discharge appears in l4v's own `kernel_entry_invs` (AInvs.thy:47), which is
   stated only for the `unit` extension and so cannot be reused directly. *)
lemma thread_set_ctxt_invs:
  "thread_set (ctxt_upd tc) t \<lbrace>invs :: det_state \<Rightarrow> bool\<rbrace>"
  by (wp thread_set_invs_trivial | clarsimp simp: tcb_cap_cases_def)+

(* `valid_sched` survives it: the update changes neither the thread state, the
   priority nor the domain, which is all `valid_sched` reads from a TCB. *)
lemma thread_set_ctxt_valid_sched:
  "thread_set (ctxt_upd tc) t \<lbrace>valid_sched :: det_state \<Rightarrow> bool\<rbrace>"
  by (rule thread_set_not_state_valid_sched; simp)

(* `amp_no_domain_cap` survives it, via l4v's `domain_sep_inv` lemma at
   `irqs = True` and the point-free bridge from AMP_Invariant. The instantiation
   is given explicitly because the assumption alone leaves `f` higher-order and
   unification picks the wrong reading. *)
lemma thread_set_ctxt_no_domain_cap:
  "thread_set (ctxt_upd tc) t \<lbrace>amp_no_domain_cap\<rbrace>"
  apply (simp only: domain_sep_inv_True_eq[where st="undefined :: det_state", symmetric])
  apply (rule thread_set_domain_sep_inv_triv[OF ctxt_upd_cap_cases])
  done

(* The remaining conjuncts are about parts of the state a TCB update cannot
   reach at all: the capability derivation list, the scheduler action, and the
   identity of the current thread. *)
crunch thread_set
  for valid_list[wp]: "valid_list :: det_state \<Rightarrow> bool"
  and scheduler_action[wp]: "\<lambda>s :: det_state. P (scheduler_action s)"
  and cur_thread[wp]: "\<lambda>s :: det_state. P (cur_thread s)"

(* The mode-dependent conjunct of `core_inv`. `ct_in_state` is preserved because
   the update does not change any thread's state, and `thread_set` does not move
   the current thread. *)
lemma thread_set_ctxt_ct_in_state:
  "thread_set (ctxt_upd tc) t \<lbrace>ct_in_state P :: det_state \<Rightarrow> bool\<rbrace>"
  by (rule thread_set_ct_in_state) simp

(* And therefore the whole mode-and-event-indexed conjunct, whichever mode it
   is. Kept separate from the preservation theorem below so that the case split
   over the mode happens once, on a small goal. *)
lemma thread_set_ctxt_mode:
  "thread_set (ctxt_upd tc) t
   \<lbrace>\<lambda>s :: det_state.
      case m of UserMode \<Rightarrow> ct_running s
              | IdleMode \<Rightarrow> ct_idle s
              | KernelMode \<Rightarrow> (ct_active s \<or> ct_idle s)
                              \<and> (\<forall>ev. e = Some ev \<longrightarrow> ev \<noteq> Interrupt \<longrightarrow> ct_running s)\<rbrace>"
  by (cases m; simp;
      wpsimp wp: thread_set_ctxt_ct_in_state hoare_vcg_disj_lift
                 hoare_vcg_all_lift hoare_vcg_const_imp_lift)

(* PRESERVATION of the whole per-core invariant across the register-context
   update. Every conjunct is one of the lemmas above; nothing new about the
   kernel is proved here. The point is that the bracket `kernel_entry` puts
   around `call_kernel` does not disturb what `call_kernel_integrity` needs. *)
lemma thread_set_ctxt_core_inv:
  "thread_set (ctxt_upd tc) t \<lbrace>core_inv bp c m e\<rbrace>"
  unfolding core_inv_def schact_is_rct_def
  by (wpsimp wp: thread_set_ctxt_pas_refined thread_set_ctxt_invs
                 thread_set_ctxt_valid_sched thread_set_ctxt_no_domain_cap
                 thread_set_ctxt_mode)

(* And it preserves integrity, provided the thread written to is the subject's
   own -- which it is, since `kernel_entry` writes to `cur_thread` and
   `pas_refined_is_subject_cur_thread` says that is always this core's. *)
lemma thread_set_ctxt_integrity:
  "\<lbrace>\<lambda>s. integrity aag X st s \<and> is_subject aag t\<rbrace>
   thread_set (ctxt_upd tc) t
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  by (wpsimp wp: thread_set_integrity_autarch)

(* The tail of `kernel_entry` reads the register context back out. `thread_get`
   is `gets_the` composed with `return`, so it changes nothing at all. *)
lemma thread_get_pres:
  "thread_get f t \<lbrace>P :: det_state \<Rightarrow> bool\<rbrace>"
  by (wpsimp simp: thread_get_def)

subsection \<open>Integrity of a whole kernel entry\<close>

(* `call_kernel_integrity` is stated relative to the state `call_kernel` starts
   in (`\<lambda>s. s = st` in its precondition). Inside `kernel_entry` that is NOT the
   state the whole entry started in, so the two integrity facts have to be
   composed rather than chained. `integrity_trans_start` (Access_AC.thy:1590) is
   l4v's own tool for exactly this: it turns the reference-state precondition
   into an accumulated `integrity aag X st`. *)
lemma call_kernel_integrity_rel:
  "\<lbrace>\<lambda>s. integrity (amp_pas bp c) {} st s \<and> core_inv bp c KernelMode (Some ev) s\<rbrace>
   (call_kernel ev :: (unit, det_ext) s_monad)
   \<lbrace>\<lambda>_. integrity (amp_pas bp c) {} st\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule integrity_trans_start[where P="core_inv bp c KernelMode (Some ev)"])
   apply (rule hoare_weaken_pre,
          rule call_kernel_integrity[where st'="undefined :: det_state"])
   apply (clarsimp simp: core_inv_def pred_conj_def domain_sep_inv_True_iff
                         RISCV64.valid_cur_hyp_def pas_refined_guarded_pas_domain
                         active_from_running)
   apply (simp add: pas_refined_cur_thread_label)
  apply (simp add: pred_conj_def)
  done

(* INTEGRITY OF A KERNEL CALL, in the form the ADT step needs: from a state
   satisfying the per-core invariant, the whole `kernel_entry` -- context save,
   kernel, context restore -- respects seL4's integrity for this core's PAS with
   an empty globals set. The empty globals set is what makes `trm_globals`
   unfirable in `integrity_imp_amp_step`; `X` is schematic in
   `call_kernel_integrity`, so choosing it costs nothing. *)
lemma kernel_entry_integrity:
  "\<lbrace>\<lambda>s. core_inv bp c KernelMode (Some ev) s \<and> s = st\<rbrace>
   (kernel_entry ev tc :: (user_context, det_ext) s_monad)
   \<lbrace>\<lambda>_. integrity (amp_pas bp c) {} st\<rbrace>"
  unfolding kernel_entry_def
  apply (wp thread_get_pres call_kernel_integrity_rel
            hoare_vcg_conj_lift[OF thread_set_ctxt_integrity thread_set_ctxt_core_inv])
  apply (fastforce simp: core_inv_def dest: pas_refined_is_subject_cur_thread)
  done

(* PRESERVATION across a kernel call, at `kernel_entry` granularity. The mode
   `kernel_call_A` moves to is decided by `ct_running` of the RESULT state, so
   the postcondition is stated in exactly that shape rather than as a
   `core_inv`. *)
lemma kernel_entry_core_inv:
  "\<lbrace>core_inv bp c KernelMode (Some ev)\<rbrace>
   (kernel_entry ev tc :: (user_context, det_ext) s_monad)
   \<lbrace>\<lambda>_ s. pas_refined (amp_pas bp c) s \<and> valid_sched s \<and> valid_list s
          \<and> amp_no_domain_cap s \<and> schact_is_rct s
          \<and> (invs s \<and> (ct_running s \<or> ct_idle s))\<rbrace>"
  unfolding kernel_entry_def
  by (wp thread_get_pres call_kernel_core_inv thread_set_ctxt_core_inv)

subsection \<open>The interrupt poll changes no memory\<close>

(* `check_active_irq` is `do_machine_op (getActiveIRQ False)`, and `getActiveIRQ`
   (MachineOps.thy:132) reads `irq_masks`, increments `irq_state` and consults
   the IRQ oracle. It never writes `underlying_memory`. Proving that outright is
   shorter than obtaining `integrity` for this transition, and gives a stronger
   conclusion: the frames changed are not merely owned, there are none. *)
lemma getActiveIRQ_underlying_memory:
  "(r, ms') \<in> fst (getActiveIRQ b ms) \<Longrightarrow> underlying_memory ms' = underlying_memory ms"
  by (clarsimp simp: RISCV64.getActiveIRQ_def in_monad split: if_splits)

(* Hence the AMP model sees no change at all across an interrupt poll. *)
lemma check_active_irq_mem_proj:
  "\<lbrace>\<lambda>s. P (mem_proj s)\<rbrace>
   (check_active_irq :: (bool, det_ext) s_monad)
   \<lbrace>\<lambda>_ s. P (mem_proj s)\<rbrace>"
  apply (wpsimp simp: check_active_irq_def do_machine_op_def)
  apply (drule getActiveIRQ_underlying_memory)
  apply (erule rsubst[where P=P])
  apply (simp add: mem_proj_def fun_eq_iff)
  done

(* The current thread's state is untouched too: `do_machine_op` cannot reach the
   kernel heap. *)
lemma check_active_irq_ct_in_state:
  "\<lbrace>ct_in_state P :: det_state \<Rightarrow> bool\<rbrace>
   check_active_irq
   \<lbrace>\<lambda>_. ct_in_state P :: det_state \<Rightarrow> bool\<rbrace>"
  by (wpsimp wp: do_machine_op_ct_in_state simp: check_active_irq_def)

(* The mode-and-event conjunct, as for the register-context update above. *)
lemma check_active_irq_mode:
  "(check_active_irq :: (bool, det_ext) s_monad)
   \<lbrace>\<lambda>s. case m of UserMode \<Rightarrow> ct_running s
                | IdleMode \<Rightarrow> ct_idle s
                | KernelMode \<Rightarrow> (ct_active s \<or> ct_idle s)
                                \<and> (\<forall>ev. e = Some ev \<longrightarrow> ev \<noteq> Interrupt \<longrightarrow> ct_running s)\<rbrace>"
  by (cases m; simp;
      wpsimp wp: check_active_irq_ct_in_state hoare_vcg_disj_lift
                 hoare_vcg_all_lift hoare_vcg_const_imp_lift)

(* PRESERVATION of the whole invariant across an interrupt poll, for every mode
   and pending event. `invs` is the one conjunct that is not a crunch, because
   it constrains `machine_state`; l4v has it as `check_active_irq_invs`
   (Move_R.thy:238), reproved in AMP_Invariant. *)
lemma check_active_irq_core_inv:
  "(check_active_irq :: (bool, det_ext) s_monad) \<lbrace>core_inv bp c m e\<rbrace>"
  unfolding core_inv_def schact_is_rct_def
  by (wpsimp wp: check_active_irq_invs_amp check_active_irq_mode)

subsection \<open>Integrity and preservation for a user-mode step\<close>

(* `do_user_op_respects` (ADT_AC.thy:89) already carries `integrity aag X st` in
   its PRECONDITION, so unlike the kernel case it composes with no transitivity
   step. The two other preconditions -- `invs` and `pas_refined` -- are conjuncts
   of `core_inv`, and `is_subject aag \<circ> cur_thread` follows from them. *)
lemma do_user_op_integrity:
  "\<lbrace>\<lambda>s. integrity (amp_pas bp c) {} st s \<and> core_inv bp c UserMode None s\<rbrace>
   (do_user_op uop tc :: (event option \<times> user_context, det_ext) s_monad)
   \<lbrace>\<lambda>_. integrity (amp_pas bp c) {} st\<rbrace>"
  apply (rule hoare_weaken_pre, rule do_user_op_respects)
  apply (fastforce simp: core_inv_def pred_conj_def
                   dest: pas_refined_is_subject_cur_thread)
  done

(* l4v's user-step invariant lemma with its `and`-form postcondition flattened,
   so that one wp rule delivers both halves `core_inv` needs. *)
lemma do_user_op_invs_ct:
  "\<lbrace>\<lambda>s. invs s \<and> ct_running s\<rbrace>
   (do_user_op uop tc :: (event option \<times> user_context, det_ext) s_monad)
   \<lbrace>\<lambda>_ s. invs s \<and> ct_running s\<rbrace>"
  using do_user_op_invs[where f=uop and tc=tc] by (simp add: pred_conj_def)

(* The scheduler-action crunch from AMP_Invariant, in the form `core_inv`
   carries it. *)
lemma do_user_op_schact_is_rct:
  "(do_user_op uop tc :: (event option \<times> user_context, det_ext) s_monad)
   \<lbrace>schact_is_rct\<rbrace>"
  unfolding schact_is_rct_def by (rule do_user_op_scheduler_action)

(* PRESERVATION across a user-mode step. `do_user_op` writes user memory and the
   register context and touches no kernel object, so every capability-shaped
   conjunct comes from the crunches in AMP_Invariant; `invs` and `ct_running`
   come from `do_user_op_invs` (AInvs.thy:92). The conjuncts are lifted
   explicitly, in an order that keeps `invs` next to `ct_running`, because
   splitting those two apart leaves a goal no l4v lemma matches. *)
lemma do_user_op_core_inv:
  "\<lbrace>core_inv bp c UserMode None\<rbrace>
   (do_user_op uop tc :: (event option \<times> user_context, det_ext) s_monad)
   \<lbrace>\<lambda>_. core_inv bp c UserMode None\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule_tac Q'="\<lambda>_ s. pas_refined (amp_pas bp c) s \<and> valid_sched s \<and> valid_list s
                             \<and> amp_no_domain_cap s \<and> schact_is_rct s
                             \<and> (invs s \<and> ct_running s)"
                in hoare_strengthen_post)
    apply (rule hoare_vcg_conj_lift[OF do_user_op_pas_refined
             hoare_vcg_conj_lift[OF do_user_op_valid_sched
               hoare_vcg_conj_lift[OF do_user_op_valid_list
                 hoare_vcg_conj_lift[OF do_user_op_no_domain_cap
                   hoare_vcg_conj_lift[OF do_user_op_schact_is_rct
                                          do_user_op_invs_ct]]]]])
   apply (simp add: core_inv_def)
  apply (simp add: core_inv_def)
  done

subsection \<open>Moving between modes\<close>

(* A state reached from user mode satisfies the invariant at KernelMode for ANY
   pending event: `ct_running` implies both `ct_active \<or> ct_idle` and the
   event-conditional `ct_running` that `core_inv` demands there. This is what
   makes clauses 3 and 4 of `global_automaton` free once clause 2 is done. *)
lemma core_inv_UserMode_KernelMode:
  "core_inv bp c UserMode None s \<Longrightarrow> core_inv bp c KernelMode e s"
  by (fastforce simp: core_inv_def active_from_running)

(* A state reached from idle mode satisfies the invariant at KernelMode when the
   pending event is `Interrupt` -- which is the only event `global_automaton`
   ever raises from idle mode (clause 6). `ct_idle` discharges the first
   conjunct and `Interrupt` makes the second vacuous. *)
lemma core_inv_IdleMode_KernelMode:
  "core_inv bp c IdleMode None s \<Longrightarrow> core_inv bp c KernelMode (Some Interrupt) s"
  by (simp add: core_inv_def)

(* The mode a kernel call lands in is `UserMode` exactly when the resulting
   state is running, and `IdleMode` otherwise; `call_kernel` guarantees the
   state is one or the other, so the invariant holds at whichever mode
   `kernel_call_A` chooses. *)
lemma core_inv_after_kernel_call:
  assumes "pas_refined (amp_pas bp c) s \<and> valid_sched s \<and> valid_list s
           \<and> amp_no_domain_cap s \<and> schact_is_rct s
           \<and> (invs s \<and> (ct_running s \<or> ct_idle s))"
  shows "core_inv bp c (if ct_running s then UserMode else IdleMode) None s"
  using assms by (auto simp: core_inv_def)

section \<open>Results\<close>

subsection \<open>J5 -- every ADT_A step of a core is an amp_step of that core\<close>

(* One transition kind at a time, first. A kernel call: the memory change it
   induces is confined to the core's own frames, and the invariant holds again
   at the mode `kernel_call_A` moves to. This is `kernel_entry_integrity`
   composed with `integrity_imp_amp_step`, plus `kernel_entry_core_inv`. *)
lemma kernel_call_A_amp:
  assumes wf: "amp_partition_wf bp"
      and inv: "core_inv bp c KernelMode (Some ev) s"
      and st: "((tc, s), m, (tc', s')) \<in> kernel_call_A ev"
  shows "amp_step c (mem_proj s) (mem_proj s') bp \<and> core_inv bp c m None s'"
proof -
  from st have run: "(tc', s') \<in> fst (kernel_entry ev tc s)"
           and m: "m = (if ct_running s' then UserMode else IdleMode)"
    by (simp_all add: kernel_call_A_def)
  from inv have pr: "pas_refined (amp_pas bp c) s" by (simp add: core_inv_def)
  have "integrity (amp_pas bp c) {} s s'"
    by (rule use_valid[OF run kernel_entry_integrity[where st=s]]) (simp add: inv)
  from integrity_imp_amp_step[OF wf pas_refined_tcbs_labelled[OF pr] this]
  have "amp_step c (mem_proj s) (mem_proj s') bp" .
  moreover from use_valid[OF run kernel_entry_core_inv inv] m
  have "core_inv bp c m None s'" by (simp add: core_inv_after_kernel_call)
  ultimately show ?thesis by simp
qed

(* A user-mode step: the same shape, discharged by `do_user_op_respects` rather
   than by `call_kernel_integrity`. The invariant is re-established at UserMode,
   from which `core_inv_UserMode_KernelMode` covers the two clauses that move
   into the kernel. *)
lemma do_user_op_A_amp:
  assumes wf: "amp_partition_wf bp"
      and inv: "core_inv bp c UserMode None s"
      and st: "((tc, s), e, (tc', s')) \<in> do_user_op_A uop"
  shows "amp_step c (mem_proj s) (mem_proj s') bp \<and> core_inv bp c UserMode None s'"
proof -
  from st have run: "((e, tc'), s') \<in> fst (do_user_op uop tc s)"
    by (simp add: do_user_op_A_def monad_to_transition_def)
  from inv have pr: "pas_refined (amp_pas bp c) s" by (simp add: core_inv_def)
  have "integrity (amp_pas bp c) {} s s'"
    by (rule use_valid[OF run do_user_op_integrity[where st=s]]) (simp add: inv)
  from integrity_imp_amp_step[OF wf pas_refined_tcbs_labelled[OF pr] this]
  have "amp_step c (mem_proj s) (mem_proj s') bp" .
  moreover from use_valid[OF run do_user_op_core_inv inv]
  have "core_inv bp c UserMode None s'" .
  ultimately show ?thesis by simp
qed

(* An interrupt poll: no memory changes at all, so `amp_step` holds for any
   partition and any core, and the invariant is preserved verbatim. *)
lemma check_active_irq_A_amp:
  assumes inv: "core_inv bp c m e s"
      and st: "((tc, s), irq, (tc', s')) \<in> check_active_irq_A"
  shows "amp_step c (mem_proj s) (mem_proj s') bp \<and> core_inv bp c m e s'"
proof -
  from st have run: "(irq, s') \<in> fst (check_active_irq s)"
    by (fastforce simp: check_active_irq_A_def)
  from use_valid[OF run check_active_irq_mem_proj[where P="\<lambda>m'. m' = mem_proj s"] refl]
  have "mem_proj s' = mem_proj s" .
  hence "amp_step c (mem_proj s) (mem_proj s') bp"
    by (simp add: amp_step_def changed_frames_def)
  moreover from use_valid[OF run check_active_irq_core_inv inv]
  have "core_inv bp c m e s'" .
  ultimately show ?thesis by simp
qed

(* THE RESULT OF THIS THEORY, and the discharge of the plan's item J5.
 *
 * From a global state satisfying the per-core invariant, EVERY step of seL4's
 * abstract system `ADT_A` -- kernel call, user step, interrupt poll, in any of
 * `global_automaton`'s six clauses -- changes only memory this core owns under
 * the declared boot partition, and leaves the invariant standing.
 *
 * `amp_step` is the hypothesis every Phase 2-6 theorem carried. It is now a
 * conclusion, resting on `amp_gs_inv` at boot and on nothing else. *)
theorem amp_step_of_ADT_A:
  assumes wf: "amp_partition_wf bp"
      and inv: "amp_gs_inv bp c gs"
      and step: "(gs, gs') \<in> Step (ADT_A uop) u"
  shows "amp_step c (gs_mem gs) (gs_mem gs') bp \<and> amp_gs_inv bp c gs'"
  using step inv
  apply (simp add: ADT_A_def global_automaton_def)
  apply (elim disjE)
       \<comment> \<open>clause 1: a kernel call, leaving the mode `kernel_call_A` chose\<close>
       apply (clarsimp simp: amp_gs_inv_def gs_mem_def)
       apply (drule (1) kernel_call_A_amp[OF wf], simp)
      \<comment> \<open>clause 2: user to user, no kernel entry\<close>
      apply (clarsimp simp: amp_gs_inv_def gs_mem_def)
      apply (drule (1) do_user_op_A_amp[OF wf], simp)
     \<comment> \<open>clause 3: user to kernel, carrying a real event\<close>
     apply (clarsimp simp: amp_gs_inv_def gs_mem_def)
     apply (drule (1) do_user_op_A_amp[OF wf])
     apply (fastforce intro: core_inv_UserMode_KernelMode)
    \<comment> \<open>clause 4: user to kernel on an interrupt\<close>
    apply (clarsimp simp: amp_gs_inv_def gs_mem_def)
    apply (drule (1) check_active_irq_A_amp)
    apply (fastforce intro: core_inv_UserMode_KernelMode)
   \<comment> \<open>clause 5: idling in idle mode\<close>
   apply (clarsimp simp: amp_gs_inv_def gs_mem_def)
   apply (drule (1) check_active_irq_A_amp, simp)
  \<comment> \<open>clause 6: an interrupt taken while idle\<close>
  apply (clarsimp simp: amp_gs_inv_def gs_mem_def)
  apply (drule (1) check_active_irq_A_amp)
  apply (fastforce intro: core_inv_IdleMode_KernelMode)
  done

section \<open>Examples\<close>

subsection \<open>J6 -- the conclusion is a real constraint, on memory that really changes\<close>

(* NON-VACUITY, the half a green build cannot detect.
 *
 * `amp_step_of_ADT_A` is an implication with a conclusion of the form
 * `changed_frames \<subseteq> owned_frames`. It would be equally green in two useless
 * worlds: one where no step ever changes memory (so `changed_frames` is always
 * empty and the subset holds for the empty reason), and one where
 * `owned_frames` is everything (so the subset is no constraint). The three
 * lemmas below rule both out, on the example two-core partition.
 *
 * What they do NOT establish is stated plainly at the end of this section. *)

(* A single-byte memory write, as a state transformer. This is the smallest
   change `mem_proj` can see, which makes it the sharpest instrument for showing
   that `changed_frames` is neither always empty nor unconstrained. *)
definition mem_upd :: "det_state \<Rightarrow> obj_ref \<Rightarrow> word8 \<Rightarrow> det_state" where
  "mem_upd s p v \<equiv>
     s\<lparr>machine_state := machine_state s
         \<lparr>underlying_memory := (underlying_memory (machine_state s))(p := v)\<rparr>\<rparr>"

(* Writing one byte changes exactly the frame containing it -- not nothing, and
   not everything. Both halves matter: the first is what makes the two teeth
   lemmas below non-empty, the second is what makes the restrictive one bite. *)
lemma changed_frames_mem_upd:
  assumes ne: "underlying_memory (machine_state s) p \<noteq> v"
  shows "changed_frames (mem_proj s) (mem_proj (mem_upd s p v)) = {frame_of p}"
proof (rule set_eqI)
  fix f
  have al: "is_aligned (frame_of p) pageBits"
    by (simp add: frame_of_def is_aligned_neg_mask)
  have lt: "(p AND mask pageBits) < 2 ^ pageBits"
    by (rule and_mask_less') (simp add: RISCV64.pageBits_def)
  have add: "frame_of p + (p AND mask pageBits) = p"
    by (simp add: frame_of_def AND_NOT_mask_plus_AND_mask_eq)
  show "(f \<in> changed_frames (mem_proj s) (mem_proj (mem_upd s p v))) = (f \<in> {frame_of p})"
  proof
    assume "f \<in> changed_frames (mem_proj s) (mem_proj (mem_upd s p v))"
    then obtain off where "is_aligned f pageBits" and "off < 2 ^ pageBits"
      and "underlying_memory (machine_state s) (f + off)
             \<noteq> underlying_memory (machine_state (mem_upd s p v)) (f + off)"
      by (auto simp: changed_frames_mem_proj)
    thus "f \<in> {frame_of p}"
      by (auto simp: mem_upd_def frame_of_aligned_add split: if_splits)
  next
    assume "f \<in> {frame_of p}"
    thus "f \<in> changed_frames (mem_proj s) (mem_proj (mem_upd s p v))"
      unfolding changed_frames_mem_proj
      using al lt ne
      by (auto simp: mem_upd_def add intro!: exI[where x="p AND mask pageBits"])
  qed
qed

(* PERMISSIVE HALF: core 0 may write its own private frame, and doing so really
   does change memory -- `changed_frames` is non-empty. Without this the main
   theorem would be satisfiable by a system in which nothing ever happens. *)
lemma example2_amp_step_changes_own_frame:
  assumes ne: "underlying_memory (machine_state s) 0x1000 \<noteq> v"
  shows "amp_step 0 (mem_proj s) (mem_proj (mem_upd s 0x1000 v)) example2
         \<and> changed_frames (mem_proj s) (mem_proj (mem_upd s 0x1000 v)) \<noteq> {}"
  using changed_frames_mem_upd[OF ne]
  by (simp add: amp_step_def owned_frames_def example2_def core0_res_def
                frame_of_def mask_eq_decr_exp RISCV64.pageBits_def)

(* RESTRICTIVE HALF: the same write to core 1's private frame is NOT an
   `amp_step` of core 0. So the subset in the conclusion is a real constraint on
   real memory, and `amp_step_of_ADT_A` says something a system could fail. *)
lemma example2_amp_step_forbids_other_frame:
  assumes ne: "underlying_memory (machine_state s) 0x3000 \<noteq> v"
  shows "\<not> amp_step 0 (mem_proj s) (mem_proj (mem_upd s 0x3000 v)) example2"
  using changed_frames_mem_upd[OF ne]
  by (simp add: amp_step_def owned_frames_def example2_def core0_res_def core1_res_def
                chan01_def channel_endpoints_def frame_of_def mask_eq_decr_exp
                RISCV64.pageBits_def)

(* And the asymmetry the channel exists for: core 0 -- the SENDER -- may write
   the channel buffer, because `owner_core` labels a buffer by its sender and
   `owned_frames` includes it for both endpoints. Core 1 reading it is covered
   by `amp_vrefs_frame_perm` (AMP_Invariant), which forces its mapping to be
   read-only. *)
lemma example2_amp_step_changes_buffer:
  assumes ne: "underlying_memory (machine_state s) 0x8000 \<noteq> v"
  shows "amp_step 0 (mem_proj s) (mem_proj (mem_upd s 0x8000 v)) example2
         \<and> changed_frames (mem_proj s) (mem_proj (mem_upd s 0x8000 v)) \<noteq> {}"
  using changed_frames_mem_upd[OF ne]
  by (simp add: amp_step_def owned_frames_def example2_def chan01_def
                channel_endpoints_def frame_of_def mask_eq_decr_exp RISCV64.pageBits_def)

text \<open>
  WHAT THESE EXAMPLES DO NOT ESTABLISH, stated plainly rather than left to be
  discovered.

  They show the CONCLUSION of @{thm [source] amp_step_of_ADT_A} is non-vacuous:
  memory changes are visible to @{const changed_frames}, an owned-frame write is
  permitted, and a foreign-frame write is refused. They do NOT exhibit a
  concrete @{typ det_state} satisfying @{const amp_gs_inv}, so they do not by
  themselves rule out the possibility that the HYPOTHESIS is unsatisfiable.

  That gap is not an oversight and it is not deferred work hiding behind a
  green build: it is exactly the boot assumption this theory discloses. Building
  such a witness means building a state satisfying @{const invs}, which l4v
  itself does only in @{text Example_Valid_State.thy} -- 1971 lines, for a
  different labelling, and even there resting on the axiomatised
  @{text akernel_init_invs}. The AMP development inherits that situation rather
  than worsening it, and @{const amp_config} is what makes the assumption
  checkable against a declared boot partition instead of against
  @{const auth_graph_map}. The satisfiability of @{const amp_config}'s own
  clauses is exhibited concretely in AMP_Invariant (@{thm [source]
  example2_sender_owns_buffer}, @{thm [source] example2_receiver_not_own_buffer},
  @{thm [source] example2_receiver_inbuf}); what remains unexhibited is the
  @{const invs} half, which is l4v's, not the AMP tree's.
\<close>

end
