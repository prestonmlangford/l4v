(*
 * Copyright 2026, PolarFire AMP verification.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory AMP_UserData_Refine_Witnesses
imports AMP_UserData_Refine "AInvs.KernelInit_AI" "AInvs.ArchKernelInit_AI" "Refine.KernelInit_R"
  "Refine.EmptyFail_H"
begin

section "Results"

(*
 * Positive witness for call_kernel_user_mem_agrees: its hypotheses are
 * jointly satisfiable, not merely individually plausible. This rests on
 * two things l4v itself has never built without an axiom - both accepted
 * here as a deliberate, recorded decision (2026-07-31), not invented by
 * AMP. See PLAN.md's "Checked initialization" item, which now points back
 * here, for the follow-up: a genuine, non-axiomatic witness would also
 * discharge both gaps below for good.
 *
 * Gap 1 - a concrete invs/invs'-satisfying state pair. init_A_st
 * (spec/abstract/RISCV64/Init_A.thy) is l4v's own hand-built "dummy initial
 * state", and most of what is needed about it is real, non-axiomatic proof:
 * invs_A (proof/invariant-abstract/RISCV64/ArchKernelInit_AI.thy) and
 * valid_list_init / valid_sched_init / valid_domain_list_init
 * (proof/refine/RISCV64/Refine.thy) cover einvs and the domain fields
 * outright, and scheduler_action = resume_cur_thread / domain_time = 15
 * follow directly from init_A_st's definition. What is NOT independently
 * proved is ct_running init_A_st, or anything at all about a matching
 * design-spec state: Init_H (proof/refine/RISCV64/ADT_H.thy) is defined by
 * running the real initKernel boot computation, and nobody has evaluated
 * it. proof/invariant-abstract/KernelInit_AI.thy and
 * proof/refine/RISCV64/KernelInit_R.thy are both headed "Currently
 * axiomatised" for exactly this reason; this witness relies on each of:
 * akernel_init_invs, ckernel_init_invs, ckernel_init_sch_norm,
 * ckernel_init_ctr, ckernel_init_domain_time, init_refinement.
 *
 * Gap 2 - Init_H \<noteq> {}. Every one of those is phrased "for every element
 * of Init_H", which holds vacuously if Init_H is empty. Nothing in l4v
 * states or needs Init_H's nonemptiness, so it is asserted here as an
 * explicit extra hypothesis, named plainly rather than folded silently
 * into that reliance: the claim is exactly "the kernel's boot code
 * produces at least one successful result", which is self-evidently true
 * of the real seL4 boot process but is not, today, a checked l4v fact.
 *
 * Neither gap touches call_kernel_user_mem_agrees itself, which remains
 * free of any such unproven starting point - only this witness, the
 * demonstration that its hypotheses are not vacuous, depends on them.
 *)
lemma pw_call_kernel_user_mem_agrees:
  assumes nonempty: "Init_H \<noteq> {}"
  shows "\<exists>s s' t' r t.
           user_mem s = user_mem' s'
           \<and> (r, t) \<in> fst (call_kernel Interrupt s) \<and> (t, t') \<in> state_relation
           \<and> user_mem t = user_mem' t'"
proof -
  from nonempty obtain tc' s' m' e' where mem: "((tc', s'), m', e') \<in> Init_H"
    by (metis surj_pair equals0I)
  have invs'_s': "invs' s'"
    using ckernel_init_invs mem by fastforce
  have sch_s': "ksSchedulerAction s' = ResumeCurrentThread"
    using ckernel_init_sch_norm[OF mem] .
  have ctr_s': "ct_running' s'"
    using ckernel_init_ctr[OF mem] .
  (*
   * init_A_st is polymorphic in the state extension type (Init_A.thy
   * declares it "'z::state_ext state"); pin it to det_state (the type
   * state_relation and einvs actually need here) once, so every later
   * mention refers to the same monomorphic term instead of each separate
   * "have" independently defaulting its own schematic instance.
   *)
  define abs_s :: det_state where abs_s_def: "abs_s \<equiv> init_A_st"
  have rel: "(abs_s, s') \<in> state_relation"
    using init_refinement mem
    by (fastforce simp: abs_s_def Init_A_def lift_state_relation_def)
  have mem_A: "((empty_context, abs_s), UserMode, None) \<in> Init_A"
    by (simp add: abs_s_def Init_A_def)
  have invs_ctr_s: "invs abs_s \<and> ct_running abs_s"
    using akernel_init_invs[THEN bspec, OF mem_A] by simp
  have invs_s: "invs abs_s" using invs_ctr_s by (rule conjunct1)
  have ctr_s: "ct_running abs_s" using invs_ctr_s by (rule conjunct2)
  (*
   * valid_list_init / valid_sched_init / valid_domain_list_init
   * (proof/refine/RISCV64/Refine.thy) are real, non-axiomatic [simp]
   * lemmas about init_A_st - cited directly rather than re-derived from
   * the raw record, which drags in unrelated fields (kheap, arch_state,
   * ...) and leaves the simplifier stuck on valid_domain_list's own
   * unfolding. Only scheduler_action/domain_time need the raw record
   * (RISCV64.state_defs), and only for those two fields specifically.
   *)
  have valid_list_abs: "valid_list abs_s"
    using valid_list_init by (simp add: abs_s_def)
  have valid_sched_abs: "valid_sched abs_s"
    using valid_sched_init by (simp add: abs_s_def)
  have valid_domain_list_abs: "valid_domain_list abs_s"
    using valid_domain_list_init by (simp add: abs_s_def)
  have sched_abs: "scheduler_action abs_s = resume_cur_thread"
    by (simp add: abs_s_def RISCV64.state_defs)
  have dt_abs: "0 < domain_time abs_s"
    by (simp add: abs_s_def RISCV64.state_defs)
  have preA: "(einvs and (\<lambda>s. Interrupt \<noteq> Interrupt \<longrightarrow> ct_running s) and (ct_running or ct_idle)
               and (\<lambda>s. scheduler_action s = resume_cur_thread)
               and (\<lambda>s. 0 < domain_time s \<and> valid_domain_list s)) abs_s"
    using invs_s ctr_s valid_list_abs valid_sched_abs valid_domain_list_abs sched_abs dt_abs
    by (simp add: pred_conj_def)
  have preH: "(invs' and (\<lambda>s. Interrupt \<noteq> Interrupt \<longrightarrow> ct_running' s) and (ct_running' or ct_idle')
               and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)) s'"
    using invs'_s' ctr_s' sch_s' by (simp add: pred_conj_def)
  (* Sequential OF chaining throughout - see AMP_UserData_Refine.thy's
     comment on why a single combined OF list is dramatically slower here. *)
  note cud0 = corres_underlyingD[OF kernel_corres[of Interrupt]]
  note cud1 = cud0[OF rel]
  note cud2 = cud1[OF preA]
  note cud3 = cud2[OF preH]
  have not_fail: "\<not> snd (callKernel Interrupt s')"
    using cud3 by simp
  have "fst (callKernel Interrupt s') \<noteq> {}"
    using not_fail callKernel_empty_fail by (fastforce simp add: empty_fail_def)
  then obtain r' t' where exec: "(r', t') \<in> fst (callKernel Interrupt s')"
    by fastforce
  note ckuma0 = call_kernel_user_mem_agrees[OF rel]
  note ckuma1 = ckuma0[OF preA]
  note ckuma2 = ckuma1[OF preH]
  show ?thesis using ckuma2[OF exec] by blast
qed

end
