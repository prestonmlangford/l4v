(*
 * Copyright 2026, PolarFire AMP verification.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory AMP_UserData_Refine_Witnesses
imports AMP_UserData_Refine "AInvs.KernelInit_AI" "AInvs.ArchKernelInit_AI" "Refine.KernelInit_R"
  "Refine.EmptyFail_H" "AMP_UserData.AMP_UserData"
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

(*
 * Extends l4v: kernelEntry (proof/refine/RISCV64/ADT_H.thy) never yields an
 * empty result set, the same way callKernel already doesn't
 * (callKernel_empty_fail, Refine.EmptyFail_H). kernelEntry only wraps
 * callKernel in a getCurThread/threadSet/threadGet save-restore, and each
 * of those is already known empty_fail - the same reasoning
 * EmptyFail_H.thy itself already uses to get callKernel_empty_fail from
 * its own subfunctions.
 *)
crunch kernelEntry
  for (empty_fail) empty_fail
  (wp: callKernel_empty_fail)

(*
 * Positive witness for kernel_entry_user_mem_agrees: its hypotheses are
 * jointly satisfiable. Reuses the same Init_H-derived abstract/design-spec
 * state pair pw_call_kernel_user_mem_agrees builds above (same two gaps,
 * same abs_s), then derives a real kernelEntry execution the same way that
 * witness derived a real callKernel execution - entry_corres in place of
 * kernel_corres, kernelEntry_empty_fail in place of callKernel_empty_fail.
 *)
lemma pw_kernel_entry_user_mem_agrees:
  assumes nonempty: "Init_H \<noteq> {}"
  shows "\<exists>s s' tc tc' t'.
           user_mem s = user_mem' s'
           \<and> (\<exists>t. (tc', t) \<in> fst (kernel_entry Interrupt tc s) \<and> (t, t') \<in> state_relation
                   \<and> user_mem t = user_mem' t')"
proof -
  from nonempty obtain tc0 s' m' e' where mem: "((tc0, s'), m', e') \<in> Init_H"
    by (metis surj_pair equals0I)
  have invs'_s': "invs' s'"
    using ckernel_init_invs mem by fastforce
  have sch_s': "ksSchedulerAction s' = ResumeCurrentThread"
    using ckernel_init_sch_norm[OF mem] .
  have ctr_s': "ct_running' s'"
    using ckernel_init_ctr[OF mem] .
  have dt_s': "ksDomainTime s' \<noteq> 0"
    using ckernel_init_domain_time[OF mem] .

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
  (* kernel_entry_user_mem_agrees's preH needs domain_time positive too - call_kernel_user_mem_agrees's did not. *)
  have dt_s'_pos: "0 < ksDomainTime s'"
    using dt_s' by (simp add: word_neq_0_conv)
  have preA: "(einvs and (\<lambda>s. Interrupt \<noteq> Interrupt \<longrightarrow> ct_running s) and (ct_running or ct_idle)
               and (\<lambda>s. scheduler_action s = resume_cur_thread)
               and (\<lambda>s. 0 < domain_time s \<and> valid_domain_list s)) abs_s"
    using invs_s ctr_s valid_list_abs valid_sched_abs valid_domain_list_abs sched_abs dt_abs
    by (simp add: pred_conj_def)
  have preH: "(invs' and (\<lambda>s. Interrupt \<noteq> Interrupt \<longrightarrow> ct_running' s) and (ct_running' or ct_idle')
               and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
               and (\<lambda>s. 0 < ksDomainTime s)) s'"
    using invs'_s' ctr_s' sch_s' dt_s'_pos by (simp add: pred_conj_def)

  (* entry_corres needs its own precondition shapes, reshaped from preA/preH the same way AMP_UserData_Refine.thy's own kernel_entry_user_mem_agrees proof does. *)
  have preA_entry: "(einvs and (\<lambda>s. Interrupt \<noteq> Interrupt \<longrightarrow> ct_running s)
                     and (\<lambda>s. 0 < domain_time s) and valid_domain_list and (ct_running or ct_idle)
                     and (\<lambda>s. scheduler_action s = resume_cur_thread)) abs_s"
    using preA by (auto simp add: pred_conj_def)
  have preH_ec: "(invs' and (\<lambda>s. Interrupt \<noteq> Interrupt \<longrightarrow> ct_running' s)
                  and (\<lambda>s. 0 < ksDomainTime s) and (ct_running' or ct_idle')
                  and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)) s'"
    using preH by (auto simp add: pred_conj_def)

  note ec0 = corres_underlyingD[OF entry_corres[of Interrupt empty_context]]
  note ec1 = ec0[OF rel]
  note ec2 = ec1[OF preA_entry]
  note ec3 = ec2[OF preH_ec]
  have not_fail: "\<not> snd (kernelEntry Interrupt empty_context s')"
    using ec3 by simp
  have "fst (kernelEntry Interrupt empty_context s') \<noteq> {}"
    using not_fail kernelEntry_empty_fail by (fastforce simp add: empty_fail_def)
  then obtain tc' t' where exec: "(tc', t') \<in> fst (kernelEntry Interrupt empty_context s')"
    by fastforce

  note keuma0 = kernel_entry_user_mem_agrees[OF rel]
  note keuma1 = keuma0[OF preA]
  note keuma2 = keuma1[OF preH]
  show ?thesis using keuma2[OF exec] by blast
qed

(*
 * Positive witness for kernel_entry_mem_unauthorized_unchanged
 * (AMP_UserData.thy, session AMP_UserData) - lives here, not in
 * AMP_UserData_Witnesses.thy, because it needs a real kernel_entry
 * execution, and AMP_UserData's own session (built on Access only,
 * deliberately Refine-free) has no way to exhibit one: no abstract-level
 * no_fail fact for kernel_entry/call_kernel is proved or cited anywhere in
 * l4v, so the only route available anywhere is the one just above -
 * derive a real kernelEntry execution, then take the abstract execution
 * kernel_entry_user_mem_agrees's own existential conclusion already gives
 * for it. check-witness.sh pairs a witness with its theorem by name alone,
 * scanning every AMP theory together, so this placement is structurally
 * fine; see AMP_UserData_Refine's ROOT entry for the session-level note.
 *
 * Reuses the same Init_H-derived state and the same two gaps as
 * pw_call_kernel_user_mem_agrees, plus a Gap 4 of the same shape
 * AMP_UserData_Confinement_C_Witnesses.thy already carries: no checked l4v
 * state has ever had a policy aag checked against it, so aag, x, st'' and
 * the eight conditions on them are free parameters here too, named
 * plainly as extra hypotheses rather than invented.
 *)
lemma pw_kernel_entry_mem_unauthorized_unchanged:
  assumes nonempty: "Init_H \<noteq> {}"
  assumes pas0: "pas_refined aag (init_A_st :: det_state)"
  assumes gpd0: "guarded_pas_domain aag (init_A_st :: det_state)"
  assumes dsi0: "domain_sep_inv (pasMaySendIrqs aag) st'' (init_A_st :: det_state)"
  assumes owns0: "ct_active (init_A_st :: det_state) \<longrightarrow> is_subject aag (cur_thread (init_A_st :: det_state))"
  assumes may1: "pasMayActivate aag"
  assumes may2: "pasMayEditReadyQueues aag"
  assumes not_owned: "pasObjectAbs aag x \<noteq> pasSubject aag"
  assumes not_written: "\<not> aag_subjects_have_auth_to {pasSubject aag} aag Write x"
  assumes reach_ipc0: "\<forall>tc tc0 sA' p'. (tc0, sA') \<in> fst (kernel_entry Interrupt tc (init_A_st :: det_state)) \<longrightarrow>
                        \<not> (case_option False can_receive_ipc (tcb_states_of_state (init_A_st :: det_state) p')
                           \<and> tcb_states_of_state sA' p' = Some Structures_A.thread_state.Running
                           \<and> x \<in> auth_ipc_buffers (init_A_st :: det_state) p')"
  shows "\<exists>tc tc' s'.
           (tc', s') \<in> fst (kernel_entry Interrupt tc (init_A_st :: det_state))
           \<and> underlying_memory (machine_state (init_A_st :: det_state)) x
             = underlying_memory (machine_state s') x"
proof -
  from nonempty obtain tc0 s' m' e' where mem: "((tc0, s'), m', e') \<in> Init_H"
    by (metis surj_pair equals0I)
  have invs'_s': "invs' s'"
    using ckernel_init_invs mem by fastforce
  have sch_s': "ksSchedulerAction s' = ResumeCurrentThread"
    using ckernel_init_sch_norm[OF mem] .
  have ctr_s': "ct_running' s'"
    using ckernel_init_ctr[OF mem] .
  have dt_s': "ksDomainTime s' \<noteq> 0"
    using ckernel_init_domain_time[OF mem] .

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
  have dt_s'_pos: "0 < ksDomainTime s'"
    using dt_s' by (simp add: word_neq_0_conv)
  have preA: "(einvs and (\<lambda>s. Interrupt \<noteq> Interrupt \<longrightarrow> ct_running s) and (ct_running or ct_idle)
               and (\<lambda>s. scheduler_action s = resume_cur_thread)
               and (\<lambda>s. 0 < domain_time s \<and> valid_domain_list s)) abs_s"
    using invs_s ctr_s valid_list_abs valid_sched_abs valid_domain_list_abs sched_abs dt_abs
    by (simp add: pred_conj_def)
  have preH: "(invs' and (\<lambda>s. Interrupt \<noteq> Interrupt \<longrightarrow> ct_running' s) and (ct_running' or ct_idle')
               and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
               and (\<lambda>s. 0 < ksDomainTime s)) s'"
    using invs'_s' ctr_s' sch_s' dt_s'_pos by (simp add: pred_conj_def)
  have preA_entry: "(einvs and (\<lambda>s. Interrupt \<noteq> Interrupt \<longrightarrow> ct_running s)
                     and (\<lambda>s. 0 < domain_time s) and valid_domain_list and (ct_running or ct_idle)
                     and (\<lambda>s. scheduler_action s = resume_cur_thread)) abs_s"
    using preA by (auto simp add: pred_conj_def)
  have preH_ec: "(invs' and (\<lambda>s. Interrupt \<noteq> Interrupt \<longrightarrow> ct_running' s)
                  and (\<lambda>s. 0 < ksDomainTime s) and (ct_running' or ct_idle')
                  and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)) s'"
    using preH by (auto simp add: pred_conj_def)

  (* Derive a real kernelEntry execution, the same way pw_kernel_entry_user_mem_agrees does above. *)
  note ec0 = corres_underlyingD[OF entry_corres[of Interrupt empty_context]]
  note ec1 = ec0[OF rel]
  note ec2 = ec1[OF preA_entry]
  note ec3 = ec2[OF preH_ec]
  have not_fail: "\<not> snd (kernelEntry Interrupt empty_context s')"
    using ec3 by simp
  have "fst (kernelEntry Interrupt empty_context s') \<noteq> {}"
    using not_fail kernelEntry_empty_fail by (fastforce simp add: empty_fail_def)
  then obtain tc' t' where exec: "(tc', t') \<in> fst (kernelEntry Interrupt empty_context s')"
    by fastforce

  (* Take the abstract execution kernel_entry_user_mem_agrees's own existential conclusion already gives for exec, rather than deriving one independently. *)
  note keuma0 = kernel_entry_user_mem_agrees[OF rel]
  note keuma1 = keuma0[OF preA]
  note keuma2 = keuma1[OF preH]
  obtain sA' where stepA: "(tc', sA') \<in> fst (kernel_entry Interrupt empty_context abs_s)"
    using keuma2[OF exec] by blast

  have einv: "einvs abs_s"
    using invs_s valid_list_abs valid_sched_abs by (simp add: pred_conj_def)
  have hyp: "valid_cur_hyp abs_s"
    by (simp add: RISCV64.valid_cur_hyp_def)
  have sched': "schact_is_rct abs_s"
    using sched_abs by (simp add: schact_is_rct_def)
  have actidle: "ct_active abs_s \<or> ct_idle abs_s"
    using ctr_s by (auto simp: ct_in_state_def st_tcb_at_def obj_at_def)
  have not_ipc: "\<And>p'. \<not> (case_option False can_receive_ipc (tcb_states_of_state abs_s p')
                          \<and> tcb_states_of_state sA' p' = Some Structures_A.thread_state.Running
                          \<and> x \<in> auth_ipc_buffers abs_s p')"
    using reach_ipc0[rule_format, OF stepA[unfolded abs_s_def]] by (simp add: abs_s_def)

  have pas: "pas_refined aag abs_s" using pas0 by (simp add: abs_s_def)
  have gpd: "guarded_pas_domain aag abs_s" using gpd0 by (simp add: abs_s_def)
  have dsi: "domain_sep_inv (pasMaySendIrqs aag) st'' abs_s" using dsi0 by (simp add: abs_s_def)
  have owns: "ct_active abs_s \<longrightarrow> is_subject aag (cur_thread abs_s)" using owns0 by (simp add: abs_s_def)
  (* Interrupt \<noteq> Interrupt is False, so this holds vacuously; x \<notin> X is witnessed by fixing X = {}. *)
  have act: "Interrupt \<noteq> Interrupt \<longrightarrow> ct_active abs_s" by simp
  have not_global: "x \<notin> ({} :: obj_ref set)" by simp

  have main: "underlying_memory (machine_state abs_s) x = underlying_memory (machine_state sA') x"
    by (rule kernel_entry_mem_unauthorized_unchanged
          [OF pas einv hyp act actidle sched' gpd dsi owns may1 may2 stepA
              not_owned not_written not_global not_ipc])

  show ?thesis
    using stepA main by (fastforce simp: abs_s_def)
qed

end
