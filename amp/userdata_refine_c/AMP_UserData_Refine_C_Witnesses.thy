(*
 * Copyright 2026, PolarFire AMP verification.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory AMP_UserData_Refine_C_Witnesses
imports AMP_UserData_Refine_C "AInvs.KernelInit_AI" "AInvs.ArchKernelInit_AI" "Refine.KernelInit_R"
begin

context kernel_m
begin

section "Results"

(*
 * Positive witness for kernel_entry_user_mem_C_agrees: its hypotheses are
 * jointly satisfiable. This rests on everything
 * pw_call_kernel_user_mem_agrees already rests on
 * (AMP_UserData_Refine_Witnesses.thy) - the same Init_H-derived
 * design-spec state s', with the same two recorded gaps - plus one
 * further gap this witness introduces itself, recorded here rather than
 * folded silently in.
 *
 * Gap 3 - a concrete C state, related to s' by rf_sr, that kernelEntry_C
 * actually executes from. l4v gives no way to construct this. Init_C'
 * (proof/crefine/RISCV64/ADT_C.thy) is a bare, uninterpreted signature --
 * unlike Init_H (built from the real initKernel computation, with
 * axiomatized properties), Init_C' has no defining content at all, so
 * there is nothing to point at to justify an "Init_C is nonempty" claim;
 * it would be a placeholder for work nobody has started, not a believable
 * real-world fact the way Init_H \<noteq> {} is. Separately, showing kernelEntry_C
 * actually produces a result (not just "does not fail", which
 * entry_refinement_C already gives) would need an empty_fail fact for its
 * AutoCorres-generated C-level primitives (setTCBContext_C, callKernel_C,
 * getContext_C) - no such fact exists in l4v today; proving one would be
 * new work of the same shape as EmptyFail_H.thy's existing
 * callKernel_empty_fail, one layer further down. c_level_entry_exists
 * below states plainly what both of those jointly amount to, as one
 * explicit hypothesis, rather than hiding either inside a derivation. See
 * PLAN.md's "Checked initialization", which now points back here too.
 *)
(* The lemma named pw_kernel_entry_user_mem_C_agrees: *)
lemma pw_kernel_entry_user_mem_C_agrees:
  (* Assume: Init_H has at least one element. *)
  assumes nonempty: "Init_H \<noteq> {}"
  (*
   * Assume: for every design-spec state s' that is some element of
   * Init_H's design-spec component, there is a C state t related to s' by
   * rf_sr, and some initial context tc, such that running kernelEntry_C on
   * Interrupt from t actually produces a result.
   *)
  assumes c_level_entry_exists:
    "\<forall>s'. (\<exists>tc0 m' e'. ((tc0, s'), m', e') \<in> Init_H) \<longrightarrow>
     (\<exists>t tc tc' t'. (s', t) \<in> rf_sr \<and> (tc', t') \<in> fst (kernelEntry_C False Interrupt tc t))"
  (*
   * Conclusion: the design-spec and C UserData memory agree at some real
   * s and t; and there exists a design-spec execution of kernelEntry on
   * Interrupt from s, with the same result tc' and some end state s', such
   * that s' is related to t' by rf_sr; and s''s UserData memory agrees
   * with t'.
   *)
  shows "\<exists>s t tc tc' t'.
           user_mem_C (globals t) = user_mem' s
           \<and> (tc', t') \<in> fst (kernelEntry_C False Interrupt tc t)
           \<and> (\<exists>s'. (tc', s') \<in> fst (kernelEntry Interrupt tc s) \<and> (s', t') \<in> rf_sr
                     \<and> user_mem_C (globals t') = user_mem' s')"
(* Begin a structured proof. *)
proof -
  (* Obtain: some design-spec state s' (with surrounding tuple components), such that ((tc0, s'), m', e') is an element of Init_H; *)
  from nonempty obtain tc0 s' m' e' where mem: "((tc0, s'), m', e') \<in> Init_H"
  (* ...from Init_H being nonempty, closed automatically. *)
    by (metis surj_pair equals0I)
  (* Derive: s' satisfies invs'; *)
  have invs'_s': "invs' s'"
  (* ...from ckernel_init_invs applied to mem. *)
    using ckernel_init_invs mem by fastforce
  (* Derive: s''s scheduler action is ResumeCurrentThread; *)
  have sch_s': "ksSchedulerAction s' = ResumeCurrentThread"
  (* ...from ckernel_init_sch_norm applied to mem. *)
    using ckernel_init_sch_norm[OF mem] .
  (* Derive: s''s current thread is running; *)
  have ctr_s': "ct_running' s'"
  (* ...from ckernel_init_ctr applied to mem. *)
    using ckernel_init_ctr[OF mem] .
  (* Derive: s''s domain time is nonzero; *)
  have dt_s': "ksDomainTime s' \<noteq> 0"
  (* ...from ckernel_init_domain_time applied to mem. *)
    using ckernel_init_domain_time[OF mem] .

  (* Name abs_s: init_A_st, pinned to det_state - see AMP_UserData_Refine_Witnesses.thy's identical comment on why. *)
  define abs_s :: det_state where abs_s_def: "abs_s \<equiv> init_A_st"
  (* Derive: abs_s and s' are related by state_relation; *)
  have rel: "(abs_s, s') \<in> state_relation"
  (* ...from init_refinement and mem. *)
    using init_refinement mem
    by (fastforce simp: abs_s_def Init_A_def lift_state_relation_def)
  (* Derive: abs_s, with an empty initial context and UserMode, is an element of Init_A; *)
  have mem_A: "((empty_context, abs_s), UserMode, None) \<in> Init_A"
  (* ...from abs_s's definition, closed automatically. *)
    by (simp add: abs_s_def Init_A_def)
  (* Derive: abs_s satisfies invs, and its current thread is running; *)
  have invs_ctr_s: "invs abs_s \<and> ct_running abs_s"
  (* ...from akernel_init_invs applied to mem_A. *)
    using akernel_init_invs[THEN bspec, OF mem_A] by simp
  (* Derive: abs_s satisfies invs; *)
  have invs_s: "invs abs_s" using invs_ctr_s by (rule conjunct1)
  (* Derive: abs_s's current thread is running; *)
  have ctr_s: "ct_running abs_s" using invs_ctr_s by (rule conjunct2)
  (* Derive: abs_s satisfies valid_list; *)
  have valid_list_abs: "valid_list abs_s"
  (* ...from valid_list_init. *)
    using valid_list_init by (simp add: abs_s_def)
  (* Derive: abs_s satisfies valid_sched; *)
  have valid_sched_abs: "valid_sched abs_s"
  (* ...from valid_sched_init. *)
    using valid_sched_init by (simp add: abs_s_def)
  (* Derive: abs_s satisfies valid_domain_list; *)
  have valid_domain_list_abs: "valid_domain_list abs_s"
  (* ...from valid_domain_list_init. *)
    using valid_domain_list_init by (simp add: abs_s_def)
  (* Derive: abs_s's scheduler action is resume_cur_thread; *)
  have sched_abs: "scheduler_action abs_s = resume_cur_thread"
  (* ...from abs_s's definition and the raw initial-state record. *)
    by (simp add: abs_s_def RISCV64.state_defs)
  (* Derive: abs_s's domain time is positive; *)
  have dt_abs: "0 < domain_time abs_s"
  (* ...from abs_s's definition and the raw initial-state record. *)
    by (simp add: abs_s_def RISCV64.state_defs)
  (* Derive: abs_s's domain time is nonzero - all_invs' needs this shape, not "0 <". *)
  have dt_abs_neq: "domain_time abs_s \<noteq> 0"
  (* ...from dt_abs. *)
    using dt_abs by simp

  (* Derive: s' satisfies all_invs' for Interrupt; *)
  have all_invs'_s': "all_invs' Interrupt s'"
  (* ...unfolding all_invs', witnessed by abs_s, from every fact gathered above. *)
    unfolding all_invs'_def
    apply (rule exI[where x=abs_s])
    using rel invs_s ctr_s valid_list_abs valid_sched_abs valid_domain_list_abs sched_abs dt_abs_neq
          invs'_s' ctr_s' sch_s' dt_s'
    by (fastforce simp: pred_conj_def)

  (* Obtain: some C state t related to s' by rf_sr, some initial context tc, and a real result (tc', t') of running kernelEntry_C on Interrupt from t; *)
  obtain t tc tc' t' where
    rel_C: "(s', t) \<in> rf_sr" and
    exec: "(tc', t') \<in> fst (kernelEntry_C False Interrupt tc t)"
  (* ...from c_level_entry_exists applied to mem, closed automatically. *)
    using c_level_entry_exists mem by blast

  (* Name keumca0: kernel_entry_user_mem_C_agrees, with its all_invs'/rf_sr/fastpath premises fixed to all_invs'_s', rel_C, and refl. *)
  note keumca0 = kernel_entry_user_mem_C_agrees[OF all_invs'_s' rel_C refl]
  (* Name keumca1: keumca0, with its execution premise fixed to exec. *)
  note keumca1 = keumca0[OF exec]

  (* Conclude the goal from rel_C, exec, and keumca1, closed automatically. *)
  show ?thesis using rel_C exec keumca1 by blast
(* End the proof. *)
qed

end

end
