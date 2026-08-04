(*
 * Copyright 2026, PolarFire AMP verification.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory AMP_UserData_Confinement_C_Witnesses
imports "AMP_UserData_Confinement_C.AMP_UserData_Confinement_C" "AInvs.KernelInit_AI" "AInvs.ArchKernelInit_AI" "Refine.KernelInit_R"
begin

context kernel_m
begin

section "Results"

(*
 * Positive witness for kernel_entry_user_mem_C_unauthorized_unchanged.
 *
 * Gaps 1-3 below are exactly the ones pw_call_kernel_user_mem_agrees
 * (AMP_UserData_Refine_Witnesses.thy) and pw_kernel_entry_user_mem_C_agrees
 * (AMP_UserData_Refine_C_Witnesses.thy) already carry; this witness reuses
 * the same Init_H-derived abstract/design-spec/C state triple (abs_s =
 * init_A_st, related to some s' \<in> Init_H's design-spec component, related
 * in turn to some C state) and inherits them unchanged - see those two
 * files' own comments for the full account. In short: Gap 1 is
 * Init_H \<noteq> {}; Gap 2 is akernel_init_invs/ckernel_init_invs/
 * ckernel_init_sch_norm/ckernel_init_ctr/ckernel_init_domain_time/
 * init_refinement all being axiomatised in l4v itself, not derived; Gap 3
 * is Init_C' having no defining content, so a real C boot state cannot be
 * constructed, only assumed to exist via c_level_entry_exists.
 *
 * Gap 4 - new here - is a checked state with a real mapped UserData frame,
 * and an access-control policy checked against it. This theorem's extra
 * hypotheses beyond kernel_entry_user_mem_C_agrees (pas_refined,
 * guarded_pas_domain, domain_sep_inv, the ownership/activation side
 * conditions, not_owned, not_written, reach_ipc, frame_before, frame_after)
 * need a concrete policy aag and address x, checked against init_A_st,
 * with at least one UserData frame actually mapped there. init_A_st
 * (spec/abstract/RISCV64/Init_A.thy) - the only initial abstract state
 * Gaps 1-3 above are built around, and the only state currently known to
 * be state_relation-related to any element of Init_H - has none: its
 * kheap (init_kheap, same file) holds only the idle thread's TCB, the
 * interrupt CNodes, and the global page table. No aag has ever been
 * checked against it either. Frame carving is a root-task (userspace) job
 * in seL4, not part of kernel boot, so this is not a proof gap so much as
 * a fact about what boot alone establishes - a genuine witness needs a
 * checked state further along than anything currently in l4v's
 * initialization story (see PLAN.md's "Checked initialization", which
 * this witness's comment now also points back to). aag/x/st'' are left as
 * free parameters of this lemma, and the eight conditions below are
 * ordinary named hypotheses on them - exactly the same shape as Gaps 1-3
 * above, naming what is missing plainly rather than bundling it into an
 * existential that would need its own destructuring.
 *
 * valid_cur_hyp and schact_is_rct are not among those eight: neither
 * depends on aag, and both are already available without it -
 * valid_cur_hyp is unconditionally True (RISCV64.valid_cur_hyp_def) and
 * schact_is_rct abs_s unfolds to exactly scheduler_action abs_s =
 * resume_cur_thread, already established non-axiomatically as sched_abs
 * below.
 *)
(* The lemma named pw_kernel_entry_user_mem_C_unauthorized_unchanged: *)
lemma pw_kernel_entry_user_mem_C_unauthorized_unchanged:
  (* Assume: Init_H has at least one element. *)
  assumes nonempty: "Init_H \<noteq> {}"
  (* Assume: for every design-spec state that is some element of Init_H's design-spec component, a real C-level kernelEntry_C execution exists from some rf_sr-related C state. *)
  assumes c_level_entry_exists:
    "\<forall>s'. (\<exists>tc0 m' e'. ((tc0, s'), m', e') \<in> Init_H) \<longrightarrow>
     (\<exists>t tc tc' t'. (s', t) \<in> rf_sr \<and> (tc', t') \<in> fst (kernelEntry_C False Interrupt tc t))"
  (* Assume: aag, x, st'' make init_A_st pas_refined, guarded, and domain-separation-respecting. *)
  assumes pas0: "pas_refined aag (init_A_st :: det_state)"
  assumes gpd0: "guarded_pas_domain aag (init_A_st :: det_state)"
  assumes dsi0: "domain_sep_inv (pasMaySendIrqs aag) st'' (init_A_st :: det_state)"
  (* Assume: if init_A_st's current thread is active, the subject owns it; and the subject may activate threads and edit ready queues. *)
  assumes owns0: "ct_active (init_A_st :: det_state) \<longrightarrow> is_subject aag (cur_thread (init_A_st :: det_state))"
  assumes may1: "pasMayActivate aag"
  assumes may2: "pasMayEditReadyQueues aag"
  (* Assume: x is owned by no one but the calling subject, and carries no Write authority. *)
  assumes not_owned: "pasObjectAbs aag x \<noteq> pasSubject aag"
  assumes not_written: "\<not> aag_subjects_have_auth_to {pasSubject aag} aag Write x"
  (* Assume: on every abstract outcome reachable by kernel_entry on Interrupt from init_A_st, from any initial register context, x is not a live IPC-buffer target, and remains a mapped user-data word. *)
  assumes reach_ipc0: "\<forall>tc tc0 sA' p'. (tc0, sA') \<in> fst (kernel_entry Interrupt tc (init_A_st :: det_state)) \<longrightarrow>
                        \<not> (case_option False can_receive_ipc (tcb_states_of_state (init_A_st :: det_state) p')
                           \<and> tcb_states_of_state sA' p' = Some Structures_A.thread_state.Running
                           \<and> x \<in> auth_ipc_buffers (init_A_st :: det_state) p')"
  assumes frame_before0: "in_user_frame x (init_A_st :: det_state)"
  assumes frame_after0: "\<forall>tc tc0 sA'. (tc0, sA') \<in> fst (kernel_entry Interrupt tc (init_A_st :: det_state)) \<longrightarrow> in_user_frame x sA'"
  (* Conclusion: some real C-level kernelEntry_C step leaves some word's C-level memory content unchanged. *)
  shows "\<exists>tC tc tc' tC' x.
           (tc', tC') \<in> fst (kernelEntry_C False Interrupt tc tC)
           \<and> user_mem_C (globals tC) x = user_mem_C (globals tC') x"
proof -
  (* Obtain: some design-spec state s' (with surrounding tuple components), such that ((tc0, s'), m', e') is an element of Init_H; *)
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
  have dt_abs_neq: "domain_time abs_s \<noteq> 0"
    using dt_abs by simp

  have all_invs'_s': "all_invs' Interrupt s'"
    unfolding all_invs'_def
    apply (rule exI[where x=abs_s])
    using rel invs_s ctr_s valid_list_abs valid_sched_abs valid_domain_list_abs sched_abs dt_abs_neq
          invs'_s' ctr_s' sch_s' dt_s'
    by (fastforce simp: pred_conj_def)

  obtain tC tc tc' tC' where
    rel_C: "(s', tC) \<in> rf_sr" and
    exec_C: "(tc', tC') \<in> fst (kernelEntry_C False Interrupt tc tC)"
    using c_level_entry_exists mem by blast

  (* Carry each Gap-4 fact over to abs_s (definitionally the same state as init_A_st). *)
  have pas: "pas_refined aag abs_s" using pas0 by (simp add: abs_s_def)
  have gpd: "guarded_pas_domain aag abs_s" using gpd0 by (simp add: abs_s_def)
  have dsi: "domain_sep_inv (pasMaySendIrqs aag) st'' abs_s" using dsi0 by (simp add: abs_s_def)
  have owns: "ct_active abs_s \<longrightarrow> is_subject aag (cur_thread abs_s)" using owns0 by (simp add: abs_s_def)
  have reach_ipc: "\<And>tc0 sA' p'. (tc0, sA') \<in> fst (kernel_entry Interrupt tc abs_s) \<Longrightarrow>
                    \<not> (case_option False can_receive_ipc (tcb_states_of_state abs_s p')
                       \<and> tcb_states_of_state sA' p' = Some Structures_A.thread_state.Running
                       \<and> x \<in> auth_ipc_buffers abs_s p')"
  proof -
    fix tc0 sA' p'
    assume a: "(tc0, sA') \<in> fst (kernel_entry Interrupt tc abs_s)"
    show "\<not> (case_option False can_receive_ipc (tcb_states_of_state abs_s p')
             \<and> tcb_states_of_state sA' p' = Some Structures_A.thread_state.Running
             \<and> x \<in> auth_ipc_buffers abs_s p')"
      using reach_ipc0 a by (simp add: abs_s_def)
  qed
  have frame_before: "in_user_frame x abs_s" using frame_before0 by (simp add: abs_s_def)
  have frame_after: "\<And>tc0 sA'. (tc0, sA') \<in> fst (kernel_entry Interrupt tc abs_s) \<Longrightarrow> in_user_frame x sA'"
  proof -
    fix tc0 sA'
    assume a: "(tc0, sA') \<in> fst (kernel_entry Interrupt tc abs_s)"
    show "in_user_frame x sA'"
      using frame_after0 a by (simp add: abs_s_def)
  qed

  have einv: "einvs abs_s"
    using invs_s valid_list_abs valid_sched_abs by (simp add: pred_conj_def)
  have hyp: "valid_cur_hyp abs_s"
    by (simp add: RISCV64.valid_cur_hyp_def)
  have sched': "schact_is_rct abs_s"
    using sched_abs by (simp add: schact_is_rct_def)
  have domA: "0 < domain_time abs_s \<and> valid_domain_list abs_s"
    using dt_abs valid_domain_list_abs by simp
  have runA: "Interrupt \<noteq> Interrupt \<longrightarrow> ct_running abs_s"
    by simp
  have runidleA: "ct_running abs_s \<or> ct_idle abs_s"
    using ctr_s by (rule disjI1)
  have not_global: "x \<notin> ({} :: obj_ref set)"
    by simp

  (* Apply the composed theorem itself to everything gathered above - state the goal explicitly first, so the conclusion pins every schematic before the reach_ipc/frame_after premises (whose bound tc0 only appears in their antecedent) are matched. *)
  have main: "user_mem_C (globals tC) x = user_mem_C (globals tC') x"
    by (rule kernel_entry_user_mem_C_unauthorized_unchanged
          [OF all_invs'_s' rel_C refl exec_C rel pas einv hyp
              runA runidleA sched_abs domA gpd dsi sched' owns may1 may2
              not_owned not_written not_global reach_ipc frame_before frame_after])

  show ?thesis
    using exec_C main by blast
qed

end

end
