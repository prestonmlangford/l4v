(*
 * Copyright 2026, PolarFire AMP verification.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory AMP_UserData_Confinement_C
imports "AMP_UserData.AMP_UserData" "AMP_UserData_Refine.AMP_UserData_Refine"
        "AMP_UserData_Refine_C.AMP_UserData_Refine_C"
begin

section "Specification"

(*
 * No new types or state are introduced here. This theory composes the
 * three separately-proved UserData transport halves - AMP_UserData
 * (abstract-specification), AMP_UserData_Refine (abstract-to-design-spec),
 * AMP_UserData_Refine_C (design-spec-to-C) - into one theorem about a real
 * C-level kernelEntry_C step. See PLAN.md's "Chain the abstract-to-C
 * UserData memory link ..." for why this composition is its own session:
 * it is the only theory in the UserData case that needs facts from all
 * three ancestor sessions (Access, Refine, CRefine) at once.
 *)

context kernel_m
begin

section "Results"

(*
 * For a real kernelEntry_C step, a C-level memory word that is owned by no
 * one but the calling subject, carries no Write authority, is not a global
 * exception, and is not a live IPC-buffer target on any reachable
 * abstract-specification outcome, keeps the same value - provided it is a
 * mapped user-data word both before the step and on that same reachable
 * outcome. This is AMP_UserData.kernel_entry_mem_unauthorized_unchanged's
 * per-word confinement fact, carried up through
 * AMP_UserData_Refine.kernel_entry_user_mem_agrees and
 * AMP_UserData_Refine_C.kernel_entry_user_mem_C_agrees to the real C
 * kernel entry point.
 *
 * The composition is straightforward everywhere except one place: reading
 * a word's value out of user_mem/user_mem'/user_mem_C is only meaningful
 * when the word is classified as a mapped user-data frame
 * (in_user_frame). AMP_UserData's own fact is about raw machine memory
 * (underlying_memory), which says nothing about frame classification -
 * l4v's own integrity_mem carries no such guarantee, and no l4v lemma
 * establishing that a kernel step cannot reclassify an unowned word's
 * frame (short of the calling subject holding the necessary Delete/Reset
 * authority over its containing object, which not_written does not cover)
 * was found. frame_before and frame_after name this gap directly, as
 * explicit hypotheses on the one hand, and, on the other, as the reason
 * this theorem's conclusion is not claimed unconditionally - see
 * AMP_Overview.thy \S 4.
 *
 * frame_after and reach_ipc are stated for every abstract-specification
 * outcome kernel_entry can produce for this event and this initial
 * context from sA, not just the one hop actually taken - kernel_entry is
 * nondeterministic, and the specific outcome used inside this proof is
 * only pinned down after composing the other two layers, too late for it
 * to appear in this lemma's own assumptions.
 *)
(* The lemma named kernel_entry_user_mem_C_unauthorized_unchanged: *)
lemma kernel_entry_user_mem_C_unauthorized_unchanged:
  (* Assume: sD satisfies all_invs' for event e - kernel_entry_user_mem_C_agrees's own precondition. *)
  assumes ai: "all_invs' e sD"
  (* Assume: sD and tC are a related pair - one design-spec state, one C state. *)
  assumes rel_C: "(sD, tC) \<in> rf_sr"
  (* Assume: the fastpath flag is off. *)
  assumes fp: "fp = False"
  (* Assume: running kernelEntry_C on event e from tC with initial context tc can produce some result tc' and end state tC'. *)
  assumes exec_C: "(tc', tC') \<in> fst (kernelEntry_C fp e tc tC)"
  (* Assume: sA and sD are a related pair - one abstract state, one design-spec state. *)
  assumes rel_A: "(sA, sD) \<in> state_relation"
  (* Assume: sA satisfies pas_refined, einvs, valid_cur_hyp. *)
  assumes pas: "pas_refined aag sA"
  assumes einv: "einvs sA"
  assumes hyp: "valid_cur_hyp sA"
  (* Assume: if event is not Interrupt, sA's current thread is running; and sA's current thread is running or idle. *)
  assumes runA: "e \<noteq> Interrupt \<longrightarrow> ct_running sA"
  assumes runidleA: "ct_running sA \<or> ct_idle sA"
  (* Assume: sA's scheduler action is the current thread; sA's domain time is positive and its domain list is valid. *)
  assumes schedA: "scheduler_action sA = resume_cur_thread"
  assumes domA: "0 < domain_time sA \<and> valid_domain_list sA"
  (* Assume: sA's domain is guarded; sA respects the domain-separation invariant; sA's scheduler action is the current thread (the schact_is_rct shape call_kernel_integrity itself needs). *)
  assumes gpd: "guarded_pas_domain aag sA"
  assumes dsi: "domain_sep_inv (pasMaySendIrqs aag) st'' sA"
  assumes sched': "schact_is_rct sA"
  (* Assume: if sA's current thread is active, the subject owns it. *)
  assumes owns: "ct_active sA \<longrightarrow> is_subject aag (cur_thread sA)"
  (* Assume: the subject may activate threads and may edit ready queues. *)
  assumes may: "pasMayActivate aag" "pasMayEditReadyQueues aag"
  (* Assume: x is owned by no one but the calling subject; carries no Write authority; is not a global exception. *)
  assumes not_owned: "pasObjectAbs aag x \<noteq> pasSubject aag"
  assumes not_written: "\<not> aag_subjects_have_auth_to {pasSubject aag} aag Write x"
  assumes not_global: "x \<notin> X"
  (* Assume: on every abstract outcome sA' reachable by kernel_entry on e from sA with context tc, x is not a live IPC-buffer target. *)
  assumes reach_ipc: "\<And>tc'' sA' p'. (tc'', sA') \<in> fst (kernel_entry e tc sA) \<Longrightarrow>
                       \<not> (case_option False can_receive_ipc (tcb_states_of_state sA p')
                          \<and> tcb_states_of_state sA' p' = Some Structures_A.thread_state.Running
                          \<and> x \<in> auth_ipc_buffers sA p')"
  (* Assume: x is a mapped user-data word at sA. *)
  assumes frame_before: "in_user_frame x sA"
  (* Assume: on every abstract outcome sA' reachable by kernel_entry on e from sA with context tc, x is still a mapped user-data word. *)
  assumes frame_after: "\<And>tc'' sA'. (tc'', sA') \<in> fst (kernel_entry e tc sA) \<Longrightarrow> in_user_frame x sA'"
  (* Conclusion: x's C-level memory content is the same before and after the real kernelEntry_C step. *)
  shows "user_mem_C (globals tC) x = user_mem_C (globals tC') x"
proof -
  (* Design-spec-to-C half: apply kernel_entry_user_mem_C_agrees to the given C-level execution. *)
  note keumca = kernel_entry_user_mem_C_agrees[OF ai rel_C fp exec_C]
  have preC: "user_mem_C (globals tC) = user_mem' sD"
    using keumca by blast
  obtain sD' where
    stepD: "(tc', sD') \<in> fst (kernelEntry e tc sD)" and
    postC: "user_mem_C (globals tC') = user_mem' sD'"
    using keumca by blast

  (* Abstract-to-design-spec half: apply kernel_entry_user_mem_agrees to the design-spec execution stepD just obtained. *)
  have preA: "(einvs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) and (ct_running or ct_idle)
               and (\<lambda>s. scheduler_action s = resume_cur_thread)
               and (\<lambda>s. 0 < domain_time s \<and> valid_domain_list s)) sA"
    using einv runA runidleA schedA domA by (simp add: pred_conj_def)
  have preH: "(invs' and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running' s) and (ct_running' or ct_idle')
               and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
               and (\<lambda>s. 0 < ksDomainTime s)) sD"
    using ai by (auto simp: all_invs'_def pred_conj_def word_neq_0_conv)
  note keuma = kernel_entry_user_mem_agrees[OF rel_A preA preH stepD]
  have preB: "user_mem sA = user_mem' sD"
    using keuma by blast
  obtain sA' where
    stepA: "(tc', sA') \<in> fst (kernel_entry e tc sA)" and
    relA': "(sA', sD') \<in> state_relation" and
    postB: "user_mem sA' = user_mem' sD'"
    using keuma by blast

  (* Abstract-specification half: apply kernel_entry_mem_unauthorized_unchanged to the abstract execution stepA just obtained. *)
  have actA: "e \<noteq> Interrupt \<longrightarrow> ct_active sA"
    using runA by (auto simp: ct_in_state_def st_tcb_at_def obj_at_def)
  have actidleA: "ct_active sA \<or> ct_idle sA"
    using runidleA by (auto simp: ct_in_state_def st_tcb_at_def obj_at_def)
  have not_ipc_inst: "\<And>p'. \<not> (case_option False can_receive_ipc (tcb_states_of_state sA p')
                              \<and> tcb_states_of_state sA' p' = Some Structures_A.thread_state.Running
                              \<and> x \<in> auth_ipc_buffers sA p')"
    using reach_ipc[OF stepA] .
  note memeq = kernel_entry_mem_unauthorized_unchanged
                 [OF pas einv hyp actA actidleA sched' gpd dsi owns may stepA
                     not_owned not_written not_global not_ipc_inst]

  (* Bridge underlying_memory back to user_mem, using frame_before/frame_after for the one gap the composition cannot close on its own. *)
  have frame_after_inst: "in_user_frame x sA'"
    using frame_after[OF stepA] .
  have umx1: "user_mem sA x = Some (underlying_memory (machine_state sA) x)"
    using frame_before by (simp add: user_mem_def)
  have umx2: "user_mem sA' x = Some (underlying_memory (machine_state sA') x)"
    using frame_after_inst by (simp add: user_mem_def)
  have umeq: "user_mem sA x = user_mem sA' x"
    using umx1 umx2 memeq by simp

  (* Conclude by chaining preC, preB, umeq, postB, postC pointwise at x. *)
  have "user_mem_C (globals tC) x = user_mem sA x"
    using preC preB by simp
  also have "\<dots> = user_mem sA' x"
    using umeq by simp
  also have "\<dots> = user_mem_C (globals tC') x"
    using postB postC by simp
  finally show ?thesis .
qed

end

end
