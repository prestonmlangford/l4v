(*
 * Copyright 2026, PolarFire AMP verification.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory AMP_Overview_Witnesses
imports AMP_Overview "Access.ExampleSystem"
        "AMP_UserData_Confinement_C.AMP_UserData_Confinement_C_Witnesses"
begin

section "Results"

(*
 * Positive witness for REQ_ISO_1_kernel_step_confines_unauthorized_memory,
 * restated from pw_integrity_mem_unauthorized_unchanged
 * (AMP_UserData_Witnesses.thy): the same instantiation against the real
 * two-domain example system (Sys1PAS/s1) that discharges that lemma's
 * hypotheses discharges this restatement's identical hypotheses too.
 *)
lemma pw_REQ_ISO_1_kernel_step_confines_unauthorized_memory:
  "underlying_memory (machine_state s1) (0x7 :: obj_ref) = underlying_memory (machine_state s1) 0x7"
proof (rule REQ_ISO_1_kernel_step_confines_unauthorized_memory
             [where aag = Sys1PAS and X = "{}" and st = s1 and s' = s1 and x = "0x7"])
  show "integrity Sys1PAS {} s1 s1" by (rule integrity_refl)
next
  show "pasObjectAbs Sys1PAS 0x7 \<noteq> pasSubject Sys1PAS"
    by (simp add: Sys1PAS_def Sys1AgentMap_simps)
next
  show "\<not> aag_subjects_have_auth_to {pasSubject Sys1PAS} Sys1PAS Write 0x7"
    by (simp add: Sys1PAS_def Sys1AgentMap_simps Sys1AuthGraph_def
                  Sys1AuthGraph_aux_def complete_AuthGraph_def)
next
  show "(0x7 :: obj_ref) \<notin> {}" by simp
next
  fix p'
  show "\<not> (case_option False can_receive_ipc (tcb_states_of_state s1 p')
           \<and> tcb_states_of_state s1 p' = Some Structures_A.thread_state.Running
           \<and> (0x7 :: obj_ref) \<in> auth_ipc_buffers s1 p')"
    by (simp add: RISCV64.auth_ipc_buffers_def get_tcb_def s1_def kh1_def kh1_obj_def
             split: option.splits Structures_A.kernel_object.splits)
qed

context kernel_m
begin

(*
 * Positive witness for
 * REQ_ISO_1_kernel_step_confines_unauthorized_memory_in_the_real_kernel,
 * restated from pw_kernel_entry_user_mem_C_unauthorized_unchanged
 * (AMP_UserData_Confinement_C_Witnesses.thy). The same instantiation,
 * against the same Init_H-derived state triple, checks this restatement's
 * identical hypotheses too - including the same Gap 4 (aag/x/st'' and the
 * eight conditions on them), carried here as explicit hypotheses because
 * init_A_st has no UserData frames to check them against. See
 * AMP_UserData_Confinement_C_Witnesses.thy's own comment for the full
 * account, and AMP_Overview.thy \S 5 for why this gap stays open.
 *)
lemma pw_REQ_ISO_1_kernel_step_confines_unauthorized_memory_in_the_real_kernel:
  (* Init_H has at least one element. *)
  assumes nonempty: "Init_H \<noteq> {}"
  (* Every design-spec state in Init_H has a real C-level kernelEntry_C step from a related C state. *)
  assumes c_level_entry_exists:
    "\<forall>s'. (\<exists>tc0 m' e'. ((tc0, s'), m', e') \<in> Init_H) \<longrightarrow>
     (\<exists>t tc tc' t'. (s', t) \<in> rf_sr \<and> (tc', t') \<in> fst (kernelEntry_C False Interrupt tc t))"
  (* The policy aag faithfully covers init_A_st's real authority. *)
  assumes pas0: "pas_refined aag (init_A_st :: det_state)"
  (* init_A_st's domain assignment matches the policy. *)
  assumes gpd0: "guarded_pas_domain aag (init_A_st :: det_state)"
  (* init_A_st respects domain separation. *)
  assumes dsi0: "domain_sep_inv (pasMaySendIrqs aag) st'' (init_A_st :: det_state)"
  (* The acting subject owns init_A_st's current thread, when it is active. *)
  assumes owns0: "ct_active (init_A_st :: det_state) \<longrightarrow> is_subject aag (cur_thread (init_A_st :: det_state))"
  (* The policy allows activating threads and editing ready queues. *)
  assumes may1: "pasMayActivate aag"
  assumes may2: "pasMayEditReadyQueues aag"
  (* Someone other than the acting subject owns x. *)
  assumes not_owned: "pasObjectAbs aag x \<noteq> pasSubject aag"
  (* The acting subject holds no Write authority to x. *)
  assumes not_written: "\<not> aag_subjects_have_auth_to {pasSubject aag} aag Write x"
  (* No thread legitimately receives x into an IPC buffer, on any outcome the step can reach. *)
  assumes reach_ipc0: "\<forall>tc tc0 sA' p'. (tc0, sA') \<in> fst (kernel_entry Interrupt tc (init_A_st :: det_state)) \<longrightarrow>
                        \<not> (case_option False can_receive_ipc (tcb_states_of_state (init_A_st :: det_state) p')
                           \<and> tcb_states_of_state sA' p' = Some Structures_A.thread_state.Running
                           \<and> x \<in> auth_ipc_buffers (init_A_st :: det_state) p')"
  (* x is a mapped user-data frame at init_A_st. *)
  assumes frame_before0: "in_user_frame x (init_A_st :: det_state)"
  (* x stays a mapped user-data frame on every outcome the step can reach. *)
  assumes frame_after0: "\<forall>tc tc0 sA'. (tc0, sA') \<in> fst (kernel_entry Interrupt tc (init_A_st :: det_state)) \<longrightarrow> in_user_frame x sA'"
  shows "\<exists>tC tc tc' tC' x.
           (tc', tC') \<in> fst (kernelEntry_C False Interrupt tc tC)
           \<and> user_mem_C (globals tC) x = user_mem_C (globals tC') x"
  using pw_kernel_entry_user_mem_C_unauthorized_unchanged
          [OF nonempty c_level_entry_exists pas0 gpd0 dsi0 owns0 may1 may2
              not_owned not_written reach_ipc0 frame_before0 frame_after0] .

end

end
