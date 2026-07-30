(*
 * Copyright 2026, PolarFire AMP verification.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory AMP_Overview_Witnesses
imports AMP_Overview "Access.ExampleSystem"
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
           \<and> tcb_states_of_state s1 p' = Some Running
           \<and> (0x7 :: obj_ref) \<in> auth_ipc_buffers s1 p')"
    by (simp add: RISCV64.auth_ipc_buffers_def get_tcb_def s1_def kh1_def kh1_obj_def
             split: option.splits Structures_A.kernel_object.splits)
qed

end
