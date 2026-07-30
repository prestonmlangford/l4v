(*
 * Copyright 2026, PolarFire AMP verification.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory AMP_UserData_Witnesses
imports AMP_UserData "Access.ExampleSystem"
begin

section "Results"

(*
 * Positive witness for integrity_mem_unauthorized_unchanged: its five
 * hypotheses are jointly satisfiable, not merely individually plausible.
 * Sys1PAS/s1 (the two-domain example system already checked into l4v)
 * gives a real policy graph and a real state to instantiate them against.
 * Object 0x7 is T1's CNode -- labelled T1, distinct from the calling
 * subject UT1, and UT1 has no Write edge to T1 in Sys1AuthGraph (that
 * graph only completes self-loops per label, see complete_AuthGraph_def).
 * Both of s1's TCBs hold NullCap in tcb_ipcframe, so auth_ipc_buffers s1
 * is empty everywhere, discharging the IPC side condition for every
 * address, not just 0x7. Taking s' = st = s1 (via integrity_refl, which
 * holds for any state unconditionally) closes the "integrity holds"
 * hypothesis without needing a real kernel step.
 *)
lemma pw_integrity_mem_unauthorized_unchanged:
  "underlying_memory (machine_state s1) (0x7 :: obj_ref) = underlying_memory (machine_state s1) 0x7"
proof (rule integrity_mem_unauthorized_unchanged
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
