(*
 * Copyright 2026, PolarFire AMP verification.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory AMP_DeviceMem_Witnesses
imports AMP_DeviceMem "Access.ExampleSystem"
begin

section "Results"

(*
 * Positive witness for integrity_device_unauthorized_unchanged: its three
 * hypotheses are jointly satisfiable, not merely individually plausible.
 * Sys1PAS/s1 (the two-domain example system already checked into l4v)
 * gives a real policy graph and a real state to instantiate them against,
 * exactly as pw_integrity_mem_unauthorized_unchanged (AMP_UserData_Witnesses.thy)
 * does for the UserData case. Object 0x7 is T1's CNode - labelled T1,
 * distinct from the calling subject UT1, and UT1 has no Write edge to T1
 * in Sys1AuthGraph (that graph only completes self-loops per label, see
 * complete_AuthGraph_def). Taking s' = st = s1 (via integrity_refl, which
 * holds for any state unconditionally) closes the "integrity holds"
 * hypothesis without needing a real kernel step. integrity_device has no
 * IPC clause, so there is no third side condition to discharge here,
 * unlike the UserData witness.
 *)
lemma pw_integrity_device_unauthorized_unchanged:
  "device_state (machine_state s1) (0x7 :: obj_ref) = device_state (machine_state s1) 0x7"
proof (rule integrity_device_unauthorized_unchanged
             [where aag = Sys1PAS and X = "{}" and st = s1 and s' = s1 and x = "0x7"])
  show "integrity Sys1PAS {} s1 s1" by (rule integrity_refl)
next
  show "pasObjectAbs Sys1PAS 0x7 \<noteq> pasSubject Sys1PAS"
    by (simp add: Sys1PAS_def Sys1AgentMap_simps)
next
  show "\<not> aag_subjects_have_auth_to {pasSubject Sys1PAS} Sys1PAS Write 0x7"
    by (simp add: Sys1PAS_def Sys1AgentMap_simps Sys1AuthGraph_def
                  Sys1AuthGraph_aux_def complete_AuthGraph_def)
qed

end
