(*
 * Copyright 2026, PolarFire AMP verification.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * The single place documenting AMP's headline results. Indexed by
 * requirement, not by work item -- a reader who has never opened PLAN.md
 * must be able to read this file. See CLAUDE.md and the amp-docs skill for
 * the rules governing this file's structure.
 *)
theory AMP_Overview
imports "AMP_UserData.AMP_UserData"
begin

section "1. Isolation"

(*
 * A kernel's step changes a physical memory word only if the kernel owns
 * that word, has explicit Write authority to it, the word is in a fixed
 * exception set, or a thread is legitimately receiving it into an IPC
 * buffer. Outside all four of those reasons, the word keeps its value.
 * This is proved at the abstract-specification level, for any kernel step
 * already known to satisfy l4v's integrity guarantee -- in particular a
 * real call_kernel step meeting call_kernel_integrity's precondition. It
 * is the per-word fact the AMP composition theorem needs: one kernel's
 * step cannot change a word outside its own authority, so kernels with
 * disjoint authority cannot interfere with each other's memory regardless
 * of execution order.
 *
 * Not yet established: the same fact for the real, compiled C kernel (see
 * section 4), for kernel-object memory (TCBs, CNodes, page tables), and
 * for device/MMIO memory.
 *)
lemma REQ_ISO_1_kernel_step_confines_unauthorized_memory:
  assumes "integrity aag X st s'"
  assumes "pasObjectAbs aag x \<noteq> pasSubject aag"
  assumes "\<not> aag_subjects_have_auth_to {pasSubject aag} aag Write x"
  assumes "x \<notin> X"
  assumes "\<And>p'. \<not> (case_option False can_receive_ipc (tcb_states_of_state st p')
                    \<and> tcb_states_of_state s' p' = Some Running
                    \<and> x \<in> auth_ipc_buffers st p')"
  shows "underlying_memory (machine_state st) x = underlying_memory (machine_state s') x"
  using assms by (rule integrity_mem_unauthorized_unchanged)

section "2. Messaging"

text \<open>
  No result yet. Shared memory and notifications are not designed or
  proved.
\<close>

section "3. Durability"

text \<open>
  No result yet. Kernel initialization is not proved.
\<close>

section "4. What is NOT established"

text \<open>
  \<^item> The composition theorem itself -- REQ-ISO-1 is one of its two
    necessary ingredients, not the theorem.
  \<^item> The hardware memory-disjointness assumption is not yet named or
    validated against the real PolarFire SoC memory system.
  \<^item> REQ-ISO-1 is proved only at the abstract-specification level. It says
    nothing yet about the real, compiled C kernel -- that transport is
    identified but not attempted.
  \<^item> REQ-ISO-1 covers only UserData (ordinary) memory. Kernel-object memory
    and device/MMIO memory are separate, open cases.
  \<^item> No claim about shared memory, notifications, or any application-level
    channel -- none of that is designed yet, let alone proved.
  \<^item> No claim about kernel initialization -- REQ-ISO-1 says nothing about
    how a kernel reaches the state it starts a step from.
  \<^item> No claim about timing or other side channels, on any result in this
    file.
  \<^item> No hardware assumption has been named yet at all -- there is currently
    no assumption ledger row, because no result in this file has needed one.
\<close>

section "5. Non-vacuity"

text \<open>
  REQ-ISO-1's five hypotheses are jointly satisfiable, not merely
  individually plausible: \<open>pw_integrity_mem_unauthorized_unchanged\<close>
  (\<open>AMP_UserData_Witnesses.thy\<close>) instantiates them against the real
  two-domain example system already checked into l4v (\<open>Sys1PAS\<close>/\<open>s1\<close>,
  \<open>proof/access-control/ExampleSystem.thy\<close>).
\<close>

end
