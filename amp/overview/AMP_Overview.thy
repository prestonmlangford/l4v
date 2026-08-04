(*
 * Copyright 2026, PolarFire AMP verification.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * The single place documenting AMP's headline results. Indexed by
 * requirement, not by work item - a reader who has never opened PLAN.md
 * must be able to read this file. See CLAUDE.md and the amp-docs skill for
 * the rules governing this file's structure.
 *)
theory AMP_Overview
imports "AMP_UserData.AMP_UserData" "AMP_UserData_Confinement_C.AMP_UserData_Confinement_C"
begin

section "1. Isolation"

(*
 * A word keeps its value across a kernel step, unless the kernel owns it,
 * holds Write authority to it, the word is a fixed exception, or a thread
 * receives it into an IPC buffer. This holds for any step already known to
 * satisfy l4v's integrity guarantee, such as a real call_kernel step. It is
 * the per-word fact the AMP composition theorem needs: kernels with
 * disjoint authority leave each other's memory alone, in any execution
 * order.
 *
 * Holds for the real, compiled kernel too - see the corollary below.
 * Covers UserData memory; kernel-object and device/MMIO memory are
 * separate, open cases (section 4).
 *)
lemma REQ_ISO_1_kernel_step_confines_unauthorized_memory:
  (* The step already satisfies l4v's integrity guarantee. *)
  assumes "integrity aag X st s'"
  (* Someone other than the acting subject owns x. *)
  assumes "pasObjectAbs aag x \<noteq> pasSubject aag"
  (* The acting subject holds no Write authority to x. *)
  assumes "\<not> aag_subjects_have_auth_to {pasSubject aag} aag Write x"
  (* x is not a fixed global exception. *)
  assumes "x \<notin> X"
  (* No thread legitimately receives x into an IPC buffer. *)
  assumes "\<And>p'. \<not> (case_option False can_receive_ipc (tcb_states_of_state st p')
                    \<and> tcb_states_of_state s' p' = Some Structures_A.thread_state.Running
                    \<and> x \<in> auth_ipc_buffers st p')"
  (* The underlying memory at x is unchanged across the kernel step. *)
  shows "underlying_memory (machine_state st) x = underlying_memory (machine_state s') x"
  using assms by (rule integrity_mem_unauthorized_unchanged)

context kernel_m
begin

(*
 * REQ-ISO-1 holds for the real, compiled kernel too. l4v's refinement
 * correspondence shows a real kernelEntry_C step's C-level memory agrees
 * with an abstract execution's memory, before and after. REQ-ISO-1 then
 * carries straight over: the C-level word keeps its value because the
 * abstract word it agrees with keeps its value. Stated as a `corollary`
 * because that is exactly what it is - no new argument, only that
 * agreement.
 *
 * Most hypotheses below are the standard well-formed-execution bundle
 * behind REQ-ISO-1's own `integrity` hypothesis one level up. One is new
 * here: x must stay a mapped user-data frame across the step
 * (frame_before, frame_after) - see section 4.
 *)
corollary REQ_ISO_1_kernel_step_confines_unauthorized_memory_in_the_real_kernel:
  (* sD is a real, well-formed design-spec state for event e. *)
  assumes "all_invs' e sD"
  (* tC is the C state that corresponds to sD. *)
  assumes "(sD, tC) \<in> rf_sr"
  (* The fast path is off. *)
  assumes "fp = False"
  (* tC' is the result of a real kernelEntry_C step from tC. *)
  assumes "(tc', tC') \<in> fst (kernelEntry_C fp e tc tC)"
  (* sA is the abstract state that corresponds to sD. *)
  assumes "(sA, sD) \<in> state_relation"
  (* The access authority policy (aag) is refined by sA: aag accurately models all authority in sA. *)
  assumes "pas_refined aag sA"
  (* sA satisfies the extended invariants (einvs): standard abstract-state predicates. *)
  assumes "einvs sA"
  (* sA satisfies the hypervisor-state invariant (always true on RISCV64). *)
  assumes "valid_cur_hyp sA"
  (* The current thread runs, unless e is an interrupt. *)
  assumes "e \<noteq> Interrupt \<longrightarrow> ct_running sA"
  (* The current thread runs or is idle. *)
  assumes "ct_running sA \<or> ct_idle sA"
  (* The scheduler is set to resume the current thread. *)
  assumes "scheduler_action sA = resume_cur_thread"
  (* The domain schedule is well-formed and has time left. *)
  assumes "0 < domain_time sA \<and> valid_domain_list sA"
  (* sA's domain assignment matches the policy. *)
  assumes "guarded_pas_domain aag sA"
  (* sA respects domain-separation invariant constraints on IRQ authority. *)
  assumes "domain_sep_inv (pasMaySendIrqs aag) st'' sA"
  (* The scheduler resumes the current thread - the exact shape call_kernel_integrity needs. *)
  assumes "schact_is_rct sA"
  (* The acting subject owns the current thread, when it is active. *)
  assumes "ct_active sA \<longrightarrow> is_subject aag (cur_thread sA)"
  (* The policy allows activating threads and editing ready queues. *)
  assumes "pasMayActivate aag" "pasMayEditReadyQueues aag"
  (* Someone other than the acting subject owns x. *)
  assumes "pasObjectAbs aag x \<noteq> pasSubject aag"
  (* The acting subject holds no Write authority to x. *)
  assumes "\<not> aag_subjects_have_auth_to {pasSubject aag} aag Write x"
  (* x is not a fixed global exception. *)
  assumes "x \<notin> X"
  (* No thread can legitimately receive x into an inter-process communication buffer on any step outcome: no thread is in receive-wait state before the step, then running after, with x as an authorized IPC buffer. *)
  assumes "\<And>tc'' sA' p'. (tc'', sA') \<in> fst (kernel_entry e tc sA) \<Longrightarrow>
                          \<not> (case_option False can_receive_ipc (tcb_states_of_state sA p')
                             \<and> tcb_states_of_state sA' p' = Some Structures_A.thread_state.Running
                             \<and> x \<in> auth_ipc_buffers sA p')"
  (* x is a mapped user-data frame before the step. *)
  assumes "in_user_frame x sA"
  (* x stays a mapped user-data frame on every outcome the step can reach. *)
  assumes "\<And>tc'' sA'. (tc'', sA') \<in> fst (kernel_entry e tc sA) \<Longrightarrow> in_user_frame x sA'"
  (* The C-level user memory at x remains unchanged across the kernel step. *)
  shows "user_mem_C (globals tC) x = user_mem_C (globals tC') x"
  using assms by (rule kernel_entry_user_mem_C_unauthorized_unchanged)

end

section "2. Messaging"

text \<open>
  No result yet. Shared memory and notifications are still to design.
\<close>

section "3. Durability"

text \<open>
  No result yet. Kernel initialization is still to prove.
\<close>

section "4. What is NOT established"

text \<open>
  \<^item> REQ-ISO-1 is one ingredient of the composition theorem, not the
    composition theorem itself.
  \<^item> The hardware memory-disjointness assumption still needs a name and a
    check against the real PolarFire SoC memory system.
  \<^item> The real-kernel corollary needs the word to stay a mapped user-data
    frame across the step. Frame-classification stability across a kernel
    step is a separate, open question in l4v.
  \<^item> REQ-ISO-1 covers UserData (ordinary) memory only. Kernel-object memory
    and device/MMIO memory are separate, open cases.
  \<^item> Shared memory, notifications, and application-level channels are
    still to design.
  \<^item> Kernel initialization is still open: REQ-ISO-1 takes its starting
    state as given.
  \<^item> Timing and other side channels are open, for every result in this
    file.
  \<^item> The assumption ledger is still empty: no result in this file has
    needed a hardware assumption yet.
\<close>

section "5. Non-vacuity"

text \<open>
  REQ-ISO-1's five hypotheses hold together, for a real system:
  \<open>pw_integrity_mem_unauthorized_unchanged\<close> (\<open>AMP_UserData_Witnesses.thy\<close>)
  checks them against the real two-domain example system already in l4v
  (\<open>Sys1PAS\<close>/\<open>s1\<close>, \<open>proof/access-control/ExampleSystem.thy\<close>).

  The real-kernel corollary's hypotheses hold together too, with one gap:
  \<open>pw_kernel_entry_user_mem_C_unauthorized_unchanged\<close>
  (\<open>AMP_UserData_Confinement_C_Witnesses.thy\<close>) checks every hypothesis
  except \<open>frame_before\<close>/\<open>frame_after\<close>, against the same \<open>Init_H\<close>-derived
  state the design-spec and C witnesses already use. Those two stay open:
  l4v's only checked initial state, \<open>init_A_st\<close>, carves no UserData frames
  - frame carving happens later, at the root task, not at kernel boot.
  Closing this needs a checked state further along than kernel boot (see
  PLAN.md's "Checked initialization").
\<close>

end
