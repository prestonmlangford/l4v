(*
 * Copyright 2026, PolarFire AMP verification.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory AMP_UserData
imports "Access.ArchSyscall_AC"
begin

section "Specification"

(*
 * No new types or state are introduced here. This theory states a
 * corollary of l4v's existing access-control development
 * (proof/access-control/), at the abstract-specification level only. The
 * remaining design-spec and C-level transport live in separate sessions --
 * see AMP_UserData_Refine for the abstract-to-design-spec continuation.
 *)

section "Results"

(*
 * l4v's integrity_mem lists every reason a memory word is allowed to
 * differ across a kernel step: the writer owns the word (trm_lrefl), the
 * writer has Write authority to it (trm_write), the word sits in a fixed
 * "globals" exception set (trm_globals), or a thread is legitimately
 * receiving it into an IPC buffer (trm_ipc). Once those four are excluded,
 * only trm_orefl -- unchanged content -- is left. This lemma names that
 * excluded-middle case directly: a word that is owned by no one but the
 * calling subject, carries no Write authority, is not a global exception,
 * and is not a live IPC-buffer target, keeps the same value across any
 * step that satisfies l4v's integrity. This is the per-word fact AMP's
 * frame-rule composition argument (the composition theorem) needs at the
 * abstract-specification level: one kernel's step cannot change a word
 * outside its own authority.
 *
 * call_kernel_integrity (proof/access-control/Syscall_AC.thy) is l4v's
 * proof that a whole kernel call establishes integrity aag X st for the
 * calling subject, for any real execution satisfying its precondition.
 * Composing that Hoare triple with a real step via the standard use_valid
 * combinator gives integrity aag X st s' for the two states either side of
 * the call; feeding that into this lemma gives the concrete per-word fact
 * AMP needs. That composition is a mechanical use_valid application, not
 * separate proof content, so it is not restated as its own lemma here.
 *
 * This is the abstract-specification half of the UserData case. Transporting
 * the same fact to the real C kernel still needs cpspace_user_data_relation,
 * user_mem_relation, user_mem_C_relation, and the refinement chain
 * connecting abstract, executable, and C states for a real call_kernel step
 * (see AMP_UserData_Refine for the abstract-to-design-spec continuation).
 *)
lemma integrity_mem_unauthorized_unchanged:
  assumes integ: "integrity aag X st s'"
  assumes not_owned: "pasObjectAbs aag x \<noteq> pasSubject aag"
  assumes not_written: "\<not> aag_subjects_have_auth_to {pasSubject aag} aag Write x"
  assumes not_global: "x \<notin> X"
  assumes not_ipc: "\<And>p'. \<not> (case_option False can_receive_ipc (tcb_states_of_state st p')
                             \<and> tcb_states_of_state s' p' = Some Running
                             \<and> x \<in> auth_ipc_buffers st p')"
  shows "underlying_memory (machine_state st) x = underlying_memory (machine_state s') x"
proof -
  have "integrity_mem aag {pasSubject aag} x (tcb_states_of_state st) (tcb_states_of_state s')
          (auth_ipc_buffers st) X
          (underlying_memory (machine_state st) x) (underlying_memory (machine_state s') x)"
    using integ unfolding integrity_subjects_def by blast
  then show ?thesis
  proof (cases rule: integrity_mem.cases)
    case trm_lrefl
    then show ?thesis using not_owned by blast
  next
    case trm_orefl
    then show ?thesis .
  next
    case trm_write
    then show ?thesis using not_written by blast
  next
    case trm_globals
    then show ?thesis using not_global by blast
  next
    case (trm_ipc p')
    then show ?thesis using not_ipc[of p'] by blast
  qed
qed

end
