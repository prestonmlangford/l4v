(*
 * Copyright 2026, PolarFire AMP verification.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory AMP_DeviceMem
imports "Access.ArchSyscall_AC"
begin

section "Specification"

(*
 * No new types or state are introduced here. This theory states the
 * device-memory analogue of AMP_UserData's abstract-specification result,
 * at the abstract-specification level only.
 *
 * device_state models user-mapped device memory (MMIO regions mapped into
 * a user address space) only -- see the comment at
 * ArchInvariants_AI.thy:127, "user-mapped devices (as opposed to
 * kernel-only device memory)". Kernel-only MMIO (PLIC, CLINT, timer) is not
 * modelled as memory at all, so it needs no confinement argument here; see
 * PLAN.md's "Device memory: abstract-level confinement via
 * integrity_device" for the full account of why this case has no
 * refinement layers to C.
 *)

section "Results"

(*
 * l4v's integrity_device lists every reason a device-memory word is
 * allowed to differ across a kernel step: the writer owns the word
 * (trd_lrefl), or the writer has Write authority to it (trd_write). Unlike
 * integrity_mem, there is no globals exception and no IPC-buffer exception
 * -- device_state carries neither notion. Once those two are excluded,
 * only trd_orefl - unchanged content - is left. This lemma names that
 * excluded-middle case directly: a word that is owned by no one but the
 * calling subject and carries no Write authority keeps the same value
 * across any step that satisfies l4v's integrity. This is the per-word
 * fact AMP's frame-rule composition argument (the composition theorem)
 * needs for device memory at the abstract-specification level, mirroring
 * integrity_mem_unauthorized_unchanged (AMP_UserData.thy) for
 * underlying_memory.
 *)
lemma integrity_device_unauthorized_unchanged:
  (* The step already satisfies l4v's integrity guarantee. *)
  assumes integ: "integrity aag X st s'"
  (* Someone other than the acting subject owns x. *)
  assumes not_owned: "pasObjectAbs aag x \<noteq> pasSubject aag"
  (* The acting subject holds no Write authority to x. *)
  assumes not_written: "\<not> aag_subjects_have_auth_to {pasSubject aag} aag Write x"
  (* The device memory at x is unchanged across the kernel step. *)
  shows "device_state (machine_state st) x = device_state (machine_state s') x"
proof -
  have "integrity_device aag {pasSubject aag} x (tcb_states_of_state st) (tcb_states_of_state s')
          (device_state (machine_state st) x) (device_state (machine_state s') x)"
    using integ unfolding integrity_subjects_def by blast
  then show ?thesis
  proof (cases rule: integrity_device.cases)
    case trd_lrefl
    then show ?thesis using not_owned by blast
  next
    case trd_orefl
    then show ?thesis .
  next
    case trd_write
    then show ?thesis using not_written by blast
  qed
qed

end
