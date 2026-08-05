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

(*
 * For a real kernel_entry step - the register-context save/restore wrapped
 * around call_kernel, see AMP_UserData.thy's comment on
 * kernel_entry_mem_unauthorized_unchanged for the general shape of this
 * argument - unauthorized device memory is unchanged, exactly as
 * integrity_device_unauthorized_unchanged says for the bare call_kernel step
 * above.
 *
 * The wrapping argument is identical to the UserData case: kernel_entry's
 * thread_set/thread_get wrapping (proof/invariant-abstract/ADT_AI.thy) only
 * ever touches the current thread's own tcb_arch field, a kernel-object
 * write via set_object (spec/abstract/KHeap_A.thy), never machine_state - so
 * device_state (machine_state s) is the same value immediately before the
 * wrapping thread_set as it is immediately after. call_kernel_integrity
 * (proof/access-control/Syscall_AC.thy) supplies the per-word fact across
 * the inner call_kernel step; thread_set's own pas_refined / einvs /
 * valid_cur_hyp / domain_sep_inv / guarded_pas_domain preservation carries
 * call_kernel_integrity's own precondition across the initial thread_set,
 * exactly as for the UserData case. Unlike that case, there is no IPC-buffer
 * exception to carry across the wrap - integrity_device has no such clause -
 * so the whole IPC-transfer block that argument needs is absent here.
 *)
(* The lemma named kernel_entry_device_state_unauthorized_unchanged: *)
lemma kernel_entry_device_state_unauthorized_unchanged:
  (* Assume: st satisfies pas_refined, einvs, valid_cur_hyp. *)
  assumes pas: "pas_refined aag st"
  assumes einv: "einvs st"
  assumes hyp: "valid_cur_hyp st"
  (* Assume: if event is not Interrupt, st's current thread is active; and st's current thread is active or idle. *)
  assumes act: "e \<noteq> Interrupt \<longrightarrow> ct_active st"
  assumes actidle: "ct_active st \<or> ct_idle st"
  (* Assume: st's scheduler action is the current thread; st's domain is guarded; st respects the domain-separation invariant. *)
  assumes sched: "schact_is_rct st"
  assumes gpd: "guarded_pas_domain aag st"
  assumes dsi: "domain_sep_inv (pasMaySendIrqs aag) st'' st"
  (* Assume: if st's current thread is active, the subject owns it. *)
  assumes owns: "ct_active st \<longrightarrow> is_subject aag (cur_thread st)"
  (* Assume: the subject may activate threads and may edit ready queues. *)
  assumes may: "pasMayActivate aag" "pasMayEditReadyQueues aag"
  (* Assume: running kernel_entry on event e from st with initial context tc can produce some result tc' and end state s'. *)
  assumes exec: "(tc', s') \<in> fst (kernel_entry e tc st)"
  (* Assume: x is owned by no one but the calling subject and carries no Write authority. *)
  assumes not_owned: "pasObjectAbs aag x \<noteq> pasSubject aag"
  assumes not_written: "\<not> aag_subjects_have_auth_to {pasSubject aag} aag Write x"
  (* Conclusion: x's device memory content is the same before and after the kernel_entry step. *)
  shows "device_state (machine_state st) x = device_state (machine_state s') x"
proof -
  (* Name t: the current thread at st - the thread whose register context kernel_entry saves and restores. *)
  define t where t_def: "t \<equiv> cur_thread st"
  define f :: "tcb \<Rightarrow> tcb" where f_def: "f \<equiv> \<lambda>tcb. tcb\<lparr>tcb_arch := arch_tcb_context_set tc (tcb_arch tcb)\<rparr>"
  (* Derive: kernel_entry's execution decomposes into a thread_set step, a call_kernel step, and a final thread_get that leaves the state unchanged. *)
  have decomp: "\<exists>mid1 r_ck. ((), mid1) \<in> fst (thread_set f t st) \<and> (r_ck, s') \<in> fst (call_kernel e mid1)"
    using exec
    apply (simp add: kernel_entry_def t_def f_def in_bind in_gets thread_get_def gets_the_in_monad in_return)
    apply (elim exE conjE)
    apply blast
    done
  then obtain mid1 r_ck where
    step1: "((), mid1) \<in> fst (thread_set f t st)" and
    step2: "(r_ck, s') \<in> fst (call_kernel e mid1)"
    by blast

  (* thread_set only replaces the kernel object at t with another TCB, leaving every other field of the state record - in particular machine_state - untouched. *)
  have mid1_eq: "\<exists>tcb. kheap st t = Some (TCB tcb) \<and> mid1 = st\<lparr>kheap := (kheap st)(t \<mapsto> TCB (f tcb))\<rparr>"
    using step1 by (clarsimp simp: thread_set_def set_object_def in_monad get_object_def get_tcb_def a_type_def
                            split: option.splits kernel_object.splits)
  then obtain tcb where
    kheap_t: "kheap st t = Some (TCB tcb)" and
    mid1_def: "mid1 = st\<lparr>kheap := (kheap st)(t \<mapsto> TCB (f tcb))\<rparr>"
    by blast
  (* Derive: x's device memory content is the same at st as at mid1 - thread_set never touches machine_state. *)
  have pre: "device_state (machine_state st) x = device_state (machine_state mid1) x"
    by (simp add: mid1_def)

  (* Derive: mid1 satisfies the same activity/ownership/scheduling facts as st - none of them depend on tcb_arch. *)
  have ct_mid1: "cur_thread mid1 = cur_thread st"
    by (simp add: mid1_def)
  have act_mid1: "ct_active mid1 = ct_active st" "ct_idle mid1 = ct_idle st"
    using kheap_t
    by (auto simp: ct_in_state_def st_tcb_at_def obj_at_def ct_mid1 mid1_def f_def)

  (* Name the Hoare triple carrying einvs across the thread_set step - invs, valid_list, and valid_sched each transfer, since f only ever touches tcb_arch. *)
  have tsp_einvs: "\<lbrace>einvs\<rbrace> thread_set f t \<lbrace>\<lambda>_. einvs\<rbrace>"
    unfolding pred_conj_def
    apply (rule hoare_vcg_conj_lift[OF hoare_vcg_conj_lift])
       apply (rule thread_set_invs_trivial; simp add: f_def tcb_cap_cases_def)
      apply wp
     apply (rule thread_set_not_state_valid_sched; simp add: f_def)
    done
  (* Name the Hoare triple carrying pas_refined across the thread_set step - re-derived here since InfoFlow (proof/infoflow/RISCV64/ArchADT_IF.thy's thread_set_pas_refined) is not in AMP_DeviceMem's session ancestry; same ingredients, all from Access. *)
  have f_cps: "\<And>tcb. \<forall>(getF, v)\<in>ran tcb_cap_cases. getF (f tcb) = getF tcb"
    by (simp add: f_def tcb_cap_cases_def)
  have f_st: "\<And>tcb. tcb_state (f tcb) = tcb_state tcb"
    by (simp add: f_def)
  have f_ntfn: "\<And>tcb. tcb_bound_notification (f tcb) = tcb_bound_notification tcb"
    by (simp add: f_def)
  have f_dom: "\<And>tcb. tcb_domain (f tcb) = tcb_domain tcb"
    by (simp add: f_def)
  (* Derive: mid1 satisfies pas_refined - every ingredient pas_refined_def depends on (caps_of_state, thread_st_auth, thread_bound_ntfns, state_vrefs, the domain map, and every plain state field untouched by a kheap-only update) is unchanged by thread_set for this f. *)
  have cos_hoare: "\<lbrace>\<lambda>s. caps_of_state s = caps_of_state st\<rbrace> thread_set f t \<lbrace>\<lambda>_ s. caps_of_state s = caps_of_state st\<rbrace>"
    by (rule thread_set_caps_of_state_trivial[OF f_cps])
  have cos_eq: "caps_of_state mid1 = caps_of_state st"
    using use_valid[OF step1 cos_hoare] by simp
  have tsa_hoare: "\<lbrace>\<lambda>s. thread_st_auth s = thread_st_auth st\<rbrace> thread_set f t \<lbrace>\<lambda>_ s. thread_st_auth s = thread_st_auth st\<rbrace>"
    by (rule thread_set_thread_st_auth_trivT[OF f_st])
  have tsa_eq: "thread_st_auth mid1 = thread_st_auth st"
    using use_valid[OF step1 tsa_hoare] by simp
  have tbn_hoare: "\<lbrace>\<lambda>s :: det_state. thread_bound_ntfns s = thread_bound_ntfns st\<rbrace> thread_set f t \<lbrace>\<lambda>_ s. thread_bound_ntfns s = thread_bound_ntfns st\<rbrace>"
    by (rule thread_set_thread_bound_ntfns_trivT[OF f_ntfn])
  have tbn_eq: "thread_bound_ntfns mid1 = thread_bound_ntfns st"
    using use_valid[OF step1 tbn_hoare] by simp
  have sv_hoare: "\<lbrace>\<lambda>s :: det_state. state_vrefs s = state_vrefs st\<rbrace> thread_set f t \<lbrace>\<lambda>_ s. state_vrefs s = state_vrefs st\<rbrace>"
    by (rule thread_set_state_vrefs)
  have sv_eq: "state_vrefs mid1 = state_vrefs st"
    using use_valid[OF step1 sv_hoare] by simp
  have tdmw_hoare: "\<lbrace>tcb_domain_map_wellformed aag\<rbrace> thread_set f t \<lbrace>\<lambda>_. tcb_domain_map_wellformed aag\<rbrace>"
    by (rule tcb_domain_map_wellformed_lift_strong[OF thread_set_edomains[OF f_dom]])
  have tdmw_mid1: "tcb_domain_map_wellformed aag mid1"
    using use_valid[OF step1 tdmw_hoare] pas
    by (simp add: pas_refined_def)
  have pas_refined_mid1: "pas_refined aag mid1"
    using pas cos_eq tsa_eq tbn_eq sv_eq tdmw_mid1
    by (simp add: pas_refined_def mid1_def state_objs_to_policy_def RISCV64.state_hyp_refs_empty)
  (* Name the Hoare triple carrying guarded_pas_domain across the thread_set step. *)
  have tsp_gpd: "\<lbrace>guarded_pas_domain aag\<rbrace> thread_set f t \<lbrace>\<lambda>_. guarded_pas_domain aag\<rbrace>"
    by (wpsimp wp: guarded_pas_domain_lift)
  (* Derive: f is the same update as l4v's own tcb_arch_update notation - needed to match thread_set_tcb_arch_update_domain_sep_inv's stated shape. *)
  have f_alt: "f = tcb_arch_update (arch_tcb_context_set tc)"
    by (rule ext) (simp add: f_def)
  (* Derive: domain_sep_inv transfers across the thread_set step - l4v's own tcb_arch_update fact, instantiated at this specific aag/st''. *)
  have dsi_hoare: "\<lbrace>domain_sep_inv (pasMaySendIrqs aag) st''\<rbrace> thread_set f t \<lbrace>\<lambda>_. domain_sep_inv (pasMaySendIrqs aag) st''\<rbrace>"
    unfolding f_alt
    by (rule thread_set_tcb_arch_update_domain_sep_inv)
  (* Derive: mid1 satisfies call_kernel_integrity's own precondition - the structural invariants transfer via the Hoare triples above; the activity/scheduling/ownership facts transfer directly, since none of them depend on tcb_arch. *)
  have mid1_pre: "pas_refined aag mid1 \<and> einvs mid1 \<and> valid_cur_hyp mid1
                  \<and> schact_is_rct mid1 \<and> guarded_pas_domain aag mid1
                  \<and> domain_sep_inv (pasMaySendIrqs aag) st'' mid1"
    using use_valid[OF step1 tsp_einvs] einv
          pas_refined_mid1
          use_valid[OF step1 tsp_gpd] gpd
          use_valid[OF step1 dsi_hoare] dsi
          sched ct_mid1
    by (simp_all add: RISCV64.valid_cur_hyp_def schact_is_rct_def mid1_def)
  (* Derive: mid1 satisfies call_kernel_integrity's precondition. *)
  have preCK: "(pas_refined aag and einvs and valid_cur_hyp
                and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s) and (ct_active or ct_idle)
                and domain_sep_inv (pasMaySendIrqs aag) st'' and schact_is_rct
                and guarded_pas_domain aag and (\<lambda>s. ct_active s \<longrightarrow> is_subject aag (cur_thread s))
                and K (pasMayActivate aag \<and> pasMayEditReadyQueues aag) and (\<lambda>s. s = mid1)) mid1"
    using mid1_pre act act_mid1 actidle owns may ct_mid1
    by (simp add: pred_conj_def)

  (* Derive: integrity holds between mid1 and s', via call_kernel_integrity and the concrete call_kernel step. *)
  have integ: "integrity aag X mid1 s'"
    using use_valid[OF step2 call_kernel_integrity[where st=mid1 and aag=aag and ev=e and st'=st'' and X=X]] preCK
    by (simp add: pred_conj_def)

  (* Derive: x's device memory content is the same at mid1 as at s', via the abstract-specification result above. *)
  have post: "device_state (machine_state mid1) x = device_state (machine_state s') x"
    using integrity_device_unauthorized_unchanged[OF integ not_owned not_written] .

  (* Conclude the goal from pre and post. *)
  from pre post show ?thesis by simp
qed

end
