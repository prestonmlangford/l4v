(*
 * Copyright 2026, PolarFire AMP verification.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory AMP_UserData_Refine
imports Refine.Refine
begin

section "Specification"

(*
 * No new types or state are introduced here. This theory states a
 * corollary of l4v's existing refinement development
 * (proof/refine/RISCV64/Refine.thy), linking the abstract specification's
 * view of UserData memory to the design specification's view for a real
 * call_kernel step.
 *)

section "Results"

(*
 * For a real call_kernel/callKernel step, user_mem (abstract) and
 * user_mem' (design spec) agree both before the step and after it.
 *
 * Four existing, unmodified l4v facts compose to give this directly.
 * kernel_corres (proof/refine/RISCV64/Refine.thy) relates call_kernel and
 * callKernel: a real callKernel step's end state is always related, by
 * state_relation, to some real call_kernel step's end state.
 * user_mem_relation (same file) says user_mem and user_mem' agree at any
 * state_relation-related pair of states, provided each state is
 * valid_state. akernel_invs_det_ext (proof/invariant-abstract/AInvs.thy)
 * and ckernel_invs (proof/refine/RISCV64/Refine.thy) say call_kernel and
 * callKernel each preserve their own invariant - invs and invs' - which
 * is what supplies valid_state at the end state.
 *
 * This is the abstract-to-design-spec half of transporting UserData memory
 * confinement to the real kernel. The design-spec-to-C half is separate,
 * still-open work.
 *)
(* The lemma named call_kernel_user_mem_agrees: *)
lemma call_kernel_user_mem_agrees: 
  (* Assume: s and s' are a related pair - one abstract state, one design-spec state. *)
  assumes rel: "(s, s') \<in> state_relation" 
  (*
   * Assume: s satisfies einvs; and, if event is not Interrupt, s's current
   * thread is running; and s's current thread is running or idle; and s's
   * scheduler action is resume_cur_thread; and s's domain time is positive,
   * and its domain list is valid.
   *)
  assumes preA: "(einvs and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running s) and (ct_running or ct_idle)
                  and (\<lambda>s. scheduler_action s = resume_cur_thread)
                  and (\<lambda>s. 0 < domain_time s \<and> valid_domain_list s)) s"
  (*
   * Assume: s' satisfies invs'; and, if event is not Interrupt, s''s current
   * thread is running; and s''s current thread is running or idle; and s''s
   * scheduler action is ResumeCurrentThread.
   *)
  assumes preH: "(invs' and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running' s) and (ct_running' or ct_idle')
                  and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)) s'"
  (* Assume: running callKernel on event from s' can produce some result r' and end state t'. *)
  assumes exec: "(r', t') \<in> fst (callKernel event s')"
  (*
   * Conclusion: the abstract and design-spec UserData memory agree at s and
   * s'; and there exists an abstract execution of call_kernel on event from
   * s, with some result r and end state t, such that t is related to t' by
   * state_relation; and t's UserData memory agrees with t'.
   *)
  shows "user_mem s = user_mem' s'
         \<and> (\<exists>r t. (r, t) \<in> fst (call_kernel event s) \<and> (t, t') \<in> state_relation
                   \<and> user_mem t = user_mem' t')"
(* Begin a structured proof. *)
proof -
  (*
   * Composing multiple facts via a single OF [a, b, c] list is dramatically
   * slower here than chaining them one at a time (OF a, then OF b, then OF
   * c): with several large einvs/invs'-shaped terms in play, Isabelle's
   * unifier explores a much bigger combined search space when asked to
   * resolve them all at once than when each resolution is committed before
   * the next begins. Every composition below is deliberately sequential,
   * via a chain of "note"s each resolving exactly one more premise.
   *)
  (* Derive: s satisfies invs; *)
  have invs_s: "invs s"
  (* ...from preA, by rewriting the and-combinator into a plain conjunction. *)
    using preA by (simp add: pred_conj_def)
  (* Derive: s' satisfies invs'; *)
  have invs'_s': "invs' s'"
  (* ...from preH, the same way. *)
    using preH by (simp add: pred_conj_def)
  (* Name valid_s: s is valid_state, from invs_s. *)
  note valid_s = invs_valid_stateI[OF invs_s]
  (* Name valid'_s': s' is valid_state', from invs'_s'. *)
  note valid'_s' = invs_valid_stateI'[OF invs'_s']
  (* Name umr1: user_mem_relation, with its state_relation premise fixed to rel. *)
  note umr1 = user_mem_relation[OF rel]
  (* Name umr2: umr1, with its valid_state' premise fixed to valid'_s'. *)
  note umr2 = umr1[OF valid'_s']
  (* Derive: user_mem at s equals user_mem' at s'; *)
  have pre: "user_mem s = user_mem' s'"
  (* ...from umr2 with its valid_state premise fixed to valid_s, tidied by simp. *)
    using umr2[OF valid_s] by simp

  (* Name kc0: corres_underlyingD2, with its correspondence premise fixed to kernel_corres instantiated at event. *)
  note kc0 = corres_underlyingD2[OF kernel_corres[of event]]
  (* Name kc1: kc0, with its state-relatedness premise fixed to rel. *)
  note kc1 = kc0[OF rel]
  (* Name kc2: kc1, with its abstract-precondition premise fixed to preA. *)
  note kc2 = kc1[OF preA]
  (* Name kc3: kc2, with its design-spec-precondition premise fixed to preH. *)
  note kc3 = kc2[OF preH]
  (* Name kc4: kc3, with its execution premise fixed to exec. *)
  note kc4 = kc3[OF exec]
  (* Obtain: some abstract result r and end state t, such that (r, t) is a possible result of call_kernel on event from s, and t is related to t' by state_relation; *)
  obtain r t where step: "(r, t) \<in> fst (call_kernel event s)" "(t, t') \<in> state_relation"
  (* ...from kc4, closed automatically. *)
    using kc4 by fastforce

  (* Derive: s satisfies invs, and, if event is not Interrupt, s's current thread is running; *)
  have preA_invs: "(invs and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running s)) s"
  (* ...from preA, by rewriting the and-combinator into a plain conjunction. *)
    using preA by (simp add: pred_conj_def)
  (*
   * Derive: s' satisfies invs', and, if event is not Interrupt, s''s current
   * thread is running; and s''s scheduler action is ResumeCurrentThread;
   *)
  have preH_invs: "(invs' and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running' s)
                    and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)) s'"
  (* ...from preH, the same way. *)
    using preH by (simp add: pred_conj_def)

  (*
   * Resolving use_valid's Hoare-triple premise (2nd) before its execution
   * premise (1st) fixes f/P/Q unambiguously from akernel_invs_det_ext /
   * ckernel_invs first; doing it the other way round leaves f as a
   * schematic function applied to a schematic argument, which OF refuses
   * to resolve ("multiple unifiers") since more than one instantiation
   * would fit.
   *)
  (* Name uv0: use_valid, with its Hoare-triple premise fixed to akernel_invs_det_ext, execution premise left open. *)
  note uv0 = use_valid[OF _ akernel_invs_det_ext]
  (* Name uv1: uv0, with its execution premise fixed to step's first part. *)
  note uv1 = uv0[OF step(1)]
  (* Derive: t satisfies invs; *)
  have invs_t: "invs t"
  (* ...from uv1 with its precondition premise fixed to preA_invs, tidied by simp. *)
    using uv1[OF preA_invs] by (simp add: pred_conj_def)

  (* Name uv0': use_valid, with its Hoare-triple premise fixed to ckernel_invs, execution premise left open. *)
  note uv0' = use_valid[OF _ ckernel_invs]
  (* Name uv1': uv0', with its execution premise fixed to exec. *)
  note uv1' = uv0'[OF exec]
  (* Derive: t' satisfies invs'; *)
  have invs'_t': "invs' t'"
  (* ...from uv1' with its precondition premise fixed to preH_invs, tidied by simp. *)
    using uv1'[OF preH_invs] by (simp add: pred_conj_def)

  (* Name valid_t: t is valid_state, from invs_t. *)
  note valid_t = invs_valid_stateI[OF invs_t]
  (* Name valid'_t': t' is valid_state', from invs'_t'. *)
  note valid'_t' = invs_valid_stateI'[OF invs'_t']
  (* Name umr3: user_mem_relation, with its state_relation premise fixed to step's second part. *)
  note umr3 = user_mem_relation[OF step(2)]
  (* Name umr4: umr3, with its valid_state' premise fixed to valid'_t'. *)
  note umr4 = umr3[OF valid'_t']
  (* Derive: user_mem at t equals user_mem' at t'; *)
  have post: "user_mem t = user_mem' t'"
  (* ...from umr4 with its valid_state premise fixed to valid_t, tidied by simp. *)
    using umr4[OF valid_t] by simp

  (* Conclude the goal from pre, post, and step, closed automatically. *)
  from pre post step show ?thesis by blast
(* End the proof. *)
qed

(*
 * For a real kernel_entry/kernelEntry step - the register-context
 * save/restore wrapped around call_kernel/callKernel, see
 * AMP_UserData_Refine_C.thy's comment on kernel_entry_user_mem_C_agrees -
 * user_mem (abstract) and user_mem' (design spec) agree both before the
 * step and after it, exactly as call_kernel_user_mem_agrees says for the
 * bare call_kernel/callKernel step above.
 *
 * Three existing, unmodified l4v facts compose to give this directly, at
 * the same kernel_entry/kernelEntry granularity - no decomposition into the
 * inner call_kernel/callKernel step is needed here. entry_corres
 * (proof/refine/RISCV64/Refine.thy) relates kernel_entry and kernelEntry
 * the same way kernel_corres relates call_kernel and callKernel: a real
 * kernelEntry step's end state is always related, by state_relation, to
 * some real kernel_entry step's end state. kernel_entry_invs (same file)
 * and kernelEntry_invs' (same file) say kernel_entry and kernelEntry each
 * preserve their own invariant - einvs and invs' - across the whole entry,
 * including the save/restore wrapping, which supplies valid_state /
 * valid_state' at the end state exactly as akernel_invs_det_ext and
 * ckernel_invs did for call_kernel_user_mem_agrees above.
 *
 * This is the abstract-to-design-spec half of transporting UserData memory
 * confinement to the real kernel, at kernel_entry granularity. Composing it
 * with kernel_entry_user_mem_C_agrees (AMP_UserData_Refine_C.thy) closes
 * the design-spec-to-C half at the same granularity; composing both with
 * an entry-level abstract confinement fact is the remaining assembly step
 * (see PLAN.md).
 *)
(* The lemma named kernel_entry_user_mem_agrees: *)
lemma kernel_entry_user_mem_agrees:
  (* Assume: s and s' are a related pair - one abstract state, one design-spec state. *)
  assumes rel: "(s, s') \<in> state_relation"
  (*
   * Assume: s satisfies einvs; and, if event is not Interrupt, s's current
   * thread is running; and s's current thread is running or idle; and s's
   * scheduler action is resume_cur_thread; and s's domain time is positive,
   * and its domain list is valid.
   *)
  assumes preA: "(einvs and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running s) and (ct_running or ct_idle)
                  and (\<lambda>s. scheduler_action s = resume_cur_thread)
                  and (\<lambda>s. 0 < domain_time s \<and> valid_domain_list s)) s"
  (*
   * Assume: s' satisfies invs'; and, if event is not Interrupt, s''s current
   * thread is running; and s''s current thread is running or idle; and s''s
   * scheduler action is ResumeCurrentThread; and s''s domain time is
   * positive.
   *)
  assumes preH: "(invs' and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running' s) and (ct_running' or ct_idle')
                  and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
                  and (\<lambda>s. 0 < ksDomainTime s)) s'"
  (* Assume: running kernelEntry on event from s' with initial context tc can produce some result tc' and end state t'. *)
  assumes exec: "(tc', t') \<in> fst (kernelEntry event tc s')"
  (*
   * Conclusion: the abstract and design-spec UserData memory agree at s and
   * s'; and there exists an abstract execution of kernel_entry on event
   * from s with initial context tc, with the same result tc' and some end
   * state t, such that t is related to t' by state_relation; and t's
   * UserData memory agrees with t'.
   *)
  shows "user_mem s = user_mem' s'
         \<and> (\<exists>t. (tc', t) \<in> fst (kernel_entry event tc s) \<and> (t, t') \<in> state_relation
                 \<and> user_mem t = user_mem' t')"
(* Begin a structured proof. *)
proof -
  (* Derive: s satisfies invs; *)
  have invs_s: "invs s"
    using preA by (simp add: pred_conj_def)
  (* Derive: s' satisfies invs'; *)
  have invs'_s': "invs' s'"
    using preH by (simp add: pred_conj_def)
  (* Name valid_s: s is valid_state, from invs_s. *)
  note valid_s = invs_valid_stateI[OF invs_s]
  (* Name valid'_s': s' is valid_state', from invs'_s'. *)
  note valid'_s' = invs_valid_stateI'[OF invs'_s']
  (* Name umr1: user_mem_relation, with its state_relation premise fixed to rel. *)
  note umr1 = user_mem_relation[OF rel]
  (* Name umr2: umr1, with its valid_state' premise fixed to valid'_s'. *)
  note umr2 = umr1[OF valid'_s']
  (* Derive: user_mem at s equals user_mem' at s'; *)
  have pre: "user_mem s = user_mem' s'"
    using umr2[OF valid_s] by simp

  (*
   * entry_corres and kernel_entry_invs share the abstract-side precondition
   * shape below, but entry_corres and kernelEntry_invs' state the
   * design-spec side in two different conjunct orders - each reshaped
   * fact below is named for the l4v lemma whose exact term it feeds.
   *)
  (* Derive: s satisfies the precondition entry_corres and kernel_entry_invs both need, from preA. *)
  have preA_entry: "(einvs and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running s)
                     and (\<lambda>s. 0 < domain_time s) and valid_domain_list and (ct_running or ct_idle)
                     and (\<lambda>s. scheduler_action s = resume_cur_thread)) s"
    using preA by (auto simp add: pred_conj_def)
  (* Derive: s' satisfies the precondition entry_corres needs, from preH. *)
  have preH_ec: "(invs' and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running' s)
                  and (\<lambda>s. 0 < ksDomainTime s) and (ct_running' or ct_idle')
                  and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)) s'"
    using preH by (auto simp add: pred_conj_def)
  (* Derive: s' satisfies the precondition kernelEntry_invs' needs, from preH. *)
  have preH_entry: "(invs' and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running' s)
                     and (ct_running' or ct_idle')
                     and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
                     and (\<lambda>s. 0 < ksDomainTime s)) s'"
    using preH by (auto simp add: pred_conj_def)

  (* Name ec0: corres_underlyingD2, with its correspondence premise fixed to entry_corres instantiated at event and tc. *)
  note ec0 = corres_underlyingD2[OF entry_corres[of event tc]]
  (* Name ec1: ec0, with its state-relatedness premise fixed to rel. *)
  note ec1 = ec0[OF rel]
  (* Name ec2: ec1, with its abstract-precondition premise fixed to preA_entry. *)
  note ec2 = ec1[OF preA_entry]
  (* Name ec3: ec2, with its design-spec-precondition premise fixed to preH_ec. *)
  note ec3 = ec2[OF preH_ec]
  (* Name ec4: ec3, with its execution premise fixed to exec. *)
  note ec4 = ec3[OF exec]
  (* Obtain: some abstract result and end state t, such that (tc', t) is a possible result of kernel_entry on event from s, and t is related to t' by state_relation; *)
  obtain t where step: "(tc', t) \<in> fst (kernel_entry event tc s)" "(t, t') \<in> state_relation"
    using ec4 by fastforce

  (* Name uv0: use_valid, with its Hoare-triple premise fixed to kernel_entry_invs, execution premise left open. *)
  note uv0 = use_valid[OF _ kernel_entry_invs]
  (* Name uv1: uv0, with its execution premise fixed to step's first part. *)
  note uv1 = uv0[OF step(1)]
  (* Derive: t satisfies invs; *)
  have invs_t: "invs t"
    using uv1[OF preA_entry] by (simp add: pred_conj_def)

  (* Name uv0': use_valid, with its Hoare-triple premise fixed to kernelEntry_invs', execution premise left open. *)
  note uv0' = use_valid[OF _ kernelEntry_invs']
  (* Name uv1': uv0', with its execution premise fixed to exec. *)
  note uv1' = uv0'[OF exec]
  (* Derive: t' satisfies invs'; *)
  have invs'_t': "invs' t'"
    using uv1'[OF preH_entry] by (simp add: pred_conj_def)

  (* Name valid_t: t is valid_state, from invs_t. *)
  note valid_t = invs_valid_stateI[OF invs_t]
  (* Name valid'_t': t' is valid_state', from invs'_t'. *)
  note valid'_t' = invs_valid_stateI'[OF invs'_t']
  (* Name umr3: user_mem_relation, with its state_relation premise fixed to step's second part. *)
  note umr3 = user_mem_relation[OF step(2)]
  (* Name umr4: umr3, with its valid_state' premise fixed to valid'_t'. *)
  note umr4 = umr3[OF valid'_t']
  (* Derive: user_mem at t equals user_mem' at t'; *)
  have post: "user_mem t = user_mem' t'"
    using umr4[OF valid_t] by simp

  (* Conclude the goal from pre, post, and step, closed automatically. *)
  from pre post step show ?thesis by blast
(* End the proof. *)
qed

end
