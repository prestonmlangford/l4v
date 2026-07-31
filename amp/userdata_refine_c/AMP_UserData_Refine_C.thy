(*
 * Copyright 2026, PolarFire AMP verification.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory AMP_UserData_Refine_C
imports CRefine.Refine_C
begin

section "Specification"

(*
 * No new types or state are introduced here. This theory states a
 * corollary of l4v's existing C-refinement development
 * (proof/crefine/RISCV64/Refine_C.thy, ADT_C.thy), linking the design
 * specification's view of UserData memory to the C specification's view
 * for a real kernelEntry/kernelEntry_C step. This is the design-spec-to-C
 * half of the UserData case; AMP_UserData_Refine.thy (session
 * AMP_UserData_Refine) already gives the abstract-to-design-spec half for
 * the bare call_kernel/callKernel step underneath.
 *)

(*
 * The facts cited below (entry_refinement_C, user_mem_C_relation, rf_sr,
 * all_invs') are only in scope inside l4v's own kernel_m locale context --
 * the same context every other crefine-consuming theory in l4v (including
 * proof/infoflow/) opens to reach them. Opening it here adds no new
 * assumption: kernel_m's own assumptions are existing, unmodified
 * machine-operation correspondence facts from
 * proof/crefine/RISCV64/Machine_C.thy, already relied upon by the whole
 * crefine development this theory builds on.
 *)
context kernel_m
begin

section "Results"

(*
 * For a real kernelEntry/kernelEntry_C step, user_mem' (design spec) and
 * user_mem_C (C) agree both before the step and after it.
 *
 * entry_refinement_C (proof/crefine/RISCV64/Refine_C.thy) is l4v's
 * existing, unmodified proof that a real kernelEntry_C step's end state is
 * always related, by rf_sr, to some real kernelEntry step's end state
 * (kernelEntry itself is the register-context save/restore wrapped around
 * a bare callKernel step - see AMP_UserData_Refine.thy's comment on
 * call_kernel_user_mem_agrees for that inner step). user_mem_C_relation
 * (proof/crefine/RISCV64/ADT_C.thy) says user_mem' and user_mem_C agree at
 * any rf_sr-related pair of states, provided the design-spec state is
 * pspace_distinct'. kernelEntry_invs' (proof/refine/RISCV64/Refine.thy) and
 * the all_invs' precondition itself supply pspace_distinct' at the start
 * and end states respectively (via invs_pspace_distinct',
 * proof/refine/Invariants_H.thy).
 *
 * This composes with AMP_UserData_Refine.thy's call_kernel_user_mem_agrees
 * to reach a C-level fact about a real kernelEntry_C step - but not yet
 * combined into one theorem: see PLAN.md's "Chain the abstract-to-C
 * UserData memory link ..." for that assembly step, still open.
 *)
(* The lemma named kernel_entry_user_mem_C_agrees: *)
lemma kernel_entry_user_mem_C_agrees:
  (* Assume: s satisfies all_invs' for event e - the same precondition entry_refinement_C itself needs. *)
  assumes ai: "all_invs' e s"
  (* Assume: s and t are a related pair - one design-spec state, one C state. *)
  assumes rel: "(s, t) \<in> rf_sr"
  (* Assume: the fastpath flag is off (entry_refinement_C is only stated for fp = False). *)
  assumes fp: "fp = False"
  (* Assume: running kernelEntry_C on event e from t with initial context tc can produce some result tc' and end state t'. *)
  assumes exec: "(tc', t') \<in> fst (kernelEntry_C fp e tc t)"
  (*
   * Conclusion: the design-spec and C UserData memory agree at s and t;
   * and there exists a design-spec execution of kernelEntry on e from s,
   * with the same result tc' and some end state s', such that s' is
   * related to t' by rf_sr; and s''s UserData memory agrees with t'.
   *)
  shows "user_mem_C (globals t) = user_mem' s
         \<and> (\<exists>s'. (tc', s') \<in> fst (kernelEntry e tc s) \<and> (s', t') \<in> rf_sr
                   \<and> user_mem_C (globals t') = user_mem' s')"
(* Begin a structured proof. *)
proof -
  (* Derive: s satisfies invs'; *)
  have invs'_s: "invs' s"
  (* ...from ai, unfolding all_invs' to extract its design-spec conjunct. *)
    using ai by (auto simp: all_invs'_def)
  (* Name dist_s: s is pspace_distinct', from invs'_s. *)
  note dist_s = invs_pspace_distinct'[OF invs'_s]
  (* Derive: the C heap at t agrees with s's UserData objects, via rf_sr. *)
  have cud_s: "cpspace_user_data_relation (ksPSpace s) (underlying_memory (ksMachineState s)) (t_hrs_' (globals t))"
  (* ...from rel, unfolding rf_sr down to its UserData conjunct. *)
    using rel by (clarsimp simp: rf_sr_def cstate_relation_def cpspace_relation_def Let_def)
  (* Derive: user_mem_C at (the globals of) t equals user_mem' at s; *)
  have pre: "user_mem_C (globals t) = user_mem' s"
  (* ...from user_mem_C_relation, with its two premises fixed to cud_s and dist_s. *)
    using user_mem_C_relation[OF cud_s dist_s] .

  (* Name er0: entry_refinement_C, with its all_invs' premise fixed to ai. *)
  note er0 = entry_refinement_C[OF ai]
  (* Name er1: er0, with its rf_sr premise fixed to rel. *)
  note er1 = er0[OF rel]
  (* Name er2: er1, with its fastpath premise fixed to fp. *)
  note er2 = er1[OF fp]
  (* Obtain: some design-spec end state s', such that (tc', s') is a possible result of kernelEntry on e from s, and s' is related to t' by rf_sr; *)
  obtain s' where step: "(tc', s') \<in> fst (kernelEntry e tc s)" "(s', t') \<in> rf_sr"
  (* ...from er2 applied to exec, closed automatically. *)
    using er2 exec by blast

  (* Derive: s satisfies the precondition kernelEntry_invs' needs, from ai. *)
  have pre2: "(invs' and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running' s) and (ct_running' or ct_idle')
               and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
               and (\<lambda>s. 0 < ksDomainTime s)) s"
  (* ...from ai, unfolding all_invs' and rewriting the and-combinator and the nat/word zero-comparison into plain conjunction. *)
    using ai by (auto simp: all_invs'_def pred_conj_def word_neq_0_conv)
  (* Name uv0: use_valid, with its Hoare-triple premise fixed to kernelEntry_invs', execution premise left open. *)
  note uv0 = use_valid[OF _ kernelEntry_invs']
  (* Name uv1: uv0, with its execution premise fixed to step's first part. *)
  note uv1 = uv0[OF step(1)]
  (* Derive: s' satisfies invs'; *)
  have invs'_s': "invs' s'"
  (* ...from uv1 with its precondition premise fixed to pre2, tidied by simp. *)
    using uv1[OF pre2] by (simp add: pred_conj_def)
  (* Name dist_s': s' is pspace_distinct', from invs'_s'. *)
  note dist_s' = invs_pspace_distinct'[OF invs'_s']

  (* Derive: the C heap at t' agrees with s''s UserData objects, via rf_sr. *)
  have cud_s': "cpspace_user_data_relation (ksPSpace s') (underlying_memory (ksMachineState s')) (t_hrs_' (globals t'))"
  (* ...from step's second part, unfolding rf_sr down to its UserData conjunct. *)
    using step(2) by (clarsimp simp: rf_sr_def cstate_relation_def cpspace_relation_def Let_def)
  (* Derive: user_mem_C at (the globals of) t' equals user_mem' at s'; *)
  have post: "user_mem_C (globals t') = user_mem' s'"
  (* ...from user_mem_C_relation, with its two premises fixed to cud_s' and dist_s'. *)
    using user_mem_C_relation[OF cud_s' dist_s'] .

  (* Conclude the goal from pre, step, and post, closed automatically. *)
  from pre step post show ?thesis by blast
(* End the proof. *)
qed

end

end
