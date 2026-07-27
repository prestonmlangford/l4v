(*
 * PolarFire verified multicore (AMP) -- the integrity connection layer.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * WHAT THIS THEORY IS FOR.  Phases 2-6 all carry `amp_step c m m' bp`
 * (AMP_Spatial.thy) as a HYPOTHESIS: "core c's step changed only frames core c
 * owns".  Nothing in the AMP tree ever established it for a real seL4 step, so
 * every result above it was conditional on an unpaid debt.  This theory pays
 * the conceptual half of that debt by proving that `amp_step` IS seL4's
 * `integrity`, projected onto frames.
 *
 * WHAT IT DOES NOT DO, stated first (see multicore-amp-plan.md section 9).
 *
 *   1. It does NOT make `amp_step` unconditional, and it does not remove
 *      `amp_step` from any Phase 2-6 theorem's hypotheses.  What exists after
 *      this theory is a theorem saying WHAT WOULD discharge it, with an l4v
 *      constant in the proof.  Lifting that to "every ADT_A step of core c
 *      satisfies amp_step" needs the per-core invariant (plan items I4/I5) and
 *      is not attempted here.
 *   2. It does NOT discharge A-THR.  `integrity aag` confines a step to
 *      `pasSubject aag`'s authority.  Getting `amp_step` needs ONE LABEL PER
 *      CORE (what `amp_pas` below builds); getting A-THR needs ONE LABEL PER
 *      THREAD, which is a different PAS with a configuration-dependent
 *      `pas_refined` obligation.  A-THR is a second instantiation of the same
 *      l4v theorem, not a free rider on this one.
 *   3. It does NOT touch the blocked-sender fact (`sender_quiescent` / A-BLK),
 *      which is untouched and still unsatisfiable.  REQ-MSG-8 remains vacuous.
 *
 * THE THREE FACTS THAT MAKE THE CONNECTION CHEAP.  `integrity_mem`
 * (Access.thy:829) has five introduction rules, and seL4's integrity is
 * therefore strictly WEAKER than "writes only frames you own".  Three of the
 * five are neutralised here rather than reasoned around:
 *
 *   - `trm_orefl` is the no-change case, which `changed_frames` has excluded by
 *     construction.
 *   - `trm_globals` fires on `p \<in> globals`, and `globals` is the free variable
 *     X of `call_kernel_integrity`.  Instantiating X = {} makes the rule
 *     unfirable.  No disjointness proof about the kernel's globals is needed.
 *   - `trm_ipc` needs a thread `p'` labelled OUTSIDE the subject.  Under a
 *     one-label-per-core PAS every TCB in core c's kheap is labelled `Core c`,
 *     so the premise is false.  That is the `tcbs_labelled` side condition
 *     below -- a fact about the state, discharged with the invariant in I4/I5,
 *     assumed here.
 *
 * That leaves `trm_lrefl` and `trm_write`, and both land exactly on
 * `owned_frames`, which is what `amp_step` asks for.
 *
 * THE ALIGNMENT TRAP, recorded because it is not obvious.  `changed_frames`
 * quantifies over EVERY obj_ref, not over page-aligned ones.  A memory
 * projection without the `is_aligned` guard in `mem_proj` below would report a
 * single changed byte as a change to every unaligned address whose page window
 * covers it, and `changed_frames \<subseteq> owned_frames` would fail for reasons that
 * have nothing to do with integrity.  The guard makes `changed_frames` land
 * exactly on the set of page-aligned frames whose contents changed.
 *
 * Note also `amp_frames_aligned`: it is NOT a hypothesis of the main theorem,
 * because it is not needed for soundness.  A partition with unaligned frames
 * would make `amp_label_of` constantly `Unowned`, integrity would then forbid
 * every change, and the theorem would hold DEGENERATELY.  The predicate is
 * defined and used in the examples section for exactly that reason: it is what
 * separates the real statement from the degenerate one.
 *
 * Session placement: this session is parented on `Access` (= AInvs = ASpec) and
 * pulls the AMP theories in via `sessions`, so nothing already green is
 * rebuilt.  `InfoFlow` is deliberately not needed.
 *
 * Organised in the usual four zones: SPECIFICATION, PROOF DEVELOPMENT,
 * RESULTS, EXAMPLES.
 *)

theory AMP_Integrity
imports
  "Access.ArchADT_AC"
  "AMP_Channel_AC.AMP_Channel_AC"
begin

section \<open>Specification\<close>

subsection \<open>Frames, and the projection of seL4 memory onto the AMP model\<close>

(* The page-aligned base address of the frame containing a byte address. seL4's
   `underlying_memory` is byte-addressed, while the AMP model is frame-addressed
   (obj_ref standing for a frame base), so every crossing between the two levels
   goes through this function. *)
definition frame_of :: "obj_ref \<Rightarrow> obj_ref" where
  "frame_of p = p AND NOT (mask pageBits)"

(* The AMP abstract model's system memory, read off a real seL4 state. The
   abstract model's memory has type `obj_ref \<Rightarrow> 'v` with 'v left polymorphic
   (AMP_Spatial.thy); this instantiates 'v to a frame's worth of bytes, so no
   Phase 2-6 statement changes shape.

   The `is_aligned` guard is load-bearing, not defensive: without it a single
   changed byte would count as a change to every unaligned address whose page
   window covers it, and `changed_frames` would leave `owned_frames` for reasons
   unrelated to integrity. With it, `changed_frames (mem_proj s) (mem_proj s')`
   is exactly the set of page-aligned frames whose contents differ. *)
definition mem_proj :: "det_state \<Rightarrow> obj_ref \<Rightarrow> (machine_word \<Rightarrow> word8)" where
  "mem_proj s f = (\<lambda>off. if is_aligned f pageBits \<and> off < 2 ^ pageBits
                         then underlying_memory (machine_state s) (f + off)
                         else 0)"

(* A partition whose declared frames really are page frames. Not required for
   the soundness of the results below -- an unaligned partition makes every
   label `Unowned`, under which integrity forbids all change and the main
   theorem holds vacuously -- but required for those results to say anything.
   Kept separate from `amp_partition_wf` on purpose: adding a conjunct there
   would invalidate every existing well-formedness witness. *)
definition amp_frames_aligned :: "amp_partition \<Rightarrow> bool" where
  "amp_frames_aligned bp \<equiv> \<forall>c. \<forall>f \<in> owned_frames bp c. is_aligned f pageBits"

subsection \<open>The per-core PAS\<close>

(* The AMP access-control labels: one per core, plus a label for memory the
   partition assigns to nobody. One label PER CORE is the design decision that
   makes this connection tractable -- it collapses `pas_refined`'s
   `state_objs_in_policy` to self-loops and makes `guarded_pas_domain`,
   `pas_cur_domain`, `is_subject o cur_thread` and `tcb_domain_map_wellformed`
   automatic. It is also precisely why this theory cannot reach A-THR, which
   needs thread-granular labels. *)
datatype amp_label = Core core_id | Unowned

(* The core a frame belongs to, if any: the core holding it privately, or -- for
   a declared channel buffer -- the channel's SENDER. Under a well-formed
   partition both descriptions are unique (private frames are pairwise disjoint;
   distinct channels have disjoint buffers), which is what makes the two
   definite descriptions well-defined; `owner_core_priv` and
   `owner_core_buffer` below discharge that.

   Labelling a buffer by its sender, not its receiver, is deliberate: the
   receiver reaches the same frame through `owned_frames` (which includes the
   buffers of every channel the core is an endpoint of, in either direction), so
   nothing is lost, while the WRITE authority stays with exactly one label. *)
definition owner_core :: "amp_partition \<Rightarrow> obj_ref \<Rightarrow> core_id option" where
  "owner_core bp f =
     (if \<exists>c. \<exists>r. ap_cores bp c = Some r \<and> f \<in> cr_frames r
      then Some (THE c. \<exists>r. ap_cores bp c = Some r \<and> f \<in> cr_frames r)
      else if \<exists>ch \<in> ap_channels bp. f \<in> ch_buffer ch
      then Some (ch_from (THE ch. ch \<in> ap_channels bp \<and> f \<in> ch_buffer ch))
      else None)"

(* The label of a byte address: the label of the frame containing it. This is
   the object labelling seL4's `integrity_mem` indexes memory by. *)
definition amp_label_of :: "amp_partition \<Rightarrow> obj_ref \<Rightarrow> amp_label" where
  "amp_label_of bp p =
     (case owner_core bp (frame_of p) of Some c \<Rightarrow> Core c | None \<Rightarrow> Unowned)"

(* The AMP authority policy in seL4's own `auth_graph` vocabulary: every core
   has full authority over its own label, and a channel's receiver additionally
   has Read on the sender's label. There is deliberately NO cross-core Write
   edge -- that absence is what `trm_write` consumes in the main theorem, and it
   is the same claim Phase 5's `amp_auth_graph` makes in AMP vocabulary (see
   `amp_pas_write_authority_iff` below, which shows the two agree). *)
definition amp_policy :: "amp_partition \<Rightarrow> (amp_label \<times> auth \<times> amp_label) set" where
  "amp_policy bp =
     {(Core c, a, Core c) | c a. True}
   \<union> {(Core (ch_to ch), Read, Core (ch_from ch)) | ch. ch \<in> ap_channels bp}"

(* The policy-and-authority structure seL4's access-control proofs are stated
   relative to, instantiated for one core of an AMP system. `pasMayActivate` and
   `pasMayEditReadyQueues` are True because `call_kernel_integrity` requires
   them; they weaken the integrity conclusion only about thread activation and
   ready queues, neither of which is memory, so `amp_step` is unaffected. *)
definition amp_pas :: "amp_partition \<Rightarrow> core_id \<Rightarrow> amp_label PAS" where
  "amp_pas bp c =
     \<lparr> pasObjectAbs = amp_label_of bp,
       pasASIDAbs = \<lambda>_. Core c,
       pasIRQAbs = \<lambda>_. Core c,
       pasPolicy = amp_policy bp,
       pasSubject = Core c,
       pasMayActivate = True,
       pasMayEditReadyQueues = True,
       pasMaySendIrqs = True,
       pasDomainAbs = \<lambda>_. {Core c} \<rparr>"

subsection \<open>The one side condition on the state\<close>

(* Every thread present in this core's kernel state belongs to this core.

   This is what makes `integrity_mem`'s `trm_ipc` rule unfirable: that rule
   needs a thread labelled OUTSIDE the subject, and in an AMP system each
   kernel's kheap holds only its own core's threads. It is a fact about the
   STATE, not a new assumption about the world -- it follows from `invs` plus
   the partition, and is discharged with the per-core invariant in plan items
   I4/I5. It is a hypothesis here because that invariant does not exist yet. *)
definition tcbs_labelled :: "amp_partition \<Rightarrow> core_id \<Rightarrow> det_state \<Rightarrow> bool" where
  "tcbs_labelled bp c s \<equiv> \<forall>t tcb. get_tcb t s = Some tcb \<longrightarrow> amp_label_of bp t = Core c"

section \<open>Proof development (internal machinery)\<close>

subsection \<open>Frames and the projection\<close>

(* An in-page offset added to an aligned frame base does not leave the frame.
   The arithmetic crossing point between byte-addressed seL4 memory and
   frame-addressed AMP memory; everything else about `frame_of` follows. *)
lemma frame_of_aligned_add:
  "\<lbrakk> is_aligned f pageBits; (off :: machine_word) < 2 ^ pageBits \<rbrakk> \<Longrightarrow> frame_of (f + off) = f"
  by (simp add: frame_of_def is_aligned_add_helper)

(* An aligned address is its own frame. *)
lemma frame_of_aligned:
  "is_aligned f pageBits \<Longrightarrow> frame_of f = f"
  by (simp add: frame_of_def is_aligned_neg_mask_eq)

(* The projection's changed set, in usable form: a frame appears exactly when it
   is page-aligned and some byte inside it differs. Both halves matter -- the
   alignment half is what keeps `changed_frames` inside the partition's
   vocabulary, the witness half is what feeds the integrity case analysis. *)
lemma changed_frames_mem_proj:
  "f \<in> changed_frames (mem_proj s) (mem_proj s')
     \<longleftrightarrow> is_aligned f pageBits
         \<and> (\<exists>off < 2 ^ pageBits. underlying_memory (machine_state s) (f + off)
                                  \<noteq> underlying_memory (machine_state s') (f + off))"
  by (fastforce simp: changed_frames_def mem_proj_def fun_eq_iff split: if_splits)

subsection \<open>The owner map is well defined\<close>

(* A privately held frame is owned by the core that holds it. The definite
   description in `owner_core` is justified here: two cores holding the same
   private frame would violate the partition's first conjunct. *)
lemma owner_core_priv:
  assumes wf: "amp_partition_wf bp" and ac: "ap_cores bp c = Some r" and f: "f \<in> cr_frames r"
  shows "owner_core bp f = Some c"
proof -
  have ex: "\<exists>c. \<exists>r. ap_cores bp c = Some r \<and> f \<in> cr_frames r" using ac f by blast
  have "(THE c'. \<exists>r'. ap_cores bp c' = Some r' \<and> f \<in> cr_frames r') = c"
  proof (rule the_equality)
    show "\<exists>r'. ap_cores bp c = Some r' \<and> f \<in> cr_frames r'" using ac f by blast
  next
    fix c' assume "\<exists>r'. ap_cores bp c' = Some r' \<and> f \<in> cr_frames r'"
    then obtain r' where ac': "ap_cores bp c' = Some r'" and f': "f \<in> cr_frames r'" by blast
    show "c' = c"
      using amp_partition_wf_private_disjoint[OF wf ac' ac] f f' by blast
  qed
  with ex show ?thesis by (simp add: owner_core_def)
qed

(* A channel buffer frame is owned by that channel's sender. The definite
   description is justified by `wf_buffer_unique` (buffers of distinct channels
   are disjoint); the first branch of `owner_core` cannot intervene because a
   buffer is never private (partition conjunct 3). *)
lemma owner_core_buffer:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
  shows "owner_core bp f = Some (ch_from ch)"
proof -
  have npriv: "\<not> (\<exists>c. \<exists>r. ap_cores bp c = Some r \<and> f \<in> cr_frames r)"
    using amp_partition_wf_buffer_not_private[OF wf ch] f by blast
  have ex: "\<exists>ch' \<in> ap_channels bp. f \<in> ch_buffer ch'" using ch f by blast
  have the_ch: "(THE ch'. ch' \<in> ap_channels bp \<and> f \<in> ch_buffer ch') = ch"
    using wf_buffer_unique[OF wf _ ch _ f] ch f by blast
  have "owner_core bp f = Some (ch_from (THE ch'. ch' \<in> ap_channels bp \<and> f \<in> ch_buffer ch'))"
    by (simp add: owner_core_def npriv ex)
  with the_ch show ?thesis by simp
qed

(* The converse, and the only direction the main theorem needs: whatever the
   owner map attributes to core c really is a frame core c owns. Both branches
   land inside `owned_frames` -- the private branch directly, the buffer branch
   because the sender is one of the channel's endpoints. *)
lemma owner_core_owned:
  assumes wf: "amp_partition_wf bp" and oc: "owner_core bp f = Some c"
  shows "f \<in> owned_frames bp c"
proof (cases "\<exists>c'. \<exists>r. ap_cores bp c' = Some r \<and> f \<in> cr_frames r")
  case True
  then obtain c' r where ac: "ap_cores bp c' = Some r" and fr: "f \<in> cr_frames r" by blast
  from owner_core_priv[OF wf ac fr] oc have "c' = c" by simp
  with ac fr show ?thesis by (simp add: owned_frames_def)
next
  case notpriv: False
  show ?thesis
  proof (cases "\<exists>ch \<in> ap_channels bp. f \<in> ch_buffer ch")
    case True
    then obtain ch where ch: "ch \<in> ap_channels bp" and fb: "f \<in> ch_buffer ch" by blast
    from owner_core_buffer[OF wf ch fb] oc have "ch_from ch = c" by simp
    with ch fb show ?thesis
      by (fastforce simp: owned_frames_def channel_endpoints_def)
  next
    case nobuf: False
    have "owner_core bp f = None" by (simp add: owner_core_def notpriv nobuf)
    with oc show ?thesis by simp
  qed
qed

(* The form the case analysis actually uses: a byte address labelled `Core c`
   sits in a frame core c owns. *)
lemma amp_label_of_owned:
  assumes wf: "amp_partition_wf bp" and lbl: "amp_label_of bp p = Core c"
  shows "frame_of p \<in> owned_frames bp c"
proof -
  from lbl have "owner_core bp (frame_of p) = Some c"
    by (simp add: amp_label_of_def split: option.splits)
  from owner_core_owned[OF wf this] show ?thesis .
qed

subsection \<open>What the policy does and does not permit\<close>

(* THE structural fact about `amp_policy`: its only cross-label edge carries
   `Read`, so any other authority is confined to a single label, and that label
   is always a core's (never `Unowned`, which holds no authority at all). Eight
   of `policy_wellformed`'s nine conjuncts reduce to this one lemma. *)
lemma amp_policy_nonread_self:
  "\<lbrakk> (x, a, y) \<in> amp_policy bp; a \<noteq> Read \<rbrakk> \<Longrightarrow> \<exists>c. x = Core c \<and> y = Core c"
  by (auto simp: amp_policy_def)

(* A core holds every authority over its own label. The consequent of every
   `policy_wellformed` conjunct is a self-loop, so this is what closes them. *)
lemma amp_policy_self: "(Core c, a, Core c) \<in> amp_policy bp"
  by (auto simp: amp_policy_def)

(* The policy grants Write only within a label. This is the whole content of
   `trm_write` for us: a core's write authority never crosses a label boundary,
   because the only cross-label edges `amp_policy` contains are the receivers'
   Read edges. *)
lemma amp_policy_write_self:
  "(Core c, Write, l) \<in> amp_policy bp \<Longrightarrow> l = Core c"
  using amp_policy_nonread_self by fastforce

(* Both permissive integrity rules -- "the address carries the subject's own
   label" and "the subject has Write authority over it" -- give the same
   conclusion under this PAS. *)
lemma amp_pas_write_or_self_owned:
  assumes wf: "amp_partition_wf bp"
      and w: "pasObjectAbs (amp_pas bp c) p = pasSubject (amp_pas bp c)
              \<or> aag_subjects_have_auth_to {pasSubject (amp_pas bp c)} (amp_pas bp c) Write p"
  shows "frame_of p \<in> owned_frames bp c"
proof -
  from w have "amp_label_of bp p = Core c"
    by (auto simp: amp_pas_def dest: amp_policy_write_self)
  from amp_label_of_owned[OF wf this] show ?thesis .
qed

section \<open>Results\<close>

subsection \<open>J1 -- the per-core policy is well formed\<close>

(* The first of `pas_refined`'s six conjuncts, and the only one that holds with
   no hypotheses at all: no partition well-formedness, no state, nothing. It is
   also the one that could have refuted this whole design. `policy_wellformed`'s
   first conjunct forbids the subject from holding `Control` over any label but
   its own, and `amp_policy` deliberately gives a channel's receiver an authority
   over its SENDER's label -- if that authority had been anything other than
   `Read`, a core-granular PAS would have been unusable and
   `integrity_imp_amp_step` with it.
 *
 * Eight of the nine conjuncts have a non-`Read` authority in the antecedent, so
 * `amp_policy_nonread_self` collapses both endpoints to one core label and the
 * consequent is then a self-loop (`amp_policy_self`). The remaining conjunct is
 * the bare self-loop requirement. Note this is where `pasMaySendIrqs = True`
 * gets paid for: it enables the fourth conjunct, which survives only because
 * `Notify \<noteq> Read`. *)
theorem amp_pas_wellformed: "pas_wellformed (amp_pas bp c)"
  unfolding policy_wellformed_def amp_pas_def
  by simp (intro conjI allI impI;
           fastforce dest: amp_policy_nonread_self intro: amp_policy_self)

subsection \<open>I2 -- the PAS agrees with Phase 5's authority graph\<close>

(* The connection is only real if the policy stated here in seL4's vocabulary is
   the SAME policy Phase 5 states in AMP vocabulary, rather than a similar one.
   On a channel buffer frame the two coincide exactly: this PAS gives core c
   Write authority over the frame's label iff Phase 2's enforced permission map
   gives c PermRW on that frame, iff Phase 5's authority graph carries c's XSend
   edge for that channel. Chaining through `amp_auth_graph_write_iff` is what
   makes that a theorem rather than a claim in a comment. *)
theorem amp_pas_write_authority_iff:
  assumes wf: "amp_partition_wf bp" and al: "amp_frames_aligned bp"
      and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
  shows "(Core c, Write, pasObjectAbs (amp_pas bp c) f) \<in> pasPolicy (amp_pas bp c)
           \<longleftrightarrow> (c, XSend, ch) \<in> amp_auth_graph bp"
proof -
  \<comment> \<open>the label of a FRAME is the label of its own base address, which needs the
      frame to be page-aligned -- this is where `amp_frames_aligned` earns its keep\<close>
  have "f \<in> owned_frames bp (ch_from ch)"
    using ch f by (fastforce simp: owned_frames_def channel_endpoints_def)
  with al have "is_aligned f pageBits" by (simp add: amp_frames_aligned_def)
  from frame_of_aligned[OF this] have ff: "frame_of f = f" .
  have lbl: "amp_label_of bp f = Core (ch_from ch)"
    using owner_core_buffer[OF wf ch f] by (simp add: amp_label_of_def ff)
  show ?thesis
  proof
    assume "(Core c, Write, pasObjectAbs (amp_pas bp c) f) \<in> pasPolicy (amp_pas bp c)"
    with lbl have "c = ch_from ch"
      by (auto simp: amp_pas_def dest: amp_policy_write_self)
    with ch show "(c, XSend, ch) \<in> amp_auth_graph bp" by (simp add: amp_auth_graph_def)
  next
    assume "(c, XSend, ch) \<in> amp_auth_graph bp"
    with wf ch f have "frame_perm bp c f = PermRW" by (simp add: amp_auth_graph_write_iff)
    with buffer_perm_only_endpoints[OF wf ch f, of c] buffer_perm_asymmetric[OF wf ch f]
    have "c = ch_from ch" by (cases "c = ch_from ch"; cases "c = ch_to ch") auto
    with lbl show "(Core c, Write, pasObjectAbs (amp_pas bp c) f) \<in> pasPolicy (amp_pas bp c)"
      by (auto simp: amp_pas_def amp_policy_def)
  qed
qed

subsection \<open>I3 -- amp_step is seL4's integrity, projected onto frames\<close>

(* THE RESULT OF THIS THEORY.  If a real seL4 state pair on core c satisfies
   seL4's own `integrity` for that core's PAS with an empty globals set, then
   the memory change it induces on the AMP abstract model is an `amp_step` for
   core c -- the hypothesis every Phase 2-6 theorem carries.
 *
 * Read the hypotheses as the price:
 *   - `amp_partition_wf bp` is Phase 1's existing well-formedness;
 *   - `tcbs_labelled bp c s` says core c's kernel holds only core c's threads,
 *     a state fact to be discharged with the per-core invariant (I4/I5);
 *   - `integrity (amp_pas bp c) {} s s'` is the CONCLUSION of
 *     `call_kernel_integrity` (Syscall_AC.thy:1311) and of
 *     `do_user_op_respects` (ADT_AC.thy:89), instantiated at X = {}.
 *
 * The globals set is {} rather than an arbitrary X, which is what makes
 * `trm_globals` unfirable; X is schematic in both l4v lemmas, so this costs
 * nothing.  What is NOT here is the discharge of those lemmas' preconditions --
 * `einvs`, `pas_refined`, `schact_is_rct` and the rest -- which is I4/I5. Until
 * then this theorem says what would discharge `amp_step`, not that it is
 * discharged. *)
theorem integrity_imp_amp_step:
  assumes wf: "amp_partition_wf bp"
      and tcbs: "tcbs_labelled bp c s"
      and integ: "integrity (amp_pas bp c) {} s s'"
  shows "amp_step c (mem_proj s) (mem_proj s') bp"
  unfolding amp_step_def
proof
  fix f assume "f \<in> changed_frames (mem_proj s) (mem_proj s')"
  then obtain off where al: "is_aligned f pageBits" and lt: "off < 2 ^ pageBits"
    and diff: "underlying_memory (machine_state s) (f + off)
                 \<noteq> underlying_memory (machine_state s') (f + off)"
    by (auto simp: changed_frames_mem_proj)
  let ?p = "f + off"
  from integ
  have "integrity_mem (amp_pas bp c) {pasSubject (amp_pas bp c)} ?p
          (tcb_states_of_state s) (tcb_states_of_state s') (auth_ipc_buffers s) {}
          (underlying_memory (machine_state s) ?p) (underlying_memory (machine_state s') ?p)"
    by (simp add: integrity_subjects_def)
  then have "frame_of ?p \<in> owned_frames bp c"
  proof (cases rule: integrity_mem.cases)
    case trm_lrefl
    \<comment> \<open>the address carries the subject's own label\<close>
    thus ?thesis using amp_pas_write_or_self_owned[OF wf] by simp
  next
    case trm_orefl
    \<comment> \<open>excluded: `changed_frames` already witnessed a difference here\<close>
    thus ?thesis using diff by simp
  next
    case trm_write
    \<comment> \<open>the subject has Write authority, which `amp_policy` keeps inside its label\<close>
    thus ?thesis using amp_pas_write_or_self_owned[OF wf] by simp
  next
    case trm_globals
    \<comment> \<open>unfirable: the globals set was instantiated to the empty set\<close>
    thus ?thesis by simp
  next
    case (trm_ipc p')
    \<comment> \<open>unfirable: an IPC buffer belongs to a TCB, and every TCB here is core c's\<close>
    from trm_ipc have "auth_ipc_buffers s p' \<noteq> {}" by blast
    then obtain tcb where "get_tcb p' s = Some tcb"
      by (fastforce simp: RISCV64.auth_ipc_buffers_def split: option.splits)
    with tcbs have "amp_label_of bp p' = Core c" by (simp add: tcbs_labelled_def)
    with trm_ipc show ?thesis by (simp add: amp_pas_def)
  qed
  with al lt show "f \<in> owned_frames bp c" by (simp add: frame_of_aligned_add)
qed

section \<open>Examples\<close>

subsection \<open>The example partition is made of real page frames\<close>

(* Phase 1's two-core witness satisfies the alignment condition, so the results
   above are not degenerate on it: its declared frames are genuine page frames
   and therefore actually receive core labels. *)
lemma example2_frames_aligned: "amp_frames_aligned example2"
  by (auto simp: amp_frames_aligned_def owned_frames_def example2_def core0_res_def
                 core1_res_def chan01_def channel_endpoints_def is_aligned_def
                 RISCV64.pageBits_def)

subsection \<open>Labels are not all Unowned\<close>

(* Non-degeneracy, the half that a green build cannot detect. If `amp_label_of`
   were constantly `Unowned`, `integrity` would forbid every memory change and
   `integrity_imp_amp_step` would be true for the empty reason. It is not: in
   the example partition, core 0's private frame is labelled `Core 0` and the
   channel buffer is labelled with its SENDER, core 0 -- so real addresses do
   carry real core labels, and the write-authority rules above have something to
   fire on. *)
lemma example2_label_private: "amp_label_of example2 0x1000 = Core 0"
  by (simp add: amp_label_of_def frame_of_def owner_core_def example2_def core0_res_def
                core1_res_def chan01_def is_aligned_def mask_eq_decr_exp RISCV64.pageBits_def)

(* The same for the shared frame, and the case that carries the design decision:
   a channel buffer takes its SENDER's label, so core 0 -- the writer -- holds
   the write authority over it and core 1 reaches it only through
   `owned_frames`. This is what keeps `trm_write` from crossing a core boundary
   on the one frame two cores can both see. *)
lemma example2_label_buffer: "amp_label_of example2 0x8000 = Core 0"
proof -
  have ch: "chan01 \<in> ap_channels example2" by (simp add: example2_def)
  have fb: "(0x8000 :: obj_ref) \<in> ch_buffer chan01" by (simp add: chan01_def)
  have ff: "frame_of (0x8000 :: obj_ref) = 0x8000"
    by (simp add: frame_of_def mask_eq_decr_exp RISCV64.pageBits_def)
  from owner_core_buffer[OF example2_partition_wf ch fb]
  show ?thesis by (simp add: amp_label_of_def ff chan01_def)
qed

subsection \<open>The integrity constraint has teeth, and does not forbid everything\<close>

(* The other half of non-degeneracy, and the one the merge gate cannot see. The
   theorem above is an implication from `integrity`; it would be equally green if
   `integrity` at this PAS were unsatisfiable (permitting nothing, so no step
   ever has to be checked) or trivially true (permitting everything, so
   `owned_frames` were no constraint). These two lemmas show it is neither, on
   the memory conjunct that `integrity_imp_amp_step` actually consumes.

   PERMISSIVE HALF: a write inside core 0's own private frame is allowed, by
   `trm_lrefl`, for ANY pair of values -- so core 0 can still do work. *)
lemma example2_integrity_mem_permits_own:
  "integrity_mem (amp_pas example2 0) {Core 0} 0x1000 ts ts' ipcbufs {} w w'"
  by (rule integrity_mem.trm_lrefl)
     (simp add: amp_pas_def example2_label_private)

(* RESTRICTIVE HALF: a write to core 1's private frame is NOT allowed -- the
   only rule that can still fire is `trm_orefl`, which forces the value to be
   unchanged. `trm_lrefl` fails because the frame carries core 1's label,
   `trm_write` because `amp_policy` has no cross-core Write edge, `trm_globals`
   because the globals set is empty, and `trm_ipc` because no address here is an
   IPC buffer. This is the fact `amp_step` rests on, exhibited concretely. *)
lemma example2_integrity_mem_forbids_other:
  assumes im: "integrity_mem (amp_pas example2 0) {Core 0} 0x3000 ts ts' (\<lambda>_. {}) {} w w'"
  shows "w = w'"
proof -
  have lbl: "amp_label_of example2 0x3000 = Core 1"
  proof -
    have ac: "ap_cores example2 1 = Some core1_res" by (simp add: example2_def)
    have fr: "(0x3000 :: obj_ref) \<in> cr_frames core1_res" by (simp add: core1_res_def)
    have ff: "frame_of (0x3000 :: obj_ref) = 0x3000"
      by (simp add: frame_of_def mask_eq_decr_exp RISCV64.pageBits_def)
    from owner_core_priv[OF example2_partition_wf ac fr]
    show ?thesis by (simp add: amp_label_of_def ff)
  qed
  from im show ?thesis
  proof (cases rule: integrity_mem.cases)
    case trm_lrefl thus ?thesis using lbl by (simp add: amp_pas_def)
  next
    case trm_orefl thus ?thesis .
  next
    case trm_write thus ?thesis
      using lbl by (auto simp: amp_pas_def dest: amp_policy_write_self)
  next
    case trm_globals thus ?thesis by simp
  next
    case (trm_ipc p') thus ?thesis by simp
  qed
qed

end
