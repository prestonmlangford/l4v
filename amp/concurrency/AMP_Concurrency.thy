(*
 * PolarFire verified multicore (AMP) — Phase 6: concurrency core (D1-D3).
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * WHAT THIS PHASE DISCHARGES. Every phase before this one states the channel
 * protocol (xchan_send / xchan_recv_ack, and their message-carrying and
 * thread-owned refinements) as a single ATOMIC step. Phase 5.5's message
 * integrity (M2) and Phase 5.75's discharge of it both reason about "an
 * arbitrary run of steps while the message sits pending" via
 * `quiescent_step`'s reflexive-transitive closure — a genuinely useful
 * abstraction, but still one step removed from an actual INTERLEAVED
 * execution with an explicit control flow for the two threads driving the
 * protocol. This phase builds that explicit interleaving: a small state
 * machine with two commit points (the buffer write, then the status-word
 * store that makes it visible — exactly the two hardware stores the plan's
 * D3 fence discussion is about) for the sender, and two for the receiver
 * (the read, then the acknowledging store), with every OTHER thread's action
 * free to interleave anywhere around them. The headline result derives
 * `xchan_send_msg`, `xchan_recv_ack`, and message integrity DIRECTLY from a
 * genuine trace of this machine, rather than assuming quiescence.
 *
 * METHOD — explicit state, not a mover/rely-guarantee framework. As the plan
 * argues (section 5, Phase 6): the protocol has STATIC linearization points
 * (a send commits at one store, a recv/ack commits at one store), so the
 * refinement to the atomic Phase 3/5.5 relations is an ordinary forward
 * simulation, not a Lipton/CIVL-style reduction. `cstep`/`csteps` below are
 * exactly the plan's "inductive steps :: state => label list => state =>
 * bool over a state record, with an inductive invariant over a finite, small
 * control skeleton — the status word, the two program counters, and the
 * thread statuses."
 *
 * WHAT TO READ FIRST, AND WHY THE ORDER MATTERS. This theory has two kinds
 * of result and they are not equally strong:
 *
 *   - `conc_inv` and `pending_window_freezes_the_buffer` are the GENERAL
 *     results. The invariant is proved preserved by all five transitions and
 *     hence at every reachable state; the freezing theorem then quantifies
 *     over an ARBITRARY label list — any number of threads, any labels, in
 *     any order — and shows the buffer and the status word cannot move while
 *     a message is pending. `receiver_reads_msg_under_any_interleaving` is
 *     its message-integrity corollary and is what REQ-MSG-11 should be read
 *     against.
 *   - `interleaved_round_trip_refines_protocol` is a SPECIFIC TRACE SHAPE:
 *     it fixes the order of the four protocol labels in its hypotheses and
 *     quantifies only over the other-thread activity interposed between
 *     them. It exhibits the whole round trip and derives all three atomic
 *     relations in one place, which is why it is kept — but on its own it
 *     would be a statement about ONE interleaving, not about interleaving.
 *
 * The bridge between them is D2 below: `no_owner_write_while_pending` and
 * `no_owner_commit_while_pending` prove the owner has NO enabled transition
 * while the channel is pending, so the orderings the trace-shape theorem
 * omits are not reachable. That exclusion is derived from the invariant, not
 * assumed by the shape of a hypothesis list.
 *
 * STILL NOT GENERAL, AND NOT CLAIMED TO BE. There is no projection from an
 * arbitrary trace onto a SEQUENCE of abstract protocol steps, so "every
 * trace refines a run of the atomic protocol" is not proved here — only that
 * every trace preserves the invariant, that the pending window is frozen
 * under any interleaving, and that one exhibited round-trip shape refines
 * the atomic relations. Repeated round trips are likewise not covered (see
 * SCOPE below). Also, the receiver's read is modelled as a control-state
 * transition that extracts no value, and the owner's buffer write is a
 * single transition swapping the whole memory function — so a PARTIALLY
 * written buffer is not a state this machine has, and tearing cannot be
 * expressed here at all, let alone ruled out.
 *
 * D2 (ownership mutex) IS CITED, NOT REPROVED. The one fact this development
 * leans on hardest is Phase 5.75's T1 (`buffer_write_requires_owner`): on a
 * declared channel's buffer, the ONLY thread that ever holds write authority
 * is that channel's declared send-owner. Every "other thread" label below
 * (`COther`) is guarded by `amp_step_t t ... /\ t \<noteq> tp_send_owner tp ch`,
 * and T1 alone (no locale, no A-THR) is what proves such a step can never
 * touch the buffer — this is D2, cited exactly as the plan predicts ("fully
 * discharged by Phase 5.75 ... it is the side condition D1 cites"). The
 * owner's OWN commit point is similarly guarded by `owner_status ch tp (cs_xm
 * s) (tp_send_owner tp ch) = TRunning`, so a second send while the first is
 * still pending is not merely disallowed by a side condition checked
 * separately — it has no enabled transition in this model at all, precisely
 * mirroring T3's "owner_blocked_while_pending" being true by construction.
 *
 * WHERE A-THR STILL LIVES. Every non-owner action below is modelled as
 * `amp_step_t t m m' bp tp` for an EXPLICITLY NAMED thread t — i.e. this
 * model's very alphabet is thread-attributed by construction, not derived by
 * attributing an already-core-level `amp_step_w` fact after the fact (that
 * translation is exactly what Phase 5.75 needed A-THR for). Do not read this
 * as retiring A-THR: modelling every step as thread-driven is precisely
 * A-THR's content ("every core-level write is actually taken by some
 * thread"), simply built into the shape of the interleaving alphabet instead
 * of stated as a locale hypothesis and invoked. A-THR is therefore CONSUMED
 * here on exactly the same footing as in Phase 5.75, not re-derived from
 * seL4's `integrity` theorem, and remains a real, named TCB entry (see the
 * plan's section 6).
 *
 * SCOPE OF D3 (fence / happens-before) IN THIS THEORY. D3 splits into D3-a
 * (the code issues the required fences — Phase 4's remaining problem-area
 * item, not yet done) and D3-b (the trust seam: correctly-fenced RVWMO
 * accesses behave sequentially consistently, assumed as A-MEM; the compiler
 * preserves that ordering to the binary, trusted as A-BIN; the buffer is
 * cache-coherent across harts, assumed as A-COH). None of A-MEM/A-COH/A-BIN
 * appears as an explicit Isabelle hypothesis anywhere below, for the same
 * reason A-HW (Phase 1) and A-BIN (Phase 4's C half) do not: they justify
 * the RELATIONSHIP between this formal interleaved model and real hardware
 * execution (that real RVWMO execution of correctly-fenced, correctly-
 * compiled, cache-coherent code is faithfully represented by SOME `csteps`
 * trace of this machine), not a hypothesis consumed INSIDE a proof about the
 * model itself. They are named here, in the TCB table (plan section 6), and
 * nowhere else — silence in the proof text is the honest outcome for an
 * assumption about the model's own fidelity, exactly as the plan's section
 * 2.5 established for A-BIN.
 *
 * SCOPE — ONE CHANNEL, ONE ROUND TRIP. Exactly Phase 5.5/5.75's scope: a
 * single message's lifecycle (one send, one recv/ack), with an arbitrary
 * FINITE number of other threads' steps interleaved anywhere around it.
 * REQ-MSG-7's channel-independence result already says traffic on other
 * channels cannot perturb this one, so nothing is lost by not modelling
 * multiple channels' protocols racing here; generalising to repeated round
 * trips is straightforward (the state returns to its starting shape, per
 * REQ-MSG-6) but not separately proved.
 *
 * This theory is organized in the usual four zones (plan section 2.5).
 *)

theory AMP_Concurrency
imports "AMP_Thread.AMP_Thread"
begin

section \<open>Specification\<close>

subsection \<open>D1 — the receiver's control state\<close>

(* The receiver thread's progress through its half of the protocol. The
   sender's equivalent progress is NOT a fresh datatype: owner_status (Phase
   5.75) already derives it from the channel's own runtime status, and
   cs_written below supplies the one extra bit owner_status does not track
   (whether the buffer write has landed but not yet been made visible by the
   status-word store) — see cs_written's own comment. *)
datatype recv_pc = RIdle | RRead

subsection \<open>D1 — the explicit interleaved state\<close>

(* The state this phase's machine steps over: the system memory (cs_mem),
   channel ch's own runtime status entry (cs_xm — a full xchan_map, but only
   ch's entry is ever touched below), whether the sender's buffer write has
   landed but not yet been committed by the status-word store (cs_written —
   the second control bit the plan's D1 calls for, alongside the status word
   and the two "program counters"), and the receiver's progress (cs_recv_pc).
   This IS the "finite, small control skeleton" the plan specifies: two
   control bits plus one shared word. *)
record 'v conc_state =
  cs_mem     :: "obj_ref \<Rightarrow> 'v"
  cs_xm      :: xchan_map
  cs_written :: bool
  cs_recv_pc :: recv_pc

(* The five actions this machine's threads can take. COwnerWrite and
   COwnerCommit are the sender's two commit points (buffer store, then
   status-word store) that a real fence separates; CRecvRead and CRecvCommit
   are the receiver's mirror image (buffer load, then status-word store).
   COther t is every other thread's activity, interleaved freely — including
   other threads on the SAME core as the sender or receiver, which is
   exactly the case T1 (Phase 5.75) exists to rule safe. *)
datatype clabel = COwnerWrite | COwnerCommit | COther thread_id | CRecvRead | CRecvCommit

(* cstep bp ch tp msg s l s': one labelled transition of the machine, for a
   fixed channel ch, thread assignment tp, and message value msg (msg is a
   parameter, not part of the mutable state — mirroring xchan_send_msg's own
   shape, where msg is an argument to the relation, not carried in xm).

   cstep_owner_write: enabled only when the owner has nothing outstanding
   (\<not> cs_written s) and is actually free to run (owner_status ... = TRunning
   — by owner_status's own definition this is equivalent to ch not currently
   being pending, so this is also where "no second send while one is
   pending" fails to have an enabled transition, exactly as T3 predicts).
   Writes msg into ch's buffer and nothing else — the same footprint+value
   clause xchan_send_msg states — and marks the write outstanding.

   cstep_owner_commit: enabled only once a write is outstanding. Flips ch's
   status word to XSendPending (the send's actual linearization point — see
   the theory header) and clears the outstanding flag. Touches no memory.

   cstep_other: any OTHER thread's permission-respecting step (Phase 5.75's
   amp_step_t), for any thread that is NOT ch's declared send-owner. No
   further restriction: this is deliberately allowed at ANY point in the
   trace, including between the owner's write and its commit, which is
   exactly the interleaving this phase must show is harmless (see
   cstep_other_no_buffer_write below).

   cstep_recv_read: enabled only when the receiver is idle and ch is
   genuinely pending. A pure read — cs_mem is unchanged, matching
   xchan_recv_ack having no memory operand.

   cstep_recv_commit: enabled only once the receiver has read. Flips ch's
   status word back to XIdle (the recv/ack's own linearization point) and
   resets the receiver to idle. *)
inductive cstep ::
  "amp_partition \<Rightarrow> amp_channel \<Rightarrow> thread_partition \<Rightarrow> (obj_ref \<Rightarrow> 'v)
     \<Rightarrow> 'v conc_state \<Rightarrow> clabel \<Rightarrow> 'v conc_state \<Rightarrow> bool"
  for bp ch tp msg
where
  cstep_owner_write:
    "\<lbrakk> \<not> cs_written s;
       owner_status ch tp (cs_xm s) (tp_send_owner tp ch) = TRunning;
       changed_frames (cs_mem s) m' \<subseteq> ch_buffer ch;
       \<forall>f \<in> ch_buffer ch. m' f = msg f \<rbrakk>
     \<Longrightarrow> cstep bp ch tp msg s COwnerWrite (s\<lparr> cs_mem := m', cs_written := True \<rparr>)"
| cstep_owner_commit:
    "cs_written s
     \<Longrightarrow> cstep bp ch tp msg s COwnerCommit
           (s\<lparr> cs_xm := (cs_xm s)(ch \<mapsto> XSendPending), cs_written := False \<rparr>)"
| cstep_other:
    "\<lbrakk> t \<noteq> tp_send_owner tp ch; amp_step_t t (cs_mem s) m' bp tp \<rbrakk>
     \<Longrightarrow> cstep bp ch tp msg s (COther t) (s\<lparr> cs_mem := m' \<rparr>)"
| cstep_recv_read:
    "\<lbrakk> cs_recv_pc s = RIdle; cs_xm s ch = Some XSendPending \<rbrakk>
     \<Longrightarrow> cstep bp ch tp msg s CRecvRead (s\<lparr> cs_recv_pc := RRead \<rparr>)"
| cstep_recv_commit:
    "cs_recv_pc s = RRead
     \<Longrightarrow> cstep bp ch tp msg s CRecvCommit
           (s\<lparr> cs_xm := (cs_xm s)(ch \<mapsto> XIdle), cs_recv_pc := RIdle \<rparr>)"

(* csteps bp ch tp msg s ls s': a finite TRACE — a list of labelled cstep
   transitions from s to s'. This is the plan's "inductive steps :: state =>
   label list => state => bool" literally. *)
inductive csteps ::
  "amp_partition \<Rightarrow> amp_channel \<Rightarrow> thread_partition \<Rightarrow> (obj_ref \<Rightarrow> 'v)
     \<Rightarrow> 'v conc_state \<Rightarrow> clabel list \<Rightarrow> 'v conc_state \<Rightarrow> bool"
  for bp ch tp msg
where
  csteps_nil: "csteps bp ch tp msg s [] s"
| csteps_cons: "\<lbrakk> cstep bp ch tp msg s l s'; csteps bp ch tp msg s' ls s'' \<rbrakk>
                \<Longrightarrow> csteps bp ch tp msg s (l # ls) s''"

inductive_cases cstep_owner_write_E[elim!]: "cstep bp ch tp msg s COwnerWrite s'"
inductive_cases cstep_owner_commit_E[elim!]: "cstep bp ch tp msg s COwnerCommit s'"
inductive_cases cstep_other_E[elim!]: "cstep bp ch tp msg s (COther t) s'"
inductive_cases cstep_recv_read_E[elim!]: "cstep bp ch tp msg s CRecvRead s'"
inductive_cases cstep_recv_commit_E[elim!]: "cstep bp ch tp msg s CRecvCommit s'"
inductive_cases csteps_nil_E[elim!]: "csteps bp ch tp msg s [] s'"
inductive_cases csteps_cons_E[elim!]: "csteps bp ch tp msg s (l # ls) s'"

subsection \<open>D1 — the reachability invariant\<close>

(* conc_inv ch s: the state predicate that pins down WHICH interleavings this
   machine can actually reach, and hence the fact every result below rests on.
   Two clauses, each relating one of the two control bits to the shared status
   word:

     (A) if the owner has a buffer write outstanding but not yet committed,
         then ch is NOT pending. (The owner cannot have started a second
         message while its first is still in flight.)
     (B) if the receiver is mid-read, then ch IS pending. (The receiver only
         ever reads a message that has actually been committed.)

   These are deliberately NOT stated as "the owner and receiver never touch
   the buffer at the same time" — that is the CONSEQUENCE
   (no_outstanding_write_during_read below), derived by putting the two
   clauses together: mid-read forces pending by (B), and pending forbids an
   outstanding write by (A). Stating the invariant over the control bits
   rather than over the conclusion is what makes it inductive; the mutual
   exclusion itself is not.

   This is the piece the plan's D1 calls for and that nothing in this theory
   previously supplied: an inductive invariant over the finite control
   skeleton, from which the reachable orderings are DERIVED rather than
   assumed by fixing a trace shape in a theorem's hypotheses. *)
definition conc_inv :: "amp_channel \<Rightarrow> 'v conc_state \<Rightarrow> bool" where
  "conc_inv ch s \<equiv>
     (cs_written s \<longrightarrow> cs_xm s ch \<noteq> Some XSendPending)
     \<and> (cs_recv_pc s = RRead \<longrightarrow> cs_xm s ch = Some XSendPending)"

(* conc_init ch s: the machine's starting shape — ch idle, no write
   outstanding, receiver idle. Every reachable state of a run begun here
   satisfies conc_inv (conc_init_conc_inv, then csteps_preserves_conc_inv),
   which is what makes the invariant a statement about REACHABILITY rather
   than an extra hypothesis quietly narrowing the theorems below. *)
definition conc_init :: "amp_channel \<Rightarrow> 'v conc_state \<Rightarrow> bool" where
  "conc_init ch s \<equiv> cs_xm s ch = Some XIdle \<and> \<not> cs_written s \<and> cs_recv_pc s = RIdle"

section \<open>Proof development (internal machinery)\<close>

subsection \<open>T3, unfolded: "the owner is running" IS "the channel is not pending"\<close>

(* The bridge that makes Phase 5.75's T3 do work inside a trace, rather than
   only at a single abstract step. owner_status was DEFINED as a function of
   the channel's runtime status, so the guard cstep_owner_write carries
   ("the owner is free to run") is literally equivalent to "ch is not
   currently pending". Every exclusion result below is this equivalence plus
   conc_inv; T3 is cited here, never reproved. *)
lemma owner_running_iff_not_pending:
  "owner_status ch tp xm (tp_send_owner tp ch) = TRunning \<longleftrightarrow> xm ch \<noteq> Some XSendPending"
  by (simp add: owner_status_def)

subsection \<open>The invariant is genuinely inductive\<close>

(* conc_init implies conc_inv: the starting shape satisfies both clauses
   vacuously (nothing outstanding, receiver idle). Non-vacuity for the
   invariant — without this, "every reachable state satisfies conc_inv" could
   hold because no state is reachable. *)
lemma conc_init_conc_inv: "conc_init ch s \<Longrightarrow> conc_inv ch s"
  by (simp add: conc_init_def conc_inv_def)

(* The core of D1: EVERY one of the five transitions preserves conc_inv. Each
   case is where one specific piece of the design pays for itself:

     COwnerWrite  — sets the outstanding bit, so clause (A) must be
                    re-established; the guard owner_status ... = TRunning is
                    exactly what supplies it (via T3, unfolded above). This is
                    the case that would FAIL if the design had a timeout,
                    since a timeout is precisely a way for the owner to run
                    while ch is pending.
     COwnerCommit — clears the outstanding bit, making (A) vacuous, and sets
                    the status pending, which is what (B) needs.
     COther       — touches only cs_mem; both clauses are about control state,
                    so they survive untouched. (That such a step cannot touch
                    the BUFFER is a separate fact — D2, cited below.)
     CRecvRead    — sets the receiver mid-read, so clause (B) must be
                    re-established; its own guard (ch is pending) supplies it.
     CRecvCommit  — returns the status to idle, re-establishing (A), and
                    resets the receiver, making (B) vacuous. *)
lemma cstep_preserves_conc_inv:
  assumes step: "cstep bp ch tp msg s l s'" and inv: "conc_inv ch s"
  shows "conc_inv ch s'"
  using step
proof (cases rule: cstep.cases)
  case (cstep_owner_write m')
  then show ?thesis
    using inv by (auto simp: conc_inv_def owner_running_iff_not_pending)
next
  case cstep_owner_commit
  then show ?thesis using inv by (auto simp: conc_inv_def)
next
  case (cstep_other t m')
  then show ?thesis using inv by (auto simp: conc_inv_def)
next
  case cstep_recv_read
  then show ?thesis using inv by (auto simp: conc_inv_def)
next
  case cstep_recv_commit
  then show ?thesis using inv by (auto simp: conc_inv_def)
qed

subsection \<open>D2, cited: a non-owner step never touches the buffer\<close>

(* The single-step content of D2 (Phase 5.75's ownership mutex, cited not
   reproved — see the theory header): a COther transition, by construction
   taken by a thread that is not ch's declared send-owner, cannot change any
   of ch's buffer frames. Proof is exactly buffer_write_requires_owner (T1)
   applied to the one frame that would have to have been written for the
   buffer to change. *)
lemma cstep_other_no_buffer_write:
  assumes wf: "amp_partition_wf bp" and chd: "ch \<in> ap_channels bp"
      and step: "cstep bp ch tp msg s (COther t) s'"
  shows "\<forall>f \<in> ch_buffer ch. cs_mem s' f = cs_mem s f"
proof (intro ballI)
  fix f assume f: "f \<in> ch_buffer ch"
  from step obtain m' where tne: "t \<noteq> tp_send_owner tp ch"
                         and astep: "amp_step_t t (cs_mem s) m' bp tp"
                         and seq: "s' = s\<lparr> cs_mem := m' \<rparr>"
    by (cases rule: cstep_other_E) auto
  show "cs_mem s' f = cs_mem s f"
  proof (rule ccontr)
    assume "cs_mem s' f \<noteq> cs_mem s f"
    with seq have "m' f \<noteq> cs_mem s f" by simp
    then have "f \<in> changed_frames (cs_mem s) m'" by (simp add: changed_frames_def)
    with astep have "thread_perm bp tp t f = PermRW" by (simp add: amp_step_t_def)
    from buffer_write_requires_owner[OF wf chd f this] have "t = tp_send_owner tp ch" .
    with tne show False by simp
  qed
qed

(* The rest of a COther transition: it never touches ch's status word, the
   outstanding-write flag, or the receiver's control state — only cs_mem
   moves, and only within the bound the definition itself already states. *)
lemma cstep_other_preserves_control:
  assumes step: "cstep bp ch tp msg s (COther t) s'"
  shows "cs_xm s' = cs_xm s" and "cs_written s' = cs_written s" and "cs_recv_pc s' = cs_recv_pc s"
  using step by (cases rule: cstep_other_E; simp)+

subsection \<open>Stuttering: a run of only COther labels leaves the protocol-relevant state fixed\<close>

(* ceq s s' ch: s and s' agree on everything the protocol cares about — ch's
   status word, the outstanding-write flag, the receiver's control state, and
   the content of ch's buffer (memory OUTSIDE the buffer is deliberately not
   compared here: other threads' steps are free to change it, and the
   protocol correctness argument below never needs it to be fixed). *)
definition ceq :: "'v conc_state \<Rightarrow> 'v conc_state \<Rightarrow> amp_channel \<Rightarrow> bool" where
  "ceq s s' ch \<equiv> cs_xm s' = cs_xm s \<and> cs_written s' = cs_written s \<and> cs_recv_pc s' = cs_recv_pc s
                  \<and> (\<forall>f \<in> ch_buffer ch. cs_mem s' f = cs_mem s f)"

(* ceq is reflexive: an empty run (zero COther steps) trivially leaves the
   protocol-relevant state fixed. The base case of the induction below. *)
lemma ceq_refl: "ceq s s ch"
  by (simp add: ceq_def)

(* ceq is transitive: chaining two COther-only runs (e.g. one on either side
   of a single labelled commit point) is itself a COther-only run's worth of
   preservation. The step case of the induction below. *)
lemma ceq_trans: "ceq s s' ch \<Longrightarrow> ceq s' s'' ch \<Longrightarrow> ceq s s'' ch"
  by (simp add: ceq_def)

(* D1's stuttering lemma: ANY finite run consisting entirely of COther labels
   — any number of other threads, in any order, touching whatever non-buffer
   memory they like — is invisible to the protocol state. This is the fact
   that lets the headline theorem below treat "an arbitrary amount of
   unrelated activity happened here" as a single hypothesis instead of
   reasoning about each interleaved step individually. *)
lemma csteps_other_ceq:
  assumes wf: "amp_partition_wf bp" and chd: "ch \<in> ap_channels bp"
      and allo: "\<forall>l \<in> set ls. \<exists>t. l = COther t"
      and run: "csteps bp ch tp msg s ls s'"
  shows "ceq s s' ch"
  using allo run
proof (induct ls arbitrary: s)
  case Nil
  then have "s' = s" by (auto elim: csteps_nil_E)
  then show ?case by (simp add: ceq_refl)
next
  case (Cons l ls)
  from Cons.prems(2) obtain sm where step: "cstep bp ch tp msg s l sm"
                                  and rest: "csteps bp ch tp msg sm ls s'"
    by (auto elim: csteps_cons_E)
  from Cons.prems(1) obtain t where l: "l = COther t" by auto
  from step l have step': "cstep bp ch tp msg s (COther t) sm" by simp
  from cstep_other_no_buffer_write[OF wf chd step']
       cstep_other_preserves_control[OF step']
  have "ceq s sm ch" by (simp add: ceq_def)
  moreover from Cons.prems(1) l have "\<forall>l \<in> set ls. \<exists>t. l = COther t" by simp
  ultimately show ?case using Cons.hyps[OF _ rest] ceq_trans by blast
qed

subsection \<open>One step of the pending window\<close>

(* The single-step engine behind pending_window_freezes_the_buffer below.
   While ch is pending, and for any label other than the acknowledgement
   itself, one transition can change neither ch's status nor its buffer.
   The five cases split into three genuinely different reasons, and it is
   worth reading which is which because they are the three separate facts
   this phase is composing:

     COwnerWrite  — NOT ENABLED. Its guard requires the owner to be running,
                    which (T3, unfolded) contradicts ch being pending. This is
                    the exclusion that the previous version of this theory
                    assumed by fixing a trace shape; here it is derived.
     COwnerCommit — NOT ENABLED. Its guard requires an outstanding write,
                    which conc_inv's clause (A) forbids while pending.
     COther       — ENABLED, and harmless: T1 (Phase 5.75, via
                    cstep_other_no_buffer_write) says a non-owner thread
                    cannot write the buffer, and the step touches no control
                    state.
     CRecvRead    — ENABLED, and harmless: it moves the receiver's program
                    counter and nothing else.
     CRecvCommit  — excluded by hypothesis; it is the step that ENDS the
                    pending window, so freezing cannot be claimed across it. *)
lemma cstep_pending_preserves_buffer:
  assumes wf: "amp_partition_wf bp" and chd: "ch \<in> ap_channels bp"
      and inv: "conc_inv ch s"
      and pend: "cs_xm s ch = Some XSendPending"
      and notack: "l \<noteq> CRecvCommit"
      and step: "cstep bp ch tp msg s l s'"
  shows "cs_xm s' ch = Some XSendPending \<and> (\<forall>f \<in> ch_buffer ch. cs_mem s' f = cs_mem s f)"
proof (cases l)
  case COwnerWrite
  (* Not enabled: the guard says the owner is running, T3 says that means
     not pending, and pend says otherwise. *)
  with step pend show ?thesis
    by (auto simp: owner_running_iff_not_pending)
next
  case COwnerCommit
  (* Not enabled: the guard says a write is outstanding, conc_inv (A) says
     that cannot hold while pending. *)
  with step inv pend show ?thesis
    by (auto simp: conc_inv_def)
next
  case (COther t)
  with step have st: "cstep bp ch tp msg s (COther t) s'" by simp
  from cstep_other_no_buffer_write[OF wf chd st] cstep_other_preserves_control[OF st] pend
  show ?thesis by simp
next
  case CRecvRead
  with step have "s' = s\<lparr> cs_recv_pc := RRead \<rparr>" by (auto elim!: cstep_recv_read_E)
  with pend show ?thesis by simp
next
  case CRecvCommit
  with notack show ?thesis by simp
qed

section \<open>Results\<close>

subsection \<open>D1 — every reachable state satisfies the invariant\<close>

(* The invariant lifted from one step to an ARBITRARY trace: any finite
   sequence of labelled transitions, in any order, preserves conc_inv. Note
   what is and is not quantified here — unlike the trace-shape theorem later
   in this section, `ls` is a completely arbitrary label list. Nothing fixes
   how many protocol steps it contains, in which order, or how much other
   activity surrounds them. *)
theorem csteps_preserves_conc_inv:
  "csteps bp ch tp msg s ls s' \<Longrightarrow> conc_inv ch s \<Longrightarrow> conc_inv ch s'"
proof (induct rule: csteps.induct)
  case (csteps_nil s)
  then show ?case by simp
next
  case (csteps_cons s l sm ls s'')
  then show ?case using cstep_preserves_conc_inv by blast
qed

(* Packaged for use: every state reachable from the machine's starting shape
   satisfies the invariant. This is what lets the exclusion results below be
   read as facts about the system rather than as conditional statements about
   states that might never occur. *)
corollary reachable_conc_inv:
  assumes init: "conc_init ch s" and run: "csteps bp ch tp msg s ls s'"
  shows "conc_inv ch s'"
  using csteps_preserves_conc_inv[OF run conc_init_conc_inv[OF init]] .

subsection \<open>D2 — mutual exclusion, derived rather than assumed\<close>

(* THE ORDERING EXCLUSION. In any state satisfying the invariant — hence in
   any reachable state — the owner CANNOT take a buffer-write step while ch is
   pending. There is no such transition; it is not that the transition exists
   and is shown harmless. This is the fact the trace-shape theorem below
   silently assumed by never placing a COwnerWrite between the receiver's read
   and its acknowledgement, and it is the trace-level form of REQ-MSG-3 ("a
   pending message is never overwritten"): previously a statement about the
   abstract relation having no enabled instance, now a statement about the
   interleaved machine having no enabled transition. *)
theorem no_owner_write_while_pending:
  assumes pend: "cs_xm s ch = Some XSendPending"
  shows "\<not> cstep bp ch tp msg s COwnerWrite s'"
  using pend by (auto simp: owner_running_iff_not_pending)

(* Its companion: nor can the owner COMMIT while pending, because conc_inv's
   clause (A) rules out an outstanding write in that state. Together with the
   previous theorem this says the owner has NO enabled transition at all
   during the pending window — which is exactly "the sender blocks until the
   ack", now a property of the interleaved model rather than a property of
   owner_status's definition. *)
theorem no_owner_commit_while_pending:
  assumes inv: "conc_inv ch s" and pend: "cs_xm s ch = Some XSendPending"
  shows "\<not> cstep bp ch tp msg s COwnerCommit s'"
  using inv pend by (auto simp: conc_inv_def)

(* D2 proper, in the form the plan states it — "at most one agent may write
   the buffer at any instant" — for this machine's own notion of an instant:
   whenever the receiver is mid-read, the owner has no write outstanding.
   Derived from the two invariant clauses together, exactly as conc_inv's
   comment describes. *)
theorem no_outstanding_write_during_read:
  assumes inv: "conc_inv ch s" and rd: "cs_recv_pc s = RRead"
  shows "\<not> cs_written s"
  using inv rd by (auto simp: conc_inv_def)

subsection \<open>D1 — message integrity across an ARBITRARY interleaving\<close>

(* THE GENERAL TRACE THEOREM, and the one to read if you read only one result
   in this theory. Take any state where ch is pending, and ANY finite trace at
   all out of it — any number of threads, any labels, in any order — subject
   to the single condition that the acknowledgement has not yet occurred. Then
   ch is still pending at the end, and its buffer is bit-for-bit unchanged.

   The contrast with interleaved_round_trip_refines_protocol below is the
   point. That theorem fixes the sequence of protocol labels in its
   hypotheses and quantifies only over the other-thread activity BETWEEN
   them. This one quantifies over the label list itself: `ls` is an arbitrary
   clabel list, and the proof works by showing that the transitions which
   would break the property are NOT ENABLED (the owner's two), while those
   that are enabled cannot touch the buffer (T1) or the status word.

   That is what makes this a statement about the protocol working under
   interleaving, rather than a statement about one interleaving. *)
theorem pending_window_freezes_the_buffer:
  assumes wf: "amp_partition_wf bp" and chd: "ch \<in> ap_channels bp"
  shows "csteps bp ch tp msg s ls s' \<Longrightarrow> conc_inv ch s
          \<Longrightarrow> cs_xm s ch = Some XSendPending \<Longrightarrow> CRecvCommit \<notin> set ls
          \<Longrightarrow> cs_xm s' ch = Some XSendPending
              \<and> (\<forall>f \<in> ch_buffer ch. cs_mem s' f = cs_mem s f)"
proof (induct rule: csteps.induct)
  case (csteps_nil s)
  then show ?case by simp
next
  case (csteps_cons s l sm ls s'')
  from csteps_cons.prems
  have inv: "conc_inv ch s" and pend: "cs_xm s ch = Some XSendPending"
   and na: "CRecvCommit \<notin> set (l # ls)" by auto
  from na have lne: "l \<noteq> CRecvCommit" and na': "CRecvCommit \<notin> set ls" by auto
  from cstep_pending_preserves_buffer[OF wf chd inv pend lne csteps_cons.hyps(1)]
  have mp: "cs_xm sm ch = Some XSendPending"
   and mb: "\<forall>f \<in> ch_buffer ch. cs_mem sm f = cs_mem s f" by auto
  from cstep_preserves_conc_inv[OF csteps_cons.hyps(1) inv] have minv: "conc_inv ch sm" .
  from csteps_cons.hyps(3)[OF minv mp na']
  have "cs_xm s'' ch = Some XSendPending"
   and "\<forall>f \<in> ch_buffer ch. cs_mem s'' f = cs_mem sm f" by auto
  with mb show ?case by simp
qed

(* REQ-MSG-11 as it should be stated: the receiver reads bit-for-bit what the
   owner sent, under ANY interleaving of the pending window rather than under
   one fixed trace shape. Given a state where the message has been committed
   and the buffer holds it, every reachable state before the acknowledgement
   presents the receiver with the same message — so whenever the receiver's
   read happens, and whatever ran in between, it reads msg.

   Note what this does NOT need: no hypothesis about how many other threads
   ran, what they touched, or where in the trace the receiver's own read
   falls. The quiescent_step abstraction Phase 5.5 needed is gone, and so is
   the fixed label ordering. *)
corollary receiver_reads_msg_under_any_interleaving:
  assumes wf: "amp_partition_wf bp" and chd: "ch \<in> ap_channels bp"
      and inv: "conc_inv ch s"
      and pend: "cs_xm s ch = Some XSendPending"
      and held: "\<forall>f \<in> ch_buffer ch. cs_mem s f = msg f"
      and noack: "CRecvCommit \<notin> set ls"
      and run: "csteps bp ch tp msg s ls s'"
  shows "xchan_recv ch (cs_mem s') = xchan_recv ch msg"
proof -
  from pending_window_freezes_the_buffer[OF wf chd run inv pend noack]
  have "\<forall>f \<in> ch_buffer ch. cs_mem s' f = cs_mem s f" by simp
  with held have "\<forall>f \<in> ch_buffer ch. cs_mem s' f = msg f" by simp
  then show ?thesis by (auto simp: xchan_recv_def)
qed

subsection \<open>D1 — a genuine interleaved trace refines the atomic protocol\<close>

(* A SPECIFIC TRACE SHAPE, retained as the worked end-to-end round trip.
   READ pending_window_freezes_the_buffer FIRST — that is this theory's
   general result. This theorem is weaker than it looks and the difference
   matters: its hypotheses FIX the order of the four protocol labels and
   quantify only over the other-thread activity between them. It therefore
   says "this interleaving refines the atomic protocol", not "every
   interleaving does". What justifies restricting attention to this shape is
   not stated here but proved above: no_owner_write_while_pending and
   no_owner_commit_while_pending show the owner has no enabled transition
   during the pending window, so no other ordering of the protocol labels is
   reachable in the first place.

   Its value is that it exhibits the two commit points and the full round
   trip in one place, deriving all three atomic relations at once. Read the
   hypotheses as one concrete shape of trace:
   from a starting state where ch is idle, the owner is free to run, and the
   receiver is idle (s0) —
     any amount of other-thread activity (os0),
     the owner's write (sA -> sB),
     any amount of other-thread activity (os1),
     the owner's commit (sC -> sD) — ch becomes pending here,
     any amount of other-thread activity (os2),
     the receiver's read (sE -> sF),
     any amount of other-thread activity (os3),
     the receiver's commit (sG -> sH) — ch becomes idle again.
   No hypothesis says the "any amount of other-thread activity" runs are
   empty, or bounds how many threads or how much memory elsewhere they touch
   — this IS the concurrency Phase 5.5/5.75 could only reason about via the
   quiescent_step abstraction, now derived from an actual trace shape.

   The three conclusions are exactly Phase 3/5.5's atomic relations,
   RE-DERIVED (not assumed) from this trace: the write-then-commit pair IS a
   genuine xchan_send_msg (from sA to sB for the memory clause, sA to sD for
   the status clause — the two components of one atomic relation, produced
   here by two separate commit points exactly as D1 requires); the
   read-then-commit pair IS a genuine xchan_recv_ack; and the message the
   receiver reads at its own commit point (sF) is bit-for-bit the message the
   owner wrote (xchan_recv ch (cs_mem sF) = xchan_recv ch msg) — Phase 5.5's
   M2 conclusion, needing no sender_quiescent locale and no A-THR premise in
   THIS statement (see the theory header for where A-THR still lives). *)
theorem interleaved_round_trip_refines_protocol:
  fixes msg :: "obj_ref \<Rightarrow> 'v"
  assumes wf:  "amp_partition_wf bp" and chd: "ch \<in> ap_channels bp"
      and twf: "thread_partition_wf bp tp"
      and os0: "\<forall>l \<in> set os0. \<exists>t. l = COther t"
      and run0: "csteps bp ch tp msg s0 os0 sA"
      and idle0: "cs_xm s0 ch = Some XIdle"
      and owr: "cstep bp ch tp msg sA COwnerWrite sB"
      and os1: "\<forall>l \<in> set os1. \<exists>t. l = COther t"
      and run1: "csteps bp ch tp msg sB os1 sC"
      and commit: "cstep bp ch tp msg sC COwnerCommit sD"
      and os2: "\<forall>l \<in> set os2. \<exists>t. l = COther t"
      and run2: "csteps bp ch tp msg sD os2 sE"
      and rread: "cstep bp ch tp msg sE CRecvRead sF"
      and os3: "\<forall>l \<in> set os3. \<exists>t. l = COther t"
      and run3: "csteps bp ch tp msg sF os3 sG"
      and rcommit: "cstep bp ch tp msg sG CRecvCommit sH"
  shows "xchan_send_msg ch msg (cs_mem sA) (cs_mem sB) (cs_xm sA) (cs_xm sD)"
    and "xchan_recv_ack ch (cs_xm sD) (cs_xm sH)"
    and "xchan_recv ch (cs_mem sF) = xchan_recv ch msg"
proof -
  from csteps_other_ceq[OF wf chd os0 run0] have e0: "ceq s0 sA ch" .
  from csteps_other_ceq[OF wf chd os1 run1] have e1: "ceq sB sC ch" .
  from csteps_other_ceq[OF wf chd os2 run2] have e2: "ceq sD sE ch" .
  from csteps_other_ceq[OF wf chd os3 run3] have e3: "ceq sF sG ch" .

  from owr obtain m' where wr_written: "\<not> cs_written sA"
                          and wr_running: "owner_status ch tp (cs_xm sA) (tp_send_owner tp ch) = TRunning"
                          and wr_footprint: "changed_frames (cs_mem sA) m' \<subseteq> ch_buffer ch"
                          and wr_value: "\<forall>f \<in> ch_buffer ch. m' f = msg f"
                          and wr_sB: "sB = sA\<lparr> cs_mem := m', cs_written := True \<rparr>"
    by (cases rule: cstep_owner_write_E) auto
  have cm_written: "cs_written sC" using commit by (auto elim!: cstep_owner_commit_E)
  have cm_sD: "sD = sC\<lparr> cs_xm := (cs_xm sC)(ch \<mapsto> XSendPending), cs_written := False \<rparr>"
    using commit by (auto elim!: cstep_owner_commit_E)
  have rr_pc: "cs_recv_pc sE = RIdle" using rread by (auto elim!: cstep_recv_read_E)
  have rr_pending: "cs_xm sE ch = Some XSendPending" using rread by (auto elim!: cstep_recv_read_E)
  have rr_sF: "sF = sE\<lparr> cs_recv_pc := RRead \<rparr>" using rread by (auto elim!: cstep_recv_read_E)
  have rc_pc: "cs_recv_pc sG = RRead" using rcommit by (auto elim!: cstep_recv_commit_E)
  have rc_sH: "sH = sG\<lparr> cs_xm := (cs_xm sG)(ch \<mapsto> XIdle), cs_recv_pc := RIdle \<rparr>"
    using rcommit by (auto elim!: cstep_recv_commit_E)

  have xm_sA: "cs_xm sA ch = Some XIdle" using e0 idle0 by (simp add: ceq_def)
  have mem_sB: "cs_mem sB = m'" using wr_sB by simp
  have xm_sB: "cs_xm sB = cs_xm sA" using wr_sB by simp
  have xm_sC: "cs_xm sC = cs_xm sB" using e1 by (simp add: ceq_def)
  have xm_sD: "cs_xm sD = (cs_xm sA)(ch \<mapsto> XSendPending)"
    using cm_sD xm_sC xm_sB by simp

  show send: "xchan_send_msg ch msg (cs_mem sA) (cs_mem sB) (cs_xm sA) (cs_xm sD)"
    unfolding xchan_send_msg_def xchan_send_def
    using xm_sA wr_footprint mem_sB xm_sD wr_value by simp

  have xm_sE: "cs_xm sE = cs_xm sD" using e2 by (simp add: ceq_def)
  have xm_sF: "cs_xm sF = cs_xm sE" using rr_sF by simp
  have xm_sG: "cs_xm sG = cs_xm sF" using e3 by (simp add: ceq_def)
  have pending_sD: "cs_xm sD ch = Some XSendPending" using xm_sD by simp

  show recv: "xchan_recv_ack ch (cs_xm sD) (cs_xm sH)"
    unfolding xchan_recv_ack_def
    using pending_sD rc_sH xm_sG xm_sF xm_sE by simp

  have buf_sB_eq_msg: "\<forall>f \<in> ch_buffer ch. cs_mem sB f = msg f" using mem_sB wr_value by simp
  have buf_sC: "\<forall>f \<in> ch_buffer ch. cs_mem sC f = cs_mem sB f" using e1 by (simp add: ceq_def)
  have mem_sD: "cs_mem sD = cs_mem sC" using cm_sD by simp
  have buf_sE: "\<forall>f \<in> ch_buffer ch. cs_mem sE f = cs_mem sD f" using e2 by (simp add: ceq_def)
  have mem_sF: "cs_mem sF = cs_mem sE" using rr_sF by simp
  have "\<forall>f \<in> ch_buffer ch. cs_mem sF f = msg f"
    using buf_sE mem_sF mem_sD buf_sC buf_sB_eq_msg by simp
  then show "xchan_recv ch (cs_mem sF) = xchan_recv ch msg"
    by (auto simp: xchan_recv_def)
qed

section \<open>Examples\<close>

subsection \<open>A concrete, genuinely interleaved round trip on the example system\<close>

(* A witness that the headline theorem's hypotheses are jointly satisfiable —
   not vacuous — using the same example2/chan01/example_tp/example_msg
   fixtures every earlier phase's non-vacuity section reuses. The "other
   activity" runs are witnessed non-trivially (os1 has one genuine COther
   step, by thread 20 — chan01's own RECEIVE owner, taking some unrelated
   step of its own between the send's write and its commit) rather than all
   being empty, so this is a genuine interleaving instance, not a
   degenerate serial one. *)

definition example_s0 :: "nat conc_state" where
  "example_s0 = \<lparr> cs_mem = (\<lambda>_. 0), cs_xm = example_xchan0, cs_written = False, cs_recv_pc = RIdle \<rparr>"

(* A concrete instance of the owner's write transition: from the example
   system's idle starting state, chan01's declared send-owner (thread 10,
   idle by example_owner_status_tracks_chan01) may write example_msg's value
   into chan01's one buffer frame (0x8000) — the enabling side conditions of
   cstep_owner_write, discharged for real fixtures rather than left as an
   abstract possibility. *)
lemma example_owner_write:
  "cstep example2 chan01 example_tp example_msg
     example_s0 COwnerWrite
     (example_s0\<lparr> cs_mem := (cs_mem example_s0)(0x8000 := 42), cs_written := True \<rparr>)"
proof (rule cstep_owner_write)
  show "\<not> cs_written example_s0" by (simp add: example_s0_def)
  show "owner_status chan01 example_tp (cs_xm example_s0) (tp_send_owner example_tp chan01) = TRunning"
    using example_owner_status_tracks_chan01(1) by (simp add: example_s0_def example_tp_def)
  show "changed_frames (cs_mem example_s0) ((cs_mem example_s0)(0x8000 := 42)) \<subseteq> ch_buffer chan01"
    by (auto simp: changed_frames_def chan01_def)
  show "\<forall>f \<in> ch_buffer chan01. ((cs_mem example_s0)(0x8000 := 42)) f = example_msg f"
    by (simp add: chan01_def example_msg_def)
qed

(* A concrete instance of a genuine COther transition: chan01's own declared
   RECEIVE owner (thread 20, on core 1) — a thread that is emphatically not
   chan01's send-owner, so cstep_other's guard is satisfied — takes a step
   confined to core 1's own private frame 0x3000 (thread_owns_priv, via T1),
   while the owner's write from example_owner_write above sits uncommitted.
   This is the witness that the "arbitrary other-thread activity" in the
   headline theorem's hypotheses is genuinely instantiable, not just
   syntactically well-typed. *)
lemma example_other_step:
  "cstep example2 chan01 example_tp example_msg
     (example_s0\<lparr> cs_mem := (cs_mem example_s0)(0x8000 := 42), cs_written := True \<rparr>)
     (COther 20)
     ((example_s0\<lparr> cs_mem := (cs_mem example_s0)(0x8000 := 42), cs_written := True \<rparr>)
        \<lparr> cs_mem := ((cs_mem example_s0)(0x8000 := 42))(0x3000 := 7) \<rparr>)"
proof (rule cstep_other)
  show "(20 :: thread_id) \<noteq> tp_send_owner example_tp chan01" by (simp add: example_tp_def)
  show "amp_step_t 20 (cs_mem (example_s0\<lparr> cs_mem := (cs_mem example_s0)(0x8000 := 42), cs_written := True \<rparr>))
          (((cs_mem example_s0)(0x8000 := 42))(0x3000 := 7)) example2 example_tp"
    unfolding amp_step_t_def
    by (auto simp: changed_frames_def thread_perm_def thread_owns_priv_def owns_priv_def
                   thread_maps_writer_def thread_maps_reader_def
                   example_tp_def example2_def chan01_def core1_res_def example_s0_def)
qed

(* Non-vacuity, end to end: the headline theorem's premises hold of a
   concrete run through example_s0 with os0 = os3 = [], os1 = [COther 20]
   (a genuine interleaved step from chan01's own receive-owner thread,
   landing on a frame outside the buffer), os2 = [], and the theorem's three
   conclusions consequently hold of this run — witnessed, not merely
   claimed possible. *)
lemma example_interleaved_round_trip:
  shows "xchan_send_msg chan01 example_msg
           (cs_mem example_s0) ((cs_mem example_s0)(0x8000 := 42))
           (cs_xm example_s0) (example_xchan0(chan01 \<mapsto> XSendPending))"
    and "xchan_recv_ack chan01
           (example_xchan0(chan01 \<mapsto> XSendPending)) example_xchan0"
    and "xchan_recv chan01 (((cs_mem example_s0)(0x8000 := 42))(0x3000 := 7))
         = xchan_recv chan01 example_msg"
proof -
  define sA where "sA = example_s0"
  define sB where "sB = example_s0\<lparr> cs_mem := (cs_mem example_s0)(0x8000 := 42), cs_written := True \<rparr>"
  define sC where "sC = (example_s0\<lparr> cs_mem := (cs_mem example_s0)(0x8000 := 42), cs_written := True \<rparr>)
                          \<lparr> cs_mem := ((cs_mem example_s0)(0x8000 := 42))(0x3000 := 7) \<rparr>"
  define sD where "sD = sC\<lparr> cs_xm := (cs_xm sC)(chan01 \<mapsto> XSendPending), cs_written := False \<rparr>"
  define sE where "sE = sD"
  define sF where "sF = sE\<lparr> cs_recv_pc := RRead \<rparr>"
  define sG where "sG = sF"
  define sH where "sH = sG\<lparr> cs_xm := (cs_xm sG)(chan01 \<mapsto> XIdle), cs_recv_pc := RIdle \<rparr>"

  have run0: "csteps example2 chan01 example_tp example_msg sA [] sA" by (rule csteps_nil)
  have owr: "cstep example2 chan01 example_tp example_msg sA COwnerWrite sB"
    using example_owner_write by (simp add: sA_def sB_def)
  have other: "cstep example2 chan01 example_tp example_msg sB (COther 20) sC"
    using example_other_step by (simp add: sB_def sC_def)
  have run1: "csteps example2 chan01 example_tp example_msg sB [COther 20] sC"
    by (rule csteps_cons[OF other csteps_nil])
  have commit: "cstep example2 chan01 example_tp example_msg sC COwnerCommit sD"
    unfolding sD_def by (rule cstep_owner_commit) (simp add: sC_def)
  have run2: "csteps example2 chan01 example_tp example_msg sD [] sE" using sE_def by (simp add: csteps_nil)
  have xm_sE: "cs_xm sE chan01 = Some XSendPending"
    using commit by (simp add: sD_def sE_def sC_def chan01_def example_xchan0_def example_s0_def)
  have rread: "cstep example2 chan01 example_tp example_msg sE CRecvRead sF"
    unfolding sF_def by (rule cstep_recv_read) (simp_all add: sE_def sD_def sC_def example_s0_def xm_sE)
  have run3: "csteps example2 chan01 example_tp example_msg sF [] sG" using sG_def by (simp add: csteps_nil)
  have rcommit: "cstep example2 chan01 example_tp example_msg sG CRecvCommit sH"
    unfolding sH_def by (rule cstep_recv_commit) (simp add: sG_def sF_def)

  have wf: "amp_partition_wf example2" by (rule example2_partition_wf)
  have chd: "chan01 \<in> ap_channels example2" by (simp add: example2_def)
  have twf: "thread_partition_wf example2 example_tp" by (rule example_tp_wf)
  have idle0: "cs_xm sA chan01 = Some XIdle" by (simp add: sA_def example_s0_def example_xchan0_def)

  note main = interleaved_round_trip_refines_protocol
                [OF wf chd twf _ run0 idle0 owr _ run1 commit _ run2 rread _ run3 rcommit]
  have allo1: "\<forall>l \<in> set [COther (20::thread_id)]. \<exists>t. l = COther t" by simp
  have allo0: "\<forall>l \<in> set ([] :: clabel list). \<exists>t. l = COther t" by simp
  from main[OF allo0 allo1 allo0 allo0]
  have send: "xchan_send_msg chan01 example_msg (cs_mem sA) (cs_mem sB) (cs_xm sA) (cs_xm sD)"
    and recv: "xchan_recv_ack chan01 (cs_xm sD) (cs_xm sH)"
    and integ: "xchan_recv chan01 (cs_mem sF) = xchan_recv chan01 example_msg" by auto

  show "xchan_send_msg chan01 example_msg
          (cs_mem example_s0) ((cs_mem example_s0)(0x8000 := 42))
          (cs_xm example_s0) (example_xchan0(chan01 \<mapsto> XSendPending))"
    using send
    by (simp add: sA_def sB_def sD_def sC_def example_s0_def example_xchan0_def)

  show "xchan_recv_ack chan01 (example_xchan0(chan01 \<mapsto> XSendPending)) example_xchan0"
    using recv
    by (simp add: sD_def sC_def sH_def sG_def sF_def sE_def example_s0_def example_xchan0_def)

  show "xchan_recv chan01 (((cs_mem example_s0)(0x8000 := 42))(0x3000 := 7))
        = xchan_recv chan01 example_msg"
    using integ by (simp add: sF_def sE_def sD_def sC_def sB_def)
qed

end
