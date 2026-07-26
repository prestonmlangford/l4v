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
 * machine in which each side's buffer traffic is a LOOP OF PER-FRAME STORES
 * AND LOADS followed by a status-word store, with every other thread's action
 * free to interleave anywhere — including in the middle of either loop.
 *
 * THE MODEL IS COPY-BASED, NOT ZERO-COPY, AND THAT IS THE POINT. The original
 * design had the receiving APPLICATION read the shared frame directly through
 * a pointer. That is not provable, and the obstacle is a real hazard rather
 * than a modelling gap: an application may read through such a pointer
 * whenever it likes, including after the acknowledgement, when the channel has
 * gone idle and the sender is free to overwrite the frame. Nothing in the
 * kernel bounds that window, so "the receiver reads only while the message is
 * pending" would be an ASSUMPTION ABOUT UNVERIFIED APPLICATION CODE — the
 * receiver-side twin of the `sender_quiescent` locale Phase 5.75 spent a whole
 * phase retiring, and it takes the same cure. Here the KERNEL is the only
 * agent that ever touches the shared frame, on both sides:
 *
 *   Send.  The app calls Send(msg). The kernel copies app memory into the
 *          shared frame frame-by-frame (`COwnerWrite f`), then stores the
 *          status word (`COwnerCommit`) and blocks the sending thread.
 *   Recv.  The app calls Recv(). The kernel copies the shared frame into the
 *          APP'S OWN receive buffer frame-by-frame (`CRecvStart`,
 *          `CRecvCopy f`), then stores the status word (`CRecvCommit`) and
 *          returns.
 *
 * This is seL4's own IPC — seL4_Send copies message registers into the
 * receiver's IPC buffer and has never been zero-copy shared memory. The cost
 * is two copies per message; the benefit is that "the reader reads only inside
 * the pending window" becomes a property of verified kernel code performing a
 * bounded, straight-line loop, which is what the results below prove.
 *
 * WHAT THE PER-FRAME SPLIT BUYS, AND WHY THE PREVIOUS MODEL COULD NOT BUY IT.
 * An earlier version of this theory modelled the owner's write as ONE
 * transition swapping the whole memory function, and the receiver's read as a
 * control-state move that extracted no value. A PARTIALLY written buffer was
 * therefore not a state that machine had, and a torn read could not be
 * expressed in it at all, let alone ruled out — no theorem can rule out a
 * state the datatype lacks. Splitting both loops into per-frame steps, and
 * giving the receiver a real `cs_recv_val` to copy into, makes tearing
 * expressible; `buffer_complete_while_pending` and
 * `delivered_message_is_intact` below then rule it out.
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
 * WHAT TO READ FIRST. Two invariants carry everything else:
 *
 *   - `conc_inv` is the CONTROL invariant: three clauses relating the
 *     outstanding-store set and the receiver's program counter to the shared
 *     status word. It needs no well-formedness hypotheses at all. Mutual
 *     exclusion (`no_outstanding_write_during_copy`) and the owner's having no
 *     enabled transition during the pending window
 *     (`no_owner_write_while_pending`, `no_owner_commit_while_pending`) are
 *     DERIVED from it, not assumed by fixing a trace shape.
 *   - `copy_inv` is the MESSAGE invariant: what is actually in the shared
 *     frame, and what the receiver has copied out so far. Its preservation is
 *     the one place D2 (Phase 5.75's T1) does real work, which is why it is
 *     the only invariant needing `amp_partition_wf`.
 *
 * `cinv` is their conjunction, `reachable_cinv` lifts it to every reachable
 * state, and the two results worth quoting elsewhere are
 * `buffer_complete_while_pending` (whenever the channel is pending — the only
 * window in which the receiving kernel reads — every buffer frame ALREADY
 * holds the whole sent message, so there is no partial buffer to observe) and
 * `delivered_message_is_intact` (whatever the receiving kernel hands the
 * receiving application is bit-for-bit the message that was sent, under any
 * interleaving whatsoever). The latter is what REQ-MSG-11 should be read
 * against.
 *
 * STILL NOT GENERAL, AND NOT CLAIMED TO BE. There is no projection from an
 * arbitrary trace onto a SEQUENCE of abstract protocol steps, so "every trace
 * refines a run of the atomic protocol" is not proved here.
 * `interleaved_round_trip_refines_protocol` exhibits ONE round trip's worth of
 * that projection: it fixes where the two commit steps fall and quantifies
 * over everything between them, which is enough to re-derive
 * `xchan_send_msg` and `xchan_recv_ack` from a genuine trace but is not a
 * forward simulation. Building the simulation relation (and thereby covering
 * repeated round trips) is the remaining Phase 6 work; the plan tracks it.
 *
 * D2 (ownership mutex) IS CITED, NOT REPROVED. The one fact this development
 * leans on hardest is Phase 5.75's T1 (`buffer_write_requires_owner`): on a
 * declared channel's buffer, the ONLY thread that ever holds write authority
 * is that channel's declared send-owner. Every "other thread" label below
 * (`COther`) is guarded by `amp_step_t t ... /\ t \<noteq> tp_send_owner tp ch`,
 * and T1 alone (no locale, no A-THR) is what proves such a step can never
 * touch the buffer — this is D2, cited exactly as the plan predicts ("fully
 * discharged by Phase 5.75 ... it is the side condition D1 cites"). The
 * owner's OWN store is similarly guarded by `owner_status ch tp (cs_xm s)
 * (tp_send_owner tp ch) = TRunning`, so a second send while the first is
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
 * A-AVL, THE ACCEPTED AVAILABILITY GAP. The sender blocks until the ack,
 * unconditionally — there is no timeout (see the plan's Phase 6). A receiver
 * that never acks therefore wedges the sending thread forever, which is a real
 * receiver-to-sender interference channel that this phase does not close and
 * does not claim to. It is named A-AVL in the TCB table and accepted, not
 * assumed away; Phase 8's wait-free channel is what removes it.
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
 * D3-a is the reason the per-frame split matters for the C code too: the
 * fences that must bracket each copy loop are exactly the boundaries between
 * the `COwnerWrite`/`CRecvCopy` runs and their following commit steps.
 *
 * SCOPE — ONE CHANNEL, ONE ROUND TRIP. Exactly Phase 5.5/5.75's scope: a
 * single message's lifecycle (one send, one recv/ack), with an arbitrary
 * FINITE number of other threads' steps interleaved anywhere around it.
 * REQ-MSG-7's channel-independence result already says traffic on other
 * channels cannot perturb this one, so nothing is lost by not modelling
 * multiple channels' protocols racing here. `msg` being a parameter of `cstep`
 * rather than mutable state is what fixes the scope at one message; covering
 * repeated round trips is part of the simulation work above, not a separate
 * exercise.
 *
 * This theory is organized in the usual four zones (plan section 2.5).
 *)

theory AMP_Concurrency
imports "AMP_Thread.AMP_Thread"
begin

section \<open>Specification\<close>

subsection \<open>D1 — the receiver's control state\<close>

(* The receiving KERNEL's progress through its half of the protocol: idle, or
   part-way through the bounded copy loop that empties the shared frame into
   the application's own receive buffer. The sender's equivalent progress is
   NOT a fresh datatype: owner_status (Phase 5.75) already derives it from the
   channel's own runtime status, and cs_written below supplies the extra
   information owner_status does not track (which of the owner's per-frame
   stores have landed but not yet been made visible by the status-word
   store). *)
datatype recv_pc = RIdle | RCopy

subsection \<open>D1 — the explicit interleaved state\<close>

(* The state this phase's machine steps over.

     cs_mem      system memory, including the channel's shared frame.
     cs_xm       channel ch's own runtime status entry (a full xchan_map, but
                 only ch's entry is ever touched below).
     cs_written  the set of ch buffer frames the owner has STORED but not yet
                 made visible by the status-word store. Empty means "no store
                 outstanding"; a proper non-empty subset of ch_buffer ch is
                 precisely a PARTIALLY WRITTEN BUFFER — the state the previous
                 model could not represent, and the one every tearing question
                 is about.
     cs_shadow   GHOST STATE (see abs_mem, and cstep_ignores_shadow for the
                 proof that it is one): the buffer's content as of the last
                 commit. No transition guard reads it, so it cannot restrict
                 which traces exist; it exists only to give the ABSTRACT
                 protocol state a well-defined buffer content while the
                 owner's copy loop is part-way through, and is not implemented
                 in the kernel.
     cs_recv_pc  the receiving kernel's progress.
     cs_recv_val what the receiving kernel has copied out so far, i.e. the
                 application's own receive buffer, as a partial map so that
                 "not yet copied" is distinguishable from "copied a value that
                 happens to be the default". This is the field that makes
                 message integrity a claim about REAL STATE the application
                 can go on to read, rather than a claim about shared memory at
                 an index; note it deliberately SURVIVES the acknowledgement,
                 which is the whole content of the copy redesign. *)
record 'v conc_state =
  cs_mem      :: "obj_ref \<Rightarrow> 'v"
  cs_xm       :: xchan_map
  cs_written  :: "obj_ref set"
  cs_shadow   :: "obj_ref \<Rightarrow> 'v"
  cs_recv_pc  :: recv_pc
  cs_recv_val :: "obj_ref \<rightharpoonup> 'v"

(* The six actions this machine's threads can take. COwnerWrite f is ONE
   iteration of the sending kernel's copy loop and COwnerCommit is the
   status-word store that publishes it — a real fence separates them (D3-a).
   CRecvStart, CRecvCopy f and CRecvCommit are the receiving kernel's mirror
   image. COther t is every other thread's activity, interleaved freely —
   including other threads on the SAME core as the sender or receiver, which
   is exactly the case T1 (Phase 5.75) exists to rule safe. *)
datatype clabel =
    COwnerWrite obj_ref
  | COwnerCommit
  | COther thread_id
  | CRecvStart
  | CRecvCopy obj_ref
  | CRecvCommit

(* cstep bp ch tp msg s l s': one labelled transition of the machine, for a
   fixed channel ch, thread assignment tp, and message value msg (msg is a
   parameter, not part of the mutable state — mirroring xchan_send_msg's own
   shape, where msg is an argument to the relation, not carried in xm).

   cstep_owner_write: one iteration of the sending kernel's copy loop. Enabled
   only when the owner is actually free to run (owner_status ... = TRunning —
   by owner_status's own definition this is equivalent to ch not currently
   being pending, so this is also where "no store into a frame someone may be
   reading" fails to have an enabled transition, exactly as T3 predicts).
   Stores msg f into ONE buffer frame and records the store as outstanding.
   Note there is no requirement that the loop visit frames in any order, or
   only once each; nothing below needs one.

   cstep_owner_commit: enabled only once the loop has covered the WHOLE buffer
   (ch_buffer ch \<subseteq> cs_written s) — this is the loop's exit condition, and it is
   what makes "the published buffer is complete" a guard rather than a wish.
   Flips ch's status word to XSendPending (the send's actual linearization
   point), clears the outstanding set, and takes the ghost snapshot. Touches
   no memory.

   cstep_other: any OTHER thread's permission-respecting step (Phase 5.75's
   amp_step_t), for any thread that is NOT ch's declared send-owner. No
   further restriction: this is deliberately allowed at ANY point in the
   trace, including in the middle of either copy loop, which is exactly the
   interleaving this phase must show is harmless (see
   cstep_other_no_buffer_write below).

   cstep_recv_start: the receiving kernel enters its copy loop. Enabled only
   when it is idle and ch is genuinely pending; clears the receive buffer so
   that what the loop delivers is what THIS message put there.

   cstep_recv_copy: one iteration of the receiving kernel's copy loop — load
   one buffer frame, store it into the application's receive buffer. This is
   the step that could tear, if the buffer could be observed part-written.

   cstep_recv_commit: enabled only once the loop has covered the whole buffer.
   Flips ch's status word back to XIdle (the recv/ack's own linearization
   point) and returns the receiving kernel to idle. cs_recv_val is left alone:
   the application keeps the copy. *)
inductive cstep ::
  "amp_partition \<Rightarrow> amp_channel \<Rightarrow> thread_partition \<Rightarrow> (obj_ref \<Rightarrow> 'v)
     \<Rightarrow> 'v conc_state \<Rightarrow> clabel \<Rightarrow> 'v conc_state \<Rightarrow> bool"
  for bp ch tp msg
where
  cstep_owner_write:
    "\<lbrakk> owner_status ch tp (cs_xm s) (tp_send_owner tp ch) = TRunning;
       f \<in> ch_buffer ch \<rbrakk>
     \<Longrightarrow> cstep bp ch tp msg s (COwnerWrite f)
           (s\<lparr> cs_mem := (cs_mem s)(f := msg f),
               cs_written := insert f (cs_written s) \<rparr>)"
| cstep_owner_commit:
    "ch_buffer ch \<subseteq> cs_written s
     \<Longrightarrow> cstep bp ch tp msg s COwnerCommit
           (s\<lparr> cs_xm := (cs_xm s)(ch \<mapsto> XSendPending),
               cs_written := {},
               cs_shadow := cs_mem s \<rparr>)"
| cstep_other:
    "\<lbrakk> t \<noteq> tp_send_owner tp ch; amp_step_t t (cs_mem s) m' bp tp \<rbrakk>
     \<Longrightarrow> cstep bp ch tp msg s (COther t) (s\<lparr> cs_mem := m' \<rparr>)"
| cstep_recv_start:
    "\<lbrakk> cs_recv_pc s = RIdle; cs_xm s ch = Some XSendPending \<rbrakk>
     \<Longrightarrow> cstep bp ch tp msg s CRecvStart
           (s\<lparr> cs_recv_pc := RCopy, cs_recv_val := Map.empty \<rparr>)"
| cstep_recv_copy:
    "\<lbrakk> cs_recv_pc s = RCopy; f \<in> ch_buffer ch \<rbrakk>
     \<Longrightarrow> cstep bp ch tp msg s (CRecvCopy f)
           (s\<lparr> cs_recv_val := (cs_recv_val s)(f \<mapsto> cs_mem s f) \<rparr>)"
| cstep_recv_commit:
    "\<lbrakk> cs_recv_pc s = RCopy; ch_buffer ch \<subseteq> dom (cs_recv_val s) \<rbrakk>
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

inductive_cases cstep_owner_write_E[elim!]: "cstep bp ch tp msg s (COwnerWrite f) s'"
inductive_cases cstep_owner_commit_E[elim!]: "cstep bp ch tp msg s COwnerCommit s'"
inductive_cases cstep_other_E[elim!]: "cstep bp ch tp msg s (COther t) s'"
inductive_cases cstep_recv_start_E[elim!]: "cstep bp ch tp msg s CRecvStart s'"
inductive_cases cstep_recv_copy_E[elim!]: "cstep bp ch tp msg s (CRecvCopy f) s'"
inductive_cases cstep_recv_commit_E[elim!]: "cstep bp ch tp msg s CRecvCommit s'"
inductive_cases csteps_nil_E[elim!]: "csteps bp ch tp msg s [] s'"
inductive_cases csteps_cons_E[elim!]: "csteps bp ch tp msg s (l # ls) s''"

subsection \<open>D1 — the control invariant\<close>

(* conc_inv ch s: the CONTROL invariant. It pins down which interleavings this
   machine can actually reach, using only the control skeleton — the
   outstanding-store set, the receiver's program counter, and the shared
   status word. It mentions no memory contents and needs no well-formedness
   hypothesis, which is why every exclusion result below is hypothesis-free.

     (A0) the owner only ever has stores outstanding into ch's own buffer.
     (A)  if the owner has ANY store outstanding, ch is NOT pending — i.e. a
          part-written buffer only ever exists while the channel is idle.
     (B)  if the receiving kernel is mid-copy, ch IS pending — i.e. the only
          window in which the buffer is read is one in which it is complete.

   These are deliberately NOT stated as "the two sides never touch the buffer
   at the same time" — that is the CONSEQUENCE
   (no_outstanding_write_during_copy below), derived by putting (A) and (B)
   together: mid-copy forces pending by (B), and pending forbids an
   outstanding store by (A). Stating the invariant over the control skeleton
   rather than over the conclusion is what makes it inductive; the mutual
   exclusion itself is not. *)
definition conc_inv :: "amp_channel \<Rightarrow> 'v conc_state \<Rightarrow> bool" where
  "conc_inv ch s \<equiv>
     cs_written s \<subseteq> ch_buffer ch
     \<and> (cs_written s \<noteq> {} \<longrightarrow> cs_xm s ch \<noteq> Some XSendPending)
     \<and> (cs_recv_pc s = RCopy \<longrightarrow> cs_xm s ch = Some XSendPending)"

(* copy_inv ch msg s: the MESSAGE invariant — what is actually in the shared
   frame and in the receiver's copy.

     (C1) every frame the owner has stored holds msg.
     (C2) whenever ch is pending, the WHOLE buffer holds msg. This is the
          no-partial-buffer property in value form, and it is the clause the
          previous model had no way even to state.
     (C3) every value the receiving kernel has copied out equals msg at that
          frame — no torn or stale value has ever been delivered.
     (C4) when nothing is outstanding, the ghost shadow agrees with real
          memory on the buffer; this is what makes abs_mem below mean "memory
          as of the last commit" rather than an arbitrary function.

   Unlike conc_inv this one is about memory, so its preservation is where D2
   (Phase 5.75's T1, via cstep_other_no_buffer_write) does its work, and it is
   the only invariant here that needs amp_partition_wf. *)
definition copy_inv :: "amp_channel \<Rightarrow> (obj_ref \<Rightarrow> 'v) \<Rightarrow> 'v conc_state \<Rightarrow> bool" where
  "copy_inv ch msg s \<equiv>
     (\<forall>f \<in> cs_written s. cs_mem s f = msg f)
     \<and> (cs_xm s ch = Some XSendPending \<longrightarrow> (\<forall>f \<in> ch_buffer ch. cs_mem s f = msg f))
     \<and> (\<forall>f v. cs_recv_val s f = Some v \<longrightarrow> v = msg f)
     \<and> (cs_written s = {} \<longrightarrow> (\<forall>f \<in> ch_buffer ch. cs_shadow s f = cs_mem s f))"

(* The two together. Everything downstream of the copy loops needs both:
   copy_inv's (C3) is only preserved because conc_inv's (B) says the receiving
   kernel reads inside the pending window, and (C2) says the buffer is
   complete there. *)
definition cinv :: "amp_channel \<Rightarrow> (obj_ref \<Rightarrow> 'v) \<Rightarrow> 'v conc_state \<Rightarrow> bool" where
  "cinv ch msg s \<equiv> conc_inv ch s \<and> copy_inv ch msg s"

(* conc_init ch s: the machine's starting shape — ch idle, no store
   outstanding, receiving kernel idle with an empty receive buffer, ghost
   shadow agreeing with memory. Every reachable state of a run begun here
   satisfies cinv (conc_init_cinv, then csteps_preserves_cinv), which is what
   makes the invariants statements about REACHABILITY rather than extra
   hypotheses quietly narrowing the theorems below. *)
definition conc_init :: "amp_channel \<Rightarrow> 'v conc_state \<Rightarrow> bool" where
  "conc_init ch s \<equiv>
     cs_xm s ch = Some XIdle \<and> cs_written s = {} \<and> cs_recv_pc s = RIdle
     \<and> cs_recv_val s = Map.empty
     \<and> (\<forall>f \<in> ch_buffer ch. cs_shadow s f = cs_mem s f)"

subsection \<open>D1 — the abstract buffer content\<close>

(* abs_mem ch s: system memory as the ABSTRACT protocol sees it — real memory
   everywhere except ch's buffer, where it is the last committed content. The
   two differ exactly while the owner's copy loop is part-way through, which
   is the whole reason the abstract protocol can treat a send as atomic: at
   every point where abs_mem's buffer half moves, it moves all at once, to a
   complete message. This is the projection the eventual forward simulation
   will be built on, and it is already what makes
   interleaved_round_trip_refines_protocol's footprint clause true. *)
definition abs_mem :: "amp_channel \<Rightarrow> 'v conc_state \<Rightarrow> (obj_ref \<Rightarrow> 'v)" where
  "abs_mem ch s = (\<lambda>f. if f \<in> ch_buffer ch then cs_shadow s f else cs_mem s f)"

section \<open>Proof development (internal machinery)\<close>

subsection \<open>The shadow really is ghost state\<close>

(* No transition guard mentions cs_shadow, so perturbing it cannot enable or
   disable anything: from any state differing only in the shadow, the same
   label is available and leads to a state agreeing on every REAL component.
   This is what licenses reading abs_mem as a projection of the machine rather
   than as an extra piece of the machine — without it, "the buffer's last
   committed content" would be a modelling assumption rather than a
   derived quantity. *)
lemma cstep_ignores_shadow:
  assumes step: "cstep bp ch tp msg s l s'"
  shows "\<exists>u'. cstep bp ch tp msg (s\<lparr> cs_shadow := g \<rparr>) l u'
              \<and> cs_mem u' = cs_mem s' \<and> cs_xm u' = cs_xm s'
              \<and> cs_written u' = cs_written s' \<and> cs_recv_pc u' = cs_recv_pc s'
              \<and> cs_recv_val u' = cs_recv_val s'"
  using step by (cases rule: cstep.cases) (fastforce intro: cstep.intros)+

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
   outstanding-store set, the ghost shadow, or either of the receiver's
   fields — only cs_mem moves, and only within the bound the definition
   itself already states. *)
lemma cstep_other_preserves_control:
  assumes step: "cstep bp ch tp msg s (COther t) s'"
  shows "cs_xm s' = cs_xm s" and "cs_written s' = cs_written s"
    and "cs_recv_pc s' = cs_recv_pc s" and "cs_recv_val s' = cs_recv_val s"
    and "cs_shadow s' = cs_shadow s"
  using step by (cases rule: cstep_other_E; simp)+

subsection \<open>The control invariant is genuinely inductive\<close>

(* The starting shape satisfies both invariants: every clause is vacuous there
   (nothing outstanding, receiver idle with an empty buffer, channel idle),
   except (C4), which conc_init states outright. Non-vacuity for the
   invariants — without this, "every reachable state satisfies cinv" could
   hold because no state is reachable. *)
lemma conc_init_conc_inv: "conc_init ch s \<Longrightarrow> conc_inv ch s"
  by (simp add: conc_init_def conc_inv_def)

(* The same for the message invariant, and note it holds for EVERY msg: at the
   starting shape nothing has been stored, published or copied, so no clause
   constrains what the message will turn out to be. *)
lemma conc_init_copy_inv: "conc_init ch s \<Longrightarrow> copy_inv ch msg s"
  by (simp add: conc_init_def copy_inv_def)

(* The two packaged together, which is the form every trace-level result
   below starts from. *)
lemma conc_init_cinv: "conc_init ch s \<Longrightarrow> cinv ch msg s"
  by (simp add: cinv_def conc_init_conc_inv conc_init_copy_inv)

(* The core of D1: EVERY one of the six transitions preserves conc_inv, with
   no well-formedness hypothesis at all. Each case is where one specific piece
   of the design pays for itself:

     COwnerWrite  — adds to the outstanding set, so clause (A) must be
                    re-established; the guard owner_status ... = TRunning is
                    exactly what supplies it (via T3, unfolded above). This is
                    the case that would FAIL if the design had a timeout,
                    since a timeout is precisely a way for the owner to run
                    while ch is pending. (A0) needs the guard f \<in> ch_buffer ch.
     COwnerCommit — empties the outstanding set, making (A) vacuous and (A0)
                    trivial, and sets the status pending, which is what (B)
                    needs.
     COther       — touches only cs_mem; all three clauses are about control
                    state, so they survive untouched. (That such a step cannot
                    touch the BUFFER is a separate fact — D2, used for
                    copy_inv below, not needed here.)
     CRecvStart   — puts the receiving kernel mid-copy, so clause (B) must be
                    re-established; its own guard (ch is pending) supplies it.
     CRecvCopy    — moves no control state at all.
     CRecvCommit  — returns the status to idle, re-establishing (A), and
                    returns the receiver to idle, making (B) vacuous. *)
lemma cstep_preserves_conc_inv:
  assumes step: "cstep bp ch tp msg s l s'" and inv: "conc_inv ch s"
  shows "conc_inv ch s'"
  using step
proof (cases rule: cstep.cases)
  case (cstep_owner_write f)
  then show ?thesis
    using inv by (auto simp: conc_inv_def owner_running_iff_not_pending)
next
  case cstep_owner_commit
  then show ?thesis using inv by (auto simp: conc_inv_def)
next
  case (cstep_other t m')
  then show ?thesis using inv by (auto simp: conc_inv_def)
next
  case cstep_recv_start
  then show ?thesis using inv by (auto simp: conc_inv_def)
next
  case (cstep_recv_copy f)
  then show ?thesis using inv by (auto simp: conc_inv_def)
next
  case cstep_recv_commit
  then show ?thesis using inv by (auto simp: conc_inv_def)
qed

subsection \<open>The message invariant is genuinely inductive\<close>

(* The other half of D1, and the place D2 is actually consumed. Case by case:

     COwnerWrite  — stores msg f at f and records it, re-establishing (C1) at
                    the new frame and leaving it at the others. (C2) is vacuous
                    because the guard says ch is not pending. (C4) becomes
                    vacuous because the outstanding set is now non-empty —
                    this is exactly the window in which the shadow and real
                    memory legitimately disagree.
     COwnerCommit — the guard says the copy loop covered the WHOLE buffer, and
                    (C1) says every covered frame holds msg, so (C2) follows.
                    This is the step where "the published buffer is complete"
                    is established, and it is established from the loop's exit
                    condition rather than assumed.
     COther       — D2 (cstep_other_no_buffer_write) says the buffer does not
                    move, and conc_inv's (A0) says the outstanding set lies
                    inside the buffer, so (C1), (C2) and (C4) all survive. This
                    is the ONLY case needing amp_partition_wf, and the only
                    place T1 is used.
     CRecvStart   — empties the receive buffer, making (C3) vacuous.
     CRecvCopy    — THE CRUX. It copies cs_mem s f into the receive buffer, so
                    (C3) demands cs_mem s f = msg f. The guard gives
                    f \<in> ch_buffer ch and mid-copy; conc_inv's (B) turns mid-copy
                    into "ch is pending"; and (C2) then gives the value. This
                    single chain is the no-torn-read argument.
     CRecvCommit  — returns the status to idle, making (C2) vacuous; touches
                    neither memory nor the receive buffer. *)
lemma cstep_preserves_copy_inv:
  assumes wf: "amp_partition_wf bp" and chd: "ch \<in> ap_channels bp"
      and step: "cstep bp ch tp msg s l s'"
      and cinv: "conc_inv ch s" and inv: "copy_inv ch msg s"
  shows "copy_inv ch msg s'"
  using step
proof (cases rule: cstep.cases)
  case (cstep_owner_write f)
  then show ?thesis
    using inv by (auto simp: copy_inv_def owner_running_iff_not_pending)
next
  case cstep_owner_commit
  then show ?thesis using inv by (fastforce simp: copy_inv_def)
next
  case (cstep_other t m')
  then have st: "cstep bp ch tp msg s (COther t) s'" by (simp add: cstep.cstep_other)
  from cstep_other_no_buffer_write[OF wf chd st] cstep_other_preserves_control[OF st]
  have buf: "\<forall>f \<in> ch_buffer ch. cs_mem s' f = cs_mem s f"
   and ctl: "cs_xm s' = cs_xm s" "cs_written s' = cs_written s"
            "cs_recv_val s' = cs_recv_val s" "cs_shadow s' = cs_shadow s" by auto
  from cinv have sub: "cs_written s \<subseteq> ch_buffer ch" by (simp add: conc_inv_def)
  show ?thesis using inv buf ctl sub by (fastforce simp: copy_inv_def)
next
  case cstep_recv_start
  then show ?thesis using inv by (auto simp: copy_inv_def)
next
  case (cstep_recv_copy f)
  then show ?thesis
    using inv cinv by (fastforce simp: copy_inv_def conc_inv_def)
next
  case cstep_recv_commit
  then show ?thesis using inv by (auto simp: copy_inv_def)
qed

(* Both invariants at once. The order of the conjuncts matters to the proof,
   not just to the reader: cstep_preserves_copy_inv consumes conc_inv at the
   PRE-state, so the control invariant has to be available before the message
   invariant can be re-established. *)
lemma cstep_preserves_cinv:
  assumes wf: "amp_partition_wf bp" and chd: "ch \<in> ap_channels bp"
      and step: "cstep bp ch tp msg s l s'" and inv: "cinv ch msg s"
  shows "cinv ch msg s'"
  using inv cstep_preserves_conc_inv[OF step] cstep_preserves_copy_inv[OF wf chd step]
  by (simp add: cinv_def)

subsection \<open>Stuttering: a run of only COther labels leaves the protocol-relevant state fixed\<close>

(* ceq s s' ch: s and s' agree on everything the protocol cares about — ch's
   status word, the outstanding-store set, the ghost shadow, both of the
   receiver's fields, and the content of ch's buffer (memory OUTSIDE the
   buffer is deliberately not compared here: other threads' steps are free to
   change it, and the protocol correctness argument below never needs it to be
   fixed). *)
definition ceq :: "'v conc_state \<Rightarrow> 'v conc_state \<Rightarrow> amp_channel \<Rightarrow> bool" where
  "ceq s s' ch \<equiv> cs_xm s' = cs_xm s \<and> cs_written s' = cs_written s
                  \<and> cs_recv_pc s' = cs_recv_pc s \<and> cs_recv_val s' = cs_recv_val s
                  \<and> cs_shadow s' = cs_shadow s
                  \<and> (\<forall>f \<in> ch_buffer ch. cs_mem s' f = cs_mem s f)"

(* ceq is reflexive: an empty run of COther steps trivially leaves the
   protocol-relevant state fixed. The base case of the induction below. *)
lemma ceq_refl: "ceq s s ch"
  by (simp add: ceq_def)

(* ceq is transitive: chaining two COther-only runs is itself a COther-only
   run's worth of preservation. The step case of the induction below. *)
lemma ceq_trans: "ceq s s' ch \<Longrightarrow> ceq s' s'' ch \<Longrightarrow> ceq s s'' ch"
  by (simp add: ceq_def)

(* D1's stuttering lemma: ANY finite run consisting entirely of COther labels
   — any number of other threads, in any order, touching whatever non-buffer
   memory they like — is invisible to the protocol state. *)
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
   itself, one transition can change neither ch's status map nor its buffer.
   The six cases split into three genuinely different reasons:

     COwnerWrite  — NOT ENABLED. Its guard requires the owner to be running,
                    which (T3, unfolded) contradicts ch being pending. This is
                    the exclusion the previous version of this theory assumed
                    by fixing a trace shape; here it is derived.
     COwnerCommit — NOT ENABLED. Its guard requires the whole buffer to be
                    outstanding, which conc_inv's (A) forbids while pending
                    (a non-empty outstanding set and pending cannot coexist),
                    provided the buffer is non-empty — hence the hypothesis.
     COther       — ENABLED, and harmless: T1 (Phase 5.75, via
                    cstep_other_no_buffer_write) says a non-owner thread
                    cannot write the buffer, and the step touches no control
                    state.
     CRecvStart,
     CRecvCopy    — ENABLED, and harmless: they move the receiving kernel's
                    own state and its private copy, never the shared frame.
     CRecvCommit  — excluded by hypothesis; it is the step that ENDS the
                    pending window, so freezing cannot be claimed across it. *)
lemma cstep_pending_preserves_buffer:
  assumes wf: "amp_partition_wf bp" and chd: "ch \<in> ap_channels bp"
      and inv: "conc_inv ch s"
      and nemp: "ch_buffer ch \<noteq> {}"
      and pend: "cs_xm s ch = Some XSendPending"
      and notack: "l \<noteq> CRecvCommit"
      and step: "cstep bp ch tp msg s l s'"
  shows "cs_xm s' = cs_xm s \<and> (\<forall>f \<in> ch_buffer ch. cs_mem s' f = cs_mem s f)"
  using step
proof (cases rule: cstep.cases)
  case (cstep_owner_write f)
  (* Not enabled: the guard says the owner is running, T3 says that means
     not pending, and pend says otherwise. *)
  with pend show ?thesis by (simp add: owner_running_iff_not_pending)
next
  case cstep_owner_commit
  (* Not enabled: the guard says the whole (non-empty) buffer is outstanding,
     and conc_inv (A) says nothing can be outstanding while pending. *)
  with inv pend nemp show ?thesis by (auto simp: conc_inv_def)
next
  case (cstep_other t m')
  then have st: "cstep bp ch tp msg s (COther t) s'" by (simp add: cstep.cstep_other)
  from cstep_other_no_buffer_write[OF wf chd st] cstep_other_preserves_control[OF st]
  show ?thesis by simp
next
  case cstep_recv_start
  then show ?thesis by simp
next
  case (cstep_recv_copy f)
  then show ?thesis by simp
next
  case cstep_recv_commit
  with notack show ?thesis by simp
qed

subsection \<open>Traces compose\<close>

(* Concatenation of traces, needed to reassemble the round trip below out of
   the segments its hypotheses name. *)
lemma csteps_append:
  "csteps bp ch tp msg s ls sm \<Longrightarrow> csteps bp ch tp msg sm ls' s'
   \<Longrightarrow> csteps bp ch tp msg s (ls @ ls') s'"
  by (induct rule: csteps.induct) (auto intro: csteps.intros)

subsection \<open>No commit step, no status change\<close>

(* Only the two commit steps ever touch the status map, so a segment
   containing neither leaves it exactly where it was. This is what lets the
   round-trip theorem below hypothesise nothing about the sending kernel's
   copy loop beyond "it has not committed yet" and still know the channel is
   idle when the commit finally happens. *)
lemma csteps_no_commit_preserves_xm:
  "csteps bp ch tp msg s ls s' \<Longrightarrow> COwnerCommit \<notin> set ls \<Longrightarrow> CRecvCommit \<notin> set ls
   \<Longrightarrow> cs_xm s' = cs_xm s"
proof (induct rule: csteps.induct)
  case (csteps_nil s)
  then show ?case by simp
next
  case (csteps_cons s l sm ls s'')
  from csteps_cons.prems have lo: "l \<noteq> COwnerCommit" and lr: "l \<noteq> CRecvCommit"
    and rest: "COwnerCommit \<notin> set ls" "CRecvCommit \<notin> set ls" by auto
  from csteps_cons.hyps(1) lo lr have "cs_xm sm = cs_xm s"
    by (cases rule: cstep.cases) auto
  with csteps_cons.hyps(3)[OF rest] show ?case by simp
qed

section \<open>Results\<close>

subsection \<open>D1 — every reachable state satisfies the invariants\<close>

(* The invariants lifted from one step to an ARBITRARY trace: any finite
   sequence of labelled transitions, in any order, preserves them. Note what
   is and is not quantified here — unlike the round-trip theorem later in this
   section, `ls` is a completely arbitrary label list. Nothing fixes how many
   protocol steps it contains, in which order, or how much other activity
   surrounds them. *)
theorem csteps_preserves_conc_inv:
  "csteps bp ch tp msg s ls s' \<Longrightarrow> conc_inv ch s \<Longrightarrow> conc_inv ch s'"
proof (induct rule: csteps.induct)
  case (csteps_nil s)
  then show ?case by simp
next
  case (csteps_cons s l sm ls s'')
  then show ?case using cstep_preserves_conc_inv by blast
qed

(* The same for the message invariant. This one carries amp_partition_wf and
   the channel's declaredness, because its single-step case does: they are
   what D2 (Phase 5.75's T1) needs in order to say a non-owner thread's step
   cannot disturb the buffer. Everything about message integrity below flows
   through this theorem, and hence through T1. *)
theorem csteps_preserves_cinv:
  assumes wf: "amp_partition_wf bp" and chd: "ch \<in> ap_channels bp"
  shows "csteps bp ch tp msg s ls s' \<Longrightarrow> cinv ch msg s \<Longrightarrow> cinv ch msg s'"
proof (induct rule: csteps.induct)
  case (csteps_nil s)
  then show ?case by simp
next
  case (csteps_cons s l sm ls s'')
  then show ?case using cstep_preserves_cinv[OF wf chd] by blast
qed

(* Packaged for use: every state reachable from the machine's starting shape
   satisfies both invariants. This is what lets every result below be read as
   a fact about the system rather than as a conditional statement about states
   that might never occur. *)
corollary reachable_cinv:
  assumes wf: "amp_partition_wf bp" and chd: "ch \<in> ap_channels bp"
      and init: "conc_init ch s" and run: "csteps bp ch tp msg s ls s'"
  shows "cinv ch msg s'"
  using csteps_preserves_cinv[OF wf chd run conc_init_cinv[OF init]] .

subsection \<open>D2 — mutual exclusion, derived rather than assumed\<close>

(* THE ORDERING EXCLUSION. In any state satisfying the control invariant —
   hence in any reachable state — the owner CANNOT store into the buffer while
   ch is pending. There is no such transition; it is not that the transition
   exists and is shown harmless. This is the trace-level form of REQ-MSG-3 ("a
   pending message is never overwritten"): previously a statement about the
   abstract relation having no enabled instance, now a statement about the
   interleaved machine having no enabled transition. *)
theorem no_owner_write_while_pending:
  assumes pend: "cs_xm s ch = Some XSendPending"
  shows "\<not> cstep bp ch tp msg s (COwnerWrite f) s'"
  using pend by (auto simp: owner_running_iff_not_pending)

(* Its companion: nor can the owner COMMIT while pending, because conc_inv's
   clause (A) rules out anything outstanding in that state. Together with the
   previous theorem this says the owner has NO enabled transition at all
   during the pending window — which is exactly "the sender blocks until the
   ack", now a property of the interleaved model rather than a property of
   owner_status's definition. *)
theorem no_owner_commit_while_pending:
  assumes inv: "conc_inv ch s" and nemp: "ch_buffer ch \<noteq> {}"
      and pend: "cs_xm s ch = Some XSendPending"
  shows "\<not> cstep bp ch tp msg s COwnerCommit s'"
  using inv nemp pend by (auto simp: conc_inv_def)

(* D2 proper, in the form the plan states it — "at most one agent may write
   the buffer at any instant" — and now in the sharper form the per-frame
   split makes available: whenever the receiving kernel is copying, the owner
   has NOTHING outstanding at all. Not "the owner is not writing right now",
   but "there is no partially completed write in existence". Derived from the
   two control clauses together, exactly as conc_inv's comment describes. *)
theorem no_outstanding_write_during_copy:
  assumes inv: "conc_inv ch s" and rd: "cs_recv_pc s = RCopy"
  shows "cs_written s = {}"
  using inv rd by (auto simp: conc_inv_def)

subsection \<open>D1 — partial writes are unobservable\<close>

(* THE RESULT THE PREVIOUS MODEL COULD NOT STATE. Whenever ch is pending —
   and by conc_inv's (B) that is the only window in which the receiving kernel
   ever loads from the shared frame — the buffer ALREADY holds the whole
   message, every frame of it. A partially written buffer is a state this
   machine genuinely has (cs_written a proper non-empty subset of ch_buffer),
   and this theorem says the receiving side can never be looking at one.

   Read together with no_outstanding_write_during_copy: that theorem says no
   write is in flight during a copy; this one says the buffer is complete.
   Neither is derivable from the other, and the earlier model could express
   neither. *)
theorem buffer_complete_while_pending:
  assumes inv: "copy_inv ch msg s" and pend: "cs_xm s ch = Some XSendPending"
  shows "\<forall>f \<in> ch_buffer ch. cs_mem s f = msg f"
  using inv pend by (simp add: copy_inv_def)

subsection \<open>D1 — message integrity across an ARBITRARY interleaving\<close>

(* Take any state where ch is pending, and ANY finite trace at all out of it —
   any number of threads, any labels, in any order — subject to the single
   condition that the acknowledgement has not yet occurred. Then the status
   map is unchanged and ch's buffer is bit-for-bit unchanged.

   The contrast with interleaved_round_trip_refines_protocol below is the
   point. That theorem fixes where the commit steps fall and quantifies over
   the activity between them. This one quantifies over the label list itself:
   `ls` is an arbitrary clabel list, and the proof works by showing that the
   transitions which would break the property are NOT ENABLED (the owner's
   two), while those that are enabled cannot touch the buffer (T1) or the
   status word.

   That is what makes this a statement about the protocol working under
   interleaving, rather than a statement about one interleaving. *)
theorem pending_window_freezes_the_buffer:
  assumes wf: "amp_partition_wf bp" and chd: "ch \<in> ap_channels bp"
      and nemp: "ch_buffer ch \<noteq> {}"
  shows "csteps bp ch tp msg s ls s' \<Longrightarrow> conc_inv ch s
          \<Longrightarrow> cs_xm s ch = Some XSendPending \<Longrightarrow> CRecvCommit \<notin> set ls
          \<Longrightarrow> cs_xm s' = cs_xm s
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
  from cstep_pending_preserves_buffer[OF wf chd inv nemp pend lne csteps_cons.hyps(1)]
  have mp: "cs_xm sm = cs_xm s"
   and mb: "\<forall>f \<in> ch_buffer ch. cs_mem sm f = cs_mem s f" by auto
  from cstep_preserves_conc_inv[OF csteps_cons.hyps(1) inv] have minv: "conc_inv ch sm" .
  from mp pend have mpend: "cs_xm sm ch = Some XSendPending" by simp
  from csteps_cons.hyps(3)[OF minv mpend na']
  have "cs_xm s'' = cs_xm sm"
   and "\<forall>f \<in> ch_buffer ch. cs_mem s'' f = cs_mem sm f" by auto
  with mp mb show ?case by simp
qed

(* NO TORN OR STALE VALUE IS EVER DELIVERED, under any interleaving. Every
   value the receiving kernel has copied into the application's receive buffer
   equals the sent message at that frame — at every reachable state, with no
   hypothesis about how many other threads ran, what they touched, or where in
   the trace the copy loop's iterations fell.

   This is a claim about the RECEIVER'S OWN STATE, which is what the copy
   redesign bought: the previous model's integrity statement was about shared
   memory at an index, and said nothing about what any reader ended up
   holding. *)
theorem receiver_never_holds_a_torn_value:
  assumes wf: "amp_partition_wf bp" and chd: "ch \<in> ap_channels bp"
      and init: "conc_init ch s" and run: "csteps bp ch tp msg s ls s'"
  shows "\<forall>f v. cs_recv_val s' f = Some v \<longrightarrow> v = msg f"
  using reachable_cinv[OF wf chd init run] by (simp add: cinv_def copy_inv_def)

(* REQ-MSG-11 as it should be stated: what the receiving kernel hands the
   receiving APPLICATION, at the moment it acknowledges, is bit-for-bit the
   message that was sent — every frame present, every frame correct.

   Completeness comes from the copy loop's exit condition (the acknowledgement
   is not enabled until the whole buffer has been copied) and correctness from
   the invariant; and because cs_recv_val survives the acknowledgement, this
   is a statement about memory the application still owns after the channel
   has gone idle and the sender has been released. That is precisely the
   property zero-copy could not have. *)
theorem delivered_message_is_intact:
  assumes wf: "amp_partition_wf bp" and chd: "ch \<in> ap_channels bp"
      and init: "conc_init ch s" and run: "csteps bp ch tp msg s ls s'"
      and ack: "cstep bp ch tp msg s' CRecvCommit s''"
  shows "\<forall>f \<in> ch_buffer ch. cs_recv_val s'' f = Some (msg f)"
proof (intro ballI)
  fix f assume f: "f \<in> ch_buffer ch"
  from ack have dom: "ch_buffer ch \<subseteq> dom (cs_recv_val s')"
            and eq: "cs_recv_val s'' = cs_recv_val s'"
    by (auto elim!: cstep_recv_commit_E)
  from dom f obtain v where v: "cs_recv_val s' f = Some v" by auto
  from receiver_never_holds_a_torn_value[OF wf chd init run] v have "v = msg f" by simp
  with v eq show "cs_recv_val s'' f = Some (msg f)" by simp
qed

subsection \<open>D1 — a genuine interleaved trace refines the atomic protocol\<close>

(* The round trip, end to end, against Phase 3/5.5's ATOMIC relations. Read
   the hypotheses as one shape of trace, from the machine's starting state:

     ws   — the sending kernel's copy loop, ARBITRARILY interleaved with any
            other threads' activity; nothing says how many frames it writes
            per step, in what order, or how much else runs in between. The
            only condition is that neither commit has happened yet.
     COwnerCommit  — the send's linearization point (sC -> sD).
     ms   — the receiving kernel's copy loop, again arbitrarily interleaved,
            and again with only one condition: the acknowledgement has not
            happened yet. Note that nothing here SAYS the receiver copies; the
            acknowledgement's own guard forces it.
     CRecvCommit   — the acknowledgement's linearization point (sG -> sH).

   The three conclusions are exactly the atomic relations, RE-DERIVED (not
   assumed) from this trace. The first is stated over abs_mem rather than
   cs_mem, and that is not a weakening: xchan_send_msg's footprint clause says
   a send changes NOTHING outside ch's buffer, which is false of cs_mem across
   an interleaved segment (other threads legitimately change their own
   memory) and true of the abstract memory the protocol actually talks about.
   abs_mem is where the "send is atomic" abstraction lives, and this theorem
   is where it is cashed.

   WHAT THIS IS NOT. It fixes where the two commit steps fall, so it exhibits
   one round trip's projection onto the atomic protocol rather than proving
   that every trace has one. The general statement is a forward simulation
   over abs_mem with the two commit steps as its non-stuttering cases — the
   remaining Phase 6 work. What justifies restricting attention to this shape
   in the meantime is proved above, not assumed: no_owner_write_while_pending
   and no_owner_commit_while_pending show the owner has no enabled transition
   during the pending window, so no other ordering of the protocol's own
   labels is reachable. *)
theorem interleaved_round_trip_refines_protocol:
  fixes msg :: "obj_ref \<Rightarrow> 'v"
  assumes wf: "amp_partition_wf bp" and chd: "ch \<in> ap_channels bp"
      and nemp: "ch_buffer ch \<noteq> {}"
      and init: "conc_init ch s0"
      and ws: "csteps bp ch tp msg s0 wls sC"
      and wnc: "COwnerCommit \<notin> set wls" "CRecvCommit \<notin> set wls"
      and commit: "cstep bp ch tp msg sC COwnerCommit sD"
      and ms: "csteps bp ch tp msg sD mls sG"
      and mnc: "CRecvCommit \<notin> set mls"
      and rcommit: "cstep bp ch tp msg sG CRecvCommit sH"
  shows "xchan_send_msg ch msg (abs_mem ch sC) (abs_mem ch sD) (cs_xm sC) (cs_xm sD)"
    and "xchan_recv_ack ch (cs_xm sD) (cs_xm sH)"
    and "\<forall>f \<in> ch_buffer ch. cs_recv_val sH f = Some (msg f)"
proof -
  from csteps_no_commit_preserves_xm[OF ws wnc] init
  have idleC: "cs_xm sC ch = Some XIdle" by (simp add: conc_init_def)
  from reachable_cinv[OF wf chd init ws] have invC: "cinv ch msg sC" by simp

  from commit obtain covered: "ch_buffer ch \<subseteq> cs_written sC"
    by (auto elim!: cstep_owner_commit_E)
  have sD: "sD = sC\<lparr> cs_xm := (cs_xm sC)(ch \<mapsto> XSendPending),
                     cs_written := {}, cs_shadow := cs_mem sC \<rparr>"
    using commit by (auto elim!: cstep_owner_commit_E)

  (* The value clause: the loop's exit condition covered the whole buffer, and
     (C1) says every covered frame holds msg. *)
  have bufC: "\<forall>f \<in> ch_buffer ch. cs_mem sC f = msg f"
    using invC covered by (fastforce simp: cinv_def copy_inv_def)

  (* The footprint clause: abs_mem moves only on the buffer, because the
     commit step changes no real memory at all and the shadow is only read
     inside the buffer. *)
  have fp: "changed_frames (abs_mem ch sC) (abs_mem ch sD) \<subseteq> ch_buffer ch"
    using sD by (auto simp: changed_frames_def abs_mem_def split: if_splits)
  have absD: "\<forall>f \<in> ch_buffer ch. abs_mem ch sD f = msg f"
    using sD bufC by (simp add: abs_mem_def)

  show "xchan_send_msg ch msg (abs_mem ch sC) (abs_mem ch sD) (cs_xm sC) (cs_xm sD)"
    unfolding xchan_send_msg_def xchan_send_def
    using idleC fp absD sD by simp

  from sD have pendD: "cs_xm sD ch = Some XSendPending" by simp
  from invC cstep_preserves_conc_inv[OF commit] have invD: "conc_inv ch sD"
    by (simp add: cinv_def)
  from pending_window_freezes_the_buffer[OF wf chd nemp ms invD pendD mnc]
  have xmG: "cs_xm sG = cs_xm sD" by simp
  have sH: "sH = sG\<lparr> cs_xm := (cs_xm sG)(ch \<mapsto> XIdle), cs_recv_pc := RIdle \<rparr>"
    using rcommit by (auto elim!: cstep_recv_commit_E)

  show "xchan_recv_ack ch (cs_xm sD) (cs_xm sH)"
    unfolding xchan_recv_ack_def using pendD sH xmG by simp

  have run: "csteps bp ch tp msg sC (COwnerCommit # mls) sG"
    by (rule csteps_cons[OF commit ms])
  have runs: "csteps bp ch tp msg s0 (wls @ COwnerCommit # mls) sG"
    by (rule csteps_append[OF ws run])
  show "\<forall>f \<in> ch_buffer ch. cs_recv_val sH f = Some (msg f)"
    by (rule delivered_message_is_intact[OF wf chd init runs rcommit])
qed

section \<open>Examples\<close>

subsection \<open>A concrete, genuinely interleaved round trip on the example system\<close>

(* A witness that the round-trip theorem's hypotheses are jointly satisfiable
   — not vacuous — using the same example2/chan01/example_tp/example_msg
   fixtures every earlier phase's non-vacuity section reuses. The "other
   activity" is witnessed non-trivially (the sending kernel's copy loop has a
   genuine COther step interleaved into it, by thread 20 — chan01's own
   RECEIVE owner, taking an unrelated step of its own on core 1's private
   memory) rather than being empty, so this is a genuine interleaving
   instance, not a degenerate serial one. *)

definition example_s0 :: "nat conc_state" where
  "example_s0 = \<lparr> cs_mem = (\<lambda>_. 0), cs_xm = example_xchan0, cs_written = {},
                  cs_shadow = (\<lambda>_. 0), cs_recv_pc = RIdle, cs_recv_val = Map.empty \<rparr>"

(* The example state really is a legitimate starting shape for chan01, so the
   reachability results below are being applied to a genuine initial state
   rather than to an arbitrary one that happens to satisfy the invariants. *)
lemma example_conc_init: "conc_init chan01 example_s0"
  by (simp add: conc_init_def example_s0_def example_xchan0_def chan01_def)

(* A concrete iteration of the sending kernel's copy loop: from the example
   system's idle starting state, chan01's declared send-owner (thread 10, idle
   by example_owner_status_tracks_chan01) stores example_msg's value into
   chan01's one buffer frame (0x8000) — the enabling side conditions of
   cstep_owner_write, discharged for real fixtures rather than left as an
   abstract possibility. *)
lemma example_owner_write:
  "cstep example2 chan01 example_tp example_msg
     example_s0 (COwnerWrite 0x8000)
     (example_s0\<lparr> cs_mem := (cs_mem example_s0)(0x8000 := 42),
                  cs_written := {0x8000} \<rparr>)"
proof -
  have "cstep example2 chan01 example_tp example_msg
          example_s0 (COwnerWrite 0x8000)
          (example_s0\<lparr> cs_mem := (cs_mem example_s0)(0x8000 := example_msg 0x8000),
                       cs_written := insert 0x8000 (cs_written example_s0) \<rparr>)"
  proof (rule cstep_owner_write)
    show "owner_status chan01 example_tp (cs_xm example_s0) (tp_send_owner example_tp chan01) = TRunning"
      using example_owner_status_tracks_chan01(1) by (simp add: example_s0_def example_tp_def)
    show "(0x8000 :: obj_ref) \<in> ch_buffer chan01" by (simp add: chan01_def)
  qed
  then show ?thesis by (simp add: example_msg_def example_s0_def)
qed

(* A concrete instance of a genuine COther transition, interleaved INSIDE the
   sending kernel's copy loop — after the store has landed but before it has
   been published. chan01's own declared RECEIVE owner (thread 20, on core 1)
   — a thread that is emphatically not chan01's send-owner, so cstep_other's
   guard is satisfied — takes a step confined to core 1's own private frame
   0x3000 (thread_owns_priv, via T1). This is the witness that the "arbitrary
   other-thread activity" in the round-trip theorem's hypotheses is genuinely
   instantiable, not just syntactically well-typed. *)
lemma example_other_step:
  "cstep example2 chan01 example_tp example_msg
     (example_s0\<lparr> cs_mem := (cs_mem example_s0)(0x8000 := 42), cs_written := {0x8000} \<rparr>)
     (COther 20)
     ((example_s0\<lparr> cs_mem := (cs_mem example_s0)(0x8000 := 42), cs_written := {0x8000} \<rparr>)
        \<lparr> cs_mem := ((cs_mem example_s0)(0x8000 := 42))(0x3000 := 7) \<rparr>)"
proof (rule cstep_other)
  show "(20 :: thread_id) \<noteq> tp_send_owner example_tp chan01" by (simp add: example_tp_def)
  show "amp_step_t 20 (cs_mem (example_s0\<lparr> cs_mem := (cs_mem example_s0)(0x8000 := 42),
                                           cs_written := {0x8000} \<rparr>))
          (((cs_mem example_s0)(0x8000 := 42))(0x3000 := 7)) example2 example_tp"
    unfolding amp_step_t_def
    by (auto simp: changed_frames_def thread_perm_def thread_owns_priv_def owns_priv_def
                   thread_maps_writer_def thread_maps_reader_def
                   example_tp_def example2_def chan01_def core1_res_def example_s0_def)
qed

(* Non-vacuity, end to end: the round-trip theorem's premises hold of a
   concrete run through example_s0 with the sending kernel's copy loop
   interleaved with a real other-thread step, and the receiving kernel's copy
   loop run to completion; its three conclusions consequently hold of this run
   — witnessed, not merely claimed possible. The third is the one to read: the
   receiving application's own buffer ends up holding example_msg at chan01's
   buffer frame, and goes on holding it after the acknowledgement. *)
lemma example_interleaved_round_trip:
  shows "\<exists>sC sD sH :: nat conc_state.
           xchan_send_msg chan01 example_msg
             (abs_mem chan01 sC) (abs_mem chan01 sD) (cs_xm sC) (cs_xm sD)
           \<and> xchan_recv_ack chan01 (cs_xm sD) (cs_xm sH)
           \<and> cs_xm sD = example_xchan0(chan01 \<mapsto> XSendPending)
           \<and> cs_xm sH = example_xchan0
           \<and> (\<forall>f \<in> ch_buffer chan01. cs_recv_val sH f = Some (example_msg f))"
proof -
  define sB where "sB = example_s0\<lparr> cs_mem := (cs_mem example_s0)(0x8000 := 42),
                                    cs_written := {0x8000} \<rparr>"
  define sC where "sC = sB\<lparr> cs_mem := ((cs_mem example_s0)(0x8000 := 42))(0x3000 := 7) \<rparr>"
  define sD where "sD = sC\<lparr> cs_xm := (cs_xm sC)(chan01 \<mapsto> XSendPending),
                            cs_written := {}, cs_shadow := cs_mem sC \<rparr>"
  define sE where "sE = sD\<lparr> cs_recv_pc := RCopy, cs_recv_val := Map.empty \<rparr>"
  define sG where "sG = sE\<lparr> cs_recv_val := (cs_recv_val sE)(0x8000 \<mapsto> cs_mem sE 0x8000) \<rparr>"
  define sH where "sH = sG\<lparr> cs_xm := (cs_xm sG)(chan01 \<mapsto> XIdle), cs_recv_pc := RIdle \<rparr>"

  have wf: "amp_partition_wf example2" by (rule example2_partition_wf)
  have chd: "chan01 \<in> ap_channels example2" by (simp add: example2_def)
  have nemp: "ch_buffer chan01 \<noteq> {}" by (simp add: chan01_def)

  have owr: "cstep example2 chan01 example_tp example_msg example_s0 (COwnerWrite 0x8000) sB"
    using example_owner_write by (simp add: sB_def)
  have oth: "cstep example2 chan01 example_tp example_msg sB (COther 20) sC"
    using example_other_step by (simp add: sB_def sC_def)
  have ws: "csteps example2 chan01 example_tp example_msg
              example_s0 [COwnerWrite 0x8000, COther 20] sC"
    by (rule csteps_cons[OF owr csteps_cons[OF oth csteps_nil]])

  have commit: "cstep example2 chan01 example_tp example_msg sC COwnerCommit sD"
    unfolding sD_def by (rule cstep_owner_commit) (simp add: sC_def sB_def chan01_def)

  have pendD: "cs_xm sD chan01 = Some XSendPending" by (simp add: sD_def)
  have rstart: "cstep example2 chan01 example_tp example_msg sD CRecvStart sE"
    unfolding sE_def
    by (rule cstep_recv_start) (simp_all add: sD_def sC_def sB_def example_s0_def pendD)
  have rcopy: "cstep example2 chan01 example_tp example_msg sE (CRecvCopy 0x8000) sG"
    unfolding sG_def
    by (rule cstep_recv_copy) (simp_all add: sE_def chan01_def)
  have ms: "csteps example2 chan01 example_tp example_msg sD [CRecvStart, CRecvCopy 0x8000] sG"
    by (rule csteps_cons[OF rstart csteps_cons[OF rcopy csteps_nil]])

  have rcommit: "cstep example2 chan01 example_tp example_msg sG CRecvCommit sH"
    unfolding sH_def
    by (rule cstep_recv_commit) (simp_all add: sG_def sE_def chan01_def)

  note main = interleaved_round_trip_refines_protocol
                [OF wf chd nemp example_conc_init ws _ _ commit ms _ rcommit]
  have r: "xchan_send_msg chan01 example_msg
             (abs_mem chan01 sC) (abs_mem chan01 sD) (cs_xm sC) (cs_xm sD)"
      "xchan_recv_ack chan01 (cs_xm sD) (cs_xm sH)"
      "\<forall>f \<in> ch_buffer chan01. cs_recv_val sH f = Some (example_msg f)"
    using main by simp_all

  have xmD: "cs_xm sD = example_xchan0(chan01 \<mapsto> XSendPending)"
    by (simp add: sD_def sC_def sB_def example_s0_def)
  have xmH: "cs_xm sH = example_xchan0"
    by (simp add: sH_def sG_def sE_def sD_def sC_def sB_def example_s0_def
                  example_xchan0_def fun_upd_idem)
  have "xchan_send_msg chan01 example_msg
          (abs_mem chan01 sC) (abs_mem chan01 sD) (cs_xm sC) (cs_xm sD)
        \<and> xchan_recv_ack chan01 (cs_xm sD) (cs_xm sH)
        \<and> cs_xm sD = example_xchan0(chan01 \<mapsto> XSendPending)
        \<and> cs_xm sH = example_xchan0
        \<and> (\<forall>f \<in> ch_buffer chan01. cs_recv_val sH f = Some (example_msg f))"
    using r xmD xmH by simp
  then show ?thesis by blast
qed

end
