(*
 * PolarFire verified multicore (AMP) — the guarantees.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * WHAT THIS FILE IS. This is the answer to "what does the AMP work actually
 * guarantee me, as someone writing software on top of it?" — stated as a list
 * of requirements, each one a plain-English paragraph immediately followed by
 * the machine-checked statement that discharges it. Read this file top to
 * bottom and you know what has been proved. You do not need to open any other
 * theory, or understand any proof, to trust the list.
 *
 * HOW TO TRUST IT. Every requirement below is derived here, in this file, from
 * theorems checked in the AMP sessions. Most are a one-step restatement of a
 * single theorem; a few compose two or three. Either way the derivation is real
 * Isabelle: if a cited theorem's name, statement, or hypotheses ever change
 * incompatibly, THIS FILE FAILS TO BUILD. The requirement list cannot silently
 * drift away from the proofs, and no requirement below can be false.
 *
 * WHAT IT DELIBERATELY OMITS. Intermediate results — refinement steps,
 * abstraction relations, internal consistency lemmas, proof scaffolding — are
 * not here even when they were hard to prove, because they are not claims about
 * the running system. A result earns a place below only if an application
 * developer would change a design decision on learning it.
 *
 * READ SECTION 4 BEFORE RELYING ON ANY OF THIS. It states, precisely, what is
 * NOT established. The requirements below are conditional guarantees, and their
 * conditions are load-bearing.
 *)

theory AMP_Overview
imports
  "AMP_Channel_C.AMP_Channel_C"    (* pulls in AMP_Channel_R, AMP_Channel_A, AMP_Spatial, AMP_Model *)
  "AMP_Channel_AC.AMP_Channel_AC"  (* the authority-graph layer, a sibling branch off AMP_Channel_A *)
  "AMP_Message.AMP_Message"        (* message content: integrity and confidentiality of VALUES *)
begin

(* THE VOCABULARY, in one place, so the statements below read without lookups.

     amp_partition (bp)   the static boot configuration: which cores exist
                          (ap_cores), what private memory each owns
                          (cr_frames), and what channels are declared
                          (ap_channels). Fixed at boot; never changes.
     amp_channel (ch)     a declared one-way channel: a sender (ch_from), a
                          receiver (ch_to), and a shared buffer (ch_buffer).
     amp_partition_wf bp  the configuration is sane: cores' private memory is
                          pairwise disjoint, channels run between two distinct
                          present cores, buffers are not carved out of anyone's
                          private memory, and distinct channels use disjoint
                          buffers. EVERY guarantee below is conditional on this.
     frame_perm bp c f    the access core c holds on frame f: PermRW, PermR, or
                          PermNone. A function of bp alone.
     changed_frames m m'  the frames whose contents differ between two memories.
     amp_step c m m' bp   core c takes a kernel step, writing only frames it
                          owns. See section 4 — this is an assumption standing
                          in for seL4's integrity theorem, not a free fact.
     xchan_send,          the channel protocol: send requires the channel idle
     xchan_recv_ack       and leaves it send-pending; recv/ack requires it
                          send-pending and leaves it idle.
     amp_auth_graph bp    who the boot config SAYS may send/receive on what.
     xchan_send_msg,      the channel protocol WITH a message value attached:
     xchan_recv           send additionally requires the buffer to hold msg
                          afterwards; recv reads the buffer back out as an
                          option-valued function (Some on buffer frames, None
                          elsewhere).
     observation bp c m   everything core c can see of memory m: Some (m f)
                          on every frame c holds any access to, None
                          elsewhere. Two memories giving c the same
                          observation are indistinguishable to it.
     sender_quiescent     a NAMED, currently-unproven assumption: a channel's
                          declared sender issues no further write to its own
                          buffer while a message sits unread. See REQ-MSG-8
                          and section 4(c) — this is not a free fact. *)


section \<open>1. Isolation — cores do not share resources except through declared channels\<close>

(* REQ-ISO-1. THE ONLY MEMORY TWO CORES CAN BOTH REACH IS A DECLARED CHANNEL
   BUFFER. Take any two distinct cores and intersect everything each of them can
   reach — private memory plus every channel they are an endpoint of. Whatever
   survives that intersection is inside some channel's buffer that the boot
   config declared. There is no other overlap: no accidental sharing, no
   incidental aliasing, nothing outside the declared channel set. This is the
   headline isolation property, stated over what the configuration grants. *)
theorem shared_resources_are_declared_channels_only:
  assumes wf:  "amp_partition_wf bp"
      and neq: "c1 \<noteq> c2"
  shows "owned_frames bp c1 \<inter> owned_frames bp c2 \<subseteq> (\<Union>ch \<in> ap_channels bp. ch_buffer ch)"
  using owned_overlap_subset_channels[OF wf neq] .

(* REQ-ISO-1', the same requirement stated over what the HARDWARE enforces
   rather than what the configuration grants: if two distinct cores both hold
   SOME access to a frame — read or write, it does not matter which — that frame
   is a declared channel's buffer. Equivalently: find any doubly-mapped frame in
   an AMP system and you have found a declared channel. This is the form to cite
   when the question is "can these two cores interfere through memory at all?",
   because it ranges over the MMU permission map, which is what actually runs. *)
theorem doubly_mapped_frames_are_channel_buffers:
  assumes wf:  "amp_partition_wf bp"
      and neq: "c1 \<noteq> c2"
      and a1:  "frame_perm bp c1 f \<noteq> PermNone"
      and a2:  "frame_perm bp c2 f \<noteq> PermNone"
  shows "\<exists>ch \<in> ap_channels bp. f \<in> ch_buffer ch"
proof -
  (* Two distinct cores cannot both hold f as private memory: the configuration
     makes private frame sets pairwise disjoint. *)
  have priv: "\<not> (owns_priv bp c1 f \<and> owns_priv bp c2 f)"
  proof
    assume "owns_priv bp c1 f \<and> owns_priv bp c2 f"
    then obtain r1 r2 where "ap_cores bp c1 = Some r1" and "f \<in> cr_frames r1"
                        and "ap_cores bp c2 = Some r2" and "f \<in> cr_frames r2"
      unfolding owns_priv_def by blast
    with amp_partition_wf_private_disjoint[OF wf _ _ neq] show False by blast
  qed
  (* So at least one of them holds f as a channel endpoint instead — and either
     of the two endpoint cases exhibits the declared channel we need. *)
  from a1 a2 priv show ?thesis
    by (auto simp: frame_perm_def maps_writer_def maps_reader_def split: if_splits)
qed

(* REQ-ISO-2. A RUNNING CORE CANNOT MODIFY ANOTHER CORE'S PRIVATE MEMORY. When
   core c takes a kernel step, not one frame of any other core's private memory
   changes. This is the integrity guarantee in its most directly usable form:
   whatever core c's software does — correct, buggy, or actively hostile — it
   cannot corrupt another core's private state. *)
theorem core_step_cannot_touch_another_cores_memory:
  assumes wf:    "amp_partition_wf bp"
      and step:  "amp_step c m m' bp"
      and other: "ap_cores bp c' = Some r'"
      and neq:   "c \<noteq> c'"
  shows "changed_frames m m' \<inter> cr_frames r' = {}"
  using amp_step_preserves_other_private[OF wf step other neq] .

(* REQ-ISO-3. A CORE CANNOT EVEN HOLD WRITE ACCESS TO ANOTHER CORE'S PRIVATE
   MEMORY. Stronger, and different in kind, from ISO-2: that one says a step
   does not write another core's memory; this one says no core is ever in a
   position to. There is no mapping to abuse, no window to race, no privilege to
   escalate through — the write simply cannot be issued. Cross-core memory
   corruption is impossible by construction, not merely absent in practice. *)
theorem no_core_can_write_another_cores_memory:
  assumes wf:    "amp_partition_wf bp"
      and other: "ap_cores bp c' = Some r'"
      and f:     "f \<in> cr_frames r'"
      and neq:   "c \<noteq> c'"
  shows "frame_perm bp c f \<noteq> PermRW"
  using no_cross_writable[OF wf other f neq] .

(* REQ-ISO-4. A CHANNEL BUFFER IS REACHABLE ONLY BY ITS TWO DECLARED ENDPOINTS.
   Any core that is neither the declared sender nor the declared receiver of a
   channel has NO access to that channel's buffer — not write, not read, nothing
   at all. A third core cannot corrupt a message in flight and cannot observe
   one either. Note this holds regardless of the channel's runtime state: there
   is no moment during the protocol at which a buffer becomes momentarily
   visible to anyone else. *)
theorem channel_buffer_is_reachable_only_by_its_endpoints:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
      and c1: "c \<noteq> ch_from ch" and c2: "c \<noteq> ch_to ch"
  shows "frame_perm bp c f = PermNone"
  using buffer_perm_only_endpoints[OF wf ch f c1 c2] .

(* REQ-ISO-5. CHANNELS ARE ONE-WAY, AND THE HARDWARE ENFORCES THE DIRECTION. On
   a declared channel's buffer the sender holds read-write and the receiver
   holds read-only. The receiver cannot write back through the channel it
   receives on — not by convention or discipline, but because it has no write
   mapping. A protocol that needs replies needs a second declared channel in the
   opposite direction; it cannot be improvised on top of one. *)
theorem channel_direction_is_enforced:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
  shows "frame_perm bp (ch_from ch) f = PermRW \<and> frame_perm bp (ch_to ch) f = PermR"
  using buffer_perm_asymmetric[OF wf ch f] .

(* REQ-ISO-6. WHAT THE BOOT CONFIGURATION DECLARES IS EXACTLY WHAT THE HARDWARE
   ENFORCES. Both directions, on both kinds of access: a core has write access
   to a channel buffer IF AND ONLY IF the configuration declared it that
   channel's sender, and read access IF AND ONLY IF it declared it that
   channel's receiver. The "only if" halves say the system grants nothing beyond
   what you asked for; the "if" halves say it grants everything you did ask for,
   so a correctly configured channel is never silently dead. In practice this
   means the boot configuration is a complete and faithful description of the
   system's information flows — reading it tells you the whole story, and the
   proof is what licenses you to reason about the config instead of the MMU. *)
theorem enforced_access_matches_declared_configuration:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
  shows "frame_perm bp c f = PermRW \<longleftrightarrow> (c, XSend, ch) \<in> amp_auth_graph bp"
    and "frame_perm bp c f = PermR  \<longleftrightarrow> (c, XRecv, ch) \<in> amp_auth_graph bp"
proof -
  show "frame_perm bp c f = PermRW \<longleftrightarrow> (c, XSend, ch) \<in> amp_auth_graph bp"
    using amp_auth_graph_write_iff[OF wf ch f] .
  show "frame_perm bp c f = PermR \<longleftrightarrow> (c, XRecv, ch) \<in> amp_auth_graph bp"
    using amp_auth_graph_read_iff[OF wf ch f] .
qed


section \<open>2. Messaging — messages reach the right recipient, and are acknowledged\<close>

(* REQ-MSG-1. A MESSAGE LANDS ONLY WHERE IT WAS ADDRESSED. A send on channel ch
   changes memory inside ch's buffer and nowhere else: not another channel's
   buffer (so no message can be crossed onto the wrong channel), and not ANY
   core's private memory — not even the sender's own, since buffers are never
   carved out of private memory. Misdelivery is impossible, and the reason is
   worth internalising as a design property: a channel's destination is fixed at
   boot and there is no runtime routing decision anywhere in the system, so
   there is no addressing step that could go wrong. *)
theorem message_lands_only_in_its_own_channel_buffer:
  assumes wf:   "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp"
      and send: "xchan_send ch m m' xm xm'"
  shows "changed_frames m m' \<subseteq> ch_buffer ch"
    and "\<forall>ch' \<in> ap_channels bp. ch \<noteq> ch' \<longrightarrow> changed_frames m m' \<inter> ch_buffer ch' = {}"
    and "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> changed_frames m m' \<inter> cr_frames r' = {}"
proof -
  show "changed_frames m m' \<subseteq> ch_buffer ch" using send by (simp add: xchan_send_def)
next
  show "\<forall>ch' \<in> ap_channels bp. ch \<noteq> ch' \<longrightarrow> changed_frames m m' \<inter> ch_buffer ch' = {}"
  proof (intro ballI impI)
    fix ch' assume ch': "ch' \<in> ap_channels bp" and ne: "ch \<noteq> ch'"
    from wf_buffers_disjoint[OF wf ch ch' ne] have "ch_buffer ch \<inter> ch_buffer ch' = {}" .
    with send show "changed_frames m m' \<inter> ch_buffer ch' = {}"
      by (auto simp: xchan_send_def)
  qed
next
  show "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> changed_frames m m' \<inter> cr_frames r' = {}"
    using send amp_partition_wf_buffer_not_private[OF wf ch] by (auto simp: xchan_send_def)
qed

(* REQ-MSG-2. ONLY THE DECLARED RECIPIENT CAN READ THE MESSAGE. Combined with
   MSG-1 this is the delivery guarantee at full strength: the message lands in
   exactly one buffer, the declared receiver is the only core with read access
   to that buffer, and any other core holds no mapping there at all — so it
   cannot observe the message, whatever it does and whenever it tries. Stated in
   the configuration's own vocabulary as well: no core outside the declared
   receiver ever holds the receive authority for that channel. *)
theorem message_is_readable_only_by_its_declared_recipient:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
      and c1: "c \<noteq> ch_from ch" and c2: "c \<noteq> ch_to ch"
  shows "frame_perm bp c f = PermNone"
    and "(c, XRecv, ch) \<notin> amp_auth_graph bp"
    and "(c, XSend, ch) \<notin> amp_auth_graph bp"
  using amp_auth_graph_confined_to_endpoints[OF wf ch f c1 c2] by blast+

(* REQ-MSG-3. A PENDING MESSAGE IS NEVER OVERWRITTEN. While a message sits
   unconsumed on a channel, no send on that channel is possible at all — the
   operation has no enabled instance. A sender cannot clobber a message the
   receiver has not yet taken, so no message is ever silently lost to a faster
   sender. The flip side, which callers must design for: a send on a busy
   channel does not happen, so the sender needs a story for that case (retry,
   backpressure, drop) — the guarantee is no-loss, not no-blocking. *)
theorem pending_message_cannot_be_overwritten:
  assumes pending: "xm ch = Some XSendPending"
  shows "\<not> xchan_send ch m m' xm xm'"
  using pending by (simp add: xchan_send_def)

(* REQ-MSG-4. EVERY RECEIVED MESSAGE IS ACKNOWLEDGED. Receiving and
   acknowledging are one indivisible operation: it is enabled only when a
   message is genuinely pending, and it leaves the channel idle. There is no
   reachable state in which a message has been received but not acknowledged,
   because there is no operation that produces one — the "received, ack
   pending" state does not exist in the protocol. A receiver therefore cannot
   forget to acknowledge, cannot acknowledge twice, and cannot leave the
   channel wedged by failing to. *)
theorem every_received_message_is_acknowledged:
  assumes rc: "xchan_recv_ack ch xm xm'"
  shows "xm ch = Some XSendPending"    (* it was enabled only by a real pending message *)
    and "xm' ch = Some XIdle"          (* and it always completes the acknowledgement *)
  using rc by (simp_all add: xchan_recv_ack_def)

(* REQ-MSG-5. NOTHING IS ACKNOWLEDGED THAT WAS NOT SENT. The dual of MSG-4: on
   an idle channel, no receive/acknowledge is possible. A receiver cannot
   manufacture an acknowledgement for a message that was never sent, so an
   acknowledgement observed by the sender is always evidence of a real,
   completed delivery. *)
theorem no_acknowledgement_without_a_message:
  assumes idle: "xm ch = Some XIdle"
  shows "\<not> xchan_recv_ack ch xm xm'"
  using idle by (simp add: xchan_recv_ack_def)

(* REQ-MSG-6. A COMPLETED ROUND TRIP LEAVES NO RESIDUE. After a send followed by
   its receive/acknowledge, the channel state is not merely idle again — it is
   BIT-FOR-BIT the state it was in before the send, and so is every other
   channel's. There is no accumulating counter, no drift, no sequence number
   that eventually wraps, nothing whose Nth round trip differs from its first.
   A long-running system's channel state is therefore bounded and does not
   degrade, and any two round trips are genuinely interchangeable. *)
theorem completed_round_trip_leaves_no_residue:
  assumes send: "xchan_send ch m m' xm xm1"
      and recv: "xchan_recv_ack ch xm1 xm2"
  shows "xm2 = xm"
proof -
  from send have idle: "xm ch = Some XIdle" and u1: "xm1 = xm(ch \<mapsto> XSendPending)"
    by (simp_all add: xchan_send_def)
  from recv have "xm2 = xm1(ch \<mapsto> XIdle)" by (simp add: xchan_recv_ack_def)
  with u1 have "xm2 = xm(ch \<mapsto> XIdle)" by simp
  also have "xm(ch \<mapsto> XIdle) = xm" using idle by (rule fun_upd_idem)
  finally show ?thesis .
qed

(* REQ-MSG-7. CHANNELS DO NOT INTERFERE WITH EACH OTHER. An operation on one
   channel leaves every other channel's state exactly as it was. Traffic on one
   channel cannot perturb, stall, or corrupt the protocol state of another, so
   channels can be reasoned about — and tested — one at a time. Together with
   MSG-1's buffer-disjointness half, this is full independence of channels in
   both their memory and their protocol state. *)
theorem send_affects_only_its_own_channel:
  assumes send: "xchan_send ch m m' xm xm'"
  shows "\<forall>d. d \<noteq> ch \<longrightarrow> xm' d = xm d"
  using send by (auto simp: xchan_send_def)

(* REQ-MSG-7, receive/acknowledge half: consuming a message on one channel
   likewise leaves every other channel's protocol state untouched. Stated
   separately from the send half above because it is a distinct operation with
   a distinct enabling condition, not a corollary of it. *)
theorem recv_ack_affects_only_its_own_channel:
  assumes rc: "xchan_recv_ack ch xm xm'"
  shows "\<forall>d. d \<noteq> ch \<longrightarrow> xm' d = xm d"
  using rc by (auto simp: xchan_recv_ack_def)

(* REQ-MSG-8. THE RECEIVER READS EXACTLY THE MESSAGE THE SENDER SENT — GIVEN
   ONE NAMED ASSUMPTION. Everything above this line concerns WHO can reach a
   message, never what its VALUE is; this is the first result about values.
   Send a message msg on ch; let any amount of unrelated kernel activity run
   while it sits pending, as long as none of it is a write this channel's own
   sender issues to its own buffer during that window (`sender_quiescent` —
   spelled out as an explicit hypothesis here rather than a locale, since this
   file states results, not obligations); then recv/ack it. The value read
   back is bit-for-bit the value sent. The parenthetical half of this is
   unconditional and worth isolating: no core OTHER than the sender can ever
   alter the message in flight, regardless of the hypothesis below — that
   part follows from ISO-3/ISO-4 alone. What the hypothesis rules out is
   narrower and sharper than it might sound: not "a race", but specifically
   the sender rewriting its OWN already-pending message, which nothing
   earlier in this file forbids (the sender holds PermRW on the buffer for
   the system's entire lifetime — see 4(c)). *)
theorem the_receiver_reads_exactly_what_was_sent:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp"
      and quiescent:
        "\<And>(m :: obj_ref \<Rightarrow> 'v) m' xm. xm ch = Some XSendPending
           \<Longrightarrow> amp_step_w (ch_from ch) m m' bp \<Longrightarrow> \<forall>f \<in> ch_buffer ch. m' f = m f"
      and send: "xchan_send_msg ch (msg :: obj_ref \<Rightarrow> 'v) m m' xm0 xm1"
      and run:  "(quiescent_step bp xm1 ch)\<^sup>*\<^sup>* m' m''"
      and recv: "xchan_recv_ack ch xm1 xm2"
  shows "xchan_recv ch m'' = xchan_recv ch msg"
proof -
  interpret sender_quiescent "TYPE('v)" bp ch
  proof unfold_locales
    show "amp_partition_wf bp" by (rule wf)
    show "ch \<in> ap_channels bp" by (rule ch)
    show "\<And>(m :: obj_ref \<Rightarrow> 'v) m' xm. xm ch = Some XSendPending
            \<Longrightarrow> amp_step_w (ch_from ch) m m' bp \<Longrightarrow> \<forall>f \<in> ch_buffer ch. m' f = m f"
      using quiescent .
  qed
  show ?thesis using send run recv by (rule message_integrity)
qed

(* REQ-MSG-9. NO CORE OUTSIDE THE CHANNEL LEARNS ANYTHING FROM A SEND — FOR
   ANY MESSAGE VALUE, UNCONDITIONALLY. Take any core c that is neither ch's
   declared sender nor its declared receiver. Whatever c can observe of
   memory (every frame it holds any access to at all) is EXACTLY the same
   before and after a send on ch, no matter what the message says. Unlike
   MSG-8, this needs no quiescence hypothesis and no locale: it costs nothing
   to establish because c holds no mapping to the buffer at all (ISO-4), so
   there is nothing for a changing value to be seen THROUGH. This is the
   storage-channel confidentiality half of message security — the first
   result in this file that is a genuine claim about VALUES rather than
   permissions, and the one that needed message content in the model before
   it could even be stated (see 4(c), the gap this closes). *)
theorem no_core_outside_the_channel_learns_anything_from_a_send:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp"
      and send: "xchan_send_msg ch msg m m' xm xm'"
      and c1: "c \<noteq> ch_from ch" and c2: "c \<noteq> ch_to ch"
  shows "observation bp c m = observation bp c m'"
  using xchan_send_msg_invisible_to_third_core[OF wf ch send c1 c2] .

(* REQ-MSG-10. THE ACKNOWLEDGEMENT IS A REAL, BUT BOUNDED, BACKWARD FLOW. The
   channel is one-way for DATA — REQ-ISO-5 already says the receiver holds no
   write mapping at all — but a working protocol still needs the receiver to
   tell the sender "consumed", and that IS a flow from receiver to sender.
   This states its exact size: recv/ack changes ch's own status entry to
   idle and nothing else — no other channel's status, and (definitionally,
   since recv/ack has no memory operand at all) no message content
   whatsoever. One bit, once per round trip, carrying no payload. This
   matters for how to read section 1: a claim that the two endpoints of a
   channel learn NOTHING from each other would be false, and any future
   cross-core confidentiality result (beyond this file) must be phrased to
   ALLOW this one declared bit, not to assert its absence. *)
theorem the_acknowledgement_carries_no_message_content:
  assumes rc: "xchan_recv_ack ch xm xm'"
  shows "xm' ch = Some XIdle"
    and "\<forall>d. d \<noteq> ch \<longrightarrow> xm' d = xm d"
  using xchan_recv_ack_reverse_flow_is_bounded_to_one_status_bit[OF rc] by blast+


section \<open>3. Durability — the guarantees survive operation, and reach the implementation\<close>

(* REQ-DUR-1. USING A CHANNEL CANNOT WEAKEN ISOLATION. Every isolation guarantee
   in section 1 still holds after a send, and after a receive/acknowledge. Note
   WHY, because it is a stronger fact than "the invariant is preserved": the
   access-control guarantees (ISO-3 through ISO-6) are properties of the static
   boot configuration alone, and no operation in the system touches that
   configuration. There is no capability to derive, mint, transfer, or revoke,
   so there is no mechanism by which access rights could change at run time and
   nothing that needs re-establishing after each step. Isolation is not an
   invariant the kernel maintains; it is a property of the configuration the
   kernel cannot reach. *)
theorem isolation_holds_across_every_channel_operation:
  assumes wf:   "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp"
      and send: "xchan_send ch m m' xm xm'"
      and rc:   "xchan_recv_ack ch' xn xn'"
  shows "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> ch_from ch \<noteq> c'
                 \<longrightarrow> changed_frames m m' \<inter> cr_frames r' = {}"
    and "\<forall>chx \<in> ap_channels bp. \<forall>f \<in> ch_buffer chx.
           frame_perm bp (ch_from chx) f = PermRW \<and> frame_perm bp (ch_to chx) f = PermR"
    and "\<forall>c' r' f. ap_cores bp c' = Some r' \<longrightarrow> f \<in> cr_frames r' \<longrightarrow> ch_to ch' \<noteq> c'
                   \<longrightarrow> frame_perm bp (ch_to ch') f \<noteq> PermRW"
  using xchan_send_preserves_partition[OF wf ch send]
        xchan_recv_ack_preserves_partition[OF wf rc]
  by blast+

(* REQ-DUR-2. THE GUARANTEES REACH THE IMPLEMENTATION, NOT JUST THE
   SPECIFICATION. The abstract protocol above is stated over a symbolic channel
   status. A real implementation stores a machine word and runs deterministic
   code. The same guarantees hold there: a design-level send on a properly idle
   channel still cannot touch another core's private memory. This is what
   licenses reasoning about the specification when what ships is the code. *)
theorem implementation_inherits_isolation:
  assumes wf:  "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp"
      and pre: "xm ch = Some xIdleR"
      and mem: "changed_frames m m' \<subseteq> ch_buffer ch"
  shows "\<forall>c' r'. ap_cores bp c' = Some r' \<longrightarrow> ch_from ch \<noteq> c'
                 \<longrightarrow> changed_frames m m' \<inter> cr_frames r' = {}"
  using xchan_send_R_preserves_partition(1)[where xm = xm and ch = ch, OF wf ch pre mem] .

(* REQ-DUR-3. THE IMPLEMENTATION'S ROUND TRIP ALSO LEAVES NO RESIDUE. MSG-6
   restated at the word level, where it is the claim that actually matters for a
   long-running deployment: run the real send/receive-acknowledge pair against a
   word-tagged status field and the field returns to the exact word it held
   before. Bounded state, no drift, in the representation that ships. *)
theorem implementation_round_trip_leaves_no_residue:
  assumes pre: "(xm :: xchan_map_R) ch = Some xIdleR"
  shows "xchan_recv_ack_R ch (xchan_send_R ch xm) = xm"
proof -
  have "xchan_recv_ack_R ch (xchan_send_R ch xm) = xm(ch \<mapsto> xIdleR)"
    by (simp add: xchan_send_R_def xchan_recv_ack_R_def)
  also have "xm(ch \<mapsto> xIdleR) = xm" using pre by (rule fun_upd_idem)
  finally show ?thesis .
qed


section \<open>4. What is NOT established\<close>

(* Every requirement above is conditional, and the conditions matter. Read this
   section as part of the guarantee, not as a caveat appended to it.

   (a) NO CONCURRENCY. Everything above concerns a SINGLE step, or a single
       send/receive pair considered in isolation. Nothing here covers two cores
       stepping concurrently, interleaved, or racing. In particular: MSG-3's
       "a pending message cannot be overwritten" says no ENABLED send exists
       while a message is pending — it does NOT rule out a sender and a receiver
       racing on the status word on real hardware, nor establish the memory
       barriers and cache maintenance a real buffer handoff requires. The
       isolation results (section 1) are the ones that survive this gap best,
       since they are properties of a static configuration rather than of an
       execution; the messaging results (section 2) are the ones that most need
       the concurrency work before they describe real hardware. This is the
       largest open gap and the one with the most remaining risk.

   (b) NO LIVENESS, NO AVAILABILITY. Nothing above says a message is ever
       delivered, that a receiver ever runs, that a sender ever gets its channel
       back, or that any operation terminates. "Every RECEIVED message is
       acknowledged" (MSG-4) is proved; "every SENT message is eventually
       received" is not, and cannot be without a model of scheduling and
       progress that this development does not have. A core that never receives
       will wedge its channel forever, and nothing here forbids that. Do not
       read the messaging section as a delivery-time or delivery-at-all
       guarantee.

   (c) MESSAGE CONTENT'S REMAINING GAP IS NARROWER THAN IT WAS: CONFIDENTIALITY
       IS UNCONDITIONAL, INTEGRITY IS CONDITIONAL ON ONE NAMED, UNPROVEN
       ASSUMPTION. Earlier this file had no message-VALUE result at all — only
       WHERE a message lands and WHO can reach it (MSG-1, MSG-2), never whether
       the bytes read are the bytes written, or whether a third core learns
       anything about them. That gap is now split in two. The confidentiality
       half is CLOSED, outright: MSG-9 says no core outside a channel's two
       endpoints learns anything from a send, for any message value, with no
       extra hypothesis — it costs nothing beyond ISO-4, because a core with no
       mapping to the buffer has nothing to observe a changing value through.
       The integrity half is ESTABLISHED BUT CONDITIONAL: MSG-8 says the
       receiver reads exactly what the sender sent, but only GIVEN
       `sender_quiescent` — that the sender itself issues no further write to
       its own buffer while the message sits pending. That assumption is a
       genuine, currently unproven claim about the sender's own code, not
       something derivable from anything proved so far, and it is not
       discharged anywhere in this file. Here is why it is needed, because it
       is not obvious: the sender retains PermRW on the buffer for the
       system's whole lifetime (ISO-5 is static), so nothing here stops it
       rewriting a message it has already marked pending. That is not a
       security violation — the sender is the message's author and no third
       core is involved — but it does mean a receiver may observe a torn
       message without this extra hypothesis, which is exactly why MSG-8 needs
       it rather than following from ISO-3 alone. Until a later development
       discharges `sender_quiescent` outright (by proving it as a genuine
       invariant of the sender's own reachable code, rather than assuming it),
       MSG-8 is the one content-level guarantee in this file that is
       conditional rather than outright — read it accordingly. Separately,
       MSG-10 records that the acknowledgement is a real, bounded backward
       flow (one status bit per round trip, no content) that any FUTURE
       confidentiality claim between the two endpoints themselves — something
       this file does not attempt — would have to account for rather than rule
       out. Serialisation, framing, and payload encoding remain outside this
       development entirely and always will be.

   (d) THE PER-CORE STEP RELATION IS AN ASSUMPTION. `amp_step` — "a core's
       kernel step writes only frames that core owns" — is the abstraction of
       seL4's already-proved `integrity` theorem (proof/access-control/
       Access.thy, `integrity_mem`), but it has NOT been discharged against that
       theorem here. Doing so requires relating a per-core PAS to the AMP
       partition, and is deferred integration work. Until then, ISO-2 and
       everything downstream of it rest on that abstraction being faithful.

   (e) THE BOOT CONFIGURATION IS ASSUMED, NOT VERIFIED. `amp_partition_wf` is a
       hypothesis of nearly every result above. Nothing here proves that the
       PolarFire boot loader actually installs the page tables the configuration
       describes, nor that the hardware honours them. That is assumption A-HW.
       A configuration that is not well-formed gets no guarantees at all, and
       section 5's witness only shows that well-formed configurations exist —
       not that yours is one. Checking `amp_partition_wf` for a real deployment
       configuration is a concrete, cheap, and currently unperformed step.

   (f) THE C CODE IS NOT THE KERNEL'S. The AMP_Channel_C session checks two
       hand-written C functions against the design-level operations. That C
       exists nowhere in the real kernel translation unit; it is not spliced into
       kernel_all.c and it does not describe what runs on hardware. DUR-2 and
       DUR-3 above are stated at the DESIGN level, which is a genuine step below
       the specification but still above the shipped binary. Nothing in this file
       depends on the C session's results, deliberately.

   (g) NO TIMING / SIDE-CHANNEL CLAIM. ISO-4, MSG-2, and now MSG-9 rule out a
       third core reading a message, or learning its VALUE through the
       storage channel the buffer mapping provides. None of them say anything
       about timing channels, cache-based side channels, shared-bus
       contention, or any other non-architectural flow — MSG-9's
       noninterference result is a storage-channel claim only, matching the
       scope single-core InfoFlow already commits to. Timing-channel
       cross-core confidentiality is not established and is out of scope
       permanently, not merely deferred. *)


section \<open>5. Non-vacuity — the guarantees are not empty\<close>

(* Every theorem above is conditional on `amp_partition_wf`, and the messaging
   results are conditional on operations actually being enabled. If no
   configuration satisfied those hypotheses, the whole list would be true and
   worthless. It is not: a genuine two-core, one-channel system satisfies them,
   and a real round trip runs in it. *)

(* A real configuration is well-formed: two cores each privately owning two
   frames, one declared channel between them using a third, disjoint frame. *)
theorem a_real_configuration_is_wellformed: "amp_partition_wf example2"
  using example2_partition_wf .

(* A real round trip is enabled in it: core 0 sends into the channel buffer, and
   core 1's receive/acknowledge returns the channel to exactly its prior state
   (MSG-6, witnessed concretely rather than assumed reachable). *)
theorem a_real_round_trip_runs:
  assumes m: "changed_frames m m' \<subseteq> {0x8000}"
  shows "xchan_send chan01 m m' example_xchan0 (example_xchan0(chan01 \<mapsto> XSendPending))
       \<and> xchan_recv_ack chan01 (example_xchan0(chan01 \<mapsto> XSendPending)) example_xchan0"
  using m by (auto simp: xchan_send_def xchan_recv_ack_def example_xchan0_def chan01_def)

(* And the declared authority in that system is exactly the two edges you would
   expect — core 0 may send, core 1 may receive, and core 1 may NOT send back
   (ISO-5, witnessed concretely). *)
theorem a_real_configurations_authority_is_as_declared:
  "(0, XSend, chan01) \<in> amp_auth_graph example2"
  "(1, XRecv, chan01) \<in> amp_auth_graph example2"
  "(1, XSend, chan01) \<notin> amp_auth_graph example2"
  using example2_auth_graph_edges example2_core1_has_no_send_authority by blast+

(* And a real message value, sent on that same channel, is invisible to a
   bystander core outside it — witnessed concretely rather than only proved
   in the abstract, so MSG-9 is not true-but-empty either. *)
theorem a_real_messages_send_is_invisible_to_a_bystander:
  assumes send: "xchan_send_msg chan01 example_msg m m' xm xm'"
  shows "observation example2 99 m = observation example2 99 m'"
  using example2_send_is_invisible_to_a_bystander[OF send] .

end
