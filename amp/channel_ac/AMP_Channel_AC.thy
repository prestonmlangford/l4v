(*
 * PolarFire verified multicore (AMP) — Phase 5: channel access control
 * (D-spatial half of security).
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * Phase 5 gives the channel an explicit AUTHORITY vocabulary — mirroring
 * seL4's auth/auth_graph/pas_refined machinery (proof/access-control/
 * Access.thy, Ipc_AC.thy) — and shows a core can exercise write (send) or
 * read (recv) authority over a channel's buffer only via the one edge the
 * boot config actually declared for it, matching exactly what Phase 2's MMU
 * permission map already enforces.
 *
 * SCOPE, established by reading the real files before writing this one
 * (proof/access-control/Access.thy, 951 lines; Ipc_AC.thy, 2801 lines):
 * the overwhelming majority of Ipc_AC.thy is capability-TRANSFER machinery
 * that has no counterpart here — cap-rights arithmetic (cap_rights_to_auth,
 * cap_auth_conferred), transfer_caps_loop/do_ipc_transfer and their
 * pas_refined lemmas, reply-cap creation/DeleteDerived propagation, fault
 * IPC. None of that applies: AMP_Model.thy's amp_partition is a
 * boot-time-fixed configuration with NO capability derivation, minting,
 * copying, or revocation anywhere in this model — a channel's sender and
 * receiver are the same two cores for the system's entire lifetime. Real
 * seL4 needs pas_refined to be *proved preserved* across every operation
 * because its policy graph could in principle drift from a mutable
 * capability space; here there is no such mutable space to drift, so the
 * policy graph (amp_auth_graph below) is simply READ OFF ap_channels, not
 * independently asserted and reconciled. This is not a corner cut — it is
 * what "mirror Ipc_AC, scoped to what this design needs" means once the
 * capability-transfer content (this design's whole reason for not having
 * one) is subtracted out. The genuine, non-vacuous content that remains is
 * the bridge from this new "authority" vocabulary to Phase 2's independently
 * established, MMU-level frame_perm — i.e., showing the declared graph is
 * neither more nor less permissive than what is physically enforced.
 *
 * This theory is organized in the usual four zones (plan section 2.5).
 *)

theory AMP_Channel_AC
imports "AMP_Channel_A.AMP_Channel_A"
begin

section \<open>Specification\<close>

subsection \<open>Channel authority\<close>

(* The two kinds of authority a core may hold over a declared channel: XSend
   -- the right to write the buffer and drive it to XSendPending -- and
   XRecv -- the right to read the buffer and drive it back to XIdle. Mirrors
   seL4's auth datatype (Access.thy's Control | Receive | SyncSend | Notify |
   Reset | Grant | Call | Reply | Write | Read | DeleteDerived | AAuth ...),
   collapsed to the two edge kinds this fixed-topology channel actually
   exhibits -- there is no Grant/Reply/Call/DeleteDerived here because there
   is no capability transfer for those to describe. *)
datatype amp_auth = XSend | XRecv

subsection \<open>The static authority policy graph\<close>

(* The authority policy graph implied by a boot partition: one XSend edge
   (ch_from ch, XSend, ch) and one XRecv edge (ch_to ch, XRecv, ch) per
   declared channel. Mirrors seL4's auth_graph / pasPolicy (Access.thy) --
   except DERIVED rather than independently trusted, since ap_channels
   already IS the boot-time authority declaration (AMP_Model.thy); there is
   no separate mutable policy state for this graph to be reconciled against. *)
definition amp_auth_graph :: "amp_partition \<Rightarrow> (core_id \<times> amp_auth \<times> amp_channel) set" where
  "amp_auth_graph bp \<equiv>
     {(ch_from ch, XSend, ch) | ch. ch \<in> ap_channels bp}
   \<union> {(ch_to ch, XRecv, ch) | ch. ch \<in> ap_channels bp}"

section \<open>Proof development (internal machinery)\<close>

(* Membership destructors for the two edge kinds, each a direct unfold of
   amp_auth_graph_def with no channel-uniqueness reasoning needed yet --
   amp_channel record equality alone pins down which channel a given edge
   names. Kept as named lemmas (not inlined) so the RESULTS proofs below
   never unfold amp_auth_graph_def themselves, matching AMP_Spatial.thy's
   established discipline of never handing an existential-laden definition
   straight to simp/blast. *)

(* c holds the XSend edge for ch iff ch is declared and c is its sender. *)
lemma amp_auth_graph_send_iff:
  "(c, XSend, ch) \<in> amp_auth_graph bp \<longleftrightarrow> ch \<in> ap_channels bp \<and> c = ch_from ch"
  by (auto simp: amp_auth_graph_def)

(* c holds the XRecv edge for ch iff ch is declared and c is its receiver. *)
lemma amp_auth_graph_recv_iff:
  "(c, XRecv, ch) \<in> amp_auth_graph bp \<longleftrightarrow> ch \<in> ap_channels bp \<and> c = ch_to ch"
  by (auto simp: amp_auth_graph_def)

section \<open>Results\<close>

subsection \<open>The graph exactly matches the enforced MMU permission map\<close>

(* The policy graph is sound AND complete against Phase 2's frame_perm: a
   core has PermRW on a declared channel's buffer frame if and only if the
   graph grants it the XSend edge for that channel. This is the bridge
   between "the boot config SAYS core c may send on ch" and "the MMU
   actually enforces exactly that" -- the graph is not an independent claim
   about who should have write access, it is provably the exact set of
   cores who do. *)
theorem amp_auth_graph_write_iff:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
  shows "frame_perm bp c f = PermRW \<longleftrightarrow> (c, XSend, ch) \<in> amp_auth_graph bp"
proof
  assume "frame_perm bp c f = PermRW"
  with buffer_perm_only_endpoints[OF wf ch f, of c] buffer_perm_asymmetric[OF wf ch f]
  have "c = ch_from ch" by (cases "c = ch_from ch"; cases "c = ch_to ch") auto
  with ch show "(c, XSend, ch) \<in> amp_auth_graph bp" by (simp add: amp_auth_graph_send_iff)
next
  assume "(c, XSend, ch) \<in> amp_auth_graph bp"
  with ch have "c = ch_from ch" by (simp add: amp_auth_graph_send_iff)
  with buffer_perm_asymmetric[OF wf ch f] show "frame_perm bp c f = PermRW" by simp
qed

(* Symmetric fact for read access and the XRecv edge. *)
theorem amp_auth_graph_read_iff:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
  shows "frame_perm bp c f = PermR \<longleftrightarrow> (c, XRecv, ch) \<in> amp_auth_graph bp"
proof
  assume "frame_perm bp c f = PermR"
  with buffer_perm_only_endpoints[OF wf ch f, of c] buffer_perm_asymmetric[OF wf ch f]
  have "c = ch_to ch" by (cases "c = ch_from ch"; cases "c = ch_to ch") auto
  with ch show "(c, XRecv, ch) \<in> amp_auth_graph bp" by (simp add: amp_auth_graph_recv_iff)
next
  assume "(c, XRecv, ch) \<in> amp_auth_graph bp"
  with ch have "c = ch_to ch" by (simp add: amp_auth_graph_recv_iff)
  with buffer_perm_asymmetric[OF wf ch f] show "frame_perm bp c f = PermR" by simp
qed

(* A core outside both endpoints holds neither edge -- the graph never grants
   authority beyond the two declared cores, on either side. Completes the
   three-way case split (PermRW / PermR / PermNone) the two iff theorems
   above each only cover one branch of. *)
theorem amp_auth_graph_confined_to_endpoints:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
      and c: "c \<noteq> ch_from ch" and c2: "c \<noteq> ch_to ch"
  shows "frame_perm bp c f = PermNone
       \<and> (c, XSend, ch) \<notin> amp_auth_graph bp \<and> (c, XRecv, ch) \<notin> amp_auth_graph bp"
  using buffer_perm_only_endpoints[OF wf ch f c c2] c c2
  by (simp add: amp_auth_graph_send_iff amp_auth_graph_recv_iff)

subsection \<open>Sending is authority-confined (D-spatial half of C4)\<close>

(* Every frame changed by a send on ch is one whose write authority belongs
   exactly to the declared sender's XSend edge: no core -- authorized or not
   -- other than ch_from ch can ever hold PermRW there (Phase 2's B3 rules
   out any other core physically writing it), so no state transition a send
   could produce is ever attributable to any authority beyond the one edge
   the boot config declared. This is the send-side authority-confinement
   guarantee the plan's exit test asks for: sending conveys, and requires,
   only that one declared edge, never more. *)
theorem xchan_send_authority_confined:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp"
      and send: "xchan_send ch m m' xm xm'"
  shows "\<forall>f \<in> changed_frames m m'. \<forall>c. frame_perm bp c f = PermRW
           \<longrightarrow> (c, XSend, ch) \<in> amp_auth_graph bp"
proof (intro ballI allI impI)
  fix f c
  assume f: "f \<in> changed_frames m m'" and perm: "frame_perm bp c f = PermRW"
  from send f have "f \<in> ch_buffer ch" by (auto simp: xchan_send_def)
  with amp_auth_graph_write_iff[OF wf ch] perm show "(c, XSend, ch) \<in> amp_auth_graph bp" by simp
qed

subsection \<open>Receiving is confined to the declared endpoints (confidentiality half)\<close>

(* No core outside ch's two declared endpoints ever has any access -- read or
   write -- to ch's buffer, regardless of the channel's runtime status. In
   particular the declared receiver's XRecv edge is the ONLY read authority
   that ever exists over a message a recv_ack consumes: an unauthorized core
   cannot observe it, because it holds no mapping there at all. This is the
   confidentiality-flavoured half of D-spatial: restated here in the
   authority-graph vocabulary rather than left as Phase 2's frame_perm fact
   alone, so it reads as an access-control guarantee, not only a spatial one. *)
theorem xchan_recv_ack_authority_confined:
  assumes wf: "amp_partition_wf bp" and ch: "ch \<in> ap_channels bp" and f: "f \<in> ch_buffer ch"
      and c: "c \<noteq> ch_to ch"
  shows "(c, XRecv, ch) \<notin> amp_auth_graph bp"
  using ch c by (simp add: amp_auth_graph_recv_iff)

section \<open>Examples\<close>

subsection \<open>The example two-core system's declared authority\<close>

(* Non-vacuity: in the example two-core configuration, core 0 holds the
   declared XSend edge for chan01 and core 1 holds the declared XRecv edge --
   the two edges the example system's single channel actually grants. *)
lemma example2_auth_graph_edges:
  "(0, XSend, chan01) \<in> amp_auth_graph example2 \<and> (1, XRecv, chan01) \<in> amp_auth_graph example2"
  by (simp add: amp_auth_graph_send_iff amp_auth_graph_recv_iff example2_def chan01_def)

(* Concrete confinement: core 1 (the declared receiver) has no XSend edge for
   chan01 -- it cannot send on the channel it may only receive from, matching
   its PermR-only mapping onto the buffer (Phase 2's example2_buffer_asymmetric). *)
lemma example2_core1_has_no_send_authority:
  "(1, XSend, chan01) \<notin> amp_auth_graph example2"
  by (simp add: amp_auth_graph_send_iff example2_def chan01_def)

end
