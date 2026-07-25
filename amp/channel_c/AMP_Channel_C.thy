(*
 * PolarFire verified multicore (AMP) -- Phase 4: channel refinement, C level
 * (the "C half" -- mirrors Ipc_C).
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * Phase 4's R half gave the channel design-level (word-tagged, deterministic
 * function) semantics, xchan_send_R / xchan_recv_ack_R, refining Phase 3's
 * abstract relations. This theory adds the C level: two minimal, hand-written
 * C functions (amp/channel_c/xchan.c) that write the same idle/send-pending
 * tag convention directly to memory, proven -- via AutoCorres, not full
 * ccorres/Simpl CRefine -- to correctly implement xchan_send_R /
 * xchan_recv_ack_R.
 *
 * SCOPE AND WHY AUTOCORRES, NOT CREFINE. Real CRefine (proof/crefine/RISCV64/
 * Ipc_C.thy, the ccorres framework) proves properties of C functions that
 * already exist inside seL4's single combined kernel_all.c translation unit
 * -- every ccorres lemma is stated against procedures pulled out of ONE
 * global Simpl environment built by parsing the whole kernel
 * (spec/cspec/RISCV64/Kernel_C.thy). The channel's C code is brand new: it
 * exists nowhere in kernel_all.c, so there is nothing there yet to write
 * ccorres lemmas against, and pulling in the full CRefine dependency chain
 * (CSpec/CBaseRefine/Refine/AInvs/...) would mean rebuilding hours of
 * unrelated proof just for two four-line functions. AutoCorres parses a
 * SEPARATE, standalone .c file into its own isolated environment and lifts
 * it directly to a monadic Isabelle spec -- exactly the tool the l4v tree
 * itself uses for small hand-written C snippets
 * (tools/autocorres/tests/examples/). When (if) this code is eventually
 * spliced into the real kernel_all.c, the proof obligation shifts to a
 * genuine ccorres lemma against that Gamma; nothing here substitutes for
 * that future step, it only establishes functional correctness of the C now,
 * at the cost this phase can actually afford.
 *
 * Buffer CONTENTS remain unmodelled, exactly as every earlier phase left
 * them -- this theory is about the status-word transition only. The memory
 * fence a real cross-core implementation needs around this store is a
 * Phase 6 concern (see xchan.c's header and ../../multicore-amp-plan.md).
 *
 * This theory is organized in the usual four zones (plan section 2.5):
 * SPECIFICATION, PROOF DEVELOPMENT, RESULTS, EXAMPLES.
 *)

theory AMP_Channel_C
imports
  "AMP_Channel_R.AMP_Channel_R"
  "AutoCorres.AutoCorres"
begin

section \<open>Specification\<close>

external_file "xchan.c"
install_C_file "xchan.c"
autocorres "xchan.c"

context xchan begin

(* xchan_c_represents: a 32-bit C memory word REPRESENTS a design-level
   status tag exactly when the two agree on idle-vs-pending -- the same
   0-means-idle/nonzero-means-pending convention xchan_status_R already uses
   (AMP_Channel_R.thy), just now on the concrete side too. Phrased as an
   agreement-on-classification predicate, not a type/value equality, because
   the C word (32-bit `unsigned`) and xchan_status_R (a full machine_word)
   need not even be the same bit-width for this phase's purposes -- only the
   idle/pending boolean the R level actually reads has to match, exactly
   what xchan_status_abs itself already reduces the word down to one level
   up. *)
definition xchan_c_represents :: "32 word \<Rightarrow> xchan_status_R \<Rightarrow> bool" where
  "xchan_c_represents cv rv \<equiv> (cv = 0) \<longleftrightarrow> (rv = xIdleR)"

section \<open>Proof development (internal machinery)\<close>

(* The concrete zero word represents xIdleR -- routine unfolding, stated once
   so the Results section below doesn't repeat it. *)
lemma xchan_c_represents_idle: "xchan_c_represents 0 xIdleR"
  by (simp add: xchan_c_represents_def)

(* Any nonzero concrete word represents xSendPendingR -- the symmetric
   unfolding for the pending tag. *)
lemma xchan_c_represents_pending:
  "cv \<noteq> 0 \<Longrightarrow> xchan_c_represents cv xSendPendingR"
  by (simp add: xchan_c_represents_def xIdleR_def xSendPendingR_def)

section \<open>Results\<close>

subsection \<open>The C send refines the design-level send\<close>

(* xchan_send_c_refines_R: running the C send on a validly-allocated status
   word always leaves it representing xSendPendingR -- exactly the tag
   xchan_send_R (AMP_Channel_R.thy) writes for its channel, regardless of
   what the word represented beforehand. This is the C-level counterpart of
   xchan_send_R_corres: every C-level send, read through
   xchan_c_represents, is a genuine design-level send outcome. *)
theorem xchan_send_c_refines_R:
  "\<lbrace>\<lambda>s. is_valid_w32 s p\<rbrace>
     xchan_send_c' p
   \<lbrace>\<lambda>_ s. xchan_c_represents (heap_w32 s p) xSendPendingR\<rbrace>!"
  apply (unfold xchan_send_c'_def)
  apply wp
  apply (auto simp: xchan_c_represents_def xIdleR_def xSendPendingR_def)
  done

subsection \<open>The C recv/ack refines the design-level recv/ack\<close>

(* xchan_recv_ack_c_refines_R: symmetric to the send result -- running the C
   recv/ack always leaves the status word representing xIdleR, exactly the
   tag xchan_recv_ack_R writes. *)
theorem xchan_recv_ack_c_refines_R:
  "\<lbrace>\<lambda>s. is_valid_w32 s p\<rbrace>
     xchan_recv_ack_c' p
   \<lbrace>\<lambda>_ s. xchan_c_represents (heap_w32 s p) xIdleR\<rbrace>!"
  apply (unfold xchan_recv_ack_c'_def)
  apply wp
  apply (auto simp: xchan_c_represents_def)
  done

section \<open>Examples\<close>

(* Non-vacuity: a status word already representing send-pending, after
   running the C recv/ack, represents idle -- a concrete round trip at the
   C level, the same sanity check every earlier phase's Examples zone ends
   with. *)
lemma xchan_recv_ack_c_example:
  "\<lbrace>\<lambda>s. is_valid_w32 s p \<and> heap_w32 s p = 7\<rbrace>
     xchan_recv_ack_c' p
   \<lbrace>\<lambda>_ s. heap_w32 s p = 0\<rbrace>!"
  apply (unfold xchan_recv_ack_c'_def)
  apply wp
  apply auto
  done

end

end
