(*
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Architecture-specific lemmas constraining Kernel_Config definitions *)

theory Arch_Kernel_Config_Lemmas
imports
  Kernel_Config_Lemmas
  Platform
begin

context Arch begin global_naming RISCV64

lemma pptrBase_kernelELFBase:
  "pptrBase < kernelELFBase"
  by (simp add: pptrBase_def canonical_bit_def kernelELFBase_def kernelELFPAddrBase_def pptrTop_def
                Kernel_Config.physBase_def mask_def)

(* 12 in this lemma and below is pageBits, which is not yet defined in this theory.
   Definition will be folded and the lemmas shadowed in AInvs. *)
lemma is_page_aligned_physBase:
  "is_aligned physBase 12"
  by (simp add: Kernel_Config.physBase_def is_aligned_def)

(* 22 is kernel_window_bits, defined in Init_A. To be folded in AInvs. *)
lemma kernel_window_sufficient:
  "pptrBase + (1 << 22) \<le> kernelELFBase"
  unfolding pptrBase_def canonical_bit_def kernelELFBase_def kernelELFPAddrBase_def pptrTop_def
  by (simp add: mask_def Kernel_Config.physBase_def)

lemma kernel_elf_window_at_least_page:
  "kernelELFBase + 2 ^ 12 \<le> kdevBase"
  unfolding kernelELFBase_def kernelELFPAddrBase_def kdevBase_def pptrTop_def
  by (simp add: mask_def Kernel_Config.physBase_def)

(* This doesn't follow from alignment, because we need <, not \<le> *)
lemma kernelELFBase_no_overflow:
  "kernelELFBase < kernelELFBase + 2 ^ 12"
  unfolding kernelELFBase_def kernelELFPAddrBase_def pptrTop_def
  by (simp add: mask_def Kernel_Config.physBase_def)

(* maxIRQ conditions.
   Ported from AARCH64/Arch_Kernel_Config_Lemmas.thy so that RISCV64 proofs can reason about
   maxIRQ generically (via Kernel_Config) rather than assuming a single platform's numeral.
   Needed once Platform.maxIRQ is defined as Kernel_Config.maxIRQ instead of a literal. *)

lemma maxIRQ_less_2p_irqBits:
  "(Kernel_Config.maxIRQ::nat) < 2^irqBits"
  by (simp add: Kernel_Config.maxIRQ_def Kernel_Config.irqBits_def)

(* follows from value_type definition of irq_len *)
lemma LENGTH_irq_len_irqBits[simp]: (* [simp] will fire only for simp del: len_of_numeral_defs *)
  "LENGTH(irq_len) = irqBits"
  using irq_len_def irq_len_val
  by simp

(* The largest IRQ number fits in the irq word type: as a natural number, maxIRQ is
   strictly below 2^LENGTH(irq_len). This restates maxIRQ_less_2p_irqBits in terms of the
   word length rather than irqBits, which is the form the word-level rules below need. On
   PolarFire it amounts to 187 < 2^8 = 256. The `simp del: len_of_numeral_defs` keeps
   LENGTH(irq_len) folded so that the LENGTH_irq_len_irqBits rewrite can fire. *)
lemma maxIRQ_less_2p_irq_len:
  "(Kernel_Config.maxIRQ::nat) < 2^LENGTH(irq_len)"
  using maxIRQ_less_2p_irqBits
  by (simp del: len_of_numeral_defs)

(* maxIRQ as a generic numeral allows us to write rules about casts/unat/uint etc without
   mentioning numbers: *)

lemma of_nat_maxIRQ[simp]:
  "of_nat Kernel_Config.maxIRQ = (Kernel_Config.maxIRQ::'a::len word)"
  by (simp add: Kernel_Config.maxIRQ_def)

(* The integer-literal companion to of_nat_maxIRQ: injecting maxIRQ from int into any word
   type yields the maxIRQ numeral at that type. Holds at every word length. Together the
   two rules let later proofs rewrite casts of maxIRQ without ever mentioning the concrete
   number, which is exactly what makes the IRQ proofs platform-independent. *)
lemma of_int_maxIRQ[simp]:
  "of_int Kernel_Config.maxIRQ = (Kernel_Config.maxIRQ::'a::len word)"
  by (simp add: Kernel_Config.maxIRQ_def)

(* Safe for [simp] because we don't use maxIRQ at lower than irq_len *)
lemma unat_maxIRQ[simp]:
  "LENGTH(irq_len) \<le> LENGTH('a::len) \<Longrightarrow> unat (Kernel_Config.maxIRQ::'a word) = Kernel_Config.maxIRQ"
  by (metis maxIRQ_less_2p_irq_len Word.of_nat_unat of_nat_inverse of_nat_maxIRQ unat_ucast_up_simp)

(* Safe for [simp] because we don't use maxIRQ at lower than irq_len *)
lemma uint_maxIRQ[simp]:
  "LENGTH(irq_len) \<le> LENGTH('a::len) \<Longrightarrow> uint (Kernel_Config.maxIRQ::'a word) = Kernel_Config.maxIRQ"
  by (metis Kernel_Config.maxIRQ_def of_nat_numeral uint_nat unat_maxIRQ)

(* Safe for [simp] because we don't use maxIRQ at lower than irq_len *)
lemma ucast_maxIRQ[simp]:
  "\<lbrakk> LENGTH(irq_len) \<le> LENGTH('a::len); LENGTH(irq_len) \<le> LENGTH('b::len) \<rbrakk> \<Longrightarrow>
   UCAST ('a \<rightarrow> 'b) Kernel_Config.maxIRQ = Kernel_Config.maxIRQ"
  by (metis of_nat_maxIRQ ucast_nat_def unat_maxIRQ)

(* Safe for [simp] because we don't cast down from irq type *)
lemma maxIRQ_less_upcast[simp]:
  "LENGTH(irq_len) \<le> LENGTH('a::len) \<Longrightarrow>
   (Kernel_Config.maxIRQ < (ucast irq :: 'a word)) = (Kernel_Config.maxIRQ < irq)" for irq::irq
  by (simp add: word_less_nat_alt unat_ucast_up_simp)

(* Safe for [simp] because we don't cast down from irq type *)
lemma maxIRQ_le_upcast[simp]:
  "LENGTH(irq_len) \<le> LENGTH('a::len) \<Longrightarrow>
   ((ucast irq :: 'a word) \<le> Kernel_Config.maxIRQ) = (irq \<le> Kernel_Config.maxIRQ)" for irq::irq
  by (simp add: word_le_nat_alt unat_ucast_up_simp)

(* The following are instances -- for some we could derive general rules, but the number of
   instances is limited and the concrete proofs are much simpler: *)

lemma le_maxIRQ_machine_less_irqBits_val[simplified]:
  "w \<le> Kernel_Config.maxIRQ \<Longrightarrow> unat w < 2^LENGTH(irq_len)" for w::machine_word
  using maxIRQ_less_2p_irq_len
  by (simp add: word_le_nat_alt)

(* Narrowing a bounded IRQ is safe: if a machine-word IRQ is within maxIRQ, casting it
   down to the narrower irq type leaves it within maxIRQ. The hypothesis is what makes
   the downcast lossless -- without the bound, ucast could wrap and produce a small value
   that still satisfies the conclusion vacuously. Needed wherever the kernel accepts an
   IRQ number as a machine word (e.g. a syscall argument) and stores it at the irq type. *)
lemma irq_machine_le_maxIRQ_irq:
  "irq \<le> Kernel_Config.maxIRQ \<Longrightarrow> (ucast irq::irq) \<le> Kernel_Config.maxIRQ" for irq::machine_word
  by (simp add: Kernel_Config.maxIRQ_def word_le_nat_alt unat_ucast)

(* Bridges the C representation of an IRQ to the abstract one: maxIRQ equals the upcast of
   an irq value into the 32-bit signed word that the C code uses exactly when that value's
   unsigned interpretation is maxIRQ. The upcast is lossless because irq_len is well below
   32, which is what lets uint_arith discharge the goal. Used in CRefine, where IRQ numbers
   appear as signed 32-bit C ints. *)
lemma maxIRQ_eq_ucast_irq_32_signed_uint:
  "(Kernel_Config.maxIRQ = (ucast b :: 32 signed word)) = (uint b = Kernel_Config.maxIRQ)" for b::irq
  unfolding Kernel_Config.maxIRQ_def
  apply uint_arith
  apply (simp add: uint_up_ucast is_up)
  done

(* Reading maxIRQ back out of a 32-bit signed C word returns maxIRQ unchanged: the signed
   interpretation coincides with the numeral because maxIRQ is far below 2^31, so the sign
   bit is never set and no negative wrap-around is possible. Marked [simp] because this is
   always the direction the C proofs want. *)
lemma sint_maxIRQ_32[simp]:
  "sint (Kernel_Config.maxIRQ :: 32 signed word) = Kernel_Config.maxIRQ"
  by (simp add: Kernel_Config.maxIRQ_def)

(* Sign-casting maxIRQ up from the 32-bit signed word used by C to a machine word yields
   maxIRQ unchanged -- again because the value is positive and fits, so sign extension
   contributes nothing. This is the rule that lets CRefine move an IRQ bound between the C
   and machine-word representations. *)
lemma scast_maxIRQ_32_machine[simp]:
  "scast (Kernel_Config.maxIRQ::32 signed word) = (Kernel_Config.maxIRQ::machine_word)"
  by (simp add: Kernel_Config.maxIRQ_def)

(* As scast_maxIRQ_32_machine, but casting into the narrower irq type rather than into a
   machine word. Stated separately because the two target types are used at different
   points in CRefine and neither instance follows from the other by simp alone. *)
lemma scast_maxIRQ_32_irq[simp]:
  "scast (Kernel_Config.maxIRQ :: 32 signed word) = (Kernel_Config.maxIRQ::irq)"
  by (simp add: Kernel_Config.maxIRQ_def)

(* Round-tripping a bounded IRQ through the enumeration is the identity: for a machine word
   within maxIRQ, converting to a natural and back with toEnum returns the original word.
   The bound is essential, since toEnum is only well behaved inside the IRQ range. Used
   where the kernel indexes IRQ tables by enumerating IRQ numbers. *)
lemma maxIRQ_ucast_toEnum_eq_machine:
  "x \<le> Kernel_Config.maxIRQ \<Longrightarrow> toEnum (unat x) = x" for x::machine_word
  by (simp add: word_le_nat_alt Kernel_Config.maxIRQ_def)

(* The irq-typed counterpart of maxIRQ_ucast_toEnum_eq_machine: for a machine word within
   maxIRQ, toEnum of its value is the narrowed irq value. Same hypothesis for the same
   reason -- the bound guarantees the narrowing loses nothing. Kept separate because the
   result type differs and both forms are needed downstream. *)
lemma maxIRQ_ucast_toEnum_eq_irq:
  "x \<le> Kernel_Config.maxIRQ \<Longrightarrow> toEnum (unat x) = (ucast x :: irq)" for x::machine_word
  by (simp add: word_le_nat_alt Kernel_Config.maxIRQ_def)

(* Adding one to maxIRQ does not overflow a machine word: the unsigned value of
   1 + maxIRQ is exactly Suc maxIRQ. Needed wherever the code iterates over the IRQ range
   with an exclusive upper bound of maxIRQ + 1, which appears in loop guards and in
   array-size side conditions. Trivial at PolarFire's 187, but stated so that downstream
   proofs never have to unfold the numeral. *)
lemma maxIRQ_1_plus_eq_Suc_machine[simp]:
  "unat (1 + Kernel_Config.maxIRQ :: machine_word) = Suc Kernel_Config.maxIRQ"
  by (simp add: Kernel_Config.maxIRQ_def)

end
end
