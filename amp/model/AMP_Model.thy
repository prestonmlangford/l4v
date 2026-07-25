(*
 * PolarFire verified multicore (AMP) — Phase 1 scaffold.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * This theory is the target of the fast-iteration harness (see amp/README.md).
 * It is deliberately EMPTY of declarations for now: its present job is to make
 * the AMP_Model session exist and build green on top of the cached ASpec heap,
 * so that when Phase 1 modelling begins, editing this file rebuilds only this
 * file (~seconds) rather than the whole abstract spec (~minutes).
 *
 * Phase 1 (per multicore-amp-plan.md section 5) will populate this theory with:
 *   - core_id, and amp_state = a finite map core_id => abstract_state
 *     (the per-core abstract_state is imported UNCHANGED from ASpec below);
 *   - boot_partition: the static assignment of frames/IRQs/channels to cores;
 *   - partition_wf: the well-formedness predicate (cores' owned frame sets are
 *     disjoint except at declared channel buffers).
 * Every declaration added here must carry a complete preceding comment
 * (coding standard, plan section 2).
 *)

theory AMP_Model
imports "ASpec.Syscall_A"
begin

(* Phase 1 content goes here. Importing ASpec.Syscall_A brings the single-core
   abstract specification -- including `record abstract_state` -- into scope so
   the multicore composition can be defined over per-core states without
   modifying the verified single-core spec. *)

end
