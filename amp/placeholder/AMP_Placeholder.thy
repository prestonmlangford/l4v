(*
 * Copyright 2026, PolarFire AMP verification.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory AMP_Placeholder
imports "Access.ExampleSystem"
begin

(*
 * This session is not AMP proof content. It exists only so the merge
 * gate's traceability check (scripts/check-traceability.sh) has one real,
 * merged theorem to run against, instead of only the scratch files used to
 * develop that script (which were deleted after testing, never merged).
 * Delete this session and its entry in amp/ROOT once real per-kernel or
 * channel proof work begins (PLAN.md items 1-5) -- do not add real AMP
 * results to this file.
 *)

section "Results"

(*
 * The two-domain example system already checked into l4v has a
 * well-formed authority graph: Sys1_wellformed (proved in
 * Access.ExampleSystem) states that Sys1PAS satisfies pas_wellformed. This
 * lemma restates that fact under a new name, so the traceability check has
 * a genuine, checked, non-vacuous dependency on real l4v content to run
 * against -- not a self-contained fact invented for the occasion.
 *)
lemma amp_placeholder_pas_wellformed: "pas_wellformed Sys1PAS"
  using Sys1_wellformed .

end
