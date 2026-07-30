(*
 * Copyright 2026, PolarFire AMP verification.
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory AMP_Placeholder_Witnesses
imports AMP_Placeholder
begin

(*
 * This session is not AMP proof content -- see AMP_Placeholder.thy's header
 * comment. This theory holds nothing but positive witnesses for that
 * theory's hypothesis-bearing theorems, named pw_<theorem-name> per the
 * convention in vocabulary.md, kept out of the main proof file.
 *)

section "Results"

(*
 * Positive witness for amp_placeholder_self_authority: its hypothesis,
 * pas_wellformed aag, is satisfiable, witnessed by Sys1PAS (Sys1_wellformed
 * already proves pas_wellformed Sys1PAS). Fixing the authority Control makes
 * the instance fully concrete, so this is a real derived fact about a real
 * example system, not a restatement of the hypothesis it discharges.
 *)
lemma pw_amp_placeholder_self_authority:
  "(pasSubject Sys1PAS, Control, pasSubject Sys1PAS) \<in> pasPolicy Sys1PAS"
  using amp_placeholder_self_authority[OF Sys1_wellformed] .

end
