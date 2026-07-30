# AMP proof development — fast-iteration harness

This directory holds the sessions for the verified AMP (multicore) work. See
`../../PLAN.md` for the current work stack; a session gets added here as work
on it starts. This file explains how to iterate on those proofs quickly.

## What gets cached

Isabelle persists each *session* as a **heap image** — a snapshot of the checked
logical state (every definition, theorem, and simp set) — under
`~/.isabelle/heaps/polyml-*/<SessionName>`. Building a session that imports
another loads the imported session's heap instead of re-checking its theories.

Two properties of that cache to keep in mind:

- **Ephemeral.** `~/.isabelle/heaps` does *not* survive a devcontainer rebuild
  (only `/workspaces/polarfire` persists). Prerequisite heaps are rebuilt once
  per fresh container, then reused.
- **A snapshot, so it can go stale.** A heap is valid only while nothing *below*
  it changes. Edit a theory and every session that imports it must rebuild.

## Regime A — fast iteration for free (the default here)

Because we control our own session boundaries, each phase's theory lives in its
own session sitting on top of **already-built prerequisite heaps**. Rebuilding
that session then re-checks only *your* theory.

```sh
export L4V_ARCH=RISCV64 L4V_PLAT=polarfire
cd l4v
./isabelle/bin/isabelle build -d . -v <YourSession>
```

Measured (attempt 1): with the `ASpec` heap present, editing a session's
top theory and rebuilding it re-checked that one theory in **~1 s** (≈10 s
including process start), *not* the whole abstract spec. The build log shows
`ASpec`, `ExecSpec`, and the `Lib` sessions listed but not "Running" — they
are loaded from cache.

This is why each unit of work should sit in its own session: you get
incremental rebuilds without any special tooling, as long as your edits stay
in the top-most theory.

## Regime B — the scratch-base trick (when Regime A is not enough)

You need this only when you are iterating on a theory that sits **on top of
other new theories inside the same growing session** — e.g. late in a phase,
tweaking `Foo_C.thy` while `Foo_A.thy` and `Foo_R.thy` below it are stable but
un-cached (they are not their own session). Rebuilding the whole session each
time re-checks the stable lower theories too.

The fix (this is the generalized `EVSBase`/`EVSTest` pattern used during the
single-core work): split the stack at the theory you are editing.

1. **Base session** = everything *below* the cut, built once → cached heap.
2. **Scratch session** = imports the base heap, contains *only* the theory you
   are editing.

Template — drop into a throwaway `amp/scratch/ROOT` (never merge it):

```
chapter "AMP"

(* Cache everything stable below the theory under edit, ONCE. *)
session AmpBase in "base" = ASpec +          (* or Access, CRefine, ... per phase *)
  theories
    "Foo_A"                                    (* the stable lower theories *)
    "Foo_R"

(* Rebuilds in seconds: only the theory under edit. *)
session AmpScratch in "test" = AmpBase +
  theories
    "Foo_C"                                    (* the one you are iterating *)
```

Then `isabelle build -d . -d amp/scratch AmpBase` once, and thereafter
`isabelle build -d . -d amp/scratch AmpScratch` on each edit.

Rules learned the hard way:

- **Two sessions may not own the same directory.** Give `base/` and `test/`
  distinct dirs (hence `in "base"` / `in "test"`).
- **Cross-session imports need the session-qualified name** — `AmpBase.Foo_A`,
  not `"Foo_A"` — once the theory lives in another session.
- **Move the cut line down when you edit lower.** If you start changing `Foo_R`,
  it belongs in the scratch session (or the base must be rebuilt). The base is
  only a speedup while it is stable.
- **Scratch ROOTs are throwaway.** Keep them out of `amp/ROOT` and out of
  merges; they exist only to speed up local iteration.

## Rebuilding a stale prerequisite heap

If a prerequisite is missing (fresh container) or you changed something below
it, rebuild just that heap once:

```sh
./isabelle/bin/isabelle build -d . -b ASpec     # -b = build heap image
```
