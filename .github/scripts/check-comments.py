#!/usr/bin/env python3
"""Check that every Isabelle declaration under a directory carries a preceding prose comment.

Implements the coding standard in CLAUDE.md / CONTRIBUTING.md: every
definition and lemma in the AMP body of work must be preceded by a
plain-English comment that explains it completely.

Scope is a fixed directory (l4v/amp/), not a git diff against a base ref.
l4v/amp/ IS the entire AMP body of work -- CLAUDE.md forbids touching
existing l4v proofs at all -- so scanning it whole is exactly as complete as
the rule requires, and it stays correct regardless of which branch or base
ref a check happens to run against. It is a review aid, not a judge of
comment quality -- it can tell that a comment exists, not that it is complete.

Usage: check-comments.py <dir>
Exit:  0 = every declaration is commented, 1 = some are not.
"""

import re
import sys
from pathlib import Path

# Isabelle declaration forms that the standard requires a comment on.
DECL = re.compile(
    r"^\s*(definition|lemma|theorem|corollary|abbreviation|primrec|fun|"
    r"function|record|datatype|inductive|inductive_set|type_synonym|"
    r"locale|instantiation|schematic_goal)\b"
)


def in_comment_mask(lines):
    """Per-line bool: True if that line is inside an Isabelle (* ... *) block.

    A line that OPENS a comment and doesn't close it on the same line counts
    as inside (it's comment text, even though the "(*" token itself isn't).
    Nesting depth is tracked so nested comments don't close early. This is a
    plain textual scan -- it doesn't understand Isabelle strings, so a "(*"
    or "*)" inside a quoted string could in principle confuse it, but that
    pattern doesn't occur in this project's theories.
    """
    mask = []
    depth = 0
    for line in lines:
        starts_inside = depth > 0
        i = 0
        while i < len(line):
            if line[i:i + 2] == "(*":
                depth += 1
                i += 2
            elif line[i:i + 2] == "*)":
                depth = max(0, depth - 1)
                i += 2
            else:
                i += 1
        mask.append(starts_inside or depth > 0)
    return mask


def is_commented(lines, idx):
    """True if the declaration at 0-based idx has a comment block above it.

    Walks back over blank lines, then requires the nearest non-blank line to
    close an Isabelle comment. Also accepts Isabelle's text/section markup.
    Callers must first check in_comment_mask(lines)[idx] and skip this
    entirely if it's set -- a wrapped comment line that happens to start with
    a keyword like "function" or "theorem" is prose, not a declaration.
    """
    i = idx - 1
    while i >= 0 and not lines[i].strip():
        i -= 1
    if i < 0:
        return False
    prev = lines[i].strip()
    return prev.endswith("*)") or prev.startswith(("text", "section", "subsection"))


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    root = Path(sys.argv[1])

    findings = []
    for path in sorted(root.rglob("*.thy")):
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
        mask = in_comment_mask(lines)
        for i, text in enumerate(lines):
            if mask[i]:
                continue  # this "declaration-looking" line is prose inside a comment
            if DECL.match(text) and not is_commented(lines, i):
                findings.append((path, i + 1, text.strip()[:70]))

    if not findings:
        print("  OK: every declaration has a preceding comment")
        return 0

    print(f"  {len(findings)} declaration(s) with no preceding comment:\n")
    for path, n, text in findings:
        print(f"    {path}:{n}")
        print(f"      {text}")
    print("\n  Coding standard (CLAUDE.md): each must be preceded by prose")
    print("  giving its meaning, its assumptions, and the assumption it pays, if any.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
