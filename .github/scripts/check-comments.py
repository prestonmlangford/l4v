#!/usr/bin/env python3
"""Check that newly added Isabelle declarations carry a preceding prose comment.

Implements the coding standard in multicore-amp-plan.md section 2: every
definition and lemma we add must be preceded by a plain-English comment that
explains it completely.

This only inspects lines ADDED relative to a base ref, so untouched upstream
seL4 declarations are never flagged. It is a review aid, not a judge of comment
quality -- it can tell that a comment exists, not that it is complete.

Usage: check-comments.py <base-ref> [repo-dir]
Exit:  0 = every added declaration is commented, 1 = some are not.
"""

import re
import subprocess
import sys

# Isabelle declaration forms that the standard requires a comment on.
DECL = re.compile(
    r"^\s*(definition|lemma|theorem|corollary|abbreviation|primrec|fun|"
    r"function|record|datatype|inductive|inductive_set|type_synonym|"
    r"locale|instantiation|schematic_goal)\b"
)

HUNK = re.compile(r"^@@ -\S+ \+(\d+)(?:,(\d+))? @@")


def added_lines(base, repo):
    """Map each changed .thy file to the set of line numbers added vs base.

    `git diff` only ever considers tracked paths, so a brand-new file that
    hasn't been `git add`-ed yet would otherwise be invisible here and skip
    the check entirely. Untracked .thy files are unioned in separately, with
    every line treated as added (the whole file is new).
    """
    out = subprocess.run(
        ["git", "-C", repo, "diff", "--unified=0", "--no-color", base, "--", "*.thy"],
        capture_output=True, text=True, check=True,
    ).stdout
    files, cur, lineno = {}, None, 0
    for line in out.splitlines():
        if line.startswith("+++ b/"):
            cur = line[6:]
            files.setdefault(cur, set())
        elif line.startswith("@@"):
            m = HUNK.match(line)
            if m:
                lineno = int(m.group(1))
        elif line.startswith("+") and not line.startswith("+++") and cur:
            files[cur].add(lineno)
            lineno += 1

    untracked = subprocess.run(
        ["git", "-C", repo, "ls-files", "--others", "--exclude-standard", "--", "*.thy"],
        capture_output=True, text=True, check=True,
    ).stdout
    for path in untracked.splitlines():
        if not path:
            continue
        try:
            with open(f"{repo}/{path}", encoding="utf-8", errors="replace") as fh:
                n_lines = len(fh.read().splitlines())
        except FileNotFoundError:
            continue
        files.setdefault(path, set()).update(range(1, n_lines + 1))
    return files


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
    base = sys.argv[1]
    repo = sys.argv[2] if len(sys.argv) > 2 else "."

    findings = []
    for path, added in sorted(added_lines(base, repo).items()):
        if not added:
            continue
        try:
            with open(f"{repo}/{path}", encoding="utf-8", errors="replace") as fh:
                lines = fh.read().splitlines()
        except FileNotFoundError:
            continue  # deleted in the working tree
        mask = in_comment_mask(lines)
        for n in sorted(added):
            if n > len(lines):
                continue
            text = lines[n - 1]
            if mask[n - 1]:
                continue  # this "declaration-looking" line is prose inside a comment
            if DECL.match(text) and not is_commented(lines, n - 1):
                findings.append((path, n, text.strip()[:70]))

    if not findings:
        print("  OK: every added declaration has a preceding comment")
        return 0

    print(f"  {len(findings)} added declaration(s) with no preceding comment:\n")
    for path, n, text in findings:
        print(f"    {path}:{n}")
        print(f"      {text}")
    print("\n  Coding standard (plan section 2): each must be preceded by prose")
    print("  giving its meaning, its assumptions, and the phase/obligation it serves.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
