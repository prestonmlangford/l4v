#!/usr/bin/env python3
"""Transitive AMP-session directory closure for one session, from amp/ROOT.

Companion to list-amp-sessions.py, for a different consumer: the check
scripts' content-addressed cache (scripts/amp-cache.sh) needs to know, for a
given AMP session, every AMP-session directory whose files an `isabelle
process -T <theory>` call for it can actually depend on -- its declared base
(`= Base +`) and every name in its `sessions` block, transitively -- so that
changing any of them invalidates its cache entry. A base or `sessions` name
that is not itself an AMP session (Access, Refine, CRefine, ...) is not an
AMP session's own content and is covered instead by amp-cache.sh's l4v-pin
input, not by this script.

Usage: amp-session-deps.py <amp-root-dir> <session-name>
Output: one directory (relative to <amp-root-dir>) per line, for <session-name>
itself and every AMP session it transitively sits on. Sorted, deduplicated.
"""

import re
import sys
from pathlib import Path

SESSION = re.compile(r'^\s*session\s+(\S+)\s+in\s+"([^"]+)"\s*=\s*(\S+)\s*\+')
IDENT = re.compile(r'^\s*([A-Za-z_][A-Za-z0-9_.]*)\s*$')


def parse_root(root_path):
    lines = root_path.read_text(encoding="utf-8").splitlines()
    sessions = {}  # name -> (directory, {dep session names})
    i = 0
    n = len(lines)
    while i < n:
        m = SESSION.match(lines[i])
        if not m:
            i += 1
            continue
        name, directory, base = m.groups()
        deps = {base}
        i += 1
        in_sessions_block = False
        while i < n and not SESSION.match(lines[i]):
            stripped = lines[i].strip()
            if stripped == "sessions":
                in_sessions_block = True
            elif stripped == "theories":
                in_sessions_block = False
            elif in_sessions_block:
                im = IDENT.match(lines[i])
                if im:
                    deps.add(im.group(1))
            i += 1
        sessions[name] = (directory, deps)
    return sessions


def main():
    if len(sys.argv) != 3:
        print(__doc__, file=sys.stderr)
        return 2
    amp_dir = Path(sys.argv[1])
    target = sys.argv[2]
    sessions = parse_root(amp_dir / "ROOT")
    if target not in sessions:
        print(f"unknown AMP session: {target}", file=sys.stderr)
        return 2

    seen = set()
    dirs = set()
    stack = [target]
    while stack:
        name = stack.pop()
        if name in seen:
            continue
        seen.add(name)
        entry = sessions.get(name)
        if entry is None:
            continue  # not an AMP session -- see module docstring
        directory, deps = entry
        dirs.add(directory)
        stack.extend(deps)

    for d in sorted(dirs):
        print(d)
    return 0


if __name__ == "__main__":
    sys.exit(main())
