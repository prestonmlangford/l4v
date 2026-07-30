#!/usr/bin/env python3
"""List every session/theory declared in amp/ROOT.

This is structural metadata only -- which sessions exist, which theory files
they contain, and which session each one sits on (for heap-cache reuse via
`isabelle process -l`). It does not decide which THEOREMS need checking;
that is discovered separately, from Isabelle's own fact tables, by
check-traceability.sh -- not by parsing source text here. A theorem's name
never appears in this script.

Usage: list-amp-sessions.py [amp-root-dir]  (default: amp)
Output: one line per theory: "<session>\t<parent>\t<Session.Theory>"
"""

import re
import sys
from pathlib import Path

SESSION = re.compile(r'^\s*session\s+(\S+)\s+in\s+"([^"]+)"\s*=\s*(\S+)\s*\+')
THEORY_LINE = re.compile(r'"([A-Za-z_][A-Za-z0-9_]*)"')


def main():
    amp_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("amp")
    root_path = amp_dir / "ROOT"
    if not root_path.exists():
        return 0

    lines = root_path.read_text(encoding="utf-8").splitlines()
    i = 0
    while i < len(lines):
        m = SESSION.match(lines[i])
        if not m:
            i += 1
            continue
        session, _directory, parent = m.groups()
        i += 1
        while i < len(lines) and not SESSION.match(lines[i]):
            for thy in THEORY_LINE.findall(lines[i]):
                print(f"{session}\t{parent}\t{session}.{thy}")
            i += 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
