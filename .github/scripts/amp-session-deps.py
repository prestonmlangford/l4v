#!/usr/bin/env python3
"""Transitive AMP-session closure for one session, from amp/ROOT.

Companion to list-amp-sessions.py, for a different consumer: the check
scripts' content-addressed cache (scripts/amp-cache.sh) needs to know, for a
given AMP session, every AMP-session directory whose files an `isabelle
process -T <theory>` call for it can actually depend on -- its declared base
(`= Base +`) and every name in its `sessions` block, transitively -- so that
changing any of them invalidates its cache entry. A base or `sessions` name
that is not itself an AMP session (Access, Refine, CRefine, ...) is not an
AMP session's own content and is covered instead by amp-cache.sh's l4v-pin
input, not by this script.

Default usage: amp-session-deps.py <amp-root-dir> <session-name>
Output: one directory (relative to <amp-root-dir>) per line, for <session-name>
itself and every AMP session it transitively sits on. Sorted, deduplicated.

--stanzas usage: amp-session-deps.py --stanzas <amp-root-dir> <session-name>
Output: the raw amp/ROOT declaration text (session line through its
`theories`/`sessions` block) for <session-name> and every AMP session it
transitively sits on, one block per session, sorted by session name. This is
the part of amp/ROOT that can actually change what an `isabelle process -T`
call for <session-name> depends on -- which non-AMP base it sits on, which
AMP sessions it cites, which theory files it declares. Hashing just this
(amp-cache.sh's amp_cache_key) instead of the whole ROOT file means editing
one session's stanza does not invalidate every other session's cache entry,
the way hashing the whole file would.
"""

import re
import sys
from pathlib import Path

SESSION = re.compile(r'^\s*session\s+(\S+)\s+in\s+"([^"]+)"\s*=\s*(\S+)\s*\+')
IDENT = re.compile(r'^\s*([A-Za-z_][A-Za-z0-9_.]*)\s*$')
QUOTED_THEORY = re.compile(r'^\s*"[A-Za-z_][A-Za-z0-9_.]*"\s*$')


def parse_root(root_path):
    lines = root_path.read_text(encoding="utf-8").splitlines()
    # First pass: each session's own declaration span (session line through
    # its sessions/theories block), not yet including the comment that
    # precedes it -- that comment sits *before* the session line, i.e. in
    # the gap left over from the previous session's span, so it has to be
    # reattached in a second pass below rather than picked up here.
    #
    # The walk below has to stop at the *last line of actual content*
    # (the session header, a "sessions"/"theories" keyword, a dependency
    # identifier, or a quoted theory name) rather than at the next
    # `session` line -- otherwise the blank lines and the next session's
    # own preceding comment, which sit between this session's last theory
    # name and the next `session` line, end up counted as this session's
    # body, and the second pass below has nothing left to reattach them to.
    order = []  # [(name, directory, deps, body_start, body_end)]
    i = 0
    n = len(lines)
    while i < n:
        m = SESSION.match(lines[i])
        if not m:
            i += 1
            continue
        body_start = i
        last_content = i
        name, directory, base = m.groups()
        deps = {base}
        i += 1
        in_sessions_block = False
        while i < n and not SESSION.match(lines[i]):
            stripped = lines[i].strip()
            if stripped == "sessions":
                in_sessions_block = True
                last_content = i
            elif stripped == "theories":
                in_sessions_block = False
                last_content = i
            elif in_sessions_block:
                im = IDENT.match(lines[i])
                if im:
                    deps.add(im.group(1))
                    last_content = i
            elif QUOTED_THEORY.match(lines[i]):
                last_content = i
            i += 1
        order.append((name, directory, deps, body_start, last_content + 1))

    # Second pass: reattach each session's preceding comment (the gap
    # between the previous session's body end and this session's own body
    # start) to this session's stanza, so an edit to a session's own
    # descriptive comment invalidates that session's cache entry, not its
    # predecessor's.
    sessions = {}  # name -> (directory, {dep session names}, stanza text)
    prev_end = 0
    for name, directory, deps, body_start, body_end in order:
        stanza = "\n".join(lines[prev_end:body_end])
        sessions[name] = (directory, deps, stanza)
        prev_end = body_end
    return sessions


def transitive_closure(sessions, target):
    seen = set()
    stack = [target]
    while stack:
        name = stack.pop()
        if name in seen:
            continue
        seen.add(name)
        entry = sessions.get(name)
        if entry is None:
            continue  # not an AMP session -- see module docstring
        _directory, deps, _stanza = entry
        stack.extend(deps)
    return seen


def main():
    args = sys.argv[1:]
    stanzas_mode = False
    if args and args[0] == "--stanzas":
        stanzas_mode = True
        args = args[1:]
    if len(args) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    amp_dir = Path(args[0])
    target = args[1]
    sessions = parse_root(amp_dir / "ROOT")
    if target not in sessions:
        print(f"unknown AMP session: {target}", file=sys.stderr)
        return 2

    closure = transitive_closure(sessions, target)

    if stanzas_mode:
        for name in sorted(closure):
            entry = sessions.get(name)
            if entry is None:
                continue
            _directory, _deps, stanza = entry
            print(f"### {name}")
            print(stanza)
        return 0

    dirs = {sessions[name][0] for name in closure if name in sessions}
    for d in sorted(dirs):
        print(d)
    return 0


if __name__ == "__main__":
    sys.exit(main())
