#!/usr/bin/env python3
"""Copy the shared definitions of a library module into `Challenge.lean`, or check the copy.

Comparator requires every constant that a Challenge statement uses to be the same in the
Challenge and in the Solution's environment. When the statements need definitions too large to
restate inline, keep them in one module of the library between the two marker lines below, and
let this script copy that block verbatim into `Challenge.lean`, which may not import the project.
The Solution imports the library, so both environments then contain the same definitions.

Run from the repository root:

    python3 scripts/sync_challenge_defs.py           # rewrite the block in the Challenge
    python3 scripts/sync_challenge_defs.py --check   # exit 1 if the copy differs (for CI)

Configure the block below for the project.
"""

import sys
from pathlib import Path

# ---- configuration -------------------------------------------------------------------------
# The library module that holds the shared definitions, and the Challenge file.
DEFS = 'ChallengeDefs.lean'
CHALLENGE = 'Challenge.lean'
# The marker lines around the shared blocks, in both files. Between the blocks, the Challenge states
# `ABφθSpec.existsUnique` and `ChallengeDefs` proves it.
BLOCKS = [('-- BEGIN SHARED DEFINITIONS 1\n', '-- END SHARED DEFINITIONS 1\n'),
          ('-- BEGIN SHARED DEFINITIONS 2\n', '-- END SHARED DEFINITIONS 2\n')]
# ---------------------------------------------------------------------------------------------

ROOT = Path(__file__).resolve().parent.parent


def block(text: str, name: str, begin: str, end: str) -> tuple[int, int]:
    """The span of a shared block in `text`, markers included."""
    i, j = text.find(begin), text.find(end)
    if i < 0 or j < i or text.count(begin) != 1 or text.count(end) != 1:
        sys.exit(f'{name}: expected exactly one pair of markers {begin.strip()!r}')
    return i, j + len(end)


def main() -> None:
    defs_path, chal_path = ROOT / DEFS, ROOT / CHALLENGE
    defs, chal = defs_path.read_text(), chal_path.read_text()
    check = '--check' in sys.argv[1:]
    for begin, end in BLOCKS:
        di, dj = block(defs, DEFS, begin, end)
        ci, cj = block(chal, CHALLENGE, begin, end)
        shared = defs[di:dj]
        if check:
            if chal[ci:cj] != shared:
                sys.exit(f'{CHALLENGE}: the shared definitions {begin.strip()!r} differ from {DEFS}; '
                         f'run python3 scripts/sync_challenge_defs.py')
        else:
            chal = chal[:ci] + shared + chal[cj:]
    if check:
        print(f'{CHALLENGE}: the shared definitions match {DEFS}')
    else:
        chal_path.write_text(chal)
        print(f'{CHALLENGE}: shared definitions copied from {DEFS}')


if __name__ == '__main__':
    main()
