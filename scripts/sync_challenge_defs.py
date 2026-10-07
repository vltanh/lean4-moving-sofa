#!/usr/bin/env python3
"""Copy the shared definitions of library modules into the Challenge files, or check the copies.

Comparator requires every constant that a Challenge statement uses to be the same in the
Challenge and in the Solution's environment. When the statements need definitions too large to
restate inline, keep them in a module of the library between marker lines, and let this script
copy those blocks verbatim into the Challenge, which may not import the project. The Solution
imports the library, so both environments then contain the same definitions.

Lean names the auxiliary theorems that it makes from proofs inside definitions after the first
definition that needs them in a module, so a block must follow the same blocks in the Challenge as
in the library. The script therefore also checks that each Challenge holds its blocks in the order
of the configuration below.

Run from the repository root:

    python3 scripts/sync_challenge_defs.py           # rewrite the blocks in the Challenges
    python3 scripts/sync_challenge_defs.py --check   # exit 1 if a copy differs (for CI)

Configure the copies below for the project.
"""

import sys
from pathlib import Path

# ---- configuration -------------------------------------------------------------------------
# The marker lines around the shared blocks, in the library module and in the Challenge.
BAEK_CORE = ('-- BEGIN BAEK CORE DEFINITIONS\n', '-- END BAEK CORE DEFINITIONS\n')
BAEK_STABILITY = ('-- BEGIN BAEK STABILITY DEFINITIONS\n', '-- END BAEK STABILITY DEFINITIONS\n')
# Formal-conjectures' definitions. Between the two blocks, the Challenges state
# `ABφθSpec.existsUnique` and `MovingSofaBridge.Defs` proves it.
SHARED_1 = ('-- BEGIN SHARED DEFINITIONS 1\n', '-- END SHARED DEFINITIONS 1\n')
SHARED_2 = ('-- BEGIN SHARED DEFINITIONS 2\n', '-- END SHARED DEFINITIONS 2\n')
CERTIFICATE = ('-- BEGIN CERTIFICATE DEFINITIONS\n', '-- END CERTIFICATE DEFINITIONS\n')
# Each copy: the library module that holds the shared definitions, the Challenge file, and its
# blocks. The blocks of each Challenge appear in it in the order of this list.
COPIES = [
    # Version 5 of the Palomar entry (comparator.json), at the root. The certificate's block comes
    # after all the blocks of MovingSofaBridge/Defs.lean, as `MovingSofaExtremal.CertificateDefs`
    # assumes.
    ('MovingSofaBridge/Defs.lean', 'Challenge.lean',
     [BAEK_CORE, BAEK_STABILITY, SHARED_1, SHARED_2]),
    ('MovingSofaExtremal/CertificateDefs.lean', 'Challenge.lean', [CERTIFICATE]),
    # The Challenge of versions 1 to 4 (baek/comparator.json).
    ('MovingSofaBridge/Defs.lean', 'baek/Challenge.lean', [BAEK_CORE, SHARED_1, SHARED_2]),
]
# ---------------------------------------------------------------------------------------------

ROOT = Path(__file__).resolve().parent.parent


def block(text: str, name: str, begin: str, end: str) -> tuple[int, int]:
    """The span of a shared block in `text`, markers included."""
    i, j = text.find(begin), text.find(end)
    if i < 0 or j < i or text.count(begin) != 1 or text.count(end) != 1:
        sys.exit(f'{name}: expected exactly one pair of markers {begin.strip()!r}')
    return i, j + len(end)


def sync(defs_name: str, chal_name: str, blocks: list[tuple[str, str]], check: bool) -> None:
    """Copy the blocks of `defs_name` into `chal_name`, or check that they match."""
    defs_path, chal_path = ROOT / defs_name, ROOT / chal_name
    defs, chal = defs_path.read_text(), chal_path.read_text()
    for begin, end in blocks:
        di, dj = block(defs, defs_name, begin, end)
        ci, cj = block(chal, chal_name, begin, end)
        shared = defs[di:dj]
        if check:
            if chal[ci:cj] != shared:
                sys.exit(f'{chal_name}: the shared definitions {begin.strip()!r} differ from '
                         f'{defs_name}; run python3 scripts/sync_challenge_defs.py')
        else:
            chal = chal[:ci] + shared + chal[cj:]
    if check:
        print(f'{chal_name}: the shared definitions match {defs_name}')
    else:
        chal_path.write_text(chal)
        print(f'{chal_name}: shared definitions copied from {defs_name}')


def check_order() -> None:
    """Exit 1 unless each Challenge holds its blocks in the order of `COPIES`."""
    for chal_name in dict.fromkeys(chal for _, chal, _ in COPIES):
        chal = (ROOT / chal_name).read_text()
        blocks = [b for _, c, bs in COPIES if c == chal_name for b in bs]
        starts = [block(chal, chal_name, begin, end)[0] for begin, end in blocks]
        if starts != sorted(starts):
            sys.exit(f'{chal_name}: the shared blocks are not in the order of '
                     f'scripts/sync_challenge_defs.py')


def main() -> None:
    check = '--check' in sys.argv[1:]
    check_order()
    for defs_name, chal_name, blocks in COPIES:
        sync(defs_name, chal_name, blocks, check)


if __name__ == '__main__':
    main()
