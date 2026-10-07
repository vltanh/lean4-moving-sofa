#!/usr/bin/env python3
"""Redraw every figure of baek/proof/, in baek/proof/figures/.

    python3 scripts/figures/make_all.py

Runs the `main()` of each chapter's module fig_<chapter>.py, in alphabetical order. The figures are
computed from the definitions of the formalization (gerver.py) and check, with `assert`s, the facts
that their captions state.
"""
import importlib
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent


def main():
    sys.path.insert(0, str(HERE))
    for path in sorted(HERE.glob('fig_*.py')):
        print(f'{path.name}:')
        importlib.import_module(path.stem).main()


if __name__ == '__main__':
    main()
