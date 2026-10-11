"""Run local symbolic checks for a SCHANUEL-CONDITIONAL theorem draft.

No numerical root search or geometric/number-theoretic proof verification is
performed. Source checks identify the exact algebra code being exercised.
"""
from __future__ import annotations

import argparse
import hashlib
import io
import json
from pathlib import Path
import platform
import sys
import unittest
import sympy

from elementary_descent_algebra import verify_identities

EXPECTED_BLOBS = {
    "elementary_descent_algebra.py": "ea03fb2605cfacfe00d14eb00b8e148245748e81",
    "test_elementary_descent.py": "f24b1c6b4e73c3f83cc48177302159468956a5da",
}


def git_blob(path: Path) -> str:
    data = path.read_bytes()
    return hashlib.sha1(f"blob {len(data)}\0".encode()+data).hexdigest()


def run_checks() -> dict:
    root = Path(__file__).resolve().parent
    blobs = {name: git_blob(root/name) for name in EXPECTED_BLOBS}
    if blobs != EXPECTED_BLOBS:
        raise RuntimeError("Source hashes changed; review the algebra and update the record explicitly.")
    identities = verify_identities()
    suite = unittest.defaultTestLoader.loadTestsFromName("test_elementary_descent")
    capture = io.StringIO()
    result = unittest.TextTestRunner(stream=capture, verbosity=2).run(suite)
    sys.stderr.write(capture.getvalue())
    if not result.wasSuccessful() or result.skipped:
        raise RuntimeError("Algebra regression tests failed or were skipped.")
    return {
        "format": "elementary-descent-checks-v1",
        "starting_commit": "e5b064b6d6986580252ed5f58dc7d14eb0b77bb6",
        "status": "Conditional proof draft: Schanuel assumed; only symbolic identities tested here.",
        "source_blobs": blobs,
        "environment": {"python": platform.python_version(), "sympy": sympy.__version__},
        "tests": {"run": result.testsRun, "passed": result.testsRun, "skipped": 0,
                  "command": "python -m unittest -v test_elementary_descent"},
        "identities": identities,
        "negative_controls": [
            "P constant allows the elementary solution x=log(2)/(sqrt(2)-1).",
            "P(0)=0 allows the elementary solution x=log(2)/(sqrt(2)+1).",
            "A common factor can hide a monomial graph and an elementary solution.",
            "A rational multiplier permits nonzero rational logarithmic coefficients."
        ],
        "initial_failure": {
            "kind": "test expression-tree equality versus algebraic equality",
            "details": "One initial test compared (d+6)/(4*(d+2)) with (d+6)/(4*d+8) syntactically.",
            "repair": "Compare the exact cancelled difference with zero; no mathematical formula changed."
        },
        "not_verified_by_tests": [
            "Schanuel's conjecture",
            "the conditional field-theoretic/tower-descent proof",
            "unconditional non-elementarity or irrationality",
            "identification of the model root with the unrestricted phase transition",
            "prior geometric theorem drafts or old numerical certificates"
        ],
        "ci": False,
        "lean_build": False,
        "reproduction": "python run_elementary_descent_checks.py --output results/elementary-descent-checks.json"
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    output = json.dumps(run_checks(), indent=2)+"\n"
    if args.output is None:
        print(output, end="")
    else:
        args.output.write_text(output, encoding="utf-8")
