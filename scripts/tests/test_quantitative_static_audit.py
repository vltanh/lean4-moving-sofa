#!/usr/bin/env python3
"""Regression checks for source-only proof-gate bookkeeping.

These checks do not execute Lean, Lake, CI, or numerical certificates.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "audit_quantitative_source_static.py"
spec = importlib.util.spec_from_file_location("quantitative_static_audit", SCRIPT)
assert spec is not None and spec.loader is not None
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


class SourceReviewKeyTests(unittest.TestCase):
    def test_no_duplicate_proof_review_keys(self):
        self.assertEqual(audit.duplicate_gate_keys(SCRIPT.read_text(encoding="utf-8")), [])

    def test_duplicate_key_regression_is_detected(self):
        source = ('PROOF_REVIEW_GATES: dict[str, tuple] = '
                  '{"Example.lean": (), "Example.lean": ()}')
        self.assertEqual(audit.duplicate_gate_keys(source), ["Example.lean"])

    def test_regularization_gates_are_all_present(self):
        rules = audit.PROOF_REVIEW_GATES[
            "MovingSofaQuantitative/EffectiveRegularizationSupport.lean"]
        self.assertGreaterEqual(len(rules), 3)
        joined = " ".join(pattern for pattern, _ in rules)
        self.assertIn("sup_le_of_L2_lipschitz", joined)
        self.assertIn("exists_integral_penalized_limit", joined)
        self.assertIn("subset", joined)

    def test_audit_never_self_certifies_kernel_status(self):
        self.assertIn("source-only", audit.source_audit.__doc__ or
                      SCRIPT.read_text(encoding="utf-8"))
        self.assertNotIn("native_decide", " ".join(
            pattern for rules in audit.PROOF_REVIEW_GATES.values()
            for pattern, _ in rules))


if __name__ == "__main__":
    unittest.main()
