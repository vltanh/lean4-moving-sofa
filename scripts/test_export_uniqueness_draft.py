"""Static source-assembly tests only. They never run or elaborate Lean."""
import re
import unittest

import export_uniqueness_draft as draft


class ExportTests(unittest.TestCase):
    def fixture(self):
        return ("module\n\n" + draft.IMPORT_ANCHOR + "\nnamespace MovingSofa\n"
                "theorem earlier_placeholder : True := by\n  sorry\n\n" +
                draft.DOC_ANCHOR + "\n-/\n" + draft.ORIGINAL + "\n\nend MovingSofa\n")

    def target(self):
        # Deliberately a synthetic source fixture, not an asserted Lean proof.
        return "@[category research open, AMS 49]\n" + draft.SIGNATURE + "\n  exact fixtureProof"

    def test_git_blob_hash(self):
        self.assertEqual(draft.git_blob_sha(b""), "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391")

    def test_namespace_and_module_relocation(self):
        source = "import MovingSofa.Main\nnamespace MovingSofa\n#check ``MovingSofa.foo\nend MovingSofa"
        result = draft.transform_lean(source, relocate=True)
        self.assertNotIn("MovingSofa", result)
        self.assertIn("import SofaLegacy.Main", result)
        self.assertIn("``SofaLegacy.foo", result)

    def test_comments_strings_and_similar_names_are_not_relocated(self):
        source = ('/- MovingSofa /- nested MovingSofa -/ -/\n-- MovingSofa\n'
                  'def MovingSofaα := "MovingSofa"\ndef MovingSofaChallenge := 0\n')
        self.assertEqual(draft.transform_lean(source, relocate=True), source)

    def test_mask_counts_code_admissions_only(self):
        source = '"sorry" /- sorry /- sorry -/ -/\n-- sorry\ntheorem x : True := by sorry'
        self.assertEqual(len(re.findall(r"\bsorry\b", draft.transform_lean(source, mask=True))), 1)

    def test_unterminated_comment_rejected(self):
        with self.assertRaisesRegex(ValueError, "unterminated"):
            draft.transform_lean("/- unfinished")

    def test_unterminated_string_rejected(self):
        with self.assertRaisesRegex(ValueError, "unterminated"):
            draft.transform_lean('"unfinished')

    def test_assembly_preserves_signature_and_existing_placeholders(self):
        result = draft.assemble(self.fixture(), "namespace UniquenessDraft\nend UniquenessDraft",
                                "-- second fragment", self.target())
        code = draft.transform_lean(result, mask=True)
        self.assertEqual(code.count(draft.SIGNATURE), 1)
        self.assertEqual(len(re.findall(r"\bsorry\b", code)), 1)
        self.assertIn("public import SofaUniqueness.Draft.ShapeUniqueness", result)
        self.assertNotIn(draft.ORIGINAL, result)

    def test_changed_statement_rejected(self):
        changed = self.target().replace("(s : Set ℝ²)", "(s : Set ℝ²) (h : False)")
        with self.assertRaisesRegex(ValueError, "statement"):
            draft.assemble(self.fixture(), "", "", changed)

    def test_circular_target_use_rejected(self):
        with self.assertRaisesRegex(ValueError, "before its declaration"):
            draft.assemble(self.fixture(), "#check " + draft.TARGET, "", self.target())

    def test_new_axiom_rejected(self):
        with self.assertRaisesRegex(ValueError, "axiom"):
            draft.assemble(self.fixture(), "axiom fake : False", "", self.target())

    def test_unfilled_target_rejected(self):
        with self.assertRaisesRegex(ValueError, "admission"):
            draft.assemble(self.fixture(), "", "", draft.ORIGINAL)

    def test_changed_upstream_rejected(self):
        with self.assertRaisesRegex(ValueError, "differs"):
            draft.assemble(self.fixture().replace(draft.ORIGINAL, ""), "", "", self.target())


if __name__ == "__main__":
    unittest.main()
