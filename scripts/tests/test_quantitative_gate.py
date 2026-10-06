"""Pure Python regression tests. Passing these does not check a Lean theorem."""
from __future__ import annotations
from contextlib import redirect_stderr
from fractions import Fraction as F
import io
from itertools import product
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import paper_claim_inventory as pc
import quantitative_gate as qg


class InventoryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / 'docs/paper/sections').mkdir(parents=True)

    def put(self, path, text):
        p = self.root / path
        p.write_text(text)
        return p

    def test_input_comment_verbatim_and_item_labels(self):
        self.put('docs/paper/main.tex', r'''\begin{document}
% \input{not-a-file}
\input{sections/results}
\end{document}
''')
        self.put('docs/paper/sections/results.tex', r'''\begin{theorem}\label{thm:test}
A statement containing a literal \% sign.
\begin{enumerate}\item\label{thm:test:a} A subclaim.\end{enumerate}
\end{theorem}
\begin{lstlisting}
\begin{theorem}\label{thm:fake}\end{theorem}
\end{lstlisting}
\verb|\label{thm:fake2}|
''')
        result = pc.inventory(self.root, Path('docs/paper/main.tex'))
        self.assertEqual(len(result['claims']), 1)
        self.assertEqual(result['claims'][0]['labels'], ['thm:test', 'thm:test:a'])
        self.assertEqual(result['claims'][0]['status'], 'unmapped')
        self.assertEqual(result['claims'][0]['line'], 1)

    def test_duplicate_labels_fail(self):
        self.put('docs/paper/main.tex', r'\begin{theorem}\label{x}\label{x}\end{theorem}')
        with self.assertRaisesRegex(pc.InventoryError, 'duplicate label'):
            pc.inventory(self.root, Path('docs/paper/main.tex'))

    def test_unlabelled_claim_is_reported(self):
        self.put('docs/paper/main.tex', r'\begin{remark}A claim.\end{remark}')
        self.assertEqual(pc.inventory(self.root, Path('docs/paper/main.tex'))['unlabelled'], 1)

    def test_cycle_fails(self):
        self.put('docs/paper/main.tex', r'\input{main}')
        with self.assertRaisesRegex(pc.InventoryError, 'cyclic'):
            pc.inventory(self.root, Path('docs/paper/main.tex'))

    def test_dynamic_input_fails(self):
        self.put('docs/paper/main.tex', r'\input{\chosen}')
        with self.assertRaisesRegex(pc.InventoryError, 'nonliteral'):
            pc.inventory(self.root, Path('docs/paper/main.tex'))

    def test_path_escape_fails(self):
        self.put('docs/paper/main.tex', r'\input{../../../../outside}')
        with self.assertRaisesRegex(pc.InventoryError, 'escapes'):
            pc.inventory(self.root, Path('docs/paper/main.tex'))

    def test_unbalanced_environment_fails(self):
        self.put('docs/paper/main.tex', r'\begin{theorem}X\end{lemma}')
        with self.assertRaisesRegex(pc.InventoryError, 'unmatched'):
            pc.inventory(self.root, Path('docs/paper/main.tex'))

    def test_comment_does_not_shift_line_numbers(self):
        source = '% gone\n\\begin{theorem}\\label{x}X\\end{theorem}\n'
        self.put('docs/paper/main.tex', source)
        result = pc.inventory(self.root, Path('docs/paper/main.tex'))
        self.assertEqual(result['claims'][0]['line'], 2)
        self.assertEqual(len(pc.mask_tex(source)), len(source))

    def test_escaped_percent_and_double_backslash(self):
        text = r'yes \% remains' + '\n' + r'yes \\% hidden \label{bad}'
        masked = pc.mask_tex(text)
        self.assertIn(r'\% remains', masked)
        self.assertNotIn('bad', masked)

    def test_unbraced_input_cannot_silently_escape_inventory(self):
        self.put('docs/paper/main.tex', r'\input omitted.tex')
        with self.assertRaisesRegex(pc.InventoryError, 'unsupported'):
            pc.inventory(self.root, Path('docs/paper/main.tex'))

    def test_escaped_label_command_is_not_counted(self):
        self.put('docs/paper/main.tex',
                 r'\begin{theorem}\label{real}Text \\label{fake}\end{theorem}')
        result = pc.inventory(self.root, Path('docs/paper/main.tex'))
        self.assertEqual(result['all_labels'], ['real'])

    def test_source_change_changes_hash(self):
        self.put('docs/paper/main.tex', r'\begin{theorem}\label{x}A\end{theorem}')
        before = pc.inventory(self.root, Path('docs/paper/main.tex'))
        self.put('docs/paper/main.tex', r'\begin{theorem}\label{x}B\end{theorem}')
        after = pc.inventory(self.root, Path('docs/paper/main.tex'))
        self.assertNotEqual(before['sources'], after['sources'])
        self.assertNotEqual(before['claims'][0]['statement_source_sha256'],
                            after['claims'][0]['statement_source_sha256'])


class GateTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / 'MovingSofaQuantitative').mkdir()
        (self.root / 'MovingSofaQuantitative/Targets.lean').write_text('def ExplicitCutoff : Prop := True\n')
        (self.root / 'MovingSofaQuantitative/Example.lean').write_text('theorem example : True := True.intro\n')
        self.path = self.root / 'manifest.json'
        self.data = {'schema': 1, 'scope': 'quantitative_extension', 'required_ids': ['explicit-cutoff'],
                     'results': [{'id': 'explicit-cutoff', 'target': qg.PREFIX + 'ExplicitCutoff',
                                  'declaration': None, 'module': None, 'status': 'planned'}]}

    def load(self):
        self.path.write_text(json.dumps(self.data))
        return qg.load_manifest(self.root, self.path)

    def test_planned_is_not_proved(self):
        self.load()
        with self.assertRaisesRegex(qg.GateError, 'unproved'):
            qg.verify(self.root, self.path, self.data, False, self.root/'receipt.json')
        self.assertFalse((self.root/'receipt.json').exists())

    def test_manifest_cannot_self_attest_checked(self):
        self.data['results'][0]['status'] = 'checked'
        with self.assertRaisesRegex(qg.GateError, 'fresh Lean receipt'):
            self.load()

    def test_cutoff_cannot_disappear(self):
        self.data['results'][0]['id'] = 'other'
        self.data['required_ids'] = ['other']
        with self.assertRaisesRegex(qg.GateError, 'mandatory'):
            self.load()

    def test_cutoff_cannot_point_at_weaker_target(self):
        self.data['results'][0]['target'] = qg.PREFIX + 'AlreadyLocalCutoff'
        with self.assertRaisesRegex(qg.GateError, 'different proposition'):
            self.load()

    def test_duplicate_result_fails(self):
        self.data['results'].append(self.data['results'][0].copy())
        with self.assertRaisesRegex(qg.GateError, 'duplicate'):
            self.load()

    def test_missing_proof_module_fails(self):
        self.data['results'][0].update(status='source', declaration='MovingSofaQuantitative.nope',
                                       module='MovingSofaQuantitative.Missing')
        with self.assertRaisesRegex(qg.GateError, 'missing file'):
            self.load()

    def test_no_lake_no_receipt(self):
        self.data['results'][0].update(status='source', declaration='MovingSofaQuantitative.example',
                                       module='MovingSofaQuantitative.Example')
        self.load()
        with patch.object(qg.shutil, 'which', return_value=None):
            with self.assertRaisesRegex(qg.GateError, 'unavailable'):
                qg.verify(self.root, self.path, self.data, False, self.root/'receipt.json')
        self.assertFalse((self.root/'receipt.json').exists())

    def test_emission_is_an_exact_type_check_not_a_check_command(self):
        self.data['results'][0].update(status='source', declaration='MovingSofaQuantitative.example',
                                       module='MovingSofaQuantitative.Example')
        self.load()
        output = qg.lean_program(self.root, self.data['results'], 'TEST_ONLY')
        self.assertIn('Meta.isDefEq proof.type (mkConst t.getId)', output)
        self.assertIn('collectAxioms p.getId', output)
        self.assertIn('.thmInfo', output)
        self.assertIn('#quantitative_statement ' + qg.PREFIX + 'ExplicitCutoff', output)
        self.assertNotIn('native_decide', output)
        self.assertFalse((self.root/'receipt.json').exists())

    def test_injected_module_identifier_fails(self):
        self.data['results'][0].update(status='source', declaration='x\naxiom bad : False', module='X')
        with self.assertRaisesRegex(qg.GateError, 'invalid proof'):
            self.load()

    def test_planned_entry_cannot_smuggle_proof(self):
        self.data['results'][0]['declaration'] = 'MovingSofaQuantitative.example'
        with self.assertRaisesRegex(qg.GateError, 'planned result'):
            self.load()


class QuotientArithmeticTests(unittest.TestCase):
    def test_exact_finite_interval_formula_with_zero_and_negative_weights(self):
        count = 0
        for values in product(map(F, (-1, 0, 2)), repeat=3):
            for weights in product(map(F, (-2, 0, 1)), repeat=3):
                if not any(weights):
                    continue
                radius = max((abs(values[i]*weights[j]-values[j]*weights[i]) /
                              (abs(weights[i])+abs(weights[j]))
                              if weights[i] or weights[j] else F(0))
                             for i in range(3) for j in range(3))
                lo = max(values[i]/weights[i] - radius/abs(weights[i])
                         for i in range(3) if weights[i])
                hi = min(values[i]/weights[i] + radius/abs(weights[i])
                         for i in range(3) if weights[i])
                self.assertLessEqual(lo, hi)
                self.assertEqual(max(abs(values[i]-lo*weights[i]) for i in range(3)), radius)
                shifted = tuple(values[i] - F(7, 3)*weights[i] for i in range(3))
                for i in range(3):
                    for j in range(3):
                        self.assertEqual(values[i]*weights[j]-values[j]*weights[i],
                                         shifted[i]*weights[j]-shifted[j]*weights[i])
                count += 1
        self.assertEqual(count, 702)

    def test_zero_weight_obstruction_is_not_discarded(self):
        f, w = (F(7), F(1)), (F(0), F(1))
        radius = abs(f[0]*w[1]-f[1]*w[0]) / (abs(w[0])+abs(w[1]))
        self.assertEqual(radius, 7)
        self.assertEqual(abs(f[0]-100*w[0]), radius)


if __name__ == '__main__':
    unittest.main()
