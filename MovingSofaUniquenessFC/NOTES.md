# Shared moving-sofa uniqueness and the exact upstream reference

## Source status

Start with [MovingSofaUniquenessFC/Final.lean](../MovingSofaUniquenessFC/Final.lean),
[the concrete shape correspondence](../MovingSofaUniquenessFC/Bridge/ReferenceShape.lean),
and [the mathematical explanation in note 22](../docs/uniqueness/22-reference-correspondence.md).

The final source now contains the exact requested declaration:

```lean
theorem volume_eq_sofaConstant_iff_congruent_gerversSofa (s : Set ℝ²)
    (hs : ∃ m, IsMovingSofa s m) :
    volume s = sofaConstant ↔ ∃ g : E(2), s = g '' gerversSofa := by
  exact Canonical.volume_eq_constant_iff_congruent hs
    isMovingSofa_gerversSofa sofaConstant_eq_volume_gerversSofa
```

Its concrete reference is the integral-defined `gerversSofa` from the inspected
formal-conjectures file, not a differently defined reference under the same
name. Both reference facts used in this final term now have local explicit
proof bodies. The full parameter existence-and-uniqueness theorem used to
choose its constants also has a local analytic proof.

**All this is uncompiled source.** No Lean, Lake, CI, Comparator or independent
checker was executed. Written proof bodies are not a claim of successful
elaboration, a computed admission-free axiom closure, accepted upstream
submission, or Palomar certification. Source/API/tactic errors, mathematical
errors and version-porting problems have not been excluded by execution.

## Exact correspondence, without circular use of sofa uniqueness

The central bridge is stronger than congruence:

```lean
theorem coordinates_gerversSofa_eq_paper {P : MovingSofa.GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    coordinates '' MovingSofa.gerversSofa = MovingSofa.gerverSofa P
```

It identifies the actual sets under the canonical coordinate map. The proof
has four parts:

1. **Full-domain parameters.** `ReferenceUniqueness.lean` proves uniqueness
   throughout `0<=phi<=theta<=pi/4`, `A,B>=0`, by analytic localization and
   monotone residual separation. `ReferenceFromPaper.lean` constructs an
   actual solution from the existing paper witness. `ReferenceExistence.lean`
   combines them into the exact nested-tuple `existsUnique` statement.
2. **Literal integral formulas.** `ReferenceRadius.lean` proves integrability
   and identifies the reference radius with the paper contact derivative.
   Breakpoint values agree almost everywhere, not falsely pointwise.
   `ReferenceContacts.lean` integrates that derivative to obtain the actual
   reference X,Y and their normalizations.
3. **Path conventions and endpoints.** `ReferencePath.lean` proves
   `R_t p(t)=x(t)`: the reference translation is BEFORE rotation and the paper
   translation is AFTER it. It proves `p(0)=0` and carries the final vertical
   hallway separately. All intermediate hallway intersections are preserved.
4. **Canonical orientation.** `Bridge/ReferenceRotation.lean` verifies the
   coordinate matrix of the actual `EuclideanGeometry.o.rotation` used by
   upstream. `Bridge/ReferenceShape.lean` then transfers the literal reference
   through coordinates and obtains the exact set equality above.

None of these correspondence modules uses the new sofa shape-uniqueness
argument. The global parameter proof does not silently replace the upstream
domain by the paper's small box; membership in that box is deduced only after
the full-domain uniqueness theorem has been established in the source.

## One proof for publication and submission

`MovingSofaUniquenessFC/Model.lean` contains the canonical hallway, the induced topology
on affine isometries, the identity-start motion structure, and the ENNReal
supremum. Its mathematical definitions are those of the inspected upstream
source. It imports Mathlib only.

The paper presentation is retained with explicit `MovingSofa.Paper` names for
the colliding hallway and moving-sofa predicates. `Bridge/Motions.lean` proves
the exact relationship, including initial placement, and equality of the two
supremum problems independently of uniqueness. The coordinate map is a
volume-preserving homeomorphism, not an isometry for the ordinary product norm.

The same core uniqueness proof supplies all four endpoints in `Final.lean`:

- `MovingSofa.Canonical.maximizers_congruent`;
- `MovingSofa.Canonical.volume_eq_constant_iff_congruent_paper_gerver`;
- `MovingSofa.Canonical.exists_unique_maximizer_modulo_isometry`;
- `MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa`.

There is no extra smoothness, balancedness, injectivity or regular-closedness
assumption on a competing sofa. Set recovery concerns the original closed set,
not merely its cap, envelope, area or equivalence modulo null sets.

## Source restrictions and historical alternatives

No new reference proof uses `decide +kernel`, `native_decide`, an external
root-checking process, a generated proof-source step or a custom axiom.
The analytic estimates are written using ordinary algebra and calculus proofs.
A transitive source-policy audit and elaborated axiom audit have not been run;
these are distinct from the absence of those mechanisms in the new scripts.

The previously considered external reference provider used a decision-kernel
certificate and was rejected. Its dependency remains removed. [Note 21](../docs/uniqueness/21-reference-dependency-audit.md)
records that historical finding; [note 22](../docs/uniqueness/22-reference-correspondence.md)
records the analytic replacement. No source relocation or exporter is needed.
The old exporter, its tests, and generated insertion fragments remain deleted.

## Comparison configuration, examples and version boundary

[comparator.reference-uniqueness.json](../comparator.reference-uniqueness.json)
is configured to compare the exact concrete-reference target, the full
parameter theorem, and the defining constants/path/hallways against the
independent `SofaSubmission.ChallengeUniqueness` fixture. The allowed axioms are
`propext`, `Quot.sound`, `Classical.choice`, with the independent checker enabled.
It has not been run. Configuration alone is not validation or certification.

[comparator.shared-uniqueness.json](../comparator.shared-uniqueness.json)
retains the reference-independent comparison. The Challenge fixtures contain
intentional statement placeholders but are not imported by the solution.

The new [reference examples](../MovingSofaUniquenessFC/Tests/Reference.lean) record
full-domain parameter existence, exact coordinate set equality, the rotation
convention, concrete motion/attainment and the exact final theorem type. These
examples are unexecuted; no test-pass claim is attached to them.

The source remains on Lean `v4.35.0-rc3`; the inspected upstream checkout used
`v4.33.1`. No version pin has been changed here and the port remains untested.
The uniqueness/submission libraries remain opt-in; the original paper default
build targets and axiom allowlists are unchanged.

For the current dependency map and verification boundaries see [OBLIGATIONS.md](OBLIGATIONS.md).
