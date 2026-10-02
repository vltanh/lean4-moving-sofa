# Toward uniqueness of the optimal moving sofa

## Scope

The existing `theorem1_1_1` proves optimality of Gerver's sofa.
`GerverParams.romik_unique` proves uniqueness of Romik's parameters in their box.
Neither statement says that every area-maximizing moving sofa is congruent to
Gerver's sofa. The equality-case development is a step toward that separate goal;
it does not assert geometric uniqueness or introduce a uniqueness axiom.

## Equality cases now available

Import `MovingSofa.Optimality.Equality` to use the new results.

For a quadratic functional `f` on a convex domain, with midpoint `m`,
`ConvexDomain.quadratic_deficit_identity` proves the exact identity

```text
f(x) - f(y) = -Df(x; y) + 4 * (f(m) - (f(x) + f(y)) / 2).
```

For a concave functional maximized at `x`, both terms on the right are
nonnegative. Equality of endpoint values therefore forces both a zero first
variation and a zero midpoint gap. The converse holds as well. This is stronger
than the nonpositive-variation condition used to prove maximality.

For `upperQL`, the proof of Theorem 8.3.8 decomposes the concavity gap into three
convexity gaps for `mamikonS`, `mamikonR`, and `mamikonL`:

```text
Q(c(x,y)) - ((1-c) Q(x) + c Q(y))
  = ((1-c) S(x) + c S(y) - S(c(x,y)))
  + ((1-c) R(x) + c R(y) - R(c(x,y)))
  + ((1-c) L(x) + c L(y) - L(c(x,y))).
```

The new `mamikonSegmentEquality_iff` extracts the equality case: the left-hand
gap vanishes exactly when all three nonnegative right-hand gaps vanish.
`MamikonSegmentEquality` records the three equalities separately.

Consequently, `upperQL_eq_gerver_iff` characterizes every competing triple with
Gerver's `upperQL` value by zero first variation at Gerver's triple and
`MamikonSegmentEquality` at the midpoint. Moreover,
`gerver_mamikonSegmentEquality` gives these equalities at every parameter in
`[0,1]`, and `upperQL_eq_gerver_on_segment` gives an entire segment of maximizers.
These are statements about functional values, not equality of triples.

The link to sofa area is not assumed: `ki_upperQL_eq_gerver_of_sofaArea_eq`
uses the existing two bounding steps to prove it for the canonical extension
`kiExtensionTriple` of a cap in `IsKi`. The resulting
`ki_maximizer_equality_conditions` supplies zero first variation and all three
Mamikon equalities whenever that cap's `sofaArea` is Gerver's area.

## Remaining geometric proof obligations

1. Analyze equality in the Mamikon convexity proof, especially `theorem7_4_2`,
   to derive constraints on the cap's support function. Equality of the three
   scalar functional gaps is not yet equality of support functions. In
   particular, the four terms inside `mamikonS` still need their own equality
   analysis.
2. Prove rigidity of those constraints with an explicit normalization or up to
   the appropriate rigid motions. The target should identify the cap/sofa;
   strict concavity of the entire auxiliary-triple representation must not be
   assumed without proof.
3. Connect an arbitrary maximizing moving sofa to these cap conditions while
   preserving enough geometry to recover the original sofa. The current proof
   of `gm_area_le` compares areas with selected maximizing caps; equality of
   those numbers alone does not identify the original sets. The balancing,
   rotation, monotonicity, and final set-recovery steps need their own equality
   arguments.

These obligations are not added as unproved Lean declarations.

## Validation

Run the existing checks:

```sh
lake build
lake env lean scripts/Audit.lean
python3 scripts/linkify_docs.py --check
python3 scripts/check_md_tables.py README.md REPORT.md
```

`MovingSofa.Tests.Equality` is included in the default library build. It tests
`f(x) = -x^2`, where a zero first variation does not imply equality of values;
a constant functional, which genuinely has distinct maximizers; the exact
deficit identity and equality characterization; and the Gerver-cap application.
The axiom audit explicitly imports all three new Lean modules. The existing
challenge statements, optimality proofs, and axiom allowlist are unchanged.
