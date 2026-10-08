# Higher-rank ordinary-area research: a genuine cut, and a quantified stop rule

**Status (October 8, 2026):** The unrestricted sharp
ambidextrous-area theorem is **not proved**. This line of
work deliberately avoids all \(P_J\) and curvature-repair
functional arguments. No Lean formalization was performed.

## Rigorously established this continuation

[FT-FRAC1](forbidden-triple-fractional-barrier.md)
exhibits an explicit feasible fractional point
\(z_C=2/3\) for **every** bare occupancy LP whose only
geometric inequalities are the distinct-cell forbidden
triples \(z_P+z_Q+z_R\le2\). On a full possible
\(W\times1\) rectangle the objective is \(2W/3\).
For \(W\ge5/2\), this is \(5/3>M\).
The proof is independent of grid size, angular sampling
and LP optimization; the upper incoming strip also
excludes dangerous repeated-point pair cuts.
Thus *triple-only* refinements cannot by themselves
prove the conjectured sharp bound throughout
the competitive width class.

[FCR1](four-cell-rank-cut.md) supplies a concrete,
**strictly stronger** inequality
\(z_0+z_1+z_2+z_3\le2\) on four disjoint
positive-area squares of side \(1/12\).
Every three of the four squares are incompatible
in one of four actual full-turn rational hallway
frames. The minimum worst-case dot-product
margin is exactly \(1/39>0\); this holds for
**every real point** in the squares.
The 53-line [rational verifier](computer-assisted/check_four_cell_rank.py)
passed with source Git blob
482405a2956ee5f59c2f350fdc61402fe6156be5.
The fractional \(z_i=2/3\) assignment is
excluded by this new inequality.

These are methodological advances in **sound
geometric constraints**, not new absolute upper
bounds for ordinary sofa area.

## Width-uniform zigzag obstruction

[ZZ1/ZZ2](parametric-zigzag-four-point-exclusion.md) extends
the four-cell theorem to every \(W\ge2\): four alternating
points at horizontal offsets \(0,W/3,2W/3,W\) cannot have
any three simultaneously present in a complete-two-turn sofa.
The exact point obstruction holds already for span \(W>15/8\).

The positive-area version uses square side \(1/64\) for
all \(W\ge2\) (minimum exact margin \(31/960\)),
or square side \(1/12\) for all \(W\ge23/10\)
(minimum exact margin \(1/58\)).
Both ranges were certified by
[the exact parametric checker](computer-assisted/check_parametric_zigzag_rank.py),
which proves the required rectangle dot-product minima have
strictly positive affine slopes as functions of W.
Committed checker Git blob:
0f981847c17f2c37a7c8d40dfff15c64d413c970.

This strengthens the geometric cut at widths near Romik's
candidate, but it does **not** improve the current coarse
LP area objective. The new acceptance gate remains
a rigorous global *area aggregation*, not a fourth
isolated configuration lemma.

## Numerical controls: why the new inequalities do not yet close an area gap

A bounded exploratory diagnostic on a uniform
\(30\times12\) partition of the
\(W=5/2\), \(H=1\) rectangle used both
conventional handed turns, all nine primitive
Pythagorean triples and their interchanged
orientations (18 frames per turn).
It constructed 37,188 robust forbidden
triples and identified 574 four-cell complete
subhypergraphs (rank-two conflicts).
Eight vertex-disjoint four-cell conflicts
were found; an exact search on this
*particular grid and orientation list*
found no five-cell complete subhypergraph.

In exploratory floating-point HiGHS:
- The bare triple LP objective was
  \(2.0347222\ldots\) in ordinary-area units.
- Adding **all 574 four-cell rank cuts**
  left the optimum at \(2.0347222\ldots\).
- The corresponding binary occupancy MILP
  optimized to \(2.0277777\ldots\).
- Adding **columnwise interval-occupation
  constraints** (required by vertical
  filling of canonical full-turn envelopes)
  did not improve that binary objective.

These are **diagnostics, not exact rational
global certificates**. In particular the
geometry used here is intentionally coarsened
to whole cells; a numerical solver's
global-optimality flag is not itself a
continuum proof. The data show that the
current failure is not primarily the
two-thirds fractional assignment or
lack of clique cuts: *the coarse spatial
forbidden configurations still admit
far too much ordinary area.*

The result should **not** be advertised as
a stronger numerical sofa bound. The
existing external verified global bound
\(353/200=1.765\) is much smaller.

## Strategic implications

1. Do not keep extending the original CF2
   triple-only LP and expect its limit to
   prove the sharp value on widths \(W\ge2.5\):
   FT-FRAC1 supplies a mathematical barrier.
2. Do not assert that rank-four cuts alone
   repair this: FCR1 is sound but the complete
   \(30\times12\) diagnostic shows no
   objective improvement.
3. To make progress near Romik's width,
   retain *actual mutually supporting occupied
   witnesses* at a finer geometric level.
   Alternatives worth **falsifiable tests**
   include full component-aware exact
   per-offset polygon-area branch-and-bound,
   a proof of a rank inequality for much
   larger region families, or exact continuous
   fiber constraints coupling adjacent
   abscissae.
4. For each proposed method the acceptance
   criterion is an **exact, independently
   replayable ordinary-area upper bound
   improving the best existing bound on
   a substantial unresolved region**.
   A certificate of local non-occupancy,
   a larger repository, a running optimizer,
   or another unchanged LP objective does
   not meet that criterion.

The previous **wide-width bound**
[TS-CERT1](two-switch-global-wide-area-certificate.md)
remains a separate genuine partial result
for \(W\ge2.822\). This continuation
does not extend that bound to the widths
around Romik's candidate, nor does it
complete arbitrary partial turns.
