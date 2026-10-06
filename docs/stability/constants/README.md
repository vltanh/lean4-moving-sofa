# Explicit global stability coefficients

Base paper checkpoint: `a8f7719fd43fa91b223d9f6c0eb53594e5a95716`.
PR #8 is merged; this constants branch is separate from the coercive-route PR #9.
The first six constants commits, ending at
`4acfa639976ce41eab7ae77f2485591b9e3f6bb9`, were inherited. Their simpler bounds
are retained in the research history and notes.

## Strongest written analytic result

There exists a positive threshold epsilon0 such that every original moving sofa
with deficit epsilon=|G|-|S|<epsilon0 satisfies, after the prescribed normalization,

| Quantity | Explicit coefficient |
| --- | --- |
| Euclidean Hausdorff distance | `(61/2) * sqrt(epsilon)` |
| Symmetric-difference area | `100 * sqrt(epsilon)` |
| Missing angle of every admissible reduced motion | `(31/10) * epsilon` |

The simple integer Hausdorff coefficient 31 works without the final small-surplus
refinement. The strongest 30.5 uses the improved terminal trapezoid. These are
uniform bounds for the unrestricted class of near-optimal sofas, not claims of
optimal coefficients or bounds valid at every area deficit.

**Status:** written analytic proof plus supporting uncompiled Lean lemmas.
The full numerical-coefficient theorem has NOT been assembled or checked in Lean.
No Lean, Lake, CI, remote build, or TeX compilation was run. The new source may
contain elaboration, tactic, API, or mathematical errors pending review.

## Main improvements

The cap and missing set spend complementary portions of the deficit. Orthogonal
hallway normals reduce the erosion allowance from `2*delta` to `sqrt(2)*delta`.
Recovery uses the full surviving disk and its exact area, rather than a smaller
inscribed square.

Phase-wise reference velocity bounds improve the roof Lipschitz coefficient
from 26 to 9.45. An adaptive hallway angle balances the two inner-wall first
variations and improves the reference roof recovery factor to 10.2. Euclidean
interior-ball geometry then supplies the numerical ratio `100/1051`.

For area distance, compare the competing envelope directly with the reference
cap and niche: a convex square-parallel layer plus a thin roof band suffices.
This avoids multiplying the global Hausdorff constant into the area estimate.
A trapezoidal terminal-floor slice also improves the angle coefficient to 3.1
and keeps the surplus outside the full-angle envelope very small.

## Read in this order

1. [07-global-constants.md](07-global-constants.md): the strongest theorem and
   its assembly, including both deficit budgets and the full-angle subclass.
2. [06-phase-aware-reference.md](06-phase-aware-reference.md): the new reference
   slope, adaptive-angle slack argument, and explicit interior-ball ratio.
3. [08-effective-reference-scales.md](08-effective-reference-scales.md): numerical
   height, ball scale, outer margin, and clipping threshold, with the remaining
   effective-entry gap isolated explicitly.
4. [05-area-and-angle.md](05-area-and-angle.md): the direct area argument and
   improved terminal trapezoid. Note 07 substitutes the sharper reference data.
5. [09-audit-and-limitations.md](09-audit-and-limitations.md): negative results,
   formalization scope, lower bounds, and validation limits.

The earlier notes document the progression: shared deficit and exact disks in
01, the inherited reference estimates in 02, then the simpler Hausdorff 80 and
area 204 bounds in 03--05. They are intermediate estimates, not contradictions
of the stronger result.

## Explicit coefficient is not an explicit global threshold

The new analytic reference scales can be fixed at

    roof height <= 2/3,
    interior-ball scale = 1/24,
    outer-wall margin = 1/5,
    roof clipping threshold = 1/2040000.

A deficit of at most `10^(-14)` satisfies the subsequent recovery inequalities
once the local cap and terminal certificates apply. It has NOT been proved to
guarantee those certificates for every sofa. The missing numerical global
separation/entry bound is not supplied by the existing compactness argument.
Accordingly epsilon0 in the unconditional result remains existential.

The punctured-sofa family gives the necessary lower bound `C >= 1/sqrt(pi)`
for any unrestricted rigid-Hausdorff square-root coefficient. The new upper
coefficient 30.5 is not asserted to attain that infimum.

## Source and actual checks

`MovingSofaStability/Constants.lean` is the dedicated review root. It collects
exact deficit identities, orthogonal erosion, scalar phase and numerical
budgets, conditional actual-set recovery, direct roof-band localization, and
the puncture-based coefficient lower bound. The unconditional numerical theorem
still needs the geometric reference adapters and final assembly; these are not
hidden in an assumed final-stability interface.

The local command

    python docs/stability/constants/check_global_constants.py

passed 3,212 assertions, including exact rational budgets and 128 exact polygon
square-dilation identities, plus sampled high-precision reference, adaptive-angle,
and deficit-splitting checks. The tested script's Git blob SHA is
`6ec33e06e8a6425e8179d5103cbc749068a6935d`, matching the committed source.
[global-constant-checks.json](global-constant-checks.json) is the recorded output.
These diagnostics do not check Lean, topology, or the global entry gap.

The faithful Baek library, original uniqueness, bridge, Challenge files,
canonical Solution, manuscript, workflows, and lakefile are unchanged. The
merged paper branch already builds the stability-library glob by default, so
new files will be included when that target is eventually compiled; no claim
is made that they are excluded from that build. All research commits use
`[skip ci]`, and the paper's existing verification claims are not extended.
