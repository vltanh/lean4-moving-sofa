# Handoff: punctured sofas and the improved cap constant

## Status and integration boundary

The requested PR #8 additions now have intended Lean proof-source assemblies.
**No Lean, Lake, CI, remote build, or TeX compilation was run.** These are not
kernel-checked theorems, and elaboration, API, tactic, and mathematical review
remain necessary. No new axiom, `sorry`, or assumed final stability estimate
was introduced in these additions.

This work started at `fa4a20e2dde9f80c3a2034bd44e403d0bb06af4e` and stays on
`research/quantitative-stability`. Manuscript integration is intentionally left
to the separate session. The coercive-framework refactor belongs to PR #9, not
this PR. Baek's formalization, main uniqueness, the bridge, Challenge, existing
solution, and manuscript files have not been changed by this continuation.

The older descriptions in the original notes and FORMALIZATION.md that say
sharpness is only analytic or that 80 is the only available cap coefficient are
superseded by this handoff. The original declarations with coefficient 80 remain
available for compatibility; they have not been silently strengthened.

## 1. Punctured Gerver family

Read these modules in order:

- `PunctureTopology.lean`: removing an open region with connected frontier from
  a closed connected containing set preserves connectedness. A disk satisfies
  this hypothesis in dimension two. No path-connectedness assumption is added.
- `EuclideanDisks.lean`: Euclidean circles/disks in the pair coordinates, using
  the existing measure-preserving coordinate bridge. Disk area is exactly
  `pi*r^2`, not the area of a ball for the product sup norm.
- `PunctureMetric.lean`: inherited original hallway motion, the retained circle,
  the identity-aligned distance r, and the actual infimum over rigid alignments.
- `RigidInterior.lean`: any fixed interior point of a compact set is retained by
  every sufficiently close rigid copy of that set. The proof extracts a compact
  subsequence of cosine/sine coefficients and translations, not unbounded angles.
- `PuncturedSofa.lean`: combines those facts for Gerver, including the lower
  distance bound for every orientation-preserving rigid alignment.
- `SharpExponent.lean`: rules out every exponent above one half.

The headline family theorem is `punctured_gerver_family`. There are p and r0>0
such that for every 0<r<r0, the set

    S_r = gerverSofa P minus openEuclideanBall p r

is an actual closed connected moving sofa and satisfies

    sofaDeficit P S_r = pi*r^2,
    rigidHausdorffDistance S_r (gerverSofa P) = r.

The theorem also supplies the stronger witness form: identity alignment attains
r, and every `EuclideanClose d S_r (g '' G)` implies r<=d. This ensures that the
infimum statement is neither a fixed-alignment shortcut nor a totalized empty
infimum.

`no_hausdorff_exponent_gt_half` quantifies over each exponent a>1/2, every real
constant C, every positive threshold epsilon0, and every rigid alignment. It
produces a moving sofa with positive deficit below epsilon0 that violates the
proposed bound. `rigid_distance_not_higher_order` states the same obstruction in
terms of the rigid-distance infimum.

These results do not prove exponent sharpness for symmetric-difference area,
for cap distance, or for monotone sofas. They compare closed sets, not boundaries.

## 2. Improved cap coefficient

The stronger API is in `SharpCapDistance.lean`:

    sharp_wide_cap_support_bound
    sharp_ki_cap_support_bound
    sharp_wide_cap_distance_bound
    sharp_ki_cap_distance_bound
    wide_cap_distance_bound_2002
    ki_cap_distance_bound_2002

The wide-domain statement is

    EuclideanClose ((2 / cos P.phi) * sqrt(M - wideUpperQ P.phi xi))
      K (shiftedReferenceCap P.cap K).

It uses the same enlarged nonsmooth domain and pinned horizontal translation
as the previous coefficient-80 theorem. The Ki corollary replaces the Q deficit
by `M - sofaArea (pi/2) K`. The source-box corollaries use the rational coefficient
1001/500, justified by

    2 / cos(phi) <= 2500/1249 < 1001/500 = 2.002.

This is a cap constant, NOT a computed constant for arbitrary nonconvex sofas.
The global theorem still has existential constants. The sharper cap estimate
is available as an additive theorem; existing downstream proofs using 80 remain
valid without edits.

### Proof mechanism

`SharpIntegralControl.lean` packages an estimate `value^2 <= kernelNorm*energy`.
When independent residual intervals are combined, their squared kernel norms
and energies add, avoiding the repeated triangle-inequality losses in the old
mass estimate.

`TrigKernelIntegrals.lean` integrates the actual squared trigonometric kernels.
`SharpReconstruction.lean` derives the actual support evaluation formulas.
For the middle interval a product derivative replaces the double integral:

    B_A(u) = (A + cos u) / sin u,
    (B_A f)' = -f - B_A r4.

The two pieces of the last residual are split at pi/2+t and their disjoint
energies recombined. They are not counted twice. The apparent singular endpoint
at pi is treated by the pinned value f(pi)=0, not an unjustified improper integral.

`SharpKernelNorms.lean` identifies the kernel square integrals with the four
closed forms from analytic note 01. `SharpEvaluation.lean` uses the already
proved bound on those forms to obtain `sharp_four_arc_coercivity`. Finally the
actual cap residual identities discharge its analytic hypotheses in
`SharpCapDistance.lean`.

No hypothesis saying that the kernel norm has the desired value, or that the
support already satisfies the desired estimate, remains in those final cap
statements. Optimality of this coefficient in the abstract pinned residual space
is still the separate analytic witness of note 01; no claim is made of a best
constant among feasible caps or after optimizing translations.

## 3. Non-Lean validation

Run separately, without Lean or Lake:

    python docs/stability/check_sharpness.py

The recorded run used Python 3.13.5 and mpmath 1.3.0 at 60 decimal digits.
All 179 numerical formula comparisons passed with tolerance 1e-45. They cover
actual kernel-square quadratures, primitive derivatives, reconstruction for
three independently chosen functions, the product identity, interval junctions,
the rational coefficient, and the puncture power-law identity. A sampled norm
bound was also checked over 301 directions for each of five cut angles.

The tested script has Git blob SHA
`b08fabd8fc060a282e2111e24f0e104870f549bb`, matching the committed file.
`sharpness-checks.json` is the exact recorded output. These checks do NOT test
Lean syntax, import resolution, proof terms, topology, or rigid-orbit compactness.
They are not interval certificates or replacements for proof review.

Separate fix commits retain source-review corrections: inverse-distance
orientation, first-arc integrand normalization, scalar-power reassociation,
trigonometric denominator cancellation, and the nontrivial-space requirement
for disk frontiers. They were not discovered by a Lean compiler.

`All.lean` now imports all twelve new modules. The old source-manifest JSON
records its earlier checkpoint and is not a validation of this enlarged root.

## 4. Suggested integration checks when compilation is authorized

Check the puncture chain and sharp-kernel chain independently before the global
import root. Check standard axioms and the absence of unresolved proof terms.
Retain the circle and all rigid-alignments quantifiers in the paper statement.
Do not advertise the coefficient 2.002 as a global-sofa constant or an optimized
free-translation cap constant. Keep the paper's verification-scope statement
unchanged until the new source has actually been checked.
