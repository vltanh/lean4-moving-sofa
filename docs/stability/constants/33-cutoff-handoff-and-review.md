# Explicit cutoff: handoff and review map

This continuation starts at `0ae744d727e77876cf148d19d0d0012d56e1bd8b` in PR #10.
It completes the local-radius part of the WRITTEN ANALYTIC argument. No Lean
source, manuscript, bridge, Challenge, workflow, or library configuration is
changed. No Lean, Lake, CI, remote build, or TeX compilation was run.

## Final statement

Under horizontal-midpoint/top normalization, the proposed quantitative theorem is

    0<=epsilon=M-|S|<=10^(-600)
       ==> d_H(S_c,G)<=2.3*sqrt(epsilon),
           |S_c triangle G|<=50*sqrt(epsilon),
           pi/2-omega<=3.1*epsilon

for every original moving sofa and every admissible reduced motion angle.
These are actual-set Euclidean and finite-area estimates. No input smoothness,
injectivity, monotonicity, or eligibility of an unspecified envelope is assumed.

Read [32-explicit-sharp-cutoff.md](32-explicit-sharp-cutoff.md) for the assembly.
The statement no longer leaves an entry radius or common deficit threshold
unspecified. It is not yet independently reviewed or formally verified.

## Dependency map

1. **Global entry:** notes26--27 provide the explicit coarse bounds
   `3000000*epsilon^(1/12)` for shape and `500*epsilon^(1/6)` for angle. Their
   penalized variation and polygon-limit arguments are analytic inputs, not
   certified by the new scalar checker. The sharp local theorem is not used
   to prove its own entry condition.
2. **Cap neighborhood:** note29 proves that support error at most10^-40 gives
   the actual canonical triple, positive core/arm margins, separated cuts,
   niche containment, and the geometric inequality A(K)<=Q<=M.
3. **Terminal neighborhood:** note30 uses two explicit angles,1/1600000 and its
   complement, to exclude the interior low floor band. Together with numerical
   top-face/niche-foot localization, it gives the trapezoidal loss and the
   complementary missing-area budget whenever alpha<=10^-20.
4. **Reference recovery scales:** note31 gives a translated-sector radius
   10^-20 at aperture1.53, and a Euclidean normal estimate for support-plus-slack
   error at most10^-10. The normal Taylor calculation uses depth10^-8.
5. **Final budget:** note32 applies the centered cap coefficient1.001, orthogonal
   erosion, whole-sector area, and the direct roof-band area estimate. Exact
   arithmetic verifies all the chosen numerical margins simultaneously.

At the proposed cutoff, coarse entry gives support error at most3*10^-44 and
angle at most5*10^-98. These are below the fixed10^-40 and10^-20 local thresholds.
After the local certificate applies, the refined cap/slack bounds have order
sqrt(epsilon) and epsilon, satisfying the much smaller recovery scales.

## Geometric details explicitly reviewed in this continuation

- **A supporting face is not a selected smooth point.** Note29 bounds every
  exposed point by the two neighboring support inequalities. It treats the
  reference top segment separately, using one-sided support expansions. No
  top contact is assumed to lie near a particular endpoint of that segment.
- **Reflection does not assume symmetry of the competitor.** A left-hand
  estimate is obtained by applying the right-hand argument to the reflected
  competing cap and the symmetric reference. The support-error hypothesis is
  preserved. This is how note29's left-cut argument and note30's second floor
  witness are used.
- **Curvature gives angular control.** The bound2^20 in note31 bounds total
  tangent-angle variation per unit arclength on a regular piece, not merely
  the chord distance between two unit tangent vectors. It follows by integrating
  the absolute curvature bound. This supplies the explicit angular reserve
  used in the corner and smooth epigraph charts.
- **Other boundary branches are excluded.** The32-Lipschitz upper/lower graphs,
  quantitative separation from the outer corners, and vertical gap estimate
  rule out a second boundary in the chosen chart. A curvature bound alone would
  not establish a uniform embedded chart.
- **Outside-cap recovery keeps the floor constraint.** If a nearest point of
  Gcap lies in its niche, its upper-wall margin is positive. It is either in
  the interior of Gcap or on its floor with only a downward exterior normal.
  Neither can be the nearest cap point of a point outside Gcap with nonnegative
  height. Thus the nearest cap point used in forward recovery belongs to G.
- **The input sofa need not be contained in U.** The terminal proof retains
  g=|S minus U|, so the missing area is epsilon-e+g rather than epsilon-e.
  The local cap is not substituted for the actual input in the conclusion.
- **The full-height rectangle is in the convex hull.** Note27's previous wording
  put the entire rectangle in the actual sofa. This was false because of the
  niche. It is corrected there: its four corner points belong to G and suffice
  for the width comparison. The coefficient41200 and subsequent modulus do
  not change. The same witness argument handles zero-deficit terminal angles.

These checks address particular proof issues; they do not replace an independent
review of the entire research branch.

## Reproducible numerical certificate

The committed files are

    effective_entry/check_cutoff_radii.py
    effective_entry/replay_cutoff_radii.py
    effective_entry/cutoff-radius-summary.json

Run

    python docs/stability/constants/effective_entry/replay_cutoff_radii.py \
      --expect docs/stability/constants/effective_entry/cutoff-radius-summary.json

The replay executes the checker afresh before comparison. The final run passed
5440 checks:18 scalar reference checks,5120 complete phase-cell inequalities,
256 extended-arm cell inequalities,41 exact rational local/cutoff margins,
three exact power identities, and two negative controls. The reference cells
cover their entire parameter intervals, not just mesh sample points.

Acceptance uses integer90-bit dyadic intervals for reference trigonometry and
exact Fractions for the radii and cutoff. In particular10^-600 is not rounded
to zero in the interval grid. Full rational output is regenerated locally;
the committed compact receipt hashes its complete invariant contents.

Verified local/committed source identifiers:

| File | Git blob |
| --- | --- |
| `check_cutoff_radii.py` | `ee82b0f3817efd6137e21a8e32afba082fce3d87` |
| `replay_cutoff_radii.py` | `a59e242bad0ef605c39e1e616d292033e7e40e84` |
| `cutoff-radius-summary.json` | `ca353f283f1cf04c1e96de7777d0da5a3d0ead01` |

Full invariant report SHA256:
`5d1a503086145b5e521e81692f3dc79ba3f74eb0e81017bd0710b80a148b9061`.
The existing interval backend is unchanged. Earlier critical-cone, trial-energy,
and branch-and-bound reports were not rerun or relabelled by this continuation.

## What may be claimed, and what may not

The contribution is an explicit radius table and a complete analytic numerical-
cutoff assembly, supported by executed exact arithmetic for its reference and
scalar inequalities. There is no remaining existential local radius in this
assembly. The arbitrary-input entry step remains the analytic penalized-
regularization argument already developed in notes26--27.

Do not describe the Python report as checking the whole moving-sofa theorem.
It does not verify variational arguments, limiting measures, contact topology,
or arbitrary-set epigraph geometry. No new Lean theorem or kernel-audit result
is supplied. Independent mathematical review should give priority to notes26--27
and the boundary-chart argument of note31 before the paper advertises a checked
explicit cutoff.

The cutoff10^-600 is sufficient and deliberately conservative. It is not a
sharp threshold or a recommended numerical optimizer tolerance. The coefficient
2.3 is likewise not claimed optimal. The full-Q asymptotic interval0.922<C_Q<=0.93
of note25 is a different theorem on cap triples and was not needed to obtain
this original-sofa area cutoff. The previously quantified Q-deficit threshold
10^-18 must not be substituted for it.

Manuscript integration remains a separate session. This branch's original
proofs and formal-conjectures interface remain intact.
