# Fourth-round failures, limitations, and corrections

These records distinguish unsuccessful arguments from counterexamples to the actual sofa conjectures. No CI or Lean build was attempted.

## 1. Width optimality alone does not cancel alignment loss

Suppose an unrestricted sofa is scaled by lambda<1 into the reverse class. The width-dependent quadratic bound gives area(lambda*S)<=F_e(lambda) at best. To deduce the original area is at most V(e) from this alone would require

    F_e(lambda)<=lambda^2 V(e)

near lambda=1. The sign is wrong:

    e[F_e'(1)-2V(e)] -> -6T0/(1+T0)<0,
    T0=tan(sqrt(3)/2)/sqrt(3).

Thus F_e(lambda)/lambda^2>V(e) for lambda just below one and small e. At e=pi/6, F_e'(1)-2V(e) is approximately -4.67977. This is a counterexample to the proposed bound comparison, not a feasible sofa beating the candidate. The regression test retains the failure.

A possible alternative must use more geometric information than the width polynomial. In particular, the flat contact segments and quantitative set stability can constrain a nonzero entry/exit mismatch directly. This different route is examined in `FLAT_CONTACT_ALIGNMENT.md`.

## 2. The sharpened crossing estimate still has a real cutoff

The full-width lower estimate for canonical vertical velocity changes sign when e exceeds arccos(sqrt(2)-1). For example, e=80 degrees and phi=1 degree make the reduced bracket negative. Therefore this sufficient estimate cannot establish the entire full-width reverse theorem at every obtuse bend. No feasible nonmonotone canonical-corner counterexample is claimed.

Uniform shrinking to width 983/1000 makes a weaker all-obtuse upper bound possible. That bound retains its factor 1/(983/1000)^2; it is not exact reverse optimality below the extended cutoff.

## 3. Bound-comparison roots are not the actual transition

The roots near 133.644346373 and 142.098382577 degrees compare H or the midpoint upper bound with V. They are not two new estimates of a single precisely located beta_c. The continuity theorem and ordered dominance prove a nonempty compact set of crossings of the optimal ALIGNED-class values between them. They do not establish a unique crossing, or an unrestricted global transition. Numerical local branches near 136.673 degrees do not close this gap.

## 4. Exact interval proofs can be inconclusive

The width certificate rejects covers with 1, 8, and 32 cells. The 8-cell monotonicity and early-exclusion certificates also reject an inconclusive cell. None is interpreted as proof of a false inequality. The retained passing covers use 256 cells for width and 512 for monotonicity and early exclusion. A deliberately wrong root bracket is rejected by the tests.

The formulas must avoid dividing by cos K at e=pi/2. The endpoint-stable version uses R=eta sin K/(cos K+eta sin K); treating tan K as a finite interval at that endpoint would be invalid.

## 5. Area or fixed-angle uniqueness alone does not give shape stability

Small missing area alone does not control Hausdorff distance for arbitrary compact sets. Nor does uniqueness at each fixed e justify a uniform limit as e tends to zero: coercivity can degenerate.

The proof instead establishes a uniformly rescaled quadratic deficit estimate, then puts the actual sofa inside an intermediate region whose missing area is controlled and whose geometry is trapped between homothetic copies of the explicit convex optimizer. An inball argument excludes macroscopic holes. The endpoint strip heights require nearby hallway poses to exclude leftward boundary spurs; the endpoint pose alone is insufficient.

These are analytic proof steps, not consequences of the numerical polygon tests. The constants in the Hausdorff estimates have not been numerically bounded or optimized.

## 6. Scope of verification and novelty

The local work includes exact-integer scalar certificates and separate floating-point regression tests. Passing them does not mechanically verify the cap-area identity, geometric majorant, set-stability argument, or alignment theorem. The draft still requires independent mathematical review.

The circular-notch family extends the familiar Hammersley construction and is not claimed new. Earlier numerical work by Xingyi He already found competing branches. A full priority review of the stronger analytic statements remains necessary; absence from a short search is not evidence of priority.
