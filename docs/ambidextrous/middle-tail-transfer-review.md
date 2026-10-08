# Review: variable middle supports, rough tails, and the remaining admission gap

**Unrestricted optimality remains unproved.** This continuation extends the previously fixed-middle clipping budget in two directions. MT/ME allow genuine middle-support changes while retaining reference collars and permitting signed rough-tail changes. CT removes the exact reference collars for inward changes, using curvature-weighted area pairing on a more general background. HC proves that a required lower tail-curvature hypothesis cannot be deleted.

Baseline: `1a1805f904ad8c67dfec182a12970c6c021dedd0`. All new results are written and self-reviewed, not independently refereed or kernel-verified. No theorem in this continuation puts an arbitrary saturated opposite-face body into an admitted background class.

## 1. Variable middle data and a preserved quantitative deficit

[MT1](movable-middle-tail-transfer.md) replaces the fixed reference middle by a curvature-controlled background B. It keeps reference support collars near the two horizontal normals and the vertical top normal, requires a half-height rectangle and niche height at most one half, and permits the middle supports to vary independently in the two caps.

The first needed verification is that changing the middle does not silently change the reference tail geometry. The hand proof shows:

- unit curvature makes both single-wall tangency abscissae nondecreasing;
- the exact end collars give strict same-sign contact velocities near the two end intervals;
- a two-case comparison prunes every late angle outside its inner-tail abscissa interval, and reflection prunes the early angles;
- consequently all non-tail positive niche values have an attaining parameter in the unchanged middle interval;
- the actual background tail is still the stated circle, because a single-wall global maximum and its strict companion gap are proved.

The altered cap U then retains B's middle supports but may change its top-normal supports without a density bound. Both inward and permitted outward changes are allowed. The companion gap at least 19/8 dominates the permitted upward first-wall displacement at most 1/99, so the signed pairing remains valid. No unchanged contact pattern is assumed for U.

The result is

$$\Psi(B)-\Psi(U)\ge L(U),\qquad L(U)=\int_a^b(1-A_U)dx.$$

[ME1](middle-energy-with-rough-tails.md) retains rather than spends the middle deficit. For the background, unit curvature and width greater than two give the ordinary identity Psi(B)=F(f,g)-m by SR1. Reference stationarity and convex positive/negative-part remainders yield

$$M/2-\Psi(B)\ge\frac7{50}\int_0^{\pi/2}
[(f'-f_*')^2+(g'-g_*')^2]dt.$$

The constant follows from the exact magnetic-square completion in AF and the Dirichlet inequality, including the factor that converts the gauge derivative to the ordinary derivative. It is not a sampled eigenvalue or a new optimization run.

Combining with MT for two independent altered caps gives

$$|E|\le M-\frac7{50}\sum_{i=1}^2\int|z_i'|^2,$$

where z_i measures only the background middle change. The entire positive clipping is paid by the separate face losses L(U_i). Crucially the derivative energy is not imposed on the rough altered support: the earlier point-face energy counterexamples are not ignored.

The note constructs genuine nonzero middle perturbations of either sign by smooth support bumps where the reference density lies strictly between zero and one. A uniform support perturbation at most 1/100 keeps the background corner height below 34/75<1/2. Thus the admitted middle variation is nonempty and infinite-dimensional, not an assertion based on an arbitrary numerical support tuple.

## 2. Exact reference collars can be removed for inward changes

[CT1](curvature-weighted-tail-transfer.md) starts from a general background cap of height one and width greater than two, with a positive top face, unit support-curvature density, a half-height rectangle, and full niche height at most one half. Suitable early/late signs and separated tail intervals are required. The vertical-adjacent tail densities must additionally be at least one half.

For an inward support defect e, the two relevant horizontal area Jacobians are

$$dx_{\rm inner}=(1-\rho)\sin t\,dt,\qquad
-dx_{\rm outer}=\rho\sin t\,dt.$$

Thus the niche saving is at most integral e(1-rho), while the outer cap loss is at least integral e rho. Their difference retains the nonnegative surplus integral e(2rho-1). The left tail has the same formula with cosine.

This proves

$$\Psi(B)-\Psi(U)\ge L(U)+J_B(U),\qquad J_B(U)\ge0,$$

without any exact reference collar or circular-tail hypothesis. Monotone absolutely continuous substitution handles densities that are merely bounded measurable, including constant-abscissa intervals of the inner tangency. No ordinary-perimeter convergence claim is used.

For independent backgrounds with the same projection and the same top-face interval, the actual envelope satisfies

$$|E|\le\Psi(B_1)+\Psi(B_2)-J_{B_1}(U_1)-J_{B_2}(U_2)
\le\Phi(W/2)\le M.$$

The last step is the existing analytic SR/AF chain on the curvature-controlled backgrounds. This does not require WV's maximizing-cap regularity, VE's limiting exposure, or Gerver's theorem. It also does not make the two actual altered caps maximize any one-turn objective.

The common background face interval matters for paying the two cross-clipping terms. It is not a statement that the altered caps have matching faces. Neither the existence nor the required ordinary-area comparison of these backgrounds has been proved for an arbitrary opposite-face body.

## 3. A real counterexample if the half-density threshold is removed

[HC](tail-half-curvature-obstruction.md) uses the explicit downward stadium cap

$$h_B(\theta)=1/4+(4/5)|\cos\theta|+(3/4)\sin\theta.$$

It has width 21/10, height one, top-face length 8/5, endpoint heights 3/4, and quarter density rho=1/4. Its maximum niche height is 31/20-3sqrt(2)/4<1/2. It therefore gives a genuine connected full-turn symmetric body with zero clipping.

Choose a nonnegative compactly supported smooth perturbation phi in a late same-sign phase and lower one support by epsilon phi. For sufficiently small epsilon the changed support is a genuine convex cap inside the old cap, with the same width and face and with unit curvature. Nevertheless the exact objective change is

$$\Psi(U_\varepsilon)-\Psi(B)
=\frac\varepsilon2\int\phi-\varepsilon^2\int(\phi'^2-\phi^2)>0.$$

The symmetric surviving body's ordinary area increases as well. Thus unit curvature alone does not make all inward tail changes lose area. This is an exact geometric counterexample to a stronger transfer premise, not a body above M. The deficit direction predicted by the Jacobians is correct: rho=1/4 gives 1-rho>rho.

Likewise the CT surplus cannot be assigned a nonnegative sign for outward defects when rho>1/2. MT's signed theorem uses equal half-density collars and a separate clearance test. The two domains are intentionally kept distinct.

## 4. What is still not covered

The fixed-middle restriction has been relaxed on stated domains, not eliminated for arbitrary bodies:

- MT/ME keep three exact reference collars and require the background middle density to be at most one.
- CT removes those exact collars for inward changes but requires an admissible global unit-curvature background, the lower half-density tail condition, and a common background face interval.
- No admissible background construction or global localization is supplied for arbitrary saturated positive opposite-face competitors.
- A small middle facet can violate background unit curvature. Merely being close to the reference does not meet these hypotheses.
- Partial turns still require actual angular coverage; a full canonical envelope is not automatically an upper enclosure of a body with only a partial witness.

The earlier PD/PS reduction does not remove these requirements. It preserves the full-turn supremum inside the positive opposite-face class, which itself has reference-area limits. It does not construct the new backgrounds or justify a uniform strict exclusion margin.

The next missing theorem is a valid background admission/improvement step, or an independent global ordinary-area inequality. These results do not justify announcing a completed local-neighborhood theorem, a completed unrestricted proof, or imminent closure.

## 5. Checks actually executed

The standard-library [checker](computer-assisted/check_middle_tail_transfer.py) ran under an external five-second timeout, taking approximately 0.105 seconds internally. The [record](computer-assisted/middle-tail-checks.json) reports 18 named checks: 578 convex scalar remainder cases, 768 exact integrand expansions, 420 end-angle pruning cases, 100 signed support pairings, 25 Jacobian comparisons and nine finite quadratic gains, with three stronger-claim controls.

The executed bytes match Git blob `5f906630534e424f04955485ab5bef633c4afcb6` and SHA-256 `6de07c9114fd61e226ef7d4031f92e3ddb49ad1bf9a69ac0ddef46352ed5569c`. The checks do not verify background admission, the continuum area substitution, reference stationarity or the earlier SR/AF chain.

One exploratory run tested 48 prescribed convex cuts of a polygonal reference cap, retaining the half-height rectangle. It ran under a five-second timeout in approximately 1.079 seconds. It did not find a defensible counterexample to a broader face-loss budget, and did not prove that budget. The reference diagnostic itself has an apparent half-value excess about 0.000193 due to finite-angle/polygon/spatial approximation; the largest cut-sample apparent excess, about 0.000147, is smaller. These outputs have no certified error sign and are not lower bounds above M. The complete source and outputs are preserved in the session bundle rather than reported as a certificate.

No long search or repeated refinement was run. The exact HC counterexample is analytic and does not rely on the inconclusive sampled cuts.

## 6. Execution and handoff

All substantive positive and negative findings are committed under docs/ambidextrous with `[skip ci]`. No CI, Lean/Lake compilation, dependency installation or manuscript build was used. The central statements are hand proofs; numerical work was confined to the short regression and exploratory runs described above.

Unrestricted optimality and independent verification remain unfinished. Keep PR #3 open and draft and preserve the distinction between proved budget transfer on an admitted domain and the unproved admission of every competitor.
