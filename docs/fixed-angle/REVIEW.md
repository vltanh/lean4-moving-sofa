# Proof and certificate review; retained failure log

This is an internal mathematical and implementation audit, **not an independent referee report or proof-assistant certificate**. The all-angle assembly is a computer-assisted research proof draft. Every angle in `[0,pi/2]` is accounted for, but the analytic reductions, the ordinary-Python verifier, and its arithmetic model remain explicit dependencies requiring independent review.

No Lean, `lake`, CI, workflow dispatch, axiom audit, or TeX compilation was run. Every research commit uses `[skip ci]`. Changes are confined to the separate fixed-angle research directory.

## Current theorem and coverage boundary

[all-angle-optimality-uniqueness.tex](all-angle-optimality-uniqueness.tex) is the current assembly. It proves unrestricted optimality and uniqueness at every fixed net angle using three overlapping continuation components above one radian:

- an explicit analytic bridge on `(1,1.01]`;
- a parameter-uniform interval cover of `[1.01,1.5706]`;
- a regular endpoint branch whose image covers `[1.5706,pi/2)`.

The exact result on `[0,1]` is analytic. The right-angle endpoint is the **separate companion Gerver theorem**, not an extrapolated numerical root or an application of strict open-angle concavity at its degenerate endpoint. The open-angle normalization fixes translation, but at `pi/2` horizontal translation is not fixed by the coincident endpoint support directions. The endpoint conclusion is uniqueness up to congruence.

Earlier notes stating that their individual results do not solve the full interval describe their original scope. The README, PEM and all-angle assembly describe the current cumulative result. The earlier negative results remain valid and are essential to distinguishing the new optimizer from Baek's relaxed candidate above one radian.

## Imported inputs and quantifiers

The analytic route imports the companion's fixed-angle cap/monotonization identities, penalized selection, and floating/pinned first variations at commit `1ade045936f32cf76572ee668ed8aa1627772bde`. Those statements already quantify over the prescribed angle; they are not inferred by changing a right-angle hypothesis.

Selection targets **any chosen positive maximizing cap**, not just a selected balanced maximizer. This quantifier permits the final equality argument to classify all maximizers. The new fixed-angle curvature passage, arm estimates, global cut geometry, strengthened lifting, cap attainment and equality recovery are written out in the research notes.

Baek's *A Conditional Upper Bound for the Moving Sofa Problem*, arXiv:2406.10725v1, is credited for `A_1`, `K_(omega,1)` and its relaxed value. Constructing a cap with a specified boundary measure is not treated as proof that it is the only relaxed maximizer; strict quadratic gaps supply that conclusion. The support/contact approach follows Romik and Baek. The final Gerver theorem is not an input to the new open-angle continuation; it is explicitly used at the right-angle endpoint only.

## Definitions checked

The prescribed angle is the net change of a continuous angular lift, from zero to `-omega`. Backtracking is permitted. Intermediate-angle exclusions use the intermediate value theorem and do not require monotone rotation of the original motion.

Two upper support equations fix the open-angle translation because `cos(omega)>0`; the width bounds then imply containment in the endpoint parallelogram. Arbitrary sofas need not touch both lower walls. This normalization is linear algebra, not an argument for uniqueness of different bodies.

Niches use the fan intersected with the union of open quarter-planes. They are not silently truncated to the cap, parallelogram or convex hull. Cap-minus-niche area is identified with the area of a feasible sofa only after the relevant containment, connectedness and continuous motion have been proved.

The cap functional's strict upper bounds use either a uniform deficit or attainment. A pointwise strict inequality for each individual feasible body does not by itself imply a strict bound on the supremum.

## Fixed-angle curvature and endpoint audit

The local polygon proof is not a blind substitution of omega for pi/2.

1. The normal set contains the two upper pinned normals separately. The local estimate is applied only at floating normals, with the corresponding neighboring supporting lines available in both active intervals.
2. An inner-wall ray meets the two fan boundary rays in at most two points at an interior angle. These exceptions have zero length. Both endpoint quarter-planes lie outside the fan and can be used as neighbors without adding them to the niche union.
3. The penalty error is retained with a **total mass** tending to zero. Pointwise convergence of each polygon error would not suffice as the number of normals grows.
4. On a mesh cell the relevant vertices are fixed. The diameter-times-mesh bound controls the arm variation and justifies the Riemann-sum passage despite jumps at grid normals.
5. At almost every limiting normal the support point is unique; Hausdorff convergence then gives convergence of both one-sided polygon support points. The fixed parallelogram supplies domination. Weak convergence of curvature measures follows from `sigma=h+h''` against smooth tests.
6. Test functions cross the outer endpoint zero, rather than only lying inside the open arc. This excludes a possible limiting endpoint atom. Reflection excludes the atom at `pi/2+omega`. The two pinned atoms remain allowed.
7. The bounded curvature densities give the continuous interior-sided support derivatives and correct endpoint traces, hence the absolutely continuous arm inequalities. Pinned-edge estimates separately account for floating mass approaching the pinned normals.

The exact quadrilateral counterexample in `negative-results.tex` checks the necessity of this endpoint argument: it has endpoint atoms of mass one and zero interior arms. Ignoring those atoms would incorrectly assert the arm endpoint values needed by the bootstrap.

## Arm and area-comparison audit

For intervals of length at most one, the short bootstrap gives `f>=1-t`, `g>=1-omega+t`, then `f,g>=2/3`, then `f,g>=1`, then the strict linear bounds. The minimum of `1-t+3t^2/4` is exactly `2/3`.

The all-angle arm certificate uses twelve cells and eight downward-rounded integer recurrences, ending at `699/1000>2/3`. Its extension to all shorter intervals uses `1+(L/R)(H-1)>=min(1,H)` with stored bounds clipped at one, rather than an unjustified monotonicity of a partial integral in the interval length. This older exact rational certificate is distinct from the later contact-root interval computation.

The direct signed-area comparison represents the corner as a horizontally monotone graph above the fan floor. Lowering the ordinate strictly decreases both wall coordinates at interior angles. Integration retains the nonnegative endpoint corrections:

`I = integral(Y-ell) - (cot(omega)/2) alpha_-^2 - (sin(omega)cos(omega)/2) beta_-^2`.

These signs are essential. Injectivity alone does not imply fan containment, and omitting these terms would introduce an unproved hypothesis. Equality in the resulting comparison recovers fan containment afterwards. A primitive of the continuous graph function justifies the change of variable without assuming a differentiable inverse parameterization.

## Universal lifting and strictness

The first version of the lifted niche bound used radial core contractions and assumed positive interior thresholds. The later all-maximizer geometry did not directly supply that assumption. `vertical-core-lifting.tex` closes this mismatch: the core consists of vertical slices below the cut segments and corner graph. Each slice lies in an actual excluded quarter-plane even when an individual threshold is negative. The hypotheses are now exactly strict arms, fan containment, positive selected cuts and separation of their niche portions.

The support-area formulas include all normal-gap contributions, including `sec(omega)-tan(omega)`. The core and two exterior-region areas cancel the tangent-square terms with the displayed signs. Pairwise disjointness of the regions is justified by the cut geometry; it is not assumed because the candidate happens to be symmetric.

The quadratic part of the lifted functional is strictly negative on every nonzero difference satisfying the affine traces. The proof cancels the two outer support energies against the two lifted energies, completes a central square, and ends with the strictly positive coefficient `cot(omega-a)-tan(a)` for `omega<pi/2`. Equality forces every remaining difference to vanish. This statement is not extrapolated to the right-angle endpoint.

In the first variation, the cap free-endpoint terms vanish by `p'(0)=k'(omega)=0`; the terms at the cuts cancel using the matching corner derivatives of the lifted supports. On a wall-contact interval the envelope curvature is `r_p-1<0`, and the obstacle gives the correct inequality direction. The remaining coefficient is exactly `r_p-C(g-1)+B(r_p-1)=0`. The reflected coefficient also vanishes. Thus stationarity is upgraded to a global certificate on a convex domain, not merely a local extremum of a finite-dimensional ansatz.

## Contact-order-independent geometry

The arm boundary-value problem is a positive affine contraction on `L2 x L2`, with norm at most `2omega/pi<1`. This proves existence, uniqueness, strict arms and nonsingularity of the linear shooting equations for any admissible reflected contact ordering. The support shooting coefficient at the midpoint is explicitly positive. Nonlinear contact roots are a separate task.

The two joining equations imply a unique crossing `g=2` before the first wall contact and give `r_p<1` afterwards. The sine-kernel comparison uses monotonicity of `g`, not the formula `g=A-t` valid only before reflected-contact overlap. The increasing tangent angle gives the required projection endpoint minima. The initial tent comparison uses the exact derivatives of its two branches and an exact slope separation forced by the joining equations, not a near-transition asymptotic estimate.

These arguments show every displayed corner or wall arc avoids every excluded quarter-plane. Conversely, strict radial contractions of those arcs belong to the niche. Positivity of the thresholds makes the niche star-shaped. Therefore the arcs describe the whole niche, not just a plausible visible boundary from a plot.

The sufficient admissibility tests were reduced to `p''<0`, `p0<5/3`, and `d=g0-p0<1`. The first test and pinned traces give positive thresholds and `d>0`. The arm balance gives active convexity, while the full circular extension has positive pinned atoms `sec(omega)-tan(omega)+d`, positive lower edges and matching outer derivatives. Corner norms are bounded by `sqrt(2)(p0-1)<1`. The wall norm increases up to its floor endpoint, whose abscissa is below `d sin(omega)<1`. Thus the niche lies strictly inside the unit fan sector and the cap contains that sector.

Radial paths to the unit fan arc prove path-connectedness of the cap-minus-niche set. The supporting-hallway motion gives actual feasibility. Regular closedness follows from outward radial perturbations and interior cap approximation. An equal-area closed subset of this regular-closed sofa must equal it, so the final uniqueness statement includes arbitrary original compact sofas rather than just monotone envelopes.

## Analytic bridge and endpoint coverage

The bridge immediately above one radian is explicit, not an unspecified epsilon. A parameter `L=b-phi` solves the first two contact equations by elementary trigonometric formulas. Rational Taylor bounds bracket the unique scalar floor-contact root and prove the support tests for all `0<L<=1/50`. The resulting continuous angle function starts at one and exceeds `1.013` at the other endpoint, covering `(1,1.01]` without assuming monotonicity.

At the other endpoint the external parameter is `h=omega-c`. The last residual is derived from the exact harmonic support on `[c,omega]`:

`2 cos(omega-h/2) sin(h/2) - d cos(omega)=0`.

With certified `1/2<d<1`, it gives `omega(0)=pi/2` exactly and `omega(h)<pi/2` for positive h. It also gives `omega(1/32)<pi/2-1/4096<1.5706`. The endpoint root boxes can enclose values on both sides of pi/2, but the **actual roots** lie on the correct side by this equation. No rounding of pi or extrapolation of a floating root supplies that conclusion.

Fifteen joining certificates verify actual root-box containment in each neighboring pair, identifying the roots at the shared parameter. Continuity plus the intermediate value theorem then covers every angle in the final tail. Sampled monotonicity of the branch is unnecessary.

## Interval-certificate implementation audit

The code and acceptance theorem are in `validated-contact-cover.tex` and `checks/`. Verification uses exact elementary flows, not numerical time integration. The primitive regression checks all eight indicator combinations through initial value, first derivative and second derivative against exact ODE fractions; the paper derives the full flow formulas separately.

Floating Newton steps and approximate inverses only propose data. The checker treats each stored number as an exact dyadic value and encloses the centered Newton map and derivative with interval automatic differentiation through second order. Strict self-inclusion and a weighted norm less than one establish a root for every external parameter in the closed interval. Nonsingularity of the proposed preconditioner follows from the verified derivative bound; it is not assumed from a floating inversion.

At event crossings the verifier enumerates every compatible **reflected** order. Each fixed-order formula extends analytically by oriented durations to the entire box; the hull covers the actual continuous piecewise-analytic residual. Derivative bounds apply on each piece and hence give a global Lipschitz bound along segments. Impossible non-reflected permutations were initially included and caused unnecessarily wide bounds; removing only those impossible orders corrected a verifier obstruction, not a mathematical counterexample or an omitted physical regime.

The interval layer rounds basic operations outward using `nextafter`, rejects division through zero and nonfinite bounds, and checks the IEEE-754 binary64 format and subnormal behavior. Sine and cosine verification use interval Taylor polynomials with explicit factorial remainder bounds on `[-2,2]`, not the platform's trigonometric values. Critical points are enclosed using Machin's identity. Rational coefficient conversion and the basic floating-point model are documented implementation assumptions, not silently treated as a proof-assistant guarantee.

Geometry is checked over sixteen or twenty **relative-time intervals** per coefficient piece. These are interval evaluations over the entire subinterval, not values sampled at a finite mesh. Exact `Fraction` comparisons verify compact-angle coverage against the rational endpoints `101/100` and `7853/5000`. The endpoint chain and all joining-box containments are also checked exactly at their stored dyadic parameter values.

The full standard-library builder generated 750 compact boxes, 16 endpoint boxes and 15 joining boxes. All 781 were replayed from saved coordinates and preconditioners, ignoring their stored success flags. The largest outward contraction bound was below `0.439`, the largest support-second-derivative upper bound below `-0.093`, and every endpoint support test was strict. Source and data hashes are frozen in `checks/CERTIFICATE_REPORT.json`.

A final regression found an **unused mixed interval/second-derivative division dispatch** that could discard the Hessian class. It was corrected to preserve the right operand's derivative type. The actual contact formulas did not traverse the bad path, but all 781 records were nevertheless replayed again against the corrected source. The exact-rational regression also passed 49 interval-pair cases, 1640 rational conversions, the mixed reciprocal Hessian, and all eight flow pieces. These tests supplement the proof and replay; they are not an independent verifier implementation.

## Negative results and rejected shortcuts retained

- **Apply `A_1` to every feasible cap:** false. The explicit convex monotone quadrilateral has empty niche and `A_1=1-omega < sec(omega)-tan(omega)=A_omega`.
- **Ignore endpoint curvature atoms:** false. That same quadrilateral has zero open-arc arms but endpoint atoms of mass one.
- **Infer fan containment from injectivity:** not justified; the direct signed-area comparison and later endpoint geometry provide the actual argument.
- **Continue the old relaxed stationary cap above one radian:** false as an optimality claim. A whole early interval of its niche constraints is redundant; a smooth support bump preserves the niche exactly and increases actual feasible area.
- **Infer actual candidate suboptimality from a non-sharp relaxed value alone:** logically invalid. The separate redundant-angle perturbation proves the stronger claim.
- **Pass from pointwise strictness to a strict supremal bound without attainment:** invalid; the cap compactness and upper-semicontinuity proof supplies the required attainment.
- **Replace the niche by its convex hull or assume convexity of the raw tail correction from experiments:** not justified and not used. The new lift has its own proved convex domain and strict quadratic structure.
- **Use sampled quarter-plane unions as exact area certificates:** invalid. They underestimate niche area and overestimate the remaining area. Early exploratory sampling is not a premise of the final proof.
- **Continue one contact-order formula past a reflected crossing:** invalid. The new proof is order-independent, and the checker encloses all compatible reflected branches.
- **Identify the endpoint with Gerver merely by close numerical constants:** not used. The right-angle theorem is a separately declared companion input.
- **Apply right-angle equality rigidity after merely extending a motion:** invalid. Enlarging the feasible class does not preserve maximizing status.

## What remains outside the completed angle coverage

Independent review of the analysis and implementation, consolidation of the many research notes, and any later Lean formalization remain distinct tasks. This draft does not address corridors with a different physical corner angle or ambidextrous sofas. The ordinary-Python arithmetic model is not a kernel proof, and the absence of a remaining angle interval is not a claim that external review has already occurred.
