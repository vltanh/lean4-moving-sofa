# Paper-proof review

This is an internal mathematical review of the research notes, not an independent referee report or machine-verification certificate. No Lean, `lake`, CI, workflow dispatch, or axiom audit was run. The TeX sources were not compiled. The notes should be reviewed before their results are promoted into the main manuscript.

## Status of the assertions

**Complete arguments written in this directory:** endpoint normalization; the zero-angle equality case; a rotating-corner competitor; a quantitative strict endpoint-strip deficit; feasibility of the corner-carved parallelogram for small angles; the unrestricted small-angle expansion and convergence in measure of the rescaled missing region; direct feasibility of Baek's relaxed candidate for `0 < omega <= 1`; and a strict quadratic gap for the relaxed functional in this range.

**A theorem with an explicit external mathematical input:** exact optimality and uniqueness among normalized injective monotone sofas for `0 < omega <= 1`. Its input is Baek, *A Conditional Upper Bound for the Moving Sofa Problem*, arXiv:2406.10725v1, Theorem 5.5. It requires both injectivity of the canonical corner curve and containment of that curve in the fan. Those assumptions are not removed by the present proof.

**Not established:** the exact unrestricted maximum at any positive angle, uniqueness among all positive-angle sofas, applicability of the conditional majorant to every maximizing envelope, a full contact-regime classification, or any Lean theorem corresponding to these new notes. In particular, the exact lower bound `m(omega) >= 1 + omega^2/2` is not an exact unrestricted value theorem.

## Checks on definitions and quantifiers

1. **Net angle, not minimal angle.** The motion starts at angular lift zero and ends at `-omega`. Backtracking is permitted. The inner-corner exclusion argument uses the intermediate value theorem and is therefore applicable to those motions.
2. **Normalization is not uniqueness.** For `cos(omega) > 0`, the two upper endpoint supports determine one translation. No conclusion about reflection or noncongruent optimizers follows from this linear algebra.
3. **The fan is retained.** Niches are defined by intersecting the union of open quarter-planes with the fan. Neither paper silently replaces the fan by the endpoint parallelogram.
4. **Caps are not automatically sofas.** Both explicit families have direct continuous motions, compactness proofs, and radial path-connectedness arguments. Their niche containment in their caps is proved before area subtraction.
5. **The supremum is handled uniformly.** The endpoint-strip improvement subtracts one explicit positive quantity depending only on the angle. The small-angle upper bound uses sofas within `omega^5` of the finite supremum and does not assume maximizer existence.
6. **Translation after normalization.** The lower endpoint inequalities follow from the width bounds. They do not require every arbitrary sofa to touch both lower walls. Cap-specific equalities are invoked only for caps.
7. **Zero-angle equality.** The area-one square conclusion uses closedness. Removing a boundary or interior point from a closed subset leaves a ball whose intersection with the square has positive area.

## Checks on the small-angle proof

- The niche is star-shaped because every contributing quarter-plane has positive thresholds and contains the origin. Its relative openness makes the remaining sofa closed in its compact cap.
- The unit fan arc lies inside the cap and outside the niche. Expanding a radius cannot enter a star-shaped removed set; contracting from outside the unit disk cannot enter a niche lying strictly inside that disk. These are separate cases in the connectedness proof.
- The spatial scale is `omega^2`; the area scale is `omega^4`. These are not interchangeable.
- The rescaled quarter-plane thresholds converge uniformly in the parameter `s = t/omega`. The proof uses a maximum of a minimum of the two margins, avoiding an unjustified interchange of a limit and an uncountable union.
- The moving fan converges away from its boundary rays. The limiting curved boundary and axes have zero planar measure. A common bounded rescaled niche permits dominated convergence.
- The missing-slice triangle works for nonconvex compact sofas: every point of the triangle has scalar product strictly above the sofa's support value. No convexity of the sofa itself is used.
- The support estimate is uniform on both active normal intervals. Reflection transfers a bound, but does not assume that the sofa is symmetric.
- The upper asymptotic is proved for arbitrary near-maximizers, not just the explicit competitor. Eventual exclusion of the limiting corner gives a lower bound on every near-optimal missing area by Fatou's lemma.
- The limiting-defect rigidity statement is convergence in symmetric-difference area. It is not Hausdorff convergence or exact uniqueness. Convergence of the total missing area is explicitly used to rule out a positive amount of rescaled area escaping elsewhere.

## Checks on the relaxed candidate and its equality case

- The candidate and relaxed functional are attributed to Baek's 2024 conditional-bound paper. His existence of a cap with a specified boundary measure is not treated as a proof that every relaxed maximizer is that cap.
- Coordinates use `o = (sec(omega) - tan(omega), 1)`, derived from the two pinned upper supports. This avoids copying an incompatible coordinate expression from an earlier presentation.
- The candidate is checked through its support functions and boundary arcs. Its inner corner is `gamma(t) = o + (omega-t-1)u_t + (t-1)v_t`, with derivative `-t u_t + (omega-t)v_t`.
- `gamma_x` is strictly decreasing; strict concavity of `gamma_y` and reflection prove fan containment. The closed curve with the two fan rays bounds a convex region by the tangent-turn calculation.
- The crucial no-tail inequality is explicit:

  `(a(t)/cos(t)) - r = ((omega-1)(1-cos(t)) + sin(t) - t)/cos(t) <= 0`.

  Its sign uses `omega <= 1`. It must not be extrapolated to all angles.
- The niche is sandwiched between the interior and closure of the corner-curve region. Its boundary has area zero, which is sufficient for the Green area computation. No unsupported exact equality of boundary conventions is needed.
- Support points survive removal of the niche because they have norm at least one, whereas the niche has radius less than one. This verifies that the feasible sofa really has the stated cap and canonical curve.
- The support-area identity is justified first in the smooth case and then by support-function smoothing in `H^1`. All complementary normal-gap contributions are included; omitting the constant `c` would give the wrong functional.
- Both free endpoint terms vanish in the first variation. The actual conditions are `f(omega)=0`, `g(0)=0`, `p_*'(0)=0`, and `k_*'(omega)=0`, together with the pinned supports.
- The exact quadratic gap is coercive for the stated range. Zero gap forces both support differences to vanish; this is the equality argument establishing unique normalized relaxation optimality.
- The restricted sofa theorem uses the imported majorization only after its hypotheses are stated. No claim of all-maximizer injectivity is smuggled into that application.

## Local symbolic and numerical sanity checks

These were exploratory calculations in Python, not CI and not substitutes for the written proofs. No check invoked Lean or a theorem prover.

SymPy verified the displayed derivatives of the candidate boundary and corner curves, the two Euler--Lagrange identities, the elementary Taylor coefficients used in the small-angle squeeze, and the integral `integral_0^1 (s-s^2/2)s ds = 5/24`. It also verified `A(s)+B(s)+(A(s)-B(s))^2 = 3/4` for the limiting boundary parameterization.

Finite unions of sampled niche polygons gave the following illustrative rescaled areas for the parallelogram family; the limit in the proof is `5/24 = 0.208333333...`:

| Angle | Sampled niche area divided by angle to the fourth power |
| --- | --- |
| 0.20 | 0.242759866 |
| 0.10 | 0.223419314 |
| 0.05 | 0.215381549 |
| 0.02 | 0.211014949 |
| 0.01 | 0.209630815 |

For the relaxed candidate, direct quadrature of the boundary formulas returned areas `1.005`, `1.125`, and `1.5` at angles `0.1`, `0.5`, and `1.0`, respectively, matching `1 + omega^2/2`. Sampled niche polygons stayed inside the sampled outer cap. The finite-sampling sofa areas were slightly above the exact target because omitting angular constraints underestimates the niche; they are not certificates of feasibility or optimality.

## Highest-priority remaining audit/research item

Establish the majorization `A_omega(K) <= A_1(K)` for global fixed-angle maximizing caps in a justified interval. Injectivity plus fan containment is one sufficient route, but a direct signed-area/niche inequality could also suffice. For global uniqueness the statement must cover every maximizing envelope, followed by a valid equality recovery of the original sofa. The existing penalized selection machinery should be inspected at its variation and endpoint hypotheses, not assumed to prove this automatically.
