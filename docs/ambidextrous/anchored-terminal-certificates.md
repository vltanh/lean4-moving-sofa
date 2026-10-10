# Anchored ordinary-area certificates for terminal-angle boxes

This strengthens CF2 in the way required by OR1. It uses two mandatory extreme-point witnesses and the two terminal-strip constraints. It keeps ordinary area in the certified layer and does not use the adaptive functional, curvature, full turns, wing admission, or local candidate structure.

Labels AT are local. This note proves the certificate mechanism. A numerical search is not an accepted covering: the final endpoint exclusion is available only for the endpoint range and every box accepted by `computer-assisted/verify_anchored_terminal.py`.

## 1. The domain to cover

Write q=41/25. Consider a compact connected ambidextrous body with area at least q in its common incoming strip. The earlier canonical/sign reduction and AW-W give a representation in

$$
[0,W]\times[0,1],\qquad 2<W<4.
$$

The upper width bound is DU1; no maximizing assumption is needed. Let alpha,gamma in (0,pi/2] be the two reduced endpoint magnitudes, and put a=tan(alpha/2), g=tan(gamma/2). The endpoint-strip inequalities are

$$
|S|\le1/\cos\alpha,\qquad |S|\le1/\cos\gamma,
\qquad |S|\le1/\sin(\alpha+\gamma)
$$

whenever the denominators are nonzero. In particular alpha+gamma>pi/2 because q>sqrt(2).

Values a<=12/25 are excluded analytically: cos(2 arctan(12/25))=481/769>25/41, giving area strictly below q.

For an alpha box a in [a_0,a_1], choose a rational g_0 such that

$$
\cos(\alpha_1+\gamma_0)\le0,\qquad
\sin(\alpha_1+\gamma_0)>25/41,
$$

where alpha_1=2 arctan(a_1), gamma_0=2 arctan(g_0). If gamma<=gamma_0, then pi/2<alpha+gamma<=alpha_1+gamma_0<=pi, so the third strip bound contradicts |S|>=q. Thus it suffices to cover g in [g_0,1]. Both trigonometric tests use only rational addition formulas.

There is also an elementary width cutoff in each terminal box. Comparing the two horizontal extreme points in the lower terminal strip gives

$$
W\cos\alpha\le1+\sin\alpha,
\quad\text{hence}\quad W\le\frac{1+a}{1-a}.
$$

Use the upper box endpoints for a,g, and combine the two estimates with W<4. This is the function `strip_width_limit` in the verifier. At a=1 the latter cutoff four is used directly.

## 2. Spatial cells and forced witnesses

For a width interval [W_0,W_1], partition [0,W_1] times [0,1] into nx by ny closed cells, each of area

$$
b=\frac{W_1}{nx\,ny}.
$$

Boundary overlap has measure zero. A cell's meet indicator z_i is in {0,1}, and |S|<=b sum_i z_i.

Add the two zero-area witness rectangles

$$
P_l=\{0\}\times[0,1],\qquad
P_r=[W_0,W_1]\times[0,1].
$$

Compactness and the definition of horizontal width supply a point of S in each. Their two meet indicators are fixed to one. They need not be spatial partition cells. They impose geometric conditions but contribute no area to the objective.

## 3. Two kinds of exact incompatibility

**Hallway witnesses.** At any fixed rational-half-angle frame known visited throughout the endpoint box, compute exact minima and maxima of each scalar product over every cell or witness rectangle. If

$$
\min_Q x\cdot u-\max_P x\cdot u>1,
\qquad
\min_R x\cdot v-\max_P x\cdot v>1,
$$

CF1 implies that P,Q,R cannot all be met. Distinct geometric variables form an edge e with `sum_{i in e} z_i <= |e|-1`. If Q=R the same conclusion is a pair inequality. The verifier reconstructs each fixed frame at an angle no larger than the appropriate lower endpoint of the motion box.

**Terminal witnesses.** For the lower terminal normal `(cos alpha,sin alpha)`, bound its two coefficients on the rational a-interval by their endpoint extrema. For the upper terminal normal use `(cos gamma,-sin gamma)`. For cells P,Q, the difference of their points lies in a known rational coordinate rectangle. If the sum of the two minimum coefficient-times-coordinate products is greater than one, no pair of points in P,Q can lie in the same terminal unit strip. This gives a pair inequality.

Treating the two normal-coordinate intervals independently only weakens the bound. Their endpoints need not be attained at the same angle; the verifier does not assume they are.

## 4. Rational dual bound with the forced variables substituted

Let lambda_e>=0 be any finite list of weights attached to verified incompatibilities. Put k_e equal to the number of forced witness variables in edge e, let c_i=sum_{e containing i}lambda_e for ordinary cells, and set

$$
T=\sum_e\lambda_e(|e|-1-k_e)+\sum_i(1-c_i)_+.
$$

**Theorem AT1 (anchored ordinary-area bound).** Every body in the specified angle/width box satisfies

$$
\boxed{|S|\le bT.}
$$

**Proof.** Substitute z=1 for the two forced variables in every incompatibility. Multiply by lambda_e and sum, then use z_i<=1 to pay the positive residual `(1-c_i)_+`. This bounds sum_i z_i by T. Multiply by b. QED.

If lambda_e=m_e/D for positive integers m_e and a common positive denominator D, the entire dual calculation is integer arithmetic:

$$
T=\frac{\sum_e m_e(|e|-1-k_e)+\sum_i\max(D-\sum_{e\ni i}m_e,0)}D.
$$

There is no requirement that a numerical optimizer be correct, or that every possible incompatibility be listed. Any proposed weights whose geometry is checked give a valid bound. Rounding numerical dual weights cannot invalidate AT1: the rounded weights are simply a new proposal, and the residual is recalculated exactly. A proposal that does not reach the target is rejected.

## 5. Complete coverage and logical consequence

A certificate lists adjacent rational alpha intervals from 12/25 to a declared endpoint a_end<1. Within each, the independently checked coupled-angle test supplies g_0, and adjacent gamma intervals cover [g_0,1]. Within each angle box, adjacent width intervals cover [2,W_end], where W_end is the analytic cutoff of Section 1. All interval endpoints are compared as exact fractions.

**Theorem AT2 (verified endpoint exclusion).** If the checker accepts such a certificate with every leaf's AT1 bound strictly below 41/25, then no body of area at least 41/25 has a reduced endpoint half-tangent at most a_end. The assertion holds for both turns by horizontal-strip reflection and exchange of the two motions.

**Proof.** Values below 12/25 contradict the initial strip estimate. Every remaining putative endpoint lies in an alpha interval. The coupled estimate puts the other endpoint in its gamma covering, and the width bounds put W in one of its width leaves. AT1 contradicts |S|>=41/25 there. Reflection supplies the other turn. QED.

This conclusion is a necessary angle condition, not full quarter-turn completion or optimality. The reported endpoint is read from the accepted certificate; extending it requires additional accepted boxes.

## 6. Trust boundary

The generator may use floating-point LP solving and adaptive refinement. The verifier uses only Python unbounded integers and rational arithmetic to check all witnesses, nonnegative dual weights, angle guarantees, and coverage. It does not trust the solver's success flag, its reported bound, its constraint residuals, or its explored-node count.

No local candidate theorem is embedded in this verifier, and no unresolved box can be marked as locally solved. Failure to cover a box keeps the endpoint exclusion unproved for that requested range. The underlying motion, width and strip reductions remain written mathematical dependencies subject to independent review. No CI or Lean/Lake compilation is involved.
