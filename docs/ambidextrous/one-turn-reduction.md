# Two one-turn sofas: a floor-trace face classification and a width-penalized reduction

**Draft, not independently reviewed.** **Status: this does not close the unrestricted proof.** It replaces the single missing statement of the README ("full curvature-measure domination for every maximizer") by a sharper, smaller list. The new results below are written, self-reviewed arguments; nothing here is Lean-checked. Floating-point experiments are labelled as diagnostics and are not proof steps.

Labels OT1–OT8 are local to this note.

What is new, in one paragraph. Every canonical two-turn envelope is the intersection of two Baek one-turn monotone sofas, and its area is *exactly* the sum of two one-turn functionals minus the width, plus the area of the niches that fall outside the hull (OT1). The symmetric slice of the problem is the **width-penalized Gerver problem** `max A(U) - W(U)/2`, and Romik's replacement of the contact point (1,0) by (1,1/2) is precisely its transversality condition (OT2). Using only the first and last hallway positions and the fact that extreme points of the hull belong to the body, the two horizontal faces of any competitive hull fall into a short list of configurations, *with no curvature hypothesis* (OT3–OT4). In the main configuration the faces are aligned and long, nothing is clipped, and the two caps decouple into two one-turn problems (OT5). The PR's three obstructions then separate cleanly: GR1 and AF4 are one-turn statements in the aligned configuration, while SC3 lives in the configuration where the turns interact, a hull whose top face has collapsed to a point (OT6).

## OT.0 Setting and notation

Use Notes 1, 2, 5, 8, 10 and AW-W. S is a compact connected ambidextrous body in the common incoming unit-span normalization, both turns in the conventional direction (true when |S| > sqrt 2, Note 10), with horizontal width W > 2 (true for competitive bodies, AW-W). Let K = conv S, with support function h, horizontal extent [x_l, x_r], top face T = [l_t, r_t] x {1}, bottom face B = [l_b, r_b] x {0}, and

$$
x_0=x_r-1,\qquad x_1=x_l+1,\qquad x_1<x_0 .
$$

Put mu_t = (cos t, sin t), nu_t = (-sin t, cos t), L = pi/2.

**Caps.** The *upper cap* U is the strip intersected with the supporting half-planes of K at normals in [0, pi]; the *lower cap* U' is defined the same way for rho K, rho(x,y) = (x, 1-y). Both are Baek caps of rotation angle pi/2 with the same horizontal extent as K, and

$$
K=U\cap\rho U' .
$$

Write a(x), a'(x) for the upper boundaries of U, U'. For a cap V, its niche is Baek's

$$
N(V)=\{y\ge0\}\cap\bigcup_{0<t<L}Q_V(t),\qquad
Q_V(t)=\{p:\ p\cdot\mu_t<h_V(t)-1,\ p\cdot\nu_t<h_V(t+L)-1\},
$$

its vertical sections are [0, alpha_V(x)) (each Q_V(t) is closed under moving down), and Baek's one-turn functional is

$$
\mathcal A(V)=|V|-|N(V)|=\int (a_V-\alpha_V)\,dx .
$$

T_V = V \ N(V) is Baek's monotone sofa; it is a moving sofa exactly when N(V) is contained in V (Baek Thm 2.5.9, docs/proof Thm 3.26). The canonical envelope of the two full turns is

$$
E=T_U\cap\rho\,T_{U'}=K\setminus\bigl(N(U)\cup\rho N(U')\bigr),\qquad S\subseteq E .
$$

## OT.1 The two-sofa identity

**Theorem OT1.** Let U, U' be Baek caps with the same horizontal extent [x_l, x_r] and K = U cap rho U', and let E = T_U cap rho T_U'. (When S has full canonical turns and these are its caps, S is contained in E.) Suppose every vertical fibre of E over [x_l, x_r] is nonempty; this holds when E contains a connected S with conv S = K, since S then projects onto [x_l, x_r]. Then

$$
\boxed{|E|=\Bigl(\mathcal A(U)-\tfrac W2\Bigr)+\Bigl(\mathcal A(U')-\tfrac W2\Bigr)+|G|,}
\qquad
|G|=\int_{x_l}^{x_r}\Bigl[\min(\alpha,1-a')+\min(\alpha',1-a)\Bigr]dx ,
$$

where alpha, alpha' are the niche roofs of U, U'. The first term of G is the part of N(U) below the bottom boundary 1-a' of K; the second is the part of rho N(U') above the top boundary a of K. Thus G is exactly the niche area lying outside K. No curvature, contact, or symmetry assumption is used.

**Proof.** The fibre of E at x is [max(alpha, 1-a'), min(a, 1-alpha')]. For a, a' <= 1 and alpha, alpha' >= 0 one has

$$
\min(a,1-\alpha')=a-\alpha'+\min(\alpha',1-a),\qquad
\max(\alpha,1-a')=\alpha+(1-a')-\min(\alpha,1-a'),
$$

(check the two cases of each minimum). Subtracting, the fibre length is

$$
\ell=(a+a'-1)-\alpha-\alpha'+\min(\alpha,1-a')+\min(\alpha',1-a).
$$

Nonempty fibres give |E| = integral of ell. Integrate: the integral of a + a' - 1 is |U| + |U'| - W, and the integrals of alpha, alpha' are |N(U)|, |N(U')|. QED.

SR2 is the same identity written against the adaptive functional; OT1 is the version that needs no hypothesis because A is the actual one-turn area functional, not a formula for it.

## OT.2 The symmetric slice is the width-penalized Gerver problem

**Proposition OT2.** Let V be any Baek cap with N(V) contained in V and niche height at most 1/2. Then T_V cap rho T_V contains a compact connected ambidextrous body of area at least 2A(V) - W(V).

**Proof.** T_V is a moving sofa for the canonical right turn, and rho T_V for the reflected left turn; both start in the incoming strip, which rho preserves. On the interval {a_V >= 1/2}, every fibre [max(alpha_V, 1-a_V), min(a_V, 1-alpha_V)] contains y = 1/2, so this part of the intersection is compact and connected (every fibre meets the midline segment). As min(a_V, 1-alpha_V) >= a_V - alpha_V, its area is at least the integral over {a_V >= 1/2} of 2(a_V - alpha_V) - 1, which is at least the integral over the whole extent, because the integrand is negative where a_V < 1/2. That integral is 2A(V) - W. QED.

**Corollary OT2a (a necessary one-turn inequality).** If Romik's candidate is optimal, then

$$
\mathcal A(V)-\tfrac12W(V)\le \tfrac M2
$$

for every Baek cap V with N(V) inside V and niche height at most 1/2. A cap violating this would give an ambidextrous body larger than the candidate. Conversely the candidate satisfies A(U*) - W*/2 = M/2 with W* = 8A/3, since its two caps coincide and nothing is clipped.

**Remark OT2b (Romik's boundary condition is a transversality condition).** Let V have a vertical right end edge {x_r} x [0, e_0], e_0 > 0, whose top vertex has normal cone [0, t_c], and suppose the inner walls b(t), 0 < t < t_c, carry no niche boundary. This is the situation of U*, whose first phase has contact set {A, C, D} only (Romik, Section 5). Translate that vertex and edge outward by epsilon. The hull gains e_0 epsilon + O(epsilon^2), the width gains epsilon, and the niche changes by o(epsilon). So the first variation of A - lambda W in this direction is e_0 - lambda, and balance forces e_0 = lambda. For lambda = 1/2 the support point at the start of the turn sits at height 1/2. This is exactly Romik's modification in his Section 5: contact (1, 1/2) for A(0) instead of Gerver's (1, 0), with the interior phases solving the same ODE1/ODE6/ODE5 as Gerver's. Indeed the candidate cap U* has sigma({0}) = f_*'(0) = 1/2 by (14.2). A penalty on h(0) + h(pi) does not change balance at interior normals.

So Romik's ambidextrous sofa is a critical point of a *one-turn* problem with a linear width penalty; the conjecture implies that this point is the problem's global maximum on the stated class, and the candidate attains the value.

## OT.3 The floor-trace lemma (no curvature hypothesis)

**Lemma OT3.** Both turns are in the conventional direction, so the right turn visits every angle in (0, epsilon) for some epsilon > 0, by continuity of its angle.

(i) If l_t < x < x_0, then (x, 0) lies in the canonical quadrant Q_K(t) for all sufficiently small t > 0. Hence (x, 0) is not in S.

(ii) If the right turn is full and x_1 < x < r_t, then (x, 0) lies in Q_K(t) for all t sufficiently close to pi/2. Hence (x, 0) is not in S.

(iii) The reflected statements hold for the left turn, with (x, 1) in place of (x, 0) and the bottom face in place of the top face: (x, 1) is not in S for l_b < x < x_0, and, for a full left turn, for x_1 < x < r_b.

**Proof.** S avoids Q_K(t) at every visited angle (the tightening argument of Note 8: translating a feasible hallway until its outer walls support K only shrinks its inner quadrant).

(i) Since (x_r, y_r) is in K with y_r >= 0, h(t) >= x_r cos t, so (x,0).mu_t - (h(t) - 1) <= 1 - (x_r - x) cos t, which is negative once cos t > 1/(x_r - x); this is possible because x_r - x > 1. Since (l_t, 1) is in K, h(t + L) >= -l_t sin t + cos t, so (x,0).nu_t - (h(t+L) - 1) <= -(x - l_t) sin t + (1 - cos t), which is negative once tan(t/2) < x - l_t.

(ii) Symmetrically, (x_l, y_l) in K gives h(t+L) >= -x_l sin t, so (x,0).nu_t - (h(t+L)-1) <= 1 - (x - x_l) sin t < 0 once sin t > 1/(x - x_l). And (r_t, 1) in K gives (x,0).mu_t - (h(t)-1) <= -(r_t - x) cos t + (1 - sin t) < 0 once tan(pi/4 - t/2) < r_t - x.

(iii) Apply (i) and (ii) to rho S, whose right turn is the left turn of S. QED.

**Corollary OT3a.** The endpoints of a face are extreme points of K, hence belong to S. Therefore

$$
l_b,r_b\notin(l_t,x_0)\ \bigl[\cup(x_1,r_t)\bigr],\qquad
l_t,r_t\notin(l_b,x_0)\ \bigl[\cup(x_1,r_b)\bigr],
$$

the bracketed parts requiring full turns.

The PR's CW2 and CW3 used the same extreme-point principle, but obtained the forbidden baseline intervals from monotone intercepts, which needs curvature domination. OT3 obtains enough of them from the first and last hallway positions alone.

## OT.4 What the first hallway positions force on the faces

**Theorem OT4.** Let S be competitive (|S| > sqrt 2) with W > 2. Exactly one of the following holds.

- **(A) common left end:** l_t = l_b =: l < x_0 and r_t, r_b >= x_0.
- **(P) point face:** l_t = l_b =: l < x_0 and at least one face is the single point {l}.
- **(R) right-end face:** at least one face lies inside [x_0, x_r].

Moreover, in case (A) with x_0 - l >= tan(pi/8), both turns are full quarter turns, T = B, and the common face [l, r] satisfies l <= x_1 and r >= x_0 ("aligned long faces").

**Proof.** Use only the start parts of OT3a. If l_t < l_b, then l_b is not in (l_t, x_0), so l_b >= x_0 and B lies in [x_0, x_r]: case (R). Symmetrically if l_b < l_t. If l_t = l_b = l >= x_0, both faces lie in [x_0, x_r]. If l_t = l_b = l < x_0, OT3a gives r_b, r_t not in (l, x_0), so each of r_t, r_b equals l or is at least x_0: cases (A) and (P).

For the second part, K contains the rectangle [l, x_0] x [0, 1]. A partial turn ending at angle omega requires the width of K in the direction mu_omega (or mu_{-omega}) to be at most one, but that width is at least (x_0 - l) cos omega + sin omega, which exceeds one whenever x_0 - l > tan(pi/4 - omega/2). Bodies of area greater than sqrt 2 have canonical terminal angles greater than pi/4, by the two-strip bound (8.9) of Note 8 as used in the proof of Corollary WG3; there tan(pi/4 - omega/2) < tan(pi/8). So both turns are full, and the end parts of OT3a apply. Both faces are nondegenerate and cross the core, l < x_0 and r > x_1. Then (l_t, x_0) cup (x_1, r_t) is the single open interval (min(l_t, x_1), max(r_t, x_0)), because x_1 < x_0. B is an interval meeting it whose endpoints lie outside it, so B contains it, hence contains T; symmetrically T contains B. So T = B, and containment of (min(l, x_1), max(r, x_0)) in [l, r] gives l <= x_1 and r >= x_0. QED.

The candidate is in case (A) with x_0 - l = 2A - 1 = 0.7506 > tan(pi/8) = 0.4142.

If one also assumes full turns, the end parts of OT3a split cases (P) and (R) further, into a point face at an end of the other face, both faces at one point, and *tilted* faces, one in [x_l, x_1] and the other in [x_0, x_r]. Only aligned long faces avoid all of these.

## OT.5 Aligned long faces: no clipping, and two decoupled one-turn problems

**Theorem OT5.** Suppose both turns are full, T = B = [l, r] x {0, 1} with l <= x_1 < x_0 <= r, and the canonical corner heights c_y(t) are positive for 0 < t < L. These are the conclusions of OT4 in case (A) with x_0 - l >= tan(pi/8), plus the corner-height condition. Then G is empty, both niches lie in the rectangle [l, r] x [0, 1], and

$$
\boxed{|S|\le|E|=\Bigl(\mathcal A(U)-\tfrac W2\Bigr)+\Bigl(\mathcal A(U')-\tfrac W2\Bigr).}
$$

The positivity of c_y holds whenever r - l >= 1, since then c_y(t) >= (r - l) sin t cos t + 1 - sin t - cos t > 0 using the face endpoints. In particular it holds near the candidate, whose face has length 4A/3 > 1.

**Proof.** Q_K(t) meets {y >= 0} exactly in the open triangle over the baseline interval (d(t), e(t)) with apex c(t), nonempty iff c_y(t) > 0. So the projection J of N(U) is the union of these intervals. With c_y > 0 throughout they form a continuous family of nonempty open intervals, and J is one open interval. By OT3, J contains (l, x_0) cup (x_1, r) = (l, r). Since (l, 0) and (r, 0) are in S, neither is in J, so J = (l, r). Over (l, r) the bottom of K is y = 0 and the top is y = 1, and alpha <= 1 - alpha' <= 1 because the fibres of E are nonempty. Hence N(U) lies inside K, and likewise rho N(U'). So G is empty and OT1 gives the identity. QED.

**Remark OT5a (each cap is a constrained one-turn local maximizer).** Let S be a global maximizer in the situation of OT5. For any variation U_nu of U with the same axis supports, for which T_{U_nu} cap rho T_{U'} remains connected with nonempty fibres, OT1 with |G| >= 0 gives

$$
|S|\ \ge\ |T_{U_\nu}\cap\rho T_{U'}|\ \ge\ \mathcal A(U_\nu)+\mathcal A(U')-W ,
$$

so A(U_nu) <= A(U). Thus, inside this configuration, the first-order analysis of each cap is the *one-turn* balance of Baek's Chapter 3, with no hidden or clipped edge lengths: the visibility obstruction of Note 21 does not arise.

**Corollary OT5b.** In the configuration of OT5, the width-penalized inequality A(V) - W/2 <= M/2 for the two caps of S implies |S| <= M. Conversely, by OT2a, Romik's conjecture implies that inequality for each cap whose niche height is at most 1/2. So, in this configuration, the remaining problem is a one-turn problem.

## OT.6 Where the PR's obstructions live

- **SC3 is a point-face configuration.** In SC3 the upper niche is the candidate's, whose top trace is the whole open interval (0, m) (OT3(iii)), and the outer set bar K_z has top face [0, x_Z] with x_Z < m. Hence the only top point of B_z is (0, 1), and the *actual* hull H_z has top face {(0,1)} and bottom face [0, m]. This is case (P), and the clipping in (SC.8) is the term G of OT1 for that configuration. SC3 is thus an explicit near-optimal family in the configuration where the two turns interact through clipping.
- **GR1 is a one-turn statement.** K_0 and K_epsilon have the aligned faces [-b, b], 2b > 1, so OT5 applies to both. Only the first upper quarter changes, so U' is fixed and |S_epsilon| - |S_0| = A(U_epsilon) - A(U_0). With R(U_epsilon) = U_0 (GR.12), GR1 proves that **one-turn curvature repair can decrease A** at width 63/25. Its first-order coefficient is the integral of (q - 1) psi with q > 1.01: the corner's speed along the inner wall exceeds the unit curvature. So the one-turn half cannot be closed by a universal repair argument; maximality must enter.
- **AF4 is a one-turn statement.** Its protected bodies keep the candidate's faces, of length 4A/3 > 1, so OT5 applies. |S| > Q̃(h_{conv S}) then says A(U) > F̃(h_U) for a cap with curvature excess. This is the expected direction: where rho_f > 1 the inner-wall envelope folds, the signed-roof formula counts the fold, and it over-estimates the true niche.

## OT.7 The one-turn half

Write Psi(V) = A(V) - W(V)/2 for Baek caps V. The needed one-turn theorem is

$$
\textbf{(W-Gerver)}\qquad \Psi(V)\le \tfrac M2\ \text{for every Baek cap }V,\ \text{with equality only for translates of }U_* .
$$

- If W(V) <= 1, Psi(V) <= |V| - W/2 <= W/2 < M/2.
- If W(V) >= 2(2.21953 - M/2) = 2.7941, Baek's theorem (A <= |Gerver| for every cap; docs/proof Thms 4.38 and 9.33, formalized in this repository) gives Psi(V) <= M/2.
- For W in [1, 2.7941]: if the maximizer of Psi is curvature-dominated on its two open quarters, then SR1 gives A <= F̃ and AF3 gives F̃ - W/2 <= M/2, with AF3's equality case.

For the last bullet, Baek's limit inequality (his Thm 6.4.3; docs/proof Thm 7.18) says that for every balanced maximum cap

$$
\sigma_K\le k_0\bigl(g_K^+(t)\bigr)\,dt\ \text{ on }[0,\pi/2),\qquad
k_0(x)=\max\Bigl(|x-1|,\ \tfrac{|x-1|+1}2\Bigr),
$$

with g Baek's arm length, and the mirror statement on (pi/2, pi]. In particular sigma is absolutely continuous on the open quarters. Since k_0(x) <= 1 exactly for 0 <= x <= 2, **a balanced cap is curvature-dominated wherever its arm lengths are at most 2.** The candidate's arm lengths are at most 2A = 1.7506, attained at the axis normals. A width penalty changes balance only at the axis edges (OT2b).

So W-Gerver would follow from three things:

1. Baek's Chapter 3 (existence of balanced maximum caps) and the interior part of Theorem 6.4.3, carried over to A - W/2. This should be routine but must be checked.
2. A full right-angle turn for the maximizer. The one-turn argument (docs/proof Chapter 5) uses area at least 2.2, while here the maximizer has A ≈ 1.99.
3. Arm lengths at most 2 at the maximizer. Baek's relations f' = g - rho_f and g' = rho_g - f (docs/proof Thm 7.9 and its mirror), with the limit inequality, give g' <= k_0(f) - f = -m_0(f). So g can increase only where f < 2/3, and there at rate at most 1, and symmetrically for f. The end values are g(0) = x_r - l and f(L) = r - x_l. Item 3 therefore reduces to bounds on these two distances plus control of the set where an arm is below 2/3. Baek's iteration (docs/proof §7.5) proves arm bounds of this type for the unpenalized problem.

GR1 shows that item 3 cannot be dropped: an unbalanced cap with q > 1 and rho = 1 exists, and for it inward deformation increases A.

## OT.8 The remaining obligations

The README's single missing statement, curvature domination for every maximizer, is replaced by the following.

- **O1 (exceptional start configurations).** Exclude, for maximizers or for all bodies of area at least M, cases (R) and (A) with x_0 - l < tan(pi/8). These are configurations far from the candidate, with both faces crowded into the last 1 + tan(pi/8) units of one end. Area estimates from a few hallway positions, as in AW-W and Note 44, are the expected tool.
- **O2 (point faces, the genuine two-turn core).** Exclude case (P) for a maximizer. SC3 shows this cannot be done by any area threshold below M, because these bodies have area tending to M. A variational argument at a maximizer is needed. Balance at the top vertex gives one useful first-order fact: if the top face is the single point (l, 1), pulling in an a-wall whose normal is interior to that vertex's normal cone removes only O(epsilon^2) of the body but shrinks the right niche at the rate of its visible boundary length tau(t) on the inner wall b(t), so a maximizer has tau(t) = 0 on that cone. The competing effects of reopening the face are then both of second order; SC3's margin is of order z^3.
- **O3 (corner height).** In case (A) with face length below 1, rule out a middle parameter interval on which the right corner dips below the baseline and then re-emerges outside [l, r]. Otherwise OT5 applies verbatim.
- **O4 (W-Gerver),** via OT.7 items 1 to 3.

O3 and O4 are one-turn statements. O1 is expected to be elementary. O2 is where the two-turn difficulty now lives.

## OT.9 Numerical diagnostics (not proof steps)

The scripts are in `computer-assisted/one-turn/`. They use fiberwise areas on dense angle grids, so computed niches are inner approximations, and areas slightly over-estimate the truth. None of the following is a certificate.

| Check | Result |
|---|---|
| Candidate, exact support (14.2) | 2Psi(U*) = abs(E(U*,U*)) = 1.645005 at 3000 hallway angles, against M = 1.644955; clipping 0; niche height 0.3878 = 1/2 + R - sqrt 2 |
| Maximize Psi over polygon caps, 16 runs: 4 at 12 normals per quarter (candidate and random starts), 12 at 14 normals per quarter (wide starts, W from 3.6 to 4.6; narrow starts, W from 1.4 to 1.8) | All converge to one configuration: W in [2.327, 2.336], face 1.18–1.22, end edges 0.44–0.51, niche height 0.387–0.390. At 14 normals none exceeds the discretized candidate (0.821628, best run 0.821626); at 12 normals the best run is 3e-5 above the projected candidate polygon, which is not itself the optimal 12-normal polygon |
| Maximize abs(T_U cap rho T_U') over asymmetric pairs and a relative shift, from 3 starts | No asymmetric gain beyond discretization; clipping at most 5e-6 at the optima |
| Repair R on 60 random polygon caps, all curvature in atoms | A(R U) - A(U) >= +0.007 |
| Adversarial minimization of A(R U) - A(U), W <= 2.8, 10 runs | Minimum +0.000005, approached by near-rectangles |
| Same, W <= 4.5 | Minimum -0.050 at W ≈ 4.5: repair can lose for wide caps |
| SR1/AF3 chain on repaired random caps | A - F̃ -> 0 under refinement (6.4e-4, 3.2e-4, 1.6e-4); F̃ - W/2 <= M/2 - 0.032 on samples |

The GR1 failure of repair monotonicity at W = 2.52 is invisible to these searches. Its first-order coefficient is about 1e-4 times epsilon, on a normal window of width 0.01 radians, and convexity forces epsilon below 1e-5. This is a warning that the sampling diagnostics test typical caps, not worst cases.

## OT.10 Execution

Pen-and-paper arguments plus the labelled diagnostics above. No CI, Lean/Lake build, or manuscript build. No existing file is changed.
