# 37. An active corner cannot converge to a buried endpoint

The endpoint exceptions in Theorem 73 can be excluded under the same regular-contact variation hypotheses. The additional argument uses actual global activity of the corner on the swept boundary, not just its differential equations. It removes the strict endpoint-clearance assumption from that theorem.

This closes the curvature calculation for the regular critical-point model. It does not yet prove that arbitrary maximizers have the regularity and admissible contact charts required in Section 36.1.

## 37.1 A closed-boundary observation

**Lemma 74 (no buried limit of active corners).** Let W be an open union of forbidden quadrants and let c(t_n) be corner points on the boundary of W, with t_n tending to t_0 and c continuous. Then c(t_0) is not in W.

**Proof.** If c(t_0) lies in one open forbidden quadrant, a neighborhood of it lies in that quadrant. Eventually c(t_n) lies in the same neighborhood and hence in the interior of W, a contradiction. Equivalently, the complement of the open set W is closed. QED.

A corner that realizes the positive roof belongs to this complement: if it were strictly inside any other forbidden quadrant, that quadrant would give a strictly higher roof at the same horizontal coordinate.

## 37.2 The initial excess pattern buries its own initial corner

Suppose the initial exceptional pattern (36.4) occurs. Then

\[
f'(0)=p(0)=0,\qquad g(0)=1,\qquad
\rho_f(0)=q(0)>1.
\tag{37.1}
\]

The last strict inequality follows because rho_f=q strictly decreases on a positive interval where it exceeds one. Let

\[
x_0=f(0)-1,\qquad c(0)=(x_0,0).
\]

For a small positive s, test this fixed point against the two strict inner inequalities of Q_s. Taylor's theorem gives

\[
f(s)-1-c(0)\cdot\mu_s
=\frac{\rho_f(0)-1}{2}s^2+o(s^2)>0,
\tag{37.2}
\]

\[
g(s)-1-c(0)\cdot\nu_s
=q(0)s+o(s)>0.
\tag{37.3}
\]

Indeed the linear term in (37.2) vanishes by f'(0)=0, and its quadratic coefficient is (f''(0)+f(0)-1)/2. The second coefficient is g'(0)+f(0)-1=q(0).

Thus c(0) lies strictly inside Q_s for any sufficiently small fixed positive s. By Lemma 74 it cannot be the limit of active corner points. But the balance argument producing (36.4) requires standard corner activity almost everywhere throughout that initial interval, so such a sequence of active corners exists. This is a contradiction.

The comparison is between c(0) and a **fixed** nearby quadrant after choosing s. It does not assume a uniform angular contact gap as t tends to zero.

## 37.3 The terminal excess pattern gives the reflected contradiction

For the terminal pattern (36.5),

\[
g'(L)=q(L)=0,\qquad f(L)=1,\qquad
\rho_g(L)=-p(L)>1.
\]

Put x_L=1-g(L), so c(L)=(x_L,0). At t=L-s with s>0 small,

\[
f(L-s)-1-c(L)\cdot\mu_{L-s}
=-p(L)s+o(s)>0,
\tag{37.4}
\]

\[
g(L-s)-1-c(L)\cdot\nu_{L-s}
=\frac{\rho_g(L)-1}{2}s^2+o(s^2)>0.
\tag{37.5}
\]

The endpoint corner is therefore strictly inside an earlier forbidden quadrant. Lemma 74 again contradicts the active corners approaching that endpoint.

## 37.4 The completed regular-critical curvature result

**Theorem 75 (curvature cap for regular full-turn critical points).** Assume Section 36.1, including the actual local maximality against the specified feasible support variations, C^2 quarter supports, and a stable finite contact-chart description of the positive niche roof. Then

\[
0\leq f''+f\leq1,\qquad0\leq g''+g\leq1
\quad\text{on }[0,L].
\tag{37.6}
\]

The same holds on the reflected half if its corresponding hypotheses hold. No endpoint-clearance condition p(0)>0 or q(L)<0 needs to be assumed.

**Proof.** Theorem 73 confines any excess to its initial or terminal exceptional pattern. Sections 37.2 and 37.3 rule out those patterns by global corner activity and openness of the forbidden sweep. Nonnegativity is convexity of the hull. QED.

In particular, the high-frequency feasible examples of Note 28 cannot be local maxima **when the regular critical-point hypotheses apply**. Theorem 75 alone does not establish those hypotheses for that family, and does not assign a sign to their area difference from M.

## 37.5 Exact remaining distinction

This is a derivation of the desired density cap from actual stationarity in a defined regular model. It is not a proof of the measure domination needed for every unrestricted maximizing hull. Singular curvature, exposed edges, changes of contact topology, clipping or touching configurations, and partial turning endpoints are not covered by Section 36.1.

The separate contact inequality p<=q is also not supplied by the curvature cap alone. The disk example still separates these two statements. The next calculation must either derive that inequality for critical configurations or treat the configurations where it fails, while the finite-angle/measure passage must justify the regular calculation for general maximizers.
