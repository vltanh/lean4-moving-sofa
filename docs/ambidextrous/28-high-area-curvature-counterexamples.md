# 28. Arbitrarily high-area feasible bodies need not satisfy the curvature cap

**Subsequent result:** [Note 41](41-resolving-the-high-curvature-family.md) now proves that these bodies have area strictly below M for all sufficiently large n, using an actual feasible curvature repair. The construction and its negative conclusion below remain valid: area arbitrarily close to M does not force the curvature cap. The former unresolved area-sign question is no longer open for this family.

This is a negative result about a proposed structural reduction. Full quarter turns, symmetry, aligned faces, smooth quarter supports, the contact inequality p<=q, and area arbitrarily close to M do **not** force h''+h<=1. The missing curvature theorem must use actual maximality or a valid area-improving replacement, not just feasibility and a fixed area threshold below M.

The construction is analytic. No numerical experiment or symbolic computation is used. The strict area comparison is supplied separately by the repair argument in Note 41, rather than inferred from convergence of areas.

## 28.1 A protected candidate interval

Use the candidate constants and support h_* from Note 14. Put t_0=pi/4, k=1-4A/3, and

\[
m=c_{*,y}(t_0)=1/2+R-\sqrt2.
\]

Notes 4 and 18 show 0<m<1/2 and A>3/4. The common exposed-face interval is

\[
[\ell,r]=[k-2A/3,k+2A/3].
\]

At t_0 the two intersections of the lower forbidden quadrant's boundary rays with y=0 have x-coordinates k-m and k+m. Both lie strictly inside [ell,r], because 2A/3>1/2>m.

The candidate curvature density of the first quarter at t_0 is

\[
\rho_*(t_0)=\frac{3R}{4\sqrt2}>\frac12,
\]

using R>2sqrt(2)/3 from Note 4. It is also strictly less than one. By continuity, choose a compact interval J around t_0, strictly inside (beta,pi/2-beta), and eta_0>0 such that:

- rho_*(t)>=1/2+eta_0 on J;
- c_{*,y}(t) is positive and strictly below 1/2 on J;
- both baseline intercepts of its quadrant lie strictly inside (ell,r), with a common positive margin.

For a corner c(t), those intercepts are
\(c_x-c_y\cot t\) and \(c_x+c_y\tan t\).
All three assertions are strict inequalities at t_0, so such a J exists without choosing numerical endpoints.

## 28.2 Small support displacement with non-small curvature change

Choose a smooth cutoff eta supported in the interior of J and equal to one on a smaller interval J_0 containing t_0. On the first quarter set

\[
\delta_n(t)=\frac{1}{2n^2}\eta(t)\cos(n(t-t_0)).
\tag{28.1}
\]

Set delta_n=0 on the other upper quarter and extend by delta_n(-theta)=delta_n(theta) to the lower half. Define h_n=h_*+delta_n.

The perturbation vanishes in neighborhoods of every coordinate-axis normal and of the original contact switches. Thus the face intervals, all endpoint traces, and vertical span remain unchanged. Its C^0 norm is O(n^-2) and its quarterwise C^1 norm is O(n^-1).

On its support,

\[
\delta_n''+\delta_n
=-\tfrac12\eta(t)\cos(n(t-t_0))+O(n^{-1}),
\tag{28.2}
\]

with a uniform error bounded explicitly by the fixed cutoff's first two derivative norms. Therefore h_n+h_n'' remains nonnegative for all sufficiently large n: on J it is at least eta_0/2, and outside the perturbation it is the unchanged nonnegative candidate curvature. The reflected quarter has the same property. The two positive face atoms are unchanged. Lemma 43 therefore constructs a compact convex hull K_n with support h_n.

On J_0, at a point where cos(n(t-t_0))=-1,

\[
\rho_n(t)=\rho_*(t)+\tfrac12-\frac{1}{2n^2}>1
\]

for all sufficiently large n. Such points occur in J_0, and continuity makes the inequality hold on intervals of positive length. Thus the curvature cap fails genuinely, not only at an isolated parameter.

The candidate gap q_*-p_* has a strictly positive minimum on the compact quarter interval, as verified in Note 16. Since the C^1 perturbation tends uniformly to zero, both reflected halves still satisfy p_n<q_n for large n. Reflection symmetry is preserved by construction.

## 28.3 Feasibility and retention of the whole hull

The canonical corner depends on h, not on its second derivative. Its perturbation on J is delta_n(t)mu_t; elsewhere on the lower turn the corner is unchanged. For large n, all perturbed corners on J retain the strict height and baseline-intercept margins in Section 28.1.

At an angle in (0,pi/2), the part of a downward forbidden quadrant above y=0 is the open triangle with its corner as apex and the two baseline intercepts as base endpoints, provided the corner height is positive; it is empty if that height is nonpositive. Consequently every modified positive-height quadrant lies inside [ell,r] times [0,1/2). The unmodified candidate quadrants already have that property by Notes 4 and 18. Reflection gives the upper sweep inside [ell,r] times (1/2,1].

Because K_n has the same aligned top and bottom faces, it contains the whole rectangle [ell,r] times [0,1]. Remove the two open sweeps from K_n and call the result S_n. Its central vertical fibers contain a fixed neighborhood of y=1/2; outside [ell,r] no part of K_n is removed. All fibers over its horizontal projection are therefore nonempty intervals. The interval-fiber argument proves compactness and connectedness.

Every subset of this canonical envelope satisfies both full-turn hallway constraints and their endpoint strips. Thus S_n is an ambidextrous body. Moreover every extreme point of K_n survives: nonhorizontal extreme points lie on the flanks outside the interior of the central rectangle, and all four face endpoints survive. A compact convex body is the convex hull of its extreme points, or equivalently its support values are attained at retained face endpoints/extreme points. Hence

\[
\operatorname{conv}(S_n)=K_n.
\tag{28.3}
\]

This verifies a genuine common-hull example, rather than an arbitrary support perturbation with unproved feasibility.

## 28.4 Area tends to the candidate value

For the modified angle interval J, the two wall-height functions in Note 17 have denominators bounded away from zero. Their changes are uniformly O(n^-2), so the change in their minimum is uniformly O(n^-2). Taking a supremum over angles preserves this bound; the unmodified angles contribute identical functions. Thus the lower niche roof changes uniformly by O(n^-2) on [ell,r], and the reflected upper roof has the same bound.

The convex bodies K_n converge to K_* in Hausdorff distance, by uniform convergence of support functions. Their areas converge as well. One direct justification uses the fixed rectangle contained in every K_n: after choosing an interior point as origin, all contain a fixed-radius disk. A support error epsilon then sandwiches one body between the (1+/-epsilon/r)-dilates of the other, for sufficiently small epsilon, and the areas converge.

Both niches remain inside the central rectangle and separated, so exact subtraction gives

\[
|S_n|\longrightarrow|\Sigma_*|=M.
\tag{28.4}
\]

In particular, for every A_0<M all sufficiently large S_n have area above A_0 while their hull curvature exceeds one on a set of positive angular measure.

## 28.5 The precise negative conclusion and its later refinement

**Theorem 60 (no suboptimal-threshold curvature reduction).** No assertion of the following form is valid for any fixed A_0<M:

> Every full-turn, unit-span feasible ambidextrous body of area greater than A_0, with a reflection-symmetric common hull, aligned exposed faces, regular quarter supports, and p<=q, has curvature density at most one on the open quarters.

The bodies S_n disprove it. Their high-frequency support perturbations are small in C^1 but not in second derivative, which is exactly the distinction the false inference misses.

The convergence proof above alone establishes neither sign of |S_n|-M. The subsequent convex-minorant repair in [Theorem 81](41-resolving-the-high-curvature-family.md) now establishes |S_n|<M for all sufficiently large n. Thus the family remains a counterexample to the threshold-based structural inference, not to candidate optimality.

Theorem 52 and its weak-bound extension, Theorem 65, are unaffected because the original S_n violate their curvature hypothesis. The new repair raises their support, restores that bound, and strictly increases actual area while preserving feasibility; its corner-area cost is included explicitly. It has not yet been extended to every unrestricted maximizing hull.
