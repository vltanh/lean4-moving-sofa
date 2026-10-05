# 49. Feasible edge-atom and singular-continuous examples are strictly suboptimal

This tests the measure-valued theorem on actual inputs outside the earlier smooth classes. Both constructions give convex common hulls, preserve the complete two-turn motions, and have areas approaching M from below. One has a genuine exposed-edge atom at a non-axis normal; the other has singular-continuous curvature.

These examples do not contradict candidate optimality. They show why a proof must distinguish feasible near-optimal bodies from maximizers, and they verify that the new repair handles more than large smooth curvature densities.

## 49.1 Adding an interior edge atom

Choose a compact window J strictly inside the candidate's middle phase, small enough for Note 48. Let t_0 be an interior point, and choose a nonnegative smooth cutoff chi supported inside J and equal to one near t_0. Define on the first upper quarter

\[
\delta_\varepsilon(t)=\varepsilon\chi(t)|\sin(t-t_0)|,
\qquad f_\varepsilon=f_*+\delta_\varepsilon.
\tag{49.1}
\]

Leave all other quarters unchanged. Reflection of the perturbation is optional, not required. In distributions,

\[
\delta_\varepsilon''+\delta_\varepsilon
=2\varepsilon\delta_{t_0}
+\varepsilon\left[\chi''|\sin(t-t_0)|
+2\chi'\operatorname{sgn}(\sin(t-t_0))\cos(t-t_0)\right]dt.
\tag{49.2}
\]

The bracket is bounded and is supported away from t_0 wherever chi' is nonzero. The reference curvature density has a strictly positive minimum on J. Thus, for all sufficiently small epsilon>0, the resulting global curvature measure is nonnegative. The unchanged axis neighborhoods and the nonnegative curvature define a compact convex hull with the intended support; it contains the same central face rectangle as the candidate.

There is an exposed-edge atom of mass 2epsilon at t_0. In particular its curvature measure is not dominated by dt on the open quarter. Yet the uniform support perturbation tends to zero, and Theorem 92 supplies a feasible connected canonical envelope E_epsilon with this exact hull. Its other, unchanged turn need not be the reflection of the altered turn.

The transformed wall obstacle has a negative derivative jump at t_0, so its convex minorant differs strictly from it. The repair is therefore nonzero, and (48.4) proves

\[
|E_\varepsilon|<M.
\tag{49.3}
\]

This is a genuinely polygonal feature of the hull inside a protected arc, not an atom at one of the permitted horizontal-face normals.

## 49.2 A singular-continuous perturbation with exact endpoint matching

Choose an atomless singular probability measure nu supported on a compact set J_0 in the interior of J; a rescaled Cantor probability measure is one example. Choose nonnegative smooth bumps chi_L and chi_R, with supports inside J and strictly to the left and right of J_0.

For a measure mu on this quarter, write its two trigonometric moments as

\[
\mathbf m(\mu)=\left(\int\cos t\,d\mu(t),\ \int\sin t\,d\mu(t)\right).
\]

There are positive constants a_L,a_R such that

\[
\mathbf m(\nu)=a_L\mathbf m(\chi_Ldt)+a_R\mathbf m(\chi_Rdt).
\tag{49.4}
\]

Indeed the first coordinate is positive for each measure. The ratio of the second coordinate to the first is a positive cosine-weighted average of tan(t), lying within the tangent range of its support. The ratio for nu therefore lies strictly between the two bump ratios. The two bump moment vectors are linearly independent, and nu's moment vector lies in the interior of their positive cone, proving (49.4).

Put r(t)=a_L chi_L(t)+a_R chi_R(t), tau=nu-r dt, and define

\[
\delta_\varepsilon(t)=\varepsilon\int_{\inf J}^{t}\sin(t-s)\,d\tau(s).
\tag{49.5}
\]

Then

\[
\delta_\varepsilon''+\delta_\varepsilon=\varepsilon\tau.
\]

It is zero before the support of tau. After that support, both it and its derivative are zero because the sine/cosine moments of tau vanish by (49.4). Thus the support perturbation is confined to J and matches the candidate exactly in neighborhoods of both endpoints. Since tau has no atoms, delta_epsilon is C¹; its derivative has bounded variation and its second derivative has a nonzero singular-continuous part.

For f_epsilon=f_*+delta_epsilon the new curvature measure on J is

\[
(\rho_{f,*}-\varepsilon r)dt+\varepsilon\nu.
\tag{49.6}
\]

The reference density is bounded below positively on J and r is bounded, so this measure is nonnegative for sufficiently small epsilon. All other quarters can again remain unchanged. The support perturbation and both derivative traces are O(epsilon), directly from the total variation of tau and the bounded sine/cosine kernels.

This produces another convex hull in Note 48's neighborhood, and hence an actual feasible connected common-hull envelope. Its singular-continuous curvature violates domination by dt. The measure repair is nonzero and gives a strict area deficit exactly as in (49.3).

## 49.3 Area convergence and the negative reduction conclusion

For either construction, the hull supports converge uniformly to h_*. The fixed central rectangle gives a common interior disk, so hull areas converge: the support error bounds the bodies between small dilates about that interior point. On the compact perturbed angular windows, the sine/cosine denominators in the wall-height formulas are bounded away from zero. Their uniform changes tend to zero, and taking a minimum and then a supremum preserves that bound. Thus the niche roof areas converge as well.

Both niches remain separated and inside the same retained rectangle. Exact subtraction therefore proves

\[
\boxed{|E_\varepsilon|<M\quad(\varepsilon>0\text{ sufficiently small}),
\qquad |E_\varepsilon|\longrightarrow M.}
\tag{49.7}
\]

**Corollary 93 (near-optimal feasibility does not exclude singular curvature).** For every fixed A_0<M there are feasible full-turn common-hull bodies of area greater than A_0 with a non-axis curvature atom, and others with singular-continuous curvature. They may keep the candidate's aligned faces and satisfy the strict contact inequality p<q in the one-sided-trace sense. All the examples above are nevertheless strictly suboptimal.

The contact statement follows from Lemma 90 and the positive reference gap; in the explicit constructions the derivative trace change is already O(epsilon). No claim is made that an arbitrary maximizer has such singularities. Rather, excluding them must use maximality or an actual improving operation, not a suboptimal area threshold.

No numerical experiment, solver, or compilation is used in these constructions.
