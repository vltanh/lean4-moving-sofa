# 41. The high-curvature near-candidate family is strictly suboptimal

Note 28 deliberately left the sign of |S_n|-M undetermined. This note resolves that sign by applying an explicitly feasible curvature repair and accounting for its corner-area cost. It also proves a local area-and-uniqueness statement for a class of arbitrarily oscillatory protected support perturbations; a curvature upper bound is not assumed for those perturbations.

This is a genuine improvement operation for that class, not a regular-critical-point assumption. It does not yet control arbitrary perturbations of the switching regions, face normals, both upper quarter functions at once, or partial turning endpoints.

## 41.1 A protected pair of nested intervals

Retain the candidate h_*, its switches beta and b=L-beta, and the aligned face interval [ell,r]. Choose closed nested intervals J_0 inside int(J_1), both containing pi/4 and contained in (beta,b), sufficiently small that the strict margins in Section 28.1 hold on J_1.

They may also be chosen with the following uniform strict inequalities:

\[
p_*<0<q_*<1,\qquad 0<c_{*,y}<1/2,
\]

\[
c_{*,x}(\beta)<B_{*,x}(t)<r,
\qquad D_{*,x}(t)<c_{*,x}(b)\quad(t\in J_1).
\tag{41.1}
\]

The B and D inequalities follow from their strictly increasing abscissae at the candidate and the fact that J_1 lies strictly between the switches. The bound q_*<1 follows, for example, from q_*(beta)=1/(2Y)-1<3/4 and the decreasing candidate q_*. The margin on both baseline intercepts is part of the choice in Note 28.

The wall obstacle phi_* of (40.1) is strongly convex on the corresponding compact s-interval because rho_f,*<1 there. Thus Lemma 79 applies on J_1 to sufficiently small C^1 perturbations supported in J_0.

## 41.2 The actual competitor class

Let delta be C^2, supported in int(J_0), and define h by adding delta to the first upper quarter of h_*, leaving the second upper quarter unchanged, and reflecting the perturbation evenly to the lower half. Assume

\[
\|\delta\|_{C^1}\text{ is sufficiently small},\qquad
\rho_{f,*}+\delta''+\delta\geq0.
\tag{41.2}
\]

There is no upper bound on delta'' in the smallness condition. The last inequality is convexity, not the disputed curvature cap.

The axis traces and face lengths are unchanged. Nonnegative curvature and the unchanged positive face atoms define a convex hull K_h. The strict quadrant-height and baseline-intercept margins imply that every changed positive-height quadrant lies inside the retained central rectangle below y=1/2. The unchanged quadrants already have this property. Reflection supplies a separated upper sweep.

Let S_h be the full canonical saturation. Its central vertical fibers contain a fixed neighborhood of the midline; outside the central rectangle the hull is unchanged by removal. Therefore S_h is compact, connected, and feasible for both full turns. All nonhorizontal extreme points lie on the convex flanks outside the central face interval, and the face endpoints survive. Consequently conv(S_h)=K_h, as in Section 28.3.

## 41.3 Verifying the hybrid roof, rather than assuming it

Only f is changed on the upper half. The path D=c-q mu is unchanged identically, including its strictly increasing x-coordinate. The zeros of p and q remain beta and b because the perturbation is supported away from them and their strict signs persist on J_1. The corner abscissa remains strictly decreasing throughout [beta,b].

Write x_b=c_{*,x}(b) and x_a=c_{*,x}(beta); these endpoints do not change.

**Left portion.** For ell<x<x_b, the unique global maximum of L_t(x) occurs where D_x(t)=x, with t in (0,b). At that point q>=0, so the companion R wall does not cut it off. The full min-wall roof is therefore this unchanged D graph.

**Middle portion.** For x_b<=x<=x_a choose the unique t_0 in [beta,b] with c_x(t_0)=x. For t<=t_0,

\[
D_x(t)\leq D_x(b)=x_b\leq x,
\]

so L_t(x)<=L_{t_0}(x). For t>=t_0, the candidate B_x bound, preserved on the perturbed interval by (41.1), gives B_x(t)>=x_a>=x. Hence R_t(x)<=R_{t_0}(x). The two wall values agree at t_0, proving that the actual roof is the standard corner graph on the middle portion.

**Right portion.** For x_a<x<r, the maximum of R_t(x) over [beta,L] is attained at an interior parameter: its derivative at beta is positive and at L is negative. At any maximizing parameter, x=B_x(t) and p<0, so the companion L wall does not cut it off. Angles below beta cannot do better, since R_t(x) increases up to beta there. Therefore the right roof is exactly the supremum of the R family, even when B_x is no longer monotone inside J_0.

**Outside the faces.** If x<ell, D_x(t)>=ell forces L_t(x)<=L_0(x)=0. If x>r, B_x(t)<=r forces R_t(x)<=R_L(x)=0. Thus no positive niche occurs outside [ell,r]. All uses of B_x bounds inside J_1 follow from the fixed strict margins and C^1 smallness, not from rho_f<=1.

This verifies all parts of the hybrid description required in Section 40.3. It also explains exactly where excessive curvature is allowed: it can create folds in the tangential B parametrization without changing which wall family defines the right roof.

## 41.4 The repaired body is feasible and falls under Theorem 65

Apply Lemma 79 on J_1 and let f_c=f+nu. Its support change vanishes near the interval endpoints, remains C^1-small, and has curvature between zero and one. The unchanged g and all other quarters already satisfy the candidate curvature bounds. The candidate's strict contact gap persists under this C^1-small repair, so p_c<q_c for both halves.

Every interpolation f_z=f+z nu remains a convex support, preserves the aligned faces, and retains the strict quadrant margins. The preceding hybrid-roof argument applies to it as well. Its R supremum stays fixed by the convex-minorant identity, and its D path is fixed identically. Thus its full envelope is genuinely feasible and the gain calculation of Lemma 80 applies, not merely a signed formal area calculation.

For a sufficiently small initial C^1 perturbation, the repair is also C^1-small by Lemma 79. In particular there is a constant eta>0, depending only on the chosen protected interval and candidate, such that

\[
1-q-\nu\geq\eta\quad\text{on }J_1.
\tag{41.3}
\]

The repaired hull has the weak curvature bound and contact inequalities of Theorem 65, so its surviving body has area at most M.

## 41.5 The comparison and its equality case

**Theorem 81 (protected-perturbation optimality without an input curvature cap).** For every perturbation in Section 41.2,

\[
\boxed{
M-|S_h|\geq 2\eta\int_{J_1}\nu\,dt
+\int_{J_1}\nu'^2\,dt\geq0.
}
\tag{41.4}
\]

Equality |S_h|=M holds exactly when delta is identically zero.

**Proof.** The repaired body's area is at most M. Equations (40.5) and (41.3) give its gain over S_h, proving (41.4). If nu is nonzero, its nonnegative continuous values have a positive integral, so the area is strictly below M.

If nu=0, the original h already has the curvature cap and satisfies the other verified hypotheses of Theorem 65. Equality in that theorem forces h=h_*+a cos(theta). The support values at the unperturbed axis normals agree with h_*, so a=0. Thus delta=0. The unperturbed candidate attains M. QED.

This is a local theorem in a specified support neighborhood. It is not local optimality against every Hausdorff-small body perturbation, since its angular support and symmetry restrictions are substantive.

## 41.6 The unresolved sign in Note 28 is now resolved

For the high-frequency family

\[
\delta_n(t)=\frac{1}{2n^2}\eta_0(t)\cos(n(t-t_0))
\]

from Note 28, choose J_0,J_1 enclosing the fixed cutoff support within its protected interval. The C^1 norm tends to zero, convexity holds for large n, and rho_f exceeds one on an open interval. By (40.2) its phi is not convex, so its repair nu_n is nonzero. Therefore

\[
\boxed{|S_n|<M\quad\text{for all sufficiently large }n,
\qquad |S_n|\longrightarrow M.}
\tag{41.5}
\]

The earlier negative conclusion remains valid: near-optimal feasible bodies need not satisfy the curvature cap. What changes is that this family now has a proved area-improving repair and a proved strict deficit, rather than an unknown sign. No numerical area calculation or computer algebra was used.

The operation has not been extended to arbitrary maximizing hulls. In particular, both-family interference, contact switching neighborhoods, endpoint angles, and clipping/degenerate configurations remain outside this argument.
