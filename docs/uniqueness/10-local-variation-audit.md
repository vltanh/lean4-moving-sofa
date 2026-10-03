# 10. Local support variations, including redundant facets

Date: 2026-10-02. Paper proof. This supplies the mesh-local estimate used in notes 05–06 without assuming that adjacent facets have positive length. No Lean or CI execution is involved.

Write L=pi/2. The uniform mesh is Theta={j delta:1<=j<n}, delta=omega/n. The allowed polygon normals, with duplicates removed, are

    Theta, Theta+L, omega, L, omega+pi, 3pi/2.

For n>=4 all consecutive circular gaps lie strictly between 0 and pi. The first and last upper normals are delta and L+omega-delta. Normal 0 and normal L+omega are NOT polygon facets.

## 1. Exact variation of a positive floating facet

Let h be the actual support function of a polygon with these allowed normals; normals with zero facet length remain in the list. Fix a floating normal t (not omega or L) with facet length ell_t>0. Let a<t<b be its adjacent allowed normals, using a circular lift. Define the sine hat

    H_t(s)=sin(s-a)/sin(t-a)       on [a,t],
    H_t(s)=sin(b-s)/sin(b-t)       on [t,b],
    H_t(s)=0                     outside [a,b], periodically.

For sufficiently small epsilon>0, the intersection obtained by increasing just the assigned height at t by epsilon has ACTUAL support function

    h_epsilon=h+epsilon H_t.                                      (1)

Here is a direct verification, including zero-length neighboring facets. Between adjacent allowed normals a,b, the support of the original polygon is the sine interpolation of h(a),h(b): their supporting lines intersect at the common vertex, even if one or both listed facets have length zero. A continuous piecewise-sine interpolation is convex precisely when its derivative jumps, the facet lengths, are nonnegative. In (1) those jumps change by

    +epsilon/sin(t-a)                       at a,
    -epsilon(cot(t-a)+cot(b-t))             at t,
    +epsilon/sin(b-t)                       at b,
    0                                      elsewhere.

The jumps at a,b only increase. The jump at t stays nonnegative by ell_t>0 and a sufficiently small epsilon. Thus the interpolant is a support function. It has exactly the assigned values at every listed normal and has no other facet normals, so its half-plane intersection is the claimed polygon. Equivalently, this follows by reconstructing the polygon from the nonnegative edge vectors; the closing identity follows from periodicity of the piecewise-sine function.

The resulting polygon contains the old one, and all other sampled supports remain EXACTLY unchanged. Since the fixed strip heights are unchanged, it is still a standard cap. The permitted epsilon can depend on n and the chosen polygon. No uniform lower bound on ell_t or on epsilon is needed: differentiate at fixed n first, and only then let n tend to infinity.

## 2. The penalty sees only O(delta) of the sine hat

Put J_omega=[0,omega] union [L,L+omega]. For omega=L this is [0,pi]. At an ordinary floating facet, H_t is supported on two cells of length delta inside J_omega and is bounded by 1 there.

At the first facet t=delta the preceding circular normal is 3pi/2. The part of the hat on [0,delta] is

    H_delta(s)=cos(s)/cos(delta).

At the last facet t=L+omega-delta the reflected formula holds. Thus for delta<=pi/4,

    0<=H_t<=2 on J_omega,
    length(support(H_t) intersect J_omega)<=2 delta,
    integral_J H_t<=4 delta,
    integral_J H_t^2<=8 delta.                                  (2)

For omega<L one may integrate the selector over the whole interval [0,L+omega], as in note 06: the additional gap (omega,L) has hat zero because both adjacent pinned heights are unchanged.

Suppose |h-h_*|<=M on that interval and

    P(K)=integral (h_K-h_*)^2.

Then (1) gives the exact formula

    P(K_epsilon)-P(K)
      =2 epsilon integral (h-h_*)H_t + epsilon^2 integral H_t^2,

hence

    |D_+P(K; t)|<=8 M delta.                                    (3)

This is the required per-facet estimate. It is valid at the extreme cells and with redundant neighboring facets.

## 3. Approximate balance, with the limits in the correct order

Let K_n maximize A_n-lambda_n P. The finite Nef-polygon calculation gives

    A_n(h+epsilon e_t)-A_n(h)
      =epsilon(sigma_n(t)-tau_n(t))+O_n,t(epsilon^2).

For a floating facet, section 1 identifies these assigned heights with the actual sampled supports. Maximality and (3), followed by epsilon down to zero at FIXED n,t, imply

    sigma_n(t)-tau_n(t)<=8 M lambda_n delta_n.                    (4)

For ell_t=0 the inequality holds without perturbation since tau_n(t)>=0. The O(epsilon^2) coefficient need not be uniform in n: it has already disappeared before the mesh limit. Constants in (2)–(4), unlike that coefficient, are uniform in n.

The first-variation formula used here is the general polygon formula, not its specialization to maximizers: Baek Lemma 3.4.7 and the corrected proof in `MovingSofaOptimality/Balanced/MaximumPolygonCap.lean`. The sine interpolation is the same elementary consecutive-normal geometry used by `inj_consecutive` and `inj_polygon_vertices_at` in `MovingSofaOptimality/Injectivity/DiscreteIneq.lean`.

## 4. Negative result: the full-circle penalty loses this estimate

Replacing P by an integral over ALL normal directions is not an innocuous simplification. At t=delta, the preceding normal is 3pi/2, so the full sine hat occupies an interval of length L+delta below the first facet. For example,

    H_delta(7pi/4)=sin(pi/4)/cos(delta),

which stays bounded away from zero as delta goes to zero. Its full-circle L1 norm is bounded below by a positive constant. Thus no bound of the form integral_circle |H_t|<=C delta holds uniformly. A generic full-circle quadratic penalty gives only O(lambda_n), not O(lambda_n delta_n), at this facet.

The selector in notes 05–06 deliberately integrates the upper support data, which already determine a standard cap. Formula (2), not a nonexistent full-circle estimate, is what justifies the error budget.

This is a counterexample to a proposed estimate, not a competing moving sofa.
