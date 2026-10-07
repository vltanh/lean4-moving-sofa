# Attainment, continuity, and a genuine class-crossing theorem

Status: analytic proof draft. These arguments adapt standard support canonicalization, compactness, and strict-clearance perturbation; no claim is made that these general principles are new. No computation or uniqueness theorem is required for Sections 1-5.

A sofa is a nonempty compact connected planar set admitting a continuous rigid passage between the two unbounded arms of the sharp unit-width hallway. The bend beta lies in (0,pi). Let M, M_plus, and M_minus denote the unrestricted and two aligned-class area suprema.

## 1. Canonical monotone selection

At a body-fixed hallway orientation theta, let its two unit outer normals be n1,n2, and let K=conv(S). Define the canonical inner corner C(theta) by

    n_j.C(theta)=h_K(n_j)-1, j=1,2.

The normals are independent since sin beta>0. If c is any feasible corner, then n_j.C<=n_j.c. Thus for every p in S, n_j.(p-C)>=n_j.(p-c), preserving the inner disjunction, while the canonical outer inequalities follow from the support definition. C(theta) is continuous in theta, S in Hausdorff distance, and beta away from the degenerate endpoints.

Any original continuous orientation path visits every intermediate value between its initial and final lifts. Canonical corners therefore give a feasible monotone orientation path between those same lifts. The initial and final strip constraints are preserved, so straight-arm translations attach. This is a replacement of the motion of the same set, not a convexification of the sofa.

In the unrestricted problem the final lift can further be chosen in [-2pi,2pi]. If the original lift is positive, take its nonnegative representative modulo 2pi; if negative, take its nonpositive representative. The resulting shorter interval was contained in the original visited angle interval, and the final hallway and strip orientations are unchanged modulo 2pi.

## 2. Uniform horizontal diameter bounds for the aligned classes

Normalize the entry strip to 0<=y<=1 and put s=sin(beta/2), c=cos(beta/2).

For the forward midpoint hallway, with corner (x0,z),

    0<=s|x-x0|+c(y-z)<=1.

If z<=0, the horizontal width is at most 2/s. If 0<=z<=1, it is at most 2(1+c)/s. If z>1, the strip/hallway intersection has two separated components. Connectedness forces S into one of them; within either component the horizontal width is at most (1+c)/s. The endpoint z=1 is covered by the middle case. Hence uniformly

    width_x(S)<=L_plus(beta):=2(1+c)/s.

For the reverse midpoint hallway,

    0<=c(x-x0)+s|y-z|<=1.

The horizontal sections have length 1/c and their left endpoints vary by at most s/c over a unit-height strip, since y -> |y-z| is 1-Lipschitz. Therefore

    width_x(S)<=L_minus(beta):=(1+s)/c.

These are diameter bounds, not the sharper earlier area bounds.

## 3. Uniform diameter in the unrestricted problem

The alignment argument in `ALIGNMENT_REDUCTION.md`, Sections 1-3, scales any unrestricted sofa by lambda=cos(delta/2)>=1/sqrt(2) into one of the aligned classes, without changing the body-coordinate directions. Consequently, in an entry-horizontal normalization,

    width_x(S)<=sqrt(2)*max{L_plus(beta),L_minus(beta)}.

Every value function is finite. On a compact interval of bends inside (0,pi), all competitors can therefore be placed, by horizontal and vertical translations, in one common compact rectangle. The disk of radius 1/2 supplies positive-area competitors in either aligned class: at each orientation place its center at wall coordinates (1/2,1/2), so it fits both unit strips; entry and exit translations attach.

## 4. Maxima exist; the values are upper semicontinuous

Fix beta, or let beta_n converge to beta in (0,pi), and choose nearly maximizing sofas S_n. Normalize their entry strips and translate them horizontally into the common rectangle above. Compactness of the hyperspace of nonempty compact subsets gives a Hausdorff-convergent subsequence S_n -> S. The limit is compact and connected.

Lebesgue area is upper semicontinuous under Hausdorff convergence in a common bounded box: S_n is eventually contained in every positive-radius neighborhood of S, whose areas decrease to area(S). Thus area(S)>=limsup area(S_n).

For an aligned class use theta_n(u)=beta_n u or (beta_n-pi)u. Supports and canonical corners converge uniformly for 0<=u<=1, so containment in every closed hallway passes to the limit, as do the endpoint strip constraints.

For the unrestricted problem, first use Section 1 to choose final lifts in [-2pi,2pi]; pass to a subsequence with convergent final lifts and use theta_n(u)=u theta_final,n. The same canonical-corner limit works. At either endpoint the sofa fits the appropriate strip, and the canonical placement has that wall coordinate in [1-width,1], so straight-arm translations again attach.

The limiting set is therefore feasible in the relevant problem. This proves attainment of all three suprema and upper semicontinuity of their values. It does not assume that a limit of arbitrary time-parametrized motions exists.

## 5. The three value functions are locally Lipschitz

Fix a compact bend interval I inside (0,pi). By the diameter bounds, normalize every sofa into a ball of radius R. Canonical corners satisfy

    |C(theta)|<=2(R+1)/sin beta.

This follows by inverting the two-row unit-normal matrix; its smallest singular value squared is 1-|cos beta|.

Take 0<lambda<1 and let a=(1-lambda)/2. Choose d(theta) with n_j.d=-a for both normals and put

    C_lambda(theta)=lambda C(theta)+d(theta).

Then for p in S the two wall coordinates of lambda*p become

    n_j.(lambda*p-C_lambda)=lambda n_j.(p-C)+a.

The maximum wall coordinate is therefore in [a,1-a]. The appropriate individual coordinate at each entry/exit endpoint is in this interval too. Also |d|=a/cos(beta/2), so the shifted corners remain uniformly bounded on I.

Perturb beta to beta'. In an aligned class reschedule the angle linearly to the new aligned endpoint; for the unrestricted problem retain the original final lift. In either case each normal changes by at most |beta'-beta|, uniformly in u. Retain the shifted corner path. Every wall coordinate changes by at most

    K |beta'-beta|,

where one possible uniform choice is

    K=R+2(R+1)/min_I(sin beta)+1/[2 min_I(cos(beta/2))].

Taking lambda=1-2K|beta'-beta|, for sufficiently small differences so lambda>=1/2, preserves hallway containment and the endpoint strip conditions. Thus, for any one of the three value functions f,

    f(beta')>=lambda^2 f(beta)>=(1-4K|beta'-beta|)f(beta).

There is a common finite area upper bound U on I. Swapping beta and beta' gives

    |f(beta')-f(beta)|<=4KU|beta'-beta|

locally. In particular all three value functions are continuous.

The inward shift of BOTH wall coordinates is essential. Uniform scaling alone gives outer-wall clearance but need not separate an inner-wall contact from the forbidden wedge.

## 6. A crossing of optimal class values exists

Combine continuity with `REVERSE_EXTENDED_RESULTS.md`. Define

    Z={beta in (0,pi): M_plus(beta)=M_minus(beta)}.

Then Z is nonempty and compact, and

    Z subset [beta_H,beta_U],
    133.644346372 degrees < beta_H,
    beta_U < 142.098382577 degrees.

The intermediate value theorem supplies a zero because the difference has opposite strict signs on the two outside intervals. Ordered dominance excludes every zero outside the bracket. Closedness and its location inside a compact subinterval give first and last crossing angles.

This is a theorem about optimal values of ENTIRE aligned motion classes, not just a crossing of two locally optimized paths. However Z might have multiple points or intervals. No unique beta_c is proved, and M(beta) need not equal max{M_plus(beta),M_minus(beta)}. Consequently this is not an unrestricted global phase-transition theorem.
