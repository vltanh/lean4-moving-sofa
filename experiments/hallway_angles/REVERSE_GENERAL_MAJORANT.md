# An area majorant for the entire aligned reverse-turn class

This derivation removes the increasing-height and strip-spanning assumptions from `REVERSE_VARIATIONAL.md` when 0 < e=pi-beta <= pi/3. It is independent of the uniqueness proof. A final scalar width comparison is isolated in Section 6 rather than assumed.

## 1. Canonicalization and actual width

Let S be any compact connected sofa of positive area that admits an aligned reverse passage through a unit-width hallway of bend beta. Its orientation need not be monotone: continuity and the intermediate value theorem provide a feasible placement at every orientation phi in [0,e].

Normalize its actual vertical projection to [-w/2,w/2], where 0<w<=1, and let K=conv(S). Set

    n1(phi)=(sin phi,cos phi),
    n2(phi)=(sin(e-phi),-cos(e-phi)).

Use the actual support values h_plus(phi)=h_K(n1(phi)) and h_minus(psi)=h_K((sin psi,-cos psi)). Define the canonical corner C=(x,y) by n1.C=h_plus(phi)-1 and n2.C=h_minus(e-phi)-1.

This corner is feasible for S at every phi. Indeed, for any feasible corner c, the outer-wall inequalities give n_j.C<=n_j.c, so n_j.(p-C)>=n_j.(p-c) for p in S. The inner-corner disjunction remains true, and the canonical outer inequalities hold by the support definition. This argument does not require convexity of S.

Put l=1-w/2 and delta=1-w=2l-1. The canonical endpoint heights are -l and l, not generally -w/2 and w/2. Supports are Lipschitz, hence C is absolutely continuous. Its endpoint abscissae are denoted x0,xe.

## 2. The corner crosses the actual strip only once

At almost every phi in (0,e), let Y_plus,Y_minus in [-w/2,w/2] be heights of the corresponding support points. With psi=e-phi,

    sin(e) y' = (sin psi/sin phi)(cos phi-Y_plus+y)
                 +(sin phi/sin psi)(cos psi+Y_minus-y).       (1)

Whenever -w/2<=y<=w/2 and phi<=e/2, the right side is at least

    (sin psi/sin phi)(cos phi-w)+(sin phi/sin psi)cos psi
      >= (sin phi/[sin psi(1+cos phi)])
           [cos psi(1+cos phi)+cos(psi)^2-1] > 0.            (2)

Here w<=1 was used. For e<=pi/3 both cos phi and cos psi are at least 1/2, and the final inequality is strict at every interior phi. The other half of the interval follows by reflection.

Apply the absolutely continuous chain rule to y clamped to [-w/2,w/2]. Its derivative is nonnegative almost everywhere, and positive when the unclamped height lies strictly inside the strip. Thus there is a single increasing-height crossing from the bottom of the strip to the top; all excursions below precede it and all excursions above follow it. The corner may still make complicated excursions outside the strip. No global monotonicity assumption is made.

## 3. Signed area of outside excursions

For an excursion below the strip write v=y+w/2<=0 and

    a(phi)=x-cot(psi)v
          =[h_minus(psi)-1-(w/2)cos psi]/sin psi.

Differentiating the support function gives

    a'=-(Y_minus+w/2+cos psi)/sin(psi)^2 < 0.               (3)

Integration by parts gives

    integral x dy = [a v+(cot psi)v^2/2]
                    - integral a'v - integral csc(psi)^2 v^2/2.

The two integral terms on the right are nonpositive. Initially v=-delta and finally v=0. Therefore the entire below-strip contribution is at most

    delta*x0 + delta^2*cot(e)/2.                          (4)

Above the strip, set v=y-w/2>=0 and b=x+cot(phi)v. Then

    b'=(-Y_plus+w/2+cos phi)/sin(phi)^2 > 0.

The reflected integration-by-parts argument bounds the above-strip contribution by

    delta*xe + delta^2*cot(e)/2.                          (5)

The formulas are justified on closed subintervals away from any singular endpoint and then by limits. Below-strip excursions do not reach phi=e, and above-strip excursions do not reach phi=0, so their cotangents stay bounded. For w=1 the initial/final boundary terms vanish.

## 4. The area inequality

Let F(Y) be the right boundary of the cap obtained by intersecting the entry strip and all the outer support halfplanes. Its signed area relative to x=0 is Cap(h_plus,h_minus), as in `REVERSE_VARIATIONAL.md`; the formula is valid for h_plus(0)=h_minus(0)=w/2 as well.

At each height in the actual strip, connectedness of S gives a nonempty section. At the pose where the canonical corner has that height, both wall normals have positive x component, so every point of S at that height lies to the right of the corner. Consequently F is at least that corner abscissa, and

    area(S) <= Cap - integral_over_inside_crossing x dy
             <= Q(C)+delta(x0+xe)+delta^2 cot e.           (6)

The nonempty-section argument is important: dropping it and integrating potentially negative widths would be invalid.

The cap-area identity for nonsmooth convex K follows by smooth approximation of its support function in H^1, or by the Stieltjes boundary-area formula. Only the identity is approximated; no claim that smoothing preserves a feasible motion is needed. The support and corner calculations in (1)-(5) hold almost everywhere, which suffices for the integrals and the clamping argument.

## 5. Maximize the corrected functional

The right side of (6) is horizontal-translation invariant. In the gauge x0+xe=0 it is

    Q(C)+(2l-1)^2 cot e,

with y endpoints -l,l. The strict quadratic concavity proof in `REVERSE_QUADRATIC_THEOREM.md` is unchanged: its Hessian is independent of these endpoint heights. The symmetric stationary solution is obtained by replacing

    B by -(l-a/m)/[s(cos K+eta sin K)],
    A by (l c+r B sin K)/s.

Its corrected maximum F_e(w) is a quadratic polynomial in w. Writing d=cos e, q=sin e, m=2-d, T=eta tan K, it is

    F_e(w)=e/m + [c0+c1 w+c2 w^2]/q,                    (7)

where

    c0= -[T d^2-4T d-2T+d^2-4d+4]/[(T+1)m^2],
    c1= -2[T d+T+d-2]/[(T+1)m],
    c2= [2T d+3T+2d-3]/[4(T+1)].

In particular F_e(1)=V(e), the candidate value. The loose endpoint estimate F_e(0) is not zero and can exceed V(e); ignoring the width issue would invalidate a full-class optimality claim.

## 6. The remaining scalar comparison

The midpoint slicing bound, with the actual width retained, is

    area(S) <= w csc(e/2).                              (8)

It is sufficient to prove the following two scalar inequalities for 0<=e<=pi/3, interpreting continuous endpoint limits:

    V(e) sin(e/2) > 1/2,
    F_e(1/2) < F_e(1)=V(e).                             (9)

The first handles w<=1/2 by (8). For w in [1/2,1], write l=1-w/2 in [1/2,3/4]. The derivative of the quadratic corrected maximum at l=1/2 is strictly negative by exactly the trigonometric inequality already proved in the free-endpoint concavity argument. Together with its endpoint comparison in (9), this implies it is strictly below V(e) for 1/2<=w<1, regardless of the sign of the quadratic coefficient.

Thus (9), once established, proves area(S)<=V(e) for every sofa in the full aligned reverse class, with strict inequality if its actual width is below 1. The geometrically feasible candidate would then attain this bound; equality in the strict quadratic theorem would force its canonical corner path and hence its shape.

The scope remains an entire *aligned reverse-turn class*, not all motions in the unrestricted oblique moving-sofa problem. No forward/reverse exhaustiveness theorem is assumed.
