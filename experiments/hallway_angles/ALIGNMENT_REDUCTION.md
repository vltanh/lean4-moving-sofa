# From arbitrary passages to aligned classes: an asymptotically lossless reduction

This argument concerns the unrestricted sharp, unit-width oblique hallway. It does not assume that an optimizer already belongs to either aligned full-rotation class. It supplies an area comparison rather than an exact reduction preserving area.

## 1. Width interpolation in a straight strip

Let a compact set S fit inside two unit-width infinite strips whose unoriented normal directions differ by delta in [0,pi/2]. Their offsets may differ. For any intermediate normal n_theta,

    n_theta = [sin(delta-theta)/sin delta] n_0
                + [sin theta/sin delta] n_delta.

The width function is sublinear and even, so

    width_S(n_theta) <= cos(theta-delta/2)/cos(delta/2)
                       <= sec(delta/2).

The delta=0 statement is immediate. Hence lambda*S, with lambda=cos(delta/2), can be rotated between those two orientations inside a unit-width straight corridor. A continuous centering translation is obtained from the maximum and minimum transverse support values. Because S is bounded and the rotation interval compact, the maneuver can be performed arbitrarily far down an unbounded corridor arm, away from the junction.

## 2. Scaling preserves the original passage

With the inner corner at the origin, the hallway is

    H={p : 0 <= max(n1.p,n2.p) <= 1}.

For 0<lambda<=1 one has lambda*H subset H. If the original passage is R(t)S+a(t), the scaled passage is R(t)(lambda*S)+lambda*a(t). Thus the scaled sofa follows a feasible continuous rigid motion. This is uniform scaling, not an affine shear.

## 3. Alignment by an exit rotation

Normalize the initial body-fixed hallway orientation to 0. Let theta_f be a continuous lift of its final orientation, after the sofa is wholly in the exit arm. Choose an integer j so

    delta_signed = beta-theta_f-j*pi in [-pi/2,pi/2],
    delta=abs(delta_signed).

In body coordinates, the sofa fits the initial strip and the final exit strip, whose unoriented normals differ by delta. After scaling by cos(delta/2), Section 1 permits an additional exit-arm rotation so that the final lifted hallway angle becomes beta-j*pi.

If j<=0, the continuous orientation path passes through every angle between 0 and beta. If j>=1, it passes through every angle between beta-pi and 0. In the first case the scaled sofa belongs to the aligned forward class; in the second it belongs to the aligned reverse class. Repeated rotations and nonmonotone orientation paths are included. A continuous canonical hallway selection follows from support functions: at each required angle, replace a feasible corner by the intersection of the two outer support lines shifted inward by one unit. This preserves feasibility and depends continuously on angle.

This proves that some scaling by cos(delta/2) of every unrestricted sofa belongs to one of the two classes. It does NOT prove that the unscaled sofa does.

## 4. Area-dependent loss

Write A=area(S). If delta>0, S lies in the intersection of the two unit-width strips, a parallelogram of area csc(delta). Thus A<=csc(delta). For A>1 this gives

    cos(delta)>=sqrt(1-A^(-2)),
    area(lambda*S)=A cos(delta/2)^2
                 >= [A+sqrt(A^2-1)]/2.                  (1)

For delta=0, lambda=1 and the same inequality holds. If U>=1 is any upper bound for both aligned classes, (1) implies

    A <= U+1/(4U).                                      (2)

Sofas of area at most 1 satisfy (2) directly. No existence of an unrestricted maximizer is assumed: (2) applies to every feasible compact connected set and hence to the supremum.

## 5. Explicit unrestricted bounds near reversal

Let e=pi-beta, 0<e<=pi/3. The exact reverse-class theorem gives M_minus(beta)=V(e). The midpoint bound gives M_plus(beta)<=2 sec(e/2). Set

    U(e)=max{V(e), 2 sec(e/2)}.

For the unrestricted supremum M(beta),

    V(e) <= M(pi-e) <= U(e)+1/(4U(e)).                   (3)

The lower bound is the explicit feasible reverse sofa. Once V(e)>2 sec(e/2), (3) reduces to

    V(e) <= M(pi-e) <= V(e)+1/(4V(e)).                   (4)

The inequality V(e)>2 sec(e/2) holds for all sufficiently small e because V(e) diverges while 2 sec(e/2) tends to 2. No numerical crossing or monotonicity assertion is needed for this conclusion.

## 6. Sharp asymptotics for the unrestricted problem

Set

    T0=tan(sqrt(3)/2)/sqrt(3),
    C=3(1+3T0)/[4(1+T0)] = 1.35653373245229... .

The exact reverse-class expression simplifies to

    V(e)=e/(2-d)+(1+2d)/(4q)
          +[3d^2/(2q(2-d)^2)]*[eta sin K/(cos K+eta sin K)],

where d=cos e, q=sin e, eta=sqrt((2-d)/(2+d)), and

    K=(1/2)sqrt(e^2+3(e/sin e)^2).

All factors after multiplying by e extend analytically and evenly to e=0. Substitution gives

    V(e)=C/e+O(e).

Combining with (4) gives the unrestricted theorem

    M(pi-e)=C/e+O(e),
    lim_{e->0+} e M(pi-e)=C.                             (5)

In particular, this asymptotic statement does not assume full rotation, convexity, symmetry, or a monotone motion for the original sofa. The exact value V(e), by contrast, is asserted only for the aligned reverse class. The difference between the unrestricted optimum and the explicit reverse construction is at most 1/(4V(e))=O(e) near reversal.

## Review status

This is a newly derived proof in the research branch, not an independently refereed or Lean-checked theorem. Its sharp constant depends on the reverse-class upper bound, including the variable-width argument and the exact-integer scalar certificates. The scaling/width interpolation argument itself does not use numerical computation or uniqueness machinery.
