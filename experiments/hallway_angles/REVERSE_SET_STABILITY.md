# Quantitative stability of the actual sofa sets

Status: analytic proof draft. This supplies the geometric argument that is deliberately not assumed in `REVERSE_STABILITY.md`. The result concerns arbitrary compact connected competitors, not only convex bodies. The supporting reverse theorem and alignment lemma remain unrefereed and not Lean-checked.

## 1. Uniform Hausdorff stability in the reverse class

There exist constants e_0,d_0,K>0 such that, for 0<e<e_0 and any reverse-class sofa S with

    d=e[V(e)-area(S)]<d_0,

the actual-strip centering and horizontal canonical gauge give

    d_H(A_e S,A_e S_e)<=K sqrt(d).                     (1)

Here A_e(x,y)=(e x,y), and S_e is the explicit class optimizer. No regularity or convexity of S is assumed.

### A. An intermediate containing region with a controlled missing area

Use the unique inside-strip crossing of the canonical corner, and write its rescaled graph as X=g_S(Y) on the actual strip [-w/2,w/2]. Let F_S(Y) be the right boundary of the rescaled outer support cap. Define

    Omega_S={(X,Y): -w/2<=Y<=w/2,
                      g_S(Y)<=X<=F_S(Y)}.

Every interior-height section of S lies in this interval by outer-wall containment and the inner wedge at the matching corner height. The same holds at endpoint heights. If a crossing endpoint is at an interior orientation, both horizontal normal components are positive and the matching-pose argument applies directly. If it occurs at orientation 0, take interior crossing poses tending to 0: a point strictly to the left of the limiting corner has negative first wall coordinate because both its horizontal displacement and its vertical displacement from the interior corner are negative; its second wall coordinate tends to a strictly negative number. The reflected argument handles the other endpoint. Thus S has no exceptional boundary-height spur outside Omega_S.

The graph extends continuously to the two crossing endpoints. The cap is bounded on the strip. Consequently Omega_S is a compact measurable containing region. It is not asserted to be convex or a feasible sofa for all poses.

The outside-excursion argument gives

    area(A_e S)<=area(Omega_S)<=e Q_corrected(C)<=e V(e).

Hence

    area(Omega_S minus A_e S)<=d.                      (2)

This is stronger than merely comparing the area of S with that of the optimizer.

### B. The intermediate region is uniformly close to the convex optimizer

Write T_e=A_e S_e. Its left graph is g_e. Uniform path stability gives rescaled corner error O(sqrt(d)) and width deficit O(d). The candidate's rescaled corner height derivative has a uniform positive lower bound for small e, and its rescaled horizontal derivative is uniformly bounded. Thus matching a height Y to the two crossing paths yields

    sup_{|Y|<=w/2}|g_S(Y)-g_e(Y)|<=K_1 sqrt(d).         (3)

The original canonical path need only be strictly increasing during its inside crossing; no lower derivative bound for that path is needed. In fact, if its crossing parameter is u, its height differs from the candidate height at u by O(sqrt(d)); the candidate inverse is uniformly Lipschitz.

For every relevant rescaled outer normal N, canonicalization gives h=1+N.C. The support offsets therefore differ from those of T_e by at most |N| times O(sqrt(d)). After normalizing N this is an ordinary Euclidean halfplane-offset error O(sqrt(d)).

The convex body T_e is the intersection of its strip halfplanes, the outer support halfplanes, and all left tangent halfplanes to the convex graph g_e. The slopes of g_e are uniformly bounded. Equation (3) thus also bounds the unit-normal offsets of its left constraints. The actual strip differs by only O(d).

There are fixed r,D>0 and a common center z such that B(z,r) is contained in T_e and T_e is contained in B(z,D), for every sufficiently small e. This follows from the explicit convex-body convergence to the interior-bearing limit T in `UNIVERSAL_LIMIT_SHAPE.md`.

The halfplane slack of the inball and (3) imply, for a fixed c and small d,

    z+(1-c sqrt(d))(T_e-z) subset Omega_S
       subset z+(1+c sqrt(d))(T_e-z).                 (4)

For clarity, the first inclusion uses all left tangent inequalities with STRICT inward slack: at a given height it puts X at least K_1 sqrt(d) to the right of g_e(Y), hence to the right of g_S(Y). The second inclusion uses g_S>=g_e-K_1 sqrt(d). The strip loss O(d) is absorbed by the O(sqrt(d)) inward slack. No continuity theorem for arbitrary intersections is being assumed without this inball argument.

### C. The missing-area bound rules out holes of larger radius

The outer inclusion in (4) already gives directed distance from A_e S to T_e of O(sqrt(d)). For the other direction fix p in T_e. By convexity and the inball, moving p a distance O(sqrt(d)) toward z produces, inside the smaller homothetic body in (4), a ball of radius b sqrt(d). Choose the fixed b so pi*b^2>1; the displacement constant can be increased accordingly, while the required homothety remains valid for small d.

That ball lies in Omega_S and has area greater than d. By (2) it cannot be entirely disjoint from A_e S. Thus p lies within O(sqrt(d)) of A_e S. This proves (1).

This step is why thin appendages, holes, and nonconvexity do not invalidate the Hausdorff conclusion. It uses the intermediate region and its inball-based sandwich, not area deficit alone.

## 2. A quantitative universal shape theorem without a motion restriction

There are constants e_1,d_1,K'>0 such that the following holds. Let S be an unrestricted sofa at bend pi-e, with 0<e<e_1 and unrestricted normalized deficit

    D=e[M(pi-e)-area(S)]<d_1.

Then, after an incoming-strip normalization and translation,

    d_H(A_e S,T)<=K'[sqrt(D)+e].                       (5)

The body T is the explicit universal profile in `UNIVERSAL_LIMIT_SHAPE.md`.

Proof: the sharp area asymptotic ensures area(S) is of order 1/e when D is small. The alignment lemma scales S by lambda=1-O(e^2) into an aligned class, losing area O(e). Its area is too large for the O(1) forward bound, so the class is reverse. Since V(e)<=M(pi-e), its normalized reverse deficit obeys

    0<=e[V(e)-area(lambda S)]
       <=D+e[area(S)-area(lambda S)]
       <=D+K_2 e^2.

Apply (1), use d_H(A_e S_e,T)=O(e^2), and undo lambda. The bounded normalized diameter makes undoing lambda cost only O(e^2). The inequality sqrt(D+K_2 e^2)<=sqrt(D)+sqrt(K_2)e proves (5).

## 3. Consequences

For every unrestricted maximizer S at bend pi-e,

    d_H(A_e S,T)=O(e),                                 (6)

uniformly over all maximizers, after the stated normalization. Existence of such maximizers is provided by `HALLWAY_WELL_POSEDNESS.md`.

More generally, any family with area(S_e)/M(pi-e)->1 converges to T. Formula (5) quantifies that convergence in terms of its normalized area deficit. These results classify the limiting shape of the unrestricted problem, although they do NOT prove exact equality M(pi-e)=V(e) or uniqueness of unrestricted maximizers for a fixed e>0.

The square-root rate is established with unspecified uniform constants. No numerical value for K or e_0 is certified here, and no optimality claim for the rate is made.
