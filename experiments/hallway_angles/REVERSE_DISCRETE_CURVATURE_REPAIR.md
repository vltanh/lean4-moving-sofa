# A noncircular discrete reverse-wall curvature estimate

**Proved finite-ray algebra and a conditional measure-limit theorem.** This replaces the premature regularity passage in REVERSE_LOCAL_VARIATION.md and REVERSE_PIECEWISE_CURVATURE.md. The condition on a selected sequence below is an explicit hypothesis; the existence of such a sequence for arbitrary feasible reverse maximizers is not asserted here.

Fix 0<e<pi/2, q=sin(e), d=cos(e), and a mesh increment delta with positive sin(e-delta), sin(e+delta). Write u=tan(delta/2). At the current plus facet put sigma=a^+-a^->=0; on the other support family b^-<=b^+. The exact neighboring-line calculations give

    A=u-a^+,
    B=[1-cos(delta)+b^- sin(delta)]/sin(e-delta),
    U=-u-a^-,
    V=[1-cos(delta)-b^+ sin(delta)]/sin(e+delta).

The next wedge removes the tail r>max(0,A,B). The previous wedge removes V<r<U. Therefore the length E left on the current ray after these two deletions is exactly

    T=max(0,A,B),
    E=T-max(0,min(T,U)-max(0,V)).                       (1)

An exposed inner boundary is a subset of that remaining ray, so tau<=E. This conclusion needs no assumed facet-jump rate.

## 1. Keep the self term before taking limits

The identity A-U=2u-sigma gives the universal estimate

    E <= B_+ + V_+ + (2u-sigma)_+.                    (2)

Indeed, a point left after deleting the previous interval is either in [0,B_+], in [0,V_+], or in the gap between U and A. The last gap has length at most (A-U)_+; overlap only improves the estimate. Formula (1) also proves (2) directly in the cases U<=0, U>0.

There is an important strengthening when V<=0:

    E <= max{B_+, (2u-sigma)_+}.                      (3)

If U>=0 the remaining interval has length (T-U)_+; if U<0 then A<=2u-sigma. These give (3). The two error terms are combined by a maximum, not added.

Suppose a finite stationarity estimate sigma<=tau+epsilon is available, epsilon>=0. Then (2) implies

    sigma <= max{H+epsilon,(H+epsilon+2u)/2},
    H=B_++V_+.                                       (4)

When V<=0, (3) instead implies

    sigma <= max{B_++epsilon,u+epsilon/2}.             (5)

Both follow by splitting at sigma=2u. These statements hold before any differentiability or absolute continuity assumption about a limiting support function.

## 2. Uniform regularity from a stated selection hypothesis

Assume convex polygon caps K_n converge in Hausdorff distance to K, have uniformly bounded diameter after translation, and have the stated two adjacent support fans at mesh delta_n->0. Assume the exposed-ray calculation applies at every floating normal and

    sigma_n(t)<=tau_n(t)+epsilon_n(t),
    epsilon_n(t)>=0, sum_t epsilon_n(t)->0.             (6)

On a compact subinterval of (0,e), the arms are uniformly bounded by a constant M. From b^-<=b^+,

    (b^-)_+ + (-b^+)_+ <= max(|b^-|,|b^+|)<=M.

Using positive neighboring denominators in (2), H<=C_e,M delta_n. Equation (4) then gives

    sigma_n(t)<=C'_e,M delta_n+epsilon_n(t).           (7)

Spread each atom over its adjacent mesh cell. Testing against nonnegative continuous compactly supported functions and using the vanishing total error in (6) shows that the limiting curvature measure has a bounded density on every such compact subinterval. No claim about the two strip atoms or terminal atoms is hidden in this interior statement.

Thus the support derivative is locally Lipschitz and the oblique arms are locally absolutely continuous. Convex support convergence to a differentiable limit also gives uniform convergence of the one-sided derivatives on compact interior intervals: bound each derivative between the forward/backward support difference quotients, take n->infinity at fixed quotient step, then use uniform continuity of the limiting derivative. The resulting uniform arm convergence now justifies sign localization. This order avoids the circular inference 'support convergence implies O(delta) facet jumps'.

## 3. A simpler limiting bound

Where b>0, uniform convergence on a compact positive-b neighborhood makes V<0 for all fine meshes. Equation (5), together with the same spread-measure argument, gives

    rho_+ <= max{1/2,b/q}.                            (8)

Where also a>0, A<0 and U<0, so (1) gives tau<=B_+ and the sharper

    rho_+ <= b/q.                                    (9)

Where a>0 with b of either sign, the same argument gives rho_+ <= (b/q)_+. Where a<0 and b>0, A dominates B and U>0, while V<0; hence tau<=(2u-sigma)_+ and rho_+<=1/2.

These are a.e. density statements. No second derivative is evaluated at an arbitrary isolated horizontal tangent.

## 4. Use the actual strip geometry

For support contacts P_+=C+n1+a t1 and P_-=C+n2+b t2 in a strip of actual height w<=1,

    sin(phi)a+sin(e-phi)b
       >= cos(phi)+cos(e-phi)-w >0.                  (10)

Both arms therefore cannot be nonpositive at the same interior parameter. On {b<=0}, continuity and (10) give a>0. Localizing (9) there proves rho_+=0 a.e.; this also handles a positive-measure zero level of b without first assuming a value for its derivative. The reflected argument applies to rho_-.

The resulting conditional density bound is

    0<=rho_+<=k_e(b),    0<=rho_-<=k_e(a),
    k_e(z)=0 for z<=0,
    k_e(z)=max{1/2,z/q} for z>0.                      (11)

On the two-positive-arm set it improves to rho_+<=b/q and rho_-<=a/q. Negative-a regions have rho_- =0 and rho_+<=1/2.

Convexity also gives a,b<=(1+d)/q, since the opposite supporting half-plane contains each support contact. Therefore (11) gives the uniform interior ceiling

    rho_+,rho_- <= (1+d)/q^2 = 1/(1-d).              (12)

All bounds in Sections 2-4 retain hypothesis (6). The missing reverse-cap selection/variation theorem must ensure (6) for the correct objective and admissible domain; it is not supplied by this finite-ray calculation.

## 5. Validation and scope

`reverse_wall_checks.py` checks (1)-(5) with exact rational arithmetic, verifies the four neighboring-line identities in rational orthonormal frames, and checks the support-gap identity (10). These are primitive tests, not a proof of (6), endpoint regularity, or global sofa optimality. No CI or Lean build is used.

The corrected estimates make the analytic bootstrap more precise, but do not by themselves establish nonnegative arms everywhere. See REVERSE_LOCAL_BOOTSTRAP_OBSTRUCTION.md for an exact negative-arm excursion satisfying the local laws.
