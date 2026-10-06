# Flat contacts eliminate the alignment loss near reversal

**Status:** a new analytic proof draft. This argument depends on the uniform ACTUAL-SET stability theorem in `REVERSE_SET_STABILITY.md`, not just on path stability or a numerical Hessian. The underlying cap/majorant and stability proofs require independent review. No numerical bend threshold, Lean verification, or CI run is claimed.

Write e=pi-beta, let S_e be the exact reverse optimizer, V(e)=area(S_e), and put T_e=A_e S_e with A_e(x,y)=(e x,y).

## 1. The geometric feature missed by the width-polynomial shortcut

The normalized candidate T_e contains the four points

    (0,-1/2), (l_e,-1/2), (0,1/2), (l_e,1/2),

where l_e=e h_e'(0) is its horizontal contact-segment length. The explicit limit gives

    l_e -> l_0=3(1-T0)/[2(1+T0)]>0.

Consequently, for every signed mismatch angle nu with |nu|<=pi/2, and

    N_nu=(sin(nu)/e,cos(nu)),

its directional width satisfies

    width(T_e,N_nu)>=cos(nu)+l_e |sin(nu)|/e.          (1)

For positive sin(nu), use the top-right and bottom-left points; for negative sin(nu), use the other pair. Thus a small angular mismatch causes a LINEAR width penalty of order |nu|/e. Uniform alignment scaling, in contrast, loses only a QUADRATIC proportion of area in nu.

## 2. Uniform constants available from the previous theorems

For some e_0>0 and fixed positive c_0,c_1,l_*,K,d_*, all 0<e<e_0 satisfy

    c_0<=e V(e)<=c_1,  l_e>=l_*,
    d_H(A_e R,T_e)<=K sqrt(d),
    d=e[V(e)-area(R)] in [0,d_*),                     (2)

for every aligned reverse sofa R, after the prescribed translations. The Hausdorff theorem imposes no convexity or smoothness on R. Make e_0 smaller as necessary below; the constants remain uniform.

## 3. No unaligned sofa of area at least V(e) for sufficiently small e

Let S be an UNRESTRICTED sofa with area A>=V(e). Normalize the incoming strip horizontally, and let nu in [-pi/2,pi/2] be the unoriented normal mismatch between the entry and final exit strips of any complete passage. Both widths of S are at most one. The intersection-of-strips area bound gives

    |sin nu|<=1/A<=e/c_0,
    |nu|<=B e,  B=pi/(2c_0).                          (3)

The alignment lemma takes lambda S, lambda=cos(nu/2), to an aligned class. Its area is at least A/2, which exceeds the bounded forward midpoint estimate for sufficiently small e. Hence it is in the reverse class, and lambda^2 A<=V(e).

Its normalized reverse deficit therefore satisfies

    0<=d=e[V(e)-lambda^2 A]
       <=e V(e)(1-lambda^2)
       <=c_1 nu^2/4.                                 (4)

By (3) this lies within the stability range for small e. Write R=lambda S with the translations needed for (2); widths are unaffected by those translations. The original exit strip implies

    width(A_e R,N_nu)<=lambda.

For compact sets, directional widths differ by at most twice the direction norm times their Hausdorff distance. Also |N_nu|<=N_0=sqrt(1+B^2), by (3). Using (1), (2), and (4),

    lambda>=cos nu+l_* |sin nu|/e-K sqrt(c_1) N_0 |nu|.

Since lambda-cos nu<=1-cos nu<=nu^2/2 and |sin nu|>=2|nu|/pi, every nonzero nu would imply

    2l_*/(pi e)<=|nu|/2+K sqrt(c_1) N_0
               <=B e/2+K sqrt(c_1) N_0.               (5)

The left side tends to infinity while the right side stays bounded. Choosing one fixed sufficiently small e_1>0 rules out (5) simultaneously for all 0<e<e_1. Thus nu=0.

When nu=0 the alignment scaling is the identity. S itself belongs to an aligned class, necessarily reverse by its area, so A<=V(e). Therefore A=V(e), and reverse-class uniqueness gives S congruent to S_e.

There is no circular use of unrestricted optimality here: (3)-(5) apply to an arbitrary hypothesized feasible competitor with A>=V(e). Sofas of smaller area need no exclusion, and the explicit S_e already attains V(e).

## 4. Exact unrestricted theorem

There exists e_1>0 such that for EVERY 0<e<e_1,

    M(pi-e)=V(e),

and every maximizing compact connected sofa is congruent to the explicit S_e. Neither its motion nor its shape is assumed aligned, monotone, convex, or symmetric. Moreover the entry and exit strips of every complete passage of a maximizer have parallel unoriented normals.

This solves the unrestricted problem exactly on a nonempty interval of bends immediately below pi. It does NOT identify a numerical left endpoint of that interval. The current proof supplies uniform constants existentially from explicit formulas and geometric inequalities; their numerical propagation has not been carried out. In particular it does not assert that the result starts at 143 degrees, 150 degrees, or at the observed numerical branch crossing.

## 5. Quantitative alignment and stability for arbitrary near-maximizers

After possibly decreasing e_1, there are uniform K_1,D_*>0 with the following property. Let S be any unrestricted sofa at bend pi-e, with

    D=e[V(e)-area(S)] in [0,D_*).

Then every complete passage has entry/exit mismatch

    |nu|<=K_1 e sqrt(D),                               (6)

and, after incoming-strip normalization and translation,

    d_H(A_e S,T_e)<=K_1 sqrt(D).                        (7)

Indeed D small makes e*area(S) bounded above and below by positive constants. The same strip-area estimate yields |nu|<=B_1 e. Alignment again leads to a reverse sofa R=lambda S. Its deficit satisfies

    d=e[V(e)-lambda^2 area(S)]
      =D+e*area(S)(1-lambda^2)
      <=D+c_1 nu^2/4.

The directional-width argument now gives

    2l_* |nu|/(pi e)
      <=nu^2/2+2K N_1 sqrt(D+c_1 nu^2/4)
      <=nu^2/2+2K N_1 sqrt(D)+K N_1 sqrt(c_1)|nu|.

Use nu^2<=B_1 e |nu| and absorb the two terms linear in |nu| into the left side for uniformly small e. This proves (6). It follows that d<=C_1 D, so (2) controls A_e R by O(sqrt(D)). Undoing lambda costs O(nu^2)=O(e^2 D), since the normalized sets have a uniform diameter bound. This proves (7).

Thus the earlier O(sqrt(D)+e) unrestricted shape estimate improves to a pure square-root deficit estimate relative to the FINITE-ANGLE exact optimizer. Relative to the limiting body T it becomes O(sqrt(D)+e^2), because d_H(T_e,T)=O(e^2).

## 6. Why the earlier negative result is not contradicted

The failed comparison F_e(lambda)<=lambda^2 V(e) uses only a scalar width majorant. It does not use that a nearly optimal shape has two positive-length flat contact segments. The present proof compares widths in TWO directions, relates their mismatch to area through alignment, and uses actual-set stability. Its linear-in-angle obstruction can dominate the quadratic scaling loss; the scalar polynomial alone cannot.

## Review and reproducibility limits

No numerical search, sampled collision test, or exact scalar root certificate proves (2) or the geometric width argument. They are analytic inputs. The delicate dependencies are the intermediate-region Hausdorff stability proof and its uniform constants as e tends to zero. The limit contact length is explicit and positive. Local tests check the contact-width inequality and the scaling-deficit algebra as regression evidence, not as a formal verification of this theorem.
