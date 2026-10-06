# Explicit quantitative rigidity of near-optimal passages

**Analytic proof draft with exact-rational constant checks.** This is an additional consequence of the contact-rectangle proof, not a use of the existential Hausdorff constants. It assumes the exact reverse-class majorant and explicit global theorem in `EXPLICIT_GLOBAL_CUTOFF.md`.

## Theorem

Let 0<e<=1/100, beta=pi-e. For an arbitrary compact connected feasible sofa S set

    D=e[V(e)-area(S)]>=0.

Let nu in [-pi/2,pi/2] be the unoriented mismatch between the incoming and final exit strip normals of ANY complete passage. If D<=1/10000, then

    |nu| <= 40e sqrt(D),                              (1)
    1-w_S <= 11D,                                    (2)

where w_S is its actual width perpendicular to that passage's incoming arm.

For the aligned scaled sofa R=cos(nu/2)S, actual-strip centering and the horizontal canonical gauge give explicit path estimates

    sup |e(C_Rx-C_*x)| <= 3sqrt(D),
    sup |C_Ry-C_*y| <= 2sqrt(D).                       (3)

The original S need not be convex or aligned. No uniqueness of intermediate motions is claimed.

An equivalent useful area-penalty consequence, now valid for ALL feasible S, is

    V(e)-area(S) >= min{1/(10000e), nu^2/(1600e^3)}.    (4)

The first branch simply handles sofas outside the near-optimal deficit range; the second follows by rearranging (1). In particular any nonzero mismatch enforces a strictly positive area loss. This is not a claim that the rate or constants are sharp.

## Proof

Write n=|nu|. The global theorem supplies D>=0. For D<=1/10000 the same strip-area and alignment argument as before gives

    n<=3e/4,
    R=lambda S is reverse, lambda=cos(n/2),
    d=e[V(e)-area(R)]<=D+(17/50)n^2.                  (5)

The sine comparison now uses e*area(S)>=27/20-1/10000; `explicit_motion_rigidity.py` checks its strict rational margin. The area of R exceeds the forward bound by a large margin.

For e<=1/100, (5) gives d<=1/10000+(17/50)(3/400)^2. Its square root is less than 9/800. Equations (2)-(3) of `EXPLICIT_PATH_CONSTANTS.md` and the contact-core lemma therefore provide a rectangle Q whose width and height satisfy

    W>=9/40, H>=19/20,
    area(Q minus A_e R)<=d.                           (6)

Put a=sin n/e and b=cos n when n>0. As before,

    (999/1000)n/e<=a<=3/4, 99/100<=b<=1.

The vertical triangular-cap condition d<bH^2/(2a) follows immediately from the fixed bounds in (5)-(6). The horizontal condition needs a case distinction: it must not be assumed automatically when D>0 and n is very small.

### Case 1: the horizontal triangular-cap condition fails

Then d>=aW^2/(2b), so (6) implies

    n <= 40e d <= 40eD+(68/5)e n^2.

Use n<=3e/4, e<=1/100, and absorb the last term. The exact rational comparison gives

    n<=41eD<=40e sqrt(D).

The latter follows from sqrt(D)<=1/100. This also covers the limiting zero-deficit case by the same absorption argument.

### Case 2: both triangular-cap conditions hold

The directional-width lemma and the original exit strip imply

    ell_e a <= n^2/2+2a eta_x+2b eta_y+2sqrt(abd),

where eta_x=(5/2)sqrt(d)+(7/2)d and eta_y=(17/10)sqrt(d)+5d. Since a<=3/4 and b<=1,

    (143/500)(999/1000)n/e
       <= n^2/2+9sqrt(d)+(61/4)d.

Use sqrt(d)<=sqrt(D)+(7/12)n in (5). Since D<=sqrt(D)/100,

    [(143/500)(999/1000)-(21/4)e-(1137/200)e n] n/e
       <= (3661/400)sqrt(D).                          (7)

At e<=1/100, n<=3e/4, forty times the positive bracket in (7) exceeds 3661/400. The exact margin at the worst endpoint is 31801/200000>0. This proves (1). For n=0 it is immediate.

### Width and path consequences

Equation (1) improves (5) to

    d <= [1+544e^2]D <= (659/625)D.

The actual width of S is at least that of lambda S, so the width estimate for R gives 1-w_S<=10d<=11D, proving (2). Also sqrt(659/625)<103/100. Applying the explicit path estimates, and again using D<=sqrt(D)/100, gives (3), with room in both constants.

Finally, if D>=1/10000 then the area loss is at least 1/(10000e). Otherwise square (1) and divide by e. This proves (4) for every feasible S, not just near-maximizers.

## Exact checks and limitations

```sh
python explicit_motion_rigidity.py --cells 256 --output motion-rigidity.json
```

The program rechecks the whole [0,1/10] scalar cover and verifies all remaining constant comparisons with exact fractions. The proof still needs the analytic geometric arguments to relate d to a missing area. No claim of a numerical solution to the forward class, the middle-angle phase transition, or the best possible global cutoff is added.
