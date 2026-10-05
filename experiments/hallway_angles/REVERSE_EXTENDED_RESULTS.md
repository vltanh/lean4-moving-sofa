# Extended reverse theorem and explicit branch comparisons

Status: mathematical proof draft with exact-integer scalar certificates. This file extends, rather than silently replaces, the round-three theorem. It is not independently reviewed or Lean-checked.

Use the original bend convention, e=pi-beta, and the explicit reverse value V(e). Let

    e_* = arccos(sqrt(2)-1),
    beta_* = pi-e_* = 114.4698005207... degrees.

## 1. Exact reverse-class optimality on a larger interval

For every beta_*<=beta<pi, the entire aligned reverse class has optimum V(pi-beta), with the same unique explicit maximizer, modulo normalized horizontal translation, as in `REVERSE_MAIN_THEOREM.md`.

Proof: `REVERSE_CROSSING_EXTENSION.md` extends the canonical crossing and excursion majorant through e=e_*. The quadratic maximization and candidate realization already hold for every e<pi/2. The remaining three scalar width comparisons now hold on the entire closed interval 0<=e<=pi/2, as certified by `extended_width_certificate.py` using 256 cells. The new formulas divide by cos K+eta sin K rather than cos K, so the endpoint e=pi/2 is removable, not omitted. The original combination of the midpoint bound for w<=1/2 and F_e(w)<V(e) for 1/2<=w<1 therefore applies unchanged. Equality forces full width, the unique quadratic maximizer, and equality of the compact sets.

This theorem still concerns an aligned motion class, not the unrestricted optimum.

## 2. A uniform reverse bound at every obtuse bend

Let r=983/1000. For every pi/2<beta<pi,

    V(pi-beta) <= M_minus(beta) <= V(pi-beta)/r^2.      (1)

The lower bound is the explicit feasible reverse sofa. For the upper bound, shrink any reverse sofa uniformly by r. Scaling the hallway motion about its inner corner preserves containment; the scaled sofa still has a reverse passage and has actual height at most r. The uniform narrow-width crossing lemma now applies at every obtuse bend. The newly certified scalar width comparisons imply that its area is at most V(e). Undoing the area scaling gives (1).

One can replace r by the stronger exact algebraic constant

    r_*=(1+t_*^3)/sqrt(1+t_*^2),
    2t_*^3+3t_*-1=0, t_*>0,

using the minimum established in the crossing file. The simpler rational r is used in the subsequent certificates. Neither bound proves exact class optimality below beta_*.

## 3. A forward lower bound and two exact comparison angles

The circular-notch construction gives, for every 0<beta<pi,

    M_plus(beta)>=H(beta)
      =pi/2+sin(beta)^2/[beta-sin(beta)cos(beta)].       (2)

The function H is strictly decreasing by its explicit derivative. The exact-integer derivative certificate proves V'(e)<0 for all 0<e<pi/2, including uniform control at both endpoint limits. Consequently V(pi-beta) is strictly increasing on the obtuse range.

Define beta_H as the unique root in (120 degrees,135 degrees) of

    H(beta_H)=V(pi-beta_H).

Define beta_U as the unique root in (140 degrees,145 degrees) of

    2 csc(beta_U/2)=V(pi-beta_U).

Existence follows from the certified endpoint signs, and uniqueness from the opposing strict monotonicities. Exact rational degree brackets are

    133.644346372 < beta_H*180/pi < 133.644346373,
    142.098382576 < beta_U*180/pi < 142.098382577.        (3)

These are roots of explicit LOWER/UPPER bound comparisons. Neither is called beta_c or asserted to be the actual optimal-branch crossing.

## 4. Ordered dominance on entire parameter intervals

The following are statements about the suprema of the entire aligned classes:

    M_plus(beta)>M_minus(beta) for 0<beta<beta_H,
    M_minus(beta)>M_plus(beta) for beta_U<beta<pi.      (4)

For beta<=pi/2, the reverse midpoint upper bound is at most sqrt(2), below the feasible forward semicircle area pi/2. For pi/2<beta<=2pi/3, `branch_comparison_certificate.py` certifies

    V(pi-beta)/r^2 < pi/2

on the whole parameter interval, so (1) and the semicircle again give strict dominance. For 2pi/3<beta<beta_H, the exact reverse theorem and (2) apply, and H>V by monotonicity and the root definition.

For beta>beta_U, the exact reverse theorem exceeds the universal forward midpoint bound 2 csc(beta/2), giving the second inequality in (4).

Thus reverse-class optimality is rigorously excluded throughout the previously unresolved 90-to-120-degree region, and indeed all the way to beta_H. This does not identify the unrestricted forward optimizer.

## 5. Consequence for unrestricted bounds

For beta>=beta_* the alignment lemma gives

    V(e)<=M(beta)<=U(e)+1/[4U(e)],
    U(e)=max{V(e),2 csc(beta/2)}.

In particular, the stronger specialization

    V(e)<=M(beta)<=V(e)+1/[4V(e)]

holds for every beta>=beta_U, improving the earlier convenient 143-degree cutoff to an exactly defined threshold.

## 6. Crossing versus phase transition

The continuity theorem in `HALLWAY_WELL_POSEDNESS.md` makes (4) into a genuine existence theorem: there is at least one angle where the optimal aligned-class values agree. Every such angle lies in [beta_H,beta_U]. This is NOT a proof of a unique crossing, and still less an unrestricted global phase transition. The forward branch has not been solved.

## Reproduction

    python extended_width_certificate.py --cells 256
    python branch_comparison_certificate.py --cells 512

The proof functions reject inconclusive cells and root brackets. They use the existing exact-integer arithmetic, rational pi/trigonometric enclosures, and integer square roots. All finite-angle area formulas remain dependent on the analytic proof drafts, not just on scalar certificate success.
