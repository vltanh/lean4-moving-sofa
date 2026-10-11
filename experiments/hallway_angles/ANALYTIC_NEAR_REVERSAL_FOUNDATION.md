# A purely analytic foundation for the near-reversal theorem

Status: proof-dependency clarification and analytic lemma. The exact unrestricted theorem for SOME interval immediately below pi does not require running any integer interval checker. The checkers remain useful for the larger explicit reverse-class range and the numerical brackets on comparison roots.

The argument here deliberately makes no claim about a numerical global cutoff. It establishes uniform signs in a sufficiently small interval by strictly positive analytic endpoint limits.

## 1. Elementary bounds on the one limiting constant

Let a=sqrt(3)/2 and T0=tan(a)/sqrt(3). Since tan(a)>a,

    T0>1/2.

Alternating Taylor estimates give

    sin(a)<=a-a^3/6+a^5/120=563a/640,
    cos(a)>=1-a^2/2=5/8.

Therefore

    1/2<T0<=563/800<13/17<1.                          (1)

All bounds follow from exact rational arithmetic and elementary Taylor remainders; no numerical evaluation is needed.

## 2. All width comparisons hold near zero by strict endpoint limits

For the exact quadratic value V(e) and width majorant F_e(w), the coefficients after multiplying by e extend continuously to e=0. The limiting polynomial is

    f_0(w)=[(5T0-1)+2(1-2T0)w+(5T0-1)w^2/4]/(1+T0).

Its value at one is

    C=f_0(1)=3(1+3T0)/[4(1+T0)]>1,

where the last inequality follows from T0>1/2. Hence

    e[V(e)-1/(2sin(e/2))] -> C-1>0.                   (2)

The other required width comparisons have limits

    e F_e'(1) -> 3(1-T0)/[2(1+T0)]>0,
    2e[V(e)-F_e(1/2)] -> (13-17T0)/[8(1+T0)]>0.      (3)

By continuity, (2)-(3) hold with uniform positive margins for all sufficiently small e>0. They give the original midpoint/quadratic width argument and the uniform width-deficit estimate without `width_certificate.py` or `extended_width_certificate.py`.

## 3. The geometric and coercivity inputs are analytic in this range

The canonical crossing and excursion proof is already analytic for e<=pi/3. The candidate realization theorem has an analytic proof for e<=pi/6; the integer interval calculation in its middle range is not needed near zero.

The strict quadratic theorem uses Poincare's inequality and the explicit endpoint Jacobi field. Its rescaled free-endpoint coefficient satisfies

    -E(e)/e -> (1/T0-1)/2>0.

The explicit uniform zero-endpoint coercivity estimate for e<=1/2 is proved in `REVERSE_STABILITY.md` by elementary Taylor bounds, Poincare's inequality, and Young's inequality. The limit candidate has positive contact-segment length 3(1-T0)/[2(1+T0)] by (1).

Thus every sign and uniform boundedness needed for the reverse set-stability theorem and the flat-contact alignment argument follows analytically on one common sufficiently small interval.

## 4. Acyclic proof dependencies

The strongest theorem can be read in the following order:

1. `REVERSE_CAP_AREA.md`: cap identity for nonsmooth convex hulls.
2. `REVERSE_GENERAL_MAJORANT.md`, Sections 1-5: analytic canonicalization, crossing, excursions, and corrected width functional for small e.
3. `REVERSE_QUADRATIC_THEOREM.md`: strict maximization of that functional, including free asymmetric endpoints.
4. Sections 1-2 of this file: analytic width comparisons near zero.
5. `REVERSE_GEOMETRIC_THEOREM.md`, using only its SMALL-angle endpoint proof: explicit feasible reverse maximizer and exact class uniqueness.
6. `REVERSE_STABILITY.md`: uniform reverse path coercivity. `UNIVERSAL_LIMIT_SHAPE.md`, Sections 1-2 ONLY: explicit candidate limit and uniform inball.
7. `REVERSE_SET_STABILITY.md`, Section 1 ONLY: actual-set stability within the reverse class.
8. `ALIGNMENT_REDUCTION.md`, Sections 1-4 ONLY: lossy alignment of an arbitrary sofa, independent of any global optimality theorem.
9. `FLAT_CONTACT_ALIGNMENT.md`: the flat segments force the scaling loss to vanish for every putative global competitor.
10. `EXACT_NEAR_REVERSAL.md`: exact global optimality, uniqueness, unrestricted stability, and the refined expansion.

In particular, step 7 does not use that file's later unrestricted consequence, and the candidate convergence in step 6 does not use the later universal convergence of arbitrary sofas. There is no use of exact unrestricted optimality to establish the reverse stability that proves exact unrestricted optimality.

## 5. What still uses computation

The broader explicit angle interval starting at beta=pi-arccos(sqrt(2)-1), monotonicity over the entire obtuse range, and the tight decimal brackets on beta_H and beta_U use the separately documented exact-integer scalar certificates. They are additional results, not premises of the existential near-reversal theorem.

The claim here is a purely analytic proof route, not machine verification of that route. Independent checking of the geometric majorant, actual-set stability, and final alignment argument remains necessary. The existence of a positive common parameter interval does not produce a numerically certified value for its endpoint.
