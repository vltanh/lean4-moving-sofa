# Exact reverse-class optimality and sharp unrestricted asymptotics

**Status:** a new mathematical proof draft with exact-integer computer assistance for scalar parameter inequalities. It has not been independently reviewed or checked in Lean. No CI or Lean build was run. The theorem is not an assertion that the unrestricted oblique-sofa optimum equals the reverse-class optimum at a fixed angle.

## Definitions

The bend beta is the change in travel direction, 0<beta<pi; the angle between the corridor rays pointing away from the junction is pi-beta. Write e=pi-beta.

A sofa is a compact connected planar set that completes a continuous rigid passage from one unbounded arm of the sharp unit-width hallway to the other. Let M(beta) be the unrestricted supremum of its Lebesgue area.

The aligned reverse class consists of sofas that, in body-fixed coordinates with the incoming strip horizontal, admit hallway orientations from 0 to beta-pi=-e and finish with the outgoing strip parallel to the incoming strip. The path is not assumed monotone. Equivalently, after a vertical normalization, the sofa fits a unit-width horizontal strip and, for every phi in [0,e], fits a translated hallway with normals

    n1(phi)=(sin phi,cos phi),
    n2(phi)=(sin(e-phi),-cos(e-phi)).

A continuous canonical selection follows from support functions, and entry/exit translations attach in the arms. Let M_minus(beta) be this class's supremum. No convexity, symmetry, smoothness, or full actual strip width is imposed on competitors. The aligned forward class and M_plus(beta) are defined similarly with orientation change beta.

## Theorem A: exact optimizer of the full reverse class

For every 2pi/3<=beta<pi, set

    e=pi-beta, d=cos e, q=sin e, m=2-d,
    eta=sqrt((2-d)/(2+d)),
    K=(e/2)sqrt(1+3/sin(e)^2),
    R=eta sin K/(cos K+eta sin K).

Then

    M_minus(beta)=V(e)
      :=e/m+(1+2d)/(4q)+3d^2 R/(2q m^2).               (A)

The maximum is attained by the explicit convex sofa S_e in `REVERSE_GEOMETRIC_THEOREM.md`, whose boundary consists of two support arcs, the convex corner graph, and two horizontal segments. It is the unique maximizer up to horizontal translation in normalized coordinates. In particular symmetry, convexity, and actual strip width one are conclusions about maximizers, not assumptions.

The explicit corner formula is given in `REVERSE_QUADRATIC_THEOREM.md`; no finite-dimensional shape ansatz is imposed on competing sofas.

### Proof

For a competitor S of actual height w in (0,1], canonicalize its corner using the support values of conv(S). Every feasible pose remains feasible under this canonicalization. As shown in `REVERSE_GENERAL_MAJORANT.md`, for e<=pi/3 the canonical corner crosses the actual strip once in increasing height, even if it makes excursions outside it. Integration by parts bounds the outside contributions with their correct signs. Consequently

    area(S)<=Q(C)+(1-w)(x0+xe)+(1-w)^2 cot e.           (1)

Fix the horizontal gauge x0+xe=0. The quadratic functional has the same strictly negative Hessian for all fixed endpoint heights. The complete continuous maximization, including asymmetric endpoint variations, is proved in `REVERSE_QUADRATIC_THEOREM.md`. At height w it gives the explicit quadratic upper bound F_e(w) in `REVERSE_GENERAL_MAJORANT.md`, with F_e(1)=V(e).

Midpoint slicing gives the independent inequality

    area(S)<=w csc(e/2).                               (2)

For w<=1/2, (2) is strictly below V(e). For 1/2<=w<1, the corrected quadratic bound F_e(w) is strictly below V(e). The scalar comparisons establishing these statements are proved below. Thus every maximizer must have w=1 and area at most V(e).

The geometric realization theorem proves that S_e is feasible at every real pose, has full width, and has area Q(C_*)=V(e), so the upper bound is attained. Equality for any other sofa forces equality in the strictly concave quadratic maximization and hence C=C_* up to horizontal translation. The corresponding support cap and forbidden wedges force S subset S_e. Since S is closed, S_e is the closure of its interior, and their areas agree, S=S_e: omitting a point of S_e would omit an open neighborhood intersecting its interior in positive area. This proves uniqueness as an equality of compact sets, not merely almost everywhere.

### The scalar width comparisons

Let T=eta tan K and retain the coefficients c0,c1,c2 from the general-majorant file.

First, q V(e)>cos(e/2) on 0<e<=pi/3, so V(e)>1/[2 sin(e/2)]. This also has an elementary proof. Both eta and K increase with e, and

    tan(sqrt(3)/2)>2/sqrt(3),

so T>2/3. To verify the tangent inequality, differentiate

    (1-x^2/3)sin x-x cos x;

its derivative is x(sin x-x cos x)/3>0 for x>0. Substitute x=sqrt(3)/2. It follows that R=T/(1+T)>2/5. Using e>=q and 1/2<=d<1 gives

    qV > (1-d^2)/(2-d)+(1+2d)/4+3d^2/[5(2-d)^2] > 1.

For the last inequality, multiply the difference from 1 by 20(2-d)^2 and set u=d-1/2 in [0,1/2]. Its numerator becomes

    30u^3-38u^2+(39/2)u+3
      >=30u^3+u/2+3>0.

Second,

    F_e(1)-F_e(1/2)
      =[(2-d)(6d+7)-T(6d^2+13d-2)]/[16q(1+T)(2-d)]>0.  (3)

The positive numerator in (3) is certified on the entire closed parameter interval 0<=e<=pi/3 by `width_certificate.py`, including the removable endpoint at e=0. Sixty-four exact-integer interval cells suffice and give a numerator lower bound greater than 7/5.

Finally F_e'(1)>0 follows from the same inequality used for the free-endpoint Jacobi field in the strict quadratic theorem:

    (2-d)(2d+1)-T(2d-1)(d+2)>0.

For a quadratic polynomial, F_e(1/2)<F_e(1) together with F_e'(1)>0 implies F_e(w)<F_e(1) for 1/2<=w<1: if convex, compare with the endpoint chord; if concave, its derivative is positive throughout this interval. The width checker independently verifies all three comparisons, though two already have analytic proofs.

## Theorem B: sharp asymptotics without any motion-class restriction

Let

    T0=tan(sqrt(3)/2)/sqrt(3),
    C=3(1+3T0)/[4(1+T0)] = 1.35653373245229... .

For the unrestricted moving-sofa problem,

    M(pi-e)=C/e+O(e) as e->0+.                          (B)

More explicitly, for 0<e<=pi/3 define U(e)=max{V(e),2 sec(e/2)}. Then

    V(e)<=M(pi-e)<=U(e)+1/[4U(e)].                     (4)

Whenever V(e)>2 sec(e/2), the upper bound becomes V(e)+1/[4V(e)]. This holds for all sufficiently small e; the separate exact-integer scalar check in `reverse_value_certificate.py` proves it throughout 0<e<=37pi/180, equivalently 143 degrees<=beta<180 degrees.

### Proof

`ALIGNMENT_REDUCTION.md` proves that any unrestricted sofa of area A>1 can be uniformly scaled to a member of one of the two aligned classes while retaining area at least

    [A+sqrt(A^2-1)]/2.

The argument uses the area of the intersection of the incoming and outgoing strips to bound their normal mismatch, then rotates a slightly scaled sofa farther down the straight exit arm. It includes nonmonotone motions and arbitrary winding of the orientation. The area loss is not asserted to be zero.

The forward midpoint bound is 2 sec(e/2), and Theorem A gives the reverse bound V(e). Inverting the displayed area inequality proves (4); sofas of area at most 1 are harmless. After multiplying (A) by e, every term extends evenly and analytically to e=0. Its limiting value is C, so V(e)=C/e+O(e). Since V(e) diverges and 2 sec(e/2) stays bounded, (4) yields (B).

This determines the sharp leading constant for the unrestricted problem and bounds the gap from the explicit reverse construction by O(e). It does not determine that gap's coefficient or show that it vanishes at any fixed nonzero e.

## Illustrative exact-class values

These decimal enclosures are reproducible with `reverse_value_certificate.py`; the formulas, not floating-point optimization, define the values.

| Bend beta | Lower endpoint for M_minus | Upper endpoint for M_minus |
| --- | ---: | ---: |
| 120 degrees | 1.399979511 | 1.399979512 |
| 135 degrees | 1.803764167 | 1.803764168 |
| 137 degrees | 1.880508238 | 1.880508239 |
| 150 degrees | 2.641025081 | 2.641025082 |
| 170 degrees | 7.788929081 | 7.788929082 |
| 179 degrees | 77.725311765 | 77.725311766 |

## Proof and computational dependencies

Read the quadratic theorem for the variational maximization, the general-majorant file for canonicalization and width, the geometric theorem for realization, and the alignment reduction for the unrestricted result. The two parameter checkers use only exact integer/rational operations, integer square roots, and rigorously bounded Taylor series; the previous floating-point rectangle certificates and all local optimizers are outside these theorem proofs.

The numerical module `reverse_exact.py` and its tests check the formulas, finite differences, asymmetric variations, whole-polygon collisions, and quadrature independently of candidate optimization. Such tests are regression evidence, not substitutes for the analytic derivations or exact-integer parameter enclosures.

## Publication status and limitations

This is a substantive theorem draft rather than a claim of journal readiness. Independent scrutiny should concentrate on the nonsmooth cap-area identity, the canonical-corner crossing argument, outside-excursion integration, the free-endpoint quadratic calculation, and the rotation-extension lemma. None has yet been independently refereed or formalized here.

The exact reverse-class formula does not prove the numerical branch crossing near 136.673 degrees to be a unique global phase transition, nor establish a fixed-angle unrestricted optimum. The forward class is not solved. No novelty claim is made merely for observing the two competing numerical branches; that is prior work of Xingyi He, arXiv:2608.11206v1. A full literature and priority check for the new analytic results remains necessary.
