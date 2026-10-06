# Exact unrestricted optimal sofas for all sufficiently sharp bends

**Current main theorem draft, fourth round.** This supersedes the earlier limitation to unrestricted asymptotics near reversal. It is an analytic proof draft, not independently refereed or Lean-checked. Exact-integer computations support specified scalar lemmas only. No CI or Lean build was run.

The hallway is sharp and has two arms of unit width. Its bend beta is the change in travel direction; write e=pi-beta. A sofa is any compact connected planar set completing a continuous rigid passage from one unbounded arm to the other. M(beta) is the unrestricted supremum of its area.

## Theorem 1: exact global optimality on a nonempty interval of bends

There exists e_1>0 such that for EVERY 0<e<e_1,

    M(pi-e)=V(e),

and the unique maximizing shape, up to Euclidean congruence, is the explicit convex sofa S_e from `REVERSE_GEOMETRIC_THEOREM.md`.

No aligned endpoints, convexity, symmetry, smoothness, full strip width, or monotone motion is assumed for competing sofas. The candidate is a genuine two-dimensional shape with an explicit continuous passage, not just a formula for the area.

The exact value is

    d=cos e, q=sin e, m=2-d,
    eta=sqrt((2-d)/(2+d)),
    K=(1/2)sqrt(e^2+3(e/sin e)^2),
    R=eta sin K/(cos K+eta sin K),

    V(e)=e/m+(1+2d)/(4q)+3d^2 R/(2q m^2).             (1)

The boundary and corner-path formulas are in `REVERSE_QUADRATIC_THEOREM.md` and `REVERSE_GEOMETRIC_THEOREM.md`; `reverse_exact.py` evaluates them numerically. The formula itself, rather than its decimal evaluation, defines the candidate.

### Proof structure

1. The exact reverse-class theorem, including nonsmooth and narrower competitors, identifies S_e as its unique optimizer. It holds on the larger explicit interval beta>=pi-arccos(sqrt(2)-1), approximately 114.4698 degrees; see `REVERSE_EXTENDED_RESULTS.md`.
2. Uniformly rescaled quadratic coercivity controls a reverse sofa's canonical path by the square root of its normalized area deficit. An intermediate containing region, a missing-area estimate, and an inball argument upgrade this to stability of the ACTUAL possibly nonconvex set; see `REVERSE_STABILITY.md` and `REVERSE_SET_STABILITY.md`.
3. Any unrestricted sofa can be scaled by lambda=cos(nu/2) into an aligned class, where nu is the entry/exit strip-normal mismatch. For a hypothesized competitor of area at least V(e), that class must be reverse, and its normalized reverse deficit is O(nu^2).
4. Thus its normalized shape is O(|nu|)-close to S_e. But S_e has top and bottom horizontal contact segments of length asymptotic to a positive constant divided by e. A nonparallel exit strip would incur a width penalty of order |nu|/e. For uniformly small e this cannot be compensated by the O(|nu|) shape error or the O(nu^2) scaling loss.
5. Therefore nu=0. The original, unscaled competitor itself lies in the reverse class and cannot beat V(e). Equality forces S_e.

The complete quantitative inequalities for steps 3-5 are in `FLAT_CONTACT_ALIGNMENT.md`. This is a different argument from the failed scalar comparison F_e(lambda)<=lambda^2 V(e), which remains false and is preserved in the negative-results log.

### Essential limitation on the angle range

The proof establishes the existence of ONE positive e_1 valid for the entire interval (0,e_1). A numerical value for e_1 has not been certified. It is not claimed that exact unrestricted optimality begins at 114.4698, 142.0984, 143, or 150 degrees. Those thresholds belong to different class-level statements. Obtaining a useful explicit global cutoff is additional work.

## Theorem 2: uniform quantitative rigidity for unrestricted near-maximizers

There exist e_2,D_*,C_*>0 such that, for every 0<e<e_2 and every unrestricted sofa S with normalized area deficit

    D=e[V(e)-area(S)] in [0,D_*),

incoming-strip normalization and a translation give

    d_H(A_e S,A_e S_e)<=C_* sqrt(D),
    A_e(x,y)=(e x,y).                                 (2)

Here d_H is Hausdorff distance. No convexity assumption on S is made. The normals of the entry and final exit strips of every complete passage differ, as unoriented directions, by at most

    C_* e sqrt(D).                                   (3)

The constants are uniform in e, but are not numerically estimated. Equations (2)-(3) follow from the same flat-contact absorption argument; see Section 5 of `FLAT_CONTACT_ALIGNMENT.md`.

## Theorem 3: an explicit universal limit shape and a sharper expansion

Let T be the explicit convex body parametrized in `UNIVERSAL_LIMIT_SHAPE.md`. Then

    d_H(A_e S_e,T)=O(e^2).

Consequently every unrestricted near-maximizer in Theorem 2 obeys

    d_H(A_e S,T)<=C'[sqrt(D)+e^2].                     (4)

In particular ALL unrestricted maximizing shapes, after normalization, approach the same T at rate O(e^2). The spatial map A_e is a way to compare elongated shapes; it is not used to transport rigid motions by an affine shear.

Put

    T0=tan(sqrt(3)/2)/sqrt(3),
    C=3(1+3T0)/[4(1+T0)],
    C1=(9-4T0-9T0^2)/[8(1+T0)^2].

Then exact global optimality and (1) give

    M(pi-e)=C/e+C1 e+O(e^3),                          (5)

where C=1.35653373245229... and C1=0.09477330574913... . In fact e M(pi-e) has an even analytic extension to zero, so the complete odd-power Laurent expansion is determined by (1).

To check the second coefficient without numerical fitting, expand

    eta tan K = T0+[(1+2T0+3T0^2)/6]e^2+O(e^4),
    e/sin e=1+e^2/6+O(e^4),
    cos e=1-e^2/2+O(e^4).

Substitution into (1) gives (5). The exact constant is also area(T). Earlier work proved only C/e+O(e) for the unrestricted problem; the exact finite-angle theorem is what now identifies the next coefficient and the complete expansion.

## Other fourth-round theorems, independent of the unspecified global cutoff

- All three value functions M, M_plus, and M_minus attain their maxima and are locally Lipschitz on (0,pi); see `HALLWAY_WELL_POSEDNESS.md`.
- The exact reverse-class optimizer is valid for beta>=pi-arccos(sqrt(2)-1).
- Forward-class dominance is proved for beta<beta_H, and reverse-class dominance for beta>beta_U. The exactly defined comparison roots satisfy, in degrees,

      133.644346372<beta_H<133.644346373,
      142.098382576<beta_U<142.098382577.

  There is at least one crossing of the optimal aligned-class values; all such crossings lie in [beta_H,beta_U]. Neither root is beta_c, uniqueness of the crossing is not proved, and this is not a global transition classification.
- A circular-notch forward construction has explicit area pi/2+sin(beta)^2/[beta-sin(beta)cos(beta)] at every bend. This extends the familiar Hammersley construction; no novelty claim is made for that family.

## Reading order and review priorities

For the strongest new result, read this file, `FLAT_CONTACT_ALIGNMENT.md`, `REVERSE_SET_STABILITY.md`, and `REVERSE_STABILITY.md`. The limiting profile is in `UNIVERSAL_LIMIT_SHAPE.md`. The foundational dependencies are the earlier cap-area identity, canonical-corner majorant and excursion estimates, free-endpoint quadratic theorem, width comparisons, and alignment lemma.

Independent scrutiny is especially important for uniform set stability: its intermediate region must contain all of S, including strip-boundary points, and its two-sided geometric control must be uniform as e tends to zero. These are proved analytically in the draft, not verified by a finite polygon test. The final flat-contact step then uses only width subadditivity, the strip-area bound, and explicit inequalities.

A full literature and priority review remains necessary. The numerical competing-branch phenomenon and pressure interpretation are not new claims here. The PR remains a research draft, and the old Lean libraries and existing paper have not been changed.
