# An explicit interval of globally optimal arbitrary-angle sofas

**Fifth-round main theorem draft.** The argument gives an explicit cutoff and replaces the preceding use of full Hausdorff stability by a contact-rectangle estimate. It remains an unrefereed analytic proof draft with exact-integer assistance for scalar inequalities; it is not a Lean-checked result. No CI or Lean build was run.

## Theorem

For every

    0<e<=1/19 radians,    beta=pi-e,

in the sharp unit-width hallway,

    M(beta)=V(e).

The unique maximizing compact connected sofa, up to Euclidean congruence, is the explicit convex S_e from `REVERSE_GEOMETRIC_THEOREM.md`. Competing sofas need not be convex, symmetric, smooth, aligned, of full actual width, or moved monotonically.

In particular the result covers EVERY bend

    177 degrees <= beta < 180 degrees.

Indeed pi/60<1/19 follows from pi<22/7. The exact proved left endpoint is pi-1/19, approximately 176.9844 degrees. This is a sufficient global cutoff, not the actual onset of optimality, a claimed phase-transition angle, or a numerical optimizer's crossing.

The exact formula is unchanged:

    d0=cos e, q=sin e, m=2-d0,
    eta=sqrt((2-d0)/(2+d0)),
    K=sqrt(e^2+3(e/sin e)^2)/2,
    R=eta sin K/(cos K+eta sin K),
    V(e)=e/m+(1+2d0)/(4q)+3d0^2 R/(2q m^2).

This determines both the shape and area on the stated continuum of fixed non-right-angle hallways, not merely an endpoint asymptotic.

## Proof

### 1. Scale a hypothetical high-area competitor into the reverse class

Suppose an unrestricted sofa S has area A>=V(e). Choose ANY complete passage and let n=|nu| in [0,pi/2] be the mismatch between its initial and final unoriented strip normals. The strip-intersection area bound and the scalar bounds of `EXPLICIT_PATH_CONSTANTS.md` give

    sin n<=1/A<=20e/27.

Since sin(3e/4)>20e/27 for 0<e<=1/10, one has

    n<=3e/4<=3/40.

The displayed strict sine comparison follows from sin x>=x-x^3/6; its remaining rational margin is checked by `prove_propagation`.

The alignment lemma places R=lambda S, lambda=cos(n/2), in one aligned class. Its area is at least A/2>=27/(40e)>3, whereas the forward-class midpoint upper bound 2sec(e/2) is less than 3. Thus R is reverse. Its normalized deficit satisfies

    0<=d=e[V(e)-lambda^2 A]<=17n^2/50<1/3.            (1)

The geometric reverse-class theorem is an input here, already valid on a much larger interval. No unrestricted optimality premise is used.

### 2. A large rectangular core with a small missing area

Apply the explicit path constants. Since sqrt(17/50)<7/12, (1) gives coordinatewise canonical-path errors at most

    eta_x=(35/24)n+(119/100)n^2,
    eta_y=(119/120)n+(17/10)n^2.                       (2)

The contact-rectangle lemma places

    Q=[eta_x,ell_e-eta_x] x [-1/2+eta_y,1/2-eta_y]

inside the intermediate majorant region Omega, where

    area(Q minus A_e R)<=area(Omega minus A_e R)<=d.

Write W=ell_e-2eta_x, H=1-2eta_y. At e<=1/19 the scalar bound ell_e>143/500 and n<=3/76 give

    W>=241379/1444000>0,
    H>=13233/14440>0.                                 (3)

This step requires only the crossing/excursion majorant and the coordinatewise path estimate. It does NOT require the fourth-round Hausdorff theorem, an inball argument, or an existential uniform geometry constant.

### 3. A nonzero mismatch forces an impossible width

Assume n>0. Put

    a=sin n/e, b=cos n.

The elementary Taylor bounds give

    (999/1000)n/e<=a<=3/4,    99/100<=b<=1.             (4)

The exact rational propagation verifies

    d<min{a W^2/(2b), b H^2/(2a)}.                    (5)

For the first inequality it suffices to check

    (17/50)(3/76)(1/19)<(999/1000)W_min^2/2;

for the second use d<=(17/50)(3/76)^2 and the lower bound for H in (3). These are strict rational inequalities.

The original exit strip makes the directional width of A_e R at most lambda. The missing-area triangle lemma and (5) imply

    lambda >= aW+bH-2sqrt(abd).

Using (2), lambda-cos n<=n^2/2, and (4), then dividing by n>0, gives

    (143/500)(999/1000)/e
       <= 6217/1200+(1137/200)n
       <= 6217/1200+(3411/800)e.                      (6)

For the square-root term we used

    2sqrt((3/4)(17/50))<101/100,

whose squared comparison is rational. The other coefficients in (6) are obtained directly from (2).

The left side of (6) decreases in e and the right side increases. At the largest allowed e=1/19 their difference is exactly

    166189/7125000>0.

Therefore (6) is impossible throughout 0<e<=1/19. Hence n=0.

### 4. Remove the scaling and classify equality

Now lambda=1, so S itself belongs to the aligned reverse class. Its area is at most V(e), and equality forces the explicit S_e up to congruence by reverse-class uniqueness. Conversely S_e completes a passage and has area V(e). This proves the theorem without assuming existence of an unrestricted maximizer in advance.

Because the complete passage was arbitrary, every passage of a maximizing sofa has parallel unoriented initial and final strip normals. This does not mean that its intermediate motion is unique.

## Reproduction

From this directory:

```sh
python explicit_cutoff_certificate.py --cells 256 --output explicit-cutoff.json
```

The checker first covers the WHOLE closed parameter interval [0,1/10], including the removable endpoint at zero, by exact-integer interval bounds for the ten scalar quantities. It then checks the trace coefficients, core dimensions, triangle regime, and final contradiction using exact fractions. No floating point, optimization, shape sampling, or external numerical library is used by this checker.

An overly aggressive cutoff such as `--cutoff 53/1000` is rejected by these sufficient estimates. That is not a counterexample to S_e optimality at that angle. Improving the estimate or lowering the true global cutoff is a separate problem.

## Proof dependencies and review boundary

Read `CONTACT_RECTANGLE_LEMMA.md`, `EXPLICIT_PATH_CONSTANTS.md`, then the earlier cap identity, canonical crossing/excursion majorant, quadratic theorem, and geometric realization. The alignment-by-scaling lemma remains an input. The previous full-set stability and limiting-profile files are not required for this proof.

This is stronger and has fewer geometric dependencies than the unspecified-cutoff theorem. Nevertheless exact scalar certificates do not validate the mathematical modeling or analytic derivations. The draft needs independent review, particularly of canonicalization, the cap-area identity, and the interpretation of the quadratic functional as a majorant for all compact connected reverse competitors. No claim of publication priority is made here.
