# Strongest explicit global coefficients in this continuation

## Statement and status

The arguments in notes 01, 05, and 06 yield the following analytic strengthening
of the existing near-maximizer theorem. The new specialization is NOT claimed
as an assembled, kernel-checked Lean theorem.

For every Gerver parameter solution P in the source box, there exists epsilon0>0
such that every original moving sofa S with epsilon=|G|-|S|<epsilon0 satisfies,
after the prescribed top/left-support translation,

    d_H(S,G) <= (61/2)*sqrt(epsilon),
    |S symmetric_difference G| <= 100*sqrt(epsilon).

For each admissible reduced angle omega of such a sofa, also

    0 <= pi/2-omega <= (31/10)*epsilon.

In particular the simple integer Hausdorff coefficient 31 works. The somewhat
stronger 61/2=30.5 uses the small-surplus information from the improved terminal
trapezoid. The constants are uniform over all near-optimal original sofas, not
just smooth/injective/monotone ones. They are NOT claimed optimal. The entry
threshold remains positive but existential, not numerically certified.

## 1. Numerical reference data

Note 06 proves from explicit reference phase formulas and parameter enclosures:

    cap coefficient k <= 1001/500,
    roof factor F = 51/5,
    interior-ball ratio kappa = 100/1051.

The reference cap horizontal width W and niche-floor width w satisfy

    W < 323/100,       w < 807/500.

The interior-ball scale, roof clipping depth, and local neighborhood sizes are
still allowed to depend on the fixed reference. None of them is inserted as a
numerical value in the leading constants.

## 2. Keep the two deficit budgets

Use qualitative entry to place the normalized sofa and its right-angle completion
K in the established local certificate regime. Let U=K minus N(K), e=M-|U|,
alpha=pi/2-omega, g=|S minus U|, m=|U minus S|. Then

    0<=e<=epsilon,       delta<=k*sqrt(e).

The improved trapezoid of note 05 gives simultaneously

    alpha <= (31/10)*(epsilon-e),
    g <= alpha/1000 <= (31/10000)*(epsilon-e),
    m = epsilon-e+g <= (10031/10000)*(epsilon-e).

These estimates use actual measurable sets and finite areas. No containment
S subset U, monotone motion of S, or completed right-angle motion is assumed.
The weaker m<=2*(epsilon-e) remains a convenient fallback, but loses a little
in the final numerical constant.

## 3. Reverse Hausdorff estimate with coefficient 61/2

For a desired radius rho, the full interior disk after reference erosion has
radius kappa*rho-sqrt(2)*delta. If

    sqrt(2)*delta+sqrt(m/pi)<kappa*rho,

its area exceeds the missing area m, forcing a point of S within rho of every
point of G. This is the exact disk recovery argument, not a square-inside-disk
estimate.

The split budget and Cauchy--Schwarz give

    sqrt(2)*delta+sqrt(m/pi)
      <= sqrt(2)*k*sqrt(e)
         +sqrt(10031/(10000*pi))*sqrt(epsilon-e)
      <= sqrt(2*k^2+10031/(10000*pi))*sqrt(epsilon).

Using only k<=1001/500 and pi>3,

    2*k^2+10031/(10000*pi) < (29/10)^2,
    29/10 < (100/1051)*(61/2).

Both are strict rational inequalities. Therefore rho=(61/2)*sqrt(epsilon)
works whenever rho is below the fixed interior-ball scale. That requirement is
met by reducing epsilon0, not by changing the leading coefficient.

The weaker budget m<=2*(epsilon-e) independently gives the integer 31 via

    sqrt(2*k^2+2/pi)<737/250<(100/1051)*31.

This fallback uses the old terminal comparison and does not require the improved
trapezoid estimate. Thus a potential issue confined to that trapezoid refinement
would not invalidate the simpler 31 proof.

## 4. Forward Hausdorff estimate

The adapted reference roof margin gives, for a fixed B>=0,

    directed_distance(S,G) <= (51/5)*(delta+B*(epsilon-e)).

Reduce epsilon0 until B*sqrt(epsilon)<=1/2 and all the reference clipping and
outer-wall margins apply. Then

    directed_distance(S,G)
      <= (51/5)*(1001/500+1/2)*sqrt(epsilon)
      = (63801/2500)*sqrt(epsilon)
      = 25.5204*sqrt(epsilon)
      < (61/2)*sqrt(epsilon).

The actual leading coefficient before absorbing the linear term is at most
20.4204. A small finite threshold absorbs the remainder without requiring an
explicit B. This is why the terminal-angle coefficient does not inflate the
leading square-root coefficient.

Together the two directions establish the stated Hausdorff estimate for every
positive deficit sufficiently small. Zero deficit follows from existing exact
normalized uniqueness, as in the original global assembly.

## 5. Symmetric difference with coefficient 100

Use the direct excess-area argument of note 05, now with the better roof margin.
The Euclidean delta-neighborhood of the convex cap lies in its square dilation;
Cavalieri's two successive segment dilations give

    |K minus K_G| <= 2*(W+1)*delta+4*delta^2.

Inside K_G, points of U minus G lie in a roof band of thickness F*delta once
delta is below the reference clipping threshold. Hence

    |U minus G| <= [2*(W+1)+F*w]*delta+4*delta^2
                <= (62307/2500)*delta+4*delta^2.

The exact finite-area identity and the weaker g<=epsilon-e now suffice:

    |S triangle G| = epsilon+2*|S minus G|
      <=3*epsilon-2*e+(62307/1250)*k*sqrt(e)+8*k^2*e
      <=(62369307/625000)*sqrt(epsilon)+(827/25)*epsilon.

With sqrt(epsilon)<=1/200 this is at most

    (31236341/312500)*sqrt(epsilon)
      =99.9562912*sqrt(epsilon)
      <100*sqrt(epsilon).

Intersect this explicit smallness condition with the other local thresholds.
The area estimate does not use either Hausdorff coefficient, or the numerical
interior-ball ratio, at any point. It is therefore useful independently of the
Hausdorff recovery calculation.

## 6. Quantifiers, simultaneous constants, and scope

All choices of neighborhood and scale depend only on the reference parameter
solution. Take their finite minimum, together with the original qualitative-entry
threshold and the deficit threshold guaranteeing a reduced angle. This gives
one positive epsilon0 for all three conclusions and all eligible input sofas.

The constants 61/2, 100, and 31/10 are numerical. The resulting epsilon0 is
not. This is an explicit-coefficient theorem, NOT a fully effective numerical
stability certificate. It also does not state that the same constants work for
all deficits up to M. 'Global' here refers to the unrestricted class of sofas
near the optimum.

The proof still depends on the correctness of the existing analytic local
certificate and qualitative-entry arguments. New source files prove scalar
budgets, orthogonal erosion, and conditional set-level recovery. The explicit
reference geometry and its uniform adaptive-angle specialization remain an
analytic proof with formalization work outstanding. No claim of successful
Lean elaboration, a new global numeric theorem declaration, or executed kernel
audit is made.

## 7. More informative forms and subclasses

The two-scale estimates are often more useful than a single number:

    reverse cost <= [sqrt(2)*k*sqrt(e)+sqrt((epsilon-e+g)/pi)]/kappa,
    forward cost <= F*k*sqrt(e)+F*B*(epsilon-e),
    area distance <= epsilon+2*g+2*[2*(W+1)+F*w]*k*sqrt(e)+8*k^2*e.

For a full-angle contained sofa, g=0 and m=epsilon-e exactly. For the monotone
full-angle shape S=U, e=epsilon and m=0: the reverse cost has coefficient
sqrt(2)*k/kappa<30, while the forward leading cost is at most20.4204 with no
missing-angle allowance. Consequently the monotone full-angle subclass admits
coefficient 30 in a sufficiently small neighborhood. This is a stronger subclass
statement, not an assertion that arbitrary sofas have no holes or omitted wedges.

The punctured Gerver family has e=0, g=0, and missing area epsilon. Its exact
rigid distance is sqrt(epsilon/pi); it exhibits why spending epsilon twice in
both the cap and missing-area terms is wasteful, and gives the lower bound
1/sqrt(pi) on any unrestricted near-optimal rigid-Hausdorff coefficient. There
is still a substantial gap between that lower bound and the conservative upper
coefficient above.
