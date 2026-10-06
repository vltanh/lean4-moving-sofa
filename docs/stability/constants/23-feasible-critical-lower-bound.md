# A feasible critical family: a lower bound exceeding 0.922

Analytic geometry plus an exact interval energy calculation. This is not a
claim about a merely discretized tangent cone. The perturbations below give
actual feasible wide triples for every sufficiently small positive amplitude.
No Lean verification is claimed.

## 1. Explicit symmetric support perturbation

Put p=phi, v=pi/2, c=v-theta, T=pi-p, d=v+theta. Let q=117/100. Define g on
[0,p] by

    g(t)=-cos(t)+q*sin(t).

On [p,v], take a piecewise cubic Hermite function on seventeen nodes: eight
equal subdivisions of [p,c] followed by eight of [c,v]. Its endpoint values
are g(p)=-cos(p)+q*sin(p), g(v)=0. The fifteen intervening rational values
and the fourteen ordinary rational endpoint slopes are recorded verbatim in
`critical_cone/certify_feasible_trial_final.py`. Three slopes are prescribed
analytically rather than rounded:

    g'(p)=sin(p)+q*cos(p),
    g'(c)=[g(c)*cos(c-p)-g(p)]/sin(c-p),
    g'(v-)=499991095/10^9.

The last of these is rational; the first two enforce exact matching. Extend
by g(pi-t)=g(t). Thus g(0)=g(pi)=-1, and the top support remains zero.

For K_tau put h_Ktau=h_KG+tau*g on [0,pi], and extend its lower support by
its two floor endpoints. Take tau>0 sufficiently small.

## 2. Convexity is not inferred from sampled curvature

On (0,p), the perturbation is harmonic, so g''+g=0. Its derivative at0 is
q>0, producing a nonnegative new vertical face, not the negative face of the
infeasible positive width direction. Reflection gives the same correct sign
at pi. On (p,T), the reference cap curvature density is bounded below by1/2,
as in note15's phase calculation. The cubic perturbation has bounded second
derivative on each of finitely many intervals and is C1 at their joins.
Choose tau small enough to retain positive curvature density. At the top,
the derivative jump can be negative, but the reference has a strictly positive
top-face atom, so it remains positive for small tau. The floor width changes
by -2tau and stays positive. There are no other negative curvature atoms.

Thus the full periodic support measure h''+h is nonnegative and defines an
actual normalized convex cap. The argument works for each reference solution
in the parameter box, not only the central numerical parameter values.

## 3. Construct B_tau rather than assuming it exists

Describe support directions of B in ordinary angle alpha. Its perturbation b is:

* b(alpha)=g(alpha) on [0,v], where the reference B shares the outer cap;
* b(alpha)=[g(p)/cos(p)]*cos(alpha) on [v,pi+p];
* b(pi+t)=-H(t) on [p,c], where H is the harmonic interpolant of g(p),g(c);
* b(pi+t)=-g(t) on [c,v];
* b(alpha)=-cos(alpha) on [3pi/2,2pi].

The middle prescribed slope is exactly g'(c)=H'(c), so there is no new
curvature atom where the harmonic part meets -g. On the two harmonic gaps
there is no curvature-density perturbation. On the active curved arc the
reference B density is at least1/8, which absorbs the bounded density change.
The reference atoms at the top, the cut angle pi+p, and the bottom are all
strictly positive, so their bounded changes are allowed for sufficiently
small tau. The endpoint at angle0 has the same new positive face as the cap.
Consequently h_BG+tau*b is a genuine convex support function.

Define D_tau by reflecting B_tau across Gerver's vertical symmetry axis.
Because K_tau has the same symmetry, this gives the corresponding left-body
construction and matching conditions without introducing a different cap.

## 4. Containment and inactive walls are checked

For the reference B, equality of its support with the cap occurs on [0,v]
and [3pi/2,2pi]. On precisely those intervals the new perturbations coincide.
On the complementary open interval the reference containment gap is positive.
At its two endpoints the gap has positive one-sided linear margin, from the
positive removed portions of the top and bottom faces. The perturbation gap
vanishes at the endpoints and is Lipschitz. Compactness away from the endpoints
and these linear estimates therefore preserve B_tau subset K_tau for small tau.
Reflection gives D_tau subset K_tau.

On the constrained B angles [p,v], let R(t)=1-h_KG(t)-h_BG(pi+t). It is positive
on (p,c), zero on [c,v], and has the following endpoint behavior:

    R(p)=R(c)=R'(c)=0,
    R'(p+)>0,
    R''(c-)=1-rho_KG(c)>0.

These are the fixed contact-gap properties behind the reference active arc.
The last inequality follows from rho_KG(c)=theta/2-b1<7/8; the first derivative
is the positive reference inner-arm speed at p. Thus, for some r0>0,

    R(t)>=r0*(t-p)*(c-t)^2 on [p,c].

The perturbation of the paired wall support is w(t)=g(t)-H(t). By construction,
w(p)=w(c)=w'(c)=0. It is piecewise C2 with bounded second derivative near c,
so |w(t)| is bounded above by a constant times (t-p)*(c-t)^2. Choosing tau
smaller if necessary preserves R-tau*w>=0 throughout the gap. On [c,v] the
paired perturbations cancel exactly, and at p they also cancel. Reflection
handles every left-wall constraint. The two endpoint contact equalities remain
exact. No inactive inequality is replaced by a numerical sampling test.

This verifies every part of the wide domain: cap normalization, convexity of
all three bodies, containment, all continuous paired-wall inequalities, and
the endpoint equalities.

## 5. Exact zero slack and exact quadratic deficit

On both reference active arcs the paired support perturbations are zero.
Therefore the dual first-variation slack L is exactly zero for the constructed
triple. The exact deficit identity, not a second-order approximation, gives

    M-Q(xi_tau)=tau^2*E_trial.

Write f=g-cos(t), the corresponding left-pinned support difference. Eliminating
the two harmonic auxiliary gaps, E_trial is precisely the six-residual energy
of note18, including both forced auxiliary integrals. The committed checker
uses the equivalent expressions on [0,v] to remove avoidable singularities.
For example the middle residual becomes g(v-t)-g'(t), and the last cap residual
becomes g'(t)-(cos(t)*g(t)+1)/sin(t) after reflection. The removable zero in
(tan t)*g(t) at v is factored before interval evaluation.

The interval calculation covers the entire source parameter box and encloses

    1.1743426270 < E_trial < 1.1751419732 < 147/125.

It integrates whole interval enclosures on 32,768 cells with exact 90-bit
outward dyadic arithmetic. There are no floating-point acceptance comparisons.

For EVERY horizontal shift s, the two extreme supports give

    ||tau*g-s*cos||_infinity >= tau,

because their sum is -2tau. Thus

    d_tr(K_tau,K_G)/sqrt(M-Q(xi_tau)) >= 1/sqrt(E_trial) > 461/500.

The last strict inequality follows from the exact rational check

    (461/500)^2*(147/125)=31240587/31250000<1.

This is a continuously feasible full-Q lower bound above0.922. It is not a
lower bound obtained by maximizing over an enlarged, infeasible vector space.

## 6. Scope

The family tends to Gerver as tau decreases, so the lower bound applies to
the asymptotically optimal Q coefficient as well as the zero-slack face.
The threshold for feasible tau is existential; its numerical value is not
needed for a lower bound on an asymptotic coefficient. That existence argument
must not be confused with the unresolved NUMERICAL entry threshold for arbitrary
sofas. No claim is made here about the best midpoint-aligned coefficient,
the best original-sofa area coefficient, or uniqueness of the critical mode.

The geometric reference gap and support-arc descriptions are analytic inputs
from Gerver's explicit geometry. The interval program certifies the energy
inequality, not those geometric statements or a Lean proof. Independent review
should check the support extension, the two positive face margins, and the
quadratic gap at c in particular.
