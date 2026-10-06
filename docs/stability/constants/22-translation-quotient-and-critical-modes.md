# Optimal translation is a two-point problem, not midpoint coercivity

Analytic reduction; numerical values in this initial note are exploratory.
No Lean, Lake, or CI is used. The full-Q target needs its normalization stated.
The earlier 0.98 critical-face estimate uses the FIXED midpoint translation.
The best translation can perform better, even for the same support perturbation.

## 1. Exact quotient norm

For continuous f on [0,pi], f(pi/2)=0, put

    d_tr(f)=inf_s sup_t |f(t)-s*cos(t)|.

For a proposed radius R>=0, every angle with nonzero cosine supplies a closed
interval of allowable s. Those intervals have common intersection if and only
if they intersect pairwise: in one real dimension this follows by comparing
the supremum of all lower endpoints and infimum of all upper endpoints.
The angles with zero cosine impose only |f(pi/2)|<=R, already satisfied.
Hence

    d_tr(f)=sup_{t,u; |cos(t)|+|cos(u)|>0}
      |cos(u)*f(t)-cos(t)*f(u)|/(|cos(t)|+|cos(u)|).

Existence of a minimizing translation follows from continuity and coercivity
in s, since the angle-zero evaluation grows as |s| tends to infinity.
The formula is exact; it is not a finite angular discretization.

## 2. Critical-face energy relaxation

Use E_rel from note18, which includes the forced B and D residual energies on
the active arcs and the minimal B energy on its inactive gap. For an evaluation
functional ell_{t,u}, the relaxed upper coefficient is

    sup_{t,u} sqrt(2*<ell_{t,u}, A_rel^{-1} ell_{t,u}>),

with A_rel the quadratic energy operator. The simpler rank-two update gives
a slightly larger, explicitly computable upper coefficient. A certificate for
this TWO-angle expression establishes a best-translation estimate; a bound on
midpoint kernels is a different and potentially larger operator norm.

## 3. New exploratory calculations

Piecewise support interpolation, quadrature split at all shifted knots, and the
full relaxed auxiliary energy reproduce the earlier midpoint norm near0.968.
Adding the two-angle quotient gives a different mode: the sampled maximum occurs
at the pair (0,pi), measuring horizontal width, with values approaching0.9252.
For the simpler rank-two relaxation the sampled quotient maximum is about
0.92959, again at (0,pi).

A 128-subdivision diagnostic gave:

    full relaxed width coefficient: 0.9251593561;
    sampled rank-two quotient coefficient: 0.9295872562.

These are NOT certified bounds on the feasible optimum. The continuum upper
bound still needs an all-pairs interval check. The lower bound must be realized
by continuously feasible triples, not merely interpolation eigenvectors.

## 4. Feasibility obstacle and promising sign

The midpoint-maximizing relaxed mode near angle2.79 has opposite violations of
the two outer normal gaps: its right endpoint derivative has the wrong sign
for one orientation and its left-gap support has the wrong sign after reversing
that orientation. A lower estimate obtained by assuming that eigenvector is
feasible would be invalid.

The negative width mode has the correct signs at BOTH gaps. Its first-gap
support is harmonic with positive new endpoint face height, and its last-gap
support is positive with the required left face sign. On the central upper
angles, the reference curvature is positive, allowing bounded smooth
perturbations. On the active auxiliary arcs, B=-f and D=-f preserve the exact
wall equalities. The inactive auxiliary pieces are harmonic interpolants.

This suggests a continuously feasible family after simultaneous one-sided
smoothing at zero-curvature/positive-curvature junctions. It still requires an
explicit audit of containment contacts, derivative jumps, and the unchanged
wall inequalities. A certificate will not treat those conditions as automatic.

The distinction is potentially useful for the paper: the exact feasible
midpoint coefficient and the coefficient modulo arbitrary translations are
separate optimization questions. The latter is the geometrically intrinsic one.
