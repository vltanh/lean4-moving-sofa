# Arm-closure audit and continuation

Starting checkpoint: a38fc00d17d5a495f275b7ed886166271c5320f2. This continuation attempts to close the all-obtuse reverse theorem. No CI, workflow invocation, or Lean build is used. New claims must follow from verified geometric hypotheses, not a plausible ODE analogy.

## A prerequisite gap in the preceding notes

REVERSE_PIECEWISE_CURVATURE.md uses absolute continuity of the arms on their zero sets. The preceding REVERSE_LOCAL_VARIATION.md also invokes O(delta) facet jumps before providing a uniform curvature bound. Those are not consequences of uniform support convergence alone. A convex support function can have atoms in its curvature measure. Thus those passages must be treated as conditional calculations until a discrete uniform measure bound and endpoint argument establish the claimed regularity.

The suggested use of a classical second derivative at a horizontal tangent also needs additional regularity or a distributional/no-crossing argument. An almost-everywhere curvature inequality cannot simply be evaluated at an arbitrary isolated tangent. No all-obtuse optimality theorem follows from those notes as currently written.

## Verified support identities to retain

With e=pi-beta, q=sin(e), d=cos(e), phi+psi=e, define the two unit normals and tangents as in REVERSE_MAXIMIZER_ARMS.md. At differentiability points of the actual convex support, the identities

    n1.C'=a, n2.C'=-b,
    q y'=sin(psi)a+sin(phi)b,
    a'=rho_+-1-d a/q+b/q,
    b'=1-rho_- -a/q+d b/q

are obtained by direct differentiation. In the nonsmooth setting the last two require the corresponding curvature measures rather than assuming ordinary densities.

There is also a useful geometric constraint independent of maximality. Both support contacts lie in the actual strip of height w<=1, so

    sin(phi)a+sin(psi)b >= cos(phi)+cos(psi)-w > 0.

Consequently a and b cannot both be nonpositive at an interior angle. This follows directly by subtracting the support-contact heights. It is stronger than treating the two arm variables as unrelated scalar functions.

Equivalently set A=1+d, F=A-q a, G=A-q b. Convexity gives F,G>=0, and the same strip-height constraint becomes

    sin(phi)F+sin(psi)G <= q w.

The resulting arm system and this geometric constraint will be audited together. A scalar counterexample to a weakened system is not automatically a feasible sofa.

## Immediate work

1. Check the exact two-neighbor exposed-length inequality without assuming small facet jumps.
2. Separate genuine geometric bounds from formal continuum heuristics.
3. Seek either a valid all-maximizer arm bootstrap or an area comparison avoiding arm positivity.
4. Preserve any counterexample and revise dependent claims rather than claiming closure from a failed premise.

The restricted reverse theorem and the numerical/analytic candidate formulas are not extended by this audit note. Independently reviewing earlier foundational identities remains part of the work.
