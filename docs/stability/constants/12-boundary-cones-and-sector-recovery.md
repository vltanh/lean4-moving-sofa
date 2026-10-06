# Rotate the boundary charts and use the whole eroded sector

Analytic work only. No Lean source is changed or verified. This note replaces
the coordinate-dependent interior-ball ratio by the actual boundary angles and
uses the full area of a sector, rather than one inscribed disk.

## 1. Correction to the initial quarter-plane hypothesis

The two outer floor corners are NOT exactly right angles. On the first Romik
phase, contact A(t) is the fixed point (1,0) for 0<=t<=phi. To check this directly,
write x'=-a*u+b*v. The first-phase formulas give

    a=2*a1*sin(t)+(1/2)*cos(t)-1/2,
    b=2*a1*cos(t)-(1/2)*sin(t)-1,
    a'=b+1.

Since A_contact=x-a*v+u, its derivative is (b-a'+1)*v=0. The nonconstant
outer boundary starts at normal angle phi. The floor meets it with interior
angle pi/2-phi, not pi/2. The reflected corner has the same angle.

This invalidates using an exact quarter-plane cone at those corners. It does
not invalidate the improvement: phi<=0.04 and pi>3.14159 give

    pi/2-phi > 1.530795 > beta := 153/100.

The strict margin is reserved for variation of the boundary tangent nearby.
The first exploratory note's pi/2 cone was a hypothesis, not a proved result.

## 2. Audit of the other junctions

The outer reference boundary consists of the contact arcs and the horizontal
upper segment. Each nonconstant contact arc has tangent perpendicular to its
support normal. Adjacent arcs meet at the same point and normal, so changes
of curvature or speed do not create an extra corner. The flat upper segment
has the same limiting horizontal tangent as its neighboring arcs. The only
outer normal gaps are the two endpoint intervals just described.

The lower boundary is the zero-extended three-piece niche roof. The tails meet
the floor tangentially (their end parameter is 0 or pi/2). The reference core
is regular: x'=-a*u+b*v with a,b>0; it has negative horizontal speed. Across
its internal phase changes the first derivative is continuous.

At the left tail/core junction the tail tangent has angle theta. The core,
traversed from left to right, has angle eta in (0,pi/2): positivity of its slope
there follows from the phase-2 velocity bounds and reflection. The epigraph's
interior angle is pi+theta-eta. Whether or not eta>theta, this is strictly
larger than pi/2. The reflected junction has the same opening. For the numerical
reference, eta is about 1.464235 and the opening is about 2.358659 radians
(135.141 degrees); these numbers are diagnostics, not needed for the inequality.

There are no contacts between the upper and lower graphs except the two outer
floor corners: the central cap rectangle and positive roof-to-ceiling gap give
strict separation elsewhere. The cap plus zero-extended roof description
therefore gives a simple closed, finite piecewise regular C1 boundary. All its
interior angles exceed beta=1.53.

The reference facts used here are the explicit contact formulas and matching
conditions, the cap/contact boundary description, and the three-piece envelope
in GerverRoof/EnvelopeSlope. No regularity is imposed on a competing sofa.

## 3. Uniform translated interior sectors

Let W_beta={r*(cos(theta),sin(theta)): r>=0, |theta|<=beta/2}, with its axis
rotated as needed. There is R0>0 such that for every p in G, some rotation W_p
satisfies

    (p+W_p) intersect closedBall(p,R0) is contained in G.             (1)

Here is the uniformity argument. At a regular boundary point, rotate its tangent
so the set is locally an epigraph with arbitrarily small slope. At a corner
with interior angle greater than beta, rotate the angle bisector; both limiting
one-sided slopes are strictly smaller in absolute value than cot(beta/2).
Continuity of the one-sided tangents supplies a neighborhood with that common
Lipschitz bound. Translating the corresponding cone from ANY point of the
local epigraph stays in it while inside the chart. A finite cover of the compact
boundary, with smaller concentric neighborhoods, gives a uniform chart radius
for all sufficiently near-boundary points. Points farther inside have a fixed
ball contained in G and hence admit the same truncated cone. Take the minimum
of these finitely many positive radii. Curvature jumps do not affect the argument.

The scale R0 remains existential. This is a local geometric property of the
fixed reference, not an effective entry theorem for arbitrary competitors.

## 4. Erosion of the entire sector

Suppose G eroded by a closed Euclidean disk of radius r is contained in U.
Fix p in G, a cone W_p in (1), and a target distance rho with rho+r<=R0.
Inside closedBall(p,rho), retain all points of p+W_p whose distances from BOTH
sides of the infinite wedge are at least r. Every closed radius-r disk about
such a point stays in the wedge and in closedBall(p,R0), hence in G. Therefore
this whole region is contained in U.

If S has no point within rho of p, the entire region lies in U minus S.
This argument compares actual sets; neither S nor U is assumed convex.

Put u=r/rho and h=beta/2. For 0<=u<sin(h), the region's exact area is

    rho^2 * F_beta(u),
    F_beta(u)=h-asin(u)-u*sqrt(1-u^2)+u^2*cot(h).                    (2)

To derive it, in polar coordinates about p the allowable angles satisfy
|theta|<=h-asin(u), and the radial coordinate runs from
r/sin(h-|theta|) to rho. Integrating (rho^2-r^2/csc-denominator)/2 on both sides
of the bisector gives (2). If u>=sin(h), the area is zero.

Thus

    |U minus S| < rho^2*F_beta(r/rho)                              (3)

forces directed distance from G to S at most rho. No ball ratio kappa appears.
At r=0 the surviving area is exactly (beta/2)*rho^2.

## 5. A simpler, weaker sector estimate

The eroded wedge has vertex at distance r/sin(h) from p along the bisector.
A sector with that vertex and radius rho-r/sin(h) lies in the same region.
Its area is (beta/2)*(rho-r/sin(h))^2. This gives the convenient bound

    rho > r/sin(h)+sqrt(2*m/beta),       m=|U minus S|.

With r=sqrt(2)*k*sqrt(e), m<=lambda*(epsilon-e), the resulting sufficient
coefficient is

    sqrt(2*k^2/sin(h)^2 + 2*lambda/beta).

For beta=1.53, lambda=1.0031, this is about 4.24558 at the old pinned k=2.002,
and 2.34301 at the new centered k=1.001. Whole-sector recovery already beats
the old 30.5 substantially. The next note optimizes (2) itself, not just this
inscribed-sector lower bound.

## 6. Limitations

Do not use beta=pi/2: it fails at the outer corners. Do not deduce (1) from a
sampled tangent plot or from a Hausdorff approximation. The reference's exact
piecewise boundary and strict corner margins are essential. Do not call the
sector coefficient the sharp sofa constant: erosion is still a sufficient
condition that can discard points of U which were never actually lost.
