# An explicit Hausdorff coefficient for all near-maximizers

## Status and precise theorem

This is an analytic proof using the existing local Q-certificate, terminal
comparison, and qualitative-entry arguments. The new geometric refinements
below are proved here. Their full specialization and assembly into a Lean
`UnrestrictedStability` theorem with fixed coefficient have not been completed
or kernel-checked. The supporting source files are uncompiled.

**Derived theorem.** For each reference parameter solution P in the source box,
there is epsilon0>0 such that every original moving sofa S with

    epsilon = |G|-|S| < epsilon0

satisfies, in the prescribed top/left-support normalization,

    d_H(normalizedSofa P S, G) <= 80*sqrt(epsilon).

The same numerical 80 works for every P in that box. The theorem does not give
a numerical epsilon0 or claim that 80 is optimal. It is uniform over all
near-maximizers, not restricted to smooth, injective, or monotone input sofas.

## 1. Reference data with numerical ratios

Retain the notation of note 02: the cap bottom endpoints are (l,0),(r,0), and
the niche roof endpoints are (a,0),(b,0). The source parameter enclosures give

    D = a-l = r-b > 403/500 > 4/5,
    D < 1,      1 < b-a < 13/8,      r-l < 13/4.

The cap contains [a,b] x [0,1], and the reference niche is the strict subgraph
of a nonnegative roof gamma with gamma(a)=gamma(b)=0 and maximum H<1.

As in note 02, the roof has Lipschitz constant 26. This follows directly from
sin(phi)>1/26, the signs of the reference core's two velocity components, the
tail slope bounds, and their matching endpoints. It does not require a numerical
lower bound on horizontal core speed. The reference slack certificate can also
use c_roof=1/26: both core wall coefficients are >=1/26; each tail's active
coefficient is >=1/2, and its inactive slack has a positive compactness margin.
Only the clipping threshold tau remains existential.

### Better Euclidean interior-ball ratio

Set

    kappa = 10/271,
    rho0 = min(1, b-a, (1-H)/8) > 0.

Then G has the interior-ball property at ratio kappa and scale rho0. Here is the
full case split; all balls are Euclidean, closed, and contained in Bbar(p,rho).

**Wing points.** In the left wing, the cap's chord from (l,0) to (a,1) and
vertical downward closure contain [l+D/2,a] x [0,1/2]. The point
z0=(l+3D/4,1/4) has an inscribed disk of radius 1/8 in that rectangle. Every
point of the wing has coordinate distances at most 3/4 from z0, hence Euclidean
distance at most 3/2. Contracting this fixed disk towards an arbitrary point p
of the convex wing gives ratio

    (1/8)/(3/2+1/8) = 1/13 > 10/271

for every rho<=13/8. Shrinking the resulting disk gives the requested ratio.
The right wing is identical. Both wings lie in G, including their cut lines,
because gamma is zero at the roof endpoints.

**Low central points.** Suppose a<=p.x<=b and p.y<=(1+H)/2. Extend gamma by zero
outside [a,b]; it is still nonnegative and 26-Lipschitz. Write

    w = (10/271)*rho,
    z = p + (0,(261/10)*w).

For q=z+v with |v|<=w, Cauchy--Schwarz gives

    26*abs(v.x)-v.y <= sqrt(677)*w < (261/10)*w.

Since p.y>=gamma(p.x), this proves q.y>=gamma(q.x). In particular q.y>=0.
Also q.x is within rho of [a,b]. The convex cap contains the trapezoid with
vertices (l,0),(a,1),(b,1),(r,0). Its top over this enlarged interval is at
least 1-2*rho, because D>=1/2. The enlargement lies between l and r because
rho<=(1-H)/8<=1/8<D. Meanwhile

    q.y <= p.y+rho <= (1+H)/2+rho <= 1-2*rho.

Thus q lies in the cap and above the zero-extended roof, hence in G. Finally,

    |z-p|+w = (271/10)*w = rho.

This uses the Euclidean norm directly and improves the old ratio 1/28.

**High central points.** Suppose p.y>(1+H)/2. Set w=rho/4. Move the center by
w horizontally towards the farther endpoint of [a,b] and by w vertically
downward. Its radius-w disk lies in [a,b] x [H,1]: horizontal fit uses
rho<=b-a, and the lower height uses rho<=1-H. The disk is within distance
3w<=rho of p. Shrink it to radius (10/271)*rho.

This proves HasInteriorBalls G (10/271) rho0 without assigning a numerical value
to rho0. The height gap affects the scale, not the numerical ratio.

## 2. Enter the local regime, then preserve the deficit split

The existing qualitative-entry theorem and normalization allow us to work with
a right-angle completion K of the normalized input and a reduced angle omega.
Shrink epsilon0 until all existing local certificate, support-neighborhood,
terminal, and roof-margin hypotheses hold. Put

    U = K minus N(K),
    e = M-|U|,           alpha = pi/2-omega,
    g = |S minus U|,     m = |U minus S|.

The local geometric certificate gives |U|=A(K)<=Q(xi_K)<=M. The terminal
comparison gives |S|<=|U|-c*alpha and g<=c*alpha for a fixed c>0. Therefore

    0 <= e <= epsilon,
    c*alpha <= epsilon-e,
    g <= epsilon-e,
    m = epsilon-e+g <= 2*(epsilon-e).

No containment S subset U is assumed. The final equality here is the finite
measure identity, not a continuity assertion for nonconvex area.

The improved cap estimate gives an actual Euclidean/support error delta with

    delta <= k*sqrt(e),     k=2/cos(phi)<=1001/500.

The prescribed left-support normalization removes its horizontal translation.

## 3. Reverse directed distance: retain the entire disk

Orthogonality of the two hallway normals proves

    G eroded by radius sqrt(2)*delta is contained in U.

See note 01 and `OrthogonalErosion.lean`; the original factor 2 is unnecessary.
At scale rho the interior-ball property supplies a disk of radius kappa*rho.
After erosion, its surviving radius is kappa*rho-sqrt(2)*delta. If S missed the
entire rho-neighborhood of p in G, that disk would be part of U minus S. Thus
any rho<=rho0 satisfying

    sqrt(2)*delta + sqrt(m/pi) < kappa*rho

gives directed distance from G to S at most rho. This is precisely the
full-disk comparison in `DiskRecovery.lean`.

Take rho=80*sqrt(epsilon), reducing epsilon0 to ensure rho<=rho0. The budget
split and Cauchy--Schwarz give

    sqrt(2)*delta+sqrt(m/pi)
      <= sqrt(2)*k*sqrt(e)+sqrt(2/pi)*sqrt(epsilon-e)
      <= sqrt(2*k^2+2/pi)*sqrt(epsilon)
      < (59/20)*sqrt(epsilon)
      < (10/271)*80*sqrt(epsilon).

The two strict numerical inequalities use only k<=1001/500 and pi>3. They
are supplied in uncompiled source by `RefinedConstantAlgebra.lean`.
This proves the reverse direction with coefficient 80 when epsilon>0.

## 4. Forward directed distance: do not promote a linear error

The existing approximate-hallway estimate and the roof margin give

    directed_distance(S,G) <= 26*(delta+B*(epsilon-e))

for some fixed B>=0. Here B absorbs the terminal coefficient and the reference
bounding rectangle. It is not necessary to compute B to specify the leading
coefficient: reduce epsilon0 until B*sqrt(epsilon)<=1. Then

    26*(delta+B*(epsilon-e))
      <=26*(1001/500+1)*sqrt(epsilon)
      =78.052*sqrt(epsilon)
      <80*sqrt(epsilon).

The old argument made the coefficient depend on B by replacing epsilon with
sqrt(epsilon) too early. Keeping the actual two-scale estimate avoids that loss.
The smallness assumptions delta<d0 and delta+B*(epsilon-e)<tau hold after a
further reduction of epsilon0, because both terms tend to zero.

## 5. Zero deficit and quantifiers

For epsilon=0 use the existing exact normalized uniqueness theorem; both sets
are equal. Every threshold reduction above is by a fixed positive number
determined by the reference, so their finite minimum and the qualitative-entry
threshold give one positive epsilon0 for all input sofas. No smoothness or
injectivity of S has entered the argument.

This supplies the stated numerical coefficient 80. The proof remains a local
near-optimality theorem with a global quantifier over S. It does not furnish an
effective positive epsilon0, nor a bound valid for all deficits with the same 80.

## Numerical perspective, not an optimality claim

The reverse-direction reference formula with these conservative ratios is

    sqrt(2*k^2+2/pi)/kappa <= 79.715597...

at k=2.002 and kappa=10/271. The forward leading coefficient is at most 52.052;
its linear remainder is absorbed into the threshold. Choosing 80 leaves a
rationally provable margin. Replacing the rational center shift by its exact
Euclidean value would reduce the reverse budget to about 79.478, but would not
make 80 optimal for the moving-sofa problem. The punctured-sofa example supplies
only the lower bound 1/sqrt(pi) for any universal near-optimal Hausdorff coefficient.
