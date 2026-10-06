# Rational reference geometry for a global coefficient

This is a written analytic proof. It uses the reference facts already established
in `GerverRoof`, the envelope hypotheses, and `GerverParams.Bounds`. It does not
assert that the new adapters have been Lean-checked.

Write the bottom endpoints of the cap as (l,0),(r,0), and the niche-roof endpoints
as (a,0),(b,0). The reference cap contains [a,b] x [0,1]; the niche has a
nonnegative roof gamma with gamma(a)=gamma(b)=0 and maximum H<1.

## 1. Explicit lengths from existing parameter enclosures

The endpoint identities in the Gerver/bridge construction give

    l = 2*kappa3.x-1,       r = 1,
    a = 1-2*a1,             b = 2*kappa3.x-1+2*a1.

The existing rational enclosures are

    1.210322322 <= a1 <= 1.210322523,
    -0.613763330 <= kappa3.x <= -0.613763129.

Consequently both wing widths equal

    D = a-l = r-b = 2-2*a1-2*kappa3.x,
    0.806881212 <= D <= 0.806882016.

In particular 4/5 < D < 1. Also

    1 < b-a < 2,       r-l < 4.

These are rational-arithmetic consequences, not floating-point measurements.
They imply that G is contained in [l,r] x [0,1] and that its convex cap has area
at most 4. A Euclidean disk of radius 1/4 centered at ((a+b)/2,1/2) lies in the cap.

## 2. A reference roof Lipschitz coefficient of 26

On the exposed core, t lies in [phi,pi/2-phi]. The source box gives
0.039<=phi<=0.04. Taylor's elementary bound gives

    sin(phi) >= phi-phi^3/6 >= 0.039-0.04^3/6 > 1/26.

Hence sin(t),cos(t)>=1/26 throughout that interval. Write the reference velocity
as alpha(t)*u_t+beta(t)*v_t, where alpha<0 and beta>0. Then

    -x'(t).x = (-alpha)*cos(t)+beta*sin(t)
                >= ((-alpha)+beta)/26,
    |x'(t).y| <= (-alpha)*sin(t)+beta*cos(t)
                <= (-alpha)+beta.

Thus |dy|<=26*(-dx). Integration gives a slope bound of 26 for the core without
choosing an unspecified minimum horizontal speed. The two tails already have
slope at most 2 in `EnvelopeSlope.lean`; joining at the matching endpoints gives

    |gamma(x)-gamma(y)| <= 26*|x-y|.

Extend gamma by zero outside [a,b]. Its endpoint zeros and nonnegativity imply
that this extension is globally 26-Lipschitz.

The same trigonometric lower bound gives the coefficient c_roof=1/26 in the
source's `RoofSlackMargin`. On each tail the active wall coefficient is at least
1/2, while the inactive wall has a positive compactness margin. On the core
both coefficients are at least 1/26. The clipping threshold tau remains
existential; only the slope factor becomes explicit. Thus the forward recovery
factor can be fixed at F=max(1,1/c_roof)=26.

## 3. Explicit local interior balls: kappa=1/28

The interior-ball SCALE may depend on the positive roof-to-ceiling gap 1-H.
Its ratio kappa need not. Set

    rho0 = min(1, b-a, (1-H)/8) > 0.

The reference facts give H>=0. We prove that, for every p in G and
0<rho<=rho0, there is a closed disk of radius rho/28 contained in
G intersect Bbar(p,rho).

### Wing points

For the left wing, convexity and the chord from (l,0) to (a,1) put the rectangle

    [l+D/2,a] x [0,1/2]

inside it. Its center z0=(l+3D/4,1/4) has a disk of radius 1/8 inside that
rectangle because D>=1/2. Every wing point has coordinate distances at most
3D/4 and 3/4 from z0, hence Euclidean distance at most 3/2, because D<=1.

The existing convex ball-contraction construction therefore supplies ratio

    (1/8)/(3/2+1/8) = 1/13

at every scale at most 13/8. Shrink its disk to radius rho/28. The right wing
is treated identically. This argument covers their artificial top cut corners
without any assumed smoothness.

### Low central points

Suppose a<=p.x<=b and p.y<=(1+H)/2. Put w=rho/28 and

    z = p + (0,27*w).

For q in Bbar(z,w), q.y>=p.y+26*w>=gamma(p.x)+26*w>=gamma(q.x), using the
zero-extended roof. Also q.y>=0 and |q.x-[a,b]|<=w<=rho.

The cap contains the convex trapezoid with vertices (l,0),(a,1),(b,1),(r,0).
For x within rho of [a,b], its top is at least 1-2*rho, since both wings have
width at least 1/2. Meanwhile

    q.y <= p.y+rho <= (1+H)/2+rho <= 1-2*rho,

because rho<=(1-H)/8. Thus q lies in the cap and above the roof, hence in G.
Finally |z-p|+w=28*w=rho. This avoids the unnecessary horizontal shift and
factor four in the old roof-strip ball construction.

### High central points

Suppose p.y>(1+H)/2. Put w=rho/4. Move the center horizontally by w toward the
farther end of [a,b] and vertically down by w. The resulting disk of radius w
lies in [a,b] x [H,1]: its horizontal fit follows from rho<=b-a, and its lower
height from rho<=1-H. Its points lie within 3w<=rho of p. This rectangle is
contained in G. Shrinking from w to rho/28 gives the required disk.

Combining the cases proves

    HasInteriorBalls G (1/28) rho0.

No effective lower bound for 1-H is needed to specify the ratio 1/28. It is
needed only to give a numerical value of rho0.

## 4. What this does and does not compute

We have explicit reference factors

    cap coefficient k <= 1001/500,
    roof recovery factor F = 26,
    interior-ball ratio kappa = 1/28.

The shape-neighborhood radius, clipping threshold, and qualitative-entry deficit
are still not numerically computed. These factors are enough for an explicit
Hausdorff coefficient with an existential positive threshold; they are not yet
an explicit certified range of deficits for numerical use.
