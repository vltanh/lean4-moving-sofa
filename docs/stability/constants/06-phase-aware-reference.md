# Phase-aware reference geometry and an adaptive hallway witness

This note strengthens the conservative reference data in notes 02 and 04.
It is a written analytic argument. The rational/scalar parts have supporting
Lean source; the uniform C1 neighborhood argument and full Gerver adapters
are not claimed kernel-checked or completely assembled in Lean.

The reference is the fixed Gerver parameter solution P in the source box.
Only this reference path is differentiated. No smoothness is imposed on a
competing cap or sofa.

## 1. Explicit frame velocities on the second phase

Write the reference path velocity as

    x'(t) = -a(t)*u_t + b(t)*v_t,
    X(t) = -x'(t).x = a(t)*cos(t)+b(t)*sin(t),
    Y(t) = x'(t).y = -a(t)*sin(t)+b(t)*cos(t).

The existing sign theorem gives a,b>0 in the interior of the turn. Differentiating
Romik's second phase, on [phi,theta], gives exactly

    a(t) = t-1-2*b1,
    b(t) = 1/2-t^2/4+b1*t+b2.

`GerverParams.Bounds` supplies

    phi >= 0.039177264,
    b1 <= -0.527624498,
    b2 <= 0.920258486.

In particular, throughout this phase,

    a(t) >= 59/625 = 0.0944,
    0 < b(t) <= 7/5.

For the upper bound on b it suffices to use b1<=-527/1000, b2<=9203/10000,
and t>=39/1000, discarding -t^2/4. These are all rational consequences of the
source enclosures, not values fitted from a computed boundary.

## 2. Better slope and transversality bounds

Let

    L = 189/20 = 9.45,
    c0 = 10/101.

We prove throughout the exposed core t in [phi,pi/2-phi] that

    |Y(t)| <= L*X(t),
    X(t) >= c0*(a(t)+b(t)).

### Second phase with t<=1/8

The source lower bound for phi and elementary Taylor inequalities give

    sin(t) >= 39/1000,
    cos(t) >= 127/128.

For the sine bound, monotonicity on [0,pi/2] reduces to phi, and
phi-phi^3/6 >= 0.039177264-0.04^3/6 > 0.039.
For the cosine bound use 1-t^2/2.

Put amin=59/625, bmax=7/5, smin=39/1000, cmin=127/128. Then

    L*X-Y = a*(L*cos+sin)+b*(L*sin-cos)
      >= amin*(L*cmin+smin)+bmax*(L*smin-1)
      = 190489/40000000 > 0.

This bound is valid even if L*sin-cos changes sign: first replace it by the
negative lower bound L*smin-1, then use b<=bmax. The other direction follows
from -Y<=a and L*X>=L*a*cos>=a.

Similarly,

    X-c0*(a+b) = a*(cos-c0)+b*(sin-c0)
      >= amin*(cmin-c0)+bmax*(smin-c0)
      = 2441/8080000 > 0.

Again the substituted coefficient of b is negative, so its upper bound is the
correct one to use.

### Second phase with t>=1/8

Since t<=theta<pi/4,

    sin(t) >= sin(1/8) >= 383/3072 > 1/L,
    cos(t) >= 1/2 > 1/L.

Hence X>=(a+b)/L and |Y|<=a+b. The same two trigonometric lower bounds exceed
c0, proving the transversality bound as well.

### Middle phase and reflected fourth phase

On [theta,pi/2-theta], both sine and cosine exceed 1/2, since theta>=0.68>pi/6.
Thus X>=(a+b)/2 and |Y|<=a+b, stronger than both desired inequalities.
The fourth phase is the reflection of the second under t -> pi/2-t; a and b
are interchanged, X is unchanged and Y changes sign. The bounds therefore
transfer. Matching of the reference first derivatives includes the junctions.

Integrating |Y|<=L*X, using X>0, makes the core a graph with Lipschitz constant
L. The two existing tail estimates have coefficient 2, and the pieces join at
their actual endpoints. The whole niche roof, extended by zero outside its
floor interval, is consequently 189/20-Lipschitz.

## 3. Do not use the same hallway angle below a core point

The old vertical-slack argument tested the point below x(t) only at angle t.
It paid the small factor min(sin(t),cos(t)), about 0.039 near the endpoint.
Instead adapt the test angle so BOTH wall violations have the same first-order
size.

For a core parameter t, let

    lambda(t) = (sin(t)-cos(t))/(a(t)+b(t)),
    s(t,d) = t+lambda(t)*d,
    p(t,d) = x(t)-(0,d).

Define the two reference wall slacks

    F1(t,d) = <p(t,d)-x(s(t,d)),u_(s(t,d))>,
    F2(t,d) = <p(t,d)-x(s(t,d)),v_(s(t,d))>.

At d=0 both are zero. Differentiation in d, holding t fixed, gives

    partial_d F1(t,0) = -sin(t)+a(t)*lambda(t),
    partial_d F2(t,0) = -cos(t)-b(t)*lambda(t)
                       = -X(t)/(a(t)+b(t)).

The first expression is the same fraction as the second. The terms from
rotating u and v vanish at d=0 because p(t,0)-x(s(t,0))=0. Thus both derivatives
are at most -10/101, uniformly over the compact core interval.

### Uniformity requires C1, not C2

The reference path is C1 across all phase boundaries. Its derivative is
continuous, and a+b is positive on the compact core, so lambda is continuous
and bounded there. Since the core is strictly inside (0,pi/2), there is a fixed
positive d0 such that s(t,d) stays in (0,pi/2) for all core t and 0<=d<=d0.

The derivatives partial_d Fj(t,d) are continuous jointly in (t,d): they involve
only x, x', lambda, and the trigonometric frame, not x''. Uniform continuity
on a compact rectangle then allows d0 to be reduced until both derivatives
are at most -c, where

    c = 5/51,
    10/101-5/51 = 5/5151 > 0.

Integration from 0 to d proves Fj(t,d)<=-c*d for 0<=d<=d0. This is a uniform
estimate at all core endpoints and phase transitions, not a pointwise asymptotic
claim with a t-dependent neighborhood.

For d>d0, retain the angle s(t,d0) and lower p further. Both wall slacks decrease,
because sin(s),cos(s)>0. Consequently the clipped bound

    both slacks <= -min(c*d,c*d0)

holds for all relevant depths. The tested point is allowed to cross below the
floor; when applying the niche criterion one separately retains nonnegative
height, exactly as in the existing roof-margin definition.

### Tail pieces

On each tail the active wall has vertical coefficient at least 1/2, while
the inactive wall has a uniform strictly negative margin, including its floor
endpoint. These are existing envelope facts. Since c=5/51<1/2, the same clipped
bound applies, after intersecting the clipping thresholds of the core and the
two tails.

The result is an explicit reference roof-margin coefficient

    c_roof = 5/51,
    F = max(1,1/c_roof) = 51/5 = 10.2.

Only its clipping threshold remains existential. This adaptive-angle improvement
is independent of and stronger than merely sharpening the roof Lipschitz bound.

## 4. Euclidean interior balls at ratio 100/1051

Use the reference cap trapezoid and positive roof-to-ceiling gap as in note 04.
Let

    h = 951/100 = 9.51,
    kappa = 100/1051 = 1/(h+1),
    rho0 = min(1,b-a,(1-H)/8)>0.

The exact inequality

    h^2-(L^2+1)=86/625>0

means that a ball of radius w around p+(0,h*w) stays above any L-Lipschitz roof
whenever p is above that roof. For low central points choose w=kappa*rho. The
ball lies within distance (h+1)*w=rho of p. The cap trapezoid argument of note04
still applies because q.y<=p.y+rho and the horizontal enlargement is at most
rho. Thus the ball lies in the actual nonconvex reference sofa.

For wing points, improve the earlier contraction bound as well. The fixed
radius-1/8 inscribed disk centered at (l+3D/4,1/4) has Euclidean distance at most
3*sqrt(2)/4<9/8 from every point of the wing, since each coordinate distance is
at most 3/4. Its contraction therefore gives ratio

    (1/8)/(9/8+1/8)=1/10 > 100/1051

at all scales <=5/4. Both wings satisfy this. The high central construction
has ratio 1/4, also larger than kappa. Shrink those disks when necessary.

Consequently

    HasInteriorBalls G (100/1051) rho0.

No lower bound for 1-H is needed to specify kappa. It is still needed to give
a numerical rho0 and hence an effective deficit threshold.

## 5. Status of the improvement

The reference constants used in the strongest analytic result are now

    cap coefficient k<=1001/500,
    roof recovery factor F=51/5,
    interior-ball ratio kappa=100/1051.

The next note gives the global numerical consequences. The argument here uses
only explicit parameter enclosures and established reference geometry, plus
the uniform C1 calculation above. It is not inferred from sampled slopes or
floating-point minimization. Numerical checks serve only as diagnostics.
