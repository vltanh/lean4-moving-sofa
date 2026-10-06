# Quantifying reference scales without claiming an effective global threshold

This note is an analytic refinement of note 06. It supplies explicit reference
scales for several steps that were previously left to compactness. The last
section identifies the remaining gap to a usable numerical pair (C,epsilon0).
No Lean compilation or kernel verification is claimed.

## 1. The roof is below 2/3

The reference path height attains its maximum at t=pi/4. Here is a direct
phase-wise justification, rather than a plot-based inference.

On the first phase, t<=phi<=0.04, the frame components satisfy

    a=2*a1*sin(t)+(cos(t)-1)/2 <= 2*1.211*0.04 < 0.097,
    b=2*a1*cos(t)-sin(t)/2-1 > 1.39.

The existing signs give a>=0. Consequently
Y=-a*sin(t)+b*cos(t)>0, using sin(t)<=0.04 and cos(t)>=1-0.04^2/2.

On the second phase t<=theta<=0.69, the parameter enclosures give

    a<=3/4,       b>=93/100,
    sin(t)<=0.69, cos(t)>=1-0.69^2/2.

Thus Y>=0.93*(1-0.69^2/2)-0.75*0.69>0. The lower bound on b follows from
b2>=0.9202, b1>=-0.528, and t<=0.69, retaining the negative quadratic term.

On the third phase before pi/4,

    a=1+c2+t,       b=1+c1-t,
    b-a=pi/2-2*t>=0.

Since cos(t)>=sin(t) and a,b>=0, Y=(b-a)*cos(t)+a*(cos(t)-sin(t))>=0.
The C1 matching and reflection symmetry handle all later phases. Therefore
all reference path heights are at most their value at pi/4. Each tail envelope
point has height no larger than the corresponding path point because the tail
frame coefficients have the established signs.

The maximum height is

    H = kappa3.y + (2*c1-pi/2)/sqrt(2).

Use the rational enclosures c1<=6261/10000, kappa3.y<=8897/10000, together with
pi>157/50 and sqrt(2)<283/200. The numerator is negative, so the upper bound on
the denominator gives the correct upper bound:

    H < 8897/10000-(1589/5000)*(200/283)
      =1882251/2830000 < 2/3.

Consequently the reference interior-ball scale in note06 can be fixed at

    rho0 = 1/24,

since b-a>1 and (1-H)/8>1/24. This does not change the ratio kappa=100/1051.

## 2. A numerical outer-wall margin

The reference niche is inside [a,b] x [0,H]. Let D=a-l=r-b>=4/5. For an upper
normal with c=abs(cos t), s=sin t>=0, the reference cap contains the relevant
floor endpoint and top endpoint. For every p in the reference niche its
support slack is therefore at least

    max(D*c-H*s, (1-H)*s).

This quantity is at least 1/5. Otherwise the second term would imply s<3/5,
and the first, with D>=4/5,H<=2/3, would imply c<3/4. But then
c^2+s^2<9/16+9/25<1, contradicting c^2+s^2=1.

Thus the outer-support margin may be fixed at

    d_outer = 1/5.

This applies to every upper normal, including the two horizontal endpoints.
It eliminates another unspecified compactness minimum in forward recovery.

## 3. Quantitative uniformity of the adaptive-angle argument

The five path formulas have the form x(t)=R_t f(t)+kappa on 0<=t<=pi/2<2.
The parameter enclosures give the following convenient uniform bounds:

    |x'(t)| <= 10,
    x' is 100-Lipschitz on the full turn.

For completeness these follow by direct differentiation. On phase1, the sums
of absolute coordinates of f, f', and f'' are bounded respectively by 4.424,
2.924, and 2.924. Hence |x'|<=7.348 and |x''|<=13.196 there. On phase2 the
corresponding bounds 5.506, 2.028, 0.5 give |x'|<=7.534, |x''|<=10.062. On phase3,
using |c1|<0.627 and |c2|<1.374 (pi/2<2), the bounds 6.001,2,0 give
|x'|<=8.001 and |x''|<=10.001. Reflection handles phases4 and5.
The loose integer bounds 10 and100 follow. The derivative is continuous at the
junctions, so piecewise derivative Lipschitz bounds combine across them; no
second derivative at the junction itself is required.

On the exposed core a+b>=1. In phase2 this follows from a>=0.0944 and
b>=0.93; in phase3 it follows from a+b=2+2*c1-pi/2>1; phase4 follows by
reflection. Thus

    |lambda(t)|=|(sin(t)-cos(t))/(a+b)|<=1.

For the adaptive wall slack F_j(t,d), let s=t+lambda(t)*d. Its derivative is

    partial_d F_j = <-e_y-lambda*x'(s),n_j(s)>
                 +lambda*<x(t)-d*e_y-x(s),n'_j(s)>.

Subtract the value at d=0. The trigonometric frame is 1-Lipschitz, x is
10-Lipschitz, x' is100-Lipschitz, and |lambda|<=1, so

    |partial_d F_j(t,d)-partial_d F_j(t,0)|
      <=11*d+100*d+11*d=122*d.

Take d_star=1/200000. Since phi>0.039, all shifted angles stay in (0,pi/2).
The exact inequality

    122/200000 < 10/101-5/51

then yields the required derivative bound -5/51 on 0<=d<=d_star. The clipped
core slack threshold can be fixed at

    tau = (5/51)*d_star = 1/2040000.

On the two tails the inactive frame speed is at least0.9: on phase1 this is
immediate from b>1.39, on phase2 from b>=0.93, and on the reflected tail by
symmetry. The active vertical coefficient is at least1/2. Therefore both tails
also admit this much smaller common tau, with c_roof=5/51. This supplies explicit
reference clipping constants, not just a continuity-based existence proof.

## 4. Explicit downstream recovery conditions

Suppose the local area certificate and the improved terminal comparison already
apply to a normalized input. They provide e in [0,epsilon],

    delta<=2.002*sqrt(e),       alpha<=3.1*(epsilon-e).

Once the cap support error is at most1, its Euclidean radius is at most4:
the reference is inside [-2.228,1] x [0,1] and Euclidean cap error is at most1.
Thus the approximate full-angle slack can be bounded by

    zeta<=16*alpha<=49.6*(epsilon-e).

For epsilon<=10^(-14), all these explicit recovery requirements hold:

    delta+zeta <= 2.002*10^(-7)+49.6*10^(-14) < 1/2040000,
    delta < 1/5,
    (61/2)*sqrt(epsilon) <= 3.05*10^(-6) < 1/24,
    49.6*sqrt(epsilon) <= 1/2,
    sqrt(epsilon) <= 1/200.

Thus 10^(-14) is a concrete sufficient bound for the DOWNSTREAM radius, margin,
linear-remainder, and area-budget conditions, once the local area/terminal
certificates hold. The inequalities are exact rational checks after setting
sqrt(epsilon)<=10^(-7).

## 5. What is still not an effective theorem

This does NOT prove that every sofa with deficit <=10^(-14) is in the local
certificate regime. The remaining obstacles are:

1. numerical support-neighborhood radii for the local canonical-body and area
   certificate;
2. numerical neighborhood/angle radii for the terminal floor and omitted-wedge
   localization;
3. a numerical global separation gap excluding all normalized sofas outside
   those neighborhoods.

The existing uniqueness/compactness argument proves that the last gap is
positive, but does not compute it. A certified branch-and-bound cover or another
quantitative global reduction could supply it. The earlier floating-point
Q experiments, whose discretization can relax continuous constraints, do not.

Accordingly the strongest unconditional analytic assertion remains

    explicit C_H=30.5, C_area=100, C_angle=3.1, with existential epsilon0>0.

The explicit downstream threshold is a useful intermediate calculation, not
permission to substitute10^(-14) for that existential epsilon0. This distinction
is essential for any numerical validation application.
