# Explicit terminal neighborhoods and the 3.1 angle coefficient

Analytic argument only. Use the reference notation and cap certificate of
note29. The input S is a normalized original sofa; K is its right-angle cap
completion, whose upper supports agree with S. Suppose

    sup_[0,pi]|h_K-h_Gcap|<=10^(-40),
    0<alpha=pi/2-omega<=10^(-20).                              (1)

No completed right-angle motion of S is assumed. Let U=K minus N(K),
e=M-|U|, epsilon=M-|S|, and g=|S minus U|.

## 1. Two explicit visited angles cover the interior floor

Set

    w=1/100000,   t0=w/16,   t1=pi/2-t0,
    m=(a+b0)/2=kappa3.x in (-1,-3/5).

Both angles are visited because alpha<t0. For the reference, the floor endpoint
(r,0)=(1,0) and top endpoint (a,1) give

    h0(t0)>=cos(t0),
    h0(t0+pi/2)>=-a*sin(t0)+cos(t0).

For a point (x,y) with a+w<=x<=m and 0<=y<=12alpha, its two reference inner-wall
slacks at t0 are at most

    (x-1)cos(t0)+1+y*sin(t0)
      <=-3/5+(4/5)*t0^2+12alpha*t0,
    -w*sin(t0)+1-cos(t0)+y*cos(t0)
      <=-w*t0/2+t0^2/2+12alpha.

The exact checks

    (4/5)*t0^2+12alpha*t0+delta<1/10,
    delta+12alpha<w^2/128

leave both competing slacks strictly negative after adding the support error
delta (the first below-1/2 and the second below-w^2/64). The reference midpoint
bound was strengthened from m<-1/2 to m<-3/5 to make that first strict margin
explicit. Reflection about x=m gives the same conclusion on [m,b0-w] at t1.
Here the reference is reflected and the reflected competing support errors
are still bounded by delta; no symmetry of S or K is assumed. Thus

    S has no point in [a+w,b0-w] x [0,12alpha].                 (2)

The support witnesses are fixed explicit points of Gerver's cap, so this does
not require a finite-cover argument or a lower bound on a sampled roof graph.

## 2. Omitted wedges fit in explicit endpoint windows

Every nonempty floor-truncated wedge has its two feet strictly between the
horizontal extremes of K. This follows directly from height<=1 and the upper
support bounds furnished by those extremes. Its height is

    sin(t)cos(t)*(R_K(t)-L_K(t)).

The width of K is below6. For omega<=t<=pi/2, the height is consequently at most
6alpha, and certainly at most12alpha. The horizontal niche localization from
note29, with eta=w, confines all such points to [a-w,b0+w]. A point of S in
the full-angle niche can only come from an omitted wedge: visited wedges are
forbidden by its actual motion. Combining this with (2) leaves only two windows
of total width4w. Therefore

    g <=48w*alpha < alpha/1000.                               (3)

All omitted wedges are bounded at once by this same rectangle union. Their
areas are not summed separately, and no arbitrary subset of S is discarded.

## 3. A fixed floor trapezoid belongs to U

Put D=a-l and eta=D/1000. Let I=[l+eta,a-eta] and lambda=999/1000. Define

    F_alpha={(x,y): x in I, 0<=y<=lambda*alpha*(a-x)}.

The reference cap contains the triangle conv{(l,0),(a,0),(a,1)}. For x in I
and 0<=y<=1/2000 its upper-support margin is at least eta/4>1/10000.
One direct verification writes, with c=-cos(t)>=0,s=sin(t), the slack as

    max((x-l)c-y*s, -(a-x)c+(1-y)*s)

when cos(t)<=0. The two expressions cross at s=D*c; their minimum over t is
at that crossing or an endpoint. At the crossing it is
((x-l)-D*y)/sqrt(1+D^2)>=eta/(2sqrt(2))>eta/4.
For cos(t)>=0 the top endpoint alone gives at leasteta. The floor inequality
is kept separately, since a Euclidean ball about a floor point is not contained.

By (1), F_alpha has height below1/2000 and remains in K. Its rightmost abscissa
is a-eta<a-w, while the competing niche starts no farther left than a-w.
Consequently F_alpha is disjoint from N(K) and is contained in U.

## 4. The terminal strip excludes the whole trapezoid

The top-face localization of note29 with eta_top=10^(-8) provides a point
q=(q.x,1) in K with q.x>=a-zeta, zeta=10^(-8). Thus h_K(omega)>=<q,u_omega>.
For p=(x,y) in F_alpha, put v0=a-x, so eta<=v0<=D-eta. Its terminal lower-wall
violation is bounded below by

    <q-p,u_omega>-1
      >=(v0-zeta)sin(alpha)+cos(alpha)-1-lambda*alpha*v0
      >=alpha*((1-lambda)*v0-zeta-alpha/2-v0*alpha^2/6).

The exact inequalities

    zeta<eta/4000,
    alpha/2+D*alpha^2/6<eta/4000,
    (1-lambda)*v0>=eta/1000

make this strictly positive. Therefore no point of F_alpha belongs to S.
The terminal-strip support is h_S(omega)=h_K(omega); no assumption S subset U
has been used to assert this exclusion.

## 5. Deficit budget with explicit hypotheses

The trapezoid area is

    |F_alpha|=(999/1000)*(499/1000)*D^2*alpha.

Since F_alpha subset U and F_alpha is disjoint from S,

    |S|<=|U|-|F_alpha|+g
         <=|U|-[(999/1000)*(499/1000)*D^2-1/1000]*alpha.

At D>=403/500, the bracket is strictly greater than10/31, by exact rational
arithmetic. The local cap certificate supplies |U|=A(K)<=M. Hence

    0<=e<=epsilon,
    alpha<=(31/10)*(epsilon-e),
    g<=(31/10000)*(epsilon-e),
    |U minus S|=epsilon-e+g<=(10031/10000)*(epsilon-e).          (4)

At alpha=0, S subset U and the same conclusions hold with g=0. Thus (4) has
no division-by-zero exception. The displayed support and angle radii in (1)
replace the previous unspecified floor-persistence and omitted-window radii.

## Scope

The argument applies to the specified input sofa and its own cap completion,
not to an auxiliary optimizer. It remains analytic and relies on note29's
reference contact and local cap facts. Scalar checks alone do not prove that
those geometric identities or the earlier global entry modulus are correct.
