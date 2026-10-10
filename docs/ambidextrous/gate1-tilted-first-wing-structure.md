# First-unit tilted stationary caps: the remaining branch

Written structural lemmas, independently checked within the research session, October 10, 2026. These assume that the first charged-wing
curvature density is at most one. They support the subsequent
[folded-companion exclusion](gate1-tilted-first-wing-exclusion.md);
they do not establish the first-unit hypothesis for every remaining width.

## 1. Setting and the initial interval

Use the actual stationary cap and left-wing surrogate notation of the
[two-unit exclusion](gate1-tilted-unit-wing-exclusion.md), but assume only

\[
\frac12<C<\frac45,\quad 0<\epsilon<\frac12,\qquad
0\le u=f''+f\le1,
\]

with v=g''+g nonnegative and obeying the proved spatial arm/regularity
bounds. Put b=C+T. The EP source equalities remain
\(\nu_f=u\,dt\), \(\nu_g=v\,dt\).

Before \(\delta=\arctan(\epsilon/(2C))\), both wing densities vanish:
the actual central high-point quadrants have no positive niche in J.
There

\[
f=2C\cos t+e_R\sin t,\qquad
g=C\sin t+(1-\epsilon)\cos t.
\]

The general box-wall bound n(-C)<=H(C)<=2/5 and the positive EP pressure
law imply e_R>=2/5. Since tan(t)<=epsilon/(2C) for t<=delta,

\[
p(t)=1+(e_R-1+\epsilon)\cos t-3C\sin t
\ge e_R-\epsilon/2>3/20>0.                    \tag{FG1}
\]

Also q'=p-1>=-1 there, so

\[
q(\delta)\ge3C-1-\delta>1/2-\epsilon>0.
\]

For t>=delta the surrogate equals the actual companion. Hence the usual
arm bounds, kinematics, and same-sign spatial AR7 consequences apply:

\[
p\le1,\quad q\ge-1,\quad
u,v\le\kappa(q),\kappa(p)\ \text{respectively},
\quad\kappa(s)=\max\{|s|,(1+|s|)/2\},
\]
\[
p'=u-1-q,\qquad q'=v-1+p,
\]
\[
u=0,\ v\le1/2\ \text{on }\{p>0,q>0\},\qquad
v=0,\ u\le1/2\ \text{on }\{p<0,q<0\}.          \tag{FG2}
\]

Because u<=1, B_x is nondecreasing from 2C-1 to b and B_y is
nonincreasing from e_R to zero. Let beta be the first B_x=C crossing;
when T=0 one can take the last such crossing L. Every crossing obeys

\[
\beta\ge\arccos C                                \tag{FG3}
\]

by the actual source point (B_x+cos t,B_y+sin t) in the cap.

## 2. A first bad companion state must lie beyond the charged B tangencies

Consider the open set

\[
\mathcal E=\{t\in(\delta,L):p(t)<-1, q(t)>0\}.
\]

If it is nonempty, let tau=inf E. Before tau, v<=1 a.e. Indeed v=0
before delta; the arm bound gives v<=1 when p>=-1; and when p<-1,q<0,
FG2 gives v=0. The residual set {p<-1,q=0} has measure zero: on it the
kinematic bound gives q'<=-1, whereas an absolutely continuous function
has derivative zero a.e. on a level set. Thus D_x is nondecreasing from
-C throughout the past [0,tau].

The boundary of E at its first entry must satisfy

\[
p(\tau)=-1,\qquad q(\tau)>0.                     \tag{FG4}
\]

Entry through q=0 is impossible: whenever p<0, FG2 and the arm bound give
q'<=-1/2, with the stronger q'<=-1 when p<=-1. Consequently a crossing
with p negative can only leave the q-positive region.

Let (a_0,a_1) be the q-positive component containing the approach to tau.
Its initial p-value is positive: this follows from FG1 if the component
meets delta, and otherwise from the preceding one-sided crossing bound
at q=0. Since p'<=-q<0 on that component, it has a unique p-zero alpha
before tau. On (alpha,tau), p is negative, q is positive, and D_x has the
past monotonicity already proved.

Fix a compact interval of parameters with

\[
\alpha<t<\min(\tau,\beta),\quad -1<p(t)<0.
\]

The corner is positive and strictly inside J:

\[
c_y=B_y-p\cos t>0,\qquad
-C<D_x+q\cos t=c_x=B_x+p\sin t<C.                 \tag{FG5}
\]

For an earlier angle s<t, D_x(s)<=D_x(t)<c_x(t), so its second wall is
strictly below the current corner. For a later angle s>t, the global
first-unit monotonicity gives B_x(s)>=B_x(t)>c_x(t), so its first wall
is strictly below that corner. The actual high-point companion wall is
nonpositive on J and cannot change this positive-corner comparison.
Thus the full active angle is unique, with uniform strict localization
on compact subintervals. Finite positive graph vector flux therefore
gives at least q dt of first-source exposure there.

The B tangent at the same parameter is globally visible: the first wall
attains its global maximum there, and its companion has gap -p/cos t>0.
It lies in J before beta and contributes (1-u)dt of first-source
exposure wherever its height is positive. If a B plateau has height
zero, then u=1 a.e. on it and its claimed tangent contribution is zero.
The corner and B graph pieces are spatially disjoint on the compact
parameter interval: B_x increases whereas c_x'=p cos-q sin<0, and at
the left parameter endpoint B_x>c_x. Thus their source contributions
can be added. Compact exhaustion and \(\nu_f=u\,dt\) give

\[
u\ge q+(1-u),\qquad u\ge(1+q)/2.                 \tag{FG6}
\]

This argument requires only the already established finite vector-flux
passage on positive compact graph arcs. It neither identifies full
niche arclength nor assumes that future D tangencies are monotone.

Suppose tau<=beta. Then FG6 and u<=1 show q<=1 immediately after
alpha; continuity gives q(alpha)<=1. On (alpha,tau), v<=1 and p<0
make q strictly decrease. Therefore 0<q<=1, and the upper regularity
bound u<=kappa(q) gives

\[
u=(1+q)/2,\qquad v\le(1-p)/2.
\]

The absolutely continuous energy

\[
E=(p-1)^2+(q+1)^2
\]

satisfies E'<=0 there. At alpha it is at most 5, while at the first
bad entry FG4 gives

\[
E(\tau)=4+(q(\tau)+1)^2>5,
\]

a contradiction. Hence

\[
\boxed{\tau\ge\beta\ge\arccos C.}                \tag{FG7}
\]

Using open/closed crossing conventions can strengthen the first comparison
when the crossings are strict; the weak comparison is all that is used.

### Consequence when the top overhang vanishes

If T=0, every B tangent is in J, including any final constant B plateau.
The same proof applies over the whole quarter, with beta=L. Thus E is
empty. Outside E, FG2 and the arm bound give v<=1 a.e. as above. The
cap is therefore two-unit, and the audited two-unit exclusion contradicts
its positive tilt. In particular every remaining first-unit tilted
stationary cap must have

\[
\boxed{T>0.}                                      \tag{FG8}
\]

## 3. The actual positive niche is a single interval even if D folds

Set

\[
x_0=2C-1,\qquad x_1=1-2C,
\]

so x_1<x_0. For the surrogate second walls define

\[
F(x)=\sup_{0<t<L}S_t(x),\qquad
S_t(x)=\frac{g(t)-1+x\sin t}{\cos t}.
\]

For x<x_1 this supremum is finite, convex, and nondecreasing in x.
Its endpoint-angle limits are -epsilon at t=0 and minus infinity at
t=L. The left wing lies inside [-2C,-C] x [0,1-epsilon], so

\[
S_t(x)\le1-\epsilon-\sec t+(x+2C)\tan t
\le-\epsilon\quad\text{if }x\le-2C.
\]

At x=x_1 the t=L limit is e_L>0. Hence F has a zero
\(x_*\in(-2C,x_1)\). It is unique: any zero is attained at an interior
angle with strictly positive slope tan(t), so a second zero to its right
would instead be positive. The same observation gives strict negativity
on the whole interval x<x_* and strict positivity on (x_*,x_1].

The first-unit bound gives

\[
\frac{d}{dt}\frac{f(t)-1}{\cos t}
   =\frac{B_y(t)}{\cos^2t}\ge0.
\]

The intercept therefore rises from x_0 to b. Thus every first wall is
strictly positive at x<=x_1<x_0, while every first wall is nonpositive at
x>=b. If x_1<x<b, use angles close to L:

\[
R_t(x)=(b-x)(L-t)+o(L-t)>0,\qquad S_t(x)\longrightarrow+\infty.
\]

The high-point actual second wall is nonpositive for x<=C. It therefore
cannot create positive niche to the left of x_*, and it cannot remove any
positive surrogate niche. Combining these facts proves the full actual
positive-set identity

\[
\boxed{\{x:n_U(x)>0\}=(x_*,b).}                   \tag{FG9}
\]

This argument uses convexity of the scalar envelope F, with no
monotonicity assumption on D and no contact-chart restriction.

## 4. Exact projection balance in the folded case

On a compact K inside J and strictly left of x_*, the surrogate second
wall envelope is uniformly negative. The actual high-point wall is also
strictly negative once its angle is bounded away from zero. Consequently
all finite positive graph remaining over K must use source normals in
arbitrarily small neighborhoods of the endpoint directions. EP.22 bounds
their total exposure and horizontal projection by O(zeta)+o_n(1), exactly
as in the two-unit no-ghost proof. Uniform convergence on compact positive
subintervals of FG9 supplies the complementary lower bound.

Thus the selected finite positive projections converge to the actual
positive projected length in J:

\[
2C-T=\lim_n|\{x\in J_n:n_n(x)>0\}|
       =C-\max\{-C,x_*\}.
\]

Here the first equality is the unchanged EP moment
\(\int(u\sin t+v\cos t)dt=2C-T\), which needs no unit bound on v.
Equivalently,

\[
\boxed{T=(C+x_*)_+.}                              \tag{FG10}
\]

In view of FG8, every surviving first-unit tilted stationary cap has

\[
x_*>-C,\qquad n_U(-C)=0,\qquad T=C+x_*.
\]

## 5. A stronger left-boundary signed margin when C<=1/sqrt(2)

If a bad companion state occurs, FG7 and the actual left-wing source
point (X,Y)=D+nu give, for t>=tau,

\[
D_x(t)=X(t)+\sin t\ge-2C+\sin\tau
\ge-2C+\sqrt{1-C^2}\ge-C.
\]

Before tau the first-bad argument already gives D_x>=-C. If no bad state
occurs, v<=1 everywhere and the same conclusion follows directly. Thus
for C<=1/sqrt(2),

\[
D_x(t)\ge-C\qquad(0\le t\le L).
\]

The exact second-wall derivative now yields

\[
\partial_tS_t(-C)=\frac{-C-D_x(t)}{\cos^2t}\le0.
\]

Starting from its t=0 limit -epsilon gives the useful strict bound

\[
\boxed{F(-C)\le-\epsilon<0.}                      \tag{FG11}
\]

The companion curve may still fold to the right of -C. Neither FG10 nor
FG11 rules out such folds or pays their lost positive exposure. That is
the remaining issue for extending the two-unit energy identity.

## 6. The first bad entry has q at most one quarter

The actual source-box estimate from the two-unit proof did not use v<=1:

\[
p(t)<0\quad\text{whenever }B_x(t)\ge C.             \tag{FG12}
\]

It holds on the whole remaining range C<4/5, epsilon<1/2. Thus the
p-zero alpha preceding the first bad entry tau lies strictly before beta.
The corner remains positive and in J throughout (alpha,tau): its
x-coordinate strictly decreases from B_x(alpha)<C, while past D_x>=-C
and q>0 give the strict lower bound. There is no additional case in
which that corner enters J from the right after beta.

On (alpha,beta), the preceding proof gives E<=5 and 0<q<=1. On
(beta,tau), the positive corner is still globally unique: past D_x
monotonicity excludes earlier sources, and global B_x monotonicity
excludes later ones. Finite source flux therefore gives

\[
u\ge q.
\]

No equality u=q and no assertion about all other source exposure is
needed. Since -1<p<0 there, the upper arm bound is v<=(1-p)/2.
For

\[
K=q+(p-1)^2/4
\]

we obtain

\[
K'=v-1+p+\frac{p-1}{2}(u-1-q)
\le v+\frac{p-1}{2}\le0.                          \tag{FG13}
\]

At beta, E<=5 yields

\[
K(\beta)\le q(\beta)+\frac{5-(q(\beta)+1)^2}{4}
=1+\frac{q(\beta)}2-\frac{q(\beta)^2}{4}\le\frac54.
\]

Since p(tau)=-1, continuity and FG13 give

\[
\boxed{q(\tau)\le\frac14.}                        \tag{FG14}
\]

Finally FG12 keeps p<0 after beta. The arm bound then gives q'<=-1/2
there (and q'<=-1 where p<=-1). Consequently every later bad companion
state has q<=q(tau)<=1/4. This controls the amplitude at entry but does
not yet bound the score contribution of a folded or shadowed episode.
