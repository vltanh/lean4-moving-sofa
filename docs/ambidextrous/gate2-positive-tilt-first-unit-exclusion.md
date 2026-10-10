# Gate 2: a proper terminal angle excludes a positive tilted first-unit maximizer

Written proof, independently checked within the research session,
October 10, 2026. This is a conditional sharp reduction for the actual
partial spatial objective.
It does not assume a common occupation for angle and support variations,
a terminal first-moment law, or a full-turn completion.

The fixed-angle inputs are [PD](gate2-partial-cap-domain-reductions.md)
and [PS](gate2-partial-endpoint-source-and-green.md). The exact one-sided
angle derivative is [TV1–TV3](gate2-terminal-angle-variations.md).
The first-unit hypothesis below is a remaining curvature theorem, not a
consequence asserted by this note.

## 1. Statement and normalization

Suppose the joint global supremum of the partial score exceeds the
full-turn sharp value. Choose a joint maximizer with the **largest**
terminal angle among all joint maximizers, and perform PD's height,
middle-chord, top, and used-support saturation reductions at that angle.
These operations preserve maximality and the angle. The angle remains
largest. Compact attainment makes this selection legitimate; Gate 1
ensures its angle is less than pi/2.

Consider its positive middle-tilt branch, normalized as

\[
I=[-2C,2C],\quad J=[-C,C],\quad
A(-C)=1-h,\quad A(C)=1,\quad 0<h<1/2.
\tag{PU.1}
\]

The strict upper bound on h follows already from PS's one-angle
low-height exclusion. Assume additionally

\[
C>1/2,\qquad 3\pi/8\le a< L:=\pi/2.
\tag{PU.2}
\]

Write the top face as [C,b] at height one and put T=b-C. Set

\[
c=\cos a,\quad s=\sin a,\quad
k=\frac{1-s}{c}=\tan((L-a)/2),\quad w=sk=c-k.
\tag{PU.3}
\]

In particular

\[
c<5/13<2/5,\quad s>12/13,\quad
0<w<c/2,\quad 0<k<c.
\tag{PU.4}
\]

The exact comparison at 3pi/8 follows from
(238/169)^2<2: it gives cos(3pi/8)<5/13 and hence
sin(3pi/8)>12/13. Also w/c=s/(1+s)<1/2.

Let f be the actual first support and g the **left-wing support**:

\[
f(t)=h_U(\cos t,\sin t),\qquad
g(t)=\max_{-2C\le x\le-C}[-x\sin t+A(x)\cos t].
\]

The actual second support is the maximum of g and the high point
(C,1). The inner wall of that high point is nonpositive on J. Thus
replacing the actual second support by g does not change the positive
partial barrier on J. This removes the uncharged central-facet atom
from the support parameterization.

Put u=f''+f and v=g''+g on the open used interval (0,a). Both are
bounded measurable nonnegative functions by PS, away from the removed
central atom. The theorem to be proved is:

> **PU1.** Under PU.1–PU.2, this selected positive-tilt joint
> maximizer cannot satisfy u<=1 almost everywhere on (0,a).

The lower curvature hypothesis u>=0 is part of convexity. No upper
bound on C and no assumption v<=1 are made.

## 2. Exact support data and the local partial-source laws

Write e_R=A(2C) and e_L=A(-2C). PS gives positive endpoint pressures
and equality of the actual charged wing measure with the limiting
finite positive-source measure. Saturation and pinning give

\[
\begin{array}{llll}
 f(0)=2C,&f'(0)=e_R,&f(L)=1,&f'(L)=-b,\\
 g(0)=1-h,&g'(0)=C,&g(L)=2C,&g'(L)=-e_L.
\end{array}
\tag{PU.5}
\]

There is no curvature on the unused open source arcs. Consequently

\[
f(t)=b\cos t+\sin t,\qquad
g(t)=2C\sin t+e_L\cos t\quad(a<t<L).
\tag{PU.6}
\]

The first source may have a facet at a. Its upper/left endpoint is
(b,1); write its lower/right endpoint as

\[
(b+m,1-mc/s),\qquad m\ge0.
\tag{PU.7}
\]

This facet is entirely exterior charged. Its arclength is m/s.
PS forbids a companion terminal atom, so g and g' are continuous at a.

Define

\[
p=f'-g+1,\quad q=g'+f-1,
\quad p'=u-1-q,\quad q'=v-1+p.
\tag{PU.8}
\]

Here q is a contact velocity, not the spatial barrier. Denote that
barrier by N. Define the corner and the two tangency curves by

\[
z=(f-1)\mu_t+(g-1)\nu_t,\quad
B=z+p\nu_t,\quad D=z-q\mu_t,
\]
\[
z'=p\mu_t+q\nu_t,\qquad
B'=(u-1)\nu_t,\qquad D'=(1-v)\mu_t.
\tag{PU.9}
\]

In particular B(0)=(2C-1,e_R), D(0)=(-C,-h), and
D(L)=(1-2C,e_L). The inner walls are

\[
R_t(x)=\frac{f(t)-1-x\cos t}{\sin t},\qquad
S_t(x)=\frac{g(t)-1+x\sin t}{\cos t}.
\]

Their parameter derivatives have the useful exact form

\[
\partial_tR_t(x)=\frac{x-B_x(t)}{\sin^2t},\qquad
\partial_tS_t(x)=\frac{x-D_x(t)}{\cos^2t}.
\tag{PU.10}
\]

The following local laws apply on compact subintervals of (d,a),
where d is the central switch defined below and the surrogate agrees
with the actual second support. The surrogate arm bound p<=1 is not
asserted before d:

\[
p\le1,\quad q\ge-1,\qquad
u\le\kappa(q),\quad v\le\kappa(p),\quad
\kappa(r)=\max\{|r|,(1+|r|)/2\},
\tag{PU.11}
\]
\[
u=0,\ v\le1/2\quad(p>0,q>0),\qquad
v=0,\ u\le1/2\quad(p<0,q<0).
\tag{PU.12}
\]

These are direct partial-source consequences, as follows. The arm
inequalities use only that each support point of one normal lies
below the supporting line of the perpendicular normal. For the
curvature inequalities, use PS's selected polygons and the WR.1
four-line neighbor calculation on any compact subinterval of (0,a).
Its circumscribed-neighbor facet length is at least the actual facet
length, so replacing it by the latter only enlarges the exposure
upper bound. Combine the bound with PS.11 and pass to the limit exactly
as in WR.5. The extra outgoing wall can only hide the exposed pieces;
it cannot invalidate any neighbor upper bound. For PU.12 use the
same-sign finite neighboring-quadrant calculation AR7: in the ++
region the first source is covered and the second exposed length is
at most (2tan(mesh/2)-facet_length)_+. PS.11 then gives u=0 and
v<=1/2. Exchanging the two local line families proves the -- statement.
This is a local geometric exchange, not reflection invariance of the
partial objective. Compact exhaustion supplies the almost-everywhere
statements, retaining all finite penalty errors until their sums vanish.

The central switch is

\[
d=\arctan(h/(2C))<\arctan(1/2)<a.
\]

Before d the actual second wall is nonpositive on J, so its used
source and the paired first source have no exposure. PS implies
u=v=0 there, with g the low endpoint harmonic support. After d,
g is the actual second support and PU.11–PU.12 apply. These conclusions
do not introduce an atom into the surrogate g.

The pressure law gives a particularly useful bound without a left
niche box estimate. Let n_- and n_+ be N at the two middle endpoints.
Concavity gives e_L<=1-3h/2, while

\[
e_L=(2-3h+3n_--n_+)/4,
\quad e_R=(2+h+3n_+-n_-)/4.
\]

Therefore

\[
\boxed{e_R\ge1/3+h/2+(2/3)n_+\ge1/3.}
\tag{PU.13}
\]

The initial state is p(0)=e_R+h and q(0)=3C-1. Both remain positive
through d. For example, before d, with H=e_R-1+h,

\[
p(t)=1+H\cos t-3C\sin t,\quad
q(t)=3C\cos t+H\sin t-1.
\]

Since tan t<=h/(2C), p(t)>=min(1,e_R-h/2)>=1/3.
Also H>=-2/3, cos t>=2/sqrt(5), sin t<=1/sqrt(5), and C>1/2,
so q(t)>7/(3sqrt(5))-1>0. All later sign-component arguments therefore
start beyond the removed atom with legitimate partial-source laws.

## 3. A short terminal facet, using only a one-sided angle variation

Let

\[
B_+=(b-c,1-s),\quad B_-=B_++(m,-mc/s),\quad
r_0=b-k.
\tag{PU.14}
\]

Here B_+ and B_- are the shifted endpoints of the terminal facet,
and R_a(x)>0 exactly for x<r_0. Write z_a for the inner corner at a.
The harmonic terminal traces give

\[
(z_a)_x-(B_+)_x
=s[1-(b+2C)s+(1-e_L)c].
\]

By PU.4 and b>=C,

\[
(b+2C)s+(e_L-1)c\ge3Cs-c
>\tfrac32\tfrac{12}{13}-\tfrac5{13}=1.
\tag{PU.15}
\]

Thus (z_a)_x<(B_+)_x and p(a+)<0. This fact does not use u<=1.

Suppose m>w. Then (B_-)_x>r_0. At every x in the open interval
((z_a)_x,(B_-)_x), S_a(x)>R_a(x), while the left parameter derivative
of R at a is negative. A sufficiently close earlier angle therefore
has both wall heights strictly above R_a(x). Hence its historical
partial niche strictly masks the terminal wall there.

Let E={R_a>n_a} and H={R_a=n_a}, with n_a including the floor.
All positive terminal exposure or ties outside a null set now lie
to the left of (z_a)_x<(B_+)_x: the remaining possible region
x>=(B_-)_x has R_a<0. TV3 therefore reads

\[
\int_E(x-(B_+)_x)\,dx\ge0,
\]

whose integrand is strictly negative. Consequently E has measure zero.
Continuity makes E empty in the interior of J, so n_a>=R_a on J.

In fact the angle can now be increased without changing the barrier.
Choose zeta strictly between (z_a)_x and (B_+)_x. Below zeta, all
nearby harmonic tail walls R_t, t>a, decrease with t, by PU.10.
Above zeta, the positive portion of those nearby walls ends at
r_0(t)=b-tan((L-t)/2). For sufficiently small epsilon this endpoint
remains strictly below (B_-)_x. On the resulting compact interval
[zeta,r_0(a+epsilon)], the old history has a uniformly strict gap
above R_a. Uniform continuity pays the small increase of every
R_t for a<=t<=a+epsilon. Beyond r_0(a+epsilon) those walls are
nonpositive. Thus all new first walls lie below n_a, and each new
two-wall minimum does as well:

\[
N_{a+\epsilon}=N_a\quad\hbox{on }J.
\]

This contradicts the choice of the largest maximizing angle. We have
proved, without joint offset/rotation stationarity,

\[
\boxed{m\le w.}
\tag{PU.16}
\]

There is also a one-sided projection estimate. The total horizontal
projection of the finite positive-source graph is its positive-set
length in J. On every compact interval where N>0, uniform convergence
makes the finite barriers positive. PS and lower semicontinuity give

\[
2C-T=\int\sin\theta\,d\nu
\ge |\{x\in J:N(x)>0\}|
\ge |J\cap(-\infty,r_0)|.
\]

If T>=k, the final term is 2C, which is impossible. Thus T<k,
and r_0=C+T-k lies inside J because k<c<2/5<C. The same inequality
then becomes 2C-T>=2C+T-k. Therefore

\[
\boxed{0\le T\le k/2.}
\tag{PU.17}
\]

This argument allows arbitrary limiting zero-height source pieces.
It does not assume convergence of niche zero sets.

## 4. A first-unit wing forces the companion wing to be unit

Assume now u<=1 on (0,a). PU.14–PU.17 give

\[
(B_-)_x=C+T+m-c\le C+T-k<C,
\]
\[
(B_-)_y=1-s-mc/s\ge0.
\]

By PU.9, B_x is nondecreasing and B_y is nonincreasing on the whole
used interval. Consequently

\[
0<2C-1\le B_x(t)<C,\qquad B_y(t)\ge0.
\tag{PU.18}
\]

The entire B curve also lies above the outgoing line. Indeed, for

\[
F_B(t)=B(t)\cdot\mu_a-(f(a)-1),
\]

one has F_B(a-)=0 and
F_B'(t)=(u(t)-1)sin(a-t)<=0. Hence F_B>=0.

By PU.11–PU.12, v>1 is possible only where p<-1 and q>0. If this
open bad region is entered, choose its first boundary time tau<a:
p(tau)=-1 and q(tau)>0. Entry through q=0 with p<0 is impossible,
because PU.11 gives q'<=-1/2 throughout p<0. Before tau, v<=1, so
D_x is nondecreasing from -C. The positive-q component reaching
tau has a preceding p-zero at t_0. On the core
interval from t_0 toward tau, p<0,q>0, and

\[
z_x=D_x+q\cos t>-C,
\quad z_x=B_x+p\sin t<B_x<C,
\quad z_y=B_y-p\cos t>0.
\tag{PU.19}
\]

Moreover F_z=F_B-p sin(a-t)>0, so the corner is strictly above the
outgoing line. The corner is globally visible: for every earlier
r<t, D_x(r)<=D_x(t)<z_x(t), so S_r(z_x(t))<S_t(z_x(t)); for every
later r>t up to a, B_x(r)>=B_x(t)>z_x(t), so
R_r(z_x(t))<R_t(z_x(t)). At the same angle the two wall heights
agree. These inequalities also give strict remote-angle gaps on
compact strict core intervals.

The B tangency is globally visible whenever p<0 and it has positive
height: monotonic B_x makes R_t its global first-wall maximum,
the companion wall is above it, and F_B>=0. A parameter interval
where B is at height zero has u=1 almost everywhere and contributes
zero tangency arclength.

The finite vector-flux limit therefore charges the first source by
at least its B arclength 1-u and its corner coefficient q. Explicitly,
the increasing-x tangent to the reversed corner is

\[
-z'=q(-\nu_t)+(-p)\mu_t,
\]

so its two nonnegative source coefficients are q and -p. Localization
by the preceding strict gaps and the two vector components proves
this at bounded measurable densities, exactly as in the Gate 1 local
positive-corner argument. Since the first source equals u by PS,

\[
u\ge1-u+q.
\tag{PU.20}
\]

In particular q<=1 on this core, including the trace at t_0. While
-1<=p<0, PU.11 gives u<=(1+q)/2 and v<=(1-p)/2, so PU.20 forces
u=(1+q)/2. Thus

\[
\frac d{dt}\big[(1-p)^2+(1+q)^2\big]
=2[(1+q)v-(1-p)u]\le0.
\]

The energy is at most 5 at p=0, q<=1. It would exceed 5 at
p=-1,q>0. This rules out the first bad entry. Therefore

\[
\boxed{0\le v\le1\quad\hbox{on }(0,a).}
\tag{PU.21}
\]

There is no companion curvature after a, and no companion atom at a.
Thus D_x is now nondecreasing all the way to L. This proof used
D_x>=-C only **before** the first bad entry; it did not assume
confinement after a curvature fold.

## 5. Ordered contact geometry and the terminal source intervals

Now both wing densities are unit. From PU.18 and D(L),

\[
B_x(t)-D_x(t)\ge (2C-1)-(1-2C)=4C-2>0.
\tag{PU.22}
\]

Since B_x-D_x=q cos t-p sin t, the sign regime p>0,q<0 is
impossible. On q>0 the first variable p strictly decreases by PU.11;
on p<0 the second variable q strictly decreases. Initially both are
positive, whereas PU.15 gives p(a-)<0. Thus p has a unique zero
t_0 in (0,a). Afterwards p<0, and q either stays nonnegative until a
or has one later zero eta.

For every x>=(B_-)_x, all R_t(x) increase up to their terminal
value, by PU.10. Since (B_-)_x<=r_0,

\[
N(x)>0\iff x<r_0\quad(x\in J),
\tag{PU.23}
\]

apart from the single zero endpoint r_0. The forward implication for
x>=r_0 uses R_t(x)<=R_a(x)<=0 at every visited angle; the reverse
implication uses the whole outgoing wall itself.

There is no hidden limiting source over a compact interval to the
right of r_0. All its limiting first walls are uniformly negative:
away from t=0 this follows from R_t<=R_a<0, while near zero it
follows from x>r_0>=(B_-)_x>=2C-1 and the first-axis support gap.
The same inequalities persist for the finite selections. The finite
horizontal flux measures are bounded by dx, so a single boundary
abscissa cannot retain residual mass. On the positive interval the
finite barriers are eventually positive on compacts. Accordingly
the limiting total horizontal source flux is exactly dx on
[-C,r_0] and zero elsewhere. This observation justifies complete
source accounting below, including constant-parameter pieces; it
also gives T=k/2 as an optional consequence, which the subsequent
estimates do not need.

For D define

\[
F_D(t)=D(t)\cdot\mu_a-(f(a)-1),\qquad
F_D'(t)=(1-v(t))\cos(a-t)\ge0,
\]
\[
F_D(0)=c(k-2C-T)-hs<0,\qquad F_D(a-)=-q(a-).
\tag{PU.24}
\]

First suppose q(a-)>=0. Then every D tangency is on or below the
outgoing line, so there is no D tangent source of positive projected
length. A level interval F_D=0 has v=1 and maps to a single D point,
which has zero horizontal source measure. In the initial ++ phase
there is no other companion source: the corner is strictly locally
hidden, since both wall values increase with angle there. On the
core p<0,q>0, the globally visible B and corner give

\[
u=(1+q)/2,\qquad v=-p.
\tag{PU.25}
\]

These exact source equations can also be obtained by first proving
the local lower bounds on compact strict arcs and then using the
complete horizontal source accounting just proved. No zero-height
arclength convergence is assumed. The only possible regular
positive-source limits are B, D, or the corner: at an active
interior parameter the first-order condition for max_t min(R_t,S_t)
gives precisely these three cases. Flat B or D parameter intervals
map to one abscissa and cannot carry remaining projected flux.

Let Q=q(t_0)<=1, and let r=t-t_0. Equations PU.25 give

\[
q=Q-r,\qquad v=-p=(1+Q)r/2-r^2/4.
\]

The terminal assumption gives 0<=r<=Q<=1. The exact left-wing
horizontal moment from PU.5–PU.6 is C=int_0^a v(t)cos t dt, since
there is no companion terminal atom. Hence

\[
C\le\int_0^1(r-r^2/4)\,dr=5/12,
\]

contradicting C>1/2. We have proved q(a-)<0. Let eta in (t_0,a)
be its unique zero. At eta, D=z and the corner is strictly above
the outgoing line, so F_D(eta)>0. Thus F_D has a zero at some

\[
0<\gamma<\eta.
\]

Any zero plateau has v=1 and constant D, so the point D(gamma)
is independent of the choice within the plateau.

The positive spatial barrier now consists of the following pieces,
listed in increasing horizontal order:

1. the outgoing line from -C to D_x(gamma);
2. the D tangency from gamma to eta;
3. the reversed corner from eta to t_0;
4. the B tangency from t_0 to a-;
5. the terminal endpoint ray from (B_-)_x to r_0;
6. the zero floor from r_0 to C.

Here D_x(gamma)>=-C and D_x(eta)<=1-2C<0, while B_x(t_0)>0
and B_x(a-)<C. The corner abscissa is strictly decreasing between
the two tangency endpoints, so every listed positive arc is in J.
The tangency maxima follow directly from monotonic B_x and D_x.
The corner is the unique active parameter by the earlier-S/later-R
comparison used in Section 4. The outgoing line cuts D exactly at
gamma. It lies strictly below the core, and below the B arc except
at its terminal endpoint; on the final -- phase u<=1/2 ensures that
F_B(t)>0 for every t<a. This proves the listed spatial order for
absolutely continuous support derivatives, allowing tangency plateaux.

Put

\[
e=D_x(\gamma)+C\ge0.
\tag{PU.26}
\]

The first interval is strict outgoing-strip exposure except at its
endpoint. Indeed, for -C<x<D_x(gamma), monotonic D_x makes the
global S maximum occur at a tangency before gamma (or its constant
plateau). There F_D<0, so this maximum is strictly below R_a(x).
At x=-C, every S wall is at most its t=0 limit -h, again strictly
below the positive outgoing wall. This proves strict exposure on
the entire left interval up to its right endpoint, without assigning
terminal-only ties there. The fifth interval has length

\[
r_0-(B_-)_x=w-m.
\]

On its interior, every earlier first wall is strictly below R_a:
x>(B_-)_x>=B_x(t) makes R_t(x) strictly increasing for all t<a.
Thus it is a positive terminal-only historical tie, H_new in TV1L.

The fixed-angle terminal occupation is exactly one on both intervals.
For the fifth interval this also has a short direct finite-source
proof: on any compact subinterval H_0, all angles t<=a-epsilon
have a uniform strict historical gap. Every finite graph piece
over H_0 is therefore terminal or has its source angle within
epsilon of a. PS.13 bounds the total nonterminal source arclength
in that neighborhood by O(epsilon). First pass to the selected
limit, then let epsilon decrease to zero. The occupation is one
almost everywhere on H_0, and exhaustion proves the claim. There
are no positive-length older-angle tie intervals in the listed
graph. PS's exact terminal atom mass consequently gives

\[
\boxed{m=e+(w-m),\qquad m=(e+w)/2,\qquad 0\le e\le w.}
\tag{PU.27}
\]

This uses only fixed-angle mass, including terminal-only ties. It is
not a terminal first-moment equality.

## 6. The one-sided angle inequality makes the left interval quadratic

Apply TV3 to the explicit terminal intervals. The first, strict strip
interval contributes

\[
-e(2C+T-c)+e^2/2.
\]

The terminal-only right interval lies between B_++m and B_++w;
its positive tie contribution is (w^2-m^2)/2. Hence

\[
-e(2C+T-c)+e^2/2+(w^2-m^2)/2\ge0.
\tag{PU.28}
\]

Substitute m=(e+w)/2 and use 0<=e<=w. If A=2C+T-c, the
resulting inequality is

\[
3e^2-(8A+2w)e+3w^2\ge0,
\]

so (8A-w)e<=3w^2. Since T>=0 and w<c/2,

\[
\boxed{e\le\frac{3w^2}{8(2C+T-c)-w}
<\frac{3c^2}{64C-34c}.}
\tag{PU.29}
\]

All denominators are positive: C>1/2 and c<2/5 give
64C-34c>92/5. Dividing the denominator by C also gives
64-34c/C>184/5. Therefore

\[
\boxed{e<\frac{c^2}{6}<\frac2{75},\qquad
Ce<\frac{c^2}{12}.}
\tag{PU.30}
\]

The exact constants follow from 15/92<1/6 and 15/184<1/12.

## 7. The initial curvature cannot produce the required crossing height

If e=0, then gamma maps to D_x=-C. Monotonic D_x and v<=1 imply
D remains equal to D(0)=(-C,-h) up to that point, contradicting
its position on the positive outgoing line. Thus e>0. Set

\[
t_* =\arcsin(2e)\le4e<8/75<a.
\tag{PU.31}
\]

On the initial ++ phase, u=0 and v<=1/2, including the zero
densities before the central switch. While p,q>0,

\[
-1\le q'\le1/2,
\quad q(t)\le3C-1+t/2,
\quad p(t)\ge p(0)-3Ct-t^2/4.
\tag{PU.32}
\]

For the upper q' bound, after the switch use p<=1; before it use
v=0 and p<=p(0)<=e_R+h<3/2. The lower bound uses p>0 and v>=0.
For t<=t_*<=4e, PU.13 and PU.30 give

\[
p(t)>1/3-12Ce-4e^2
>1/3-c^2-c^4/9>1/6.
\tag{PU.33}
\]

The last rational comparison is
4/25+16/5625=916/5625<1/6. Also
q(t)>1/2-8/75>0. A first-exit argument proves that the ++ phase
indeed lasts through t_*, so v<=1/2 on that whole interval.

Now

\[
D_x(t_*)+C=\int_0^{t_*}(1-v(t))\cos t\,dt
\ge\tfrac12\sin t_*=e.
\]

Since D_x(gamma)+C=e and D_x is nondecreasing, its line-crossing
point occurs by t_* (a plateau has the same D point). Integrating
g''+g=v<=1/2 from its initial data gives, for t<=t_*,

\[
g(t)\le(1-h)\cos t+C\sin t+\tfrac12(1-\cos t).
\]

At x=-C+e this yields

\[
S_t(-C+e)\le-h+\tfrac12-\tfrac12\sec t+e\tan t.
\]

The all-angle maximum of the final two terms is
-sqrt(1/4-e^2). Evaluating at the D tangency therefore gives

\[
D_y(\gamma)\le-h+\tfrac12-\sqrt{\tfrac14-e^2}
\le2e^2.
\tag{PU.34}
\]

On the other hand D(gamma) lies on the outgoing line, so

\[
D_y(\gamma)=R_a(-C+e)
=\frac c s(2C+T-k-e)>c/2.
\tag{PU.35}
\]

Indeed, 2C>1, T>=0, k<c<2/5, and e<2/75 make the bracket
larger than 1-2/5-2/75=43/75>1/2. But PU.30 gives

\[
2e^2<c^4/18<c/2
\]

because 0<c<2/5. Equations PU.34–PU.35 contradict each other.
This proves PU1.

## 8. Exact scope

The proved mechanism excludes every positive tilted selected
first-unit maximizer in C>1/2 and a>=3pi/8. It has no small-angle
deficit approximation, no assumed symmetry, no full-turn completion,
and no terminal first spatial moment. The only terminal stationarity
input is the accepted one-sided right derivative TV3, with its positive
tie term retained.

The remaining external task for applying this theorem is to establish
the width/angle prerequisites and u<=1, or to exclude the complementary
first-curvature-excess branch by an additional argument. Horizontal
middle roofs have a second possible top overhang and are not covered
by this positive-tilt normalization. Negative tilt requires its own
outgoing-strip analysis. Accordingly this note alone does not pass
Gate 2.
