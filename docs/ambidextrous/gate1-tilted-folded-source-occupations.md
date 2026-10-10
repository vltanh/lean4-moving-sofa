# Fractional finite-source occupations for the folded first-unit branch

Independent written audit of the source-occupation argument in the
[first-wing exclusion](gate1-tilted-first-wing-exclusion.md), October 10, 2026.
The energy algebra is checked separately below. This note supplies the
measure details without assuming a finite contact chart or ordinary
niche-arclength convergence.

## 1. Geometric inputs used here

The preceding first-unit arguments give the actual ordered signs

\[
p,q>0\quad(0,\alpha),\qquad
p<0<q\quad(\alpha,\eta),\qquad
p,q<0\quad(\eta,L),
\]

with \(\alpha<\beta<\tau<\eta\). The first unit bound makes B_x
nondecreasing and B_y nonincreasing to zero. Its positive tangencies
inside J are B on (alpha,beta). The entire core corner is positive and
strictly inside J, and

\[
c_x'=p\cos t-q\sin t<0.
\]

The companion D may fold and cross the floor more than once. Every positive D point lies in J: its second wall height is positive only at x>L0(t)>=x_zero>-C, while D_x<=1-C<C. The argument below needs only the stated positive-projection identity, not a unique floor crossing. Before tau, the whole past D_x is
nondecreasing, so every strict core corner before tau is the unique
active full quadrant at its abscissa.

The actual niche is positive precisely on (x_zero,b), with b=C+T and
T>0. Its positive projection inside J is (x_zero,C). The finite no-ghost
argument proves convergence of those positive projections in measure,
and EP identifies the angle marginals with u dt and v dt.

## 2. Retain source angle and abscissa jointly

For each finite selected niche, place each positive first-source edge's
arclength measure at its source parameter t and its actual graph
abscissa x. Denote this nonnegative measure by mu_{n,f}; define
mu_{n,g} similarly. Their angle marginals are the usual finite source
measures. Their two exact graph-vector identities are

\[
\pi_{x\#}(\sin t\,\mu_{n,f}+\cos t\,\mu_{n,g})
   =\mathbf1_{\{n_n>0\}\cap J_n}\,dx,
\]
\[
\pi_{x\#}(-\cos t\,\mu_{n,f}+\sin t\,\mu_{n,g})
   =D(n_n|_{J_n})
\]

on the window interior. The second statement is distributional; the
zero-height pieces contribute zero derivative. Endpoint terms can instead
be retained explicitly and cancel under compact interior tests.

Take a joint weak subsequence on the compact angle-position rectangle.
The bounded angle densities exclude endpoint-angle atoms. Uniform roof
convergence passes the vertical distributional identity, while the
proved positive-projection convergence passes the first identity. Thus

\[
\pi_{x\#}(\sin t\,\mu_f+\cos t\,\mu_g)
   =\mathbf1_{(x_{\rm zero},C)}\,dx,                 \tag{FO1}
\]
\[
\pi_{x\#}(-\cos t\,\mu_f+\sin t\,\mu_g)
   =n'(x)\,dx                                      \tag{FO2}
\]

locally on the positive interval. There the roof is locally Lipschitz:
on a compact interval where n is bounded below by a positive number,
the endpoint-angle walls have heights tending to zero or below, so all
active angles lie in a common compact subinterval of (0,L).

Every limiting source point lies on its corresponding limiting source
wall and attains the actual full niche. FO1 shows that neither a floor
point nor a spatial singleton can carry extra interior-angle source mass.
The angle marginals remain

\[
\pi_{t\#}\mu_f=u\,dt,\qquad \pi_{t\#}\mu_g=v\,dt. \tag{FO3}
\]

All subsequent classifications are made outside null sets for these
measures. Exceptional support derivatives have zero angle marginal, and
exceptional graph derivatives have zero weighted x marginal.

## 3. Classification of an active parameter

At a regular active parameter t, if its first wall is strictly below its
companion, it must be stationary under a change of t. The exact wall
derivative gives x=B_x(t), and its height is B_y(t). This requires p<0;
otherwise its companion does not have the requisite slack. Similarly a
sole second-wall contribution is at D(t), with q>0. If both walls are
active, the point is c(t).

There are no corner contributions in (++): at the corner the two angle
derivatives are p/sin(t)>0 and q/cos(t)>0, so a slightly larger angle
raises both walls. In (--), a slightly smaller angle raises both walls.
Hence corner contributions occur only on the core.

A genuine D tangent must satisfy v<=1. At a regular tangent its second
angular derivative is

\[
\partial_t^2 S_t(D_x(t))=-(1-v(t))/\cos t.
\]

If v>1 this is a strict local minimum, while the companion first wall has
the strict gap q/sin(t)>0. Such a parameter cannot maximize the full niche.
Therefore D contributions vanish where v>1. They also vanish where
D_y<0 or q<0. A D_y=0 point cannot carry residual positive exposure by
FO1.

This exhausts every regular positive limiting source point. No global
monotonicity of D was used.

## 4. The B contribution is full

At a B tangent with p<0, the first wall is its global angular maximum,
and the companion has strict slack. Thus the actual niche equals the B
graph there. On (alpha,beta) it lies inside J and has negative slope.
The corner abscissae are at most B_x(alpha), while this B graph runs
from that abscissa to C. Thus no positive-length core corner can compete
with a B segment. A competing D tangent would have positive slope and
cannot agree with the negative B slope on a positive-measure graph set.

Consequently FO1 assigns the full graph projection to its first source.
The resulting angle density is

\[
(1-u)\mathbf1_{(\alpha,\beta)}\,dt.                \tag{FO4}
\]

A B plateau has B_x'=B_y'=0, and therefore zero spatial projection;
FO1 excludes any additional mass there. The B graph outside J contributes
nothing to these window source measures.

## 5. A common fractional occupation at a corner

On the core, c_x is strictly decreasing, so there is at most one corner
parameter t at a prescribed abscissa. On the measurable contact set

\[
E_c=\{t:n(c_x(t))=c_y(t)\},
\]

the chain rule and the derivative-zero property on level sets give

\[
n'(c_x(t))=\frac{p\sin t+q\cos t}{p\cos t-q\sin t}
\quad\text{a.e. on }E_c.                           \tag{FO5}
\]

Work on a compact core interval; c_x is then bi-Lipschitz, so both the
angle and spatial null sets in this assertion are harmless. Compact
exhaustion gives the whole core.

At such an abscissa, a competing non-corner source must be a D tangent.
At a regular contact of D with the actual graph, the same level-set chain
rule gives n'(D_x(t))=tan(t) whenever D_x' is nonzero. Points with
D_x'=0 have zero projection. Therefore any D contribution to this same
abscissa is parallel to the actual graph direction (1,n'). Its angle
is determined uniquely by n'=tan(t), except on a null set.

Disintegrate FO1--FO2 at the abscissa. Subtract this parallel D flux.
Let A_f and A_g denote the remaining first/second corner-source arclength
densities with respect to dx. Their directions are -nu_t and mu_t, so

\[
(-\cos t-n'\sin t)A_f+(\sin t-n'\cos t)A_g=0.
\]

Insert FO5. Since p<0<q, this gives

\[
A_g=(-p/q)A_f.
\]

The nonnegative horizontal share assigned to this pair is at most one
by FO1. Since the increasing-x corner displacement is -c'(t)dt,
there is a measurable chi(t) in [0,1] such that the two angle densities
are exactly

\[
q\chi\,dt,\qquad -p\chi\,dt.                     \tag{FO6}
\]

The same chi appears in both sources; this is forced by the vector
equations, rather than chosen independently. If no other parameter
attains the corner, FO1 makes chi=1. In particular chi=1 throughout
(alpha,tau), by the established past-D/global-B strict localization.

## 6. The residual D occupation

At a visible regular D tangent, v<=1 and

\[
D_x'=(1-v)\cos t,\qquad D_y'=(1-v)\sin t.
\]

The tangent's horizontal share of FO1 is some measurable number in
[0,1]. The area formula for the absolutely continuous map D_x pulls
this share back to angle. Different visible D parameters at the same
differentiability point would have different tan(t) slopes, so there is
at most one such parameter for almost every abscissa. Its source
arclength density is consequently

\[
(1-v)d\,dt\qquad\text{for a measurable }0\le d\le1. \tag{FO7}
\]

One may set d=0 where v>=1 and where the D contribution is absent.
When v=1 the factor is zero regardless of the choice. In particular d=0
where v>1, where D_y<0, and where q<0. The formula permits a fractional
share when an earlier D tangent coincides with a later corner curve.

FO4, FO6 and FO7 partition all the joint source mass classified in
Section 3. They are not merely independently postulated lower bounds.
No nonnegative residual can survive, because FO1 assigns exactly the
actual positive graph projection and the endpoint-angle marginals have
no atoms. Using FO3 gives the exact source equations

\[
(++):\quad u=0,\quad v=(1-v)d,
\]
\[
\text{core}:\quad
u=(1-u)b+q\chi,\qquad v=(1-v)d-p\chi,
\quad b=\mathbf1_{\{t<\beta\}},
\]
\[
(--):\quad u=v=0.                                 \tag{FO8}
\]

The final first-source zero uses beta<eta, so every late B tangent is
outside J. The final second-source zero also follows from AR7.

## 7. Independent algebra check

On the core, FO8 is equivalent to

\[
u=\frac{b+q\chi}{1+b},\qquad
v=\frac{d-p\chi}{1+d}.
\]

After beta, b=0. The exact identities checked directly are

\[
w':=(q-p)'=(1-\chi)\left[p+q+\frac d{1+d}\right]
              +\frac{\chi d(1+p)}{1+d},
\]
\[
H'-(1-p)(1-u)+(q+1)(1-v)(1-d)
       =(1-\chi)(p+q),
\quad H=(p-1)^2+(q+1)^2.                           \tag{FO9}
\]

On the bad interval p<=-1 and q<=1/4, both terms in the first expression
are nonpositive. Hence w<=w(tau)<=5/4. It follows that v<=5/4 globally,
and on {v>1}, where d=0,

\[
v-1\le1/4-q\le(1-q\chi)/4=(1-u)/4.
\]

The energy residual in FO9 is nonpositive after tau; before tau chi=1.
Thus the integrated defect estimate and the bound
\(6CT\le97T/48<3T\) in the general first-wing exclusion are valid with these
fractional occupations, after retaining that theorem's favorable first-floor displacement term. The remaining hypotheses were checked separately
in the first-unit structural addendum and the floor-crossing calculation.

## Verdict

The occupation passage and its energy use are sound under the proved
ordered-sign, positive-projection and first-unit hypotheses. Together with the first-floor argument, it excludes every first-unit tilted maximizer in 1/2<C<4/5. It does not supply the first-unit hypothesis for every width.
