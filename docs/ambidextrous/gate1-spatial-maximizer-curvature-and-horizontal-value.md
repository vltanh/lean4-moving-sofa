# Gate 1: source curvature and the horizontal value branch

**October 10, 2026. Written proof, independently checked within this research
session; not externally refereed or Lean-verified.** This proves the sharp
spatial value for a horizontal canonical global maximizer whose width satisfies

\[
W\le W_H:=\frac4{35}\sqrt{523+2\sqrt{701}}.
\tag{CH.1}
\]

In particular the result covers \(W\le137/50\). For a tilted canonical
maximizer of width at most \(8/3\), it proves a unit-curvature bound on the
quarter **without** the middle-facet atom. The companion [HW1 theorem](gate1-horizontal-maximizer-sharp-value.md)
now excludes every wider horizontal maximizer and closes that entire branch.
The tilted value comparison remains open. **Gate 1 remains ACTIVE.**

The main inputs are the spatial attainment and canonicalization theorems
[SD3](gate1-spatial-dual-height-width-compactness.md) and
[MID2](gate1-global-middle-chord-canonicalization.md), the selected-polygon
curvature bounds [RG1–RG3](gate1-spatial-maximizer-wing-curvature-regularity.md),
the endpoint and source-measure laws
[EP1–EP2](gate1-global-endpoint-complementarity.md), and the positive-pressure
theorem [LH2](gate1-global-positive-pressure-and-wing-identity.md).
[TF3–TF4](gate1-spatial-tilted-facet-pinning.md) supply the exact tilted-facet
endpoints and the location of the top face. The finite neighboring-wall
argument [AR7](one-turn-arm-reduction.md) and the source-flux argument
[VE, Section 3](one-turn-visible-exposure-bound.md) are transferred below with
their spatial hypotheses checked. The final value comparison uses the
general signed-roof identity [AR2](one-turn-arm-reduction.md) and the
function-space calibration
[AF1–AF3](adaptive-functional-global-calibration.md), without importing the
weighted maximizer's endpoint conditions or an ordinary sofa-feasibility
bound.

## 1. Domain, source measures, and velocities

Let \(U\) be a chosen MID-canonical global maximizer of the spatial score

\[
\mathcal P(U)=\int_{I\setminus J}A(x)\,dx-\int_J n_U(x)\,dx,
\]

where \(U\) is a downward convex cap of height one, its projection is
\(I=[l,r]\), its width is \(W=r-l\), and

\[
j_-=l+W/4,\qquad j_+=r-W/4,\qquad J=[j_-,j_+].
\]

The roof \(A\) is affine on \(J\), and \(n_U\) is the **entire
continuous-angle positive two-attached-wall niche**. SD3 gives
\(8/5<W<6\). Write

\[
L=\pi/2,\quad \mu_t=(\cos t,\sin t),\quad
\nu_t=(-\sin t,\cos t),
\]
\[
f(t)=h_U(\mu_t),\quad g(t)=h_U(\nu_t),\quad
p=f'-g+1,\quad q=g'+f-1,
\quad u=f''+f,\quad v=g''+g.
\tag{CH.2}
\]

Away from the possible central-facet parameter these functions have the
regularity supplied by RG. Their a.e. identities and inequalities are

\[
\begin{gathered}
p'=u-1-q,\qquad q'=v-1+p,\qquad p\le1,\qquad q\ge-1,\\
0\le u\le\kappa(q),\qquad0\le v\le\kappa(p),\qquad
\kappa(z)=\max\{|z|,(1+|z|)/2\}.
\end{gathered}
\tag{CH.3}
\]

The arm bounds are the elementary support-point inequalities AR0. They
hold independently of the choice of objective. The density bounds in
CH.3 are the spatial theorem RG3.

Let \(U_n\) be the selected finite polygons of RG/EP, with grid spacing
\(\delta_n\). Their floating facet lengths and positive source exposures
inside their moving windows obey

\[
\ell^{\rm wing}_{n,j}\le\tau^J_{n,j}+b_{n,j},\qquad
\sum_j b_{n,j}\longrightarrow0,\qquad
\tau^J_{n,j}\le\tau^{\rm full}_{n,j}=O(\delta_n).
\tag{CH.4}
\]

The finite niche roofs converge uniformly. By LH2 both endpoint pressures
are positive, so EP2 identifies their limiting source measures with the
actual charged wing-curvature measures. The central facet and horizontal
top face are excluded from those wing measures. In the horizontal case,
all open-quarter curvature belongs to the charged wings, and therefore

\[
\boxed{\nu_f=u(t)\,dt,\qquad\nu_g=v(t)\,dt.}
\tag{CH.5}
\]

These are equalities of **limiting finite source measures**. No equality
with the ordinary arclength measure of the limiting niche is assumed.

## 2. Nonpositive corner height cannot carry curvature excess

Define the inner corner

\[
\mathbf c=(f-1)\mu_t+(g-1)\nu_t,
\qquad \mathbf c'=p\mu_t+q\nu_t.
\]

**Lemma CH1.** At almost every regular parameter, excluding the possible
central-facet atom,

\[
\begin{array}{ll}
u=v=0&\text{on }\{c_y<0\},\\[1ex]
|p|,|q|\le(1+\sqrt2)/4,\quad
u,v\le(5+\sqrt2)/8<1&\text{on }\{c_y=0\}.
\end{array}
\tag{CH.6}
\]

**Proof.** On a compact parameter interval where \(c_y<0\), all
corresponding finite corners are negative for sufficiently large \(n\).
A two-ray quadrant has its maximum vertical height at its corner, so
these sampled quadrants have no positive exposed boundary. Both finite
source measures vanish there. Their limiting equality with the wing
measures proves the first assertion.

On a regular interval \(c_y\) is \(C^{1,1}\). The derivative of an
absolutely continuous function vanishes a.e. on each of its level sets.
Applied successively to \(c_y\) and \(c_y'\), this gives
\(c_y'=c_y''=0\) at almost every point of \(\{c_y=0\}\).
At such a point put \(z=c_x'\), \(s=\sin t\), \(k=\cos t\).
Then

\[
p=zk,\qquad q=-zs,
\qquad su+kv=s+k-2z.
\tag{CH.7}
\]

The last identity follows by differentiating \(\mathbf c'\) and using
CH.3. Since \(\kappa(x)\le|x|+1/2\), the same inequalities give

\[
su+kv\le |z|(s^2+k^2)+(s+k)/2=|z|+(s+k)/2.
\]

If \(z\le0\), CH.7 would imply
\(s+k+2|z|\le|z|+(s+k)/2\), a contradiction. Thus \(z>0\), and
nonnegativity of \(u,v\) in CH.7 gives \(z\le(s+k)/2\). Hence
\(|p|,|q|\le(1+\sqrt2)/4<1\), and applying \(\kappa\) proves
the stated density bound. \(\square\)

This controls possible exposure remaining at height zero without asserting
its disappearance as arclength. Apart from the separately excluded facet
atom, every curvature excess above one must occur at positive corner
height.

## 3. Horizontal middle roof and the exact top interval

Suppose now that the canonical middle roof is horizontal. TF4 says that
the top face meets \(J\); therefore its affine value is one. Write the
top face as \([a,b]\times\{1\}\). It contains \(J\).

For this branch, positivity of the pressures also follows directly from
EP1. Set \(Q_\pm=1+n_U(j_\pm)\ge1\). If
\(C_R=(3Q_+-Q_-)/4\le0\), then
\(C_L=(3Q_--Q_+)/4\ge2Q_+\ge2\), contradicting
\(e_L=(C_L)_+\le1\). Reflection treats the other side. Thus

\[
e_R=A(r)=C_R>0,\qquad e_L=A(l)=C_L>0.
\tag{CH.8}
\]

**Lemma CH2.** If the middle roof is horizontal and \(W\ge2\), then
the top face is exactly \(J\times\{1\}\).

**Proof.** At the first source endpoint,

\[
f(t)\longrightarrow r,\qquad g(t)=1-at+o(t)
\quad(t\downarrow0).
\]

For \(a<x<r-1\), the first wall height tends to positive infinity,
while the second wall height is \((x-a)t+o(t)>0\). Thus
\(n_U(x)>0\) on \((a,r-1)\). At the other source endpoint,
reflection gives \(n_U(x)>0\) on \((l+1,b)\).
These intervals are nonempty because
\(r-1-a,b-l-1\ge3W/4-1>0\). When \(W\ge2\), they overlap or
touch, and cover the interior of \([a,b]\), except possibly one point.
In particular the niche is positive a.e. on \(J\).

Let \(Z_n=\{x\in J_n:n_n(x)>0\}\). Uniform convergence gives only the
lower-semicontinuity statement needed here:

\[
\liminf_n|Z_n|\ge W/2.
\tag{CH.9}
\]

The x-component of a finite positive graph segment's unit tangent is
\(\sin\theta_j\) for either upper source quarter. Consequently

\[
|Z_n|=\sum_j\sin\theta_j\,\tau^J_{n,j}.
\]

The \(O(\delta_n)\) bounds prevent source atoms at the omitted endpoint
normals. Passing to the weak limit in this identity and using CH.5 gives

\[
\lim_n|Z_n|
=\int\sin\theta\,d\omega
=W/2-(T-W/2)=W-T,
\]

where \(T=b-a\), \(\omega\) is charged wing curvature with the top
omitted, and \(T-W/2\) is the charged portion of the top. Thus
\(W-T\ge W/2\), whereas \(T\ge W/2\). Equality follows, and
containment of \(J\) identifies both top endpoints. \(\square\)

This proof uses no convergence theorem for niche zero sets and no bound
\(u,v\le1\).

## 4. Same-sign shadowing for the spatial objective

For a horizontal middle roof, the open-quarter supports are
\(W^{2,\infty}\) with no interior atoms. Their selected polygon
one-sided derivatives converge uniformly on compact open-quarter
intervals, by semiconvexity and differentiability of the limit.

**Lemma CH3.** In this horizontal branch,

\[
\boxed{
u=0,\ v\le\tfrac12\text{ on }\{p>0,q>0\};\qquad
v=0,\ u\le\tfrac12\text{ on }\{p<0,q<0\}
}\quad\text{a.e.}
\tag{CH.10}
\]

**Proof.** The exact finite neighboring-wall lemma of AR7 applies to
every selected polygon, independently of the objective. On a compact
interval in \(\{p>0,q>0\}\), its hypotheses hold uniformly for all
large \(n\), and it gives

\[
\tau^{\rm full}_{n,j}=0,\qquad
\tau^{\rm full}_{n,j+n}
\le\bigl(2\tan(\delta_n/2)-\ell_{n,j+n}\bigr)_+.
\]

Combining these with CH.4 and
\(\ell=\ell^{\rm wing}+\ell^{\rm mid}\) yields

\[
\begin{aligned}
\ell_{n,j}&\le b_{n,j}+\ell^{\rm mid}_{n,j},\\
\ell_{n,j+n}&\le\tan(\delta_n/2)+b_{n,j+n}
                         +\ell^{\rm mid}_{n,j+n}.
\end{aligned}
\tag{CH.11}
\]

For the second inequality, split at \(\ell=2\tan(\delta_n/2)\),
or move the negative \(\ell\) term to the left. The sums of middle
lengths on these compact intervals tend to zero by RG1, because their
normals avoid the horizontal middle facet. Penalty sums also vanish.
Summation and the weak curvature-measure limit prove the first regime.
Horizontal reflection proves the other. \(\square\)

Some useful consequences are

\[
p'\le-1/2\text{ on }\{q>0\},\qquad
q'\le-1/2\text{ on }\{p<0\},
\tag{CH.12}
\]

and, in the positive-positive regime,

\[
p'=-1-q\le-1,\qquad q'\le p-1/2.
\tag{CH.13}
\]

Every positive-\(q\) component whose left endpoint \(t_A\) is
strictly positive satisfies \(q\le1/8\). Before \(p\) becomes
negative, \(q(t_A)=0\), \(p(t_A)\le1\), and CH.13 give

\[
q(t)\le\int_0^{1/2}(1/2-s)\,ds=1/8.
\tag{CH.14}
\]

After \(p\) becomes negative, \(q\) strictly decreases until the
component ends. Unlike the weighted argument with \(p(0)=1/2\), we
do not claim that \(q\) is nonincreasing on its initial component.

## 5. An endpoint energy supplies one good quarter

Assume \(W\ge2\), so CH2 gives top \(=J\). Put \(d=3W/4\).
The endpoint support formulas are

\[
p(0)=e_R\in(0,1],\quad q(0)=d-1>0,\qquad
q(L)=-e_L<0,\quad p(L)=1-d.
\tag{CH.15}
\]

On the initial positive-\(q\) component while \(p>0\), CH.10 gives

\[
E=(p-1/2)^2+(q+1)^2,
\qquad E'=2(q+1)(v-1/2)\le0.
\tag{CH.16}
\]

If that component ends before \(p\) crosses zero, its positive-positive
part has \(u=0\). Otherwise, at its unique crossing \(t_0\) of
\(p=0\),

\[
(q(t_0)+1)^2
\le d^2+(e_R-1/2)^2-1/4
=d^2-e_R(1-e_R).
\tag{CH.17}
\]

Thus

\[
\boxed{d^2\le4+e_R(1-e_R)\quad\Longrightarrow\quad u\le1
\text{ a.e. on }(0,L).}
\tag{CH.18}
\]

Indeed, CH.17 bounds \(q\le1\) after the crossing; it subsequently
decreases on this component, and later positive components obey CH.14.
Wherever \(q>1\) before the crossing, \(u=0\) by CH.10. Everywhere
else \(-1\le q\le1\), so CH.3 gives \(u\le1\). Reflection gives
the criterion \(d^2\le4+e_L(1-e_L)\) for the other quarter. Either
criterion holds automatically when \(W\le8/3\). The next section shows
that only one is needed.

## 6. One good quarter forces both, with visibility inside J

**Theorem CH4.** For a horizontal canonical global maximizer with
\(W\ge2\), if either \(u\le1\) or \(v\le1\) a.e. on its
whole quarter, then both inequalities hold.

**Proof.** Reflect if necessary so that \(v\le1\). Suppose
\(\{u>1\}\) has positive measure. CH.3 forces \(q>1\) there.
By CH.14 such a point belongs to the initial positive-\(q\) component.
Its \(p>0\) part has \(u=0\), and \(p=0\) contains at most one
point by CH.12. Hence choose \(t_*\) with \(p(t_*)<0\),
\(q(t_*)>1\). This component ends at \(\tau<L\), since
\(q(L)=-e_L<0\). On its remaining part \(p\) stays negative and
\(q\) strictly decreases. There is a unique \(b_0\in(t_*,\tau)\)
such that

\[
q(b_0)=1,\quad p(b_0)<0,\quad p<0<q<1
\text{ on }(b_0,\tau).
\]

The **entire future** after \(b_0\) has \(q\le1\), using CH.14
after \(\tau\). Thus \(u\le1\) a.e. on \((b_0,L)\).

Define the two tangent loci

\[
B=\mathbf c+p\nu_t,\qquad D=\mathbf c-q\mu_t,
\qquad B'=(u-1)\nu_t,\qquad D'=(1-v)\mu_t.
\tag{CH.19}
\]

Top \(=J\) gives \(D(0)=(j_-,0)\) and \(B(L)=(j_+,0)\).
The global bound \(v\le1\) makes \(D_x,D_y\) nondecreasing.
The future bound on \(u\) makes \(B_x\) nondecreasing on
\((b_0,L)\). Therefore, for \(b_0<t<\tau\),

\[
\boxed{j_-\le D_x(t)<c_x(t)<B_x(t)\le j_+.}
\tag{CH.20}
\]

Also \(c_y=D_y+q\sin t>0\). The corner graph lies strictly inside
the charged window. The \(D\) graph has positive height wherever it
contributes nonzero arc measure: since \(D_y'=(1-v)\sin t\ge0\),
the density \(1-v\) vanishes a.e. on \(\{D_y=0\}\). A
positive-height point of \(D\) also has \(D_x>j_-\) and, by
CH.20, \(D_x<j_+\). Thus window clipping discards none of its
nonzero contribution.

To prove full-envelope visibility, write the two wall roofs as
\(R_t(x)\) and \(S_t(x)\). Their parameter derivatives are

\[
\partial_tR_t(x)=\frac{x-B_x(t)}{\sin^2t},\qquad
\partial_tS_t(x)=\frac{x-D_x(t)}{\cos^2t}.
\tag{CH.21}
\]

Global monotonicity of \(D_x\) makes \(D(t)\) a global maximum of
the second-wall family; its first-wall companion has positive gap
\(q/\sin t\). Except for constant \(D\) parameter intervals,
which have zero \(D\) arc measure, this source parameter is unique.
At \(\mathbf c(t)\), every earlier second wall is strictly lower,
since \(c_x(t)-D_x(s)\ge q(t)\cos t>0\) for \(s<t\). Every
later first wall is strictly lower, since
\(c_x(t)-B_x(s)\le p(t)\sin t<0\) for \(s>t\). Thus the corner
also has a unique global source parameter. Its x-coordinate strictly
decreases.

On a compact interval \(K=[t_0,t_1]\subset(b_0,\tau)\), the two
graph images are disjoint:

\[
\max_KD_x=D_x(t_1)<c_x(t_1)=\min_Kc_x.
\tag{CH.22}
\]

We can therefore add their source contributions. Here are the limiting
facts needed from VE, with the spatial clipping checked by CH.20.
Positive-height compact pieces exclude finite source angles near the
axes. Their graph slopes are uniformly bounded, the roofs converge
uniformly, and uniqueness of the limiting source parameter forces the
finite active parameters to converge to it. Orient the finite graph with
increasing x. Its exact vector flux is

\[
(dx,dy)=(-\nu_t)\,d\mu_n^f+\mu_t\,d\mu_n^g.
\]

The x-flux is Lebesgue measure and the y-flux converges by uniform roof
convergence and the common slope bound. Solving the limiting two-direction
system gives

\[
d\mu^g=\cos t\,dx+\sin t\,dy,\qquad
d\mu^f=\sin t\,dx-\cos t\,dy.
\tag{CH.23}
\]

The \(D\) graph contributes \((1-v)dt\) to the second source. The
corner graph, traversed in reverse when x increases, contributes
\(-p\,dt\) to that same source. Constant \(D\) intervals and
zero-height pieces have zero \(D\) contribution; cutoffs and exhaustion
remove them. All other finite niche pieces add nonnegative source mass.
Using CH.5,

\[
2v\ge1-p\quad\text{a.e. on }(b_0,\tau).
\tag{CH.24}
\]

Since \(v\le1\), this gives \(p\ge-1\), with endpoint values
following by continuity. CH.3 then gives the opposite inequality
\(v\le\kappa(p)=(1-p)/2\). Hence

\[
v=(1-p)/2,\qquad -1\le p<0\quad\text{on }(b_0,\tau).
\]

Set \(x=1-p\), \(y=1+q\). Then

\[
x'=1+q-u\ge y/2,\qquad y'=v-1+p=-x/2,
\qquad (x^2+y^2)'\ge0.
\]

At \(b_0\), \(y=2\), \(x>1\), so the energy exceeds five.
At \(\tau\), \(y=1\), \(x\le2\), so it is at most five.
This is a contradiction. \(\square\)

The lower bound CH.24 comes from proved globally visible pieces **inside
J**. It is not inferred from source equality and an upper bound alone.
The two source fluxes retain alternating finite edges; their sum is not
replaced by ordinary limiting perimeter.

## 7. Niche confinement and the horizontal sharp value

When both \(u,v\le1\), CH.19 and the top endpoint values give

\[
B_y'=(u-1)\cos t\le0,\quad B_y(L)=0,\qquad
D_y'=(1-v)\sin t\ge0,\quad D_y(0)=0.
\]

Thus \(B_y,D_y\ge0\). The baseline intercepts of the first and
second walls are

\[
R_0(t)=\frac{f(t)-1}{\cos t},\qquad
L_0(t)=\frac{1-g(t)}{\sin t}.
\]

Their derivatives are \(B_y/\cos^2t\ge0\) and
\(D_y/\sin^2t\ge0\), and their respective endpoint limits are
\(R_0(L)=j_+\) and \(L_0(0)=j_-\). Every positive point of every
two-ray quadrant therefore satisfies

\[
j_-\le L_0(t)<x<R_0(t)\le j_+.
\]

The whole positive niche is confined horizontally to \(J\). Since
\(A=1\) on \(J\),

\[
\mathcal P(U)=|U|-|N(U)|-W/2=\Psi(U).
\tag{CH.25}
\]

The general unit-curvature signed-roof identity AR2 now gives
\(\Psi(U)\le F(f,g)-W/2\). Centering the projection puts the pair
in \(X_{W/2}\), whose defining conditions in AF are only the four
endpoint support values. AF1–AF3 give
\(\max_{X_a}F-a\le M/2\) for \(a\ge1/2\). Consequently

\[
\boxed{\mathcal P(U)\le F(f,g)-W/2\le M/2.}
\tag{CH.26}
\]

This route does not require the full historical weighted-maximizer
curvature proof or its ordinary Gerver bound.

### A sharper endpoint criterion

**Lemma CH5 (box-wall endpoint bound).** For any cap inside
\([-2C,2C]\times[0,1]\), with \(0<C<1\),

\[
n_U(C),\ n_U(-C)\le H(C):=1-\sqrt{1-C^2}.
\tag{CH.27}
\]

**Proof.** The first wall at \(x=C\) has height at most
\(1+(C\cos t-1)/\sin t\). Its maximum over \(0<t<L\) is
\(1-\sqrt{1-C^2}\), attained at \(\cos t=C\). Since the niche
uses the minimum of the two attached walls, the same bound applies to
its full-angle supremum. Reflect for \(x=-C\). \(\square\)

For a horizontal maximizer with \(W=4C\), put
\(x=n_U(C)\), \(y=n_U(-C)\). EP gives

\[
e_R-1/2=(3x-y)/4,\qquad e_L-1/2=(3y-x)/4,
\qquad0\le x,y\le H(C).
\]

At least one endpoint satisfies
\(|e-1/2|\le H(C)/2\). To verify this, assume \(x\ge y\).
If \(3y\ge x\), then \((3y-x)/4\le H(C)/2\); otherwise
\(|3y-x|/4\le H(C)/4\). Thus at least one endpoint has

\[
e(1-e)\ge\frac{1-H(C)^2}{4}.
\tag{CH.28}
\]

Either one-quarter energy criterion therefore holds whenever

\[
9C^2\le4+\frac{1-H(C)^2}{4}.
\tag{CH.29}
\]

Writing \(z=C^2\), this is
\(35z\le15+2\sqrt{1-z}\). Its left side minus right side is
strictly increasing on \((0,1)\). Solving its unique zero gives

\[
z=\frac{523+2\sqrt{701}}{1225},
\]

which is exactly the width threshold CH.1.

**Theorem CH6 (horizontal spatial value in the stated width range).**
Let \(U\) be a canonical global maximizer with horizontal middle roof
and \(W\le W_H\). Then \(\mathcal P(U)\le M/2\).

**Proof.** For \(W\le2\), the independently proved
[SW1](gate1-horizontal-short-width-exclusion.md) gives the strict bound
\(\mathcal P\le41/50<M/2\), so this range cannot contain a global
maximizer. For \(2<W\le W_H\), CH2 gives top \(=J\);
CH.28–CH.29 and CH.18 give one good quarter. CH4 gives both, and
CH.25–CH.26 prove the value. \(\square\)

## 8. A good quarter at a tilted maximizer of width at most 8/3

This final result is a necessary condition, not a tilted value theorem.
Reflect if needed so the central facet rises to the right, and write

\[
I=[-2C,2C],\quad J=[-C,C],\quad
A(C)=1,\quad A(-C)=1-\varepsilon,
\]
\[
\frac25<C\le\frac23,\qquad0<\varepsilon<\frac12,\qquad
\delta=\arctan\frac{\varepsilon}{2C},\quad
c=\cos\delta,\quad s=\sin\delta.
\tag{CH.30}
\]

The lower width bound is SD3 and the upper bound on \(\varepsilon\)
is LH1. Both source measures equal the charged wing measures by LH2/EP2.
TF3 says the tilted facet is exactly the segment over \(J\), of
length \(2C/c\), with its normal in the second quarter at parameter
\(\delta\).

For \(0<t<\delta\), the second supporting point is \((C,1)\),
so

\[
g(t)=\cos t-C\sin t.
\]

Its second inner-wall height on \(J\) is
\(1-\sec t+(x-C)\tan t\le0\). These quadrants make no positive
niche there; source equality forces \(u=v=0\) on this parameter
interval. Put \(b=1-e_R\in[0,1]\). Then

\[
f(t)=2C\cos t+(1-b)\sin t\qquad(0<t<\delta).
\]

The first support derivative is continuous at \(\delta\), while the
second has its exact jump \(2C/c\). Therefore

\[
p(\delta+)=1-bc-Cs,\qquad
q(\delta+)+1=Cc-bs+2C/c.
\tag{CH.31}
\]

Before the jump, \(q=C\cos t-b\sin t-1<0\), since \(C<1\).
Thus all potentially large positive-\(q\) components begin after this
single explicit jump.

### Pressure control of the post-jump energy

By CH5, \(n_U(C)\le H(C)\). The endpoint law yields

\[
b=\frac{2-\varepsilon-3n_U(C)+n_U(-C)}4
\ge\frac{3\sqrt{1-C^2}-1-\varepsilon}4>\frac18.
\tag{CH.32}
\]

Here \(3\sqrt{1-C^2}\ge\sqrt5>2\) and
\(\varepsilon<1/2\). The reflected bound also gives
\(e_R\ge(2+\varepsilon-H(C))/4>5/12\), so

\[
p(\delta+)=c(e_R-\varepsilon/2)+(1-c)>0.
\]

Expanding CH.31 gives the exact identity

\[
\begin{aligned}
E_\delta
&=(p(\delta+)-1/2)^2+(q(\delta+)+1)^2\\
&=9C^2+1/4+T(b),\\
T(b)&=b^2-b(c+2\varepsilon)+\varepsilon^2
                                      -\varepsilon c/2.
\end{aligned}
\tag{CH.33}
\]

Since \(C>2/5\), \(\varepsilon<1/2\),

\[
\tan\delta<5/8<3/4,\qquad c>4/5,\qquad
1-c\le\tan\delta<5\varepsilon/4.
\]

The function \(T\) is convex in \(b\). Using
\(\varepsilon^2\le\varepsilon/2\), its values at the endpoints
of the enlarged allowed interval \([1/8,1]\) satisfy

\[
T(1/8)\le-27/320-3\varepsilon/20<0,
\qquad T(1)\le-13\varepsilon/20<0.
\]

Hence

\[
\boxed{E_\delta<9C^2+1/4\le17/4.}
\tag{CH.34}
\]

After \(\delta\), the spatial AR7 argument from Section 4 applies
on every compact interval away from this central normal: RG1 removes the
middle-facet errors there, and there are no further quarter atoms.
If \(q(\delta+)\le0\), all subsequent positive-\(q\) components
start at zero and obey the \(1/8\) bound. If \(q(\delta+)>0\),
the decreasing positive-positive energy CH.16 and CH.34 imply that at
the first crossing of \(p=0\), \(q<1\). If the component ends
earlier, its positive-positive portion has \(u=0\). After the
crossing \(q\) decreases; later positive components again obey the
\(1/8\) bound. CH.3 therefore gives the following conclusion.

**Theorem CH7 (one regular quarter controlled at short tilted maximizers).**
Under CH.30,

\[
\boxed{0\le f''+f\le1\quad\text{a.e. on the entire first quarter}.}
\tag{CH.35}
\]

There is no atom hidden in CH.35: the unique tilted middle-facet atom is
in the second quarter. Reflection gives the corresponding statement for
a negative tilt.

## 9. Remaining scope

CH6 is an actual sharp value comparison on its stated horizontal branch.
CH7 controls one quarter of the short tilted branch. The horizontal
one-good-quarter argument cannot be applied across a tilted central
facet without further work: \(D=\mathbf c-q\mu_t\) has a
leftward and downward jump there, and the globally monotone tangency
locus used in CH4 is absent. CH7 alone also does not identify the spatial
score with the signed weighted value.

The companion [HW1 theorem](gate1-horizontal-maximizer-sharp-value.md)
settles every horizontal width outside CH.1 by exact ordinary-area
exclusions. A tilted sharp value, general fixed contact chart, and
full-turn area theorem remain unproved. Gate 1 is not passed by these
results.
