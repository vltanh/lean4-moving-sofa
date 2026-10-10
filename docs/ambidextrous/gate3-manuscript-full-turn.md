# Full-turn sharpness: the spatial cap problem and its equality case

This chapter proves the full-turn part of the sharp ambidextrous theorem
and identifies every cap attaining its scalar bound. It presents the
reduction and dependency order in one place. The linked technical proofs
provide the detailed source-measure, geometric, and finite arithmetic
arguments used below; they are the corresponding manuscript appendices.
The argument is written mathematics, with its external input stated
explicitly.

Let

\[
4Y^3+3Y-1=0,\quad Y>0,\qquad
M=1+4Y^2+\arctan Y.
\tag{FTM.1}
\]

The reference construction has area \(M\). Its exact support formulas,
matching, feasibility, and area are established in
[the reference calculation](14-sharp-quadratic-calibration.md) and
[the direct reference construction in the introduction, Section 3](gate3-manuscript-introduction.md).
Write \(U_*\) for the upper downward cap of its centered convex hull.
In particular \(M/2>41/50\): the cubic is negative at \(297/1000\),
and \(\arctan x\ge x-x^3/3\) gives the required strict rational
comparison.

## 1. The full-turn problem reduces to a global cap maximum

Let \(U\subset\mathbb R\times[0,1]\) be a nonempty compact convex
cap closed downward to its baseline. Write its actual horizontal
projection as \(I=[l,r]\), its width as \(W=r-l\), and its concave
upper roof as \(A\). Put

\[
j_-=(3l+r)/4,\qquad j_+=(l+3r)/4,\qquad J=[j_-,j_+].
\]

For \(L=\pi/2\), define the two upward unit normals
\(\mu_t=(\cos t,\sin t)\), \(\nu_t=(-\sin t,\cos t)\).
Write \(h_U(n)=\max_{z\in U}z\cdot n\) for the support function
and \([z]_+=\max\{z,0\}\) for the positive part.
The genuine attached inner walls and their complete positive niche are

\[
R_t(x)=\frac{h_U(\mu_t)-1-x\cos t}{\sin t},\qquad
D_t(x)=\frac{h_U(\nu_t)-1+x\sin t}{\cos t},
\]
\[
n_U(x)=\left[\sup_{0<t<L}\min\{R_t(x),D_t(x)\}\right]_+,
\qquad
P(U)=\int_{I\setminus J}A(x)\,dx-\int_J n_U(x)\,dx.
\tag{FTM.2}
\]

Thus the cap score rewards the exterior half of the roof and charges
the entire niche on the middle half. It is defined even when the
cap-minus-niche survivor has not been shown feasible or connected.
It is the full-angle score \(P(U)=\mathcal P_L(U)\) in the
introduction and the partial-turn chapter.

The decisive scalar theorem is

\[
\boxed{P(U)\le M/2\quad\text{for every such cap}.}
\tag{FTM.3}
\]

To see why this suffices, let \(S\) be an actual connected body making
both full conventional turns, and retain its actual convex hull in a
common incoming unit strip. Its upper downward cap \(U\) and vertically
reflected lower downward cap \(V\) share \(I\) and \(J\).
Set \(d_U=1-A_U\), \(d_V=1-A_V\). The exact signed envelope fiber is

\[
\ell(x)=1-\max\{d_V(x),n_U(x)\}
             -\max\{d_U(x),n_V(x)\}.
\tag{FTM.4}
\]

On \(J\), drop the outer deficits to obtain
\(\ell\le1-n_U-n_V\); outside \(J\), drop the niche terms to
obtain \(\ell\le A_U+A_V-1\). The constant terms cancel because
both regions have length \(W/2\). Connectedness makes every projected
fiber of the actual canonical envelope nonempty, and hence

\[
|S|\le\int_I\ell\le P(U)+P(V)\le M.
\tag{FTM.5}
\]

For an auxiliary hull the middle inequality remains a signed-integral
statement; it does not discard negative fibers. This distinction is
proved directly in [the original-motion bridge](original-motion-global-bridge-gate0-audit.md)
and [the spatial partition](gate1-spatial-dual-height-width-compactness.md).
At the reference the two roofs equal one on \(J\), both niches are
confined to \(J\), and equality holds throughout FTM.5.

The scalar maximum is attained. Vertical Minkowski extrusion by
\(\varepsilon\) raises the exterior roof by \(\varepsilon\) and
each positive niche height by at most \(\varepsilon\); equal lengths
of the two integration regions make this operation score-nondecreasing.
It therefore suffices for attainment to use height-one caps. After
horizontal centering, the actual \(45^\circ\) walls give

\[
P(U)\le W/2,\qquad
n_U(x)\ge(W/2-\sqrt2-|x|)_+.
\]

For \(W\ge6\), integration yields

\[
P(U)\le\frac{(1+\sqrt2)W}{2}-\frac{3W^2}{16}<M/2.
\tag{FTM.6}
\]

Every competitive cap consequently has \(8/5<W<6\). Centered caps
then lie in a fixed compact box. Their roofs converge in \(L^1\)
under Hausdorff convergence. Their full niches converge uniformly:
on \([\delta,L-\delta]\) the wall denominators stay bounded below,
while omitted endpoint-angle positive heights are uniformly
\(O(\delta)\). Moving endpoints of \(J\) also converge. These facts
prove continuity of \(P\) and attainment.

There is an exact canonical reduction. Let \(a_J(x)\) be the chord
joining \((j_-,A(j_-))\) to \((j_+,A(j_+))\). Concavity gives
\(A\ge a_J\) on \(J\) and \(A\le a_J\) outside it. The cap

\[
U^c=U\cap\{y\le a_J(x)\}
\tag{FTM.7}
\]

therefore has the same exterior roofs and projection. All supports
decrease, so its whole niche decreases pointwise. Restore height one
by vertical extrusion. The result has no smaller score and is affine
on all of \(J\). Thus a global maximizer may be chosen canonical in
this precise sense. These are operations on the scalar cap score,
not asserted area-preserving operations on an original sofa. The
complete argument is [the middle-chord reduction](gate1-global-middle-chord-canonicalization.md).

## 2. Actual source laws at a prescribed canonical maximizer

Fix any canonical global maximizer \(U\). The source laws must hold
for this same cap. To obtain them, approximate the full niche by dyadic
turning grids and maximize the sampled score with a penalty
\(\eta_n D_n(V,U)^2\), where \(D_n^2\) is a positively weighted
squared distance between sampled supports. If
\(e_n=\sup(P_n-P)\to0\), take \(\eta_n=\sqrt{e_n}+1/n\).
Grid circumscription of \(U\) preserves the sampled supports and has
zero penalty, so the selected polygons satisfy

\[
D_n(U_n,U)^2\le e_n/\eta_n\longrightarrow0.
\tag{FTM.8}
\]

Compactness identifies their Hausdorff limit with the prescribed
\(U\). This targeting argument, detailed in
[the regularity proof](gate1-spatial-maximizer-wing-curvature-regularity.md),
is available for every canonical maximizer, not merely one existential
choice.

An outward variation of a floating outer facet gives
\(\ell^{\rm wing}_{n,j}\le\tau^J_{n,j}+b_{n,j}\), where
\(\tau^J\) is its attached positive inner-wall exposure inside the
moving middle window and \(\sum_jb_{n,j}\to0\). The geometric
neighboring-wall estimate gives, with mesh \(\delta_n\),

\[
\tau^J_{n,j}\le\tau^{\rm full}_{n,j}
\le C_0\delta_n+
       \bigl(2\tan(\delta_n/2)-\ell_{n,j}\bigr)_+.
\tag{FTM.9}
\]

The affine middle roof makes uncharged facet mass vanish away from
its single normal. Consequently the charged wings have bounded
curvature densities; no singular continuous part or other interior
charged atoms survive. The top and the uncharged middle normal are
kept separate throughout this passage.

The moving-window endpoint variables are

\[
Q_\pm=A(j_\pm)+n_U(j_\pm),\qquad
C_R=\frac{3Q_+-Q_-}{4},\quad
C_L=\frac{3Q_--Q_+}{4}.
\tag{FTM.10}
\]

Actual inward trimming, combined with the valid outward variation
when an end face is positive, proves

\[
e_R=A(r)=(C_R)_+,\qquad e_L=A(l)=(C_L)_+.
\tag{FTM.11}
\]

Moving a redundant vertical wall is not used as an endpoint variation.
Horizontal erosion then controls the nonnegative defect between the
limiting finite middle-exposure measure \(\nu\) and the actual
charged wing measure \(\omega\). Its right and left cosine moments
are respectively \((-C_R)_+\) and \((-C_L)_+\). These are the
[endpoint and exposure laws](gate1-global-endpoint-complementarity.md).
Here \(\omega\) omits the vertical end faces and the horizontal top;
any charged top length is accounted for separately.

Two genuine cap operations and estimates complete the normalization.
Inserting a height-one point at the nearer middle endpoint strictly
improves the score if the top misses \(J\). A tilted central facet
cannot extend into either charged wing; a safe support-normal variation
would improve its exterior roof without changing the niche on \(J\).
These are the [top-localization and facet-pinning laws](gate1-spatial-tilted-facet-pinning.md).
A direct roof-and-tent calculation further gives
\(P<31233/39200<4/5\) when the lower middle endpoint has height at
most \(1/2\). Thus every canonical maximizer has both endpoint
pressures positive. Indeed, if \(C_L\le0\), then
\(Q_+\ge3Q_-\) and \(e_R=C_R\ge2Q_->1\), contradicting the
height ceiling; the opposite case is identical. Equations FTM.11 become \(e_R=C_R\),
\(e_L=C_L\), the exposure defect vanishes, and the finite Green
identity gives

\[
\boxed{\nu=\omega,\qquad
2P=L_{\rm wing},\qquad
\max_Jn_U\le(e_R+e_L)/2.}
\tag{FTM.12}
\]

Here \(L_{\rm wing}\) includes horizontal top overhangs but excludes
vertical end faces. The proof of
[these identities](gate1-global-positive-pressure-and-wing-identity.md)
retains finite source measures; it does not identify their weak limit
with ordinary arclength of a niche graph whose zero-height portions
may disappear.

For the actual open-quarter supports put

\[
f=h_U(\mu_t),\quad g=h_U(\nu_t),\quad
p=f'-g+1,\quad q=g'+f-1,\quad
u=f''+f,\quad v=g''+g.
\]

Away from a possible central atom, the source laws imply

\[
p'=u-1-q,\quad q'=v-1+p,\qquad p\le1,\quad q\ge-1,
\]
\[
0\le u\le\kappa(q),\qquad0\le v\le\kappa(p),\qquad
\kappa(z)=\max\{|z|,(1+|z|)/2\}.
\tag{FTM.13}
\]

On \(p,q>0\), same-sign shadowing gives \(u=0,v\le1/2\);
on \(p,q<0\), it gives \(v=0,u\le1/2\). In particular the
critical bounds \(u,v\le1\) have not yet been assumed or proved.

## 3. Horizontal maximizers and the strict functional calibration

Write \(I=[-2C,2C]\), \(J=[-C,C]\). If the middle is horizontal,
its roof is one. For \(C\ge1/2\), the finite horizontal exposure
moment forces the top face to be exactly \(J\): any overhang would
decrease the available charged projection below the full positive
middle-niche projection. The proof needs only lower semicontinuity
of that positive projection, not continuity of zero sets.

In this geometry one globally unit-bounded quarter forces the other.
For example, if \(u\le1\), the first-wall tangencies are monotone.
Before a putative first companion excess, positive corner pieces and
the needed tangencies are genuinely visible inside \(J\). Their
source flux gives the energy bound
\((p-1)^2+(q+1)^2\le5\); reaching \(p=-1,q>0\) would violate it.
This proves the transfer without presupposing a contact chart.

There is an explicit endpoint criterion supplying one such quarter.
For \(0<C<1\), the box wall gives

\[
n_U(\pm C)\le H(C):=1-\sqrt{1-C^2}.
\]

The endpoint equations imply that at least one end height satisfies
\(e(1-e)\ge[1-H(C)^2]/4\). Reflect if necessary so this is the
initial endpoint of the first quarter. On its initial same-sign interval,
\((p-1/2)^2+(q+1)^2\) is nonincreasing. At the first \(p=0\)
crossing this gives \(q\le1\), and hence one unit quarter, whenever

\[
9C^2\le4+\frac{1-H(C)^2}{4}
\quad\Longleftrightarrow\quad
C\le C_H:=\frac1{35}\sqrt{523+2\sqrt{701}}.
\tag{FTM.14}
\]

The full horizontal width coverage is:

| Width range | Conclusion |
|---|---|
| \(C\le1/2\) | Three actual niche angles give \(P\le41/50<M/2\). |
| \(1/2<C\le C_H\) | FTM.14 and the one-quarter transfer give both unit bounds. |
| \(8571/12500\le C\le4/5\) | The exact leakage certificate contradicts the ordinary one-turn bound. |
| \(C\ge4/5\) | An initial width estimate gives \(C<13/15\); three-angle estimates exclude \([4/5,13/15]\). |

The overlap \(8571/12500<C_H\) is exact. The short and curvature
arguments are proved in [the horizontal geometry](gate1-spatial-maximizer-curvature-and-horizontal-value.md);
the wide alternatives and their rational certificates are proved in
[the complete horizontal theorem](gate1-horizontal-maximizer-sharp-value.md).

**External ordinary-area input.** We use Baek's
[*Optimality of Gerver's Sofa*, Theorem 1.1.1](https://arxiv.org/html/2411.19826v1),
together with the existing exact enclosure of Gerver's area, in the
form

\[
|\mathcal S|\le G_0:=\frac{22199}{10000}
\tag{FTM.15}
\]

for a compact connected body \(\mathcal S\) admitting a genuine
one-turn motion in a unit right-angle corridor. The
[enclosure and its source dependencies](one-turn-single-excess-quarter.md)
are explicit. Before applying FTM.15 in the horizontal wide range,
the geometric proof confines positive corners to \(J\), proves that
the niche is convex on each wing and lies below \(A\), and constructs
the continuous canonical motion of
\(\mathcal S=\{(x,y):n_U(x)\le y\le A(x)\}\).
Its connected top graph meets every nonempty fiber. Thus FTM.15 is
applied to an actual ordinary sofa, not to a formal cap score.

In the surviving horizontal range, let
\(B=(f-1)\mu_t+f'\nu_t\) and
\(D=(g-1)\nu_t-g'\mu_t\). The unit bounds imply
\(B_y'=(u-1)\cos t\le0\) and
\(D_y'=(1-v)\sin t\ge0\), with \(B_y(L)=D_y(0)=0\).
The wall baseline intercepts therefore confine the whole positive
niche to \(J\). Since \(A=1\) there,
\(P=|U|-\int_I n_U(x)\,dx-2C\).
The proved signed-roof Green identity gives

\[
P(U)\le F(f,g)-a,\qquad a=2C,
\tag{FTM.16}
\]

where \(p_-:=\min(p,0)\), \(q_+:=\max(q,0)\), and

\[
\begin{aligned}
F(f,g)=\frac12\int_0^L\bigl[&f^2+g^2-f'^2-g'^2
+(f-1)^2+(g-1)^2\\
&+(f-1)g'-(g-1)f'-p_-^2-q_+^2\bigr]dt.
\end{aligned}
\tag{FTM.17}
\]

This comparison is a geometric theorem, proved in
[the signed-roof reduction](one-turn-arm-reduction.md), rather than a
definition of ordinary area by a support functional.

The analytical maximization of FTM.17 is unrestricted within

\[
X_a=\{(f,g)\in H^1(0,L)^2:
f(0)=g(L)=a,\ f(L)=g(0)=1\}.
\]

For the difference \((v_0,w_0)\) of two elements of \(X_a\),
set \(z=v_0+iw_0\) and \(y=e^{-it/2}z\).
The negative quadratic part of the unpenalized functional satisfies

\[
B_0(v_0,w_0)=\frac12\int_0^L
\left(|y'|^2-\frac94|y|^2\right)dt
\ge\frac7{32}\int_0^L|y'|^2dt.
\tag{FTM.18}
\]

The contact penalties are also concave. Thus each fixed-width problem
has a unique maximizer, automatically satisfying \(f(t)=g(L-t)\).
Writing the auxiliary momenta as
\(\mathsf P=p+p_-\), \(\mathsf Q=q+q_+\), its Euler equations are

\[
\mathsf P'=-1-b(\mathsf Q),\qquad
\mathsf Q'=-1+c(\mathsf P),
\tag{FTM.19}
\]

with \(b(z)=z/2\) for \(z\ge0\), \(b(z)=2z\) otherwise, and
\(c(z)=2z\) for \(z\ge0\), \(c(z)=z/2\) otherwise.
At an interior maximizing width the natural endpoint variation gives
\(\mathsf P(0)=1/2\), \(\mathsf Q(L)=-1/2\).

This globally Lipschitz Hamiltonian system has only two stationary
width profiles. The disk occurs at \(a=1/2\) and has smaller value.
For the other orbit, its three transit times sum to

\[
2\beta+\pi-4\arctan(2\tan\beta)=L.
\tag{FTM.20}
\]

The left side is strictly decreasing in \(\beta\); the equation is
equivalent to the cubic in FTM.1. The corresponding cap half-width is
\(a_*=1/(3\sin\beta)\), so \(a_*=m_*\) and
\(\beta=\beta_*\) in the introductory notation.
The width boundary has smaller value,
and the explicitly solved large-width tail tends to minus infinity,
so the stationary classification computes the global maximum. The
[complete calibration proof](adaptive-functional-global-calibration.md)
therefore gives

\[
F(f,g)-a\le M/2\quad(a\ge1/2),
\tag{FTM.21}
\]

with equality only at the centered reference pair. This proves the
horizontal sharp bound and records the strictness needed later.

## 4. All tilted canonical maximizers are excluded

Reflect horizontally, which preserves the full-turn score, so a tilted
middle rises to the right. Normalize

\[
I=[-2C,2C],\quad J=[-C,C],\quad
A(-C)=1-h,\quad A(C)=1,\quad
\text{top}=[C,C+T]\times\{1\}.
\tag{FTM.22}
\]

Use the actual first support \(f\), and for \(g\) use only the
left-wing support
\(\max_{x\in[-2C,-C]}[-x\sin t+A(x)\cos t]\).
This removes the central-facet atom. The omitted high-point second
wall is nonpositive on \(J\), so positive niche contacts there are
unchanged. All subsequent curvature statements refer to these
regular wing densities.

The actual short, wide and intermediate roof/tent comparisons, followed
by the three full-triangle estimate, give

\[
\frac{1001}{2000}<C<\frac{37}{50},\qquad
0<h<\frac{17}{50}.
\tag{FTM.23}
\]

These are global scalar estimates, with all floor and moving-window
clipping retained. For example, with \(a=2C\) and \(k=\sqrt2-1\),
the intermediate comparison is

\[
P\le1-\frac{(a-\sqrt2)^2}{2}
-\frac{2a}{4a-h}(k+h/2)^2.
\tag{FTM.24}
\]

The full proofs and exact constants are in
[the width comparisons](gate1-tilted-width-exclusions.md) and
[the full-triangle cut](gate1-tilted-full-triangle-width-cut.md).

The first key exclusion is stronger than a two-unit-quarter theorem:
if \(u\le1\) on the first wing, the tilted maximizer is impossible,
with no assumption \(v\le1\). Here is the mechanism of
[the first-wing exclusion](gate1-tilted-first-wing-exclusion.md).
Monotone first-wall tangencies, exact finite-source projection, and a
first-bad-entry argument give \(T>0\), a positive niche interval
\((x_{\rm zero},C+T)\), and \(x_{\rm zero}=-C+T\).
At every possible companion excess one has \(q\le1/4\).

Measurable ties are retained through fractional occupations. On the
core \(p<0<q\), the source equations have the exact form

\[
u=(1-u)\mathbf1_{\{t<\beta_c\}}+q\chi,
\qquad v=(1-v)d-p\chi,
\qquad0\le\chi,d\le1,
\tag{FTM.25}
\]

where \(B_x(\beta_c)=C\). The same \(\chi\) appears in both
corner-source terms; this is proved by joint angle-position
disintegration, not guessed from a finite contact pattern. A visible
second tangency with \(v>1\) would be an angular local minimum, so
\(d=0\) there. The first companion-floor displacement is at least
\(T\); it need not be the global envelope minimum. The calibrated
energy retains both this displacement and the entire folded-source
defect. Its endpoint balance yields

\[
6CT\le\left(\frac23+\frac56+\frac{25}{48}\right)T
=\frac{97}{48}T<3T,
\tag{FTM.26}
\]

contrary to \(C>1/2\). The detailed
[occupation proof](gate1-tilted-folded-source-occupations.md)
is indispensable when companion tangencies fold or revisit the floor.

For \(C\le2/3\), the central-atom-aware endpoint energy estimate
already supplies \(u\le1\). For wider caps put

\[
B=e_R-1+h,\qquad s_h=\sqrt{h(2-h)}.
\]

The [initial-floor criterion](gate1-tilted-initial-floor-energy.md)
supplies the same bound whenever

\[
9C^2+B^2\le5,\qquad
9C^2+B^2+B(1-h)-3Cs_h\le4.
\tag{FTM.27}
\]

Indeed, both densities vanish while the initial same-sign tangency
lies below the floor. Stopping that exact circular evolution at the
first floor contact or the first \(p=0\) contact gives energy at
most \(17/4\), hence \(q\le1\) at the first crossing. Subsequent
positive components are too small to produce first-wing excess.
Both inequalities hold throughout \(h\ge21/100\) in FTM.23.

The remaining wider, lower-tilt branch is handled without assuming
either whole-wing unit bound. First,
[positive-corner confinement](gate1-tilted-corner-confinement.md)
proves \(n_U\le A\), convexity of the niche on both exterior wings,
and a compact connected survivor with an explicit continuous ordinary
one-turn motion. Only now is the external bound FTM.15 used.
The [early-excess estimate](gate1-tilted-first-excess-ends-early.md)
and [reflected-tail projection](gate1-tilted-reflected-tail-and-projection.md)
then give the following bounds, where
\(N_{\rm out}=\int_{I\setminus J}n_U(x)\,dx\):

\[
T>0,\quad n_U(-C)=0,\quad
e_R=\frac12+\frac h4+\frac{3z}{4},\quad
e_L=\frac12-\frac{3h}{4}-\frac z4,
\]
\[
z=n_U(C),\quad T\le s_h,\quad
z\le\frac{C}{\sqrt{1-C^2}}T,\quad
J_f:=\int_0^L(u-1)_+\sin t\,dt<\frac1{40},
\]
\[
N_{\rm out}\le\frac{(T+J_f)z}{2}.
\tag{FTM.28}
\]

In particular all possible first-wing excess ends before \(11/15\),
earlier than a positive right-endpoint tangency because
\(\cos(11/15)>37/50\). The projection argument proves its zero-set
claim through finite-source mass, not through uniform convergence of
niche roofs alone.

These estimates close the entire parameter rectangle with the following
exact alternatives.

| Tilted range after FTM.23 | Exclusion |
|---|---|
| \(C\le2/3\) | First-quarter unit bound, then FTM.26. |
| \(2/3<C<37/50,\ h\ge21/100\) | Both FTM.27 tests hold, then FTM.26. |
| \(2/3<C\le73/100,\ 1/20\le h\le21/100\) | FTM.28 makes both energy tests strict. |
| \(73/100\le C<37/50,\ 1/20\le h\le21/100\) | The actual triangle comparison gives \(P<7550393/9240000<41/50\). |
| \(2/3<C<37/50,\ 0<h\le509/10000\) | Either an energy test fails and forces ordinary area above \(G_0\), or both hold and FTM.26 applies. |

For the third row the radius bound is \(798001/160000<5\), and
the two extremal energy bounds are \(634973/160000<4\) and
\(553949/160000<4\). These rows prove \(h<1/20\), as detailed in
[the final height reduction](gate1-tilted-final-height-reduction.md).

For completeness, the last row uses a single ordinary-area lower
bound. Set
\(C_0=\sqrt{17}/6\),
\(S_0=(2\sqrt{17}+\sqrt{26})/6\),
\(\lambda=\sqrt{17/26}\),
\(m_0=3/(4\sqrt{26})\), and \(a_0=(1-\lambda)/2\).
The two wing chords and FTM.28 give

\[
|\mathcal S|\ge S_0+(2+\lambda)(C-C_0)
-Ch-m_0(h+z)+a_0T-\frac{(T+J_f)z}{2}.
\tag{FTM.29}
\]

Failure of the second energy test implies
\(C-C_0>s_h/6-3(h+z)^2/64\); substitution gives
\(|\mathcal S|>S_0>2669/1200>G_0\).
Failure of the first gives the exact bound
\(|\mathcal S|>666488123/300000000>G_0\).
[The small-height proof](gate1-tilted-small-height-exclusion.md)
contains the complete rational certificates. Equality in either energy
test belongs to the successful-test branch. Since
\(1/20<509/10000\), there is no boundary gap.

All tilted canonical maximizers have been excluded. The remaining
horizontal maximizer satisfies FTM.16–21. Attainment and the canonical
reduction now prove FTM.3 on the original cap domain, and FTM.5 proves
the sharp full-turn body bound. The ordinary one-turn input has been
used only to obtain strict contradictions for already feasible
survivors; no equality theorem for that external result is required.

## 5. Equality recovers every original cap and full-turn body

Because the selections in FTM.8 target any prescribed canonical
maximizer, every canonical equality cap follows the same exclusions.
It is horizontal and enters FTM.16–21 with equality throughout.
Extend its upper support pair to a periodic real \(H^1\) profile by
the following formulas for \(0\le t\le L\):

\[
\widehat h(t)=f(t),\quad\widehat h(t+L)=g(t),\qquad
\widehat h(-t)=f(t)-\sin t,\quad
\widehat h(-t-L)=g(t)-\cos t.
\tag{FTM.30}
\]

The endpoint values make the pieces agree, and its two reflected
halves coincide. Its full adaptive value is \(2F-2a=M\).
The strict calibration therefore identifies the reference support
profile up to horizontal translation. No independent convexity of
the auxiliary lower-half extension is required. Continuous support
representatives agree pointwise, which identifies the actual cap.

It remains to reverse the operations on an arbitrary original equality
cap. Apply the middle chord to obtain \(V\), and extrude by
\(\varepsilon\) to obtain the canonical equality cap \(V^+\).
The universal bound forces all three scores to equal \(M/2\).
Raw wall heights shift by exactly \(\varepsilon\), giving the
stronger extrusion identity

\[
n_V=(n_{V^+}-\varepsilon)_+,\qquad
P(V^+)-P(V)=\int_J(\varepsilon-n_{V^+})_+\,dx.
\tag{FTM.31}
\]

The reference niche is continuous and vanishes at both middle
endpoints. A positive \(\varepsilon\) makes the last integral
strictly positive on an interval next to either endpoint. Thus
\(\varepsilon=0\). The chord cap already has roof one on \(J\);
the original cap contains it and has height at most one, so its middle
roof is also one. Outside \(J\) the chord cut preserved the roof
pointwise. This proves

\[
\boxed{P(U)=M/2\iff U=U_*+(b,0)\text{ for some }b\in\mathbb R.}
\tag{FTM.32}
\]

The detailed equality proof, including the centering of the displayed
reference profile, is [the full-turn cap classification](gate3-full-turn-cap-equality.md).

For a connected compact full-turn body of area \(M\), equality in
FTM.5 forces both original caps to satisfy FTM.32. Their common
projection makes their translation parameters equal. Hence the actual
hull is the reference hull, and its actual canonical envelope is the
reference sofa \(\Sigma_*\). The original body is a closed subset
of this envelope with the same area. The reference is regular closed:
its central fibers lie between continuous strictly separated graphs,
and its flanks are unchanged convex-hull fibers. A proper closed subset
would omit a neighborhood containing a positive-area interior ball.
Thus the original body equals \(\Sigma_*\), up to the common rigid
normalization. This exact-set step rules out both hidden appendages
and zero-area deletions; it is proved explicitly in
[the body-recovery argument](gate3-terminal-and-body-rigidity.md).

Full-turn sharpness and its equality case concern bodies and supports.
They do not assert uniqueness of motion parameterizations, and they
do not replace the separate partial-turn argument retaining the two
actual outgoing strips.
