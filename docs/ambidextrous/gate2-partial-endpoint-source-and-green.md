# Gate 2: endpoint pressures, terminal source mass, and the stationary wing identity

**October 10, 2026. Written mathematical theorem, independently reviewed
within this research session.** This is a
fixed-terminal-angle variational theorem for the partial cap objective.
It does not by itself prove the sharp partial cap value or an angle
stationarity law; [the Gate 2 closure](gate2-sharp-partial-turn-closure.md) assembles the later inputs.

The domain and canonical reductions are those of
[the partial cap domain reductions](gate2-partial-cap-domain-reductions.md)
(PD). The proof below reconstructs the finite selections for the partial
objective. In particular it does not import a selected full-turn source
measure or discard the whole terminal first wall.

The elementary four-line estimate used below is proved in
[WR.1](one-turn-weighted-regularity.md), Section 1. Its application here is geometric only. The finite
grid used here need not consist of consecutive equally spaced outer
normals, so the distinction between a circumscribed facet length and
an actual facet length is made explicitly.

Labels PS are local.

## 1. Exact statement and conventions

Let \(L=\pi/2\). Let \((U,\alpha)\) be a joint global maximizer of
\(\mathcal P_\alpha\) over downward convex caps of height at most one and
\(\alpha\in[\pi/4,L]\). Since the full-turn reference is admissible,
\(\mathcal P_\alpha(U)\ge M/2>41/50\). One may choose \(\alpha\)
largest among all terminal angles of joint global maximizers: the
compact attainment domain in PD makes this maximum exist. Apply PD's
height and middle-chord reductions at that same angle, so that \(U\)
has height one and affine middle roof. The fixed-angle identities
proved below hold even without the additional largest-angle choice.
Assume \(\alpha<L\); the endpoint \(\alpha=L\) is already covered by
Gate 1. Write

\[
I=[l,r],\quad W=r-l,\quad
j_-=(3l+r)/4,\quad j_+=(l+3r)/4,\quad J=[j_-,j_+].
\]

PD gives \(8/5<W<6\), and the top face meets \(J\). Let \(A\) be the
roof of \(U\), and abbreviate the partial barrier by

\[
q(x)=\max\left\{0,\sup_{0<t<\alpha}\min\{R_t(x),S_t(x)\},
R_\alpha(x)\right\},
\]
\[
R_t(x)=\frac{h_U(\cos t,\sin t)-1-x\cos t}{\sin t},\qquad
S_t(x)=\frac{h_U(-\sin t,\cos t)-1+x\sin t}{\cos t}.
\tag{PS.1}
\]

Use capital \(Q\) for the combined boundary values:

\[
A_\pm=A(j_\pm),\quad q_\pm=q(j_\pm),\quad Q_\pm=A_\pm+q_\pm,
\]
\[
C_R=\frac{3Q_+-Q_-}{4},\qquad
C_L=\frac{3Q_--Q_+}{4},\qquad e_R=A(r),\quad e_L=A(l).
\tag{PS.2}
\]

Here \(\omega\) denotes the actual normal/arclength measure of the
upper boundary above \(I\setminus J\), with the vertical end faces and
the horizontal top face omitted. In particular a charged terminal
facet at normal \(\alpha\) is included. Let \(T_{\rm wing}\) be the
length of the height-one top face outside \(J\).

**Theorem PS1.** Every selected maximizer above satisfies

\[
\boxed{e_R=C_R>0,\qquad e_L=C_L>0.}
\tag{PS.3}
\]

There are finite partial-source selections converging to this prescribed
cap whose limiting positive source measure \(\nu\) satisfies

\[
\boxed{\nu=\omega.}
\tag{PS.4}
\]

On the visited open arcs \((0,\alpha)\) and \((L,L+\alpha)\), this
measure has a bounded density. Its only possible atom is at the first
terminal normal \(\alpha\). The terminal companion normal \(L+\alpha\)
has no exposure atom. There is no charged wing measure on either
unused open arc.

Consequently, with the actual charged upper-boundary length

\[
L_{\rm wing}=\omega((0,\pi))+T_{\rm wing},
\]

one has

\[
\boxed{2\mathcal P_\alpha(U)=L_{\rm wing},\qquad
\max_J q\le\frac{e_R+e_L}{2}.}
\tag{PS.5}
\]

The measure \(\nu\) is a weak limit of precisely defined finite source
measures. PS.4 does not identify it with ordinary arclength of the
limiting positive barrier graph. Vanishing-height pieces are allowed
in the limiting argument.

## 2. Select the prescribed cap at the fixed angle

The joint maximizer \(U\) is also a global maximizer with its own angle
\(\alpha\) fixed. Center its projection and choose an artificial box
\([-R,R]\times[0,1]\), with \(R>7\). Put \(B=R+1\).
The finite comparison class has height **at most** one, so inward
trimming and erosion remain admissible.

For dyadic \(n\ge2\), put \(\delta_n=\alpha/n\) and
\(t_j=j\delta_n\). Use the finite barrier

\[
q_{n,V}(x)=\max\left\{0,
\max_{1\le j<n}\min\{R_{V,t_j}(x),S_{V,t_j}(x)\},
R_{V,\alpha}(x)\right\}.
\tag{PS.6}
\]

The quadrant at \(t_n=\alpha\) may be included redundantly: its
two-wall minimum is dominated by the whole \(R_{V,\alpha}\) wall.
This redundant quadrant will supply a neighbor in the four-line bound.

Take the outer normal set

\[
\Gamma_n=
\{k\pi/(2n):0\le k\le2n\}
\cup\{t_j:0\le j\le n\}
\cup\{L+t_j:0\le j\le n\}.
\tag{PS.7}
\]

Coincident normals are kept only once. Thus the two axes and the top
normal are sampled, both source grids are sampled, and an independent
dense grid covers the whole upper semicircle. Let \(\mathcal G_n\)
be the compact class of downward grid polygons obtained from the floor
and the halfplanes at these normals, inside the artificial box. The
halfplanes can always be recorded at the polygon's actual supports.

Set \(P_n(V)=\int_{I_V\setminus J_V}A_V-\int_{J_V}q_{n,V}\).
The grids in PS.6 are nested and their union is dense. PD's uniform
endpoint-angle bound at zero, together with ordinary support
continuity on the closed interval away from zero, proves that the
finite barriers increase to \(q_{V,\alpha}\) uniformly on the compact
cap-and-abscissa domain. Equivalently one can apply Dini's theorem to
this monotone continuous sequence. Hence

\[
a_n:=\sup_V\{P_n(V)-\mathcal P_\alpha(V)\}\longrightarrow0.
\tag{PS.8}
\]

The circumscription of any cap at \(\Gamma_n\) contains the cap and
has exactly its sampled supports. It therefore has the same finite
barrier and projection, and at least its exterior reward. In
particular the circumscription of \(U\) has score at least
\(\mathcal P_\alpha(U)\).

Give the two axis normals weights \(1/4\) each and every remaining
normal weight \(1/[2(|\Gamma_n|-2)]\). The weights are positive, sum
to one, and each dense-grid weight is bounded below by a fixed
positive constant times \(1/n\). Define

\[
D_n(V,U)^2=\sum_{\theta\in\Gamma_n}w_{n,\theta}
[h_V(\theta)-h_U(\theta)]^2,\qquad
\eta_n=\sqrt{a_n}+1/n.
\]

Choose \(U_n\in\mathcal G_n\) maximizing
\(F_n(V)=P_n(V)-\eta_nD_n(V,U)^2\). The circumscription comparison has
zero penalty, whereas
\(P_n(U_n)\le\mathcal P_\alpha(U)+a_n\). Therefore

\[
D_n(U_n,U)^2\le a_n/\eta_n\longrightarrow0.
\tag{PS.9}
\]

All these supports are uniformly bounded and Lipschitz in angle.
Every Hausdorff subsequential limit must have the same support as
\(U\): otherwise a support difference on an open angular interval
would give a fixed positive lower bound in the independent dense-grid
part of PS.9. Thus

\[
U_n\longrightarrow U,\qquad W_n\ge1\quad\hbox{eventually}.
\tag{PS.10}
\]

The artificial vertical sides are consequently inactive for all large
\(n\). No finite cap is required to have an affine middle roof.

## 3. The finite measures and the terminal atom

For each non-axis, non-top \(\theta\in\Gamma_n\), let
\(\ell^{\rm wing}_{n,\theta}\) be its outer facet length above the
charged exterior. Let \(\tau_{n,\theta}\) be the total arclength of
the positive graph of \(q_{n,U_n}\) inside \(J_n\) carried by its
source line, if that normal is used in PS.6, and put it equal to zero
for all other normals.

The terminal first source \(\alpha\) is used. The companion
\(L+\alpha\) is not used: even if its quadrant is included redundantly,
the whole first wall dominates that minimum. Distinct finite source
lines have distinct slopes, so intersections do not contribute
positive arclength and each graph segment has an unambiguous source.

At a positive floating facet, moving its supporting line outward by
\(\varepsilon\) leaves every other sampled support and the horizontal
projection unchanged. The outer first variation is its charged facet
length. The barrier first variation is its positive exposed source
length, including the whole terminal wall when \(\theta=\alpha\).
Finitely many line intersections and window endpoints contribute only
\(O(\varepsilon^2)\). Penalized maximality gives

\[
\ell^{\rm wing}_{n,\theta}\le\tau_{n,\theta}+b_{n,\theta},
\qquad b_{n,\theta}=4B\eta_nw_{n,\theta},\qquad
\beta_n:=\sum_\theta b_{n,\theta}\le4B\eta_n\to0.
\tag{PS.11}
\]

If the facet has zero length, the inequality is automatic; no
derivative of an inactive support coordinate is asserted. The same
formula applies to an outer-only normal with \(\tau=0\).

### 3.1 Every nonterminal source has exposure of order the mesh

Fix \(1\le j<n\). Its two paired neighbors are \(t_j\pm\delta_n\),
with their two companion normals. The neighbor at zero has no quadrant
above the floor, while the neighbor at \(\alpha\) is contained in
the whole terminal constraint. Thus any exposed point of the source
at \(t_j\) avoids both neighboring open quadrants. The four-line
calculation WR.1 applies without change.

With extra outer normals present, the expression appearing in that
calculation is the **circumscribed** facet length

\[
L^{\rm circ}_{n,j}
=\frac{h_n(t_j-\delta_n)+h_n(t_j+\delta_n)
-2\cos\delta_n\,h_n(t_j)}{\sin\delta_n}\ge0.
\tag{PS.12}
\]

It need not equal the actual facet length. Its nonnegativity follows
by evaluating both neighboring supports at a support point for
\(t_j\). WR's two parameter intervals consequently give

\[
\tau_{n,t_j}\le(6B+4)\delta_n+
\bigl(2\tan(\delta_n/2)-L^{\rm circ}_{n,j}\bigr)_+
\le K\delta_n,\qquad K=6B+6.
\tag{PS.13}
\]

Interchanging the two local normal families and reversing the local
triple gives the same estimate at \(L+t_j\). This is a symmetry of
the four-line geometric calculation, not an invariance of
\(\mathcal P_\alpha\) under horizontal reflection.

The terminal first wall instead has the elementary bound

\[
0\le\tau_{n,\alpha}\le |J_n|/\sin\alpha\le R/\sin\alpha.
\tag{PS.14}
\]

It may retain a genuine atom. No order-mesh estimate is claimed for it.

Define

\[
\nu_n=\sum_{\theta\ne0,L,\pi}\tau_{n,\theta}\delta_\theta,
\qquad
\omega_n=\sum_{\theta\ne0,L,\pi}
\ell^{\rm wing}_{n,\theta}\delta_\theta.
\tag{PS.15}
\]

These have joint weak subsequences. PS.11–PS.14 show that every limit
satisfies \(0\le\omega\le\nu\), and that

\[
\nu=\rho_R(\theta)\mathbf1_{(0,\alpha)}\,d\theta
+\rho_L(\theta)\mathbf1_{(L,L+\alpha)}\,d\theta
+\tau_\alpha\delta_\alpha,
\qquad 0\le\rho_R,\rho_L\le K.
\tag{PS.16}
\]

In particular there is no atom at \(0,L,L+\alpha,\pi\), nor any
measure in an unused open arc. In this section \(\omega\) is a weak
limit; Section 6 identifies it with the actual charged wing measure.

## 4. Endpoint complementarity, including zero end faces

Use the finite counterparts of PS.2. If \(e_{n,R}>0\), moving the
right axis constraint outward by \(\varepsilon\) changes the actual
endpoint by \(\varepsilon\), keeps every sampled non-axis support
fixed, and hence keeps the finite barrier fixed as a function of
\(x\). Differentiating the exterior integral and the moving middle
window gives \(e_{n,R}-C_{n,R}\). Thus

\[
e_{n,R}\le(C_{n,R}+b_{n,0})_+,\qquad
e_{n,L}\le(C_{n,L}+b_{n,\pi})_+.
\tag{PS.17}
\]

The positive parts are essential. When \(e_{n,R}=0\), some retained
sloping upper halfplane with positive horizontal normal meets the
floor at \((r_n,0)\). That halfplane and the floor already prohibit
\(x>r_n\), so relaxing the vertical bound changes no body or window.
The left endpoint has the corresponding direct argument. No
positive-face equation is used at a zero face.

For the opposite inequality, actually trim a cap at its right end:

\[
U^-_\varepsilon=U\cap\{x\le r-\varepsilon\},\qquad0<\varepsilon<W.
\]

Its projection is \([l,r-\varepsilon]\), its retained roof is the
old roof, and all supports, including the terminal support, decrease.
Its barrier is therefore at most the old barrier. Concavity gives

\[
d_H(U^-_\varepsilon,U)
\le\varepsilon\sqrt{1+(W-\varepsilon)^{-2}}.
\tag{PS.18}
\]

Indeed, compare a removed point with its vertical truncation at
\(r-\varepsilon\). Any required vertical change is bounded by the
horizontal change divided by \(W-\varepsilon\), using the secant
from the left endpoint and \(0\le A\le1\).

Keep the old finite barrier on the new middle window as an upper
comparison. The two window endpoints move by
\(-\varepsilon/4,-3\varepsilon/4\), yielding

\[
P_n(U^-_\varepsilon)-P_n(U_n)
\ge\varepsilon(C_{n,R}-e_{n,R})+o(\varepsilon).
\tag{PS.19}
\]

Trimming is admissible in the grid-polygon class: it only changes an
axis halfplane, and the resulting polygon may be rerecorded at its
actual supports. The squared-support penalty changes by at most
\(4B\eta_nd_H\). As \(W_n\ge1\), PS.18 is at most
\(\sqrt5\varepsilon\) for \(\varepsilon\le1/2\). The direct left
trim has window motions \(3\varepsilon/4,\varepsilon/4\) and gives
the analogous inequality. Hence, with \(d_n=4\sqrt5B\eta_n\),

\[
e_{n,R}\ge C_{n,R}-d_n,\qquad e_{n,L}\ge C_{n,L}-d_n.
\]

Together with nonnegativity and PS.17 this proves

\[
-d_n\le e_{n,Q}-(C_{n,Q})_+\le b_{n,\mathrm{axis}(Q)},
\qquad Q=R,L.
\tag{PS.20}
\]

### 4.1 The end-face lengths actually converge

Hausdorff convergence alone is insufficient for this step. At every
point of \(J_n\), its distance from both projection endpoints is at
least \(W_n/4\ge1/4\). Concavity bounds all roof slopes there by
\(4\) in absolute value. Thus facets sufficiently close to either
horizontal axis normal have zero middle length.

Choose \(0<a<\min\{\arctan(1/4),L-\alpha\}\). On the right arc
\((0,a)\), PS.11 and PS.13 give total floating facet length at most
\(K(a+\delta_n)+\beta_n\). On \((\pi-a,\pi)\) there is no used
source at all, so its total floating length is at most \(\beta_n\).
The weaker common bound \(K(a+\delta_n)+\beta_n\) suffices on both.

The full surface-area measures \(\sigma_n=h_n+h_n''\) converge weakly
to \(\sigma=h+h''\). Downward caps have no measure in the lower
open arcs adjoining the horizontal axes. Hence

\[
\sigma_n(\{0\})=e_{n,R},\qquad
\sigma_n((-a,a))\le e_{n,R}+K(a+\delta_n)+\beta_n.
\]

Portmanteau for the singleton gives \(\limsup e_{n,R}\le e_R\).
For the open arc it gives

\[
e_R\le\sigma((-a,a))\le\liminf_n\sigma_n((-a,a))
\le\liminf_ne_{n,R}+Ka.
\]

Let \(a\downarrow0\). Thus \(e_{n,R}\to e_R\), and the direct left
argument gives \(e_{n,L}\to e_L\).

Concave roofs converge uniformly near the strictly interior middle
endpoints. The finite barriers converge uniformly to \(q\), by
PS.8 and PD continuity. The projection and window endpoints also
converge. Therefore \(C_{n,Q}\to C_Q\), and PS.20 yields the exact
preliminary endpoint law

\[
\boxed{e_R=(C_R)_+,\qquad e_L=(C_L)_+.}
\tag{PS.21}
\]

The roof is positive at both interior middle endpoints of this
positive-area cap. Thus
\(C_R+C_L=(Q_-+Q_+)/2>0\).

## 5. Horizontal erosion and the exact source defects

The right horizontal erosion is

\[
E^R_\varepsilon=U_n\cap(U_n-\varepsilon e_x).
\]

Its projection is \([l_n,r_n-\varepsilon]\), its roof is
\(\min\{A_n(x),A_n(x+\varepsilon)\}\), and for every unit normal
\(v\),

\[
h_{E^R_\varepsilon}(v)\le h_{U_n}(v)-\varepsilon(v_x)_+.
\tag{PS.22}
\]

This is an upper bound, not an asserted support equality. Uniform
Hausdorff control follows without an interior ball: set
\(\lambda=\varepsilon/W_n\). For \(p\in U_n\), the points

\[
z=(1-\lambda)p+\lambda(l_n,0),\qquad
z+\varepsilon e_x=(1-\lambda)p+\lambda(r_n,0)
\]

both belong to \(U_n\). Hence \(z\in E^R_\varepsilon\), and

\[
d_H(E^R_\varepsilon,U_n)
\le\frac{\operatorname{diam}U_n}{W_n}\varepsilon.
\tag{PS.23}
\]

For a fixed finite cap use the virtual sampled supports
\(\widehat h(\theta)=h_n(\theta)-\varepsilon(\cos\theta)_+\).
Their max/min barrier dominates the actual eroded barrier by PS.22,
whether or not these virtual values are themselves a support function.
All first sources move inward, **including the whole terminal source
at \(\alpha\)**; no second source moves. On the fixed old window,
the exact finite graph variation is

\[
\int_{J_n}\widehat q_{n,\varepsilon}
=\int_{J_n}q_n
-\varepsilon\sum_{0<\theta<L}\tau_{n,\theta}\cos\theta
+o(\varepsilon).
\tag{PS.24}
\]

The finite graph has distinct nonhorizontal source slopes. Each
relative segment interior contributes normal displacement times
arclength; finitely many intersections, floor contacts, and window
endpoints give only \(O(\varepsilon^2)\). The limit
\(\varepsilon\downarrow0\) is taken with \(n\) fixed.

At almost every fixed abscissa the outer roof derivative under right
erosion is \(\min\{0,A_n'(x)\}\). Its charged integral is
\(-\sum_{0<\theta<L}\ell^{\rm wing}_{n,\theta}\cos\theta\),
where outer-only facets are included. Include the removed end sliver
and both moving-window terms. Define

\[
D_{n,R}=\sum_{0<\theta<L}
(\tau_{n,\theta}-\ell^{\rm wing}_{n,\theta})\cos\theta,
\]
\[
D_{n,L}=\sum_{L<\theta<\pi}
(\tau_{n,\theta}-\ell^{\rm wing}_{n,\theta})(-\cos\theta).
\tag{PS.25}
\]

One obtains

\[
P_n(E^R_\varepsilon)-P_n(U_n)
\ge\varepsilon(D_{n,R}-e_{n,R}+C_{n,R})+o(\varepsilon).
\]

The direct left erosion \(U_n\cap(U_n+\varepsilon e_x)\) tightens
virtual supports by \(\varepsilon(-\cos\theta)_+\). Its projection
is \([l_n+\varepsilon,r_n]\), and the same calculation gives the
left counterpart. These are two direct variations of the original
partial objective; no reflected-objective equality is used.

Erosions remain grid polygons. Their penalty error is bounded using
PS.23. For a fixed diameter bound \(D_0\), maximality and PS.11 imply

\[
-\beta_n\le D_{n,Q}
\le e_{n,Q}-C_{n,Q}+4BD_0\eta_n,\qquad Q=R,L.
\tag{PS.26}
\]

There is also an exact slope balance. Integrating the finite positive
barrier graph, including its terminal segments, gives

\[
\sum_\theta\tau_{n,\theta}\cos\theta
=q_n(j_{n,-})-q_n(j_{n,+}).
\]

Integrating the charged outer slopes gives

\[
\sum_\theta\ell^{\rm wing}_{n,\theta}\cos\theta
=e_{n,L}-e_{n,R}+A_n(j_{n,+})-A_n(j_{n,-}).
\]

Floor segments contribute zero, and top segments have zero cosine.
Subtracting, and using the definitions of the two pressures, yields

\[
\boxed{D_{n,R}-D_{n,L}
=(e_{n,R}-C_{n,R})-(e_{n,L}-C_{n,L}).}
\tag{PS.27}
\]

Let \(D_R,D_L\) be the cosine-weighted moments of the nonnegative
weak defect \(\nu-\omega\) on the corresponding quarters. Passing to
the limit in PS.26–PS.27 and using PS.21 gives

\[
0\le D_Q\le(-C_Q)_+,\qquad
D_R-D_L=(-C_R)_+-(-C_L)_+.
\]

At least one pressure is strictly positive. Its defect is zero, and
the difference identity fixes the other defect exactly. Thus

\[
\boxed{D_R=(-C_R)_+,\qquad D_L=(-C_L)_+.}
\tag{PS.28}
\]

Whenever a pressure is nonnegative, its entire quarter defect vanishes.
For the first quarter the cosine is positive even at the retained
terminal atom. For the second quarter it is strictly negative off
the top normal, and PS.16 excludes an atom at that zero-weight endpoint.

## 6. The limiting outer measure is the actual charged wing measure

This identification concerns the convex outer graph only. Test
\(\omega_n\) against a continuous angular function \(\varphi\)
supported away from the axes and the top normal. On each interior
spatial interval the concave roofs converge uniformly and their
derivatives converge almost everywhere. The graph integrand is

\[
\varphi\bigl(\arg(-A_n'(x),1)\bigr)
\sqrt{1+(A_n'(x))^2}.
\tag{PS.29}
\]

It is uniformly bounded: the angular cutoff removes arbitrarily
steep slopes. Dominated convergence applies. Shrinking spatial strips
at the moving projection endpoints contribute nothing, and the strips
at the moving \(J_n\) endpoints have uniformly bounded slopes as
well. This proves equality with the actual charged wing measure away
from the omitted normals. The terminal angle \(\alpha\) is not
omitted, so its actual facet mass is identified by the same argument.

PS.11 and PS.13 exclude concentration of floating wing mass at the
axes. They also exclude it at the top: on one side of the top the
nearby first normals are unused, and on the other side the companion
grid bound is \(K\delta_n\). For a sufficiently small top arc its
floating charged mass is at most \(K(a+\delta_n)+\beta_n\), which
vanishes as \(a\downarrow0\). Consequently the weak measure in
PS.16 is exactly the actual \(\omega\) specified in Section 1.

No analogous passage from finite source arclength to continuum
positive-graph arclength is used.

## 7. The actual 45-degree relaxation makes both pressures positive

Define the one-angle relaxation

\[
P_{45}(U)=\int_{I\setminus J}A-
\int_J\bigl[\min\{R_{\pi/4},S_{\pi/4}\}\bigr]_+.
\]

For every \(\alpha\ge\pi/4\),
\(\mathcal P_\alpha(U)\le P_{45}(U)\): the angle is visited when
\(\alpha>\pi/4\), and at equality its two-wall minimum is dominated
by the whole outgoing wall. The auxiliary \(P_{45}\) is horizontally
reflection invariant, since reflection exchanges its two 45-degree
supports. No reflection invariance of \(\mathcal P_\alpha\) is needed.

The proof of LH.2–LH.17 in
[the low-height proof](gate1-global-positive-pressure-and-wing-identity.md)
in fact estimates this exact one-angle relaxation. Its sole niche
lower bound is the displayed 45-degree tent. Thus it gives the
following partial-objective consequence for **either** middle tilt:

\[
\boxed{\min(A_-,A_+)\le\tfrac12,
\quad\max(A_-,A_+)=1
\quad\Longrightarrow\quad
\mathcal P_\alpha(U)<\frac{31233}{39200}<\frac45.}
\tag{PS.30}
\]

For clarity, the exact scalar bounds behind this transfer are as
follows. Compute the reflection-invariant relaxation with the high
endpoint on the right, \(I=[-2C,2C]\), \(J=[-C,C]\). Concavity gives
exterior reward at most \(11C/8\). When \(C\ge1/2\), put

\[
\max_U(x+y)=2C+u,\quad \max_U(-x+y)=2C+v,
\quad \max(0,1-C)\le u\le1,\quad0\le v\le1/4.
\]

The charged reward is at most
\(11C/8-(1-u)^2/2-(1/4-v)^2/2\). For
\(1/2\le C\le23/20\), the genuine 45-degree tent integral is at least
\(H_+^2-Z_+^2/2\), where

\[
H=2C+(u+v)/2-\sqrt2,\qquad Z=C+u-\sqrt2.
\]

In the \(Z\le0\) case, completing squares bounds the resulting
relaxation by \(11\sqrt2/16-99/512\). In the \(Z>0\) case,
its derivative in \(u\) is \(1-C-(u+v)/2\); its maximum is either
the already covered boundary or \(u=2-2C-v\), whose value is at most
\(31/32-\sqrt2/8\). Both are below \(31233/39200\).
For \(C\ge23/20\), the baseline tent gives the decreasing upper bound
\(11C/8-(2C-\sqrt2)^2\) up to \(C=\sqrt2\), followed by
\((11/8+2\sqrt2)C-3C^2\). At \(C=23/20\) this is strictly less than
\(31233/39200\), using \(\sqrt2<99/70\). Finally \(C\le1/2\)
has exterior reward at most \(11/16\). These are precisely the
one-angle estimates, independent of all later visited angles.

The maximizing value is at least the full-turn reference
\(M/2>41/50\), so both middle endpoints exceed \(1/2\); one equals
one by top localization and middle affinity. A side whose middle
endpoint equals one has strictly positive pressure: if, for example,
\(Q_+\ge1\) and \(C_R\le0\), then \(Q_-\ge3Q_+\), and PS.21 gives
\(e_L=C_L\ge2Q_+\ge2\), impossible. If the other pressure were
nonpositive, then \(Q_+\ge3Q_-\) and
\(1\ge e_R=C_R\ge2Q_-\), forcing \(A_-\le Q_-\le1/2\), again
impossible. Interchanging the labels proves the other orientation.

Thus both pressures are strictly positive. PS.21 and PS.28 prove
PS.3–PS.4, including equality of the terminal first atoms.

### 7.1 Pinning the middle facet, without discarding a terminal atom

The middle facet has no charged extension. If its normal is neither
the top nor \(\alpha\), PS.16 and \(\omega\le\nu\) already exclude
a charged atom there. If its normal is \(\alpha\), its supporting
line agrees with \(A\) throughout \(J\), so

\[
R_\alpha(x)=A(x)-\csc\alpha\le1-\csc\alpha<0\qquad(x\in J).
\]

Uniform convergence makes the finite terminal line strictly negative
on \(J_n\) for all large \(n\). Hence its limiting source atom is
zero, and so is its charged outer atom. The horizontal case may of
course have a charged top overhang. In particular every nonhorizontal
middle facet is pinned to the two endpoints of \(J\).

The whole upper curvature measure therefore has bounded density on
the visited arcs, together with at most the uncharged middle-facet
atom, the top atom, and a charged first terminal atom. A missing-arc
central atom is retained as uncharged geometry.

### 7.2 The sharper geometric wing bound on the visited arcs

Write \(f(t)=h_U(\mu_t)\), \(g(t)=h_U(\nu_t)\), and define the
source arms, distinct from the spatial barrier \(q(x)\), by

\[
p(t)=f'(t)-g(t)+1,\qquad q_{\rm arm}(t)=g'(t)+f(t)-1,
\qquad \kappa(z)=\max\{|z|,(1+|z|)/2\}.
\]

At almost every \(0<t<\alpha\) away from the central-facet source
angle, the actual wing densities satisfy

\[
\boxed{0\le u(t):=f''(t)+f(t)\le\kappa(q_{\rm arm}(t)),\qquad
0\le v(t):=g''(t)+g(t)\le\kappa(p(t)).}
\tag{PS.30a}
\]

No bound is asserted on the terminal atom. The displayed densities
refer to the regular parts, and the central atom is kept separately.

To verify the transfer, use the sharper algebraic version of WR.1
from [WR, Section 4](one-turn-weighted-regularity.md). At an interior
first source it gives

\[
\tau_{n,t_j}\le
\tan\delta_n\bigl(|q^+_{n,j}|+\tan(\delta_n/2)\bigr)
+\bigl(2\tan(\delta_n/2)-L^{\rm circ}_{n,j}\bigr)_+,
\]

where

\[
q^+_{n,j}=f_n(t_j)+
\frac{g_n(t_j+\delta_n)-\cos\delta_n\,g_n(t_j)}{\sin\delta_n}-1.
\]

The actual total facet length \(\ell_{n,t_j}\) is at most
\(L^{\rm circ}_{n,j}\), since additional outer constraints can only
shorten that circumscribed facet. Replacing the last positive part
by the larger one using \(\ell_{n,t_j}\), and combining with
\(\ell_{n,t_j}\le\tau_{n,t_j}+b_{n,t_j}
+\ell^{\rm mid}_{n,t_j}\), yields

\[
\ell_{n,t_j}\le\kappa(q^+_{n,j})\delta_n+K_2\delta_n^2
+b_{n,t_j}+\ell^{\rm mid}_{n,t_j}.
\tag{PS.30b}
\]

For \(\ell_{n,t_j}\ge2\tan(\delta_n/2)\) the positive part
vanishes and gives the \(|q^+|\) branch. Otherwise move the
\(-\ell_{n,t_j}\) term to the left to obtain the
\((1+|q^+|)/2\) branch. Uniform support and angular Lipschitz bounds
make \(K_2\) independent of the index and mesh.

On every compact normal arc avoiding the central normal, the middle
length term sums to zero in the limit: concavity makes all slopes on
strict subintervals of the limiting affine middle converge to that
middle slope, while the remaining endpoint strips have arbitrarily
small arclength. The penalty terms also sum to zero. Uniform support
convergence and semiconvexity give convergence of the nearby one-sided
support secants to the limiting derivative at differentiability
points; their uniform boundedness gives the corresponding local
\(L^1\) convergence. Since \(\kappa\) is Lipschitz, summing PS.30b
and passing to the limit proves the first density bound in PS.30a.
The same two-family local calculation gives the second bound with
\(p\). No horizontal reflection of the objective is used.

## 8. The stationary clipped Green identity

Put \(O=\int_{I\setminus J}A\) and \(N=\int_Jq\). Along an actual
outer upper graph segment with outward normal \(\theta\),

\[
h(\theta)\,ds=(A-xA')\,dx.
\]

Integrating the two wings and separating their height-one top pieces
gives

\[
2O=\int h\,d\omega+T_{\rm wing}
+r e_R-l e_L+j_-A_--j_+A_+.
\tag{PS.31}
\]

For each finite positive source segment, including a terminal first
segment, the supporting line instead has signed support distance
\(h_n(\theta)-1\), and

\[
(h_n(\theta)-1)\,ds=(q_n-xq_n')\,dx.
\]

Summing all its positive segments inside \(J_n\) yields the exact
finite graph identity

\[
2\int_{J_n}q_n
=\int(h_n-1)\,d\nu_n
-j_{n,-}q_n(j_{n,-})+j_{n,+}q_n(j_{n,+}).
\tag{PS.32}
\]

The supports and barriers converge uniformly, the endpoints converge,
and the bounded source measures converge weakly with the terminal
atom included. Thus

\[
2N=\int(h-1)\,d\nu-j_-q_-+j_+q_+.
\tag{PS.33}
\]

Using \(\nu=\omega\), subtract PS.33 from PS.31:

\[
2\mathcal P_\alpha(U)
=L_{\rm wing}+r e_R-l e_L+j_-Q_--j_+Q_+.
\]

The definitions of the middle window and pressures give exactly
\(j_-Q_--j_+Q_+=lC_L-rC_R\). PS.3 cancels all boundary terms and
proves the first identity in PS.5. Both the terminal facet and any top
overhang are counted once; the vertical end faces are excluded from
\(L_{\rm wing}\).

For the height bound put \(S=A_-+A_+\), \(E=e_R+e_L\), and
\(Z=q_-+q_+\). Because the top meets \(J\), each charged wing is
monotone toward its middle endpoint. Hence

\[
\int|\cos\theta|\,d\omega=S-E.
\]

The finite barriers satisfy
\(\operatorname{TV}_{J_n}(q_n)=\int|\cos\theta|\,d\nu_n\).
Uniform convergence, lower semicontinuity of total variation, and
PS.4 give \(\operatorname{TV}_J(q)\le S-E\). The endpoint equations
give \(E=(S+Z)/2\), while continuity gives
\(2\max_Jq-Z\le\operatorname{TV}_J(q)\). Combining them proves
\(\max_Jq\le E/2\), the second part of PS.5.

## 9. A fixed-angle terminal occupation measure

There is a useful spatial form of the terminal atom, with its precise
scope. Let

\[
n_\alpha(x)=\max\{0,\sup_{0<t<\alpha}\min(R_t,S_t)\},
\quad E_\alpha=\{x\in J:R_\alpha(x)>n_\alpha(x)\},
\]
\[
H_\alpha=\{x\in J:R_\alpha(x)=n_\alpha(x)\}.
\]

For a finite selection let \(\chi_n\) be the indicator of the
positive part of the finite graph carried by its whole terminal
first line, extended by zero outside \(J_n\). Finite ties between
distinct source lines occur at only finitely many points, so they do
not affect this definition. Since \(0\le\chi_n\le1\), take a
weak-star subsequence in \(L^\infty([-R,R])\), with limit \(\chi\).
Uniform convergence of the histories and terminal lines gives

\[
0\le\chi\le1,\qquad
\chi=1\ \hbox{a.e. on }E_\alpha,\qquad
\chi=0\ \hbox{a.e. outside }E_\alpha\cup H_\alpha.
\tag{PS.34}
\]

There is no mass at a zero-height terminal contact: \(\alpha<L\)
makes \(R_\alpha\) a nonhorizontal line, so its zero set is at most
one abscissa. If \(m\) is the horizontal projection length of the
charged outer terminal facet, then PS.4 gives

\[
\boxed{\int_J\chi(x)\,dx
=\sin\alpha\,\nu(\{\alpha\})
=\sin\alpha\,\omega(\{\alpha\})=m.}
\tag{PS.35}
\]

Indeed each finite terminal source length equals
\(\int\chi_n/\sin\alpha\); the nonterminal density bound excludes
concentration of adjacent sources into the terminal atom, so the
limit is exactly its atom in PS.16. The occupation \(\chi\) may be
fractional on a positive-length historical tie set, and need not be
uniquely determined there.

### 9.1 Terminal-only historical ties have full occupation

Partition the positive part of \(H_\alpha\) into \(H_{\rm old}\),
where some actual angle \(t<\alpha\) attains
\(\min(R_t,S_t)=R_\alpha\), and \(H_{\rm new}\), where only the
limiting endpoint angle attains that height. Then the same occupation
constructed above satisfies

\[
\boxed{\chi=1\quad\hbox{a.e. on }E_\alpha\cup H_{\rm new}.}
\tag{PS.36}
\]

Older historical ties still permit fractional occupation. The proof
uses the absence of concentration in the nonterminal source measures.

Fix a compact subset \(H_0\subset H_{\rm new}\) and a small
\(\eta>0\). The terminal height has a positive minimum on \(H_0\).
Every older angle \(t\le\alpha-\eta\) has a strict two-wall gap there.
This gap is uniform: use continuity on a closed angular interval away
from zero, and the uniform small-angle bound to cover the remaining
tail. Uniform support and barrier convergence preserve the gap for the
finite selections. Thus, for all large \(n\), every positive finite
graph piece over \(H_0\) is either the whole terminal line or comes from
a paired source angle in \((\alpha-\eta,\alpha)\).

PS.13 bounds the total arclength of both nonterminal source families
in this angular interval by \(2K(\eta+\delta_n)\). Their horizontal
projections have no greater length. Therefore

\[
\int_{H_0}(1-\chi_n(x))\,dx\le2K(\eta+\delta_n)
\quad\hbox{for all large }n.
\tag{PS.37}
\]

Take the weak-star limit, then let \(\eta\downarrow0\). This gives
\(\chi=1\) almost everywhere on \(H_0\). Lebesgue inner regularity
exhausts the measurable set \(H_{\rm new}\) by compact subsets for
this purpose, proving PS.36. No convergence of terminal one-sided
support derivatives, curvature cap, or ordered contact chart is
required.

PS.35 is the fixed-angle mass balance. A first spatial moment or a
shared occupation for a simultaneous terminal-facet offset and angle
rotation is an additional theorem. It cannot be obtained by silently
assigning zero or full terminal occupation to \(H_{\rm old}\), nor
by applying an angle derivative to finite selections that were
optimized only at the fixed angle. No such extra stationarity is
claimed here.

## 10. Scope of this checkpoint

This proof supplies the partial counterpart of the endpoint/source
dependency needed before a sharp terminal argument: positive end
pressures, exact charged source equality with its permitted terminal
atom, a pinned nonhorizontal middle facet, and the full stationary
wing-length and height identities. Both middle tilt orientations are
included by direct fixed-angle variations. The universal value
\(\mathcal P_\alpha\le M/2\) and the terminal angle/shape interaction
require the additional arguments assembled in [the Gate 2 closure](gate2-sharp-partial-turn-closure.md).
