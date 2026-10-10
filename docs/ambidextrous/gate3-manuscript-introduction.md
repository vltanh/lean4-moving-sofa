# Sharp area and exact uniqueness for the ambidextrous moving sofa problem

## Abstract

We study compact connected planar bodies that negotiate both unit-width
right-angle corridors from a common incoming orientation. The two
motions may rotate nonmonotonically and may initially be specified with
independently incomplete terminal turns. If \(Y>0\) solves
\(4Y^3+3Y-1=0\), we prove
\[
|S|\le M:=1+4Y^2+\arctan Y.
\]
Equality holds exactly for bodies congruent to Romik's ambidextrous
construction. It forces the actual reference hull, unit incoming height,
and complete correct-handed angular reach for each corridor passage.

The proof charges each cap's two exterior quarters and its positive
moving-wall barrier on the middle half. For a partial turn this barrier
includes the whole first wall of the actual outgoing strip. The resulting
cap score is at most \(M/2\), with strict inequality at every proper
terminal angle. A nonnegative two-cap deficit recovers the original
equality hull. An exact extrusion deficit reverses cap canonicalization,
and regular closedness gives literal equality of compact bodies.

The ordinary one-turn area theorem, with a stated rational enclosure
of Gerver's area, is an explicit external input. It is used only after
a genuine feasible one-turn body has been constructed, and only in
strict branch exclusions. Its equality case is not assumed.

This is a written research proof with separate mathematical checks
within the research session. External refereeing and Lean-kernel
verification remain outstanding. The integrated argument and the
essential domestic proofs are included in this document. The technical
chapters supply the longer source-measure and exact inequality proofs.

## 1. Motion domain and theorem

Use the unit corridor
\[
\mathcal H=
((-\infty,1]\times[0,1])
\cup([0,1]\times(-\infty,1])
\]
and its reflection in \(y=1/2\). A passage is a continuous path of
proper rigid motions beginning with the body entirely in the incoming
horizontal arm and ending entirely in the outgoing arm. The two
initial translations may differ, but their incoming body orientation
is common. One global proper rigid change of coordinates puts that
orientation in \(\mathbb R\times[0,1]\).

The definition allows pauses, backtracking, and independent terminal
rotations. Connectedness is a condition on the physical compact set.
The original-motion chapter derives the usable angular intervals and
the actual whole-body terminal strips without replacing the body.

Put
\[
L=\pi/2,\quad 4Y^3+3Y-1=0,\quad Y>0,\quad
\beta_*=\arctan Y,\quad
m_*=\frac1{3\sin\beta_*},\quad C_*=\frac{m_*}{2}.
\tag{MS.1}
\]
The polynomial is strictly increasing on \([0,\infty)\). Evaluating it
at \(2/7\) and \(3/10\) gives
\[
2/7<Y<3/10<1/3.
\tag{MS.2}
\]
Let \(\Sigma_*\) be the explicit reference body below and
\(K_*=\operatorname{conv}\Sigma_*\).

**Main theorem.** Every compact connected body in this two-motion
domain satisfies
\[
\boxed{|S|\le M=1+4Y^2+\arctan Y.}
\tag{MS.3}
\]
Equality holds if and only if \(S\) is congruent to \(\Sigma_*\).
An equality body's normalized actual hull is \(K_*\); its two
correct-handed canonical terminal magnitudes are \(L\).

This classifies bodies and necessary angular reach. Waiting, time
reparametrization and additional translations within a straight arm
give nonunique witnesses even for the same body.

## 2. The scalar theorem and exact original-body partition

Let \(U\) be a nonempty compact convex downward cap in the unit strip:
every nonempty vertical fiber is an interval starting at zero.
Write \(I=[l,r]\), \(W=r-l\), \(A_U\) for its projection, width and
roof, and
\[
J=[l+W/4,r-W/4].
\tag{MS.4}
\]
For \(\mu_t=(\cos t,\sin t)\), \(\nu_t=(-\sin t,\cos t)\), define
\[
R_{U,t}(x)=\frac{h_U(\mu_t)-1-x\cos t}{\sin t},\qquad
D_{U,t}(x)=\frac{h_U(\nu_t)-1+x\sin t}{\cos t}.
\tag{MS.5}
\]
The actual partial barrier for \(\pi/4\le\alpha<L\) is
\[
N_{U,\alpha}(x)=
\max\{0,\sup_{0<t<\alpha}\min(R_{U,t}(x),D_{U,t}(x)),R_{U,\alpha}(x)\}.
\tag{MS.6}
\]
The last term is the whole outgoing wall. At \(\alpha=L\) use the
full positive niche \(n_U\); the limiting terminal wall is nonpositive.

The scalar score is
\[
\mathcal P_\alpha(U)=
\int_{I\setminus J}A_U-\int_JN_{U,\alpha}.
\tag{MS.7}
\]
The full-turn and partial-turn chapters establish
\[
\boxed{\mathcal P_\alpha(U)\le M/2,\quad
\mathcal P_\alpha(U)=M/2
\Longleftrightarrow \alpha=L,\ U=U_*+(a,0).}
\tag{MS.8}
\]
Here \(U_*\) is the centered upper downward reference cap. The
quantifiers include arbitrary asymmetric, nonsmooth and subunit caps.

The upper and reflected-lower downward caps \(U,V\) of an actual hull
share \(I,J\). With independent angles \(\alpha,\gamma\), their
canonical signed fiber is
\[
\ell=1-\max(1-A_V,N_{U,\alpha})-\max(1-A_U,N_{V,\gamma}).
\tag{MS.9}
\]
It is at most \(1-N_{U,\alpha}-N_{V,\gamma}\) on \(J\), and at most
\(A_U+A_V-1\) on the complement. The constants cancel because the two
regions have equal length:
\[
\int_I\ell\le\mathcal P_\alpha(U)+\mathcal P_\gamma(V)\le M.
\tag{MS.10}
\]
Connectedness gives nonempty projected envelope fibers for the actual
body, so \(|S|\le\int_I\ell\). Auxiliary hulls may have negative signed
fibers; their assertion remains the signed inequality MS.10.

## 3. The explicit reference and its geometric properties

The included calibration chapter supplies the following exact
construction. Set \(s_*=\sin\beta_*\), \(c_*=\cos\beta_*\),
\[
A_*=\frac1{4s_*},\quad k=1-\frac43A_*=1-m_*,
\quad T_*=\frac32(\pi/4-\beta_*),\quad
\mathcal R=\frac{c_*}{\cos T_*}.
\]
On the successive intervals \([0,\beta_*]\),
\([\beta_*,L-\beta_*]\), \([L-\beta_*,L]\), define
\[
(f_*,g_*)=
\begin{cases}
(\cos t+\tfrac12\sin t,\
(2A_*-1)\sin t+\tfrac12\cos t+\tfrac12),\\
(\mathcal R\cos(t/2+\pi/8)+k\cos t+\tfrac12\sin t,\
\mathcal R\sin(t/2+\pi/8)-k\sin t+\tfrac12\cos t),\\
((1-\tfrac23A_*)\cos t+\tfrac12\sin t+\tfrac12,\
(\tfrac83A_*-1)\sin t+\tfrac12\cos t).
\end{cases}
\tag{MS.11}
\]
Set \(h_*(t)=f_*(t)\), \(h_*(t+L)=g_*(t)\) and
\(h_*(-t)=h_*(t)-\sin t\). Its centered version is
\(\bar h_*=h_*-k\cos t\). The identities
\[
\mathcal R\cos T_*=c_*,\qquad
\mathcal R\sin T_*=\frac1{3s_*}-s_*
\tag{MS.12}
\]
are proved by reducing the trigonometric matching equation with
\(4Y^3+3Y-1=0\). They give matching values and first derivatives.

The upper-quarter curvature densities on the same three intervals are
\[
(f_*''+f_*,g_*''+g_*)=
(0,1/2),\quad
(\tfrac34\mathcal R\cos(t/2+\pi/8),
 \tfrac34\mathcal R\sin(t/2+\pi/8)),\quad
(1/2,0).
\tag{MS.13}
\]
They are nonnegative and less than \(7/8\). The only additional
curvature atoms are the positive top and bottom face lengths.
The support-construction argument below gives a compact convex hull
with this support. Its centered top and bottom faces both have
interval \([-C_*,C_*]\).

For completeness, a piecewise smooth periodic function with
nonnegative curvature measure \(h+h''\) has the required support
interpretation. At a smooth angle put \(X=h\mu+h'\nu\).
Variation of constants gives, for angular distance at most \(\pi\),
\[
h(\phi)-X\cdot\mu_\phi
=\int_\theta^\phi\sin(\phi-t)\,d(h+h'')(t)\ge0.
\]
For reversed integration both orientation and sine are nonpositive.
One-sided derivatives give the limiting facet endpoints. Every such
point lies in all supporting halfplanes and attains the designated
support. Their intersection is a bounded nonempty convex body.
This proves the assertion also across the stated positive jumps.

The unit-curvature signed-roof theorem and the explicit reference
calculation AR3 show that the reference's positive niche is confined
to \(J_*=[-C_*,C_*]\) and vanishes at its endpoints. Since its roof is
one on \(J_*\) and its niche is zero outside \(J_*\), the spatial
score equals the weighted score \(\Psi\) there, and AR3 gives
\(P(U_*)=\Psi(U_*)=M/2\). These proofs, including the integral identity underlying
AR3, are included below. The direct corner calculation bounds every
quadrant's apex height by
\[
H_*=\frac12+\mathcal R-\sqrt2<\frac12.
\]
Indeed MS.12 gives \(\mathcal R^2=1/3+m_*^2\). Since \(Y>2/7\),
one has \(s_*^2>4/53\), hence
\[
\mathcal R^2<\frac13+\frac{53}{36}=\frac{65}{36}<2.
\]
A two-wall tent nowhere exceeds its apex, so \(0\le n_*<1/2\).

Define \(\Sigma_*\) by removing the two open canonical swept niches
from \(K_*\). On \(J_*\) its vertical fibers are
\([n_*(x),1-n_*(x)]\); outside \(J_*\) they are the unchanged convex
flank fibers. All are nonempty and contain the horizontal midline.
The niche is continuous by the angular-tail estimate proved in the
cap-domain chapter. Thus the interval fibers make \(\Sigma_*\)
compact and connected. The support-tightened corridors give both
complete feasible motions and their endpoint unit strips.

Every exterior flank survives, as do the horizontal face endpoints.
All supports are therefore still attained:
\[
\operatorname{conv}\Sigma_*=K_*.
\tag{MS.14}
\]
The middle roofs equal one and both niches vanish outside \(J_*\).
The spatial partition has zero remainder, so AR3 gives
\[
|\Sigma_*|=2P(U_*)=\cot\beta_*-2+\beta_*
=1+4Y^2+\arctan Y=M.
\tag{MS.15}
\]
The last equality follows by dividing the root equation by \(Y\).
This proves the matching lower bound using the actual reference body.

The same fiber description proves regular closedness. For an interior
projection point the two continuous bounding graphs are strictly
separated; each boundary point is a limit of interior points. Near
the horizontal extremes the niches are absent and the same property
holds for the convex flanks. Thus
\(\Sigma_*=\overline{\operatorname{int}\Sigma_*}\).
No regular-closedness assumption is imposed on competing bodies.

One useful strict numerical margin is entirely rational. If
\(a=297/1000\), then \(4a^3+3a<1\), so \(Y>a\). Integrating
\(1/(1+t^2)\ge1-t^2\) gives
\[
M>1+4a^2+a-a^3/3
=\frac{1641103309}{1000000000}>\frac{41}{25}>\sqrt2.
\tag{MS.16}
\]
Hence original bodies of area at most \(\sqrt2\) are already below
the target, before the angular reduction for larger bodies.

## 4. Equality mechanism and proof order

The scalar value proofs use height extrusion and the middle-chord
cut, followed by a finite source selection targeted to a prescribed
canonical global maximizer. The source-distance penalty is essential:
it later allows the same necessary conditions to be used for every
canonical equality cap, not merely one selected limit.

The full-turn proof controls its horizontal branch by a strictly
calibrated \(H^1\) functional and excludes every tilted branch. The
partial proof retains terminal facet mass and one-sided angle
derivatives with historical ties. Its weighted companion moment is
paid on two overlapping angle ranges.

At full-turn equality the calibration fixes the canonical cap.
If \(V\) was extruded by \(\varepsilon\) to that cap \(U_c\), then
\[
P(U_c)-P(V)=\int_J(\varepsilon-n_{U_c})_+\,dx.
\tag{MS.17}
\]
The reference niche vanishes at the middle endpoints, so equality
forces \(\varepsilon=0\). The strip ceiling then reverses the
middle-chord cut.

For a proper-angle equality pair, an overly long terminal facet
permits one fixed-cap angle extension preserving the score. Its
positive charged facet becomes an interior visited atom, forbidden
by the prescribed-cap source theorem. This supplies the additional
contradiction needed to upgrade the value proof's extremal-angle
selection to strictness for every individual proper-angle cap.

Finally the exact nonnegative body deficit fixes both original caps.
Their shared projection aligns them, recovering the actual hull.
Containment in the regular-closed reference envelope and equal area
then force equality of compact sets.

## 5. Notation and dependency conventions

Use \(L=\pi/2\), \(M\) for area, \(W\) for width, and \(I,J\) for
projection and middle half; centered local coordinates use \(W=4C\).
The reference half-width is \(m_*\), with \(C_*=m_*/2\).
On upper support quarters put
\[
p=f'-g+1,\qquad q=g'+f-1,\qquad u=f''+f,\quad v=g''+g.
\]
For endpoint pressure use instead
\[
Q_\pm=A(j_\pm)+N(j_\pm),\quad
C_R=(3Q_+-Q_-)/4,\quad C_L=(3Q_--Q_+)/4.
\]
The source proof establishes \(e_R=C_R>0\), \(e_L=C_L>0\).
The velocity \(q\) is not this combined endpoint datum.
Capital \(P,Q,U,V\) in a reflected local system are explicitly defined
there and do not denote the cap pair in that passage.

Technical equation labels AF, RG, PS, MP and so on are retained.
A numbered note mentioned there refers to an included proof chapter,
with the original number retained for unambiguous cross-reference.
Local propositions retain their hypotheses. A weighted-objective
stationarity theorem is not applied to a spatial-score maximizer;
only the geometric identities explicitly transferred or rederived
in the spatial proof are used.

## 6. Explicit external inputs

The ordinary one-turn input is
\[
|\mathcal S|\le G_0:=22199/10000
\tag{MS.18}
\]
for every nonempty compact connected body with a genuine continuous
passage through the unit right-angle corridor. We use Jineon Baek,
*Optimality of Gerver's Sofa*, Theorem 1.1.1,
[arXiv:2411.19826](https://arxiv.org/html/2411.19826v1),
together with the retained rational Gerver enclosure
\[
(7202+13340+8069-6013-30-369)/10000=22199/10000.
\]
The six existing component enclosures have explicit Gerver parameter
hypotheses. Their source declarations are identified in the included
full-turn closure dependency section. This is an external arithmetic
input; the manuscript does not claim to reprove Baek's theorem or
newly verify those Lean declarations. Its equality case is unnecessary.

The construction is attributed to Dan Romik, *Differential equations
and exact solutions in the moving sofa problem*, Experimental
Mathematics 27 (2018), 316--330,
[arXiv:1606.08111](https://arxiv.org/abs/1606.08111).
The formulas, feasible body, area and regular closedness used here
are proved in the included chapters.

Standard real and convex analysis facts used below include Blaschke
compactness, weak compactness in \(H^1\), dominated convergence, and
the support-curvature identity. Specialized moving-wall estimates,
source selections, endpoint balances, clipping identities and equality
recovery are supplied in the manuscript. The fixed arithmetic checkers
corroborate rational comparisons and do not replace the continuum proofs.
