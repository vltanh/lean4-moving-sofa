# Sharp area and exact uniqueness for the ambidextrous moving sofa problem

<a id="manuscript-guide"></a>
## Reading guide

This manuscript includes an integrated proof followed by the complete essential technical proof sections. The first five chapters give the theorem, original-motion reduction, full and partial cap arguments, and exact uniqueness. The subsequent chapters expose the source selections, calibration, geometric reductions and rational certificates in full.

Equation labels are local to their stated proof families. Component results retain their hypotheses and distinctions between geometric identities and stationarity for a particular objective. The main theorem and the final review record govern the manuscript's status.

The source-section manifest records exact input hashes and extraction boundaries. The assembly retains the selected proofs, restores explicit local definitions and hypotheses, and records every editorial replacement as well as heading and link changes.

A few pinned historical links give optional attribution or counterexample context. They are not mathematical premises: the required arguments are reproduced in the selected proof sections.

### Contents

- [Chapter 1: The theorem, construction and external inputs](#main-introduction)
- [Chapter 2: Original continuous motions and actual-hull reduction](#main-motions)
- [Chapter 3: Integrated full-turn value and equality proof](#main-full-turn)
- [Chapter 4: Integrated partial-turn and strict-angle proof](#main-partial-turn)
- [Chapter 5: Original equality caps, actual hull and exact body](#main-equality)
- [Technical proof 1: Reference matching, stationarity and exact value (Note 14)](#proof-reference-matching)
- [Technical proof 2: The exact global reference corner-height ceiling (Note 4)](#proof-reference-height)
- [Technical proof 3: The contact integral and its boundary identity (Note 13)](#proof-contact-identity)
- [Technical proof 4: The unrestricted H1 calibration and all equality cases (AF)](#proof-adaptive)
- [Technical proof 5: Unit-curvature signed-roof identity (SR)](#proof-signed-roof)
- [Technical proof 6: Support area, reference cap and local arm geometry (AR)](#proof-arm)
- [Technical proof 7: Neighboring-wall geometry and exact threshold identities (WR)](#proof-neighboring-walls)
- [Technical proof 8: Actual visible-source flux and its finite limit (VE)](#proof-visible-flux)
- [Technical proof 9: Full-cap height, width, continuity and attainment (SD)](#proof-full-domain)
- [Technical proof 10: The exact middle-chord and height reduction (MID)](#proof-middle-chord)
- [Technical proof 11: Finite exposure and the moving spatial window (FE)](#proof-finite-exposure)
- [Technical proof 12: Prescribed-cap approximation and wing regularity (RG)](#proof-prescribed-regularity)
- [Technical proof 13: Actual full-cap endpoint complementarity (EP)](#proof-full-endpoints)
- [Technical proof 14: Positive endpoint pressures, source balance and Green identity (LH)](#proof-full-pressures)
- [Technical proof 15: Pinning the affine middle facet (TF)](#proof-facet-pinning)
- [Technical proof 16: Spatial source curvature and the horizontal calibration (CH)](#proof-full-curvature)
- [Technical proof 17: Strict short-width horizontal bound (SW)](#proof-horizontal-short)
- [Technical proof 18: Complete horizontal width coverage and exact certificates (HW)](#proof-horizontal-complete)
- [Technical proof 19: Tilted short, wide and intermediate width exclusions](#proof-tilted-width)
- [Technical proof 20: The full three-triangle tilted width cut (FT)](#proof-full-triangle)
- [Technical proof 21: The tilted first-wing structure and projection](#proof-first-wing-structure)
- [Technical proof 22: Fractional occupations for folded sources](#proof-fold-occupations)
- [Technical proof 23: The two-unit-wing energy identities used in the first-wing argument](#proof-two-unit-wings)
- [Technical proof 24: The complete tilted first-unit-wing contradiction (GF)](#proof-first-unit)
- [Technical proof 25: The tilted initial-floor energy conditions (IE)](#proof-initial-energy)
- [Technical proof 26: Constructing a genuine feasible one-turn survivor (CG)](#proof-corner-confinement)
- [Technical proof 27: Forward curvature excess and endpoint leakage (ET)](#proof-early-excess)
- [Technical proof 28: Reflected tail and exact zero-height projection (RT)](#proof-reflected-projection)
- [Technical proof 29: The final tilted height reduction (FR)](#proof-final-height)
- [Technical proof 30: The last small-height alternatives (SH)](#proof-small-height)
- [Technical proof 31: Full-turn assembly and explicit external input record (G1C)](#proof-full-closure)
- [Technical proof 32: Actual partial-cap domain and used-support saturation (PD)](#proof-partial-domain)
- [Technical proof 33: Prescribed partial-cap source theorem and terminal mass (PS)](#proof-partial-sources)
- [Technical proof 34: Same-cap completion of the negative-tilt alternatives (NT)](#proof-negative-completion)
- [Technical proof 35: Exact one-sided angle derivatives with contact ties (TV)](#proof-angle-variation)
- [Technical proof 36: The all-width initial-angle certificate (AT)](#proof-initial-angle)
- [Technical proof 37: Terminal facet geometry, width cuts and projection (TP)](#proof-terminal-geometry)
- [Technical proof 38: The all-sign partial three-angle width cut (WC)](#proof-partial-width)
- [Technical proof 39: Local positive-tilt source and support laws (PU)](#proof-positive-local-laws)
- [Technical proof 40: The all-sign reflected source system and energy calculation (RP)](#proof-reflected-local-laws)
- [Technical proof 41: The weighted companion moment and exact terminal margin (MP)](#proof-weighted-moment)
- [Technical proof 42: The near-full reflected-tail estimate (RX)](#proof-near-full)
- [Technical proof 43: The complementary reflected envelope and cubic payment (AC)](#proof-cubic-payment)
- [Technical proof 44: Universal partial-cap value and original-motion deduction (G2C)](#proof-partial-closure)
- [Technical proof 45: Every original full-turn equality cap and inverse canonicalization (CE)](#proof-full-equality)
- [Technical proof 46: Strict proper angles and literal compact-body recovery (TB)](#proof-terminal-equality)
- [Technical proof 47: Exact body deficits, equality dependencies and counterexamples (ED)](#proof-equality-audit)
- [Verification and review record](#verification-record)

---

<a id="main-introduction"></a>
## Chapter 1. The theorem, construction and external inputs

### Abstract

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

### 1. Motion domain and theorem

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

### 2. The scalar theorem and exact original-body partition

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

### 3. The explicit reference and its geometric properties

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

### 4. Equality mechanism and proof order

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

### 5. Notation and dependency conventions

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

### 6. Explicit external inputs

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

---

<a id="main-motions"></a>
## Chapter 2. Original continuous motions and actual-hull reduction

### 1. Canonical support geometry, with no unmentioned change to the body

Put the common incoming strip at \(0\le y\le1\). For an orthonormal pair of hallway normals \(u,v\), let
\[
H(u,v;a,b)=
\{p:p\cdot u\le a+1,\ p\cdot v\le b+1,\
       (p\cdot u\ge a\;\text{or}\;p\cdot v\ge b)\}.
\tag{GA.1}
\]
Its **incoming straight arm** is \(b\le p\cdot v\le b+1,\ p\cdot u\le a+1\), and its **outgoing straight arm** is \(a\le p\cdot u\le a+1,\ p\cdot v\le b+1\). The open forbidden corner has both inner inequalities strict.

For compact \(S\) and \(K=\operatorname{conv}S\), every placement containing S obeys
\(a\ge h_K(u)-1,\ b\ge h_K(v)-1\).
Lower both offsets to these exact support values. The new outer inequalities hold automatically on K, and each of the two inner alternatives has a **weaker threshold**. Thus
\[
S\subset H(u,v;h_K(u)-1,h_K(v)-1).
\tag{GA.2}
\]
This supports an *actual continuous placement path* over any continuous interval of frame angles, because \(h_K\) and the frame normals are continuous. One is not claiming that all of K survives the hallway.

For a support normal n, write \(w_K(n)=h_K(n)+h_K(-n)\). If \(w_K(v)\le1\), all of K fits the **incoming** straight arm of the canonical placement; if \(w_K(u)\le1\), all of K fits the **outgoing** straight arm. Indeed its minimum v-projection is \(-h_K(-v)\ge h_K(v)-1\), and similarly for u.

### 2. Original arbitrary motions force both correctly handed partial intervals

Let S have actual incoming vertical span \(H\in(0,1]\). Assume its area is **greater than \(\sqrt2\)**; this is the only regime needed to prove a candidate \(M>\sqrt2\) optimal. Consider the genuine **lower** physical passage. Its lifted body-relative hallway rotation \(\theta(s)\) begins at zero and ends at some \(\omega\). At the end S is contained in an **actual outgoing unit strip** normal to \(u_\omega=(\cos\omega,\sin\omega)\), while at the start it is in the horizontal incoming strip of width H. The determinant of these two strip normals has absolute value \(|\cos\omega|\); consequently, whenever it is nonzero,
\[
|S|\le H/|\cos\omega|.
\tag{GA.3}
\]
As \(|S|>\sqrt2\ge\sqrt2 H\), its endpoint cannot have \(|\cos\omega|\ge1/\sqrt2\).

At a *wrong-handed* \(-\pi/4\) lower frame, the two frame normals are
\((1,-1)/\sqrt2,(1,1)/\sqrt2\), both with positive horizontal component. For an arbitrary placement, a horizontal section of their L-hallway is **exactly a single interval of length \(\sqrt2\)**: in the (unnormalized) x-coordinate the outer right wall is the minimum of two affine expressions, and the union of the two inner alternatives is the same minimum minus \(\sqrt2\). Its intersection with the incoming horizontal H-strip has area at most \(\sqrt2 H\). Thus S cannot visit this orientation.

Now use continuity of the lifted angle: if the lower motion failed to visit the correct-handed \(+\pi/4\), its endpoint either remained in \((-\pi/4,+\pi/4)\), contradicting GA.3, or its lift crossed \(-\pi/4\), contradicting the preceding horizontal-section bound. Hence \(+\pi/4\) is visited. If the lift ever visits \(+\pi/2\), restrict to the first such visit and take \(\alpha=\pi/2\); the terminal outgoing width is then the original incoming height \(H\le1\). Otherwise the actual terminal lift lies in \((\pi/4,\pi/2)\): take it as \(\alpha\), with the original outgoing unit-strip condition. All angles in \([0,\alpha]\) were visited by the actual motion.

Reflect the **geometric constraints**, not the sofa itself, across \(y=1/2\) to repeat this proof for the independent physical upper-handed passage. It supplies a second magnitude \(\gamma\in[\pi/4,\pi/2]\), whose proper downward-reflected normals are again \(u_t,v_t\). The two paths may translate differently and have unrelated angle histories. Apply GA.2 to each visited frame to replace them by continuous support-tightened monotone angular witnesses of S; no new orientation is asserted feasible.

This rederives the only near-optimum motion coverage needed from [GH](https://github.com/vltanh/lean4-moving-sofa/blob/b525305f344e635e6264cb470514d6b8bb7a8e43/docs/ambidextrous/midpoint-bound-general-motions.md), [Note 8](https://github.com/vltanh/lean4-moving-sofa/blob/b525305f344e635e6264cb470514d6b8bb7a8e43/docs/ambidextrous/08-common-hull-tightening.md) and [Note 10](https://github.com/vltanh/lean4-moving-sofa/blob/b525305f344e635e6264cb470514d6b8bb7a8e43/docs/ambidextrous/10-wrong-angle-exclusion.md) without assuming complete quarter-turns.

### 3. The exact two partial **whole-body strip** thresholds and ordinary fibers

For *arbitrary* nonempty compact convex \(K\subseteq\mathbb R\times[0,1]\), let \(I=[l,r]\) be its horizontal projection and denote its **actual** upper/lower convex hull fiber endpoints by \(A_K(x)\), \(B_K(x)\). Define the downward upper cap with roof \(A_U(x)=A_K(x)\), and the downward cap of the vertically reflected lower hull with roof
\[
A_V(x)=1-B_K(x).
\]
Thus
\[
d_U(x)=1-A_K(x),\qquad d_V(x)=B_K(x),
\]
and both deficits are nonnegative even when the actual vertical span is *strictly below* one.

For \(0<t<L=\pi/2\), \(c=\cos t>0,s=\sin t>0\), the **lower** canonical forbidden quadrant gives
\[
y<
\min\left\{
\frac{h_K(u_t)-1-xc}{s},\
\frac{h_K(v_t)-1+xs}{c}
\right\}.
\tag{GA.4}
\]
Define its positive all-visited-angle roof \(n_{K;\alpha}(x)\) as the maximum of zero and the supremum of GA.4 over \(0<t<\alpha\). This is the **whole moving sharp inner corner AND both attached rays**, not merely a corner shadow or a finite contact sample.

The *actual outgoing straight arm* at \(\alpha\) places **the entire body** into the unit strip with normal \(u_\alpha\). Since K's outer support inequality is automatic, the additional lower boundary is
\[
\boxed{
e_{K;\alpha}(x)
=\frac{h_K(u_\alpha)-1-x\cos\alpha}{\sin\alpha}.
}\tag{GA.5}
\]
For the reflected upper passage, take \(\rho(x,y)=(x,1-y)\). Its positive lower-type niche and outgoing strip roofs are \(n_{\rho K;\gamma}\) and \(e_{\rho K;\gamma}\). Reflecting their coordinates **back** gives the upper boundary \(y\le1-\max\{n_{\rho K;\gamma},e_{\rho K;\gamma}\}\); the upper convex hull roof remains \(A_K\).

The actual canonical envelope over I therefore has **closed interval-or-empty** sections
\[
E_{\alpha,\gamma}(K)_x
=\left[
\max\{d_V,n_{K;\alpha},e_{K;\alpha}\},\
1-\max\{d_U,n_{\rho K;\gamma},e_{\rho K;\gamma}\}
\right]
\]
**only when** the left endpoint is no larger than the right; otherwise the section is empty. Put
\[
\boxed{
\ell_{K;\alpha,\gamma}(x)=
1-\max\{d_V,n_{K;\alpha},e_{K;\alpha}\}
-\max\{d_U,n_{\rho K;\gamma},e_{\rho K;\gamma}\}.
}\tag{GA.6}
\]
Then, with Fubini and the true positive-part convention,
\[
\boxed{
\mathscr V(K,\alpha,\gamma)=\int_I\ell\,dx,\qquad
|E_{\alpha,\gamma}(K)|=\int_I(\ell)_+\,dx
=\mathscr V+\int_I(-\ell)_+\,dx.
}\tag{GA.7}
\]
At \(\alpha=L\) the outgoing barrier is \(h_K(e_y)-1\le0\) and is redundant because \(d_V=B_K\ge0\). Its upper analogue is likewise redundant. At a genuine **partial** endpoint, GA.5 generally is **not** redundant and must not be omitted.

For an **actual compact connected feasible S** with \(K=\operatorname{conv}S\), \(S\subseteq E_{\alpha,\gamma}(K)\) by GA.2, and \(\operatorname{proj}_x S=I\) because continuous projection of connected S is the entire interval between its extreme abscissae. Thus **every** E fiber is nonempty and its \(\ell(x)\ge0\) *at every x*, so
\[
\boxed{|S|\le |E_{\alpha,\gamma}(K)|=\mathscr V(K,\alpha,\gamma).}
\tag{GA.8}
\]
This explicitly **does not** apply the unqualified signed identity to a disconnected auxiliary envelope.

#### An exact negative-fiber sanity check

Take \(K=[-1,1]\times[0,1]\) and both **complete** turns. At \(t=\pi/4\), \(x=0\), both lower inner-wall heights equal \(2-\sqrt2>1/2\); the reflected upper roof is the same. Therefore
\[
\ell_{K;L,L}(0)\le1-2(2-\sqrt2)=2\sqrt2-3<0.
\]
Its central fiber is empty even though the two side regions of E are nonempty. An expression integrating \(\ell\) as if it were ordinary area would be false. GA.7 gives exactly the required correction.

#### An exact outgoing-strip sanity check

The rational partial-turn triangle in [IC1](https://github.com/vltanh/lean4-moving-sofa/blob/b525305f344e635e6264cb470514d6b8bb7a8e43/docs/ambidextrous/exact-in-place-completion-obstruction.md) has vertices
\[
(0,0),\quad(1/10,1),\quad(-1,20/99),
\]
and lower terminal normal \(u_\alpha=(20/101,99/101)\) at
\(\alpha=L-2\arctan(1/10)\). The support in that normal equals one, attained at \((1/10,1)\); the minimum projection is zero, at the other two vertices. Formula GA.5 therefore gives **exactly**
\[
e_{K;\alpha}(x)=-20x/99.
\]
The third vertex \((-1,20/99)\) satisfies \(y=e_{K;\alpha}(-1)\) with equality: this is a genuinely binding **whole-body terminal arm**. The displayed support and strip equalities are all that this example uses.

### 4. The independent width-five box calculation

Suppose \(|S|>\sqrt2\), so the genuine **lower** \(\pi/4\) frame was visited by Section 2. Let its original horizontal projection be \([l,r]\), width \(W\), and vertical span H. Take actual retained extreme points \(P=(l,y_l),Q=(r,y_r)\). For every \(p=(x,y)\in S\),
\[
\begin{aligned}
h_K(u_{\pi/4})-p\cdot u_{\pi/4}
&\ge(r-x-H)/\sqrt2,\\
h_K(v_{\pi/4})-p\cdot v_{\pi/4}
&\ge(x-l-H)/\sqrt2.
\end{aligned}
\tag{GA.9}
\]
One depth must be at most one, hence
\[
x\ge r-(H+\sqrt2)\quad\text{or}\quad
x\le l+(H+\sqrt2).
\]
The horizontal projection of connected S is **all** \([l,r]\), so there cannot be a gap between those two allowed intervals. Consequently
\[
\boxed{W\le2(H+\sqrt2)\le2+2\sqrt2<5.}
\tag{GA.10}
\]
Move the horizontal projection midpoint to zero, and the actual lowest ordinate to zero: the *actual hull* of every potential above-\(\sqrt2\) original competitor is in
\[
\boxed{B=[-5/2,5/2]\times[0,1].}\tag{GA.11}
\]
This does **not** assert a width limit of five for every *auxiliary* convex K in the enlarged domain by a fake feasibility argument: the auxiliary K is simply **required** to lie in that fixed box.

### 5. Connectedification of **arbitrary auxiliary envelopes**, preserving area and both partial terminal strips

Let \(Q=E_{\alpha,\gamma}(K)\) be nonempty for an arbitrary auxiliary K in B. It is compact, has interval-or-empty vertical sections, satisfies both prescribed complete visited angular families, and **satisfies the two whole-body terminal strip inequalities GA.5**. It may be disconnected, or even have huge regions with \(\ell<0\).

Here is the precise contraction step, including its effects on supports. For a compact set Q of actual vertical span \(H_Q\le1\), and any nondecreasing 1-Lipschitz \(T:\mathbb R\to\mathbb R\), let \(F(x,y)=(T(x),y)\). For p,q in Q, n=(n_x,n_y), split according to the sign of \(n_x(q_x-p_x)\). In the nonnegative case the transformed horizontal dot-product difference does **not exceed** the old one. In the negative case the transformed horizontal difference is nonpositive and the vertical difference is bounded by \(H_Q|n_y|\). Maximizing over q yields
\[
\boxed{
h_{F(Q)}(n)-F(p)\cdot n
\le\max\{h_Q(n)-p\cdot n,\ H_Q|n_y|\}.
}\tag{GA.12}
\]
Thus **every inner-wall depth no larger than one remains safe**, regardless of which wall supplied that safety. An entire unit strip is preserved as well, because its width is the maximum support depth across all p. The result applies simultaneously to all four-handedness frame normals and both terminal normal directions.

Put \(D=\operatorname{proj}_xQ\), a compact subset of \([l,r]\), and choose
\[
T(x)=\int_l^x\mathbf1_D(z)\,dz.
\tag{GA.13}
\]
It collapses precisely the open complementary gaps of D and sends D onto the **entire interval** \([0,|D|]\). For every finite collection of gaps, the corresponding partial collapse acts as translations on the occupied x-bands, preserves area exactly, and is 1-Lipschitz. The remaining total gap length tends to zero, so these images converge in Hausdorff distance to \(F(Q)\). Their areas stay \(|Q|\). The area upper-semicontinuity of compact sets gives \(|F(Q)|\ge|Q|\); horizontal-section 1-Lipschitz nonexpansion gives \(|F(Q)|\le|Q|\). Therefore
\[
\boxed{|F(Q)|=|Q|.}\tag{GA.14}
\]
This does **not** assert general continuity of area under Hausdorff convergence.

Fill each vertical fiber of F(Q) to its interval hull. All prescribed canonical hallways have interval intersections with each fixed vertical line: for a lower conventional frame both inner alternatives are **upward** rays, and for the upper frame their reflection makes them **downward** rays. Outer walls and terminal strips are additional half-lines in y. Filling thus stays in **every** previously feasible angular placement and terminal strip. The support does not change because
\(F(Q)\subseteq Q^\sharp\subseteq\operatorname{conv}F(Q)\).
The resulting compact body \(Q^\sharp\) is connected since its projection is an interval and its fibers are intervals.

Finally, vertical filling adds area only at x-values having **more than one preimage under T**; each such value corresponds to a nontrivial interval of constancy of monotone T. Those intervals are countable (each contains a different rational). For all remaining abscissae, F(Q) already had an interval fiber. Hence
\[
\boxed{|Q^\sharp|=|Q|,\qquad Q^\sharp
\text{ is a connected compact body preserving both prescribed angular intervals and both outgoing widths}.}\tag{GA.15}
\]
Its angular support-tightened translations are continuous. The initial and terminal straight motions append since both endpoint strips are genuine *whole-body* strips: translate far along the outgoing arm at fixed terminal orientation, and correspondingly far inside the incoming arm at zero angle. Both incoming paths can be connected to **one common starting pose** while the body is well upstream in the common unit strip; transverse readjustment is permitted there when the actual height is below one.

This proof allows \(Q^\sharp\) to have a **different convex hull, horizontal width and height** from the auxiliary K. It proves an *area-preserving change of feasible shape*, not an invalid claim that the original disconnected auxiliary envelope was already a sofa.

---

<a id="main-full-turn"></a>
## Chapter 3. Integrated full-turn value and equality proof

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
[the reference calculation](#proof-reference-matching) and
[the direct reference construction in the introduction, Section 3](#main-introduction).
Write \(U_*\) for the upper downward cap of its centered convex hull.
In particular \(M/2>41/50\): the cubic is negative at \(297/1000\),
and \(\arctan x\ge x-x^3/3\) gives the required strict rational
comparison.

### 1. The full-turn problem reduces to a global cap maximum

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
proved directly in [the original-motion bridge](#main-motions)
and [the spatial partition](#proof-full-domain).
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
complete argument is [the middle-chord reduction](#proof-middle-chord).

### 2. Actual source laws at a prescribed canonical maximizer

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
[the regularity proof](#proof-prescribed-regularity),
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
[endpoint and exposure laws](#proof-full-endpoints).
Here \(\omega\) omits the vertical end faces and the horizontal top;
any charged top length is accounted for separately.

Two genuine cap operations and estimates complete the normalization.
Inserting a height-one point at the nearer middle endpoint strictly
improves the score if the top misses \(J\). A tilted central facet
cannot extend into either charged wing; a safe support-normal variation
would improve its exterior roof without changing the niche on \(J\).
These are the [top-localization and facet-pinning laws](#proof-facet-pinning).
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
[these identities](#proof-full-pressures)
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

### 3. Horizontal maximizers and the strict functional calibration

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
arguments are proved in [the horizontal geometry](#proof-full-curvature);
the wide alternatives and their rational certificates are proved in
[the complete horizontal theorem](#proof-horizontal-complete).

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
[enclosure and its source dependencies](#external-inputs)
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
[the signed-roof reduction](#proof-arm), rather than a
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
[complete calibration proof](#proof-adaptive)
therefore gives

\[
F(f,g)-a\le M/2\quad(a\ge1/2),
\tag{FTM.21}
\]

with equality only at the centered reference pair. This proves the
horizontal sharp bound and records the strictness needed later.

### 4. All tilted canonical maximizers are excluded

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
[the width comparisons](#proof-tilted-width) and
[the full-triangle cut](#proof-full-triangle).

The first key exclusion is stronger than a two-unit-quarter theorem:
if \(u\le1\) on the first wing, the tilted maximizer is impossible,
with no assumption \(v\le1\). Here is the mechanism of
[the first-wing exclusion](#proof-first-unit).
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
[occupation proof](#proof-fold-occupations)
is indispensable when companion tangencies fold or revisit the floor.

For \(C\le2/3\), the central-atom-aware endpoint energy estimate
already supplies \(u\le1\). For wider caps put

\[
B=e_R-1+h,\qquad s_h=\sqrt{h(2-h)}.
\]

The [initial-floor criterion](#proof-initial-energy)
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
[positive-corner confinement](#proof-corner-confinement)
proves \(n_U\le A\), convexity of the niche on both exterior wings,
and a compact connected survivor with an explicit continuous ordinary
one-turn motion. Only now is the external bound FTM.15 used.
The [early-excess estimate](#proof-early-excess)
and [reflected-tail projection](#proof-reflected-projection)
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
[the final height reduction](#proof-final-height).

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
[The small-height proof](#proof-small-height)
contains the complete rational certificates. Equality in either energy
test belongs to the successful-test branch. Since
\(1/20<509/10000\), there is no boundary gap.

All tilted canonical maximizers have been excluded. The remaining
horizontal maximizer satisfies FTM.16–21. Attainment and the canonical
reduction now prove FTM.3 on the original cap domain, and FTM.5 proves
the sharp full-turn body bound. The ordinary one-turn input has been
used only to obtain strict contradictions for already feasible
survivors; no equality theorem for that external result is required.

### 5. Equality recovers every original cap and full-turn body

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
reference profile, is [the full-turn cap classification](#proof-full-equality).

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
[the body-recovery argument](#proof-terminal-equality).

Full-turn sharpness and its equality case concern bodies and supports.
They do not assert uniqueness of motion parameterizations, and they
do not replace the separate partial-turn argument retaining the two
actual outgoing strips.

---

<a id="main-partial-turn"></a>
## Chapter 4. Integrated partial-turn and strict-angle proof

Put \(L=\pi/2\), and let

\[
M=1+4Y^2+\arctan Y,\qquad 4Y^3+3Y=1,\qquad Y>0.
\tag{PT.1}
\]

This chapter gives the partial-turn part of the area and rigidity
theorem. The universal value theorem
[G2C1](#proof-partial-closure) establishes that the joint
maximum of the cap functional below is \(M/2\), attained by the
full-turn reference. We use this established maximum before analyzing
equality. In particular, an arbitrary cap attaining \(M/2\) is a
joint maximizer; none of the following equality arguments replaces its
angle by the largest angle of some other maximizer.

The full-turn equality input is
[CE1--CE3](#proof-full-equality): a full-turn equality cap
is a horizontal translate of the centered reference cap, whose middle
roof is horizontal. All longer source, finite-angle and reflected
estimates used here have complete proofs in the linked notes.

### 1. The actual outgoing-wall functional

Let \(U\subset\mathbb R\times[0,1]\) be a nonempty compact downward
convex cap, with projection \(I=[l,r]\), roof \(A\), width
\(W=r-l\), and middle half
\(J=[l+W/4,r-W/4]\). For \(0<t<L\), set

\[
\mu_t=(\cos t,\sin t),\quad \nu_t=(-\sin t,\cos t),\qquad
f(t)=h_U(\mu_t),\quad g(t)=h_U(\nu_t),
\]
\[
R_t(x)=\frac{f(t)-1-x\cos t}{\sin t},\qquad
S_t(x)=\frac{g(t)-1+x\sin t}{\cos t}.
\tag{PT.2}
\]

For \(\pi/4\le a<L\), define the visited niche, actual barrier,
and score by

\[
n_a(x)=\max\{0,\sup_{0<t<a}\min(R_t(x),S_t(x))\},
\quad N_a(x)=\max\{n_a(x),R_a(x)\},
\]
\[
\mathcal P_a(U)=\int_{I\setminus J}A(x)\,dx-
\int_JN_a(x)\,dx.
\tag{PT.3}
\]

The term \(R_a\) is the whole first inner wall imposed by the
outgoing strip. It is not replaced by the terminal two-wall minimum.
At \(a=L\), use the full positive niche: the limiting outgoing
wall is nonpositive because the cap has height at most one. A
zero-width cap has score zero.

**Partial-cap theorem.** Every cap in this domain satisfies

\[
\mathcal P_a(U)\le M/2\quad(\pi/4\le a\le L),
\qquad
\mathcal P_a(U)<M/2\quad(\pi/4\le a<L).
\tag{PT.4}
\]

The non-strict statement is G2C1. We prove its strict refinement by
excluding every proper-angle equality cap. The same quantitative
estimates constitute the proper-angle contradiction in the value
theorem; their use at equality requires the fixed-cap argument in
Section 4.

### 2. Canonical reduction and prescribed-cap source laws

Suppose \(\mathcal P_a(U)=M/2\) with \(a<L\). The domain
theorems [PD1--PD5](#proof-partial-domain) permit
vertical extrusion to height one, cutting by the chord over \(J\),
and restoring height. These operations keep \(a\) fixed and do not
decrease the score, so the known universal upper bound forces equality
throughout. The resulting canonical cap has height one, affine middle
roof, and top face meeting \(J\). For this prescribed cap, saturation
by precisely the used supporting halfplanes, followed by intersection
with its middle chord, is again a nondecreasing comparison. Maximality
therefore gives the identity

\[
U=\operatorname{Sat}_a(U)\cap\{y\le\ell(x)\},
\tag{PT.5}
\]

where \(\ell\) is its middle chord. The saturation step retains all
used supports, including the outgoing support; extrusion and chord
cutting need not retain them. PD also supplies width coercivity and
joint attainment for the value proof.

These are reductions of the actual spatial objective. Vertical
extrusion raises every attached inner wall by the extrusion height;
the positive-floor maximum can increase by at most that amount.
Since the charged exterior and middle window have equal lengths, the
roof gain pays the barrier increase. Cutting by the middle chord
preserves the exterior roof and decreases all supports, so it cannot
raise the niche penalty. Saturation restores every point allowed by
the used supports without changing their barrier, and the chord
intersection retains the affine middle. The same domain
argument controls the angular endpoint tails, making the barriers
continuous under the compact cap and angle limits used for attainment.
None of these steps assumes smoothness or bounds polygon complexity.

The source theorem [PS1](#proof-partial-sources)
applies to this prescribed maximizing cap at its fixed angle. Its
finite approximants carry a vanishing support penalty toward that cap,
so the conclusion is not an existence assertion about an unrelated
regular maximizer. Translate horizontally to
\(I=[-2C,2C]\), \(J=[-C,C]\), and put
\(Q_\pm=A(\pm C)+N_a(\pm C)\). The actual endpoint heights
satisfy

\[
e_R=A(2C)=\frac{3Q_+-Q_-}{4}>0,\qquad
e_L=A(-2C)=\frac{3Q_--Q_+}{4}>0.
\tag{PT.6}
\]

The limiting finite-source measure equals the actual arclength measure
of the charged outer roof above \(I\setminus J\), omitting vertical
end faces and the horizontal top. It has bounded density on the
visited open normal arcs. Its only possible atom is at the first
terminal normal \(a\); there is no companion terminal atom and no
charged curvature on unused open arcs. The affine middle remains an
uncharged facet. These distinctions also hold when it is tilted.

The finite-source proof retains the floor in every finite maximum and
uses actual moving-window variations for PT.6. A nonterminal source
has exposure bounded by a constant times its angular mesh, excluding
both interior atoms and singular concentration in the limit. The
whole outgoing line is the one exceptional source and is kept
separately. The equality of the limiting source measure with the
actual charged wing measure is obtained before interpreting its
terminal mass. This order matters: no arclength identity for a
possibly vanishing-height limiting barrier is substituted for the
source theorem.

If the terminal charged facet has horizontal length \(m\), there is
a measurable terminal occupation \(0\le\chi\le1\) such that

\[
\int_J\chi(x)\,dx=m,\qquad
\chi=1\text{ a.e. on }E:=\{x\in J:R_a(x)>n_a(x)\}.
\tag{PT.7}
\]

Only strict exposure is used. Positive-length historical ties may have
fractional occupation; shape and angle variations are not assigned a
common fractional choice.

### 3. Exact angle, width and tilt reductions

The all-width certificate
[AT](#proof-initial-angle) gives

\[
a\le\arctan(8/3)
\quad\Longrightarrow\quad
\mathcal P_a(U)<5259/6400<M/2.
\tag{PT.8}
\]

Hence an equality pair has \(a>\arctan(8/3)>3\pi/8\).
The three genuine tents at \(\pi/8,\pi/4,3\pi/8\) are
therefore visited. Their comparisons in
[TP, Section 1](#proof-terminal-geometry) and
[WC](#proof-partial-width), using PT.6 and the joint
positive-floor loss, give

\[
\frac{1001}{2000}<C<\frac{37}{50},\qquad
A(-C)=1-h_L,\quad A(C)=1-h_R,
\]
\[
h_L,h_R\ge0,\qquad \min(h_L,h_R)=0,\qquad
h_L+h_R<\frac{17}{50}.
\tag{PT.9}
\]

These cuts have strict bounds below \(M/2\), so they apply at
equality. The width proof uses the actual partial endpoint pressures;
it requires no full-niche endpoint box at moderate angles. Reflection
in the three-tent comparison reflects its barrier as well. We retain
the original orientation for all subsequent outgoing-wall arguments.

Write \(c=\cos a\), \(s=\sin a\), and
\(\kappa=\cot a\). Then
\(0<c<3/\sqrt{73}\) and \(0<\kappa<3/8\). For a negative
middle tilt, \(h_R>0\), the exact completion theorem
[NT1](#proof-negative-completion) gives
\(N_a\ge n_L\) on \(J\) if either

\[
a\ge\theta_0:=L-\arctan(h_R/(2C)),\qquad
h_R\ge1-s.
\tag{PT.10}
\]

It follows on the same cap that
\(M/2=\mathcal P_a(U)\le\mathcal P_L(U)\le M/2\).
Full-turn equality makes its middle horizontal, contradicting
\(h_R>0\). The remaining negative case has
\(a<\theta_0\), \(0<h_R<1-s\). Positive and horizontal
middles remain in the original orientation.

### 4. Terminal geometry and the fixed-cap facet contradiction

For every remaining sign put

\[
H=1-h_R>s,\qquad b=C+T_R,\qquad
d=\frac{1-Hs}{c},\qquad w=c-d,
\tag{PT.11}
\]

where \(T_L,T_R\) are the height-one top overhangs outside the
ends of \(J\). They vanish on a strictly lower middle side. The
terminal facet endpoints, shifted endpoints, and outgoing zero are

\[
(b,H),\quad(b+m,H-mc/s),\qquad
B_+=(b-c,H-s),\quad B_-=B_++(m,-mc/s),
\]
\[
r_0=b-d,\qquad
R_a(-C+z)=\frac cs(2C+T_R-d-z).
\tag{PT.12}
\]

Let \(z_a\) be the intersection of the two terminal inner lines.
The corner estimate and horizontal source moment of TP give,
independently of any terminal mass bound,

\[
(z_a)_x<(B_+)_x,\qquad T_L+2T_R\le d,\qquad
0<d<c<C,\quad0<w<c/2.
\tag{PT.13}
\]

In particular \(0<(B_+)_x<r_0<C\). We now establish
\(m\le w\) for this individual equality pair.

Suppose \(m>w\). Then \((B_-)_x>r_0\). On
\((z_a)_x<x<(B_-)_x\), the terminal companion wall is above
the first wall, and the left angle derivative is

\[
S_a(x)>R_a(x),\qquad
\partial_-R_a(x)=\frac{x-(B_-)_x}{s^2}<0.
\tag{PT.14}
\]

Nearby earlier two-wall minima are consequently strictly greater
than \(R_a(x)\), giving \(n_a(x)>R_a(x)\) there. For
\(x\ge(B_-)_x\), the outgoing wall is negative. Thus strict
exposure and relevant ties occur only to the left of \((z_a)_x\).
The exact right angle law
[TV3](#proof-angle-variation), with
\(F=\{R_a=n_a\}\), says

\[
\int_E(x-(B_+)_x)\,dx+
\int_F(x-(B_+)_x)_+\,dx\ge0.
\tag{PT.15}
\]

The second integral vanishes and the first has a strictly negative
integrand. Hence \(|E|=0\); continuity gives \(n_a\ge R_a\)
everywhere on \(J\).

Choose

\[
\max\{-C,(z_a)_x\}<\zeta<(B_+)_x<r_0
<r_*<\min\{C,(B_-)_x\}.
\tag{PT.16}
\]

Immediately after \(a\), the first support of this same saturated
cap is the fixed point \((b,H)\), until \(\theta_0\) in the
negative case. Its first-wall derivative is
\(\partial_tR_t(x)=(x-b+\cos t)/\sin^2t\). It is negative
on \(x\le\zeta\) for sufficiently small angle increments.
On \([\zeta,r_*]\), the strict gap \(n_a-R_a\) has a positive
minimum, which covers the uniformly close new walls. For
\(x\ge r_*\), the new walls remain nonpositive because their
zero \(b-(1-H\sin t)/\cos t\) stays below \(r_*\).
Thus some \(a<\beta<L\), with \(\beta<\theta_0\) when
needed, satisfies

\[
R_t\le n_a\text{ on }J\ (a\le t\le\beta),\qquad
N_{U,\beta}=N_{U,a},\qquad \mathcal P_\beta(U)=M/2.
\tag{PT.17}
\]

Every new two-wall minimum is bounded by its first wall, while all
old minima remain available. This proves exact barrier equality.
The cap, projection, window and middle chord have not changed.
Moreover
\(U\subseteq\operatorname{Sat}_\beta(U)\cap\{y\le\ell\}
\subseteq\operatorname{Sat}_a(U)\cap\{y\le\ell\}=U\).

The original facet still has an open charged segment with \(x>C\)
and positive arclength \(m/s\), but its normal \(a\) is now
interior to the visited first arc \((0,\beta)\). It is not the
middle normal: in the negative case \(a<\beta<\theta_0\),
and in the other cases that normal is at least \(L\). PS applied
to this prescribed maximizing pair forbids the unchanged charged
atom. This contradiction proves

\[
\boxed{m\le w.}
\tag{PT.18}
\]

This is the equality upgrade [TB1](#proof-terminal-equality).
The value proof may instead select the largest maximizing angle and
contradict PT.17 directly. The atom argument proves PT.18 without
that selection and therefore applies to each equality cap.

### 5. A weighted companion moment

Let \(g\) now denote the left charged-wing support, with regular
curvature \(v=g''+g\ge0\). For positive tilt take the low-left
surrogate. Removed high-right points satisfy \(X\ge C,Y\le1\),
so their companion walls on \(J\) are bounded by
\(1-\sec t+(x-C)\tan t\le0\). Thus in every sign

\[
g(0)=1-h_L,\quad g'(0+)=C+T_L,\qquad
n_a(x)\le[\max_{0\le t\le a}S_t(x)]_+.
\tag{PT.19}
\]

Set \(A_0=C-T_L\), \(\theta=\arcsin A_0\),
\(G(x)=\sqrt{1-x^2}\), and \(\lambda=\tan\theta\).
The shifted companion support point satisfies

\[
D_x=-g'\cos t-(g-1)\sin t,\quad
D_y=-g'\sin t+(g-1)\cos t,
\]
\[
D_x'=(1-v)\cos t,\quad D_y'=(1-v)\sin t,\qquad
S_t'(x)=\frac{x-D_x(t)}{\cos^2t}.
\tag{PT.20}
\]

At \(x=-C+z\), \(0\le z\le w\), any positive maximizing
wall is interior and satisfies \(D_x(t)=x\),
\(S_t(x)=D_y(t)\), and \(\sin t\le C+z\). Indeed its outer
support abscissa is \(D_x-\sin t\ge-2C\), so the wall is
strictly decreasing when \(\sin t>C+z\); and
\(C+z\le C+c/2<s\).

The initial shifted point is \((-C-T_L,-h_L)\). Integration
at a maximizing angle gives the exact weighted identity

\[
D_y(t)+h_L-\lambda(T_L+z)
=\int_0^t(1-v(r))(\sin r-\lambda\cos r)\,dr.
\tag{PT.21}
\]

Define the early excess cost

\[
\mathcal E_\theta=
\int_0^\theta(v(r)-1)_+
\frac{\sin(\theta-r)}{\cos\theta}\,dr.
\tag{PT.22}
\]

Before \(\theta\), PT.21's integrand is bounded by this positive
excess; afterward it is bounded by \(\sin r-\lambda\cos r\)
because \(v\ge0\). Maximizing the resulting expression over
\(t\le\arcsin(C+z)\) yields

\[
n_a(-C+z)\le
[-h_L+G(C-T_L)-G(C+z)+\mathcal E_\theta]_+
\le G(C-T_L)-G(C+z)+\mathcal E_\theta.
\tag{PT.23}
\]

This is [MP.10--16](#proof-weighted-moment).
Curvature above one after \(\theta\) causes no adverse error.

MP's exact scalar comparison gives, uniformly for \(0\le z\le w\),

\[
R_a(-C+z)-[G(C-T_L)-G(C+z)]>\frac{39c}{4400}.
\tag{PT.24}
\]

For clarity, its reduction uses \(z=w\), \(T_L\le d\),
\(T_R\ge0\), and \(d\ge\delta=c/(1+s)\). After division
by \(c\), the remaining lower bound is

\[
\frac{2C-c}{s}-\mathcal A_c(C-\eta),\qquad
\mathcal A_q(y)=\frac1q\int_{y-q/2}^{y+q/2}
\frac{x}{\sqrt{1-x^2}}\,dx,\quad
\eta=\frac{c^3}{2(1+s)^2}.
\tag{PT.25}
\]

The average is increasing in its center and width and convex in its
center. Exact comparisons at \(C=1/2,37/50\), split at
\(c=1/3\), give lower margins \(8/495\) and \(39/4400\).
Concavity in \(C\) proves PT.24 throughout the interval; all radical
comparisons in MP.20--23 are certified by squaring positive rationals.

It remains to pay \(\mathcal E_\theta\le39c/4400\). Then
PT.23--24 make \([-C,-C+w]\) strictly exposed. Continuity extends
exposure a positive distance beyond its interior right endpoint, so
\(|E|>w\ge m\), contradicting PT.7.

### 6. Reflected curvature bounds pay the complete angle range

Reflection is used only on local support equations. For corresponding
wing supports put \(u=f''+f\), \(p=f'-g+1\),
\(q=g'+f-1\), and under
\(r=L-t\) write

\[
P(r)=-q(L-r),\quad Q(r)=-p(L-r),\quad
U(r)=v(L-r),\quad V(r)=u(L-r),
\]
\[
P'=U-1-Q,\quad Q'=V-1+P.
\tag{PT.26}
\]

On regular retained intervals the actual source laws give

\[
P\le1,\quad Q\ge-1,\qquad
U\le\max\{|Q|,(1+|Q|)/2\},\quad
V\le\max\{|P|,(1+|P|)/2\}.
\tag{PT.27}
\]

In the positive \(P,Q\) sector, \(U=0,V\le1/2\). Every later
positive-\(Q\) component has amplitude at most \(1/8\), hence
cannot carry \(U>1\). The unused gap has \(U=V=0\); at its
end \(\varepsilon=L-a\), the terminal facet produces one upward
jump \(j=m/s\le\delta=c/(1+s)\) in \(Q\). There are no
further used-angle atoms. For negative tilt the unused central atom
is removed by the right-wing surrogate, preserving every used first
support. On the final removed positive-central interval both densities
vanish directly, without an appeal to reflected arm bounds.

The initial reflected state is \((P,Q)=(e,d_0-1)\), where

\[
(e,d_0)=
\begin{cases}
(e_L,3C+T_R),&h_R=0,\\
(e_L+h_R,3C),&h_R>0.
\end{cases}
\tag{PT.28}
\]

For \(\mathcal H=(P-1/2)^2+(Q+1)^2\), the exact gap and
impulse calculation gives

\[
\mathcal H(\varepsilon+)-\mathcal H(0)
\le\delta^2\left[
\frac{2e-1+\delta^2}{1+\delta^2}-d_0c\right].
\tag{PT.29}
\]

**The range \(0<\kappa\le1/8\).** The valid small-deficit
endpoint bounds and PT.29 give impulse cost below \(1/480\).
The theorem [RX](#proof-near-full) proves that
every possible reflected excess has ended before \(18/25\). It
includes a first \(P\)-zero in the unused gap and the terminal
jump. Since \(\cos(18/25)>37/50>C\),

\[
v(t)\le1\quad\text{a.e. on }(0,\arcsin C),\qquad
\mathcal E_\theta=0.
\tag{PT.30}
\]

**The range \(1/8\le\kappa<3/8\).** Here the actual outgoing
wall in PT.6 yields \(e<179/200,d_0<2311/1000\) for
positive or horizontal middle, and \(e<1,d_0<111/50\) for
negative middle. The impulse cost is below \(1/30\). The theorem
[AC](#proof-cubic-payment) starts its decay
comparison at the first \(P\)-zero, or at \(\varepsilon\) if
that zero preceded the terminal impulse. With \(\rho\) the elapsed
time from this starting point, it obtains
\(Q-1\le\sqrt Z-2-\rho/2-\rho^2/4\), where
\(Z=d_0^2-e(1-e)+1/30\). Its coupled time and amplitude
comparison puts every excess endpoint before \(91/100\), giving

\[
(U(r)-1)_+\le\frac{19}{25}(91/100-r)_+
\quad\text{for a.e. }r.
\tag{PT.31}
\]

AC checks the first zero before, at, and after the impulse. Its two
parameter endpoint certificates are exact squared inequalities, and
its control of subsequent source components is uniform in the tilt.

More explicitly, after \(P\le0\), an interval with \(Q>1\)
has \(P'\le-1\). The arm bound for \(V\) then gives
\(Q'\le-1/2-\rho/2\) until the predicted excess ends. Its
duration is at most
\(D(Z)=\sqrt{1+4(\sqrt Z-2)_+}-1<13/25\).
When the zero follows the impulse, its time is bounded by
\(\tau(d_0,e)=d_0-\sqrt{d_0^2-2e}\). The relevant expression
\(\tau+D\) is increasing in both parameters on \(Z>4\), and
the two parameter pairs above give upper bounds \(91/100\) and
\(9/10\). If the zero precedes the impulse, the direct bound is
\(\varepsilon+D<22/25\). Factoring the quadratic decay supplies
the slope \(19/25\) in PT.31. This gives a coupled time and
amplitude estimate, including the nonsmooth terminal jump.

Return to \(t=L-r\), and put \(t_0=L-91/100\).
Since \(C-T_L<37/50\),
\(\cos\theta>2/3\) and
\(\arccos(C-T_L)>147/200\). Thus
\(\ell=(\theta-t_0)_+<7/40\). Using
\(\sin(\theta-t)\le\theta-t\) in PT.22 gives

\[
\begin{aligned}
\mathcal E_\theta
&\le\frac{19}{25\cos\theta}
\int_{t_0}^{\theta}(t-t_0)(\theta-t)\,dt\\
&=\frac{19\ell^3}{150\cos\theta}
<\frac{6517}{6400000}
<\frac{117}{110000}<\frac{39c}{4400}.
\end{aligned}
\tag{PT.32}
\]

If \(\ell=0\), the cost is zero and the integral is omitted.
The last comparison uses \(c\ge1/\sqrt{65}>3/25\), and the
middle rational gap is \(3193/70400000>0\). This pays the
weighted error on the entire second range. The ranges overlap at
\(\kappa=1/8\).

### 7. Strictness for the original equality angle

The order of the value and equality arguments can now be stated
explicitly. To prove the non-strict bound, assume a score greater
than \(M/2\). PD gives an attained global maximum and a largest
terminal angle among its maximizers. Its full-turn boundary is
excluded by the full-turn value theorem. PT.8--9 and the source laws
apply because the maximum exceeds the same strict numerical
thresholds. A completed negative case is excluded immediately by
\(\mathcal P_a(U)\le\mathcal P_L(U)\le M/2\), using no
full-turn equality theorem. For the remaining signs, the barrier
equality in PT.17 would preserve that larger maximum and contradict
the largest-angle choice if \(m>w\). Thus PT.18 holds,
and the weighted estimate and the two payments give the source
occupation contradiction. This is the universal value proof G2C1.
The reference attains \(M/2\), so the maximum is known exactly.

Only after that result do we start with an arbitrary equality cap,
as in Section 2. The same-cap interior-atom argument in Section 4
replaces the largest-angle choice. This is the only change needed
in the terminal mass step; the local source, geometric and reflected
estimates depend on the displayed quantitative hypotheses, which
hold unchanged at equality. The completed negative case now uses
the full-turn equality classification on that same cap.

PT.30 or PT.32 supplies the cost bound required after PT.25, giving
the contradiction to terminal occupation in every residual middle
sign. The completed negative branch was excluded on the same cap by
full-turn equality, and PT.8 includes the lower boundary
\(a=\pi/4\). No proper-angle canonical equality pair remains.

An arbitrary proper-angle equality cap would have produced such a
pair through the score-preserving, angle-preserving reductions of
Section 2. It therefore cannot exist. This proves the strict part of
PT.4 for all original caps, including subunit height and nonsmooth
boundaries. At \(a=L\), the non-strict bound and full-cap equality
classification apply. Consequently, when the original two-cap area
inequality is an equality, each of its two original scalar terminal
angles is \(L\), independently of the other angle.

---

<a id="main-equality"></a>
## Chapter 5. Original equality caps, actual hull and exact body

### 1. Exact theorem and reference

Let \(Y>0\) be the unique solution of \(4Y^3+3Y-1=0\), and put
\[
\beta_*=\arctan Y,\qquad
m_*=\frac1{3\sin\beta_*},\qquad
M=1+4Y^2+\arctan Y.
\tag{G3C.1}
\]
Let \(\Sigma_*\) be Romik's genuine ambidextrous body, centered in its
incoming strip, and \(K_*=\operatorname{conv}\Sigma_*\). Write \(U_*\)
for its upper downward convex cap. Its projection is
\([-m_*,m_*]\); its top face is
\([-m_*/2,m_*/2]\times\{1\}\). The explicit support functions,
convexity, feasible motions, actual-hull retention and exact area are
given in [the reference calculation](#proof-reference-matching)
and [the direct geometric construction](#main-introduction), Section 3.

**Theorem G3C1 (all scalar equality cases).** Let \(U\) be any nonempty
compact downward convex cap in \(\mathbb R\times[0,1]\), and let
\(\alpha\in[\pi/4,\pi/2]\). Use the actual partial spatial functional
of [G2C.2--3](#proof-partial-closure), including the whole
outgoing first wall. Then
\[
\boxed{
\mathcal P_\alpha(U)=M/2
\quad\Longleftrightarrow\quad
\alpha=\pi/2,\quad U=U_*+(a,0)
\text{ for some }a\in\mathbb R.
}
\tag{G3C.2}
\]
In particular the inequality is strict for every individual cap at
every proper allowed terminal angle.

**Theorem G3C2 (sharp value and exact body uniqueness).** If a compact
connected planar body \(S\) admits the two original unit-corridor
passages from a common incoming orientation, then
\[
\boxed{
|S|\le M,\qquad
|S|=M\quad\Longleftrightarrow\quad
S\text{ is congruent to }\Sigma_*.
}
\tag{G3C.3}
\]
This covers independent partial terminal rotations, subunit incoming
height and arbitrary continuous motion histories. An equality body's
correct-handed canonical terminal magnitudes supplied by Gate 0 are
both \(\pi/2\); its actual normalized hull is \(K_*\).

The equality is literal equality of compact sets after a rigid motion.
The theorem classifies bodies and necessary angular reach. It does
not classify time parametrizations or all translation paths of a
motion witness.

### 2. Full-turn equality and reversal of canonicalization

The [full-turn equality theorem CE](#proof-full-equality)
first resolves the prescribed-maximizer quantifier. RG's penalized
finite selections can target any prescribed height-one affine-middle
global maximizer \(V\):
\[
D_n(V_n,V)^2\le e_n/\eta_n\longrightarrow0.
\tag{G3C.4}
\]
The regularity, pressure and source arguments consequently apply to
this particular \(V\). Gate 1's tilted and discarded-width branches
all end in strict inequalities or contradictions at values at least
\(M/2\). They leave the horizontal branch covered by CH6.

For that branch, the actual upper support pair \((f,g)\) satisfies
\[
\frac M2=P(V)\le F(f,g)-W/2\le\frac M2.
\tag{G3C.5}
\]
Reflect this upper pair into a real periodic \(H^1\) profile. The two
halves then give equality in the adaptive functional AF3. Its strict
fixed-width concavity and complete stationary-width classification
identify the centered reference support. This proves canonical cap
equality without assuming the cap has symmetry in advance.

To recover an arbitrary original equality cap \(U\), cut its middle
roof to the endpoint chord, obtaining \(V\), and restore height by
\[
U_c=V+[0,\varepsilon]e_y.
\]
The original and transformed scores obey
\[
M/2=P(U)\le P(V)\le P(U_c)\le M/2.
\tag{G3C.6}
\]
Canonical equality identifies \(U_c\) with the reference. The exact
extrusion deficit is
\[
\boxed{
P(U_c)-P(V)=\int_J(\varepsilon-n_{U_c})_+\,dx.
}
\tag{G3C.7}
\]
The reference niche is continuous and zero at the two endpoints of
\(J\). Thus every \(\varepsilon>0\) would give a strictly positive
deficit. It follows that \(\varepsilon=0\). The original middle roof
is then bounded below by the recovered height-one plateau and above
by the strip height one, while the exterior roofs were unchanged by
the cut. Hence \(U=V=U_c\) pointwise, including its compact boundary.
This proves the full-turn part of G3C1 for every original cap.

### 3. Proper-angle equality is impossible

Suppose \(\mathcal P_\alpha(U)=M/2\) with \(\alpha<\pi/2\). The
score-monotone cap reductions keep \(\alpha\) fixed and produce a
canonical joint global maximizer at that angle. In the negative-tilt
completed branch, NT gives
\[
M/2=\mathcal P_\alpha(U)\le P(U)\le M/2.
\]
The full-turn equality result would make this cap the horizontal
reference, contradicting its negative slope.

For every remaining sign, the new
[terminal-atom theorem TB1](#proof-terminal-equality)
proves the terminal facet bound \(m\le w\) for this individual
maximizer. Its argument is the missing equality step: if \(m>w\), the
terminal comparison and correct one-sided derivative permit one small
angle increase while preserving the same cap and its entire charged
barrier. The old positive terminal facet is still outside \(J\), but
its normal has become an interior visited normal. PS's regularity for
this prescribed maximizing cap forbids that positive curvature atom.

The resulting bound \(m\le w\), together with the top projection law,
allows the remaining Gate 2 weighted comparison to apply at equality.
RX pays the companion error by zero for \(0<\cot\alpha\le1/8\); AC
pays it strictly below the terminal margin for
\(1/8\le\cot\alpha<3/8\). MP then forces strict terminal exposure of
length greater than \(w\), exceeding the entire available terminal
source mass \(m\). The initial-angle exclusion and full-turn boundary
cover the other angles. This proves strictness at every proper angle,
and completes G3C1.

The argument does not infer equality rigidity merely from the
existence of a largest-angle maximizer. Its fixed-cap angle increment
is the additional contradiction needed for every equality case.

### 4. An exact deficit identity recovers the two original caps

For an actual equality body use Gate 0 with its actual hull \(K\).
Let \(U,V\) be its upper and reflected-lower downward caps, let
\(\alpha,\gamma\) be the independently supplied canonical angles, and
let \(E\supseteq S\) be its canonical envelope. Put
\[
d_U=1-A_U,\quad d_V=1-A_V,\quad
N_U=N_{U,\alpha},\quad N_V=N_{V,\gamma}.
\]
Their common projection is \(I\), with middle half \(J\).
Connectedness makes every projected envelope fiber nonempty, so its
area is the integral of
\[
\ell=1-\max(d_V,N_U)-\max(d_U,N_V).
\]

The exact partition remainder is
\[
\begin{aligned}
D={}&\int_J[(d_V-N_U)_++(d_U-N_V)_+]\,dx\\
&+\int_{I\setminus J}
[(N_U-d_V)_++(N_V-d_U)_+]\,dx.
\end{aligned}
\tag{G3C.8}
\]
Using the two scalar bounds, the full deficit splits as
\[
\boxed{
M-|S|=
(M/2-\mathcal P_\alpha(U))
+(M/2-\mathcal P_\gamma(V))
+D+|E\setminus S|.
}
\tag{G3C.9}
\]
Every summand is nonnegative. At \(|S|=M\), both ORIGINAL cap scores
equal \(M/2\). G3C1 gives
\[
\alpha=\gamma=\pi/2,\qquad
U=U_*+(a,0),\qquad V=U_*+(a,0).
\tag{G3C.10}
\]
The common projection forces the same horizontal translation. The
actual hull has upper roof \(A_U\) and lower roof \(1-A_V\), so these
equalities identify \(K=K_*+(a,0)\). This uses the original caps,
after their canonicalization was rigorously reversed.

### 5. Exact compact-body recovery and angular reach

The full canonical envelope of the identified actual hull is the
corresponding translate of \(\Sigma_*\). G3C.9 gives
\[
S\subseteq\Sigma_*+(a,0),\qquad |S|=|\Sigma_*|.
\tag{G3C.11}
\]
The reference is regular closed: its central fibers lie between
continuous strictly separated niche graphs, and its exterior flanks
are unchanged convex-body fibers. Its extreme tips and face endpoints
are also limits of interior points. Therefore
\(\Sigma_*=\overline{\operatorname{int}\Sigma_*}\).

If a point of this envelope were outside the closed set \(S\), it would
have an open neighborhood disjoint from \(S\). Regular closedness
would put a smaller open ball in the envelope within that neighborhood,
giving positive omitted area. This contradicts G3C.11. Hence the
normalized body is exactly the reference, proving G3C2.

There is also an independent whole-strip check on the angle conclusion.
The actual reference hull contains
\[
[-m_*/2,m_*/2]\times[0,1],\qquad m_*>1.
\]
For every unit normal \((c,s)\) with \(c\ne0\),
\[
\operatorname{width}_{K_*}(c,s)
\ge m_*|c|+|s|>|c|+|s|\ge1.
\tag{G3C.12}
\]
Its only unit-width strip normal is therefore vertical, up to sign.
Since convex hull preserves widths, a body with this actual hull
cannot fit any proper conventional outgoing unit strip. This concerns
necessary angular reach; pauses, backtracking and different time
parametrizations of feasible motions remain possible.

---

<a id="proof-reference-matching"></a>
## Technical proof 1. Reference matching, stationarity and exact value (Note 14)

### 14.1 Exact functions and a matching identity

Let Y be the positive root of \(4Y^3+3Y-1=0\), and set

\[
\beta=\arctan Y,\quad L=\pi/2,\quad b=L-\beta,
\quad s=\sin\beta,\quad c=\cos\beta,
\]

\[
A=\frac1{4s},\quad k=1-\frac43A,\quad
T=\frac32(\pi/4-\beta),\quad R=\frac{c}{\cos T}.
\tag{14.1}
\]

On [0,L] define f_* and g_* by

\[
(f_*,g_*)=
\begin{cases}
(\cos t+\tfrac12\sin t,
(2A-1)\sin t+\tfrac12\cos t+\tfrac12),&0\leq t\leq\beta,\\
(R\cos(t/2+\pi/8)+k\cos t+\tfrac12\sin t,
R\sin(t/2+\pi/8)-k\sin t+\tfrac12\cos t),&\beta\leq t\leq b,\\
((1-\tfrac23A)\cos t+\tfrac12\sin t+\tfrac12,
(\tfrac83A-1)\sin t+\tfrac12\cos t),&b\leq t\leq L.
\end{cases}
\tag{14.2}
\]

Define h_* on [0,pi] by h_*(t)=f_*(t), h_*(t+L)=g_*(t), and extend to the lower half by

\[
h_*(-t)=h_*(t)-\sin t\quad(0\leq t\leq\pi).
\tag{14.3}
\]

This makes \(h_*^\rho=h_*\). Both values at the top normal are one, and the bottom-normal value is zero.

**Lemma 36 (matching).** The pieces in (14.2) match in value and first derivative at beta and b. Moreover

\[
p_*(\beta)=0,\qquad q_*(b)=0,
\tag{14.4}
\]

where p_*=f_*'-g_*+1 and q_*=g_*'+f_*-1.

**Proof.** The only nontrivial trigonometric relation needed is

\[
R\cos T=c,\qquad R\sin T=\frac1{3s}-s.
\tag{14.5}
\]

The first is the definition. For the second put \(z=(1-2Y^2)/(3Y)\). The exact bounds from Notes 4 and 10 give 2/7<Y<3/10 and pi/12<beta<pi/4, so 0<z<1 and 0<T<pi/4. The triple-angle and double-angle identities, reduced using the cubic, give

\[
\tan(2T)=\frac{3(4Y^2-5Y-1)}{5-15Y-12Y^2},
\quad
\tan(2\arctan z)=\frac{3(5Y-1)}{16Y^2-Y-1}.
\]

The denominators are nonzero on the indicated root bounds. Their cross-product difference, after cancelling the common factor 3, is

\[
(16Y-6)(4Y^3+3Y-1)=0.
\]

Both doubled angles lie in (0,pi/2), where tangent is injective. Hence tan(T)=z. Multiplying by R cos(T)=c proves the second part of (14.5).

For a short verification of the vector matching, form the corner c_*=(f_*-1)mu+(g_*-1)nu. Its first-phase value and derivative at beta are

\[
c_*(\beta)=(1-c,\tfrac12-s),
\qquad
c_*'(\beta)=(s-c/2,\ c^2/(2s)-c).
\tag{14.6}
\]

For the middle phase, writing z_0=t-pi/4 gives

\[
c_*(t)=
(k-R\sin(3z_0/2)+\sqrt2\sin z_0,
\tfrac12+R\cos(3z_0/2)-\sqrt2\cos z_0).
\]

Substitute t=beta and (14.5), using \(\sqrt2\sin(\pi/4-\beta)=c-s\) and \(\sqrt2\cos(\pi/4-\beta)=c+s\). This gives exactly (14.6), including its derivative. Therefore f_*,g_* and their derivatives match. The identities

\[
f_*(L-t)=g_*(t)+2k\sin t,
\qquad g_*(L-t)=f_*(t)-2k\cos t
\tag{14.7}
\]

follow directly from the displayed formulas, and transfer matching to b. Finally p_* in the first phase is 1/2-2A sin(t), so p_*(beta)=0. Equation (14.7) gives p_*(L-t)=-q_*(t), proving q_*(b)=0. QED.

No numerical matching is hidden in this lemma. In particular h_* is a well-defined periodic H^1 function, even though its derivative can jump at the top and bottom normals corresponding to flat faces.

### 14.2 Interior equations and interface fluxes

Write F=F_{beta,b}. Its three integrands, expressed without abbreviating total derivatives, are

\[
\mathscr L_1=\tfrac12[f^2+2g^2-2g+1-f'^2-2g'^2-(fg)'+f'+g'],
\]

\[
\mathscr L_2=\tfrac12[f^2+g^2-2f'^2-2g'^2-fg'+gf'+g'-f'],
\]

\[
\mathscr L_3=\tfrac12[2f^2+g^2-2f+1-2f'^2-g'^2+(fg)'-f'-g'].
\tag{14.8}
\]

Their Euler equations are, respectively,

\[
(f''+f,\ g''+g-1/2)=(0,0),
\]

\[
(2f''-g'+f,\ 2g''+f'+g)=(0,0),
\]

\[
(f''+f-1/2,\ g''+g)=(0,0).
\tag{14.9}
\]

The elementary trigonometric functions in (14.2) satisfy these equations on each open phase: the middle phase combines the frequency-1 translation solution with the frequency-1/2 solution.

Let chi be the indicator of [beta,L] and psi that of [0,b]. The derivative fluxes for integration by parts are

\[
\Pi_f=-f'-\tfrac12(g-1)-\chi p_h,
\qquad
\Pi_g=-g'+\tfrac12(f-1)-\psi q_h.
\tag{14.10}
\]

At beta the change in the f-flux is -p_*(beta)=0; at b the change in the g-flux is q_*(b)=0. Thus no interface terms remain at h_*. The endpoints satisfy

\[
f_*'(0)=\tfrac12,\qquad g_*'(L)=-\tfrac12,
\qquad f_*(L)=g_*(0)=1.
\tag{14.11}
\]

For any H^1 variation delta with delta(L)=0, integration by parts now gives

\[
DF(h_*)[\delta]=\tfrac12[\delta(0)+\delta(\pi)].
\tag{14.12}
\]

Reflection preserves these endpoint values. Therefore the two copies of (14.12) cancel the derivative of the width subtracted in (13.3):

\[
D\mathcal Q_{\beta,b}(h_*)[\delta]=0
\tag{14.13}
\]

for every periodic variation satisfying delta(L)=delta(-L)=0. This calculation includes nonsymmetric variations; it is not restricted to the reflected candidate family.

### 14.3 Exact value without integrating the geometric boundary

Here is a direct evaluation of the quadratic at h_*. It does not use the geometric area of the sofa as an input.

Write F=F_2+F_1+F_0 for its homogeneous quadratic, linear, and constant parts. Integrating the linear terms in (14.8) gives

\[
F_1=-\int_0^\beta g-\int_b^L f
+f(\beta)+g(b)-\tfrac12[f(0)+g(0)+f(L)+g(L)],
\qquad F_0=\beta.
\tag{14.14}
\]

At h_*, (14.7) and the early-phase formulas simplify this to

\[
F_1(h_*)=4A c-\tfrac83A-1-\beta.
\tag{14.15}
\]

For verification, \(\int_0^\beta g_*=(2A-1)(1-c)+s/2+\beta/2\), \(f_*(\beta)=c+s/2\), and (14.7) supplies the late integral and the other switching value.

Integration by parts against h_* itself, using the Euler equations and flux continuity, gives

\[
2F_2(h_*)+F_1(h_*)
=[\Pi_f f_*+\Pi_g g_*]_0^L=\tfrac{16}{3}A-1.
\tag{14.16}
\]

The last number follows from

\[
f_*'(L)=2A/3-1,\quad g_*'(0)=2A-1,
\quad f_*(0)=1,\quad g_*(L)=8A/3-1,
\]

and (14.10)–(14.11). Combining (14.14)–(14.16),

\[
F(h_*)=\tfrac43A+2A c-1+\beta/2.
\]

Since h_* is reflection invariant and its horizontal width is \(h_*(0)+h_*(\pi)=8A/3\),

\[
\mathcal Q_{\beta,b}(h_*)=4A c-2+\beta
=\cot\beta-2+\beta.
\tag{14.17}
\]

Finally the cubic gives \(1/Y=4Y^2+3\), and hence

\[
\cot\beta-2+\beta=1+4Y^2+\arctan Y=M.
\tag{14.18}
\]

Thus the exact constant emerges from the quadratic evaluation itself.

---

<a id="proof-reference-height"></a>
## Technical proof 2. The exact global reference corner-height ceiling (Note 4)

**Local notation and derivation.** In this chapter only, write
\(s=\sin\beta\), \(c=\cos\beta\), \(\beta=\beta_*=\arctan Y\),
and \(L=\pi/4-\beta\). Thus this local \(L\) is not the full-turn endpoint.
The root bound MS.2 gives \(2/7<Y<1/3\); also
\(2-\sqrt3<2/7\), because \(3>144/49\). Consequently
\(\pi/12<\beta<\arctan(1/3)\), the bound labeled (4.2) below.
The path ordinate \(q(t)\) in (4.6) is the vertical coordinate of the
canonical corner
\((f_*(t)-1)\mu_t+(g_*(t)-1)\nu_t\) from MS.11.
Horizontal centering does not change this ordinate. Thus the following
height proof uses the explicit construction in this manuscript and has
no additional external path or feasibility premise.

### 4.2 Vertical coordinates without the large radical constants

Let

\[
a=\frac1{4s},\qquad L=\frac\pi4-\beta,
\qquad R=\frac{c}{\cos(3L/2)}.
\tag{4.5}
\]

For the canonical corner of the explicit reference support, the vertical coordinate q(t) is

\[
q(t)=
\begin{cases}
\tfrac12+a\sin(2t)-\sin t-\tfrac12\cos t,
       &0\leq t\leq\beta,\\[2pt]
\tfrac12+R\cos\bigl(\tfrac32(t-\pi/4)\bigr)
       -\sqrt2\cos(t-\pi/4),
       &\beta\leq t\leq\pi/2-\beta,\\[2pt]
q(\pi/2-t),&\pi/2-\beta\leq t\leq\pi/2,
\end{cases}
\tag{4.6}
\]

where the last line uses the first-phase formula at its reflected argument.

Direct substitution from MS.11 proves (4.6). In the first phase,
\[
(f_*-1)\sin t+(g_*-1)\cos t
=\tfrac12+a\sin(2t)-\sin t-\tfrac12\cos t.
\]
In the middle phase the \(k\)-terms cancel, and the result is
\[
\tfrac12+R\sin(3t/2+\pi/8)-\sin t-\cos t
=\tfrac12+R\cos(3(t-\pi/4)/2)-\sqrt2\cos(t-\pi/4).
\]
The last phase is the reflected first expression. Matching at
\(t=\beta\) gives \(R\cos(3L/2)=c\), exactly (4.5).
Thus every identity required for the height proof follows from the
displayed reference support.

### 4.3 An exact maximum for the corner height

**Theorem 13 (strict candidate ceiling).** For the path (4.6),

\[
\max_{0\leq t\leq\pi/2}q(t)
=q(\pi/4)=\tfrac12+R-\sqrt2<\tfrac12.
\tag{4.7}
\]

The maximum is attained only at t=pi/4.

**Proof, first phase.** Write \(z=\sin t\), so \(0\leq z\leq s\) and \(\cos t\geq c\). Then

\[
q(t)-\tfrac12
=\cos t\left(\frac{z}{2s}-\frac12\right)-z.
\]

The coefficient of cos(t) is nonpositive. Therefore

\[
q(t)-\tfrac12
\leq c\left(\frac{z}{2s}-\frac12\right)-z
=z\left(\frac{c}{2s}-1\right)-\frac c2
\leq-s,
\tag{4.8}
\]

where the final inequality uses \(c/(2s)=1/(2Y)>1\) and z<=s. Equality is attained at t=beta. Thus the first-phase maximum is \(1/2-s\); the last phase has the same maximum by reflection.

**Proof, middle phase.** By (4.2), \(0<L<\pi/6\), so

\[
\cos(3L/2)>1/\sqrt2,
\qquad R=\frac{c}{\cos(3L/2)}<\sqrt2.
\tag{4.9}
\]

Also

\[
R\geq c>\frac3{\sqrt{10}}>\frac{2\sqrt2}{3}.
\tag{4.10}
\]

The first strict inequality follows from \(\beta<\arctan(1/3)\); the second follows by squaring, since \(9/10>8/9\).

Set \(F(z)=R\cos(3z/2)-\sqrt2\cos z\). It is even. For \(0<z\leq L<\pi/6\), both z and 3z/2 lie in (0,pi/2), so \(\sin(3z/2)\geq\sin z>0\). Hence

\[
F'(z)=-\tfrac32R\sin(3z/2)+\sqrt2\sin z
\leq-(\tfrac32R-\sqrt2)\sin z<0.
\tag{4.11}
\]

Thus the middle-phase maximum is attained uniquely at its center and equals \(1/2+R-\sqrt2\). Its endpoint value agrees with the first-phase maximum, and is strictly smaller than its center value. This proves the global assertion and, using (4.9), the strict ceiling. QED.

---

<a id="proof-contact-identity"></a>
## Technical proof 3. The contact integral and its boundary identity (Note 13)

**Local notation.** For a normalized support \(h\), put \(L=\pi/2\),
\(h^\rho(\theta)=h(-\theta)+\sin\theta\), and
\[
C(h)=\frac12\int_0^L(f^2-f'^2+g^2-g'^2)\,dt,\qquad
I(h)=\frac12\int_0^L\det(c(t),c'(t))\,dt,
\]
where \(f=h(t)\), \(g=h(t+L)\), and
\(c(t)=(f-1)\mu_t+(g-1)\nu_t\). These are the quantities \(C,I\)
used in AR.2 and AF.1. For a convex body \(K\) in the normalized unit
strip, AR1 identifies \(C(h)\) and \(C(h^\rho)\) with the upper and
reflected-lower cap areas. Their fibers sum to one plus the hull fiber,
so
\[
C(h)+C(h^\rho)-h(0)-h(\pi)=|K|.
\]
This proves the identity called (12.5) in the historical notation below.
For general \(H^1\) profiles, \(C,I,h^\rho\) retain the displayed
algebraic definitions; no convexity claim is made for those profiles.

### 13.1 The functional suggested by the three-piece niche boundary

Use the normalized support-function notation just defined and put L=pi/2. On the upper half write

\[
f(t)=h(t),\quad g(t)=h(t+L),\quad
p_h(t)=f'(t)-g(t)+1,\quad q_h(t)=g'(t)+f(t)-1.
\tag{13.1}
\]

These are the rotating-frame components of the canonical corner velocity. For switching parameters

\[
0<a\leq b<L,
\]

define

\[
F_{a,b}(h)=C(h)+I(h)
-\frac12\int_a^L p_h^2\,dt
-\frac12\int_0^b q_h^2\,dt,
\tag{13.2}
\]

and

\[
\mathcal Q_{a,b}(h)
=F_{a,b}(h)+F_{a,b}(h^\rho)-h(0)-h(\pi).
\tag{13.3}
\]

By (12.5), the equivalent whole-body expression is the area integral plus the two I terms, minus the four displayed squared-velocity terms. Notice the **plus** sign before I here; this is a different functional from Q_0.

The fixed parameters a,b are part of the certificate. At the Romik candidate they will be beta and L-beta. For an arbitrary body they are not automatically its actual contact-switching angles.

### 13.2 The exact boundary identity motivating the signs

Let c=(f-1)mu+(g-1)nu, and set

\[
B=c+p_h\nu,\qquad D=c-q_h\mu.
\]

For any absolutely continuous path Z write \(I_Z[r,s]=\frac12\int_r^s\det(Z,Z')\). Integration by parts gives

\[
I_B[r,s]=I_c[r,s]-\frac12\int_r^s p_h^2
+\frac12[(f-1)p_h]_r^s,
\tag{13.4}
\]

\[
I_D[r,s]=I_c[r,s]-\frac12\int_r^s q_h^2
+\frac12[(g-1)q_h]_r^s.
\tag{13.5}
\]

For example, B'=(q_h+p_h')nu; subtract det(c,c') and integrate (f-1)p_h' by parts, using (f-1)'=p_h+g-1. The D calculation is the same with the other component.

Suppose, as an **additional geometric hypothesis**, that a niche boundary is the simple positively oriented concatenation of B traversed from L down to a, c from a to b, D from b down to 0, and the baseline, with

\[
p_h(a)=0,\qquad q_h(b)=0,\qquad f(L)=g(0)=1.
\]

All endpoint terms in (13.4)–(13.5) vanish, and its enclosed area is

\[
-I(h)+\frac12\int_a^L p_h^2+\frac12\int_0^b q_h^2.
\tag{13.6}
\]

This explains (13.2). It does not prove that every niche has this boundary, that the switching parameters are fixed, or that the enclosed region lies inside the common hull. Those are separate geometric questions.

---

<a id="proof-adaptive"></a>
## Technical proof 4. The unrestricted H1 calibration and all equality cases (AF)

### A.1 Definition on unrestricted profiles

Set L=pi/2. Let h be a real, 2pi-periodic H^1 function with

\[
h(L)=1,\qquad h(3L)=0.
\]

It need not be a convex support function. Define h^rho(t)=h(-t)+sin(t). On an upper half write f(t)=h(t), g(t)=h(t+L), for 0<=t<=L, and put

\[
p=f'-g+1,\qquad q=g'+f-1,
\quad p_-=\min(p,0),\quad q_+=\max(q,0).
\]

For a pair f,g define

\[
\begin{aligned}
F(f,g)=\frac12\int_0^L\bigl[&f^2+g^2-f'^2-g'^2
 +(f-1)^2+(g-1)^2\\
 &+(f-1)g'-(g-1)f'
 -p_-^2-q_+^2\bigr]dt.
\end{aligned}
\tag{A.1}
\]

This is the half-functional C+I minus the two sign-selected contact losses from Note 16. The full adaptive functional is

\[
\widetilde{\mathcal Q}(h)
=F(f,g)+F(f_\rho,g_\rho)-h(0)-h(\pi).
\tag{A.2}
\]

The exact integral definition is used throughout. For a convex support function it is the same quantity as in the earlier notes; it is not automatically the body's area.

Adding b cos(theta) changes neither functional: p and q are unchanged; the half support-area cross term is the endpoint term [b h sin(theta)] from 0 to pi; and the signed corner-area cross term is b/2 times the difference of the corner heights at the two ends, both zero. We may therefore center the horizontal support values as

\[
h(0)=h(\pi)=a,\qquad 2a=h(0)+h(\pi).
\]

For a genuine hull in a unit-height strip, any body inside it has area at most its horizontal width 2a. Thus a competitive body of area greater than one has a>1/2. The calibration below covers a>=1/2.

### A.2 Strict concavity at fixed width

Let

\[
X_a=\{(f,g)\in H^1(0,L)^2:
 f(0)=g(L)=a,\ f(L)=g(0)=1\}.
\tag{A.3}
\]

For the difference of two members write z=v+iw. Both components vanish at both endpoints. The negative homogeneous quadratic part of the unpenalized C+I functional is

\[
B_0(v,w)=\frac12\int_0^L
\left[|z'|^2-2|z|^2-\operatorname{Im}(\overline z z')\right]dt.
\]

With y(t)=exp(-it/2)z(t), completing the square gives

\[
\boxed{B_0(v,w)=\frac12\int_0^L
\left[|y'|^2-\frac94|y|^2\right]dt.}
\tag{A.4}
\]

The Dirichlet inequality on an interval of length L=pi/2 is integral |y'|^2 >= 4 integral |y|^2. For compactly supported smooth real functions it follows by expanding the nonnegative integral of (y'-2 cot(2t)y)^2 and integrating by parts. Density extends the inequality to H^1_0, and real and imaginary parts give the complex version. Therefore

\[
B_0(v,w)\geq\frac7{32}\int_0^L|y'|^2,
\tag{A.5}
\]

which controls the H^1 norm of (v,w). The negative contact losses are concave because min(x,0)^2 and max(x,0)^2 are convex and their arguments are affine in f,g.

**Lemma AF1 (unique fixed-width maximizer).** For every real a, F attains a unique maximum on X_a. No sign, curvature, convex-body, or feasibility conditions are required. Its maximizer satisfies

\[
f(t)=g(L-t).
\tag{A.6}
\]

**Proof.** Equations (A.4)-(A.5) prove uniform strict concavity on X_a. Subtract an affine boundary lift. The unpenalized part has a coercive negative quadratic bound plus a bounded linear term; subtracting the nonnegative contact losses preserves that bound.

A maximizing sequence is bounded in H^1. Pass to a weak H^1 and strong L^2 subsequence. Cross terms involving one derivative pass to the limit by strong-weak pairing. Negative squared-derivative terms and negative convex contact losses are weakly upper semicontinuous. Trace conditions pass to the limit. A maximum exists and strict concavity makes it unique.

The transformation (f(t),g(t)) -> (g(L-t),f(L-t)) preserves X_a and F. It sends p to -q(L-t) and q to -p(L-t), interchanging the two losses. The signed corner integral is invariant because spatial reflection and parameter reversal each reverse orientation. Uniqueness gives (A.6). QED.

For a fixed a, both halves of (A.2) belong to X_a and may be optimized independently. Consequently

\[
\widetilde{\mathcal Q}(h)\leq\Phi(a):=2\max_{X_a}F-2a.
\tag{A.7}
\]

Equality requires both halves to be the unique maximizer. This is symmetry of an auxiliary function-space optimizer, not a claim that averaging feasible bodies preserves feasibility.

### A.3 The Euler system has globally Lipschitz momenta

The contact-loss functions are continuously differentiable. The weak Euler equations at the fixed-width maximizer are

\[
f''+f+q+(p_-)' -q_+=0,
\qquad g''+g-p+p_-+(q_+)'=0.
\tag{A.8}
\]

Set

\[
P=p+p_-,\qquad Q=q+q_+.
\]

Initially P,Q are L^2. Their distributional derivatives from (A.8) are in L^2, so they are H^1 and continuous. Their inverse relations to p,q are Lipschitz. Substitution gives

\[
\boxed{P'=-1-b(Q),\qquad Q'=-1+c(P),}
\tag{A.9}
\]

where

\[
b(Q)=\begin{cases}Q/2&Q\geq0,\\2Q&Q\leq0,\end{cases}
\qquad
c(P)=\begin{cases}2P&P\geq0,\\P/2&P\leq0.\end{cases}
\]

The right side is globally Lipschitz. Thus P,Q are C^1, p,q are Lipschitz, and f,g are C^1 with Lipschitz first derivatives. This regularity concerns the auxiliary optimizer, not a general feasible hull.

Reflection (A.6) gives

\[
Q(t)=-P(L-t).
\tag{A.10}
\]

The boundary fluxes of F are

\[
\Pi_f=-f'-\tfrac12(g-1)-p_-,\qquad
\Pi_g=-g'+\tfrac12(f-1)-q_+.
\]

In particular Pi_f(0)=-P(0), Pi_g(L)=-Q(L). At an interior maximum where the common horizontal endpoint a is also free, varying a in both halves gives

\[
0=2(P(0)-Q(L))-2=4P(0)-2.
\]

Hence

\[
\boxed{P(0)=1/2,\qquad Q(L)=-1/2.}
\tag{A.11}
\]

This is an actual endpoint variation in the function space. No switching angle was frozen or differentiated as an independent coordinate.

### A.4 Hamiltonian form and the period bound

Define

\[
H(P,Q)=U(P)-P+V(Q)+Q,
\]

\[
U(P)=\begin{cases}P^2&P\geq0,\\P^2/4&P\leq0,\end{cases}
\qquad
V(Q)=\begin{cases}Q^2/4&Q\geq0,\\Q^2&Q\leq0.\end{cases}
\tag{A.12}
\]

Then (A.9) is P'=-H_Q, Q'=H_P, and H is constant along each solution. It is C^1, strictly convex, and coercive, with unique minimum at (1/2,-1/2). It is invariant under (P,Q)->(-Q,-P).

Put X=P-1/2, Y=Q+1/2. Each secant slope of c and b is between 1/2 and 2, so along a nonstationary orbit its polar angle satisfies

\[
\frac12\leq\frac{XQ'-YP'}{X^2+Y^2}\leq2.
\tag{A.13}
\]

A nonminimal level of H is a compact strictly convex closed curve, traversed with strictly positive angular speed. Its full period is at least pi. Therefore an orbit on an interval of length L=pi/2 cannot make an additional full revolution between a prescribed pair of points on that level.

### A.5 All stationary widths are classified

Let v=Q(0). By (A.10)-(A.11), a stationary full profile starts at (1/2,v) and ends at (-v,-1/2). These two points lie on the same H level. For v not equal to -1/2, they differ by a positive quarter revolution about (1/2,-1/2). The first transit is the only possible one in time L, by the period bound.

**Case 1: v<=0.** If v=-1/2 the orbit is stationary. Otherwise the entire first quarter transit stays in P>=0,Q<=0. There the equations are P'=-1-2Q, Q'=-1+2P, a rotation of angular speed two about the equilibrium. Its transit time is pi/4, not L. Additional full periods are too long.

The stationary orbit has p=1/2,q=-1/2. Solving f'=g-1/2, g'=1/2-f with the four boundary conditions gives a=1/2 and

\[
f(t)=\tfrac12+\tfrac12\sin t,\qquad
 g(t)=\tfrac12+\tfrac12\cos t.
\tag{A.14}
\]

This is the radius-one-half disk profile.

**Case 2: v>0 and the orbit reaches Q=0 first.** Put r=1+v/2. In the initial quadrant P>0,Q>0,

\[
P(t)=\tfrac12-r\sin t,\qquad Q(t)=-2+2r\cos t.
\tag{A.15}
\]

If 1<r<=sqrt(5)/2, put d=sqrt(r^2-1) in (0,1/2]. The first segment takes time arctan(d), ending at (1/2-d,0). The intermediate P>=0,Q<=0 arc has angular speed two and takes time pi/4-arctan(2d). By reflection the final segment has the same duration as the first. The total is

\[
T(d)=2\arctan d+\pi/4-\arctan(2d).
\]

Its derivative is 6d^2/((1+d^2)(1+4d^2)), so

\[
T(d)\leq T(1/2)=2\arctan(1/2)<\pi/2.
\tag{A.16}
\]

This case cannot supply the required length L.

**Case 3: the orbit reaches P=0 first.** Now r>=sqrt(5)/2 and

\[
\beta=\arcsin(1/(2r)),\qquad0<\beta\leq\arctan(1/2).
\]

The initial segment ends at (0,z), where z=cot(beta)-2>=0. In P<=0,Q>=0 the motion is a rotation of speed 1/2 about (2,-2). It proceeds to (-z,0), taking time

\[
\pi-4\arctan(2\tan\beta).
\]

The last segment is the reflected first segment. Thus

\[
T(\beta)=2\beta+\pi-4\arctan(2\tan\beta).
\tag{A.17}
\]

This formula agrees with (A.16) at the boundary r=sqrt(5)/2. Its derivative is

\[
T'(\beta)=-\frac6{1+4\tan^2\beta}<0.
\]

Its endpoint values range from the limit pi as beta tends to zero down to 2 arctan(1/2). Exactly one beta gives T=L. For that beta,

\[
2\arctan(2Y)=\pi/4+\arctan Y,\qquad Y=\tan\beta\in(0,1/2).
\]

The double-angle tangent identity, with its positive denominators on this interval at the required solution, gives

\[
\boxed{4Y^3+3Y-1=0.}
\tag{A.18}
\]

The cubic is strictly increasing, so the solution is unique.

**Lemma AF2 (classification of full stationary profiles).** An interior stationary width for the optimized full functional is either the disk width a=1/2 or the centered candidate width

\[
a_*=\frac1{3\sin\beta},
\]

with beta determined by (A.18). In the second case the whole profile is the centered candidate profile of Note 14.

**Proof.** The cases above exhaust v. In Case 3 the candidate's matched momenta have exactly the same initial values: P(0)=1/2 and Q(0)=1/sin(beta)-2. Uniqueness for the globally Lipschitz system (A.9) identifies P,Q, hence p,q, on the whole interval. Two pairs f,g with the same p,q differ by a solution of v'=w, w'=-v. Since g(0) is fixed their difference is (b cos(t),-b sin(t)), the horizontal translation mode. Requiring f(0)=g(L)=a forces b=0 between two centered pairs. The centered candidate has width a_* by the formulas in Note 14, so it is the only second profile. Case 1 gave the disk, and Case 2 is impossible. QED.

The candidate's piecewise curvature jumps are allowed here. The momenta, not second derivatives of support functions, are the continuous variables in the classification.

### A.6 The width boundary and large-width escape are controlled

A global maximum over a>=1/2 exists; this is not assumed just because stationary points have been classified.

At a=1/2 the disk pair (A.14) satisfies the fixed-width Euler equations. By Lemma AF1 it is the unique fixed-width maximizer. Direct substitution gives

\[
\Phi(1/2)=\pi/2-1/2<M.
\tag{A.19}
\]

For the strict comparison it suffices to use pi<4 and the already proved M>8/5 from Note 10.

For large a put phi=pi/8, tau=tan(phi)>0, R=a/cos(phi), B=1-a tau. The explicit pair

\[
f_a(t)=R\cos(t/2+\phi)+B\sin t,
\qquad
 g_a(t)=R\sin(t/2+\phi)+B\cos t
\tag{A.20}
\]

belongs to X_a. If a>=2/(3tau), it has

\[
p=1-\tfrac32R\sin(t/2+\phi)\leq0,
\qquad q=\tfrac32R\cos(t/2+\phi)-1\geq0.
\]

It satisfies (A.8), equivalently the P<=0,Q>=0 part of (A.9). Lemma AF1 therefore identifies it as the unique fixed-width maximizer for every such a.

This explicit pair depends affinely on a. Differentiating its value and integrating by parts, the interior Euler terms vanish and the boundary fluxes give

\[
\Phi'(a)=4P(0)-2=6-12\tau a.
\]

Consequently on this whole tail

\[
\Phi(a)=-6\tau a^2+6a+C\longrightarrow-\infty.
\tag{A.21}
\]

This calculation uses the explicit tail optimizer, not an unproved envelope differentiability assertion.

On a bounded interval of widths, the coercive estimate in the proof of AF1 is uniform after choosing boundary lifts bounded in H^1. A sequence maximizing the full functional therefore has a subsequence with convergent a, weak H^1 halves and strong L^2 halves. The same upper-semicontinuity argument as before attains the maximum. Equation (A.21) rules out escape to infinite width. Thus a global maximum on a>=1/2 is attained.

### A.7 The completed wide-profile theorem

**Theorem AF3 (unrestricted adaptive calibration for wide profiles).** Let h be any real 2pi-periodic H^1 function satisfying

\[
h(\pi/2)=1,\qquad h(3\pi/2)=0,
\qquad h(0)+h(\pi)\geq1.
\]

Then

\[
\boxed{\widetilde{\mathcal Q}(h)\leq
 M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.}
\tag{A.22}
\]

Equality holds exactly when h=h_*+b cos(theta), where h_* is the explicit candidate support profile in Note 14 and b is real.

**Proof.** Center the horizontal endpoint values using the translation invariance in Section A.1. At fixed width, Lemma AF1 and (A.7) reduce the maximum to two identical halves with the reflection symmetry (A.6). Section A.6 gives an attained maximum over a>=1/2. Its value is at least M because the explicit candidate belongs to this function domain and its adaptive value was evaluated exactly in Note 14 as cot(beta)-2+beta=M.

The width boundary has smaller value by (A.19). Hence a maximizing width is interior, so the natural boundary condition (A.11) applies. Lemma AF2 leaves only the candidate: the disk has a=1/2 and smaller value. Therefore the global maximum is M.

At equality the width must be a_*, and strict fixed-width concavity forces each half to equal the candidate half. Undoing horizontal centering gives exactly the stated translation family. Conversely those profiles attain M by translation invariance. QED.

This theorem has **no convexity, curvature cap, contact-order, monotone-contact, or feasible-motion hypothesis** on h. Its width restriction is explicit and automatic for the normalized hull of any body with area greater than one.

One nonnegative decomposition of the deficit is

\[
M-\widetilde{\mathcal Q}(h)
=\bigl(M-\Phi(a)\bigr)
+\bigl(F_a-F(f,g)\bigr)
+\bigl(F_a-F(f_\rho,g_\rho)\bigr),
\tag{A.23}
\]

where F_a=max_{X_a}F. Each term is nonnegative for a>=1/2. The last two have the strict concavity control from (A.4)-(A.5). No claim of a quantified geometric distance estimate is made for the first term here.

---

<a id="proof-signed-roof"></a>
## Technical proof 5. Unit-curvature signed-roof identity (SR)

### S.1 Hypotheses and the signed roof

Let L=pi/2. Suppose f,g belong to W^{2,infinity}(0,L), with

\[
f(L)=g(0)=1,\qquad
0\leq f''+f\leq1,\quad0\leq g''+g\leq1\quad\text{a.e.}
\tag{S.1}
\]

No inequality between p=f'-g+1 and q=g'+f-1 is imposed. On 0<t<L set

\[
R_t(x)=\frac{f(t)-1-x\cos t}{\sin t},\qquad
L_t(x)=\frac{g(t)-1+x\sin t}{\cos t}.
\]

Let W be the union of the lower forbidden quadrants, including the axis-angle quadrants. Its vertical sections are downward open half-lines. Write their finite thresholds as

\[
F(x)=\sup\{y:(x,y)\in W\}.
\tag{S.2}
\]

Equivalently, take the supremum of min(R_t,L_t) over interior angles, and include the value zero when x<f(0)-1 or x>1-g(L), as supplied by the two axis quadrants. Endpoint equalities in x do not affect any area integral. This F is the **signed** roof: it can be negative. The roof of W above the incoming baseline is F_+=max(F,0), not F itself.

Put

\[
c=(f-1)\mu+(g-1)\nu,\quad
B=c+p\nu=(f-1)\mu+f'\nu,
\quad D=c-q\mu=(g-1)\nu-g'\mu,
\]

and

\[
\ell=-g'(0),\quad r=-f'(L),\quad
x_0=f(0)-1,\quad x_1=1-g(L).
\]

The derivatives are

\[
B'=(\rho_f-1)\nu,\qquad D'=(1-\rho_g)\mu.
\tag{S.3}
\]

Thus B_x and D_x are nondecreasing, with B_x(0)=x_0, B_x(L)=r, D_x(0)=ell, D_x(L)=x_1. Also B_y>=0 and D_y>=0, using B_y(L)=D_y(0)=0.

For x<ell, L_t(x) is nonincreasing in t and has limiting value zero at t=0. For x>r, R_t(x) is nondecreasing and has limiting value zero at t=L. Consequently

\[
\{F>0\}\subseteq[\ell,r].
\tag{S.4}
\]

The axis quadrants give F>=0 off [x_0,x_1] when x_0<x_1. Therefore F is zero outside a bounded interval containing ell,r,x_0,x_1. It is bounded there: it is at most max_t c_y(t), or zero where an axis quadrant contributes, and it is bounded below by the finite roof value at t=L/2. Its signed integral is well-defined.

### S.2 Curvature makes both parameter families unimodal

The exact wall derivatives are

\[
\partial_tR_t(x)=\frac{x-B_x(t)}{\sin^2t},\qquad
\partial_tL_t(x)=\frac{x-D_x(t)}{\cos^2t}.
\tag{S.5}
\]

For fixed x, each family is nondecreasing up to its maximum set and nonincreasing afterwards. In particular its superlevel sets in t are intervals. The same is true of their minimum, whose superlevel sets are intersections of those intervals.

First assume strict curvature inequalities and analytic functions, with p and q not identically zero. Their zero sets on the closed interval can be taken finite by analytic extension; arbitrarily small homogeneous perturbations eliminate the identically-zero cases. Then B_x,D_x strictly increase on the open interval. The signed roof has the following complete list of nonconstant graph pieces:

- B(t) for p(t)<0, traversed with increasing t;
- D(t) for q(t)>0, traversed with increasing t;
- c(t) for p(t)<0<q(t), traversed with **decreasing** t;
- c(t) for q(t)<0<p(t), traversed with **increasing** t.

The last pieces are reverse corners. They must not be discarded just because the candidate uses the standard orientation.

Here is a direct verification of completeness and activity. At B(t), R has its global maximum and p<0 makes its companion L value larger. Thus min(R,L) attains the roof there. The D statement is identical with q>0. At a standard corner x=c_x(t), D_x(t)<=x<=B_x(t). For parameters s<=t, monotonicity of D_x bounds L_s(x) by L_t(x); for s>=t, monotonicity of B_x bounds R_s(x) by R_t(x). Both agree at the corner, proving global activity. At a reverse corner B_x(t)<=x<=D_x(t); use R for s<=t and L for s>=t instead.

Conversely, an interior maximizer with unequal wall heights must be a stationary point of the smaller wall, hence a B or D point with the indicated companion sign. At equal heights, the one-sided maximum test gives one of the two opposite-sign corner cases. Axis maxima lie at height zero and contribute no signed graph area. Except for finitely many joining heights/abscissae, the strictly unimodal families give a unique active parameter; a maximum interval would force a wall to be constant on a parameter interval. Thus the pieces cover the signed graph once, not with multiplicity. The finite analytic zero sets partition them into ordinary monotone graph arcs.

### S.3 Exact signed area, including reverse corners

Let

\[
I(f,g)=\frac12\int_0^L\det(c,c')\,dt.
\]

**Theorem SR1 (signed roof identity).** Under (S.1),

\[
\boxed{\int_{\mathbb R}F(x)\,dx
=-I(f,g)+\frac12\int_0^L\min(p,0)^2\,dt
+\frac12\int_0^L\max(q,0)^2\,dt.}
\tag{S.6}
\]

There is no contact-order assumption and no claim that the left side is a nonnegative area.

**Proof in the strict analytic case.** Since F is zero off a bounded interval, its graph integral is one half of integral (F-xF')dx. An increasing graph parametrization Z=(X,Y) contributes minus one half of integral det(Z,Z'); a decreasing parametrization contributes the opposite sign when written with increasing t.

Let i_p=1_{p<0}, i_q=1_{q>0}, and let chi be 1 on the standard corner set, -1 on the reverse corner set, and zero on the two equal-sign sets. The graph decomposition gives

\[
2\int F=-\int i_p\det(B,B')-\int i_q\det(D,D')+\int\chi\det(c,c').
\]

The elementary identity chi=i_p+i_q-1 holds away from the finite zero sets. The determinant identities are

\[
\det(B,B')=\det(c,c')-p^2+[(f-1)p]',
\]

\[
\det(D,D')=\det(c,c')-q^2+[(g-1)q]'.
\]

Insert them. The coefficient of det(c,c') is exactly -1. Every sign-interval endpoint derivative term vanishes: an interior endpoint has p=0 or q=0; at L, f-1=0; at 0, g-1=0. The only other potential terms do not occur because p(0)>=0 and q(L)<=0. Those two signs follow from

\[
p(0)=1-\int_0^L\rho_f\cos t\,dt,\qquad
q(L)=-1+\int_0^L\rho_g\sin t\,dt.
\]

The remaining terms give (S.6).

**Passage to weak bounds.** Approximate each bounded density rho in L^1 by real analytic densities in (0,1), and solve f''+f=rho_f and g''+g=rho_g with the original endpoint values. The Dirichlet operator on length L has a bounded Green kernel and derivative kernel, so these solutions converge in C^1. A vanishing homogeneous adjustment, preserving f(L)=g(0)=1, avoids identically-zero p,q without changing the density bounds. Each resulting analytic formula extends past the closed interval; hence the sign sets are finite unions of intervals unless identically zero, which was excluded.

The right side of (S.6) converges by C^1 convergence. For the left side, all roofs have common bounded support and a common finite bound. On every compact interior angular interval their wall functions converge uniformly for bounded x. Near an axis, the corner heights are uniformly O(t) or O(L-t); when an endpoint quadrant applies it contributes zero, and otherwise, away from the two limiting endpoint abscissae, the appropriate wall tends to minus infinity. This proves pointwise roof convergence except possibly at those two abscissae. Dominated convergence gives the signed integral identity. This limiting step concerns wall envelopes, not presumed feasibility of interpolated convex bodies. QED.

---

<a id="proof-arm"></a>
## Technical proof 6. Support area, reference cap and local arm geometry (AR)

**Scope and notation.** The domain used here consists of compact
downward convex caps in \(0\le y\le1\), normalized to height one.
Let \(N(U)\) be the full positive two-wall niche,
\(\mathcal A(U)=|U|-|N(U)|\), and
\(\Psi(U)=\mathcal A(U)-W/2\). The notation PA.1 below refers to this
explicit domain, not to an additional attainment theorem.
The selected material proves the support-area identity, its
unit-curvature comparison, the reference value, and an elementary
finite neighboring-wall lemma. Weighted-maximizer propagation results
from the intervening historical sections are not used.

### 1. Notation and the two endpoint arms

Use the domain PA.1. For a normalized cap U with upper support h write L=pi/2,

$$
f(t)=h(t),\quad g(t)=h(t+L),\quad p=f'-g+1,\quad q=g'+f-1,\quad \rho_f=f''+f,\quad \rho_g=g''+g
$$

on 0<t<L. Let `[x_L,x_R]` be the horizontal projection, `[x_tl,x_tr] x {1}` the top face (possibly a point), W=x_R-x_L and T=x_tr-x_tl.

Whenever the quarter supports are in W^(2,infinity), p and q are Lipschitz with one-sided traces and satisfy the kinematic identities

$$
p'=\rho_f-1-q,\qquad q'=\rho_g-1+p\qquad\text{a.e.}
$$

Near the vertical normal the support points are the two ends of the top face. Hence h'(L-)=-x_tr and h'(L+)=-x_tl, while h(0)=x_R and h(pi)=-x_L. Substituting,

$$
\boxed{q(0)=x_R-x_{tl}-1,\qquad p(L)=1-(x_{tr}-x_L).}
\tag{AR.1}
$$

Thus 1+q(0) is the horizontal distance from the far end of the top face to the right end of the cap, and 1-p(L) is the mirror distance. These are Baek's two arms at the start and end of the turn. Also W+T=2+q(0)-p(L).

Put c=(f-1)mu+(g-1)nu, the inner corner, and

$$
C(f,g)=\frac12\int_0^L(f^2-f'^2+g^2-g'^2)\,dt,\qquad
I(f,g)=\frac12\int_0^L\det(c,c')\,dt,
$$

$$
S(f,g)=-I(f,g)+\frac12\int_0^L(p_-^2+q_+^2)\,dt .
$$

Since c'=p mu+q nu, direct expansion gives det(c,c')=(f-1)^2+(g-1)^2+(f-1)g'-(g-1)f'. Comparing with (A.1),

$$
F(f,g)=C+I-\frac12\int_0^L(p_-^2+q_+^2)\,dt=C(f,g)-S(f,g).
\tag{AR.2}
$$

S is the right side of SR1's identity (S.6). To avoid a clash with the functional F of (A.1), the signed roof of SR1 is written Lambda here; its negative-part magnitude is Lambda_-=max(-Lambda,0).

**Lemma AR0 (Baek's arms are nonnegative).** For every normalized cap whose quarter supports are C^1 on (0,L),

$$
p\le1,\qquad q\ge-1\qquad\text{on }(0,L).
$$

**Proof.** The support point f mu_t+f' nu_t lies in U, which lies in the half-plane z.nu_t<=g(t); hence f'<=g. The support point g nu_t-g' mu_t lies in z.mu_t<=f(t); hence -g'<=f. QED.

### 2. Cap area as a support integral

**Lemma AR1.** Every normalized cap satisfies

$$
\boxed{|U|=\frac12\int_0^\pi(h^2-h'^2)\,d\theta=C(f,g).}
\tag{AR.3}
$$

**Proof.** For a planar convex body, 2|U| is the integral of h against the length measure S_U on the circle. On the open lower half circle S_U is the bottom-edge atom at 3pi/2, where h=0; the two bottom corners carry no length. On [0,pi], S_U consists of the end-edge atoms e_R=h'(0+) and e_L=-h'(pi-), plus the measure h dtheta+d(h') on the open interval (0,pi). The latter includes the top-face atom at L.

The function h is Lipschitz and h' has bounded variation with one-sided limits. Hence

$$
\int_{(0,\pi)}h\,d(h')=h(\pi)h'(\pi-)-h(0)h'(0+)-\int_0^\pi h'^2\,d\theta .
$$

Adding h(0)e_R+h(pi)e_L cancels both endpoint products. QED.

### 3. The signed objective under unit curvature

**Proposition AR2.** Let U be a normalized cap whose quarter supports belong to W^(2,infinity)(0,L) with 0<=rho_f,rho_g<=1 a.e. Then

$$
\boxed{\mathcal A(U)=F(f,g)-\int_{\mathbb R}\Lambda_-\,dx\le F(f,g).}
\tag{AR.4}
$$

If W>=2, then Lambda>=0 almost everywhere and A(U)=F(f,g).

**Proof.** By PA.1 the vertical section of N(U) over x is the half-open interval from 0 to sup_t min(R_t(x),L_t(x)) over interior angles, or is empty. The axis quadrants included in SR1's roof only contribute the value zero. Hence Lambda_+ is the positive part of that interior supremum, and |N(U)|=integral Lambda_+.

Height one gives f(L)=g(0)=1, so SR1 applies and integral Lambda=S. Therefore |N(U)|=S+integral Lambda_-, and AR1 with AR.2 gives A(U)=C-S-integral Lambda_- = F-integral Lambda_-.

If W=f(0)+g(L)>=2, then x_0=f(0)-1>=1-g(L)=x_1. Every x except possibly one point satisfies x<x_0 or x>x_1. There an axis quadrant gives Lambda(x)>=0. QED.

This is the one-turn form of SR2. There is no clipping term because PA.1 subtracts the whole niche.

### 4. The candidate cap has value M/2

Recall AF2, Case 3. Y=tan(beta) is the root of 4Y^3+3Y-1=0, equivalently of (A.18). Then

$$
M=1+4Y^2+\arctan Y=\cot\beta-2+\beta,\qquad a_*=\frac1{3\sin\beta}.
$$

The centered candidate half (f_*,g_*) in X_(a_*) has momenta P(0)=1/2 and Q(0)=1/sin(beta)-2. Its orbit has three parts:

- an initial segment in {P,Q>=0} ending at (0,z), with z=cot(beta)-2;
- a rotation in {P<=0<=Q} from there to (-z,0);
- the mirror final segment, ending at (-Q(0),-1/2).

Use rho_f=p'+1+q and rho_g=q'+1-p, with P=p+p_- and Q=q+q_+. Then (A.9) becomes

$$
\begin{array}{lll}
\{p,q\ge0\}:&\rho_f=0,&\rho_g=\tfrac12;\\
\{p\le0\le q\}:&\rho_f=\tfrac{1+q}2,&\rho_g=\tfrac{1-p}2;\\
\{p,q\le0\}:&\rho_f=\tfrac12,&\rho_g=0.
\end{array}
\tag{AR.5}
$$

On the rotation, 0<=q<=z/2 and -z/2<=p<=0. On the first segment, q=Q/2<=Q(0)/2.

The cubic 4Y^3+3Y-1 is increasing and changes sign on (0.29,0.30). Hence sin(beta) lies in (0.277,0.288), cot(beta) in (3.33,3.45), and z in (1.33,1.45). Consequently

$$
0\le\rho_f,\rho_g\le\tfrac14\cot\beta<1,\qquad
W_*=2a_*=\frac2{3\sin\beta}>2 .
\tag{AR.6}
$$

The mirror symmetry (A.6) gives p(L)=-q(0). Hence the two arms and the top face are

$$
1+q(0)=1-p(L)=\frac1{2\sin\beta}\approx1.7506,\qquad T_*=2+2q(0)-W_*=a_*.
\tag{AR.7}
$$

Let U_* be the normalized cap with upper support h_*, the downward saturation of the candidate hull. It is a genuine cap: rho>=0 on both open quarters, the end-edge atoms are p(0)=1/2 and -q(L)=1/2, the top-face atom is T_*>0, and h_*(L)=1.

**Proposition AR3.** Psi(U_*)=M/2.

**Proof.** By AR.6 the hypotheses of AR2 hold and W_*>2, so A(U_*)=F(f_*,g_*). The adaptive value of h_* is M (Note 14). By the equality analysis in the proof of AF3, both halves of h_* are the unique fixed-width maximizer on X_(a_*). Hence M=2F(f_*,g_*)-2a_*, and Psi(U_*)=F(f_*,g_*)-a_*=M/2. QED.

**Discrete lemma.** Use any grid caps with spacing delta and finite niche N_n, the union of open quadrants Q_i for 1<=i<n. Fix 2<=j<=n-2 and keep WR §1 and §4 notation: f=h_j, g=h_(j+n), c, s, T=tan(delta/2), mu=mu_(theta_j), nu=nu_(theta_j). Write

$$
d^\pm,\ d_\pm:\ \text{the one-sided derivatives of }h\text{ at }\theta_j\text{ and }\theta_{j+n},
$$

$$
p_\pm=d^\pm-g+1,\qquad q_\pm=f+d_\pm-1,\qquad \ell_j=d^+-d^-,\qquad \ell_{j+n}=d_+-d_- .
$$

For a grid polygon these are exact: between consecutive grid normals the support point is a fixed vertex. So d^+=(h_(j+1)-cf)/s, d_+=(h_(j+n+1)-cg)/s, and similarly for the left derivatives. Recall mu_(j±1)=c mu±s nu and nu_(j±1)=∓s mu+c nu.

(a) If p_+>T and q_+>T, the first inner-wall ray x(v)=(f-1)mu+v nu, v<=v_0=g-1, lies in the open quadrant Q_(j+1). Hence the exposed length tau_j of the finite first-wall ray is zero.

(b) If p_+>T and q_-+T>=tan(delta)(p_-+T), the companion ray y(u)=(g-1)nu+u mu, u<=f-1, has exposed length

$$
\tau_{j+n}\le(2T-\ell_{j+n})_+ .
$$

*Proof of (a).* The two defining inequalities of Q_(j+1) on the first ray read

$$
v<d^+-T\quad(\text{and }d^+-T-v_0=p_+-T),\qquad
v<v_+\quad(\text{and }v_+-v_0=\tan\delta\,(q_+-T),\ \text{WR §4}).
$$

Both thresholds exceed v_0. The whole ray, including its corner, is therefore inside an open quadrant. Its points above the floor are interior points of N_n.

*Proof of (b).* On the companion ray the four inequalities are:

- Q_(j+1), first wall: u<f-1+tan(delta)(p_+-T);
- Q_(j+1), second wall: u>T-d_+;
- Q_(j-1), second wall: u<-d_--T;
- Q_(j-1), first wall: u<f-1-tan(delta)(p_-+T).

When p_+>T, Q_(j+1) covers T-d_+<u<=f-1. When q_-+T>=tan(delta)(p_-+T), the last threshold is at least -d_--T, so Q_(j-1) covers u<-d_--T. The exposed part lies in [-d_--T, T-d_+], of length (2T-ell_(j+n))_+. QED.

---

<a id="proof-neighboring-walls"></a>
## Technical proof 7. Neighboring-wall geometry and exact threshold identities (WR)

**Scope.** This excerpt contains only the geometric adjacent-wall
estimate WR.1 and its exact threshold refinements. It does not import
the historical weighted first variation or its limiting curvature
argument. RG3 supplies the full spatial limit with the uncharged
middle-facet errors accounted for, and PS supplies the partial spatial
limit with its actual-versus-circumscribed facet comparison. Those
complete proofs are included separately.

### 1. The local line calculation

Let a grid cap have spacing delta<=pi/4, height at most one, and supports h_j at theta_j=j delta. Fix a first-quarter interior index 1<=j<n and write

$$f=h_j,\quad g=h_{j+n},\quad c=\cos\delta,\quad s=\sin\delta,\quad T=\tan(\delta/2).$$

The outer facet length is

$$\ell_j=(h_{j-1}+h_{j+1}-2cf)/s.$$

Parameterize its corresponding inner wall by

$$x(v)=(f-1)\mu_{\theta_j}+v\nu_{\theta_j},\qquad v\le v_0:=g-1.$$

The two neighboring companion inner walls give parameter thresholds

$$v_-=(h_{j+n-1}-1-(f-1)s)/c,\qquad
v_+=(h_{j+n+1}-1+(f-1)s)/c.$$

The two neighboring first walls give

$$v_{
m lo}=(h_{j+1}-1-(f-1)c)/s,\qquad
v_{
m hi}=((f-1)c-h_{j-1}+1)/s.$$

Any point of this ray on the boundary of the finite niche is, except for its corner and its possible floor intersection, in

$$[\min(v_-,v_+),v_0]\ \cup\ [v_{
m lo},v_{
m hi}].$$

Indeed, if it satisfies a neighboring companion-wall alternative, it lies in the first interval. Otherwise it must satisfy both neighboring first-wall alternatives to avoid their open quadrants and lies in the second interval. The endpoint-angle quadrants used for j=1 or j=n-1 have no part above the floor because the cap height is at most one; the same alternatives therefore remain valid there. No curvature or maximizing premise is used.

Taking lengths gives

$$\boxed{\tau_j\le (v_0-\min(v_-,v_+))_++(2T-\ell_j)_+.}
\tag{WR.1}
$$

The equality v_hi-v_lo=2T-ell_j is direct subtraction. Floor clipping can only shorten these intervals; no niche is clipped to the outer cap.

### 4. Retain the sharper neighboring-wall information

At the companion normal let

$$d_-=(gc-h_{j+n-1})/s,\qquad d_+=(h_{j+n+1}-gc)/s,$$

the two one-sided support derivatives. Define q_-=f+d_--1 and q_+=f+d_+-1, with q_-<=q_+. Direct algebra in WR.1 gives

$$v_0-v_-=\tan\delta(q_-+T),\qquad
v_0-v_+=\tan\delta(-q_++T).$$

Thus

$$\tau_j\le\tan\delta(|q_+|+T)+(2T-\ell_j)_+.$$

---

<a id="proof-visible-flux"></a>
## Technical proof 8. Actual visible-source flux and its finite limit (VE)

**Local visible-graph hypotheses.** Use the finite source sequences
from FE/RG with LH, or from PS: their first- and second-wall exposed
length measures converge weakly on the interval in question to
\(u(t)\,dt\), \(v(t)\,dt\). Supports converge uniformly and are uniformly
bounded and Lipschitz. Set \(L=\pi/2\), \(u=f''+f\), \(v=g''+g\),
\(p=f'-g+1\), \(q=g'+f-1\), and
\[
c=(f-1)\mu_t+(g-1)\nu_t,\qquad D=c-q\mu_t.
\]
Then \(c'=p\mu_t+q\nu_t\), \(D'=(1-v)\mu_t\).
The local application assumes positive-height Lipschitz roof graphs:
the corner graph has \(p<0<q\) and a unique maximizing angle;
the second-wall tangency graph has \(0\le v\le1\), a strict companion
gap, and a unique maximizing angle outside the images of its constant
parameter intervals. Each graph piece lies compactly inside the
charged middle window \(J\), and its source angles lie in a compact
regular visited interval avoiding omitted, terminal and exceptional
facet normals. Thus its physical exposure is counted by the spatial
source measures. The two graph images are disjoint when their
contributions are added. CH proves these visibility and separation
hypotheses in its application, as do the specified later local source
arguments. The following section proves the finite tangent-flux limit
under these stated hypotheses; it does not assert global visibility
for an arbitrary cap.

### 3. How finite exposed edges converge on a unique-source graph

Let U_n be a sequence satisfying the stated local hypotheses and let n_n be its finite positive niche roof. Denote by nu_n^f and nu_n^g the measures that assign to each grid angle the total exposed first- or second-wall length. By hypothesis they converge weakly to u(t)dt and v(t)dt, respectively.

The following local facts justify reading part of those limiting measures from the positive unique-source graphs specified in the prelude. Details are included because uniform convergence of curves alone would not preserve their ordinary perimeter.

#### Local uniform roof convergence and bounded slopes

Near any compact positive-height piece of the limiting roof, all active parameters of sufficiently large n stay in a fixed compact subinterval of (0,L). Indeed the finite corner heights are at most C t near zero and C(L-t) near L, uniformly in n: supports are uniformly bounded and Lipschitz, and the finite cap height is at most one. A quadrant cannot reach above its corner. Positive-height points therefore exclude endpoint parameters uniformly.

On that remaining compact angular interval, both wall families are uniformly Lipschitz in x, and their support offsets converge uniformly. Density of the nested angle meshes gives local uniform convergence of their max-min roofs. In particular n_n -> n uniformly near these pieces, and their graph slopes have a common bound.

#### Localization of active parameters

Suppose a limiting positive roof point has a unique maximizing parameter t. Any sequence of nearby finite exposed points and their source angles has a convergent subsequence. The wall equalities, companion inequalities and local uniform convergence show that its limiting angle attains the full roof at the limiting point. Uniqueness forces that angle to be t. This also proves uniform angle localization on compact sets of such points by a subsequence contradiction.

On a second-wall tangency with strict companion gap, only second-wall sources can occur eventually in such a compact neighborhood. For the D graph, the exceptions are its countably many plateau image points. They can be removed in arbitrarily small total x-length. Because the slopes and angle ranges are uniformly bounded, the corresponding finite graph lengths and exposure masses are bounded by a constant times that removed x-length. Thus they do not obstruct the limiting statement. The inverse parameter along the remaining monotone D graph is continuous at every unique-source point.

#### Tangent flux, including alternating first and second edges

Orient a finite roof graph in the direction of increasing x. A first-wall edge of length ds has tangent -nu_theta=(sin theta,-cos theta); a second-wall edge has tangent mu_theta=(cos theta,sin theta). Thus, as vector measures along the graph,

$$
(dx,dy)=(-\nu_\theta)d\mu_n^f+(\mu_\theta)d\mu_n^g,\tag{VE.4}
$$

where mu_n^f,mu_n^g are the physical exposed-length measures there. Since the angular range stays away from the axes, both tangent x-components have a uniform positive lower bound. Total exposed length is consequently controlled by the x-length of the graph interval.

The x-flux is Lebesgue measure. The y-flux is the distributional derivative of n_n, which converges weakly to that of n by uniform convergence and the common slope bound. Active-angle localization lets the coefficients in VE.4 be replaced in the limit by the unique-source angle t(x). Solving the two-by-two linear system gives

$$d\mu^g=\cos t(x)\,dx+\sin t(x)\,dy,\qquad
 d\mu^f=\sin t(x)\,dx-\cos t(x)\,dy.\tag{VE.5}$$

This identifies the two limiting source lengths, not the sum with the ordinary arc length. Alternating staircase edges are retained by the two coefficients. For continuous compactly supported angular weights, the same equations hold after multiplying by that weight composed with t(x). Approximation after removing the plateau image points gives the D-graph conclusion as well.

On D(t), oriented with increasing t, dx=(1-v)cos(t)dt and dy=(1-v)sin(t)dt. VE.5 therefore gives second-wall contribution (1-v)dt and zero first-wall contribution. This also follows directly from its strict companion gap.

On c(t), increasing x corresponds to decreasing t, so

$$(dx,dy)=-[p\mu_t+q\nu_t]dt$$

when dt denotes positive parameter measure on J and the path orientation has been reversed. VE.5 gives second-wall contribution -p dt and first-wall contribution q dt. Both are nonnegative in the specified sign regime.

These identities may first be applied on slightly smaller graph intervals with continuous cutoffs. Exhausting J removes endpoint terms; neither endpoints nor plateau image points contribute to the limiting absolutely continuous angular measures. All remaining parts of the finite niche add nonnegative exposure.

---

<a id="proof-full-domain"></a>
## Technical proof 9. Full-cap height, width, continuity and attainment (SD)

### 1. The sharp scalar theorem and its full-turn implication

Let \(U\subset\mathbb R\times[0,1]\) be a compact convex **downward closed** cap whose horizontal projection \(I_U=[l,r]\) has width \(W=r-l>0\). Write \(A_U(x)=\max\{y:(x,y)\in U\}\). For \(0<t<L=\pi/2\), put \(u_t=(\cos t,\sin t)\), \(v_t=(-\sin t,\cos t)\) and define the **entire attached-two-ray** forbidden roof
\[
R_t(x)=\frac{h_U(u_t)-1-x\cos t}{\sin t},\qquad
D_t(x)=\frac{h_U(v_t)-1+x\sin t}{\cos t},
\]
\[
\boxed{n_U(x)=\max\{0,\sup_{0<t<L}\min(R_t(x),D_t(x))\}.}\tag{SD.1}
\]
This is the true positive *ambient* niche roof: it is not truncated to the cap and is not the area of a single selected angle. Define the **moving middle-half window**
\[
J(U)=[l+W/4,r-W/4],\qquad |J(U)|=W/2
\]
and the scalar spatial score
\[
\boxed{\mathcal P(U)=
\int_{I_U\setminus J(U)}A_U(x)\,dx
-\int_{J(U)}n_U(x)\,dx.}\tag{SD.2}
\]
The scalar theorem, proved in [G1C1](#proof-full-closure), is
\[
\boxed{\mathcal P(U)\le M/2
\quad\text{for every normalized height-one downward convex cap }U.}
\tag{SD.3 — PROVED}
\]
Here \(M=1+4Y^2+\arctan Y\), \(4Y^3+3Y-1=0\), \(Y>0\).

**Theorem SD1 (sharp spatial dual implies the full Gate 1 theorem).**
The completed scalar bound SD.3 implies \(|S|\le M\) for **every compact connected full-conventional-two-turn sofa**, without restrictions on vertical span, curvature, symmetry, face order, contact changes or polygon complexity.

**Proof.** For such a genuine sofa put \(K=\operatorname{conv}S\), and let \(U,V\) be its downward upper and reflected-lower convex caps. Their horizontal projections are the same I. Write \(d_U=1-A_U\), \(d_V=1-A_V\), and let \(n_U,n_V\) be their full positive niches. By the completely audited Gate 0 fiber formula, at each x
\[
\ell_K(x)=1-\max\{d_V(x),n_U(x)\}
             -\max\{d_U(x),n_V(x)\}\ge0.
\]
For x in the common middle half J, drop the outer deficits:
\(\ell_K\le1-n_U-n_V\).
For x outside J, drop the two niche terms:
\(\ell_K\le A_U+A_V-1\).
Integrate and use \(|J|=|I\setminus J|=W/2\) to cancel constants:
\[
\boxed{|S|\le|E_{\rm full}(K)|
=\int_I\ell_K
\le\mathcal P(U)+\mathcal P(V)\le M.}\tag{SD.4}
\]
No unearned subtraction of **untruncated** niches from K occurs: the two upper relaxations hold pointwise precisely because of the max operation.

The same inequalities hold for *signed* fibers of an arbitrary auxiliary convex K. Thus SD.3 also gives \(\mathscr S(K)\le M\) on the whole Gate 0 signed convex-hull domain, without applying facet triangles to incompatible hulls. \(\square\)

**Exact sharpness:** For Romik's reference cap \(U_*\), its full niche is supported in the central interval \(J(U_*)\), the upper roof is exactly one there, and the spatial upper relaxation SD.4 is **equality**. The explicit reference area identity therefore gives
\[
\boxed{\mathcal P(U_*)=M/2.}\tag{SD.5}
\]
This is the previously recognized exact equality in [SPB1](#main-equality). Its existing failure of **global Minkowski concavity** ([CN](https://github.com/vltanh/lean4-moving-sofa/blob/b525305f344e635e6264cb470514d6b8bb7a8e43/docs/ambidextrous/candidate-functional-concavity-counterexample.md)) does *not* disprove the proposed global **value** bound SD.3. Do not try to prove it via that false Jensen statement.

### 2. **Global** vertical-height saturation for this exact spatial score

**Lemma SD2 (extrusion monotonicity).** Let U have actual vertical height H≤1. For every \(0\le\varepsilon\le1-H\), define
\[
U_\varepsilon=U+[0,\varepsilon]e_y.
\]
This is a downward convex cap with the same horizontal projection and width, and
\[
\boxed{\mathcal P(U_\varepsilon)\ge\mathcal P(U).}\tag{SD.6}
\]

**Proof.** The outer roof rises by precisely \(\varepsilon\) at **every x of I**. For any upward unit normal n, the support of \(U_\varepsilon\) exceeds that of U by \(\varepsilon n_y\). Hence at every lower-turn angle the first supporting inner-ray roof rises exactly by \(\varepsilon\), and so does the second:
\[
R_t^{U_\varepsilon}(x)=R_t^U(x)+\varepsilon,\qquad
D_t^{U_\varepsilon}(x)=D_t^U(x)+\varepsilon.
\]
The signed ambient angular supremum rises by \(\varepsilon\). Taking the positive part is 1-Lipschitz, so
\[
0\le n_{U_\varepsilon}(x)-n_U(x)\le\varepsilon
\quad\text{for every }x.
\]
The *exterior-half outer area* increases by exactly \(\varepsilon W/2\); the *central-half niche area* increases by at most \(\varepsilon W/2\). Subtract to get SD.6. \(\square\)

Thus any global upper value theorem restricted to actual **height one** automatically holds for *all* downward caps of height≤1, including those induced by a subunit-height common hull. There is no unsupported monotone-padding assertion for actual **two-handed sofa areas**: the operation is applied solely to the one-cap *dual score*, which obeys the exact inequality above. Known counterexamples to padding the genuine sofa therefore do not contradict SD2.

### 3. **Global** width coercivity: only \(8/5<W<6\) can beat the candidate score

Translation invariance permits centering I at zero, so \(I=[-W/2,W/2]\) and \(J=[-W/4,W/4]\). Since \(A_U(x)\le1\) and \(n_U\ge0\),
\[
\boxed{\mathcal P(U)\le W/2.}\tag{SD.7}
\]
The established exact root bound \(M>8/5\) shows that no cap with \(W\le8/5\) can attain the reference value \(M/2\).

For large W use **one real inner-wall angle with both genuine support witnesses**. At \(t=\pi/4\), support against actual points in U at horizontal extremes gives
\[
h_U(u_{\pi/4})\ge\frac{W}{2\sqrt2},
\qquad h_U(v_{\pi/4})\ge\frac{W}{2\sqrt2}.
\]
This uses only that U is contained in \(y\ge0\), not its support-contact type. The two physical ray roofs at that angle therefore satisfy
\[
R_{\pi/4}(x)\ge W/2-\sqrt2-x,\qquad
D_{\pi/4}(x)\ge W/2-\sqrt2+x.
\]
Their minimum and the full angular supremum give the **universal true-niche lower bound**
\[
\boxed{n_U(x)\ge(W/2-\sqrt2-|x|)_+.}\tag{SD.8}
\]
For \(W\ge6>4\sqrt2\), the expression inside the positive part is nonnegative throughout J. Hence
\[
\begin{aligned}
\int_Jn_U(x)dx
&\ge\int_{-W/4}^{W/4}(W/2-\sqrt2-|x|)dx\\
&=\frac{3W^2}{16}-\frac{\sqrt2 W}{2},
\\
\boxed{\mathcal P(U)}
&\le \frac{(1+\sqrt2)W}{2}-\frac{3W^2}{16}.
\end{aligned}\tag{SD.9}
\]
The final quadratic is strictly decreasing for \(W\ge6\); at six it equals \(3\sqrt2-15/4<3/4<M/2\), using only \(\sqrt2<3/2\) and \(M>8/5\). Thus **any cap attaining or exceeding** \(M/2\) has
\[
\boxed{8/5<W<6.}\tag{SD.10}
\]
These are deliberately conservative exact bounds. No uniform curvature, polygon count, positive-face length or candidate proximity is assumed.

### 4. Attainment and continuity of the spatial-score maximization

**Lemma SD3 (the one-cap scalar variational problem is compact and attained).** Define
\[
\mathcal P_{\max}=\sup\{\mathcal P(U):U\text{ downward compact convex cap of height }\le1\}.
\]
Then \(\mathcal P_{\max}\ge M/2\) and is attained by some **height-one** convex cap whose horizontal width lies strictly between \(8/5\) and 6. No regularity of its exposed curvature measure is assumed.

**Proof.** The reference U* supplies the lower bound. By SD2 and SD.10, a maximizing sequence may be taken with height exactly one and widths in the compact interval \([8/5,6]\). Translate each projection's left endpoint to zero. All caps lie in \([0,6]\times[0,1]\); by compactness of convex bodies (or uniform convergence of support functions), a subsequence converges in Hausdorff distance to a downward convex cap U of height one and nonzero width in the same compact range.

The outer-roof functions converge in L1 on [0,6]. One direct proof uses that the cap graphs define nested-from-below vertical intervals, convex-body indicator functions converge almost everywhere away from their null-area boundaries under Hausdorff convergence, and all indicators lie in the bounded fixed box; dominated convergence gives convergence of symmetric-difference area, equal to the L1 roof difference.

The **full all-angle niche roofs** also converge uniformly on the fixed box. If \(\eta=\|h_{U_j}-h_U\|_\infty\to0\), truncate the angle set to \([\delta,L-\delta]\). On this compact angular interval both physical ray denominators are at least \(\sin\delta\), so the corresponding two-ray roof and its maximum vary by at most \(\eta/\sin\delta\). At the omitted near-axis intervals, the first (near \(t=L\)) or second (near \(t=0\)) ray is at height at most \(C\delta\) **uniformly** for every cap in the fixed box: this follows from \(h_C(e_y)\le1\), the common support-function angular Lipschitz bound, and \(x\in[0,6]\). Thus
\[
\|n_{U_j}-n_U\|_{L^\infty([0,6])}
\le C'\delta+\frac{\eta}{\sin\delta}.
\]
Choosing \(\delta=\sqrt\eta\) (for small \(\eta\)) makes the right side tend to zero. Importantly this **does not assume the same maximizing angle or contact chart** in the approximating cap.

Finally the endpoints of the *moving* middle-half J(U_j) converge because their widths converge. The outer-roof L1 convergence, uniform niche convergence and uniformly bounded roof heights imply \(\mathcal P(U_j)\to\mathcal P(U)\). The limit therefore attains the maximum. Apply height extrusion if needed (it is already height one here). \(\square\)

This establishes the compact infinite-dimensional scalar problem used by the [completed Gate 1 proof](#proof-full-closure). That proof applies canonicalization and the audited spatial source laws to a selected attained maximizer, bounds its horizontal branch, and excludes every tilted branch. It thereby computes the maximum as \(M/2\) and extends the bound to the entire cap domain by SD2.

---

<a id="proof-middle-chord"></a>
## Technical proof 10. The exact middle-chord and height reduction (MID)

### 1. A chord cut changes only the uncharged middle roof

Let U be any nonempty compact convex downward-closed cap contained in \(\mathbb R\times[0,1]\), with nondegenerate horizontal projection \(I=[l,r]\) and width \(W>0\). Its concave upper-roof function is \(A(x)\ge0\). Define
\[
j_-=l+W/4,\qquad j_+=r-W/4,\qquad J=[j_-,j_+].
\tag{MID.1}
\]
Both \(j_\pm\) belong to the *interior* of I, so \(A(j_\pm)>0\) when U has positive area; degenerate zero-area caps are harmless and can be excluded at a positive global maximizer. Put
\[
\ell(x)
=A(j_-)+\frac{A(j_+)-A(j_-)}{j_+-j_-}(x-j_-).
\tag{MID.2}
\]

**Lemma MID1 (global chord ordering).** Every concave \(A:I\to\mathbb R\) satisfies
\[
A(x)\ge\ell(x)\quad (x\in J),\qquad
A(x)\le\ell(x)\quad(x\in I\setminus J).
\tag{MID.3}
\]

**Proof.** The first assertion is exactly concavity above a chord. For \(x<j_-\), write \(j_-=(1-s)x+sj_+\) with \(0<s<1\). Concavity gives \(A(j_-)\ge(1-s)A(x)+sA(j_+)\); solve for \(A(x)\le\ell(x)\). The right exterior interval follows by exchanging the endpoints. In particular \(\ell(x)\ge A(x)\ge0\) outside J and \(\ell(x)\ge0\) inside J as a convex combination of nonnegative chord heights. \(\square\)

Define the actual compact convex **chord-clipped cap**
\[
\boxed{U^\flat=U\cap\{(x,y):y\le\ell(x)\}.}\tag{MID.4}
\]
It retains the same full baseline \(I\times\{0\}\), hence the same projection I and width W; it is downward closed and convex. Its upper roof is precisely
\[
\boxed{
A^\flat(x)=
\begin{cases}
A(x),&x\notin J,\\
\ell(x),&x\in J.
\end{cases}
}\tag{MID.5}
\]
Thus **all charged outer roof area** in the spatial score,
\(\int_{I\setminus J}A(x)dx\), is **identical** before and after chord clipping.

### 2. The *entire physical moving-wall niche* cannot grow

For every lower-turn angle \(0<t<L=\pi/2\) write
\[
u_t=(\cos t,\sin t),\quad v_t=(-\sin t,\cos t),\quad
q_{U,t}(x)=\min\left(
\frac{h_U(u_t)-1-x\cos t}{\sin t},
\frac{h_U(v_t)-1+x\sin t}{\cos t}
\right).
\tag{MID.6}
\]
The complete positive two-ray niche roof is
\(n_U(x)=\max(0,\sup_{0<t<L}q_{U,t}(x))\).
Because \(U^\flat\subseteq U\), the genuine convex **outer supports** satisfy \(h_{U^\flat}(n)\le h_U(n)\) for **all** directions n. Therefore both attached inner-ray heights weakly decrease for **every** t and x:
\[
q_{U^\flat,t}(x)\le q_{U,t}(x),\qquad
\boxed{n_{U^\flat}(x)\le n_U(x)\quad\text{for every }x.}
\tag{MID.7}
\]
This includes the physical corner path, arbitrary switches of the maximizing angle, and any number of disconnected angular superlevel components. We do **not** assume a stable contact order or smoothness.

For the width-dependent spatial score
\[
\mathcal P(U)=\int_{I\setminus J}A_U(x)\,dx-\int_Jn_U(x)\,dx
\]
the two exact facts MID.5 and MID.7 give
\[
\boxed{
\mathcal P(U^\flat)-\mathcal P(U)
=\int_J[n_U(x)-n_{U^\flat}(x)]dx\ge0.
}\tag{MID.8}
\]
No ambient niche is incorrectly subtracted from a two-handed hull here: \(\mathcal P\) is a **one-cap dual score**, not an ordinary physical sofa area, and its use as a global *upper relaxation* is justified separately by [SD1](#proof-full-domain).

### 3. Restore unit height without losing the score

The clipped cap may have maximal vertical coordinate \(H^\flat\in(0,1]\). Let
\[
\varepsilon=1-H^\flat\ge0,\qquad
\boxed{U^\sharp=U^\flat+[0,\varepsilon]e_y.}\tag{MID.9}
\]
The upper roof is \(A^\sharp=A^\flat+\varepsilon\); it is still **affine on J**. Both inner-wall supports gain precisely \(\varepsilon\sin t,\varepsilon\cos t\), so each full ray roof \(q_{U^\sharp,t}(x)=q_{U^\flat,t}(x)+\varepsilon\). Taking max with zero gives
\[
0\le n_{U^\sharp}(x)-n_{U^\flat}(x)\le\varepsilon.
\]
The exterior charged roof increases by \(\varepsilon|I\setminus J|=\varepsilon W/2\), while the middle charged niche increases by at most \(\varepsilon|J|=\varepsilon W/2\). Consequently
\[
\boxed{
\mathcal P(U^\sharp)\ge\mathcal P(U^\flat)\ge\mathcal P(U).
}\tag{MID.10}
\]
The transformed U-sharp is again a compact convex downward cap of **exact height one** and the **same width W**, and has one affine upper segment across all of J. The operation is explicit and does not invoke an optimizer, a curvature cap, a chosen ray witness, or a feasibility-preserving deformation of the *actual physical sofa*.

### 4. A necessary sharp-value reduction of the entire infinite-dimensional problem

Define the canonical subclass
\[
\mathcal C_{\rm chord}=
\{U:\ U\text{ is downward compact convex, has height 1, width }W>0,\,
 A_U|_{[l+W/4,r-W/4]}\text{ is affine}\}.
\tag{MID.11}
\]

**Theorem MID2 (exact supremum reduction).**
\[
\boxed{
\sup_{\text{all downward convex height}\le1\text{ caps }U}\mathcal P(U)
=
\sup_{U\in\mathcal C_{\rm chord}}\mathcal P(U).
}\tag{MID.12}
\]
Furthermore, because [SD3](#proof-full-domain) establishes attainment of the original scalar supremum in the range \(8/5<W<6\), the supremum on \(\mathcal C_{\rm chord}\) is **also attained**. In particular, **at least one global maximizer** of the spatial score has an **entire affine middle-half outer roof**.

**Proof.** The right-hand supremum is bounded by the left because the canonical subclass is contained in the original. Conversely MID.10 explicitly assigns to every cap of positive width a member \(U^\sharp\in\mathcal C_{\rm chord}\) with at least the same score; the width-zero case contributes zero and cannot improve the positive reference score. Taking suprema proves equality. Apply the construction to an attained global cap optimizer from SD3; its resulting canonical cap is still a global maximizer, proving attainment. \(\square\)

**Geometric interpretation.** The central upper roof of the cap is not rewarded anywhere in the spatial objective; reducing that roof without altering either exterior wing can only lower the *complete* moving-inner-ray niche. Convexity allows exactly one **maximal** reduction: replace the entire uncharged central curved roof by its supporting-endpoint chord. The candidate Romik cap already has its middle-half roof equal to its horizontal top face, so the transformation fixes the exact equality witness. The global competitor may have a **tilted** central facet and a height-one maximum on an exterior wing. One **cannot** assert the facet is horizontal or coincides with the top face, nor that it creates a feasible two-handed sofa; neither claim follows from MID2.

---

<a id="proof-finite-exposure"></a>
## Technical proof 11. Finite exposure and the moving spatial window (FE)

### 1. Finite-polygon spatial objective; keep the center interval moving

Let \(L=\pi/2\), \(I=[l,r]\), \(W=r-l>0\), and
\[
j_-=l+W/4=\tfrac34 l+\tfrac14r,\qquad
j_+=r-W/4=\tfrac14 l+\tfrac34r.
\tag{FE.1}
\]
Take a convex downward polygon \(U\) of height at most one, defined as intersection of \(y\ge0\) with finitely many supporting halfplanes, including the horizontal normal \(e_y\), both vertical sides \(x=l,r\), and a grid of upper support normals
\(\theta_j=j\pi/(2n)\), \(j=0,\ldots,2n\). The outer upper roof \(A(x)\) is concave and continuous at both interior abscissae \(j_\pm\).

Use *only* the finite physical turning angles \(t_j=j\pi/(2n)\), \(j=1,\ldots,n-1\), and denote their entire **two-ray positive forbidden roof** by
\[
n_n(x)=\left[\max_{1\le j<n}
\min\left(\frac{h_U(u_{t_j})-1-x\cos t_j}{\sin t_j},
\frac{h_U(v_{t_j})-1+x\sin t_j}{\cos t_j}\right)\right]_+ .
\tag{FE.2}
\]
The finite spatial score is
\[
\boxed{P_n(U)=\int_l^{j_-}A\,dx+
\int_{j_+}^r A\,dx-
\int_{j_-}^{j_+}n_n\,dx.}\tag{FE.3}
\]
All three integrals use true ordinary vertical heights; no signed-curve formula, candidate contact phases, or sampled-angle area assumption enters FE.3.

For a non-top source normal \(\theta_j\), \(j\notin\{0,n,2n\}\), let

- \(\ell^{\rm wing}_j\) be the total **actual outer facet arclength** lying over the charged exterior quarters \(I\setminus J\);
- \(\tau^{\rm middle}_j\) be the arclength of positive-height **exposed inner-wall boundary pieces** of the full finite union, supported by the inner wall of that source normal and having horizontal abscissa within \(J\).

Boundary points at J's endpoints and at ray intersections do not contribute arclength ambiguities. If the outer facet is absent, set \(\ell^{\rm wing}_j=0\).

Let \(e_R=A(r)\), \(e_L=A(l)\) be the lengths of the **right/left vertical end facets** (possibly zero), and abbreviate
\[
q_-=A(j_-)+n_n(j_-),\qquad
q_+=A(j_+)+n_n(j_+).
\tag{FE.4}
\]

### 2. Move a single floating facet outward: the **charged** exposure inequality

Fix a non-top, non-axis grid source normal \(\theta_j\) and move *only* its supporting line outward by \(\varepsilon>0\), preserving every other grid side, the floor, the top height constraint, and both horizontal axis supports. For small \(\varepsilon\), the new polygon has the **same W and same middle J**, and the support at \(\theta_j\) grows by exactly \(\varepsilon\) when the old facet has positive length. All other sampled supports remain unchanged because their old attaining points stay in the enlarged body and their original halfplanes remain.

Moving the outer facet gains an area strip of first-order area \(\varepsilon\ell^{\rm wing}_j\) over the **exterior wings**. The finite union of inner forbidden quadrants changes by moving **one inner line** of the unique corresponding t_j angle; its newly swept, unmasked **positive-height boundary pieces inside J** contribute exactly \(\varepsilon\tau^{\rm middle}_j\). All intersections of distinct nonparallel source lines, the floor, or the fixed window endpoints contribute only \(O(\varepsilon^2)\) ordinary area. Thus
\[
\boxed{
\left.\frac{d}{d\varepsilon}P_n(U_\varepsilon)
\right|_{\varepsilon=0+}
=\ell^{\rm wing}_j-\tau^{\rm middle}_j
\quad\text{when the facet is positive length.}
}\tag{FE.5}
\]
A zero-length facet has \(\ell^{\rm wing}_j=0\), and needs no differentiability claim. In particular *the weighted one-turn exposure measure is not the right one here*: it counts the **entire** niche and the **entire** outer facet, while FE.5 counts only the two **charged spatial portions**.

### 3. Move a positive-length vertical end face: an **exact moving-J boundary term**

**First assume \(e_R>0\).** Move only the side \(x\le r\) to \(x\le r+\varepsilon\), retaining **all** non-axis grid halfplanes. A relative-interior point of the positive vertical face has strict slack against the finitely many other nonparallel sides. Thus the actual right projection endpoint is \(r+\varepsilon\) for sufficiently small positive \(\varepsilon\). The finite niche function \(n_n(x)\) remains **identically unchanged at every fixed x**, since none of its source supporting normals is an axis normal: each old attaining point remains, and each old non-axis halfplane is retained. The added rightmost sliver has area \(\varepsilon e_R+O(\varepsilon^2)\).

But W increases by \(\varepsilon\), so both endpoints of the **middle** window move:
\[
j_-(\varepsilon)=j_-+\varepsilon/4,\qquad
j_+(\varepsilon)=j_++3\varepsilon/4.
\]
Differentiate FE.3 using continuity of A and \(n_n\) at the moving window endpoints:
\[
\boxed{
\left.\frac{d}{d\varepsilon}P_n(U_\varepsilon)
\right|_{0+}
=e_R+\frac14q_- -\frac34q_+.
}\tag{FE.6}
\]
The terms \(q_\pm\) are **A+n**, not A-n. The + sign on n is forced by subtracting the integral over the moving central interval.

Similarly, **when \(e_L>0\)**, moving only the **left** side \(x\ge l\) to \(x\ge l-\varepsilon\) yields
\[
j_-(\varepsilon)=j_--3\varepsilon/4,\qquad
j_+(\varepsilon)=j_+-\varepsilon/4,
\]
and therefore
\[
\boxed{
\left.\frac{d}{d\varepsilon}P_n(U_\varepsilon)
\right|_{0+}
=e_L-\frac34q_-+\frac14q_+.
}\tag{FE.7}
\]
These are actual **outward** derivatives of a finite polygonal ordinary-area score, including the **width-dependent moving J**, under the respective positive-face hypothesis. They hold without symmetry and whether or not the finite niche is connected at any horizontal level. They are not automatically inward derivatives: an inward cut can remove the sole attaining point of another sampled support, even if the vertical face has positive length.

#### 3a. Zero end faces: the axis wall does not move the body

Suppose \(e_R=0\), with U of positive area. Its last upper roof segment meets the floor at \((r,0)\), so one of the retained upper halfplanes has the form
\[
a(x-r)+b y\le0,\qquad a,b>0.
\]
Together with \(y\ge0\), this halfplane already implies \(x\le r\). Relaxing only the redundant vertical constraint therefore leaves **the entire polygon unchanged for every \(\varepsilon>0\)**. Its actual width and J are constant; the derivative is zero. Reflection gives the same conclusion when \(e_L=0\).

With \(\chi_R=1_{\{e_R>0\}}\), \(\chi_L=1_{\{e_L>0\}}\), and
\[
C_R=\tfrac34q_+-\tfrac14q_-,\qquad
C_L=\tfrac34q_--\tfrac14q_+,
\tag{FE.7a}
\]
the universally valid isolated-outward-wall derivatives are
\[
\boxed{D_R^+P_n=\chi_R(e_R-C_R),\qquad
D_L^+P_n=\chi_L(e_L-C_L).}
\tag{FE.7b}
\]
An axis-wall *parameter* is not the actual support coordinate when its constraint has become redundant.

**Exact rational-vertex counterexample to the former unconditional FE.6.** Let
\[
U=\operatorname{conv}\{(0,0),(0,1),(1,1),(2,0)\},\qquad n=2.
\]
The sole proper turning angle is \(\pi/4\); its supports are \(f=\sqrt2\), \(g=1/\sqrt2\), and its positive niche is
\[
n_2(x)=\bigl[\min(2-\sqrt2-x,\,1-\sqrt2+x)\bigr]_+.
\]
Here \(J=[1/2,3/2]\), \(e_R=0\), \(q_-=5/2-\sqrt2\), and \(q_+=1/2\). The former FE.6 would give
\[
e_R+q_-/4-3q_+/4=(1-\sqrt2)/4<0.
\]
The actual derivative is **zero**: the retained roof constraint \(x+y\le2\) and floor already imply \(x\le2\).

The omitted coefficient need not even have a fixed sign. For the \(n=3\) grid take
\[
U=\operatorname{conv}\{(0,0),(0,1),(\sqrt3,0)\}.
\]
Its upper facet normal is \(\pi/3\), and \(J=[\sqrt3/4,3\sqrt3/4]\). At \(t=\pi/6\) the two roofs are \(1-\sqrt3x\) and \(1-2/\sqrt3+x/\sqrt3\); the \(t=\pi/3\) first roof is nonpositive for \(x\ge0\). Thus \(q_-=2-2/\sqrt3\), \(q_+=1/4\), \(e_R=0\), and the formerly claimed derivative is
\[
5/16-1/(2\sqrt3)>0,
\]
whereas relaxing the redundant right wall again leaves the cap unchanged. These examples refute the **unconditional derivative claim**; neither example is asserted to be a global maximizer or a counterexample to the sharp score bound.

### 4. First-order constraints at a globally selected finite maximizer

To state a clean theorem, fix an artificial broad box \([-R,R]\times[0,1]\), with all sides of U strictly inside its vertical walls, and maximize
\[
P_n(U)-\eta_n\sum_{j=0}^{2n}w_j[h_U(\theta_j)-h_{*,j}]^2
\tag{FE.8}
\]
over upper-grid convex polygons, where \(\eta_n\ge0\), \(w_j\ge0\), and \(\sum w_j\le1\). All samples use the **same** actual support function; the penalty is not inserted into the geometric area definition.

At a maximizer, a permitted outward variation has nonpositive objective derivative. If all support values are bounded by \(B\), the absolute penalty derivative at j is at most \(4B\eta_nw_j\). Therefore FE.5–FE.7 imply:

**Theorem FE1 (global finite-polygon spatial pressure constraints).** Put \(b_{n,j}=4B\eta_nw_j\ge0\). Then
\[
\boxed{\begin{aligned}
\ell^{\rm wing}_j&\le\tau^{\rm middle}_j+b_{n,j}
&& (j\notin\{0,n,2n\}),\\
e_R&\le\chi_R(C_R+b_{n,0}),\\
e_L&\le\chi_L(C_L+b_{n,2n}).
\end{aligned}}\tag{FE.9}
\]
In particular, the two **unconditional** axis bounds are
\[
e_R\le(C_R+b_{n,0})_+,\qquad
e_L\le(C_L+b_{n,2n})_+.
\tag{FE.9a}
\]
**When both end faces have positive length**, adding the two axis bounds gives
\[
\boxed{
e_R+e_L\le\frac12(q_-+q_+)+b_{n,0}+b_{n,2n}.
}\tag{FE.10}
\]

For arbitrary end faces, the valid summed bound is instead the sum of FE.9a's two positive parts. The original FE.10 is not inferred when an end face vanishes.

**Proof.** When the artificial box sides are inactive, each positive-length floating or axis facet admits an outward variation changing exactly its own sampled support coordinate. FE.5–FE.7 and the bounded penalty derivatives give the corresponding inequalities. At zero floating length the first inequality is trivial. At zero axis length the actual polygon and every actual support stay fixed by Section 3a, so the indicator form reads \(0\le0\). This proves FE.9 and hence FE.9a. Add the two positive-face inequalities for the stated conditional FE.10. \(\square\)

**Sharp reference calibration:** Romik's cap has right and left end heights \(e_R=e_L=1/2\), and at the central-half face endpoints \(A(j_\pm)=1\), \(n(j_\pm)=0\). The limiting (unpenalized) axis formulas therefore read \(1/2=3/4-1/4\) at both ends. This is the precise replacement for the old constant \(1/2\) weighted-one-turn endpoint condition, but **only at the reference** do its two moving-window pressures collapse to that constant.

### 5. The finite outer/inner **projection budget** and the exact limit warning

A polygon upper facet with normal \(\theta_j\) has horizontal projected length \(\ell_j\sin\theta_j\); its charged exterior contribution is \(\ell^{\rm wing}_j\sin\theta_j\). Let \(T_{\rm wing}\) be the total horizontal length of any **horizontal top-face segment lying outside J**. Horizontal projection of all upper exterior graph pieces gives the **exact identity**
\[
\boxed{
\sum_{j\notin\{0,n,2n\}}
\ell^{\rm wing}_j\sin\theta_j
=\frac W2-T_{\rm wing}.
}\tag{FE.11}
\]
The first- and second-wall exposed positive niche graph pieces have horizontal projections \(\tau^{\rm middle}_j\sin\theta_j\). Each exposed ray line has horizontal projection **strictly monotone** with x, and the upper boundary of the finite niche over J is a single graph. There are no positive-length source-line coincidences between distinct sampled angles. Consequently
\[
\boxed{
\sum_{j\notin\{0,n,2n\}}
\tau^{\rm middle}_j\sin\theta_j
=\left|\{x\in J:n_n(x)>0\}\right|.
}\tag{FE.12}
\]
Multiply the first inequality of FE.9 by \(\sin\theta_j\), sum, and use \(\sum b_{n,j}\le4B\eta_n\):
\[
\boxed{
\left|\{x\in J:n_n(x)=0\}\right|
\le T_{\rm wing}+4B\eta_n.
}\tag{FE.13}
\]
This is a nontrivial **whole-upper-profile, whole-finite-niche projection restriction** at every selected finite maximizing polygon; it is not an assumption of positive middle niche support or a candidate contact phase.

**Mandatory limit warning:** It is **invalid** to pass FE.13 to the angular continuum by merely using uniform convergence of niche roofs. The indicator of \(\{n_n=0\}\) is not continuous under uniform convergence; arbitrarily shallow positive roofs can converge uniformly to a roof that is zero on a long interval. The weighted half-face proof [HF](https://github.com/vltanh/lean4-moving-sofa/blob/b525305f344e635e6264cb470514d6b8bb7a8e43/docs/ambidextrous/one-turn-half-width-top-face.md) needed a separate endpoint support-derivative estimate to control precisely this loss of niche projection. Such a theorem for the **different** spatial P maximizer has *not* yet been proved here. Thus FE.13 is a rigorously proved **finite** structural condition, **not** a claim that an actual infinite-angle maximizer has a fully exposed central niche.

The subsequent RG regularity theorem and [EP1–EP3](#proof-full-endpoints) establish uniform wing control and exact limiting finite-exposure moments using additional arguments. Identifying the actual positive continuum niche geometry and proving the global sharp scalar inequality remain open. **Neither follows from FE.13 by uniform roof convergence.**

---

<a id="proof-prescribed-regularity"></a>
## Technical proof 12. Prescribed-cap approximation and wing regularity (RG)

### 1. State the exact geometric object

For a compact downward convex cap \(U\subset\mathbb R\times[0,1]\) of width \(W>0\), let \(A_U\) be its concave upper roof and
\[
J=[l+W/4,r-W/4],\qquad
\mathcal P(U)=\int_{I\setminus J}A_U\,dx-\int_Jn_U\,dx,
\]
where \(n_U(x)\) is the **entire continuous-angle two-attached-inner-wall** positive niche roof from [SD.1](#proof-full-domain). SD2–SD3 prove height-one attainment and \(8/5<W<6\) for any value at least the reference's \(M/2\). MID2 gives a score-nondecreasing transformation of *every cap* whose output has \(A_U|_J\) affine.

Pick **one such globally maximizing canonical cap**, denoted \(U_*\), translated so its horizontal projection lies strictly inside a fixed artificial box \([-R,R]\) with \(R>7\), and write
\[
\boxed{A_*(x)=a+sx\quad(x\in J_*).}\tag{RG.1}
\]
Its affine facet has unique outward normal
\[
\boxed{n_c=\frac{(-s,1)}{\sqrt{1+s^2}},\qquad
\theta_c=\arg n_c\in(0,\pi).}\tag{RG.2}
\]
The maximal facet may extend outside J*. The height-one **top** face, if a nondegenerate horizontal segment, has normal \(e_y\), \(\theta=\pi/2\). No assertion that these two normals coincide is made.

Let \(\sigma_*=h_{U_*}+h_{U_*}''\) on the **open upper semicircle**, interpreted as the nonnegative surface-area/curvature **measure** of the actual convex cap. It counts both smooth curvature and exposed-facet atoms (but not the bottom-face atom at the downward normal).

### 2. Finite selections converge to this **particular canonical global optimizer**

Fix grid angles \(\theta_j=j\delta\), \(j=0,\ldots,2n\), \(\delta=\pi/(2n)\), with n dyadic so grids are nested. Use the finite positive niche \(n_{n,U}\) of angles \(0<t_j<L=\pi/2\), \(t_j=j\delta\), \(1\le j<n\), and
\[
\mathcal P_n(U)=\int_{I_U\setminus J(U)} A_U-\int_{J(U)}n_{n,U}.
\tag{RG.3}
\]
On the fixed compact space of all downward convex caps inside \([-R,R]\times[0,1]\), including zero-area limits, the full positive niche and every finite grid niche are jointly **uniformly continuous in cap support and abscissa**, by the endpoint truncation and angular-fraction argument of [SD3](#proof-full-domain). The finite roofs \(n_{n,U}\) monotonically increase to the complete roof \(n_U\). Hence Dini's theorem on the compact product of cap domain and x-box gives
\[
\sup_{U,x}|n_U(x)-n_{n,U}(x)|\longrightarrow0,\qquad
e_n:=\sup_U(\mathcal P_n(U)-\mathcal P(U))\longrightarrow0 .
\tag{RG.4}
\]
(The exterior-score term is identical in both, so \(e_n\ge0\).) The finite objective \(\mathcal P_n\) is continuous even though J moves with the width, by the uniform boundedness of its roof and convergence of interval endpoints.

For each n, let \(\mathcal G_n\) be the compact family of polygons cut by the floor, the upper grid halfplanes at their own supporting values, and the fixed artificial box walls. For any cap U, its grid circumscription \(C_n(U)\supseteq U\) has exactly the **same** support values at every grid normal, so the same sampled niche \(n_{n,U}\), same horizontal projection (the two horizontal axis normals are sampled), and exterior roof at least \(A_U\). Therefore
\[
\boxed{\mathcal P_n(C_n(U))\ge\mathcal P_n(U)\ge\mathcal P(U).}\tag{RG.5}
\]

Choose positive sample weights
\[
w_0=w_{2n}=1/4,\qquad
w_j=\delta/(2\pi)\quad(0<j<2n),\qquad\sum w_j\le1,
\]
and
\[
D_n(U,U_*)^2=\sum_{j=0}^{2n}w_j[h_U(\theta_j)-h_{U_*}(\theta_j)]^2,\qquad
\eta_n=\sqrt{e_n}+1/n.
\tag{RG.6}
\]
Let \(U_n\in\mathcal G_n\) maximize
\(\mathcal P_n(U)-\eta_nD_n(U,U_*)^2\).
Since \(C_n(U_*)\) has **zero penalty**, RG.5 and maximality give a penalized value at least \(\mathcal P(U_*)=\mathcal P_{\max}\). But for arbitrary \(U_n\), RG.4 gives
\[
\mathcal P_n(U_n)\le\mathcal P(U_n)+e_n
\le\mathcal P_{\max}+e_n.
\]
Thus
\[
\boxed{D_n(U_n,U_*)^2\le e_n/\eta_n\longrightarrow0.}\tag{RG.7}
\]
By Hausdorff compactness and Riemann-sum convergence of the strictly positive sample weights, every limit of \(U_n\) has identical upper-half support function to \(U_*\), hence is exactly \(U_*\). Therefore the **whole selected sequence** satisfies
\[
\boxed{U_n\longrightarrow U_*\quad\text{in Hausdorff support distance},}\tag{RG.8}
\]
including all actual upper/lower top-roof and horizontal-axis support data. As \(U_*\) lies strictly inside the artificial vertical box sides, so do \(U_n\) eventually. This permits all following outward source-facet variations.

No curvature cap, candidate phase chart, or symmetry of the selected polygons has been inserted.

### 3. Finite spatial exposure + adjacent wall geometry bounds all but the **uncharged** outer facet length

Let \(\ell_{n,j}\) be the *total* upper outer-facet arclength of \(U_n\) at normal \(\theta_j\), and let \(\ell_{n,j}^{\rm wing}\) be the portion over the charged exterior wings \(I_n\setminus J_n\). Put
\(\ell_{n,j}^{\rm mid}=\ell_{n,j}-\ell_{n,j}^{\rm wing}\ge0\).
For \(j\notin\{0,n,2n\}\), [FE.9](#proof-finite-exposure) gives
\[
\ell_{n,j}^{\rm wing}\le\tau_{n,j}^{\rm middle}+b_{n,j},
\qquad
b_{n,j}=4B\eta_nw_j,\quad
B=R+1.
\tag{RG.9}
\]
Here \(\tau_{n,j}^{\rm middle}\) is the exposed length of the actual source inner wall **inside J_n**. It is nonnegative and bounded by the **full finite-niche source exposure** \(\tau_{n,j}^{\rm full}\).

The independent elementary neighboring-two-wall estimate [WR.1](#proof-neighboring-walls) applies to every finite upper grid polygon and every interior source normal, in both upper quarters. It gives
\[
\boxed{
\tau_{n,j}^{\rm full}
\le(6B+4)\delta+
(2\tan(\delta/2)-\ell_{n,j})_+ .
}\tag{RG.10}
\]
It comes from intersecting the exposed ray's parameter line with the two **neighboring first** and **neighboring companion** inner walls. It does not assume maximizing the *different* weighted objective \(\Psi\), nor that any local ray is globally visible.

If \(\ell_{n,j}<2\tan(\delta/2)\), then \(\ell_{n,j}\le2\delta\).
Otherwise the positive-part term in RG.10 vanishes and
\(\ell_{n,j}=\ell_{n,j}^{\rm wing}+\ell_{n,j}^{\rm mid}\le(6B+4)\delta+b_{n,j}+\ell_{n,j}^{\rm mid}\).
In both cases,
\[
\boxed{
\ell_{n,j}\le C\delta+b_{n,j}+\ell_{n,j}^{\rm mid},
\qquad C=6B+6 .
}\tag{RG.11}
\]
The only part not controlled by an \(O(\delta)\) geometric bound is the outer facet portion over the **uncharged middle roof**.

### 4. The affine middle roof prevents any **off-facet** concentration

Let \(E\Subset(0,\pi)\setminus\{\theta_c,\pi/2\}\) be any compact set of upper supporting normal angles separated by a positive angular distance from the central affine-facet normal and the horizontal top normal.

**Lemma RG1 (uncharged noncentral facet mass disappears).**
\[
\boxed{
\lim_{n\to\infty}
\sum_{\theta_j\in E}\ell_{n,j}^{\rm mid}=0.
}\tag{RG.12}
\]

**Proof.** Since \(j_\pm^*\) are strictly interior abscissae of the limiting projection, concavity and bounded vertical height give a uniform Lipschitz constant for the roofs \(A_n\) on a fixed slightly larger compact horizontal interval containing all \(J_n\), for n large. For example a roof between zero and one on an interval whose points stay at distance \(\delta_x>0\) from its projection endpoints has one-sided slope magnitude at most \(1/\delta_x\), by comparing with endpoint values and concavity.

Hausdorff convergence RG.8 gives uniform convergence of these roofs to \(A_*=a+sx\) on that compact interval. On any strictly smaller middle interval
\([j_-^*+\varepsilon,j_+^*-\varepsilon]\), the secant-slope inequalities for concave functions imply all one-sided slopes \(A'_{n,\pm}\) converge **uniformly** to the constant s. Hence for large n, every outer facet over that strict middle interval has outward normal in a small fixed neighborhood of \(\theta_c\), disjoint from E. (At a corner, all normals are between the adjacent one-sided slope normals and obey the same bound.)

Only the two boundary strips of horizontal width \(O(\varepsilon)+o_n(1)\) near \(j_\pm^*\) remain. Their *total* upper-boundary arclength is at most
\((1+L_x)\times\text{total horizontal width}\), using the uniform Lipschitz constant \(L_x\). Thus the sum on the left of RG.12 has limsup at most \(4(1+L_x)\varepsilon\), independently of E. Let \(\varepsilon\downarrow0\). \(\square\)

This argument uses the **entire affine central facet** furnished by MID2. Merely having a nonsmooth cap or Hausdorff convergence would not rule out concentration of curvature on an arbitrary middle arc; the global chord canonicalization is what makes RG.12 true.

### 5. The global-exterior-wing curvature density theorem

For each finite convex polygon, the upper surface-area measure is exactly its facet-normal length measure
\(\sigma_n=\sum_{j=0}^{2n}\ell_{n,j}\,\delta_{\theta_j}\).
Uniform convergence of the convex support functions, their distributional identity \(\sigma_n=h_n+h_n''\), and bounded total perimeter imply weak convergence
\[
\sigma_n\rightharpoonup\sigma_* \quad\text{on the upper semicircle}.
\tag{RG.13}
\]

Take any compact E as above, and sum RG.11 over grid indices \(\theta_j\in E\):
\[
\begin{aligned}
\sigma_n(E)
&\le C\bigl(|\mathrm{conv}(E)|+2\delta\bigr)
+\sum_j b_{n,j}
+\sum_{\theta_j\in E}\ell_{n,j}^{\rm mid}
\end{aligned}
\]
for an interval E, and by additivity for finite unions of intervals. The penalty mass satisfies \(\sum_j b_{n,j}\le4B\eta_n\to0\), and the middle term vanishes by RG.12. By testing against continuous nonnegative functions supported away from \(\{\theta_c,\pi/2\}\), or using the weak-convergence open-set inequality on finite unions of intervals, obtain
\[
\boxed{
\sigma_*(E)\le C\,|E|
\quad\text{for all Borel }E\subset(0,\pi)\setminus\{\theta_c,\pi/2\}.
}\tag{RG.14}
\]

**Theorem RG2 (global one-cap spatial maximizer: all arbitrary wing singularities removed).**
There exists a global maximizer \(U_*\) of the scalar spatial score \(\mathcal P\), with exactly unit height and width \(8/5<W<6\), whose roof is affine on J and whose upper curvature measure decomposes as
\[
\boxed{
\sigma_*|_{(0,\pi)}
=\rho(\theta)\,d\theta+
a_c\,\delta_{\theta_c}
+a_t\,\delta_{\pi/2},
\qquad
0\le\rho(\theta)\le6(R+1)+6\quad\text{a.e.},
}\tag{RG.15}
\]
where \(a_c,a_t\ge0\) represent at most **two** permitted facet atoms. When \(\theta_c=\pi/2\), combine them into a single top-face atom; a normal with no facet has zero atom. No singular-continuous upper curvature remains at any interior upper normal, and no other interior curvature atoms are present.

**Proof.** Choose a score maximizer, canonize it by MID2 to make its middle roof affine while keeping its score maximal, and use RG.7–RG.14. The bound on the absolutely continuous density follows from absolute measure domination on the complement of the two angles. All remaining nonnegative measure supported on those two singleton normals consists of atoms. \(\square\)

The result is **existential**: an uncanonicalized score maximizer could have gratuitous interior roof curvature which does not change the charged objective, so there is no claim that *every* maximizer shares RG.15. No upper unit-curvature domination \(\rho\le1\), endpoint balance equality, signed roof formula, or candidate contact chart has been inferred.

### 5b. A *sharp-form* nonlinear bound on the wing densities

The coarse absolute bound RG.15 can be strengthened to exactly the **velocity-dependent geometric upper function** appearing in the independently established one-turn neighboring-wall inequality, *without assuming this spatial maximizer also maximizes the different weighted objective*.

On the two upper normal quarters, put
\[
f(t)=h_{U_*}(u_t),\quad g(t)=h_{U_*}(v_t),\quad
p(t)=f'(t)-g(t)+1,\quad q(t)=g'(t)+f(t)-1.
\]
The selected canonical cap is \(W^{2,\infty}\) on compact subintervals of the open quarters away from the **one central-facet atom** (and from their axis endpoints); thus \(p,q\) and the curvature densities
\[
\rho_f=f+f'',\qquad\rho_g=g+g''
\]
are defined almost everywhere, with possible point jumps of derivatives only at the explicitly allowed facet normals.

Write
\[
\boxed{\kappa(z)=\max\left\{|z|,\frac{1+|z|}{2}\right\}.}\tag{RG.16}
\]

**Theorem RG3 (universal wing source-curvature constraint at a global P maximizer).** At almost every open-quarter angle whose corresponding exposed outer normal is not the central facet normal,
\[
\boxed{
0\le\rho_f(t)\le\kappa(q(t)),\qquad
0\le\rho_g(t)\le\kappa(p(t)).
}\tag{RG.17}
\]
There are no singular-continuous source curvatures on those same intervals; RG.17 is a **pointwise necessary condition of a global score optimizer**, not an extra assumed smoothness or corridor curvature domination.

**Proof.** For the first quarter, use [WR, Section 4](#proof-neighboring-walls) solely as a **polygonal geometric inequality**. Every grid facet of every selected U_n obeys
\[
\tau^{\rm full}_{n,j}\le
\tan\delta\bigl(|q^+_{n,j}|+\tan(\delta/2)\bigr)
+\bigl(2\tan(\delta/2)-\ell_{n,j}\bigr)_+,
\tag{RG.18}
\]
where \(q^+_{n,j}=h_n(\theta_j)+
[h_n(\theta_{j+n+1})-\cos\delta\,h_n(\theta_{j+n})]/\sin\delta-1\).
This is the neighboring *companion* wall bound for the first source, not a stationary-flux equality.

Combine RG.18 with the **spatial** finite maximality inequality
\(
\ell_{n,j}\le \tau^{\rm middle}_{n,j}+b_{n,j}
+\ell^{\rm mid}_{n,j}
\)
and \(\tau^{\rm middle}\le\tau^{\rm full}\).
If \(\ell_{n,j}\ge 2\tan(\delta/2)\), the positive part vanishes and the result is
\[
\ell_{n,j}\le\ell^{\rm mid}_{n,j}
+\delta|q^+_{n,j}|+O(\delta^2)+b_{n,j}.
\]
If \(\ell_{n,j}<2\tan(\delta/2)\), move its \(-\ell_{n,j}\) from the positive-part expression to the left to obtain
\[
2\ell_{n,j}\le\ell^{\rm mid}_{n,j}
+\delta(1+|q^+_{n,j}|)+O(\delta^2)+b_{n,j}.
\]
The two cases combine, with the larger harmless middle term, to give the exact uniform inequality
\[
\boxed{
\ell_{n,j}\le
\kappa(q^+_{n,j})\delta+C_1\delta^2
+b_{n,j}+\ell^{\rm mid}_{n,j}.
}\tag{RG.19}
\]
The \(O(\delta^2)\) coefficient \(C_1\) is independent of n,j because all U_n lie in the fixed artificial R-box and all their supports are uniformly bounded and Lipschitz.

On a compact source-angle interval avoiding \(\theta_c\) and the top normal, RG1 proves the sum of the \(\ell^{\rm mid}\) contributions vanishes. The penalty sum also tends to zero. The companion one-sided grid derivatives \(q^+_{n,j}\) converge in \(L^1_{\rm loc}\) to \(q(t)\): for convex supports, uniform convergence implies their a.e. first derivatives converge at all differentiability points; uniform boundedness gives dominated \(L^1\) convergence. The function \(\kappa\) is 1-Lipschitz, so Riemann summation of RG.19 over any such source interval yields the measure inequality
\[
\sigma_f(E)\le\int_E\kappa(q(t))\,dt
\quad\text{for every interval }E
\text{ avoiding the exceptional normals}.
\]
RG2 has already proved absolute continuity there, giving its pointwise density bound.

For the second quarter, reverse horizontal x and interchange the two source normal families in the same elementary neighboring-wall argument. Its geometric companion velocity is \(p\), yielding \(\rho_g\le\kappa(p)\). Countably many compact intervals exhaust the nonexceptional portions of both quarters. \(\square\)

**The sharp-wall threshold remains missing:** \(\kappa(z)\le1\) if \(|z|\le1\), but \(\kappa(z)>1\) when \(|z|>1\). RG3 does **not** establish \(|p|,|q|\le1\) for the global spatial maximizer. The previous weighted \(\Psi\) proof obtained such control using a **different** global balance and a niche-height bound; those facts do not automatically transfer to the spatial P objective. In particular the permitted central affine facet may have a genuine jump in source velocity, changing the matching/flux equations. This is now the explicit **remaining global value theorem** to attack.

---

<a id="proof-full-endpoints"></a>
## Technical proof 13. Actual full-cap endpoint complementarity (EP)

### 1. Exact global conclusions and their scope

Let U be a height-one global maximizer of the [SD.2 spatial score](#proof-full-domain), with projection \(I=[l,r]\), width W, roof A, full continuous-angle positive niche n, and
\[
j_-=(3l+r)/4,\qquad j_+=(l+3r)/4,\qquad J=[j_-,j_+].
\]
The global existence and width theorem SD3 gives \(8/5<W<6\). Define the **boundary values**, not the source-angle velocities,
\[
q_\pm=A(j_\pm)+n(j_\pm),\qquad
C_R=(3q_+-q_-)/4,\quad C_L=(3q_--q_+)/4,
\]
\[
e_R=A(r),\qquad e_L=A(l),\qquad z_+=\max(z,0).
\tag{EP.1}
\]

**Theorem EP1 (global endpoint complementarity).**
\[
\boxed{e_R=(C_R)_+,\qquad e_L=(C_L)_+.}
\tag{EP.2}
\]
In particular, a zero end face permits a **negative** corresponding pressure; it must not be assigned the positive-face stationary equation. Since \(C_R+C_L=(q_-+q_+)/2>0\), at least one end face is positive.

There is also an exact exposure statement. Use the selected finite polygons below, and let \(\nu_R,\nu_L\) be any joint weak limits of their positive middle-window inner-wall exposure measures. Let \(\omega_R,\omega_L\) be the corresponding limits of their charged outer-wing facet measures, omitting axes and the horizontal top normal. Then:

**Theorem EP2 (the remaining limiting exposure defect).** These measures have bounded densities, \(\nu_Q\ge\omega_Q\) for \(Q=R,L\), and
\[
\boxed{
\int_{[0,\pi/2]}\cos\theta\,d(\nu_R-\omega_R)=(-C_R)_+,\qquad
\int_{[\pi/2,\pi]}(-\cos\theta)\,d(\nu_L-\omega_L)=(-C_L)_+.
}
\tag{EP.3}
\]
Consequently \(C_Q\ge0\) forces \(\nu_Q=\omega_Q\) on that entire source quarter. At least one quarter has equality. An unmatched limiting exposure can occur only on a side with **zero end height and negative pressure**, with the moment in EP.3 fixed exactly.

For the MID2-canonical maximizer, \(\omega\) is the actual outer-wing normal measure with the top face omitted. **We do not identify \(\nu\) with the arclength measure of the limiting positive niche graph.** Arbitrarily shallow finite niche pieces can disappear at height zero while their exposure measures retain mass. EP2 is a statement about their precisely defined limits, not an assumed continuity theorem for niche zero sets.

### 2. Finite selection and the valid outward inequalities

Translate the prescribed maximizer strictly inside \([-R,R]\times[0,1]\), with \(R>7\), and use the dyadic upper grids and penalized selections of [RG, Section 2](#proof-prescribed-regularity):
\[
\theta_j=j\delta_n,\quad\delta_n=\pi/(2n),\qquad
F_n(V)=P_n(V)-\eta_n\sum_{j=0}^{2n}w_j
       [h_V(\theta_j)-h_U(\theta_j)]^2.
\tag{EP.4}
\]
Here \(\sum_jw_j\le1\), \(\eta_n\to0\), all absolute supports are bounded by \(B=R+1\), and U_n maximizes F_n over the upper-grid polygon class. The selection proof gives
\[
U_n\longrightarrow U\quad\text{in Hausdorff distance},\qquad W_n\ge1
\quad\text{eventually}.
\tag{EP.5}
\]
To recall why the selection is legitimate: finite niches converge uniformly on the bounded cap-and-abscissa domain by SD3 and Dini's theorem. If \(a_n=\sup(P_n-P)\to0\), choose \(\eta_n=\sqrt{a_n}+1/n\). Grid circumscription of U has the same sampled supports, zero penalty, and at least its score. Maximality then bounds the selected squared support distance by \(a_n/\eta_n\to0\), proving EP.5. This argument targets any prescribed global maximizer; affinity of its middle roof is not needed for EP1.

Write \(q_{n,\pm},C_{n,R},C_{n,L},e_{n,R},e_{n,L}\) for the finite counterparts of EP.1. The corrected [FE.9a](#proof-finite-exposure) gives
\[
e_{n,R}\le(C_{n,R}+b_{n,0})_+,\qquad
e_{n,L}\le(C_{n,L}+b_{n,2n})_+,
\quad b_{n,j}=4B\eta_nw_j.
\tag{EP.6}
\]
Indeed, a positive end face admits an outward move with derivative \(e-C\) and only its own sampled support changes. A zero face gives no outward constraint: the retained last sloping roof halfplane and the floor already imply the old horizontal endpoint. This is exactly why the positive parts are necessary.

For non-axis, non-top normals, the unchanged floating-facet inequality is
\[
\ell^{\rm wing}_{n,j}\le\tau_{n,j}+b_{n,j},\qquad
\beta_n:=\sum_jb_{n,j}\le4B\eta_n\longrightarrow0.
\tag{EP.7}
\]
Here \(\tau_{n,j}\) is exposed positive inner-wall arclength **inside J_n**. Only EP.7, not the former axis formulas, is used in the regularity estimates below.

### 3. Actual inward trimming gives the opposite pressure inequality

For any downward cap of height at most one, put
\[
U^-_\varepsilon=U\cap\{x\le r-\varepsilon\},\qquad0<\varepsilon<W.
\]
Its projection is exactly \([l,r-\varepsilon]\) and its roof agrees with A there. Every support decreases, so its finite or full positive niche is pointwise at most the old niche.

There is a uniform geometric estimate even when the end face vanishes:
\[
\boxed{d_H(U^-_\varepsilon,U)
\le\varepsilon\sqrt{1+(W-\varepsilon)^{-2}}.}
\tag{EP.8}
\]
For a removed point \((x,y)\), compare with \((r-\varepsilon,\min(y,A(r-\varepsilon)))\). If a vertical displacement is needed, concavity bounds the increasing secant slope by
\[
\frac{A(x)-A(r-\varepsilon)}{x-r+\varepsilon}
\le\frac{A(r-\varepsilon)-A(l)}{W-\varepsilon}
\le\frac1{W-\varepsilon}.
\]
This proves EP.8. For \(W\ge1\), \(\varepsilon\le1/2\), the bound is \(\sqrt5\varepsilon\).

Keep the old niche on the new window as an upper comparison for the trimmed niche. The actual roof is unchanged on the retained interval, while the window endpoints move by \(-\varepsilon/4,-3\varepsilon/4\). Ordinary integration at these endpoints gives
\[
P_n(U^-_\varepsilon)-P_n(U)
\ge\varepsilon(C_R-e_R)+o(\varepsilon).
\tag{EP.9}
\]
For each fixed n this uses continuity at the interior window endpoints and one-sided continuity of A at r. It does **not** freeze the actual sampled supports under an inward cut. The same argument works directly for the full niche.

Trimming preserves the finite grid-polygon class. Some old bounds may become redundant, but replacing them by the new polygon's actual sampled supports gives the same intersection. The squared-support penalty changes in absolute value by at most \(4B\eta_n d_H\), since its total weight is at most one. Penalized maximality, EP.8 and \(\varepsilon\downarrow0\) therefore yield
\[
e_{n,R}\ge C_{n,R}-d_n,\qquad
e_{n,L}\ge C_{n,L}-d_n,
\qquad d_n=4\sqrt5 B\eta_n.
\tag{EP.10}
\]
Reflection supplies the left inequality. Combining nonnegativity, EP.6 and EP.10 gives the finite approximate complementarity
\[
\boxed{
-d_n\le e_{n,R}-(C_{n,R})_+\le b_{n,0},\qquad
-d_n\le e_{n,L}-(C_{n,L})_+\le b_{n,2n}.}
\tag{EP.11}
\]
At an unpenalized finite maximizer these are exact equalities. No positive-face hypothesis is left in EP.11.

### 4. End-face convergence and the proof of EP1

Hausdorff convergence alone does not imply end-face length convergence: nearby floating facets might accumulate into an axis atom. The required exclusion follows from the valid floating-facet estimates.

Every point of J_n is at distance at least \(W_n/4\ge1/4\) from both ends. Concavity and \(0\le A_n\le1\) bound its one-sided slopes between -4 and 4. Hence for any fixed \(0<a<\arctan(1/4)\), facets with normals in \((0,a)\) or \((\pi-a,\pi)\) have **zero middle length**. The neighboring-wall estimate [WR.1](#proof-neighboring-walls), combined with EP.7 as in RG.11, gives
\[
\sum_{0<\theta_j<a}\ell_{n,j}\le C(a+\delta_n)+\beta_n,
\qquad
\sum_{\pi-a<\theta_j<\pi}\ell_{n,j}\le C(a+\delta_n)+\beta_n,
\quad C=6B+6.
\tag{EP.12}
\]

Let \(\sigma_n\rightharpoonup\sigma\) be the full circular surface-area measures, whose weak convergence follows from uniform support convergence and \(\sigma=h+h''\). Downward caps have no curvature mass in the open lower quarters; their bottom-face atom is away from the two horizontal axis normals. Thus
\[
\sigma_n(\{0\})=e_{n,R},\qquad
\sigma_n((-a,a))\le e_{n,R}+C(a+\delta_n)+\beta_n.
\]
Portmanteau on the closed singleton gives \(\limsup e_{n,R}\le e_R\). On the open arc, EP.12 gives
\[
e_R\le\sigma((-a,a))\le\liminf_n\sigma_n((-a,a))
\le\liminf_ne_{n,R}+Ca.
\]
Let a decrease to zero. This proves \(e_{n,R}\to e_R\); reflection gives \(e_{n,L}\to e_L\).

The roofs converge uniformly near the interior J endpoints by concavity and Hausdorff convergence. The selected finite niches converge uniformly to the full niche by the uniform finite-angle approximation and SD3. The moving window endpoints also converge, so
\[
q_{n,\pm}\to q_\pm,\qquad C_{n,Q}\to C_Q.
\tag{EP.13}
\]
Pass to the limit in EP.11 to obtain EP.2. This proof uses no axis pressure in EP.12 and has no circular dependence on the statement being proved. Since A is strictly positive at both interior J endpoints for a positive-area cap, \(q_-+q_+>0\), proving the stated positive-end consequence.

### 5. Horizontal erosion supplies the missing exposure moments

Define the right erosion of any downward convex cap by
\[
E^R_\varepsilon=U\cap(U-\varepsilon e_x),\qquad0<\varepsilon<W.
\tag{EP.14}
\]
Its projection and roof are exactly
\[
[l,r-\varepsilon],\qquad A^R_\varepsilon(x)=\min(A(x),A(x+\varepsilon)).
\]
It remains a downward convex cap even when its old top face is a point. For every unit normal v,
\[
h_{E^R_\varepsilon}(v)\le h_U(v)-\varepsilon(v_x)_+.
\tag{EP.15}
\]
This is an **inequality**; equality is not assumed when horizontal sections disappear.

Erosion also has uniform linear Hausdorff control. Put \(\lambda=\varepsilon/W\). For any \(p\in U\), the two points
\[
z=(1-\lambda)p+\lambda(l,0),\qquad
z+\varepsilon e_x=(1-\lambda)p+\lambda(r,0)
\]
belong to U. Thus z belongs to the erosion, and
\[
d_H(E^R_\varepsilon,U)\le(\operatorname{diam}U/W)\varepsilon.
\tag{EP.16}
\]
The reflected left erosion has projection \([l+\varepsilon,r]\), roof \(\min(A(x),A(x-\varepsilon))\), and the analogous support and distance bounds. Grid polygons remain grid polygons because the intersection only tightens parallel grid halfplanes.

For a fixed selected polygon define the **virtual** support values
\[
\widehat h_j=h_{U_n}(\theta_j)-\varepsilon(\cos\theta_j)_+.
\]
They need not be the supports of a body. Nonetheless their finite max/min niche dominates the actual eroded niche by EP.15. Only the first-quarter inner walls move in this virtual family. On the fixed old window, their finite union-area derivative is
\[
\int_{J_n}\widehat n_{n,\varepsilon}
=\int_{J_n}n_n-\varepsilon\sum_{0<j<n}\tau_{n,j}\cos\theta_j+o(\varepsilon).
\tag{EP.17}
\]
Each exposed relative edge interior contributes its arclength times inward normal displacement. Distinct source lines are nonparallel unless they are the same source. Their finitely many intersections, floor contacts and window endpoints contribute only \(O(\varepsilon^2)\); a zero-height tent birth has the same order. This is a **finite** polygonal area derivative, with \(\varepsilon\to0\) before \(n\to\infty\), not a differentiability assertion for the complete niche.

At almost every fixed x the eroded outer-roof derivative is \(\min(0,A_n'(x))\). Thus its integral over the charged exterior is
\[
-\sum_{0<j<n}\ell^{\rm wing}_{n,j}\cos\theta_j.
\]
Include the removed right sliver and both moving-J boundary terms. With
\[
D_{n,R}=\sum_{0<j<n}(\tau_{n,j}-\ell^{\rm wing}_{n,j})\cos\theta_j,
\quad
D_{n,L}=\sum_{n<j<2n}(\tau_{n,j}-\ell^{\rm wing}_{n,j})(-\cos\theta_j),
\tag{EP.18}
\]
the two actual erosions satisfy
\[
P_n(E^Q_\varepsilon)-P_n(U_n)
\ge\varepsilon(D_{n,Q}-e_{n,Q}+C_{n,Q})+o(\varepsilon),\quad Q=R,L.
\tag{EP.19}
\]
The penalty error is at most \(4B\eta_n d_H\). For a fixed diameter bound D_0, EP.7, EP.16 and maximality yield
\[
\boxed{-\beta_n\le D_{n,Q}
\le e_{n,Q}-C_{n,Q}+4BD_0\eta_n.}
\tag{EP.20}
\]
No top-face length or end-face positivity has been used.

### 6. Translation identifies both defects exactly

The finite cap and niche roofs are continuous piecewise-linear graphs. Integrating their slopes gives
\[
\sum_j\tau_{n,j}\cos\theta_j=n_n(j_{n,-})-n_n(j_{n,+}),
\]
\[
\sum_j\ell^{\rm wing}_{n,j}\cos\theta_j
=e_{n,L}-e_{n,R}+A_n(j_{n,+})-A_n(j_{n,-}).
\]
The sums omit axes and the top normal; top pieces have zero cosine. All positive niche components are included, and their zero-height endpoints cancel. Subtracting gives the exact identity
\[
\boxed{D_{n,R}-D_{n,L}
=(e_{n,R}-C_{n,R})-(e_{n,L}-C_{n,L}).}
\tag{EP.21}
\]

The neighboring-wall bound also gives, for **every** non-axis, non-top index,
\[
0\le\tau_{n,j}\le(6B+4)\delta_n+
(2\tan(\delta_n/2)-\ell_{n,j})_+
\le(6B+6)\delta_n.
\tag{EP.22}
\]
Hence the measures
\[
\nu_{n,R}=\sum_{0<j<n}\tau_{n,j}\delta_{\theta_j},\quad
\omega_{n,R}=\sum_{0<j<n}\ell^{\rm wing}_{n,j}\delta_{\theta_j}
\]
and their second-quarter counterparts have joint weak subsequences. EP.7 and EP.22 imply that every limit obeys
\[
0\le\omega_Q\le\nu_Q\le(6B+6)\,d\theta.
\tag{EP.23}
\]
In particular there are no endpoint atoms where the cosine weights vanish.

Let \(D_R,D_L\) be the corresponding cosine-weighted nonnegative defect moments. Pass to the limit in EP.20 and EP.21 using EP1:
\[
0\le D_Q\le(-C_Q)_+,
\qquad D_R-D_L=(-C_R)_+-(-C_L)_+.
\tag{EP.24}
\]
At least one pressure is positive since their sum is positive. Its upper bound in EP.24 is zero. The difference identity then forces equality in the other bound too, proving EP.3. If \(C_Q\ge0\), a nonnegative measure with zero strictly positive interior cosine moment must vanish; EP.23 excludes an atom at the remaining top endpoint. Thus \(\nu_Q=\omega_Q\).

For completeness, identify \(\omega\) with the actual charged outer-wing normal measure by testing against a continuous angular function supported away from the axes and top normal. On interior spatial intervals, concave roofs converge uniformly and their slopes converge almost everywhere. The integrand
\(\varphi(\arg(-A_n',1))\sqrt{1+(A_n')^2}\)
is uniformly bounded: the angular cutoff removes arbitrarily steep slopes. Dominated convergence therefore applies, and shrinking spatial strips at the moving projection endpoints contribute nothing. Strips beside the moving J endpoints have uniformly bounded slopes as well. This identifies the measure off the omitted normals. EP.7 and EP.22 exclude any floating wing mass at those omitted normals in the limit. For the canonical cap, TF3 additionally puts any tilted central facet entirely over J, so it has no charged wing atom. This argument makes no analogous identification for the nonconvex niche graph.

#### 6a. The possible negative-pressure side is localized further

The [TF4 global top-insertion theorem](#proof-facet-pinning) says that every maximizer's top face meets J. For a MID2-canonical height-one maximizer, the horizontal-middle case therefore has \(A(j_-)=A(j_+)=1\); in the tilted case its higher endpoint has height one.

**Corollary EP3.** A side whose J endpoint has height one has **strictly positive pressure**. Hence both quarter exposure equalities hold in the horizontal-middle global-maximizer case. In the tilted case, any nonpositive pressure is confined to the side of the lower middle endpoint; that side has zero end-face height and \(q_{\rm low}\le1/2\).

**Proof.** Suppose \(A(j_+)=1\), so \(q_+\ge1\). If \(C_R\le0\), then \(q_-\ge3q_+\). EP1 would force
\[
e_L=C_L=(3q_--q_+)/4\ge2q_+\ge2,
\]
contradicting \(e_L\le1\). Thus \(C_R>0\); reflection handles the other endpoint. If the lower side has \(C_L\le0\), then \(q_+\ge3q_-\), and
\[
1\ge e_R=C_R=(3q_+-q_-)/4\ge2q_-.
\]
So \(q_-\le1/2\), while EP1 gives \(e_L=0\). The reflected case is identical. If the pressure is strictly negative then \(q_{\rm low}<1/2\). \(\square\)

This corollary uses the endpoint law and the height bound, **not** a new numerical width exclusion. It does not exclude the remaining tilted alternative or prove the value in the horizontal case.

---

<a id="proof-full-pressures"></a>
## Technical proof 14. Positive endpoint pressures, source balance and Green identity (LH)

### Theorem LH1: a strict global low-height exclusion

Let U be any downward convex height-one cap whose roof A is affine on the middle half of its projection. Suppose its higher middle endpoint has height one and its lower middle endpoint has height at most one half. Then
\[
\boxed{\mathcal P(U)<\frac{31233}{39200}<\frac45.}
\tag{LH.1}
\]
The strict first inequality may be weakened to a non-strict one if preferred. In particular such a cap cannot be a global maximizer, since the reference value is \(M/2>4/5\).

Combined with EP3, this excludes **every nonpositive endpoint pressure** at a canonical global maximizer. Both end faces are then strictly positive, and both limiting finite-exposure measures equal the charged outer-wing curvature measures.

### 1. Normalize and bound both charged roofs

Reflect horizontally if needed and center the projection:
\[
I=[-2C,2C],\quad J=[-C,C],\quad C>0,\quad
A(C)=1,\quad A(-C)=a\le1/2.
\]
The central slope is \(s=(1-a)/(2C)\). For the left wing, write \(x=-2C+z\), \(0\le z\le C\). Concavity below the extension of the middle chord gives
\[
A(-2C+z)\le \frac{3a-1}{2}+\frac{1-a}{2C}z
\le \frac14+\frac{z}{4C}.
\tag{LH.2}
\]
The last affine expression is increasing in a at every z in [0,C], so replacing a by 1/2 is valid. On the right wing \(A\le1\). Thus the entire charged exterior reward R obeys
\[
R:=\int_{I\setminus J}A\le\frac{3C}{8}+C=\frac{11C}{8}.
\tag{LH.3}
\]
For \(C\le1/2\), this already gives \(P\le11/16<4/5\). Henceforth take \(C\ge1/2\).

Let
\[
m_R=\max_U(x+y)=2C+u,\qquad
m_L=\max_U(-x+y)=2C+v.
\]
The two baseline endpoints and the high point (C,1) imply
\[
\max(0,1-C)\le u\le1.
\tag{LH.4}
\]
Also
\[
0\le v\le1/4.
\tag{LH.5}
\]
For the upper bound in LH.5: on the left wing, LH.2 gives
\[
-x+A(x)\le2C+1/4-\left(1-\frac1{4C}\right)z\le2C+1/4.
\]
On J, the roof is at most its a=1/2 affine majorant \(3/4+x/(4C)\); since \(C\ge1/2\), \(-x+A(x)\) is bounded by \(C+1/2\le2C+1/4\). On the right wing it is at most \(1-C\le2C+1/4\). The left baseline endpoint gives the lower bound.

The actual support constraints improve the reward bound. On the right wing, setting z=2C-x,
\[
A(x)\le\min\{1,u+z\},\quad0\le z\le C.
\]
Since \(1-u\le C\), integration gives
\[
R_R\le C-\frac{(1-u)^2}{2}.
\tag{LH.6}
\]
On the left wing,
\[
A(-2C+z)\le
\min\left\{v+z,\frac14+\frac{z}{4C}\right\}.
\]
Put \(k=1-1/(4C)\), so \(1/2\le k<1\). The two lines cross at \(z_0=(1/4-v)/k\le C\): indeed \(1/4-v\le1/4\le C-1/4=kC\). Integrating the missing triangle gives
\[
R_L\le\frac{3C}{8}-\frac{(1/4-v)^2}{2k}
\le\frac{3C}{8}-\frac{(1/4-v)^2}{2}.
\tag{LH.7}
\]
Consequently
\[
\boxed{R\le\frac{11C}{8}
-\frac{(1-u)^2}{2}
-\frac{(1/4-v)^2}{2}.}
\tag{LH.8}
\]

### 2. Use the genuine full two-ray niche at one exact angle

At t=pi/4 the two actual ray roofs are
\[
m_R-\sqrt2-x,\qquad m_L-\sqrt2+x.
\]
Thus the full positive niche satisfies
\[
n_U(x)\ge (h-|x-d|)_+,\qquad
h=2C+\frac{u+v}{2}-\sqrt2,\quad d=\frac{u-v}{2}.
\tag{LH.9}
\]
Because \(u\le1\), \(v\le1/4\), and \(C\ge1/2\), the tent apex d lies in J.

For now suppose \(1/2\le C\le23/20\). One tent tail cannot reach the endpoint because
\[
h-C-d=C+v-\sqrt2\le7/5-\sqrt2<0.
\]
Exact integration of the positive tent over J gives
\[
\int_J n_U\ge h_+^2-\frac12 z_+^2,\qquad z=C+u-\sqrt2.
\tag{LH.10}
\]
If h is nonpositive then z is also nonpositive, so the formula still holds. Hence P is at most
\[
F(C,u,v)=\frac{11C}{8}
-\frac{(1-u)^2}{2}
-\frac{(1/4-v)^2}{2}
-h_+^2+\frac12z_+^2.
\tag{LH.11}
\]

### 3. Unclipped tent case

Suppose z<=0. Write \(x_0=1-u\), \(y_0=1/4-v\), and
\[
H=2C+5/8-\sqrt2>0,\qquad h=H-(x_0+y_0)/2.
\]
Since \(x_0,y_0\ge0\), Cauchy's elementary inequality gives, with \(w=(x_0+y_0)/2\),
\[
\frac{x_0^2+y_0^2}{2}+(H-w)_+^2
\ge w^2+(H-w)_+^2\ge H^2/2.
\]
The last inequality follows by completing the square for w<=H, and by \(w^2\ge H^2\) for w>=H. Therefore
\[
F\le \frac{11C}{8}-\frac12(2C+5/8-\sqrt2)^2.
\]
Complete the square in C, or put \(H=2C+5/8-\sqrt2\), to obtain the global bound
\[
\boxed{F\le\frac{11\sqrt2}{16}-\frac{99}{512}
<\frac{2827}{3584}<\frac45,}
\tag{LH.12}
\]
using \(\sqrt2<10/7\). No optimization over a finite sample is involved.

### 4. Clipped tent case

For fixed C,v, the z>0 range begins at \(u_0=\sqrt2-C\). This threshold is larger than the feasible lower bound \(\max(0,1-C)\), and for the current C range lies below 1 whenever the clipped range is nonempty. In this range h>0 and
\[
\frac{\partial F}{\partial u}
=1-u-h+z=1-C-\frac{u+v}{2},
\qquad
\frac{\partial^2 F}{\partial u^2}=-1/2.
\tag{LH.13}
\]
Hence the maximum on \([u_0,1]\) is either the boundary u_0, already covered by LH.12, or the stationary point
\[
u_*=2-2C-v.
\]
Because C>=1/2 and v>=0, \(u_*\le1\); the upper endpoint cannot furnish another case. For the stationary point to belong to the clipped region, it is necessary that
\[
C+v\le2-\sqrt2=:D.
\tag{LH.14}
\]
Thus \(C\le D\) and \(v\le D-1/2=3/2-\sqrt2\). In particular
\[
1/4-v\ge\sqrt2-5/4>0.
\]
The tent integral and right-roof deficit are nonnegative, so at that stationary point they may be discarded from the upper bound:
\[
F(C,u_*,v)\le
\frac{11D}{8}-\frac12(\sqrt2-5/4)^2
=\frac{31}{32}-\frac{\sqrt2}{8}.
\]
Consequently
\[
\boxed{F(C,u_*,v)<\frac{127}{160}<\frac45,}
\tag{LH.15}
\]
using \(\sqrt2>7/5\). This covers every clipped case, including a stationary point coinciding with the boundary.

### 5. All larger widths

For \(C\ge23/20\), use the baseline endpoints alone in the same genuine pi/4 niche:
\[
n_U(x)\ge(2C-\sqrt2-|x|)_+.
\]
Together with LH.3, this gives
\[
P\le
\begin{cases}
\displaystyle \frac{11C}{8}-(2C-\sqrt2)^2,
&23/20\le C\le\sqrt2,\\[1ex]
\displaystyle \left(\frac{11}{8}+2\sqrt2\right)C-3C^2,
&C\ge\sqrt2.
\end{cases}
\tag{LH.16}
\]
Both expressions are strictly decreasing on their respective stated ranges, and they agree at C=sqrt2. For the first, the derivative is \(11/8-4(2C-\sqrt2)<0\) already at C=23/20; for the second it is \(11/8+2\sqrt2-6C<0\) at C=sqrt2 and thereafter. Therefore the maximal bound in this entire large-width range is at 23/20. Using \(\sqrt2<99/70\),
\[
P\le\frac{253}{160}-(23/10-\sqrt2)^2
<\frac{253}{160}-(31/35)^2
=\boxed{\frac{31233}{39200}<\frac45.}
\tag{LH.17}
\]
The gap is exact: \(4/5-31233/39200=127/39200\).

The small-width bound 11/16 and middle-width bounds in LH.12 and LH.15 are all below 31233/39200 as well. This proves LH.1.

### 6. Consequence for the full global maximizing domain

**Theorem LH2 (strictly positive pressures).** Every canonical global maximizer of the spatial score has both endpoint pressures strictly positive and both limiting finite-exposure measures equal to its charged wing curvature measures.

[MID2](#proof-middle-chord) and [TF4](#proof-facet-pinning) select a canonical maximizer whose middle roof is affine and whose higher endpoint is at height one. If its lower endpoint were at most one half, LH.1 would contradict the reference lower value \(M/2>4/5\). Thus every such tilted maximizer has
\[
A(j_{\rm low})>1/2.
\]
[EP3](#proof-full-endpoints) says a nonpositive lower-side pressure forces
\(q_{\rm low}=A(j_{\rm low})+n(j_{\rm low})\le1/2\), which is impossible. The higher-side pressure is already positive by EP3. Hence both pressures are strictly positive, both end heights are positive by EP1, and EP2 gives both full limiting finite-exposure measure equalities.

In the horizontal case both pressures are already strictly positive by EP3. Thus, writing \(\omega_R,\omega_L\) for the actual charged curved-wing normal measures and \(\nu_R,\nu_L\) for the weak limits of selected finite middle-niche source exposures, the global conclusion is
\[
\boxed{C_R=e_R>0,\qquad C_L=e_L>0,\qquad
\nu_R=\omega_R,\quad\nu_L=\omega_L.}
\tag{LH.18}
\]
The central affine facet and the horizontal top face are omitted from these open-quarter wing measures. A tilted maximizer may still have a positive horizontal top segment extending from its high middle endpoint into that exterior wing. Top insertion does not imply a point top.

### 7. Exact clipped Green identity at a global maximizer

Let \(U\) be a canonical global maximizer and return to the general
coordinates \(I=[l,r]\), \(J=[j_-,j_+]\). Write
\[
O=\int_{I\setminus J}A,\qquad N_J=\int_Jn,\qquad
A_\pm=A(j_\pm),\quad n_\pm=n(j_\pm),\quad q_\pm=A_\pm+n_\pm.
\]
Put \(\omega=\omega_R+\omega_L\), \(\nu=\nu_R+\nu_L\), and let
\(T_{\rm wing}\) be the horizontal length of the height-one top face
outside J. The actual upper-boundary arclength above the charged wings,
excluding the vertical end faces, is
\[
L_{\rm wing}=\omega((0,\pi))+T_{\rm wing}.
\tag{LH.19}
\]

For an upper graph with outward normal \(\theta\), the support line
identity gives
\(h\,ds=(A-xA')\,dx\). Integrating separately on the two wings,
and separating the horizontal top segments, yields
\[
2O=\int h\,d\omega+T_{\rm wing}
+r e_R-l e_L+j_-A_--j_+A_+.
\tag{LH.20}
\]
This is integration by parts on monotone convex-boundary arcs. The
vertical end faces are represented by the displayed endpoint terms,
and are not counted again in \(\omega\).

For a selected finite polygon, every positive exposed niche segment
is supported by a line at signed distance \(h_n(\theta)-1\).
The same graph identity on that segment is
\[
(h_n(\theta)-1)\,ds=(n_n-xn_n')\,dx.
\]
Summing all positive segments in the moving \(J_n\), with the floor
segments contributing zero, gives the exact finite identity
\[
2\int_{J_n}n_n
=\int(h_n-1)\,d\nu_n-j_-^{(n)}n_n(j_-^{(n)})
+j_+^{(n)}n_n(j_+^{(n)}).
\]
[RG](#proof-prescribed-regularity) and
[EP](#proof-full-endpoints) give uniform support
and niche convergence, convergence of J endpoints, and weak convergence
of the bounded source exposure measures. Their endpoint estimates
exclude lost atoms at the omitted axis and top normals. Therefore
\[
2N_J=\int(h-1)\,d\nu-j_-n_-+j_+n_+.
\tag{LH.21}
\]
No equality between \(\nu\) and ordinary arclength of the actual
continuum niche graph is needed for this passage.

By LH2, \(\nu=\omega\). Subtract LH.21 from LH.20:
\[
2\mathcal P(U)=L_{\rm wing}+r e_R-l e_L+j_-q_--j_+q_+.
\]
The definitions of the middle endpoints and pressures give exactly
\[
j_-q_--j_+q_+=lC_L-rC_R.
\]
Using \(e_R=C_R\), \(e_L=C_L\), all four boundary terms cancel.

**Theorem LH3 (stationary wing identity).** Every canonical global
maximizer satisfies
\[
\boxed{2\mathcal P(U)=L_{\rm wing}.}
\tag{LH.22}
\]
In particular the length includes a possible top overhang. Omitting
that horizontal contribution would give the wrong identity for a
tilted cap whose top extends into a charged wing.

### 8. A height bound that survives zero-height exposure loss

Put
\[
S=A_-+A_+,\qquad E=e_R+e_L,\qquad Z=n_-+n_+.
\]
At a canonical maximizer the top meets J. Each exterior roof is
monotone toward its middle endpoint, including a possible horizontal
top portion. Hence its total vertical rise on the two wings is
\[
\int|\cos\theta|\,d\omega=S-E.
\tag{LH.23}
\]
For each finite positive niche graph the exact source decomposition
gives
\[
\operatorname{TV}(n_n|_{J_n})
=\int|\cos\theta|\,d\nu_n.
\]
Uniform convergence, after affinely identifying \(J_n\) with J, and
lower semicontinuity of total variation imply
\[
\operatorname{TV}(n|_J)\le\int|\cos\theta|\,d\nu
=S-E.
\tag{LH.24}
\]
The maximum of the continuous roof is attained. Going from the left
endpoint to a maximizing point and then to the right endpoint gives
\(2\max_J n-Z\le\operatorname{TV}(n|_J)\). Meanwhile the sum of
the two endpoint pressure equalities says \(E=(S+Z)/2\).
Consequently
\[
\boxed{\max_{x\in J}n_U(x)\le\frac{e_R+e_L}{2}.}
\tag{LH.25}
\]
This is a bound on the charged middle niche. It is not a bound on
the full niche outside J, nor an assertion that zero-height source
exposure disappears. It holds for horizontal and tilted canonical
maximizers alike.

---

<a id="proof-facet-pinning"></a>
## Technical proof 15. Pinning the affine middle facet (TF)

### 1. A whole-angle **support-inactivity neighborhood** for any tilted middle facet

Let \(U\subset\mathbb R\times[0,1]\) be a compact convex downward-closed cap of positive width \(W=r-l\), with full horizontal projection \(I=[l,r]\), height exactly one, and concave upper roof \(A\). Put
\[
j_-=l+W/4,\qquad j_+=r-W/4,\qquad J=[j_-,j_+].
\]
Suppose the whole central charged window is affine:
\[
\boxed{A(x)=a+s x\quad(x\in J),\qquad s\ne0.}\tag{TF.1}
\]
The corresponding **actual outer facet** has outward unit normal
\[
n_c=\frac{(-s,1)}{\sqrt{1+s^2}}\in\{n:n_y>0\}.
\]
Its upper supporting value is
\[
h_U(n_c)=\frac{a}{\sqrt{1+s^2}}.
\]
For every \(x\in J\), at the baseline point \(p_x=(x,0)\) the **inner-wall** inequality for this source normal would require
\(p_x\cdot n_c<h_U(n_c)-1\), but
\[
\boxed{
h_U(n_c)-1-p_x\cdot n_c
=\frac{A(x)}{\sqrt{1+s^2}}-1
\le-\delta_s,\qquad
\delta_s=1-\frac1{\sqrt{1+s^2}}>0.
}\tag{TF.2}
\]
Since \(n_{c,y}>0\), the same strict inequality against entering the *forbidden* halfplane holds for every \(y\ge0\), not only y=0:
\(
h_U(n_c)-1-(x,y)\cdot n_c\le-\delta_s
\)
for x∈J.

By uniform continuity of \(n\mapsto h_U(n)-1-(x,0)\cdot n\) on the compact unit upper semicircle times J, there is an open arc \(\Omega\Subset\{n:n_y>0\}\) around \(n_c\) such that
\[
\boxed{
h_U(n)-1-(x,y)\cdot n\le-\delta_s/2
\quad(n\in\Omega,\ x\in J,\ y\ge0).
}\tag{TF.3}
\]
The positivity of \(n_y\) is why the inequality extends to all \(y\ge0\).

**Lemma TF1 (complete niche blind spot).** If another downward convex cap \(V\) has the same horizontal projection and
\[
h_V(n)=h_U(n)\quad(n\in[0,\pi]\setminus\Omega),
\qquad
\|h_V-h_U\|_{\infty,[0,\pi]}<\delta_s/4,
\tag{TF.4}
\]
then their **entire true positive continuous-angle inner-wall niche roofs** coincide on J:
\[
\boxed{n_V(x)=n_U(x)\qquad(x\in J).}\tag{TF.5}
\]

**Proof.** Every proper lower-turn quadrant has one of the normals \(u_t=(\cos t,\sin t)\), \(v_t=(-\sin t,\cos t)\) in the upper semicircle. If **either** of its normals belongs to \(\Omega\), TF.3 and the support perturbation bound show that this *single wall* rules out the whole **positive-height forbidden quadrant at every x∈J** for both U and V. If neither normal lies in \(\Omega\), both wall supports and thus the entire one-angle V-tents are identical for U,V. The union over all real \(t\in(0,\pi/2)\), followed by max with zero, gives TF.5. No unique contact angle, active-ray chart or absence of angular superlevel components is assumed. \(\square\)

### 2. A local *outer-wing gain* with no **inner-ray cost**

Fix \(x_0\) in the relative interior of a **charged exterior wing**
\((l,j_-)\cup(j_+,r)\), and let \(p_0=(x_0,A(x_0))\) be its actual upper boundary point. Suppose
\[
A(x_0)<1,\qquad
\boxed{N_U(p_0)\cap\{n:n_y>0\}\subset\Omega,}\tag{TF.6}
\]
where \(N_U(p_0)\) denotes the set of outward supporting normal directions at \(p_0\) (relative to the upper semicircle). This is automatically satisfied for any relative-interior point of the tilted central exposed facet, since its only upper normal is \(n_c\).

Let
\[
p_\varepsilon=p_0+\varepsilon e_y,\quad
0<\varepsilon<1-A(x_0),
\]
and define the **genuine downward convex** cap
\[
\boxed{
U_\varepsilon=\operatorname{conv}
\bigl(U\cup(\{x_0\}\times[0,A(x_0)+\varepsilon])\bigr).
}\tag{TF.7}
\]
Convexity and downward closure follow directly: any convex combination of downward vertical fibers contains all heights below it at the same abscissa, by simultaneously decreasing the contributing heights. The new cap has the **same horizontal projection I and width W**, and retains height one.

For every upper normal n, the support of the new cap is
\[
h_{U_\varepsilon}(n)=
\max\{h_U(n),p_\varepsilon\cdot n\}.
\]
The continuous function \(h_U(n)-p_0\cdot n\) is positive on the compact **complement of** \(\Omega\) in the upper semicircle by TF.6. Thus it has a positive minimum \(d>0\) there. If \(\varepsilon<d\), then
\[
h_{U_\varepsilon}(n)=h_U(n)\quad(n\notin\Omega),\qquad
0\le h_{U_\varepsilon}(n)-h_U(n)\le\varepsilon\quad(n\in\Omega).
\]
Taking also \(\varepsilon<\delta_s/4\) invokes TF1 and gives **exact equality of the entire central charged niche**:
\[
\int_J n_{U_\varepsilon}=\int_J n_U.
\tag{TF.8}
\]
On the other hand \(p_\varepsilon\) lies strictly above the old roof at the **charged** x-coordinate \(x_0\). The new concave upper roof \(A_\varepsilon\) is continuous in the interior of I; it strictly exceeds A on a positive-length neighborhood of \(x_0\) inside the wing, and does not decrease anywhere. Hence
\[
\boxed{
\mathcal P(U_\varepsilon)-\mathcal P(U)
=\int_{I\setminus J}(A_\varepsilon-A)\,dx>0.
}\tag{TF.9}
\]

**Lemma TF2 (wing-boundary source normals cannot be hidden).** No **local** or global maximizer of the full spatial score \(\mathcal P\) can have a charged upper-roof boundary point satisfying TF.6, when its central roof has a nonhorizontal affine facet TF.1. The proof is the arbitrary-small, actually convex perturbation TF.7–TF.9; **it accounts for the complete moving-corner plus both attached inner-ray envelopes**, not a single contact shadow.

### 3. The canonical middle facet must terminate in two real corners

**Theorem TF3 (two strict middle-window facet junctions).** Let U be a **global maximizer** of the score \(\mathcal P\) on all downward convex caps of height at most one, selected by the global [MID2](#proof-middle-chord) reduction so that its roof is affine throughout J. If that affine slope \(s\ne0\), then
\[
\boxed{
A'_-(j_-)>s>A'_+(j_+).
}\tag{TF.10}
\]
In particular the maximal affine facet of slope s has **horizontal projection exactly** \([j_-,j_+]\). A global score maximizer whose upper roof is differentiable at **either** of the two central-window endpoints necessarily has \(s=0\), hence
\[
\boxed{A(x)\equiv1\quad(x\in J).}\tag{TF.11}
\]

**Proof.** A finite concave roof is locally Lipschitz in the interior of its projection. Its one-sided derivatives satisfy the non-strict inequalities \(A'_-(j_-)\ge s\ge A'_+(j_+)\). Suppose \(A'_+(j_+)=s\). Because \(A'\) is monotone decreasing, the one-sided slope intervals (and thus *every* upper supporting normal cone) at boundary points \(p_x=(x,A(x))\) with \(x\downarrow j_+\) from the **right wing** converge to the singleton \(\{n_c\}\). Thus there exist actual wing coordinates \(x_0>j_+\), arbitrarily close to \(j_+\), with **every** upper outward normal at \(p_0\) lying inside the open inactivity arc \(\Omega\) of TF1.

We may choose \(A(x_0)<1\). Indeed if \(s<0\), values to the right decrease strictly near \(j_+\), hence are less than one. If \(s>0\), continuity with right derivative \(s>0\) would give \(A(x)>A(j_+)\) immediately to the right; the height-one bound then forces \(A(j_+)<1\). Hence TF.6 holds. Lemma TF2 contradicts maximality. The same argument at the **left** endpoint (x\uparrow j_- through the left wing) rules out \(A'_-(j_-)=s\): for \(s>0\), the roof decreases when moving left; for \(s<0\), any matching negative left derivative forces \(A(j_-)<1\) by the height-one bound. Therefore both strict inequalities hold.

Any continuation of the affine facet into either exterior wing would give the corresponding one-sided derivative equality, which is impossible. Thus the facet's maximal x-projection is exactly J. If a global maximizer were differentiable at either endpoint, both one-sided derivatives there would equal the inside slope s, contradicting TF.10 unless \(s=0\). Finally, a downward cap of exact height one with a **horizontal** upper face on J has \(A|_J\equiv1\), because a concave roof with a horizontal segment has its global maximum at the height of that segment and its global maximum is exactly one. \(\square\)

#### 3a. A global top-insertion map, with exactly zero charged niche cost

**Theorem TF4 (top localization for every global spatial maximizer).** Let U be any positive-area downward compact convex cap of height \(H\le1\), with projection I and middle-half window J as above. If its top face \([a,b]\times\{H\}\) is disjoint from J, there is a downward convex cap \(\widehat U\supset U\) of the **same height and projection**, whose top face meets J, such that
\[
\boxed{n_{\widehat U}|_J=n_U|_J,\qquad
\mathcal P(\widehat U)>\mathcal P(U).}
\tag{TF.10a}
\]
Consequently the top face of **every** global maximizer meets J. For a height-one MID2-canonical maximizer with nonzero central slope,
\[
\boxed{s>0\Longrightarrow A(j_+)=1,\qquad
s<0\Longrightarrow A(j_-)=1.}
\tag{TF.10b}
\]

**Proof.** Suppose first that the top face lies to the right, so \(a>j_+\). Put
\[
p=(j_+,H),\qquad
\widehat U=\operatorname{conv}\bigl(U\cup(\{j_+\}\times[0,H])\bigr).
\tag{TF.10c}
\]
This cap has the same projection and height. For an upper unit normal \(n=(n_x,n_y)\), its support is \(\max(h_U(n),p\cdot n)\). If \(n_x\ge0\), the old top point \((a,H)\) dominates p, so the support is unchanged. If a support **does** change, then \(n_x<0\) and \(h_{\widehat U}(n)=p\cdot n\). At every \(x\in J\) and \(y\ge0\),
\[
h_{\widehat U}(n)-1-(x,y)\cdot n
=(j_+-x)n_x+(H-y)n_y-1\le0.
\tag{TF.10d}
\]
Thus this changed source wall excludes the entire positive-height forbidden quadrant over J, for both the old and new cap. Every angle whose two source supports are unchanged has exactly the same quadrant. Taking the union over **all real turning angles** proves equality of the two positive niche roofs on J.

The new roof is H on \([j_+,a]\). The old roof is strictly below H on \((j_+,a)\), by the definition of a. This interval lies in the charged right wing, and the new roof does not decrease anywhere. Hence
\[
\mathcal P(\widehat U)-\mathcal P(U)
\ge\int_{j_+}^{a}(H-A(x))\,dx>0.
\tag{TF.10e}
\]
If the old top lies left of J, reflect the construction and insert \((j_-,H)\). This proves the global map and excludes a disjoint top face at any maximizer. On a tilted affine central segment the only point that can have the global maximum height is its higher endpoint, proving TF.10b. \(\square\)

**Exact elementary check.** For \(A(x)=(x+1)/2\) on \([-1,1]\), the top point is \((1,1)\) and \(J=[-1/2,1/2]\). Inserting \((1/2,1)\) gives the roof \(2(x+1)/3\) up to \(x=1/2\), then height one. The all-angle argument just given proves the charged niche is unchanged, and direct rational integration gives
\[
\Delta\mathcal P=\frac1{48}+\frac1{16}=\frac1{12}>0.
\tag{TF.10f}
\]
This construction does not claim the cap itself is a feasible ambidextrous sofa. It is a globally score-improving map on the exact auxiliary domain of SD.3.

**Limit of the conclusion.** A tilted central facet can still have a low endpoint below one and a strict corner at each J endpoint. TF4 places its top at the higher endpoint; it does not flatten that facet or establish the sharp value.

---

<a id="proof-full-curvature"></a>
## Technical proof 16. Spatial source curvature and the horizontal calibration (CH)

**Local width threshold.** The constant labeled CH.1 is
\[
W_H=\frac4{35}\sqrt{523+2\sqrt{701}},\qquad C_H=W_H/4.
\tag{CH.1}
\]
The source laws below concern a prescribed canonical global maximizer
of the full spatial score. The horizontal value conclusion CH6 has
the stated hypothesis \(W\le W_H\); the later HW proof covers the
complement.

### 1. Domain, source measures, and velocities

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

### 2. Nonpositive corner height cannot carry curvature excess

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

### 3. Horizontal middle roof and the exact top interval

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

### 4. Same-sign shadowing for the spatial objective

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

### 5. An endpoint energy supplies one good quarter

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

### 6. One good quarter forces both, with visibility inside J

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

### 7. Niche confinement and the horizontal sharp value

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

#### A sharper endpoint criterion

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
[SW1](#proof-horizontal-short) gives the strict bound
\(\mathcal P\le41/50<M/2\), so this range cannot contain a global
maximizer. For \(2<W\le W_H\), CH2 gives top \(=J\);
CH.28–CH.29 and CH.18 give one good quarter. CH4 gives both, and
CH.25–CH.26 prove the value. \(\square\)

### 8. A good quarter at a tilted maximizer of width at most 8/3

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

#### Pressure control of the post-jump energy

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

---

<a id="proof-horizontal-short"></a>
## Technical proof 17. Strict short-width horizontal bound (SW)

**October 10, 2026. Written proof, independently audited within this research session.** This is a globally quantified, nonsharp exclusion within the [active spatial one-cap problem](#proof-full-domain). It uses three actual hallway angles and ordinary areas. Maximality, endpoint stationarity, curvature bounds, reflection symmetry and niche connectivity are not hypotheses.

**Theorem SW1.** Let U be a compact downward convex cap of height one with
\[
I=[-a,a],\quad 0<a\le1,\quad J=[-a/2,a/2],\quad A_U|_J=1.
\]
For its entire continuous-angle positive niche n,
\[
\boxed{\mathcal P(U)=\int_{I\setminus J}A_U-\int_J n
\le\frac{41}{50}<\frac M2.}
\tag{SW.1}
\]
In particular a horizontal canonical global maximizer cannot have width
at most two. This theorem does not bound the remaining wide or tilted caps.

### 1. Exact 45-degree relaxation and quantitative restrictions

Write
\[
k=\sqrt2-1,\quad
u=\sqrt2h_U(\pi/4)-1,\quad v=\sqrt2h_U(3\pi/4)-1,
\quad m=(u+v)/2,\quad d=(u-v)/2.
\]
The top endpoints and the containing box imply \(a/2\le u,v\le a\).
The cap lies below
\[
A_0(x)=\min(1,1+u-x,1+v+x),\qquad
O_0:=\int_{I\setminus J}A_0
=a-\frac{(a-u)^2+(a-v)^2}{2}.
\]
Put \(D=\int_{I\setminus J}(A_0-A_U)\ge0\).
The actual angle \(\pi/4\) supplies the tent
\[
n_{45}(x)=[\min(u-k-x,v-k+x)]_+.
\]
Its apex d lies in J. For \(a>k\), exact triangle integration gives
\[
N_{45}:=\int_Jn_{45}
=(m-k)_+^2-\frac{(u-k-a/2)_+^2+(v-k-a/2)_+^2}{2}.
\]
Consequently \(\mathcal P\le F-D\), where
\[
F=a-\frac{(a-u)^2+(a-v)^2}{2}-(m-k)_+^2
+\frac{(u-k-a/2)_+^2+(v-k-a/2)_+^2}{2}.
\tag{SW.2}
\]
This F is concave in \((u,v)\) on \([a/2,a]^2\). Where \(m>k\),
its piecewise Hessian is
\[
\begin{pmatrix}
-3/2+\mathbf1_{u-k-a/2>0}&-1/2\\
-1/2&-3/2+\mathbf1_{v-k-a/2>0}
\end{pmatrix},
\]
negative semidefinite in all four cases. Where \(m\le k\), both
clipping terms vanish and the Hessian is \(-\mathrm{Id}\). First
derivatives agree across all boundaries. The symmetric interior critical
point \(u=v=(a+k)/2\) therefore proves
\[
F\le B(a):=a-(a-k)^2/2\le B(1)=2k.
\tag{SW.3}
\]

Suppose for contradiction that \(\mathcal P>41/50\). The trivial
bound \(\mathcal P\le a\) gives \(a>41/50>k\). We claim
\[
a>9/10,\quad m>16/25,\quad
u-a/2<8/25,\quad v-a/2<8/25,
\quad D<2k-41/50<3/350.
\tag{SW.4}
\]
Here are the full checks.

- B increases on \((k,1]\), and \(k<1/2\) gives
  \(B(9/10)<9/10-(2/5)^2/2=41/50\).
- Concavity and exchange symmetry give \(F(a,u,v)\le F(a,m,m)\).
  If \(m\le16/25\) and \(a>9/10\), the clipping terms vanish.
  For \(m\le1/2\),
  \(a-(a-m)^2=m+1/4-(a-m-1/2)^2\le3/4\).
  For \(1/2<m\le16/25\), the symmetric expression increases with
  \(a\le1\), then with \(m\le16/25\). Its upper value is
  \((2050k-337)/625<41/50\).
- On the constrained half-square \(v-a/2\ge t_0:=8/25\), the
  concave maximum is at
  \(v=a/2+t_0\), \(u=a/2+(2k-t_0)/3\).
  Both clipping terms vanish there, the u derivative is zero, and
  the v derivative is \((2k-4t_0)/3<0\). These are the sufficient
  concave optimality conditions on the whole constrained square.
  The resulting value is
  \[
  B(a)-\frac23(t_0-k/2)^2
  \le\frac{9550k-881}{3750}<\frac{41}{50}.
  \]
  The last comparison follows from \(\sqrt2<577/408\), whose
  squared difference is \(577^2-2\cdot408^2=1\).
  Exchanging u and v proves the other restriction.
- Finally \(\sqrt2<99/70\) gives \(2k-41/50<3/350\).

Since \(8/25<k\), the entire positive 45-degree tent is now inside J.

### 2. Exterior area pays for two support deficits

Set
\[
\theta=\pi/8,\quad c=\cos\theta,\quad s=\sin\theta,\quad
\beta=c-s,\quad K=1/k=1+\sqrt2,
\quad C_0=\frac1{2k(1-k)}=Kc^2=\frac{4+3\sqrt2}{4}.
\]
The support of \(A_0\) at normal \((-s,c)\) is \(c+sv\), at
\((-v,1)\). Define the actual deficits
\[
\delta_L=c+sv-h_U(5\pi/8)\ge0,\qquad
\delta_R=c+su-h_U(3\pi/8)\ge0.
\]
Since \((-a/2,1)\in U\),
\[
\delta_L\le s(v-a/2).
\tag{SW.5}
\]
Cutting \(A_0\) by its actual support line lowered by \(\delta_L\)
removes a triangle at \((-v,1)\). Its horizontal side lengths are
\(\delta_L/s\) toward the top and \(\delta_L/(c-s)\) toward the
45-degree outer facet. If the latter is at most \(a-v\), SW.5 puts
the entire triangle in the charged left wing. Its exact area is
\[
\frac{\delta_L^2}{2s(c-s)}=K\delta_L^2.
\]
This containment must hold. Otherwise set
\(\delta_0=(c-s)(a-v)<\delta_L\). SW.5 still puts the corresponding
smaller triangle entirely in the wing, forcing
\[
D\ge K\delta_0^2=\frac{(a-v)^2}{\sqrt2}
>\frac{(13/100)^2}{\sqrt2}>\frac3{350},
\]
because \(a-v>9/20-8/25=13/100\). This contradicts SW.4.
The reflected triangle lies in the other wing, so no material is counted
twice and
\[
\boxed{D\ge K(\delta_L^2+\delta_R^2).}
\tag{SW.6}
\]

### 3. Two disjoint genuine additional niche tails

Put \(\eta=2/25\) and
\[
E_L=(\eta-\delta_L/c)_+,\qquad E_R=(\eta-\delta_R/c)_+.
\]
The second wall at \(\pi/8\) has height
\(S_\theta(x)=(h_U(5\pi/8)-1)/c+kx\).
At the left zero \(x_0=k-v\) of the 45-degree tent, it equals
\[
S_\theta(x_0)=1-1/c+k^2-\delta_L/c.
\]
Suppose \(E_L>0\). The exact inequality
\[
1-1/c+k^2>\eta
\tag{SW.7}
\]
shows that this wall dominates \(S'(x)=E_L+k(x-x_0)\).
The companion first wall is also sufficient, as follows.

An attaining point for \(h_U(\pi/4)\) has \(x+y=1+u\) and
\(y\le1\), hence \(x\ge u\). Therefore
\[
h_U(\pi/8)\ge s+cu.
\tag{SW.8}
\]
At \(x_R=x_0+E_L/(1-k)\), the first-wall lower bound from SW.8
is at least \(S'\) exactly when
\[
2m\ge1/c+(1+\sqrt2)E_L.
\]
This follows from \(m>16/25\), \(E_L\le\eta\), and
\[
1/c+(1+\sqrt2)\eta<32/25.
\tag{SW.9}
\]
The difference of the two lines increases as x decreases. Hence the
whole tail interval ending at \(x_R\) really is under both attached
walls, and the full niche dominates \(S'_+\) there.

Furthermore
\[
x_R-d=k-m+\frac{E_L}{1-k}
<k-\frac{16}{25}+\frac\eta{1-k}<0.
\]
The last comparison follows from
\(k+\eta/(1-k)=(26k+3)/25<16/25\).
Thus the extra niche area above \(n_{45}\), on the left side of
its apex, contains a triangle of peak height \(E_L\), left slope k,
and right downward slope \(1-k\). Its area is \(C_0E_L^2\).

The peak is inside J because \(x_0+a/2>k-8/25>0\).
Only the outer tip can be clipped by J. The omitted horizontal length
is at most
\[
L_0=8/25-k+\eta/k=(12-23k)/25>0,
\]
so the omitted area is at most \(kL_0^2/2\).
If \(E_L=0\), the lower bound
\(C_0E_L^2-kL_0^2/2\) is already true by nonnegativity; no wall
comparison is asserted in that case.

Horizontal reflection supplies the corresponding right tail at
\(3\pi/8\). It lies strictly to the right of d, so the two added
regions are disjoint. Consequently
\[
\boxed{\int_Jn\ge N_{45}
+C_0(E_L^2+E_R^2)-kL_0^2.}
\tag{SW.10}
\]
This remains valid for arbitrary additional overlaps and disconnected
horizontal sections of the full niche.

For exact checks of SW.7 and SW.9 use \(c^2=(2+\sqrt2)/4\)
and square positive sides. SW.7 is equivalent to
\(\sqrt2<1777/1249\), which follows from \(\sqrt2<99/70\).
SW.9 is equivalent to \(\sqrt2>231/167\), implied by
\(\sqrt2>24/17\).

### 4. Combine the two ordinary-area payments

Since \(Kc^2=C_0\), every \(\delta\ge0\) satisfies
\[
K\delta^2+C_0(\eta-\delta/c)_+^2
=C_0\bigl[(\delta/c)^2+(\eta-\delta/c)_+^2\bigr]
\ge C_0\eta^2/2.
\]
Apply this separately to the two wings and their disjoint niche tails.
SW.3, SW.6 and SW.10 give
\[
\mathcal P\le F-C_0\eta^2+kL_0^2
\le2k-C_0\eta^2+kL_0^2
=\frac{5140k-1617}{625}
<\frac{3587}{4375}<\frac{41}{50}.
\]
The simplification uses \(k^2=1-2k\); the penultimate comparison uses
\(k<29/70\). The last rational gap is \(1/8750\).
This contradicts the supposition \(\mathcal P>41/50\) and proves SW1.

Finally the defining cubic is negative at \(297/1000\), so
\(Y>297/1000\). The inequality \(\arctan Y\ge Y-Y^3/3\)
and monotonicity on the relevant positive interval give
\[
\frac M2>
\frac{1+4(297/1000)^2+297/1000-(297/1000)^3/3}{2}
>\frac{41}{50}.
\]
Thus the exclusion is strictly below the exact reference value, without
using a rounded numerical approximation to M.

The proof was checked independently for the support constraints, all
window clipping, disjointness, concave optimization, and exact constants.
It is a written mathematical proof, not a Lean verification or a
finite-angle numerical certificate for the full sharp inequality.

---

<a id="proof-horizontal-complete"></a>
## Technical proof 18. Complete horizontal width coverage and exact certificates (HW)

**Scope.** The cap is a horizontal, middle-chord-canonical global
maximizer of the full spatial score, as defined in FTM and CH.
This chapter excludes the remaining widths for such a maximizer.

### Part I. A first exact width exclusion

Center \(I=[-2C,2C]\), \(J=[-C,C]\), with \(A=1\) on \(J\). Set \(a=2C\), \(k=\sqrt2-1\), and define the actual support parameters
\[
u=\sqrt2h_U(\pi/4)-1,\qquad
v=\sqrt2h_U(3\pi/4)-1,\qquad m=(u+v)/2.
\]
The central plateau and height-one box give \(a/2\le u,v\le a\). The actual endpoint points imply
\[
u\ge a+e_R-1,\qquad v\ge a+e_L-1.
\]
For a horizontal global maximizer, EP gives
\[
e_R+e_L=1+\frac{n_U(C)+n_U(-C)}2\ge1.
\]
Hence
\[
m\ge a-1/2=2C-1/2.
\tag{HW.1}
\]

The actual 45-degree support lines majorize the exterior roof by
\(A_0(x)=\min(1,1+u-x,1+v+x)\), and its actual niche tent is
\([\min(u-k-x,v-k+x)]_+\). Integrating gives, whenever \(m>k\),
\[
\mathcal P(U)\le F(u,v)
=a-\frac{(a-u)^2+(a-v)^2}{2}-(m-k)^2
+\frac{(u-k-a/2)_+^2+(v-k-a/2)_+^2}{2}.
\tag{HW.2}
\]
At fixed \(a\), this function is symmetric and concave in \((u,v)\). In each of the four clipping regions its Hessian has diagonal entries \(-3/2\) plus the respective clipping indicator and off-diagonal entries \(-1/2\); all are nonpositive. The first derivatives agree across clipping boundaries. Thus
\[
F(u,v)\le F(m,m)
=a-(a-m)^2-(m-k)^2+(m-k-a/2)_+^2.
\tag{HW.3}
\]

Suppose \(C\ge13/15\). Then HW.1 places \(m\) to the right of the unconstrained maximum \(C+k/2\) in the unclipped region; in the clipped region the derivative in \(m\) is \(2(C-m)<0\). Therefore HW.3 is bounded above by its value at \(m=2C-1/2\):
\[
\mathcal P(U)\le
\begin{cases}
Q_1(C)=2C-1/4-(2C-1/2-k)^2,& C\le1/2+k,\\
Q_2(C)=(1+2\sqrt2)C-3C^2-1/4,& C\ge1/2+k.
\end{cases}
\tag{HW.4}
\]
Both branches are decreasing on their stated parts of \([13/15,\infty)\), and their values agree at the switch. Using \(\sqrt2<99/70\),
\[
Q_1(13/15)=\frac{67\sqrt2}{15}-\frac{2477}{450}
<\frac{256}{315}<\frac{41}{50}<\frac M2.
\tag{HW.5}
\]
This contradicts the reference score at a global maximizer. Together with SW1 it proves
\[
\boxed{\frac12<C<\frac{13}{15}.}
\tag{HW.6}
\]

### Part II. Exact horizontal leakage bootstrap

The next argument excludes the whole interval
\[
\frac{8571}{12500}\le C\le\frac45.
\tag{B.1}
\]
Its lower endpoint lies strictly below \(C_H\), as checked exactly below.

### 1. Canonical horizontal hypotheses and one-turn feasibility

Let U be a horizontal canonical global maximizer, centered with
\(I=[-2C,2C]\), \(J=[-C,C]\). SW1 gives C>1/2. CH2 gives top exactly
\(J\times\{1\}\). Write \(e_R,e_L\) for its end heights,
\(E=e_R+e_L\), and \(n_\pm=n(\pm C)\). EP and LH give

\[
e_R=\frac{2+3n_+-n_-}{4},\quad
e_L=\frac{2+3n_--n_+}{4},\quad
E=1+\frac{n_++n_-}{2},\quad
\max_J n\le E/2,\quad 2P=L_{\rm wing}.
\tag{B.2}
\]

The box-wall bound CH5 gives

\[
n_\pm\le H(C):=1-\sqrt{1-C^2},\qquad
\frac12-\frac H4\le e_R,e_L\le\frac12+\frac{3H}4.
\tag{B.3}
\]

Here and below C<1. The following geometric facts justify applying the
ordinary one-turn bound, rather than assuming it transfers automatically.

#### Every inner corner lies horizontally in J for 1/2<=C<=13/15

Put s=sin t, k=cos t. The unit-height box and the left top endpoint give
\(f(t)\le2Ck+s\), \(g(t)\ge Cs+k\). Hence

\[
c_x=(f-1)k-(g-1)s\le C(2-3s^2)-k+s.
\]

We show \(C(1-3s^2)\le k-s\).

* If \(s^2\le1/3\), then \(k\ge1-3s^2/5\), as follows by
  squaring positive sides. Using C<=13/15, the desired margin is at least
  \[
  2s^2-s+2/15=2(s-1/4)^2+1/120>0.
  \]
* If \(1/3\le s^2\le1/2\), the left side is nonpositive and the
  right side nonnegative.
* If \(s^2\ge1/2\), use C>=1/2 and
  \[
  2(s-k)=\frac{2(2s^2-1)}{s+k}
       \le4s^2-2\le3s^2-1.
  \]

Thus c_x<=C; reflection gives c_x>=-C. This proof does not use curvature
domination or a source contact chart.

#### Convex wing niches and a genuine connected one-turn body

For x>=C, all quadrant apexes have x-coordinate at most C. Each positive
quadrant roof there uses its first descending wall, so n is the maximum
of affine first-wall roofs and zero. Thus n is convex on [C,2C]. It is
convex on [-2C,-C] by reflection. The box bound gives n(+-2C)=0, and
indeed the niche vanishes outside I.

On J, A=1 and B.2 gives n<=E/2<=1. On each wing A-n is concave and is
nonnegative at both endpoints. Therefore n<=A everywhere. The set

\[
S=U\setminus N(U)=\{(x,y):x\in I,\ n(x)\le y\le A(x)\}
\]

is compact and connected: its continuous top graph is connected and
every interval fiber meets that graph. The outer support halfplanes of U
and exclusion of every corresponding inner quadrant provide the full
canonical one-turn placements for S. Actual equality between U's hull
and the moving sofa's hull is not needed.

Thus the existing ordinary one-turn bound applies to S. Use the already
recorded exact bound

\[
G\le G_0:=22199/10000
\]

from SE.1 of [one-turn-single-excess-quarter.md](#external-inputs), whose explicit external
dependency is Baek's ordinary one-turn theorem and whose rational value
comes from the six existing AreaBounds enclosures. No stronger numerical
bound or new Lean computation is assumed here.

Convexity of n on each wing gives

\[
N_{\rm out}:=\int_{I\setminus J}n
\le\frac C2(n_++n_-)=C(E-1).
\]

The two wing chord bounds and the triangle inequality give

\[
P=\frac{L_{\rm wing}}2
\ge\frac12\left[\sqrt{C^2+(1-e_R)^2}
                +\sqrt{C^2+(1-e_L)^2}\right]
\ge\sqrt{C^2+(1-E/2)^2}.
\]

Since \(|S|=P+2C-N_{\rm out}\), we obtain the necessary inequality

\[
\boxed{C(3-E)+\sqrt{C^2+(1-E/2)^2}\le G_0.}
\tag{B.4}
\]

In particular, if \(n_\pm\le B\le1\), then E<=1+B and the left
side of B.4 decreases with E. Hence

\[
\boxed{C(2-B)+\sqrt{C^2+(1-B)^2/4}\le G_0.}
\tag{B.5}
\]

This is the exact scalar inequality used below.

### 2. Curvature excess can occupy only a short initial interval

Use the horizontal velocity notation p,q,u,v of CH.2. The same-sign
shadowing and propagation theorems are valid for the spatial maximizer:
u=0,v<=1/2 on p>0,q>0; every later positive-q component has q<=1/8.
Consequently any u>1 must lie in the initial positive-q component after
its first p=0 time t_A. If this crossing does not occur, u<=1 everywhere
and the endpoint leakage is zero.

Let e=e_R. The initial energy calculation gives

\[
q(t_A)+1\le\sqrt{9C^2-e(1-e)}.
\]

Define

\[
\epsilon=\bigl(\sqrt{9C^2-e(1-e)}-2\bigr)_+,
\qquad h=\sqrt{1+4\epsilon}-1.
\tag{B.6}
\]

While q>1 after the crossing, p'<=-1, hence p(t_A+tau)<=-tau.
The nonlinear bound on v then gives

\[
q'\le-\frac{1+\tau}{2}\qquad(0\le\tau\le1).
\]

When p>=-1 this follows from v<=kappa(p)=(1-p)/2. If p<-1, the
stronger bound q'<=-1 still implies it for tau<=1. Thus

\[
(u(t_A+\tau)-1)_+
\le\left(\epsilon-\frac\tau2-\frac{\tau^2}{4}\right)_+.
\tag{B.7}
\]

For C<=4/5, B.3 gives

\[
\epsilon\le
\left(\sqrt{9C^2-1/4+9H(C)^2/16}-2\right)_+<2/5,
\]

so h<1 and the whole possible excess interval is covered by B.7. All
other parameter values have u<=1.

On the initial positive-positive interval q'>=-1, since v>=0,p>=0.
Therefore p'=-1-q<=-3C+t, and

\[
p(t)\le e-3Ct+t^2/2.
\]

The first root of this upper quadratic bounds the crossing:

\[
t_A\le T(C,e):=3C-\sqrt{9C^2-2e}.
\tag{B.8}
\]

If the positive component ends before such a crossing, the leakage-zero
case has already been treated.

### 3. The endpoint leakage kernel

The top exactly equals J, so f(L)=1,f'(L)=-C. Solving f''+f=u backward
from L gives the exact first-wall identity at x=C:

\[
R_t(C)=\frac1{\sin t}\int_t^L\sin(s-t)[u(s)-1]ds.
\tag{B.9}
\]

The box-wall estimate further says R_t(C)<=0 unless

\[
t>t_{\rm box}(C):=\frac\pi2-2\arctan C
 =2\arctan\frac{1-C}{1+C},
\qquad
\sin t_{\rm box}=\frac{1-C^2}{1+C^2}.
\tag{B.10}
\]

For these remaining angles, discard negative curvature differences in
B.9 and use sin(s-t)<=s-t. B.7 yields

\[
n(C)\le
\frac{A_0(t_A-t_{\rm box})_++A_1}{\sin t_{\rm box}},
\tag{B.11}
\]

where the integrals of the quadratic envelope are

\[
A_0=\int_0^h(\epsilon-\tau/2-\tau^2/4)d\tau
    =h^2/4+h^3/6,
\]
\[
A_1=\int_0^h\tau(\epsilon-\tau/2-\tau^2/4)d\tau
    =h^3/12+h^4/16.
\tag{B.12}
\]

Here epsilon=(h^2+2h)/4. The extra factor bound in B.11 is valid even
if t_A<t_box, because s=t_A+tau and t>=t_box imply
s-t<=(t_A-t_box)_++tau. Reflection gives the same estimates for n(-C).

### 4. Seven exact rational intervals

Every decimal in the following table denotes the exact terminating
rational number. Each row supplies an interval [a,b] and witnesses
\(H_*,h_*,T_*,t_*,B_*\).

| a | b | H_* | h_* | T_* | t_* | B_* |
|---|---|---|---|---|---|---|
| 0.68568 | 0.686 | 0.2724 | 0.0135 | 0.377 | 0.368 | 1/400000 |
| 0.686 | 0.69 | 0.2762 | 0.038 | 0.3784 | 0.3627 | 1/30000 |
| 0.69 | 0.7 | 0.2859 | 0.0971 | 0.3801 | 0.3492 | 1/2000 |
| 0.7 | 0.725 | 0.3113 | 0.2323 | 0.3845 | 0.3161 | 3/400 |
| 0.725 | 0.75 | 0.3386 | 0.3542 | 0.3799 | 0.2837 | 31/1000 |
| 0.75 | 0.775 | 0.3681 | 0.4662 | 0.3765 | 0.2521 | 83/1000 |
| 0.775 | 0.8 | 0.4 | 0.5703 | 0.3742 | 0.2213 | 9/50 |

The following **rational inequalities** verify every row. They are the
certificate, rather than numerical evaluations of a transcendental
function. Put \(z=(1-b)/(1+b)\),
\(\epsilon_*=(h_*^2+2h_*)/4\), and use A0,A1 from B.12 with h=h_*.

\[
\begin{aligned}
&(1-H_*)^2\le1-b^2,\\
&(2+\epsilon_*)^2\ge9b^2-1/4+9H_*^2/16,\\
&6aT_*-T_*^2\ge1+3H_*/2,\qquad T_*<3a,\\
&t_*\le2(z-z^3/3),\\
&B_*\frac{1-b^2}{1+b^2}
 \ge A_0(T_*-t_*)_++A_1.
\end{aligned}
\tag{B.13}
\]

Indeed H(C)<=H_* for C<=b. The second inequality gives h<=h_* by
B.6–B.7 and B.3. The third gives T(C,e)<=T_* whenever C>=a and
e<=1/2+3H_*/4; it is just the squared version of B.8. The fourth uses
the elementary integral bound arctan z>=z-z^3/3. Finally sin t_box(C)
is decreasing with C, so B.11 and the last inequality prove
n(C),n(-C)<=B_* uniformly throughout the row's interval.

For every row the final contradiction is also a rational check:

\[
R_*:=G_0-a(2-B_*)>0,
\qquad
a^2+(1-B_*)^2/4>R_*^2.
\tag{B.14}
\]

Thus
\(a(2-B_*)+\sqrt{a^2+(1-B_*)^2/4}>G_0\). The left side in B.5
increases with C at fixed B_*, so B.14 contradicts B.5 on the whole
interval [a,b].

All B.13 and B.14 inequalities were checked with exact rational
arithmetic, not floating point. The companion
[check_horizontal_leakage_exact.py](#verification-record) uses only Python's standard-library
Fraction class and the seven stated rows.
It performs no search or sampled-angle approximation.

The initial rational a0=8571/12500 is below C_H. To check this without
rounding C_H, put z0=a0^2. Then 35z0-15>0 and

\[
4(1-z_0)-(35z_0-15)^2
=\frac{878611101631}{976562500000000}>0.
\]

The increasing defining expression 35z-15-2sqrt(1-z) is therefore still
negative at z0. This proves the claimed overlap with the existing
horizontal sharp-value interval.


### Part III. Wide-width exclusion by three actual niche angles

### Statement

Let a height-one downward convex cap have projection I=[-a,a], horizontal
roof A=1 on J=[-a/2,a/2], and endpoint heights e_R=A(a), e_L=A(-a).
Assume its actual full niche n satisfies the horizontal EP identities

    e_R = 1/2+(3 n(a/2)-n(-a/2))/4,
    e_L = 1/2+(3 n(-a/2)-n(a/2))/4.

If 8/5 <= a <= 26/15, then its actual spatial score satisfies

    P < 261719/320000 < 41/50 < M/2.                 (W1)

Together with Part I's independent 45-degree exclusion for
C=a/2 >=13/15, this excludes every horizontal global maximizer with
C>=4/5. Only the three real niche angles pi/8, pi/4, 3pi/8 are used
to prove (W1); all other niche portions are retained as nonnegative gain.

Put

    r=sqrt(2), k=r-1, c=cos(pi/8), s=sin(pi/8).

Useful exact identities are

    s/c=k, k+1/k=2r, 1+k=r,
    1/s+1/c=4c, 1/s-1/c=4s,
    1/(r c)=2s, 1/(2sc)=r.

### 1. Endpoint and 45-degree data

The unit-height box gives, for C=a/2<1,

    n(+-C) <= H(C):=1-sqrt(1-C^2).

Indeed, the first wall at x=C is at most
1+(C cos(t)-1)/sin(t), whose maximum is H(C); reflect for -C.
Since C<=13/15, H(C)<2/3. Thus EP implies

    e_R,e_L >=1/3,       E:=e_R+e_L >=1.             (W2)

Define the actual supports

    u=r h(pi/4)-1,       v=r h(3pi/4)-1,
    m=(u+v)/2,           d=(u-v)/2,
    w_R=a-u,             w_L=a-v.

The plateau and box give a/2<=u,v<=a. The actual endpoint points give
u>=a+e_R-1 and v>=a+e_L-1. Consequently

    0<=w_R,w_L<=2/3,     m>=a-1/2>=11/10.           (W3)

The cap is below the genuine upper majorant

    A0(x)=min(1,1+u-x,1+v+x),      -a<=x<=a.

Its two charged exterior wings have area

    O0=a-[(a-u)^2+(a-v)^2]/2.

Write D=integral_(I\J)(A0-A)>=0. The actual 45-degree niche tent is

    n45(x)=[min(u-k-x,v-k+x)]_+.

Its apex d is in J. Since m>k, its exact integral on J is

    N45=(m-k)^2
         -[(u-k-a/2)_+^2+(v-k-a/2)_+^2]/2.

Let F=O0-N45. For fixed a, F is concave in (u,v), and symmetric.
This is the same elementary 45-degree concavity used in the
short-width proof: the Hessian in the positive-apex region is
diagonal -3/2 plus the corresponding clipping indicator, with
off-diagonal -1/2; all four resulting Hessians are nonpositive.
Therefore

    F <= Fsym(a,m)
       :=a-(a-m)^2-(m-k)^2+(m-k-a/2)_+^2.           (W4)

### 2. Exterior payment from flat pieces only

Define the actual near-vertical support deficits

    delta_L=c+s v-h(5pi/8),
    delta_R=c+s u-h(3pi/8).

These are nonnegative because A0 supports those directions at its two
top corners. The height-one points at the endpoints of J imply

    0<=delta_L<=s(v-a/2)=s(a/2-w_L),
    0<=delta_R<=s(u-a/2)=s(a/2-w_R).                 (W5)

On the flat portion x=-v+z, 0<=z<=delta_L/s, the new supporting line
cuts A0 by the height delta_L/c-kz. This entire small triangle lies
in the left charged wing by (W5). Its area is

    delta_L^2/(2sc)=r delta_L^2.

The reflected right triangle lies in the other wing. In particular,
there is no need to fit any triangle past a vertical endpoint, and

    D >= r(delta_L^2+delta_R^2).                    (W6)

### 3. Two disjoint additional niche half-triangles

At theta=pi/8 the actual second wall is

    b+kx,       b=1-1/c+k v-delta_L/c.

The actual endpoint (a,e_R) supplies a lower bound for the companion
first wall:

    R_theta(x) >= B-x/k,
    B=e_R+a/k-1/s.

Thus the full niche contains the positive part of the true two-wall
lower tent min(b+kx,B-x/k).

On the right of the 45-degree apex d, the signed 45-degree roof is
u-k-x. Set

    x_L=(u-k-b)/r,
    x_*=(B-b)/(2r),
    Z_R=(B+b)/2-u+k.

Then Z_R=r(x_*-x_L). If Z_R>0, on [x_L,x_*] the lower tent equals
b+kx and exceeds the signed 45-degree roof by r(x-x_L). We now
check that this entire half-triangle is inside J, to the right of d,
and above the positive part of the 45-degree roof.

First,

    x_L-d = k m+2s-1+delta_L/(r c)>0,               (W7)

because m>=11/10, k>2/5, and s>3/8.

Next, writing v=a-w_L,

    x_*=[2a+e_R+k w_L-(1+4s)+delta_L/c]/(2r).

Using delta_L/c<=k(a/2-w_L) and e_R<=1 shows that x_*<=a/2 follows
from

    ((3-r)/2)a <=4s.

This holds throughout a<=26/15: its left side is below 104/75
using r>7/5, while its right side is above 3/2. Hence

    x_* < a/2.                                    (W8)

Finally, x_*<=u-k follows from

    e_R+2r w_R <=(3k/2)a+1+4s-2rk.

Since e_R<=1-w_R and w_R<=2/3, it is enough to prove

    (2r-1)*2/3 <=(12/5)k+4s-2rk.                  (W9)

For a completely rational check, r<10/7 and k<3/7 bound the left
side by 26/21 and bound the right side below by
3/2-48/245=639/490>26/21. We used r>7/5 to note that
12/5-2r<0 when applying the bound k<3/7. Therefore

    x_* < u-k.                                    (W10)

Equations (W7)-(W10) prove the claimed half-triangle containment.
Its area is Z_R^2/(2r). If Z_R<=0 the zero lower bound is immediate;
no interval assertion is needed in that case.

Reflection, using the actual angle 3pi/8 and endpoint (-a,e_L),
gives a half-triangle on the left of d of area (Z_L)_+^2/(2r), with

    Z_R=Z_R^0-delta_L/(2c),
    Z_L=Z_L^0-delta_R/(2c),

and

    Z_R^0+Z_L^0
      =E/2+a/k+(k-2)m+1-1/s-1/c+2k=:S0.            (W11)

The two half-triangles lie on opposite sides of d, so there is no
overlap overcount. Hence the actual full niche satisfies

    integral_J n >= N45+[(Z_R)_+^2+(Z_L)_+^2]/(2r). (W12)

### 4. Combine the ordinary exterior and niche payments

Put D0=r(delta_L^2+delta_R^2),
G0=[(Z_R)_+^2+(Z_L)_+^2]/(2r), and Delta=delta_L+delta_R.
By (W11) and Cauchy-Schwarz,

    (S0)_+ <= sqrt(4r G0)+sqrt(r D0/(4c^2)),

so

    (S0)_+^2 <= [4r+r/(4c^2)](D0+G0) <=8(D0+G0).

The coefficient is strictly below 8 already from r<3/2 and c^2>3/4;
the displayed product inequality also covers D0+G0=0.
Together with (W6) and (W12), this yields the weak bound sufficient
for the proof:

    P <= Fsym(a,m)-(S0)_+^2/8.                     (W13)

Use E>=1 and the elementary coefficient inequalities

    1/k>12/5,        k-2>-8/5,
    3/2+2k-4c >-11/8

to lower-bound S0 by the simple affine expression

    S(a,m)=(12/5)a-(8/5)m-11/8.

For the last constant comparison, 4c<7/8+2r follows by squaring:
the difference of the squared right and left sides is 49/64-r/2>0.
Consequently

    P <= G(a,m):=Fsym(a,m)-[S(a,m)_+]^2/8.          (W14)

### 5. A single concave scalar bound

The function Fsym is jointly concave in (a,m) on the region in use.
Its Hessian before window clipping is

    [[-2,2],[2,-4]],

and after clipping is

    [[-3/2,1],[1,-2]].

Both are negative definite, and the first derivatives match at the
clipping boundary. Subtracting the convex positive square of the
affine function S preserves concavity of G.

At a0=8/5, m0=11/10, the clipping term vanishes and S=141/200>0.
The exact derivatives are

    G_a(a0,m0)=-423/1000,
    G_m(a0,m0)=2k-459/500<0.

For every a>=a0, m>=a-1/2, the displacement decomposes as

    (a-a0,m-m0)=(a-a0)(1,1)
                      +(m-a+1/2)(0,1).

Both directional derivatives are negative, so the supporting-plane
inequality for the concave G gives G(a,m)<=G(a0,m0). Finally

    G(a0,m0)=(21/5)k-295081/320000
             <261719/320000<41/50,

where k<29/70 follows from sqrt(2)<99/70. This proves (W1).

All payments used ordinary cap area and ordinary portions of the
actual full two-ray niche; no niche connectivity, reflection
symmetry, curvature bound, artificial grid stationarity, or
candidate contact chart was assumed.

---

<a id="proof-tilted-width"></a>
## Technical proof 19. Tilted short, wide and intermediate width exclusions

### Part A. Short widths, including every tilted middle facet

#### Statement

Let U be a downward convex cap of height one with projection I=[-a,a],
0<a<=1, and upper roof A affine on J=[-a/2,a/2]. Suppose the higher
middle endpoint has height one. After reflection write

    A(-a/2)=1-h, A(a/2)=1, 0<=h<1.

Let n be the actual full continuous-angle positive two-wall niche. Then

    P(U):=integral_(I\J) A - integral_J n <41/50.               (TS1)

Thus the entire short tilted canonical maximizing range C=W/4<=1/2
is excluded. The stronger assumed bound h<1/2 is not needed here.

Put

    k=sqrt(2)-1, r=sqrt(2), c=cos(pi/8), s=sin(pi/8),
    K=1/k, Gamma=1/[2k(1-k)]=K c^2=(4+3r)/4,
    t0=8/25, eta=2/25, L0=t0-k+eta/k=(12-23k)/25>0.

We use k^2=1-2k, s/c=k, 1/(kc)=1/s, K(1-k)=r,
2/5<k<29/70<3/7<1/2, and the two elementary inequalities

    1-1/c+k^2>eta,
    1/c+K eta<32/25.                                           (TS2)

For completeness, after squaring positive sides the first comparison
follows from r<1777/1249, and the second from r>231/167. The simpler
bounds r<99/70 and r>24/17 imply them.

#### 1. Raise the left wing to a genuine horizontal-middle cap

Define a new roof

    Ahat(x)=A(x)+h for -a<=x<=-a/2,
    Ahat(x)=1      for -a/2<=x<=a/2,
    Ahat(x)=A(x)   for  a/2<=x<=a.

This is a concave height-one roof. The old left-wing slopes are at
least h/a, and the old right-wing slopes are nonpositive; replacing
the intervening slope h/a by zero preserves the required ordering.
All old left-wing heights are at most 1-h, so raising them by h
preserves the height bound. Let Uhat be this actual cap. Its charged
area satisfies the exact identity

    O(U)=O(Uhat)-a h/2.                                         (TS3)

The first-quarter supports f of U and Uhat are identical: the old
point (a/2,1) dominates every raised left-wing point for any upper
normal with nonnegative horizontal component. If ghat denotes Uhat's
companion support, the actual companion support of U is

    g_U(t)=max(ghat(t)-h cos t, cos t-(a/2)sin t).

Indeed the entire right wing is dominated by (a/2,1), while a linear
middle facet contributes only its endpoints. On J the wall associated
with the displayed high-point term has height

    1-sec t+(x-a/2)tan t<=0.

Consequently the distributive identity for min and max proves the
exact all-angle positive-niche formula

    n_U(x)=max(0,sup_t min(Rhat_t(x),Shat_t(x)-h)), x in J.       (TS4)

No assertion that raising the wing improves P is made or needed.

Define the lifted cap's actual 45-degree support parameters

    u=r H_Uhat(pi/4)-1, v=r H_Uhat(3pi/4)-1,
    M=(u+v)/2, d=(u-v+h)/2.

Since Uhat has height one on J,

    a/2<=u,v<=a.

It lies below A0=min(1,1+u-x,1+v+x), with exact charged area

    O0=a-[(a-u)^2+(a-v)^2]/2.

Write D=integral_(I\J)(A0-Ahat)>=0. Equation (TS4) gives the
actual 45-degree tent on J as

    n45(x)=[min(u-k-x,v-h-k+x)]_+.

#### 2. Exact 45-degree concavity, with a shifted critical point

Assume for contradiction P>=41/50. The two charged wings have roof
bounded above by 1-h and 1 respectively, so P<=a(1-h/2). Hence

    a>=41/50, h<=9/25<a/2.

Thus the apex d lies in J for every (u,v) in [a/2,a]^2. Direct
integration gives

    N45=integral_J n45
       =(M-h/2-k)_+^2
          -[(u-k-a/2)_+^2+(v-h-k-a/2)_+^2]/2.

Combining with (TS3),

    P<=F_h(a,u,v)-D,
    F_h=a-[(a-u)^2+(a-v)^2]/2-a h/2-(M-h/2-k)_+^2
          +[(u-k-a/2)_+^2+(v-h-k-a/2)_+^2]/2.                 (TS5)

For fixed a,h this is concave in (u,v) on the whole square. When
M-h/2>k, its Hessian has diagonal entries -3/2 plus the corresponding
clipping indicator and off-diagonal entries -1/2, always nonpositive.
When M-h/2<=k the clipping terms vanish because the apex is in J,
and the Hessian is -Id. First derivatives match at the boundaries.

The critical point

    u=v=(a+k+h/2)/2

is interior to the square, has positive apex height, and has no
clipping. These facts follow already from a>=41/50 and h<=9/25.
Therefore

    F_h<=B(a)-k h/2-h^2/8,
    B(a):=a-(a-k)^2/2<=B(1)=2k.                              (TS6)

As in the horizontal short-width argument, B(9/10)<41/50, so
a>9/10. Also, if h>=1/24, then (TS6) gives

    P<=(95/48)k-1/4608<26441/32256<41/50.

Consequently every hypothetical high-score cap satisfies

    a>9/10, h<1/24,
    D<=2k-41/50-k h/2-h^2/8<3/350.                          (TS7)

##### 2a. The precise stability bounds needed for the two tail payments

In fact the high-score hypothesis forces

    u-a/2<t0+h/4, v-a/2<t0+h/4,
    m:=M-h/4>16/25.                                        (TS8)

For the first bound, maximize the concave F_h on the additional
half-square u>=a/2+t0+h/4. Its constrained critical point is

    u=a/2+t0+h/4,
    v=a/2+(2k-t0)/3+h/4.

Both clipping terms vanish there. The v derivative is zero and the
u derivative is (2k-4t0)/3<0, giving the global concave KKT conditions.
The maximum is

    B(a)-k h/2-h^2/8-(2/3)(t0-k/2)^2
       <=(9550k-881)/3750<41/50.                            (TS9)

The last strict comparison follows from r<577/408, or k<169/408.
The other bound follows by the same constrained KKT calculation with
u,v exchanged; the absence of clipping makes the local formulas equal,
even though F_h is not globally symmetric. All displayed KKT points
lie in the square because a>9/10 and h<1/24.

These bounds imply both actual 45-degree clipping terms vanish:
t0+h/4<1/3<k. Also M-h/2>=a/2-h/2>9/20-1/48>k.
Put x=u-h/4,y=v-h/4, whose mean is m. Then direct expansion of
(TS5), in this nonclipped regime, gives

    F_h=a-(a-m)^2-(m-k)^2-((x-y)/2)^2-k h/2-h^2/8.           (TS10)

If m<=1/2, the identity a-(a-m)^2=m+1/4-(a-m-1/2)^2 bounds
this by 3/4. If 1/2<m<=16/25, the symmetric part in (TS10)
increases first with a<=1 and then with m<=16/25. Its upper value
is (2050k-337)/625<41/50, using k<29/70. This proves the final
assertion of (TS8).

#### 3. The ordinary exterior deficit pays for two complete cut triangles

Use the lifted cap's actual near-vertical deficits

    delta_L=c+s v-H_Uhat(5pi/8)>=0,
    delta_R=c+s u-H_Uhat(3pi/8)>=0.

The genuine height-one points at the J endpoints give

    delta_L<=s(v-a/2), delta_R<=s(u-a/2).

At (-v,1), a support cut by delta_L removes a triangle whose two
horizontal lengths are delta_L/s along the flat face and
delta_L/(c-s) along the outer 45-degree face. If the latter length
does not exceed a-v, the whole triangle is in the charged left wing
and has area

    delta_L^2/[2s(c-s)]=K delta_L^2.

This containment must hold. Otherwise cut only by
delta0=(c-s)(a-v)<delta_L. The resulting whole charged triangle
already gives

    D>=K delta0^2=(a-v)^2/r.

But (TS7)-(TS8) imply

    a-v>a/2-t0-h/4>13/100-1/96=287/2400>7/60,

so D>49/5400>3/350, a contradiction. The mirrored right cut
triangle obeys the same argument. They lie in opposite wings, hence

    D>=K(delta_L^2+delta_R^2).                              (TS11)

#### 4. Two actual extra niche tails, with the tilt retained

Set

    eta_L=eta-(1-k)h>0,
    E_L=(eta_L-delta_L/c)_+,
    E_R=(eta-delta_R/c)_+.

##### Left additional tail

The actual pi/8 tent contains the lower second wall

    1-1/c+k v-delta_L/c-h+kx

by (TS4). At the left 45-degree zero x0=k-v+h, its height is

    1-1/c+k^2-delta_L/c-(1-k)h.

If E_L>0, (TS2) shows this dominates the line

    D_L(x)=E_L+k(x-x0).

If E_L=0, the claimed extra-area bound below is nonpositive and
already follows from nonnegativity; no wall assertion is needed.

An attaining point for u satisfies x+y=1+u and y<=1, hence x>=u.
It lies on the unchanged right portion of Uhat, so the actual first
wall has the lower bound

    R_pi/8(x)>=1-1/s+(u-x)/k.

At x_R=x0+E_L/(1-k), this dominates D_L exactly when

    2M-h>=1/c+K E_L.                                        (TS12)

The condition holds: 2M-h=2m-h/2>32/25-h/2, while
E_L<=eta-(1-k)h and K(1-k)=r>1/2. Thus (TS2) makes the
right side strictly smaller. For x<=x_R the companion gap only
increases.

The end x_R lies before the 45-degree apex d, since

    x_R-d=k-m+h/4+E_L/(1-k)
          <=k-m+eta/(1-k)-3h/4<0.

Here k+eta/(1-k)=(26k+3)/25<16/25. Therefore the extra niche
area contains the usual triangle with peak E_L at x0, left slope k
and right downward slope 1-k. Its full area is Gamma E_L^2.

##### Right additional tail and its actual companion wall

In the reflected coordinate y=-x the right 45-degree zero is
y0=k-u. The pi/8-type near-vertical wall on this side is unchanged,
so its analogous peak lower bound is E_R. Apply this wall construction
only when E_R>0; if E_R=0 the nonnegative extra-area bound suffices,
exactly as for the left tail. A point attaining v for
Uhat can be chosen on the left wing. Its reflected abscissa is at
least v; lowering it by h gives an actual point of U. Hence

    H_U(7pi/8)>=s(1-h)+c v.

This supplies the genuine reflected companion-wall bound

    R_ref(y)>=1-h-1/s+(v-y)/k.

At y_R=y0+E_R/(1-k), it dominates the near-vertical tail exactly
when

    2M-kh>=1/c+K E_R.                                       (TS13)

Indeed 2M-kh=2m+(1/2-k)h>32/25, while E_R<=eta. Equation
(TS2) applies. Also y_R lies before the reflected apex -d:

    y_R+d=k-m+h/4+E_R/(1-k)<0,

because k+eta/(1-k)<99/175, h/4<1/96, and
99/175+1/96<16/25. This tail is therefore disjoint from the left
tail, being on the opposite side of d.

##### Window clipping of the two tails

Both 45-degree zeros are in J, by (TS8):

    x0+a/2>k-t0+3h/4>0,
    y0+a/2>k-t0-h/4>0.

Only the outer tips of the two extra triangles can leave J. Their
omitted horizontal lengths are bounded respectively by

    (v-h-a/2-k+E_L/k)_+<=L0+h/4,
    (u-a/2-k+E_R/k)_+<=L0+h/4.

The slope of each omitted triangle is k, so the sum of the omitted
areas is at most k(L0+h/4)^2. We conclude that the actual full
positive niche satisfies

    integral_J n>=N45+Gamma(E_L^2+E_R^2)-k(L0+h/4)^2.          (TS14)

The zero-peak cases are covered by the same lower bound. No overlap
or angular-connectivity assertion concerning other niche pieces is used.

#### 5. The final scalar upper bound strictly decreases with tilt

For every eta_i>=0 and delta>=0, Gamma=K c^2 gives

    K delta^2+Gamma(eta_i-delta/c)_+^2>=Gamma eta_i^2/2.

Apply this to eta_L and eta, using (TS11) and (TS14), then use
the sharp 45-degree maximum (TS6). It yields

    P<=H(h):=2k-kh/2-h^2/8
                -(Gamma/2)[(eta-(1-k)h)^2+eta^2]
                +k(L0+h/4)^2.

Its expansion is

    H(h)=H(0)+[(7/10)k-19/50]h
                   +[-1/8-Gamma(1-k)^2/2+k/16]h^2.          (TS15)

The linear coefficient is negative already from k<1/2, and the
quadratic coefficient is negative since k/16<1/8. Thus H(h)<=H(0)
for h>=0. The same exact simplification as in the horizontal proof is

    H(0)=2k-Gamma eta^2+k L0^2
         =(5140k-1617)/625<3587/4375<41/50,                  (TS16)

using k<29/70. This contradicts the assumed P>=41/50 and proves
(TS1).

The proof uses three genuine angles and ordinary exterior area only.
The lifting map is an explicit way of recording tilt, not a claim of
monotonicity for the original score. In particular it retains the
lower companion height on the right added tail and the moving 45-degree
zero on the left tail; both effects are included in (TS12)-(TS15).


### Part B. The exact positive width gap above two

#### Statement

The short tilted theorem TS1 remains true with

    0<a<=a_max:=1001/1000,

under exactly the same geometric hypotheses. Consequently every remaining
canonical tilted global maximizer has

    C=W/4>1001/2000,   4C-2>1/500.                              (GAP1)

The original proof already treats a<=1. It is enough to check 1<=a<=a_max.
Keep k,r,c,s,K,Gamma,eta=2/25 from that proof, and change only

    t0=323/1000,  L0=t0-k+eta/k=(483-920k)/1000.

The computations below list every changed numerical premise. All geometric
and actual-niche arguments of TS3-TS16 are unchanged with these constants.

#### 1. High-score stability in the extra interval

Suppose P>=41/50 and 1<=a<=1001/1000. The immediate outer-area bound
P<=a(1-h/2) gives

    h<=362/1001<a/2.

Thus the global concavity of the 45-degree relaxation still applies.
The same interior critical point has positive apex and no clipping, and

    F_h<=B(a)-kh/2-h^2/8,
    B(a)<=B(a_max)=(2001/1000)k-1/2000000.                    (GAP2)

The right side decreases with h. At h=1/23 it is, using k<29/70,

    <=6071014497/7406000000<41/50.

Therefore h<1/23. Also

    D<=B(a_max)-41/50
       <125793/14000000<9/1000.                              (GAP3)

The two shifted constrained KKT points are exactly those in TS9, with
t0=323/1000. Their largest possible value is

    B(a_max)-(2/3)(t0-k/2)^2
       =(7649/3000)k-1417319/6000000<41/50,                  (GAP4)

using k<169/408. All the points lie inside [a/2,a]^2 and have no
clipping: t0+h/4<17/50<k, and the other coordinate is smaller.
Thus a hypothetical high score forces

    u-a/2<t0+h/4,  v-a/2<t0+h/4.                             (GAP5)

Now the 45-degree tent is unclipped, with positive apex, and the shear
identity TS10 holds. Its symmetric part

    a-(a-m)^2-(m-k)^2

increases with m for m<=16/25 and a>=1. Set m=16/25 first; the resulting
expression increases with a<=a_max. Its maximum is

    a_max-(a_max-16/25)^2-(16/25-k)^2
       =(82/25)k-538921/1000000
       <5739553/7000000<41/50.                              (GAP6)

The strict rational bound uses k<29/70 and k^2=1-2k. Hence
m>16/25, as required by both genuine companion-wall checks.

#### 2. Every triangle still fits

For the exterior cut triangles, (GAP5) gives

    a-v>a/2-t0-h/4>=1/2-323/1000-1/92>23/200,

and the same holds for a-u. A cut that reaches the vertical endpoint
would therefore force

    D>(23/200)^2/r>3703/400000>9/1000,

using r<10/7. This contradicts (GAP3). Therefore TS11's full two-cut
payment D>=K(delta_L^2+delta_R^2) still holds.

The left effective tail height eta_L=eta-(1-k)h remains positive,
since h<1/23<eta. The two actual companion inequalities TS12-TS13
are unchanged because m>16/25 and eta is unchanged. The right-tail
apex check uses

    k+eta/(1-k)<99/175,  h/4<1/92,
    99/175+1/92<16/25.

Both tail peaks remain inside J because

    k-t0-h/4>2/5-323/1000-1/92>0.

The two clipping lengths are again at most L0+h/4. Thus TS14 holds
with the updated L0.

#### 3. The final scalar payment

With the new upper-width value B(a_max), the argument in TS15 yields

    P<=B(a_max)-kh/2-h^2/8
          -(Gamma/2)[(eta-(1-k)h)^2+eta^2]
          +k(L0+h/4)^2.

Its linear coefficient in h is

    (1403/2000)k-19/50<0,

and its quadratic coefficient is unchanged and negative. The maximum is
therefore at h=0. Exact use of k^2=1-2k gives

    P<=B(a_max)-Gamma eta^2+kL0^2
       =(8238929/1000000)k-5185441/2000000
       <334549037/408000000<41/50,                            (GAP7)

using k<169/408, a consequence of 577^2-2*408^2=1. The final strict
rational gap is

    41/50-334549037/408000000=10963/408000000>0.

This contradicts the high-score hypothesis, extending the global short
tilted theorem and proving GAP1. No endpoint-pressure or curvature premise
has been introduced.


### Part C. Wide widths with the actual endpoint law

#### Statement and notation

Let U be a downward convex cap of height one, with projection
I=[-a,a], 8/5<=a<3, and upper roof A affine on J=[-a/2,a/2].
After reflection suppose

    A(-a/2)=1-h,   A(a/2)=1,   0<=h<1/2.

Let n be its full continuous-angle positive niche roof, and put
e_R=A(a), e_L=A(-a), n_+=n(a/2), n_-=n(-a/2). Assume the actual
positive-pressure endpoint laws

    e_R=1/2+h/4+(3n_+-n_-)/4,
    e_L=1/2-3h/4+(3n_--n_+)/4.                    (TW1)

Then

    P(U)=integral_(I\J) A - integral_J n <41/50.   (TW2)

More precisely, a hypothetical P(U)>=41/50 is forced below
261719/320000<41/50. For canonical global maximizers the premises
come from height/width compactness, the middle-affine reduction,
top localization, low-height exclusion, and positive EP. The theorem
therefore excludes the whole remaining canonical width range
C=W/4=a/2>=4/5, including tilted caps.

Write H_U(theta) for upper support, and use the constants

    r=sqrt(2), k=r-1, c=cos(pi/8), s=sin(pi/8).

We use

    s/c=k, k+1/k=2r, 1+k=r, k^2=1-2k,
    1/s+1/c=4c, 1/s-1/c=4s, 1/(rc)=2s,
    1/(2sc)=r,   2/5<k<29/70,   s>3/8.

#### 1. The tilted 45-degree majorant

Set

    z=h/a,  L(x)=1-h/2+zx,
    u=r H_U(pi/4)-1,  v=r H_U(3pi/4)-1,
    m=(u+v)/2, d=(u-v)/2, w_R=a-u, w_L=a-v.

Concavity gives A<=L on all I, and the unit-height condition gives
A<=1. The actual J endpoint points and these two global upper
bounds imply

    a/2<=u<=a,  a/2-h<=v<=a-3h/2,
    u>=a+e_R-1, v>=a+e_L-1.                       (TW3)

For the bound on v, the function -x+min(1,L(x)) decreases on I
because z<1. Define

    q=(v+h/2)/(1-h/a),   a/2<=q<=a.

The line 1+v+x meets L at x=-q. The cap is below

    Abar(x)=min(1,L(x),1+u-x,1+v+x).

Its exact charged exterior area is

    Obar=a-(5/8)ah
           -1/2[(a-u)^2+(a-v-3h/2)^2/(1-h/a)].    (TW4)

Indeed, the right charged wing is the unit rectangle minus the
usual 45-degree triangle. The integral of L on the left charged
wing is a/2-5ah/8; the left triangle removed from it has height
a-v-3h/2 and base (a-v-3h/2)/(1-h/a).

The endpoint laws imply

    E:=e_R+e_L=1-h/2+(n_++n_-)/2>=1-h/2.

Since e_R<=1-w_R and e_L<=1-w_L, we obtain

    w_R>=0, w_L>=3h/2, w_R+w_L<=1+h/2,
    m>=a-1/2-h/4.                                 (TW5)

The 45-degree niche is the actual tent

    n45(x)=[min(u-k-x,v-k+x)]_+.

Its apex d lies in J: u-v<=1<=a follows from v>=a-1 and u<=a;
v-u<=a/2-3h/2<=a follows from (TW3). Also m>=a-5/8>=39/40>k.
Thus, writing b0=a/2-k,

    N45:=integral_J n45
      =(m-k)^2-1/2[(b0-w_R)_+^2+(b0-w_L)_+^2].     (TW6)

#### 2. A perspective tangent pays both 45-degree clipping terms

For any t>=b0 with 3/2-t/a>=0, one has

    w^2-(b0-w)_+^2 >=2tw-t^2,

    (w-3h/2)^2/(1-h/a)-(b0-w)_+^2
        >=2tw-t^2+(-3t+t^2/a)h.                   (TW7)

For the second inequality use the exact identity

    (w-3h/2)^2/(1-h/a)
       =2tw-t^2+(-3t+t^2/a)h
          +[w-t-h(3/2-t/a)]^2/(1-h/a).

If w<b0<=t, the last nonnegative square is at least (b0-w)^2:
its numerator has absolute value at least t-w, and 1-h/a<=1.
If w>=b0 the clipping term is zero. The first inequality is the
same argument with h=0. In particular this handles clipping
without a symmetry assumption on u and v.

Let F=Obar-N45. Equations (TW4)-(TW7) give

    F<=a-2t(a-m)+t^2-(m-k)^2
           -[(5/8)a-(3/2)t+t^2/(2a)]h.             (TW8)

When a<=1+2k choose t=1/2. Then

    F<=m+1/4-(m-k)^2-D(a)h,
    D(a)=(5/8)a-3/4+1/(8a)>=21/64,                (TW9)

where D is increasing for a>=8/5.

##### 2a. Preliminary consequences of a hypothetical P>=41/50

All other niche portions and the deficit Abar-A have nonnegative
area, so P<=F. We now prove that a high-scoring cap must satisfy

    a<9/5,    h<1/4,    a+h<37/20.                (TW10)

First suppose 9/5<=a<=1+2k. The right side of (TW9) decreases
with m throughout m>=a-1/2-h/4, since m>k+1/2. Substitute this
lower bound for m. The resulting derivative with respect to h is

    -a/8+1/4-k/2-1/(8a)-h/8<0.

At h=0 its value is a-1/4-(a-1/2-k)^2, which decreases for a>=9/5.
Consequently

    P<=(23/5)k-57/50<134/175<41/50.               (TW11)

If instead 1+2k<=a<3, choose t=b0 in (TW8). This gives

    F<=a-(3/4)a^2+ak+am-m^2-[k+k^2/(2a)]h.

It decreases with m>=a-1/2-h/4 because a-2m<0 there. After that
substitution the upper bound becomes

    (3/2)a-(3/4)a^2+ak-1/4
      +[(a-1)/4-k-k^2/(2a)]h-h^2/16.

The h=0 part decreases for a>=1+2k, taking value 3k-1/2 at that
left endpoint. Since a<3 and h<1/2, the remaining part is at most
(1/2-k)/2. Therefore

    P<=(5/2)k-1/4<11/14<41/50.                    (TW12)

This proves a<9/5. We may use (TW9) and D>=21/64. Because its
right side decreases with m>=11/10-h/4, it gives

    P<=27/20-h/4-(11/10-h/4-k)^2-(21/64)h.

This expression has derivative -9/320-k/2-h/8<0. If h>=1/4,

    P<=(163/40)k-2787/3200
        <18307/22400<41/50.                       (TW13)

Finally, if a+h>=37/20 and h<1/4, (TW5) implies
m>=27/20-5h/4>=83/80>k+1/2. Hence (TW9) gives

    P<=8/5-(101/64)h-(27/20-k-5h/4)^2
      <=8/5-(101/80)(27/20-k)+10201/25600
      =7529/25600+(101/80)k
      <146431/179200<41/50.                       (TW14)

The middle inequality completes the square and is valid for all
real h. This proves (TW10). All rational comparisons in (TW11)-
(TW14) use only k<29/70.

For the rest of the proof assume P>=41/50 and thus (TW10).

#### 3. Near-vertical support deficits have ordinary exterior payment

The right supporting direction 3pi/8 touches Abar at (u,1).
The left direction 5pi/8 touches Abar at (-q,L(-q)); here
z< (1/4)/(8/5)=5/32<k. Set

    Hbar_L=c(1-h/2)+(s-cz)q,
    delta_L=Hbar_L-H_U(5pi/8),
    delta_R=c+s u-H_U(3pi/8).

They are nonnegative. The actual J endpoint points yield

    delta_R<=s(u-a/2),
    delta_L<=(s-cz)(q-a/2).                        (TW15)

On the left affine segment x=-q+t, the new support line lies
below Abar by delta_L/c-(k-z)t. Equation (TW15) fits the entire
cut triangle in the charged interval [-q,-a/2]. Its area is

    delta_L^2/[2c^2(k-z)]>=r delta_L^2.

The right flat-piece triangle analogously has area r delta_R^2.
The two lie in opposite charged wings, so

    D:=integral_(I\J)(Abar-A)
          >=r(delta_L^2+delta_R^2).                (TW16)

For comparison with the horizontal formulas, define the exact
extra left support deficit

    tau=(c+s v-Hbar_L)/c
       =(1-k)h(1/2+q/a),
    0<=tau<=(3/2)(1-k)h.                          (TW17)

#### 4. Two genuine niche half-triangles, truncated at baseline zeros

At the actual angle pi/8 the second wall is b_R+kx, with

    b_R=1-1/c+k v-delta_L/c-tau.

The actual endpoint (a,e_R) gives the companion-wall lower bound
B_R-x/k, where

    B_R=e_R+a/k-1/s.

Thus the full niche contains the positive part of
min(b_R+kx,B_R-x/k). Against the right branch u-k-x of n45, set

    x_L^R=(u-k-b_R)/r,
    x_*^R=(B_R-b_R)/(2r),
    Z_R=(B_R+b_R)/2-u+k=r(x_*^R-x_L^R).

Reflection, using the actual angle 3pi/8, gives the left-side
quantities in the coordinate y=-x:

    b_L=1-1/c+k u-delta_R/c,  B_L=e_L+a/k-1/s,
    x_L^L=(v-k-b_L)/r,
    x_*^L=(B_L-b_L)/(2r),
    Z_L=(B_L+b_L)/2-v+k=r(x_*^L-x_L^L).

The right and reflected-left 45-degree apices are d and -d.
Their crossover offsets are

    x_L^R-d=km+2s-1+(delta_L/c+tau)/r>0,
    x_L^L+d=km+2s-1+delta_R/(rc)>0.                (TW18)

Use m>=a-1/2-h/4>83/80, k>2/5, s>3/8 for the signs.

The actual low J point gives b_R>=1-h-1/c+k a/2. Consequently
x_*^R<=a/2 follows from

    e_R+h+alpha a<=1+4s,  alpha=(3-r)/2.

Indeed e_R<=1, and (TW10) gives

    h+alpha a<alpha*(37/20)+(1-alpha)/4
             =53/20-4r/5<4s.                     (TW19)

For the last comparison, both sides are positive and
16s^2-(53/20-4r/5)^2=(-121+96r)/400>0.
On the other side the actual high J point gives
b_L>=1-1/c+k a/2; thus x_*^L<=a/2 follows from
e_L+alpha a<=1+4s. This holds from e_L<=1,
alpha a<(4/5)(9/5)=36/25<3/2<4s.

The tentative half-triangle might extend past the zero of its
45-degree baseline. Retain only the part before that zero. Put

    F_R=r(u-k-x_L^R),   F_L=r(v-k-x_L^L),
    Zhat_R=min(Z_R,F_R), Zhat_L=min(Z_L,F_L).

If Zhat_R>0, integrate the linear gain r(x-x_L^R) from x_L^R
to min(x_*^R,u-k). Equations (TW18)-(TW19) place the interval in J,
to the right of d, and where the 45-degree baseline is positive.
The actual two-wall tent has the requisite ascending wall there.
This gives genuine niche gain Zhat_R^2/(2r). If Zhat_R<=0, the
zero lower bound requires no interval assertion. Reflection gives
the same statement on the left, disjoint from the right interval.
Therefore

    integral_J n >=N45+[(Zhat_R)_+^2+(Zhat_L)_+^2]/(2r). (TW20)

##### 4a. Bound the loss caused by the baseline truncation

Let ell_R=(Z_R-F_R)_+, ell_L=(Z_L-F_L)_+, so that
Zhat_R=Z_R-ell_R and Zhat_L=Z_L-ell_L exactly.
The actual J support bounds used in (TW19) also imply

    2ell_R <=[e_R+2r w_R+h-(3k/2)a-1-4s+2rk]_+,
    2ell_L <=[e_L+2r w_L  -(3k/2)a-1-4s+2rk]_+.   (TW21)

For example, 2(Z_R-F_R)=B_R-b_R-2r(u-k), and substitute
b_R>=1-h-1/c+k a/2. The coefficient of a is
1/k-k/2-2r=-3k/2. The left formula is its reflection, without h.

The unit-height box yields

    0<=n(+-C)<=1-sqrt(1-C^2),  C=a/2<9/10.

For completeness, at x=C the first wall is bounded by
1+(C cos(t)-1)/sin(t); its supremum is 1-sqrt(1-C^2),
and the other endpoint follows by reflection. This is below 2/3.
Together with (TW1), it gives

    e_R>=1/3+h/4, e_L>=1/3-3h/4,
    w_R<=2/3-h/4, w_L<=2/3+3h/4.                 (TW22)

The horizontal fitting constant is strictly negative:

    K:=(2r-1)*2/3-(12/5)k-4s+2rk<0.              (TW23)

An entirely rational verification uses r<10/7 and k<3/7 to bound
(2r-1)*2/3<26/21, whereas (12/5)k+4s-2rk>
3/2-48/245=639/490>26/21. Here 12/5-2r<0 and s>3/8.

Now use e_Q<=1-w_Q, a>=8/5, and (TW22) in (TW21). It follows that

    ell_R<=(5-2r)h/8,
    ell_L<=3(2r-1)h/8,
    ell_R+ell_L<=(1+2r)h/4<=h.                   (TW24)

The inequalities include h=0. No assumption on the sign of the
untruncated peak is made.

#### 5. Combine exterior area and additional niche area

Write Z_R=Z_R^0-delta_L/(2c)-tau/2 and
Z_L=Z_L^0-delta_R/(2c). Direct addition gives

    Z_R^0+Z_L^0
       =E/2+a/k+(k-2)m+1-1/s-1/c+2k.

Use E>=1-h/2, (TW17), and

    1/k>12/5, k-2>-8/5, 3/2+2k-4c>-11/8.

The last inequality follows by squaring 4c<7/8+2r, since the
difference of the squared sides is 49/64-r/2>0. Thus, with

    S(a,m)=(12/5)a-(8/5)m-11/8,

we have

    Z_R+Z_L >= S(a,m)-(7/10)h-(delta_L+delta_R)/(2c).

The coefficient of h before the weakening to 7/10 is
1/4+3(1-k)/4=1-3k/4<7/10. By (TW24),

    Zhat_R+Zhat_L
       >=Q(a,m,h)-(delta_L+delta_R)/(2c),
    Q(a,m,h):=S(a,m)-(17/10)h.                    (TW25)

Set D0=r(delta_L^2+delta_R^2) and
G0=[(Zhat_R)_+^2+(Zhat_L)_+^2]/(2r). Cauchy-Schwarz yields

    Q_+<=sqrt(4r G0)+sqrt(r D0/(4c^2)),
    (Q_+)^2<=[4r+r/(4c^2)](D0+G0)<=8(D0+G0).

The last coefficient is strictly below 8, using r<3/2 and c^2>3/4;
the weak product inequality covers D0+G0=0. Equations (TW16),
(TW20), and (TW9) therefore imply

    P<=Gtilde(a,m,h)
       :=m+1/4-(m-k)^2-(21/64)h-[Q(a,m,h)_+]^2/8. (TW26)

#### 6. One supporting plane closes the wide tilted range

The function Gtilde is jointly concave in (a,m,h), since it is a
linear function minus a square in m and the convex positive square
of an affine function. At

    (a0,m0,h0)=(8/5,11/10,0), Q=141/200>0,

its exact gradient is

    G_a=-423/1000,
    G_m=2k-459/500<0,
    G_h=-57/2000.

The feasible displacement furnished by (TW5) decomposes as

    (a-a0,m-m0,h)
       =(a-a0)(1,1,0)
          +(m-a+1/2+h/4)(0,1,0)
          +h(0,-1/4,1).

Each coefficient is nonnegative. The three directional derivatives
at the base point are strictly negative; for the tilt direction,

    G_h-G_m/4=201/1000-k/2<0,

using k>41/100 (equivalently sqrt(2)>141/100). Hence the supporting
plane of the concave Gtilde gives

    P<=Gtilde(a,m,h)<=Gtilde(a0,m0,0)
      =(21/5)k-295081/320000
      <261719/320000<41/50.                        (TW27)

This contradicts the high-score hypothesis and proves (TW2).

Every niche payment above is an ordinary region in one of the
three actual two-wall tents at pi/8, pi/4, 3pi/8. In particular,
the proof retains the possible high-side top overhang, includes
the full niche through its lower-bound direction, and does not
apply endpoint stationarity to an artificial finite-angle cap.

### Part D. Exact intermediate-width and tilt restriction

#### Statement

Let U be a downward convex cap of height one with projection I=[-a,a],
1<=a<=8/5, and affine middle roof on J=[-a/2,a/2], with

    A(-a/2)=1-h, A(a/2)=1, 0<=h<1/2.

Then, for the full continuous-angle positive niche,

    P(U)<=B_*(a,h)
       :=a-(5/8)ah-2(a-3h/4-k)^2/(4-h/a)
        =1-(a-r)^2/2-[2a/(4a-h)](k+h/2)^2,                  (INT1)

where r=sqrt(2), k=r-1. No endpoint law or curvature assumption is used.

In particular any such cap with P>=41/50 satisfies

    (a-r)^2+[4a/(4a-h)](k+h/2)^2<=9/25,                     (INT2)
    h<17/50.                                                (INT3)

Combined with the already audited short positive-gap and wide theorems,
every remaining canonical global maximizer has

    1001/1000<a<8/5, 0<h<17/50,

and obeys the exact coupled inequality INT2.

#### 1. The lifted cap and its mandatory extra exterior deficit

Use the exact lifted cap Uhat of the short tilted proof: raise the entire
left wing by h, make the middle roof height one, and retain the right wing.
It is a genuine downward convex cap of height one. Its first-quarter
supports agree with those of U, while on J the exact positive niche of U
is the all-angle maximum of

    min(Rhat_t(x),Shat_t(x)-h).

Let u,v be Uhat's 45-degree supports minus one in the normalization

    u=r H_Uhat(pi/4)-1, v=r H_Uhat(3pi/4)-1,
    M=(u+v)/2.

Then a/2<=u,v<=a. Concavity of the original tilted roof also imposes

    v<=a-h/2.                                                (INT4)

Indeed the original support parameter in the second 45-degree direction
is v-h; the global affine extension L(x)=1-h/2+(h/a)x bounds it above by
a-3h/2. Equivalently this follows directly by maximizing -x+Ahat(x)
under Ahat(x)<=1+h/2+(h/a)x on the left wing.

Put z=h/a. The lifted cap lies below the ordinary horizontal 45-degree
majorant

    A0=min(1,1+u-x,1+v+x).

But on the left wing it also lies below

    Lhat(x)=1+h/2+zx.

The lines Lhat and 1+v+x meet at x=-q, where

    q=(v-h/2)/(1-z),  a/2<=v<=q<=a.

The exact area by which this affine constraint cuts A0 on the charged
left wing is

    D_tilt=h(v-a/2)^2/[2(a-h)].                              (INT5)

To check it, on [-v,-a/2] the depth under the flat roof grows linearly
from zero to z(v-a/2), giving area z(v-a/2)^2/2. On [-q,-v] the
remaining triangle has base z(v-a/2)/(1-z) and the same depth, giving
z^2(v-a/2)^2/[2(1-z)]. Their sum is INT5. Both triangles are wholly
charged by INT4.

Consequently the true exterior area of U is at most

    a-[(a-u)^2+(a-v)^2]/2-ah/2-D_tilt.                       (INT6)

All additional exterior deficit is nonnegative.

#### 2. A globally concave two-support relaxation, including clipping

Since h<a/2, the apex (u-v+h)/2 of the actual 45-degree tent lies in J
for every pair (u,v) in the square [a/2,a]^2. Hence its exact J-area is

    N45=(M-h/2-k)_+^2
        -[(u-k-a/2)_+^2+(v-h-k-a/2)_+^2]/2.                 (INT7)

Let F_h be the right side of INT6 minus N45 with D_tilt omitted. For
fixed a,h it is concave on that entire square, by exactly the TS5
piecewise-Hessian argument: diagonal entries -3/2 plus a clipping
indicator, off-diagonal -1/2 in the positive-apex region, and -Id
otherwise. The first derivatives match at all clipping boundaries.

Therefore

    Q_h(u,v):=F_h(a,u,v)-h(v-a/2)^2/[2(a-h)]

is also concave on the entire square. Its formula is a valid upper bound
on P for every actual cap satisfying INT4. We may maximize it on the
larger full square, even though the affine-area interpretation INT5 is
needed only on the actual cap's feasible subset.

#### 3. The actual global critical point is unclipped

Put

    A_*=a-3h/4-k>0,
    D=2A_* /(4-h/a),
    u_*=a-D, v_*=a-h/2-(1-h/a)D.                            (INT8)

These are the stationary supports in the regime without clipping.
One can check this directly in the proper tilted variables:
w_R=a-u, w_L=a-v-h/2, so the proper exterior/niche expression is

    a-(5/8)ah
      -(w_R^2+w_L^2/(1-h/a))/2
      -[a-3h/4-(w_R+w_L)/2-k]^2.

Its stationary equations give w_R=D,w_L=(1-h/a)D.

Since D>0 and D<a/2, both u_*,v_* lie strictly inside [a/2,a], and
v_*<=a-h/2. The inequality D<a/2 follows at once from

    4(a-3h/4-k)<a(4-h/a).

Their apex height is D>0. The right clipping term vanishes because

    D-(a/2-k)=[2k-h(1+k/a)]/(4-h/a)>0.                       (INT9)

Indeed a>=1 and h<1/2 give
h(1+k/a)<(1+k)/2=r/2<2k, the last inequality being r>4/3.
For the left clipping term,

    v_*-h-k-a/2
      =(u_*-k-a/2)-3h/2+(h/a)D
      <=u_*-k-a/2-h<0.

Thus Q_h is differentiable and stationary at this interior point.
Concavity proves it is a global maximum of Q_h on the square,
including all configurations whose 45-degree tent is window-clipped.
Its value is the first expression in INT1.

For the second expression set b=a-h/4 and q0=k+h/2, expand the first,
and use r=1+k and k^2=1-2k. Equivalently,

    B_*=1-(a-r)^2/2-q0^2/2-h q0^2/[8(a-h/4)].

This proves INT1 and INT2.

#### 4. A simple global rational tilt exclusion

For fixed a, the expression in INT1 strictly decreases with h, because
q0 increases and 4a-h decreases. For fixed positive h, the coefficient
2a/(4a-h) decreases as a increases. Dropping the nonpositive width square
therefore gives, uniformly for a<=8/5,

    B_*(a,h)<=1-[(16/5)/(32/5-h)](k+h/2)^2.                  (INT10)

If h>=17/50, the right side is bounded above by its value at h=17/50.
The rational lower bound k>41/99 follows from 140^2<2*99^2. Substituting
it gives

    P<1-[(16/5)/(32/5-17/50)](41/99+17/100)^2
      =304326697/371212875<41/50,

where the last rational gap is

    41/50-304326697/371212875=135721/742425750>0.

This proves INT3.

The estimate is global on the displayed geometric domain. It is a
finite-angle upper bound on the original spatial score, with the
mandatory tilt cut included as ordinary exterior area. It does not assume
a finite-angle optimizer satisfies EP, does not claim unit curvature, and
is joined with the subsequent tilted source analysis in the integrated full-turn chapter.

---

<a id="proof-full-triangle"></a>
## Technical proof 20. The full three-triangle tilted width cut (FT)

Written proof, independently checked within the research session, October 10, 2026. This improves the
[preceding canonical cutoff](#proof-tilted-width) C<4/5 to C<37/50. It uses actual
two-wall niche regions at pi/8, pi/4, and 3pi/8. The new ingredient is a
complete additional triangle together with an exact loss bound for the
positive floor. The final relaxation includes all 45-degree window
clipping, and a supporting plane controls its entire width range.

### Statement and standing notation

Let U be a downward convex cap of height one, with projection I=[-a,a]
and middle window J=[-a/2,a/2]. Its roof is affine on J and satisfies

    A(-a/2)=1-h, A(a/2)=1,
    37/25<=a<=8/5, 0<=h<=17/50.                         (FT1)

Write e_R=A(a), e_L=A(-a), n_+=n(a/2), n_-=n(-a/2), where n is the
full continuous-angle positive niche. Assume the actual endpoint laws

    e_R=1/2+h/4+(3n_+-n_-)/4,
    e_L=1/2-3h/4+(3n_--n_+)/4.                         (FT2)

Then

    P(U)<25811237/31500000<41/50.                       (FT3)

Consequently, combining this theorem with the already audited short,
wide, and intermediate-width bounds, every remaining canonical global
maximizer has

    1001/2000<C=W/4<37/50, 0<h<17/50.

Use the constants

    r=sqrt(2), k=r-1, c=cos(pi/8), s=sin(pi/8),
    A=1-k, b=2-k, d=3r-1,
    gamma=1-r/2, t=2c-r, d0=3/5-t.

Relevant exact identities are

    s/c=k, k+1/k=2r, 1+k=r, k^2=1-2k,
    1/s+1/c=4c, 1/(rc)=2s, 1/(rs)=2c,
    r/(4c^2)=k, 2d+b^2=9.

The letter A without an argument denotes the constant 1-k only in
scalar formulas; A(x) always denotes the cap roof.

### 1. Lift the low wing and retain a genuine 45-degree niche

Raise the left charged wing by h, put the middle roof at height one,
and retain the right wing. This gives the genuine concave roof Ahat of
a height-one cap Uhat. Concavity follows because the left wing has
slopes at least h/a, the inserted middle has slope zero, and the right
wing has nonpositive slopes since its initial endpoint already has
the global maximum height one. In particular

    O(U)=O(Uhat)-ah/2.                                  (FT4)

Set

    u=r H_Uhat(pi/4)-1, v=r H_Uhat(3pi/4)-1,
    M=(u+v)/2, C=a/2.

The actual middle endpoint points and the height bound give

    C<=u,v<=a.

The original first-quadrant support equals the lifted one: the point
(C,1) dominates every lifted point to its left in each such direction.
In the second 45-degree direction, the point (-C,1-h) beats (C,1)
by (a-h)/r>0. Hence the actual original parameter is exactly v-h.
Its 45-degree niche is therefore

    n45(x)=[min(u-k-x,v-h-k+x)]_+.

The apex x_d=(u-v+h)/2 lies in J, because |u-v|<=a/2 and h<=a/2.
Consequently its exact area, including both possible window clips, is

    N45=(M-h/2-k)^2
         -[(u-k-a/2)_+^2+(v-h-k-a/2)_+^2]/2.             (FT5)

The apex height is positive throughout the enlarged square: it is at
least 37/50-17/100-k>0.

The lifted cap lies under

    A0(x)=min(1,1+u-x,1+v+x).

Let D be the charged exterior area between A0 and Ahat. Then D>=0,
and the exact exterior area of A0 together with (FT4) gives

    P(U)<=F_h(a,u,v)-D-[integral_J n-N45],                (FT6)

where

    F_h=a-[(a-u)^2+(a-v)^2]/2-ah/2
         -(M-h/2-k)^2
         +[(u-k-a/2)_+^2+(v-h-k-a/2)_+^2]/2.             (FT7)

No mandatory tilt deficit is subtracted from F_h; ignoring that extra
nonnegative area is allowed.

### 2. Endpoint controls and two near-vertical support deficits

The unit-height box yields

    n(+-C)<=1-sqrt(1-C^2)<=2/5,

since C<=4/5. For example at x=C the first wall is at most
1+(C cos(theta)-1)/sin(theta), whose supremum over theta is
1-sqrt(1-C^2); the opposite endpoint follows by reflection. Combining
this with (FT2) gives

    e_R>=2/5+h/4, e_L>=2/5-3h/4,
    E:=e_R+e_L>=1-h/2.                                  (FT8)

Put w_R=a-u and w_L=a-v+h, the actual original 45-degree endpoint
deficits. Support containment at the endpoints gives

    e_R<=1-w_R, e_L<=1-w_L,
    w_R<=3/5-h/4, w_L<=3/5+3h/4,
    M-h/2>=a-1/2-h/4.                                  (FT9)

Define the nonnegative lifted support deficits

    delta_L=c+s v-H_Uhat(5pi/8),
    delta_R=c+s u-H_Uhat(3pi/8).

The actual lifted middle endpoints imply

    delta_L<=s(v-C), delta_R<=s(u-C).

On the flat part [-v,-C] the left support line cuts a triangle of
depth delta_L/c and slope k. It fits completely before -C and has
area delta_L^2/(2c^2 k)=r delta_L^2. The right flat part [C,u]
provides the analogous disjoint triangle. Thus

    D>=D0:=r(delta_L^2+delta_R^2).                       (FT10)

Only the flat portions are used, so there is no need to fit any
additional exterior triangle at either endpoint.

### 3. Full additional niche triangles fit the middle window

At angle pi/8 the actual niche dominates the positive part of

    f_R(x)=min(b_R+kx,B_R-x/k),
    b_R=1-1/c+k v-h-delta_L/c,
    B_R=e_R+a/k-1/s.

The first displayed wall follows from
H_U(5pi/8)>=H_Uhat(5pi/8)-ch. Indeed A(x)>=Ahat(x)-h on I,
so every translated upper point is dominated vertically by a point of U;
the support normal has positive vertical component. This argument also
covers a translated upper point falling below the floor. The companion
wall follows from the actual endpoint
(a,e_R). Equality of the actual support with either lower bound is
not assumed.

Against the right branch u-k-x of n45 set

    x_L=(u-k-b_R)/r,
    x_*=(B_R-b_R)/(2r),
    x_R=(B_R-u+k)/r,
    Z_R=(B_R+b_R)/2-u+k.

When Z_R>0, the signed gain f_R-(u-k-x) is a full triangle on
[x_L,x_R], with slopes r and -r and height Z_R. Its area is Z_R^2/r.
Its endpoints are x_*+-Z_R/r.

Reflection, in y=-x, gives the analogous left construction

    f_L(y)=min(b_L+ky,B_L-y/k),
    b_L=1-1/c+k u-delta_R/c,
    B_L=e_L+a/k-1/s,
    x_L^L=(v-h-k-b_L)/r,
    x_R^L=(B_L-v+h+k)/r,
    Z_L=(B_L+b_L)/2-v+h+k.

The right and reflected-left crossovers lie strictly beyond their
respective 45-degree apices:

    x_L-x_d=k(M+h/2)+2s-1+delta_L/(rc)>0,
    x_L^L+x_d=k(M-h/2)+2s-1+delta_R/(rc)>0.              (FT11)

Indeed M-h/2>=37/25-1/2-17/200=179/200, while k>2/5 and
2s>3/4. This also places the two gain regions on opposite sides
of the apex.

The outer zero of either signed triangle lies inside the window.
For the right one, using e_R<=1-w_R gives

    x_R<=1+a-2c,
    x_R-C<=1+C-2c<0.                                  (FT12)

Here C<=4/5 and c>9/10. The same calculation with w_L proves
x_R^L<C. Whenever Z_Q>0, its left endpoint is below its right
endpoint; (FT11)-(FT12) therefore fit the entire triangle in J.
There is no interval claim when Z_Q<=0, for which the zero gain
bound suffices.

### 4. An exact positive-floor loss

The preceding triangle describes signed gain above a linear baseline.
We now account for its possible continuation past the zero of that
baseline. Let

    z0=u-k, Delta_R=(x_R-z0)_+,
    Delta_L=(x_R^L-(v-h-k))_+.

The genuine positive niche gains obey

    integral_J n >=N45+(Z_R)_+^2/r+(Z_L)_+^2/r
                       -gamma(Delta_R^2+Delta_L^2).     (FT13)

Here is a one-dimensional proof of the required floor inequality.
Write Z>0 for one signed peak and q=x_R-x for the reversed coordinate
on its support. Then 0<=q<=2Z/r=rZ, the baseline is q-Delta, and
the signed triangular gain has height r q up to q=Z/r and height
2Z-rq afterwards. If Delta<=0, the baseline is everywhere
nonnegative and there is no loss.

If 0<Delta<=rZ, its zero lies in the triangle interval. The tent's
right zero has q=k Delta. Before that zero, the lost area is
integral_0^(k Delta) r q dq; between it and the baseline zero, the
lost area is integral_(k Delta)^Delta (Delta-q) dq. These sum to

    [r k^2+(1-k)^2]Delta^2/2=gamma Delta^2.

The tent remains positive throughout the latter interval, including
when that interval crosses its apex; its values at the apex and the
baseline zero are positive.

If Delta>rZ, the baseline is negative throughout the interval. The
remaining positive tent has area

    r[(1+1/r)Z-Delta]_+^2.

When the bracket is nonnegative, subtracting Z^2/r-gamma Delta^2
from this expression gives exactly

    (1+r/2)(Delta-rZ)^2>=0.

When the bracket is negative, Z^2/r-gamma Delta^2 is already
nonpositive, since
gamma(1+1/r)^2-1/r=gamma/2>0. This proves the same inequality
in every case. If Z<=0 its right-hand side is nonpositive and no
positive interval is needed. Applying the lemma on the two disjoint
regions in (FT11) proves (FT13).

The loss admits a simple uniform endpoint bound. Directly,

    Delta_R=[(e_R+1+w_R/k-1/s)/r]_+
           <=(w_R-t)_+,
    Delta_L<= (w_L-t)_+.

Use (FT9) and d0=3/5-t. On 0<=h<=17/50, d0-h/4>0: for example
c<15/16 and r>7/5 give d0>1/8>17/200. Thus

    gamma(Delta_R^2+Delta_L^2)<=L(h),
    L(h):=gamma[(d0-h/4)^2+(d0+3h/4)^2]
          =2gamma d0^2+gamma d0 h+(5/8)gamma h^2.        (FT14)

### 5. Combine exterior and niche payments without double counting

Write Z_R=Z_R^0-delta_L/(2c), Z_L=Z_L^0-delta_R/(2c).
Their undepleted sum satisfies

    Z_R^0+Z_L^0
      =E/2+a/k+(k-2)M+1-1/s-1/c+2k+h/2
      >=S(a,M,h),
    S(a,M,h):=a/k+(k-2)M+3/2+2k-4c+h/4.               (FT15)

Let G0=[(Z_R)_+^2+(Z_L)_+^2]/r. Cauchy-Schwarz, followed by
the elementary two-term square inequality, gives

    S_+<=sqrt(2r G0)+sqrt(r D0/(4c^2)),
    S_+^2<=[2r+r/(4c^2)](D0+G0)=d(D0+G0).             (FT16)

Combining (FT6), (FT10), and (FT13)-(FT16),

    P(U)<=G_h(a,u,v)+L(h),
    G_h:=F_h(a,u,v)-S(a,(u+v)/2,h)_+^2/d.               (FT17)

All niche payments in this calculation are true regions contained in
the original niche. Exterior payment is used once, through D0. The
positive-floor loss is added back explicitly.

### 6. Joint concavity controls all widths and all clipping patterns

Fix h in [0,17/50]. The function G_h is jointly concave in (a,u,v)
on the convex domain a>=37/25, u,v in [a/2,a]. To verify this,
use coordinates (a,M,Dv), where Dv=(u-v)/2. The Hessian of F_h
before clipping terms is

    [ -2,  2,  0 ]
    [  2, -4,  0 ].
    [  0,  0, -2 ]

Each active clip adds the outer product of (-1/2,1,+1) or
(-1/2,1,-1), respectively. Even with both clips active the Hessian is

    [ -3/2,  1, 0 ]
    [    1, -2, 0 ],
    [    0,  0, 0 ]

which is negative semidefinite. Every other clipping pattern subtracts
positive semidefinite outer products from this matrix. First derivatives
match at clipping boundaries. The subtraction of the convex function
S_+^2/d preserves concavity. Throughout this domain the apex is
positive, as checked after (FT5).

Set

    a0=37/25,
    B(a)=a-(a-k)^2/2,
    s0(a)=d a/2-(4c-2),
    m0(a)=(a+k)/2.

For u=v=M in the regime without window clipping and with S>=0,
put m'=M-h/4. Direct
completion of squares in (FT7) and (FT15) gives

    G_h=B(a)-kh/2-h^2/8-2[m'-m0(a)]^2
         -[s0(a)-b(m'-m0(a))-Ah/4]^2/d.                (FT18)

Since 2d+b^2=9, the stationary point at a=a0 is

    m'=m0(a0)+(b/9)[s0(a0)-Ah/4],
    u_*=v_*=m'+h/4.                                   (FT19)

We must check that this point is genuinely unclipped for every allowed
h, so that it is a global support critical point of the full function.
The elementary radical bounds

    140/99<r<99/70, 923/1000<c<231/250

imply

    703/1000<s0(a0)<71/100.                            (FT20)

Indeed the lower and upper intermediate bounds are respectively
5803/8250 and 2477/3500. The right clipping quantity at (FT19) is

    u_*-k-a0/2=-k/2+(b/9)s0(a0)+(1/4-bA/36)h.

Use k>41/99, b<8/5, bA>3/4, and h<=17/50. It is strictly below

    -41/198+(8/5)(71/100)/9+(11/48)(17/50)
      =-129/44000<0.                                  (FT21)

The left clipping quantity is smaller by h. Also s0(a0)-Ah/4>0
by (FT20), A<3/5, and h<=17/50; therefore u_*>a0/2.
Equation (FT21) implies u_*<a0/2+k<a0. Both supports are interior.
The affine S is positive there, because after (FT19) it equals
(2d/9)[s0(a0)-Ah/4]. Thus (FT19) is an actual interior critical
point in (u,v) of the full, differentiable G_h.

Its value is

    K(a0,h)=B(a0)-kh/2-h^2/8-(2/9)[s0(a0)-Ah/4]^2.     (FT22)

Its partial derivative in a, since the other two derivatives vanish,
equals the derivative of the same optimized expression:

    K_a(a0,h)=r-a0-(2d/9)[s0(a0)-Ah/4]<0.              (FT23)

Here a0>r and the bracket is positive. Joint concavity and the
supporting plane at (a0,u_*,v_*) now give

    G_h(a,u,v)<=K(a0,h)  for every a>=a0,              (FT24)

including configurations with one or both 45-degree clips. The
geometry was needed only up to a=8/5, but the supporting-plane
inequality itself holds on the entire enlarged convex domain.

### 7. The resulting scalar bound decreases with tilt

Expanding K(a0,h)+L(h) as a quadratic in h gives constant
B(a0)-(2/9)s0(a0)^2+2gamma d0^2, linear coefficient

    ell=-k/2+A s0(a0)/9+gamma d0,

and quadratic coefficient

    q=-1/8-A^2/72+5gamma/8.

The bounds k>2/5, A<3/5, gamma<3/10, (FT20), and

    d0<3/5-2(923/1000)+99/70=589/3500

yield

    A s0(a0)/9+gamma d0
      <(3/5)(71/100)/9+(3/10)(589/3500)
       =10271/105000<1/10.

Hence ell<-1/10, while q<1/16. On 0<=h<=17/50,

    ell+2qh<-1/10+h/8<=-1/10+17/400<0.                (FT25)

Thus the complete bound, including its positive-floor correction,
is maximized at h=0. Finally

    B(a0)=(62/25)k-72/625,
    2gamma d0^2<(3/5)(589/3500)^2<17/1000.

Use k<29/70 and s0(a0)>703/1000 to obtain

    P(U)<(62/25)(29/70)-72/625
           -(2/9)(703/1000)^2+17/1000
         =25811237/31500000<41/50.                     (FT26)

The final rational gap is 18763/31500000>0. This proves (FT3).

This is a scalar exclusion for actual canonical caps satisfying the
endpoint law. It assumes neither source unit curvature nor a finite
angle stationary optimizer. It lowers the remaining width ceiling
to C<37/50; it does not by itself establish the missing unit-curvature
condition below that ceiling.

---

<a id="proof-first-wing-structure"></a>
## Technical proof 21. The tilted first-wing structure and projection

Written structural lemmas, independently checked within the research session, October 10, 2026. These assume that the first charged-wing
curvature density is at most one. They support the subsequent
[folded-companion exclusion](#proof-first-unit);
they do not establish the first-unit hypothesis for every remaining width.

### 1. Setting and the initial interval

Use the actual stationary cap and left-wing surrogate notation of the
[two-unit exclusion](#proof-two-unit-wings), but assume only

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

### 2. A first bad companion state must lie beyond the charged B tangencies

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

#### Consequence when the top overhang vanishes

If T=0, every B tangent is in J, including any final constant B plateau.
The same proof applies over the whole quarter, with beta=L. Thus E is
empty. Outside E, FG2 and the arm bound give v<=1 a.e. as above. The
cap is therefore two-unit, and the audited two-unit exclusion contradicts
its positive tilt. In particular every remaining first-unit tilted
stationary cap must have

\[
\boxed{T>0.}                                      \tag{FG8}
\]

### 3. The actual positive niche is a single interval even if D folds

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

### 4. Exact projection balance in the folded case

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

### 5. A stronger left-boundary signed margin when C<=1/sqrt(2)

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

### 6. The first bad entry has q at most one quarter

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

---

<a id="proof-fold-occupations"></a>
## Technical proof 22. Fractional occupations for folded sources

Independent written audit of the source-occupation argument in the
[first-wing exclusion](#proof-first-unit), October 10, 2026.
The energy algebra is checked separately below. This note supplies the
measure details without assuming a finite contact chart or ordinary
niche-arclength convergence.

### 1. Geometric inputs used here

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

### 2. Retain source angle and abscissa jointly

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

### 3. Classification of an active parameter

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

### 4. The B contribution is full

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

### 5. A common fractional occupation at a corner

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

### 6. The residual D occupation

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

### 7. Independent algebra check

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

---

<a id="proof-two-unit-wings"></a>
## Technical proof 23. The two-unit-wing energy identities used in the first-wing argument

**Written two-unit-wing lemma, independently audited within the research session.**

This note proves that a canonical global maximizer of the actual spatial
score cannot be tilted if both of its regular charged-wing curvature
densities are at most one. Every possible order of the floor and window
crossings is covered. The proof establishes the needed finite-source
projection and local flux identities explicitly, including portions that
disappear at height zero.

The geometric reductions and source-measure inputs are
[MID](#proof-middle-chord),
[TF](#proof-facet-pinning),
[RG](#proof-prescribed-regularity),
[EP](#proof-full-endpoints), and
[LH](#proof-full-pressures).
The [tilted-width exclusions](#proof-tilted-width) place every
remaining tilted maximizer in the range used below. The
[horizontal theorem](#proof-horizontal-complete) already proves
the sharp value for every horizontal canonical global maximizer.

**The extra hypothesis here is that both regular wing densities are at most
one.** [CH7](#proof-full-curvature) supplies
one such bound for tilted maximizers with C at most 2/3. It does not supply
the other bound, and this note does not infer it. Every remaining
above-reference maximizer must therefore have a genuinely nonunit regular
wing. That is the current obstruction to Gate 1.

### 1. Domain and exact dependencies

Let U be the MID-canonical, EP-selected global maximizer of the actual spatial
objective P. Assume its affine middle roof is positively tilted after
reflection if needed. Translate so that

    I=[-2C,2C], J=[-C,C], A(-C)=a=1-epsilon, A(C)=1,
    1/2<C<4/5, 1/2<a<1.

The bounds in this display are available for every remaining tilted
maximizer from the exact short-width, wide-width and low-endpoint exclusions.
The stronger current bounds C>1001/2000 and epsilon<17/50 are not needed here.
TF4 places the top face at [C,b] x {1}; define

    T=b-C >=0, eR=A(2C), eL=A(-2C), z=n_U(C).

In particular the argument does not assume that the top face is a point.
LH2 gives positive endpoint pressures, and therefore EP gives equality of
limiting finite positive source measures and actual charged wing-curvature
measures. RG supplies the regularity and excludes open-quarter wing atoms.
The only additional hypothesis of this note is the unit bound on both
charged-wing densities, made explicit below.

Write L=pi/2, mu=(cos t,sin t), nu=(-sin t,cos t), and use the **left-wing
surrogate support** rather than the actual companion support across the
central-facet switch:

    f(t)=h_U(mu_t),
    g(t)=max_{-2C<=x<=-C}[-x sin t+A(x)cos t].

The endpoint values and derivatives are

    f(0)=g(L)=2C, f(L)=1, g(0)=a,
    f'(0)=eR, f'(L)=-b, g'(0)=C, g'(L)=-eL.          (TU.1)

Assume, in addition to the proved W^(2,infinity) regularity,

    0<=u=f''+f<=1, 0<=v=g''+g<=1  a.e. on (0,L).     (TU.2)

The actual companion is max(g,-C sin t+cos t). Its second term gives the
inner-wall height

    1-sec t+(x-C)tan t <=0  for x in J.

Consequently the full actual **positive** niche on J is exactly the positive
part of the surrogate two-wall roof. This follows by distributing min over the displayed maximum and then
taking the positive part; it is an all-angle identity, not an assumed
contact pattern. The surrogate has no central-facet atom;
before delta=atan(epsilon/(2C)) its curvature is zero. Actual quadrants with
0<t<delta have no positive part in J, so the finite-source equality also
forces u=0 there. These observations permit all subsequent source statements
to be made with f,g, including angles below the central-facet switch.

### 2. Monotone wall tangencies and ordered contacts

Set

    p=f'-g+1, q=g'+f-1,
    c=(f-1)mu+(g-1)nu,
    B=c+p nu=(f-1)mu+f'nu,
    D=c-q mu=(g-1)nu-g'mu.

Then

    p'=u-1-q, q'=v-1+p,
    B'=(u-1)nu, D'=(1-v)mu.                         (TU.3)

Thus B_x and D_x are nondecreasing, B_y is nonincreasing, and D_y is
nondecreasing. Their endpoints are

    B(0)=(2C-1,eR), B(L)=(b,0),
    D(0)=(-C,-epsilon), D(L)=(1-2C,eL).              (TU.4)

Because C>1/2,

    q cos t-p sin t=B_x-D_x >=4C-2>0.                (TU.5)

The endpoint contact signs are

    p(0)=eR+epsilon>0, q(0)=3C-1>0,
    p(L)=1-3C-T<0, q(L)=-eL<0.

The differential inequalities p'<=-q and q'<=p, together with TU.5, imply
unique ordered sign changes alpha<eta:

    p>0 on (0,alpha), p<0 on (alpha,L),
    q>0 on (0,eta), q<0 on (eta,L).                  (TU.6)

For example, while p>=0, TU.5 makes q>0 and hence p strictly decreases.
After p becomes negative, q strictly decreases as long as it is nonpositive;
at p=0 the vector field points strictly into p<0 whenever q>0. A return
through either zero is therefore impossible. At a common zero TU.5 would
fail. This also handles possible weak-density degeneracies without an
assumed finite contact chart.

Let gamma be a crossing of D_y=0 and beta a crossing of B_x=C. If T>0 both
are interior. Crossing plateaus cause no integration ambiguity: 1-v=0 a.e.
on a D_y plateau, and 1-u=0 a.e. on a B_x plateau. Write

    x_zero=D_x(gamma), D(gamma)=(x_zero,0),
    B(beta)=(C,z).                                  (TU.7)

The following source-separation estimate holds throughout C<=4/5. For the
right-window statement, any B tangency with B_x>=C has k=cos t<=C and

    p <= 1-(2C+k)sqrt(1-k^2)+epsilon k <0.            (TU.8)

The expression is convex in k. Its value at k=0 is 1-2C<0; at k=C it is
strictly below 1-3C sqrt(1-C^2)+C/2<0. The last strict inequality follows
from

    9C^2(1-C^2)-(1+C/2)^2>0  on [1/2,4/5].

Its derivative is (2-3C)(24C^2+16C-1)/2, and its endpoint values are
1/8 and 71/625, so its minimum is positive. Hence B(alpha)_x<C and
beta>alpha. Also B_y>=0, with B_y(alpha)>0: if it were zero, monotonicity
would make B constant at (b,0) from alpha to L, contradicting TU.8 and
p(alpha)=0. On the core interval (alpha,eta),

    c_y=B_y-p cos t>0,
    c_x'=p cos t-q sin t<0.

Its endpoints are c(alpha)=B(alpha), c(eta)=D(eta). Since D_x>=-C and
B(alpha)_x<C, the entire corner arc lies strictly inside J. Its positive
height at eta proves gamma<eta.

Global monotonicity of the two wall tangencies gives the signed envelope
graph: D up to eta, the corner c traversed in reverse from eta to alpha,
and B from alpha onward. In particular its negative part occurs before
x_zero, its positive part is exactly (x_zero,b), and n_U(-C)=0. Its positive
graph inside J is precisely

    D[gamma,eta], reverse c[alpha,eta], B[alpha,beta]. (TU.9)

This graph description follows from the signs and monotonicity in TU.3--6;
it is not imposed on the initial cap. For an explicit verification, the two wall derivatives are

    partial_t R_t(x)=(x-B_x(t))/sin^2 t,
    partial_t S_t(x)=(x-D_x(t))/cos^2 t.

At a D tangency with q>0, S is the global second-wall maximum and its
first companion lies strictly higher, so the full two-wall envelope equals
D there. At a B tangency with p<0 the reflected argument applies. At a
corner with p<0<q, every earlier second wall and every later first wall
is strictly below the corner, so the full envelope equals that corner.
The three spatial intervals meet at D(eta)=c(eta) and c(alpha)=B(alpha),
and cover [-C,b]. Their endpoint-angle limits supply the constant signed
heights -epsilon to the left and zero to the right. This verifies the
claimed graph directly from the full wall families.

### 3. Exact projection balance, with the zero-height limit issue resolved

Let U_n be the EP-selected finite polygons and Z_n={x in J_n:n_n(x)>0}.
The exact finite graph projection identity and the limiting source equality
give

    lim |Z_n| = integral_0^L [u sin t+v cos t]dt
              = (2C-b)+C=2C-T.                       (TU.10)

The last equality uses TU.1 and the horizontal projections of the two
outer source curves. It excludes the charged horizontal top segment T.

It is not legitimate to identify this limit merely from uniform roof
convergence. Here is the needed separate argument. The continuum roof is
positive on (x_zero,C], so uniform convergence gives the corresponding
lower bound liminf |Z_n|>=C-x_zero. On a compact K strictly inside
(-C,x_zero), the **surrogate signed** roof is strictly negative. For every
fixed angular cutoff h>0, every surrogate quadrant height on
K x [h,L-h] is therefore bounded strictly below zero. The added actual
high-point wall is also strictly negative there: x<C and t>0 in its
displayed height formula. Thus all actual quadrants with turning angle in
[h,L-h] have strictly negative height on K, uniformly. The converging
finite quadrants cannot contribute positive graph there for large n.

Any finite positive graph left over K must consequently come from source
normals within h of one of the endpoint directions. EP.22 (the uniform
O(grid spacing) finite source-exposure bound) bounds their total source
mass, and hence their horizontal projection, by O(h)+o(1). Exhaust K toward
(-C,x_zero), then let h decrease to zero. This proves

    lim |Z_n|=C-x_zero.

Together with TU.10 it gives the exact relation

    boxed: T=C+x_zero.                                (TU.11)

In particular T>0. Indeed D_y rises from -epsilon to zero before the
interior angle eta, so integral_0^gamma(1-v)sin t=epsilon>0. On this
interval cos t>0, and its horizontal projection
integral_0^gamma(1-v)cos t=T cannot vanish.

### 4. Exact local source equations, without assuming arclength convergence

On strict compact pieces of the positive graph TU.9, finite active-angle
localization gives the following lower bounds on limiting source measures:

    sigma_f=[(1-u)1_(alpha,beta)+q1_(alpha,eta)]dt,
    sigma_g=[(1-v)1_(gamma,eta)-p1_(alpha,eta)]dt.       (TU.12)

Here B and D have ordinary tangent lengths (1-u)dt and (1-v)dt. On the
strict corner arc, the two vector projection equations for the finite
alternating source edges give q dt to the first source and -p dt to the
second. All those corners have positive height and lie strictly in J, as
proved above. This is exactly the local finite-wall flux calculation used
in the horizontal branch, with its spatial hypotheses verified here.

More explicitly, for a compact strict corner interval, the two source
edge directions are -nu and mu. Their positive lengths a_f dt,a_g dt must
sum to the forward corner displacement after choosing the graph orientation;
comparing coefficients of mu,nu gives a_f=q and a_g=-p. The strict signs
in TU.6 make these lengths positive. Uniform localization to that interval
passes the resulting local finite lower bounds to the limiting measures.
Exhaustion extends them over the open graph pieces. Flat B or D parameter
intervals map to one spatial point and have zero ordinary tangent length,
so the displayed tangency contributions remain valid there.

At this stage assert only nu_f>=sigma_f and nu_g>=sigma_g. This avoids an
unproved global niche-arclength convergence statement. Their weighted total
is already determined by the actual positive graph projection:

    integral sin t d sigma_f + integral cos t d sigma_g
       = C-x_zero.

By EP and TU.10--11, the same weighted total for nu_f=u dt and nu_g=v dt
equals C-x_zero. Their nonnegative differences have zero weighted total;
both weights are strictly positive in (0,L), and EP.22 excludes endpoint
mass. Therefore the differences vanish. We obtain the exact equations

    boxed: u=(1-u)1_(alpha,beta)+q1_(alpha,eta),
           v=(1-v)1_(gamma,eta)-p1_(alpha,eta)  a.e.   (TU.13)

This conclusion also removes all residual floor/plateau mass. It does not
postulate that every weak finite exposure limit is ordinary continuum
arclength.

### 5. Endpoint pressures and the two clipped strip moments

Since n_U(-C)=0 and n_U(C)=z, EP's actual moving-window laws read

    eR=1/2+epsilon/4+3z/4,
    eL=1/2-3epsilon/4-z/4.                            (TU.14)

From D'= (1-v)mu, B'=(u-1)nu, TU.7 and TU.11,

    T=integral_0^gamma(1-v)cos t dt,
    epsilon=integral_0^gamma(1-v)sin t dt,
    T=integral_beta^L(1-u)sin t dt,
    z=integral_beta^L(1-u)cos t dt.                    (TU.15)

All four quantities are nonnegative. Also 0<=z<=eR<=1 and 0<epsilon<1/2,
so epsilon+z<2. The first-source box yields cos beta<=C, hence

    beta>=acos C, sin beta>=3/5, cot beta<=4/3.        (TU.16)

No relative order between gamma and beta, or between either of them and
the opposite contact switch, is assumed anywhere below.

### 6. A continuous contact energy and its exact derivative

Define a continuous, piecewise quadratic function of the ordered contact
state (p,q):

    H=(p-1/2)^2+(q+1)^2+3/4,       if p>=0,q>=0;
    H=(p-1)^2+(q+1)^2,             if p<=0,q>=0;
    H=(p-1)^2+(q+1/2)^2+3/4,       if p<=0,q<=0.     (TU.17)

The formulas match at p=0 and q=0. The reverse sign sector is absent by
TU.5. The composition H(p(t),q(t)) is absolutely continuous. Substitution
of TU.3 and the exact source equations TU.13 gives

    H'=-(q+1)(1-v)1_(0,gamma)
         +(1-p)(1-u)1_(beta,L)   a.e.              (TU.18)

For verification, without either clipping flag the three regimes are

    (++): u=0, v=1/2;
    (-+): u=(1+q)/2, v=(1-p)/2;
    (--): u=1/2, v=0,

and each makes H'=0. In the core, floor clipping replaces v=(1-p)/2 by
v=-p, contributing -(q+1)(1-v); window clipping replaces u=(1+q)/2 by
u=q, contributing (1-p)(1-u). In the initial regime floor clipping gives
v=0 and the same first contribution. In the final regime window clipping
gives u=0 and the same second contribution. If both clips occur in the
core, their contributions add. The conditions gamma<eta and beta>alpha
already exclude the other cases. Thus TU.18 covers every event order.

Endpoint substitution from TU.1 and TU.14 gives

    H(L)-H(0)
      =6CT+T^2-(epsilon+z)(epsilon+z/2).              (TU.19)

Indeed q(0)+1=3C, p(L)-1=-3C-T,
p(0)-1/2=(5epsilon+3z)/4, and q(L)+1/2=(3epsilon+z)/4.

### 7. Evaluate the two energy fluxes exactly

Write

    I_D=integral_0^gamma(q+1)(1-v)dt,
    I_B=integral_beta^L(1-p)(1-u)dt,

    R_D=integral_0^gamma(1-v(t))
              integral_0^t u(s)sin(t-s)ds dt >=0,
    R_B=integral_beta^L(1-u(t))
              integral_t^L v(s)sin(s-t)ds dt >=0.     (TU.20)

Variation of constants from the initial endpoint gives

    q(t)+1=3C cos t+(eR+epsilon)sin t
          -integral_0^t(1-v(s))cos(t-s)ds
          +integral_0^t u(s)sin(t-s)ds.

For any integrable d, symmetry of the cosine kernel gives

    integral_0^gamma d(t) integral_0^t d(s)cos(t-s)ds dt
      =1/2[(integral_0^gamma d cos)^2
             +(integral_0^gamma d sin)^2].

Apply this with d=1-v and TU.15. The result is

    I_D=3CT-T^2/2+eR epsilon+epsilon^2/2+R_D.         (TU.21)

Backward variation of constants from the final endpoint similarly gives

    1-p(t)=(3C+T)sin t+eL cos t
           -integral_t^L(1-u(s))cos(s-t)ds
           +integral_t^L v(s)sin(s-t)ds,

and therefore

    I_B=3CT+T^2/2+eL z-z^2/2+R_B.                   (TU.22)

Integrate TU.18, so H(L)-H(0)=I_B-I_D. Combine TU.19--22, cancel T^2,
and substitute the moving-window pressures TU.14. All terms simplify to
the exact identity

    boxed: 6CT=(z-epsilon)(2-epsilon-z)/4+R_B-R_D.     (TU.23)

For clarity, the endpoint algebra before its final factorization is

    6CT=eL z-eR epsilon+epsilon^2/2
                      +3epsilon z/2+R_B-R_D,

and TU.14 turns the first four terms into
(z-epsilon)/2+(epsilon^2-z^2)/4. There is no discarded sign term and no
symmetry assumption.

### 8. The contradiction is uniform over every event order

Because v<=1,

    integral_t^L v(s)sin(s-t)ds <=1-sin t.

Use TU.15--16 to bound

    R_B <= integral_beta^L(1-u)(1-sin t)dt
         <= [(1-sin beta)/sin beta] T <=2T/3,

    z <=cot beta T <=4T/3.                           (TU.24)

Since epsilon,z>=0 and epsilon+z<2,

    (z-epsilon)(2-epsilon-z)/4 <=z/2.

Dropping the nonpositive term -R_D in TU.23 now gives

    6CT <=z/2+R_B <=4T/3.

But C>1/2 and T>0 imply 6CT>3T>4T/3, a contradiction.

**Conclusion.** No positively tilted canonical spatial global maximizer in
the remaining width/height range can have both charged-wing curvature
densities at most one. Reflection excludes negative tilt under the same
condition. Coupled with the already proved horizontal sharp-value branch,
this closes the scalar value problem as soon as a global two-unit-wing
theorem, or a valid extension of the present argument to the remaining
nonunit branch, is supplied. The first-quarter-only theorem for C<=2/3
does not yet supply that missing hypothesis.

---

<a id="proof-first-unit"></a>
## Technical proof 24. The complete tilted first-unit-wing contradiction (GF)

Written theorem, independently checked within the research session, October 10, 2026. This excludes a tilted maximizer whenever its first regular wing has curvature at most one, with arbitrary bounded companion folds. The finite-source occupation proof is expanded in the
[independent source audit](#proof-fold-occupations).

### 1. Statement and genuine global inputs

Let U be the selected canonical positively tilted global maximizer for the
actual spatial one-cap score P, normalized by

    I=[-2C,2C], J=[-C,C], A(-C)=1-epsilon, A(C)=1,
    1/2<C<4/5, 0<epsilon<1/2,
    top=[C,b], T=b-C, eR=A(2C), eL=A(-2C).

Assume the established positive endpoint-pressure and regularity theorems,
and assume the first regular wing density satisfies 0<=u<=1. Then U cannot
be a global maximizer. No bound v<=1 on the companion wing is assumed.

Use the actual first support f and the low-left-wing surrogate g. With
L=pi/2, mu=(cos t,sin t), nu=(-sin t,cos t), put

    u=f''+f, v=g''+g,
    p=f'-g+1, q=g'+f-1,
    c=(f-1)mu+(g-1)nu, B=c+p nu, D=c-q mu.

Their endpoint data and kinematics are

    f(0)=g(L)=2C, f(L)=1, g(0)=1-epsilon,
    f'(0)=eR, f'(L)=-b, g'(0)=C, g'(L)=-eL,
    p'=u-1-q, q'=v-1+p,
    B'=(u-1)nu, D'=(1-v)mu,
    B(0)=(2C-1,eR), B(L)=(b,0),
    D(0)=(-C,-epsilon), D(L)=(1-2C,eL).              (GF.1)

The surrogate differs from the actual companion only by an additional
high-top-point wall whose height is nonpositive everywhere on J. Thus
positive niche contacts on J are unchanged. Before the central switch
delta=atan(epsilon/(2C)), both regular densities vanish.

We use the [two-unit theorem TU](#proof-two-unit-wings), the
[first-wing structural lemmas](#proof-first-wing-structure), the
[regularity and sharp arm bounds RG/AR](#proof-prescribed-regularity),
and the [endpoint/source identities EP](#proof-full-endpoints). In particular, the last source identities concern limits of
finite exposed-source measures. They do not assert convergence of ordinary
niche arclength at zero height.

If v<=1 a.e., TU already gives the contradiction. If T=0, the audited
first-bad-entry transfer gives v<=1. We may therefore assume

    T>0 and v>1 on a set of positive measure.

The general first-good positive-interval and no-ghost projection theorem,
which does not require monotonicity of D, gives

    {x:n_U(x)>0}=(x_zero,b),
    x_zero=-C+T, n_U(-C)=0.                              (GF.2)

For reference, write the two proper-angle inner wall heights as

    R_t(x)=(f(t)-1-x cos t)/sin t,
    S_t(x)=(g(t)-1+x sin t)/cos t
          =tan t [x-L0(t)],
    L0(t)=(1-g(t))/sin t.

The same positive-interval theorem identifies x_zero with the global
minimum of L0. Also x_zero<1-2C. The actual endpoint pressures are

    eR=1/2+epsilon/4+3z/4,
    eL=1/2-3epsilon/4-z/4, z=n_U(C).                    (GF.3)

### 2. Ordered contact signs and the first bad entry

Let tau be the first entry into {p<-1,q>0}. Before tau, the generic arm
bound and same-sign shadowing give v<=1 a.e. The source-box estimate TU.8,
which needs only the first unit bound, says that p<0 whenever B_x>=C.
If beta denotes the crossing B_x=C, it also gives

    beta>=acos C, sin beta>=3/5, cot beta<=4/3.          (GF.4)

Let alpha be the p-zero on the positive-q component leading to tau. Past
second-unit curvature and global first-unit curvature give strict positive
corner visibility from alpha to tau. Before beta its B tangencies are also
charged. The same argument as in the structural addendum proves
alpha<beta<tau and the first-source lower bounds

    u>=(1+q)/2 on (alpha,beta),
    u>=q on (beta,tau).

The core lies in J there: before tau, D_x is nondecreasing from -C, while
c_x decreases from B_x(alpha)<C. Its height satisfies
c_y=B_y-p cos t>0. In particular q(alpha)<=1 because u<=1.

On (alpha,beta) use

    E=(p-1)^2+(q+1)^2, E'<=0, E(alpha)<=5.

On (beta,tau) use

    K=q+(p-1)^2/4,
    K'=v-1+p+(p-1)(u-1-q)/2
       <=v+(p-1)/2<=0.

At tau, p=-1, so

    1+q(tau)<=K(beta)
       <=1+q(beta)/2-q(beta)^2/4<=5/4.                  (GF.5)

Thus q(tau)<=1/4. A later positive-q component has q<=1/8 by AR7, so its
entry energy is less than 4; the same E/K comparison prohibits a bad
entry there. Consequently the nonunit branch has the ordered signs

    (++): (0,alpha), (-+): (alpha,eta), (--): (eta,L),
    alpha<beta<tau<eta.                                 (GF.6)

The initial positive state remains valid for epsilon<1/2: the positive
pressure side bounds give eR>=2/5, and before delta one has
p(t)>=eR-epsilon/2>3/20, while q(delta)>=3C-1-delta>0.
After beta, p<0 and the arm inequality gives q'<=-1/2. Hence every later
bad point has q<=1/4.

### 3. Fractional source occupations, without a floor-shape assumption

Retain the selected finite source measures jointly in angle and graph
position. Their sin/cos weighted x-marginal is Lebesgue measure on the
finite positive graph projection. The no-ghost projection in GF.2 gives
the limiting weighted x-marginal exactly on (x_zero,C). Thus there is no
residual floor mass. The independent occupation audit gives the following
local disintegration; its proof is recalled to specify its scope.

At a regular positive active point, the max/min first-order condition
places the contact at B(t), D(t), or c(t). Endpoint-angle mass vanishes by
EP.22. The global first unit bound makes B the full first-wall envelope.
On the core it has strict companion slack, so its complete charged
contribution is (1-u)dt on (alpha,beta). Its negative-slope graph lies to
the right of every core corner, because c_x is strictly decreasing from
B_x(alpha).

On a measurable actual corner contact set, the identity n_U(c_x)=c_y and
the level-set chain rule identify the graph tangent a.e. Any competing D
tangent has that same graph tangent. Subtracting its parallel vector flux
and resolving the residual in the two independent wall-ray directions
gives the common ratio q:(-p). The joint horizontal projection bound limits
the remaining occupation to one. Thus one measurable chi in [0,1] gives
the two corner source densities q chi and -p chi.

A positive visible D tangent must have v<=1; if v>1 its second wall has
an angular local minimum with strict first-wall slack. Its remaining
source density is (1-v)d for one measurable d in [0,1], with d=0 wherever
v>1 or D_y<0. Flat projected arcs have no residual measure because the
weighted projection is already exact. Fractions allow arbitrary ties and
measurable contact sets; no finite contact chart is assumed.

All positive core corners and positive D points are inside J. Indeed
S_t(x)>0 implies x>L0(t)>=x_zero>-C. The core's upper bound is
c_x<=B_x(alpha)<C, while D_x=x_g+sin t<=1-C<C. Thus neither family has
an additional positive piece beyond J. One may equivalently set its
occupation to zero outside J; this yields the same equations.

The local first-order classification exhausts the limiting graph pieces;
the exact joint projection rules out any nonnegative residual. EP then
identifies the angular marginals with u dt and v dt. The exact equations
are

    (++): u=0, v=(1-v)d;
    core: u=(1-u)b_flag+q chi,
          v=(1-v)d-p chi;
    (--): u=v=0,
    b_flag=1_(t<beta) on the core.                       (GF.7)

In particular

    u=(b_flag+q chi)/(1+b_flag),
    v=(d-p chi)/(1+d).                                  (GF.8)

The strict visibility already used in Section 2 gives chi=1 before tau.
These source equations do not require D_y to have a unique zero, or D_x
to be monotone.

### 4. The first floor crossing precedes every bad episode

Let gamma be the first zero of D_y. It exists because D_y(0)=-epsilon
and D_y(eta)=c_y(eta)>0. We claim

    gamma<tau.                                          (GF.9)

Suppose D_y has not become positive by tau. While its initial nonpositive
interval persists, L0'=D_y/sin^2 t<=0. At any positive core corner c(t),
write x=c_x(t), y=c_y(t)>0. For every proper earlier angle r<t,

    L0(r)>=L0(t),
    S_r(x)=tan r [x-L0(r)]
           <tan t [x-L0(t)]=S_t(x)=y.

This remains true if the bracket at r is negative. Actual extra high-point
walls are nonpositive on J, so they do not affect the strict inequality
at y>0. For every later angle r>t,

    partial_r R_r(x)=(x-B_x(r))/sin^2 r<0,

because B_x is nondecreasing and x<B_x(t). Thus the current corner is
globally unique and fully exposed: chi=1. Its position is in J by the
argument in Section 3. The same conclusion applies at an isolated first
zero of D_y and extends as long as D_y stays nonpositive.

After tau, while this condition persists, d=0 and b_flag=0. Equations
GF.7 therefore give

    u=q, v=-p, p'=q'=-1,
    D_y'=(1+p)sin t<0.

Consequently D_y cannot leave the nonpositive region; p remains below -1
and q reaches zero while the same strict visibility argument continues.
This contradicts D_y(eta)=c_y(eta)>0.

At the boundary case D_y(tau)=0, justify the initial continuation before
invoking that argument. The corner at tau is positive and in the interior
of J, and p(tau)=-1, q(tau)>0. Its remote-angle gaps are strict; on a
compact set of remote angles they are uniform. The two local wall-angle
derivatives have opposite strict signs, p/sin t<0 and q/cos t>0, so the
current corner remains the unique maximum against nearby angles as well.
Continuity therefore preserves strict corner localization on a
neighborhood of tau, giving chi=1 there. Since b_flag=0, we have u=q and
p'=-1 immediately to the right. For p<-1, equation GF.8 then gives
v=(d-p)/(1+d)>1; the D visibility condition forces d=0. Consequently
D_y'=(1+p)sin t<0, excluding an immediate positive departure from zero.
The preceding continuation argument now applies. This proves GF.9,
including its boundary case and any harmless zero plateaus.

Define the first-floor abscissa

    S=C+D_x(gamma).

Unlike T, this is not assumed to be the global minimum baseline abscissa.
At D_y(gamma)=0 we have L0(gamma)=D_x(gamma), hence

    S>=C+x_zero=T>0,
    S<=1, T<=C.                                         (GF.10)

The bound S<=1 follows from x_g<=-C and D_x=x_g+sin gamma. Integrating
GF.1 gives the exact initial-floor and right-window moments

    S=integral_0^gamma(1-v)cos t,
    epsilon=integral_0^gamma(1-v)sin t,
    T=integral_beta^L(1-u)sin t,
    z=integral_beta^L(1-u)cos t.                         (GF.11)

Here v<=1 on [0,gamma] by GF.9. Later floor recrossings are allowed.

### 5. Every later fold has a paid curvature budget

On (tau,eta), equations GF.8 give

    p'=q chi-1-q<=-1.

Thus p<=-1 throughout that interval, and 0<q<=1/4. For w=q-p, direct
substitution yields

    w'=(1-chi)[p+q+d/(1+d)]
                +chi*d*(1+p)/(1+d)<=0.

Since w(tau)<=5/4, we obtain v<=-p<=5/4-q there. Before tau, v<=1;
after eta, v=0. In particular v<=5/4 globally. Where v>1, d=0 and
v=-p chi, u=q chi, so

    (v-1)_+<=1/4-q<=(1-u)/4.                            (GF.12)

This estimate pays actual excess curvature even if its D image goes below
the floor. It does not assert that every fold stays above zero.

### 6. Calibrated energy with the entire fold defect retained

Use the continuous energy

    (++): H=(p-1/2)^2+(q+1)^2+3/4;
    core: H=(p-1)^2+(q+1)^2;
    (--): H=(p-1)^2+(q+1/2)^2+3/4.

Before beta the source equations and chi=1 give
H'=-(q+1)(1-v)(1-d). On the core after beta put

    G=(1-p)(1-u)-(q+1)(1-v)(1-d).

The exact fractional residual is

    H'-G=(1-chi)(p+q).                                  (GF.13)

It vanishes before tau and is nonpositive afterwards because p+q<=-3/4.
On the final sector H'=1-p. Therefore

    H(L)-H(0)
      <=I_B-integral_0^eta(q+1)(1-v)(1-d),
    I_B=integral_beta^L(1-p)(1-u).                       (GF.14)

On [0,gamma], d=0, giving the exact initial contribution
I_D=integral_0^gamma(q+1)(1-v). Beyond gamma, all pieces with v<=1 are
favorable. Every remaining piece is covered by GF.12 and q<=1/4:

    integral_(v>1)(q+1)(v-1)(1-d)
       <=(5/16)integral_beta^L(1-u)
       <=5T/(16 sin beta).

Thus

    H(L)-H(0)<=I_B-I_D+5T/(16 sin beta).                 (GF.15)

### 7. The first-floor displacement improves the contradiction

The exact endpoint algebra and harmonic support reconstructions give

    H(L)-H(0)=6CT+T^2-(epsilon+z)(epsilon+z/2),
    I_D=3CS-S^2/2+eR epsilon+epsilon^2/2+R_D,
    I_B=3CT+T^2/2+eL z-z^2/2+R_B,                      (GF.16)

where

    R_D=integral_0^gamma(1-v(t))
                       integral_0^t u(s)sin(t-s)ds dt>=0,
    R_B=integral_beta^L(1-u(t))
                       integral_t^L v(s)sin(s-t)ds dt.

For clarity, the I_D identity uses the two initial moments S and epsilon,
not T and epsilon. It follows directly by writing
q+1=3C cos t+(eR-1+epsilon)sin t
plus the u-sine and v-cosine convolutions. Replacing v by 1-(1-v) in
the latter makes its self-interaction (S^2+epsilon^2)/2.

Insert the actual pressures GF.3 into GF.15. The resulting inequality is

    6CT <= (z-epsilon)(2-epsilon-z)/4+R_B-R_D
           +(S-T)[(S+T)/2-3C]+5T/(16 sin beta).          (GF.17)

The new displacement term is nonpositive: S>=T and
(S+T)/2<=(1+C)/2<3C for C>1/2. Thus the first floor need not attain the
global minimum. Any later lower minimum only strengthens the estimate.

Finally GF.4, GF.11 and v<=5/4 give

    z<=cot beta T<=4T/3,
    R_B<=(5/4)[(1-sin beta)/sin beta]T<=5T/6.

Since epsilon+z<2 and R_D>=0, GF.17 implies

    6CT<=z/2+R_B+5T/(16 sin beta)
         <=(2/3+5/6+25/48)T=97T/48<3T.

This contradicts C>1/2 and T>0.

**Conclusion.** Every selected tilted global maximizer in the stated
range whose first wing is unit-bounded is excluded, including arbitrary
bounded nonunit companion folds, arbitrary measurable ties, and later
returns of the companion tangency below the baseline. No lower side-height
condition, unique floor crossing, or companion unit bound is needed.

Combining this theorem with [CH7](#proof-full-curvature) excludes all remaining tilted widths C<=2/3. Combining it with the independently checked [initial-floor criterion](#proof-initial-energy) also excludes 2/3<C<=18/25 with 3/100<=epsilon<17/50. Neither combination settles all larger tilted widths.

---

<a id="proof-initial-energy"></a>
## Technical proof 25. The tilted initial-floor energy conditions (IE)

Written proof, independently checked within the research session, October 10, 2026. This gives a
stronger sufficient condition for first-source unit curvature at a
remaining tilted canonical maximizer. Its sufficient curvature criteria can be combined with the
[first-wing tilted exclusion](#proof-first-unit);
the criteria alone are not a sharp scalar value theorem.

### 1. Notation and criterion

Use the actual first-quarter support f and low-wing surrogate support g,
with their regular densities u=f''+f and v=g''+g. Set

    p=f'-g+1, q=g'+f-1,
    d=3C, B=e_R-1+h,
    gamma0=acos(1-h), s0=sqrt(h(2-h)), c0=1-h.

The remaining canonical parameter range has C>1/2 and 0<h<17/50.
The following two inequalities suffice for u<=1 a.e.:

    d^2+B^2<=5,                                        (IE1)
    d^2+B^2+B(1-h)-d sqrt(h(2-h))<=4.                  (IE2)

This statement uses the established spatial same-sign source facts and
subsequent positive-component propagation. Their usual strict versions
give u<1 at the relevant first crossing when either bound is strict.

### 2. Both regular densities vanish on the initial same-sign floor interval

Before the central normal delta=atan(h/(2C)), actual high-point
quadrants make no positive niche in J, and u=v=0 is already proved.
On a compact later interval with p>0,q>0 and D_y<0, the same-sign
source theorem gives u=0. The actual corner is locally shadowed:
at the corner both physical wall heights strictly increase when the
angle increases, because their angle derivatives are respectively
p/sin(t)>0 and q/cos(t)>0.

Any sole second-wall contact contributing positive selected graph must
satisfy its angular stationarity equation, so it is the tangency D.
Its height is strictly negative. Thus no positive second-source piece
remains. The same local comparison excludes limiting floor exposure:
a nonstationary floor contact with strict companion slack is raised by
a nearby angle, and a floor corner in this sign region is raised on
both walls. Compact angle exhaustion and the exact selected source
equality therefore give v=0 as well.

Consequently, as long as the initial p,q-positive component continues
and D_y<0, both densities vanish. The exact zero-density solution is

    f=2C cos(t)+e_R sin(t),
    g=C sin(t)+(1-h)cos(t),
    D_y=1-h-cos(t),

    p-1=B cos(t)-d sin(t),
    q+1=d cos(t)+B sin(t).                            (IE3)

The first D_y zero of this solution is gamma0. The initial values
p(0)=e_R+h>0 and q(0)=3C-1>0 are strictly positive.

### 3. Stop the circle evolution at the floor or the first p-zero

Let alpha be the first p=0 crossing in the initial q-positive component,
if that crossing exists. If q leaves its positive component earlier,
u=0 on its entire positive-positive part; later positive-q components
obey the already proved small-component bound, so they cause no u>1.
We may therefore consider the case where q stays positive up to the
relevant stopping time

    tau=min(alpha,gamma0).

On the interval before tau, (IE3) is a rotation of a vector of squared
length R^2=d^2+B^2. The standard positive-positive energy is

    Epp=(p-1/2)^2+(q+1)^2
        =R^2+p-3/4.

If tau=alpha, p=0 and hence Epp(tau)=R^2+1/4-1.
If tau=gamma0, the same expression equals
R^2+1/4+B c0-d s0. In both cases it is bounded above by

    R^2+1/4+max(B c0-d s0,-1).                        (IE4)

For tau=gamma0 this is immediate. For tau=alpha only the -1 term is
needed; no extrapolation of the zero-density solution past alpha is
asserted. This formulation also avoids needing monotonicity of the
extrapolated circle after its stopping time.

Conditions (IE1)-(IE2) are exactly the statement that the right side
of (IE4) is at most 17/4. If the floor is reached first, the usual
same-sign estimate u=0,v<=1/2 makes Epp nonincreasing until alpha.
Therefore at the first p-zero,

    1/4+(q(alpha)+1)^2<=17/4,
    q(alpha)<=1.

On the rest of that q-positive component, p<0 and the arm bound make
q decrease. Every subsequent positive-q component has q<=1/8.
The established regularity bound u<=kappa(q), together with u=0 on
p,q>0 and the same-sign vanishing on the opposite sign regions,
therefore gives u<=1 a.e. This proves the criterion.

### 4. A small exact uniform consequence above C=2/3

In particular, the criterion holds throughout

    2/3<C<=18/25, 3/100<=h<=17/50.                    (IE5)

Indeed the box bound gives H(C)=1-sqrt(1-C^2)<31/100. The endpoint
laws and nonnegative niche heights place B in the enlarged interval

    -231/400+(5/4)h <= B <= -107/400+(5/4)h.           (IE6)

The sharper left-box estimate n_-<=(H(C)-h)_+ is available but is
not needed for this particular corollary.

For IE1, the maximum of B^2 on this rectangle of h and its two affine
B endpoints is (27/50)^2. Since d<=54/25,

    d^2+B^2 <= (54/25)^2+(27/50)^2
                =12393/2500<5.

For IE2 define

    Q(d,B,h)=d^2+B^2+B(1-h)-d sqrt(h(2-h)).

It increases with d on d>=2, because its derivative is
2d-sqrt(h(2-h))>0. It is convex in B, so for each h it suffices to
use the two affine endpoints in (IE6). At either endpoint B=A+5h/4,
the polynomial part B^2+B(1-h) has h^2 coefficient 5/16>0. Also
-d sqrt(h(2-h)) is convex in h. Each resulting function of h is
therefore convex, so only the endpoints h=3/100 and h=17/50 need
checking.

At h=3/100, sqrt(h(2-h))>243/1000. The two B values are
-27/50 and -23/100, respectively. Substituting d=54/25 and this
lower square-root bound gives

    Q<97713/25000<4,
    Q<99263/25000<4.

At h=17/50, sqrt(h(2-h))>3/4. The two B values are
-61/400 and 63/400, respectively. The same substitution gives

    Q<474913/160000<4,
    Q<507897/160000<4.

All radical comparisons follow by squaring positive rationals. Thus
IE1 and IE2 both hold strictly on (IE5), proving first-source unit
curvature there.

### 5. The remaining high-tilt strip is also first-unit

The same criterion holds for every remaining width when

    C<=37/50, 21/100<=h<=17/50.                       (IE8)

Use H(C)<33/100 and the improved low-wing box bound. On this strip they give

    -107/400<=B<=69/400.

Consequently

    d^2+B^2<=(111/50)^2+(107/400)^2
             =799993/160000<5,

with exact margin 7/160000. For IE2 the expression Q increases in B on
this entire enlarged rectangle, since 2B+1-h>=1/8. Use the affine upper
endpoint B=-101/400+5h/4 and d=111/50. The resulting expression is
convex in h. At h=21/100, sqrt(h(2-h))>61/100 gives

    Q<17911/5000<4.

At h=17/50, the bound sqrt(h(2-h))>3/4 gives

    Q<545121/160000<4.

These exact endpoint comparisons prove both conditions. The general
[first-wing exclusion](#proof-first-unit) therefore
excludes all remaining tilted maximizers with h>=21/100.

### 6. Stronger parameter-dependent endpoint interval

For a sharper application one should retain the actual left-box
improvement. The exact allowed interval is

    -1/2+(5/4)h-(H(C)-h)_+/4 <= B
        <= -1/2+(5/4)h+3H(C)/4.                       (IE7)

The lower endpoint has slope 3/2 for h<=H(C) and slope 5/4 afterwards.
For fixed C the two expressions in IE1-IE2 are convex in B; on each
affine h segment their IE2 expressions are convex in h. Hence any
desired additional rational rectangle can be certified by a few exact
endpoint comparisons. Such a certificate proves a sufficient curvature
condition only; it must still be combined with the appropriate folded
companion/value theorem.

---

<a id="proof-corner-confinement"></a>
## Technical proof 26. Constructing a genuine feasible one-turn survivor (CG)

Written proof, independently checked within the research session, October 10, 2026. This applies the
[proved C<37/50 width cut](#proof-full-triangle). It assumes neither regular wing has curvature
at most one. Every remaining tilted canonical global maximizer gives a
genuine connected one-turn body, so the existing ordinary one-turn area
bound becomes available on the entire remaining tilted branch.

### 1. Setting and statement

Let U be a canonical height-one global maximizer, centered with

    I=[-2C,2C], J=[-C,C],
    1/2<C<=37/50, 0<h<=17/50,
    A(-C)=1-h, A(C)=1,

and with A affine on J. The source and endpoint results already give

    e_R=1/2+h/4+(3n_+-n_-)/4,
    e_L=1/2-3h/4+(3n_--n_+)/4,
    E=e_R+e_L=1-h/2+(n_++n_-)/2,
    max_J n<=E/2, 2P=L_wing.                            (CG1)

Here e_R=A(2C), e_L=A(-2C), n_+=n(C), and n_-=n(-C).
Then every attached inner quadrant with positive apex height has its
apex strictly between -C and C. Consequently n is convex on both
charged wings, n<=A throughout I, and

    S={ (x,y): x in I, n(x)<=y<=A(x) }

is a compact connected genuine one-turn sofa. In particular the already
recorded ordinary one-turn bound G0=22199/10000 implies

    C(3-E-3h/2)+sqrt(C^2+(1-h/2-E/2)^2)<=G0.            (CG2)

One may also use the weaker but sometimes convenient necessary condition

    M/2+C(3-E-3h/2)<=G0.                               (CG3)

### 2. Reduce corner confinement to one explicit trigonometric inequality

Raise the left charged wing by h, make the middle roof horizontal at
height one, and retain the right wing. This is the same genuine lifted
cap Uhat used in the audited finite-angle proofs. Write

    s=sin t, c=cos t,
    f=H_U(c,s), g=H_U(-s,c),
    fhat=H_Uhat(c,s), ghat=H_Uhat(-s,c).

Let delta=arctan(h/(2C)). For t>=delta the original left supporting
point lies on the low wing, so

    f=fhat, g=ghat-hc.

If xhat is the lifted inner corner's horizontal coordinate, the actual
one is therefore

    x_c=xhat+hsc.                                      (CG4)

For the lifted cap, its unit-height box and the actual left middle
endpoint (-C,1) give

    fhat<=2Cc+s, ghat>=Cs+c,
    xhat=(fhat-1)c-(ghat-1)s
         <=C(2-3s^2)+s-c.                             (CG5)

The horizontal corner-confinement lemma already proved in the horizontal
maximizer note uses only these box/endpoint constraints. Since
1/2<=C<=37/50<13/15, it gives xhat>=-C as well. Equation (CG4) then
gives x_c>-C for 0<t<L. For the upper bound it suffices to prove

    c-s-C(1-3s^2)-hsc>0.                              (CG6)

The next section gives an exact certificate on the entire stated
parameter range.

For 0<t<delta the actual second supporting point is instead (C,1),
so g=c-Cs. Its apex height, using f<=2Cc+s, satisfies

    y_c=(f-1)s+(g-1)c
         <=1-c-s+Csc
          =sc[C-2/(1+c+s)]<0.                         (CG7)

Indeed C<=37/50<2/(1+sqrt(2))<=2/(1+c+s). Such a quadrant contributes
no positive niche anywhere. Thus (CG4)-(CG7) suffice to confine all
positive actual corners; no claim about negative corners is needed.

### 3. An elementary certificate for the remaining inequality

#### 3a. If s^2<=1/3

The margin in (CG6) decreases with C and h. It is therefore at least

    [c(50-17s)-(37+50s-111s^2)]/50.

We may enlarge 0<=s<=1/sqrt(3) to 0<=s<=3/5. Both terms to be
compared are positive on this interval. Their squared difference is

    Q(s)=(1-s^2)(50-17s)^2-(37+50s-111s^2)^2
         =1131-5400s+3503s^2+12800s^3-12610s^4.

Put z=s-3/8, so -3/8<=z<=9/40. The exact translation is

    Q=49647/2048-(2091/64)z
          +z^2[116213/16-6115z-12610z^2].              (CG8)

The bracket is a concave quadratic, hence its minimum on this interval
is at an endpoint. Its endpoint values are 249061/32 and 839849/160,
both above 5000. Also 49647/2048>24 and 2091/64<33. Therefore

    Q>24-33|z|+5000z^2
      >=24-1089/20000>0.

Taking the positive square roots proves (CG6) in this case.

#### 3b. If s^2>=1/3

Now the margin increases with C, so put C=1/2. We may also enlarge h
from 17/50 to 2/5. The desired lower bound factors as

    c-s-(1-3s^2)/2-(2/5)sc
      =c[1-(2/5)s-c(3s+1)/(2(1+s))].                   (CG9)

Here s>=1/sqrt(3)>1/2. The two terms compared inside the brackets
are nonnegative. After squaring, clearing the positive denominator,
and cancelling 1+s, their difference is positive precisely when

    R(s)=75-105s-139s^2+241s^3>0.

Set z=2s-1 in [0,1]. Then

    8R(s)=143-253z+445z^2+241z^3
           >=143-253^2/(4*445)>0.                     (CG10)

For 0<t<L, c>0, so (CG9) is strictly positive. This proves (CG6)
in the second case and completes positive-corner confinement.

### 4. The cap-minus-niche body is genuinely feasible

For x>=C, every positive quadrant uses its descending first wall, since
its apex lies to the left of C. Thus n is the maximum of affine first
walls and zero on [C,2C], hence is convex there. Reflection gives the
same statement on [-2C,-C]. The box bound gives n(+-2C)=0 and in fact
n=0 outside I.

The box endpoint estimate gives n_+,n_-<=2/5. Thus (CG1) yields

    max_J n<=E/2<=7/10-h/4<1-h<=A(x), x in J.          (CG11)

The strict inequality follows from 3/10-3h/4>=9/200>0.
On each charged wing, A-n is concave. It is nonnegative at both wing
endpoints by (CG11), the positive endpoint heights, and n(+-2C)=0.
Hence n<=A on every fiber of I.

The continuous top graph of A is connected, and every vertical interval
fiber of S meets it. Thus S is compact and connected. Its horizontal
placement lies in the unit-height strip. At every canonical turn angle,
the outer support halfplanes are supplied by U and S avoids the entire
attached inner forbidden quadrant by its definition. These are the same
full canonical one-turn placements used in the horizontal feasibility
proof. No equality between U and conv(S) is required.

The already established ordinary one-turn area bound therefore applies:

    |S|<=G0=22199/10000.                               (CG12)

Its external mathematical input remains Baek's ordinary one-turn theorem
with the existing exact AreaBounds enclosure recorded in
[one-turn-single-excess-quarter.md](#external-inputs). This argument introduces no new
numerical one-turn bound or formalization claim.

### 5. The exact tilted Gerver inequality

The central cap area is 2C-Ch. Convexity of the niche on each wing and
the zero outer endpoint values give

    N_out<=C(n_++n_-)/2=C(E-1+h/2).

Consequently

    |S|=P+2C-Ch-N_out
        >=P+C(3-E-3h/2).                              (CG13)

The two charged-wing chord lengths, including a possible horizontal top
overhang in the total length, imply by (CG1)

    P=L_wing/2
      >=[sqrt(C^2+(1-e_R)^2)
          +sqrt(C^2+(1-h-e_L)^2)]/2
      >=sqrt(C^2+(1-h/2-E/2)^2).                       (CG14)

Both vertical drops are nonnegative because the wings are monotone
toward their middle endpoints. The final inequality is the Euclidean
triangle inequality applied to the two chord vectors.

Combining (CG12)-(CG14) proves (CG2). Replacing (CG14) by the reference
lower bound P>=M/2 gives (CG3). For fixed C,h the left side of (CG2)
decreases with E on the actual geometric range E<=2-h, so any separately
proved upper bound on endpoint niche leakage can be substituted safely.

The theorem makes the ordinary one-turn estimate available throughout
the remaining tilted domain. It does not establish small leakage or
exclude that domain by itself.

---

<a id="proof-early-excess"></a>
## Technical proof 27. Forward curvature excess and endpoint leakage (ET)

Written proof, independently checked within the research session, October 10, 2026. This uses the
[initial-floor argument](#proof-initial-energy), together with
the already established same-sign spatial propagation. No first-source
unit-curvature hypothesis is imposed.

### Statement

For every remaining tilted canonical maximizer with

    2/3<C<37/50, 0<h<17/50,

the absolutely continuous first-source density u satisfies

    u(t)<=1 for a.e. t>=11/15.                         (ET1)

Moreover

    11/15<acos(37/50)<=acos C.                        (ET2)

Thus every possible u>1 episode ends before any positive right-window
endpoint tangency. Write d=3C, B=e_R-1+h and gamma0=acos(1-h).

### 1. The universal quadratic excess envelope

All possible u>1 lies in the initial positive-q component after its
first p=0 time alpha. Before that crossing u=0. If there is no crossing,
or if q(alpha)<=1, there is no first-source excess. Later positive-q
components have q<=1/8 and cannot generate u>1.

Put epsilon=(q(alpha)-1)_+. On the initial component after alpha,
while q>1, u<=q gives p'<=-1 and hence p(alpha+tau)<=-tau.
For 0<=tau<=1, the arm estimate for v then gives

    q'<=-(1+tau)/2,
    (u(alpha+tau)-1)_+
      <=[epsilon-tau/2-tau^2/4]_+.                     (ET3)

When -1<=p<0, use v<=(1-p)/2. When p<-1, the stronger q'<=-1
implies the stated bound as long as tau<=1. Therefore, provided
epsilon<3/4, all excess ends within the time

    ell(epsilon)=sqrt(1+4epsilon)-1<1                 (ET4)

after alpha. This is the same quadratic envelope used in the audited
horizontal leakage argument.

The endpoint box H(C)<1/3 and positive EP imply

    B>=-1/2+(5/4)h-(1/3-h)_+/4,
    B<=-1/4+(5/4)h,
    -7/12<B<7/40.                                    (ET5)

The lower bound uses the sharper low-wing box n_-<=(H(C)-h)_+.

### 2. The first p-zero precedes the floor crossing

Suppose alpha<=gamma0 and epsilon>0. Both densities vanish up to
alpha by the initial-floor theorem, so

    p-1=B cos t-d sin t,
    q+1=d cos t+B sin t,
    (q(alpha)+1)^2=d^2+B^2-1.

The positive excess therefore forces d^2+B^2>5. In view of
d<111/50 and B<7/40, this is impossible for B>=0. Thus B<0.
At alpha,

    d sin(alpha)=1+B cos(alpha)<=1,

so alpha<=pi/6<8/15. Also

    (q(alpha)+1)^2
      <(111/50)^2+(7/12)^2-1
       =384181/90000<(207/100)^2.

Hence epsilon<7/100. Since 1+4(7/100)=32/25<(17/15)^2,
ET4 gives ell(epsilon)<2/15. All excess ends before

    alpha+ell<8/15+2/15=2/3<11/15.                    (ET6)

### 3. The floor crossing precedes the first p-zero

Now suppose gamma0<alpha, with the initial q-positive component still
present. The exact initial solution gives

    p(gamma0)=1+B(1-h)-d sqrt(h(2-h))>0.               (ET7)

In this case necessarily h<1/8. To see this, use ET5 and d>2 to bound
the right side above by

    V(h)=1+[-1/4+(5/4)h](1-h)-2sqrt(h(2-h)).

On [1/8,17/50], V is convex: its second derivative is
-5/2+2/[h(2-h)]^(3/2)>0. Both endpoints are negative. At 1/8,

    V(1/8)=235/256-sqrt(15)/4<235/256-15/16<0.

At 17/50, use sqrt(1411)>75/2 to obtain

    V(17/50)=1+231/2000-sqrt(1411)/25<0.

Convexity excludes ET7 on that whole interval. Therefore h<1/8, and
the more precise interval from ET5 is

    -7/12+(3/2)h <=B<=-1/4+(5/4)h< -3/32.             (ET8)

The initial positive-positive energy, evaluated at the floor and then
propagated to alpha, gives

    (q(alpha)+1)^2
       <=Q(d,B,h)
        :=d^2+B^2+B(1-h)-d sqrt(h(2-h)).               (ET9)

#### 3a. If 1/25<=h<1/8

The function Q increases with d. It is convex in B. At each of the
two affine endpoints of ET8 it is convex in h, since the quadratic
coefficient is respectively 3/4 or 5/16 and the negative square root
is convex. Thus it suffices to check d=111/50 and h=1/25 or 1/8.

At h=1/25 the square root is exactly 7/25, and the two B endpoints
are -157/300 and -1/5. The second endpoint gives the larger Q
because the sum of those endpoints plus 1-h is positive. Its value is

    Q(111/50,-1/5,1/25)=10387/2500.                   (ET10)

At h=1/8 both B endpoints are negative and B+1-h>0. Their contribution
B^2+B(1-h) is therefore negative. Using sqrt(15)>15/4 gives

    Q<(111/50)^2-(111/50)(15/32)<10387/2500.

Consequently

    (q(alpha)+1)^2<=10387/2500<(51/25)^2,
    epsilon<1/25,
    ell(epsilon)<2/25.                               (ET11)

To bound alpha, on the initial p,q-positive component q'>=-1 and
p'=-1-q<=-d+t. Since p(0)=1+B<29/32,

    p(t)<=29/32-dt+t^2/2.

The upper bound is negative at t=3/5 when d>=2. Thus alpha<3/5
unless the q-positive component ends earlier, in which case it has no
excess. Combining with ET11,

    alpha+ell<3/5+2/25=17/25<11/15.                   (ET12)

#### 3b. If 0<h<1/25

Now -7/12<B<-1/5, so p(0)=1+B<4/5. The same quadratic estimate gives

    alpha<=d-sqrt(d^2-8/5).                           (ET13)

Also B(1-h)-d sqrt(h(2-h))<=B: since B<0, its excess over B is
|B|h-d sqrt(h(2-h))<0, using |B|<7/12, d>2 and
sqrt(h(2-h))>=h. The convex quadratic B^2+B is at most -4/25 on
[-7/12,-1/5]. Hence ET9 yields

    epsilon<=(sqrt(d^2-4/25)-2)_+.                   (ET14)

If the right side vanishes there is no excess. On its positive range,
d>=sqrt(104)/5, put

    W(d)=d-sqrt(d^2-8/5)
            +sqrt(4sqrt(d^2-4/25)-7)-1.

This is increasing for sqrt(104)/5<=d<=111/50. Indeed the derivative
of its first two terms is greater than -1/3, since

    d^2/(d^2-8/5)<=13/8<16/9.

The derivative of its square-root term is

    2d/[sqrt(d^2-4/25)*sqrt(4sqrt(d^2-4/25)-7)]>10/7,

using 4d-7<=47/25<49/25. Thus W'>0.

At d=111/50, the alpha term is strictly below 2/5 because
sqrt(8321)>91. Also

    sqrt(d^2-4/25)<219/100,
    epsilon<19/100,
    ell(epsilon)<1/3,

the last inequality following from 1+4(19/100)=44/25<16/9.
Therefore ET13-ET14 and monotonicity give

    alpha+ell<=W(d)<2/5+1/3=11/15.                    (ET15)

The three cases prove ET1.

### 4. The endpoint angle lies strictly later

The alternating Taylor lower bound for cosine at 11/15 gives

    cos(11/15)
       >=1-(11/15)^2/2+(11/15)^4/24-(11/15)^6/720
        =6093080189/8201250000
        >37/50.

The exact final gap is 24155189/8201250000>0. This proves ET2.

### 5. The resulting right endpoint estimate

The independently audited positive-corner confinement theorem implies
that any positive active angle at x=C uses its first wall with strict
companion slack. Its angular stationarity therefore gives B_x(t)=C.
The actual first source point is B+mu and lies at horizontal coordinate
at most 2C. Consequently cos(t)<=C and t>=acos C.

If the top endpoint is b=C+T, the exact backward support formula is

    R_t(C)=T cot t
        +(1/sin t) integral_t^L sin(s-t)(u(s)-1) ds.

By ET1-ET2 the integral is nonpositive at every possible positive
endpoint-active angle. Hence

    n(C)<=[C/sqrt(1-C^2)]T.                            (ET16)

Separately, for the positive first-wall intercept R0(t)=(f(t)-1)/cos t,
the same support formula gives

    R0(t)<=b+J_f,
    J_f:=integral_0^L (u(s)-1)_+ sin s ds.              (ET17)

Indeed sin(s-t)/cos t=sin s-cos s tan t<=sin s. Since the niche
is convex on the right wing and vanishes once every first wall does,

    integral_C^(2C) n <=(T+J_f)n(C)/2.                 (ET18)

If b+J_f exceeds the cap endpoint, using its larger width only weakens
the bound. ET16-ET18 are genuine endpoint and area bounds; they do not
identify limiting exposure with full graph arclength.

### 6. A uniform small exterior-leakage moment

The three cases above give epsilon<19/100 and ell<1/3 whenever excess occurs. Integrating ET3 gives

    integral (u-1)_+ <= ell^2/4+ell^3/6 <11/324.

All such angles are below 11/15, so sin(t)<11/15. Therefore

    J_f < (11/15)(11/324)=121/4860<1/40.               (ET19)

This is an exact integral bound for the proved quadratic envelope, not an angular sampling estimate.

---

<a id="proof-reflected-projection"></a>
## Technical proof 28. Reflected tail and exact zero-height projection (RT)

Written proof, independently checked within this research session, October 10, 2026. This applies to every remaining
canonical tilted spatial global maximizer with

    2/3<=C<37/50, 0<h<17/50,
    I=[-2C,2C], J=[-C,C], A(-C)=1-h, A(C)=1,
    top=[C,b], T=b-C>=0.

Neither full regular wing is assumed unit-bounded. The inputs are the
established regularity/arm/source bounds, positive endpoint pressures,
the exact box estimate H(C)<1/3, and the EP finite source projection.

The dependencies are the [endpoint source identities](#proof-full-endpoints),
[spatial regularity and arm bounds](#proof-full-curvature),
[positive pressures](#proof-full-pressures),
[first-wing structural notation](#proof-first-wing-structure), and
[forward excess estimate](#proof-early-excess).

The conclusion is

    T>0, n_U(-C)=0,
    T=C+x_zero,

where x_zero is the unique zero of the low-wing second-wall envelope.

### 1. The global middle projection requires no unit-curvature hypothesis

Use the first support f and low-left-wing surrogate g from the tilted
notes, and put L=pi/2. Their proper-angle inner walls are

    R_t(x)=(f(t)-1-x cos t)/sin t,
    S_t(x)=(g(t)-1+x sin t)/cos t.

On J, the actual extra high-top-point second wall is nonpositive. Thus
positive niche agrees with the surrogate construction on J.

Let x1=1-2C and F(x)=sup_(0<t<L) S_t(x). Exactly as in the first-good
structural addendum, the support of the low wing gives F finite, convex
and nondecreasing for x<x1. Its endpoint-angle limits are -h at t=0 and
minus infinity at t=L. It is negative for x<=-2C, and its limiting
t=L value at x1 is eL>0. Hence it has a unique zero x_zero<x1, with
strictly negative values to the left and strictly positive values to the
right. Uniqueness follows because a zero is attained at an interior
angle whose affine wall has strictly positive slope.

The pinned high point (C,1) gives f(t)>=C cos t+sin t. Consequently, for
every x<=x1 and every proper angle,

    f(t)-1-x cos t
       >=(3C-1)cos t+sin t-1
       >=cos t+sin t-1>0.                              (RT.1)

Thus every first wall is positive on x<=x1. For x1<x<C, angles approaching
L also give positive niche, because b>=C>x and

    R_t(x)=(b-x)(L-t)+o(L-t)>0,
    S_t(x)->+infinity.

It follows that the exact positive projection in the interior of J is

    {x in (-C,C):n_U(x)>0}
       =(max(-C,x_zero),C).                            (RT.2)

There is no claim about the full positive interval to the right of J;
first-wing excess may produce additional exterior leakage there.

On a compact interval inside J and strictly left of x_zero, all surrogate
second walls are uniformly negative. The extra high-point wall is also
strictly negative when its angle is bounded away from zero. Thus finite
positive graph on that compact interval can use only arbitrarily small
endpoint-angle neighborhoods. EP.22 makes their total source mass and
horizontal projection O(angle cutoff)+o_n(1). On compact subsets of the
positive interval RT.2, uniform convergence supplies the converse bound.

The exact EP horizontal moment therefore gives

    2C-T=integral_0^L(u sin t+v cos t)dt
         =lim_n |{x in J_n:n_n(x)>0}|
         =C-max(-C,x_zero).

Equivalently,

    T=(C+x_zero)_+.                                    (RT.3)

This proof uses no unit bound on u or v. In particular, T>0 will imply
x_zero>-C and n_U(-C)=0. It remains to rule out T=0.

### 2. Reflected arm variables when T=0

Assume T=0, so b=C. Reflect the parameter by r=L-t and define

    p_tilde(r)=-q(t), q_tilde(r)=-p(t),
    u_tilde(r)=v(t), v_tilde(r)=u(t), d=3C.

Before the reflected central normal, these obey the same equations and
sharp spatial arm estimates as the original pair:

    p_tilde'=u_tilde-1-q_tilde,
    q_tilde'=v_tilde-1+p_tilde,
    p_tilde(0)=eL, q_tilde(0)=d-1.                    (RT.4)

After the reflected central normal, the first density u_tilde=v is
identically zero because it comes from the low-wing surrogate's initial
point-supported interval. Thus an excess estimate only needs to cover
the initial regular interval; any terminal central atom is harmless.

Write e=eL. The actual endpoint law and the box bounds give

    e=1/2-3h/4+(3n_- -n_+)/4,
    3/20<1/2-3(17/50)/4-1/12<e<3/4.                 (RT.5)

The displayed middle rational equals 97/600, which exceeds 3/20. The
upper bound follows from n_-<1/3 and h,n_+>=0.

As in the forward excess estimate, every possible u_tilde>1 belongs to
the initial positive-q_tilde component after its first p_tilde=0 time
alpha. If there is no such crossing before the terminal central normal,
there is no excess. Later positive components have q_tilde<=1/8 and do
not generate excess.

On the initial (++), u_tilde=0, v_tilde<=1/2, and the energy
(p_tilde-1/2)^2+(q_tilde+1)^2 is nonincreasing. At alpha it gives

    (q_tilde(alpha)+1)^2<=d^2-e(1-e).                  (RT.6)

Also q_tilde'>=-1 and p_tilde'<=-d+r before alpha. Therefore

    alpha<=d-sqrt(d^2-2e).                            (RT.7)

The bound applies unless the positive component ends or the terminal
central normal arrives first, either of which removes any prospective
excess. Its right side decreases with d and increases with e.

Put eta_ex=(q_tilde(alpha)-1)_+. The universal quadratic arm envelope is

    (u_tilde(alpha+s)-1)_+
        <=[eta_ex-s/2-s^2/4]_+,

so when eta_ex<3/4 all excess ends within

    ell(eta_ex)=sqrt(1+4 eta_ex)-1                     (RT.8)

of alpha. This is the same pointwise envelope as ET3-ET4.

### 3. An exact two-case bound for the reflected excess end time

First suppose e<=2/3. From e>=3/20 and e<=2/3,
e(1-e)>=51/400. Using d<111/50 in RT.6 gives

    (q_tilde(alpha)+1)^2
       <(111/50)^2-51/400=48009/10000<(11/5)^2.

Hence eta_ex<1/5 and ell<7/20, since 9/5<(27/20)^2. Equation RT.7 gives

    alpha<=2-sqrt(8/3)<3/8,
    alpha+ell<3/8+7/20=29/40<11/15.                  (RT.9)

The radical comparison for alpha is 8/3>(13/8)^2.

Now suppose 2/3<=e<3/4. Here e(1-e)>=3/16. Therefore

    (q_tilde(alpha)+1)^2
       <(111/50)^2-3/16=47409/10000<(109/50)^2.

Thus eta_ex<9/50 and ell<5/16, since 43/25<(21/16)^2. Also

    alpha<=2-sqrt(5/2)<21/50,
    alpha+ell<21/50+5/16=293/400<11/15.               (RT.10)

The radical comparison here is 5/2>(79/50)^2. These are all exact rational
comparisons. The two cases prove

    u_tilde(r)<=1 for a.e. r>=11/15,
    v(t)<=1 whenever L-t>=11/15.                     (RT.11)

The already checked alternating cosine estimate gives

    cos(11/15)>37/50,
    11/15<acos C.                                    (RT.12)

### 4. The zero-overhang hypothesis makes the low endpoint strictly dry

Suppose F(-C)>=0. Since S_t(-C)->-h at t=0 and tends to minus infinity
at t=L (because C<1), its nonnegative maximum is attained at a proper
angle t. Regularity of g gives the stationary equation

    0=partial_t S_t(-C)=(-C-D_x(t))/cos^2 t,
    D_x(t)=-C.

If X is the horizontal coordinate of the supporting low-wing point,
D_x=X+sin t and X>=-2C. Consequently sin t<=C, or

    L-t>=acos C>11/15.

By RT.11, the entire original prefix [0,t] has v<=1. The exact support
formula from g(0)=1-h and g'(0)=C is

    g(t)=(1-h)cos t+C sin t
              +integral_0^t v(s)sin(t-s)ds.

It follows that

    S_t(-C)
       =1-h-sec t+(1/cos t)integral_0^t v(s)sin(t-s)ds
       <=1-h-sec t+(1-cos t)/cos t=-h<0.

This contradicts the assumed nonnegative maximum. Therefore F(-C)<0,
so x_zero>-C. But RT.3 with T=0 requires x_zero<=-C. The contradiction
excludes zero top overhang.

**Conclusion.** Every remaining tilted global maximizer with
2/3<=C<37/50 has T>0, x_zero=-C+T, and n_U(-C)=0, without requiring
either entire wing to have unit curvature.

### 5. Two exact support-point bounds for the overhang

The left outer endpoint (-2C,eL) lies in the cap, so
g(t)>=2C sin t+eL cos t. At the proper angle
cos t=eL, sin t=sqrt(1-eL^2), its second wall at
x=-2C+sqrt(1-eL^2) is nonnegative. This x is strictly below x1,
where F has its unique zero. Hence

    T<=sqrt(1-eL^2)-C.                                (RT.13)

In particular T>0 implies eL<sqrt(1-C^2).

The pinned low point (-C,1-h) gives instead
g(t)>=C sin t+(1-h)cos t. At cos t=1-h and
sin t=sqrt(h(2-h)), its second wall is nonnegative at
x=-C+sqrt(h(2-h)). If this x is below x1, the same zero comparison
applies; if it is at or above x1, x_zero<x1 gives the comparison
directly. Therefore

    T<=sqrt(h(2-h)).                                  (RT.14)

Combining these with x_zero<x1 gives the convenient summary

    0<T<=min{sqrt(h(2-h)),sqrt(1-eL^2)-C},
    T<1-C.                                           (RT.15)

These are pure support-point comparisons; they require no curvature or
visibility statement beyond the already established projection formula.
Together with the independently proved forward terminal-unit bound
z=n_U(C)<=lambda T, lambda=C/sqrt(1-C^2), they give

    z<=lambda sqrt(h(2-h)),
    (C+z/lambda)^2+(1/2-3h/4-z/4)^2<=1.              (RT.16)

The second inequality follows from RT.13 and the actual pressure law
eL=1/2-3h/4-z/4; all quantities before squaring are nonnegative.

This is a dependency of the [completed Gate 1 proof](#proof-full-closure).
The written argument has not been externally refereed or formalized in Lean.

---

<a id="proof-final-height"></a>
## Technical proof 29. The final tilted height reduction (FR)

Written proof, independently checked within this research session, October 10, 2026. This combines the
accepted full-triangle estimate with the now accepted global projection
`T>0, n(-C)=0`. It sharpens only the positive-floor loss in the earlier
three-angle proof. No new niche region, stationarity assumption, or angle
discretization is introduced.

The global projection is proved in [RT](#proof-reflected-projection).
The sufficient curvature criterion and its earlier high-tilt strip are proved in
[IE](#proof-initial-energy), and the resulting first-unit branch is
excluded by [GF](#proof-first-unit).

### 1. Statement and hypotheses

Consider a remaining canonical tilted maximizer. All the already proved
reductions give

    2/3<C<37/50,     0<h<21/100,
    I=[-2C,2C],     J=[-C,C],
    A(-C)=1-h,      A(C)=1,
    n(-C)=0.

Write z=n(C), e_R=A(2C), e_L=A(-2C), and

    H(C)=1-sqrt(1-C^2),
    0<=z<=H(C),
    e_R=1/2+h/4+3z/4,
    e_L=1/2-3h/4-z/4.                                  (FR1)

The endpoint identities are the actual endpoint pressure laws, and n is
the ambient, full continuous-angle positive niche. The accepted
first-good theorem excludes every such maximizer for which the first
regular wing density is at most one. The accepted initial-floor energy
test supplies that conclusion whenever, with d=3C,

    B=-1/2+5h/4+3z/4,
    s_h=sqrt(h(2-h)),
    d^2+B^2<=5,
    d^2+B^2+B(1-h)-d s_h<=4.                            (FR2)

Then every remaining canonical maximizer satisfies

    h<1/20.                                             (FR3)

The proof splits at C=73/100. Below that value (FR2) holds whenever
h>=1/20. Above it, the actual full-triangle upper bound is strictly less
than 41/50, itself below the candidate lower bound for P.

### 2. An exact first-good strip below C=73/100

Suppose

    2/3<C<=73/100,     1/20<=h<=21/100.

The box bound gives H(C)<8/25, since
1-(73/100)^2>(17/25)^2. Therefore

    -1/2+5h/4 <= B <= -13/50+5h/4,
    -7/16 <= B <= 1/400.

The radius condition in (FR2) follows immediately:

    d^2+B^2
      <=(219/100)^2+(7/16)^2
       =798001/160000
       =5-1999/160000 <5.                               (FR4)

Set Q(d,B,h)=d^2+B^2+B(1-h)-d sqrt(h(2-h)). Its derivative in B
on the actual allowed interval obeys

    Q_B=2B+1-h >=3h/2>0.

Its derivative in d is 2d-s_h>0. Thus it is enough to bound

    Q(219/100,-13/50+5h/4,h).

This expression is convex in h. The polynomial part has quadratic
coefficient 5/16, and -sqrt(h(2-h)) is convex. Its maximum on the
displayed interval occurs at an endpoint. At h=1/20 use s_h>31/100;
at h=21/100 use s_h>61/100. These elementary square-root bounds give

    Q(219/100,-79/400,1/20)
      <634973/160000=4-5027/160000,

    Q(219/100,1/400,21/100)
      <553949/160000=4-86051/160000.                      (FR5)

Both conditions (FR2) hold throughout this strip. The accepted general
first-good theorem excludes it.

### 3. The improved full-triangle positive-floor loss

It remains to exclude

    73/100<=C<37/50,     1/20<=h<=21/100.                (FR6)

Use all notation and the exact niche/exterior payments of the accepted
[full-triangle width theorem](#proof-full-triangle) (FT4--FT17). In particular set

    a=2C, r=sqrt(2), k=r-1, c=cos(pi/8),
    A_0=1-k, b=2-k, d_0=3r-1,
    gamma=1-r/2, t_0=2c-r.

The subscript on A_0 and d_0 here merely distinguishes these scalar
constants from the roof and from d=3C in (FR2). Let u,v be the lifted
45-degree support parameters, and let

    w_R=a-u,     w_L=a-v+h.

Exactly as in FT9, support containment at the actual endpoints gives
w_R<=1-e_R and w_L<=1-e_L. The stronger endpoint information (FR1)
therefore yields

    w_R<=1/2-h/4,
    w_L<=1/2+3h/4+z/4
        <7/12+3h/4.                                    (FR7)

Here H(C)<1/3 for C<37/50. The exact floor-loss inequality FT13 bounds
the discarded negative-baseline portions by

    gamma[(w_R-t_0)_+^2+(w_L-t_0)_+^2].

Consequently the complete actual-niche estimate becomes

    P<=G_h(a,u,v)+L_asym(h),

    L_asym(h)=gamma[(D-h/4)_+^2+(D+1/12+3h/4)_+^2],
    D=1/2-t_0.                                         (FR8)

G_h is precisely the jointly concave clipped function in FT17; it is
unchanged. Thus this refinement does not replace any actual support
by a surrogate niche and does not drop any clipping term.

For completeness, all geometric range checks in FT4--FT17 still hold
on (FR6), although its left width endpoint is slightly smaller:

* The 45-degree apex has positive height and lies in J, since
  C-h/2-k>=73/100-21/200-k>0 and h<C.
* The endpoint sum E=e_R+e_L>=1-h/2 gives
  M-h/2>=a-1/2-h/4>=363/400>179/200, where M=(u+v)/2.
  This is stronger than the lower bound used for both strict
  crossover inequalities FT11.
* The outer gain-triangle zeros still lie in J: C<37/50<4/5 is
  within the original FT12 range.

The exterior and full niche triangles are therefore exactly the
previously audited disjoint regions. Their Cauchy payment remains
unchanged.

### 4. A support critical point at a=73/50

Write

    a_*=73/50,
    B_0(a)=a-(a-k)^2/2,
    s_0(a)=d_0 a/2-(4c-2).

The completion of squares FT18 shows that the support critical point
at a=a_* is u_*=v_*, with

    u_*=(a_*+k)/2+(b/9)[s_0(a_*)-A_0h/4]+h/4.

It is interior, unclipped, and has S>0 for every h in [1/20,21/100].
Here are direct checks, using the same radical bounds as FT20:

    140/99<r<99/70,     923/1000<c<231/250.

They give 2/3<s_0(a_*)<7/10. Hence
s_0(a_*)-A_0h/4>2/3-(3/5)(21/400)>0. The right clipping
quantity has the form

    -k/2+(b/9)s_0(a_*)+(1/4-b A_0/36)h.

It is strictly smaller than the negative upper bound in FT21, because
s_0(a_*)<71/100 and h<=21/100<17/50. The left clipping
quantity is smaller by h. The lower support bound follows from the
positive bracket, and the strict clipping bound also gives
u_*<a_*/2+k<a_*.

The value at this actual critical point is

    K(a_*,h)=B_0(a_*)-kh/2-h^2/8
             -(2/9)[s_0(a_*)-A_0h/4]^2.                 (FR9)

Its partial derivative in a is

    r-a_*-(2d_0/9)[s_0(a_*)-A_0h/4]<0.

Thus the joint supporting-plane argument FT23--FT24 applies without
change and gives

    G_h(a,u,v)<=K(a_*,h)       for every a>=a_*.          (FR10)

This covers every possible 45-degree clipping pattern in (FR6).

### 5. The scalar bound decreases in h and is below 41/50

On the entire tilt interval in (FR6), the positive parts in (FR8) are
positive. Indeed the displayed radical bounds give

    1/2-2(231/250)+140/99 < D < 239/3500,

and the lower expression is greater than 21/400. We can therefore
expand (FR8) as an ordinary quadratic. The linear coefficient of
K(a_*,h)+L_asym(h) is

    ell=-k/2+A_0 s_0(a_*)/9+gamma(D+1/8).

Using k>2/5, A_0<3/5, gamma<3/10, s_0(a_*)<7/10 and
D<239/3500 yields

    ell<-1/5+(3/5)(7/10)/9
                +(3/10)(239/3500+1/8)<-9/100.

The quadratic coefficient is the same as in FT25:

    q=-1/8-A_0^2/72+5gamma/8<1/16.

The total derivative is therefore less than
-9/100+h/8<=-9/100+21/800<0. The bound is largest at h=1/20.

At that endpoint,

    s_0(a_*)-A_0/80
      >43789/66000>53/80.                               (FR11)

Also D-1/80<7/125 and D+1/12+3/80<19/100, so

    L_asym(1/20)
      <(3/10)[(7/125)^2+(19/100)^2]
       =29427/2500000<3/250.                            (FR12)

Finally B_0(a_*)=(123/50)k-529/5000. Using k<29/70 for its
positive coefficient and k>41/99 for the negative tilt term gives

    P <(123/50)(29/70)-529/5000-41/3960-1/3200
          -(2/9)(53/80)^2+3/250
       =7550393/9240000
       =41/50-26407/9240000 <41/50.                     (FR13)

Thus (FR6) is impossible for a maximizer with P at least the known
candidate value. Together with (FR4)--(FR5), this proves (FR3).

#### Provenance of the initial bound h<21/100

The controlling repository note
`docs/ambidextrous/gate1-tilted-initial-floor-energy.md`, IE8, already
contains the following independently audited corollary. On
C<=37/50 and 21/100<=h<=17/50, the box bounds give
-107/400<=B<=69/400. Thus

    d^2+B^2<=(111/50)^2+(107/400)^2
             =799993/160000=5-7/160000<5.

The energy expression Q increases in B because 2B+1-h>=1/8.
At its affine upper endpoint B=-101/400+5h/4 and d=111/50 it is
convex in h. Its upper bounds at h=21/100 and h=17/50 are,
respectively, 17911/5000 and 545121/160000, both less than four;
these use sqrt(h(2-h))>61/100 and >3/4. Hence the general
first-good theorem excludes this whole strip. This is the h<21/100
input in Section 1, and completes its provenance even for a reader
using only the scratch drafts.

The [small-height theorem](#proof-small-height) excludes the entire
remaining h<1/20 range. The [Gate 1 closure](#proof-full-closure)
records the full domain coverage. The fixed rational comparisons are reproduced by
[the exact certificate checker](#verification-record).

---

<a id="proof-small-height"></a>
## Technical proof 30. The last small-height alternatives (SH)

Written proof, independently checked within this research session, October 10, 2026. This combines the initial
floor-energy criterion with the actual ordinary-area lower bound. It uses
no sampled optimization or assumed contact chart. Every displayed final
certificate is rational.

### 1. Statement and dependencies

Let U be the selected canonical global maximizer of the actual spatial
one-cap objective P, with

\[
I=[-2C,2C],\qquad J=[-C,C],\qquad
A(-C)=1-h,\quad A(C)=1,
\]

\[
\frac23<C<\frac{37}{50},\qquad
0<h\le\frac{509}{10000}.
\tag{SH1}
\]

Then U cannot exist.

The established ingredients used below are:

* The endpoint pressures, regularity, and stationary identity
  \(2P=L_{\rm wing}\).
* The positive-corner confinement and genuine ordinary one-turn
  feasibility theorem in
  [CG](#proof-corner-confinement).
* The reflected terminal-unit and projection theorem in
  [RT](#proof-reflected-projection). In the current
  width range it gives positive top overhang and zero left endpoint
  niche, without either global unit-curvature assumption.
* The early-end theorem and endpoint estimates ET1--ET18 in
  [ET](#proof-early-excess).
* The initial floor-energy criterion IE1--IE2 in
  [IE](#proof-initial-energy).
* The general first-good exclusion in
  [GF](#proof-first-unit).

The ordinary one-turn bound remains the already recorded exact enclosure

\[
|\mathcal S|\le G_0:=\frac{22199}{10000}.
\tag{SH2}
\]

Here \(\mathcal S=U\setminus N(U)\) is the genuine connected one-turn body
supplied by the confinement theorem. No equality between U and the convex
hull of \(\mathcal S\) is required.

### 2. Exact endpoint and leakage information

Write the top face as \([C,C+T]\times\{1\}\), and put

\[
z=n_U(C),\qquad s=\sqrt{h(2-h)},\qquad
K=\frac{C}{\sqrt{1-C^2}},\qquad
J_f=\int_0^{\pi/2}(u(t)-1)_+\sin t\,dt.
\]

The projection theorem and the actual pressure equations give

\[
T>0,\quad n_U(-C)=0,
\]

\[
e_R=\frac12+\frac h4+\frac{3z}{4},\qquad
e_L=\frac12-\frac{3h}{4}-\frac z4.
\tag{SH3}
\]

The pinned low middle point and the endpoint estimate ET16 imply

\[
T\le s,\qquad 0\le z\le KT,\qquad K<\frac{10}{9}.
\tag{SH4}
\]

For completeness, the first inequality follows from the signed second
wall envelope at its zero \(x_{\rm zero}=-C+T\). The low middle point
\((-C,1-h)\) gives the lower wall
\(1-h-\sec t+T\tan t\). Its value at \(\sin t=T\) is
\(1-h-\sqrt{1-T^2}\), and cannot be positive at an envelope zero.
Thus \(T^2\le h(2-h)\). We have \(T\le C<1\), so this angle is
proper. The bound on K follows by squaring and using
\(81\cdot1369<100\cdot1131\).

The ordinary box estimate also gives

\[
z\le1-\sqrt{1-C^2}<\frac{33}{100}.
\tag{SH5}
\]

The early-end proof bounds all possible first-source excess by one
initial envelope

\[
(u(\alpha+\tau)-1)_+
\le\left(\varepsilon-\frac\tau2-\frac{\tau^2}{4}\right)_+,
\qquad \varepsilon<\frac{19}{100}<\frac7{36}.
\]

Its duration is less than \(1/3\), and all excess occurs at angles
less than \(11/15\). Since the parabola with initial value \(7/36\)
vanishes at \(1/3\),

\[
\int(u-1)_+\,dt
<\int_0^{1/3}\left(\frac7{36}-\frac\tau2-\frac{\tau^2}{4}\right)d\tau
=\frac{11}{324}.
\]

Consequently

\[
J_f<\frac{11}{15}\frac{11}{324}
=\frac{121}{4860}<\frac1{40};
\qquad \frac1{40}-\frac{121}{4860}=\frac1{9720}.
\tag{SH6}
\]

ET17--ET18 and convexity of the actual niche on the right wing give

\[
N_{\rm out}\le\frac{(T+J_f)z}{2}.
\tag{SH7}
\]

The left wing contributes no outside niche: its niche roof is convex
with zero values at both endpoints. The middle cap area is \(2C-Ch\).
Thus

\[
|\mathcal S|\ge P+C(2-h)-\frac{(T+J_f)z}{2}.
\tag{SH8}
\]

### 3. A common tangent lower bound for the wing lengths

Define the fixed constants

\[
C_0=\frac{\sqrt{17}}6,\quad
R_0=\frac{\sqrt{26}}6,\quad
S_0=2C_0+R_0,
\]

\[
\lambda=\sqrt{\frac{17}{26}},\qquad
m=\frac{3}{4\sqrt{26}},\qquad
a=\frac{1-\lambda}{2}.
\tag{SH9}
\]

The two charged-wing vertical drops are

\[
r_R=1-e_R=\frac12-\frac h4-\frac{3z}{4},\qquad
r_L=1-h-e_L=\frac12-\frac h4+\frac z4.
\]

They are nonnegative by the actual cap geometry. The top overhang has
length T, while the nonhorizontal right wing has horizontal displacement
\(C-T\). The stationary length identity and the two chord bounds yield

\[
P\ge\frac12\left[T+
\sqrt{(C-T)^2+r_R^2}+\sqrt{C^2+r_L^2}\right].
\tag{SH10}
\]

The tangent inequality for the Euclidean norm at \((C_0,1/2)\) is

\[
\sqrt{x^2+y^2}\ge\lambda x+\frac{3}{\sqrt{26}}y.
\]

Apply it to the two chords in SH10, and use
\(\lambda C_0+3/(2\sqrt{26})=R_0\). Combining with SH8 gives

\[
|\mathcal S|\ge S_0+(2+\lambda)(C-C_0)
-Ch-m(h+z)+aT-\frac{(T+J_f)z}{2}.
\tag{SH11}
\]

The following rational enclosures follow by squaring positive numbers:

\[
\frac{8086}{10000}<\lambda<\frac{8087}{10000},\qquad
m<\frac{1471}{10000},\qquad a>\frac{956}{10000}.
\tag{SH12}
\]

Since SH4 implies \(T\ge9z/10\), SH6 and SH12 imply

\[
-mz+aT-\frac{J_fz}{2}\ge-\frac{1839}{25000}z.
\]

Here

\[
\frac{1471}{10000}+\frac1{80}
-\frac{956}{10000}\frac9{10}
=\frac{1839}{25000}.
\]

In particular the useful common lower bound is

\[
|\mathcal S|\ge S_0+(2+\lambda)(C-C_0)
-\frac{8871}{10000}h-\frac{1839}{25000}z-\frac{Tz}{2}.
\tag{SH13}
\]

Finally

\[
S_0>\frac{2\cdot4123+5099}{6000}
=\frac{2669}{1200}>G_0,
\quad \frac{2669}{1200}-G_0=\frac{16}{3750}.
\tag{SH14}
\]

The radical comparisons here are
\((4123/1000)^2<17\) and \((5099/1000)^2<26\).

### 4. Failure of the second initial-energy inequality is impossible

Put

\[
d=3C,\qquad B=e_R-1+h=-\frac12+\frac{5h+3z}{4}.
\]

The second initial-floor criterion is

\[
Q:=d^2+B^2+B(1-h)-ds\le4.
\]

Suppose it fails. The exact square completion is

\[
Q=\left(3C-\frac s2\right)^2
+\frac9{16}(h+z)^2-\frac14,
\]

so

\[
\left(3C-\frac s2\right)^2
+\frac9{16}(h+z)^2>\frac{17}{4}.
\tag{SH15}
\]

Write \(w=h+z\). SH1 and SH5 give \(w<2/3\), and
\(3C-s/2>0\). Rationalizing the difference of the two positive
square roots gives

\[
\frac{\sqrt{17}}2-
\sqrt{\frac{17}{4}-\frac9{16}w^2}
=\frac{9w^2/16}{\sqrt{17}/2+
\sqrt{17/4-9w^2/16}}
<\frac9{64}w^2.
\]

The denominator exceeds four because \(w<2/3\). Therefore SH15
implies

\[
C-C_0>\frac s6-\frac3{64}(h+z)^2.
\tag{SH16}
\]

Insert SH16 into SH13. Use the lower enclosure for \(\lambda\) on
the positive s term, its upper enclosure on the negative squared term,
and SH4 on all occurrences of z and T. The result is

\[
|\mathcal S|-S_0\ge
\frac{57955}{150000}s
-\frac{8871}{10000}h-\frac59s^2
-\frac{84261}{640000}
\left(h+\frac{10}{9}s\right)^2.
\tag{SH17}
\]

The linear coefficient is exactly

\[
\frac{2+8086/10000}{6}
-\left(\frac{1471}{10000}+\frac1{80}
-\frac{956}{10000}\frac9{10}\right)\frac{10}{9}
=\frac{11591}{30000}=\frac{57955}{150000}.
\]

Here is a complete rational positivity certificate for SH17. Set

\[
A=\frac{11591}{30000},\quad
D=\frac{8871}{10000},\quad
Q_0=\frac{84261}{640000},\quad
k=\frac{10000}{19491},\quad s_* =\frac{63}{200}.
\]

Since \(h\le509/10000\),

\[
h\le ks^2,\qquad 0<s<s_*.
\]

Indeed \(s^2=h(2-h)\ge(19491/10000)h\), and

\[
s_*^2-\frac{509}{10000}\frac{19491}{10000}
=\frac{1581}{100000000}>0.
\]

The right side of SH17 is consequently at least

\[
s\left[A-\left(Dk+\frac59\right)s
-Q_0s\left(\frac{10}{9}+ks\right)^2\right].
\]

The bracket decreases for \(s\ge0\). Its value at \(s_*\) is
exactly

\[
A-\left(Dk+\frac59\right)s_*
-Q_0s_*\left(\frac{10}{9}+ks_*\right)^2
=\frac{11102231813}{13507522880000}>0.
\tag{SH18}
\]

Thus \(|\mathcal S|>S_0>G_0\), contradicting SH2. Failure of
IE2 is impossible on SH1.

### 5. Failure of the first initial-energy inequality is impossible

Suppose instead that

\[
9C^2+B^2>5.
\tag{SH19}
\]

Write \(\xi=(5h+3z)/4\), so \(B=-1/2+\xi\).
SH1 and SH5 imply \(0<\xi<1/2\), hence \(-1/2<B<0\).
It follows from SH19 that

\[
C>\frac{\sqrt{19}}6>\frac{29}{40}.
\tag{SH20}
\]

Also

\[
B^2>5-9\left(\frac{37}{50}\right)^2
=\frac{179}{2500}>\frac{16}{225}.
\]

The last gap is \(11/22500\). Since B is negative,

\[
B<-\frac4{15},\qquad \xi<\frac7{30}.
\tag{SH21}
\]

These inequalities give a useful improved endpoint bound

\[
z<\frac{27}{100}.
\tag{SH22}
\]

To verify it, if \(h\le1/40\), then
\(s<9/40\) and SH4 gives \(z<1/4\).
If \(h\ge1/40\), then
\(\xi\ge1/32+3z/4\); SH21 therefore gives
\(z<97/360<27/100\).

Use SH20 together with \(C_0<11/16\),
\(2+\lambda>14/5\), and SH14. Since the width difference is positive,

\[
S_0+(2+\lambda)(C-C_0)
>\frac{2669}{1200}+\frac{14}{5}
\left(\frac{29}{40}-\frac{11}{16}\right)
=\frac{559}{240}.
\]

Finally \(T\le s<63/200\). Substituting this, SH1 and SH22 into
SH13 gives

\[
\begin{aligned}
|\mathcal S|
&>\frac{559}{240}
-\frac{8871}{10000}\frac{509}{10000}
-\left(\frac{1839}{25000}+\frac{63}{400}\right)
\frac{27}{100}\\
&=\frac{666488123}{300000000}.
\end{aligned}
\tag{SH23}
\]

Its exact margin over the ordinary bound is

\[
\frac{666488123}{300000000}-G_0
=\frac{518123}{300000000}>0.
\tag{SH24}
\]

This contradicts SH2 and excludes failure of IE1 throughout the same
height range as Section 4.

### 6. Conclusion

If both initial-floor inequalities hold, IE gives \(u\le1\) on the
whole first quarter, and the general first-good theorem excludes the
tilted global maximizer. Sections 4 and 5 exclude failure of either
inequality. Therefore every cap satisfying SH1 is impossible.

This is an actual selected-maximizer branch exclusion. It does not assert
the global first-quarter curvature bound for larger tilts, and it does
not by itself settle Gate 1.

Together with the [final height reduction](#proof-final-height),
this closes every remaining tilted canonical maximizer. See the
[complete Gate 1 theorem](#proof-full-closure) for the global implication.
[The fixed Fraction checker](#verification-record)
reproduces the rational certificates without sampling or optimization.

---

<a id="proof-full-closure"></a>
## Technical proof 31. Full-turn assembly and explicit external input record (G1C)

### 1. Exact statements

Let

\[
M=1+4Y^2+\arctan Y,
\qquad 4Y^3+3Y-1=0,\quad Y>0.
\tag{G1C.1}
\]

For a nonempty compact downward convex cap
\(U\subset\mathbb R\times[0,1]\), write its horizontal projection as
\(I=[l,r]\), its roof as \(A_U\), its width as \(W=r-l\), and set

\[
J=[l+W/4,r-W/4].
\]

The positive ambient niche is the full two-attached-wall envelope

\[
n_U(x)=\left[\sup_{0<t<\pi/2}
\min\left\{
\frac{h_U(\cos t,\sin t)-1-x\cos t}{\sin t},
\frac{h_U(-\sin t,\cos t)-1+x\sin t}{\cos t}
\right\}\right]_+.
\tag{G1C.2}
\]

Define

\[
\mathcal P(U)=\int_{I\setminus J}A_U(x)\,dx
-\int_J n_U(x)\,dx.
\tag{G1C.3}
\]

**Theorem G1C1 (SD.3, sharp scalar value).** Every such cap satisfies

\[
\boxed{\mathcal P(U)\le M/2.}
\tag{G1C.4}
\]

The supremum equals \(M/2\), attained by Romik's reference cap. The
statement includes caps of height below one, arbitrary asymmetry,
nonsmooth boundaries, unbounded polygon complexity, and caps whose
ordinary one-turn survivor is not known to be connected or feasible.
A zero-width cap has score zero and is immediate.

**Theorem G1C2 (Gate 1, sharp full-turn value).** Every compact connected
body that can make both complete conventional quarter turns through the
two unit right-angle corridors, from a common incoming orientation, has

\[
\boxed{|S|\le M.}
\tag{G1C.5}
\]

Romik's construction attains equality. The same upper bound holds for
the signed full-turn envelope functional on every auxiliary convex hull
in Gate 0's domain. This last assertion concerns the signed integral;
it does not identify that integral with ordinary area when an auxiliary
hull has empty survivor fibers.

### 2. The global maximizer reduction

The proofs in [SD](#proof-full-domain) and
[MID](#proof-middle-chord) apply to the entire
cap domain of G1C1. Vertical Minkowski extrusion to height one cannot
decrease \(\mathcal P\): it raises each charged exterior roof by the
extrusion amount, and raises each positive middle niche roof by at most
that amount. The two regions have equal horizontal measure.

The actual 45-degree two-wall niche gives width coercivity, and the
whole-angle niche is continuous under Hausdorff convergence. Consequently
the scalar maximum is attained by a height-one cap with \(8/5<W<6\).
Replacing its uncharged middle roof by its chord and then saturating the
height preserves global maximality and makes the entire middle roof
affine. The polygon selections used for regularity target this chosen
maximizer, rather than a different finite optimizer.

The reference score is \(M/2\), and \(M/2>41/50\). This strict rational
comparison needs no decimal approximation: if \(a=297/1000\), then
\(4a^3+3a<1\), so \(Y>a\), while

\[
M>1+4a^2+a-a^3/3
=\frac{1641103309}{1000000000}>\frac{41}{25}.
\tag{G1C.6}
\]

Here \(\arctan a\ge a-a^3/3\) follows by integrating
\(1/(1+t^2)\ge1-t^2\).

The [regularity theorem](#proof-prescribed-regularity),
[facet-pinning theorem](#proof-facet-pinning),
[endpoint complementarity](#proof-full-endpoints), and
[positive-pressure theorem](#proof-full-pressures)
then apply to the canonical global maximizer. They prove bounded regular
wing curvature, the necessary corner locations, positive endpoint
pressures, exact limiting finite-source balances, and

\[
2\mathcal P=L_{\mathrm{wing}}.
\tag{G1C.7}
\]

The wing length includes any horizontal top overhang and excludes the
vertical end faces. These are necessary conditions for the spatial
objective itself. Ordinary niche arclength is not silently identified
with a weak limit of finite source measures.

If the affine middle roof is horizontal, the complete
[horizontal theorem HW1](#proof-horizontal-complete)
already proves G1C.4 at every width. It remains to exclude tilted
canonical global maximizers. The following sections exhaust them.

### 3. Tilted normalization and the first-unit exclusion

Reflect horizontally if needed so that the higher middle endpoint is on
the right. Put

\[
I=[-2C,2C],\quad J=[-C,C],\quad
A(-C)=1-h,\quad A(C)=1,
\]

and write the top face as \([C,C+T]\times\{1\}\). Here \(h>0\) is
the tilt height and \(T\ge0\) is the top overhang. To fix the two wing
conventions explicitly, put

\[
f(t)=h_U(\cos t,\sin t),\qquad
g(t)=\max_{x\in[-2C,-C]}\{-x\sin t+A_U(x)\cos t\},
\]

\[
u=f''+f,\qquad v=g''+g
\quad\text{almost everywhere on }(0,\pi/2).
\]

Thus the first density \(u\) belongs to the high-right wing, and \(v\)
uses the low-left-wing surrogate, excluding the central-facet atom.
The extra high-point second wall is nonpositive on \(J\); the tilted
source notes justify this convention for the actual positive niche.

The [short, wide, and intermediate cuts](#proof-tilted-width)
and the [full-triangle width bound](#proof-full-triangle)
give

\[
\frac{1001}{2000}<C<\frac{37}{50},\qquad
0<h<\frac{17}{50}.
\tag{G1C.8}
\]

The general [first-unit theorem GF](#proof-first-unit)
excludes any tilted canonical global maximizer in this domain for which
\(u\le1\) almost everywhere. It places no unit bound on \(v\).
Its [structural argument](#proof-first-wing-structure) and
[joint-source occupation audit](#proof-fold-occupations)
retain companion folds and measurable contact ties. The exact energy
inequality ends with

\[
6CT\le\frac{97}{48}T<3T,
\]

where the geometry has forced \(T>0\), contradicting \(C>1/2\).
The first companion-floor crossing has displacement at least \(T\);
it is not assumed to be the global niche minimum.

[CH7](#proof-full-curvature) supplies
\(u\le1\) whenever \(C\le2/3\), including the endpoint. Hence only

\[
\frac23<C<\frac{37}{50}
\tag{G1C.9}
\]

remains. For this entire wider range, the
[initial-floor energy test IE](#proof-initial-energy)
gives a sufficient condition for \(u\le1\). With

\[
d=3C,\quad B=e_R-1+h,\quad s=\sqrt{h(2-h)},
\]

the two conditions are

\[
d^2+B^2\le5,
\qquad d^2+B^2+B(1-h)-ds\le4.
\tag{G1C.10}
\]

IE8 proves both throughout \(21/100\le h<17/50\), without using the
later zero-niche endpoint result. GF excludes that strip, leaving
\(h<21/100\).

### 4. Endpoint geometry and the final height reduction

The next three results assume neither whole wing has curvature at most
one. This order matters for the remaining branch.

[CG](#proof-corner-confinement) proves that all positive inner
corners lie in \(J\), the actual niche lies below the cap, and
\(\mathcal S=U\setminus N(U)\) is a nonempty compact connected body
with a genuine continuous one-turn motion. Thus the established ordinary
one-turn bound

\[
|\mathcal S|\le G_0:=\frac{22199}{10000}
\tag{G1C.11}
\]

may be applied to this body.

The [early-excess theorem ET](#proof-early-excess)
shows \(u\le1\) for \(t\ge11/15\), before every possible positive
right endpoint tangency because \(\cos(11/15)>37/50\). It also bounds
the earlier excess moment by \(J_f<1/40\).

The new [reflected-tail and projection theorem RT](#proof-reflected-projection)
uses the high pinned point, the actual finite-source horizontal moment,
and a reflected arm estimate under \(T=0\). It proves

\[
T>0,\qquad n_U(-C)=0,
\qquad T=C+x_{\rm zero}.
\tag{G1C.12}
\]

Here \(x_{\rm zero}\) is the unique zero of the low-wing second-wall
envelope. Passing through its zero-height interval is justified by the
finite source mass estimate, rather than by an invalid continuity claim
for zero-set lengths.

Writing \(z=n_U(C)\), the actual endpoint laws and ET/RT now give

\[
e_R=\frac12+\frac h4+\frac{3z}{4},\qquad
e_L=\frac12-\frac{3h}{4}-\frac z4,
\]

\[
0<T\le s,\quad 0\le z\le KT,\quad
K=\frac{C}{\sqrt{1-C^2}}<\frac{10}{9},\quad
N_{\rm out}\le\frac{(T+J_f)z}{2}.
\tag{G1C.13}
\]

The [final height reduction FR](#proof-final-height)
uses these pressure identities to exclude \(h\ge1/20\). For
\(C\le73/100\), both IE conditions hold throughout
\(1/20\le h\le21/100\); the exact radius bound is
\(798001/160000<5\), and the two extremal energy bounds are
\(634973/160000<4\) and \(553949/160000<4\).

For \(C\ge73/100\), the zero left endpoint niche sharpens the
positive-floor loss in the full-triangle proof. The joint concave support
relaxation retains every clipping pattern. Its supporting-plane bound
decreases in \(h\) over this strip and at \(h=1/20\) is

\[
\mathcal P<\frac{7550393}{9240000}
=\frac{41}{50}-\frac{26407}{9240000}<\frac{41}{50}.
\tag{G1C.14}
\]

Both subranges contradict maximality. Every remaining tilt therefore
has \(0<h<1/20\).

### 5. Every small-tilt alternative is impossible

The [small-height theorem SH](#proof-small-height)
covers the slightly larger interval

\[
\frac23<C<\frac{37}{50},\qquad
0<h\le\frac{509}{10000}.
\tag{G1C.15}
\]

It combines G1C.7, the two actual wing chord lengths, and G1C.13 to obtain
an ordinary-area lower bound. Set

\[
C_0=\frac{\sqrt{17}}6,\quad
S_0=\frac{2\sqrt{17}+\sqrt{26}}6,\quad
\lambda=\sqrt{\frac{17}{26}},\quad
m=\frac{3}{4\sqrt{26}},\quad a_0=\frac{1-\lambda}{2}.
\]

The tangent inequality for the Euclidean norm gives

\[
|\mathcal S|\ge S_0+(2+\lambda)(C-C_0)
-Ch-m(h+z)+a_0T-\frac{(T+J_f)z}{2}.
\tag{G1C.16}
\]

If the second inequality of G1C.10 fails, completion of squares gives

\[
\left(3C-\frac s2\right)^2+\frac9{16}(h+z)^2>\frac{17}{4},
\]

and therefore

\[
C-C_0>\frac s6-\frac3{64}(h+z)^2.
\]

Substitution into G1C.16 and the exact endpoint bounds reduce the area
surplus to a decreasing cubic bracket. Its value at the rational endpoint
\(s_*=63/200\) is

\[
\frac{11102231813}{13507522880000}>0.
\tag{G1C.17}
\]

Thus \(|\mathcal S|>S_0>2669/1200>G_0\), contradicting G1C.11.

If the first inequality of G1C.10 fails, then
\(C>\sqrt{19}/6>29/40\) and \(B<-4/15\). These force the improved
endpoint bound \(z<27/100\). The same chord estimate yields

\[
|\mathcal S|>\frac{666488123}{300000000}
=G_0+\frac{518123}{300000000}>G_0,
\tag{G1C.18}
\]

again a contradiction. If neither inequality fails, IE gives \(u\le1\)
and GF excludes the cap. These alternatives include equality in either
energy criterion. They exhaust G1C.15.

Since \(1/20<509/10000\), this excludes every tilt left by Section 4.
The complete coverage is recorded explicitly below.

| Canonical maximizer branch | Complete bound or exclusion |
|---|---|
| Horizontal middle, every width | HW1 proves \(\mathcal P\le M/2\) |
| Tilted, outside G1C.8 | Actual short/wide/intermediate and full-triangle bounds |
| Tilted, \(C\le2/3\) inside G1C.8 | CH7 followed by GF |
| \(2/3<C<37/50\), \(h\ge21/100\) | IE8 followed by GF |
| \(2/3<C\le73/100\), \(1/20\le h\le21/100\) | FR's IE strip followed by GF |
| \(73/100\le C<37/50\), \(1/20\le h\le21/100\) | FR's actual full-triangle bound |
| \(2/3<C<37/50\), \(0<h\le509/10000\) | SH: either IE failure contradicts ordinary area; otherwise IE and GF |

The selected canonical maximizing cap is therefore horizontal. HW1 bounds its
value by \(M/2\); the reference attains \(M/2\). Attainment, the
score-preserving canonical reduction, and height extrusion prove G1C1
for the entire original cap domain. No global curvature hypothesis has
been imposed on that domain.

### 6. Ordinary one-turn dependency and verification record

The external input in G1C.11 is Baek's
[*Optimality of Gerver's Sofa*, Theorem 1.1.1](https://arxiv.org/html/2411.19826v1),
which bounds every nonempty connected closed planar shape admitting a
continuous rigid motion through the unit right-angle hallway by Gerver's
area. CG constructs a body in exactly that class before the theorem is
used. No optimality premise for the spatial cap under the ordinary-area
objective is imported.

The rational relaxation \(G_0=22199/10000\) is the existing exact
enclosure recorded in [SE.1](#external-inputs).
Its six component bounds occur in
[Gerver/AreaBounds.lean](#external-inputs),
with their stated Gerver parameter solution and bounds hypotheses. Their
signed upper sum is

\[
\frac{7202+13340+8069-6013-30-369}{10000}
=\frac{22199}{10000}.
\]

The assembled declaration `gerverSofa_area_mem` in
[Main.lean](#external-inputs) gives the same upper
endpoint. The declarations `romik_exists` and `romik_bounds` in
[External/Romik.lean](#external-inputs)
supply a solution in the stated box and its parameter bounds in the
existing source chain. Those declarations and their premises were
inspected; they were not recompiled or newly proved in this work. The
external theorem and this existing enclosure are explicit dependencies
of the written result.

The [dependency and coverage audit](#verification-record)
checks that the source arguments, corner confinement, forward and
reflected terminal estimates, and final energy alternatives have no
circular unit-curvature or ordinary-feasibility premise. The
[fixed exact checker](#verification-record)
reproduces the final rational certificates using Python's `Fraction`
only. Its checks are arithmetic certificates, not a substitute for the
continuum geometric proofs. No angle sampling, optimization campaign,
Lean/Lake command, CI run, or Lean source edit is part of this checkpoint.

### 7. Deduction of Gate 1 and the remaining gate

For a genuine connected both-full-turn sofa, let \(U,V\) be the upper
and reflected lower downward caps of its common convex hull. They share
the same projection \(I\) and middle half \(J\). With
\(d_U=1-A_U\) and \(d_V=1-A_V\), the
[Gate 0 fiber formula](#main-motions) is

\[
\ell(x)=1-\max\{d_V(x),n_U(x)\}
-\max\{d_U(x),n_V(x)\}.
\]

On \(J\), \(\ell\le1-n_U-n_V\); on \(I\setminus J\),
\(\ell\le A_U+A_V-1\). The constants cancel after integration because
the two regions have equal length. Connectedness supplies nonempty
projected fibers for the actual canonical envelope, so

\[
|S|\le\int_I\ell(x)\,dx
\le\mathcal P(U)+\mathcal P(V)\le M.
\tag{G1C.19}
\]

For arbitrary auxiliary hulls the same pointwise inequalities bound the
signed integral, without assuming its fibers are nonempty. At Romik's
reference hull, the middle roofs equal one, both niches are confined to
the middle window, and the
[exact reference calculation](#main-equality)
gives equality throughout G1C.19. Thus the complete full-turn supremum
is exactly \(M\), and the original coupled ordinary niche-loss inequality
G1.2 / G1.5 follows as well. This meets the controlling plan's Gate 1
acceptance condition.

The proof above uses both full angle intervals and supplies no arbitrary
no-loss completion theorem for partial turns. The separate
[Gate 2 proof](#proof-partial-closure) now establishes the sharp
joint charge with independent terminal angles
\(\alpha,\gamma\in[\pi/4,\pi/2]\) and their two actual outgoing
whole-body strips. That later theorem, with its own source and weighted
terminal arguments, provides the unrestricted sharp area value.

---

<a id="proof-partial-domain"></a>
## Technical proof 32. Actual partial-cap domain and used-support saturation (PD)

### 1. The exact objective and its sufficient implication

Let \(L=\pi/2\), and let \(U\subset\mathbb R\times[0,1]\) be a nonempty
compact downward convex cap. Write its horizontal projection as
\(I=[l,r]\), its roof as \(A_U\), and put

\[
W=r-l,\qquad J=[l+W/4,r-W/4].
\]

For \(0<t<L\), define

\[
\begin{aligned}
R_{U,t}(x)
&=\frac{h_U(\cos t,\sin t)-1-x\cos t}{\sin t},\\
S_{U,t}(x)
&=\frac{h_U(-\sin t,\cos t)-1+x\sin t}{\cos t}.
\end{aligned}
\tag{PD.1}
\]

For \(\pi/4\le\alpha<L\), the full positive constraint is

\[
q_{U,\alpha}(x)=
\max\left\{
0,\ \sup_{0<t<\alpha}\min\{R_{U,t}(x),S_{U,t}(x)\},
\ R_{U,\alpha}(x)
\right\}.
\tag{PD.2}
\]

The last term is the lower boundary of the actual outgoing straight
arm, a whole first wall. A terminal two-wall minimum would be an
insufficient replacement. At \(\alpha=L\), set \(q_{U,L}=n_U\), the
full positive niche. The limiting outgoing wall is
\(h_U(e_y)-1\le0\), so it is redundant.

The partial spatial score is

\[
\mathcal P_\alpha(U)=
\int_{I\setminus J}A_U(x)\,dx-\int_Jq_{U,\alpha}(x)\,dx.
\tag{PD.3}
\]

A zero-width cap has score zero.

For an arbitrary auxiliary convex hull \(K\) in the unit incoming strip,
let \(U,V\) be its upper and reflected-lower downward caps. Their upward
supports are exactly those used by the lower and upper canonical
motions. The signed full constraint at independent terminal magnitudes
\(\alpha,\gamma\in[\pi/4,L]\) is

\[
\ell(x)=1-\max\{1-A_V(x),q_{U,\alpha}(x)\}
          -\max\{1-A_U(x),q_{V,\gamma}(x)\}.
\]

On \(J\), discard the outer deficits; on \(I\setminus J\), discard the
niche and terminal deficits. Since both sets have length \(W/2\),

\[
\boxed{\int_I\ell(x)\,dx
\le\mathcal P_\alpha(U)+\mathcal P_\gamma(V).}
\tag{PD.4}
\]

For a genuine compact connected feasible body \(S\), its actual hull
has no empty projected survivor fiber, so
\(|S|\le\int_I\ell\). For auxiliary hulls the integral remains signed.
Consequently the universal bound

\[
\mathcal P_\alpha(U)\le M/2
\qquad\text{for every such cap and every }\alpha\in[\pi/4,L]
\tag{PD.5 — scalar target}
\]

is sufficient for Gate 2 by PD.4. Gate 1 proves its endpoint
\(\alpha=L\), and the results below reduce the proper-angle domain.
The full dependency chain is assembled in [the Gate 2 closure](#proof-partial-closure).

### 2. Height extrusion and the middle chord

**Theorem PD1 (height-one reduction).** If \(U\) has height \(H\le1\)
and \(0\le\varepsilon\le1-H\), then

\[
U^\varepsilon=U+(\{0\}\times[0,\varepsilon])
\quad\Longrightarrow\quad
\mathcal P_\alpha(U^\varepsilon)\ge\mathcal P_\alpha(U).
\tag{PD.6}
\]

Indeed, both upper supports in PD.1 increase by their vertical normal
component times \(\varepsilon\). Hence each attached wall increases by
\(\varepsilon\), and the terminal wall does likewise. Taking the maximum
with zero gives

\[
0\le q_{U^\varepsilon,\alpha}-q_{U,\alpha}\le\varepsilon.
\]

The roof rises by exactly \(\varepsilon\) on the exterior wings.
Their measure equals that of \(J\), proving PD.6. The same argument
applies at \(\alpha=L\). The projection and the angle are unchanged.

**Theorem PD2 (affine middle).** For each cap and each fixed terminal
angle, there is a height-one cap with the same projection, an affine
roof on \(J\), and score at least the original score.

To prove this, let \(a(x)\) be the affine line joining the original roof
at the two endpoints of \(J\), and put

\[
U^c=U\cap\{(x,y):y\le a(x)\}.
\]

Concavity gives \(A_U\ge a\) on \(J\) and \(A_U\le a\) outside \(J\).
The chord is nonnegative on \(J\), and outside \(J\) it is at least the
nonnegative original roof. Thus \(U^c\) remains a downward convex cap
with the same projection. Its two charged exterior wings are unchanged.
Its smaller supports can only decrease both attached walls and the
terminal whole wall, so \(q_{U^c,\alpha}\le q_{U,\alpha}\). Therefore
its score does not decrease. Apply PD1 to restore exact height one;
the middle roof remains affine.

In particular, this procedure preserves global maximality when applied
to a global maximizer. No sign of the chord slope has been selected.

### 3. Width coercivity and joint attainment

Translate horizontally so that \(I=[-W/2,W/2]\). The two floor endpoints
give, at the actual angle \(t=\pi/4\),

\[
\left[\min\{R_{U,\pi/4}(x),S_{U,\pi/4}(x)\}\right]_+
\ge (W/2-\sqrt2-|x|)_+.
\]

For \(\alpha>\pi/4\) this angle is visited. For \(\alpha=\pi/4\),
the outgoing first wall dominates its two-wall minimum. Thus for every
allowed terminal angle,

\[
q_{U,\alpha}(x)\ge(W/2-\sqrt2-|x|)_+.
\tag{PD.7}
\]

The trivial exterior bound gives \(\mathcal P_\alpha\le W/2\). For
\(W\ge6\), the tent in PD.7 is positive throughout \(J\), so

\[
\mathcal P_\alpha(U)
\le \frac{1+\sqrt2}{2}W-\frac3{16}W^2
\le 3\sqrt2-\frac{15}{4}<\frac45.
\tag{PD.8}
\]

The quadratic decreases for \(W\ge6\), and the last strict comparison
follows, for example, from \(\sqrt2<3/2\). Caps with \(W\le8/5\)
also have score at most \(4/5\).

The reference cap at \(\alpha=L\) has score \(M/2>41/50\), as established
exactly in [G1C.6](#proof-full-closure). Hence every global
maximizer of the joint cap-and-angle problem has

\[
\boxed{\frac85<W<6.}
\tag{PD.9}
\]

Here is the continuity needed for attainment, including the endpoint
\(\alpha=L\). On a fixed box
\([-B,B]\times[0,1]\), uniformly for \(x\in[-B,B]\),

\[
\begin{aligned}
\bigl[\min\{R_{U,t}(x),S_{U,t}(x)\}\bigr]_+
&\le 2B\min\{\tan t,\cot t\},\\
(R_{U,\alpha}(x))_+&\le2B\cot\alpha.
\end{aligned}
\tag{PD.10}
\]

For example,
\(h_U(-\sin t,\cos t)\le B\sin t+\cos t\), so
\(S_{U,t}(x)\le(B+x)\tan t+1-\sec t\le2B\tan t\).
The other bounds follow in the same way.

The first inequality makes the two omitted angular tails uniformly
small. On a closed interior angular interval, Hausdorff convergence of
caps gives uniform convergence of both support functions and wall
heights. The maximum of a continuous function over
\([\eta,\min(\alpha,L-\eta)]\) varies continuously with its upper
endpoint. The second inequality makes the positive terminal wall tend
uniformly to zero as \(\alpha\uparrow L\). These facts prove uniform
convergence of \(q_{U_n,\alpha_n}\) on the fixed horizontal box whenever
\(U_n\to U\) in Hausdorff distance and \(\alpha_n\to\alpha\).

The endpoints of \(I\) and \(J\) also converge, being expressions in
horizontal supports. The middle niche integral is therefore continuous.
The exterior roof integral is
\[
|U|-|U\cap(J\times\mathbb R)|.
\]
Area of bounded planar convex sets is Hausdorff-continuous; moving the
two vertical cuts does not change this conclusion. Equivalently, use
almost-everywhere convergence of convex-set indicators and the cuts.
If the limiting cap is degenerate, its area and the areas of the
approximating caps tend to zero. Thus the full score is continuous.

**Theorem PD3 (attainment).** The joint supremum of
\(\mathcal P_\alpha(U)\) over all downward caps in the unit-height strip
and \(\alpha\in[\pi/4,L]\) is attained. One may choose a height-one
maximizer satisfying PD.9 whose entire middle roof is affine.

Indeed, after horizontal centering and PD1, it suffices to maximize on
the compact class of height-one downward convex caps in
\([-3,3]\times[0,1]\), with centered projection, and the compact angle
interval. Blaschke compactness and the preceding continuity give a
maximizer; PD.8–PD.9 and PD2 give the stated refinements. Degenerate caps
are harmless in the compactification.

### 4. The top meets the middle window from either side

**Theorem PD4 (top insertion).** At every height-one global maximizer,
the horizontal top face intersects \(J\).

Suppose first that the left endpoint \(a\) of the top face is strictly
to the right of \(j_+=r-W/4\). Adjoin the point \(p=(j_+,1)\) and take
the convex downward hull. Its projection and height are unchanged.
For every upward normal \(n=(n_x,n_y)\) with \(n_x\ge0\), the old point
\((a,1)\) dominates \(p\), so that support is unchanged. If a support
with \(n_x<0\) changes, the new support is \(p\cdot n\), and for
\(x\in J\), \(y\ge0\),

\[
p\cdot n-1-(x,y)\cdot n
=(j_+-x)n_x+(1-y)n_y-1\le0.
\tag{PD.11}
\]

Thus every newly changed inner second wall is nonpositive throughout
the positive middle half-strip. Both its old and new quadrant make no
positive contribution there. All first-wall supports, including the
terminal one, are unchanged. Hence \(q_{U,\alpha}|_J\) is unchanged.
The new top plateau on \([j_+,a]\) strictly increases the charged
exterior area, a contradiction.

If the right endpoint \(b\) of the top face is strictly to the left of
\(j_-=l+W/4\), instead insert \(p=(j_-,1)\). All upward supports with
\(n_x\le0\) are unchanged. Every changed support with \(n_x>0\) satisfies

\[
p\cdot n-1-(x,y)\cdot n
=(j_--x)n_x+(1-y)n_y-1\le0
\qquad(x\in J,\ y\ge0).
\tag{PD.12}
\]

This covers the changed first walls and, specifically, the outgoing
whole first wall. They remain nonpositive on \(J\); the middle
constraint is again unchanged. The newly filled top plateau on
\([b,j_-]\) strictly increases exterior reward. This is the second
contradiction.

For an affine-middle maximizer, a positive middle slope therefore has
height one at \(j_+\), and a negative slope has height one at \(j_-\).
A horizontal middle roof equals one throughout \(J\). The two tilted
cases are separate alternatives; no horizontal reflection of the
partial objective has been invoked.

### 5. Saturation by precisely the used supports

For a cap \(U\) at fixed terminal angle, define

\[
U^{\rm sat}
=(I\times[0,1])\cap
\bigcap_{0\le t\le\alpha}
\left\{
z:\ z\cdot(\cos t,\sin t)\le h_U(\cos t,\sin t),\
z\cdot(-\sin t,\cos t)\le h_U(-\sin t,\cos t)
\right\}.
\tag{PD.13}
\]

**Theorem PD5 (used-support saturation).** This is a compact downward
convex cap containing \(U\), with the same projection, height, and all
used upper supports. In particular,

\[
q_{U^{\rm sat},\alpha}=q_{U,\alpha},
\qquad
\mathcal P_\alpha(U^{\rm sat})\ge\mathcal P_\alpha(U).
\tag{PD.14}
\]

Every normal used in PD.13 has nonnegative vertical component, so
downward closure is preserved. The floor segment over \(I\) remains
inside. Inclusion gives one support inequality, and the defining
halfplanes give the reverse inequality in each used direction. The top
normal occurs at \(t=0\) in the second family, fixing the height.
Thus every wall in PD.2 is unchanged, proving PD.14.

At a global maximizer, saturation cannot increase the exterior roof
anywhere on an open charged interval: continuity would produce a
strict area increase. Consequently it preserves both exterior wings
and, by their one-sided limits, their endpoints. If the original middle
roof is the chord \(a(x)\), it follows that

\[
\boxed{U=U^{\rm sat}\cap\{(x,y):y\le a(x)\}.}
\tag{PD.15}
\]

This is an exact description of a selected affine-middle maximizer.
In the open unused normal arcs
\[
(\alpha,L)\quad\text{and}\quad(L+\alpha,\pi),
\]
the only possible nonzero upper curvature measure is the atom of the
uncharged central facet, if its normal belongs to one of these arcs.
There is no charged wing curvature there. To see this without assuming
regularity, first consider \(U^{\rm sat}\). Compactness of its family of
defining normals ensures that every boundary point has an active
defining constraint. At boundary-arclength almost every point the outer
normal is unique, and hence equals the normal of any active constraint.
Every such normal is a used normal or an axis normal. Its upper
curvature measure therefore vanishes on the unused open arcs.

The original maximizing cap has the same charged wings as
\(U^{\rm sat}\), so their wing curvature measures agree. Any remaining
curvature of the original cap within these arcs comes from its affine
middle roof and is the central-facet atom. Equivalently, on each
component away from that possible central normal, the supporting point
is constant and the support satisfies \(h''+h=0\). A vertex can have
an entire unused interval in its normal cone; it contributes no
boundary length or curvature measure on that interval.

This statement does not eliminate possible terminal facets at the
endpoints of the used normal intervals, and does not identify a weak
finite niche-source limit with ordinary continuum arclength.

### 6. An exact low-terminal-angle exclusion

This bound holds for every cap, with no maximizing or canonical-form
hypothesis. Center \(I=[-2C,2C]\), let \(\alpha<L\), and put
\[
a=\cot\alpha>0,\qquad
H=\frac{h_U(\cos\alpha,\sin\alpha)}{\sin\alpha}.
\]

The upper support gives \(A_U(x)\le H-a x\), and the outgoing wall gives
\(q_{U,\alpha}(x)\ge H-\csc\alpha-a x\). Bound the left exterior reward
by \(C\), bound the right exterior reward by this support line, and
charge only the left half of \(J\). The uncharged niche remainder is
nonnegative. Therefore

\[
\begin{aligned}
\mathcal P_\alpha(U)
&\le C+\int_C^{2C}(H-a x)\,dx
-\int_{-C}^0(H-\csc\alpha-a x)\,dx\\
&=(1+\csc\alpha)C-2\cot\alpha\,C^2\\
&\le\boxed{\frac{(1+\csc\alpha)^2}{8\cot\alpha}}.
\end{aligned}
\tag{PD.16}
\]

The cancellation is valid even when the affine niche lower bound is
negative on part of its integration interval.

For \(a\in[4/5,1]\), the final expression is
\((1+\sqrt{1+a^2})^2/(8a)\). Its derivative has the sign of
\[
(\sqrt{1+a^2}-2)(\sqrt{1+a^2}+1)<0.
\]
Since \(\sqrt{41}<641/100\), this proves

\[
\boxed{
\pi/4\le\alpha\le\arctan(5/4)
\ \Longrightarrow\
\mathcal P_\alpha(U)\le\frac{33+5\sqrt{41}}{80}
<\frac{1301}{1600}<\frac{41}{50}<\frac M2.}
\tag{PD.17}
\]

At \(\alpha=\pi/4\), PD.16 gives \((3+2\sqrt2)/8\).

---

<a id="proof-partial-sources"></a>
## Technical proof 33. Prescribed partial-cap source theorem and terminal mass (PS)

### 1. Exact statement and conventions

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

### 2. Select the prescribed cap at the fixed angle

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

### 3. The finite measures and the terminal atom

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

#### 3.1 Every nonterminal source has exposure of order the mesh

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

### 4. Endpoint complementarity, including zero end faces

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

#### 4.1 The end-face lengths actually converge

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

### 5. Horizontal erosion and the exact source defects

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

### 6. The limiting outer measure is the actual charged wing measure

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

### 7. The actual 45-degree relaxation makes both pressures positive

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
[the low-height proof](#proof-full-pressures)
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

#### 7.1 Pinning the middle facet, without discarding a terminal atom

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

#### 7.2 The sharper geometric wing bound on the visited arcs

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
from [WR, Section 4](#proof-neighboring-walls). At an interior
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

### 8. The stationary clipped Green identity

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

### 9. A fixed-angle terminal occupation measure

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

#### 9.1 Terminal-only historical ties have full occupation

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

---

<a id="proof-negative-completion"></a>
## Technical proof 34. Same-cap completion of the negative-tilt alternatives (NT)

**October 10, 2026. Written mathematical reduction.** The complete
angle and tilt coverage is assembled in [the Gate 2 closure](#proof-partial-closure).
This note closes a whole branch of the selected partial-cap maximizer
domain using the completed Gate 1 value. It uses the exact
[used-support saturation](#proof-partial-domain), not an
assumed full-turn extension of an original physical body.

Write \(L=\pi/2\), \(I=[-2C,2C]\), \(J=[-C,C]\), and use the walls,
partial roof \(q_{U,\alpha}\), and spatial score \(\mathcal P_\alpha\) of
[PD.1–PD.3](#proof-partial-domain). We compare the actual
partial cap score with the full cap score on this same cap. Labels NT are
local.

### 1. The selected negative-tilt geometry

Let \((U,\alpha)\) be a height-one global cap-and-angle maximizer in the
PD3 canonical form, with \(\alpha<L\) and a strictly negative middle slope:

\[
A(-C)=1,\qquad A(C)=1-h,\qquad h>0.
\tag{NT.1}
\]

The middle-facet normal is

\[
\theta_0=L-\arctan\frac{h}{2C}.
\tag{NT.2}
\]

The right endpoint of the height-one top face is exactly \((-C,1)\).
Indeed, the negative affine slope makes \(A(x)<1\) for \(x>-C\), while
PD4 gives the top point at \(-C\). Therefore, if \(\alpha\ge\theta_0\),
all missing first supports are attained at this point:

\[
h_U(\cos t,\sin t)=-C\cos t+\sin t
\qquad(\alpha<t<L).
\tag{NT.3}
\]

If instead \(\alpha<\theta_0\), PD5 shows that there is no charged wing
curvature on \((\alpha,L)\). The middle facet, at normal \(\theta_0\),
cannot extend to the right of \(C\): a positive extension would itself
be charged curvature in this unused open arc. Its right endpoint is
therefore \((C,1-h)\). On either side of its single normal atom the
supporting point is constant, giving

\[
h_U(\cos t,\sin t)=
\begin{cases}
C\cos t+(1-h)\sin t,&\alpha<t<\theta_0,\\
-C\cos t+\sin t,&\theta_0<t<L.
\end{cases}
\tag{NT.4}
\]

At \(\theta_0\) these expressions agree; at \(\alpha\) the first has the
correct support value by continuity, whether or not a terminal facet is
present. No regularity of the used normal arcs or source identity is
needed here.

### 2. Dominate every missing first wall

**Theorem NT1.** In the domain above, either of the conditions

\[
\alpha\ge\theta_0
\qquad\text{or}\qquad h\ge1-\sin\alpha
\tag{NT.5}
\]

implies

\[
\boxed{n_U(x)\le q_{U,\alpha}(x)\quad(x\in J),
\qquad\mathcal P_\alpha(U)\le\mathcal P_L(U)\le M/2.}
\tag{NT.6}
\]

For NT.3, the missing first wall is

\[
R_t(x)=(-C-x)\cot t+1-\csc t\le0
\qquad(x\in J).
\]

Every corresponding two-wall niche value is at most this first wall,
so no missing positive niche is created. This proves NT.6 when
\(\alpha\ge\theta_0\).

Otherwise use NT.4. The part \(t\ge\theta_0\) is again nonpositive.
For \(\alpha\le t\le\theta_0\), put \(z=C-x\in[0,2C]\). The missing
first wall is

\[
F_z(t)=1-h+\frac{z\cos t-1}{\sin t},\qquad
F_z'(t)=\frac{\cos t-z}{\sin^2t}.
\tag{NT.7}
\]

If \(z\ge\cos\alpha\), this derivative is nonpositive for all
\(t\ge\alpha\). Thus \(F_z(t)\le F_z(\alpha)=R_\alpha(x)\).

If \(0\le z\le\cos\alpha<1\), the maximum of \(F_z\) over the larger
interval \([\alpha,L]\) is attained at \(t=\arccos z\), with the endpoint
interpretation at \(z=0\). Its value is

\[
1-h-\sqrt{1-z^2}\le1-h-\sin\alpha.
\tag{NT.8}
\]

This is nonpositive under the second condition in NT.5. Hence every
missing first wall is at most \(\max\{0,R_\alpha(x)\}\), and every missing
two-wall minimum is at most the same quantity. The already visited
angles are included in \(q_{U,\alpha}\). This proves the first inequality
in NT.6 pointwise. Subtract its middle integral from the unchanged
exterior reward and apply Gate 1 to obtain the two score inequalities.

This is a comparison between cap functionals in a proved maximizer
normal form. It does not assert that every partial-motion physical body
can be completed in place.

### 3. The exact remaining negative-tilt region

An above-reference selected partial-cap maximizer with negative middle
slope must therefore satisfy both

\[
\boxed{0<h<1-\sin\alpha,
\qquad\alpha< L-\arctan\frac{h}{2C}.}
\tag{NT.9}
\]

In terms of the missing angle \(\varepsilon=L-\alpha\), this gives the
explicit small-height restriction

\[
0<h<1-\cos\varepsilon\le\varepsilon^2/2.
\tag{NT.10}
\]

There is also an exact localization of every possible failure of the
pointwise comparison. Under NT.9, NT.7–NT.8 show that any point where a
missing first wall exceeds both zero and the terminal first wall must
satisfy

\[
\sqrt{2h-h^2}<C-x<\cos\alpha.
\tag{NT.11}
\]

Indeed, \(C-x\ge\cos\alpha\) is covered by the monotonicity in NT.7,
and a positive value in NT.8 requires
\(1-h>\sqrt{1-(C-x)^2}\), equivalent to the strict lower bound in
NT.11. Thus the uncharged missing contribution is confined to this
explicit right-hand subinterval of \(J\); it is not asserted to vanish
there.

The remaining small negative tilt, the horizontal middle, and every
positive middle tilt lie outside this completion lemma and use the
terminal-source argument assembled in [the Gate 2 closure](#proof-partial-closure). NT1 removes the other negative-tilt cases from that global
obligation without assuming endpoint pressure, a curvature cap, or
ordinary survivor feasibility.

---

<a id="proof-angle-variation"></a>
## Technical proof 35. Exact one-sided angle derivatives with contact ties (TV)

**Local definitions.** Let \(U\) be a compact downward convex cap
of height at most one, with roof \(A\), projection \(I\), and middle
half \(J\). Put \(L=\pi/2\), \(f(t)=h_U(\mu_t)\),
\(g(t)=h_U(\nu_t)\), and use the wall functions \(R_t,D_t\) from MS.5.
For \(\pi/4\le a<L\), define
\[
n_a(x)=\max\{0,\sup_{0<t<a}\min(R_t(x),D_t(x))\},\quad
N_a=\max(n_a,R_a),\quad
\mathcal P_a(U)=\int_{I\setminus J}A-\int_JN_a.
\]
Thus \(n_a\) excludes the terminal whole wall, while \(N_a\) includes it,
as in PT.3. Horizontal reflection at fixed \(a\) is not assumed.

### 1. Exact right derivative in the terminal angle

Fix a in [pi/4,L). The support right derivative f'_+(a) exists. Let

    B_+(a)=(f(a)-1) mu_a + f'_+(a) nu_a.

Equivalently, B_+ is the upper/left endpoint of the outer mu_a supporting
face, translated inward by mu_a. Define disjoint measurable sets

    E={x in J: R_a(x)>n_a(x)},
    H={x in J: R_a(x)=n_a(x)}.

Then the exact pointwise right derivative is

    d_+ N_a(x)/da = (x-B_{+,x})/sin(a)^2              on E,
                    ((x-B_{+,x})/sin(a)^2)_+         on H,
                    0                              elsewhere.       (TV1)

Consequently

    d_+ P_a(U)/da
      = -1/sin(a)^2 [ integral_E (x-B_{+,x}) dx
                      + integral_H (x-B_{+,x})_+ dx ].               (TV2)

In particular every joint global maximizer (U,a) with a<L satisfies

    integral_E (x-B_{+,x}) dx
       + integral_H (x-B_{+,x})_+ dx >= 0.                            (TV3)

#### Proof

Uniformly on compact x intervals,

    R_{a+h}(x)=R_a(x)+h (x-B_{+,x})/sin(a)^2+o(h).

The old n_a remains among the competitors defining n_{a+h}. Every
newly visited two-ray value at a+t is at most R_{a+t}. If R_a>n_a,
then min(R_a,D_a)<R_a; otherwise its limit from below would already
give n_a>=R_a. Continuity gives a strict gap for all sufficiently
nearby newly visited angles, so only R_{a+h} moves the maximum to
first order. This gives the first case of TV1.

If R_a<n_a, the strict gap makes the value locally constant to first
order, giving the last case. If R_a=n_a, the lower bound

    max(n_a,R_{a+h}) <= N_{a+h}

and the upper bound

    N_{a+h} <= max(n_a,sup_{0<=t<=h} R_{a+t})

have the same right derivative: the positive part of R'_+(a).
This gives the middle case. Local boundedness of the supports and
their one-sided derivatives makes these difference quotients
uniformly bounded on J, so dominated convergence proves TV2.
TV3 is the necessary one-sided derivative inequality at a maximum.

The formula is valid at an outer facet: it uses f'_+(a), not an
unjustified single f'(a).

#### The corresponding exact left derivative

Suppose a>pi/4. Let B_-=(f(a)-1)mu_a+f'_-(a)nu_a, the lower/right
endpoint of the outer supporting face translated inward by mu_a.
Partition H further into H_old and H_new. Put x in H_old if R_a=0
(the fixed floor competitor) or if some t<a attains min(R_t,D_t)=R_a.
Put every other x in H_new. Then

    d_- N_a(x)/da = (x-B_{-,x})/sin(a)^2             on E or H_new,
                    min((x-B_{-,x})/sin(a)^2,0)      on H_old,
                    0                              elsewhere.       (TV1L)

Here d_- denotes [N_a-N_{a-h}]/h. On H_new, R_a>0 and the running
maximum is attained only at t=a, where min(R_a,D_a)=R_a. Write
R'_- for the left derivative of R and m'_- for that of min(R,D).
If R_a<D_a then m'_-=R'_-. If R_a=D_a then
m'_-=max(R'_-,D'_-). The terminal running maximum requires m'_->=0.
Its value at a-h is R_a-h m'_-+o(h): the elementary linear upper and
lower estimates near a prove this even without monotonicity of m.
Taking the maximum with R_{a-h}=R_a-h R'_-+o(h) leaves the derivative
R'_-. This proves the H_new case. On H_old a fixed earlier maximizing
competitor remains for every sufficiently small h, so the derivative
is min(R'_-,0). The strict cases are immediate. The same uniform local
angle-Lipschitz bound permits integration of TV1L.

Thus, in particular, if E is null and H_old is null, an interior-angle
maximum requires

    integral_H (x-B_{-,x}) dx <=0.                                 (TV3L)

For a genuine terminal-only first-wall tie, the absence of a larger
earlier R_t forces x>=B_{-,x}; any positive-length such H therefore
contradicts TV3L. This is a useful exclusion when all terminal charge
comes only from a new terminal ray. It does not replace the mixed
old-contact/strict-strip analysis for a general maximizing cap.

---

<a id="proof-initial-angle"></a>
## Technical proof 36. The all-width initial-angle certificate (AT)

**October 10, 2026. Written mathematical proof, independently audited
within this research session.** The actual 45-degree
two-wall niche together with the whole outgoing first wall excludes a
further terminal-angle interval, uniformly over the entire downward-cap
domain. All floor, window, and wall-switch clipping is retained. No
stationary curvature law, terminal source occupation, reflection symmetry
of the partial objective, or numerical search enters this argument.

Write

\[
M=1+4Y^2+\arctan Y,\qquad 4Y^3+3Y=1,\quad Y>0.
\]

**Theorem AT1.** For every compact downward convex cap of height at most
one, with its own middle-half window, and every
\(\pi/4\le\alpha\le\arctan(8/3)\),

\[
\boxed{\mathcal P_\alpha(U)<\frac{5259}{6400}
<\frac{411}{500}<\frac M2.}
\tag{AT.1}
\]

Here \(\mathcal P_\alpha\) is exactly PD.1–PD.3 in
[the partial-domain reductions](#proof-partial-domain),
including its **whole outgoing first wall**. In particular, any cap with
score at least \(M/2\) has \(\alpha>\arctan(8/3)\). This is an
individual scalar-cap exclusion; it does not close Gate 2's remaining
partial-angle interval or by itself impose this lower bound separately
on the two angles of a common-hull competitor. The full scalar and
common-hull implications are assembled in [the Gate 2 closure](#proof-partial-closure).

### 1. Reduction and the three actual supports

PD.6–PD.15 supply height extrusion, middle-chord reduction, coercivity,
attainment, and top insertion. The attainment proof also applies with
\(\alpha\) fixed: if a cap has score greater than \(41/50\), the
fixed-angle maximum is attained inside the same compact width interval.
Its canonical representative has height one, an affine middle roof, and
a top face meeting the middle window. Thus, a hypothetical cap with score
at least \(5259/6400\) yields such a canonical fixed-angle maximizer
with at least the same score. It suffices to rule out that maximizer.
No maximization in the angle is needed.

Center the projection and introduce the parameters

\[
I=[-2C,2C],\quad J=[-C,C],\quad
K=\sqrt2-1,\quad \kappa=\cot\alpha,\quad
d=\frac{\kappa}{1+\sqrt{1+\kappa^2}}.
\tag{AT.2}
\]

The previously proved outgoing-only estimate handles
\(\alpha\le\arctan(5/4)\). For the new interval it suffices to take

\[
\frac38\le\kappa\le\frac45,\qquad
\kappa d=\sqrt{1+\kappa^2}-1,\qquad
\kappa=\frac{2d}{1-d^2},\qquad 0<d<K.
\tag{AT.3}
\]

Use the actual supports to define

\[
u=\max_U(x+y)-1,\quad v=\max_U(-x+y)-1,\quad
b=\max_U\left(x+\frac{y-1}{\kappa}\right).
\tag{AT.4}
\]

The three outer support lines are
\(1+u-x\), \(1+v+x\), and \(1-\kappa(x-b)\). The actual outgoing
inner wall is \(\kappa(b-d-x)\). Consequently

\[
\begin{aligned}
A(x)&\le \min\{1,1+u-x,1+v+x,1-\kappa(x-b)\},\\
q_{U,\alpha}(x)&\ge
\max\{0,\min(u-K-x,v-K+x),\kappa(b-d-x)\}.
\end{aligned}
\tag{AT.5}
\]

The 45-degree angle is genuinely visited throughout the new interval.
Only the displayed lower bound on the true niche is used.

There is an essential compatibility condition between the two first
supports:

\[
\boxed{b\le u\le 2(1-\kappa)C+\kappa b,
\qquad u,v,b\le2C.}
\tag{AT.6}
\]

Indeed, \(y\le1\) and \(\kappa<1\) give
\(x+(y-1)/\kappa\le x+y-1\), hence \(b\le u\). At a point attaining
\(u\),

\[
\kappa b\ge\kappa x+y-1=u-(1-\kappa)x
\ge u-2(1-\kappa)C.
\]

The remaining upper bounds follow directly from the containing box.

Since the middle is affine and its top meets \(J\), either
\(A(-C)=1\) or \(A(C)=1\). The first alternative gives
\(v\ge C\) and \(u,b\ge-C\); the second gives \(u,b\ge C\) and
\(v\ge-C\). These alternatives will be handled directly.

### 2. Two preliminary width cuts

#### 2.1 The 45-degree relaxation alone handles \(C\le49/100\)

Put

\[
g_C(z)=\int_C^{2C}(x-z)_+\,dx
=\frac{(2C-z)_+^2-(C-z)_+^2}{2}.
\]

For this paragraph only, the 45-degree relaxation is reflection
invariant, so label the high endpoint as the left one. Then
\(v\in[C,2C]\), \(u\in[-C,2C]\), and the support bounds give

\[
P_{45}\le F_{45}(u,v):=2C-g_C(u)-g_C(v)
-\int_{-C}^C[\min(u-K-x,v-K+x)]_+\,dx.
\tag{AT.7}
\]

This function is concave on that rectangle. Here is a clipping-inclusive
verification which will also be used below. For an integrated maximum of
two affine lines with different spatial slopes, the moving intersection
contributes the nonnegative second variation

\[
\frac{(\hbox{difference of varied intercepts})^2}
{|\hbox{difference of spatial slopes}|}.
\tag{AT.8}
\]

An integrated minimum has the opposite sign. These formulas follow by
integrating the triangle swept out by the moving intersection. A switch
outside the integration interval contributes zero. The resulting
integrals are continuously differentiable and piecewise quadratic in
the intercepts, so checking their quadratic second variations on the
open pieces also checks concavity across all clipping boundaries.

For the loss \(2C-F_{45}\), the sole negative term can occur at an
exposed tent apex inside \(J\); it is
\(- (\xi-\eta)^2/2\), for variations \((\xi,\eta)\) of \((u,v)\).
The left outer switch supplies \(\eta^2\). If \(u>C\), the right
outer switch supplies \(\xi^2\). If \(u\le C\) and the apex is
positively exposed, its falling side meets the floor at
\(u-K\in(-C,C)\), supplying \(\xi^2\) instead. Thus the loss has
nonnegative second variation; cases without an exposed interior apex
already have only nonnegative terms. Boundary parameters follow by
continuity.

For \(C\ge K/2\), the common critical point
\(u=v=C+K/2\) lies in the rectangle. Its positive tent is contained in
\(J\), and AT.7 is at most

\[
2C-2(C-K/2)^2.
\tag{AT.9}
\]

For \(C<K/2\), the trivial bound \(P_{45}\le2C<K\) suffices. The
right side of AT.9 increases up to \(C=49/100\), and

\[
\frac{49}{50}-\frac12\left(\frac{49}{50}-K\right)^2
<\frac{41}{50}.
\tag{AT.10}
\]

For an exact check, \(\sqrt2<99/70\) gives
\(49/50-K=99/50-\sqrt2>2\sqrt2/5\). Hence every remaining
canonical cap has \(C>49/100\).

#### 2.2 For \(\kappa\ge3/5\), the outgoing wall handles \(C\le1/2\)

The outgoing-only calculation PD.16 gives, for every cap,

\[
\mathcal P_\alpha\le(1+\sqrt{1+\kappa^2})C-2\kappa C^2.
\tag{AT.11}
\]

For \(C\le1/2\) and \(3/5\le\kappa\le4/5\), this expression
increases with \(C\); at \(C=1/2\) it decreases with \(\kappa\).
Therefore it is at most

\[
\frac{2+\sqrt{34}}{10}<\frac45.
\tag{AT.12}
\]

It remains to consider

\[
\begin{cases}
C>49/100,&3/8\le\kappa\le3/5,\\
C>1/2,&3/5\le\kappa\le4/5.
\end{cases}
\tag{AT.13}
\]

### 3. The exact finite-support relaxation and the high-right case

For \(b\le u\), write

\[
x_0=\frac{u-\kappa b}{1-\kappa},\qquad
Q_C(u,b)=\int_C^{2C}\max\{0,x-u,\kappa(x-b)\}\,dx
=\kappa g_C(b)+(1-\kappa)g_C(x_0).
\tag{AT.14}
\]

The identity follows from \(b\le u\le x_0\): the three successive
active pieces are zero, \(\kappa(x-b)\), and \(x-u\), with any
pieces outside \([C,2C]\) automatically clipped by \(g_C\).

Define

\[
\begin{aligned}
N(u,v,b)&=\int_{-C}^C
\max\{0,\min(u-K-x,v-K+x),\kappa(b-d-x)\}\,dx,\\
F(u,v,b)&=2C-g_C(v)-Q_C(u,b)-N(u,v,b).
\end{aligned}
\tag{AT.15}
\]

In either high-endpoint alternative the left exterior majorant in AT.5
is \(\min(1,1+v+x)\), and the right exterior majorant is
\(1-\max(0,x-u,\kappa(x-b))\). Thus
\(\mathcal P_\alpha\le F\).

Suppose first that the high endpoint is on the right and \(v<C\).
Increase \(v\) to \(C\), keeping \(u,b\) fixed. This is a variation
of the relaxation; it need not preserve realizability by a cap. The
charged left exterior reward increases at rate \(C\). The derivative
of \(N\) is the length of the interval on which the rising tent line
\(v-K+x\) is exposed. Put

\[
p=\frac{u-v}{2},\quad e=b-d,\quad
x_L=\frac{\kappa e-v+K}{1+\kappa}.
\tag{AT.16}
\]

Every such exposed point lies between \(x_L\) and \(p\), so its
length is at most \((p-x_L)_+\). Since \(u\le2C\), \(v\le C\),
and \(b\ge C\),

\[
p-x_L\le
\frac{(3-\kappa)C+2\kappa d-2K}{2(1+\kappa)}<C.
\tag{AT.17}
\]

The strict inequality uses \(\kappa>1/3\) and \(\kappa d<K\).
Hence \(F\) strictly increases until \(v=C\). All of AT.6 is
preserved. It is therefore enough to bound \(F\) on the convex domain

\[
\boxed{D_C=\{C\le v\le2C,\ -C\le b\le2C,
\ b\le u\le2(1-\kappa)C+\kappa b\}.}
\tag{AT.18}
\]

This also contains the original high-left alternative. No reflection of
the partial objective has been used.

### 4. Two convex domains cover the useful part of the relaxation

Put

\[
a=u-K,\quad c=v-K,\quad e=b-d,\quad
Y_0=(1+\kappa)C+K-v+\kappa(b-d).
\tag{AT.19}
\]

Thus \(Y_0\ge0\) means \(x_L\ge-C\). Define the two convex sets

\[
D_1=D_C\cap\{a\le C\},\qquad
D_2=D_C\cap\{Y_0\ge0\}.
\tag{AT.20}
\]

**Lemma AT2.** The function \(F\) is concave on each of \(D_1,D_2\).

**Proof.** Work at generic parameters in the relative interiors of the
finite quadratic pieces, and use variations \((\xi,\eta,\zeta)\)
of \((u,v,b)\). As in AT.8, all switches of the positive niche
contribute nonnegative second variations except an exposed tent apex
\(p=(u-v)/2\) inside \(J\). If there is no such apex, the loss
\(2C-F=g_C(v)+Q_C+N\) is already convex on that piece. Otherwise the
only negative term is

\[
-\frac{(\xi-\eta)^2}{2}.
\tag{AT.21}
\]

Throughout the interior of \(D_C\), the left outer switch contributes
\(\eta^2\). The complete compensation is as follows.

**On \(D_1\).** If \(a\ge e\), the exposed falling tent meets the
floor at \(x=a\in(-C,C)\). This contributes \(\xi^2\).
If \(a<e\), it instead meets the terminal wall at

\[
x_R=\frac{a-\kappa e}{1-\kappa}\in(p,C),
\]

which contributes \((\xi-\kappa\zeta)^2/(1-\kappa)\).
For \(e<C\), the subsequently exposed terminal wall meets the floor
at \(e\in(-C,C)\), contributing \(\kappa\zeta^2\). For
\(e>C\), instead \(b=e+d\in(C,2C)\), and the outer right
height/terminal switch at \(b\) supplies the same contribution.
In both cases

\[
\frac{(\xi-\kappa\zeta)^2}{1-\kappa}
+\kappa\zeta^2\ge\xi^2.
\tag{AT.22}
\]

Thus the positive contributions include \(\xi^2+\eta^2\), which
dominate AT.21.

**On \(D_2\), outside \(D_1\).** Now \(u>C+K\). Consequently
\(C<x_0<2C\), so the outer terminal/45-degree switch contributes
\((\xi-\kappa\zeta)^2/(1-\kappa)\).
If \(c+e>0\), the rising tent meets the terminal wall at
\(x_L\in(-C,p)\); this contributes
\((\eta-\kappa\zeta)^2/(1+\kappa)\). The inequality

\[
\frac{(\xi-\kappa\zeta)^2}{1-\kappa}
+\frac{(\eta-\kappa\zeta)^2}{1+\kappa}
\ge\frac{(\xi-\eta)^2}{2}
\tag{AT.23}
\]

cancels AT.21.

If \(c+e<0\), the rising tent instead emerges from the floor at
\(-c>e\). The support compatibility and \(u>C+K\) give

\[
\kappa(e+C)\ge u-(2-3\kappa)C-\kappa d
>(3\kappa-1)C+K-\kappa d>0.
\tag{AT.24}
\]

Hence \(-C<e<-c<p\). The terminal/floor switch at \(e\) supplies
\(\kappa\zeta^2\), and the rising-tent/floor switch at \(-c\)
supplies \(\eta^2\). AT.22 again supplies \(\xi^2\), cancelling
the only negative term.

All remaining switch terms are nonnegative. The affine spatial slopes
\(0,1,-1,-\kappa\) are distinct, so ties have zero spatial measure;
the integrals in AT.15 are continuously differentiable and piecewise
quadratic in the parameters. The verified nonnegative second variations
therefore prove convexity of the loss on each convex set, including all
degenerate switch and window boundary cases by continuity. This proves
the lemma. \(\square\)

### 5. A common critical point, with all its clipping checked

Define

\[
\begin{aligned}
b_*&=\frac{K+d}{2},\\
u_*&=(1-\kappa)C+\frac K2+\frac{\kappa d}{2},\\
v_*&=(1+\kappa)C+\frac K2-\frac{\kappa d}{2}.
\end{aligned}
\tag{AT.25}
\]

Its relevant switch positions are

\[
\begin{aligned}
x_{0,*}&=C+K/2,&x_{L,*}&=K/2-C,\\
p_*&=-\kappa(C-d/2),&e_*&=(K-d)/2,\\
a_*&=u_*-K.&&
\end{aligned}
\tag{AT.26}
\]

The only potentially delicate clipping condition is \(a_*\ge e_*\).
The exact identities in AT.3 and \(K^2=1-2K\) give

\[
a_*-e_*=(1-\kappa)(C-1/2)
+\frac{(K-d)^2}{2(1+d)}.
\tag{AT.27}
\]

This is positive for \(C\ge1/2\). For
\(C>49/100\), \(3/8\le\kappa\le3/5\), use
\(K>41/100\), \(d<7/25\), and \(1-\kappa\le5/8\). They give

\[
a_*-e_*>-\frac1{160}+\frac{169}{25600}
=\frac9{25600}>0.
\tag{AT.28}
\]

Here \(d\le(\sqrt{34}-5)/3<7/25\), because
\(\sqrt{34}<146/25\). Thus AT.13 proves the required clipping in
every remaining case.

We have \(b_*<C\), \(C<x_{0,*}<2C\), and

\[
-C<x_{L,*}<p_*<0<e_*<a_*<C.
\tag{AT.29}
\]

For example \(p_*-x_{L,*}=a_*>0\),
\(a_*-p_*=C-K/2>0\), and \(C>d/2\); these identities check the
displayed ordering. Also \(2C-v_*=a_*>0\),
\(v_*-C=\kappa(C-d/2)+K/2>0\), and
\(u_*-b_*=(1-\kappa)(C-d/2)>0\). Together with the value of
\(x_{0,*}\), these show that the point is in the interior of
\(D_C\). It lies in both \(D_1,D_2\), since
\(a_*<C\) and \(Y_{0,*}=(1+\kappa)K/2>0\).

The outer first-45-degree, second-45-degree, and terminal horizontal
exposure lengths are respectively

\[
C-K/2,\qquad a_*,\qquad K/2.
\]

By AT.29 the corresponding niche exposure lengths are exactly the same:
\(a_*-p_*\), \(p_*-x_{L,*}\), and \(x_{L,*}+C\).
Consequently all three first derivatives of \(F\) vanish at AT.25.
Lemma AT2 proves that this point maximizes \(F\) on each of
\(D_1,D_2\).

For the value, put \(z=C-K/2\), \(s=\kappa(C-d/2)\). Direct
integration over the displayed intervals gives

\[
\begin{aligned}
g_C(v_*)&=(z-s)^2/2,\\
Q_C(u_*,b_*)&=\kappa(3C^2/2-Cb_*)+(1-\kappa)z^2/2,\\
N(u_*,v_*,b_*)&=z^2-s^2/2+Ks/2+\kappa K^2/8.
\end{aligned}
\]

Their sum is \(2z^2+Ks\). Thus on \(D_1\cup D_2\),

\[
\boxed{F\le F_*:=2C-2(C-K/2)^2-\kappa K(C-d/2).}
\tag{AT.30}
\]

### 6. The complement is strictly below \(319/400\)

Suppose \((u,v,b)\in D_C\setminus(D_1\cup D_2)\). Then
\(u>C+K\) and \(Y_0<0\). Combining the latter with AT.6 gives

\[
v-u>(3\kappa-1)C+K-\kappa d>0.
\tag{AT.31}
\]

In particular \(u,v>C+K\), so both ends of the 45-degree tent are
strictly positive. Its apex belongs to \((-C,C)\), since
\(u,v\in(C+K,2C]\). Dropping the outgoing support and charge only
enlarges the relaxation. With \(h=(u+v)/2\), exact 45-degree
integration therefore gives

\[
F\le 2C-2C^2+2KC-(h-C)^2.
\tag{AT.32}
\]

Moreover, AT.31 implies

\[
h-C>\frac{3K}{2}-\frac{\kappa d}{2}>\frac9{20},
\tag{AT.33}
\]

using \(K>2/5\) and
\(\kappa d\le\sqrt{41}/5-1<3/10\). Finally
\(1+K=\sqrt2\), so

\[
2(1+K)C-2C^2\le1.
\]

Equations AT.32–AT.33 prove

\[
\boxed{F<1-(9/20)^2=319/400.}
\tag{AT.34}
\]

This completes all parameter and clipping cases in \(D_C\).

### 7. Exact optimization in width and angle

Completing the square in \(C\) in AT.30 gives the unrestricted bound

\[
F_*\le B(\kappa):=
\frac12+\frac K2+\frac K2\sqrt{1+\kappa^2}
-\frac{\kappa(1-K)}2+\frac{\kappa^2K^2}{8}.
\tag{AT.35}
\]

The maximizing width for this quadratic is
\(C=1/2+K(2-\kappa)/4\); no assumption that a cap realizes the
critical supports or this width is required for the upper bound.
On \([3/8,4/5]\),

\[
\begin{aligned}
B'(\kappa)
&=\frac{K\kappa}{2\sqrt{1+\kappa^2}}
-\frac{1-K}{2}+\frac{\kappa K^2}{4}\\
&\le\frac{2K}{5}-\frac{1-K}{2}+\frac{K^2}{5}
=\frac{5K-3}{10}<0.
\end{aligned}
\tag{AT.36}
\]

Hence the largest value occurs at \(\kappa=3/8\), where

\[
B(3/8)=\frac{169}{512}
+\frac{K(167+16\sqrt{73})}{256}.
\tag{AT.37}
\]

The exact rational bounds \(K<29/70\) and
\(\sqrt{73}<171/20\) now give

\[
B(3/8)<\frac{169}{512}
+\frac{29(167+16\cdot171/20)}{70\cdot256}
=\frac{5259}{6400}
=\frac{411}{500}-\frac9{32000}.
\tag{AT.38}
\]

All other cases were bounded strictly below \(41/50\), \(4/5\),
or \(319/400\), each smaller than \(5259/6400\). The earlier
outgoing-only theorem covers the initial interval
\([\pi/4,\arctan(5/4)]\) by a value below \(41/50\).
Fixed-angle attainment and the canonical reduction in Section 1 therefore
prove the universal first inequality of AT.1.

For the exact reference comparison, the same elementary argument as
G1C.6 in [the Gate 1 closure](#proof-full-closure), now with
\(a=149/500\), gives

\[
4a^3+3a-1=-\frac{4551}{31250000}<0,\qquad
\frac M2>\frac{1+4a^2+a-a^3/3}{2}
=\frac{616648051}{750000000}>
\frac{411}{500}.
\tag{AT.39}
\]

This proves AT1. \(\square\)

---

<a id="proof-terminal-geometry"></a>
## Technical proof 37. Terminal facet geometry, width cuts and projection (TP)

Written mathematical reduction, October 10, 2026. This note treats all
three signs of the affine middle roof. It retains the actual outgoing
wall and does not assume a common terminal occupation for shape and
angle variations. Its final exclusion is conditional on an explicitly
stated initial companion-curvature bound, supplied by separate
curvature arguments in [the Gate 2 closure](#proof-partial-closure).

The inputs are [PD](#proof-partial-domain),
[PS](#proof-partial-sources),
[TV](#proof-angle-variation), and the
[negative-tilt completion theorem](#proof-negative-completion).
The all-width [angle exclusion](#proof-initial-angle)
supplies the three visited angles used in Section 1. Gate 2 is not
asserted by this note alone; [the Gate 2 closure](#proof-partial-closure) records the complete
dependency chain.

Labels TP are local. Suppose an above-reference joint partial-cap
maximum exists. Select one with the largest terminal angle, then apply
the score-preserving canonical reductions at that angle. Write

\[
I=[-2C,2C],\qquad J=[-C,C],\qquad a=\alpha<\pi/2,
\qquad c=\cos a,\quad s=\sin a.
\]

Use \(N\) for the actual partial barrier, including the outgoing wall.
All source measures below are the selected finite-source limits of PS.

### 1. Width and tilt cuts that use only three actual angles

The angle exclusion gives \(a>\arctan(8/3)>3\pi/8\). Consequently
the genuine two-wall tents at \(\pi/8,\pi/4,3\pi/8\) all occur in
the partial history. Their maximum is unchanged by horizontal
reflection, which exchanges the first and third tents.

For the purposes of this three-angle comparison only, orient the high
middle endpoint to the right and put

\[
A(-C)=1-h,\quad A(C)=1,\quad
q_-=N(-C),\quad q_+=N(C),\quad 0\le h<1/2.
\]

If the cap was reflected, reflect \(N\) as well. There is no assertion
that the reflected barrier is another partial objective with the same
first outgoing wall. PS's endpoint equations, simply relabeled, give

\[
e_R=\tfrac12+\tfrac h4+\tfrac{3q_+-q_-}{4},\qquad
e_L=\tfrac12-\tfrac{3h}{4}+\tfrac{3q_--q_+}{4}.
\tag{TP.1}
\]

The affine middle roof and concavity imply \(e_R\le1\) and
\(e_L\le1-3h/2\). Eliminating the opposite barrier endpoint from
TP.1 therefore gives the useful direct inequalities

\[
\boxed{e_R\ge\tfrac13+\tfrac h2+\tfrac23q_+,\qquad
e_L\ge\tfrac13-\tfrac{2h}{3}+\tfrac23q_-.}
\tag{TP.2}
\]

In particular the lower bounds used in TW.22,
\(e_R\ge1/3+h/4\) and \(e_L\ge1/3-3h/4\), remain valid even
when one endpoint is charged by the whole outgoing wall. No endpoint
niche box bound is needed for this step.

The short-width proofs TS and GAP in
[the Gate 1 width note](#proof-tilted-width), Parts A--B,
bound exterior area minus the maximum of precisely the three displayed
tents. Their lifted support calculations and all floor/window clips
therefore bound the present score. The wide proof TW in Part C does
the same; its only use of a two-sided endpoint box estimate is to derive
TW.22, for which TP.2 is a stronger replacement. Its other endpoint
inputs are TP.1 and the nonnegativity of \(q_\pm\). Finally INT in
Part D uses only the 45-degree tent and the affine roof. These explicit
transfers give, for every remaining sign of the middle tilt,

\[
\boxed{\frac{1001}{2000}<C<\frac45,\qquad 0\le h<\frac{17}{50}.}
\tag{TP.3}
\]

The horizontal case is included by \(h=0\). This invokes the actual
finite-angle area estimates, not the full-turn maximizer laws.

### 2. Tail data without reflecting the outgoing wall

Return to the original orientation. Write

\[
A(-C)=1-h_L,\qquad A(C)=1-h_R,
\qquad h_L,h_R\ge0,\quad \min(h_L,h_R)=0.
\]

Let \(T_L,T_R\) be the lengths of any height-one top overhangs
outside the left and right ends of \(J\). Thus \(T_L=0\) when
\(h_L>0\), and \(T_R=0\) when \(h_R>0\).

If \(h_R>0\), the negative-tilt theorem already completes the cap
unless

\[
h_R<1-s,\qquad
a<\theta_0:=\pi/2-\arctan(h_R/(2C)).
\tag{TP.4}
\]

Discard that completed branch. Set

\[
b=C+T_R,\qquad H=1-h_R,\qquad
d=\frac{1-Hs}{c},\qquad w_H=c-d.
\tag{TP.5}
\]

In all remaining cases, \(s<H\le1\), and hence

\[
0<d<c,\qquad
0<w_H\le\frac{sc}{1+s}<\frac c2.
\tag{TP.6}
\]

PD's support saturation and PS's facet pinning identify the first
support immediately after \(a\) with the point \((b,H)\). For
positive or horizontal middle this is the right endpoint of the top
face. For negative middle it is \((C,1-h_R)\), until the unused
central normal \(\theta_0\). The second support immediately after
\(a\) is the outer left endpoint \((-2C,e_L)\), and PS excludes
a companion terminal atom.

The first terminal facet therefore has endpoints

\[
(b,H),\qquad (b+m,H-mc/s),\qquad m\ge0,
\tag{TP.7}
\]

where \(m\) is its charged horizontal length. Its shifted endpoints,
the outgoing wall, and its zero are

\[
B_+=(b-c,H-s),\qquad B_-=B_++(m,-mc/s),
\]
\[
R_a(x)=\frac cs(b-d-x),\qquad r_0=b-d.
\tag{TP.8}
\]

### 3. Two unconditional terminal bounds

The terminal corner \(z_a\) satisfies

\[
(z_a)_x-(B_+)_x
=s[1-(b+2C)s+(H-e_L)c]<0.
\tag{TP.9}
\]

Indeed \(b\ge C>1/2\), \(H\le1\), and \(e_L\ge0\). Since
\(a>3\pi/8\), we have \(s>12/13\) and \(c<5/13\), so
\((b+2C)s+(e_L-H)c\ge3Cs-c>1\).

**Terminal facet bound.** One has

\[
\boxed{m\le w_H.}
\tag{TP.10}
\]

Here is the direct extension of PU's largest-angle argument, including
the lower tail height \(H\). If \(m>w_H\), then
\((B_-)_x>r_0\). At every
\(x\in((z_a)_x,(B_-)_x)\), the second terminal wall exceeds
\(R_a(x)\), while the left angle derivative of the first wall is
negative. A sufficiently close earlier quadrant strictly exceeds
\(R_a\) there. Every positive strip exposure or terminal tie must
therefore lie left of \((z_a)_x<(B_+)_x\). TV.3 makes the strict
exposure set null, since its entire derivative integrand is negative;
continuity then gives \(n_a\ge R_a\) on \(J\).

Choose \(\zeta\) between \((z_a)_x\) and \((B_+)_x\), taking
its intersection with \(J\) when appropriate. Immediately after
\(a\), the first supports are the fixed point \((b,H)\). Below
\(\zeta\) their walls decrease with angle, because the shifted
point's abscissa \(b-\cos t\) increases. Above \(\zeta\) their
positive support ends at
\(b-(1-H\sin t)/\cos t\), which stays below \((B_-)_x\) for
a sufficiently small angle increment. The compact intervening
interval has a strict old-history gap; uniform continuity pays every
new first wall there. The new two-wall minima are bounded by those
same first walls. Thus the partial barrier is unchanged for a small
increase of \(a\), contradicting the largest-angle choice. In the
negative case the increment is chosen below \(\theta_0-a\).

**Top projection bound.** The exact source horizontal moment is
\(2C-T_L-T_R\). Uniform convergence on compact positive-barrier
intervals gives

\[
2C-T_L-T_R\ge |\{x\in J:N(x)>0\}|
\ge |J\cap(-\infty,r_0)|.
\]

If \(T_R\ge d\), the last length is \(2C\), impossible because
\(d>0\). Thus \(T_R<d\). Also \(r_0>C-c>0>-C\), so the
same inequality now yields

\[
\boxed{T_L+2T_R\le d.}
\tag{TP.11}
\]

No zero-set convergence or ordinary continuum source-arclength
identity has been assumed in this projection argument.

### 4. The ordinary endpoint box is recovered at small deficit

Put \(H_0(C)=1-\sqrt{1-C^2}\). The unit-height box gives
\(n_a(C),n_a(-C)\le H_0(C)\) for the visited niche: use its
first wall at \(C\) and its second wall at \(-C\), respectively.
The outgoing wall at \(C\) is negative by TP.11, whereas

\[
R_a(-C)=\frac cs(2C+T_R-d)\le 2C\cot a.
\]

For \(C>1/2\),
\(H_0(C)=C^2/(1+\sqrt{1-C^2})\ge C^2/2>C/4\).
Consequently

\[
\cot a\le\tfrac18
\quad\Longrightarrow\quad
\boxed{N(-C),N(C)\le H_0(C).}
\tag{TP.12}
\]

The [three full triangle width proof](#proof-full-triangle)
FT.4--FT.26 uses the three visited tents, the endpoint equations, and
these two box bounds. Every one of those inputs now holds for the
partial score, including after the purely comparative reflection of
Section 1. Its exact upper bound excludes \(C\ge37/50\). Thus

\[
\boxed{\cot a\le1/8\quad\Longrightarrow\quad C<37/50.}
\tag{TP.13}
\]

This is a transfer of a finite-angle scalar upper bound. It does not
assert that a full-turn extremizer theorem applies to the partial cap.

### 5. An initial companion-unit bound suffices

Let \(g\) be the support of the left charged wing. When \(h_L>0\),
this is the usual low-wing surrogate; the omitted high-point second
wall is nonpositive on \(J\). In the other two cases it is the
actual second support. In all cases

\[
g(0)=1-h_L,\qquad g'(0)=C+T_L,\qquad
g(a)=2C\sin a+e_L\cos a.
\tag{TP.14}
\]

Suppose additionally that

\[
0<c\le1/25,\qquad
0\le v(t):=g''(t)+g(t)\le1
\quad\text{for a.e. }0<t<\arcsin(C+w_H).
\tag{TP.15}
\]

This prefix lies before \(a\): TP.13 gives \(C<37/50\), and
TP.6 gives \(C+w_H<19/25<s\). We claim TP.15 is impossible at
the selected maximizer.

For \(x=-C+z\), \(0\le z\le w_H\), the second terminal wall is
strictly negative. Indeed, using \(e_L\le1\),

\[
S_a(x)=e_L-\frac{1-(C+z)s}{c}
\le1-\frac{1-19/25}{1/25}<0.
\tag{TP.16}
\]

At zero the wall limit is \(-h_L\le0\). Therefore a positive
maximum of the whole second-wall family on \([0,a]\) is attained
at an interior angle. Its stationary equation is
\(D_x(t)=x\), where the outer support point has horizontal
coordinate at least \(-2C\). Since \(D_x=X+\sin t\),

\[
\sin t\le C+z\le C+w_H.
\tag{TP.17}
\]

The support representation and TP.15 then give

\[
g(t)\le(1-h_L)\cos t+(C+T_L)\sin t+1-\cos t,
\]
\[
S_t(-C+z)\le-h_L+(T_L+z)\tan t
\le c\,K(C+c/2),\qquad K(x)=\frac{x}{\sqrt{1-x^2}}.
\tag{TP.18}
\]

The last step uses TP.11 and \(z\le w_H=c-d\), which give
\(T_L+z\le c-2T_R\le c\), as well as TP.17. If no positive
maximum exists, the same upper bound for the positive visited niche
is immediate. The surrogate support is continuously differentiable
on the proper used interval by PS after removal of the uncharged
central facet; thus the stationary equation used here introduces
no unexamined support atom.

For \(1/2\le C\le37/50\) and \(0<c\le1/25\),

\[
\boxed{K(C+c/2)<2C-c.}
\tag{TP.19}
\]

To check this exact scalar comparison, its margin decreases with
\(c\), and is concave in \(C\), since \(K\) is convex. It is
enough to check \(c=1/25\) and the two width endpoints. At
\(C=1/2\), \(K(13/25)<2/3<24/25\); at \(C=37/50\),
\(K(19/25)<6/5<36/25\). Both radical bounds follow by squaring
positive quantities: \(169/625<4/13\) and
\(361/625<36/61\).

By TP.8, throughout the same spatial interval,

\[
R_a(-C+z)=\frac cs(2C+T_R-d-z)
\ge\frac cs(2C-c)>cK(C+c/2)\ge n_a(-C+z).
\tag{TP.20}
\]

Thus the strict terminal exposure set contains
\([-C,-C+w_H]\), and by strictness and continuity it contains
a further interval to its right. This endpoint is interior to \(J\).
Its measure is consequently greater than \(w_H\). But PS.34--35
give full terminal occupation on strict exposure and total occupation
\(m\le w_H\), a contradiction.

**Conclusion TP1.** No above-reference largest-angle partial maximizer
can satisfy TP.15. The argument covers positive, horizontal, and the
remaining negative middle tilt, and uses only an initial bound on
the companion curvature. The separate curvature bounds and complete
angle coverage are assembled in [the Gate 2 closure](#proof-partial-closure).

---

<a id="proof-partial-width"></a>
## Technical proof 38. The all-sign partial three-angle width cut (WC)

Written mathematical proof, October 10, 2026. This note transfers the
three full-triangle comparison [FT](#proof-full-triangle)
to the actual partial score at every remaining terminal angle. It replaces
FT's two-sided endpoint niche box estimate by the partial endpoint
identities and a joint bound on the two positive-floor losses. The three
geometric niche payments remain the actual tents at
\(\pi/8,\pi/4,3\pi/8\).

The inputs are the [partial endpoint and source theorem
PS](#proof-partial-sources), the [all-width terminal
angle exclusion AT](#proof-initial-angle), and the
three-angle transfers in [TP, Section 1](#proof-terminal-geometry).
No upper bound on either endpoint value of the partial barrier is used.
There is no reflection of the outgoing constraint in the variational
problem.

### 1. Statement and the finite-angle comparison

Suppose an above-reference joint partial-cap maximum exists, and choose
the largest-angle canonical representative used in PS and TP. Write
\(C=W/4\). AT and TP supply

\[
\alpha>\arctan(8/3)>3\pi/8,\qquad
\frac{1001}{2000}<C<\frac45,\qquad 0\le h<\frac{17}{50},
\tag{WC.1}
\]

where \(h\) is the absolute height difference between the middle
endpoints. The conclusion is

\[
\boxed{C<\frac{37}{50}.}
\tag{WC.2}
\]

More precisely, the following comparison excludes the complementary
width range. Put

\[
I=[-a,a],\qquad J=[-a/2,a/2],\qquad a=2C.
\]

For this finite-angle comparison only, label the high middle endpoint
as the right one and write

\[
A(-a/2)=1-h,\qquad A(a/2)=1,\qquad
\frac{37}{25}\le a\le\frac85,\quad 0\le h\le\frac{17}{50}.
\tag{WC.3}
\]

If this requires reflecting the cap, reflect its actual barrier \(N\)
at the same time. The maximum of the three displayed tents is unchanged
by this reflection: it exchanges the tents at \(\pi/8\) and
\(3\pi/8\), and preserves the one at \(\pi/4\). Thus the reflected
\(N\) still dominates those three actual tents, whether or not it is
itself a partial objective with a first outgoing wall.

Let

\[
q_\pm=N(\pm a/2),\qquad e_R=A(a),\qquad e_L=A(-a).
\]

PS's endpoint identities, with the same relabeling, are

\[
e_R=\frac12+\frac h4+\frac{3q_+-q_-}{4},\qquad
e_L=\frac12-\frac{3h}{4}+\frac{3q_--q_+}{4}.
\tag{WC.4}
\]

We prove that every cap and nonnegative barrier satisfying these
geometric hypotheses, WC.4, and domination of the three tents obeys

\[
\boxed{\int_{I\setminus J}A-\int_JN
<\frac{25811237}{31500000}<\frac{41}{50}<\frac M2.}
\tag{WC.5}
\]

This statement supplies WC.2 for all three signs of the original middle
tilt. It requires neither unit source curvature nor any estimate on the
terminal facet mass.

### 2. Replace FT's endpoint bounds

Use FT's constants and lifted support notation:

\[
r=\sqrt2,\quad k=r-1,\quad
c_8=\cos(\pi/8),\quad s_8=\sin(\pi/8),
\]
\[
\gamma=1-r/2,\qquad t=2c_8-r,\qquad
\mathsf A=1-k,\quad \mathsf b=2-k,\quad \mathsf d=3r-1.
\tag{WC.6}
\]

Raise the low charged wing by \(h\), put the middle roof at height one,
and keep the high charged wing. This is FT's genuine lifted cap
\(\widehat U\). Put

\[
u=rh_{\widehat U}(\pi/4)-1,\qquad
v=rh_{\widehat U}(3\pi/4)-1,\qquad
M_0=(u+v)/2,
\]
\[
w_R=a-u,\qquad w_L=a-v+h.
\tag{WC.7}
\]

Here the arguments of \(h_{\widehat U}\) denote the angles of its
outward normals. In the original cap the two 45-degree support
parameters are \(u\) and \(v-h\), so its actual 45-degree tent is

\[
\bigl[\min\{u-k-x,\ v-h-k+x\}\bigr]_+.
\]

Concavity and the height bound give \(e_R\le1\) and
\(e_L\le1-3h/2\). Solving WC.4 for the opposite endpoint and using
\(q_\pm\ge0\) gives

\[
e_R\ge\frac13+\frac h2+\frac23q_+\ge\frac13+\frac h2,
\qquad
e_L\ge\frac13-\frac{2h}{3}+\frac23q_-\ge\frac13-\frac{2h}{3}.
\tag{WC.8}
\]

The actual endpoint support inequalities are
\(e_R\le1-w_R\), \(e_L\le1-w_L\). Also, adding WC.4 gives

\[
e_R+e_L=1-\frac h2+\frac{q_-+q_+}{2}\ge1-\frac h2.
\]

Consequently the support deficits satisfy

\[
\boxed{
\begin{aligned}
0&\le w_R\le \frac23-\frac h2,\\
0&\le w_L\le \frac23+\frac{2h}{3},\\
w_R+w_L&\le1+\frac h2.
\end{aligned}}
\tag{WC.9}
\]

Nonnegativity also follows directly from the lifted support bounds and
the affine extension of the original middle roof. These inequalities
replace FT.8–FT.9. In particular their sum retains the bound
\(M_0-h/2\ge a-1/2-h/4\) used in FT.11 and FT.15. No endpoint
niche box has entered the argument.

### 3. Bound the two floor losses together

FT.10's disjoint exterior triangles, FT.11–FT.12's fitting of the
two full additional niche triangles, and FT.13's exact positive-floor
correction use actual supports and the three genuine tents. They
therefore hold with \(N\) in place of the full-turn niche. In
particular, their floor correction is at most

\[
\gamma\bigl[(w_R-t)_+^2+(w_L-t)_+^2\bigr].
\tag{WC.10}
\]

We now maximize this expression on the entire enlarged polygon WC.9.
Set

\[
R_h=\frac23-\frac h2,\qquad
L_h=\frac23+\frac{2h}{3},\qquad S_h=1+\frac h2.
\]

The cost is nondecreasing in each coordinate. Since
\(R_h+L_h-S_h=(1-h)/3>0\), every feasible point can be increased
coordinatewise to the segment \(w_R+w_L=S_h\). The restriction of
the cost to this segment is convex, so its maximum is at one of

\[
(R_h,S_h-R_h)=\left(\frac23-\frac h2,\frac13+h\right),
\qquad
(S_h-L_h,L_h)=\left(\frac13-\frac h6,\frac23+\frac{2h}{3}\right).
\tag{WC.11}
\]

The second pair has the same sum and is at least as spread as the
first: its smaller entry \(1/3-h/6\) is no larger than either
entry of the first, and its larger entry is no smaller than either.
For the convex function \(\phi(w)=(w-t)_+^2\), this implies that
the second pair has at least as large a total cost. Explicitly, each
entry of the first pair is a convex combination of the two entries
of the second, with complementary coefficients; convexity and addition
give the comparison.

The elementary bounds \(1/3<t<2/3\) hold, and hence the smaller
entry of the second pair has zero cost. We obtain the exact uniform
replacement for FT.14:

\[
\boxed{
\gamma\bigl[(w_R-t)_+^2+(w_L-t)_+^2\bigr]
\le \gamma\left(D+\frac{2h}{3}\right)^2,
\qquad D:=\frac23-t>0.}
\tag{WC.12}
\]

This is a joint estimate; bounding the two deficits separately would
discard the sum constraint in WC.9.

### 4. The same support concavity completes the comparison

Retain the genuine exterior and niche payments in FT.15–FT.17, changing
only the floor correction to WC.12. The undepleted peak sum uses
\(e_R+e_L\ge1-h/2\), which was proved above. Thus FT's function
\(G_h(a,u,v)\), with all 45-degree floor and window clipping retained,
satisfies

\[
\int_{I\setminus J}A-\int_JN
\le G_h(a,u,v)+\gamma\left(D+\frac{2h}{3}\right)^2.
\tag{WC.13}
\]

FT.18–FT.24 prove joint concavity of \(G_h\) in the geometric support
variables and verify its unclipped support critical point at
\(a_0=37/25\). Those calculations use no endpoint niche estimate.
Consequently, for every \(a\ge a_0\) in WC.3,

\[
G_h(a,u,v)\le K_0(h),
\]
\[
K_0(h)=B(a_0)-\frac{kh}{2}-\frac{h^2}{8}
-\frac29\left(\sigma_0-\frac{\mathsf A h}{4}\right)^2,
\tag{WC.14}
\]

where

\[
B(a)=a-\frac{(a-k)^2}{2},\qquad
\sigma_0=\frac{\mathsf d a_0}{2}-(4c_8-2),\qquad
\frac{703}{1000}<\sigma_0<\frac{71}{100}.
\tag{WC.15}
\]

This retains all of FT's genuine tents; the larger partial barrier
only strengthens the required niche lower bound.

### 5. An exact decreasing scalar bound

Let

\[
F(h)=K_0(h)+\gamma\left(D+\frac{2h}{3}\right)^2.
\]

Differentiation gives the affine expression

\[
\begin{aligned}
F'(h)={}&-\frac k2+\frac{\mathsf A\sigma_0}{9}
+\frac{4\gamma D}{3}\\
&+h\left(-\frac14-\frac{\mathsf A^2}{36}
+\frac{8\gamma}{9}\right).
\end{aligned}
\tag{WC.16}
\]

Use

\[
k>\frac25,\quad \mathsf A<\frac35,\quad
\gamma<\frac3{10},\quad \sigma_0<\frac{71}{100},
\]
\[
D=\frac23-2c_8+r
<\frac23-\frac{1846}{1000}+\frac{99}{70}
<\frac{47}{200}.
\tag{WC.17}
\]

The radical bounds here are the same
\(c_8>923/1000\), \(r<99/70\) already checked in FT.20.
The constant and linear coefficients in WC.16 respectively obey

\[
-\frac k2+\frac{\mathsf A\sigma_0}{9}
+\frac{4\gamma D}{3}
<-\frac15+\frac{71}{1500}+\frac{47}{500}
=-\frac{22}{375},
\]
\[
-\frac14-\frac{\mathsf A^2}{36}+\frac{8\gamma}{9}
<\frac1{60}.
\]

It follows, on the whole tilt interval in WC.3, that

\[
F'(h)<-\frac{22}{375}+\frac{17}{3000}
=-\frac{53}{1000}<0.
\tag{WC.18}
\]

Thus the complete upper bound is maximal at \(h=0\). Moreover,

\[
\gamma D^2<\frac3{10}\left(\frac{47}{200}\right)^2
=\frac{6627}{400000}<\frac{17}{1000}.
\]

Since \(B(a_0)=(62/25)k-72/625\), the same rational endpoint
certificate as FT.26 applies:

\[
\begin{aligned}
\int_{I\setminus J}A-\int_JN
&<\frac{62}{25}\frac{29}{70}-\frac{72}{625}
-\frac29\left(\frac{703}{1000}\right)^2
+\frac{17}{1000}\\
&=\frac{25811237}{31500000}
<\frac{41}{50}.
\end{aligned}
\tag{WC.19}
\]

The final strict rational gap is \(18763/31500000\). This proves
WC.5 and excludes WC.3. Combining with WC.1 gives WC.2 for every
remaining sign of the middle roof and every remaining terminal angle.
In particular, the width conclusion requires no small-terminal-deficit
hypothesis. The sharp partial-cap comparison on the smaller width
interval uses the separate arguments assembled in [the Gate 2 closure](#proof-partial-closure).

---

<a id="proof-positive-local-laws"></a>
## Technical proof 39. Local positive-tilt source and support laws (PU)

Written proof, independently checked within the research session,
October 10, 2026. This is a conditional sharp reduction for the actual
partial spatial objective.
It does not assume a common occupation for angle and support variations,
a terminal first-moment law, or a full-turn completion.

The fixed-angle inputs are [PD](#proof-partial-domain)
and [PS](#proof-partial-sources). The exact one-sided
angle derivative is [TV1–TV3](#proof-angle-variation).
The first-unit hypothesis below is a separate curvature input, not a
consequence asserted by this note. The complete proof is assembled in
[the Gate 2 closure](#proof-partial-closure).

### 1. Statement and normalization

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

### 2. Exact support data and the local partial-source laws

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
upper bound. Write \(T_n=\tan(\delta_n/2)\), and let \(\ell_{n,j}\) be the
charged facet length at a paired first-source grid normal. The retained
WR threshold identities give
\[
\tau_{n,j}\le
\tan(\delta_n)(|q^+_{n,j}|+T_n)+(2T_n-L^{\rm circ}_{n,j})_+
\le\tan(\delta_n)(|q^+_{n,j}|+T_n)+(2T_n-\ell_{n,j})_+.
\]
Here \(q^+_{n,j}\) uses the forward companion secant support derivative.
Combining with PS.11 and separating
\(\ell_{n,j}\ge2T_n\) from \(\ell_{n,j}<2T_n\) gives
\[
\ell_{n,j}\le
\kappa(q^+_{n,j})\delta_n+O(\delta_n^2)+b_{n,j}
\]
uniformly on each compact regular interval. Outer-only normals have
charged length at most \(b_{n,j}\). Semiconvexity, uniform support
convergence and the \(C^1\) limit on that interval make these secant
derivatives converge locally to the companion derivative, in particular
in \(L^1\). Sum the estimate against nonnegative continuous angular
tests. The summed \(O(\delta_n^2)\) and \(b\)-errors vanish, while PS
identifies the weak charged-curvature limit. This proves
\(u\le\kappa(q)\). Interchanging the paired normal families proves
\(v\le\kappa(p)\). The extra outgoing wall can only hide the exposed pieces;
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

### 3. A short terminal facet, using only a one-sided angle variation

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

### 4. A first-unit wing forces the companion wing to be unit

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

---

<a id="proof-reflected-local-laws"></a>
## Technical proof 40. The all-sign reflected source system and energy calculation (RP)

Written mathematical proof, October 10, 2026. The theorem below
excludes every above-reference partial-cap maximum with
`0<cos(a)<=1/25`, covering positive, horizontal, and the remaining
negative middle tilt. The inputs are the canonical domain reductions
[PD](#proof-partial-domain), the fixed-angle source
and endpoint laws [PS](#proof-partial-sources),
the local support inequalities in
[PU](#proof-positive-local-laws), and the all-sign
terminal bounds [TP](#proof-terminal-geometry).
The reflection exchanges only the local support equations; it does
not assert reflection invariance of the partial spatial objective.

For reviewability, Section 1 lists the exact modular hypotheses.
TP supplies all of them for an above-reference largest-angle
maximizer with `0<cos(a)<=1/25`. This proves that entire terminal
angle branch. The other angles and the original-motion implication
are assembled in [the Gate 2 closure](#proof-partial-closure).

### 1. Geometric hypotheses for the three middle orientations

Use I=[-2C,2C], J=[-C,C], and assume

    1/2<C<=37/50, 0<c=cos(a)<=1/25,
    s=sin(a), epsilon=pi/2-a=asin(c),
    k=(1-s)/c=c/(1+s), w=sk<c/2.                  (RP1)

Suppose the cap is a canonical saturated joint maximizer, so the
fixed-angle PS source and endpoint laws apply. The terminal first
facet has horizontal length m. The first harmonic unused tail is
supported at (b,H), where the following alternatives cover the
middle signs:

* Positive tilt: b=C+T_R, H=1, g is the low left-wing surrogate,
  with g(0)=1-h and g'(0)=C. Here 0<h<1/2.
* Horizontal middle: b=C+T_R, H=1, the left top overhang is T_L,
  and g(0)=1, g'(0)=C+T_L.
* Remaining negative tilt: b=C, H=1-h, with 0<h<1-s. Replace the
  actual first support by its right-wing surrogate. Its unused
  tail is supported at (C,1-h), removing the central-facet atom
  that lies in the unused arc. On all visited angles the surrogate
  equals the actual first support. Here g(0)=1 and
  g'(0)=C+T_L.

All three have the companion unused tail

    g(t)=2C sin(t)+e_L cos(t), a<t<pi/2.           (RP2)

There is no companion terminal atom. Put

    D_H=(1-Hs)/c, m_max=c-D_H=s(H-s)/c.

Assume the exact terminal consequences

    0<=m<=m_max<=w,
    T_L+2T_R<=D_H.                               (RP3)

These are TP.10–11 for all three signs. For positive tilt they
also occur as PU.16–17, with T_L=0 and D_H=k. The present proof
uses these exact terminal bounds rather than assuming a terminal
first moment.

Finally suppose the ordinary box estimate holds for the partial
barrier at the left middle endpoint:

    N(-C)<=H_C=1-sqrt(1-C^2)<1/3.                 (RP4)

TP.12 supplies this estimate, because c<=1/25 implies cot(a)<1/8;
TP.13 supplies C<37/50. The comparison with 1/3 uses
(37/50)^2<5/9. Only this upper bound, not a lower endpoint pressure
estimate, is needed below.

The first conclusion is

    v=g''+g<=1 a.e. on [0,asin(C+w)].              (RP5)

The second conclusion is a contradiction with terminal source mass.
Thus RP1–RP4, with the standard local partial-source laws, exclude
all three orientations. For the claimed small-deficit branch these
are all established prerequisites. Any extension to larger c must
recheck the displayed parameter bounds and quantitative certificate.

### 2. Reflection of the support system and the terminal impulse

Write L=pi/2. On regular used angles use

    p=f'-g+1, q=g'+f-1,
    p'=u-1-q, q'=v-1+p.

At r=L-t set

    P(r)=-q(L-r), Q(r)=-p(L-r),
    U(r)=v(L-r), V(r)=u(L-r).

Then

    P'=U-1-Q, Q'=V-1+P.                           (RP6)

The arm, curvature and same-sign local source inequalities become

    P<=1, Q>=-1, U<=kappa(Q), V<=kappa(P),
    U=0, V<=1/2 on {P>0,Q>0},
    V=0, U<=1/2 on {P<0,Q<0}.                    (RP7)

They hold on the reflected used interval. In the positive-tilt case,
the final interval beyond the removed central switch has U=V=0
directly, so no arm inequality is asserted for the surrogate there.
The horizontal and negative cases have no removed atom in the
visited interval.

The initial data in the two relevant cases are

    (P(0),Q(0))=(e,d-1),
    e=e_L, d=3C+T_R               (positive/horizontal),
    e=e_L+h, d=3C                (negative).      (RP8)

Both densities vanish on (0,epsilon). At epsilon there is just one
impulse in the second reflected density, of size

    j=m/s<=k.

Thus P is continuous and Q jumps upward by j. There are no further
atoms on the reflected used interval. In particular the unused
negative-tilt central facet has already been removed from f; keeping
it would give the wrong initial height and an extra spurious impulse.

The endpoint pressure and RP4 bound the initial parameters. For
positive tilt,

    e_L=1/2-3h/4+(3N(-C)-N(C))/4<3/4.

The horizontal case has h=0. For negative tilt,

    e=e_L+h=1/2+5h/4+(3N(-C)-N(C))/4
      <3/4+5/4000<19/25,

because h<1-s=c^2/(1+s)<1/1000. No positive lower bound on e is
needed beyond e>=0. From RP1–RP3,

    k<21/1000, epsilon<41/1000,
    3/2<d<2231/1000, 0<=e<3/4   (positive/horizontal),
    3/2<d<=111/50,  0<=e<19/25  (negative).       (RP9)

For k use s>99/100, so k<4/199<21/1000. For epsilon, sin(41/1000)
>=41/1000-(41/1000)^3/6>1/25. Also T_R<=k/2, proving the stated
d bound.

The free initial trajectory is

    P(r)=1+(e-1)cos(r)-d sin(r),
    Q(r)+1=d cos(r)+(e-1)sin(r).                  (RP10)

Throughout this short initial gap Q>0: its terminal value satisfies
Q(epsilon-)+1=ds-(1-e)c>(3/2)(99/100)-1/25>1.

### 3. Exact energy paid by the terminal impulse

Let E=(P-1/2)^2+(Q+1)^2. At r=0,
E_0=(e-1/2)^2+d^2. Direct expansion of RP10 and the Q impulse gives

    E(epsilon+)-E_0
      =(1-e)(1-s)-dc+2j[ds-(1-e)c]+j^2.           (RP11)

The bracket ds-(1-e)c is positive, so the right side increases with
j>=0. At j=k it simplifies exactly to

    k^2[(2e-1+k^2)/(1+k^2)-dc].                   (RP12)

Since e<=19/25 and k<21/1000, this is less than

    (53/100)k^2<1/4000.

Therefore

    E(epsilon+)<=E_0+1/4000.                     (RP13)

This estimate is valid even when P has already become negative in
the unused initial gap. It is an exact impulse calculation, not a
smooth-angle approximation.

In the reflected ++ region after the impulse, RP7 gives

    E'=2(Q+1)(V-1/2)<=0.                          (RP14)

Whenever the first P-zero occurs after the impulse, RP13–14 imply

    Q_at_P_zero+1<=sqrt(Z),
    Z=d^2-e(1-e)+1/4000.                         (RP15)

If P is already nonpositive at the impulse, the same inequality
holds there: (P-1/2)^2>=1/4. The component still has Q>0 at the
impulse, by RP10.

### 4. Duration of a possible reflected first-source excess

Any U>1 requires Q>1, except the other possibility Q<-1 which is
excluded by the arm bound. In the ++ regime U=0. Every positive-Q
component after the initial one has amplitude at most 1/8 by the
same-sign propagation argument, so it cannot contain U>1.

After P has become nonpositive, on the remaining part of the initial
component with Q>1,

    P'<=-1.

Starting at P<=0 and writing rho for elapsed time, P<=-rho. For
rho<=1, RP7 gives

    Q'<=-1/2-rho/2.

When P lies in [-1,0] this is V<=(1-P)/2; if P<-1, the stronger
bound V<=-P gives Q'<=-1. Thus RP15 implies that every possible
remaining excess has ended by elapsed time

    D(Z)=sqrt(1+4 max(sqrt(Z)-2,0))-1.            (RP16)

This is zero for Z<=4 and equals sqrt(4sqrt(Z)-7)-1 for Z>4,
provided the displayed time is less than one. All bounds below
are much smaller than one and therefore close the comparison
without a circular time assumption.

#### 4.1 Small initial P needs no lower endpoint estimate

Suppose e<=1/4. As long as P>0 in the initial component,
Q'>=-1 and the terminal jump is upward. Since U=0 there,

    Q(r)>=d-1-r,
    P(r)<=e-dr+r^2/2.

Thus its first P-zero is no later than

    tau<=d-sqrt(d^2-2e)<1/5.                     (RP17)

The last inequality uses d>3/2 and e<=1/4. The component cannot
end through Q=0 earlier, because Q>d-1-1/5>0 on this interval.
If the P-zero occurs before the impulse, start the excess comparison
at epsilon instead; there was no curvature during the unused gap.
In either case the comparison starts by max(tau,epsilon)<1/5.

For e<=1/4, RP9 gives Z<5, hence sqrt(Z)<9/4 and
D(Z)<sqrt(2)-1<5/12. Therefore every reflected excess ends before

    1/5+5/12=37/60<7/10.                         (RP18)

This handles all arbitrarily small positive e as well as the limiting
case e=0. It removes any need for an h-dependent lower bound on e_L.

#### 4.2 Larger initial P: two exact endpoint certificates

Now e>=1/4. At the impulse,

    P(epsilon)=1-(1-e)s-dc>=e-dc>0.

Hence the first P-zero follows the impulse and satisfies RP17's
time formula, without its final numerical bound. If Q reaches zero
first, no initial excess occurs. Otherwise combine RP15–16 to obtain

    last_excess_time<=W_+(d,e),
    W_+(d,e)=d-sqrt(d^2-2e)+D(Z).                 (RP19)

If d<=2, then Z<4 on 1/4<=e<=19/25, so there is no excess after
the P-zero. It remains to bound RP19 for d>2 and Z>4.

On Z>4 put A=sqrt(d^2-2e), S=sqrt(Z), Q0=sqrt(4S-7). The
unclipped expression W has derivatives

    W_e=1/A+(2e-1)/(Q0 S),
    W_d=1-d/A+2d/(Q0 S).                         (RP20)

For e in [1/4,19/25] and d in [2,2231/1000], these are positive.
Indeed, if e<1/2 the negative term in W_e has absolute value at
most 1/4, while 1/A>=1/d>4/9. If e>=1/2 both terms are nonnegative.
Also d/A<4/3, S<sqrt(5)<9/4 and Q0<sqrt(2)<3/2, so
W_d>-1/3+32/27>0.

The clipped W_+ remains increasing in e across Z=4: below that
level it is just d-sqrt(d^2-2e), increasing in e. If increasing e
to its upper endpoint places Z below 4, the remaining time is at
most 2-sqrt(4-38/25)<9/20<7/10. Otherwise increasing d to its
upper endpoint keeps Z>4, where W is increasing. It therefore
suffices to check these two endpoint pairs:

    (d,e)=(2231/1000,3/4),
    (d,e)=(111/50,19/25).                         (RP21)

At the first pair,

    d-sqrt(d^2-2e)<11/30,
    Z=4790111/1000000<(219/100)^2,
    D(Z)<1/3.

For the first time comparison, squaring reduces it to
d>1471/660, satisfied by 2231/1000. For the duration comparison,
4(219/100)-7=44/25<16/9. Hence W<7/10.

At the second pair,

    d-sqrt(d^2-2e)<3/8,
    Z=18985/4000<(109/50)^2,
    D(Z)<5/16.

The first inequality follows from (3/4)d>38/25+9/64.
The second duration comparison is 4(109/50)-7=43/25<441/256.
Thus W<11/16<7/10. Together with RP18,

    U(r)<=1 a.e. for r>=7/10 on the reflected used interval.       (RP22)

Any final removed positive-tilt interval has U=0 directly, so the
conclusion includes it as well.

---

<a id="proof-weighted-moment"></a>
## Technical proof 41. The weighted companion moment and exact terminal margin (MP)

Written mathematical proof, October 10, 2026. This note strengthens
the conditional companion-prefix exclusion in
[TP, Section 5](#proof-terminal-geometry). It uses
the all-angle width bound [WC](#proof-partial-width), the
terminal mass and top-projection bounds TP.10--11, and the regular
charged-wing measure and terminal occupation theorem
[PS](#proof-partial-sources).

The conclusion is conditional on a companion-curvature estimate on
an explicitly shorter initial interval. Curvature exceeding one after
that interval does not weaken the comparison. A weighted allowance for
excess inside the interval is also recorded. No reflection of the
partial spatial objective or common shape/angle terminal occupation is
assumed. Labels MP are local.

### 1. Geometric setting and the conditional exclusion

Suppose an above-reference partial-cap maximum exists. Choose its
largest terminal angle and the canonical representative used in TP.
All-width [AT](#proof-initial-angle), TP, and WC
give

\[
I=[-2C,2C],\qquad J=[-C,C],\qquad
\frac12<C<\frac{37}{50},\qquad
0<c:=\cos a<\frac3{\sqrt{73}},\qquad s:=\sin a.
\tag{MP.1}
\]

Retain TP's original, unreflected orientation and notation:

\[
A(-C)=1-h_L,\quad A(C)=1-h_R,\quad
\min(h_L,h_R)=0,\quad H=1-h_R,
\]
\[
d=\frac{1-Hs}{c},\qquad w=c-d,\qquad
0<d<c,\qquad 0<w<\frac c2,
\]
\[
T_L+2T_R\le d,\qquad m\le w.
\tag{MP.2}
\]

Here \(T_L,T_R\) are the height-one top overhangs and \(m\) is the
horizontal length of the charged first terminal facet. The negative
tilt branch already completed by the negative-tilt theorem has been
discarded, so \(s<H\le1\). The actual outgoing wall is

\[
R_a(-C+z)=\frac cs(2C+T_R-d-z).
\tag{MP.3}
\]

Let \(g\) be the support of the left charged wing. In positive tilt
this is the low-wing surrogate; in the other two signs it is the
actual companion support. Its initial data are

\[
g(0)=1-h_L,\qquad g'(0+)=C+T_L.
\tag{MP.4}
\]

Write \(v=g''+g\ge0\) for its regular curvature density. PS, after
removing the uncharged central facet when required, makes \(g\)
continuously differentiable on the proper used interval and gives no
interior singular curvature or companion terminal atom. All support
identities below are consequently valid by absolute continuity.

Put

\[
A_0=C-T_L,\qquad \theta=\arcsin A_0,\qquad
G(x)=\sqrt{1-x^2},\qquad K(x)=\frac{x}{\sqrt{1-x^2}},
\qquad \lambda=K(A_0).
\tag{MP.5}
\]

The possible weighted early excess is

\[
\mathcal E_\theta
=\int_0^\theta (v(r)-1)_+
\bigl(\lambda\cos r-\sin r\bigr)\,dr.
\tag{MP.6}
\]

The kernel is nonnegative on this interval. The conditional theorem is

\[
\boxed{\mathcal E_\theta\le\frac{39}{4400}c
\quad\Longrightarrow\quad\text{no such maximum exists}.}
\tag{MP.7}
\]

In particular, it suffices that

\[
\boxed{v\le1\text{ a.e. on }(0,\arcsin(C-T_L)).}
\tag{MP.8}
\]

The stronger assumption \(v\le1\) on \((0,\arcsin C)\) is often
more convenient. Both intervals are shorter than the old TP.15
interval \((0,\arcsin(C+w))\).

### 2. Every relevant companion-wall maximum is interior and localized

First observe that

\[
0<C-T_L<C+w\le C+\frac c2<s<1.
\tag{MP.9}
\]

The first inequality follows from \(T_L\le d<c<C\). For the last
nontrivial inequality, its left side minus \(\sqrt{1-c^2}\) increases
with both \(C\) and \(c\). At their enlarged endpoints it is
negative because

\[
\frac{37}{50}+\frac3{2\sqrt{73}}
<\frac8{\sqrt{73}},\qquad
37^2\,73=99937<105625=325^2.
\]

For \(x=-C+z\), \(0\le z\le w\), define

\[
S_t(x)=\frac{g(t)-1+x\sin t}{\cos t}\qquad(0\le t\le a).
\]

The omitted high charged wing in the positive-tilt surrogate
contributes only nonpositive companion walls on \(J\): each of its
points has \(X\ge C\), \(Y\le1\), and its wall is at most
\(1-\sec t+(x-C)\tan t\le0\). The affine middle segment is
controlled by its endpoints: the low endpoint belongs to the left
wing and the high endpoint has the same nonpositive wall bound.
Therefore in every sign the positive
visited niche satisfies

\[
n_a(x)\le\left[\max_{0\le t\le a}S_t(x)\right]_+.
\tag{MP.10}
\]

The shifted companion support point has coordinates

\[
D_x=-g'\cos t-(g-1)\sin t,\qquad
D_y=-g'\sin t+(g-1)\cos t.
\tag{MP.11}
\]

Its actual outer abscissa is \(X=D_x-\sin t\ge-2C\), and direct
differentiation gives

\[
S'_t(x)=\frac{x-D_x(t)}{\cos^2t},\qquad
D_x'=(1-v)\cos t,\qquad D_y'=(1-v)\sin t.
\tag{MP.12}
\]

In particular \(S'_t(x)<0\) whenever \(\sin t>C+z\). Since
\(C+z<s\), a positive maximum of this companion-wall family is
attained in \((0,a)\); its value at zero is \(-h_L\le0\), and
the function is strictly decreasing after \(\arcsin(C+z)\).
At a positive maximizing angle \(t\),

\[
D_x(t)=x,\qquad S_t(x)=D_y(t),\qquad
\sin t\le C+z.
\tag{MP.13}
\]

This argument does not require the terminal companion wall to be
negative. It also handles a maximum at the joining point
\(\arcsin(C+z)\), which remains an interior differentiability point.

### 3. A weighted moment needs only the shorter prefix

MP.4 gives \(D_x(0)=-C-T_L\), \(D_y(0)=-h_L\). At an angle
satisfying MP.13, integration of MP.12 yields

\[
D_y(t)+h_L-\lambda(T_L+z)
=\int_0^t(1-v(r))\bigl(\sin r-\lambda\cos r\bigr)\,dr.
\tag{MP.14}
\]

The kernel changes sign precisely at \(r=\theta\). Before
\(\theta\), the integrand is at most
\((v-1)_+(\lambda\cos r-\sin r)\). After \(\theta\), its
upper bound is simply \(\sin r-\lambda\cos r\), since \(v\ge0\).
Consequently, when \(t\ge\theta\),

\[
D_y(t)+h_L
\le G(A_0)-\cos t+\lambda(C+z-\sin t)
+\mathcal E_\theta.
\tag{MP.15}
\]

The right side apart from the excess has derivative
\(\sin t-\lambda\cos t\ge0\) on \([\theta,\pi/2)\).
Since \(t\le\arcsin(C+z)\), it is at most
\(G(A_0)-G(C+z)\). If \(t<\theta\), MP.14 instead gives
\(D_y+h_L\le\lambda(T_L+z)+\mathcal E_\theta\); monotonicity
of \(K\) gives the same conclusion because

\[
\lambda(T_L+z)=K(A_0)(C+z-A_0)
\le\int_{A_0}^{C+z}K(q)\,dq
=G(A_0)-G(C+z).
\]

Using MP.10 also when there is no positive maximum proves

\[
\boxed{
n_a(-C+z)
\le\bigl[-h_L+G(C-T_L)-G(C+z)+\mathcal E_\theta\bigr]_+
\le G(C-T_L)-G(C+z)+\mathcal E_\theta.}
\tag{MP.16}
\]

The last right side is nonnegative. This is why curvature exceeding
one after \(\theta\) carries no adverse error: its weighted kernel
in MP.14 is already nonnegative.

### 4. Reduce the terminal comparison to one symmetric average

The outgoing wall decreases with \(z\), while the circle difference
in MP.16 increases. It is enough to compare them at \(z=w=c-d\).
Using \(T_R\ge0\) and \(T_L\le d\), their gap is at least

\[
\frac cs(2C-c)-\bigl[G(C-d)-G(C+c-d)\bigr].
\tag{MP.17}
\]

Moreover \(H\le1\) implies

\[
d\ge\delta:=\frac{1-s}{c}=\frac c{1+s}.
\]

The bracket in MP.17 decreases with \(d\), since its derivative is
\(K(C-d)-K(C+c-d)<0\). It is therefore at most its value at
\(d=\delta\). Put

\[
\eta=\delta-\frac c2
=\frac{c^3}{2(1+s)^2}\ge\frac{c^3}{8},\qquad
\mathcal A_q(y)=\frac1q\int_{y-q/2}^{y+q/2}K(x)\,dx.
\tag{MP.18}
\]

The desired normalized gap is bounded below by

\[
\frac{2C-c}{s}-\mathcal A_c(C-\eta).
\tag{MP.19}
\]

On every interval used below, \(K\) is increasing and convex.
Thus \(\mathcal A_q(y)\) is increasing in both \(y\) and \(q\),
and is convex in \(y\). Width monotonicity follows, for example,
by writing the average on \([-1/2,1/2]\) and pairing the positive
and negative integration variables; the derivative in \(q\) is
nonnegative because \(K'\) is increasing. A linear function of
\(C\) minus either fixed-width average is therefore concave in
\(C\), so its lower bound can be checked at the two width endpoints.

### 5. Exact scalar margin on the complete remaining angle interval

#### 5.1 The range \(0<c\le1/3\)

Here

\[
\mathcal A_c(C-\eta)\le\mathcal A_{1/3}(C).
\]

Also \((2C-c)/\sqrt{1-c^2}\) decreases with \(c\), since its
derivative is \((2Cc-1)/(1-c^2)^{3/2}<0\). The bound
\(\sqrt2<99/70\) gives

\[
\frac{2C-c}{s}>\frac{35}{33}\left(2C-\frac13\right).
\tag{MP.20}
\]

At \(C=1/2\),

\[
\mathcal A_{1/3}(1/2)=2\sqrt2-\sqrt5
<\frac{23}{35}<\frac23,
\]

using \(\sqrt2<10/7\), \(\sqrt5>11/5\). The gap from the
right side of MP.20 is greater than
\(70/99-2/3=4/99\). At \(C=37/50\),

\[
\mathcal A_{1/3}(37/50)
=\frac{8\sqrt{59}-\sqrt{1001}}{25}<\frac65,
\]

using \(\sqrt{59}<77/10\), \(\sqrt{1001}>158/5\). The gap
is greater than \(602/495-6/5=8/495\). All four radical bounds
follow by squaring positive rationals. Concavity in \(C\) now gives

\[
\frac{2C-c}{s}-\mathcal A_c(C-\eta)>\frac8{495}
>\frac{39}{4400}.
\tag{MP.21}
\]

#### 5.2 The range \(1/3\le c\le3/\sqrt{73}\)

Use

\[
\eta\ge\frac1{216},\qquad c<q:=\frac{44}{125},\qquad
s\le\frac{2\sqrt2}{3}<\frac{33}{35}.
\]

The rational angle bound follows from
\(9\cdot15625=140625<141328=1936\cdot73\). Thus

\[
\mathcal A_c(C-\eta)\le\mathcal A_q(C-1/216),\qquad
\frac{2C-c}{s}>\frac{35}{33}\left(2C-\frac{44}{125}\right).
\tag{MP.22}
\]

At \(C=1/2\), the two integration endpoints are
\(8623/27000\) and \(18127/27000\). They satisfy

\[
G(8623/27000)<\frac{19}{20},\qquad
G(18127/27000)>\frac{37}{50}.
\]

For the first comparison, use
\(8623/27000>5/16\) and \((5/16)^2>1-(19/20)^2\).
For the second, use
\(18127/27000<84/125\) and
\((84/125)^2+(37/50)^2<1\). Hence

\[
\mathcal A_q(1/2-1/216)<\frac{105}{176}<\frac23.
\]

Its gap from the linear expression in MP.22 is greater than
\(189/275-2/3=17/825\).

At \(C=37/50\), the endpoints are
\(15103/27000\) and \(24607/27000\). The exact inequalities

\[
G(15103/27000)<\frac{829}{1000},\qquad
G(24607/27000)>\frac{411}{1000}
\]

follow respectively from

\[
15103^2=228100609>228001311
=27000^2\bigl(1-(829/1000)^2\bigr),
\]
\[
24607^2=605504449<605856591
=27000^2\bigl(1-(411/1000)^2\bigr).
\]

Therefore

\[
\mathcal A_q(37/50-1/216)<\frac{19}{16},
\]

whose gap from MP.22 is greater than
\(329/275-19/16=39/4400\). Concavity in \(C\) yields

\[
\frac{2C-c}{s}-\mathcal A_c(C-\eta)>\frac{39}{4400}
\tag{MP.23}
\]

throughout this second range. Together, MP.17--23 give the uniform
strict terminal margin

\[
\boxed{
R_a(-C+z)-\bigl[G(C-T_L)-G(C+z)\bigr]
>\frac{39}{4400}c
\quad(0\le z\le w).}
\tag{MP.24}
\]

### 6. The occupation contradiction

If MP.7's excess bound holds, MP.16 and MP.24 imply
\(R_a>n_a\) on the entire interval \([-C,-C+w]\).
The right endpoint lies in the interior of \(J\), and the strict
gap persists a positive distance farther right by continuity. Hence
the strict terminal exposure set has measure greater than \(w\).

PS.34--35 give a terminal occupation equal to one on that strict
exposure set, with total occupation \(m\). This contradicts
\(m\le w\) from TP.10. The contradiction proves MP.7--8 for
positive, horizontal, and every remaining negative middle tilt.

Keeping the nonpositive term \(-h_L\) in MP.16 would allow the
slightly larger error \(\mathcal E_\theta\le h_L+39c/4400\).
The uniform version MP.7 suffices for a prefix theorem stated without
separating the tilt signs. Establishing such a curvature or weighted
excess estimate remains a separate input; this note does not assert
it throughout the full angle range.

### 7. A concrete cubic allowance for a late excess tail

The following modular criterion is useful when a reflected-support
estimate controls an excess tail rather than proving the exact unit
prefix. Suppose additionally that \(\cot a\ge1/8\), and assume

\[
(v(t)-1)_+\le\frac{19}{25}
\bigl(t-(\pi/2-91/100)\bigr)_+
\quad\text{for a.e. }0<t<\theta.
\tag{MP.25}
\]

Then MP.7's weighted allowance holds. Indeed, its kernel has the exact
form

\[
\lambda\cos t-\sin t
=\frac{\sin(\theta-t)}{\cos\theta}.
\]

Put \(t_0=\pi/2-91/100\) and
\(\ell=(\theta-t_0)_+\). Since \(C-T_L\le37/50\),

\[
\cos\theta>\frac23,\qquad
\ell<\frac{91}{100}-\frac{147}{200}=\frac7{40}.
\tag{MP.26}
\]

The first assertion uses \(1-(37/50)^2>4/9\). For the second,
the Taylor lower bound \(\cos x\ge1-x^2/2+x^4/25\) on
\([0,1]\) gives

\[
\cos(147/200)>\frac{37}{50},\qquad
1-\frac{(147/200)^2}{2}+\frac{(147/200)^4}{25}
-\frac{37}{50}=\frac{62448881}{40000000000}>0.
\]

Thus \(\arccos(C-T_L)>147/200\), proving MP.26. If
\(\ell=0\), MP.25 gives \(\mathcal E_\theta=0\). Otherwise,
\(\sin(\theta-t)\le\theta-t\), and a direct integral yields

\[
\begin{aligned}
\mathcal E_\theta
&\le\frac{19}{25\cos\theta}
\int_{t_0}^{\theta}(t-t_0)(\theta-t)\,dt\\
&=\frac{19\ell^3}{150\cos\theta}
<\frac{19}{100}\left(\frac7{40}\right)^3
=\frac{6517}{6400000}.
\end{aligned}
\tag{MP.27}
\]

Finally \(\cot a\ge1/8\) implies
\(c\ge1/\sqrt{65}>3/25\). Therefore

\[
\frac{6517}{6400000}<\frac{117}{110000}
<\frac{39c}{4400},\qquad
\frac{117}{110000}-\frac{6517}{6400000}
=\frac{3193}{70400000}>0.
\tag{MP.28}
\]

This proves the conditional exclusion from MP.25. The reflected
curvature estimate that supplies MP.25 is a separate obligation; the
cubic payment itself uses only MP's geometric hypotheses.

---

<a id="proof-near-full"></a>
## Technical proof 42. The near-full reflected-tail estimate (RX)

Written mathematical proof, October 10, 2026. This extends the
[small-deficit reflected estimate](#proof-reflected-local-laws)
(RP) and proves `v<=1` on `[0,asin(C)]` whenever `cot(a)<=1/8`.
The [weighted companion comparison](#proof-weighted-moment)
(MP) uses only `[0,asin(C-T_L)]`, making this local curvature theorem
sufficient for that angle range.

The inputs are the all-sign tail data, terminal facet bound, top
projection, ordinary endpoint boxes, and width cut in
[TP.1–13](#proof-terminal-geometry), together
with the reflected local source laws and exact terminal impulse
identity in RP.6–16. No objective reflection invariance is used.
The curvature theorem is established here; the global exclusion uses
the separately proved geometric implication MP.7–8.

### 1. Parameters and exact impulse bound

Suppose a remaining above-reference largest-angle partial maximum
has

    0<cot(a)<=1/8.

Set c=cos(a), s=sin(a), epsilon=L-a, k=(1-s)/c. TP gives

    1/2<C<37/50, N(-C)<1/3,
    m/s<=k, T_R<=k/2.

Moreover

    epsilon<=atan(1/8)<1/8,
    k=(sqrt(1+cot(a)^2)-1)/cot(a)<1/16.       (RX1)

At the endpoint cot(a)=1/8, k=sqrt(65)-8<1/16;
monotonicity of k in the angle deficit proves the general bound.

The reflection is exactly RP's:

    P=-q(L-r), Q=-p(L-r), U=v(L-r), V=u(L-r),
    P'=U-1-Q, Q'=V-1+P.

On the used interval P<=1, Q>=-1 and the usual curvature/same-sign
inequalities hold. Both densities vanish before epsilon. At epsilon
only Q jumps, upward by j=m/s<=k. There are no further atoms in the
used interval. The unused central facet is removed in the negative
case, as in RP.

The initial values are (P,Q)=(e,d-1), with

    0<=e<3/4, d=3C+T_R<1801/800  (positive/horizontal),
    0<=e<19/25, d=3C<=111/50     (negative).       (RX2)

Here d>3/2. For the negative case, e=e_L+h_R and
h_R<1-s<1/125. Indeed s>=8/sqrt(65)>124/125; the last
squared margin is 112/203125. The endpoint pressure bound then gives
e<3/4+5h_R/4<19/25. In the other cases e=e_L<3/4.
The initial Q-positive component persists through this enlarged gap:

    Q(epsilon-)+1=ds-(1-e)c
      >(3/2)(124/125)-1/8>1.

The upward terminal impulse preserves that positivity.

For E=(P-1/2)^2+(Q+1)^2, the exact impulse calculation gives

    E(epsilon+)-E(0)
      <= k^2[(2e-1+k^2)/(1+k^2)-dc]
      <(53/100)k^2<1/480.                       (RX3)

The penultimate inequality uses e<=19/25 and k<1/16. Thus the
parameter controlling Q at the first P-zero, or at epsilon when
P has already become nonpositive, is

    Z=d^2-e(1-e)+1/480.                          (RX4)

Precisely, Q+1<=sqrt(Z). If P has already crossed zero in the
unused gap, this follows from (P-1/2)^2>=1/4 at epsilon.
Otherwise E is nonincreasing on the subsequent initial ++ sector.

As in RP, every positive-Q component after the initial one has
amplitude at most 1/8 and cannot support U>1. Within the initial
component, once P<=0 and Q>1, the universal decay is

    P<=-rho,
    Q-1<=sqrt(Z)-2-rho/2-rho^2/4,               (RX5)

for elapsed rho<=1. The possible excess duration is consequently

    D(Z)=sqrt(1+4 max(sqrt(Z)-2,0))-1.

All bounds below are less than one, making the comparison valid up
to its predicted endpoint.

### 2. Small initial P, including an earlier zero in the unused gap

Suppose e<=3/10. If Z<=4, there is no possible excess after the
initial P-zero or the impulse. Before that zero U=0; the unused gap
also has U=0. Thus there is no excess to estimate in this case.

If Z>4, then d^2>4-1/480, whence

    d>1999/1000.                                (RX6)

The squared margin is 5747/3000000. While P>0 and Q>0,
Q'>=-1 and the impulse is upward, so

    P(r)<=e-dr+r^2/2.

The first P-zero occurs by

    tau<=d-sqrt(d^2-2e)<4/25.                    (RX7)

The final inequality follows from e<=3/10, RX6, and

    2(1999/1000)(4/25)-(4/25)^2-3/5=44/3125>0.

The Q-component cannot end first on this interval, since
Q>=d-1-r>0. If P has crossed before epsilon, start RX5 at epsilon;
RX1 still places this start before 4/25.

Uniformly over RX2,

    Z<(451/200)^2,
    sqrt(Z)-2<51/200,
    D(Z)<17/40.

For the first bound the worst value is d=1801/800 and e(1-e)>=0;
the exact margin is 5689/384000. The last comparison uses
1+4(51/200)=101/50<(57/40)^2. Therefore all possible excess for
e<=3/10 has ended before

    4/25+17/40=117/200<18/25.                   (RX8)

This case does not require a positive lower side-pressure bound.

### 3. Larger initial P and two exact endpoint certificates

Suppose e>=3/10. At the impulse,

    P(epsilon)=1-(1-e)s-dc>=e-dc
      >3/10-(1801/800)/8>0.

Thus the first P-zero follows epsilon. If the initial Q-component
ends earlier, it has no first-density excess. Otherwise its crossing
time satisfies

    tau<=d-sqrt(d^2-2e),
    last_excess_time<=W_+(d,e),
    W_+(d,e)=d-sqrt(d^2-2e)+D(Z).                (RX9)

Here Z is RX4. If Z<=4, no excess follows the crossing. If Z>4,
then d>2, since e(1-e)>=114/625>1/480 in this parameter range.

On Z>4 set A=sqrt(d^2-2e), S=sqrt(Z), Q0=sqrt(4S-7). The
unclipped W has derivatives

    W_e=1/A+(2e-1)/(Q0 S),
    W_d=1-d/A+2d/(Q0 S).                         (RX10)

Both are positive on 3/10<=e<=19/25 and 2<=d<=1801/800.
For W_e, the negative term when e<1/2 is at most 1/5 in absolute
value, whereas 1/A>=1/d>11/25. For W_d use d/A<4/3,
S<sqrt(5)<9/4 and Q0<sqrt(2)<3/2 to obtain
W_d>-1/3+32/27>0. Here S<sqrt(5) uses
Z<=d^2-114/625+1/480<5; the endpoint d^2 alone need not be below
five.

The clipped W_+ is increasing in e across Z=4: below that level
it is the increasing function d-sqrt(d^2-2e). If increasing e to
its upper endpoint places Z below 4, this endpoint value is at most
2-sqrt(4-38/25)<9/20. Otherwise increase d to its upper endpoint,
remaining in Z>4. It is therefore enough to check the following
pairs separately.

#### Positive or horizontal pair

At d=1801/800 and e=3/4,

    d-sqrt(d^2-2e)<109/300,
    Z<(221/100)^2,
    D(Z)<107/300.                               (RX11)

The first squared margin is 1403/360000. The second margin is
2669/1920000. Finally 4(221/100)-7=46/25 and
(407/300)^2-46/25=49/90000>0. Thus

    W_+<109/300+107/300=18/25.

#### Negative pair

At d=111/50 and e=19/25,

    d-sqrt(d^2-2e)<3/8,
    Z<(109/50)^2,
    D(Z)<5/16.                                  (RX12)

The middle margin is 259/60000. The first and last comparisons
are the same elementary squared inequalities as RP.21. Thus
W_+<11/16<18/25.

Together RX8, RX11, and RX12 prove

    U(r)<=1 a.e. for r>=18/25 on the used interval.              (RX13)

In the positive-tilt final surrogate interval the source density is
zero directly, so this conclusion includes that interval too.

### 4. Consequence for the original companion support

The Taylor lower bound cos x>=1-x^2/2+x^4/25 on [0,1] gives

    cos(18/25)>37/50.

Its exact rational margin is 225577/19531250. Since C<37/50,

    acos(C)>18/25.

If t<=asin(C), then r=L-t>=acos(C)>18/25. Therefore

    v(t)<=1 a.e. on [0,asin(C)].                  (RX14)

In particular this holds on [0,asin(C-T_L)] whenever C-T_L>=0.
TP's top projection gives T_L<=D_H<c<1/8<C, so the latter angle
is well defined in every present orientation.

This proves the complete local curvature premise needed by the
weighted second-wall comparison through cot(a)<=1/8. The global
exclusion uses that separately stated geometric comparison; the
present note does not infer a full barrier from these local ODEs.

---

<a id="proof-cubic-payment"></a>
## Technical proof 43. The complementary reflected envelope and cubic payment (AC)

Written mathematical proof, October 10, 2026. This note
supplies the weighted early-excess bound in MP.7 on the entire remaining
angle interval cot(a)>=1/8. The complementary cot(a)<=1/8 interval is
covered by RX.14 and MP.8. All three signs of the affine middle roof
are included.

The inputs are the all-width angle cut
[AT](#proof-initial-angle), the all-angle width
bound [WC](#proof-partial-width), the canonical saturated
tail data and terminal bounds
[TP](#proof-terminal-geometry), the fixed-angle
finite-source theorem [PS](#proof-partial-sources),
the local support laws rederived in
[PU](#proof-positive-local-laws), and the weighted
companion support comparison
[MP](#proof-weighted-moment).
The complementary curvature theorem is
[RX](#proof-near-full), while the exact reflected
impulse calculation is in
[RP](#proof-reflected-local-laws).
No reflected partial objective, two-unit-wing assumption, terminal
first-moment law, or full-turn completion is introduced.

### 1. Domain and all-sign endpoint parameters

For an above-reference largest-angle partial-cap maximum, AT and WC
leave

    1/2<C<37/50,
    1/8<=kappa:=cot(a)<3/8,
    c=cos(a), s=sin(a), epsilon=L-a=atan(kappa), L=pi/2.       (AC1)

Let k=(1-s)/c=tan(epsilon/2). Then

    c<3/8, s>14/15, k<2/11, epsilon<9/25.                    (AC2)

For s, use s>8/sqrt(73)>14/15; after squaring, the latter is
14400>14308. For k, its endpoint value is (sqrt(73)-8)/3<2/11,
since 73<(94/11)^2. Finally
atan(3/8)<3/8-(3/8)^3/3+(3/8)^5/5<9/25;
the last rational margin is 897/819200. The integral inequality
1/(1+x^2)<=1-x^2+x^4 proves the displayed arctangent bound.

Use I=[-2C,2C], J=[-C,C]. Write H=1-h_R for the right middle
height, and D_H=(1-Hs)/c. TP.10--11 give

    m<=c-D_H<=sk, T_L+2T_R<=D_H,
    H>s, min(h_L,h_R)=0.                                      (AC3)

The negative tilt already completed by NT has been discarded. For
positive or horizontal middle H=1 and D_H=k, so T_R<=k/2.
For negative middle T_R=0 and 0<h_R<1-s<1/15.

Let N_-=N(-C), N_+=N(C) be the actual partial barrier endpoints,
including the outgoing wall. The ordinary visited niche has the box
bound H_0(C)=1-sqrt(1-C^2)<1/3 at both endpoints. Thus

    N_-<=max(H_0(C), R_a(-C)),
    R_a(-C)=kappa(2C+T_R-D_H).                                (AC4)

This is not an assumption that the outgoing wall obeys the ordinary
niche box.

#### Positive or horizontal middle

The endpoint pressure law gives

    e:=e_L=1/2-3h_L/4+(3N_--N_+)/4<=1/2+3N_-/4.

AC3 implies

    R_a(-C)<=kappa(2C-k/2)
      =2C kappa-(sqrt(1+kappa^2)-1)/2.

This expression increases with both C and kappa: its kappa derivative
is 2C-kappa/(2sqrt(1+kappa^2))>0. At their enlarged endpoints it
is less than

    111/200-(sqrt(73)-8)/16
      <111/200-1/32=419/800,

using sqrt(73)>17/2. Since H_0(C)<1/3<419/800, we obtain

    0<=e<2857/3200<179/200,
    d:=3C+T_R<111/50+1/11=1271/550<2311/1000.               (AC5)

The last rational margin is 1/11000.

#### Negative middle

Here the reflected initial pressure is e=e_L+h_R. From PS's endpoint
law,

    e=1/2+5h_R/4+(3N_--N_+)/4.

AC4 gives N_-<=max(H_0(C),2C kappa)<111/200. Therefore

    0<=e<1/2+1/12+333/800=2399/2400<1,
    d:=3C<111/50.                                           (AC6)

All cases have d>3/2. These estimates use the actual partial endpoint
pressures and the explicit outgoing wall. In particular AC5's
improvement over e<1 is paid by the top projection bound.

### 2. The reflected local system and the one terminal impulse

Use the left charged-wing surrogate when the middle tilts upward.
For a downward tilt, remove the unused first central-facet atom by
using the right-wing first-support surrogate. It equals the actual
first support on every visited angle. The harmonic unused tails are
then exactly those in RP.2 and RP.8, and the initial reflected values
are (P,Q)=(e,d-1), with AC5 or AC6.

More explicitly, if p=f'-g+1 and q=g'+f-1, reflect only the local
support equations:

    P(r)=-q(L-r), Q(r)=-p(L-r),
    U(r)=v(L-r), V(r)=u(L-r),
    P'=U-1-Q, Q'=V-1+P.                                     (AC7)

On the regular reflected used interval the finite-source arm laws are

    P<=1, Q>=-1,
    U<=max(|Q|,(1+|Q|)/2),
    V<=max(|P|,(1+|P|)/2).

On the ++ sector U=0,V<=1/2; on the -- sector V=0,U<=1/2.
These are the actual local PS/PU source laws; no stationarity of a
reflected objective is claimed.

Every positive-Q component after the initial one has amplitude at
most 1/8. Indeed it starts at Q=0 with P<=1. While P>0, the ++
laws give P'<=-1 and Q'<=P-1/2. The total positive increase of Q
is therefore at most the integral of 1/2-r over [0,1/2], namely
1/8. Once P<=1/2 the derivative Q' is nonpositive, and once P<=0
the arm bounds make it strictly negative. P cannot rise again while
Q>0. Thus these later components cannot support U>1.

Both densities vanish on 0<r<epsilon. At epsilon there is one
impulse, in the second reflected density, of size

    j=m/s<=k.

Consequently P is continuous and Q jumps upward by j. PS excludes
all subsequent used-angle atoms, including a companion terminal atom.
The unvisited negative central atom has been removed, and in the
positive case the final removed-central interval has U=V=0 directly.
No arm bound for that final surrogate interval is needed.

The free initial trajectory is

    P(r)=1+(e-1)cos r-d sin r,
    Q(r)+1=d cos r+(e-1)sin r.                              (AC8)

The initial Q-positive component persists across the full unused gap:

    Q(epsilon-)+1=ds-(1-e)c
      >(3/2)(14/15)-3/8=41/40>1.                           (AC9)

The impulse is upward, so it preserves this positivity. Also
P'=(1-e)sin r-d cos r<0 throughout the unused gap, since
(1-e)tan r<=tan r<3/8<d. A P-zero there therefore cannot return
to positivity before the impulse; this makes the two entry cases in
Section 4 exhaustive.

For E=(P-1/2)^2+(Q+1)^2 the exact RP impulse calculation gives

    E(epsilon+)-E(0)
      <=k^2[(2e-1+k^2)/(1+k^2)-dc]
      <=k^2<4/121<1/30.                                   (AC10)

Here e<=1, so the bracket is at most one. If the first P-zero occurs
after epsilon, E is nonincreasing in the preceding initial ++ sector,
where E'=2(Q+1)(V-1/2)<=0. If P is already nonpositive at epsilon,
then (P-1/2)^2>=1/4 directly. In both cases, at the beginning r_b
of the possible excess comparison,

    Q(r_b)+1<=sqrt(Z),
    Z=d^2-e(1-e)+1/30.                                     (AC11)

If the initial Q-positive component ends before P reaches zero, it
has U=0 throughout and supports no first-source excess. All later
positive-Q components are too small to support U>1. Thus only the
case covered by AC11 remains.

### 3. Universal decay and the resulting linear excess envelope

After P<=0, as long as Q>1, the curvature bounds give P'<=-1.
With rho=r-r_b>=0, this implies P<=-rho. For rho<=1,

    Q'<=-1/2-rho/2.

When P is in [-1,0], use V<=(1-P)/2. When P<-1, the stronger
bound V<=-P gives Q'<=-1, which implies the displayed estimate
for rho<=1. Therefore

    Q(r)-1<=sqrt(Z)-2-rho/2-rho^2/4.                       (AC12)

Once Q falls to at most one within this component, P remains
nonpositive: on 0<Q<=1 the arm bound gives P'<=-(1+Q)/2, while
P<=0 gives Q'<=-1/2. Thus Q cannot re-enter Q>1 before the
component ends; AC12 is controlling its only possible excess episode.

Put

    D(Z)=sqrt(1+4 max(sqrt(Z)-2,0))-1.

Every possible excess ends by r_b+D(Z), provided this time increment
is less than one. The following common bound closes that condition:

    Z<(58/25)^2,
    D(Z)<13/25.                                             (AC13)

Indeed e(1-e)>=0 and AC5--6 give
Z<(2311/1000)^2+1/30<(58/25)^2, with squared margin
25037/3000000. The duration comparison follows from
(38/25)^2-(4(58/25)-7)=19/625>0.

If Z<=4 there is no excess. Otherwise D=D(Z)>0 and the polynomial
in AC12 factors as

    sqrt(Z)-2-rho/2-rho^2/4
      =(D-rho)(1/2+(D+rho)/4).

For 0<=rho<=D, its second factor is at most (1+D)/2<19/25.
Since U-1<=Q-1 wherever U>1, we get

    (U(r)-1)_+ <= (19/25)(r_b+D-r)_+                     (AC14)

throughout the possible excess episode. All other components have no
excess. It remains to bound the episode endpoint uniformly.

### 4. Every possible episode ends before 91/100

#### 4.1 The first P-zero precedes the impulse

In this case take r_b=epsilon. AC2 and AC13 yield

    r_b+D<9/25+13/25=22/25<91/100.                         (AC15)

This also handles a zero exactly at epsilon. No smooth transition
through the terminal atom is being assumed.

#### 4.2 The first P-zero follows the impulse

While P>0 and Q>0, the same-sign law gives U=0. Since Q'>=-1
and the terminal jump is upward,

    Q(r)>=d-1-r,
    P(r)<=e-dr+r^2/2.

If Q ends its component earlier there is no relevant excess.
Otherwise its first P-zero obeys

    r_b<=tau(d,e):=d-sqrt(d^2-2e).                          (AC16)

The square root is real on our whole parameter domain since d>3/2
and e<=1. Consequently

    r_b+D<=W_+(d,e):=tau(d,e)+D(Z).                        (AC17)

We only need to control AC17 when Z>4. Put

    A=sqrt(d^2-2e), S=sqrt(Z), Q0=sqrt(4S-7).

For the unclipped expression W on Z>4,

    W_e=1/A+(2e-1)/(Q0 S),
    W_d=1-d/A+2d/(Q0 S).                                  (AC18)

Both derivatives are strictly positive for 0<=e<=1 on this domain.
For W_e, when e<1/2 observe
S^2-A^2=e+e^2+1/30>0 and Q0>=1. Thus Q0 S>A and the negative
term has magnitude less than 1/A. For e>=1/2 positivity is immediate.

For W_d, Z>4 implies d^2>119/30. Hence

    d/A<sqrt(119/59)<3/2.

Also S<7/3, Q0<sqrt(7/3)<31/20, and d>3/2. Therefore

    W_d>-1/2+180/217>0.                                    (AC19)

The clipped W_+ remains increasing in e across Z=4, since below
that level it is tau(d,e), which increases in e. Raise e to its
orientation-specific upper endpoint in AC5 or AC6. If this places Z
at or below four, its endpoint value is less than 3/5: indeed the
original Z>4 fixes d^2>119/30, and

    tau(d,e)<=tau(d,1)<3/5.

The last comparison is equivalent to d>59/30, which follows from
d^2>119/30>(59/30)^2. Otherwise increase d to its corresponding
upper endpoint while remaining in Z>4, using AC19. It is therefore
enough to check the two following rational endpoint pairs.

**Positive or horizontal:** d=2311/1000, e=179/200. Then

    tau<107/250, sqrt(Z)<2299/1000, D<241/500.              (AC20)

The three squared margins, respectively, are

    2d(107/250)-(107/250)^2-179/100=629/125000,
    (2299/1000)^2-Z=3193/600000,
    (741/500)^2-(4(2299/1000)-7)=81/250000.

All are positive. Thus W_+<107/250+241/500=91/100.

**Negative:** d=111/50, e=1. Then

    tau<51/100, sqrt(Z)<223/100, D<39/100.                  (AC21)

The squared margins are respectively 43/10000, 67/6000, and
121/10000. Thus W_+<9/10<91/100.

Combining AC15--21 with AC14 proves the global reflected envelope

    (U(r)-1)_+ <=(19/25)(91/100-r)_+                      (AC22)

on the used interval. Its support is contained in r<91/100. The
final removed-positive-central interval has U=0, so the same envelope
holds there without appealing to the surrogate arm bounds.

### 5. The weighted cubic payment

MP defines

    theta=asin(C-T_L), lambda=tan(theta),
    E_theta=int_0^theta (v(t)-1)_+(lambda cos t-sin t) dt.

By AC3, 0<C-T_L<=C<37/50. In particular

    cos(theta)>sqrt(1-(37/50)^2)>2/3.                       (AC23)

Also cos(147/200)>37/50. The standard Taylor lower bound
cos x>=1-x^2/2+x^4/25 on [0,1] proves this with exact rational
margin 62448881/40000000000. Therefore

    acos(C-T_L)>=acos C>147/200.

Let t_0=L-91/100. Under t=L-r, AC22 becomes

    (v(t)-1)_+ <=(19/25)(t-t_0)_+.

Moreover

    theta-t_0<91/100-147/200=7/40.                         (AC24)

If theta<=t_0, the weighted excess is zero. Otherwise the exact
kernel identity and sin x<=x give

    lambda cos t-sin t
      =sin(theta-t)/cos(theta)
      <=(theta-t)/cos(theta).

Integrating the product of the two linear factors,

    E_theta
      <=(19/25)/cos(theta) * (theta-t_0)^3/6
      <(19/25)/(6(2/3))*(7/40)^3
      =6517/6400000.                                       (AC25)

This is the full reason only a small early curvature excess must be
paid: the excess envelope and the weighted support kernel both vanish
at opposite ends of the relevant interval.

Finally kappa>=1/8 implies

    c>=1/sqrt(65)>3/25.

Consequently MP's allowed error satisfies

    39c/4400>117/110000>6517/6400000.                       (AC26)

The last rational margin is 3193/70400000. Thus AC25 establishes
MP.7, and the terminal occupation contradiction excludes every
remaining maximum in AC1.

### 6. Coverage and scope

For cot(a)<=1/8, the independently proved RX.14 supplies
v<=1 on [0,asin C], so MP.8 applies with zero weighted excess.
For cot(a)>=1/8, AC1--26 supply MP.7 with the strict cubic payment.
AT has already excluded cot(a)>=3/8. The full-turn endpoint a=L
is bounded by the Gate 1 theorem. Hence, given the established
canonical/attainment, source, width, and MP inputs stated at the start,
there is no above-reference joint partial-cap maximizer at any angle.

This is a proof of the universal partial spatial inequality through
that explicitly listed dependency chain. Passing the original-motion
Gate 2 additionally uses the exact two-cap spatial partition from the
Gate 2 signed-domain reduction; no new motion-completion assumption
is needed for that final implication.

---

<a id="proof-partial-closure"></a>
## Technical proof 44. Universal partial-cap value and original-motion deduction (G2C)

### 1. Exact statements

Put

\[
L=\pi/2,\qquad
M=1+4Y^2+\arctan Y,\qquad
4Y^3+3Y-1=0,\quad Y>0.
\tag{G2C.1}
\]

Let \(U\subset\mathbb R\times[0,1]\) be a nonempty compact downward
convex cap. Write its projection as \(I=[l,r]\), its width as \(W=r-l\),
its roof as \(A\), and its middle half as

\[
J=[l+W/4,r-W/4].
\]

For \(0<t<L\), define

\[
\mu_t=(\cos t,\sin t),\qquad \nu_t=(-\sin t,\cos t),
\]
\[
R_t(x)=\frac{h_U(\mu_t)-1-x\cos t}{\sin t},\qquad
S_t(x)=\frac{h_U(\nu_t)-1+x\sin t}{\cos t}.
\tag{G2C.2}
\]

For \(\pi/4\le\alpha<L\), the actual partial barrier and score are

\[
N_{U,\alpha}(x)=\max\left\{0,
\sup_{0<t<\alpha}\min\{R_t(x),S_t(x)\},\ R_\alpha(x)\right\},
\]
\[
\mathcal P_\alpha(U)=\int_{I\setminus J}A(x)\,dx
-\int_JN_{U,\alpha}(x)\,dx.
\tag{G2C.3}
\]

The terminal term is the whole first inner wall, imposed by the
whole-body outgoing strip. At \(\alpha=L\), use the full positive
two-wall niche of Gate 1. The limiting terminal wall is nonpositive
because the cap has height at most one.

**Theorem G2C1 (universal partial-cap value).** Every cap and every angle
in this domain satisfy

\[
\boxed{\mathcal P_\alpha(U)\le M/2.}
\tag{G2C.4}
\]

The global supremum is \(M/2\), attained by the full-turn reference cap.
The statement includes arbitrary asymmetry, subunit height, nonsmooth
roofs and unbounded polygon complexity. A zero-width cap has score zero.

**Theorem G2C2 (original ambidextrous area).** Every compact connected
body admitting both original unit-corridor passages from a common
incoming orientation, including independent partial terminal rotations
and nonmonotone motions, satisfies

\[
\boxed{|S|\le M.}
\tag{G2C.5}
\]

Romik's reference attains equality, so the unrestricted area supremum
in the original motion domain is exactly \(M\). The same upper bound
holds for Gate 0's signed joint functional on arbitrary auxiliary convex
hulls. The signed integral is not identified with ordinary area when
such a hull has empty survivor fibers.

### 2. A hypothetical failure has an attained canonical maximizer

Suppose G2C.4 fails. The global domain theorem
[PD](#proof-partial-domain) supplies an attained joint
maximum over caps and angles. Choose a maximizing pair with the largest
terminal angle, and apply the score-preserving canonical reductions at
that angle. The selected cap has height one, affine middle roof, and a
top face meeting the middle window. Its unused outer normals are
saturated while every used support and the outgoing wall are preserved.

These reductions apply to both signs of the middle slope. They begin
with arbitrary heights and boundaries, prove width coercivity using an
actual 45-degree tent, and justify continuity of the partial barrier
including its endpoint-angle tails. Thus the finite polygon selection
used for source regularity targets this chosen global maximizer.

If \(\alpha=L\), G1C1 already contradicts the supposed score excess.
For proper angles the all-width certificate
[AT](#proof-initial-angle) gives

\[
\pi/4\le\alpha\le\arctan(8/3)
\quad\Longrightarrow\quad
\mathcal P_\alpha(U)<5259/6400<M/2.
\tag{G2C.6}
\]

It follows that \(\alpha>\arctan(8/3)>3\pi/8\). All three
genuine tents at \(\pi/8,\pi/4,3\pi/8\) have been visited.

The partial source theorem
[PS](#proof-partial-sources) rederives actual
endpoint complementarity, positive endpoint pressures, regular used-wing
curvature bounds, source balance and the Green identity for this
objective. It retains the possible first terminal facet atom and excludes
the companion terminal atom. It does not import the source law of a
different full-turn maximizer.

The finite three-angle comparisons transferred in
[TP](#proof-terminal-geometry) give the short-width,
initial wide-width and tilt cuts. The new
[WC](#proof-partial-width) uses the partial endpoint pressures
and a joint bound on the two positive-floor losses to sharpen the width
cut without a full-niche endpoint-box assumption. Hence, with
\(I=[-2C,2C]\) and \(J=[-C,C]\),

\[
\frac{1001}{2000}<C<\frac{37}{50},\qquad
0\le |A(C)-A(-C)|<\frac{17}{50}.
\tag{G2C.7}
\]

Horizontal reflection is used only to compare this symmetric set of
three tents, with the barrier reflected at the same time. It is not
asserted to preserve the fixed partial objective.

### 3. The actual terminal facet and its source mass

Keep the original orientation and put

\[
A(-C)=1-h_L,\qquad A(C)=1-h_R,\qquad
h_L,h_R\ge0,\quad \min(h_L,h_R)=0,
\]
\[
c=\cos\alpha,\qquad s=\sin\alpha.
\]

If \(h_R>0\), the negative-tilt theorem
[NT](#proof-negative-completion) already proves
\(N_{U,\alpha}\ge n_U\) on \(J\), and hence
\(\mathcal P_\alpha(U)\le\mathcal P_L(U)\le M/2\), unless

\[
0<h_R<1-s,\qquad
\alpha<L-\arctan(h_R/(2C)).
\tag{G2C.8}
\]

Discard the completed branch. In every remaining sign, put

\[
H=1-h_R>s,\qquad
d=\frac{1-Hs}{c},\qquad w=c-d>0.
\tag{G2C.9}
\]

Let \(T_L,T_R\) be the height-one top overhangs outside the left and
right ends of \(J\). They are zero on a strictly lower middle side.
The canonical first support immediately after the terminal angle is
the point \((C+T_R,H)\); in the negative case it remains so until the
unvisited central normal. The first terminal facet has charged horizontal
length \(m\), and the whole outgoing wall is

\[
R_\alpha(-C+z)=\frac cs(2C+T_R-d-z).
\tag{G2C.10}
\]

Using the correct one-sided angle derivative with historical ties from
[TV](#proof-angle-variation), TP proves

\[
\boxed{m\le w<\frac c2,\qquad T_L+2T_R\le d.}
\tag{G2C.11}
\]

The first inequality uses the largest-angle choice: a longer facet would
make the outgoing wall redundant and permit a small angle increase
without changing the barrier. The second comes from the finite-source
horizontal projection, passed on compact positive-barrier intervals.
It does not assume continuity of the length of a zero set.

PS additionally gives a terminal occupation \(\chi\) with
\(0\le\chi\le1\), total horizontal mass \(\int_J\chi=m\), and
\(\chi=1\) on the strict exposure set

\[
E=\{x\in J:R_\alpha(x)>n_\alpha(x)\},\qquad
n_\alpha=\max\{0,\sup_{0<t<\alpha}\min(R_t,S_t)\}.
\tag{G2C.12}
\]

Only this strict-exposure statement is needed below. No common
fractional occupation for separate shape and angle variations is used.

### 4. A weighted companion moment gives the contradiction

Let \(g\) be the support of the left charged wing and \(v=g''+g\)
its regular curvature. For positive tilt use the low-left surrogate:
the omitted high-point companion wall is nonpositive on \(J\).
In the other two signs use the actual companion support. Then

\[
g(0)=1-h_L,\qquad g'(0+)=C+T_L.
\]

Put

\[
\theta=\arcsin(C-T_L),\qquad \lambda=\tan\theta,
\]
\[
\mathcal E_\theta
=\int_0^\theta(v(t)-1)_+
\bigl(\lambda\cos t-\sin t\bigr)\,dt.
\tag{G2C.13}
\]

The quantity \(C-T_L\) is positive by G2C.7, G2C.9 and G2C.11.
The exact weighted moment theorem
[MP](#proof-weighted-moment) proves, throughout
\(0\le z\le w\),

\[
n_\alpha(-C+z)
\le\sqrt{1-(C-T_L)^2}-\sqrt{1-(C+z)^2}
+\mathcal E_\theta.
\tag{G2C.14}
\]

To explain the localization, a positive global companion-wall maximum
has an interior maximizing angle and shifted support abscissa
\(D_x=-C+z\). The outer support point has \(X\ge-2C\), so
\(\sin t\le C+z\). The derivative relations
\(D_x'=(1-v)\cos t\), \(D_y'=(1-v)\sin t\) then yield
G2C.14 by weighting horizontal displacement with \(\lambda\).
The weight changes sign at \(\theta\); curvature above one after
that angle contributes no adverse error.

MP's exact scalar comparison, retaining all top overhangs and the lower
negative-tilt terminal height, gives the strict uniform margin

\[
R_\alpha(-C+z)
-\left[\sqrt{1-(C-T_L)^2}-\sqrt{1-(C+z)^2}\right]
>\frac{39}{4400}c
\quad(0\le z\le w).
\tag{G2C.15}
\]

This follows from two concave-in-width comparisons of symmetric
integral averages of \(x/\sqrt{1-x^2}\), with exact rational endpoint
certificates covering \(c\le1/3\) and \(c\ge1/3\). It is not an
angular discretization of the niche.

Consequently it suffices to prove

\[
\mathcal E_\theta\le\frac{39}{4400}c.
\tag{G2C.16}
\]

If G2C.16 holds, the entire interval \([-C,-C+w]\) is strictly
exposed to the outgoing wall. Continuity extends strict exposure a
positive distance beyond its interior right endpoint. Thus
\(|E|>w\ge m\), contradicting G2C.12. The remaining task is the
weighted error estimate, with no full-wing unit-curvature assumption.

### 5. The two overlapping angle ranges pay the weighted error

Write \(\kappa=\cot\alpha\). We have \(0<\kappa<3/8\).
Reflect the support equations only, by \(r=L-t\), and set
\(P=-q\), \(Q=-p\), \(U=v\), \(V=u\). On regular used intervals
where the surrogate agrees with the actual relevant supports, the local
equations and source laws give

\[
P'=U-1-Q,\qquad Q'=V-1+P,
\]
\[
P\le1,\quad Q\ge-1,\quad
U\le\max\{|Q|,(1+|Q|)/2\},
\quad V\le\max\{|P|,(1+|P|)/2\}.
\tag{G2C.17}
\]

The final removed positive-central interval has \(U=V=0\) directly;
no surrogate arm inequality is claimed or needed on that interval.

On the initial positive \(P,Q\) component, \(U=0,V\le1/2\).
Every later positive-\(Q\) component has amplitude at most \(1/8\).
The harmonic unused gap has zero regular curvature. The first terminal
facet becomes a single upward impulse in \(Q\), of size
\(j=m/s\le\delta=c/(1+s)\). The unused negative central atom is
removed by the right-wing surrogate; no used support changes. The
initial reflected state is

\[
(P,Q)=(e,d_0-1),\qquad
\begin{cases}
e=e_L,\ d_0=3C+T_R,&\text{positive or horizontal},\\
e=e_L+h_R,\ d_0=3C,&\text{negative}.
\end{cases}
\tag{G2C.18}
\]

For the energy \(\mathcal H=(P-1/2)^2+(Q+1)^2\), the exact
unused-gap and terminal-impulse calculation is

\[
\mathcal H((L-\alpha)+)-\mathcal H(0)
\le\delta^2\left[
\frac{2e-1+\delta^2}{1+\delta^2}-d_0c\right].
\tag{G2C.19}
\]

#### The range \(0<\kappa\le1/8\)

The [reflected-tail theorem RX](#proof-near-full)
uses the valid small-deficit endpoint box, the two parameter pairs in
G2C.18, and G2C.19. It proves that every possible reflected first-density
excess has ended before \(18/25\). Since
\(\cos(18/25)>37/50>C\), this yields

\[
v(t)\le1\quad\text{for a.e. }0<t<\arcsin C.
\tag{G2C.20}
\]

It bounds the shorter interval ending at \(\theta\), so
\(\mathcal E_\theta=0\), proving G2C.16 on this whole range.

#### The range \(1/8\le\kappa<3/8\)

The [all-angle reflected-envelope theorem AC](#proof-cubic-payment)
uses the actual outgoing-wall value in the endpoint pressures. It gives
\(e<179/200,d_0<2311/1000\) for positive or horizontal middle, and
\(e<1,d_0<111/50\) for negative middle. The impulse cost in
G2C.19 is below \(1/30\).

After the first \(P\)-zero, the source equations give the quadratic
decay \(Q-1\le\varepsilon_0-\rho/2-\rho^2/4\). A coupled
time-and-amplitude bound is monotone in the two initial parameters;
its exact endpoint certificates place every possible excess before
\(91/100\). The resulting uniform linear envelope is

\[
(U(r)-1)_+\le\frac{19}{25}(91/100-r)_+.
\tag{G2C.21}
\]

The proof includes a first zero before the terminal impulse, the
impulse itself, both tail heights, and all later source components.

Under \(t=L-r\), put \(t_0=L-91/100\). Since
\(\cos\theta>2/3\) and
\(\arccos(C-T_L)>147/200\), the potentially relevant excess
interval has length less than \(7/40\). The exact weight is
\(\lambda\cos t-\sin t=\sin(\theta-t)/\cos\theta\). Thus
G2C.21 yields the cubic payment

\[
\mathcal E_\theta
<\frac{19/25}{6(2/3)}\left(\frac7{40}\right)^3
=\frac{6517}{6400000}
<\frac{117}{110000}
<\frac{39}{4400}c.
\tag{G2C.22}
\]

The final inequality uses \(c\ge1/\sqrt{65}>3/25\). The strict
rational gap between the middle two fractions is
\(3193/70400000\). This proves G2C.16 on the second range.

The two ranges overlap at \(\kappa=1/8\). Together they contradict
every proper-angle maximizing pair left by Sections 2--3. The
full-turn boundary was already bounded by G1C1. Hence no cap in the
original scalar domain has score above \(M/2\), proving G2C1.

### 6. Deduction for both independent original motions

The [Gate 0 original-motion audit](#main-motions)
applies to every actual compact connected competitor of area above
\(\sqrt2\). It supplies independent terminal magnitudes
\(\alpha,\gamma\in[\pi/4,L]\) while retaining both actual outgoing
strips. Its reduction uses the angles visited by the original continuous
motions, so it also covers backtracking and nonmonotone rotations.

Let \(K\) be the actual convex hull in its incoming strip. Its upper
downward cap \(U\) and vertically reflected lower downward cap \(V\)
share the same horizontal projection \(I\) and middle half \(J\).
Gate 0's exact signed fiber is

\[
\ell(x)=1-\max\{1-A_V(x),N_{U,\alpha}(x)\}
-\max\{1-A_U(x),N_{V,\gamma}(x)\}.
\tag{G2C.23}
\]

On the middle half, \(\ell\le1-N_{U,\alpha}-N_{V,\gamma}\).
On its complement, \(\ell\le A_U+A_V-1\). The constants cancel
because both regions have length \(W/2\). Therefore, for every
auxiliary hull as well as the actual one,

\[
\int_I\ell\le\mathcal P_\alpha(U)+\mathcal P_\gamma(V)\le M.
\tag{G2C.24}
\]

For an actual connected body, every projected fiber of the canonical
envelope is nonempty and contains the body fiber. Gate 0 consequently
gives \(|S|\le\int_I\ell\). For an auxiliary hull, G2C.24 is
still a bound on the signed integral, without dropping its possible
negative fibers or replacing it by its positive part.

Bodies of area at most \(\sqrt2\) are already below \(M\), since
G1C.6 gives \(M>41/25>\sqrt2\). This proves G2C2 on the entire
original domain. Romik's genuine two-full-turn body is also admissible
in that domain and has exact area G2C.1. Its reference caps attain
equality in the spatial partition, as recorded in
[the reference calculation](#main-equality). The
unrestricted supremum is therefore exactly \(M\).

### 7. Scope and verification

The [dependency and coverage audit](#verification-record)
records every angle boundary, middle-slope sign, source convention and
original-motion implication. The
[fixed exact arithmetic checker](#verification-record)
passes 83 rational and squared comparisons used in the final scalar and
reflected-envelope arguments. It does not verify the continuum geometry
or replace the written source proofs.

The mathematical dependency on Gate 1 includes Baek's ordinary one-turn
theorem and the existing Gerver area enclosure, documented in G1C
Section 6. Gate 2 adds no application of that ordinary area theorem to
an unproved partial survivor. All new arguments are in the research
documentation tree. External refereeing and Lean verification remain
separate from the written-proof acceptance condition. No equality
classification or uniqueness result is asserted here.

---

<a id="proof-full-equality"></a>
## Technical proof 45. Every original full-turn equality cap and inverse canonicalization (CE)

### 1. Domain and exact reference normalization

Put

\[
L=\frac\pi2,\qquad
4Y^3+3Y-1=0,\quad Y>0,\qquad
\beta=\arctan Y,\qquad s=\sin\beta,
\]
\[
M=1+4Y^2+\arctan Y,\qquad
a_*=\frac1{3s},\qquad C_*=\frac{a_*}{2},\qquad
k=1-a_*.
\tag{CE.1}
\]

Let \(h_*\) denote the displayed reference profile in
[Note 14, equations 14.2–14.3](#proof-reference-matching).
That displayed profile has horizontal endpoint support values
\(h_*(0)=1\) and \(h_*(\pi)=2a_*-1\), so it is not centered.
Define

\[
\bar h_*(\theta)=h_*(\theta)-k\cos\theta.
\tag{CE.2}
\]

Both horizontal endpoint values of \(\bar h_*\) are \(a_*\).
Let \(U_*\) be the centered downward reference cap: its upper support
function is \(\bar h_*|_{[0,\pi]}\), and its lower boundary is its
full horizontal baseline. Its existence as a genuine compact convex
cap, and its reference score, are proved in
[AR3](#proof-arm) and
[SD1](#proof-full-domain).

For an arbitrary nonempty compact downward convex cap
\(U\subset\mathbb R\times[0,1]\), let \(I=[l,r]\) be its actual
horizontal projection, \(W=r-l\), \(A_U\) its roof, and
\(J=[l+W/4,r-W/4]\). Its full positive niche and spatial score are

\[
n_U(x)=\left[\sup_{0<t<L}\min\left\{
\frac{h_U(\cos t,\sin t)-1-x\cos t}{\sin t},
\frac{h_U(-\sin t,\cos t)-1+x\sin t}{\cos t}
\right\}\right]_+,
\]
\[
P(U)=\int_{I\setminus J}A_U(x)\,dx-\int_J n_U(x)\,dx.
\tag{CE.3}
\]

Here “downward” means that every vertical fiber is an interval beginning
at height zero. In particular the cap contains \(I\times\{0\}\).
The zero-width case has score zero and cannot attain \(M/2\).

### 2. Every prescribed canonical equality cap enters the Gate 1 proof

A canonical cap has height one and a roof affine on all of its middle
interval \(J\), as in [MID.11](#proof-middle-chord).
The following quantifier is essential for equality recovery.

**Prescribed-cap observation.** Every canonical global maximizer can be
used as the target of the finite selections and all subsequent necessary
conditions in Gate 1.

Indeed, fix such a cap \(V\), translate it strictly inside the artificial
horizontal box, and use the penalty
\(\eta_nD_n(\,·\,,V)^2\) from
[RG, Section 2](#proof-prescribed-regularity).
The comparison with the grid circumscription of this same \(V\) gives
\(D_n(V_n,V)^2\le e_n/\eta_n\to0\). Thus the selected polygons converge
to this prescribed cap. The vanishing-middle-curvature argument RG1
uses only the affinity of this cap's middle roof. The proofs of
RG2–RG3, [EP1–EP2](#proof-full-endpoints), and the later
spatial necessary conditions therefore apply to \(V\) itself.
Although RG2 was stated as an existence theorem, its proof does not
select one favored canonical maximizer at the expense of others.

Now suppose \(V\) is canonical and \(P(V)=M/2\). G1C1 makes \(V\)
a global maximizer on the entire cap domain. The complete tilted
coverage in [G1C, Sections 3–5](#proof-full-closure) excludes
every nonzero middle slope. These arguments use the maximizing lower
bound \(P(V)\ge M/2>41/50\), not the stronger and unavailable premise
\(P(V)>M/2\). Their strict contradictions consequently apply at equality.

For a horizontal canonical maximizer, the strict short and wide
exclusions in [HW](#proof-horizontal-complete) leave

\[
\frac12<C=\frac W4<\frac{8571}{12500}<C_H,
\qquad C_H=\frac1{35}\sqrt{523+2\sqrt{701}}.
\tag{CE.4}
\]

The entire surviving range is inside CH6. The actual spatial laws
[CH2 and CH4–CH6](#proof-full-curvature)
therefore give:

- the top face is exactly \(J\times\{1\}\);
- the two open-quarter supports have regular curvature densities at
  most one;
- the full positive niche is confined to \(J\);
- the sharp comparison CH.26 holds for these actual supports.

All these conclusions concern the chosen cap \(V\), and no
stationarity law for the different weighted functional is imported.

### 3. The functional equality identifies the canonical cap

**Theorem CE1 (canonical equality).** A canonical cap \(V\) has
\(P(V)=M/2\) if and only if it is a horizontal translate of \(U_*\).

**Proof.** Translate the projection to \([-a,a]\), where
\(a=W/2=2C>1\), and write

\[
f(t)=h_V(\cos t,\sin t),\qquad
g(t)=h_V(-\sin t,\cos t),\qquad 0\le t\le L.
\]

The exact endpoint data are
\(f(0)=g(L)=a\) and \(f(L)=g(0)=1\). Thus
\((f,g)\in X_a\) in the notation of AF. By CE.4 and CH.26,

\[
\frac M2=P(V)\le F(f,g)-a\le\frac M2.
\tag{CE.5}
\]

To apply AF3's equality statement directly to this pair, define a real
periodic profile \(\widehat h\) by

\[
\widehat h(t)=f(t),\qquad
\widehat h(t+L)=g(t),
\]
\[
\widehat h(-t)=f(t)-\sin t,\qquad
\widehat h(-t-L)=g(t)-\cos t,
\qquad 0\le t\le L.
\tag{CE.6}
\]

The endpoint values make these formulas agree at \(0,\pm L,\pm\pi\),
so \(\widehat h\) is a real \(2\pi\)-periodic \(H^1\) function.
It has \(\widehat h(L)=1\), \(\widehat h(3L)=0\), and horizontal
width \(2a>1\). The reflected half in AF's definition equals the
original pair. Consequently CE.5 gives

\[
\widetilde{\mathcal Q}(\widehat h)=2F(f,g)-2a=M.
\tag{CE.7}
\]

No assertion that this auxiliary lower-half extension is a convex
support function is needed: AF3 is proved on the full real \(H^1\)
profile domain. Its equality statement gives
\(\widehat h=h_*+b\cos\theta\) for a real \(b\).
The continuous representatives of these \(H^1\) functions agree
pointwise, so this also identifies the actual upper supports at every
normal, not merely almost everywhere.
The two horizontal endpoint values are both \(a\), while those of
\(h_*\) are \(1\) and \(2a_*-1\). Therefore
\(a=a_*\) and \(b=a_*-1=-k\). In particular the actual upper support
function of the centered cap \(V\) is \(\bar h_*\).

A downward compact convex cap is the intersection of \(\{y\ge0\}\)
with its upper supporting halfplanes, including the two horizontal
axis normals. To see why the remaining lower normals add no data,
their support is attained on the full baseline: lowering a point to
height zero increases its scalar product with such a normal. Equality
of all the upper supports therefore gives the exact identity
\(V=U_*\). Undo the initial horizontal translation.

Conversely, the reference has score \(M/2\), and horizontal
translation preserves CE.3. \(\square\)

In particular every canonical equality cap has

\[
A_V=1\text{ on }J,\qquad
n_V(j_-)=n_V(j_+)=0.
\tag{CE.8}
\]

The niche endpoint statement also follows directly before AF equality:
CH Section 7 places every positive two-wall point strictly between the
two endpoints of \(J\). The niche is continuous, by the endpoint-angle
truncation argument in SD3.

### 4. Exact height-extrusion deficit

The weak monotonicity used for Gate 1 has a stronger identity suitable
for recovering equality.

**Lemma CE2 (extrusion deficit).** Let \(V\) be a downward cap of
positive width, let \(\varepsilon\ge0\), and suppose
\(W=V+[0,\varepsilon]e_y\) still has height at most one. The two caps
have the same projection \(I\) and middle interval \(J\), and

\[
\boxed{\quad n_V=(n_W-\varepsilon)_+,\qquad
P(W)-P(V)=\int_J(\varepsilon-n_W(x))_+\,dx.\quad}
\tag{CE.9}
\]

If \(n_W\) is continuous and vanishes at either endpoint of \(J\),
then \(\varepsilon>0\) makes this score difference strictly positive.

**Proof.** Minkowski addition of the vertical segment raises the roof
by \(\varepsilon\) and adds \(\varepsilon n_y\) to each upward
support. Both raw inner-wall heights consequently rise by precisely
\(\varepsilon\), for every parameter and abscissa. If \(r_V\) is
their signed angular supremum, then
\(n_W=(r_V+\varepsilon)_+\) and
\(n_V=(r_V)_+=((r_V+\varepsilon)_+-\varepsilon)_+\).
This proves the first identity, including where the signed supremum is
negative.

The charged exterior area increases by \(\varepsilon|I\setminus J|\).
Since \(|I\setminus J|=|J|\),

\[
\begin{aligned}
P(W)-P(V)
&=\varepsilon|J|-\int_J\bigl[n_W-(n_W-\varepsilon)_+\bigr]\,dx\\
&=\int_J(\varepsilon-n_W)_+\,dx.
\end{aligned}
\]

For the strict assertion, continuity next to an endpoint where
\(n_W=0\) gives a positive-length subinterval on which
\(n_W<\varepsilon/2\). The displayed integral is then positive.
\(\square\)

### 5. Recovery of every original equality cap

**Theorem CE3 (universal full-turn equality).** For every nonempty
compact downward convex cap \(U\subset\mathbb R\times[0,1]\),

\[
\boxed{\qquad P(U)=\frac M2
\quad\Longleftrightarrow\quad
U=U_*+(b,0)\text{ for some }b\in\mathbb R.\qquad}
\tag{CE.10}
\]

**Proof.** Assume equality. The cap has positive width and positive
area. Perform the exact [MID](#proof-middle-chord)
construction on this original cap. If \(\ell\) is the chord of its
roof between the endpoints of \(J\), put

\[
V=U\cap\{y\le\ell(x)\},\qquad
\varepsilon=1-\max_{(x,y)\in V}y,\qquad
W=V+[0,\varepsilon]e_y.
\tag{CE.11}
\]

The projection and middle interval are unchanged. The roof of \(V\)
agrees pointwise with that of \(U\) outside \(J\); on \(J\) it is
the chord \(\ell\). All outer supports decrease under the cut, so
the complete niche weakly decreases. MID.10 and the already proved
universal bound therefore give

\[
\frac M2=P(U)\le P(V)\le P(W)\le\frac M2.
\tag{CE.12}
\]

Every term is equal. The cap \(W\) is canonical, so CE1 identifies it
as a horizontal translate of \(U_*\). In particular CE.8 holds.
The extrusion deficit CE.9 and \(P(W)=P(V)\) force
\(\varepsilon=0\); otherwise the deficit is strictly positive on an
interval next to either middle endpoint. Thus \(W=V\), and its roof
is one throughout \(J\).

Finally \(V\subseteq U\subset\mathbb R\times[0,1]\) forces the
original roof to be one on \(J\) as well. Outside \(J\), the chord
cut already preserved that roof pointwise. Hence \(U=V=W\) as compact
sets. This proves the forward implication. The converse was included
in CE1. \(\square\)

The proof does not claim that middle-chord clipping is always strictly
improving. It can preserve the score on other inputs. What removes that
possible non-rigidity at the sharp value is the recovered unit-height
plateau, together with the original height ceiling.

### 6. Reference data available to later equality arguments

**Corollary CE4.** In the centered normalization, every full-turn
equality cap has

\[
I=[-a_*,a_*],\qquad J=[-C_*,C_*],\qquad
\text{top}=J\times\{1\},\qquad
A(-a_*)=A(a_*)=\frac12.
\tag{CE.13}
\]

Its two regular source curvatures have the exact end intervals

\[
f''+f=0,\quad g''+g=\frac12
\quad(0<t<\beta),
\]
\[
f''+f=\frac12,\quad g''+g=0
\quad(L-\beta<t<L).
\tag{CE.14}
\]

These follow from Note 14's explicit first and last pieces; the
centering term has zero curvature. The endpoint heights follow from
\(f'(0)=1/2\) and \(g'(L)=-1/2\). Both the top location and the
reflection symmetry are conclusions of equality, not assumptions on
the input cap.

The argument is for the cap functional. Passing from an equality body
to its two caps, excluding proper terminal angles, and using any
vanishing ordinary-area defects still require their own exact
arguments. In particular an almost-everywhere equality of arbitrary
compact bodies is not upgraded to set equality by CE3 alone.

---

<a id="proof-terminal-equality"></a>
## Technical proof 46. Strict proper angles and literal compact-body recovery (TB)

**Local maximizer convention.** A joint global maximizer means a pair
\((U,a)\) maximizing the full cap-and-angle objective over all compact
downward caps of height at most one and all
\(\pi/4\le a\le L=\pi/2\). Its value is \(M/2\) by G2C.
No largest-angle selection is assumed in this equality chapter.

### 1. The equality-selection issue

G2C proves the upper bound by assuming a value greater than \(M/2\),
selecting a joint maximizer with the largest terminal angle, and
contradicting that selection. This alone does not prove that an
individual equality cap has terminal angle \(L\): the global equality
set already contains the full-turn reference, so its largest angle is
\(L\) regardless of whether another equality cap has a proper angle.

The only use of that selection in the quantitative terminal argument
is TP.10's final step. TP first proves that a terminal facet with
\(m>w_H\) allows a small angle increase with the *same cap* and
unchanged barrier. The largest-angle choice then supplies its stated
contradiction. The next section gives a different contradiction at the
same point, valid for every proper-angle joint maximizer.

PS explicitly states that its fixed-angle identities and regularity
hold without a largest-angle choice. Its first theorem concerns the
actual charged outer measure of the prescribed maximizing cap: it has
bounded density on the visited open arcs, with a possible atom only at
the first terminal normal. This stronger quantifier is essential here.

### 2. A short terminal facet at every proper-angle maximizer

Let \((U,a)\) be any height-one, affine-middle joint maximizer with
\(a<L\), in PD's used-support normal form. The strict numerical cuts
AT, TP Section 1 and WC apply at value \(M/2\): each excluded range has
an explicit upper bound strictly smaller than \(M/2\). Thus

\[
I=[-2C,2C],\qquad J=[-C,C],\qquad
\frac{1001}{2000}<C<\frac{37}{50},\qquad
a>\arctan(8/3).
\tag{TB.1}
\]

Write the middle heights as
\(A(-C)=1-h_L\), \(A(C)=1-h_R\), with
\(h_L,h_R\ge0\), \(\min(h_L,h_R)=0\), and
\(h_L+h_R<17/50\) by TP Section 1. If the middle tilt
is negative, temporarily restrict to the residual case of
[NT](#proof-negative-completion):

\[
0<h_R<1-\sin a,\qquad
a<\theta_0=L-\arctan(h_R/(2C)).
\tag{TB.2}
\]

The other negative cases will be handled in Section 3. Put

\[
c=\cos a,\qquad s=\sin a,\qquad H=1-h_R,\qquad
b=C+T_R,\qquad d=\frac{1-Hs}{c},\qquad w=c-d.
\tag{TB.3}
\]

Then \(s<H\le1\), \(0<d<c<C\), and \(0<w<c/2\). The
actual first terminal facet has endpoints

\[
(b,H),\qquad (b+m,H-mc/s),\qquad m\ge0,
\tag{TB.4}
\]

and its shifted endpoints and outgoing zero are

\[
B_+=(b-c,H-s),\qquad B_-=B_++(m,-mc/s),\qquad r_0=b-d.
\tag{TB.5}
\]

The facet is on the charged right wing: \(b\ge C\), and if
\(m>0\), its open segment has \(x>C\) and arclength \(m/s>0\).
Its supporting normal is \((\cos a,\sin a)\).

The source horizontal-moment proof of TP.11 does not use a largest
angle or the terminal-facet bound. It gives

\[
T_L+2T_R\le d,\qquad T_R<d.
\tag{TB.6}
\]

In particular
\(0<(B_+)_x<r_0<C\). The same terminal-corner estimate as
TP.9 gives

\[
(z_a)_x<(B_+)_x.
\tag{TB.7}
\]

**Lemma TB1 (the terminal mass bound needs no extremal-angle
selection).** Under TB.1--7,

\[
\boxed{m\le w.}
\tag{TB.8}
\]

**Proof.** Suppose \(m>w\). Then
\((B_-)_x>r_0\). If
\((z_a)_x<x<(B_-)_x\), the terminal companion wall is greater
than the first wall, while the first wall has strictly negative left
angle derivative:

\[
S_a(x)>R_a(x),\qquad
\partial_-R_a(x)=\frac{x-(B_-)_x}{s^2}<0.
\tag{TB.9}
\]

The first identity is the two-wall intersection criterion; the second
uses the lower/right endpoint of the terminal support facet. The
companion support has no terminal atom by PS. Therefore sufficiently
close earlier angles have both walls strictly above \(R_a(x)\), so

\[
n_a(x)>R_a(x)
\quad\text{for }(z_a)_x<x<(B_-)_x.
\tag{TB.10}
\]

Here \(n_a\) includes the positive floor. For \(x\ge(B_-)_x\),
the outgoing wall is negative since \((B_-)_x>r_0\). Thus every
strict terminal exposure, and every relevant terminal tie, lies at
\(x\le(z_a)_x<(B_+)_x\). The right angle-variation inequality TV.3
is valid at every joint maximizer. Its nonnegative tie term vanishes
on this region, while its strict-exposure integrand is bounded above
by the strictly negative constant \((z_a)_x-(B_+)_x\). It follows
that the strict exposure set has measure zero. Continuity gives

\[
n_a\ge R_a\quad\text{on }J,\qquad N_a=n_a.
\tag{TB.11}
\]

We record explicitly that the ensuing angle extension keeps \(U\)
fixed. Choose

\[
\max\{-C,(z_a)_x\}<\zeta<(B_+)_x<r_0
<r_*<\min\{C,(B_-)_x\}.
\tag{TB.12}
\]

These choices are possible by TB.5--7 and \(m>w\). Immediately
after \(a\), the first support of this same cap is the fixed point
\((b,H)\). For negative tilt choose all angle increments below
\(\theta_0-a\); for the other two signs this harmonic tail runs to
\(L\). Its attached first walls have

\[
\partial_t R_t(x)=\frac{x-(b-\cos t)}{\sin^2t}.
\]

For \(x\le\zeta\) and \(t\ge a\) close to \(a\), this is
negative, so \(R_t(x)\le R_a(x)\le n_a(x)\). On the compact
interval \([\zeta,r_*]\), TB.10 gives a uniform strictly positive
gap \(n_a-R_a\). Uniform convergence of \(R_t\) to \(R_a\)
pays every new first wall there. Finally the positive zero of the new
first wall,

\[
r_0(t)=b-\frac{1-H\sin t}{\cos t},
\]

is continuous at \(a\), so it remains below \(r_*\) for a
sufficiently small increment. The new first walls are nonpositive for
\(x\ge r_*\). Consequently, for some \(\beta\in(a,L)\),

\[
R_t\le n_a\quad\text{on }J\quad(a\le t\le\beta).
\tag{TB.13}
\]

Every newly visited two-wall minimum is at most its first wall; the
new outgoing wall is also covered by TB.13. All old visited minima
remain in the new history. Therefore, pointwise on \(J\),

\[
N_{U,\beta}=N_{U,a},\qquad
\mathcal P_\beta(U)=\mathcal P_a(U)=M/2.
\tag{TB.14}
\]

The cap, height, projection, affine middle, and both charged wings have
not changed. Its used-support normal form is preserved as well: if
\(\ell\) is the same middle chord, the newly added support constraints
are valid for \(U\), so
\(U\subseteq\operatorname{Sat}_{\beta}(U)\cap\{y\le\ell\}
\subseteq\operatorname{Sat}_{a}(U)\cap\{y\le\ell\}=U\).
In particular the positive facet in TB.4 is still outside
the same middle window \(J\), still has arclength \(m/s>0\), and
still has normal \(a\). But now \(a\in(0,\beta)\): it is an
interior visited first normal for the joint maximizer \((U,\beta)\).
PS applies to this prescribed cap at its new fixed angle and forbids
any charged atom there. In the residual negative case
\(a<\beta<\theta_0\), so this is not the uncharged middle normal;
positive and horizontal middles likewise have no middle normal at
\(a<L\). This contradicts the unchanged positive charged facet.
Hence \(m\le w\). \(\square\)

No repeated continuation, limiting reachable set, new cap or change of
horizontal window occurs in this proof. The contradiction is already
available after one fixed-cap angle increment.

### 3. Every scalar equality cap has a full terminal angle

**Theorem TB2 (strict proper-angle cap inequality).** For every
downward compact convex cap \(U\) of height at most one,

\[
\boxed{\pi/4\le a<L
\quad\Longrightarrow\quad\mathcal P_a(U)<M/2.}
\tag{TB.15}
\]

**Proof.** G2C gives the non-strict upper bound. Suppose equality
holds at a proper angle. The height and middle-chord reductions of
PD do not decrease the score and keep the angle fixed. By the already
proved universal bound they therefore give a height-one affine-middle
joint maximizer at that same proper angle. PD4 and PD5 give its top
localization and used-support normal form. The cuts in TB.1 apply.

First suppose the canonical middle is negative and belongs to an
NT-completed branch: either \(a\ge\theta_0\) or
\(h_R\ge1-\sin a\). NT gives

\[
M/2=\mathcal P_a(U)\le\mathcal P_L(U)\le M/2.
\tag{TB.16}
\]

CE1 (or the stronger CE3) identifies this canonical full-turn equality
cap with the reference cap. That already contradicts a negative
middle slope. There is also a direct incompatibility with the partial unused-source
condition, as can be seen directly from its final circular phase.
In centered reference coordinates let

\[
\beta_* =\arctan Y,\qquad
m_* =\frac1{3\sin\beta_*},\qquad C_* =m_*/2.
\]

By CE4, for \(L-\beta_*<t<L\), its first support is

\[
f_*(t)=\frac12+C_*\cos t+\frac12\sin t,
\qquad f_*''+f_*=\frac12.
\tag{TB.17}
\]

The actual support point on this phase is

\[
\left(C_*+\tfrac12\cos t,\ \tfrac12+\tfrac12\sin t\right).
\tag{TB.18}
\]

Its abscissa is strictly greater than \(C_*\), so this is charged
right-wing curvature. The nonempty interval
\((\max\{a,L-\beta_*\},L)\) lies in the unused first arc of the
proper partial maximizer and has curvature density \(1/2\), contrary
to PD5 or PS1. Thus no NT-completed equality case exists.

All other cases are positive, horizontal or residual negative middle.
Lemma TB1 supplies \(m\le w_H\) without a largest-angle selection,
and TB.6 supplies the top projection bound. The remainder of Gate 2's
quantitative argument is now applicable to this individual maximizer.
For precision, its uses of an above-reference assumption were only to
ensure global maximality and the strict fixed numerical cuts; value
\(M/2>41/50\) already supplies those same hypotheses. The subsequent
estimates themselves use the displayed geometry and local source laws.

For \(0<\cot a\le1/8\),
[RX](#proof-near-full) gives \(v\le1\) through
\(\arcsin C\). For \(1/8\le\cot a<3/8\),
[AC](#proof-cubic-payment) gives the weighted
early-excess bound. The [MP comparison](#proof-weighted-moment)
then gives a strict terminal exposure interval longer than \(w_H\),
contradicting the separate fixed-angle PS occupation identity with
total occupation \(m\le w_H\). This exhausts the angle and tilt
cases and proves TB.15. \(\square\)

The theorem concerns the original individual cap and angle. The
canonical replacements are only used inside a contradiction and keep
that angle fixed. It does not assert that an original equality cap is
identified merely by choosing some other full-turn maximizer.

### 4. An independent global strip obstruction for the reference hull

The following elementary fact is stronger than a local terminal-angle
area penalty when the hull is the *actual hull* of the body.

**Lemma TB3 (only the horizontal unit-strip direction fits the reference
hull).** In its centered normalization the reference hull \(K_*\)
has width one in the vertical normal direction. Its width in every
other normal direction is strictly greater than one.

**Proof.** Its top and bottom faces both contain
\([-m_*/2,m_*/2]\), so

\[
[-m_*/2,m_*/2]\times[0,1]\subset K_*.
\tag{TB.19}
\]

The root equation \(4Y^3+3Y=1\), \(Y>0\), gives \(Y<1/3\)
and therefore \(\sin\beta_*<1/3\); hence \(m_*>1\).
For a unit normal \(n=(c,s)\), support width is at least the
width of the contained rectangle:

\[
\operatorname{width}_{K_*}(n)\ge m_*|c|+|s|.
\tag{TB.20}
\]

If \(c\ne0\), this is greater than \(|c|+|s|\ge1\).
For \(c=0\), the hull's vertical span is exactly one. This proves
the assertion. \(\square\)

Since convex hulls preserve support widths, every body whose actual
hull is \(K_*\) has the same obstruction. In particular a
correct-handed outgoing unit strip at a conventional angle
\(0\le a<L\) is impossible:

\[
\operatorname{width}_{K_*}(u_a)
\ge m_*\cos a+\sin a>1.
\tag{TB.21}
\]

This is a statement about the whole outgoing strip, independent of
which interior corners were visited. It also identifies the possible
incoming unit-strip normal of the reference body, up to sign.

There is no conflict with the partial auxiliary envelopes in
[the outgoing-strip area note](https://github.com/vltanh/lean4-moving-sofa/blob/b525305f344e635e6264cb470514d6b8bb7a8e43/docs/ambidextrous/romik-terminal-angle-outgoing-strip-rigidity.md).
An envelope cut from an auxiliary \(K_*\) may discard its extremal
face points and have a smaller actual hull. Lemma TB3 asserts the
obstruction when \(K_*\) remains the body's actual convex hull;
the older EP estimates instead bound the area lost by those cuts.

### 5. From equality caps to the actual compact body

Consider a compact connected admissible body \(S\) with \(|S|=M\).
Use the common-pose normalization and the *actual-hull* construction
of [Gate 0](#main-motions). It supplies
\(K=\operatorname{conv}S\subset\mathbb R\times[0,1]\), its
upper and reflected-lower downward caps \(U,V\), a common projection
\(I\), and independent conventional terminal angles
\(a,b\in[\pi/4,L]\). The actual body is contained in its canonical
envelope, and every envelope fiber is nonempty by connectedness of
\(S\). The sharp chain is

\[
M=|S|\le |E_{a,b}(K)|
\le\mathcal P_a(U)+\mathcal P_b(V)\le M.
\tag{TB.22}
\]

The second inequality is PD.4's spatial partition, with the signed
integral equal to ordinary area on this actual hull. Both scalar
deficits are nonnegative, so equality forces

\[
\mathcal P_a(U)=\mathcal P_b(V)=M/2.
\tag{TB.23}
\]

Equivalently, ED1 in the
[equality dependency audit](#proof-equality-audit)
expresses \(M-|S|\) as the sum of the two original scalar deficits,
the nonnegative spatial-partition defect, and the nonnegative filling
defect \(|E_{a,b}(K)\setminus S|\). Thus TB.23 retains the original
caps, rather than only their canonical replacements.

Theorem TB2 gives \(a=b=L\). CE3 now recovers each *original*
full-turn equality cap as a horizontal translate of the reference
cap, with height one. The two caps have the same projection \(I\),
so their horizontal translations agree. Their roofs recover the actual
hull by

\[
A_K=A_U,\qquad B_K=1-A_V.
\tag{TB.24}
\]

Thus the normalized actual hull is the corresponding translate of
\(K_*\). The exact support-tightened full-turn envelope is then the
same translate of the reference sofa \(\Sigma_*\), by the
[direct reference construction](#main-introduction), Section 3.
The containment from Gate 0 was for the original \(S\), so

\[
S\subseteq\Sigma_*,\qquad |S|=|\Sigma_*|.
\tag{TB.25}
\]

No cap replacement is substituted for the original body in TB.25.
The reversal of height extrusion and middle canonicalization occurs
inside CE3, before the original hull is identified.

**Lemma TB4 (regular-closed recovery).** If \(F\) is compact and
regular closed, \(S\subseteq F\) is closed, and
\(|S|=|F|\), then \(S=F\).

**Proof.** If \(p\in F\setminus S\), closedness of \(S\) gives
an open ball about \(p\) disjoint from \(S\). Since
\(F=\overline{\operatorname{int}F}\), that ball contains an
interior point of \(F\) and hence a smaller ball in
\(F\setminus S\). This has positive area, contradicting the area
equality. \(\square\)

The same direct construction proves that \(\Sigma_*\) is regular closed. Its central
survivor fibers are bounded by continuous strictly separated graphs;
outside the middle interval they are the unchanged convex-hull fibers.
At the horizontal extremes the convex flanks are limits of interior
points. Therefore every point of \(\Sigma_*\) is a limit of its
interior points, including face endpoints and extreme tips.

Applying TB4 to TB.25 and undoing the common rigid normalization gives
the exact body statement:

\[
\boxed{|S|=M\quad\Longrightarrow\quad
S\text{ is congruent to }\Sigma_*.}
\tag{TB.26}
\]

The converse is the already verified feasibility and exact area of
the reference. Lemma TB3 supplies an independent check that the
identified actual body cannot end a conventional turn at a proper
angle. The conclusion concerns the body and the extracted conventional
terminal angles; it does not claim that its arbitrary physical motion
witnesses have unique parameterizations or histories.

### 6. What happens to measure-zero changes

Area equality by itself does not imply equality of compact connected
sets: a disk together with an attached line segment has the disk's
area. That generic example is not a feasible equality counterexample
to TB.26. The proof uses two additional facts about the actual body.

First, an appendage outside the recovered reference hull would change
one of the original equality caps, contrary to CE3 and TB.24. An
appendage inside that hull but outside \(\Sigma_*\) would violate
the actual canonical envelope containment. Hence no new zero-area
appendage is left unexamined by the support argument.

Second, a proper closed subset of the regular-closed reference cannot
have its full area, by TB4. Thus no compact zero-area deletion is
possible either. The regular-closed hypothesis belongs to the larger
identified envelope; no regularity assumption on arbitrary competing
bodies has been introduced.

Compactness matters for literal set uniqueness. If it were dropped,
removing one upper boundary point of \(\Sigma_*\) would leave a
nonclosed set with the same area and the same feasible motions. Choose
the removed point away from the horizontal midline. Every remaining
point can still be joined vertically to that midline, and then along
the midline, so the resulting set remains connected. This is a genuine
counterexample to literal uniqueness in a broader class of nonclosed
connected measurable bodies; it lies outside the stated compact-body
domain.

Motion witnesses are also nonunique even for the same exact body:
time reparameterization, waiting, or additional translations while
fully inside a straight arm preserve feasibility. No equality claim
here identifies those choices.

---

<a id="proof-equality-audit"></a>
## Technical proof 47. Exact body deficits, equality dependencies and counterexamples (ED)

### 1. An exact deficit for the original two-cap partition

Let \(S\) be an actual compact connected admissible body of area greater
than \(\sqrt2\). Normalize its common incoming strip to
\(0\le y\le1\). The [Gate 0 audit](#main-motions)
supplies the actual hull \(K=\operatorname{conv}S\), its projection
\(I=[l,r]\), and two independent canonical terminal magnitudes
\(\alpha,\gamma\in[\pi/4,\pi/2]\). It retains the outgoing whole-body
strip for each motion.

Let \(U\) have the actual upper hull roof \(A_U=A_K\), and let \(V\)
have roof \(A_V=1-B_K\), where \(B_K\) is the actual lower hull roof.
These are the original downward caps; no cap replacement has yet been
made. For every upward normal, the downward upper cap has the same
support as \(K\), because maximizing that normal over each vertical
fiber selects its upper endpoint. The reflected statement identifies
the supports of \(V\) with those of the reflected hull.

Put

\[
J=[l+(r-l)/4,r-(r-l)/4],\qquad
d_U=1-A_U,\quad d_V=1-A_V,
\]
\[
N_U=N_{U,\alpha},\qquad N_V=N_{V,\gamma},
\]

where each \(N\) is the entire partial barrier from G2C.3, including
the whole terminal first wall. The exact signed fiber is

\[
\ell=1-\max(d_V,N_U)-\max(d_U,N_V).
\tag{ED.1}
\]

Define the partition defect

\[
\begin{aligned}
D_{\rm part}={}&
\int_J\bigl[(d_V-N_U)_++(d_U-N_V)_+\bigr]\,dx\\
&+\int_{I\setminus J}
\bigl[(N_U-d_V)_++(N_V-d_U)_+\bigr]\,dx.
\end{aligned}
\tag{ED.2}
\]

Subtract ED.1 from \(1-N_U-N_V\) on \(J\), and from
\(A_U+A_V-1\) on its complement. The identity
\(\max(a,b)-a=(b-a)_+\), together with
\(|J|=|I\setminus J|\), gives the exact formula

\[
\boxed{
\mathcal P_\alpha(U)+\mathcal P_\gamma(V)
-\int_I\ell\,dx=D_{\rm part}\ge0.}
\tag{ED.3}
\]

This is the signed version of
[SPB.4](#main-equality), with both terminal strips
included. It holds for arbitrary auxiliary convex hulls as well, even
when some signed fibers are negative.

For the actual connected body, Gate 0 gives a canonical envelope
\(E\supseteq S\). Connectedness implies
\(\operatorname{proj}_x S=I\), so every \(E\)-fiber is nonempty and
\(\ell\ge0\) everywhere. Thus \(|E|=\int_I\ell\), and

\[
D_{\rm fill}:=|E\setminus S|=\int_I\ell\,dx-|S|\ge0.
\tag{ED.4}
\]

**Theorem ED1 (exact original-body equality deficit).** With
\(M\) as in G2C.1,

\[
\boxed{
M-|S|
=\left(\frac M2-\mathcal P_\alpha(U)\right)
 +\left(\frac M2-\mathcal P_\gamma(V)\right)
 +D_{\rm part}+D_{\rm fill}.}
\tag{ED.5}
\]

Every term on the right is nonnegative by G2C1, ED.2 and ED.4.
Consequently \(|S|=M\) forces both **original** caps to be scalar
equality caps, both partition integrals to vanish, and \(|E\setminus S|=0\).
The pointwise partition conditions are, almost everywhere,

\[
\begin{array}{ll}
d_V\le N_U,\ d_U\le N_V,&x\in J,\\
N_U\le d_V,\ N_V\le d_U,&x\in I\setminus J.
\end{array}
\tag{ED.6}
\]

Their continuous representatives satisfy the same inequalities on the
interiors of the respective intervals. No assertion that \(S=E\) has
yet been made. For an auxiliary hull, ED.3 still holds, but ED.4 must
not be asserted without its actual-body hypotheses.

### 2. The finite selections can target any canonical equality cap

The headline statement of
[RG](#proof-prescribed-regularity) is existential.
For rigidity, merely exhibiting one regular maximizer would be
insufficient. Its selection proof gives the following stronger
quantifier, which must be stated when used.

**Theorem ED2 (regularity of every prescribed canonical maximizer).**
Let \(U_0\) be any height-one global maximizer of the full-turn spatial
score whose entire middle roof is affine. The regularity and nonlinear
wing-curvature bounds in RG.15--RG.17 hold for this same \(U_0\).
The endpoint and exposure conclusions of
[EP](#proof-full-endpoints) and
[LH](#proof-full-pressures) can likewise
be obtained from selections converging to \(U_0\).

**Proof.** Translate \(U_0\) strictly inside the artificial box of RG.
Let \(P_n\) be the sampled spatial score and
\(e_n=\sup(P_n-P)\to0\), uniformly on that compact cap domain.
Use exactly RG's support-distance penalty centered at \(U_0\), and
let \(\eta_n=\sqrt{e_n}+1/n\). The grid circumscription of \(U_0\)
has zero penalty and sampled score at least \(P(U_0)=P_{\max}\).
For a penalized optimizer \(U_n\), therefore,

\[
P_{\max}\le P_n(U_n)-\eta_nD_n(U_n,U_0)^2
\le P_{\max}+e_n-\eta_nD_n(U_n,U_0)^2.
\]

Hence

\[
D_n(U_n,U_0)^2\le e_n/\eta_n\longrightarrow0.
\tag{ED.7}
\]

Compactness and the positive Riemann-sum support weights identify every
Hausdorff subsequential limit with \(U_0\). The whole sequence converges
to that prescribed cap. RG's neighboring-wall estimates, vanishing
middle-facet error away from its single normal, and measure domination
now apply to this sequence. They prove the stated regularity of
\(U_0\), not of a different replacement maximizer. EP uses the same
penalization and explicitly allows any prescribed global maximizer.
Its trimming and erosion arguments, followed by LH's strict
positive-pressure exclusion, concern this same target. \(\square\)

No such statement has been inferred for an arbitrary uncanonicalized
maximizer. Its middle roof must first be handled with an inverse
argument, as in Section 4.

### 3. What strict functional calibration does and does not require

The horizontal sharp branch gives

\[
P(U_0)\le F(f,g)-W/2\le M/2
\tag{ED.8}
\]

by [CH.25--CH.26](#proof-full-curvature).
This comparison is used only after its geometric hypotheses, including
both unit wing bounds and niche confinement, have been proved for the
prescribed canonical maximizer.

At equality in ED.8, the strict functional theorem
[AF3](#proof-adaptive) identifies the upper
support pair. To see that its full-profile quantifier applies, define
the upper-half profile by \(h(t)=f(t)\), \(h(t+\pi/2)=g(t)\), and
extend by

\[
h(-t)=h(t)-\sin t\qquad(0\le t\le\pi).
\tag{ED.9}
\]

The endpoint conditions make this a periodic \(H^1\) profile with
\(h(\pi/2)=1\), \(h(3\pi/2)=0\), and horizontal width \(W>2\).
Its reflected upper pair is precisely \((f,g)\), so

\[
\widetilde{\mathcal Q}(h)=2F(f,g)-W=M.
\tag{ED.10}
\]

AF3's equality kernel is the reference profile plus horizontal
translation. It is a theorem on **all real \(H^1\) profiles**, so the
extension need not independently be proved convex or smooth. Strict
fixed-width concavity is already coercive on \(H^1_0\), and the
width-stationary classification is performed in that function space.
There is no inference that a geometric optimizer is smooth because an
unrelated auxiliary optimizer happens to be smooth.

The strict wide-horizontal exclusions and tilted-maximizer exclusions
in [G1C](#proof-full-closure) use only global maximality,
the reference lower value and the necessary laws of ED2. Thus their
contradictions apply at value \(M/2\) as well as in the earlier
hypothetical-above-reference proof. They force a canonical equality
cap into the horizontal branch ED.8. This exposes the precise route to
canonical full-turn rigidity rather than assuming rigidity from G1C1.

### 4. Reversing the middle chord and height extrusion

**Lemma ED3 (exact inverse at the reference).** Suppose \(U\) is an
arbitrary cap of full-turn scalar value \(M/2\). Intersect it with
the halfplane under its middle chord to obtain \(V\), then extrude
vertically by \(\varepsilon=1-\max A_V\) to obtain \(U_c\).
If canonical equality classification gives
\(U_c=U_*\), after horizontal translation, then
\(\varepsilon=0\) and \(U=V=U_*\).

**Proof.** Both maps are score-nondecreasing by MID and SD, and the
universal bound is \(M/2\). Hence
\(P(U)=P(V)=P(U_c)=M/2\). Vertical extrusion has the exact roof
identity

\[
A_V=A_*-\varepsilon.
\]

For every upward unit normal \(n\), maximizing over the translated
roof gives
\(h_V(n)=h_*(n)-\varepsilon n_y\). Both inner walls consequently
decrease by \(\varepsilon\), and

\[
n_V=(n_*-\varepsilon)_+.
\]

The two horizontal integration regions have the same length. Therefore

\[
\boxed{P(U_*)-P(V)
=\int_J(\varepsilon-n_*(x))_+\,dx.}
\tag{ED.11}
\]

The reference niche is continuous and vanishes at both endpoints of
its middle window. If \(\varepsilon>0\), a one-sided interval inside
\(J\) has \(n_*<\varepsilon\), so ED.11 is strictly positive.
This contradicts equality of the scores. Thus \(\varepsilon=0\) and
\(V=U_*\). Chord clipping leaves \(U\) unchanged outside \(J\).
Inside \(J\), it gives \(A_U\ge A_V=1\), while the original strip
gives \(A_U\le1\). Hence the original cap equals the reference
everywhere. \(\square\)

This also recovers exact height one; no separate strict-height theorem
for all caps is needed. The argument uses the vanishing reference niche
at the window endpoints, not injectivity of canonicalization in
general.

For an exact check of that distinction, let
\(I=[-1/4,1/4]\) and \(A(x)=1/2-|x|\). Its middle chord clips the
roof to \(\min(1/2-|x|,3/8)\), a different cap. Both full positive
niches vanish: for either cap, every corner height is at most

\[
\frac12+\frac12\sin t\cos t-\sin t-\cos t\le-\frac14.
\]

The exterior roofs coincide and their common score is \(5/64\).
Thus equal score through chord clipping alone is not a general
geometric equality statement. ED.11 is the additional sharp-reference
argument that makes its inverse valid here.

### 5. A largest-angle choice is not an equality theorem

Gate 2's value proof may select a largest terminal angle among global
maximizers. That is enough to rule out an above-reference global value.
It does not, on its own, rule out another global maximizer at a smaller
angle after the sharp value has been proved.

The logical distinction is already visible for the continuous function
\(F(x,a)=-x^2(1-a)^2\) on \([0,1]^2\): all largest-angle maximizers
have \(a=1\), but \((0,a)\) is a maximizer for every smaller angle.
This is a quantifier counterexample, not a proposed sofa.

The additional geometric lemma is now proved as
[TB1](#proof-terminal-equality), using
[TP, Section 3](#proof-terminal-geometry).
If a canonical equality cap has terminal facet length \(m>w_H\),
that argument, before appealing to the largest-angle choice, produces
a strictly larger angle with the **same cap and unchanged barrier**.
The old positive charged terminal facet then lies at an interior used
normal. [PS1](#proof-partial-sources) applies to any
prescribed canonical joint maximizer without a largest-angle
hypothesis and forbids such an interior charged atom. This fixed-cap
contradiction extends \(m\le w_H\) to every equality pair. The remaining
MP/RX/AC contradiction therefore applies with that stronger quantifier.

The negative-completion alternative needs its own equality check:
completion gives full-turn scalar equality for the same canonical cap;
full-turn rigidity identifies it with \(U_*\). The reference has
positive charged circular curvature on first normals arbitrarily close
to \(\pi/2\), whereas PD5 forbids charged curvature on the unvisited
open arc of a proper partial maximizer. These statements are
incompatible. Merely saying that completion does not lose value would
not be enough.

The proved consequence [TB2](#proof-terminal-equality) is strictness
\(P_\alpha(U)<M/2\) for every \(\alpha<\pi/2\), while the full-turn
equality caps are horizontal translates of \(U_*\) by
[CE3](#proof-full-equality). Both the fixed-cap extension
and equality classification have received independent mathematical
checks in this audit; they are additional results beyond the original
value-only Gate 2 proof.

### 6. Original hull alignment and literal compact-set recovery

Apply the now-proved full-turn scalar rigidity CE3 and strict
proper-angle scalar inequality TB2. ED1 then gives
\(\alpha=\gamma=\pi/2\), and both original caps are translates of
\(U_*\). They have the same actual interval \(I\). Since the
reference cap has fixed positive width, equality of these intervals
forces the two horizontal translation parameters to coincide. Thus

\[
A_K=A_*,\qquad B_K=1-A_*,\qquad K=K_*.
\tag{ED.12}
\]

This is equality of the **original hull**, not of a hull produced by
area-preserving compression or independent cap replacement. Gate 0's
support tightening changes the hallway witnesses while retaining the
body and its hull. Its auxiliary-envelope connectedification is not
used for this equality implication.

Now \(S\subseteq E_{\pi/2,\pi/2}(K_*)=\Sigma_*\), and ED1 gives
\(|\Sigma_*\setminus S|=0\). The reference envelope is regular closed.
Here is the property needed for that assertion. Its roofs are
continuous, \(A_*>1/2\) on the interior of its projection by concavity
between the endpoint values \(1/2\) and the middle plateau value one,
its niche is zero outside the plateau, and its niche has a strict
height ceiling below \(1/2\) by
[the reference separation calculation](#proof-reference-height).
Consequently its vertical fiber has strictly positive length at every
interior abscissa. Points of every boundary fiber are limits of points
in the interior of the envelope; the two extreme fibers are limits
from interior abscissae. Hence
\(\Sigma_* = \overline{\operatorname{int}\Sigma_*}\).

**Lemma ED4 (literal body recovery).** If a compact regular-closed set
\(F\) contains a closed set \(S\) and \(|F\setminus S|=0\), then
\(S=F\).

**Proof.** A point of \(F\setminus S\) has a neighborhood disjoint
from \(S\), since \(S\) is closed. Regular closedness places an
interior point of \(F\) in that neighborhood, and then a positive-area
ball in \(F\setminus S\), a contradiction. \(\square\)

This is [Lemma 4](https://github.com/vltanh/lean4-moving-sofa/blob/b525305f344e635e6264cb470514d6b8bb7a8e43/docs/ambidextrous/01-two-motion-envelopes.md), with its larger-set
hypothesis explicitly verified at the identified reference envelope.
It rules out zero-area deletions. Zero-area appendages are excluded
earlier, by the recovered original hull and canonical containment.

Even connectedness, equal area and the same hull do not replace that
last argument. Let \(D\) be the closed disk of radius \(1/4\), and set

\[
S_0=D\cup([0,3/8]\times\{0\})
       \cup(\{0\}\times[0,3/8]),
\]
\[
S_1=S_0\cup[(3/8,0),(0,3/8)].
\tag{ED.13}
\]

These are distinct compact connected sets with the same convex hull
and area \(\pi/16\). They are both genuine two-full-turn bodies:
both fit in a disk of radius \(3/8\), which can be translated into
the unit-square corner, rotated there, and translated along either
unit outgoing arm. The new segment adds no area and lies in the old
convex hull, but its midpoint \((3/16,3/16)\) is outside \(S_0\).
This low-area example invalidates an unqualified almost-everywhere to
compact-set inference, without challenging sharp-reference recovery.

Body uniqueness does not mean uniqueness of motion witnesses. The
canonical angle conclusion says that each original equality motion
must reach its correctly handed quarter turn; otherwise Gate 0 would
supply a proper equality pair. It does not prohibit pauses, upstream
translations or backtracking in a supplied witness.

### 7. What a manuscript must expose

A self-contained derivation of the new reductions can be assembled
from the accepted proofs, but a list of closure notes is not that
manuscript. The following items must appear with their hypotheses and
proofs, or as explicitly stated external inputs:

| Part | Required material |
|---|---|
| Original domain | The two independent motions, correct-handed angle reach, actual outgoing strips, common hull, signed fibers and connected projection. |
| Scalar domain | Height extrusion, middle chord, width coercivity, moving-window continuity, attainment, top insertion and used-support saturation. |
| Source selection | Penalization targeting the prescribed cap, zero-end-face complementarity, inward trimming, erosion, finite source occupation and removal of charged singular curvature. |
| Full-turn value | The unit-wing geometric comparison, the \(H^1\) calibration, all strict horizontal/tilted exclusions, and the exact feasibility argument before the ordinary one-turn bound is applied. |
| Partial-turn value | One-sided angle derivatives with historical ties, the genuine finite-angle bounds, terminal facet mass, weighted companion comparison, reflected impulse and both error-payment ranges. |
| Equality | The all-canonical quantifier ED2, strict calibration, inverse ED3, fixed-cap terminal extension contradiction, original two-cap deficit ED.5 and literal set recovery ED4. |
| Reference and inputs | Exact reference functions, matching and area, the reference feasibility input, and the precise ordinary one-turn theorem and rational area enclosure used by Gate 1. |

The external ordinary one-turn theorem is used to strictly exclude
nonreference full-turn branches. No equality classification for that
external theorem is required. The present rigidity argument must not
claim that theorem's uniqueness as an unstated input.

The manuscript should describe itself accurately as a complete
derivation from its explicitly stated external theorems if their
proofs are not reproduced. Its exact rational checks are reproducible
arithmetic evidence; they do not replace the continuum source or
compactness arguments. Historical statements that a gate was then
open, and historical conditional routes no longer used, must not be
mixed into its current proof without clear scope labels.

No external acceptance, kernel verification or uniqueness of motions
is implied by completion of this written equality audit.

---

<a id="external-inputs"></a>
## External-input cross-reference

The ordinary one-turn theorem and the exact rational Gerver enclosure are stated in Chapter 1, Section 6 and detailed in the full-turn closure's dependency section. No equality case of that external theorem is imported. Every application constructs a genuine feasible compact connected one-turn body first.

<a id="verification-record"></a>
## Verification and review record

The continuum arguments and equality deductions received separate mathematical checks within this research session. The final equality audit is included above. External referee acceptance and Lean-kernel verification are not claimed.

The existing fixed final arithmetic checkers report 74 exact rational checks for Gate 1 and 83 for Gate 2. They corroborate the displayed finite rational and squared comparisons. They do not check the continuum geometric proofs. No angle search, new numerical optimization, Lean/Lake command or CI run is part of this compilation.

The reproducible assembly records every selected source section and its SHA-256 digest in gate3-manuscript-manifest.json. Its check mode verifies that this manuscript and the manifest match those source sections exactly after the recorded prelude, editorial, heading and link transformations. This is an integrity check, not a mathematical proof checker.
