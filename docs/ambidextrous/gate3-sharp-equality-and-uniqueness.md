# Gate 3 closure: exact equality and uniqueness in the original motion domain

**October 10, 2026. Gate 3: PASS under the written-proof and
self-contained-manuscript acceptance criteria.**
The new proof classifies every original equality cap, rules out every
proper terminal angle at the sharp value, and recovers the actual
compact body. It uses the completed Gate 0--2 written value proofs;
their external ordinary one-turn area input remains explicit.
The [complete manuscript](GATE3-MANUSCRIPT.md) and its
[independent dependency review](gate3-manuscript-dependency-audit.md)
are complete and accepted. External refereeing and Lean-kernel
verification remain separate from this written result.

## 1. Exact theorem and reference

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
given in [the reference calculation](14-sharp-quadratic-calibration.md)
and [the direct geometric construction](gate3-manuscript-introduction.md), Section 3.

**Theorem G3C1 (all scalar equality cases).** Let \(U\) be any nonempty
compact downward convex cap in \(\mathbb R\times[0,1]\), and let
\(\alpha\in[\pi/4,\pi/2]\). Use the actual partial spatial functional
of [G2C.2--3](gate2-sharp-partial-turn-closure.md), including the whole
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

## 2. Full-turn equality and reversal of canonicalization

The [full-turn equality theorem CE](gate3-full-turn-cap-equality.md)
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

## 3. Proper-angle equality is impossible

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
[terminal-atom theorem TB1](gate3-terminal-and-body-rigidity.md)
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

## 4. An exact deficit identity recovers the two original caps

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

## 5. Exact compact-body recovery and angular reach

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

## 6. Dependency, review and scope

The [equality dependency audit](gate3-equality-dependency-audit.md)
checks the prescribed-cap quantifier, exact positive deficits, partial
angle boundaries, hull retention and regular-closed recovery.
The equality chain is
\[
\text{Gate 0--2 proofs and maximizing laws}\ \Longrightarrow\
\text{CE full equality}\ \Longrightarrow\
\text{TB proper-angle strictness}\ \Longrightarrow\
\text{original hull and exact body equality}.
\tag{G3C.13}
\]
No equality case of the external ordinary one-turn theorem is used.
Its only role, inherited from Gate 1, is a strict contradiction in
discarded branches after genuine one-turn feasibility was proved.

The sharp area constant is unchanged from Gate 2. The new conclusions
are all equality caps, strict proper-angle cap values, actual-hull
rigidity and exact uniqueness of the compact maximizing body.
These conclusions meet the mathematical requirements of
[the Gate 3 roadmap](GATE3-ROADMAP.md). The manuscript and its final
accepted dependency audit complete the remaining presentation and
review requirements.

## 7. Manuscript, acceptance record and verification

The [complete manuscript](GATE3-MANUSCRIPT.md) contains five integrated
chapters followed by 47 essential technical proof sections. Its first
chapters state the motion domain, construct the actual reference body,
prove the full and partial cap theorems, and recover exact uniqueness.
The technical sections include the finite source selections, endpoint
laws, signed-roof calibration, all branch exclusions and exact equality
reversals. No indispensable domestic proof is replaced by a link to
an omitted research note.

| Acceptance item | Completed evidence |
| --- | --- |
| Every original equality cap | CE1--CE4, including prescribed-target selection and exact reversal of the middle cut and extrusion |
| Every proper terminal angle | TB1--TB2, with the unchanged-cap extension and interior charged-atom contradiction |
| Actual hull and compact body | G3C.9--12, TB3--TB4 and ED1--ED4; both original caps, independent angles and regular closedness are retained |
| Complete manuscript | 52 proof sections, 83,574 whitespace-delimited words; the mathematical chain and explicit external inputs are included |
| Separate mathematical reviews | CE, TB, ED, G3C and all integrated chapters accepted; final manuscript dependency and extraction audit accepted |

The [source manifest](gate3-manuscript-manifest.json) records the
selected ranges, exact source hashes, local preludes and every editorial
replacement. Its [deterministic compiler](computer-assisted/build_gate3_manuscript.py)
was independently checked in comparison mode:

~~~text
PASS: 52 proof sections, 83574 whitespace words, 291 internal links.
Unresolved relative destinations: 0; broken internal links: 0.
~~~

The accepted manuscript SHA-256 is

    0d1b8a41f3684c9eade825678bca13aaef3350a50799302f2aef8fa604c9015f

The text comparison verifies assembly integrity; the separate
mathematical reviews address the continuum arguments. Gate 3 introduces
no numerical search or new arithmetic certificate and makes no claim
of external referee acceptance or Lean verification. The prior fixed
Gate 1 and Gate 2 arithmetic checks retain their narrower roles.

**Gate 3 is closed.** The exact area constant remains the value already
established by Gate 2; the new result is the complete equality
classification and literal uniqueness of the compact maximizing body.
