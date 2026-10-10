# Gate 2 roadmap: partial turns with the actual outgoing strips

**October 10, 2026. Status: COMPLETED — Gate 2 PASS as a written proof.**
The [closure theorem](gate2-sharp-partial-turn-closure.md) proves the
universal partial-cap value and the original-motion sharp area, with the
[dependency and coverage audit](gate2-dependency-coverage-audit.md)
accepted. This roadmap records the chosen global theorem, the reductions
developed for it, and the final argument that closes the remaining
maximizer domain. External review and Lean verification remain separate.

The controlling documents remain
[the execution plan](SHARP-OPTIMALITY-EXECUTION-PLAN.md) and
[the consolidated handoff](CONSOLIDATED-RESEARCH-HANDOFF.md). Research stays
in this documentation tree; no Lean/Lake, CI, or original Lean changes enter
the argument.

## 1. What is already available

The [Gate 1 closure](gate1-sharp-full-turn-closure.md) proves

\[
\mathcal P_L(U)\le M/2,\qquad
M=1+4Y^2+\arctan Y,\quad 4Y^3+3Y-1=0,\quad Y>0,
\qquad L=\pi/2,
\]

for **every** compact downward convex cap of height at most one, with its
own middle-half window and full positive two-wall niche. It consequently
bounds every genuine two-full-turn sofa and the signed full-turn functional
on every auxiliary convex hull. Romik gives exact equality. The external
ordinary one-turn theorem used in Gate 1 remains an explicit dependency.

For every body of area greater than \(\sqrt2\), hence every potential
above-\(M\) competitor, the
[Gate 0 audit](original-motion-global-bridge-gate0-audit.md) reduces
arbitrary original motions, including backtracking, to independent actual
terminal magnitudes \(\alpha,\gamma\in[\pi/4,L]\), retaining both whole-body
outgoing strips. It also supplies the signed-fiber correction and the
area-value reduction to a compact convex-hull domain. Thus the exact final
target is still PLAN.3, without symmetry, unit-span, or completion premises.

## 2. The universal partial-cap theorem

Let \(U\subset\mathbb R\times[0,1]\) be a nonempty compact downward convex
cap with roof \(A\), projection \(I=[l,r]\), width \(W=r-l>0\), and

\[
J=[l+W/4,r-W/4].
\]

With \(\mu_t=(\cos t,\sin t)\), \(\nu_t=(-\sin t,\cos t)\), define the
actual first and second inner walls

\[
R_t(x)=\frac{h_U(\mu_t)-1-x\cos t}{\sin t},\qquad
S_t(x)=\frac{h_U(\nu_t)-1+x\sin t}{\cos t}.
\tag{G2.1}
\]

For \(\pi/4\le\alpha<L\), put

\[
\boxed{q_{U,\alpha}(x)=\max\left\{0,
\sup_{0<t<\alpha}\min\{R_t(x),S_t(x)\},R_\alpha(x)\right\}.}
\tag{G2.2}
\]

The final term is a **whole first wall**, imposed by the outgoing straight
strip. At \(\alpha=L\) define \(q_{U,L}=n_U\); the limiting terminal wall
is \(h_U(e_y)-1\le0\), so it is redundant. Set

\[
\mathcal P_\alpha(U)=\int_{I\setminus J}A(x)\,dx
-\int_Jq_{U,\alpha}(x)\,dx.
\tag{G2.3}
\]

**Global lemma, now proved as G2C1 in the closure:**

\[
\boxed{\mathcal P_\alpha(U)\le M/2
\quad\text{for every such cap and every }\alpha\in[\pi/4,L].}
\tag{G2.4 -- PROVED}
\]

This is a sufficient separated inequality. It is stronger than the
necessary joint claim; a counterexample to G2.4 would require changing this
scalar relaxation, not rejecting the original sofa bound.

### Exact implication for both independent turns

For a common convex hull \(K\), use its upper downward cap \(U\) and
reflected-lower downward cap \(V\), with common \(I,J\). The exact signed
fiber is

\[
\ell=1-\max\{1-A_V,q_{U,\alpha}\}
-\max\{1-A_U,q_{V,\gamma}\}.
\]

On \(J\), use \(\ell\le1-q_{U,\alpha}-q_{V,\gamma}\); on its complement,
use \(\ell\le A_U+A_V-1\). The two constant integrals cancel because
\(|J|=|I\setminus J|=W/2\). Therefore

\[
\boxed{\mathscr V(K,\alpha,\gamma)=\int_I\ell
\le\mathcal P_\alpha(U)+\mathcal P_\gamma(V).}
\tag{G2.5}
\]

This is valid even for auxiliary hulls with negative signed fibers. For a
genuine connected body, Gate 0 gives \(|S|\le\int_I\ell\). Consequently
G2.4 for independent caps and angles proves PLAN.3, and Gate 0 plus Romik
then gives \(\mu_{\rm amb}=M\). No separate symmetric-angle case is enough.

## 3. Angle exclusions and the current maximizer domain

The initial support cancellation below is now strengthened by
[AT](gate2-all-width-terminal-angle-exclusion.md):

\[
\boxed{\pi/4\le\alpha\le\arctan(8/3)
\quad\Longrightarrow\quad
\mathcal P_\alpha(U)<\frac{5259}{6400}<\frac M2}
\tag{G2.7a}
\]

for every cap and every width. AT retains the whole outgoing wall, the
45-degree tent, all window and floor clips, and the compatibility of
their actual support parameters. Its piecewise quadratic relaxation has
an exact supporting-plane certificate; it is not an angular sampling
bound. The elementary cancellation is retained here as its first case.

This elementary estimate applies to the **entire** cap domain; it needs no
stationarity or prescribed contact geometry. Center \(I=[-2C,2C]\), so
\(J=[-C,C]\). For \(\alpha<L\), write

\[
a=\cot\alpha>0,\qquad H=h_U(\mu_\alpha)/\sin\alpha.
\]

The actual outgoing support gives \(A(x)\le H-a x\) and
\(q_{U,\alpha}(x)\ge H-\csc\alpha-a x\). Bound the left exterior by height
one, use this outer support on the right exterior, and charge only the
left half of \(J\). Even if its affine lower bound is negative, the latter
step is valid, since the discarded niche charge is nonnegative. Thus

\[
\begin{aligned}
\mathcal P_\alpha(U)
&\le C+\int_C^{2C}(H-a x)\,dx
-\int_{-C}^0(H-\csc\alpha-a x)\,dx\\
&=(1+\csc\alpha)C-2\cot\alpha\,C^2\\
&\le\frac{(1+\csc\alpha)^2}{8\cot\alpha}.
\end{aligned}
\tag{G2.6}
\]

For \(a\in[4/5,1]\), the last expression
\((1+\sqrt{1+a^2})^2/(8a)\) decreases with \(a\): its derivative has the
sign of \(\sqrt{1+a^2}-2<0\). Since \(\sqrt{41}<641/100\),

\[
\boxed{\alpha\in[\pi/4,\arctan(5/4)]
\Longrightarrow\mathcal P_\alpha(U)
\le\frac{33+5\sqrt{41}}{80}
<\frac{1301}{1600}<\frac{41}{50}<\frac M2.}
\tag{G2.7}
\]

The last exact reference comparison is recorded in the Gate 1 closure.
This closes an initial interval of the **scalar** problem. It does not by
itself bound the companion cap at an arbitrary larger terminal angle.

### 3a. The attained-maximizer reduction is proved

[PD](gate2-partial-cap-domain-reductions.md) proves height extrusion,
middle-chord reduction, width coercivity, joint continuity and attainment,
top insertion for both middle-slope signs, and saturation of the unused
outer normals. If G2.4 fails, choose a joint global maximizer with the
largest terminal angle and put it in this canonical form. Its middle is
affine and its height is one.

[PS](gate2-partial-endpoint-source-and-green.md) rederives its finite-source
limit, actual endpoint complementarity, positive pressures, wing/source
identity and Green balance for the partial barrier. It keeps the possible
first terminal facet atom, proves the absence of a companion terminal
atom, and supplies the bounded regular-curvature inequalities on the used
arcs. [TV](gate2-terminal-angle-variations.md) gives both one-sided angle
derivatives, including historical ties. A common fractional occupation
for separate shape and angle variations has not been assumed.

The three visited-angle comparisons and the endpoint identities yield
the all-sign bounds

\[
\frac{1001}{2000}<C=\frac W4<\frac{37}{50},\qquad
0\le h=|A(C)-A(-C)|<\frac{17}{50}.
\tag{G2.8}
\]

The lower width and tilt cuts are transferred explicitly in
[TP](gate2-terminal-facet-and-prefix-reduction.md). The upper width cut
is the new [WC](gate2-three-angle-width-cut.md), which replaces the
unavailable full-niche endpoint boxes by the exact partial endpoint
pressures. It is valid throughout the remaining angle interval.

### 3b. Terminal geometry and the excluded maximizer cases

Write \(c=\cos\alpha\), \(s=\sin\alpha\). The
[negative-tilt completion theorem](gate2-negative-tilt-completion.md)
already pays every negative middle with \(h\ge1-s\), and every negative
middle whose central normal has been visited. In the remaining cases,
write \(H=1\) for positive or horizontal middle and \(H=1-h>s\) for
negative middle, and put

\[
d=\frac{1-Hs}{c},\qquad w_H=c-d.
\]

If \(m\) is the charged horizontal length of the first terminal facet,
and \(T_L,T_R\) are the left and right height-one top overhangs, TP proves

\[
m\le w_H<\frac c2,\qquad T_L+2T_R\le d.
\tag{G2.9}
\]

The [reflected prefix theorem](gate2-small-deficit-companion-prefix.md)
then excludes every such largest-angle joint maximizer with
\(0<c\le1/25\), for all three signs of the middle slope. It controls the
terminal impulse in the reflected arm energy, bounds the companion
curvature on precisely the initial interval needed for the argument,
and makes the strict outgoing exposure longer than the entire available
terminal facet. This is a **maximizer exclusion**, not a separate claim
that every cap at these angles is bounded without solving the remaining
global maximizer cases.

For positive tilt, [PU](gate2-positive-tilt-first-unit-exclusion.md)
excludes every selected maximizer with first regular-wing curvature at
most one. [IM](gate2-initial-mask-energy.md) proves that bound whenever
\(C\le2/3\), and gives an additional exact initial floor/outgoing-strip
energy criterion for wider caps.

At the first proof checkpoint, the remaining contradiction target was a
selected joint maximizer in

\[
\boxed{\frac1{25}<\cos\alpha<\frac3{\sqrt{73}},\qquad
\frac{1001}{2000}<C<\frac{37}{50},\qquad 0\le h<\frac{17}{50}.}
\tag{G2.10 -- checkpoint domain}
\]

For positive tilt it must also have \(C>2/3\) and a genuine first-wing
curvature excess; for negative tilt it must satisfy \(0<h<1-s\) and have
an unvisited central normal. Horizontal middle remains in the target.
These restrictions apply to the chosen scalar maximizer. They are not
individual angle restrictions on the two caps of an arbitrary original
sofa. The final argument below excludes this entire domain without
requiring the first wing or the whole companion wing to have unit
curvature.

### 3c. The final weighted payment closes every remaining angle

[MP](gate2-companion-moment-prefix-exclusion.md) improves the terminal
comparison: only the weighted excess before
\(\theta=\arcsin(C-T_L)\) needs to be paid. Its exact terminal margin
is greater than \(39\cos\alpha/4400\). If the weighted excess is
at most this amount, the strict outgoing exposure is longer than the
whole terminal facet, contradicting PS and TP.

[RX](gate2-reflected-tail-cot-one-eighth.md) proves that this excess is
zero throughout \(0<\cot\alpha\le1/8\). For the complementary range
\(1/8\le\cot\alpha<3/8\),
[AC](gate2-all-angle-reflected-cubic-exclusion.md) retains the terminal
facet as an exact reflected impulse and proves

\[
(v(t)-1)_+\le\frac{19}{25}
\bigl(t-(\pi/2-91/100)\bigr)_+.
\]

The weighted kernel and this envelope give

\[
\mathcal E_\theta<\frac{6517}{6400000}
<\frac{117}{110000}<\frac{39\cos\alpha}{4400}.
\]

The middle strict gap is \(3193/70400000\). The two angle ranges
overlap at cot(alpha)=1/8, AT includes cot(alpha)=3/8, and Gate 1
handles alpha=pi/2. All three middle-slope signs are included with
their actual terminal tail heights. Attainment therefore proves G2.4
for every cap. G2.5 and Gate 0 then give the sharp original-motion
area \(M\), with the genuine reference supplying equality.

## 4. Ordered proof tasks and acceptance checks

| Stage | Current result or required theorem | Status |
|---|---|---|
| A: domain reduction | PD proves height extrusion, middle-chord canonicalization, width coercivity, joint continuity and attained maximizer selection | Proved |
| B: used-support structure | PD locates the top for both middle-slope signs and saturates unused normals; PS keeps the terminal facet and excludes the companion atom | Proved |
| C: terminal source law | PS proves spatial and endpoint balances and regular-curvature bounds; TV proves both one-sided free-angle laws with their actual tie terms | Proved as stated; no stronger common-occupation law assumed |
| D: sharp global value | MP's terminal margin is paid by RX for cot(alpha)<=1/8 and AC for cot(alpha)>=1/8; no proper-angle above-reference maximizer remains | Proved |
| E: original-domain closure | G2C.23–24 join the two independent caps and angles; Gate 0 supplies the actual-body inequality and Romik the exact lower bound | Proved — Gate 2 PASS |

The new source and terminal proofs respect the following distinctions,
which are retained in the completed Stage D proof:

- Horizontal reflection is **not** a symmetry of a fixed partial objective:
  it changes which wall supplies the outgoing barrier. A negative middle
  tilt cannot be discarded by referring to Gate 1's reflection reduction.
- A terminal first-support facet can carry positive spatial exposure of the
  whole outgoing wall. Gate 1's no-atom conclusion on an open quarter cannot
  simply be reused at that terminal normal.
- Angle differentiation must retain ties between the terminal barrier and
  the historical niche. A derivative calculated only on strictly exposed
  terminal rays does not establish the derivative of the full maximum.
- Finite exposed-graph measures can have zero-height limits. Their
  projection identities do not automatically identify the actual positive
  continuum niche or its zero set.
- Any use of the ordinary one-turn bound needs a proved physical body or
  the existing appropriate connectedification theorem. A signed cap score
  alone is not ordinary area.

## 5. Rejected shortcuts and the original-domain link

**Universal integrated niche domination is false.** One cannot prove G2.4
by replacing \(q_{U,\alpha}\) with the full niche pointwise or in its
middle-half integral. For example, the downward polygon with vertices

\[
(-1,0),\ (-1,1/10),\ (1/10,1),\ (3,0),
\qquad \alpha=L-2\arctan(1/10)
\]

has \(I=[-1,3]\), \(J=[0,2]\), and
\(R_\alpha(x)=-20x/99\le0\) on \(J\). Its visited second support is at
most one at \(x=0\), but at the missing angle
\(t_*=L-\arctan(1/10)\) both supports equal \(\sqrt{101}/10>1\).
Thus \(q_{U,\alpha}\le n_U\) on \(J\), with strict inequality on an
interval, and \(\mathcal P_\alpha(U)>\mathcal P_L(U)\). Its exterior reward
is only \(1087/1595<41/50\), so this does not refute G2.4.

The existing [in-place completion obstruction](exact-in-place-completion-obstruction.md)
also rules out arbitrary zero-loss completion in the original incoming
orientation. The [terminal concavity counterexample](terminal-angle-concavity-obstruction.md)
rules out global concavity in the terminal angles, even when the full
niches vanish. The [reference outgoing-strip rigidity theorem](romik-terminal-angle-outgoing-strip-rigidity.md)
is a valid local estimate with explicit support restrictions; it cannot be
imposed on an arbitrary maximizer.

One global physical subcase is now closed: if a body has unit width in
**every** normal direction between its two outgoing normals through the
incoming normal, [SI3](strip-interval-completion.md) completes both turns
after reorientation, and Gate 1 gives \(|S|\le M\). Individual safe incoming
and outgoing directions do not supply that entire interval.

The roadmap allowed a return to the unchanged joint target PLAN.3 if
G2.4 were falsified by an exact continuous-angle cap score. That fallback
is not needed in the completed proof: MP, RX and AC prove G2.4 directly.
The rejected full-niche domination and arbitrary completion shortcuts
remain false; the closure does not restore or assume either one.

## 6. PASS criterion and reporting discipline

**The criterion is now met by G2C1–G2C2.** The final coverage audit is
accepted and the fixed Fraction checker passes 83 exact arithmetic
checks. The result is a written mathematical proof with its external
dependencies stated, not a new Lean formalization.

**Gate 2 passes only with a complete, auditable proof of PLAN.3 or an
equivalent sharp bound for every original admissible body, together with
the exact Romik lower bound.** An initial angle exclusion, a compactness
reduction, a terminal source identity, or a local reference estimate is not
a passed gate.

At each substantive checkpoint, identify the exact universal theorem
proved, any failed premise and its counterexample, and the remaining
global inequality. Publish sparse research commits marked `[skip ci]`.
External mathematical review and Lean verification remain separate from
the written-proof acceptance condition.
