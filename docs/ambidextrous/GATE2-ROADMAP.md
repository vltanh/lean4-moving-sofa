# Gate 2 roadmap: partial turns with the actual outgoing strips

**October 10, 2026. Status: ACTIVE, UNPROVED.** Gate 0's original-motion
bridge and Gate 1's sharp full-turn value are completed written arguments.
This roadmap fixes the next global theorem, its exact implication for the
original problem, and the proof obligations that cannot be imported from
Gate 1. It does not assert unrestricted optimality.

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

## 2. The one active sufficient theorem

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

**Active global lemma, not yet proved:**

\[
\boxed{\mathcal P_\alpha(U)\le M/2
\quad\text{for every such cap and every }\alpha\in[\pi/4,L].}
\tag{G2.4 -- OPEN}
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

## 3. A whole terminal-angle interval is already closed

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

## 4. Ordered proof tasks and acceptance checks

| Stage | Required result | What it resolves |
|---|---|---|
| A: domain reduction | Prove height extrusion, middle-chord canonicalization, width coercivity and joint continuity in \((U,\alpha)\); select an attained canonical maximizer | Arbitrary heights, nonsmooth caps and variable angles; no finite facet cutoff |
| B: used-support structure | Locate the top relative to \(J\), retaining both signs of the middle slope; saturate unused outer normals while preserving all used supports | Removes freely improvable outer geometry, without assuming a reference contact chart |
| C: terminal source law | Rederive the spatial facet, endpoint and source balances for G2.2, including a possible atom at \(\mu_\alpha\), its exposed graph positions and free-angle variations | The genuine new boundary condition absent from Gate 1 |
| D: sharp global value | Exclude or sharply bound every attained proper-partial maximizer with \(\arctan(5/4)<\alpha<L\), for both slope signs and every allowed width | The unresolved substance of G2.4 |
| E: original-domain closure | Join all angle boundaries, invoke G2.5 for independent caps and angles, use the Gate 0 original-motion bridge, and check exact reference equality | Passes Gate 2 only when all preceding universal claims are proved |

Stages A and B use elementary domain transformations where valid. Stages C
and D require new proofs. In particular:

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

## 5. Routes already ruled out, and the permitted fallback

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

If G2.4 is falsified, exhibit an exact cap and its true continuous-angle
score, then return to the unchanged joint target PLAN.3. The replacement
must retain the common hull, both independent strips and the max/min
clipping terms. A maximizer-only paid completion is allowed only with a
proved global payment; no new candidate-local program substitutes for
this obligation.

## 6. PASS criterion and reporting discipline

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
