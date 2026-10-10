# Gate 3 roadmap: equality, exact uniqueness and a reviewable manuscript

**Status: COMPLETED — Gate 3 PASS (written-proof and manuscript criteria).**
The mathematical items in this roadmap are proved and have passed
separate within-session equality reviews. The final assembled manuscript,
its extraction and dependency audit, and its compiler integrity check
are accepted. This roadmap began from the written Gate 0--2 closures at commit
177e1920a5fa11eb552ea810dfb649ce1fbd0a0d. Their sharp area value is
unchanged; Gate 3 adds classification of every equality cap, exact
uniqueness of the original compact body, and an integrated presentation
with the essential technical proofs. External referee acceptance and
Lean verification are not claimed.

The controlling requirements are in
[the execution plan](SHARP-OPTIMALITY-EXECUTION-PLAN.md). The three prior
gates remain prerequisites. The additional equality arguments are
[CE: full-turn cap classification](gate3-full-turn-cap-equality.md),
[TB: proper angles and compact-body rigidity](gate3-terminal-and-body-rigidity.md),
and [G3C: the assembled equality theorem](gate3-sharp-equality-and-uniqueness.md).
The [equality audit](gate3-equality-dependency-audit.md) checks their
quantifiers and exact-set conclusions; the
[manuscript dependency audit](gate3-manuscript-dependency-audit.md)
records the final review of the
[complete manuscript](GATE3-MANUSCRIPT.md).

## 1. Exact target and acceptance criteria

Let \(Y>0\) solve \(4Y^3+3Y-1=0\), put
\[
M=1+4Y^2+\arctan Y,
\]
and let \(\Sigma_*\) denote the genuine Romik ambidextrous body with its
actual convex hull \(K_*\).

**The proved theorem G3T.** If a compact connected body \(S\) admits the
two original unit-corridor passages from a common incoming orientation
and \(|S|=M\), then \(S\) is congruent to \(\Sigma_*\). Its actual
normalized hull is \(K_*\), and the correct-handed terminal magnitudes
supplied by the original-motion reduction are both \(\pi/2\).

This is exact equality of compact sets. A conclusion only about area
almost everywhere, an auxiliary cap, a chosen maximizer, a prescribed
contact chart, or an assumed symmetric motion does not meet this target.
The statement classifies shapes and necessary angular reach; it does
not claim uniqueness of the time parametrization or translation path.

Gate 3 passes only after:

1. every equality cap needed by an original equality body is classified;
2. the original hull and both independently supplied angles are recovered;
3. containment and regular closedness give literal body equality;
4. one manuscript includes the key equations and reduction proofs, with
   each retained external mathematical input identified;
5. separate within-session mathematical audits check the equality
   quantifiers, boundary cases, dependencies and assembled deduction.

The execution plan asks for a manuscript exposed for independent review.
It expressly makes no claim of externally accepted publication or Lean
verification. An external acceptance event is therefore not manufactured
as a gate condition or as a completed result.

## 2. The exact original-body deficit

For an actual body, let \(U,V\) be the upper and reflected-lower downward
caps of its actual common hull. They share projection \(I\) and middle
half \(J\). Put \(d_U=1-A_U\), \(d_V=1-A_V\), and abbreviate the two
actual partial barriers by \(N_U,N_V\), retaining each outgoing whole
wall. The canonical envelope \(E\) contains \(S\); connectedness makes
its projected fibers nonempty.

The Gate 2 spatial partition has the exact nonnegative remainder
\[
\begin{aligned}
D={}&\int_J\bigl[(d_V-N_U)_++(d_U-N_V)_+\bigr]\,dx\\
&+\int_{I\setminus J}
\bigl[(N_U-d_V)_++(N_V-d_U)_+\bigr]\,dx.
\end{aligned}
\tag{G3R.1}
\]
Indeed, subtract the exact fiber
\[
\ell=1-\max(d_V,N_U)-\max(d_U,N_V)
\]
from its middle and exterior upper bounds, using
\(\max(a,b)-a=(b-a)_+\). The constant integrals cancel because
\(|J|=|I\setminus J|\). Consequently
\[
\boxed{
M-|S|=
\left(\frac M2-\mathcal P_\alpha(U)\right)
+\left(\frac M2-\mathcal P_\gamma(V)\right)
+D+|E\setminus S|.
}
\tag{G3R.2}
\]
Every term on the right is nonnegative by Gate 2. Thus any area-\(M\)
body has two ORIGINAL cap scores exactly \(M/2\), zero partition
remainder, and zero area omitted from its canonical envelope. This
identifies the original equality data before any cap replacement.
[ED.1--5](gate3-equality-dependency-audit.md) proves the identity in
the actual motion domain, and [G3C.8--10](gate3-sharp-equality-and-uniqueness.md)
uses it to recover both original caps. No generic reversibility of the
canonical reductions is assumed.

## 3. Universal scalar equality rigidity is proved

For every nonempty compact downward cap of height at most one and
every allowed angle \(\alpha\in[\pi/4,\pi/2]\), the classification is
\[
\boxed{
\mathcal P_\alpha(U)=M/2
\quad\Longrightarrow\quad
\alpha=\pi/2,\quad U=U_*+(a,0)
}
\tag{G3R.3}
\]
where \(U_*\) is the centered reference upper cap. The reference
attains the bound, so the converse also holds. This is
[G3C1](gate3-sharp-equality-and-uniqueness.md); the following three
arguments establish the previously separate obligations.

### 3.1 Every prescribed canonical maximizer

All tilted and discarded-width branches of Gate 1 end in strict value
bounds or contradictions valid at equality. Their source laws apply to
every prescribed canonical global maximizer: the finite approximation
is selected with a vanishing support-distance penalty targeted to that
particular cap. The estimate
\[
D_n(U_n,U)^2\le e_n/\eta_n\longrightarrow0
\]
forces its Hausdorff limit to be the prescribed \(U\). It does not
select a different regular cap and then assert a property of the
original one.

The remaining horizontal cap attains equality in the signed-roof
comparison and the strict \(H^1\) calibration. The real periodic
extension of its upper support pair has the required matching endpoint
values and identical reflected halves. The calibration applies on that
entire \(H^1\) domain; convexity of an artificial lower half is not
required. The stationary-width classification and the removal of the
horizontal translation mode identify the centered reference support.
Continuity then gives pointwise support equality.

[CE1](gate3-full-turn-cap-equality.md) proves this universal canonical
classification. The [equality audit](gate3-equality-dependency-audit.md)
and the independent terminal-rigidity review accepted the prescribed-cap
quantifier, strict width and tilt exclusions, endpoint gluing, and
reference normalization.

### 3.2 Exact reversal of the middle chord and height restoration

Apply the middle-chord cut and height restoration to an arbitrary
full-turn equality cap. The universal value bound forces equality at
each comparison. After translating the resulting canonical cap to
\(U_*\), write \(V+[0,\varepsilon]e_y=U_*\). The proved reversal is
\[
\mathcal P(U_*)-\mathcal P(V)
=\int_J(\varepsilon-n_*)_+\,dx.
\tag{G3R.4}
\]
Here \(\mathcal P=\mathcal P_{\pi/2}\) is the full-turn score.
Indeed every upward support changes by the vertical translation of
its normal component, giving the exact positive-niche identity
\(n_V=(n_*-\varepsilon)_+\). The exterior roof gain and the
middle-window niche gain have the same integration length. This
derivation retains the floor even when a raw niche height is negative.

The reference niche is continuous and vanishes at the middle endpoints.
If \(\varepsilon>0\), the right side is strictly positive. Equality
therefore forces \(\varepsilon=0\). The chord cap already has roof
one on \(J\); the original cap contains it and has height at most one,
so its middle roof is also one. Outside \(J\), the chord cut preserved
the roof pointwise. Thus the original cap itself is the reference cap,
including its compact boundary. [CE2--CE3](gate3-full-turn-cap-equality.md)
and the independent inverse audit prove this for subunit, nonsmooth,
and initially nonaffine caps as well.

### 3.3 Strictness at every proper terminal angle

Gate 2 selected a largest-angle maximizer to prove its terminal facet
bound in the value proof. [TB1--TB2](gate3-terminal-and-body-rigidity.md)
supplies the additional argument for an arbitrary individual equality
pair. If its terminal facet exceeds the allowed length, a local
comparison extends the angle while preserving that same cap and its
entire barrier on \(J\). The proof separates the region where the new
first walls decrease, a compact interval strictly masked by old walls,
and the region where all new walls are nonpositive.

The old terminal facet remains a positive charged exterior facet and
becomes an interior visited normal at the enlarged angle. The same cap
is still canonical and globally maximizing. The prescribed-cap source
theorem forbids such an interior atom. This proves the terminal facet
bound for every proper-angle equality pair without a largest-angle
choice.

The weighted companion-moment argument and its two overlapping
reflected-curvature estimates then give strict terminal exposure
exceeding the available source mass. These estimates cover all residual
middle-slope signs and the complete remaining angle interval. The
negative-tilt completed branch is treated separately: its same-cap
comparison would give full-turn equality, whereas CE forces a horizontal
reference middle. Thus every proper-angle scalar value is strictly less
than \(M/2\). The angle-preserving canonical comparisons exclude proper
equality for every original cap, without needing to reverse those
partial-turn comparisons.

## 4. The original hull, angles and compact body are recovered

G3R.2 and G3R.3 identify both original caps. Their shared
projection fixes the same horizontal translation. Their upper and
lower roofs then determine the actual hull \(K_*\), and both
independently supplied canonical terminal magnitudes equal \(\pi/2\).
The argument retains the original hull and both original outgoing
constraints throughout; no symmetry or agreement of the two motions is
assumed.

There is also an independent geometric angle check. With reference
half-width \(m_*=1/(3\sin(\arctan Y))>1\), the actual hull contains
\([-m_*/2,m_*/2]\times[0,1]\). For a unit normal \((c,s)\) with
\(c\ne0\),
\[
\operatorname{width}_{K_*}(c,s)
\ge m_*|c|+|s|>|c|+|s|\ge1.
\]
Its only unit-width strip normal is vertical, up to sign. Convex hull
preserves widths, so a body with this actual hull cannot fit a proper
conventional outgoing unit strip.

The canonical envelope of \(K_*\) at the complete angles is
\(\Sigma_*\). Its direct construction proves
\[
\Sigma_*=\overline{\operatorname{int}\Sigma_*}.
\]
Its central fibers lie between continuous strictly separated niche
graphs, while its exterior flanks are unchanged convex-hull fibers;
the extreme points are also limits of interior points.
If the original compact \(S\subseteq\Sigma_*\) has the same area, any
point in \(\Sigma_*\setminus S\) has a neighborhood disjoint from \(S\).
Regular closedness then supplies an open subset of positive area in
that neighborhood, a contradiction. This proves literal set equality.
[TB3--TB4](gate3-terminal-and-body-rigidity.md) gives the width and
compact-set arguments, and [G3C2](gate3-sharp-equality-and-uniqueness.md)
assembles them with the original-body deficit.

The equality audit retains exact counterexamples to generic
canonicalization injectivity and to recovery of compact sets from equal
area alone. Here the identified reference profile reverses the cap
operations, and original-hull retention plus the regular-closed envelope
excludes both appendages and zero-area deletions.

## 5. The assembled manuscript and accepted final review

The [assembled manuscript](GATE3-MANUSCRIPT.md) contains 52 proof
sections, 83,574 words, and 291 internal links. Its five integrated
chapters present
the theorem and direct reference construction, original-motion
reduction, full-turn value and equality proof, partial-turn value and
strict-angle proof, and original-body uniqueness. Its 47 technical
sections include the essential source, calibration, geometric, and
rational-certificate proofs. These counts describe the current build;
they are not acceptance criteria.

The [compiler](computer-assisted/build_gate3_manuscript.py) and
[source manifest](gate3-manuscript-manifest.json) record the selected
proof sections, source hashes, extraction boundaries, and editorial
changes. The direct reference construction establishes actual
feasibility, the exact area, actual-hull retention, and regular
closedness, so the proof does not depend on an unproved realization or
uniqueness assertion from the older reference presentation.

The ordinary one-turn area theorem and the retained exact Gerver
enclosure remain explicit external inputs, with their hypotheses and
precise role. Each application first establishes a genuinely feasible
ordinary survivor, and uses the external area bound only for a strict
contradiction. No external equality theorem is imported. The manuscript
distinguishes the written continuum proofs from the fixed rational
arithmetic checks and the integrity checks performed by its compiler.

Separate mathematical reviews have accepted the equality arguments and
integrated front chapters. Their recorded scope includes:

- universal maximizer quantifiers and the target of finite-source limits;
- strictness and reversibility at every equality-producing reduction;
- all proper-angle, slope-sign and facet-atom boundaries;
- actual hull retention, independent angles and regular closedness;
- the mathematical dependency order and stated external inputs.

The [equality audit](gate3-equality-dependency-audit.md) records the
accepted CE, TB, and original-body deductions. The
[manuscript dependency audit](gate3-manuscript-dependency-audit.md)
accepts the final assembled extraction, including the specialized
domestic premises, their definitions and hypotheses, and the historical
attributions distinguished from proof dependencies. The final compiler
check confirms the section inventory, source extraction records, and
internal links. The accepted manuscript has SHA-256
`0d1b8a41f3684c9eade825678bca13aaef3350a50799302f2aef8fa604c9015f`.

## 6. Completion evidence and final verdict

| Work item | Status | Completion evidence |
|---|---|---|
| Exact deficit and original equality reduction | PROVED; accepted | G3R.1--2, [ED.1--5](gate3-equality-dependency-audit.md), and G3C.8--10 retain both original cap deficits. |
| Full-turn cap equality and reversal | PROVED; accepted | [CE1--CE4](gate3-full-turn-cap-equality.md): every prescribed canonical maximizer, strict calibration, exact extrusion identity, and pointwise inverse middle-chord reduction. |
| Proper-angle equality exclusion | PROVED; accepted | [TB1--TB2](gate3-terminal-and-body-rigidity.md): the same-cap interior-atom contradiction, completed negative branch, and strict source-exposure contradiction. |
| Actual hull and body uniqueness | PROVED; accepted | [G3C2](gate3-sharp-equality-and-uniqueness.md) and TB3--TB4: common-projection alignment, actual hull, both angles, and regular-closed recovery. |
| Self-contained manuscript | ACCEPTED | [One assembled document](GATE3-MANUSCRIPT.md), with 52 proof sections, integrated front chapters, essential technical proofs, and explicit external inputs; final extraction and compiler review accepted. |
| Final equality/dependency audit | ACCEPTED | [Equality audit](gate3-equality-dependency-audit.md) and [final manuscript dependency and integrity audit](gate3-manuscript-dependency-audit.md) both accepted. |

The sharp area bound has not improved: it remains the exact \(M\)
already proved by Gate 2. The completed mathematical argument adds all
equality caps, strict proper-angle values, actual-hull rigidity, and
exact uniqueness of the compact maximizing body. Final Gate 3 status
is PASS: the written equality proof, exact-body recovery, complete
manuscript, and separate within-session audits meet all acceptance
criteria above. No mathematical or manuscript task remains pending in
this roadmap.
