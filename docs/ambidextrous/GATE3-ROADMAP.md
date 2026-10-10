# Gate 3 roadmap: equality, exact uniqueness and a reviewable manuscript

**Status: ACTIVE.** This roadmap starts from the written Gate 0--2
closures at commit 177e1920a5fa11eb552ea810dfb649ce1fbd0a0d. The sharp
area value is already established in that proof chain. Gate 3 concerns
every equality case, the actual compact body, and a self-contained
presentation for independent mathematical review. External referee
acceptance and Lean verification are not claimed.

The controlling requirements are in
[the execution plan](SHARP-OPTIMALITY-EXECUTION-PLAN.md). The three prior
gates remain prerequisites; their value proofs are not silently promoted
to equality classifications.

## 1. Exact target and acceptance criteria

Let \(Y>0\) solve \(4Y^3+3Y-1=0\), put
\[
M=1+4Y^2+\arctan Y,
\]
and let \(\Sigma_*\) denote the genuine Romik ambidextrous body with its
actual convex hull \(K_*\).

**The target theorem G3T.** If a compact connected body \(S\) admits the
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

## 2. A global equality identity already follows from Gate 2

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
reduces the active equality problem to genuine equality data without
assuming any of the canonical reductions are reversible.

## 3. One active global lemma: scalar equality rigidity

The sufficient scalar target is
\[
\boxed{
\mathcal P_\alpha(U)=M/2
\quad\Longrightarrow\quad
\alpha=\pi/2,\quad U=U_*+(a,0)
}
\tag{G3R.3 -- OPEN}
\]
for every compact downward cap of height at most one and every allowed
angle. \(U_*\) is the reference upper cap.

### 3.1 Full-turn canonical equality

All tilted and discarded-width branches of Gate 1 end in strict value
bounds or contradictions. Check that their source laws apply to every
prescribed canonical global maximizer, not just one conveniently
selected limit. The remaining horizontal branch must give equality in
the signed-roof calibration. Audit the strict fixed-width concavity and
the stationary-width classification to recover the unique reference
support.

### 3.2 Undo the cap reductions

Apply the middle-chord cut and height restoration to an arbitrary
full-turn equality cap. Once the resulting canonical cap is \(U_*\),
write \(V+[0,\varepsilon]e_y=U_*\). The proposed exact reversal is
\[
\mathcal P(U_*)-\mathcal P(V)
=\int_J(\varepsilon-n_*)_+\,dx.
\tag{G3R.4}
\]
The reference niche is continuous and vanishes at the middle endpoints.
If \(\varepsilon>0\), the right side is strictly positive. Equality
would therefore force \(\varepsilon=0\); the original central roof
cannot exceed the height-one reference plateau. Verify every support,
projection and signed/positive-niche convention in this argument.

### 3.3 Proper terminal angles

Gate 2 selected a largest-angle maximizer to prove its terminal facet
bound. That selection proves the value theorem, but by itself says
nothing about another equality maximizer at a smaller angle. This is
the specific quantifier that needs a new argument.

The proposed repair is local: if the terminal facet mass exceeds the
allowance, the existing terminal comparison extends the angle while
preserving the same cap and score. The old terminal facet would then be
an interior charged curvature atom, contrary to the interior regularity
law for that new maximizing pair. Verify that the facet remains charged
and that all canonical and stationarity hypotheses survive.

With the resulting terminal mass bound for every maximizer, the strict
Gate 2 weighted-exposure contradiction should exclude the remaining
proper-angle cases. The negative-tilt completed branch must be treated
separately using the full-turn equality classification, rather than
discarded merely because its value is at most \(M/2\).

If this stronger scalar equality lemma fails, record an exact
counterexample and retain G3R.2 as the route to a compatible two-cap
equality theorem. No change of mechanism is justified solely by lack
of progress.

## 4. Recover the original hull, angles and compact body

Once G3R.3 holds, G3R.2 identifies both original caps. Their shared
projection fixes the same horizontal translation. Their upper and
lower roofs then determine the actual hull \(K_*\).

Independently check the reference hull's width in each proper outgoing
normal. This supplies a geometric angle-rigidity check and prevents an
auxiliary cap identity from being mistaken for an original-motion
conclusion.

The canonical envelope of \(K_*\) at the complete angles is
\(\Sigma_*\). Verify explicitly that
\[
\Sigma_*=\overline{\operatorname{int}\Sigma_*}.
\]
If the original compact \(S\subseteq\Sigma_*\) has the same area, any
point in \(\Sigma_*\setminus S\) has a neighborhood disjoint from \(S\).
Regular closedness then supplies an open subset of positive area in
that neighborhood, a contradiction. This is the required upgrade from
area equality to literal set equality.

Regular closedness cannot be omitted: a disk and that disk with an
attached zero-area segment are both compact and connected and have the
same area. Hull retention and the identified reference envelope must
rule out this type of appendage.

## 5. Manuscript and audit

Compile a single manuscript with a complete theorem statement, the
candidate construction, original-motion reduction, scalar domain and
source arguments, full and partial value proofs, and equality recovery.
Include the mathematical proofs of indispensable intermediate results;
a list of repository links is not a self-contained manuscript.

Keep the ordinary one-turn area theorem and the exact Gerver enclosure
as explicit external inputs, with their hypotheses and precise role.
Distinguish the written continuum arguments from the fixed rational
arithmetic checkers. Preserve the known counterexamples to discarded
shortcuts wherever needed to explain a dependency boundary.

Separate audits must check:

- universal maximizer quantifiers and the target of finite-source limits;
- strictness and reversibility at every equality-producing reduction;
- all proper-angle, slope-sign and facet-atom boundaries;
- actual hull retention, independent angles and regular closedness;
- manuscript dependency completeness and stated external inputs.

## 6. Work sequence and status

| Work item | Initial status | Completion evidence |
|---|---|---|
| Exact deficit and original equality reduction | PROVED | G3R.1--2 above |
| Full-turn cap equality and reversal | ACTIVE | Complete theorem and independent audit required |
| Proper-angle equality exclusion | ACTIVE | Terminal-atom argument and negative branch audit required |
| Actual hull and body uniqueness | PENDING | Apply classified original caps and regular-closedness proof |
| Self-contained manuscript | PENDING | One complete document with essential proofs and dependencies |
| Final equality/dependency audit | PENDING | Separate accepted reviews of the assembled claim |

The sharp area bound has not improved: it remains the exact \(M\)
already proved by Gate 2. Gate 3 will strengthen the equality and
uniqueness conclusions and make the full argument independently
reviewable. Until all items above are complete, Gate 3 remains ACTIVE.
