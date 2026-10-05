# 34. Current proof status after Notes 25–33

**The unrestricted optimality and uniqueness problem is not closed.** This pass proves global attainment, strengthens the conditional geometric theorem to weak curvature bounds, supplies arbitrary-maximizer selection, constructs new high-area counterexamples to a proposed reduction, and proves a motion-preserving regularization with a perimeter condition for all maximizers.

This file is the current ledger. [Note 24](24-current-proof-ledger.md) and [Note 7](07-proof-ledger.md) are earlier snapshots and remain in the repository as a chronological record. All results here are written proofs with self-review, not independent refereeing or Lean verification. No novelty claim is made.

## 34.1 Strongest area-and-uniqueness theorem now established

[Theorem 65](31-closed-curvature-class-theorem.md) applies to a compact connected S with common convex hull K, normalized to vertical span one. It assumes:

1. both canonical full conventional quarter-turn motions are feasible;
2. the curvature measure sigma_K=h_K+h_K'' is dominated by dtheta on each open coordinate quarter;
3. for f(t)=h(t), g(t)=h(t+pi/2), both h_K and its reflection satisfy

\[
f'-g+1\leq g'+f-1.
\]

Then

\[
|S|\leq M=1+4Y^2+\arctan Y,
\qquad4Y^3+3Y-1=0,\quad Y>0,
\]

with equality exactly for bodies congruent to Romik's candidate.

The curvature bound is now **non-strict**. It supplies the needed Sobolev regularity itself. Contact zeros may have intervals of degeneracy; atoms at axis normals are not excluded in advance. Symmetry, face alignment, fixed switches, ordinary velocity monotonicity, and finite analytic decompositions are not hypotheses.

The proof extends the sharp adaptive functional by continuity in function space, and proves the degenerate niche geometry directly. It does not presume that interpolated hulls are feasible.

## 34.2 New unrestricted results

### Attainment

[Theorem 55](25-compactness-and-attainment.md) proves that the unrestricted posed problem has an attained finite maximum V. A competitive body has a representative in

\[
[-(1+\sqrt2),1+\sqrt2]\times[0,1].
\]

A canonical diagonal corner above the incoming strip would force a connected body into one arm and bound its area by sqrt(2). Otherwise the two outer diagonal walls give the displayed box. Compactness of bodies and endpoint angles, closed canonical feasibility, and upper semicontinuity of area then yield a maximizer.

This removes existence as a missing premise. It does not identify the maximizing body or assume V=M.

### Endpoint coupling and a full-turn criterion

[Note 26](26-coupled-endpoint-angle-bounds.md) proves that any body of area at least M has

\[
\alpha+\gamma\geq\pi-\arcsin(1/M),
\]

and gives an exact stronger three-strip formula when both endpoints are partial. The strip estimate becomes unbounded near full turns and does not prove full-angle completion.

[Proposition 61](29-a-geometric-full-turn-gate.md) proves full turns whenever the normalized hull contains an axis-parallel unit square. The candidate has a longer unit-height rectangle, and nearby hulls have quantitatively small endpoint deficits. The square property has not been proved for every maximizer.

### Boundary-measure localization

[Theorem 59](27-hidden-boundary-is-atomic.md) proves that boundary strictly hidden by a forbidden sweep lies only in interiors of exposed edges. In normal direction the difference between full and retained surface-area measures is a countable sum of edge atoms. Their diffuse parts agree.

This refines the obstruction in Note 21. It does not remove coincident-contact terms or prove that a proposed support variation is admissible.

### Selecting every maximizing hull

[Theorem 67](32-selecting-every-maximizing-hull.md) constructs penalized finite-angle polygonal optimizers converging to any prescribed maximizing hull. Finite-angle upper values decrease to V by compactness. A vanishing sampled-support-distance penalty selects the desired hull and gives an exact approximate variational inequality.

Thus a future structural proof need not silently replace an arbitrary maximizer by a preferred one. The required visible-side/contact calculation and its error control are still missing.

### Feasible regularization and finite perimeter

[Theorem 68](33-rounding-and-perimeter.md) proves that

\[
T_t(S)=\frac{S+tB_2}{1+2t}
\]

preserves both complete motions. It gives regular-closed approximants with connected interior; a strict-clearance version yields genuinely feasible connected polygonal approximants.

For every global maximizer, maximality gives

\[
|S+tB_2|\leq(1+2t)^2|S|,
\qquad\operatorname{Per}(S)\leq4|S|.
\]

The latter is distributional finite perimeter and does not assert smoothness of the topological boundary. At the explicit candidate the perimeter inequality is strict, so it is a necessary condition rather than an equality calibration identifying the optimizer.

## 34.3 The new negative finding

[Theorem 60](28-high-area-curvature-counterexamples.md) constructs feasible full-turn bodies S_n with common hull supports

\[
h_n=h_*+\frac{1}{2n^2}\eta(t)\cos(n(t-t_0))
\]

on one protected quarter interval, extended by reflection. The perturbations vanish near all face normals and contact switches. For large n:

- the hull is convex, reflection symmetric, and has the same aligned exposed faces as the candidate;
- the contact inequality p<q persists;
- the complete two-turn motions are feasible and the hull is retained exactly;
- its curvature density exceeds one on intervals of positive length;
- |S_n| tends to M.

The same central rectangle forces full endpoints in these coordinates. Thus no fixed area threshold A_0<M, even combined with the other listed favorable properties, implies the curvature cap.

The construction does **not** establish whether |S_n| lies above or below M. It is not presented as a counterexample to candidate optimality. It disproves a tempting curvature-reduction statement and explains why actual maximality or a proved improvement operation is necessary.

Earlier negative findings, including the feasible counterexample to the frozen-switch majorant in Note 19, remain valid and recorded in Note 24.

## 34.4 What the weak-bound extension actually repairs

Notes 30–31 do not use a hypothetical feasible interpolation. They establish:

```text
weak curvature and contact inequalities
  -> ordered sign intervals, possibly degenerate
  -> monotone contact graphs with constant plateaus identified
  -> a continuous nonnegative niche roof
  -> positivity of that roof confined over the opposite exposed face
     by extreme-point retention
  -> zero positive clipping loss
  -> actual area equals the adaptive functional
  -> sharp bound and exact body equality recovery
```

The special endpoint case p(0)=0 is handled separately. It forces an entire quarter's curvature to equal one, fixes the rightmost exposed point at height zero, and makes the opposite bottom face extend across the relevant roof interval. No strict interval-overlap assumption is smuggled into this case.

## 34.5 Current noncircular route and missing statement

The proved chain is now:

```text
unrestricted problem
  -> global maximum exists
  -> any prescribed maximizing hull has finite-angle penalized approximants
  -> [MISSING: admissible variations and a structural theorem]
  -> full turns + curvature-measure domination + contact inequalities
  -> Theorem 65
  -> optimality and, if the structural theorem covers every maximizer,
     exact uniqueness
```

The missing structural step still has concrete content:

- force full-quarter endpoints, or prove a covering comparison for partial endpoints;
- derive the curvature-measure cap, including exclusion/control of hidden edge atoms;
- derive the two contact inequalities;
- justify the variations under connectedness, coincident contacts, and the endpoint constraints, with errors that vanish in the selection limit.

A proof for just one selected maximizer would establish V=M, but not uniqueness of all other maximizers. The arbitrary-hull selection theorem is designed to avoid that logical gap. A purely area-dominating replacement likewise needs an equality-transfer argument to prove exact uniqueness.

No claim is made that these remaining statements follow from the newly proved perimeter bound. Finite perimeter is weaker than support-curvature domination; rounding preserves hull edge atoms rather than removing them.

## 34.6 Self-review checks in this pass

**Compactness:** the box controls the whole connected set, including zero-area appendages. The corner-height argument uses a strict inequality only where a vertical line must be entirely forbidden. Feasibility is passed to the limit in canonical support variables, not arbitrary time parametrizations. The area semicontinuity direction is the upper one.

**Endpoint bound:** all three strip directions are recorded, central alignment is used only for the convex strip relaxation, and the positive triangle correction is retained. The limiting full-angle case is not assigned a finite strip bound.

**Curvature counterexamples:** convexity is checked through a strictly positive curvature margin on the perturbed interval. Motion feasibility uses uniform corner and baseline-intercept margins, not the failed curvature condition. The area argument proves convergence only, without claiming a sign for M minus |S_n|.

**Weak profiles:** plateau parameters do not produce vertical graph segments because constant abscissa forces a constant contact point. The no-clipping claim is an area statement; zero-height baseline pieces outside the hull are harmless. Reflection endpoint traces are used with the correct maximum/minimum heights of the rightmost face.

**Selection:** the penalty is on sampled hull supports, not on an unproved differentiable body distance. Saturating a connected finite-envelope component preserves all recorded support values. Dense auxiliary normals control the unsampled hull. No convergence rate or effective computation of V is asserted.

**Rounding:** the same coordinate translation works for both fixed hallways and for both endpoint arms. Disk addition is checked pointwise against the inner disjunction. Finite perimeter is proved using Lipschitz distance cutoffs, rather than assuming the maximizer already has a smooth boundary.

## 34.7 Execution and provenance

All changes are Markdown under docs/ambidextrous. No CI was requested or used; no Lean/Lake compilation, dependency installation, numerical experiment, CAS calculation, or manuscript build was performed. Every commit carries `[skip ci]`. The existing manuscript, Lean sources, dependencies, and workflows remain unchanged.

The work is a pen-and-paper continuation of the earlier notes, motivated by Romik's explicit construction, Baek's sharp-majorant organization, and the repository's uniqueness argument. It is not a comprehensive literature or priority review. The PR remains draft because the unrestricted structural proof and independent review are unfinished.
