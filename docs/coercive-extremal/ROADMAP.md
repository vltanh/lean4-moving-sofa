# Roadmap: coercive extremal framework

This branch is a **stacked planning/refactor branch** based on
\`research/quantitative-stability\`. It is intended to reorganize the new
quantitative machinery into an independent extremal route while preserving:

1. the faithful formalization of Baek's paper in \`MovingSofaOptimality\`;
2. the existing main uniqueness proof in \`MovingSofaUniqueness.Main\`;
3. the bridge and Challenge interface used to transport the result to
   formal-conjectures.

The goal is not to replace any of those assets. The goal is to make the new
coercive framework prove optimality and uniqueness by a route that is
machine-auditable as independent of both Baek's final optimality theorem and
the old CapKernel equality proof.

No Lean, Lake, CI, remote build, or TeX compilation is to be run while this
roadmap is being implemented unless that policy is explicitly changed. Research
commits should continue to use \`[skip ci]\`.

## Target mathematical picture

Let \(M=|G|\). The new framework should expose one right-angle extremal theorem
whose consequences separate according to the size of the deficit:

\[
  \mathcal A(K)\le Q(\xi_K)\le M,
\]

together with a coercive estimate of the form

\[
  d_H^{\mathrm{Euc}}(K,K_G+(s,0))
    \le C\sqrt{M-Q(\xi_K)}.
\]

Then:

- **sign of the deficit** gives the right-angle upper bound;
- **zero deficit** gives rigidity and uniqueness of the right-angle maximizer;
- **small deficit** gives cap stability.

The global maximizing-cap machinery transports the first two consequences to
arbitrary moving sofas. The additional local/compactness geometry transports
the third consequence to unrestricted stability.

The intended source-level zero-deficit route is

\[
\begin{aligned}
K\text{ maximizes } \mathcal A
&\Longrightarrow |G|\le \mathcal A(K)\\
&\Longrightarrow K\in\mathcal K^i\\
&\Longrightarrow \mathcal A(K)\le Q(\xi_K)\le Q(\xi_G)=|G|\\
&\Longrightarrow M-Q(\xi_K)=0\\
&\Longrightarrow E_{\rm cap}=0\\
&\Longrightarrow d_H^{\mathrm{Euc}}(K,K_G+(s,0))=0\\
&\Longrightarrow K=K_G+(s,0).
\end{aligned}
\]

The classification step must use the quantitative deficit/coercivity machinery,
not \`ki_maximizer_equality_conditions\`, \`capKernel_of_triple_midpoint\`, or
\`CapKernel.eq_horizontal_translation\`.

## What stays unchanged

### Baek track

\`MovingSofaOptimality\` remains the faithful formalization of Baek's paper,
including \`MovingSofaOptimality.theorem1_1_1\`. The new route does not replace
or rewrite it.

### Main uniqueness track

\`MovingSofaUniqueness.Main\` remains the natural uniqueness proof used by the
current manuscript. It may continue to use Baek's optimality theorem and the
existing equality/CapKernel argument.

### Bridge and Challenge

\`MovingSofaBridge\`, \`Challenge.lean\`, and the formal-conjectures statements
remain an external interface. Internal proof routes may change without changing
that interface.

## Phase 1 — dependency refactor

The first implementation phase is source organization, not new mathematics.

### 1.1 Extract neutral Mamikon square-gap algebra

The following declarations currently live in \`MovingSofaUniqueness.Rigidity\`
although they are not uniqueness-specific:

- \`halfSquareIntegral\`;
- \`integrable_sq_sub\`;
- \`halfSquareIntegral_combo_gap\`;
- \`integral_sq_sub_eq_zero_iff\`;
- the associated equality lemmas used by Mamikon's formula.

Move or re-export them from a neutral module, tentatively

\`MovingSofaUniqueness/MamikonGap.lean\`.

Both the old rigidity proof and the quantitative stability proof should import
that module. The coercive route should not need to import the old CapKernel
classification just to obtain these analytic lemmas.

### 1.2 Split maximizer geometry from maximizer rigidity

The current \`MovingSofaUniqueness.Maximizers\` mixes geometry/value results
with the old rigidity classification. Split the dependency surface so the
coercive route can use:

- \`exists_maximizing_cap\`;
- \`gerver_le_of_maximizes\`;
- \`isKi_of_maximizes\`;
- \`right_angle_maximizer_value\`;
- \`maximizing_monotone_has_right_angle\`;

without importing the old equality route.

Tentative module:

\`MovingSofaUniqueness/MaximizerGeometry.lean\`.

The existing CapKernel-based classification may remain in a separate module or
be re-exported for compatibility.

### 1.3 Extract horizontal-translation geometry

Move/re-export the elementary facts used by both routes:

- support of a horizontal translate;
- cap equality from upper support;
- niche translation;
- sofa translation.

Tentative module:

\`MovingSofaUniqueness/HorizontalTranslation.lean\`.

This keeps the coercive route from importing unrelated equality machinery.

## Phase 2 — coercive right-angle rigidity

Add a module tentatively named

\`MovingSofaUniqueness/CoerciveRigidity.lean\`.

Its headline theorem should classify a maximizing right-angle cap using
\`MovingSofaStability.ki_cap_distance_bound\` (or a lower-level equivalent):

\`\`\`lean
theorem right_angle_maximizer_eq_gerver_coercive
    {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} (hK : IsCap K (π / 2))
    (hmax : ∀ C, IsCap C (π / 2) →
      sofaArea (π / 2) C ≤ sofaArea (π / 2) K) :
    ∃ a : ℝ,
      K = Rigid.translate (a, 0) '' P.cap ∧
      K \ niche K (π / 2) =
        Rigid.translate (a, 0) '' gerverSofa P
\`\`\`

Proof skeleton:

1. \`isKi_of_maximizes\`;
2. \`right_angle_maximizer_value\`;
3. apply the Ki cap-distance theorem;
4. rewrite the area deficit to zero;
5. conclude \`EuclideanClose 0 ...\`;
6. use \`EuclideanClose.eq_of_zero\`;
7. translate the niche/sofa.

There should be no midpoint-equality or CapKernel call in this proof.

## Phase 3 — coercive extremal route

Add a dedicated route, tentatively

\`MovingSofaUniqueness/CoerciveAlternative.lean\`.

It should reprove the same public mathematical conclusions as the current
maximizer route while replacing only the right-angle classification theorem.

Target entry points:

- right-angle cap upper bound and equality characterization;
- \`gerver_sofa_optimal\`;
- cap area bound for every angle;
- equality/congruence theorem for maximal sofas;
- \`gerver_sofa_optimal_and_unique\`;
- maximal-sofa iff Gerver-copy theorem.

The global steps may reuse:

- existence of maximizing caps;
- maximality-derived pinned/curvature bounds;
- remaining-angle turn;
- regular-closed recovery.

This route must not use \`MovingSofaUniqueness.Main\` or the old CapKernel
classification.

## Phase 4 — stability dependency cleanup

The unrestricted stability theorem currently uses the existing uniqueness
theorem in the compactness/local-entry step. After the coercive extremal route
exists, decide whether to switch qualitative entry to the coercive uniqueness
theorem.

This is desirable because it gives a single dependency hierarchy:

\[
\text{maximizer geometry}
\to\text{coercive right-angle theorem}
\to\text{global optimality/uniqueness}
\to\text{qualitative entry}
\to\text{global stability}.
\]

It is not necessary for the first coercive-route milestone. The first priority
is an independent zero-deficit proof, not rewriting all of global stability.

## Phase 5 — formal-conjectures interface

Keep the existing bridge statements stable:

- \`Bridge.isMovingSofa_iff\`;
- \`Bridge.sofaConstant_eq\`;
- \`Bridge.gerversSofa_eq\`.

Keep \`Challenge.lean\` stable as the statement-of-record interface.

Add a second solution entry point, tentatively \`SolutionCoercive.lean\`, proving
the same Challenge theorems using the coercive optimality/uniqueness route plus
the same bridge.

The existing \`Solution.lean\` should remain the canonical solution based on
Baek's faithful optimality theorem plus the main uniqueness proof.

Thus the repository will have two internally different proofs of the same
external formal-conjectures statements.

## Phase 6 — route audits

Extend the current dependency-audit strategy.

### Existing maximizer-route audit

Preserve \`scripts/AuditMaximizerRoute.lean\` for the historical second route
until the refactor is complete.

### New coercive-route audit

Add \`scripts/AuditCoerciveRoute.lean\`.

It should fail if any declaration of the coercive route reaches, transitively:

#### Baek final optimality

- \`MovingSofaOptimality.theorem1_1_1\`;
- \`MovingSofaOptimality.gm_area_le\`.

#### Baek's balance-derived step-(3) route

Keep the existing \`baekForbidden\` list from
\`AuditMaximizerRoute.lean\`.

#### Main uniqueness route

Forbid all declarations owned by \`MovingSofaUniqueness.Main\`.

#### Old equality/CapKernel route

At minimum forbid:

- \`MovingSofaUniqueness.ki_maximizer_equality_conditions\`;
- \`MovingSofaUniqueness.capKernel_of_triple_midpoint\`;
- \`MovingSofaUniqueness.CapKernel.eq_horizontal_translation\`;

and any higher-level old classification theorem that would bypass the
coercivity argument.

Negative controls should prove that the audit traversal really sees these
dependencies in the old routes.

## Phase 7 — manuscript integration

Do not rewrite the faithful Baek exposition.

The paper should ultimately distinguish two proof tracks:

### Track A — Baek

A faithful proof of optimality, formalized in \`MovingSofaOptimality\`.

### Track B — coercive framework

A common framework in which:

\[
M-Q\ge0 \Rightarrow \text{optimality},\qquad
M-Q=0 \Rightarrow \text{uniqueness},\qquad
M-Q\ll1 \Rightarrow \text{stability}.
\]

The current subsection “A second proof of optimality” should be absorbed into
this broader section rather than deleted mathematically. Its maximizing-cap and
remaining-angle arguments remain part of the new track.

A likely paper order is:

1. Baek's optimality background;
2. main uniqueness proof;
3. quantitative stability;
4. unified/coercive route to optimality and uniqueness;
5. formalization and bridge to formal-conjectures.

The paper may continue to present the natural narrative
optimality → uniqueness → stability while recording the coercive route as an
independently audited reorganization.

## Merge strategy

This PR is intentionally **stacked on the stability branch** because the new
route depends on cap coercivity.

Recommended merge order:

1. finish/review \`research/quantitative-stability\`;
2. merge or rebase that work into the paper branch;
3. rebase this coercive-extremal PR onto the resulting integration branch;
4. perform Lean compilation/audits only when explicitly allowed;
5. update the manuscript verification claims only after the new route is
   actually kernel-checked.

Until then, descriptions must say “proof source” or “planned formalization,”
not “verified formalization.”
