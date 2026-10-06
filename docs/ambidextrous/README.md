# Ambidextrous sofa research

**The unrestricted optimality and uniqueness proof is not closed.** The analytic width exclusion and the sharp auxiliary-functional calibrations do not yet supply a valid ordinary-area comparison for every maximizing body. The latest audit also rules out rescuing the rejected repair budget merely by requiring canonical saturation.

These are written, self-reviewed arguments and explicitly labelled computational diagnostics. They are not independently refereed or Lean-verified results. The entire historical dependency chain has not been independently audited. No novelty or best-known-bound claim is made.

Research branch: `research/ambidextrous-pen-and-paper`.
Draft PR: [#3](https://github.com/vltanh/lean4-moving-sofa/pull/3).
Original base: `paper/uniqueness-arxiv` at `1ade045936f32cf76572ee668ed8aa1627772bde`; the base has since advanced. Existing manuscript files, Lean libraries, dependencies, and workflow definitions are unchanged.

## Latest correction: saturation is not the missing theorem

[SAT1](saturation-does-not-rescue-repair.md) applies complete canonical saturation to the actual axis-cut counterexamples from [AX1](axis-cut-repair-budget-obstruction.md). The resulting bodies T_tau are compact, connected, feasible for both full turns, fixed points of saturation, and have exactly the original cut hulls K_tau.

They still satisfy

$$
|T_\tau|>
\mathcal J_{\rm side}(h_{R(K_\tau)};h_{R(K_\tau)}-h_{K_\tau})
$$

for all sufficiently small positive tau. The right side depends on the hull, which saturation preserves, while saturation can only increase the left side.

Thus the earlier suggestion that the axis-cut obstruction was only caused by deliberately omitted, unsaturated material was insufficient. Fixed-hull saturation is an inclusion closure; it is not maximization over different hulls. Requiring it does not make AS.10 true.

### The saturated family's actual area is now computed

[SAC2](saturated-axis-cut-area.md) proves analytically that these saturated bodies are nevertheless strictly suboptimal. If m is the candidate's horizontal face length, then

$$
\boxed{
M-|T_\tau|=
\frac{1+2\sqrt2}{3}\,m^{3/2}\tau^{3/2}
+o(\tau^{3/2})>0.
}
$$

The computation identifies the changed lower-niche roof as a unit-circle arc and subtracts its actual recovered area from two upper circular-cap losses. It does not count every added hull point as surviving sofa material. This resolves the sign for the saturated family without assuming unrestricted optimality.

In contrast, the squared derivative discrepancy of its hull support is of order tau. Therefore a uniform estimate charging that entire derivative energy against ordinary missing area also fails on saturated bodies arbitrarily close to the candidate. This is a concrete requirement for any replacement proof, not a counterexample to candidate optimality.

The numerical program [check_saturated_axis_cut.py](computer-assisted/check_saturated_axis_cut.py) compared the closed formulas with separate vertical-slice quadrature at five scales. [The execution record](computer-assisted/saturated-axis-diagnostics.json) labels these as diagnostics, not a proof certificate. The executed source matches its committed Git blob. The analytic argument is independent of these computations.

## The width gate is closed analytically

[Theorem AW-W](analytic-width-theorem.md) proves, for a compact connected ambidextrous body in a common incoming unit-height strip,

$$
\boxed{W\leq2\quad\Longrightarrow\quad |S|<41/25=1.64<M.}
$$

It assumes no curvature cap, symmetry, contact order, full-quarter endpoint, or functional enclosure. Incoming vertical span need only be at most one.

The proof uses four actually visited hallway positions with complementary cosine/sine pairs (sqrt(3/5),sqrt(2/5)) and (sqrt(2/5),sqrt(3/5)). A fixed disjoint partition counts independent lower- and upper-turn losses. The [mixed-area inequality](analytic-width-loss-partition.md) bounds triangular overlap; the [localization lemma](analytic-width-localization.md) uses four rational boundary checks and convexity rather than parameter enumeration. The final two-variable convex minimum gives more than 9/50 loss for each turn.

No certificate replay, numerical optimizer, or generated case list is needed for this theorem. The [review](analytic-width-review.md) separates exploratory discovery from its analytic proof. The earlier computer-assisted 411/250 bound and its [complete certificate record](computer-assisted/README.md) remain preserved as a historical approach, superseded for the width gate rather than retracted.

The [diagonal-width bound DU1](diagonal-width-upper-bound.md) also gives W<=1+2sqrt(2) for every sufficiently large body. Thus the earlier attainment and normalization arguments place every global maximizer in

$$
2<W\leq1+2\sqrt2<4.
$$

This does not localize its shape near the candidate.

## What the global repair and calibrations actually establish

[GM2](global-curvature-majorant.md) constructs the least support majorant R(K) with the same four axis supports and curvature measure dominated by angular measure on the open quarters. It has a positive, exact **hull-area** gain. It does not automatically give a feasible area-improving sofa.

[GR1](global-repair-counterexample.md) supplies wide, fully feasible examples where that repair decreases ordinary sofa area. [AC1](repair-corrected-global-calibration.md) and [AS1](repair-side-loss-calibration.md) then calibrate explicit corrected auxiliary functionals which include adverse corner work and side-mass terms. Their stated global maxima and equality kernels concern those functionals.

The hoped-for universal ordinary-area linkage is false: AX1 disproves it near the candidate, and SAT1 shows that canonical saturation does not repair it. SAC2 computes the true smaller deficit. The valid geometric consequences under the explicit standard-corner accounting hypotheses remain valid; they are not a theorem about every saturated body or every maximizer.

The older [AF3 calibration](adaptive-functional-global-calibration.md) likewise does not supply ordinary-area enclosure. For an actual hull support h,

$$
M-|S|=
\underbrace{M-\widetilde{\mathcal Q}(h)}_{\text{auxiliary deficit}}
-\underbrace{(|S|-\widetilde{\mathcal Q}(h))}_{\text{ordinary-area error}}.
$$

The second term can be positive, as [AF4](adaptive-functional-enclosure-counterexample.md) and the [narrow convex example](narrow-curvature-enclosure-counterexample.md) establish. Maximizing a further auxiliary expression does not settle the problem until its comparison with actual area is proved.

## A sufficient remaining route, with its quantifiers visible

The existing [CW4 theorem](curvature-only-wide-hulls.md) proves the sharp ordinary-area bound and exact body uniqueness for unit-span common hulls with W>=2 and

$$
\sigma_K=h_K+h_K''\leq d\theta
\quad\text{on the four open coordinate quarters}.
$$

Its proof does not separately assume contact order, full turns, or aligned faces. Therefore a sufficient route is

```text
an attained global maximizer S
  -> common incoming unit-span representative             [earlier reduction]
  -> 2 < W < 4                                            [AW-W and DU1]
  -> full curvature-measure domination                    [NOT PROVED]
  -> CW4                                                  [stated-class theorem]
  -> area(S) = M and exact candidate recovery.
```

For the value, a structural result for one attained maximizer suffices. For uniqueness it must apply to every maximizer, or be replaced by an equality-preserving comparison. Merely proving a set is fully saturated does neither. An area-dominating replacement also needs its equality case checked: hull equality alone is not exact equality of nonconvex bodies.

The unresolved maximizing-body argument includes obstructed outer/inner-corner contacts, hidden or coincident edge atoms, and the sharp absolutely continuous density bound. The earlier clear-contact exclusions have explicit scopes. Vanishing selection penalties do not discard the finite contact normal-cone terms. No step in this README substitutes these partial conclusions for full domination.

## Other exploration in this audit

A separate floating-point experiment tested a direct disjoint-loss relaxation, rather than another curvature repair. On [-a,a] times [0,1], it counted outer loss in the upper halves of |x|>a/2 and inner-niche loss in the lower half of |x|<=a/2, then optimized finitely sampled hallway offsets. This is a possible ordinary-area route, not a new theorem.

The experiments used NumPy 2.3.5 and SciPy 1.17.0, midpoint spatial sums and L-BFGS-B. At the candidate width, 26-angle/1,800-point multistarts with seeds 0 through 5 were tested, both without and with the necessary offset bounds f>=a cos(t), g>=a sin(t) and the rectangle upper bounds. Dropping these anchoring bounds produced a much looser apparent optimum; that relaxation must not be mistaken for a common-hull model. Restoring the bounds did not produce a certified global result.

Candidate-only sampled envelope areas at 512, 2,048 and 8,192 angles were approximately 1.64524946, 1.64502870 and 1.64497369. These are not rigorous numerical bounds and do not certify convergence or optimality. They are compatible with the known candidate value and the omission of intermediate angular constraints. No complete covering, analytic minimization of this loss, or inequality for the whole continuum was established. This experiment is recorded as unfinished discovery, not as additional proof progress.

## Reading map and retained history

| Source | Role |
|---|---|
| [SAT1](saturation-does-not-rescue-repair.md), [SAC2](saturated-axis-cut-area.md) | Saturation counterexample and the exact ordinary-area deficit of that family. |
| [AX1](axis-cut-repair-budget-obstruction.md) | Original cut-hull obstruction to the corrected budget. |
| [GM2](global-curvature-majorant.md), [GR1](global-repair-counterexample.md) | Global hull repair and failure of unconditional ordinary-area monotonicity. |
| [AC1](repair-corrected-global-calibration.md), [AS1](repair-side-loss-calibration.md) | Corrected auxiliary maxima, not universal geometric enclosure. |
| [AW-W](analytic-width-theorem.md), [DU1](diagonal-width-upper-bound.md) | Analytic lower and upper width restrictions for competitive bodies. |
| [CW4](curvature-only-wide-hulls.md) | Sharp geometric theorem conditional on the remaining curvature reduction. |
| [AF3](adaptive-functional-global-calibration.md), [AF4](adaptive-functional-enclosure-counterexample.md) | Sharp auxiliary calibration and ordinary-area enclosure failure. |
| [PR #8 audit](stability-pr8-transfer-audit.md) | Why one-turn Gerver stability does not give noncircular Romik localization. |
| [Historical structural ledger](57-focused-structural-status.md) | Earlier constrained variations, singular/contact analysis, and their hypotheses. |
| [Historical computer certificate](computer-assisted/README.md) | Preserved exact width covering and reproduction instructions. |

All prior findings and corrections remain in the files and Git history. The candidate is Romik's explicit construction; Baek's method and the repository's uniqueness/stability developments motivate the broader program. The recent audit uses the stated candidate formulas, but is not an independent review of every historical argument.

## Execution

All continuation commits include `[skip ci]`. No CI was requested or used, and no Lean/Lake compilation, dependency installation, or manuscript build was performed. Local Python diagnostics and exploratory optimization are disclosed above. They do not turn the unproved global geometric comparison into a theorem. PR #3 remains open and draft.
