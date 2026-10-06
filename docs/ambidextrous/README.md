# Ambidextrous sofa research

**Starting a new research session? Read [HANDOFF.md](HANDOFF.md) first, then [ROADMAP.md](ROADMAP.md).** The handoff records the current branch checkpoint, proved results, failed routes, validation status, and the next critical gates.

**The unrestricted optimality and uniqueness proof is not closed.** The analytic width exclusion and the sharp auxiliary calibrations remain available, but the ordinary-area comparison for unrestricted maximizing bodies is unproved. The latest continuation inspected PR #9's new extremal source and tested, rather than assumed, the geometric premise needed to transfer its method.

These are written, self-reviewed arguments and explicitly labelled computational diagnostics. They are not independently refereed or Lean-verified results. The entire historical dependency chain has not been independently audited. No novelty or best-known-bound claim is made.

Research branch: `research/ambidextrous-pen-and-paper`.
Draft PR: [#3](https://github.com/vltanh/lean4-moving-sofa/pull/3).
Original base: `paper/uniqueness-arxiv` at `1ade045936f32cf76572ee668ed8aa1627772bde`; the base has since advanced. Existing manuscript files, Lean libraries, dependencies, and workflow definitions are unchanged.

## PR #9: useful organization, not the missing ambidextrous hypothesis

The [transfer audit](coercive-pr9-transfer-audit.md) records two snapshots. PR #9 initially had planning documents at `5016a36`; it advanced during this pass to uncompiled extremal proof source at `8042bad`. The latter implements a proposed Gerver route through

```text
one-turn cap maximality
  -> isKi_of_maximizes
  -> actual area <= intermediate Q <= Gerver's area
  -> zero Q deficit
  -> sharp cap-distance estimate at zero
  -> cap and sofa equality.
```

The source still obtains geometric admission from the existing one-turn curvature theorem, and still invokes the geometric area inequality before applying coercivity. An ambidextrous maximizer does not maximize either one-turn cap against all caps, so that premise cannot simply be imported. The global-stability layer is deliberately not imported into low coercivity, since qualitative entry there uses uniqueness.

No PR #9 files were merged or compiled. Its new source was inspected at a pinned commit; a proof term in an uncompiled file is not a kernel-verification record. The exact transferable pattern is to keep geometric enclosure, functional calibration, and actual-body equality recovery separate.

## New ordinary-area obstruction: shared anchors do not control clipping

The [anchor bounds AB1](repair-anchor-budgets.md) are valid: genuine nested hulls with the same four axis supports satisfy

$$
u+u^\rho\leq\sin t,\qquad v+v^\rho\leq\cos t.
$$

But [Theorem SC3](repair-shadow-clipping-obstruction.md) disproves the ordinary-area inequality proposed for the derivative-free budget J_0, even with those genuine constraints.

The construction starts with an explicit curvature-dominated outer set bar K_z near the candidate. Its complete two-turn envelope B_z is compact, connected, has the candidate's width and unit span, and is fully saturated in its actual hull H_z. The actual least curvature repair is **exactly** R(H_z)=bar K_z. Nevertheless

$$
\boxed{
|B_z|-\widetilde{\mathcal Q}(h_{\bar K_z})
=\int_{x_Z}^{m}\min\{F_*(x),1-\bar T_z(x)\}\,dx>0.
}
$$

Here F_* is the candidate's lower-tail roof, bar T_z is the changed upper hull boundary, and m is its face length. The positive term is actual upper-niche clipping against the repaired hull. It is not adverse contact work: the final q is negative on the nonzero repair support. Nor does this example rely on a derivative-energy charge. In fact

$$
|B_z|>\widetilde{\mathcal Q}(h_{\bar K_z})>
\mathcal J_0(h_{\bar K_z};h_{\bar K_z}-h_{H_z}).
$$

These are not counterexamples to Romik optimality. An independent ordinary-area calculation proves

$$
\boxed{M-|B_z|=\frac{37-26\sqrt2}{24}z^3+o(z^3)>0.}
$$

Their areas tend to M from below. Therefore neither a fixed high-area threshold, shared anchors, full turns, nor canonical saturation rescues the proposed enclosure. The original AB note now explicitly marks its geometric proposal as disproved while retaining its valid inequalities.

The [standard-library diagnostic](computer-assisted/check_shadow_clipping.py) compares the direct slice loss/recovery, support-functional deficit, and clipping integral at five scales. The [executed record](computer-assisted/shadow-clipping-diagnostics.json) is labelled `is_proof_certificate: false`; the source bytes match their committed Git blob. These floating-point checks are not the analytic proof or a global certificate.

## A precise positive identity for auxiliary tail regions

[Theorem TR1](repair-invariant-tail-regions.md) identifies what the least repair really preserves. For a full quarter J let

$$
C_J(h)=\bigcap_{t\in J}\{x:x\cdot n_t\geq h(t)-1\}.
$$

Then

$$
\boxed{C_J(h)=C_J(R(h)).}
$$

In the projective coordinate used by GM2, each point tests an affine minorant of the wall obstacle. Replacing the obstacle by its convex envelope therefore changes none of these tests. The proof is elementary and exact.

The **clipped** tail bodies still change:

$$
(R(K)\cap C_J)\setminus(K\cap C_J)
=(R(K)\setminus K)\cap C_J.
$$

Only the indicated part of the new hull is safe for that wall family. The same identity applies to the intersection of the appropriate safe regions for both turns. It does not cover mixed-wall core points or extend a partial endpoint to a full turn.

The SC3 family also shows that iterating the same repair and saturation is not a solution:

$$
\mathcal E(R(\operatorname{conv}B_z))=B_z,
$$

although the actual hull still violates curvature domination and the body is strictly suboptimal. Any sharp auxiliary-body comparison must retain actual clipping rather than assume the repaired hull is the surviving body's hull.

## The width gate remains closed analytically

[Theorem AW-W](analytic-width-theorem.md) proves, for a compact connected ambidextrous body in a common incoming unit-height strip,

$$
\boxed{W\leq2\quad\Longrightarrow\quad |S|<41/25=1.64<M.}
$$

It assumes no curvature cap, symmetry, contact order, full-quarter endpoint, or functional enclosure. Incoming vertical span need only be at most one. Its four actually visited orientations, disjoint loss partition, mixed-area triangle inequality, and convex localization provide a pen-and-paper proof; no search tree is required. The [review](analytic-width-review.md) records discovery and proof separately. The older [computer certificate](computer-assisted/README.md) is retained as a superseded approach to the width gate, not retracted.

The [diagonal-width bound DU1](diagonal-width-upper-bound.md) gives W<=1+2sqrt(2) for sufficiently large bodies. Together with the earlier attainment and normalization arguments, every global maximizer has

$$
2<W\leq1+2\sqrt2<4.
$$

This is not a localization of the whole shape near the candidate.

## Earlier obstructions and their exact roles

[GM2](global-curvature-majorant.md) constructs the least same-axis curvature-dominated support majorant and an exact positive **hull-area** gain. [GR1](global-repair-counterexample.md) shows that the corresponding ordinary sofa area can decrease. [AC1](repair-corrected-global-calibration.md) and [AS1](repair-side-loss-calibration.md) bound explicitly defined corrected auxiliary functionals, not the original area for arbitrary repairs.

[AX1](axis-cut-repair-budget-obstruction.md) disproves their proposed universal area linkage; [SAT1](saturation-does-not-rescue-repair.md) preserves that failure after full saturation. [SAC2](saturated-axis-cut-area.md) computes the saturated family's actual positive deficit of order tau^(3/2), despite a hull derivative-energy discrepancy of order tau. Its [diagnostic record](computer-assisted/saturated-axis-diagnostics.json) remains separate from its analytic proof. The new SC3 example is a further obstruction with no derivative-energy charge at all.

For the original adaptive functional,

$$
M-|S|=[M-\widetilde{\mathcal Q}(h)]-[|S|-\widetilde{\mathcal Q}(h)].
$$

[AF3](adaptive-functional-global-calibration.md) controls the first bracket and its equality kernel. [AF4](adaptive-functional-enclosure-counterexample.md) and the [narrow convex example](narrow-curvature-enclosure-counterexample.md) show the second can be positive. A new calibration cannot close the problem unless its ordinary-area inequality is valid.

## The remaining sufficient theorem

The existing [CW4 theorem](curvature-only-wide-hulls.md) gives the sharp ordinary-area bound and exact body uniqueness for unit-span common hulls with W>=2 and

$$
\sigma_K=h_K+h_K''\leq d\theta
\quad\text{on the four open coordinate quarters}.
$$

It does not separately assume contact order, full turns, or aligned faces. A sufficient route therefore remains

```text
an attained global maximizer
  -> common incoming unit-span normalization
  -> 2 < W < 4                          [AW-W and DU1]
  -> full curvature-measure domination  [NOT PROVED]
  -> CW4 and exact body recovery.
```

Alternatively, a valid sharp ordinary-area comparison using auxiliary tail bodies could replace the curvature reduction. **No such unrestricted comparison is supplied by this continuation.** TR1 identifies exact tail regions; it does not bound the remaining core and clipping terms. The SC3 construction shows why the latest J_0 shortcut cannot be used.

A result for one attained maximizer determines the value. Uniqueness requires every maximizer or an equality-preserving comparison. Equal hulls alone do not identify nonconvex bodies. Obstructed contacts, hidden/coincident atoms, and the sharp diffuse density bound remain unresolved in the maximizing-body route. Vanishing finite selection penalties do not remove contact normal-cone terms.

## Reading map and research record

| Source | Role |
|---|---|
| [PR #9 audit](coercive-pr9-transfer-audit.md) | Both pinned snapshots, actual source hypotheses, and the rejected transfer shortcut. |
| [SC1–SC3](repair-shadow-clipping-obstruction.md) | Fully saturated shared-anchor counterexample, exact clipping identity, and positive actual deficit. |
| [TR1](repair-invariant-tail-regions.md) | One-wall invariance, clipped-tail set identity, and the repair/saturation fixed point. |
| [AB1](repair-anchor-budgets.md) | Valid shared anchor bounds; its proposed ordinary enclosure is marked disproved. |
| [AW-W](analytic-width-theorem.md), [DU1](diagonal-width-upper-bound.md) | Analytic width restrictions for competitive bodies. |
| [CW4](curvature-only-wide-hulls.md) | Sharp theorem conditional on the remaining curvature reduction. |
| [SAT1](saturation-does-not-rescue-repair.md), [SAC2](saturated-axis-cut-area.md) | Earlier saturation obstruction and exact axis-cut area calculation. |
| [AF3](adaptive-functional-global-calibration.md), [AF4](adaptive-functional-enclosure-counterexample.md) | Auxiliary calibration and ordinary-area failure. |
| [PR #8 audit](stability-pr8-transfer-audit.md) | Why Gerver stability does not give noncircular Romik localization. |
| [Historical structural ledger](57-focused-structural-status.md) | Finite constrained variations and partial singular/contact exclusions. |

All prior findings remain in files and Git history. The preceding README at `59ddfef` records the unfinished direct disjoint-loss numerical exploration; it did not produce a global certificate. The PR #9 audit records this continuation's abandoned fixed-width AB-model exploration. Neither numerical optimizer output is presented as proof progress on a failed geometric premise.

## Execution

All continuation commits include `[skip ci]`. No CI, Lean/Lake compilation, dependency installation, or manuscript build was used. No files from PR #9 were modified, merged, or cherry-picked. Local diagnostic calculations are disclosed and do not certify unrestricted optimality. PR #3 remains open and draft, with the global theorem and independent review unfinished.
