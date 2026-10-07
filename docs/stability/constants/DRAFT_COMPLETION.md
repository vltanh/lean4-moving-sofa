# Quantitative appendix — authoritative uncompiled draft status

**Status: source audit open. Not kernel checked. Not yet self-contained.**

This is the current concise status ledger for [PR #10](https://github.com/vltanh/lean4-moving-sofa/pull/10).
The earlier claim that the quantitative extension was "15/15 source-complete"
was withdrawn after a branch-local proof-dependency review. All 15 headline
theorems have source bodies, but some invoke missing project-specific lemmas or
contain geometric arguments that are not justified by the present source.
A Lean theorem *declaration* does not establish its proof.

The authoritative per-theorem inventory is
[quantitative_manifest.json](../../paper/quantitative_manifest.json).
The source-only audit is
[scripts/audit_quantitative_source_static.py](../../../scripts/audit_quantitative_source_static.py).

## Current classification

| Status | Count | Interpretation |
| --- | ---: | --- |
| \`source_draft\` | 6 | Main proof bodies have been drafted; not elaborated |
| \`certificate_unexecuted\` | 3 | Analytic/finite checking source exists; closed computations not run |
| \`blocked_source\` | 6 | Genuine mathematical/source dependencies still require proofs |

No Lean, Lake, CI, axiom audit, Comparator, TeX build, or Lean
\`decide\` certificate check was run in this work.

## Consolidated mathematical source

- Centered coercivity and its \(1.001\) enclosure, cap residual sharpness,
  and the puncture lower bound are in separate modules with recorded contracts.
- Full-\(Q\) upper estimates use the actual translation quotient,
  endpoint-slack transfer, and an unexecuted closed operator certificate.
- The feasible lower trial has exact Hermite data, continuous active-arc
  auxiliary bodies, a source-level energy checker, and a fixed strict margin
  \`9221/10000 > 461/500\`; the real-model/finite-cover proof and Boolean
  acceptance still need verification.
- The quantitative local sofa theorem has a complementary deficit budget,
  an explicit terminal comparison, direct area comparison and normal/sector
  drafts. Its Gerver-specific geometric transitions are **not** complete.
- The global effectivity and \`10^-600\` theorem statements are kept at their
  requested arbitrary-original-sofa strength. Their final algebra is drafted,
  but the entry and local-radius hypotheses are not all derived in Lean.

## Substantive corrections retained

1. **Anchored support error.** An unanchored Lipschitz \`L² → sup³\` estimate
   was false for constant functions. The new argument fixes
   \`f(π/2)=0\` and bounds the one-sided integration radius.
2. **Translation-invariant cap radius.** The penalized cap cannot have an
   absolute origin-centered radius bound from translation-invariant input
   data. Comparison is now relative to the input midpoint.
3. **Nearest-point nonemptiness.** Compactness alone does not imply a nearest
   point to an empty set. The revised statements require nonempty compact
   reference sets and use the minimizer property.
4. **Trial-energy cover.** Integrating both reflected and unreflected branch
   partitions double-counted energy. The checker now integrates disjoint
   ordered residual arcs and uses real-valued cell-integral bounds.
5. **Whole surviving-ball recovery (October 7, 2026).**
   At \(\delta=514\sqrt E\), the old prerequisite
   \[
     \sqrt2\,\delta\le\frac{\kappa\rho}{2},
     \qquad \rho=20(\delta+\sqrt E),\quad \kappa=\frac{100}{1051}
   \]
   is **false**. It would invalidate the advertised \`10300\` coarse
   constant. The correct square-witness condition is
   \[
      E<(\kappa\rho-\sqrt2\,\delta)^2,
   \]
   because
   \[
      \kappa\rho-\sqrt2\,\delta
      =\left(\frac{2000}{1051}-\sqrt2\right)\delta
        +\frac{2000}{1051}\sqrt E>\sqrt E.
   \]
   \`EffectiveRecovery.lean\` now has a general full-ball missing-area
   lemma and shared rational/square-root reserves; \`EffectiveEntry.lean\`
   uses it too. This is source, **not** a Lean-verified correction.
6. **Reference widths and cap outer margin.** Exact Gerver endpoint formulas
   are centralized in \`ReferenceExplicitMargins.lean\`, including both
   floor-wing lower bounds \(>4/5\). \`ExplicitReferenceScales.lean\`
   now derives the outer-wall support gap from the top rectangle and both
   floor endpoints instead of an undeclared comparison lemma.

7. **Balanced hallway remainder (October 7, 2026).** The old wall-error
   formulas omitted the rotating-displacement term and were not the claimed
   first-order expansions. \`NormalRecovery.lean\` now uses the exact identity
   for a point p=q+d*w at angle s=t+lambda*d:
   \[
      R_U=(F_U(s,q)-F_U(t,q)-a(s-t))
          +d\langle w,u_s-u_t\rangle,
   \]
   and analogously \(R_V\) with \(+b(s-t)\) and \(v_s-v_t\).
   The direction-rotation term has a generic numerical bound. The separate
   **Gerver support-function quadratic Taylor estimate** remains a real
   geometric proof obligation; correcting the algebra does not establish it.
   The source-only regression test in
   \`scripts/tests/test_quantitative_wall_expansion.py\` contains a
   counterexample to the old formulas.

8. **Tangent-ball reduction for sectors (October 7, 2026).**
   \`ReferenceSector.lean\` now isolates a quantitative geometric fact:
   for the prescribed half-angle \(h=153/200\), a cone of radius \(r\)
   at a rolling-ball tangency point fits inside the interior tangent
   ball of radius \(R\) whenever \(r\le R\). The same containment
   transfers to a point displaced inward by \(d\) when \(r+d\le R\).
   The proof uses the exact inequalities \(\sin h\le\cos h\) and the
   orthonormal frame identity; it requires no Gerver-specific smoothness.
   **Still open:** deriving uniform actual tangent balls/contact charts
   (and separately the two sharp floor-corner wedges) from the Gerver
   phase formulas. This does not by itself prove the full sector atlas.

The full mathematical evidence and negative controls remain in the numbered
notes under \`docs/stability/constants/\`.

## Remaining mathematical gates

1. **Actual Gerver sector atlas:** prove a uniform \(1.53\)-radian cone
   using the true contact/envelope parameter, not a case split on the
   boundary point's horizontal coordinate. The current source still has
   an unjustified chart step.
2. **Normal/roof/terminal scales:** discharge the fixed \(49/100\),
   \(5/51\), explicit support/niche radii and terminal trapezoid transitions
   against existing \`EnvHyp\`, \`CapRoofData\` and Gerver frame lemmas.
3. **Penalized right-angle comparison:** close the dyadic-to-integral
   objective limit and the robust curvature/arm bootstrap.
4. **Incomplete-angle entry:** prove the partial-angle pinned variation,
   exact coarse polygon search coverage, and geometric extension.
5. **Feasible \(Q\)-trial certificate:** confirm the ordered-piece
   integral/real-model bridge and check the finite Boolean reduction.

The final cutoff stays
\[
  0\le\varepsilon\le10^{-600}
  \ \Longrightarrow\
  d_H(S_c,G)\le 2.3\sqrt\varepsilon,\quad
  |S_c\triangle G|\le50\sqrt\varepsilon,\quad
  0\le\frac\pi2-\omega\le3.1\varepsilon.
\]
It is an **uncompiled target** until all transitive dependencies have
source proofs and (in a separately authorized phase) pass Lean's kernel.

## Working-paper boundary

The quantitative working copy is
[docs/paper/quantitative-draft.tex](../../paper/quantitative-draft.tex):
short main quantitative results; technical Appendix F; numerical Appendix G,
ending with the \(10^{-600}\) proposition. It must continue to label the
new results as uncompiled, not fully formalized.

This ledger supersedes the older "source-complete" handoff. No result or
failed intermediate approach has been silently deleted.
