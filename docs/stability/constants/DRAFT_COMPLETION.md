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

9. **Coarse-angle support-box indexing.** The four intermediate rational
   normals contribute two coordinates each (normal and tangent). The former
   polygon clipper used stride four for those eight coordinates; the correct
   stride is two. The native Lean source now has a box-length/index invariant.
   The numerical search and geometric soundness remain unexecuted and open.

10. **Centered-reference equivariance.** For any horizontal translation
    \(K+a\), the midpoint-aligned reference to \(K\) is \(K+a\), not
    \(K\). The former source identity was mathematically false. The
    zero-deficit right-angle theorem now uses the corrected equivariance.

11. **Actual-set comparison chain.** The previous effective right-angle
    proof attempted to compose Hausdorff comparisons whose middle sets did
    not match. The source now compares \(K\to C\to G+m(C)\to G+m(K)\);
    its stated \(514\sqrt e\) bound follows from \(256+1.001+256<514\).
    This is a corrected analytic source argument, not an elaborated proof.

12. **Fixed-radius sector case.** An arbitrary interior-ball radius
    \(\rho\) does not decide containment of the prescribed \(10^{-20}\)
    ball. The source now splits directly on that fixed ball. The genuine
    Gerver boundary sector atlas remains open.

13. **Lean-only numerical trust.** The three finite proofs (full-Q operator,
    lower trial energy, and coarse angle) must use closed Lean Boolean
    reductions and Lean soundness theorems only. Python and JSON are not
    eligible numerical theorem premises, nor required proof generators.
    See `37-lean-only-certification-contract.md`.

14. **Core roof FTC repaired (uncompiled).** An earlier proof applied
    `integral_mono_on` to an inequality at just the integration endpoint,
    and treated continuity of the *derivative* as a stand-in for a
    differentiability/FTC theorem. The proof source now contains:
    - `corePathSlackU/V`, written using Gerver's actual path instead of
      an unjustified derivative of its abstract support function;
    - exact depth derivatives `corePathRateU/V`, including the moving
      frame term;
    - `corePathSlack_eq_innerSlack`, using the integrated corner
      support identities on the reference turning interval;
    - `core_slack_of_uniform_derivative_bound`, which assumes derivative
      bounds at **every** depth, continuity/integrability, and a genuine
      HasDerivAt FTC hypothesis;
    - `uniform_core_slack_from_C1` wired through these lemmas.
    This removes the invalid pointwise-integral inference, but the
    lengthy C1 composition/source proof and `fun_prop` obligations
    remain **uncompiled and not yet kernel verified**.

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


## Rational coarse-angle and effective-angle source repairs (October 7, 2026)

This source-only pass supplied previously undeclared elementary geometry and
domain lemmas without running Lean:

- **Half-angle coverage:** \`exists_hundredth_slab\` covers every real
  \(r\in[3/5,4/5]\) by the twenty closed rational slabs; both endpoint
  inequalities are derived from cosine/sine identities instead of using
  the missing \`tan_mono_on_quadrant\` helper. The lower proof uses
  \(\omega<\pi\), not the unjustified \(\omega\le\pi/2\) implication.
- **Right-angle endpoint:** \`EffectiveAngleEntry.high_angle_cot_le_quarter\`
  handles \(\omega=\pi/2\). The old premise \(4<\tan\omega\) was false
  there because tangent is totalized; the proof now directly bounds
  \(\cot\omega=\cos\omega/\sin\omega\).
- **Exact search primitives:** rational polygon clipping now has explicitly
  decided Boolean endpoint tests; the upper-support contraction takes its
  maximum from the lower box endpoint, not the existing upper endpoint.
  Unused split-coordinate storage was removed from \`SearchTree\`.
  The rational normal has proven unit length, its paired tangent is
  orthogonal, its first component is positive on the searched slabs,
  and rational edge-line intersections have exact support values and
  parameters in \([0,1]\) when an edge crosses the support line.
- **Anchored support-error hygiene:** a zero-case branch no longer shadows
  the hypothesis fixing the top-normal support error.
- The static linter now flags recurrence of the tangent-endpoint,
  rational-clipping, contraction, and incorrect \(\pi/2\) deductions.

These are **uncompiled source lemmas**, not successful proof checks.
The entire coarse-search soundness still needs the terminal-pinned candidate
geometry, polygon containment, support-box contraction soundness, and
the whole search-tree cover to be justified. The finite Boolean reduction
has not been run. The six blocked theorem groups and three unexecuted
certificate groups remain blocked/unexecuted; **no target is promoted**.
