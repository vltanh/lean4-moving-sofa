# PR #9 transfer: zero-deficit rigidity does not replace geometric enclosure

Two snapshots were inspected during this continuation. PR #9 began the pass at `5016a36b071e66f82a7de9e327f7a63a8fad1e8c`, with four planning documents. It advanced during the work to **`8042bad7eb08037f773ea03a635d10ff203e57de`**, which contains uncompiled extremal proof source. The initial ambidextrous head was `e20a4bc7d7aa6b3f6a722fcf682e1b4b065b6c39`. Claims below are pinned to these snapshots; the original planning-only observation must not be read as the status of the later implementation.

## 1. The new implemented interface and its actual hypotheses

At the initial snapshot, [ROADMAP.md](https://github.com/vltanh/lean4-moving-sofa/blob/5016a36b071e66f82a7de9e327f7a63a8fad1e8c/docs/coercive-extremal/ROADMAP.md), [DEPENDENCIES.md](https://github.com/vltanh/lean4-moving-sofa/blob/5016a36b071e66f82a7de9e327f7a63a8fad1e8c/docs/coercive-extremal/DEPENDENCIES.md), and the README explicitly described a planned refactor. On reinspection the later branch had added `MovingSofaExtremal` and its intended global proof/Challenge interface. These files explicitly remain **uncompiled proof source**, not a successful elaboration or kernel-verification record.

The later [Geometry.lean](https://github.com/vltanh/lean4-moving-sofa/blob/8042bad7eb08037f773ea03a635d10ff203e57de/MovingSofaExtremal/Geometry.lean) defines

```text
MaximizesCap omega K :=
  forall C, IsCap C omega -> sofaArea omega C <= sofaArea omega K.
```

Its `isKi_of_maximizes` obtains positivity by comparing with Gerver, then calls the existing one-turn `curvature_of_maximal_positive` and `injectivity_of_curvature`. Thus the source still has a substantive **maximality-to-geometric-domain theorem** before the coercivity argument. Its `maximizing_monotone_has_right_angle` likewise retains one-turn maximality, a monotone sofa, and the area threshold 2.2 in its remaining-angle step.

The later [CoerciveRigidity.lean](https://github.com/vltanh/lean4-moving-sofa/blob/8042bad7eb08037f773ea03a635d10ff203e57de/MovingSofaExtremal/CoerciveRigidity.lean) makes the separation especially clear:

```text
right_angle_maximizer_certificate:
  isKi_of_maximizes
  + Gerver competitor lower bound
  + theorem8_2_4 (the geometric area bound)
  + wideUpperQ_le_gerver
  -> area and Q both equal Gerver's area.

wide_zero_deficit_cap:
  sharp_wide_cap_distance_bound at zero deficit
  + EuclideanClose.eq_of_zero
  -> equality of the cap.
```

Elementary niche translation then identifies the cap-minus-niche body. The new route replaces the old CapKernel classification; it does not replace or eliminate the geometric bound `theorem8_2_4` or the hypothesis needed to invoke it.

No PR #9 files were merged, cherry-picked, compiled, or modified here. This is source-level dependency inspection, not a verified audit of the entire transitive Lean graph.

## 2. Why this cannot be directly applied to an ambidextrous maximizer

Maximizing a two-turn body does not say that either one-turn cap maximizes `sofaArea` against **all** caps. Replacing it by a one-turn maximizer can destroy the other motion. The required premise of `isKi_of_maximizes` is therefore unavailable, not an interface conversion left to be filled in.

Also, the reference constants differ: PR #9 classifies Gerver's one-turn maximizer, whereas this branch targets Romik's two-turn candidate. A bound in terms of the Gerver deficit does not turn ambidextrous near-optimality into proximity to Romik.

The dependency contract's separation of low coercivity from global stability remains useful. Global qualitative entry uses uniqueness; importing it to establish that same uniqueness would create a cycle. The new extremal source avoids that cycle by importing only the lower quantitative layer. An ambidextrous proof needs the same separation.

## 3. The exact assembly rule that does transfer

Suppose an area functional A on an admissible class attains its supremum and a candidate S_* is feasible with area M. Suppose that **every** maximizing S admits data xi such that

$$
A(S)\leq Q(\xi)\leq M,
$$

and equality throughout implies S is congruent to S_*. Then S_* is optimal and all maximizers are congruent to it. Maximality gives A(S)>=M, so every inequality is an equality. If the construction is available for only one maximizer, it determines the value, not uniqueness of all maximizers.

A distance estimate d(xi,xi_*)^2<=C(M-Q(xi)) can identify the auxiliary data at equality. Exact body equality remains a separate requirement: equal convex hulls do not imply equal nonconvex bodies. Containment in the identified regular-closed envelope and equality of area is one valid recovery argument.

For quantitative stability, the comparison must cover near-maximizers, and their distance as actual bodies must be controlled too. A maximizer-only theorem does not automatically provide those hypotheses.

## 4. The attempted ambidextrous transfer was tested and rejected

AF3 already supplies the sharp auxiliary bound and its equality set. What remains is the ordinary-area comparison, since

$$
M_A-|S|=[M_A-Q_A(h)]-[|S|-Q_A(h)].
$$

The latest AB1 anchor constraints retain the two turns' shared original horizontal exposed points:

$$
u+u^\rho\leq\sin t,\qquad v+v^\rho\leq\cos t.
$$

Those inequalities are valid. However, **Theorem SC3 in [the shadow-clipping note](repair-shadow-clipping-obstruction.md) disproves the geometric premise of AB.5** even for actual repairs satisfying them. It constructs a fully saturated, compact connected full-turn body B_z with actual hull H_z and least repair R(H_z)=bar K_z, such that

$$
|B_z|>\widetilde Q(h_{\bar K_z})>
\mathcal J_0(h_{\bar K_z};h_{\bar K_z}-h_{H_z}).
$$

The discrepancy is a positive integral of clipped upper-niche area. The nonzero repair is confined to a region where its final q is negative, so this is not adverse contact work with q>1. Nor is there a derivative-energy charge in J_0. Shared anchors, full turns, and canonical saturation all hold. The bodies have candidate width and their areas tend to M_A from below with the explicit positive cubic deficit in SC.12.

Thus neither deleting the rejected derivative penalty nor restricting to the true shared anchor budgets supplies the missing enclosure. Further maximization of this same J_0 cannot close a false geometric premise. The earlier findings AF4, AX1, SAT1, and SAC2 remain valid; this is a separate clipping obstruction.

## 5. Computational disclosure and remaining target

Exploratory fixed-width discretizations of the AB model used 48 angular cells and L-BFGS-B from four seeds. They suggested values near the candidate, but supply no continuous bound. An exact scalar quadrature check explored one sufficient estimate for an analytic J_0 calibration. Neither experiment was used in SC3, and no new global J_0 theorem is claimed. Once its proposed ordinary-area link failed, that calibration was not pursued as a route to closure.

The committed standard-library `check_shadow_clipping.py` instead tests the explicit obstruction by two independent area computations and a support-energy computation. Its JSON result is labelled as diagnostics, not a certificate. The source Git blob matches the locally executed bytes. The continuum proof is the geometric construction and analytic limit, not its five sampled scales.

A valid use of the PR #9 pattern still needs a true ambidextrous geometric majorant, retaining actual tail intersections or an equivalent clipping correction, or a structural theorem for every global maximizer that justifies the existing CW4 comparison. The current pass proves neither unrestricted result. No separate optimality, uniqueness, or stability conclusion is inferred from a planning document or an uncompiled theorem source.

## 6. Execution

No CI, Lean/Lake invocation, dependency installation, or manuscript build was performed. PR #9 and the existing Lean libraries were left untouched. All continuation commits use `[skip ci]`. The earlier proof chain and the new analytic obstruction are self-reviewed, not independently verified. Unrestricted ambidextrous optimality and uniqueness remain unproved in this branch.
