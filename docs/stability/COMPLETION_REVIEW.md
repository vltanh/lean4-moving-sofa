# Completion audit and validation record

**Scope:** notes 05--09 contain a completed written argument for unrestricted square-root stability. This record is a self-audit, not an independent referee report, a Lean check, or an interval certificate. The original manuscript and its formal-verification claims are unchanged. No CI, Lean build, or TeX compilation was attempted.

## 1. The two missing reductions are replaced, not assumed

The previous proof needed a monotone right-angle envelope with an injective cap. That hypothesis is not deduced from Hausdorff closeness: it is false that a nearby cap must have absolutely continuous curvature. Instead:

- Note 05 derives an explicit affine-minus-squares formula for all normalized caps, handling curvature atoms by an almost-everywhere support-function calculation. The reference first-variation certificate is rederived with a nonsmooth competitor.
- Note 06 proves the geometric area bound only in a fixed neighborhood of Gerver. Core graph monotonicity persists because Gerver has unique exposed points and strictly positive arm margins on the compact core interval. Away from the cuts, cut separation persists by uniform support convergence. Canonical-body endpoint equalities are proved separately.
- Note 07 compares omitted final-angle wedges with an actual loss forced by the terminal strip. It does not extend the motion of the original sofa.
- Note 08 uses qualitative compactness only to enter those fixed neighborhoods. The square-root estimate comes from the deficit identity and the geometric estimates, not from extracting a power from compactness.

The conclusion is therefore not conditional on an unproved regularization or injective-envelope lemma.

## 2. Places where the proof would otherwise fail

**Curvature atoms.** Source Lemma 8.3.7 is presented under Ki assumptions and identifies one-sided vertices at selected normals. Simply repeating that presentation for polygons would omit atom terms. Note 05 instead proves P+S=Lambda directly from the full support-area formula and absolutely continuous primitives. The checker includes vertical edges and atoms at the cut normals.

**Top-face convergence.** Support derivatives need not converge at Gerver's top edge. Note 06 uses unique-exposed-point convergence only on compact intervals avoiding that normal. Near the top normal it uses the weaker, valid assertion that every limiting exposed point belongs to the whole top face, so its abscissa lies between a and b.

**The whole reference corner path has positive height.** The cited manuscript states positivity on the exposed core. Note 06 verifies the remaining first/last phases analytically from the given rotation-path formula before using the full niche projection to bound its wedge feet. Positivity of the roof on (a,b) follows from the positive core height and the tail derivatives: D'_y>0 for 0<t<=theta and B'_y<0 for v-theta<=t<v, with the tail endpoints on the floor.

**Choosing constants in the correct order.** In the terminal-strip lemma, the fixed containing radius and left-wing floor interval are chosen first. The endpoint-window width eta is then made small enough that the omitted wedge area has coefficient less than half the terminal loss. Only afterward are the cap neighborhood and angular threshold reduced. There is no circular choice of eta as a function of an unknown convergence rate.

**No containment of S in the full-angle envelope.** For omega<v, S can have points in the omitted wedges. The proof retains |S minus U|<=epsilon, |U minus S|<=2epsilon and an approximate hallway slack of -2R(v-omega). The factor 2 in the missing-area bound is retained in the recovery constant.

**No inference of intermediate widths from endpoint widths.** A segment of length sec(alpha/2) has width 1 in the directions -alpha/2 and alpha/2 but width greater than 1 in between. The terminal-strip comparison does not use that invalid implication.

**No Hausdorff-to-area continuity for nonconvex sets.** The qualitative entry proof uses only upper semicontinuity. The quantitative symmetric-difference bound is proved by a convex outer parallel layer and a vertical band under the reference niche roof.

**The normalization is fixed before taking limits.** The manuscript's no-rotation corollary, followed by h(v)=1 and h(pi)=h_G(pi), identifies the limiting sofa with G itself. The width lemma identifies the limiting terminal angle with v. Arbitrarily rotating near-maximizers would not preserve the prescribed initial strip and is not done.

## 3. What is and is not sharp

The cap residual constant 2sec(phi) is exact for the pinned ambient residual space, not proved optimal for feasible sofas or after optimizing the translation.

The Hausdorff exponent 1/2 is optimal on the unrestricted class of closed connected sofas. Note 09 removes a small interior disk and proves d_rig(S_r,G)=r even after optimizing the rigid alignment, while M-|S_r|=pi*r^2.

That example does not establish a sharp symmetric-difference exponent, nor a sharp rate within the monotone-cap subclass. No numerical value for the global recovery constant C or entry threshold epsilon0 is asserted. The latter is obtained non-effectively through compactness and uniqueness.

## 4. Local diagnostic run

Command:

    python docs/stability/check_completion.py

Recorded environment: Python 3.13.5, NumPy 2.3.5, mpmath 1.3.0. All 13 tests passed on the first run. The older 17-test residual/geometric suite has its own earlier validation record in CHECK_LOG.md; it was not rerun as part of this continuation.

The new checks cover analytic reference derivatives, the nonsmooth support-area formula, independent curve-area versus affine-minus-squares evaluation, the first-variation certificate, the exact deficit identity, retention of curvature atoms, local core monotonicity, a negative nonlocal rectangle control, the omitted-wedge height bound, terminal-strip exclusion, endpoint height positivity, and the invalid intermediate-width shortcut.

The independent reference evaluation gives

    Q(xi_G)=2.2195316688719657.

Two deliberately nonsmooth competing triples are checked: a rectangle with vertical sides, and a polygonal approximation to Gerver with explicit cut-normal atoms. Their auxiliary bodies are feasible segments, not optimized canonical bodies. The low Q values below are therefore not numerical approximations to the moving-sofa optimum.

| Check | Rectangle triple | Gerver-like polygon triple |
| --- | --- | --- |
| Q | 0.843184553978424 | 1.22475675334936 |
| Reference dual derivative | -0.022407250174868623 | -0.09797076415801315 |
| Difference-square energy | 1.353939864718679 | 0.8968041513645761 |
| First-variation identity error | 6.95e-15 | -3.29e-14 |
| Exact deficit identity error | -6.00e-15 | 1.64e-14 |

These floating-point tests check signs, constants, and implementation consistency. They do not establish the continuous statements by sampling.

The locally tested source has Git blob SHA

    5853d41f767b15ae1a6fdf75e71691b88239cfae

and SHA-256

    1c9a3e786cf881d3d25b6a8551f168069f55eaacf00018a5cd2e4e1e6c2ad03f.

The Git blob SHA was compared with the file fetched back from the branch and matched exactly. No test or solver failure was discarded in this continuation. The failed zero-tolerance endpoint test from the earlier stage remains recorded in CHECK_LOG.md.

## 5. Review priorities before publication

The manuscript already supplies the reference geometry, optimality, uniqueness, and the no-rotation/width lemmas. The genuinely new review targets are the nonsmooth extension of the first-variation certificate, the local three-region area bound, and the terminal-strip versus endpoint-window comparison. The final recovery and compactness steps are written out rather than left as an implicit regularity argument.

No new theorem has been formalized in Lean during this work. Including the additions in a paper whose abstract says that every proof is kernel-checked requires either formalization or an explicit revision of that scope statement. The proof branch remains a draft for this reason and for independent mathematical review, not because an injective-envelope assumption remains in the unrestricted theorem.
