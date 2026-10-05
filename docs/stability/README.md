# Stability of Gerver's sofa: completed written proof

**Status:** a completed analytic argument for unrestricted square-root stability, with local formula checks. It is **not Lean-checked or independently reviewed**. The new proof is in [notes 05--09](08-unrestricted-theorem.md); [COMPLETION_REVIEW.md](COMPLETION_REVIEW.md) records the dependency audit, rejected shortcuts and validation. This branch remains draft for mathematical review and formalization.

The work starts from `paper/uniqueness-arxiv` at `51c9be18d5b50d45561bfb93cb82d1aabca549bc`, preserving the incorporated alternative optimality route. It is separate from numerical-discovery PR #6. All changes are under `docs/stability/`. No CI, Lean build, or TeX compilation was run. Every commit carries `[skip ci]`; existing Lean libraries, audits, workflows and manuscript verification claims are unchanged.

Write M=area(G), K_G for Gerver's cap, A(K)=area(K)-area(N(K)), and d_rig for Hausdorff distance modulo orientation-preserving rigid motions.

## Main theorem: no injectivity or envelope hypothesis

There exist C,C_area,epsilon0>0 depending only on Gerver's sofa such that every moving sofa S with epsilon=M-area(S) in [0,epsilon0) can be aligned to satisfy

    d_H(S_hat,G) <= C sqrt(epsilon),
    area(S_hat symmetric_difference G) <= C_area sqrt(epsilon).

These are distances between the actual closed sets, not merely their convex hulls. No smoothness, curvature-density, injectivity, monotonicity, or special-envelope assumption is imposed on S.

In the manuscript's initial-horizontal-strip convention a **translation alone suffices**, pinned by

    h_S_hat(pi/2)=1,     h_S_hat(pi)=h_G(pi).

For any admissible reduced rotation angle omega in [omega0,pi/2], sufficiently small deficit also implies

    0<=pi/2-omega<=C_angle*epsilon.

Thus the rotation-angle deficit is controlled linearly, while the shape distance is controlled by its square root. The entry threshold epsilon0 is obtained through compactness and uniqueness and is not asserted to be effectively computed. The global constants are not the same as the explicit cap residual constant below.

**The exponent 1/2 is optimal for unrestricted Hausdorff stability.** Removing an open interior disk of radius r gives a closed connected moving sofa S_r with

    M-area(S_r)=pi*r^2,     d_rig(S_r,G)=r.

The proof includes minimization over rigid alignments. This does not establish sharpness for symmetric-difference area or for the monotone-cap subclass.

## Where the missing step was closed

A cap can be arbitrarily close to Gerver and still fail Ki, for example by having curvature atoms. The proof does not try to promote qualitative closeness to injectivity. It instead replaces that requirement with two new local arguments.

**The nonsmooth deficit certificate.** [05-nonsmooth-certificate.md](05-nonsmooth-certificate.md) enlarges the algebraic triple domain to arbitrary normalized convex caps, keeping the linear wall and body-inclusion constraints. It proves an explicit affine-minus-squares identity that includes curvature atoms. The first variation at Gerver is rederived with only the reference shape differentiated. This yields the exact identity

    M-Q(xi)=nonnegative dual slack + E_all,

where E_all is half the sum of six integrals of squared tangent-displacement differences. Dropping the two auxiliary-body squares controls the cap residual energy without regularizing flat auxiliary directions.

**The local geometric area bound.** [06-local-upper-bound.md](06-local-upper-bound.md) proves A(K)<=Q(xi_K) for every normalized right-angle cap in a fixed neighborhood of Gerver, not just Ki caps. The core remains a Lipschitz graph with strictly decreasing horizontal coordinate; cut separation, canonical-body contacts, and niche containment are established independently. All derivative statements for the competing cap are almost-everywhere statements.

**The missing final angles.** [07-terminal-angle-loss.md](07-terminal-angle-loss.md) proves, for a sofa S obeying the hallways up to omega and its terminal strip,

    area(S)<=A(K)-c*(pi/2-omega).

A fixed left-wing floor rectangle is lost to the tilted terminal strip. The omitted end-angle wedges lie in a strip of height O(pi/2-omega), and their portion not already removed can be confined to arbitrarily short endpoint windows. The rectangle loss dominates that possible gain after choosing the local neighborhood. The proof never asserts that S can complete the final rotation or is contained in the full-angle envelope.

[08-unrestricted-theorem.md](08-unrestricted-theorem.md) assembles these estimates with qualitative entry into the neighborhood, the reference interior-ball property, and a missing-area argument. [09-sharp-exponent.md](09-sharp-exponent.md) proves optimality of the exponent.

## Explicit cap result retained and extended

The exact Green-operator calculation in [01-cap-coercivity.md](01-cap-coercivity.md) gives

    ||h_K-h_KG-s cos||_infinity <= 2sec(phi) sqrt(E_cap),
    s=-(h_K(pi)-h_KG(pi)).

The constant is sharp in the pinned ambient residual space, not claimed sharp over feasible sofas or after minimizing translations. On the reference parameter box,

    2sec(phi)<=2500/1249<2.002.

No numerical fitting or spectral extrapolation enters this calculation. The new certificate extends the Q-deficit version to the enlarged nonsmooth triple domain. The local geometric bound extends the A-deficit version to all normalized caps sufficiently close to Gerver.

The previous polygonal optimizer outputs are **not automatically certified continuous feasible triples**. Although curvature atoms are now permitted analytically, their between-node wall constraints and roundoff still require certification. Substituting an unchecked discrete Q value into the continuous bound remains invalid.

## Reading order and history

Start with [08: the full theorem](08-unrestricted-theorem.md) for the statement and assembly, then review [05: algebra](05-nonsmooth-certificate.md), [06: local geometry](06-local-upper-bound.md), and [07: terminal-angle loss](07-terminal-angle-loss.md). The sharpness result is [09](09-sharp-exponent.md).

The earlier three notes remain as their original proof developments:

- [01-cap-coercivity.md](01-cap-coercivity.md): exact four-residual estimate and original Ki application.
- [02-global-qualitative.md](02-global-qualitative.md): compactness of normalized canonical-hallway descriptions and qualitative stability for arbitrary sofas.
- [03-nonconvex-recovery.md](03-nonconvex-recovery.md): local Lipschitz continuity of the cap-to-sofa map, reference interior balls, and the earlier conditional recovery theorem.

Their concluding descriptions of a then-missing unrestricted rate are historical and are superseded by notes 05--08. Their individual proofs and narrower theorems are retained, not erased. [04-completion-plan.md](04-completion-plan.md) records the route before its lemmas were proved. The sequence of commits preserves this progression.

## Verification and reproducibility

    python docs/stability/check_completion.py

All **13 new tests passed on the first run**, in Python 3.13.5 / NumPy 2.3.5 / mpmath 1.3.0. They include independent curve-area versus square-decomposition checks on polygons with vertical and cut-normal atoms, and the extended first-variation and exact deficit identities. The first-variation discrepancies are at most 3.29e-14 in the two recorded controls. No optimizer is used in these checks. The tested source's Git blob hash matches the committed file.

The earlier suite is run separately with

    python docs/stability/check_stability.py

Its **17 passing checks** and initial endpoint-roundoff failure are recorded in [CHECK_LOG.md](CHECK_LOG.md) and [checks-summary.json](checks-summary.json). That older suite was not rerun during the completion continuation. The new checks are recorded in [COMPLETION_REVIEW.md](COMPLETION_REVIEW.md). None of these tests is a formal proof or interval certificate.

## Manuscript integration and remaining verification work

[paper-section.tex](paper-section.tex) is the **earlier, pre-completion** proposal containing cap stability and qualitative sofa stability. It does not yet include the unrestricted theorem. It remains deliberately excluded from `docs/paper/main.tex`; the completed proof notes can now guide a revised stability section.

Before including these additions in a paper that says all its proofs are kernel-checked, either formalize them or explicitly revise the abstract and formalization-scope statement. Independent scrutiny should focus on the nonsmooth first-variation extension, the local three-region area bound, and the terminal-strip comparison. The mathematical reduction is written out; the remaining work is verification, formalization, and manuscript integration, not an assumed injective-envelope lemma.

No boundary-Hausdorff theorem is claimed: a tiny interior hole can add a boundary component far from the outer boundary while the closed sets themselves remain close. No globally explicit numerical constant, effective entry threshold, certified optimizer output, or best symmetric-difference exponent is claimed.
