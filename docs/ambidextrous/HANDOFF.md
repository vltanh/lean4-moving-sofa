# Ambidextrous sofa research — current handoff

**Neither the unrestricted full-turn area theorem nor unrestricted optimality is closed.** The latest uploaded partial-turn package has been audited. Its useful corner localization now has a smaller, hand-proved circular allowance. This links partial turns quantitatively to full-turn signed fibers, but does not supply the sharp margin or a connected completed competitor.

Repository: `vltanh/lean4-moving-sofa`.
Branch: `research/ambidextrous-pen-and-paper`.
Draft PR: #3, base `main`.
Latest substantive review before this handoff: `8a0eb2c2bb4fba0481f1a2db59d69e43ff8f8420`.
Always query the live tip and preserve intervening edits. Do not reset the PR base to the historical paper branch.

## 1. Scope and execution policy

The full-turn sharp area inequality remains the main task. The user authorized review of the new partial-turn package specifically to test whether it bridges the two frontiers; the new CC/IC work does that, not an unrelated partial-turn optimization campaign. Unrestricted uniqueness is deferred.

Prioritize pen-and-paper proofs. New calculations must be short: at most 30 seconds per invocation, preferably five/ten-second limits. The original package replay uses a ten-second subprocess limit; the new exact checker uses five seconds. **No CI, Lean/Lake compilation, dependency installation or manuscript build.** Commit substantive positive and negative findings with `[skip ci]` under `docs/ambidextrous/`.

All research proofs here are written and self-reviewed, not independently refereed or kernel-verified. A script checking identities does not verify a continuum theorem. Never treat floating-point hull-vertex retention or sampled positive fibers as a complete motion certificate.

## 2. Latest input and audit

Read [partial-turn-package-audit.md](partial-turn-package-audit.md), [circular-corner-completion-bound.md](circular-corner-completion-bound.md), and [partial-turn-replay-review.md](partial-turn-replay-review.md).

The user supplied `partial-turn-completion-package.zip`, SHA-256 `03dffee9b89a6cecb359b8b5c49d6284952f466bc34f7a3a21ceaa28636b1a81`. The archive and its original author output are preserved unchanged in the reproduction bundle; the audit lists all four original file hashes. Attribution is to the supplied package. No author name was supplied.

Its useful PC arguments are:

- transport the incoming orientation along a safe-strip component;
- localize missing late-quadrant material to one corner of the two supporting strips;
- retain signed full fibers and add an explicit completion allowance.

Qualifications found in review: completing by deletion need not preserve connectedness; signed full-fiber area is not ordinary full-envelope area when fibers are empty; PC3 inequalities do not prove exact endpoint equality; its sampled near-reference family is not certified; and literal universal PC6 needs a competitive/small-deficit scope. An exact disk example disproves the original triangular-margin PC6 if read as applying to all angles and all areas. It does not refute the intended competitive version.

## 3. New hand theorem CC: exact circular-corner allowance

Let L=pi/2, alpha=L-epsilon, and 0<epsilon<L. In the two supporting unit strips, translate their lower intersection to A=(0,0). Their upper intersection is D=(k,1), where k=tan(epsilon/2). The lower cone is spanned by e_1 and n_(alpha+L). Its two tangent points to the unit circle centered at D are E=k e_1 and F=k n_(alpha+L).

All missing first-wall violations lie in triangle AEF. Inside this triangle the normal maximizing (D-z) dot n_t lies in [alpha,L], so the exact relaxed violation region is its part outside the unit disk centered at D. Its area is

$$\boxed{\lambda(\varepsilon)=\tan(\varepsilon/2)-\varepsilon/2.}$$

This replaces PC's larger allowance tau(epsilon)=k^2 sin(epsilon)/2. Their difference is exactly (epsilon-sin(epsilon))/2. Thus lambda=epsilon^3/24+O(epsilon^5), while tau starts at epsilon^3/8. The circle calculation works without PC's auxiliary epsilon<pi/3 convexity estimate.

This is sharp for the first-wall/two-strip relaxation, not a claim that every point of this region can simultaneously belong to an actual feasible two-turn body.

With two missing angles and actual hull caps, define

$$\ell_{vis}=1-\max(d_U,n_V^{vis})-\max(d_V,n_U^{vis})\ge0,$$
$$\ell=1-\max(d_U,n_V)-\max(d_V,n_U),$$

where n_U,n_V are full niches and d_U=1-A_U,d_V=1-A_V. Then

$$\ell_{vis}=\ell+\xi_-+\xi_+,$$
$$0\le\int\xi_-\le\lambda(\varepsilon),\qquad
0\le\int\xi_+\le\lambda(\varepsilon').$$

Consequently CC2 proves

$$\boxed{|S|\le\int_I\ell+\lambda(\varepsilon)+\lambda(\varepsilon')
\le |E_{full}(K)|+\lambda(\varepsilon)+\lambda(\varepsilon').}$$

The latter inequality is weaker, not an equality of signed and ordinary areas. Put Z=integral(-ell)_+ and Xi=integral(xi_-+xi_+). Then exactly

$$|E_{full}|=\int\ell+Z,\qquad |E_{vis}|-|E_{full}|=\Xi-Z\ge0.$$

AS gives integral ell=C-R by pointwise algebra. In general C-|E_full|=R-Z, not R. The transfer has no curvature, common-face, weighted-maximizer or Gerver input.

Using the earlier TE endpoint certificate only for a numerical range gives k<=21/79, lambda<=approximately 0.006008415 per turn, instead of PC's approximately 0.017543826. A purely rational upper bound on their sum is 6174/493039. TE is not required for the geometric theorem.

## 4. New exact non-completion example IC

[IC1](exact-in-place-completion-obstruction.md) proves that

$$T=\operatorname{conv}\{(0,0),(1/10,1),(-1,20/99)\}$$

has a lower turn through alpha=L-2 arctan(1/10), and a full upper turn, but fails a missing lower angle t_*=L-arctan(1/10). Its area is 101/198. Both support depths at (0,0) exceed one at t_*, so an open positive-area piece is deleted by completion.

The all-angle proof uses a two-affine-depth edge calculation and one explicitly factored rational polynomial. It is independent of the original PC numerical family. The example proves only that zero-loss **in-place** completion is not universal, even at a small missing angle. It is not competitive, does not preclude another incoming orientation, and does not establish near-M non-completable bodies.

## 5. The exact unresolved target

For actual full-turn caps with nonempty fibers,

$$|E|=\Psi(U)+\Psi(V)+G,\qquad
\Delta(U)=M/2-\Psi(U),$$
$$\Delta(U)+\Delta(V)-G=M-|E|.$$

Thus the universal clipping inequality is exactly the full-turn optimality claim, not an independently established lemma. The stronger AS aggregate inequality C<=M also remains unproved globally. The reference value is

$$M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.$$

The new partial-turn bridge needs a margin, for example

$$\int_I\ell\le M-\Xi,$$

or the stronger condition with Xi replaced by lambda(epsilon)+lambda(epsilon'). That margin has not been proved. A completed full-turn set can be disconnected; bounding each connected component by M would not bound their total area by M. Even a total-area bound by M without a negative margin leaves the positive completion allowance unpaid.

Therefore do not announce that a full-turn theorem automatically settles partial turns through CC. It would need the appropriate stronger-domain margin or a separate feasible component/area-preserving completion argument.

## 6. Earlier infrastructure retained, with its real boundaries

**WV2** is the existing written weighted-cap theorem sup Psi=M/2. Its PA/WP/WR/AR/PT/TS/EB/TF/HF/CG/SE/VE chain retains its independent-review limitations. In particular an arbitrary two-turn cap is not a weighted maximizer. The recent CC/IC proofs do not use this chain.

**FAS and RS2** cover aligned positive-face full-turn bodies and the specified left-right symmetric actual unit-span class. RS2 is not a theorem for arbitrary subunit-span symmetric envelopes. **RR/PD/PS** reduce the full-turn supremum to saturated positive opposite-end faces; that subclass need not attain its supremum and has no uniform gap below M.

**TC/MT/ME/CT/CB** pay clipping on admitted regular-background/rough-tail domains. General admission, output-face compatibility, half-height geometry and regular-middle hypotheses remain unproved. **CGA** disproves unconditional common-face half-height-niche admission on the entire full-turn class, but not competitive-only admission. **NM** shows half-height rectangle failure in near-reference actual full-turn bodies, so closeness alone does not supply it.

**HS** proves a positive convex-hull symmetrization energy. It does not pay the extra forbidden area or prove connectedness of arbitrary symmetrized envelopes. Near-reference cuts show that the leading hull gain is spent on forbidden material and that unit vertical span can drop linearly while area changes only in three-halves order. **AN** disproves the simple area-preserving affine unit-span normalizer and gives the exact full-turn rectangle bound area<=1.

**AS/SPB** are valid ordinary-area relaxations with exact nonnegative mismatch formulas on actual nonempty fibers. Their sharp maxima are unproved. The new CC makes signed-versus-positive-part accounting explicit for partial hulls; it does not maximize these expressions.

Keep the earlier negative controls RA, MCA, AF4, GR1, AX1/SAT1, SAC2, SC3, TR1, AO1, FF and HC. Saturation, repair, averaging, face filling, reference proximity and support energy do not automatically imply ordinary-area enclosure. AM/TE are scoped exact certificates, not a complete global covering.

## 7. Reproduction and restart

The unchanged original PC checker finished in 2.35 seconds under ten seconds and reproduced its author output, including the impossible negative approximate completion loss at epsilon=0.02. The corrected missing-angle-only replay finished in 2.90 seconds. It adds no samples inside already visited angles; all four approximate completion losses are nonnegative and below the circular allowance. These are still not certified values or continuum feasibility proofs. A rejected union-grid trial is preserved and explained in the replay review.

The exact CC/IC checker ran in about 0.155 seconds under five seconds: one coefficientwise identity, 7,290 triangle point/frame tests, 147 tangent tests, 462 cone tests, and 934 signed-fiber cases, including 621 negative signed full fibers. The executed source matches Git blob `a9069ce6e3fedfa4301ef1434e6012b37ac1f1b0`. The replay wrapper matches blob `bbf5a43340388f5bec248bf94e39ce32845426d8` and validates the archive and original script hashes before execution.

Read this handoff, the current roadmap and the CC/IC proofs before using the new bridge. If review finds a specific incorrect implication, repair that implication rather than weaken hypotheses silently. The main missing work remains a sharp global ordinary-area comparison and its completion margin. No closure or imminent-completion claim is justified by the new local loss bound. PR #3 remains open and draft.
