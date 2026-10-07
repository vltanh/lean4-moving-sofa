# Active roadmap: the general minimum-width slack inequality

**Unrestricted full-turn and partial-turn optimality remain unproved.** The new uploaded minimum-width package supplies a useful frame and an exact signed correction. New SM/SB hand results establish a sharp area margin and same-body partial completion on the explicitly specified near-unit reference-scale hull class. No theorem places arbitrary competitors or maximizers in that class. Uniqueness remains deferred.

Read [HANDOFF.md](HANDOFF.md), [minimum-width-package-review.md](minimum-width-package-review.md), [minimum-width-frame.md](minimum-width-frame.md), [scaled-reference-slack-margin.md](scaled-reference-slack-margin.md), and [scaled-reference-safe-strip-bridge.md](scaled-reference-safe-strip-bridge.md). All proofs retain their self-review and dependency limitations.

## 1. Goal and execution policy

The goal remains the ordinary-area inequality |S|<=M, where

$$M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.$$

Prioritize hand proofs. Use short computations to check algebra or reject a precise proposed implication; at most 30 seconds per invocation, preferably five/ten-second external caps. **No CI, Lean/Lake compilation, dependency installation or manuscript build.** Commit substantive positive and negative findings with `[skip ci]` under `docs/ambidextrous/`.

The full-turn comparison is the main work. The supplied partial/minimum-width packages authorize directly related angle-coverage review, not an unrelated search campaign. A result on a family is not global closure; a script verifying scalar identities is not a continuum certificate.

## 2. Proved frame and exact remaining area budget

For an already full-turn body, SI2 permits a change of incoming normal inside its connected safe-strip component. Minimize width within that component, giving actual span 1-s. Rotate and translate into s<=y<=1 without stretching. MF1 proves the horizontal top and bottom face intervals overlap. Other safe components may exist; no global claim w>1 outside the chosen component is made.

For actual hull roof A and floor B, define the height-one downward caps with roofs A and 1+s-B and full niche roofs n_U,n_V. Their nonempty-fiber canonical envelope satisfies

$$|E|=\Psi(U)+\Psi(V)+G_s,$$

$$G_s=\int[\min(n_U,B)+\min(n_V,1+s-A)]-sW=T_s+C_s-sW,$$

where T_s is the sum of the two niche areas below the actual body levels and C_s>=0 is the remaining clipping above those levels.

The universal target is

$$\boxed{T_s+C_s-sW\le\Delta(U)+\Delta(V),\quad\Delta=M/2-\Psi.}$$

This is still equivalent to the missing full-turn value bound on actual compatible pairs. Overlap is useful but does not prove matching faces, centrality, a small niche footprint or a nonpositive G_s.

Under the package's explicit central-face conditions, MF3 makes C_s=0. Then a sufficient condition is T_s<=sW; a stronger convenient condition is that the two niche footprint lengths total at most W. Neither is established globally. At s=0, nondegenerate overlapping faces fall into FAS; end-point-face configurations remain.

## 3. The package's reference-scale phenomenon now has a hand proof

SM1 studies K_s=(1-s)K_*+(0,s), 0<=s<=1/64, and its **whole** canonical full-turn envelope E_s. A known scaled reference sofa inside it proves connected full-turn feasibility and actual hull equality. A contained face rectangle proves its vertical direction is the minimum-width normal.

The height-one caps have top-face length W/2 and open-quarter curvature at most one. Thus their niches stay within the top face and

$$G_s=-2\int_{J_s}(s-n_s)_+.$$

The two endpoint circular regions have inner radius R=(1+s)/2. Global first-wall monotonicity and elementary integration give

$$-G_s\ge\Gamma(s)=(1+s)^2\arctan\sqrt{s}-(1-s)\sqrt{s}\ge\frac83s^{3/2}.$$

With the admitted regular-cap SR/AF comparison,

$$\boxed{|E_s|\le M-2\Delta_s-\Gamma(s)\le M-\frac83s^{3/2}.}$$

This turns the numerical power-law observation into an explicit signed area margin. It does not rely on WV's maximizing-cap exposure chain or Gerver's area bound, but it does retain the existing written SR/AF dependency. It is not a complete neighborhood theorem: middle facets and arbitrary asymmetric perturbations are outside the fixed reference-scale family.

## 4. The corresponding partial-to-full bridge is exact on that class

SB1 proves that for those same hulls the entire safe-strip set modulo pi is

$$[L-\eta_s,L+\eta_s],\qquad\eta_s=\arcsin\bigl(s/((1-s)m)\bigr).$$

The exact width near vertical is (1-s)(1+m sin(delta)); a contained rectangle excludes every other direction. All incoming/outgoing strip normals of any conventional partial-turn pair with such an actual hull lie in the same component. SI therefore completes both turns for the same body without area loss, and SM supplies the bound above.

This closes both questions on hulls congruent to k K_* with 63/64<=k<=1. It does **not** establish that all competitive partial-turn bodies have a connected safe-strip bridge. No comparison of asymptotic exponents is substituted for angle coverage.

## 5. General partial turns still require a margin or safe completion

The earlier uploaded PC package and reviewed CC theorem give the cubic allowance

$$\lambda(e)=\tan(e/2)-e/2=e^3/24+O(e^5).$$

With visited and full signed fibers one has ell_vis=ell+xi_-+xi_+ and integral xi_-/+ bounded by the two allowances. Empty full fibers require Z=integral(-ell)_+. Completion by deletion can disconnect the body; a bound on each component does not bound their total area by M.

Thus a global full-turn theorem alone does not pay the positive completion allowance. A sufficient larger-domain inequality is integral ell<=M-integral(xi_-+xi_+), or a stronger uniform allowance budget. This remains unproved. The minimum-width frame starts with full turns; it cannot be used to manufacture missing orientations outside a verified safe component.

## 6. What not to infer

- The reference-scale class is not all nearby hulls, nor the whole PD/PS positive-opposite-face supremum class.
- G_s need not be assigned a nonpositive sign merely because -sW occurs in its identity. Above-slab clipping and excessive footprint remain possible.
- Arbitrary cap regularity, background face compatibility and a half-height rectangle are not supplied by the new frame.
- No actual-body symmetrization or affine rescaling theorem has been proved; HS/AN/NM and earlier repair/averaging counterexamples remain relevant.
- WV2, FAS, RS, SR/AF and the older geometric reductions retain their stated domains and independent-review limitations.
- The stronger AS aggregate upper bound and the ordinary full-turn inequality are not identical optimization targets.

## 7. Validation record and next implication

The original minimum-width checker was replayed unchanged under an eight-second cap, reporting 1.86 seconds. Its 200 Fraction samples and prescribed numerical pattern passed; its author output was preserved. The proof-table mesh and supplied executable mesh differ, as recorded in the review.

The new checker ran under five seconds in about 0.093 seconds, with 4,900 exact scalar-fiber and 33 circle/series cases. Its source blob is `ce6b327750f70e5bd92163f56087e07617a54b90`. Numerical comparisons to Gamma have errors of both signs near 10^-8; they are not rigorous upper/lower bounds. Neither program proves geometric admission.

The next global mathematical implication is control of T_s+C_s-sW by the two actual cap deficits outside the central/reference-scale cases, or another ordinary-area comparison with all hypotheses verified. Do not spend another pass re-proving a reference family merely to increase the theorem count. The new exact family margin is useful evidence for a mechanism, not a completion claim. PR #3 remains open and draft.