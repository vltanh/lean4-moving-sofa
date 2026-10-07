# Ambidextrous sofa research — current handoff

**The unrestricted full-turn and partial-turn optimality statements are not closed.** The minimum-width package has been reviewed and incorporated. It gives same-body overlap and a signed slack correction, not a universal sign for that correction. New hand theorems SM1 and SB1 close the area and partial-to-full completion questions on the specified reference-scale hull class, not on arbitrary competitors.

Repository: `vltanh/lean4-moving-sofa`.
Branch: `research/ambidextrous-pen-and-paper`.
Draft PR: #3; base `main`.
Latest substantive checkpoint before this handoff: `852a8856a2ce97e03af780963f356568405b02f5`.
Query the live tip and preserve concurrent work. Do not reset the historical PR base or infer closure from its title.

## 1. Execution and review policy

Prioritize hand proofs. Short scripts may check exact identities or reject proposed lemmas; at most 30 seconds per invocation, preferably five/ten-second external caps. **No CI, Lean/Lake compilation, dependency installation or manuscript build.** Commit substantive positive and negative findings with `[skip ci]` under `docs/ambidextrous/`.

The full-turn area theorem remains the main goal. Reviewing the supplied partial/minimum-width packages and proving their directly related bridge is authorized; this is not an instruction to reopen unrelated partial-turn or uniqueness work. All proofs are written and self-reviewed, not independently refereed or kernel-verified. Never equate finite sampled feasibility with a continuous motion certificate.

## 2. Latest package: minimum width without forced rescaling

Read [minimum-width-package-review.md](minimum-width-package-review.md) and the reviewed restatement [minimum-width-frame.md](minimum-width-frame.md), labels MF. The original archive has SHA-256 `21bc2d3b71b1deac325b94faca87d1eaac3d0849a012a0d689049f026f6eeff8`. Original proof, code and author output are preserved unchanged in the reproduction bundle; the review lists their hashes and does not claim independent authorship.

SI2 transports an already full-turn body within the connected safe-strip component containing its incoming normal. At a minimum of width in that component, write the span as H=1-s, and place the actual hull between y=s and y=1. This changes neither shape nor area. Its top and bottom face intervals overlap, by the two one-sided width derivative signs.

Do not say w>1 everywhere outside that component: other components may exist. The review repairs this overstatement, including the singleton/minimum-equals-one edge case. Horizontal width must be recomputed after rotation.

For hull roof A and floor B, the two height-one caps have roofs A and 1+s-B. Their full niches are n_U,n_V. With Psi(C)=|C|-|N(C)|-W(C)/2, the exact ordinary-area identity is

$$|E|=\Psi(U)+\Psi(V)+G_s,$$

$$G_s=\int[\min(n_U,B)+\min(n_V,1+s-A)]-sW.$$

Writing

$$T_s=\int[\min(n_U,s)+\min(n_V,s)],$$

$$C_s=\int[(\min(n_U,B)-s)_++(\min(n_V,1+s-A)-s)_+],$$

one has G_s=T_s+C_s-sW, with C_s>=0. It is **one** negative sW term after the cap penalties, not two. No affine unit-height normalization is needed for the identity.

The package's endpoint tests give conditional O(sqrt(s)) near alignment. Its central-face hypotheses give C_s=0. The further footprint condition beta_U+beta_V<=W gives T_s<=sW and hence the sharp area bound using the existing weighted theorem. Those hypotheses remain unproved globally, particularly for point faces and noncentral geometry.

## 3. New SM1: exact three-halves margin for a full saturation

Read [scaled-reference-slack-margin.md](scaled-reference-slack-margin.md). Let K_* be the centered reference hull, with projection [-m,m] and face length m=1/(3 sin beta). For 0<=s<=1/64 put k=1-s and

$$K_s=kK_*+(0,s),\qquad E_s=E_{full}(K_s).$$

The scaled actual reference k Sigma+(0,s) is full-turn feasible and has hull K_s, so its canonical saturation is connected with the same actual hull. The contained m-by-one reference face rectangle proves the vertical direction is the minimum-width orientation of K_s.

Its two caps agree, have width W=2km and top-face length W/2. Unit open-quarter curvature confines their niches to that face, yielding exactly

$$G_s=-2\int_{J_s}(s-n_s)_+.$$

The scaled inner circular end arc has radius R=(1+s)/2. On each endpoint interval of length sqrt(s), its globally maximizing first wall bounds the niche by

$$n_s(b_s-d)\le R-\sqrt{R^2-d^2}.$$

The intervals are disjoint and inside the exact circular phase throughout s<=1/64, by explicit rational bounds on beta and m. Integration gives

$$-G_s\ge\Gamma(s)=(1+s)^2\arctan\sqrt{s}-(1-s)\sqrt{s}\ge\frac83s^{3/2}.$$

The regular-cap SR/AF comparison gives Delta_s=M/2-Psi(U_s)>=0. Therefore

$$\boxed{|E_s|\le M-2\Delta_s-\Gamma(s)\le M-\frac83s^{3/2}.}$$

This proves the packet's observed favorable three-halves behavior, rather than fitting it numerically. The result controls full saturation, not just the area k^2 M of an obvious subset. Its value bound uses the written regular-cap SR/AF chain, not WV's maximizing-cap exposure argument or Gerver's theorem. It still needs independent review.

## 4. New SB1: no partial-turn obstruction in that same class

Read [scaled-reference-safe-strip-bridge.md](scaled-reference-safe-strip-bridge.md). For K_s above, the entire safe-strip set modulo pi is exactly

$$[L-\eta_s,L+\eta_s],\qquad\eta_s=\arcsin(s/(km)),\quad L=\pi/2.$$

Near vertical, the reference width is 1+m sin(delta). Away from the circular phase, the contained face rectangle gives a lower width exceeding 10/9; scaling by k>=63/64 still leaves it above one. Thus there is one connected safe interval, proved analytically over every angle.

Any pair of conventional partial-turn witnesses with actual hull congruent to k K_* has its incoming and outgoing normals in this component. SI3 and SI2 complete both turns for the same body and transport to the minimum-width normal, without deleting material. SM1 then proves its area <=M-Gamma(s).

This closes both questions **only for actual hulls congruent to k K_*, 63/64<=k<=1**. Rotations and uniform scales are not a neighborhood of arbitrary perturbed support data. The proof does not normalize arbitrary hulls into this class, assume arbitrary motion signs, or establish a global maximizer's shape.

## 5. Earlier partial-turn package and remaining margin

The preceding package has archive hash `03dffee9b89a6cecb359b8b5c49d6284952f466bc34f7a3a21ceaa28636b1a81`. Read [partial-turn-package-audit.md](partial-turn-package-audit.md), [circular-corner-completion-bound.md](circular-corner-completion-bound.md), and [partial-turn-replay-review.md](partial-turn-replay-review.md).

CC improves its triangular allowance to

$$\lambda(e)=\tan(e/2)-e/2=e^3/24+O(e^5).$$

For a connected actual partial-turn body with hull K, its visited fiber lengths ell_vis are nonnegative; full signed lengths ell need not be. The exact relation is ell_vis=ell+xi_-+xi_+, with the two integrated increments bounded by lambda(e),lambda(e'). Therefore

$$|S|\le\int\ell+\lambda(e)+\lambda(e')\le|E_{full}(K)|+\lambda(e)+\lambda(e').$$

The completed set may be disconnected. Its ordinary area is integral ell plus Z=integral(-ell)_+, not just integral ell. Full-turn componentwise bounds do not bound the sum by M. A sharp margin paying the actual completion increment remains unproved in general. The new SB theorem avoids this cost only in its explicitly connected safe-strip class.

IC supplies an exact low-area non-completion-in-place example. The original packet's sampled near-M non-completion family is not a continuum certificate. Neither those tests nor contrasting cubic and three-halves exponents automatically closes the partial-turn theorem.

## 6. Global boundary and earlier results

The full-turn sharp target is still

$$G_s\le\Delta(U)+\Delta(V)$$

on arbitrary actual minimum-width data, equivalently |E|<=M. With central confinement it becomes T_s<=sW+Delta(U)+Delta(V). Point-face endpoint configurations at s=0 and general s>0 have not been covered. A nonpositive G_s, common-face background, footprint bound or regular cap curvature is not a free consequence of being in a minimum-width frame.

WV2 is a written weighted-cap value theorem with its long PA/WP/WR/AR/PT/TS/EB/TF/HF/CG/SE/VE dependency chain; arbitrary two-turn caps are not its maximizers. FAS/RS cover their stated aligned-face or unit-span symmetric classes. SR/AF can be used directly only where their geometric equality is proved. RR/PD/PS reduce the full-turn supremum to saturated positive opposite faces but do not make that class closed or give a strict uniform gap. Minimum-width transport now offers another representation of the same bodies, not a proof that their correction is paid.

TC/MT/ME/CT/CB remain conditional paid-tail comparisons. CGA, NM, HC, AN, HS, the axis-cut/repair examples and the averaging obstructions remain necessary failure controls. In particular the minimum-width idea does not refute the old affine-normalization counterexample: it avoids stretching altogether. AS is an upper relaxation with a correctly specified switching error, but its sharp global maximum remains unproved.

## 7. Executed checks and restart

The original minimum-width checker ran unchanged under an eight-second cap, reporting 1.86 seconds, all 200 Fraction samples passing and the expected five numerical cases/control. Original author output was not overwritten. Numerical area/fiber and face-identification tolerances are not continuum verification.

The new exact checker `computer-assisted/check_minimum_width_review.py` ran under five seconds in about 0.093 seconds, checking 4,900 compatible scalar fibers, 33 circle/series identities and two false stronger claims. Its executed source matches Git blob `ce6b327750f70e5bd92163f56087e07617a54b90`. The committed record includes both signed numerical residuals against Gamma, which are about 10^-8 and not certified error signs.

Restart by reading MF, SM and SB with the review. The next universal obligation is still control of the signed slack correction outside the proved central/reference-scale cases. Do not count a new exact family theorem as global closure or invent a relation between missing angles and slack. Preserve actual hulls, retained endpoints, motion coverage and empty-fiber corrections. PR #3 stays open and draft.