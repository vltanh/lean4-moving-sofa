# Ambidextrous sofa research — start a new session here

**Unrestricted optimality is not proved.** The newest hand proof pays the actual clipping term for a stated tail-window class. It bounds full canonical saturation after arbitrary independent convex shavings in two explicit reference boundary layers, and has a signed extension permitting some outward changes. The middle supporting data remain fixed in these theorems; no global neighborhood/admission theorem has been proved. Unrestricted uniqueness is deferred.

Repository: `vltanh/lean4-moving-sofa`.
Branch: `research/ambidextrous-pen-and-paper`.
Draft PR: #3; base: `main`.
Latest substantive review before this handoff: `913cf63e43d7c41765d888c309ae916b07a6dc6f`.
Always query the live tip and read intervening commits. Do not reset the PR to the old paper branch.

## 1. Instructions and status of verification

Prefer pen-and-paper proofs. Use only short computations to check explicit algebra or reject a proposed step: no more than 30 seconds per invocation, preferably external five/ten-second limits. No long optimization or repeated refinement without a new instruction. **No CI, Lean/Lake compilation, dependency installation or manuscript build.** Commit substantive positive and negative findings with `[skip ci]`, under docs/ambidextrous. Refresh current blob SHAs and preserve concurrent edits.

All mathematical arguments are written and self-reviewed, not independently refereed or kernel-verified. The old weighted-value chain has not been independently audited. The latest proof review is [tail-pairing-review.md](tail-pairing-review.md); the earlier global reduction is reviewed in [positive-face-density-review.md](positive-face-density-review.md).

The explicit reference has

$$M=1+4Y^2+\arctan Y,\quad4Y^3+3Y-1=0,\quad Y>0.$$

In centered coordinates its horizontal extent is [-m,m] and its two horizontal faces are [a,b]=[-m/2,m/2], where m=1/(3 sin(beta)), beta=arctan(Y), and 1<m<4/3. The signed cap objective remains

$$\Psi(U)=|U|-|N(U)|-W(U)/2,$$

with the **entire** positive-height niche subtracted.

## 2. New direct clipping budget: TC/RB/STW

Read in order:

1. [tail-paired-cut-deficit.md](tail-paired-cut-deficit.md);
2. [reference-belt-saturation-bound.md](reference-belt-saturation-bound.md);
3. [signed-tail-window-comparison.md](signed-tail-window-comparison.md);
4. [tail-pairing-review.md](tail-pairing-review.md).

These results do not use the weighted-maximizer theorem WV, its source-flux limit, or Gerver's upper bound. They use only the explicit reference cap, its active circular tails, and its known reference area.

### The paired inequality

The right inner tail at b-d and outer flank at b+d are circles of radius one half. At t=pi/2-arcsin(2d), a support defect u(t)=h_*(t)-h_U(t) yields

$$n_*(b-d)-n_U(b-d)\le u(t)/\sin t\le A_*(b+d)-A_U(b+d).$$

The left inequality is a *lower test* for the new niche at a known reference angle, with its companion wall checked. It does not say that angle is the new maximizing angle. The right inequality is the cap's outer supporting-line bound. Pairing d with d preserves horizontal measure.

Outside those inner tails, an unchanged reference wall pair retains the old niche value (or gives a favorable inequality in the signed extension). Thus niche savings are paid by outer-flank losses. Convex cap material missing below the old horizontal face is left as a separate budget:

$$\boxed{\Delta(U):=M/2-\Psi(U)\ge\int_a^b(1-A_U(x))dx.}$$

For two independent admitted caps U,V, both niche projections lie in (a,b), so

$$G\le\int_a^b(1-A_U+1-A_V)dx\le\Delta(U)+\Delta(V).$$

Their fibers contain y=1/2, and the exact ordinary-area identity gives |E|<=M. This is the correctly signed clipping comparison on the stated domain, not an auxiliary maximum alone.

### A concrete geometric theorem

RB chooses eta=2 arctan(1/10), cos eta=99/101 and sin eta=20/101. If a convex K satisfies

$$\boxed{K_*\cap\{1/101\le y\le100/101\}\subseteq K\subseteq K_*,}$$

then its full canonical two-turn envelope E(K) is compact, connected, feasible and has area at most M. It may recover material outside the original cut reference; this is not just a subset-area argument. The proof does not assume conv(E(K))=K.

Arbitrary independent affine cuts are admitted if their upper lines `y<=1-e_i-s_i x` and lower lines `y>=e'_j+s'_j x` obey `e_i+m|s_i|<=1/101` and `e'_j+m|s'_j|<=1/101`. In particular the two left-tip cuts with independent slopes tau_+,tau_- are covered for `0<=tau_+,tau_-<=2/(303m)`. Faces can collapse or change differently.

For a separately given S, inferring S subset E(K) retains the **full-turn** premise. RB does not silently extend a partial motion.

### Signed extension

STW allows caps not contained in the reference. It requires:

- the full half-height rectangle inside the cap and height at most one;
- equality with reference upper supports outside `(pi/2-eta,pi/2+eta)`;
- the barrier `h_U(theta)<=1+(m/2)|cos(theta)|` inside that interval.

The allowed outward first-wall displacement is at most 1/99, while the unchanged companion gap is at least 19/8. Thus the paired inequality survives with **signed** support and area differences. The new niche still lies beneath the old face and below half height. Two such independent caps satisfy the same clipping budget and area bound.

Nonzero smooth outward support bumps compactly supported in the window are explicitly admitted for small enough amplitude. This does not permit arbitrary middle-arc changes. The current theorem is not a full Hausdorff or C1 neighborhood theorem, and PD does not put an arbitrary competitor in this reference-based domain.

## 3. The full-turn supremum reduction remains the global target

[RR](rounded-strip-regularization.md) rounds a uniformly shrunken body by `r=(1-lambda)/2`, preserving every already feasible canonical hallway by the depth inequality `lambda+2r=1`. Its width is `lambda w+1-lambda`, so it preserves the safe-strip set exactly.

Shaving less than r off two supporting planes leaves every disk center. The union of the clipped disks remains connected and has positive face chords. [PD](full-turn-positive-face-density.md) chooses an increasing record width near a safe-strip boundary, shaves sufficiently little, and shrinks again to make the whole bridge safe. SI transports full motions to the new unit-span direction. The resulting positive faces are strictly separated, and areas tend to the original area from below.

For competitive widths, FD puts these faces in opposite unit end strips. PS1 permits full same-hull saturation without decreasing area. Therefore

$$\boxed{\sup_{\rm full-turn}|S|=\sup_{\rm saturated\ positive\ opposite-face}|S|.}$$

This removes literal point faces as a separate upper-value obligation. It does **not** prove the restricted supremum is attained. Its face lengths may tend to zero along an extremizing sequence.

Applied to the reference, PD gives positive opposite-face bodies with areas below M tending to M. Thus a uniform strict gap below M on the whole remainder is impossible, even if saturation is required. TC/RB/STW cover a defined part of this sharp geometry, not the entire remainder.

## 4. Partial turns remain separate

[SI3--SI4](strip-interval-completion.md) convert the same partial-turn body to full turns if the entire interval of required outgoing strip normals has width at most one. A genuine width bump in that interval remains unhandled. Three individually safe normals do not imply a safe bridge.

RR preserves the old safe-strip set, and PD starts with full turns. The new reference-belt envelope is itself full-turn feasible, but no argument says an arbitrary partial-turn S is contained in that smaller envelope. These hypotheses must remain explicit.

## 5. Earlier written upper-value results

**WV2:** `sup Psi=M/2` on normalized full-right-angle caps. The proof goes through PA/WP/WR, AR/PT/TS/EB, TF/HF, CG/SE and VE/WV. SE uses the established ordinary Gerver theorem on an actual one-turn body. VE's limiting two-source flux argument remains a principal independent-review point. New TC/RB/STW do not rely on this chain.

**FAS1:** every full-turn unit-span body with identical positive top/bottom faces has area at most M, with no minimum positive face length or curvature premise. SCG/CSF give sufficient retained-point criteria forcing full turns as well; FL/LF cover long faces.

**FD/UC:** at width greater than two, positive full-turn faces align or occupy opposite unit end strips. A point face cannot be central: the switching argument forbids a retained unit vertical chord with flanks longer than one on both sides.

**RS2:** left-right reflection symmetry in the common incoming representation supplies complementary hallway angles and then the aligned-face area bound. This does not prove existence of a symmetric unrestricted maximizer.

**Width/angle inputs:** analytic AW-W/SW exclude competitive width at most 1001/500; AL1 gives width at most 2999/1020. AM2 and TE1 retain their scoped computer-assisted exclusions, not a global sharp covering. They are not proof inputs to TC/RB/STW.

## 6. Failed substitutions and bounded exploratory work

RA1 rejects naive averaging of actual nonconvex bodies. MCA1 rejects the analogous convex-cap averaging enclosure, including on near-reference double cuts. AF4, GR1, AX1/SAT1, SAC2, SC3, TR1 and AO1 remain mandatory negative controls. Repair, saturation, data admission or closeness alone do not imply the ordinary-area comparison. Canonical-wing accounting keeps negative winding and uncovered surviving material.

The new [face-filling-budget-obstruction.md](face-filling-budget-obstruction.md) rejects an unqualified finite top-filling rule. Filling the top interval of a downward half-disk cap creates a square with a positive niche. Its signed-objective gain is strictly smaller than the convex cap-area gain. This is an exact counterexample to that intermediate filling inequality, not to TC's restricted final deficit bound.

A narrower filling conjecture was tested on 12 prescribed cuts and 32 prescribed convex-hull point sets, all under five-second limits. No sampled violation occurred. That is inconclusive, not a theorem or a global search result. It is not used in any new proof. The scripts and outputs are preserved in the session bundle.

## 7. Exact checks actually run

`computer-assisted/check_tail_pairing.py` ran under an external five-second cap. Its record reports 12 named checks, 72 signed rational line cases, 144 paired-fiber identities and three sign/hypothesis controls. Internal time was about 0.0064 seconds. Executed source matches Git blob `e9b0beab8b786664f245100a9ac3d70b153f3c33` and the SHA-256 in `tail-pairing-checks.json`.

The samples check algebra and bookkeeping, not complete cap realizability, reference-envelope coverage or the continuum proof. No long search, CI, Lean/Lake compilation, dependency installation or manuscript build was used. Older uploaded packages and author-generated records remain preserved at their provenance checkpoints.

## 8. Next acceptance test

The global task is still a sharp bound on the saturated positive opposite-face class, together with the uncovered partial-turn comparison. The new mechanism pays tail-induced clipping while holding middle supports fixed. A genuine extension must also control changes of the middle supports or prove a separate admission theorem. Repeating `G<=Delta(U)+Delta(V)` without proving those hypotheses is not progress.

A bound for one attained unrestricted maximizer suffices for the value, but do not assign weighted-cap maximality to its two caps. Do not assume the dense positive-face subclass has a maximizing member. Preserve all positive correction terms and full-turn premises. Keep scripts short, findings committed, and verification scope explicit. PR #3 stays open and draft.
