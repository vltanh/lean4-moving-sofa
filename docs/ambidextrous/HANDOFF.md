# Ambidextrous sofa research — start a new session here

**Primary milestone: optimal value only. Unrestricted optimality is not proved.** Uniqueness is deferred. All mathematical results below are written and self-reviewed; the historical chain has not been independently audited.

Repository: `vltanh/lean4-moving-sofa`.
Branch: `research/ambidextrous-pen-and-paper`.
Draft PR: #3; base: `paper/uniqueness-arxiv`.
Last substantive checkpoint before this handoff: `dd3209c622a9a27b6b257d2fae7bf0d082c4600d`.
Always query the live branch head and read intervening changes before using this snapshot.

## 1. Instructions and target

Commit substantial positive and negative findings frequently, using `[skip ci]`. Computer assistance is permitted, but a sampled optimizer, unfinished covering, or unexecuted source is not a certificate. **No CI, no Lean/Lake compilation, no dependency installation, no manuscript build.** Keep work under `docs/ambidextrous/` and preserve concurrent edits. Keep PR #3 draft; closing the mathematical proof is not the same as closing the PR.

The candidate has area

$$
M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.
$$

For the value, a bound on one attained global maximizer suffices. Do not add a requirement to classify every equality case before establishing the value.

## 2. Latest upload: an endpoint-arm reduction

Read [one-turn-arm-package-review.md](one-turn-arm-package-review.md) first, then [one-turn-arm-reduction.md](one-turn-arm-reduction.md). The archive `one-turn-arm-reduction-package.zip` has SHA-256 `a485d55950df0f6a9adf2a752e18ab973fbb883036fb4ae938cd3b0bfaf02302`. Its four mathematical/diagnostic files are preserved byte-for-byte at `0b187ac80852234b65fe9046fc4eaf6cd4d25264`; the audit lists the blobs. The original numerical record is not the fresh replay record.

For the signed one-turn problem

$$
\Psi(U)=|U|-|N(U)|-W(U)/2,
$$

N(U) is the **full** positive-height niche, not clipped to U. Let P=max Psi, whose attainment was proved in PA2. For upper support h, use L=pi/2, f(t)=h(t), g(t)=h(t+L), p=f'-g+1 and q=g'+f-1. If [x_L,x_R] is the cap projection and [x_tl,x_tr] its top face, the endpoint arms are

$$
d_R=x_R-x_{tl}=1+q(0),\qquad d_L=x_{tr}-x_L=1-p(L).
$$

WR1 and the new AR7 imply

$$
q(t)\le\max(q(0),1/8),\qquad p(t)\ge\min(p(L),-1/8).
$$

Consequently **EA2: d_R,d_L<=2** implies unit curvature and then Psi=M/2 by SR1/AF3. For the present value-only target, EA2 for **one attained weighted maximizer** suffices. It is not proved for even one by the current reduction. Establishing P=M/2 still would not eliminate two-turn clipping.

### New finite comparison TS1--TS2

[one-turn-top-shortening.md](one-turn-top-shortening.md) proves, when top-face length T>0, that a cap can be shortened by epsilon in (0,T), with

$$
\Psi(U_{\rm minus})-\Psi(U)
\ge\varepsilon\bigl(H_N(U)-1/2-\varepsilon/2\bigr),
$$

where H_N is its full niche's supremum height. This uses an exact Minkowski inclusion and one-dimensional area growth, not a niche-area derivative.

Therefore **every weighted maximizer with T>0 has H_N<=1/2**. Its half-height rectangle then implies niche containment. Testing two retained points at the rational direction (4/5,3/5) gives **d_R,d_L<=9/4**, not two. The unresolved positive-top arms are confined to (2,9/4] if EA2 fails. **The T=0 case is not covered.**

Such a positive-top weighted maximizer also produces, by reflected intersection, a connected ambidextrous body with ordinary area

$$
|S_U|=2\Psi(U)+2\int\min(n,1-a)\,dx\ge2\Psi(U),
$$

where a is the upper cap roof and n its niche roof. A Psi-value above M/2 here would therefore be consequential, but none has been constructed. The positive integral remains an obstruction to upper enclosure.

### New ODE theorem SP1

[one-turn-saturated-passage.md](one-turn-saturated-passage.md) proves strict monotonicity of the first-passage time to q=-1/2 for the **proposed saturated piecewise ODE**, starting at p=1/2,q=q0>=0. Its unique pi/2 passage occurs at the reference q0. All regimes, including high arms, have explicit formulas.

This replaces the package's sampled monotonicity with a hand proof. **The assertion that actual maximizing caps obey this ODE is still unproved.** Differentiability/identification of exposure, exact balance and activity in folded configurations remain separate obligations. Do not substitute SP1 for those premises.

### Checks actually executed

The unchanged original script was replayed in full. The separate review checker passed 23 exact symbolic identities, 213 rational local-offset exposure cases and 200 interval-growth cases; it rejected two wrong sign/threshold controls. The finite cases do not assert cap realizations. The new passage formula agrees with the original fifty numerical ODE samples to about 1.09e-8; this is a diagnostic comparison only.

[review-results.json](computer-assisted/one-turn-arms/review-results.json) records scope, local versions and hashes. The executed review source matches Git blob `671fd75fc929f04e85eeb84937b57e7d09830a61`. Source commands are in the audit. No global certificate or certified numerical error bound was produced.

Caution: the uploaded Part D does not enforce all cap boundary conditions before testing sampled offsets, and floating-line intersections can miss near-coincident exposure. AR8 remains numerical evidence, not an exact existential counterexample.

## 3. Weighted one-turn infrastructure

Read these only as needed for the chosen proof step:

| Result | File and scope |
|---|---|
| PA2 | [one-turn-penalized-attainment.md](one-turn-penalized-attainment.md): signed weighted maximum exists. |
| ST1 | [one-turn-superlevel-trimming.md](one-turn-superlevel-trimming.md): every weighted maximizing roof is at least 1/2 throughout its projection. |
| HV1--HV2 | [one-turn-height-and-approximation.md](one-turn-height-and-approximation.md): height saturation, continuous niche area, uniform dyadic approximation. |
| WP1--WP2 | [one-turn-weighted-selection.md](one-turn-weighted-selection.md): selects any prescribed weighted maximizer; summable polygon defects and correct width-penalty endpoint terms. |
| WR1 | [one-turn-weighted-regularity.md](one-turn-weighted-regularity.md): bounded open-quarter curvature, exact half-height end edges, rho_f<=kappa(q), rho_g<=kappa(p). |
| AR7, AR5', AR6' | [one-turn-arm-reduction.md](one-turn-arm-reduction.md): same-sign improvement, endpoint-to-interior propagation and EA2 reduction. |

These statements concern maximizers of Psi, not arbitrary ambidextrous maximizers. Interior weighted and unweighted derivatives agree only when axis supports are fixed; unpenalized global maximality is not imported.

## 4. Earlier proposals and global geometry

The original `ambidextrous-one-turn-reduction-draft.zip` remains preserved as [one-turn-reduction.md](one-turn-reduction.md) and its companion directory at `7c2cb37b55ebd00d7c9d7717f170f6205101a946`. Read [one-turn-proposal-audit.md](one-turn-proposal-audit.md) for qualifications and hashes.

For full-turn caps with common projection and nonempty two-turn fibers,

$$
|E|=\Psi(U)+\Psi(V)+G,\qquad G\ge0.
$$

Empty fibers require another positive correction. Full-turn caps do not automatically cover a partial-turn body. OT3--OT4 classify face placements; OT5 eliminates G only under its actual aligned-face and two-sided positivity hypotheses. OA.3 strengthens a sufficient full-turn rectangle-width criterion to q-sqrt(q^2-1) for area greater than q.

The old imported `polycap.psi` computes clipped surviving area, not signed cap-minus-full-niche area. Its repeated-abscissa interpolation also has a demonstrated defect. Preserve the original code and use the review utility's separate quantities. Its original multistart campaign has not been independently reproduced.

The two-wing and canonical-admission packages remain alternatives, not completed global admission. Read their actual height, cut and contact hypotheses before use. [canonical-wing-winding-accounting.md](canonical-wing-winding-accounting.md) gives the exact discrepancy

$$
|S|-\widehat{\mathcal W}=N+U-B,
$$

where N counts negative winding with multiplicity, U is uncovered surviving material, and B>=0. Neither N nor U has a general paid budget. A simple signed core is not automatically ordinary area. The latest canonical-admission review includes exact height-algebra replay but no unrestricted coverage.

## 5. Direct ordinary-area computer route

Read [optimality-only-computer-plan.md](optimality-only-computer-plan.md) **together with** [occupancy-relaxation-audit.md](occupancy-relaxation-audit.md). The unconditioned triple-only LP has a structural 2/3 fractional barrier; adding pairs retains a 1/2 barrier. More angular/spatial resolution alone does not solve it. Use certified occupied anchors, integral branching, stronger justified inequalities, or direct finite-hallway area boxes.

[anchored-terminal-certificates.md](anchored-terminal-certificates.md) and [verify_anchored_terminal.py](computer-assisted/verify_anchored_terminal.py) are committed framework work. The separate `optimality_anchor_followon.zip` from the prior session contains reported local commits/certificates and a stronger width bound. **This arm-package review did not merge that local bundle.** Check the live tree and exact replay before treating it as remote infrastructure.

The committed analytic AW-W exclusion gives W<=2 => area<41/25<M. DU1 gives W<=1+2sqrt(2) for competitive bodies. The older direct width certificate is historical because AW-W has a pen-and-paper replacement. A full sharp global certificate and a local ordinary-area theorem covering its residual boxes remain unproved.

## 6. Do not repeat these failed substitutions

AF3 is a sharp auxiliary maximum, not universal area enclosure (AF4). Least curvature repair can decrease ordinary sofa area (GR1). Corrected energy budgets fail even after saturation (AX1/SAT1); SAC2 computes the true smaller-order deficit. Shared anchors and removing derivative-energy charges still fail through clipping (SC3). Repair followed by saturation can remain at a suboptimal fixed point (TR1).

The SC3 point-face examples approach M, so no fixed threshold below M dismisses that entire face type. A finite support grid does not by itself prove a C1 neighborhood. PR #8/#9's one-turn maximality or qualitative stability entry cannot be imported circularly to an unknown ambidextrous optimizer.

## 7. Immediate restart priorities

Query the live PR and read this file plus [ROADMAP.md](ROADMAP.md). Pick one actual missing comparison, not another detached calibration.

For the arm route, the sharply stated possibilities are: EA2 for one weighted maximizer; a bound/improvement excluding the remaining long arms; handling the zero-length top face; or a rigorous exposure law feeding SP1. TS1 allows finite comparisons without differentiating the niche and may be a useful template. None of these is a completed gate yet.

For the global two-turn route, retain clipping, uncovered material and actual terminal-angle coverage. The one-turn upper value alone does not pay them. For a computer search, verify that its relaxation can be sharp before generating a large tree.

Refresh blob SHAs before edits; never overwrite another session's progress. Record every executed source hash and distinguish fresh results from imported records. All source/diagnostic changes remain in docs/ambidextrous. **No CI or Lean/Lake compilation was used in this continuation.** The PR remains draft.
