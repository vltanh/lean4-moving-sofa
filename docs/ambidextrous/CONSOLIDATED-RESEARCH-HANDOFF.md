# Ambidextrous moving-sofa research — consolidated handoff

**Date:** 2026-10-08.  
**Repository:** [vltanh/lean4-moving-sofa](https://github.com/vltanh/lean4-moving-sofa).  
**Research branch:** `research/ambidextrous-pen-and-paper`.  
**Draft pull request:** [#3](https://github.com/vltanh/lean4-moving-sofa/pull/3).  
**Separate relevant projects:** [#7 — changing the physical hallway bend](https://github.com/vltanh/lean4-moving-sofa/pull/7); [#4 — prescribed net rotation in the usual 90° hallway](https://github.com/vltanh/lean4-moving-sofa/pull/4).  
**Research only. No Lean formalization requested or performed.**

> **Definitive status:** Neither the unrestricted sharp upper bound nor uniqueness of Romik's ambidextrous moving sofa is proved by this branch. **No verified larger ambidextrous sofa has been found.** The many old documents are retained as historical research, *not* a single finished proof. This file supersedes their roadmaps as the entry point; it does not supersede their actual mathematical arguments.

## 1. The problem, exact candidate, and non-negotiable distinction

The sofa is one *connected rigid planar body* able to navigate either a left-hand or a right-hand **90-degree** unit-width corner, starting in a common incoming strip. Arbitrarily partial, nonmonotone, or backtracking motions must not be excluded without a theorem. Moving one fixed shape backward along an existing trajectory does **not** impose reflection symmetry of its upper and lower halves.

Romik's explicit **feasible candidate** has area

\[
M=1+4Y^2+\arctan(Y)\approx1.6449552184,
\qquad 4Y^3+3Y-1=0,\quad Y>0.
\]

It is the intersection of a *modified Gerver-like one-turn survivor* with its vertical reflection, **not** the intersection of two unchanged Gerver sofas. The modified half has different endpoint contact conditions from Gerver's one-turn optimum. The reference candidate is a rigorous lower bound on the possible optimum. It has **not** been established to be the unrestricted maximum.

### Actual two-turn constraints and exact area identity

For a body S with support function h in a proper conventional lower-turn frame,

\[
u_t=(\cos t,\sin t),\quad
v_t=(-\sin t,\cos t),\quad
h(u_t)-p\cdot u_t\le1\ \lor\
h(v_t)-p\cdot v_t\le1
\]

for each actual point p in S at every visited angle; the opposite handedness gives the reflected constraints. Support-tightening turns them into continuous canonical motions when all required angles and endpoint strips are present.

For **complete turns** and downward convex one-turn caps U,V with a shared projection I, let \(A_U,A_V\) be their upper roofs and \(n_U,n_V\) their positive one-turn forbidden-niche roofs. Provided the two-turn envelope has nonempty vertical fibers throughout I, the actual *ordinary-area* identity is

\[
\boxed{
|S|\le |E|
=\Psi(U)+\Psi(V)+G(U,V),
\qquad \Psi(X)=|X|-|N(X)|-|I|/2,
}
\]

\[
\boxed{
G(U,V)=\int_I\!
  [\min(n_U,1-A_V)+\min(n_V,1-A_U)]\,dx
\ge0.
}
\]

See [OT1](one-turn-reduction.md), [FV1](full-turn-unconstrained-envelope-variation.md), and the [core formulation](rectangular-core-exact-two-turn-area.md). **The nonnegative clipping correction G cannot be discarded.** Its sign represents material saved when a niche falls outside the other cap's outer hull.

The branch's [WV2](one-turn-weighted-value.md) proves, **in a self-reviewed analytic dependency chain**, the signed one-turn value \(\Psi(X)\le M/2\) in its normalized cap domain. Even if this chain is fully accepted, it yields **only** \(|S|\le M+G\), not \(|S|\le M\).

**Central still-unproved global full-turn inequality:**

\[
\boxed{
G(U,V)\stackrel{?}{\le}
\left(M/2-\Psi(U)\right)
+\left(M/2-\Psi(V)\right)
}
\]

for every **actual compatible full-turn two-cap pair** in the relevant normalization, including nonsmooth and asymmetric cases. A proof of this, with the required geometric admission, would settle the *full-turn* value. Handling unrestricted **partial turns** is a separate obligation. The inequality is not asserted for arbitrary incompatible abstract caps.

## 2. Substantive mathematical achievements — but with their exact scopes

All new written arguments are **self-reviewed drafts**, not independently refereed or Lean-kernel verified. Several computational certificates use exact rational arithmetic but their geometric premises and implementation still require independent audit.

| Finding | Precise scope | Source |
| --- | --- | --- |
| Proper-angle / midpoint bound \(|S|\le2\sqrt2 H-H^2\le2\sqrt2-1\) | Arbitrary partial/nonmonotone ambidextrous motions | [GH](midpoint-bound-general-motions.md) |
| Computer-free global bound \(2\sqrt2-1-1/51\approx1.80882\) | Arbitrary common-starting-position motions; **much weaker than M** | [JD1](two-sided-clipping-dual-hand-bound.md) |
| Competitive width \(W\le2\sqrt2\) | Actual connected full turns, and partial turns under the stated high-area gate | [TSW1](three-point-switching-fiber-width.md), [PTW1](partial-turn-three-point-width.md) |
| Full-turn face classification | Above the small-width threshold, the remaining potential **full-turn** counterexample lies in the opposite-end or point-face cases; point faces can be approximated by positive opposite-end faces for value purposes | [FD](full-turn-face-dichotomy.md), [PD3](full-turn-positive-face-density.md) |
| Sharp value within the left-right reflection-symmetric class | Does **not** prove existence of a symmetric unrestricted maximizer | [RS2](reflection-symmetric-optimality.md) |
| Sharp value for complete turns with identical positive top/bottom hull faces | Does not cover opposite-end exposed faces | [FAS1](full-turn-aligned-short-faces.md) |
| Width-tail area bound \(<1.64\) for \(W\ge1411/500=2.822\) | Only full conventional turns; exact arithmetic checker | [TS-CERT1](two-switch-global-wide-area-certificate.md) |
| Sharp fixed-width signed functional maximum and coercivity | An *auxiliary signed functional*, **not** automatically ordinary sofa area | [AF3](adaptive-functional-global-calibration.md), [SD1](stability-fixed-width-deficit.md) |
| Direct exact two-cap area identities and rectangle decomposition | Every downward convex cap admits a **horizontal-segment** summand equal to its top-face length; half-height filler needs extra assumptions | [UHCD](universal-horizontal-core-decomposition.md), [RCE](rectangular-core-exact-two-turn-area.md) |
| Sharp near-reference comparisons | Asymmetric sheared parents; infinite-dimensional strong-regularity neighborhood, **not** all near-optimal shapes | [SCR](sheared-romik-core-sharp-local-theorem.md), [ASS](actual-sofa-smooth-sharp-neighborhood.md) |
| Pair-to-identical Minkowski averaging | Only when parent support-curvature gap and difference conditions pay the clipping correction | [MSY](two-cap-minkowski-symmetrization-sharp-hand.md) |
| Reflection-equivariant gap compression | Every x-reflection-symmetric full canonical envelope, even disconnected, has a connected **symmetric** feasible replacement of the same area and vertical span; does not prove hull-symmetrization area monotonicity or unit-span restoration | [SEC](reflection-equivariant-connectedification.md) |
| Exact counterexample witness completeness | Any hypothetical **larger** sofa, including arbitrary partial/backtracking motions, has a connected **rational polyomino** counterpart with two **piecewise-rational continuous motions** and finite exact positive-clearance certificates; does not find a larger sofa or bound the optimum | [RP](rational-polyomino-motion-witness-completeness.md), [exact verifier](computer-assisted/check_rational_motion_witness.py) |
| Clearance-free exact full-motion validation | Every rational polygonal motion piece has a **degree-at-most-five univariate polynomial collision decision** for all real intermediate times; handles wall tangencies, nonmonotone rotations and edge-only collisions without angular sampling | [UV](univariate-rational-motion-certificate.md), [checker](computer-assisted/check_univariate_rational_motions.py) |
| Global raw-envelope Minkowski concavity is **false**, even at fixed width and height | An exact rounded-rectangle Minkowski segment of width 12/5, unit height, aligned faces and constant quarter curvature <1/2 develops a pinching correction of order epsilon^(3/2), overpowering the smooth signed Jensen deficit of order epsilon². One endpoint envelope is **disconnected**, so actual connected-hull concavity is not addressed | [PM](pinching-failure-of-global-envelope-concavity.md) |
| Local fully certified \(<1.65\) area exclusion | **Only** full-turn hulls within Hausdorff \(7/10000\) of the Romik hull | [NL1](one-sixth-fullturn-near-reference-certificate.md) |

The branch records an external computer-assisted universal upper bound \(353/200=1.765\), stronger than its own computer-free \(1.80882\) estimate; independently check the external source before citing it as a published verified theorem. Neither bound approaches the exact candidate sufficiently.

**Concavity caution (October 8):** [PM1](pinching-failure-of-global-envelope-concavity.md) rules out a naive global Jensen proof directly on the **total ordinary area** of arbitrary full canonical envelopes, even with constant quarter curvature, common axis supports and reflection symmetry. The failure is driven by empty-fiber positive parts, and is **not** an area-above-M sofa or a counterexample to a hypothetical concavity theorem restricted to actual compatible connected hulls. The smoother *signed total-fiber functional* is a possible separate research object, but neither its global concavity nor its sharp maximum has been proved.

**Do not confuse:** showing a class has optimum M; showing every unrestricted maximizer is in that class; and showing *every* unrestricted maximizer equals Romik. These are three different claims. The latter two remain open.

## 3. Important negative controls — do not re-propose these unchecked

1. **Naive reflection symmetrization is not established.** Feasibility is reflection-invariant; that does not make each optimizer symmetric. Minkowski averaging arbitrary *surviving sofas* may destroy both motions. See [RA1](reflection-averaging-obstruction.md). The exact [SEC](reflection-equivariant-connectedification.md) result removes **connectedness**, but not the area comparison or the subunit-span issue, from the separate *convex-hull* reflection proposal.
2. **Mixing two different one-turn halves can really recover area.** A pair of oppositely sheared Romik caps can produce more area than either self-pair, while still remaining below M. The exact mixed correction G can be positive, even arbitrarily close to M. See [PII](pair-versus-identical-romik-obstruction.md).
3. **Averaging arbitrary one-turn caps does not automatically pay G.** An explicit filled triangular cap has positive self clipping. The unconditional averaged-\(\Psi\) inequality fails. See [EAC](expanded-core-averaging-clipping-counterexample.md).
4. **Global repair / hull curvature monotonicity is false without constraints.** Specific fully feasible examples lose ordinary sofa area on repair. See [GR](global-repair-counterexample.md), [SC3](repair-shadow-clipping-obstruction.md). Unrestricted global Minkowski concavity of the older \(P_J\) route is **false**; do not revive it.
5. **Coarse occupancy and finite-angle LPs are not sharp.** The uniform fractional occupancy \(2/3\) obeys every *distinct-cell forbidden triple* LP inequality and yields \(2W/3\), already above M at W≥5/2. Additional higher-rank cuts exist but coarse area LPs remain weak. See [FT-FRAC1](forbidden-triple-fractional-barrier.md), [higher-rank handoff](HIGHER-RANK-AREA-RESEARCH.md).
6. **A few anchor points cannot replace the entire shape.** There are explicit large non-feasible regions meeting every three-anchor restriction. See [AR3-NEG](three-anchor-continuum-obstruction.md).
7. **Near-equality does not imply symmetry.** The opposite-end positive-face class contains **actual** full-turn bodies with areas increasing to M from below. There is no uniform area gap for that class. See [PD3](full-turn-positive-face-density.md).
8. **Unconditional vertical height padding can strictly lose ordinary two-turn area, even for fully feasible connected symmetric bodies.** The exact vertically symmetric fiber formula [VP](vertical-padding-ordinary-area-obstruction.md) and a rational rectangle of height 19/20 prove strict loss when padding to hull height one. This does not exclude a *competitive-only* normalization and does not address horizontal convex-hull averaging.
9. **Widening to a width-two corridor and squeezing back is not reversible.** The rectangle counterexample shows invalid width-one cores with spurious area >M. Correct reversible doubling uses angle-dependent effective arm widths \(1+\sin t\), \(1+\cos t\), not a uniform width-two corridor. See [squeeze audit](double-width-fill-and-squeeze-audit.md) and [RAD](reversible-anisotropic-doubled-corridor.md).
10. **Using two original Gerver sofas does not beat Romik.** Their natural reflected intersection was numerically disconnected and smaller; this is exploratory evidence, not a theorem. The actual Romik half is a *modified* Gerver-like cap.
11. **Finite angular sampling can generate false area wins.** Several numerical "counterexamples" lost their excess on refined meshes or failed connectedness. See [adversarial search report](COUNTEREXAMPLE-SEARCH-CONTINUOUS-ANGLES-2026-10-08.md).

## 4. What the other pull requests really offer

**[#7: arbitrary physical hallway bend.](https://github.com/vltanh/lean4-moving-sofa/pull/7)** Its drafted near-\(180^\circ\) reverse-turn optimizer is for a **different physical bend** and does not solve two alternative \(90^\circ\) turns. The PR #7 forward contact equation has the same intrinsic frequency \(1/2\) at \(90^\circ\) as Romik's interior support arcs, but different endpoint data. A direct uniform-similarity transfer of the near-reversal shape is excluded by a hand diameter/area inequality; grafting its curves into 90° caps produced **no refined numerical counterexample**. Importantly, the reverse-turn proof uses a *one-crossing* forbidden corner, whereas Romik's 90° corner is strictly **two-crossing**. See [PR7 transfer analysis](PR7-OPTIMALITY-TRANSFER-BOUNDARY.md) and [two-front exact area formula](pr7-double-crossing-area-transfer.md). The latter is a useful coordinate language but not a sharp global bound.

**[#4: fixed net rotation in the usual 90° hallway.](https://github.com/vltanh/lean4-moving-sofa/pull/4)** Its draft bound \(m(\omega)\le1+\omega^2/2\), with the branch's proper-angle reduction, yields the new conditional necessary turn amount \(\alpha_\pm>227/200\) radians (about 65°) for every competitive ambidextrous sofa. See [FA65](fixed-angle-65-degree-necessary-turn.md). This does not imply full \(90^\circ\) turns and relies on unrefereed analytic input from PR #4.

No PR #7 or #4 results were silently merged into PR #3's original Lean sources. Their theorem status is research-draft, not published/verifiably formalized fact.

## 5. What would *actually* settle optimality — a strict acceptance test

A new proof must give a **universal** ordinary-area comparison for *every actual feasible competitor*. The most direct full-turn target is the two-cap clipping-deficit inequality in §1. Alternatively, a wholly new geometric area majorant is acceptable **only if it provably contains every actual full-turn sofa, including disconnected-envelope pathologies correctly resolved, without sign-dropping or missing shaded area**.

Then handle **partial turns** by exact completion of the *same sofa*, or prove that partial competitors cannot beat M by another genuine theorem. A computer-assisted proof must cover the *entire* remaining configuration space with checked interval errors; optimizer success, finite pose samples and local stability are not substitutes.

A potential counterexample instead needs (i) an explicit compact connected shape, (ii) two valid continuous left/right motions with terminal strips, and (iii) a **rigorous** ordinary-area lower bound >M. Even area ≥329/200=1.645 is sufficient but still requires rigorous geometry. No such example was found in the exploratory work.

### New independent research branch: exact falsification (October 8)

The user asked to **deprioritize the two-cap clipping-deficit inequality as the principal route**. The inequality remains a correct equivalent sharp-value target in its stated full-turn domain, but repeatedly bounding its individual terms has not produced a universal comparison. Do not misrepresent another rearrangement of it as a new mechanism.

[RP1–RP3](rational-polyomino-motion-witness-completeness.md) instead proves a *counterexample-complete* reduction for the **original arbitrary-motion problem**: if some connected sofa has area strictly exceeding Romik's candidate, another one has rational grid-square geometry, two common-starting piecewise-rational **continuous** physical motions with positive clearance, and rational area above the candidate. Exact rational interval subdivisions, or real-algebraic quantifier elimination, certify its entire motions. This adds rational motion witnesses and a verifiable semidecision procedure to the earlier polygonal density [Note 33](33-rounding-and-perimeter.md). No actual larger sofa has been found. The complementary sharp-proof direction remains a genuinely **nonseparable joint motion/area calibration**, not separate one-turn cap deficits.

Key acceptance test for a numerical counterexample: connected rational body; explicit entire motion paths with exact hallway inequalities and true outgoing arms; **exact rational area** exceeding some rigorous rational upper enclosure of \(M\). [UV2](univariate-rational-motion-certificate.md) now reduces each full-path hallway check for rational square cells to univariate polynomial sign conditions of degree at most five, **without positive clearance**. This improves verification, not the search for an actual area excess. Finite pose sampling, approximate area, or a fixed threshold \(329/200\) alone are not a complete search. The exact witness theorem supplies existential completeness, **not** a tractable search schedule or a proof of the conjecture if the search does not halt.

### Proposed research reset

- **Stop:** accumulating restricted sharp subclasses, increasing weak numerical bounds, rerunning near-Romik perturbation searches, invoking false global \(P_J\) concavity, or treating arbitrary-bend shapes as 90° sofas.
- **Review first:** independently audit the small number of proofs needed for the true global step (canonical support tightening, connectedification, ordinary clipping identity, finite-to-full motion reductions, weighted one-turn value). Record whether each is valid as stated.
- **Then choose one genuinely new universal mechanism** (for example an actual-support, component-aware area inequality that controls G for arbitrary two-cap pairs, or a no-loss structural reduction proved at **global maximizers**). Seek a falsifying configuration before extending any proposed lemma.
- **Stop if no new mechanism appears.** Report a precise blocker and do not represent another local conditional theorem as a breakthrough.

## 6. Guide to retained documents

The old research directory holds hundreds of chronological notes. **They are retained intentionally** so that rejected assertions, failed tests and derivations remain inspectable. A previous document's label "theorem" means a *written research argument*, **not** externally accepted, automatically applicable, or Lean-verified proof.

Primary references by topic:

- [Class geometry and face cases](README.md), [full-turn cases](full-turn-face-dichotomy.md), [positive opposite-end value reduction](full-turn-positive-face-density.md).
- [One-turn geometry / exact interaction](one-turn-reduction.md), [weighted value](one-turn-weighted-value.md), [signed-area caution](curvature-only-signed-roof.md).
- [Sharp mathematical near-reference comparisons](GERVER-PAIR-SYMMETRIZATION-HANDOFF.md), [rectangle core](RECTANGULAR-CORE-SHARP-HANDOFF.md).
- [Direct geometry and wide-tail certificate](TWO-SWITCH-DIRECT-AREA-HANDOFF.md), [finite occupancy barriers](HIGHER-RANK-AREA-RESEARCH.md).
- [Experiments explicitly not establishing a counterexample](ROMIK-COUNTEREXAMPLE-SEARCH-2026-10-08.md), [continuous-angle polygon probes](COUNTEREXAMPLE-SEARCH-CONTINUOUS-ANGLES-2026-10-08.md).
- [Cross-PR #7 transfer](PR7-OPTIMALITY-TRANSFER-BOUNDARY.md), [180°-shape experiments](PR7-OBLIQUE-HYBRID-AUDIT.md).

The chronological [HANDOFF.md](HANDOFF.md) and [ROADMAP.md](ROADMAP.md) remain archived in place but are **not the authoritative current status** where they mention older checkpoints or narrower proof targets.

**Next session entry point:** [FRESH-SESSION-PROMPT.md](FRESH-SESSION-PROMPT.md).
