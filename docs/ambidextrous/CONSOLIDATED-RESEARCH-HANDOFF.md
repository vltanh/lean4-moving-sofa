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
| Actual compatible full-turn hulls are **not Minkowski-convex** | Two exact rational **convex** sofas each perform both entire turns with the same axis supports and vertical span one, yet their horizontal-reflection Minkowski midpoint has a forbidden **unique bottom extreme point** and loses at least 1/50 of vertical span on canonical saturation. The continuum admission criterion is: all extreme points survive **and** no vertical fiber is empty. No area-above-M counterexample | [FH1–FH2](feasible-hull-minkowski-nonconvexity.md), [exact checker](computer-assisted/check_feasible_hull_minkowski_nonconvexity.py) |
| **Original arbitrary-motion optimum equals one signed joint convex-domain supremum** | For **any** compact convex hull \(K\subset[-5/2,5/2]\times[0,1]\) and independent terminal angles \(\alpha,\gamma\in[\pi/4,\pi/2]\), integrate the *signed* surviving fiber height after both visited turning sweeps **and outgoing whole-body strips**. Its supremum is **exactly** the original ambidextrous sofa value, conditional on the established proper-angle and gap-compression proofs. No sharp value or concavity proved; arbitrary partial/backtracking motions covered at *value-reduction* level | [OS1–OS2](original-motion-signed-convex-domain.md), [full-turn case SJ1](signed-joint-convex-domain-global-value.md) |
| **Joint signed objective is not concave in terminal angles** | With fixed \(K=[-3/8,3/8]\times[0,1]\), **both full-turn niches vanish**, every fiber is nonempty, and the signed/ordinary value for one variable terminal angle has exact second derivative \(9575/27648>0\) at \(\alpha=\arctan(4/3)\). This **does not** refute fixed-angle concavity in the convex-hull support variable | [TA1](terminal-angle-concavity-obstruction.md), [Fraction audit](computer-assisted/check_terminal_angle_concavity.py) |
| **Fixed-angle signed-area Minkowski concavity is also false globally** | Even with both turning angles fixed at 90°, smooth concentric disks of radii 1/8 and 1/4 are **actual feasible full-turn sofas** with no niches; their signed-area midpoint Jensen gap is exactly \(-\pi/256\). The defect comes from variable scale, not contact/pinch; does not refute a **fixed-height** theorem | [SCX1](signed-global-scale-concavity-obstruction.md) |
| **Vertical height-padding failure persists arbitrarily near \(M\)** | Horizontally padded Romik reference hulls followed by a small symmetric shrink give connected full-turn saturated sofas with areas tending to \(M\) from below. Restoring exact unit *hull* span by vertical Minkowski padding **strictly lowers the full canonical envelope's ordinary area**, by leading derivative at most \(-\varepsilon<0\). Does not exclude a different height repair or any theorem only for area \(>M\) | [NH1](near-romik-height-padding-nonmonotonicity.md), [VP1](vertical-padding-ordinary-area-obstruction.md) |
| Local fully certified \(<1.65\) area exclusion | **Only** full-turn hulls within Hausdorff \(7/10000\) of the Romik hull | [NL1](one-sixth-fullturn-near-reference-certificate.md) |

The branch records an external computer-assisted universal upper bound \(353/200=1.765\), stronger than its own computer-free \(1.80882\) estimate; independently check the external source before citing it as a published verified theorem. Neither bound approaches the exact candidate sufficiently.

**Actual-hull admission caution:** [FH1–FH2](feasible-hull-minkowski-nonconvexity.md) gives a rational full-turn convex-source counterexample to the convexity of *actual feasible hull supports*, with a rigorous full-angle check and quantified span loss after averaging. This does not refute signed-area concavity on all convex hulls; a Jensen proof must use that larger domain and account for points removed from the interpolated hull, rather than treating every interpolant as an actual sofa hull. The continuum iff admission criterion has two independent requirements: extreme-point retention and fiber nonemptiness.

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

### New principal sharp-proof formulation: joint signed fiber value (October 8)

The previous two-cap inequality is no longer the only global target. Two new **exact value-equivalence** drafts now provide a fundamentally different optimization domain:

- [SJ1](signed-joint-convex-domain-global-value.md): the **full conventional two-turn supremum** equals a single *signed total-fiber* objective maximized over **all** convex hulls in a fixed rectangle. Negative fibers may occur in intermediate hulls; the ordinary envelope's positive-part correction is never dropped as an area identity.
- **[OS1](original-motion-signed-convex-domain.md)**: the **original unrestricted ambidextrous supremum** (including partial/nonmonotone/backtracking motions) equals a joint signed-fiber objective maximized over the Minkowski-convex hull domain \(K\subset[-5/2,5/2]\times[0,1]\) and **two independent terminal-angle variables** \( \alpha,\gamma\in[\pi/4,\pi/2]\). Crucially, the full-body outgoing **straight-arm strips** are explicit constraints; leaving them out would give a false converse. Its proof imports Note 8/10's high-area proper-angle reduction and GC4's exact-area connectedification. These historical inputs remain research drafts requiring independent review.
- **[OS2](original-motion-signed-convex-domain.md)**: every arbitrary hull and fixed pair of terminal angles can be replaced by a **genuinely admissible actual hull with no smaller signed value**, via ordinary canonical saturation, gap compression, and support-tightening, although axis supports, width and incoming span may change. This repairs the *global value* domain, not the convexity of the actual-hull subset.

**Critical newer negative controls:** The natural rescue of the joint signed formulation through global concavity of \(K\mapsto\mathscr V(K,\alpha,\gamma)\) fails **even with terminal angles fixed**: [SCX1](signed-global-scale-concavity-obstruction.md) gives strictly convex area scaling along a smooth family of actual full-turn disks. Because that family has vertical spans below one, a fixed-height restriction might eliminate this particular counterexample. However [NH1](near-romik-height-padding-nonmonotonicity.md) shows that *near-Romik* saturated full-turn bodies can lose ordinary area under vertical padding to hull height one, so the needed height normalization cannot be justified merely from high but subcritical area or symmetric regularity. A **global-maximizer-specific** height-normalization theorem remains genuinely open. Concavity of the *signed* objective under **fixed vertical extrema** is not proved or refuted here; the convex-hull area alone satisfies a Dirichlet/Poincaré concavity law under that normalization, but moving niche costs are additional.

The resulting **still-unproved sharp theorem**, which alone would close the full original problem, is
\[
\boxed{
\mathscr V(K,\alpha,\gamma)\le M
\quad\forall\,K\subset[-5/2,5/2]\times[0,1]\text{ compact convex},\
\alpha,\gamma\in[\pi/4,\pi/2].
}
\]
Conversely one strictly larger *signed* value would, by OS2, produce a genuine connected area-\(>M\) counterexample. This is an exact biconditional global target, *not* a proof that \(M\) is optimal. Neither global concavity of \(\mathscr V\) nor a calibration at Romik is established. [FH1](feasible-hull-minkowski-nonconvexity.md) and [PM1](pinching-failure-of-global-envelope-concavity.md) remain barriers to naive Jensen arguments, but neither invalidates these signed **supremum equalities**.

[TA1](terminal-angle-concavity-obstruction.md) now **disproves global joint concavity in the terminal-angle variables** analytically—even when the niches and pinching corrections both vanish. A sound program must **separately handle angle optimization** rather than use Jensen in the entire product domain. **Fixed-angle concavity in hull support** remains unproved and unrefuted by this result. The most productive next step is a genuine fixed-angle signed hull-calibration (if true), combined with a rigorous global terminal-angle comparison; otherwise a direct nonconcave two-angle certificate. Do not revert to estimating separate \(G\) and \(\Delta_U,\Delta_V\) terms merely by changing symbols. Low-area and pinched test hulls should be treated as adversarial controls before any claimed universal theorem.

### New independent research branch: exact falsification (October 8)

The user asked to **deprioritize the two-cap clipping-deficit inequality as the principal route**. The inequality remains a correct equivalent sharp-value target in its stated full-turn domain, but repeatedly bounding its individual terms has not produced a universal comparison. Do not misrepresent another rearrangement of it as a new mechanism.

[RP1–RP3](rational-polyomino-motion-witness-completeness.md) instead proves a *counterexample-complete* reduction for the **original arbitrary-motion problem**: if some connected sofa has area strictly exceeding Romik's candidate, another one has rational grid-square geometry, two common-starting piecewise-rational **continuous** physical motions with positive clearance, and rational area above the candidate. Exact rational interval subdivisions, or real-algebraic quantifier elimination, certify its entire motions. This adds rational motion witnesses and a verifiable semidecision procedure to the earlier polygonal density [Note 33](33-rounding-and-perimeter.md). No actual larger sofa has been found. The complementary sharp-proof direction remains a genuinely **nonseparable joint motion/area calibration**, not separate one-turn cap deficits.

Key acceptance test for a numerical counterexample: connected rational body; explicit entire motion paths with exact hallway inequalities and true outgoing arms; **exact rational area** exceeding some rigorous rational upper enclosure of \(M\). [UV2](univariate-rational-motion-certificate.md) now reduces each full-path hallway check for rational square cells to univariate polynomial sign conditions of degree at most five, **without positive clearance**. This improves verification, not the search for an actual area excess. Finite pose sampling, approximate area, or a fixed threshold \(329/200\) alone are not a complete search. The exact witness theorem supplies existential completeness, **not** a tractable search schedule or a proof of the conjecture if the search does not halt.

### Current direction: construct the outer convex hull, then charge inner-wall carving

The user proposed separating the **outer supporting-wall hull** from the **inner forbidden niche carving**. The exact [OH1–OH3](outer-hull-first-carving-audit.md) study confirms this is a valid *parametrization* and a natural framework for a future **nonseparable** comparison, but **not** a way to maximize the outer hull separately:

- Any width-\(W\), height-one rectangle supports continuous outer-wall placements for both complete turns and fits the incoming and outgoing endpoint strips; hence the outer-only area supremum is **infinite**.
- After adding just the two canonical \(45^\circ\) *inner-wall* carve-outs, the rectangle's surviving ordinary area is exactly
  \[
  A_{45}(W)=
  \begin{cases}
    W,&W\le2(\sqrt2-1),\\
    W-2[W/2-(\sqrt2-1)]^2,&2(\sqrt2-1)\le W\le2\sqrt2-1,\\
    2\sqrt2-\tfrac32,&W\ge2\sqrt2-1.
  \end{cases}
  \]
  In particular the **larger** rectangle \(K_3\supset K_*\) has *smaller* completed-envelope area than Romik's actual \(K_*\): \(|E(K_3)|\le2\sqrt2-3/2<M=|E(K_*)|\).
- **Exact universal nested-hull gain/loss law:** for \(K_0\subseteq K_1\) with the *same* two visited angle intervals **and both full outgoing strips**, inner forbidden sets are nested. The ordinary envelope-area difference equals
  \[
  \boxed{|(K_1\setminus K_0)\setminus F(K_1)|
  -|E(K_0)\cap(F(K_1)\setminus F(K_0))|.}
  \]
  This counts **new surviving outer material minus old sofa material newly shadowed by the enlarged inner niches** without separately introducing \(G\). Both signs can occur globally. An actual quantitative payment is already proved along horizontally enlarged reference hulls: \(|K_\delta|-|K_*|=\delta\), \(|E(K_\delta)|\le M-9\delta^2/20\) for \(0<\delta\le1/16\), imported from the existing self-reviewed [NR.12](near-reference-positive-minwidth-slack.md).
- When the resulting canonical envelope has full horizontal projection, the **one-step retightening** \(K^\sharp=\operatorname{conv}E(K)\) makes an actual connected full-turn sofa hull with **no decrease** in envelope area; if there are empty fibers, [GC4](horizontal-gap-compression.md) is required and may change width/span.

**The sharp open challenge in this language:** construct a *global*, mathematically justified charge/transport from newly surviving outer material to newly forbidden old material for **all** competitor hull changes. Charging only inclusion-enlargements from Romik would still leave incomparable hulls and genuinely partial motions. No full sharp area certificate exists, and outer-hull maximizing before carving is invalid.

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
