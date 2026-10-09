# Ambidextrous moving-sofa research — consolidated handoff

**Gate 1.1 passed in written audit; Gate 1.2 sharp charge remains OPEN (October 9, 2026).** [PG1](gate1-facet-audit-and-feasible-polygon-density.md) audits the direct actual-hull [FT1–FT8](global-facet-triangle-niche-decomposition.md) theorem: every one-angle lower/upper physical inner-ray cut of a *genuine* connected complete-turn hull is one exact triangle on one exposed (possibly oblique) supporting facet, with both attached rays and the actual upper-roof bound. An exact genuine fullturn square-shaving construction produces a nonhorizontal active facet with one-angle carved area \((100/99)(29/20-\sqrt2)^2>0\). The audit repairs a false *strict base-endpoint clearance* inference: a forbidden cut cannot include an extreme facet endpoint, but its base **may end at** that extreme point with zero height.

**Global value-density:** Every genuine compact connected fullturn sofa is area-approximable from below by genuine connected fullturn sofas that are finite unions of rectangles and vertical connector segments, with their **actual convex hull a finite polygon**. This uses true whole-ray continuum envelope fibers and 1-Lipschitz horizontal gap compression, **not** infeasible polygonal circumscription or arbitrary support smoothing. Therefore **proving the exact coupled union-area bound on every finite *admissible polygonal hull* is equivalent to Gate 1**. The remaining **single active inequality** is [PG.12 / G1.5](SHARP-OPTIMALITY-EXECUTION-PLAN.md): the complete sum of *union* lower/upper facet carve areas must be at least \(|K|-M\), globally and sharply, including opposite-end faces. No uniform facet count exists; local triangle formulas cannot be summed over t due overlap. **No new unrestricted area upper bound and no optimality proof** resulted from this audit. Gate 2 stays blocked.


**Gate 0 completed, Gate 1 active (October 9, 2026):** [original-motion-global-bridge-gate0-audit.md](original-motion-global-bridge-gate0-audit.md) gives a standalone written audit of the exact original-motion supremum equivalence, including wrong-way reach, actual outgoing strips, upper/lower sign conventions, signed negative fibers, interval-fiber connectedification, and the fixed search box. The audit **passes the bridge only**, is self-reviewed and needs external scrutiny. It independently constructs a high-area, unit-vertical-span, true full-turn **tilted top-shaving family** with positive **ambient niche clipping**. The older [Note 9](09-separation-from-connectedness.md) niche-subtraction identity is *not wrong*: it explicitly intersects the two niches with the hull K before subtracting. The false step would be omitting those intersections; the current PLAN.1 joint max correctly includes them. **Gate 1 now asks for one global sharp full-turn area charge; no such bound was proved by this audit.** Partial turns are covered by the *variational domain* but not yet by the sharp inequality.

**Controlling next-step roadmap (October 9, 2026):** [SHARP-OPTIMALITY-EXECUTION-PLAN.md](SHARP-OPTIMALITY-EXECUTION-PLAN.md). This handoff remains the authoritative historical/technical proof ledger. The controlling plan alone governs **priorities and completion gates**: audit original-motion reduction, prove the coupled complete-turn sharp area charge globally, extend that *same* charge to the two actual partial turns with outgoing strips, then examine equality and uniqueness. All other exploratory programs are parked; no global sharp upper bound or larger sofa has been certified.


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

### Exact falsification of **general fixed-height signed Minkowski concavity** (Oct 9, later)

[RCX1](exact-unit-height-signed-concavity-failure.md) is a new explicit, **fully analytic counterexample** on **genuine connected full-two-turn sofas with their actual hulls**. For width \(W\in(2(\sqrt2-1),1]\) let \(K_W=[-W/2,W/2]\times[0,1]\) and \(S_W\) its canonically saturated complete two-turn envelope. Every \(S_W\) is connected, feasible, has full unit vertical span and *actual hull* \(K_W\), with no empty fibers or cross-cap clipping. The complete lower swept-niche roof is the reverse moving-corner graph
\(n_W(x)=(W\sin t\cos t+1-\sin t-\cos t)_+\) at the unique t solving \(x=\tfrac W2\cos2t+\sin t-\cos t\).
Its exact area near \(W=1^-\) is
\[
\boxed{\mathscr S(K_W)=|S_W|
=\frac\pi4W^2-W+\pi-2-2R_N(W),\quad
0\le R_N(W)\le90(1-W)^3.}
\]
With \(W_-=4999/5000,\ W_0=9999/10000,\ W_+=1\), the hulls satisfy the **exact** Minkowski midpoint relation, but the signed full two-turn area satisfies the opposite of concavity, with a strictly **positive Jensen violation** greater than \(678/(1000\cdot10000^2)\). This uses just \(\pi>3\), Taylor bounds and whole-angle monotonicity, no sampling, no CI or Lean. It also refutes Minkowski concavity of the separate *weighted one-turn* objective \(\Psi\) on all height-one normalized caps.

**Do not attempt to close the sharp proof by asserting generic Minkowski concavity of signed full-turn area on the whole unit-height domain. It is FALSE, even without pinching.** This does **not** refute the weaker star-concavity claim anchored at Romik's support, or a concavity assertion restricted to *competitive horizontal widths \(W>2\)*, or any sharp upper bound \(M\). Those remain unknown, and the true original problem still includes partial turns. RCX is a rigorous **stop-rule for an invalid global proof mechanism**, not a claimed advance in the optimal area value.

### Oct 9 focused star-concavity audit: exact cubic shear obstruction, global inequality still OPEN

A targeted [exact shear calculation](cubic-clipping-sharp-vertical-shear.md), beyond finite numerical interpolation tests, now establishes that MC3's \(O(\lambda^3)\) *positive clipping* bound is **optimal in order**. Let \(T_a(x,y)=(x+a(y-1/2),y)\) with sufficiently small fixed \(a>0\), and let
\(K_\lambda=(1-\lambda)K_*+\lambda T_aK_*\), of exact unit vertical span. The downward upper and reflected-lower top faces shift **oppositely** by \(\pm a\lambda/2\); on each interval of length \(\Delta=a\lambda\), the true one-turn inner niche and the opposite cap's outer roof deficit have respective local values \((\Delta-s)^2+O(\Delta^3)\) and \(s^2+O(\Delta^3)\). The complete clipped ordinary-area interaction therefore satisfies
\[
\boxed{G(U_\lambda,V_\lambda)
=\underbrace{2\int_0^\Delta\min(s^2,(\Delta-s)^2)ds}_{=\Delta^3/6}
+O_a(\lambda^4)
=\frac{a^3}{6}\lambda^3+O_a(\lambda^4).}
\]
This is a **positive** third-order clipping contribution for a far-endpoint hull which can be chosen arbitrarily close to Romik (and does not need to be a feasible sofa). It must be paid by *two weighted one-turn deficits* in any sharp comparison; replacing \(O(\lambda^3)\) by \(o(\lambda^3)\) or deleting G is **provably invalid**.

The **one proposed global sharp lemma**, unit-height **star-concavity** of the signed full-turn functional \(\mathscr S\) along every ray from \(K_*\), is STILL **UNPROVED**. Exploratory screens checked thousands of arbitrary polygonal endpoints, targeted elongated/opposite-face shapes, vertical shears, horizontal pad directions, and thousands of unit-height polygon pairs, with no robust numerical negative Jensen gap; finite approximate screens are **not** evidence of a theorem. The existing published/branch results also do **not** establish unit-height global signed concavity; global signed concavity is false if the vertical span varies. No global ordinary area upper bound improved and no sofa of verified area above \(M\) was found. The actual original problem also includes subunit incoming vertical spans and partially completed terminal angles, neither supplied by star-concavity alone.

**Do not resume small local class exclusions or randomly expand these screens.** To close, either prove an actual *global* deficit-versus-clipping estimate including \(G>0\) at finite Minkowski interpolation, or rigorously falsify star-concavity and seek a different universal mechanism. A sharp area proof cannot follow from global first-order stationarity plus MC3's cubic estimate alone.

### Oct 9 global-directional sharp research advance: **cubic** (not linear/quadratic) clipping from Romik toward *every* unit-height hull

[MC1–MC3](global-directional-romik-clipping-vanishes.md) proves a genuinely **global-in-directions** ordinary-area inequality. Let \(K_*\) be Romik's reference common convex hull; let **any** compact convex unit-height \(K\subseteq B=[-5/2,5/2]\times[0,1]\) be an arbitrary far or inadmissible hull, including asymmetric **opposite-end top/bottom faces**, nonsmooth supports, curvature atoms, and point faces. Along the exact Minkowski chord
\[
K_\lambda=(1-\lambda)K_*+\lambda K,
\]
the two downward upper/reflected lower caps interpolate under Minkowski addition, and their entire **full-turn** clipping credit \(G(U_\lambda,V_\lambda)\) is supported only in strips of combined width \(O(\lambda)\) adjacent to Romik's top-face endpoints. The **strict reference curvature gap** \(f_*+f_*'',g_*+g_*''\le393/400<1\) improves the height of every inner-ray roof on those strips to \(O(\lambda^2)\). This yields the **explicit, exact all-angle, all-hull** estimate
\[
\boxed{0\le G(U_\lambda,V_\lambda)\le500000\lambda^3,\qquad0<\lambda\le10^{-4}.}
\]
No curvature or contact hypothesis is imposed on the far endpoint **K**, only vertical span one; no finite angular sampling is used. This strengthens the initial \(O(\lambda^{3/2})\) estimate from merely Lipschitz supports. It implies the clipping interaction gives **neither first- nor second-order positive gains** at Romik along *any* such Minkowski chord.

**Conditional on the separate self-reviewed long proof WV2** of \(\Psi(U)\le M/2\) for every normalized full one-turn cap, the exact **signed**, *not positive-part ordinary*, two-turn identity
\(\mathscr S(K)=\Psi(U)+\Psi(V)+G(U,V)\) yields
\[
\boxed{\mathscr S(K_\lambda)\le M+500000\lambda^3}.
\]
This gives Romik a **global first- and second-order upper support in every height-one Minkowski direction**, **NOT a global maximum theorem**. The new *one-inequality* sharp target is the as-yet-unproved **unit-height star-concavity from Romik**
\[
\boxed{\mathscr S((1-\lambda)K_*+\lambda K)
\stackrel{?}{\ge}(1-\lambda)M+\lambda\mathscr S(K)}
\]
for every height-one K in B. Combined with MC3, WV2 and the PD3 unit-height full-turn value-density reduction, it would prove the **full-turn** sharp area bound; original **partial turns remain a separate obligation**. Existing SCX1 disproves global Minkowski concavity with varying vertical span; it does **not** settle the fixed-height star case. Neither star-concavity nor unrestricted optimality is asserted, and preliminary numerical screens cannot certify the missing inequality.

**Exponent optimality in the very opposite-end domain:** [MC4](global-directional-romik-clipping-vanishes.md) constructs one explicit unit-height **parallelogram \(P\) with strictly disjoint, positive-length, opposite-end top/bottom faces**, of width \(9/4\) and lying in B. Along the chord \(K_\lambda=(1-\lambda)K_*+\lambda P\), the ordinary two-cap clipping correction actually satisfies
\[
\boxed{G(U_\lambda,V_\lambda)\ge\frac9{32}\frac{\lambda^3}{1+\lambda}>0}
\]
for all sufficiently small positive \(\lambda\). The proof pairs the **actual** right terminal inner-ray circular wall envelope of the upper cap with the **outer** top circular flank of the reflected lower cap. Their small competing quadratic heights overlap on a horizontal interval of length \(3\lambda/2\); exact square-root geometry gives the displayed lower bound. Thus **the exponent three in MC3 is sharp even toward strict opposite-end faces**—we cannot remove the clipping credit entirely or upgrade the uniform theorem to \(o(\lambda^3)\). This is a **far hull interpolation example, not an area-\(>M\) feasible sofa**. A numerical signed-area star-segment screen at this same P showed no robust star-concavity failure; its small-\(\lambda\) values have finite polygon/angle discretization bias and are **not** proof evidence.

This has more global relevance than another near-Romik class exclusion. The sharp proof boundary is still the unknown nonlinear **finite-\(\lambda\) behavior** along arbitrary far hull directions, plus full-to-partial coverage. No Lean/CI was run.

## 2. Substantive mathematical achievements — but with their exact scopes

All new written arguments are **self-reviewed drafts**, not independently refereed or Lean-kernel verified. Several computational certificates use exact rational arithmetic but their geometric premises and implementation still require independent audit.

| Finding | Precise scope | Source |
| --- | --- | --- |
| Proper-angle / midpoint bound \(|S|\le2\sqrt2 H-H^2\le2\sqrt2-1\) | Arbitrary partial/nonmonotone ambidextrous motions | [GH](midpoint-bound-general-motions.md) |
| Computer-free global bound \(2\sqrt2-1-1/51\approx1.80882\) | Arbitrary common-starting-position motions; **much weaker than M** | [JD1](two-sided-clipping-dual-hand-bound.md) |
| Competitive width \(W\le2\sqrt2\) | Actual connected full turns, and partial turns under the stated high-area gate | [TSW1](three-point-switching-fiber-width.md), [PTW1](partial-turn-three-point-width.md) |
| **Certified convex area bound \(A\le3/2<M\)** | **All convex** ambidextrous sofas, including arbitrary partial/backtracking original motions. Uses the two actual 45-degree physical corners plus convex separation; **100,161 exact rational parameter boxes**, no CI. Does **not** apply to convex hulls of nonconvex sofas | [CV1](convex-sofa-two-corner-area-certificate.md), [Fraction checker](computer-assisted/check_convex_two_corner_area.py) |
| **Mandatory nonconvex niche above \(M\)** | Every original sofa with \(|S|\ge M\) has a full-hull point at canonical 45-degree depth \(>103/100\) on **both** walls at one handed pose, forcing missing convex-hull ordinary area \(>1/6250\) by a contained 1%-scale copy. Also a \(3/200\) Hausdorff obstruction to any convex two-pose sofa hull | [NC1](mandatory-competitive-convex-hull-niche.md) |
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

**New strongest audited result (later October 8):** The convex two-corner area theorem has now been upgraded **again**, to the certified
\(\boxed{|S_{\rm convex}|\le10/7=1.428571\ldots}\).
The final **from-scratch, Fraction-only** [rational checker](computer-assisted/check_convex_two_corner_area.py) discharged **378,771** boxes with **189,376** terminal leaves, maximum depth **32**, no unresolved cases. It maximizes over all actual incoming-strip placements and uses only exact polygon clipping/integration, plus proved coordinate-exchange and opposite-corner symmetries and exact actual-hull extreme support attainment. The largest accepted area upper was
\(1307684518073/915379200000<10/7\).
This supersedes the previous \(31/20\) and \(3/2\) convex results; the proof still applies only when **the actual sofa itself is convex**.

By the same fully general homothetic forbidden-hull argument, [NC4](mandatory-competitive-convex-hull-niche.md) now proves that **every genuine, connected ambidextrous sofa with \(|S|\ge M\)** (without convexity or full-turn assumptions) must have a point \(q\) of its actual hull and a genuinely visited proper \(45^\circ\) frame with **both** support depths strictly greater than \(1073/1000\); its ordinary missing convex-hull area satisfies
\[
\boxed{|K\setminus S|\ge\frac{5329}{9000000}|K|>\frac1{1030}},
\]
and every convex body fitting the two opposite \(45^\circ\) frames stays at Hausdorff distance **at least \(73/2000\)** from that hull in the common incoming orientation. The general continuous hull-versus-niche area law NC2 also has the updated certified constant \(C=10/7\):
\[
|K\setminus S|\ge
\frac{|K|}{\operatorname{diam}(K)^2}
\left(\sqrt{\frac{|K|}{10/7}}-1\right)_+^2.
\]
These are **unrestricted structural necessities**, not a sharp global area upper bound. They remain far below Romik's complete inner-wall swept niche cost. No verified area-\(>M\) sofa exists and no proof of \(|S|\le M\) has been completed.

**Strengthened checkpoint:** The initially proved \(31/20=1.55\) convex theorem has since been upgraded to the **exact rational \(3/2=1.5\)** area bound, using [the same verified checker](computer-assisted/check_convex_two_corner_area.py) with a sound extra projection-width enclosure. Its stronger exhaustive replay has **100,161 visited boxes, 50,079 leaves, maximum depth 24, and no unresolved cells**, independently re-executed locally. Consequently [NC3](mandatory-competitive-convex-hull-niche.md) strengthens the unrestricted necessary carving: every \(|S|\ge M\) sofa has a real \(45^\circ\) corner with both support depths \(>1047/1000\), and an ordinary missing convex-hull area **\(>1/2500\)**, with a \(47/2000\) Hausdorff gap from any convex two-pose-compatible shape. These are self-reviewed computational/analytic research results, **not** the sharp unrestricted upper bound.

### Endpoint geometry from the user's "why move to the other wall?" observation

[IW1](initial-corner-activation-and-face-asymmetry.md) directly distinguishes the **initial rigid translations** (free in the straight incoming arm and not a compulsory sideways traverse) from the real two-handed **inner-wall area loss**. Romik's 2016 paper explicitly assumes initial *outer-wall contact* \(A(0)=(1,1/2)\) for his ambidextrous ansatz, whereas Gerver's one-hand contact is \(A(0)=(1,0)\) (Sections 4–5). The two sharp inner corners of the separate canonical handed hallways at angle zero appear at opposite strip boundary heights \(0,1\), but their forbidden quadrants do **not** remove any incoming-strip area at angle zero. There is no physical requirement that one sofa slide sideways between these two corner positions.

For a general compact convex **unit-height actual hull** with horizontal projection \([l,r]\), top exposed face interval \([a,b]\times\{1\}\) and bottom exposed face interval \([c,d]\times\{0\}\), **all four one-sided moving physical inner-corner height slopes** are exactly
\[
\begin{array}{c|cc}
&\text{start}&\text{finish}\\\hline
\text{lower hand}&r-a-1&b-l-1\\
\text{upper hand (reflected height)}&r-c-1&d-l-1
\end{array}
\]
(the expansions are \(\sigma t+o(t)\) for angular distance t from the respective endpoint). These follow directly from *one-sided support directional derivatives at top/bottom faces*, without smoothness. The initial lower forbidden baseline interval tends to \((a,r-1)\); when the top and bottom faces **align over a common rectangle** its ordinary one-angle niche area grows as \(\frac12(r-a-1)^2t+o(t)\), not as a compulsory pre-turn travel time.

**Key unresolved class:** the existing full-turn face dichotomy FD1 says competitive positive **opposite-end** top/bottom face configurations satisfy, e.g.,
\([a,b]\subset[l,l+1]\), \([c,d]\subset[r-1,r]\), \(W=r-l>2\). Then the startup/end slope sign pattern is
\[
\begin{array}{c|cc}
&0&\pi/2\\\hline
\text{lower}&\ge W-2&\le0\\
\text{upper}&\le0&\ge W-2
\end{array}
\]
so **one handed corner may avoid the early ambient niche but the opposite hand pays later**. Unlike the aligned reference's early wedge, these ambient positive corner tents can fall *outside* the actual displaced lower/upper hull faces and incur **no ordinary-area removal**. This is the real geometric possibility behind the user's "wasted space" intuition, and it coincides with the [PD3 full-turn value-dense, as-yet-unbounded class](full-turn-positive-face-density.md). The next decisive task should be a **global ordinary-area bound for opposite-end-face actual sofas**, explicitly paying for outer-face disalignment and all clipped moving ray sweeps, **not** further convex-only or Romik-contact-local perturbation exclusions. No new sharp bound or counterexample is claimed.

### Latest area theorem: four independent middle arcs plus **independent top/bottom cap cuts**, with ordinary clipping restored

[AC1–AC2](four-arc-plus-top-normal-cut-area-calibration.md) extends the four-independent-ray full-turn strict upper theorem to **arbitrary inward convex cuts near the vertical top-normal support**, independently on the upper and vertically reflected lower caps. The cut caps remain downward closed, contain the common half-height horizontal strip, and agree with their middle-perturbed parent supports outside a short vertical-normal angular interval. **Unit incoming vertical span, horizontal top/bottom face preservation, hull-retention after cutting, reflection symmetry, new contact-chart stability and a new curvature upper bound are not assumed.**

The proof is a *true ordinary-area* slice comparison: after cuts, the two positive niches may lie **partly outside the new shared convex hull**. An initial draft erroneously subtracted their entire areas; that false identity has been **explicitly corrected and replaced**. On the central face J, the cut survivor's vertical length is at most the parent survivor's length plus the sum of the two genuine saved-niche heights. Outside J, there are no niches, so its loss is the sum of the outer cap roof losses. Every saved terminal inner-ray niche slice is paired **one-to-one** with lost *outer* circular-flank material under the same old reference supporting normal, at an abscissa outside the face. This yields
\[
\boxed{
|E_{\rm full}(U\cap\rho V)|
\le M-\frac12(1-|J_0|/\pi)\mathcal E_4
-\int_{I\setminus(J\cup F_{\rm out})}
   [(A_{U_0}-A_U)+(A_{V_0}-A_V)]\,dx
\le M .
}
\]
Here \(F_{\rm out}\) is the union of the two explicit small outer-flank pairing intervals. The **entire actual clipping** is handled pointwise, not discarded, and no universal pairwise clipping-deficit theorem is invoked. The correction removes an initially claimed (invalid) extra **central-face** loss term; it does not weaken the verified no-gain conclusion \(\le M\) for this whole local-and-cut class.

The [EP4–EP5](romik-terminal-angle-outgoing-strip-rigidity.md) partial-turn result extends all the way to independent final angles \(\alpha,\gamma\ge \pi/2-\beta\approx73.4^\circ\) with no cap cuts: the necessary whole-body outgoing strips cause \(\Omega(\delta^{3/2})\) **ordinary** loss, whereas the skipped terminal niche tail saves only \(O(\delta^3)\). **Combining independent arbitrary top-normal cuts and early terminal exit is still open** because a cut can move the whole-body outgoing supporting line. Do not silently add the two exclusions.

Two low-dimensional falsification screens directly attempted **above-\(M\)** variations of Romik's hull by uniform vertical contraction and by independent top/bottom horizontal-strip shaving together with early terminal exits. None improved upon the unmodified reference in the tested grids/parameter optimization; this is only a diagnostic, **not** a certified global no-counterexample claim. No universal sharp area bound or larger connected sofa has been proved.

### Further October 8 advance: full-ray **above-\(M\)** exclusion on four asymmetric hull supports and genuine **partial** exits

The latest rigorous work focuses on the user's **outer-wall contacts + moving physical corner + complete inner-ray sweep** rather than continuing the convex-sofa certificate.

- [FA2](four-independent-corner-ray-local-calibration.md) extends the **frozen-reference complete-ray calibration** to **four independently varied middle source support arcs** (two each from the upper actual hull and the vertically reflected lower hull). **Neither left-right nor vertical reflection symmetry is assumed.** Convexity turns Hausdorff-smallness into one-sided derivative closeness even with curvature atoms, so no **upper** new curvature bound, \(C^2\)-smallness or new active-contact-chart assumption is needed. The complete ordinary two-full-turn area of the genuine connected, exact-hull canonical saturation satisfies
  \[
  \boxed{|E_{L,L}(K)|\le M-
  \tfrac12(1-|J_0|/\pi)\int_{J_0}
  (|\phi_U'|^2+|\psi_U'|^2+
   |\phi_V'|^2+|\psi_V'|^2)\,dt.}
  \]
  This **excludes area-\(>M\)** competitors in an open Hausdorff neighborhood *within the fixed-outside-\(J_0\) support subspace*. It is stronger than constructing arbitrarily near-reference shapes **from below**; every nonzero perturbation in the specified whole class is uniformly below \(M\).
- [EP4–EP5](romik-terminal-angle-outgoing-strip-rigidity.md) adds the **genuine whole-body outgoing endpoint strips** and expands the sharp-sign angular comparison across the **entire Romik terminal circular phase**, not just infinitesimal rotation deficits. For independent early-stop angles \(\alpha=L-\delta_-,\gamma=L-\delta_+\), \(0\le\delta_\pm\le\beta=\arctan Y\) (i.e. each angle **at least about \(73.4^\circ\)**), the exact ordinary partial-turn envelope obeys
  \[
  \boxed{
  |E_{\alpha,\gamma}(K)|\le
  M-\tfrac12(1-|J_0|/\pi)\mathcal E_4(K)
  -\tfrac18(\delta_-^{3/2}+\delta_+^{3/2}).
  }
  \]
  The real geometric mechanism is that an **outgoing strip** removes old reference material along a *curved exterior flank* at order \(\delta^{3/2}\), while deleting the terminal inner-ray angles can save **only a circular niche tail of order \(\delta^3\)**. The outgoing lower and upper removals live in disjoint vertical strips. This provides an original **partial-turn exclusion** for a non-symmetric Hausdorff-small support neighborhood, without an unjustified completion to full turns.

The two theorems are self-reviewed and have strict domain limitations. They do **not** cover changed supports near the reference switching angles or axis normals, shifted/misaligned horizontal faces, far global competitors, or smaller partial terminal angles. They therefore do **not prove unrestricted sharp optimality**, but directly exclude genuine *above-\(M\)* possibilities within a larger joint **support × terminal-angle** region than previously considered.

### New area breakthrough for a nontrivial class: all convex sofas \( \le3/2 \), and a mandatory niche for every competitive sofa

[CV1–CV2](convex-sofa-two-corner-area-certificate.md) is an **ordinary-area theorem**, not merely another compatibility or width test: **every compact convex ambidextrous sofa, with arbitrary original motions, has area at most \(3/2=1.5<M\)**. In fact the same bound holds for every convex body fitting just the incoming strip and the **two opposite canonical \(45^\circ\) hallway positions**. The argument uses the user's **outer supporting walls plus forced physical corners** and the attached inner-wall rays. For a convex *sofa itself* (not the hull of a nonconvex sofa), avoidance of each open corner quadrant yields, by convex separation, a supporting halfplane through that sharp corner. In area-preserving diagonal coordinates \((U,V)\), the resulting convex body is in a rectangle of its two actual support widths \(P,Q\), between two weighted corner support lines, and inside one strip \(z\le U+V\le z+\sqrt2\).

The **entire finite-dimensional relaxation** is covered by the rational root box \([1,4]^2\times[0,1]^2\) for \((P,Q,\lambda,\mu)\) whenever area exceeds \(3/2\); the bounds follow directly from the two midpoint disjunctions, connectivity, and incoming-strip projection. An exhaustive **Fraction-only** [replay checker](computer-assisted/check_convex_two_corner_area.py) visits **100,161** parameter boxes, accepts **50,079** leaves at maximum depth **24**, with no unresolved cells. For each parameter box it clips an exact **rational polygon** enclosing every convex sofa candidate. It maximizes polygon area over **all** translations of any diagonal strip of rational width \(283/200>\sqrt2\), using exact one-dimensional piecewise-affine cross-sections and an exhaustive finite list of exact rational critical band positions. This is not a sampled-time, sampled-angle, or sampled-strip certificate. The maximum accepted rational upper is \(3/2\). The overall proof remains **self-reviewed**, not Lean-verified or externally refereed; the checker verifies the finite arithmetic, while the geometric separation and real-parameter enclosure are supplied by pen-and-paper proofs.

**New unrestricted quantitative consequence:** [NC1](mandatory-competitive-convex-hull-niche.md). For *any* original connected ambidextrous sofa with \(|S|\ge M\), write \(K=\operatorname{conv}S\). At least one **actually visited** opposite-handed \(45^\circ\) canonical hallway has a hull point whose **two support depths both exceed \(103/100\)**. Otherwise shrinking the entire **convex hull** by \(100/103\) would yield a valid **convex two-position** body of area \(>3/2\), contradicting CV1; \(M>(3/2)(103/100)^2=328879/200000\) follows from an explicit rational cubic-root and arctangent alternating-series comparison. By the general competitive-width gate PTW1, \(\operatorname{diam}(K)\le3\). The one-percent homothety
\[
q+\tfrac1{100}(K-q)
\]
about the depth-violating point \(q\) stays **strictly inside one open forbidden quadrant** yet remains inside the hull. Since the actual sofa avoids that quadrant, it forces the globally positive, actual **ordinary-area convexity deficit**
\[
\boxed{|K\setminus S|\ge |K|/10000>1/6250.}
\]
Also every convex body itself fitting the two \(45^\circ\) corner frames is at least \(3/200\) Hausdorff distance from the actual hull \(K\) in the common incoming frame. These are quantitative statements **about every Romik-competitive nonconvex sofa**, including arbitrary partial/backtracking motions; no global sharp optimality claim is made. The rational cubic/atan comparisons are replayed in [a tiny exact checker](computer-assisted/check_mandatory_nonconvexity_budget.py).

**Sharper continuous theorem [NC2](mandatory-competitive-convex-hull-niche.md):** For *any* compact measurable shape \(S\) satisfying the two opposite canonical 45-degree hallway positions (no convexity or connectedness of \(S\) needed), with actual hull \(K=\operatorname{conv}S\), outer area \(A_K>0\), diameter \(D\), and \(C=3/2\), the **ordinary missing hull area** obeys
\[
\boxed{|K\setminus S|\ge\frac{A_K}{D^2}
\left(\sqrt{\frac{A_K}{C}}-1\right)_+^2.}
\]
To prove this, write \(\Lambda\) for the largest of the two canonical midpoint frames' worst minimum-wall depths on \(K\). Uniformly shrinking \(K\) by \(1/\Lambda\) when \(\Lambda>1\) yields a *convex* two-midpoint feasible hull, hence CV1 forces \(\Lambda\ge\sqrt{A_K/C}\). At a witness point \(q\) both wall depths are at least \(\Lambda\). Every homothetic copy \(q+t(K-q)\) with \(t<(\Lambda-1)/D\) lies in one actual forbidden quadrant, forcing area loss \(t^2A_K\); pass to the limit. This is the **first global continuous outer-convex-area versus actual inner-wall loss coercivity bound** in this direction, but its mandatory loss is far too small to settle Romik's \(M\). For arbitrary original motions it applies when both proper 45-degree orientations are guaranteed, e.g. for area \(>\sqrt2\) by GH.

**Research pivot:** The strict convex-only area upper proves any sharp candidate is **essentially nonconvex**: one of its actual moving inner corners must carve a robust positive-area chunk of the hull. A global proof must now control how the *two complete moving inner-wall ray sweeps* interact with all convex-hull support contacts, rather than trying to convexify the full sofa or discarding the niche. The tiny \(1/6250\) mandatory deficit is not itself sufficient to show \(|S|\le M\).

### Stronger complementary-angle width restrictions, for all angles

[CD1](complementary-corner-width-continuum.md) proves a new extension of the previously isolated **45-degree** diagonal gate: if a lower normal pair at \(t\) and an upper-handed pair at complementary magnitude \(s=\pi/2-t\) are actually visited, the common hull obeys
\[
\boxed{\min\{w_K(u_t),w_K(v_t)\}\le2.}
\]
After reflecting the upper hallway, its outer normals are precisely the **negatives** of the lower perpendicular normals, so both sharp inner corners carve **opposite corners of the same rotated support rectangle**. If both perpendicular widths were \(>2\), the entire surviving set would lie in two positively separated unit squares in that rotated coordinate system, contradicting connectedness and actual support widths. This has a complete elementary proof, not a numerical bound. For **both full turns** it holds for *every* \(t\in[0,\pi/2]\). For an arbitrary **hypothetical above-\(M\) partial/backtracking competitor**, the existing proper-angle/two-strip reduction guarantees it for at least the uniform interval
\[
t\in[\pi/2-\arccos(5/8),\arccos(5/8)]
\quad(\text{roughly }38.68^\circ\ldots51.32^\circ).
\]
The old DU.2 is just \(t=\pi/4\). This is a global support-only, physical-corner consequence; it **does not prove the sharp area bound**.

[CD Section 4](complementary-corner-width-continuum.md) gives a separate **independence example**: a convex rational hexagon with outer area exactly \(1902703/10^6>M\) has
\(\min\{w_K(u_t),w_K(v_t)\}<2\) **for every real complementary angle** (proved with a 257-direction Fraction calculation plus a rigorous \(3\)-Lipschitz continuum margin), and every extreme hull point survives each of two chosen **noncomplementary** snapshots. Indeed each snapshot individually has connected nonempty interval fibers and retains the same hull. Yet the **joint** two-corner tent test CP1 produces an exact empty-fiber violation \(2431/262500>0\). Thus the true two-variable corner packing condition is demonstrably **stronger than the entire continuum of complementary width gates**. Neither hexagon nor its area is a feasible sofa or a counterexample to Romik.

The geometrically missing proof ingredient is still a **sharp ordinary-area charge** from outer contact growth to the complete union of attached inner-wall ray sweeps, not mere feasibility/nonpinching. At Romik itself the corner-pair packing constraints have strict slack \(>2/15\), so they cannot alone supply its equality ODE or optimality.

### New complete corner-pair feasibility constraints (October 8, later)

[CP1–CP2](two-moving-corner-packing.md) derives exact **two-handed corner packing** from the user's outer-wall-plus-moving-corner perspective. Each visited lower corner \(c^-(t)=(\xi_t,\eta_t)\) and reflected upper corner \(c^+(s)=(\zeta_s,\theta_s)\) carries a two-sided tent-shaped forbidden region determined by its attached inner-wall rays. Since a connected sofa occupies **every horizontal column** of its actual convex hull, the tents cannot cover an entire column. When their x-abscissae lie in the projection, this gives the explicit **necessary support-only inequality**
\[
\boxed{
\eta_t+\theta_s\le1+
\begin{cases}
\min(\cot t,\tan s)(\zeta_s-\xi_t),&\xi_t\le\zeta_s,\\
\min(\tan t,\cot s)(\xi_t-\zeta_s),&\zeta_s\le\xi_t.
\end{cases}}
\]
For arbitrary abscissae, replace the horizontal mismatch penalty by the **minimum of a convex piecewise-affine tent-cost on the hull projection**, obtained exactly by testing at most its endpoints and the two corner abscissae. This applies to **partial** turns whenever the two angles have actually been visited; no quarter-turn completion is imported. At both \(45^\circ\) angles it **recovers the previously known** diagonal width gate DU2 (not a new bound).

**A genuinely new off-diagonal exact obstruction:** The rational pentagon
\(\operatorname{conv}\{(-13/10,4/5),(-19/20,0),(-7/10,0),(13/10,3/4),(13/20,1)\}\)
has height one, passes the diagonal width necessary test, and each of the separate rational hallway snapshots with lower frame \((20/29,21/29)\), reflected upper frame \((4/5,3/5)\) leaves a connected full-projection one-pose survivor with the same actual convex hull. **Nevertheless their combined tents eliminate a whole horizontal neighborhood of one interior column**: the exact two-corner maximum-height violation is \(103/2000>0\). This is a pure *joint opposite-handed* obstruction invisible to either static snapshot separately. Independent [Fraction calculations](computer-assisted/check_two_corner_packing.py) give all support values, vertex safety margins, and piecewise roof comparisons; these are not global sofa upper-bound certificates.

[CP2](two-moving-corner-packing.md) gives a converse **full-two-turn hull admission** description entirely through (i) corner-vs-outer-top tent inequalities, (ii) reflected corner-vs-outer-bottom inequalities, (iii) all corner-pair packing inequalities, **plus extreme-point retention**. For partial turns both outgoing straight-arm strips must also be included. This repackages the earlier FH2 admission theorem into geometric corner tests.

**Important negative finding:** These corner-pair inequalities have uniform **slack \(>2/15\) at Romik** because its complete inner-corner heights are strictly below \(13/30\). They can exclude distant disconnections and tighten a global support search, but **cannot alone identify the sharp candidate or pay its outer-vs-niche area budget**. Closure still requires a global quantitative bound on the area removed by the *complete continuum of attached inner-wall rays*, as a function of the outer contact curves, including asymmetric and partial turns. Do not call the pairwise necessary conditions a sharp area certificate.

### Essential interpretation correction: outer supporting contacts **plus the moving inner corner**

The user's intended construction was **outer wall and physical corner first**, **then** carve the inner-wall niche. An earlier assistant response incorrectly discussed **outer walls alone**. See the [corrected geometry and rigorous example](outer-wall-and-moving-corner-first.md).

For each conventional angle, if the outer walls support a proposed convex hull \(K\), their perpendicular normals \(u_t,v_t\) and supports \(f=h_K(u_t),g=h_K(v_t)\) force the physical inside-corner trajectory:
\[
c_K(t)=(f(t)-1)u_t+(g(t)-1)v_t.
\]
The two attached inner-wall rays bound an exact tent-shaped forbidden quadrant with roof
\[
w_t(x)=c_y(t)-
\begin{cases}
(c_x(t)-x)\tan t,&x<c_x(t),\\
(x-c_x(t))\cot t,&x\ge c_x(t).
\end{cases}
\]
This is Romik's Section 2 rotation-path/contact-point parameterization, not a separate novel formula. The crucial detail: at Romik's 45-degree midpoint, \(c_{K_*}=(0,H_*)\) with \(0.28<H_*<0.41\), **strictly inside the actual outer convex hull**. The single-angle inner-wall rays carve a triangle of area \(H_*^2\) on each hand, total \(2H_*^2\), from the reference's central rectangle. Thus insisting **the convex hull** avoids the point corner would exclude the desired reference. One must allow the **hull** to cover the corner and require only the *carved sofa* to avoid the forbidden wedges.

An additional exact negative control shows that if one keeps **auxiliary** outer walls and only avoids the moving point-corner trajectory, while omitting the attached inner-wall rays and actual-hull consistency, connected central rectangles of area \(W-4\) survive for arbitrarily large \(W\). This does **not** refute a self-consistent hull-plus-corner/contact program; it establishes why the inner **rays** and geometric admission are essential. The promising reformulation is to jointly optimize the *corner path and outer supporting envelope*, then subtract the complete union of moving wedges. This still needs a sharp global area comparison, including partial terminal angles.

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
