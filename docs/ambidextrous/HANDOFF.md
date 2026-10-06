# Ambidextrous moving-sofa research — session handoff

This file is the **authoritative starting point for a new research session** on PR #3.

- Repository: `vltanh/lean4-moving-sofa`
- Branch: `research/ambidextrous-pen-and-paper`
- Draft PR: #3
- Base branch: `paper/uniqueness-arxiv`
- Mathematical branch head immediately before this handoff: `9207937dbdaf4d7e01ae9e8c458dbd1a65e3ff09`
- Status: **the unrestricted ambidextrous optimality and uniqueness proof is not closed**
- Execution policy: commit substantive findings frequently with `[skip ci]`; do not run CI; do not compile Lean/Lake unless the user explicitly changes that policy.

Always check the current branch tip first because later sessions may have advanced beyond the snapshot SHA above.

## 1. Research target

Prove that Romik's ambidextrous sofa is the unique maximizer, up to congruence. Its area is

[
M=1+4Y^2+arctan Y,
qquad 4Y^3+3Y-1=0,quad Y>0.
]

The task is **not** to produce another calibrated auxiliary functional unless its ordinary-area comparison is also proved. Every closure claim must identify the original nonconvex body, not merely its convex hull.

## 2. User instructions that remain in force

- Continue toward mathematical closure rather than polishing side results.
- Commit frequently, including negative findings.
- Computer assistance is allowed for discovery and for complete certificates, but scope must be explicit.
- Do not call sampled numerics, an optimizer status, an unfinished covering, or unexecuted source a theorem.
- No CI.
- No Lean/Lake compilation.
- Keep PR #3 draft until the unrestricted proof and equality recovery are genuinely complete.
- Existing manuscript, Lean libraries, dependencies and workflow files are out of scope unless the user explicitly changes the task.

## 3. What is established and should be treated as infrastructure

### 3.1 Common-hull reduction, compactness and attainment

Earlier notes establish canonical support placements, same-hull saturation, a common incoming normalization, compactness/attainment, and selection of any prescribed maximizing hull. These are historical dependencies; they have not all been independently re-audited in the latest passes.

### 3.2 The width gate is closed analytically

[Theorem AW-W](analytic-width-theorem.md) proves

[
Wle2Longrightarrow |S|<41/25<M
]

for any normalized compact connected ambidextrous body, without curvature, contact-order, symmetry or full-turn assumptions.

[DU1](diagonal-width-upper-bound.md) gives a complementary upper bound for every sufficiently large body. Hence every global maximizer in the common incoming unit-span normalization satisfies

[
oxed{2<Wle1+2sqrt2<4.}
]

The older exact computer certificate for the width gate is historical and no longer needed for this conclusion.

### 3.3 Conditional wide-hull theorem

[CW4](curvature-only-wide-hulls.md) gives the sharp ordinary-area bound and exact uniqueness when the actual common hull has width at least two and

[
h+h''le d	heta
]

on all four open coordinate quarters. It needs neither contact order nor a separately assumed full turn.

This remains a sufficient route, but the curvature domination has **not** been proved for arbitrary maximizers.

### 3.4 Sharp adaptive functional calibration

[AF3](adaptive-functional-global-calibration.md) proves the global maximum (M) and equality kernel of the adaptive support functional on a large normalized (H^1) profile space, without convexity or curvature hypotheses.

Do **not** use it as universal ordinary-area enclosure. [AF4](adaptive-functional-enclosure-counterexample.md) gives genuine feasible near-candidate bodies with

[
|S|>widetilde{mathcal Q}(h_{operatorname{conv}S}).
]

### 3.5 PR #8 / PR #9 transfer

PR #8 supplies the useful deficit/coercivity methodology. PR #9, at later snapshot `8042bad`, implements an uncompiled one-turn coercive extremal route. Its logical pattern is useful:

[
	ext{geometric admission}	o 	ext{area}le Qle M
	o	ext{zero deficit}	o	ext{rigidity}.
]

It does **not** provide the missing ambidextrous admission step. In particular, its one-turn theorem uses maximality against all one-turn caps to derive the geometric domain. An ambidextrous maximizer does not automatically have that premise. See [coercive-pr9-transfer-audit.md](coercive-pr9-transfer-audit.md).

## 4. Failed global shortcuts — do not retry without a genuinely new premise

These are committed counterexamples or exact obstructions.

1. **Universal adaptive enclosure fails:** AF4.
2. **Least curvature-majorant repair need not increase ordinary area:** [GR1](global-repair-counterexample.md).
3. **Corrected repair budgets can still undercount ordinary area:** [AX1](axis-cut-repair-budget-obstruction.md).
4. **Canonical saturation does not rescue those budgets:** [SAT1](saturation-does-not-rescue-repair.md).
5. The saturated axis-cut family is still strictly suboptimal with deficit of order (	au^{3/2}): [SAC2](saturated-axis-cut-area.md).
6. **Shared-anchor / derivative-free repair enclosure fails** through actual niche clipping: [SC3](repair-shadow-clipping-obstruction.md).
7. Repair followed by saturation can have a fixed point whose actual hull still violates the desired curvature bound: [TR1 / repair-invariant-tail-regions.md](repair-invariant-tail-regions.md).
8. High area alone does not imply the curvature cap; smoothing cannot impose the cap arbitrarily closely on a fixed violating hull.

Any proposed comparison must be stress-tested against the axis-cut and shadow-clipping families before it is used globally.

## 5. Current active route: two convex wings plus an ordinary-area core

The current program is deliberately different from whole-hull repair. It retains **actual convex safe pieces** whose areas are counted directly.

Read in this order:

1. [ROADMAP.md](ROADMAP.md)
2. [two-wing-domain.md](two-wing-domain.md)
3. [two-wing-strip-quadratic.md](two-wing-strip-quadratic.md)
4. [two-wing-calibration.md](two-wing-calibration.md)
5. [two-wing-cut-slack.md](two-wing-cut-slack.md)
6. [two-wing-slack-quadratic.md](two-wing-slack-quadratic.md)
7. [two-wing-near-full-height.md](two-wing-near-full-height.md)

### 5.1 Base two-wing theorem

For convex wings (R,D) in one unit strip, with the stated directional-width and cut conditions, a quadratic functional (mathcal W(R,D)) is calibrated sharply:

[
mathcal W(R,D)le M,
]

with equality only for the candidate wing pair up to common horizontal translation.

The negative quadratic part is not positive on the entire affine space. [WS1](two-wing-strip-quadratic.md) proves the needed sign on the **common-strip cone** by an explicit copositive factorization.

### 5.2 Arbitrary cut slack, full-height wings

[two-wing-cut-slack.md](two-wing-cut-slack.md) replaces the old prescribed inward cut points by the intersections of the **actual inward supporting lines**, introducing four nonnegative directional-width slacks.

[Theorem SQ1](two-wing-slack-quadratic.md) proves, for wings each spanning the entire common strip,

[
widehat{mathcal W}(R,D)le M
]

with exact equality only at the candidate. The favorable first-order cut-slack term pays the negative quadratic slack term. This is not a joint-concavity theorem.

The exact finite algebra has a committed SymPy checker and a committed execution record:
- `computer-assisted/check_two_wing_slack.py`
- `computer-assisted/two-wing-slack-checks.json`

That recorded run checks 16 exact identities and rejects three deliberate mutations. It does not verify geometric admission.

### 5.3 Latest result: unequal heights near full strip

The latest mathematical commit before this handoff is `e9ef366`; the following commit `9207937` adds its exact checker source.

[Theorem NH1](two-wing-near-full-height.md) allows arbitrary cut slack and unequal wing heights when:

- the two completed wings lie in one unit-height strip;
- they share the same bottom supporting line;
- after translating that bottom to zero, both vertical spans satisfy

[
oxed{min(H_R,H_D)ge1-rac{sineta}{2}.}
]

Then

[
oxed{widehat{mathcal W}(R,D)le M}
]

with equality only at the reference wing pair up to common horizontal translation.

This converts the fully general unequal-height algebra problem into a concrete geometric admission target: prove the actual canonical wings of every relevant maximizer have this shared-bottom near-full-height property, or exclude bodies where a wing is shorter.

Important validation status:
- `computer-assisted/check_two_wing_height.py` reconstructs the finite height/cut/mixed factorization with exact SymPy algebra.
- At the handoff snapshot, **there is no committed execution-result JSON for this checker**. Treat it as checker source, not an executed verification record.

## 6. Active gates

The authoritative gate definitions are in [ROADMAP.md](ROADMAP.md). In practical priority order:

### R2 — terminal angles

The wing/core construction uses fixed angular intervals. Do not insert full quarter turns by convention. Either:

- prove every global maximizer visits every required angle; or
- add an explicit ordinary-area penalty/correction for a missing terminal interval.

The direct forbidden-triple framework in [configuration-area-certificate.md](configuration-area-certificate.md) is a possible curvature-free way to exclude partial endpoint ranges. Its checker is `computer-assisted/verify_configurations.py`. Source alone is not a certificate; a complete interval covering and accepted certificate would be needed.

### R3 — canonical wings

For an arbitrary attained maximizer, construct actual convex safe pieces from the two motions and prove:

- nonempty compact convexity;
- common-strip placement;
- directional-width inequalities used by the calibration;
- the actual cut data required by the relaxed functional;
- ideally the shared-bottom condition and
  [
  min(H_R,H_D)ge1-sineta/2,
  ]
  so NH1 applies.

If that height bound fails, try to prove a strict ordinary-area loss large enough to exclude the body from maximality, rather than enlarging the algebraic domain indefinitely.

### R4 — cut slack

Current state:
- old WC2: unequal heights under old cut-vertex domain;
- SQ1: arbitrary cut slack for full-height wings;
- NH1: arbitrary cut slack for shared-bottom wings that are near full height.

So R4 is **not fully closed**, but a global arbitrary-height theorem may no longer be necessary if R3 proves the NH1 threshold for maximizing canonical wings.

### R5 — ordinary-area core

Need a genuine ordinary-area comparison. Pairwise disjointness of wing/core interiors is **not** required for the upper bound by subadditivity. What is still required is:

- containment of the body in the wings plus core;
- a correctly oriented simple core boundary, or a replacement theorem that rigorously computes/upper-bounds its ordinary area;
- correct handling of clipping and terminal-angle corrections.

Do not identify a nonsimple signed curve integral with ordinary area.

### R6/R7 — assembly and equality

Once R2–R5 are proved for every maximizer:

[
|S|lewidehat{mathcal W}le M.
]

Since the candidate is feasible with area (M), the optimal value follows. Track equality through every enlargement/comparison; the candidate's regular-closedness can then recover exact equality of the original nonconvex body.

A theorem for just one attained maximizer proves the value, not uniqueness of all maximizers.

## 7. Parallel structural route, if the two-wing admission stalls

The older contact/variation program is still available. [Note 57](57-focused-structural-status.md) summarizes it.

Useful established pieces include:
- width-one diffuse curvature identity;
- classification of diffuse single-wall contact;
- clear-contact singular repair;
- transverse two-corner pinch measure bounds;
- zero-sensitivity singular repair;
- removal of fiber-clearance for singular-continuous curvature at clear exposed points.

The unresolved structural target is still full open-quarter curvature domination for an arbitrary maximizing hull, including hidden/coincident atoms and the sharp absolutely continuous density bound. If this route closes, CW4 finishes the problem.

Do not restart local contact classification merely because another subcase is available; use it only if it materially advances the global domination theorem.

## 8. Current files worth opening first in a new session

Minimal reading set:

- `docs/ambidextrous/HANDOFF.md` — this file
- `docs/ambidextrous/ROADMAP.md`
- `docs/ambidextrous/two-wing-near-full-height.md`
- `docs/ambidextrous/two-wing-cut-slack.md`
- `docs/ambidextrous/two-wing-slack-quadratic.md`
- `docs/ambidextrous/two-wing-domain.md`
- `docs/ambidextrous/configuration-area-certificate.md`
- `docs/ambidextrous/curvature-only-wide-hulls.md`
- `docs/ambidextrous/57-focused-structural-status.md`

Open older counterexample notes only when testing a proposed comparison.

## 9. Immediate next-session procedure

1. Query PR #3 and branch tip. If newer than this snapshot, read every intervening research commit before doing new work.
2. Read this handoff and ROADMAP.
3. **Do not spend time re-maximizing an auxiliary functional.**
4. Attack R3/R5 first:
   - define canonical bottom-anchored convex wings directly from a maximizing saturated body;
   - prove the shared-bottom condition;
   - seek the NH1 height threshold from connectedness, width (>2), and the actual two motions;
   - in parallel, prove body containment in wings plus an ordinary-area core.
5. If terminal angles block these constructions, switch immediately to R2 and use either an analytic strip argument or a complete forbidden-triple certificate.
6. Commit every substantive theorem, counterexample, or failed global premise separately with `[skip ci]`.
7. Keep claims scoped: written proof, executed diagnostic, exact certificate, and kernel verification are different statuses.

## 10. What not to claim

At this handoff snapshot:

- unrestricted ambidextrous optimality is **not proved**;
- unrestricted uniqueness is **not proved**;
- no global curvature theorem for arbitrary maximizers is proved;
- no universal ordinary-area enclosure by AF3, GM2, AC1/AS1, J0, or the whole-hull repair is valid;
- the two-wing calibration is sharp on its stated data domains but arbitrary-maximizer admission is open;
- `check_two_wing_height.py` is committed checker source but has no committed execution record yet;
- PR #9's new Lean route was not compiled in this work.

No CI or Lean/Lake compilation has been used in this branch's research workflow unless a later session explicitly records otherwise.
