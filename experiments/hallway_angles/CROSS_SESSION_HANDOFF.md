# Cross-session handoff: arbitrary-angle moving sofa research

**Date:** 2026-10-06  
**PR:** #7 — `Arbitrary-angle sofas: 173-degree global cutoff and analytic contact-model crossing`  
**Branch:** `research/arbitrary-hallway-angles-20261005`  
**Head before this handoff commit:** `8fd6f6277006d99de443346601207e1ae95ed15b`

This file is the canonical handoff for continuing the arbitrary-hallway research in another session. Read it before making new claims. It intentionally distinguishes committed results, local-only exploratory progress, and unproved targets.

## Non-negotiable execution constraint

**Do not run CI, GitHub workflows, or Lean builds.** The user explicitly requested this. Research commits should continue to use `[skip ci]`.

Local Python checks and exact-arithmetic certificate generation are allowed, but must be described precisely. A passing scalar checker verifies only the scalar inequalities encoded in it; it does not independently validate the geometric premises that feed those inequalities.

## Angle convention and value functions

- `beta` is the actual change in travel direction at the sharp unit-width hallway, `0<beta<pi`.
- `e=pi-beta` is the angle between the two corridor rays pointing away from the corner.
- `beta=pi/2` is the classical right-angle hallway.
- `M(beta)`: unrestricted optimum.
- `M_+(beta)`: aligned forward class.
- `M_-(beta)`: aligned reverse class.
- `S_e`: explicit reverse-class candidate.
- `V(e)`: exact area of `S_e`.

Never conflate a class optimum with the unrestricted optimum, and never call the analytic forward-model crossing the established global phase transition.

## Strongest committed geometric results

### Reverse class

The explicit reverse candidate exists for every `0<e<pi/2`. Its exact value is

`
d=cos e, q=sin e, m=2-d,
eta=sqrt((2-d)/(2+d)),
K=(e/2)sqrt(1+3/sin(e)^2),
R=eta sin K/(cos K+eta sin K),
V(e)=e/m+(1+2d)/(4q)+3d^2 R/(2q m^2).
`

Committed proof drafts establish exact unique reverse-class optimality for

`
beta >= pi - arccos(sqrt(2)-1)
      = 114.4698005207... degrees.
`

That is the current theorem range. Do **not** claim the all-obtuse extension yet.

The quadratic maximization, candidate realization, equality/rigidity, and scalar width comparisons already work over the full `0<e<pi/2` range. The missing issue below 114.47 degrees is the universal area majorant / canonical-corner crossing for arbitrary reverse competitors.

Key files:

- `REVERSE_MAIN_THEOREM.md`
- `REVERSE_EXTENDED_RESULTS.md`
- `REVERSE_GENERAL_MAJORANT.md`
- `REVERSE_QUADRATIC_THEOREM.md`
- `REVERSE_GEOMETRIC_THEOREM.md`
- `REVERSE_CROSSING_EXTENSION.md`

### Unrestricted near reversal

A separate global theorem draft proves

`
M(pi-e)=V(e)
`

and uniqueness of `S_e` for every

`
0<e<=1/8,
beta>=pi-1/8 = 172.838027560... degrees.
`

Thus every integer bend 173–179 degrees is covered. This is a **sufficient global cutoff**, not the actual phase transition.

Key files:

- `ROUND6.md`
- `INTERIOR_CORE_GLOBAL_CUTOFF.md`
- `CURVED_CONTACT_CORES.md`
- `interior_core_certificate.py`

### Forward analytic contact model

Near the numerical competing-branch crossing there is a three-phase analytic forward model:

1. initial circular wall-pair phase;
2. central hyperbolic phase;
3. reflected final phase.

With `L=beta/2`, `T=L-alpha`, `d=cos beta`,

`
mu=sqrt(3/(4 sin(beta)^2)-1),
eta_F=sqrt((-1-2d)/(1-2d)).
`

The matching equation is

`
F(beta,T)=eta_F(3 sin(L) sin T-cos(L) cos T-1)
          +tanh(mu T)(sin(L) sin T-3 cos(L) cos T-eta_F^2)=0.
`

The exact scalar system consisting of this matching equation and equality with the reverse value has a unique model crossing on the certified branch:

`
136.672184698 degrees
< beta_model
< 136.672184699 degrees.
`

This is **not** proved to equal the global `beta_c`.

The reduced exact crossing system is in `EXACT_CONTACT_CROSSING.md`.

Key files:

- `FORWARD_CONTACT_MODEL.md`
- `FORWARD_CENTRAL_CONCAVITY.md`
- `EXACT_CONTACT_CROSSING.md`
- `contact_crossing_certificate.py`

Missing for a true phase-transition theorem:

1. continuous feasibility / correct exposed-boundary topology of the forward candidate;
2. a sharp upper bound for every forward-class competitor matching the candidate area;
3. an unrestricted reduction proving no third motion/contact class wins near the crossing.

## Cross-PR transfer audit

Other PRs in this repository contain methods likely reusable here.

Read `CROSS_PR_TRANSFER_AUDIT.md` first.

Most important transfers:

- **PR #4:** order-independent contact shooting, strict lifted concavity, vertical-core lifting, global contact certificate.
- **PR #2:** persistent-penalty selection of a specified maximizer, one-step arm bootstrap, deficit/coercivity, exact no-loss angle completion of the SAME sofa.
- **PR #6 / #8:** quantitative residual-to-Hausdorff coercivity.
- **PR #9:** maximizer-first optimality/uniqueness architecture.
- **PR #3:** finite-angle repair plus counterexamples warning against unjustified functional enclosure.

The highest-value long-term plan remains:

1. solve the reverse class for every obtuse bend;
2. prove forward-class optimality near the analytic model crossing;
3. prove class exhaustiveness / no-loss alignment near that crossing;
4. conclude the exact global phase transition as the unique class-value crossing.

## Latest reverse-class continuation: what changed

A first attempt tried to prove that every reverse maximizer has nonnegative oblique arms. The natural arm variables satisfy

`
sin(e) y' = sin(e-phi) a + sin(phi) b.
`

So `a,b>=0` would force monotone height crossing.

This was reduced in `REVERSE_MAXIMIZER_ARMS.md` and `REVERSE_ALL_OBTUSE_REDUCTION.md`.

However, a later audit found that the first local-bootstrap argument was not sufficient:

- the limit argument had used arm regularity before fully proving curvature regularity;
- a local negative-arm excursion can satisfy the local differential and curvature inequalities.

This correction is preserved in:

- `ARM_CLOSURE_AUDIT.md`
- `REVERSE_LOCAL_BOOTSTRAP_OBSTRUCTION.md`

Do not resurrect the old “local first-zero argument” without addressing those counterexamples.

## Repaired reverse variational route

The current best route is a relaxed support-function optimization plus an exact dual certificate.

### 1. Finite two-neighbor wall estimate

`REVERSE_DISCRETE_CURVATURE_REPAIR.md` gives an exact two-neighbor exposed-ray estimate without presupposing small facet jumps. Under a selected polygonal maximizing sequence with total stationarity defect tending to zero, it yields bounded interior curvature densities.

Primitive exact checks are in `reverse_wall_checks.py`.

### 2. Relaxed reverse-cap optimization

`REVERSE_RELAXED_SELECTION.md` defines a signed relaxed objective

`
J_w(h)=integral [F_h(y)-B_h(y)] dy
`

such that every genuine reverse sofa satisfies

`
area(S)<=J_w(h_S).
`

The point of the relaxation is that support facets can be varied without claiming the perturbed object remains a feasible connected sofa.

The proof draft develops:

- attainment of a relaxed maximizer;
- persistent-penalty selection of a specified maximizer;
- legitimate floating-facet stationarity;
- curvature regularity;
- terminal-facet elimination.

This is a major analytic dependency and requires independent scrutiny before any theorem-range extension is promoted.

### 3. Terminal kernel identities

With terminal facets eliminated, the two curvature densities satisfy global integral relations. The resulting convex relaxation has the form

`
r>=0,
r + c K_e r <= R,
`

with

`
R=1/(1-cos e), c=R/2.
`

See `REVERSE_TERMINAL_KERNEL.md`.

### 4. Dual certificate

`REVERSE_KERNEL_CERTIFICATE.md` formulates dual witnesses that prove linear inequalities against **all** densities satisfying the infinite-dimensional kernel constraints.

The architecture intentionally separates:

- numerical proposal generation: `reverse_kernel_proposals.py` (NumPy/SciPy);
- exact/outward mathematical acceptance: `reverse_kernel_dual.py` and `reverse_kernel_interval.py`;
- adaptive local construction: `build_kernel_cover.py`.

The proposal optimizer is not the proof. The independent verifier must recompute every record and the final cover must be checked for exact gap-free coverage.

## Current committed certificate status

As of the head immediately before this handoff:

- verifier/builder machinery is committed;
- **no final frozen gap-free kernel-cover result file is committed**;
- therefore there is **no new reverse theorem range yet** beyond 114.4698 degrees.

This distinction is essential.

## Local-only progress after the committed head

The most recent session regenerated two promising certificate components locally from the committed formulas:

- a **128-box** moment cover over approximately `1.14 <= e <= 1.23`;
- a **204-box** crossing-gate cover over the same range.

These local covers had positive exact-verifier margins in the working session, but they have **not** yet been frozen, committed, and independently replayed as final certificate artifacts.

The difficult pending portion is the direct arm/kernel certificate on approximately

`
1.23 <= e < pi/2.
`

Do not cite the 128/204 counts as repository-established results until the records themselves are committed and replayed.

## Exact next milestone

Resume here:

1. Regenerate/freeze the complete moment and crossing-gate records.
2. Complete the arm/kernel cover for `e in [1.23,pi/2)`.
3. Add an independent replay program which:
   - recomputes every dual continuum inequality from the stored rational witness;
   - ignores stored success booleans;
   - checks every parameter-box margin;
   - checks exact gap-free cover of the intended `e,u` domain.
4. Commit the frozen certificate records and replay report.
5. Audit the analytic assembly:
   - genuine sofa <= relaxed objective;
   - relaxed maximizer exists;
   - selection/facet variations are admissible;
   - curvature limit is noncircular;
   - terminal matching is justified;
   - kernel certificate implies inside-strip monotone crossing / valid general majorant.
6. Only after all of those pass, update the reverse theorem to all obtuse bends.
7. If the arm cover fails structurally near `pi/2`, preserve the failed witnesses/cells and seek a different dual target rather than weakening acceptance criteria.

## Negative results that must remain preserved

- Local arm-curvature inequalities alone do not prove arm positivity; explicit negative-arm excursions exist.
- A sampled candidate boundary is not a continuous feasibility certificate.
- A calibrated functional need not upper-bound ordinary sofa area without a valid geometric lift/enclosure.
- Scaling/alignment arguments lose area and do not prove exact class exhaustiveness.
- Direct high-degree Horner trig at large arguments can produce useless interval widths; use exact argument reduction.
- Off-branch reduced-area formulas must not be used away from the matching locus.
- Finite PSLQ / denominator searches are evidence, not nonexistence proofs.

## Arithmetic / closed-form side results

These are secondary to the geometric program but are retained.

For the contact-model crossing, any hypothetical rational representation

`
beta_model/pi=p/q
`

has an enormous proven denominator lower bound, approximately `1.21e74`, from the 512-bit Farey certificate.

Under Schanuel's conjecture, `beta_model/pi` is irrational.

This does **not** prove an elementary closed form impossible, and it does not prove `beta_model=beta_c`.

Relevant files:

- `ULTRADEEP_RATIONAL_EXCLUSION.md`
- `RATIONAL_BEND_FIELD_DEGREE.md`
- `CONTACT_TRANSCENDENCE.md`
- `SCHANUEL_RATIONAL_ANGLE.md`
- `TRANSCENDENCE_BARRIER.md`

Do not spend further effort merely increasing the finite denominator bound unless the user explicitly redirects the project back to arithmetic.

## Publication/verification language

Use conservative wording:

- “research proof draft”;
- “computer-assisted scalar certificate”;
- “not independently reviewed”;
- “not Lean-checked”;
- “local tests / exact interval replay” only when actually executed.

Do not claim journal-level completion from an unreviewed Python interval certificate.

## Current priority

**Stay on reverse all-obtuse closure until it either succeeds or yields a genuine obstruction.**

The most valuable immediate result would be:

`
M_-(beta)=V(pi-beta)
for every pi/2<beta<pi,
`

with exact uniqueness in the full aligned reverse class.

After that, return to the forward-class global contact certificate near 136.67 degrees, using PR #4's lifted-contact architecture.
