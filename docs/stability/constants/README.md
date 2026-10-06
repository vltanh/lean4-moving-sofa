# Quantitative stability: explicit coefficients and an explicit cutoff

This is the analytic research branch of PR #10, separate from the coercive
extremal refactor in PR #9. The latest continuation starts at
`0ae744d727e77876cf148d19d0d0012d56e1bd8b` and quantifies the local radii left
unspecified after the coarse global-entry modulus.

**Formalization remains frozen.** The latest continuation changes only these
analytic notes and Python certificate material. It does not change Lean source,
the faithful Baek proof, the original uniqueness proof, the bridge, Challenge,
canonical Solution, workflows, library configuration, or manuscript. No Lean,
Lake, CI, remote build, or TeX compilation was run.

## Latest written analytic theorem

Let epsilon=|G|-|S| and normalize S by horizontal midpoint and top support.
The assembled analytic argument now gives the simultaneous numerical statement

    0<=epsilon<=10^(-600)
       ==> d_H(S_c,G)<=2.3*sqrt(epsilon),
           |S_c triangle G|<=50*sqrt(epsilon),
           0<=pi/2-omega<=3.1*epsilon

for every original moving sofa and every admissible reduced motion angle.
These are Euclidean distances and areas of actual nonconvex sets. There is no
smoothness, injectivity, or monotonicity assumption on the input. Midpoint/top
alignment is different from left-support pinning. A translation suffices, so
the rigid-alignment distance has the same upper bound.

This is a WRITTEN ANALYTIC theorem with exact arithmetic checks of reference
and scalar inequalities, not an independently reviewed or kernel-checked theorem.
The cutoff10^-600 is deliberately conservative and not a practical error bar.
It is not a claim of the best threshold or best global coefficient.

Read first:

- [32-explicit-sharp-cutoff.md](32-explicit-sharp-cutoff.md): full numerical
  statement and dependency assembly.
- [33-cutoff-handoff-and-review.md](33-cutoff-handoff-and-review.md): proof map,
  corrections, replay instructions, and limits of the numerical validation.
- [29-explicit-local-cap-radius.md](29-explicit-local-cap-radius.md): local cap
  certificate at upper-support error10^-40.
- [30-explicit-terminal-radius.md](30-explicit-terminal-radius.md): explicit
  floor witnesses and terminal budget at angle error10^-20.
- [31-explicit-normal-and-cone-scales.md](31-explicit-normal-and-cone-scales.md):
  numerical Euclidean normal and translated-sector scales.

## Why the cutoff is explicit

Notes26--27 give the coarse entry bounds

    d_H(S_c,G)<=3000000*epsilon^(1/12), epsilon<=10^-144,
    pi/2-omega<500*epsilon^(1/6), 0<epsilon<=10^-30.

At epsilon<=10^-600 these are at most3*10^-44 and5*10^-98, below the required
local support and terminal radii. The new local arguments then give the
canonical Q certificate and complementary deficit budgets. Centered cap
coercivity, normal recovery, and the exact eroded-sector area recover the
stronger square-root bounds. The sharp theorem is not used to establish its
own entry hypothesis.

The global-entry modulus is an analytic penalized-variation argument, not a
computed exhaustive shape-search certificate. Its polygon limits and geometry
remain important review obligations. Notes29--32 remove the unspecified local
radii from that argument's final numerical application; scalar checks do not
verify those higher-level mathematical steps.

## Other results retained in this branch

| Quantity / normalization | Written bound and scope |
| --- | --- |
| Cap residual energy, midpoint or optimized translation | coefficient sec(phi)<1.001, sharp in the stated cap-residual class |
| Cap Q deficit, fixed midpoint | 0.98 on the zero-slack face; 0.99 for Delta<=10^-18 |
| Cap Q deficit, optimized horizontal translation | 0.93 on the zero-slack face; 0.93*sqrt(Delta)+8*Delta^(2/3) for Delta<=1/512; 0.94 for Delta<=10^-18 |
| Intrinsic asymptotic full-Q coefficient | 0.922<C_Q^*<=0.93, with analytic feasibility and executed interval energy/operator certificates |
| Actual sofa, old left/top pin | coefficient4.22 for sufficiently small deficit; distinct normalization |
| Actual sofa, midpoint/top alignment | coefficient2.3, now with the explicit10^-600 cutoff above |

The cap residual, cap Q-deficit, and actual-sofa area-deficit theorems are
DIFFERENT statements. Neither the Q threshold10^-18 nor the puncture lower
bound may be substituted for an original-sofa entry theorem. No exact optimal
feasible-Q or global-sofa coefficient is claimed.

## Research reading order

- Notes01--09: earlier explicit coefficients and reference geometry; preserve
  the84/80/30.5 research stages and their limitations.
- Notes10--16: midpoint cap coercivity, whole-sector/normal recovery, the2.3
  coefficient, feasible cap-residual sharpness, and an unexecuted pixel-entry
  certificate design.
- Notes17--23: full-Q critical-face reduction, initial interval operator bound,
  coarse angle-entry computation, and initial lower-family development.
- [25-reproducible-intrinsic-Q-bound.md](25-reproducible-intrinsic-Q-bound.md):
  reproducible two-sided0.922--0.93 result and finite-deficit consequence; this
  supersedes the unreplayable initial trial description with published data.
- [26-effective-right-angle-regularization.md](26-effective-right-angle-regularization.md)
  and [27-effective-global-entry-modulus.md](27-effective-global-entry-modulus.md):
  analytic quantitative global entry, replacing an uncomputed separation gap.
- Notes28--33: explicit local radii, final cutoff, numerical checks, and handoff.

Historical numerical values, failed searches, and initial formulations are
retained as research history, not cumulative claims that every old result or
script has been reverified by each continuation.

## Numerical checks actually run for this continuation

Run without Lean or Lake:

    python docs/stability/constants/effective_entry/replay_cutoff_radii.py \
      --expect docs/stability/constants/effective_entry/cutoff-radius-summary.json

The replay recomputes5440 checks and then compares the compact invariant receipt.
The checks include whole-phase interval bounds over the complete reference
parameter box,41 exact local/cutoff margins, exact roots of10^-600, and negative
controls. Acceptance uses90-bit outward dyadic interval arithmetic for reference
trigonometry and exact Fractions for tiny radii and deficit powers. No floating-
point comparison accepts a certificate cell.

The tested and committed checker blob is
`ee82b0f3817efd6137e21a8e32afba082fce3d87`; replay blob is
`a59e242bad0ef605c39e1e616d292033e7e40e84`; summary blob is
`ca353f283f1cf04c1e96de7777d0da5a3d0ead01`.
The full invariant report hash is
`5d1a503086145b5e521e81692f3dc79ba3f74eb0e81017bd0710b80a148b9061`.

This does NOT verify polygon-limit arguments, reference contact topology,
uniform epigraph geometry, arbitrary-set area lemmas, or Lean proofs. Earlier
critical-cone, feasible-trial, and branch-and-bound certificates retain their
separate replay procedures and were not rerun by this continuation.

## Corrections and remaining review boundary

Note27's full-height rectangle belongs to the convex hull, not the nonconvex
sofa; four actual corner witnesses suffice for its width argument. That wording
and its version-dependent external equation references have been corrected.
Note30 now uses the strict midpoint margin m<-3/5 for the early floor witness.
Reflection arguments apply to the reflected competitor, not an assumption of
symmetry. The sector argument uses integrated curvature to control tangent
ANGLE variation and explicitly excludes other boundary branches.

No unknown numerical radius remains in the written cutoff assembly. Independent
mathematical review is still necessary, especially for the penalized global
entry and explicit boundary charts. Manuscript integration and any eventual
formalization must keep that review/verification distinction visible. The
faithful original proofs and formal-conjectures interface remain preserved.
