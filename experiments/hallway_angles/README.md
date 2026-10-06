# Arbitrary-angle hallways: exact near-reversal optimizers and stability

**Current status: fourth-round mathematical proof drafts, not independently reviewed or Lean-checked.** Start with [EXACT_NEAR_REVERSAL.md](EXACT_NEAR_REVERSAL.md). The strongest new statement is exact unrestricted optimality and uniqueness for all bends sufficiently close to 180 degrees, not merely an asymptotic or an aligned-class result. Its numerical starting angle has NOT been determined.

Earlier numerical experiments, weaker theorem checkpoints, and failed approaches are retained. Statements such as "unrestricted equality is not claimed" in earlier round-three documents describe that earlier checkpoint; the current scope and dependencies are given here and in the new main theorem.

## Scope and angle convention

The bend beta is the change in travel direction, 0<beta<pi. The classical hallway has beta=pi/2. Write e=pi-beta for the angle between the corridor rays pointing away from the junction. The hallway has a sharp corner and two unit-width arms. This is not Baek's rotation parameter inside the original right-angle hallway.

The branch starts from main at `16653ae81e0e4f52a362bafae2ad3440100ad065`. All changes remain under `experiments/hallway_angles/`. Existing Lean libraries, the existing paper, and workflows are untouched. No CI, workflow dispatch/rerun, or Lean build was invoked. Commits carry `[skip ci]`.

## Main results of the current draft

### 1. Exact unrestricted optimality and uniqueness near reversal

There exists e_1>0 such that, for every 0<e<e_1,

    M(pi-e)=V(e),

and every maximizing compact connected sofa is congruent to the explicit convex sofa S_e. Neither the shape nor the motion of competitors is assumed convex, symmetric, smooth, aligned, or monotone.

The elementary formula V and explicit boundary/motion are assembled in [EXACT_NEAR_REVERSAL.md](EXACT_NEAR_REVERSAL.md). The new step is [FLAT_CONTACT_ALIGNMENT.md](FLAT_CONTACT_ALIGNMENT.md): uniform actual-set stability and two flat contact segments force any putative optimal competitor's entry/exit mismatch to vanish. This eliminates, rather than ignores, the earlier alignment scaling loss.

**The angle range is existential.** No numerical value of e_1 is certified. In particular this theorem does not assert unrestricted optimality starting at 114.47, 142.10, 150, or 179 degrees. Those specific finite-angle conclusions require an explicit global cutoff that has not been computed.

The strongest sufficiently-near-reversal theorem has a [purely analytic proof route](ANALYTIC_NEAR_REVERSAL_FOUNDATION.md). The integer interval checkers below are used for larger explicit class-level ranges and numerical comparison brackets, not required for existence of the small interval in this theorem.

### 2. Uniform quantitative rigidity and an explicit universal shape

For small e and normalized area deficit D=e[V(e)-area(S)], every unrestricted near-maximizer satisfies, after incoming-strip normalization and translation,

    d_H(A_e S,A_e S_e)<=C_* sqrt(D),
    A_e(x,y)=(e x,y).

Its entry/exit strip-normal mismatch is at most C_* e sqrt(D). The rescaled exact optimizer converges to an explicit convex body T at rate O(e^2), so the corresponding distance to T is O(sqrt(D)+e^2). These are results about the actual potentially nonconvex sets, not just their convex hulls. The scaling A_e compares shapes; it is not an affine transport of rigid motions.

See [REVERSE_STABILITY.md](REVERSE_STABILITY.md), [REVERSE_SET_STABILITY.md](REVERSE_SET_STABILITY.md), [UNIVERSAL_LIMIT_SHAPE.md](UNIVERSAL_LIMIT_SHAPE.md), and the final strengthening in [FLAT_CONTACT_ALIGNMENT.md](FLAT_CONTACT_ALIGNMENT.md). The constants are uniform but have not been numerically estimated.

### 3. Exact refined unrestricted asymptotics

Let T0=tan(sqrt(3)/2)/sqrt(3). Then

    M(pi-e)=C/e+C1 e+O(e^3),
    C=3(1+3T0)/[4(1+T0)]=1.35653373245229...,
    C1=(9-4T0-9T0^2)/[8(1+T0)^2]=0.09477330574913... .

Indeed e M(pi-e) has an even analytic extension to zero, determined by the exact formula V. The constant C is the area of the universal rescaled body T.

### 4. A larger explicit range for exact reverse-class optimality

For the ENTIRE aligned reverse class, exact optimality and uniqueness hold for

    beta >= beta_* = pi-arccos(sqrt(2)-1)
                       =114.4698005207... degrees.

This improves the earlier 120-degree cutoff. The candidate itself remains feasible at every obtuse bend. The sharper crossing argument is in [REVERSE_CROSSING_EXTENSION.md](REVERSE_CROSSING_EXTENSION.md); the complete extension and uniform weaker all-obtuse bound are in [REVERSE_EXTENDED_RESULTS.md](REVERSE_EXTENDED_RESULTS.md).

### 5. Attainment, continuity, and genuine crossings of optimal class values

The unrestricted, forward-class, and reverse-class suprema are attained and locally Lipschitz in beta; see [HALLWAY_WELL_POSEDNESS.md](HALLWAY_WELL_POSEDNESS.md).

The optimal aligned-class values have at least one crossing. Every such crossing lies between two exactly defined comparison angles:

    133.644346372 < beta_H (degrees) < 133.644346373,
    142.098382576 < beta_U (degrees) < 142.098382577.

The forward class strictly dominates below beta_H, and the reverse class strictly dominates above beta_U. **Neither number is asserted to be beta_c.** Uniqueness of the crossing, an exact forward solution in the middle range, and a global transition classification remain unresolved. Numerical crossings near 136.673 degrees are not substituted for those theorems.

The lower comparison uses an all-angle circular-notch construction of area

    H(beta)=pi/2+sin(beta)^2/[beta-sin(beta)cos(beta)].

See [CIRCULAR_NOTCH_CONSTRUCTION.md](CIRCULAR_NOTCH_CONSTRUCTION.md). This extends the familiar Hammersley construction; no priority claim is made for that family. In particular H(beta)=3/(2beta)+pi/2+O(beta) near zero, an improved elementary lower bound but not a sharp small-bend theorem.

## Reading order and dependency audit

For the strongest statement read:

1. [EXACT_NEAR_REVERSAL.md](EXACT_NEAR_REVERSAL.md): theorem statements, explicit value, scope, and limits.
2. [ANALYTIC_NEAR_REVERSAL_FOUNDATION.md](ANALYTIC_NEAR_REVERSAL_FOUNDATION.md): analytic small-parameter signs and an acyclic dependency order.
3. [FLAT_CONTACT_ALIGNMENT.md](FLAT_CONTACT_ALIGNMENT.md): why quadratic stability plus flat contacts eliminates the loss for unrestricted competitors.
4. [REVERSE_SET_STABILITY.md](REVERSE_SET_STABILITY.md), Section 1: the containing region, missing-area bound, and Hausdorff stability used by that argument.
5. [REVERSE_STABILITY.md](REVERSE_STABILITY.md) and [UNIVERSAL_LIMIT_SHAPE.md](UNIVERSAL_LIMIT_SHAPE.md), Sections 1-2: uniform coercivity and the explicit candidate limit.

The foundational geometry remains in [REVERSE_CAP_AREA.md](REVERSE_CAP_AREA.md), [REVERSE_GENERAL_MAJORANT.md](REVERSE_GENERAL_MAJORANT.md), [REVERSE_QUADRATIC_THEOREM.md](REVERSE_QUADRATIC_THEOREM.md), [REVERSE_GEOMETRIC_THEOREM.md](REVERSE_GEOMETRIC_THEOREM.md), and [ALIGNMENT_REDUCTION.md](ALIGNMENT_REDUCTION.md), Sections 1-4.

The unrestricted part of an earlier stability file is not used to prove the reverse stability on which exact unrestricted optimality depends. Independent review should especially check the nonsmooth cap identity, excursion/width corrections, uniform actual-set stability including boundary-height points, and the final flat-contact argument.

## Local checks and reproduction

The scalar checkers use only exact Python integers/rationals and integer square roots, with rational pi and Taylor remainder bounds. The numerical regression tests use NumPy, SciPy, and Shapely separately. No sampled geometry or local optimizer is part of an integer scalar certificate.

From this directory:

```sh
python extended_width_certificate.py --cells 256 --output extended-width.json
python branch_comparison_certificate.py --cells 512 --output branch-comparisons.json
python near_reversal_coefficients.py
python -m unittest -v test_round4 test_flat_alignment
```

All **37 new local tests passed**. This is not a rerun of the full older repository suite. The source dependency hashes, exact certificate summaries, rejected coarse covers, numerical profile checks, and reproduction commands are in [results/round4-checks.json](results/round4-checks.json). `limiting_profile.py` and `circular_notch.py` provide floating-point diagnostics, not proof certificates.

The completed third-round checks remain reproducible:

```sh
python parameter_certificate.py --cells 64 --output parameter-proof.json
python width_certificate.py --cells 64 --output width-proof.json
python reverse_value_certificate.py > value-proof.json
python -m unittest -v test_parameter_certificates test_reverse_exact test_reverse_value_certificate
```

Their original record is [results/theorem-checks.json](results/theorem-checks.json). Passing any of these tests does not independently verify the analytic geometry proofs.

## Preserved checkpoints, failures, and numerical data

[ROUND4.md](ROUND4.md) records the latest research progression. [ROUND4_NEGATIVE_RESULTS.md](ROUND4_NEGATIVE_RESULTS.md) retains the failed scalar alignment shortcut, the cutoff of the sufficient crossing estimate, rejected exact-interval covers, and pitfalls in converting area to set stability.

[REVERSE_MAIN_THEOREM.md](REVERSE_MAIN_THEOREM.md) and [ROUND3_NEGATIVE_RESULTS.md](ROUND3_NEGATIVE_RESULTS.md) retain the earlier exact reverse/asymptotic checkpoint. Its restriction to unrestricted bounds rather than equality has been superseded only on the unspecified near-reversal interval in the new theorem.

Rounds 1-2 remain in [THEORY.md](THEORY.md), [SWEPT_ENCLOSURE.md](SWEPT_ENCLOSURE.md), [NEGATIVE_RESULTS.md](NEGATIVE_RESULTS.md), [ROUND2.md](ROUND2.md), [INTERVAL_CERTIFICATES.md](INTERVAL_CERTIFICATES.md), [CLASS_BOUNDS.md](CLASS_BOUNDS.md), and [CLASS_EXCLUSIONS.md](CLASS_EXCLUSIONS.md). The original full-circle rigidity operator did not supply a sharp arbitrary-angle majorant.

All 14 nine-knot paths, poor candidates, unsuccessful optimizer terminations, the 17-knot refinement, 72 floating-point dense audits, and the false coarse-grid improvement remain in `results/angle-scan.json`, `results/refined90.json`, `results/enclosures.csv`, and `results/coarse-grid-counterexample.json`. The second-round search controls and seven rectangle certificates remain in `results/pressure-candidates.json` and `results/interval-manifest.json`. Those rectangle certificates use documented outward binary64 intervals; they are distinct from the new integer-only scalar checks.

Representative replays, without optimization:

```sh
python replay.py results/angle-scan.json --refinements 32 64 --output /tmp/hallway-replay.json
python replay.py results/refined90.json --refinements 64 --output /tmp/refined90-replay.json
python replay_pressure.py --candidate 150-reverse --samples 16385
```

Use an isolated environment and `requirements.txt` for the broader numerical experiment. No bitwise reproducibility across optimizer platforms is promised; saved controls avoid repeating the search.

## Literature and publication status

The proposed main contribution is exact unrestricted near-reversal optimality, uniqueness, and quantitative rigidity, together with the broader reverse-class and continuity/crossing results. A full literature and priority review remains necessary. The competing numerical branches and their approximate crossing were already reported by Xingyi He, arXiv:2608.11206v1; neither that phenomenon nor the pressure interpretation is claimed new. Related generalized-Gerver work is recorded in the earlier negative-results log.

Starting references include Jineon Baek, *Optimality of Gerver's Sofa*, arXiv:2411.19826, and Yoav Kallus and Dan Romik, *Improved upper bounds in the moving sofa problem*, arXiv:1706.06630. The repository's uniqueness manuscript motivated the initial question, but the new reverse optimization and alignment arguments do not use the uniqueness theorem.

- https://arxiv.org/html/2608.11206v1
- https://arxiv.org/abs/2411.19826
- https://arxiv.org/abs/1706.06630
