# Arbitrary-angle hallways: an explicit interval of globally optimal sofas

**Current status: fifth-round mathematical proof drafts, not independently reviewed or Lean-checked.** Start with [EXPLICIT_GLOBAL_CUTOFF.md](EXPLICIT_GLOBAL_CUTOFF.md). The draft now gives an explicit sufficient interval for unrestricted optimality and uniqueness, including **every bend from 177 degrees up to, but not including, 180 degrees**. The new proof does not require the fourth-round full Hausdorff stability theorem.

All earlier numerical data, failed approaches, and weaker proof checkpoints are retained. Statements about an unspecified cutoff in fourth-round files describe that earlier argument; the current explicit range is given here and in the new theorem.

## Scope and convention

The bend beta is the change in travel direction, 0<beta<pi. The classical hallway has beta=pi/2. Write e=pi-beta; this is the angle between the corridor rays pointing away from the corner. Both arms have unit width and the corner is sharp. This changes the actual hallway, not merely the sofa's rotation range within a right-angle hallway.

The branch starts at `16653ae81e0e4f52a362bafae2ad3440100ad065`. All changes stay under `experiments/hallway_angles/`. The existing paper, Lean libraries, and workflows are untouched. No CI, workflow dispatch/rerun, or Lean build was invoked. New commits carry `[skip ci]`.

## 1. Exact unrestricted optimality on an explicit interval

For every

    0<e<=1/19 radians, beta=pi-e,

one has

    M(beta)=V(e),

and the unique maximizing compact connected sofa, up to congruence, is the explicit convex S_e. No convexity, symmetry, smoothness, aligned endpoints, full actual width, or monotone motion is assumed for competitors.

The proved sufficient left endpoint is pi-1/19, enclosed in degrees by

    176.984432657 < cutoff < 176.984432658.

In particular every 177-, 178-, and 179-degree hallway is now covered. This is NOT the actual onset of reverse optimality or a claimed phase-transition angle.

The exact formula, with its continuous boundary and motion described in the reverse geometry files, is

    d0=cos e, q=sin e, m=2-d0,
    eta=sqrt((2-d0)/(2+d0)),
    K=sqrt(e^2+3(e/sin e)^2)/2,
    R=eta sin K/(cos K+eta sin K),
    V(e)=e/m+(1+2d0)/(4q)+3d0^2 R/(2q m^2).

The following are outward exact-integer evaluations of that formula, not optimized sampled-intersection areas. Their interpretation as unrestricted optima depends on the mathematical proof draft.

| Bend | Optimum lower endpoint | Optimum upper endpoint |
| --- | ---: | ---: |
| 177 degrees | 25.912848797 | 25.912848798 |
| 178 degrees | 38.865137208 | 38.865137209 |
| 179 degrees | 77.725311765 | 77.725311766 |

### What improved in the proof

The earlier argument invoked a uniform Hausdorff estimate, with existential constants, to compare flat contacts. The replacement uses only coordinatewise canonical-path errors and a rectangular core inside the majorant region. That core misses at most the normalized area deficit. A sharp elementary triangular-cap estimate then bounds its directional width.

This supplies explicit constants and a shorter geometric dependency chain:

    reverse cap/majorant + quadratic deficit
    -> coordinatewise path bounds
    -> rectangular core with a missing-area bound
    -> directional width obstruction
    -> zero entry/exit mismatch -> exact unrestricted optimum.

The new proof does not use the full Hausdorff theorem, a uniform inball construction, or limiting-shape convergence. It does still use the original cap identity, canonical crossing/excursions, the quadratic theorem, geometric realization, and the alignment-by-scaling lemma. These analytic dependencies still need independent review.

## 2. An explicit penalty for misaligned passages

For e<=1/100 and normalized area deficit D=e[V(e)-area(S)]<=1/10000, every complete passage satisfies

    |nu|<=40e sqrt(D),
    1-w_S<=11D,

where nu is the unoriented entry/exit strip-normal mismatch and w_S is the actual incoming-strip width. The aligned scaled canonical path has explicit rescaled coordinate errors at most 3sqrt(D) and 2sqrt(D).

For ALL feasible sofas in this e range, the corresponding area-penalty statement is

    V(e)-area(S)>=min{1/(10000e), nu^2/(1600e^3)}.

See [EXPLICIT_MOTION_RIGIDITY.md](EXPLICIT_MOTION_RIGIDITY.md). The constants are sufficient, not claimed optimal. This is a statement about every possible complete passage; it does not claim uniqueness of intermediate motions.

## Reading order

1. [EXPLICIT_GLOBAL_CUTOFF.md](EXPLICIT_GLOBAL_CUTOFF.md): current global theorem and exact constant propagation.
2. [CONTACT_RECTANGLE_LEMMA.md](CONTACT_RECTANGLE_LEMMA.md): the guaranteed core and missing-area directional-width estimate.
3. [EXPLICIT_PATH_CONSTANTS.md](EXPLICIT_PATH_CONSTANTS.md): uniform coordinatewise coercivity, asymmetric endpoint modes, and width corrections.
4. [EXPLICIT_MOTION_RIGIDITY.md](EXPLICIT_MOTION_RIGIDITY.md): explicit deficit, width, and mismatch bounds.

The foundational analytic files remain [REVERSE_CAP_AREA.md](REVERSE_CAP_AREA.md), [REVERSE_GENERAL_MAJORANT.md](REVERSE_GENERAL_MAJORANT.md), [REVERSE_QUADRATIC_THEOREM.md](REVERSE_QUADRATIC_THEOREM.md), [REVERSE_GEOMETRIC_THEOREM.md](REVERSE_GEOMETRIC_THEOREM.md), [REVERSE_STABILITY.md](REVERSE_STABILITY.md), and [ALIGNMENT_REDUCTION.md](ALIGNMENT_REDUCTION.md), Sections 1-4. The larger reverse-class range is in [REVERSE_EXTENDED_RESULTS.md](REVERSE_EXTENDED_RESULTS.md).

## Reproduce the fifth-round checks locally

```sh
python explicit_cutoff_certificate.py --cells 256 --output explicit-cutoff.json
python explicit_motion_rigidity.py --cells 256 --output motion-rigidity.json
python -m unittest -v test_explicit_cutoff test_explicit_motion_rigidity
# Reproduce proofs, rejected cases, scalar values, source hashes, and all 22 new tests:
python round5_check.py --output results/round5-checks.json
```

All **22 new local tests passed, with none skipped**. This is not a rerun of the older full repository suite. [results/round5-checks.json](results/round5-checks.json) records the exact rational slacks, source Git blob hashes, tested package versions, rejected checks, and scalar values.

The certificate commands use only Python's standard library: outward fixed-denominator integer intervals, rational series remainders, exact fractions, and integer square roots. They cover all e in the closed interval [0,1/10], including the removable endpoint at zero, rather than testing a list of angles. The separate regression tests use NumPy and Shapely. A certificate's numerical correctness does not independently establish its correspondence with the geometric proof.

`round5_check.py` verifies the pinned baseline source hashes before running. It intentionally rejects a changed baseline until the changed mathematics/code is reviewed. Full per-cell certificate margins can be regenerated; the compact result record retains their canonical SHA-256 hash.

## Failures and limits

[ROUND5_NEGATIVE_RESULTS.md](ROUND5_NEGATIVE_RESULTS.md) records the unsuccessful extrapolation to e=53/1000, an inconclusive one-cell cover, and an exact counterexample to dropping the triangular-cap regime from the width lemma. Failure of a sufficient cutoff estimate is not a counterexample to the candidate's optimality.

No unrestricted optimum at 150 or 170 degrees is asserted by the new explicit cutoff. The middle-angle forward problem and a unique global phase transition remain unresolved. No publication-priority claim follows from the numerical checks or a keyword search.

## Retained results from earlier rounds

The fourth-round [EXACT_NEAR_REVERSAL.md](EXACT_NEAR_REVERSAL.md) and [FLAT_CONTACT_ALIGNMENT.md](FLAT_CONTACT_ALIGNMENT.md) retain the earlier unspecified-cutoff argument. Their full-set Hausdorff/limit-shape results are separate from, and not needed for, the new explicit proof. The limit-shape and refined area expansion remain in [UNIVERSAL_LIMIT_SHAPE.md](UNIVERSAL_LIMIT_SHAPE.md) and `near_reversal_coefficients.py`.

Other retained theorem drafts include exact reverse-class optimality for beta>=pi-arccos(sqrt(2)-1), approximately 114.4698 degrees; attainment/local Lipschitz continuity of the value functions; and comparison roots enclosing all aligned-class crossings between about 133.6443 and 142.0984 degrees. Those roots are not beta_c. The all-angle circular-notch construction has area pi/2+sin(beta)^2/[beta-sin(beta)cos(beta)]. This fifth round does not claim to have independently rechecked all those separate proofs.

Their original checks remain reproducible:

```sh
python extended_width_certificate.py --cells 256 --output extended-width.json
python branch_comparison_certificate.py --cells 512 --output branch-comparisons.json
python near_reversal_coefficients.py
python -m unittest -v test_round4 test_flat_alignment
python parameter_certificate.py --cells 64 --output parameter-proof.json
python width_certificate.py --cells 64 --output width-proof.json
python reverse_value_certificate.py > value-proof.json
```

Rounds 1-2 retain all 14 nine-knot paths, poor candidates and unsuccessful optimizer terminations, the 17-knot refinement, 72 floating-point dense audits, the false coarse-grid improvement, and seven binary64 interval rectangle certificates. See `results/angle-scan.json`, `results/refined90.json`, `results/enclosures.csv`, `results/coarse-grid-counterexample.json`, `results/pressure-candidates.json`, and `results/interval-manifest.json`. They are not repackaged as exact scalar proofs or global optima.

Use `requirements.txt` in an isolated environment for the broader numerical experiment. Representative frozen-path replays are `python replay.py results/angle-scan.json --refinements 32 64 --output /tmp/replay.json` and `python replay_pressure.py --candidate 150-reverse --samples 16385`.

## Literature and publication status

The proposed contribution is now an explicit interval of unrestricted optimality and uniqueness, with quantitative rigidity and the broader reverse-class results. Independent mathematical and priority review remain necessary. The competing numerical branches and approximate crossing were reported by Xingyi He, arXiv:2608.11206v1; neither that phenomenon nor the pressure interpretation is claimed new.

Starting references are Jineon Baek, *Optimality of Gerver's Sofa*, arXiv:2411.19826; Yoav Kallus and Dan Romik, *Improved upper bounds in the moving sofa problem*, arXiv:1706.06630; and He, *A Gas-Driven Algorithm for Variants of the Moving Sofa Problem*, arXiv:2608.11206. Related generalized-Gerver work is recorded in earlier research logs. The uniqueness manuscript motivated the original question, but the new reverse functional and alignment arguments do not use its uniqueness theorem.
