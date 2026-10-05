# Oblique hallways: exact reverse sofas and sharp asymptotics

**Current status:** a new mathematical proof draft, accompanied by exact-integer scalar certificates and local regression tests. It is not independently reviewed or Lean-checked. The earlier numerical experiments and unsuccessful approaches are retained. Start with [REVERSE_MAIN_THEOREM.md](REVERSE_MAIN_THEOREM.md).

## Scope and angle convention

The actual bend `beta` is the change in travel direction, with `0 < beta < pi`. The classical hallway has `beta=pi/2`. Write `epsilon=pi-beta` for the angle between the corridor rays pointing away from the junction. This is not Baek's sofa-rotation parameter inside the original right-angle hallway.

The work starts from `main` at `16653ae81e0e4f52a362bafae2ad3440100ad065`. All changes remain under `experiments/hallway_angles/`; the existing paper, Lean libraries and workflows are untouched. No CI, workflow dispatch/rerun, or Lean build was invoked. Commits carry `[skip ci]`.

## Main theorem drafts

### Exact optimality and uniqueness in the aligned reverse class

For every `120 degrees <= beta < 180 degrees`, the supremum in the entire aligned reverse-turn class is the explicit elementary function `V(epsilon)` in the main theorem. Its maximizer is unique up to horizontal translation in normalized coordinates and is an explicitly constructed convex sofa. Competitors need not be convex, symmetric, smooth, of full actual strip width, or moved monotonically. These properties are not silently imposed as a numerical ansatz.

The candidate is continuously feasible for every `90 degrees < beta < 180 degrees`; the full-class upper-bound proof currently covers the smaller interval starting at 120 degrees.

### A sharp asymptotic for the unrestricted problem

Let `M(beta)` be the supremum over arbitrary compact connected moving sofas, without an aligned-motion restriction. Set

    T0 = tan(sqrt(3)/2)/sqrt(3),
    C  = 3(1+3*T0)/(4*(1+T0)) = 1.35653373245229... .

The draft proves

    M(pi-epsilon) = C/epsilon + O(epsilon),  epsilon -> 0+.

It also gives an explicit sandwich. For `0<epsilon<=pi/3`, put

    U(epsilon) = max{V(epsilon), 2 sec(epsilon/2)}.

Then

    V(epsilon) <= M(pi-epsilon) <= U(epsilon)+1/(4*U(epsilon)).

For every bend at least 143 degrees the exact-integer scalar checker proves that `U=V`. The proof uses an asymptotically lossless alignment by uniform scaling and an additional exit-arm rotation. It does not assume the original unscaled sofa belongs to either aligned class.

**Not claimed:** unrestricted fixed-angle equality `M=V`, an exact forward-class solution, or a unique phase transition near the observed numerical branch crossing.

## Rigorous scalar enclosures from the formulas

These outward-rounded bounds depend on the mathematical theorem drafts, not on a local optimizer. The interval evaluations themselves use exact integers.

| Bend beta | Reverse-class optimum: lower | Reverse-class optimum: upper | Unrestricted upper bound |
| --- | ---: | ---: | ---: |
| 120 degrees | 1.399979511 | 1.399979512 | 2.417655 |
| 135 degrees | 1.803764167 | 1.803764168 | 2.280270 |
| 137 degrees | 1.880508238 | 1.880508239 | 2.265875 |
| 143 degrees | 2.163006742 | 2.163006743 | 2.278587 |
| 150 degrees | 2.641025081 | 2.641025082 | 2.735686 |
| 170 degrees | 7.788929081 | 7.788929082 | 7.821026 |
| 179 degrees | 77.725311765 | 77.725311766 | 77.728529 |

The reverse-class lower endpoint is also an unrestricted lower bound. At smaller bends the older forward constructions can give a stronger unrestricted lower bound; this table is not a catalog of best numerical records.

## Proof reading order

1. [REVERSE_MAIN_THEOREM.md](REVERSE_MAIN_THEOREM.md): definitions, exact class theorem, uniqueness, unrestricted asymptotics, and trust boundary.
2. [REVERSE_CAP_AREA.md](REVERSE_CAP_AREA.md): the support-cap area identity, including nonsmooth convex hulls.
3. [REVERSE_QUADRATIC_THEOREM.md](REVERSE_QUADRATIC_THEOREM.md): strict continuous quadratic maximization, including asymmetric free-endpoint variations.
4. [REVERSE_GENERAL_MAJORANT.md](REVERSE_GENERAL_MAJORANT.md): canonicalization, actual strip width, and bounds for outside-strip excursions. Its final scalar comparisons are completed in the main theorem.
5. [REVERSE_GEOMETRIC_THEOREM.md](REVERSE_GEOMETRIC_THEOREM.md): convexity, all-pose wedge avoidance, complete entry/exit motion, and exact area attainment.
6. [ALIGNMENT_REDUCTION.md](ALIGNMENT_REDUCTION.md): scaling and strip-width interpolation for arbitrary motions, quantitative unrestricted bounds, and the sharp leading constant.

[REVERSE_VARIATIONAL.md](REVERSE_VARIATIONAL.md) is an earlier conditional checkpoint, retained to document the route rather than presented as the final majorant. [ROUND3_NEGATIVE_RESULTS.md](ROUND3_NEGATIVE_RESULTS.md) records the failed shortcuts and corrections. Independent review should focus on the nonsmooth cap identity, excursion inequalities, free-endpoint quadratic calculation, and alignment argument.

## Reproduce the new theorem checks locally

The exact-integer checkers require only the Python standard library. The independent numerical formula/collision tests additionally require NumPy. From this directory:

```sh
python parameter_certificate.py --cells 64 --output parameter-proof.json
python width_certificate.py --cells 64 --output width-proof.json
python reverse_value_certificate.py > value-proof.json
python -m unittest -v test_parameter_certificates test_reverse_exact test_reverse_value_certificate
```

All **31 new local tests passed**. This does not assert that the earlier full test suite was rerun in the third round. The record is [results/theorem-checks.json](results/theorem-checks.json).

`parameter_certificate.py` proves positivity on whole parameter intervals using fixed-denominator dyadic integer arithmetic. Pi is enclosed by exact Machin-series bounds; sine/cosine use Taylor polynomials with exact rational remainder bounds; square roots use integer `isqrt`. `width_certificate.py` handles a removable endpoint using sinc. The certificate proofs do not use binary64 arithmetic, platform trigonometric functions, NumPy, Shapely, or the optimizer. Their remaining trust is the implementation and exact integer/rational operations, not a Lean kernel.

`reverse_exact.py` is a separate floating-point evaluator of the analytic candidate. Its polygon, finite-difference and quadrature tests are regression evidence, not the certificate proof.

## Earlier rounds: retained results and reproduction

Round 1 developed the oblique support displacement operator, analytic baselines, a seeded nonconvex path search in both rotation directions, and swept-wedge inner constructions. [THEORY.md](THEORY.md), [SWEPT_ENCLOSURE.md](SWEPT_ENCLOSURE.md), and [NEGATIVE_RESULTS.md](NEGATIVE_RESULTS.md) retain those derivations. The full-circle rigidity operator by itself did not supply a sharp area majorant.

All 14 nine-knot paths, including poor candidates and failed optimizer terminations, remain in `results/angle-scan.json`. The 17-knot right-angle refinement is in `results/refined90.json`; all 72 floating-point denser-grid audits are in `results/enclosures.csv`. A false apparent right-angle improvement from coarse sampling remains in `results/coarse-grid-counterexample.json`. None of those sampled areas is an optimality proof.

Round 2 added exposed-wall gradients, multilevel linear/cubic discovery bases, seven independent continuous-motion rectangle certificates, and elementary whole-class bounds. See [ROUND2.md](ROUND2.md), [INTERVAL_CERTIFICATES.md](INTERVAL_CERTIFICATES.md), [CLASS_BOUNDS.md](CLASS_BOUNDS.md), and [CLASS_EXCLUSIONS.md](CLASS_EXCLUSIONS.md). The old rectangle certificates use documented binary64 outward intervals, unlike the new integer-only scalar checkers. Their paths and exact area fractions remain in `results/pressure-candidates.json` and `results/interval-manifest.json`.

Install the broader numerical experiment dependencies in an isolated environment using `requirements.txt`. Representative replay commands, without repeating optimization:

```sh
python replay.py results/angle-scan.json --refinements 32 64 --output /tmp/hallway-replay.json
python replay.py results/refined90.json --refinements 64 --output /tmp/refined90-replay.json
python replay_pressure.py --candidate 150-reverse --samples 16385
```

See the individual modules' `--help` and the interval-certificate document for the original discovery and certificate-generation commands. No bitwise reproducibility across optimizer platforms is promised; saved coordinates avoid repeating the search.

## Literature and publication positioning

The intended contribution is the exact reverse-class solution and sharp unrestricted asymptotics, subject to mathematical and priority review. The two competing numerical branches and their approximate crossing are not new claims: they appear in Xingyi He's *A Gas-Driven Algorithm for Variants of the Moving Sofa Problem*, arXiv:2608.11206v1. A complete novelty check remains necessary; a search also surfaced an angled-corridor Gerver-family preprint discussed in the third-round negative-results log.

Other starting references are Jineon Baek, *Optimality of Gerver's Sofa*, arXiv:2411.19826, and Yoav Kallus and Dan Romik, *Improved upper bounds in the moving sofa problem*, arXiv:1706.06630. The repository's uniqueness manuscript motivated the initial questions, but the new reverse functional and alignment argument do not depend on the uniqueness theorem.

- https://arxiv.org/html/2608.11206v1
- https://arxiv.org/abs/2411.19826
- https://arxiv.org/abs/1706.06630
