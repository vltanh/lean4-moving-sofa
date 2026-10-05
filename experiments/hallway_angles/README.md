# Arbitrary hallway angles: research experiment

**Status:** a reproducible numerical experiment and pen-and-paper derivations, not a theorem of global optimality. No sharp arbitrary-angle version of Baek's `Q` was obtained. The numerical geometry is not interval-certified, and none of the new derivations is Lean-checked.

## Scope and angle convention

Change the **actual bend** of a sharp, unit-width hallway. Write `beta` for the change in travel direction, with `0 < beta < pi`; `beta = pi/2` is the classical hallway. The angle between the two rays pointing away from the corner is `pi-beta`. This is **not** Baek's sofa-rotation parameter `omega` inside the original right-angle hallway.

The work starts from `main` at `16653ae81e0e4f52a362bafae2ad3440100ad065`. All changes are confined to `experiments/hallway_angles/`; existing paper and Lean claims are untouched. No CI, Lean build, workflow dispatch, or workflow rerun was invoked. Commits carry `[skip ci]`.

## What the experiment establishes and what it does not

**An ingredient of rigidity generalizes.** The oblique tangent-displacement operator is

$$D_\beta h(t)=\frac{h(t+\beta)-\cos\beta\,h(t)}{\sin\beta}-h'(t).$$

It retains the Mamikon square-gap identity. On full-circle periodic `H^1` functions, its kernel consists exactly of translations, `span{cos t, sin t}`. The proof uses the Fourier multiplier and is in [THEORY.md](THEORY.md). Extending this to the actual partial contact arcs, and obtaining a sharp geometric area majorant, remain necessary. The operator alone is not an arbitrary-angle sofa solver.

**There are exact analytic baselines.** The translation-only class has optimum `csc(beta)`. A fixed-inner-corner rotating family has area `beta+cot(beta)` for `beta<pi/2` and `pi/2` otherwise. These are elementary constructions used for regression tests; no novelty is claimed for them, and neither is the general rotating optimum.

**The direct path-area objective is not concave.** [NEGATIVE_RESULTS.md](NEGATIVE_RESULTS.md) gives an exact three-knot counterexample, as well as a saved numerical example where a successful optimizer overstates continuous feasibility. Affine shearing also fails to preserve rigid motion. These rule out shortcuts suggested by an overly direct transfer of the uniqueness argument.

**Useful numerical candidates can nevertheless be found and checked more carefully.** The code performs seeded local, nonconvex optimization of piecewise-linear corner paths. It tests two endpoint rotation directions without imposing reflection symmetry in the full path search. The largest connected polygon component is retained, rather than adding disconnected pieces. The two families and the coordinate bounds are explicit restrictions, not an exhaustive classification of motions.

## Results from the completed runs

The first scan used 9 corner knots, 33 optimization poses, one full-coordinate local run per angle/direction, and seed 0. The following are **floating-point inner-construction areas**, using the improved swept-wedge enclosure at 513 validation poses. They are not certified decimal lower bounds or global optimum values.

| Bend angle beta | Forward rotation | Reverse rotation |
| --- | ---: | ---: |
| 30 degrees | 5.305425 | 0.806161 |
| 60 degrees | 2.881108 | 0.889618 |
| 90 degrees | 2.207172 | 1.034126 |
| 120 degrees | 1.939595 | 1.396302 |
| 135 degrees | 1.864048 | 1.798377 |
| 137 degrees | 1.855714 | 1.874825 |
| 150 degrees | 1.809627 | 2.632578 |

Among these **particular saved paths**, the better rotation direction changes between bend angles 135 and 137 degrees. At 135 degrees the forward inner area exceeds the reverse raw sampled area; at 137 degrees the reverse inner area exceeds the forward raw sampled area. This comparison is robust to the reported per-path enclosure gaps, subject to floating-point qualifications. It does not establish a global phase-transition angle or exclude other motions. Competing rotation patterns have already been investigated numerically by He [4].

A separate right-angle refinement used 17 knots, seed 7, and two local restarts. At 1025 validation poses, its raw sampled area is **2.2183633893765324**, while the swept inner-construction area is **2.2150879931699343**. This is a refinement check, not an improvement on Gerver or a claim to reproduce Gerver exactly.

### Why raw sampled area is insufficient

The original right-angle run reported optimizer success and area **2.2316541712516575** at 33 poses. Holding the path fixed and checking 1025 poses reduced that area to **2.213028228128224**. The apparent improvement was an artifact of sampling; the path and unsuccessful inference are retained in `results/coarse-grid-counterexample.json`.

The first continuous-motion construction tightened every sampled hallway by a Lipschitz margin. It is simple but loses substantial area. The second construction encloses the swept forbidden corner by convex hulls of endpoint wedges, with second-order interpolation margins. For the same saved 9-knot right-angle path and 1025 poses, this improves the inner area from **2.187465851663766** to **2.2097998645873833**. See [SWEPT_ENCLOSURE.md](SWEPT_ENCLOSURE.md) for the exact-real argument, including the necessary expansion of the clipping box. Quadratic margins do not imply a quadratic rate of area convergence.

Both methods have exact-real inclusion arguments, but the implementation uses NumPy and GEOS. A numerical guard and dense audit are not a rounding-error proof. Exact/interval arithmetic is required before interpreting the decimals as certified lower bounds. No computed global upper bound is claimed.

## Reproduce locally

Requires Python 3.11 or later; tested with Python 3.13.5 and the versions in `requirements.txt`. Use an isolated Python environment. From the repository root:

```sh
cd experiments/hallway_angles
python -m pip install -r requirements.txt
python -m unittest discover -v
```

The completed local test run passed **30 tests**. All **72 saved whole-polygon dense audits** reported zero area outside the denser sampled intersection, in floating-point arithmetic. These checks are local numerical tests, not CI or Lean verification. The record is in `results/validation.json`.

Replay all saved paths with the tighter enclosure, without re-running discovery:

```sh
python replay.py results/angle-scan.json \
  --refinements 32 64 --output /tmp/hallway-swept-replay.json
```

Replay the simpler first-order margins:

```sh
python replay.py results/angle-scan.json --method lipschitz \
  --refinements 8 32 128 --output /tmp/hallway-lipschitz-replay.json
```

Re-run the original discovery experiment:

```sh
python search.py --angles 30 60 90 120 135 137 150 \
  --knots 9 --subdivisions 4 --restarts 1 --maxiter 65 --seed 0 \
  --refinements 8 32 128 --output /tmp/hallway-angle-scan.json
```

Re-run the 17-knot right-angle refinement from the saved 9-knot result:

```sh
python replay.py results/angle-scan.json --angles 90 --modes forward \
  --refine-knots 17 --restarts 2 --maxiter 80 --seed 7 \
  --refinements 32 64 --output /tmp/hallway-refined90.json
```

Or validate the already saved refined path without optimization:

```sh
python replay.py results/refined90.json --refinements 64 \
  --output /tmp/hallway-refined90-replay.json
python rigidity.py --max-mode 32
```

`subdivisions` counts samples per corner-path segment. With `k` knots, there are `(k-1)*subdivisions+1` poses. Every path knot is included. A denser audit doubles that angular sampling density. Seeds and versions are recorded, but bitwise reproducibility of optimizer outcomes across platforms is not promised; replaying saved coordinates avoids that source of variation.

## File map and provenance

- `geometry.py`, `search.py`: hallway model, analytic baselines, local path search, optimizer status recording.
- `enclosure.py`, `swept.py`: first-order and improved continuous-motion inner constructions.
- `rigidity.py`: oblique support-line algebra and full-circle Fourier diagnostics.
- `replay.py`: frozen-path validation and optional knot refinement.
- `test_hallway_angles.py`, `test_swept.py`: 30 local tests covering baselines, geometry, negative results, and enclosures.
- `THEORY.md`, `SWEPT_ENCLOSURE.md`, `NEGATIVE_RESULTS.md`: derivations, assumptions, and failures.
- `results/angle-scan.json`: all 14 saved 9-knot paths, shared run parameters, coordinate restrictions, and every local optimizer outcome. Numeric values of analytic formulas are stored as floats.
- `results/refined90.json`: the 17-knot path, both restart outcomes, and its validation records.
- `results/enclosures.csv`: all 72 refinement records, including raw total/largest-component areas, inner areas, margins, component counts, and audits.
- `results/coarse-grid-counterexample.json`, `results/validation.json`: the failed sampling inference and the final local validation summary.

During execution, the original scan was named `scan.json`; its archived path is `results/angle-scan.json`. Repeated metadata was compacted and its enclosure records moved to the CSV without rounding the saved coordinates or area records. The `input` field in the refined run preserves that original execution filename.

## Research log

1. Recorded scope and failure criteria before implementation; did not assume an arbitrary-angle sharp `Q` exists.
2. Derived the unit-normal geometry, oblique tangent equation, full-circle kernel, and two exact baselines.
3. Implemented the local search; retained the coarse-grid false improvement as a regression fixture.
4. Proved nonconcavity of the direct path-area objective and recorded why affine transport and partial-arc shortcuts fail.
5. Completed both-direction scans at seven bend angles, including poorly performing candidates rather than discarding them.
6. Replaced the overly conservative first-order validation with a tighter swept-wedge construction; retained both methods and their numerical results.
7. Completed the 17-knot refinement, saved all results, and passed 30 local tests. No CI or Lean build was attempted.

The main unresolved mathematical step is a **sharp area majorant with the correct arbitrary-angle admissible domain and contact-arc structure**. The oblique square-gap operator is an ingredient for that project, not a substitute for it. The code is useful for generating and checking conjectural geometry while those missing steps are investigated.

## References

[1] Jineon Baek, *Optimality of Gerver's Sofa*, arXiv:2411.19826, especially the cap/niche construction and the Gerver-specific core/tail decomposition of the concave bound: <https://arxiv.org/html/2411.19826v1>.

[2] This repository's uniqueness manuscript, branch `paper/uniqueness-arxiv`, `docs/paper/sections/08-equality.tex`: the Mamikon square-gap identity and support-function tangent equations.

[3] Yoav Kallus and Dan Romik, *Improved upper bounds in the moving sofa problem*, arXiv:1706.06630: <https://arxiv.org/abs/1706.06630>.

[4] Xingyi He, *A Gas-Driven Algorithm for Variants of the Moving Sofa Problem*, arXiv:2608.11206: <https://arxiv.org/html/2608.11206v1>. Relevant numerical prior work on changing the actual corridor angle and competing motion patterns, not a global optimality proof. Its corridor-ray-angle convention is supplementary to our bend-angle convention. This experiment does not claim the first arbitrary-angle numerical search or improved numerical records over that work.
