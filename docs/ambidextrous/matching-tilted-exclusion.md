# An executed full-width exclusion for steeply separated extreme heights

**This is a restricted ordinary-area theorem, not unrestricted optimality.** It completes the width covering for one nontrivial extreme-height region using the existing AM1 verifier, without curvature, full-turn, contact-order, symmetry, or auxiliary-area assumptions. The mathematical dependencies remain subject to independent review.

## 1. Statement and reduction to the certificate

Use the common incoming strip of height one and translate the horizontal projection of a compact connected ambidextrous body S to [0,W]. Suppose S contains actual extreme points

$$
P=(0,a),\qquad Q=(W,b),\qquad
19/20\le a\le1,\quad0\le b\le1/20.
$$

**Theorem AM2.** In this region,

$$
\boxed{|S|\le84151/51200<411/250<M.}
$$

The reflected low-left/high-right region has the same bound, by reflecting the incoming strip vertically and exchanging the turns. In particular a body of area at least M cannot have actual extreme witnesses with |a-b|>=19/20. The theorem does not claim to exclude every pair with |a-b|>=9/10; that larger set is not the same as the two certified rectangles.

**Proof, apart from the executed finite replay below.** If W<=2, use the analytic AW-W bound |S|<41/25, which is smaller than 84151/51200. If |S|<=8/5 there is nothing to prove. Otherwise the five-case anchor theorem AL1 gives W<=2999/1020. It remains to cover [2,2999/1020] in the specified height rectangle. The following certificate does exactly that. AM1 turns every accepted bin into an ordinary-area bound, and their maximum is 84151/51200.

For the candidate comparison, y=149/500 satisfies 4y^3+3y-1<0, hence is below the positive candidate root. Integrating 1/(1+t^2)>1-t^2 gives

$$
M>1+4y^2+y-y^3/3=616648051/375000000>411/250.
$$

No decimal approximation is used in the comparisons. The inequalities invoked are repeated in [anchor-matching-certificates.md](anchor-matching-certificates.md), and AL1 is in [anchor-width-localization.md](anchor-width-localization.md).

## 2. Complete finite covering

Each bin uses 80 by 32 cells, with a single common width coordinate as in AM.1. The rows give width interval, number of automatically re-derived empty cells E, number of disjoint incompatible pairs P, and the exact conditional area bound W_hi*(2560-E-P)/2560.

| Width interval | E | P | Exact bound |
|---|---:|---:|---:|
| [2,41/20] | 179 | 349 | 5207/3200 |
| [41/20,21/10] | 209 | 351 | 105/64 |
| [21/10,43/20] | 238 | 365 | 84151/51200 |
| [43/20,11/5] | 273 | 375 | 2629/1600 |
| [11/5,9/4] | 307 | 386 | 16803/10240 |
| [9/4,91/40] | 341 | 386 | 166803/102400 |
| [91/40,23/10] | 366 | 392 | 20723/12800 |
| [23/10,47/20] | 385 | 398 | 83519/51200 |
| [47/20,12/5] | 425 | 396 | 5217/3200 |
| [12/5,49/20] | 462 | 410 | 10339/6400 |
| [49/20,5/2] | 510 | 410 | 205/128 |
| [5/2,51/20] | 558 | 405 | 81447/51200 |
| [51/20,13/5] | 594 | 400 | 10179/6400 |
| [13/5,53/20] | 653 | 374 | 81249/51200 |
| [53/20,27/10] | 696 | 356 | 10179/6400 |
| [27/10,11/4] | 743 | 332 | 3267/2048 |
| [11/4,14/5] | 796 | 312 | 2541/1600 |
| [14/5,57/20] | 846 | 285 | 81453/51200 |
| [57/20,29/10] | 890 | 264 | 20387/12800 |
| [29/10,2999/1020] | 943 | 240 | 80973/51200 |

For individual rows below 8/5, the unconditional bound is max(8/5, the displayed expression). This does not change the maximum across all rows. The intervals are adjacent, and all 7,186 pairs were individually checked with integer arithmetic. Their incompatibilities use only frames passing the exact AA1 angle-guarantee tests.

## 3. Reproduction and proof-data policy

The committed recipe generates every concrete witness and immediately replays it:

```sh
python docs/ambidextrous/computer-assisted/occupancy/reproduce_tilted_matching.py --output-dir /tmp/tilted-cover
python docs/ambidextrous/computer-assisted/occupancy/verify_anchor_matching.py /tmp/tilted-cover/tilted_full_width.json
```

Generation uses NumPy and NetworkX; the second command uses only standard-library unbounded integers and fractions. The generator's proposed matching need not be maximum for the theorem. It is accepted only after independently checking its disjointness, every geometric incompatibility, all inferred empty cells, actual angle coverage, and complete width coverage.

The complete raw witness JSON and full replay reports are supplied in the accompanying session bundle. Its raw JSON SHA-256 is

`5a3bf2f8ea7402057b435f291c4a65eb1ffece6f5ee80741f28c3fc65f5bfff7`.

A fresh execution of the committed recipe reproduced that hash and the stated bound. The unchanged verifier has Git blob `9e6b28e0dd55d8b49ae25146d1e277019acfe592`. Source identity checks and mutation controls are recorded separately.

An attempted large compressed-payload transcription did not match the executed data and was removed in commit 244b953. That withdrawn payload is not a certificate or a proof input. Source control retains the compact reproducibility recipe; the bundle retains the correct complete witness file. No claim that the withdrawn file passed replay is made.

## 4. Remaining scope

This is an entire-width result, unlike the older certificate confined to widths near 2.9. It still excludes only the stated extreme-height rectangles. In particular it does not locate endpoints of equal height near height one half. Nor does it imply a neighborhood of the candidate in support, derivative, or curvature topology.

The paired-cell bounds remain too weak in several balanced-height trials. Ordinary-area optimality in those regions and at the sharp candidate still needs additional arguments. No CI, Lean/Lake compilation, dependency installation, or manuscript build was used.
