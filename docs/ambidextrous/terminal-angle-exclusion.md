# A complete rational exclusion of reduced turns through 2 arctan(29/50)

**This is an endpoint-angle theorem, not unrestricted optimality or full-quarter-turn completion.** It supplies a completed ordinary-area certificate without assumptions on the extreme-point heights, curvature, contact order, symmetry, or a candidate neighborhood. Labels TE are local. The canonical motion reduction and the elementary strip estimates are the stated mathematical dependencies; their historical proofs remain subject to independent review.

## 1. Statement

Let S be a compact connected ambidextrous body in the branch's common incoming unit-height normalization, with area at least 41/25. Let alpha and gamma denote the magnitudes of its conventional reduced lower and upper turns.

**Theorem TE1.**

$$
\boxed{\alpha>2\arctan(29/50),\qquad\gamma>2\arctan(29/50).}
$$

The threshold is greater than pi/3: tan(pi/6)=1/sqrt(3), and 3*29^2=2523>2500=50^2. Its approximate value in degrees is 60.2274663, but no rounded value is used by the proof. In particular all hallway orientations through pi/3 are actually visited in both turns for this area class.

## 2. Ordinary-area proof mechanism

The general canonical/sign reduction for area greater than 8/5 gives alpha,gamma in (arccos(5/8),pi/2], with the two-strip determinant estimates of CF.8. Angles with tan(alpha/2)<=12/25 are already excluded by the exact bound

$$
|S|\le769/481<8/5<41/25.
$$

Suppose instead tan(alpha/2) belongs to [12/25,29/50]. Use the body's incoming and terminal unit strips as coordinates:

$$
u=x\cos\alpha+y\sin\alpha,\qquad v=y.
$$

After translation the transformed body is in [0,1]^2, and its area is |S| cos(alpha). No width or extreme-height condition is added. Partition that square into 24 by 24 cells. For each angular bin, reconstruct all physical hallway frames guaranteed visited by CF.9, and bound their scalar products over each cell and the full endpoint interval using exact rational arithmetic.

The forbidden-triple equivalence CF1 gives z_P+z_Q+z_R<=2 for each recorded triple of cells. Their nonnegative integer weights are divided by their largest vertex load. This makes each vertex load at most one exactly, even if rounding an LP dual produced a small infeasibility before normalization. CF2 then bounds ordinary area by

$$
\frac{576-\sum_e m_e/\max_i\sum_{e\ni i}m_e}{576\cos\alpha_{\rm hi}}.
$$

Both geometric separations are checked strictly greater than one. There is no use of a signed curve area, hull repair, solver optimality status, floating-point rounding direction, or hypothetical full turn.

The certificate covers [12/25,29/50] by the eleven adjacent bins below. Every exact upper bound is less than 41/25. This contradicts the assumed area and proves the lower-turn conclusion. Reflecting the incoming strip exchanges the two motions, giving the upper-turn conclusion by the same covering. The complete continuum-to-finite proof is CF1--CF2 in [configuration-area-certificate.md](configuration-area-certificate.md); this note supplies the previously missing executed covering.

## 3. Executed covering

Every row uses n=24. The last column is the exact rational upper bound from the independent verifier, not a solver's reported objective.

| Half-tangent interval | Checked triples | Exact ordinary-area upper bound |
|---|---:|---:|
| [12/25,49/100] | 15 | 136411/85824 |
| [49/100,1/2] | 18 | 175/108 |
| [1/2,51/100] | 60 | 6892747/4261824 |
| [51/100,13/25] | 85 | 106197613939/65664065664 |
| [13/25,53/100] | 112 | 1122923567267/690336690336 |
| [53/100,27/50] | 138 | 554479711361/340032340032 |
| [27/50,11/20] | 196 | 65287819273/40176040176 |
| [11/20,14/25] | 201 | 44827531835/27456027456 |
| [14/25,57/100] | 231 | 99224304808/60759060759 |
| [57/100,23/40] | 269 | 62972922431/38556038556 |
| [23/40,29/50] | 281 | 223047107803/136512136512 |

There are **1,606 concrete triple witnesses**, with no unresolved bin in this declared interval. The largest exact bound is

$$
223047107803/136512136512<41/25,
$$

with positive target margin 20819901917/3412803412800. The smallest strict geometric margin in each bin is retained in the complete replay report. The hypotheses area>8/5 underlying the motion guarantees are always met in the contradiction proving TE1.

## 4. Reproduction and stored data

The committed generator proposes the finite data and immediately calls the existing independent verifier:

```sh
python docs/ambidextrous/computer-assisted/discover_terminal_cover.py --output-dir /tmp/terminal-cover
python docs/ambidextrous/computer-assisted/verify_configurations.py /tmp/terminal-cover/terminal_to_29_50.json
```

The first command uses NumPy/SciPy for discovery. The second needs only the Python standard library and unbounded integer/rational arithmetic. A failed exact check terminates generation; there is no provision for declaring an unresolved bin to be near the candidate.

The complete raw witness JSON and detailed replay/discovery records are included in the accompanying session bundle. Its raw certificate SHA-256 is

`7e2b52b8146559aa62dc11898ba03c297775a8be0149cce418ba958b3e4d4a71`.

The unchanged verifier has Git blob `53bc46650ffe7533fb614606264bb93899a8bdb8` and SHA-256 `0b3bc854d902bd4b7808efed91c4a6f84b3909bd11ea3f8955fc2eb96e2e021f`. A fresh execution of the committed generator reproduced the same raw certificate hash and passed a complete second replay. The raw data are provided in the bundle; the reproducible generator and theorem are committed, rather than a manually transcribed compressed stream.

## 5. Failed trials and remaining scope

The original unsplit [57/100,29/50] trial did not reach the target on this grid; splitting it at 23/40 produced the two accepted final bins. There is no missing interval hidden by that failed attempt. Enlarging the terminal range requires additional accepted bins and, as needed, an explicitly extended verifier; the current endpoint 29/50 is not extrapolated.

Trials in the larger-angle and balanced-extreme regions remain too weak for the sharp value. TE1 gives no local candidate theorem, no curvature bound, and no elimination of two-turn clipping or winding corrections. The theorem applies to ordinary area globally within its stated terminal range, independently of the separate tilted-extreme certificate AM2.

No CI, Lean/Lake compilation, dependency installation, or manuscript build was used. The verifier and written reductions have been self-reviewed, not independently refereed or kernel-verified. Unrestricted optimality remains unproved.
