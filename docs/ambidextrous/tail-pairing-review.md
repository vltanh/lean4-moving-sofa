# Review: direct tail pairing, a paid clipping correction, and the remaining global gap

**Unrestricted optimality is not proved.** This continuation establishes `G<=Delta(U)+Delta(V)` on a stated infinite-dimensional tail-window class and, in particular, bounds the full saturation of every convex shaving confined to two explicit boundary layers of the reference hull. The middle-support and barrier hypotheses are not known for arbitrary competitors. All new proofs are self-reviewed, not independently refereed or kernel-verified.

Baseline: `eede8343b503db2c8a772e86ed086d6614cb9b18`. Only files under docs/ambidextrous are changed.

## 1. The actual new inequality

The exact two-cap area identity is

$$|E|=\Psi(U)+\Psi(V)+G,$$

where G is the positive clipping correction. The new argument does not discard it. It proves, separately for each admitted cap,

$$\boxed{M/2-\Psi(U)\ge\int_a^b(1-A_U(x))dx.}$$

Here [a,b] is the reference face interval, not an assumed face of U. Both new niche roofs vanish outside that interval, so their clipping is at most the sum of these two face-loss integrals. This gives the needed sign and |E|<=M.

[TC](tail-paired-cut-deficit.md) treats inward support changes in a small top-normal window. [RB](reference-belt-saturation-bound.md) gives the concrete geometric condition

$$K_*\cap\{1/101\le y\le100/101\}\subseteq K\subseteq K_*,$$

and proves |E(K)|<=M for the full canonical saturation, not just for the original cut reference subset. U,V may be cut independently. Their top faces can shrink to points or cease to touch the old top line. Neither a curvature density nor a fixed contact pattern is assumed for the changed caps.

[STW](signed-tail-window-comparison.md) permits outward changes too. Its exact conditions are: fixed middle supports outside `(pi/2-eta,pi/2+eta)`, a half-height rectangle, height at most one, and `h_U(theta)<=1+(m/2)|cos(theta)|` in the window, where eta=2 arctan(1/10). The second cap may vary independently.

## 2. Why the proof does not overcharge missing hull material

For a reference right-tail point x_in=b-d, its matching outer point is x_out=b+d. At t=pi/2-arcsin(2d), the same support defect u(t) enters both comparisons:

$$n_*(x_{in})-n_U(x_{in})\le u(t)/\sin t\le A_*(x_{out})-A_U(x_{out}).$$

The first inequality uses a single known reference angle as a lower test for the *new* niche. It does not assert that this angle remains globally active. The second uses a supporting line as an upper bound for the changed cap roof. The mapping d -> d preserves horizontal measure, so integration pairs niche savings with lost outer-flank area.

Those outer-flank losses are separate from the convex cap loss underneath the old horizontal face. After the niche savings have been paid, that latter loss remains available to cover clipping. No derivative-energy estimate is substituted for surviving material.

For signed changes, the two differences may be negative. STW retains those signs. Outside the inner tail strips, an unchanged reference wall pair gives n_U>=n_*; outside the corresponding outer strips, an unchanged reference support bounds A_U<=A_*. These are favorable inequalities, not an unjustified equality or monotonicity assertion without cap inclusion.

## 3. Specific review checks and hypotheses

- The circular pair has radius one half on both the outer flank and inner tail. Its equal horizontal scales are used in the integral pairing.
- At a changed late first-quarter angle, the companion normal lies near pi, outside the changed window. On the early left tail the roles are reflected. Changing both walls at that same parameter would require a new estimate.
- In STW the old companion clearance is at least 19/8, while the allowed upward first-wall displacement is at most 1/99. Thus the signed lower test remains a legitimate min-wall test.
- The support barriers confine both full niches to the reference face interval. Their possible new corner heights in the changed windows are bounded by 2220/10201<1/2. Elsewhere the reference bounds apply.
- Both cap roofs are at least one half. Therefore every actual two-turn fiber contains the midline, is nonempty, and has the exact ordinary-area accounting used in the proof. A signed negative fiber is never integrated as area.
- In RB, support values outside the window are retained because their reference maximizing points lie in the preserved belt. No arbitrary interior hull point is claimed to survive as a sofa point.
- The full envelope E(K) may have a smaller actual hull than K. The proof does not need or assume equality of those hulls.
- Applying RB to an already given S requires full-turn feasibility to infer S subset E(K). Constructing E(K) itself provides full-turn feasibility independently. These statements must not be conflated for a partial-turn S.

## 4. Independence from the weighted-maximizer chain

The new proofs use the explicit reference shape, its active circular-tail formulas, and the exact reference identity Psi(U_*)=M/2. They do not use WV2, VE's limiting source-flux theorem, any maximizing-cap regularity theorem, or Gerver's global upper bound.

Thus they are standalone ordinary-area case theorems relative to the explicit reference construction. This does not independently verify the rest of the repository or remove its earlier proof obligations.

## 5. A broader filling shortcut is not a proof

[FF](face-filling-budget-obstruction.md) gives an exact counterexample to the unqualified rule

`Psi(conv(U union Z))-Psi(U) >= missing cap area beneath Z`.

A downward cap of a radius-one-half disk has no positive niche. Filling its whole top interval makes a unit square with a positive niche triangle. The signed-objective gain is strictly less than the convex cap-area gain. This rejects that intermediate comparison; it does not assert that every stronger final deficit inequality is false.

A different, narrower filling conjecture was tested only diagnostically on 12 prescribed clipped caps and 32 prescribed convex-hull point sets, all within specified circular support barriers. All sampled margins were positive. This is inconclusive: no global optimization, interval covering, or continuum implication was established. That conjecture is not used in TC/RB/STW and is not reported as a theorem.

## 6. Execution record and limits

The standard-library [check_tail_pairing.py](computer-assisted/check_tail_pairing.py) ran under an external five-second limit. It passed 12 named checks, 72 rational signed-line cases, 144 rational paired-fiber identities, and three sign/hypothesis controls. Internal time was about 0.0064 seconds.

The [record](computer-assisted/tail-pairing-checks.json) preserves Python version and hashes. Executed local bytes match fetched Git blob `e9b0beab8b786664f245100a9ac3d70b153f3c33` and SHA-256 `649c7883932b4b4198195fc55fced6bbbeb068a651107d689292b67a9020e7e9`.

These checks verify explicit arithmetic and finite bookkeeping. They do not certify reference-envelope coverage, geometric admission, or the continuum theorem. The local line samples are not asserted to be complete realizable cap trajectories.

The two exploratory filling scripts also ran under five-second external limits. The first reports about 0.193 seconds internally; the second's 32-sample loop reports about 0.437 seconds and also executes the first module when importing its helpers. Their scripts and outputs are preserved in the session bundle. Both use floating-point polygon geometry and finite-angle/spatial quadrature with no certified error direction. Neither result is a proof input.

No long search, CI, Lean/Lake compilation, dependency installation or manuscript build was used.

## 7. Exact remaining boundary

TC/RB/STW fix the middle supporting data and, in the signed version, impose baseline-intercept barriers. This is not a complete neighborhood theorem for every nearby hull. Arbitrarily small changes of the middle arcs can fall outside the domain.

PD's density theorem does not make arbitrary full-turn bodies satisfy those restrictions relative to K_*. It remains necessary to bound the full saturated opposite-face class, or prove a valid reduction into an admitted domain. Uncovered partial turns remain separate. No universal upper bound, symmetric-maximizer existence theorem, full parameter covering, or unrestricted closure is supplied by these new case results.

The useful next extension would have to pay changes of the middle supports as well as the tail corrections, or prove an independent admission theorem. Merely enlarging the named class or repeating the new clipping identity without those estimates would not finish optimality.
