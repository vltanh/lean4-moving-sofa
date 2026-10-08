# Active roadmap: identify the sharp value inside a now bounded global problem

**The exact optimum M is not proved for full or partial turns.** The latest hand proofs give a global bound 2 sqrt(2)-1 for both motion classes, a height-sensitive version, and a compact finite-offset reduction with certified angular approximation. They do not identify the limit of the finite problems as M. Read [HANDOFF.md](HANDOFF.md) before continuing.

## Externally certified global bound: O'Keefe's 3–4–5 four-hallway certificate

[Full methodological/provenance review](external-four-hallway-certified-bound-review.md). Devin O'Keefe's [ambidextrous-sofa-bounds](https://github.com/devinokeefe/ambidextrous-sofa-bounds) accompanies a September 2026 paper reporting a complete, computer-assisted global theorem
\[
\boxed{\mu_{\mathrm{ambi}}\le353/200=1.765},
\]
**for arbitrary continuous full or partial turns from one shared incoming position**. Its four hallways have rational angle data \((\cos,\sin)=(4/5,3/5),(3/5,4/5)\) and their reflections. It normalizes all **connected components** into an exhaustive eight-dimensional rational offset box and certifies a complete binary covering by exact upper enclosures of hallway unions. Leaf tests sum rational polygon areas or, when necessary, use the maximal contact-graph component; degenerate touching polygons are retained. The authors provide three separate checker implementations; the included Lean soundness theorem is conditional on checker acceptance and a recorded compiled Lean run accepts the 436,160,442-leaf release certificate. **We have inspected code and logs but not run or independently verified that huge certificate.**

This is a major **global upper bound** improvement from our \(2\sqrt2-1\), but **not sharp**: the desired value is \(M\approx1.644955\). Two exact limits prohibit superficial attempts at closure:

1. The same four-angle relaxation admits a **connected finite-hallway configuration of area \(29\,092\,957\,301/16\,800\,000\,000\approx1.73172>M\)**. Therefore further subdividing the existing eight-dimensional root box cannot prove \(G\le M\); more angles or additional continuum geometry are essential.
2. The general-motions angle-reach reduction requires \(T\ge5/3\) to guarantee the larger angle \(53.13^\circ\). But \(M<83/50<5/3\). At the sharp threshold, an arbitrary partial turn may not reach that angle by this argument. Full turns do visit it, but still confront obstruction 1.

**Actionable transfer:** borrow the exact overapproximation \(\widehat X_j(E)=\cup_{u\in E}X_j(u)\) (retains both outer and inner wall constraints), component-aware rational leaf checks, and untrusted-search/trusted-checker separation for D3/FR. Do not copy code from a repository without an explicit reviewed source license; cite it and derive the needed formulas. A prospective exact proof of \(M\) requires a **hybrid**: certified finite-box exclusion of a complement, plus a complete sharp *continuum* area theorem on the residual neighborhood, including rough/asymmetric facets and positive clipping. Our existing TC/MT/ME results do not yet cover that entire residual class.

## 1. Acceptance criterion and rules

The desired value is

$$M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.$$

The target is ordinary area, not just another auxiliary maximum. A new result should establish a universal comparison, eliminate a possible maximizing configuration, or completely reduce an unresolved class. Keep exact and sampled claims separate. Prefer hand proofs; bound every script by five/ten seconds where practical, never over 30 seconds without new authorization. Commit substantive findings with `[skip ci]`. **No CI, Lean/Lake compilation, dependency installation or manuscript build.** Uniqueness is deferred; keep the PR draft while the sharp value is open.

## 2. Completed global coarse comparison

[MH](midpoint-hallways-global-bound.md) solves the entire two-midpoint-hallway placement problem by hand. In rotated coordinates its allowed set is a rectangle with two opposite forbidden quadrants, intersected with a diagonal band. An exhaustive three-case decomposition and the exact band concentration of a 1-by-q rectangle give

$$\sup |E_{45,45}|=2\sqrt2-1.$$

There is no unprocessed offset box in this calculation. The extremizer belongs to the finite relaxation, not automatically to the continuous-motion class. The proof makes no curvature, symmetry, connectedness or maximizing-cap assumption.

[GH](midpoint-bound-general-motions.md) gives for common incoming height H<=1

$$\boxed{|S|\le2\sqrt2 H-H^2.}$$

If a body exceeds sqrt(2)H, its continuous motion cannot pass through the wrong-way midpoint; the incoming/outgoing strip area test forces the proper midpoint in each turn. Therefore this bound covers arbitrary partial as well as full motions. No completion-by-deletion is used.

A potential counterexample above M must have H>sqrt(2)-sqrt(2-M) in every justified common incoming representation. The lower-height class is closed by this inequality. The remaining high-height class still needs a sharp comparison, not a favorable sign assumption on minimum-width clipping.

## 3. The complete finite-to-full reduction

[FR](full-turn-compact-finite-reduction.md) uses one rational hallway frame and GC to put every relevant connected representative inside [0,5] times [0,1]. This proves attainment of the unpenalized full-turn maximum A_F and removes parameter escape.

For even n use the rational-angle grid

`Theta_n={2 atan(j/n):0<=j<=n} union {pi/4}`

in both turn families. All finite offset lists can be reduced without loss to the explicit compact box in FR Section 3. Let A_n be its **global** maximum. The objective is continuous and piecewise quadratic on a finite polyhedral arrangement; D1's critical-face method applies in principle, with all boundary faces retained.

GC gives actual connected sampled competitors. The rational normal identity and the diameter bound show that shrinking by `(1+6/n)^(-1)` supplies every missing angle. Therefore

$$\boxed{A_n/(1+6/n)^2\le A_F\le A_n\le2\sqrt2-1.}$$

These are analytic inequalities. No global solve of A_n was run, and a local optimizer value is not a certified upper bound on A_n. Along dyadic meshes the A_n decrease to A_F, and shrunk connected maximizing polygons have subsequences approaching an actual full-turn maximizer.

This now specifies a complete finite problem and a rigorous continuum link; it is not an arbitrary family of test polygons.

## 4. The essential warning for computer assistance

FR3 proves **A_n>M for every finite orientation-only grid**. A curved retained reference boundary has points on none of the finitely many sampled wall lines; a small disk at one such point fits all sampled constraints and adds positive area. The finite relaxation is therefore strictly loose even when all its placements are globally optimized.

Do not launch a refinement loop waiting for a finite orientation-only upper optimum to fall to M. It cannot do so. Closing the exact value requires one of:

- an analytic inequality on the finite problems uniform in n, with a limit forcing A_F<=M;
- a complete global finite exclusion together with a genuinely sharp continuum theorem on the residual class;
- a structural theorem for the actual continuum maximizer followed by an admitted sharp area comparison.

The current material establishes none of those final sharp steps. It makes their input domains and approximation error explicit.

## 5. The structural route after GC/FV

[GC](horizontal-gap-compression.md) and [FV](full-turn-unconstrained-envelope-variation.md) allow perturbations whose total envelope is disconnected or loses proposed hull witnesses. Those are no longer invalid competitors for the unpenalized value. FR supplies attainment and a legitimate finite maximizing sequence.

At a differentiable free-offset finite maximum, the equality is **visible outer length = visible inner length**. Full convex-hull edge length is not interchangeable with visible length. Positive-length wall coincidences, hidden hull facets and the continuum source measure still need control. The new reduction does not prove curvature domination or injectivity by itself.

This is a concrete remaining implication. Re-deriving the same formal first-order equation without resolving those issues is not closure.

## 6. Earlier directions retained

Read [four-direction-first-pass-review.md](four-direction-first-pass-review.md) and [four-direction-research-plan.md](four-direction-research-plan.md) for the previous first pass.

D1: finite critical-face enumeration is now applicable to the complete compact FR offset domain. No uniform tractable chart count or continuum curvature theorem is supplied.

D2: spatially allocated forbidden unions are valid. One constant weight per entire quadrant is too weak because of overlap; do not reopen that rejected version.

D3: robust boxes can exclude whole parameter regions, but a list of successful boxes is not complete coverage. FR supplies a common bounded root domain and a principled angular approximation error.

D4: the width-aware completion allowance Lambda(p,q;e) is available for partial turns. Its positive cost still requires a margin. GC resolves the disconnected-completed-envelope obstacle by a new body construction, not by pretending the old envelope was connected. GH's coarse global bound bypasses completion but does not prove the sharp M value.

## 7. Mandatory negative controls

The exact full-turn identity remains

$$|E|=\Psi(U)+\Psi(V)+G,\qquad\Delta(U)+\Delta(V)-G=M-|E|.$$

The desired clipping inequality is equivalent to full-turn optimality, not an established technical lemma. WV's long written weighted-cap chain and SR/AF's calibration retain their independent-review and admission limitations. AS is a stronger upper relaxation and is not known to be globally <=M.

CF5's proposed global concavity of the spatial one-cap functional is false, even on positive-face caps with widths just above two. The separate value conjecture is not refuted by that example. Do not conflate a false concavity method with a disproof of the target value.

Minimum-width G_s<=0 is false, including high-area subcritical examples with regular aligned symmetric faces. Keep the actual cap deficits. Body/cap averaging, curvature repair, common-face/half-height admission and affine span normalization have earlier exact counterexamples. GC does not erase those different failures.

## 8. Executed checks and current review boundary

The exact midpoint checker passed 1,296 offset/band cases, six sharp equalities and 30 concentration checks in about 0.132 seconds. The finite-to-full checker passed 124 rational normal cases and 60 diameter checks in about 0.0054 seconds. Both had external five-second caps and matching committed-source blobs. Their combined record is `computer-assisted/global-midpoint-and-mesh-checks.json`.

These checks are not global finite-optimizer solves or independent verification of continuum theorems. The new positive area and approximation results are hand proofs. No CI or Lean/Lake compilation was used.

The next decisive result must reduce the remaining interval from M to 2 sqrt(2)-1 by a sharp global argument, rather than relabeling its upper endpoint or another sample maximum as closure.
