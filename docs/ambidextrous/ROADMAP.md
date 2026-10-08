# Active roadmap: identify the sharp value inside a now bounded global problem

**The exact optimum M is not proved for full or partial turns.** JD1 now gives the global computer-free bound \(2\sqrt2-1-1/51\approx1.808819\) for both motion classes, superseding the intermediate JH1 \(1/90\) and QT1 \(1/175\) improvements, though still weaker than O'Keefe's externally computer-certified 1.765. The other finite-offset results do not identify M. Read [HANDOFF.md](HANDOFF.md) before continuing.

## New strongest hand upper bound: JD1's exact two-sided clipping dual

[**JD1 — global \(1/51\) gap**](two-sided-clipping-dual-hand-bound.md) improves the hand inequality to
\[
\boxed{\mu_{\mathrm{ambi}}\le2\sqrt2-1-\frac1{51}\approx1.8088192816}
\]
for **all** compact connected common-starting-position ambidextrous sofas, including arbitrary continuous partial turns, and hence for complete full turns. It remains weaker than O'Keefe's externally verified \(353/200=1.765\) and does not establish Romik optimality \(M\approx1.644955\).

This is a genuine **new joint deficit proof**, not constant tuning of the original tiny-area witness: exact positive-definite two-\(45^\circ\) stability + disjoint missing actual-support tip triangles + the central wedge from one \(36.87^\circ\) lower hallway. JD keeps **both** lower incoming-band and top \(v=1\) clipping errors. The weighted quadratic constrained by \(C=N+x-7y+7s_A+s_D=62-40\sqrt2\) has explicit orthogonal minimizer and variance. The lower clipping's dual norm \(31/2<16\) and negative value at that minimizer mean it is paid without a penalty. If the top clipping is active, its negative minimizer value \(<-29/20\) forces extra variance that pays the two crude remaining bounds. Together,
\[
B-|S|>\frac{1107821}{55860000}
=\frac1{51}+\frac{212957}{949620000}.
\]
The \(N\le0\) case is discharged separately by tip and base losses. The preliminary near-equality proof **retains measure-zero connector lines** at width exactly two.

[Code](computer-assisted/check_two_sided_clipping_dual.py) and [record](computer-assisted/two-sided-clipping-dual-checks.json): the **byte-matched committed checker** passed **129 exact rational arithmetic and polynomial-identity tests** under a five-second limit, in ~0.0025 seconds. These are checks of constants only; the continuum proof is the hand argument and remains subject to independent mathematical review. Nothing was built or optimized at scale.

**What should count as further progress:** either a *substantial* additional numerical improvement with a short complete analytic proof, or a structural bridge from finite-hallway stability and actual support-depth inequalities to the full continuum clipped-area comparison. The fixed four-angle relaxation admits a connected configuration above \(M\), so no pure four-angle bound can be sharp. Do not mistake more small constants for closure, or claim 1.808819 beats the external 1.765 theorem.

## Current strongest computer-free global upper bound: JH's coupled three-hallway proof

[JH1](coupled-three-hallway-hand-bound.md) improves the previous extremely small strict hand gap to a substantive explicit value:
\[
\boxed{|S|\le2\sqrt2-1-\frac1{90}<1.817317.}
\]
It holds for **all compact connected ambidextrous sofas with arbitrary continuous partial turns**, and hence for the complete full-turn subclass, using the no-sideways-motion intermediate-angle theorem already in GH/O'Keefe's paper. It is **strictly weaker numerically** than the external independently computer-certified \(353/200=1.765\); it is not the optimality proof.

**New technique beyond TH/QT.** The two \(45^\circ\) constraints admit an exact positive-definite **near-optimal envelope-area identity** for rectangle widths \(P,Q\) and diagonal-band center c. The proof includes the case of point-like zero-area connectors at exactly unit-square contact. A third **rational \(36.87^\circ\) hallway** pays for *two* separately absent tip triangles of areas \(s_A^2/14,s_D^2/14\) plus a disjoint central forbidden wedge of area \(N^2/700\), with an explicit at-most \((\Delta_+)^2/16\) portion lost below the incoming band. Rather than forcing *each* region's area independently above an entire assumed deficit, **weighted Cauchy--Schwarz couples all three losses**:
\[
B-|S|\ge\frac{(62-40\sqrt2)^2}{1500}-\frac{(\Delta_+)^2}{16}
>\frac{39667}{3528000}>\frac1{90}.
\]
There is no numerical optimization, curvature hypothesis, hidden support-feasibility assumption, or rounding argument in the proof. [Checker](computer-assisted/check_coupled_three_hallway.py) and [exact check record](computer-assisted/coupled-three-hallway-checks.json) preserve **48 passing elementary tests** under a five-second cap; these do not establish the continuum theorem on their own.

**Strategy lesson:** JH gives a useful way to incorporate the exact BH/CP *area-and-support* mechanisms into a genuine global hand result. The new metric is the **joint squared loss** of visible support witnesses and forbidden area; one-off isolated rectangle witnesses throw away nearly all this budget. The analytic three-hallway bound still cannot approach Romik's \(M\) by refinement of only these orientations, because the four-angle source relaxation contains an actual connected finite configuration with area \(1.73172\ldots>M\). A sharp continuum structural step remains indispensable.

## Completed general hand upper bound using the 45° stability and one 3–4–5 hallway

[TH1: three-hallway strict bound](strict-hand-three-hallway-bound.md) establishes a **fully analytic** global area theorem
\[
\boxed{\mu_{\rm ambi}\le2\sqrt2-1-10^{-9}}
\]
for the same shared-incoming-position ambidextrous definition as the external paper, **including nonmonotone partial turns**. Thus the pure hand upper bound is now *strictly* below the previously saturated \(2\sqrt2-1\) finite relaxation. This is weaker than the external exact **computer-assisted 1.765** upper theorem and remains above Romik's \(M\).

Mechanism: the exact two-45° envelope area bound has a rigid near-equality structure; area within \(10^{-9}\) of equality forces both rectangle dimensions within \(1/50\) of 2 and the diagonal band center within \(1/100\) of 2. Three disjoint positive-area rational witness boxes then all meet the sofa, and their selected points yield opposing 3–4–5 support-depth violations at the same point. **A necessary third hallway at angle \(\arcsin(3/5)\)** is forbidden. The wrong-way-angle argument forces proper 45° passage in both motions above \(\sqrt2\), so 36.87° is visited by the lower motion without requiring that it be a full quarter turn.

**Pitfall corrected in self-review:** a zero-area line at a 45° rectangle width *exactly 2* can connect the two otherwise separate corner squares; do not discard it. TH uses *connectedness only when both widths exceed two* and otherwise controls areas of the full corner squares. A small exact arithmetic regression is supplementary, not a computational premise. This route provides a template for how BH-style box area stability and actual support depths can yield hand results, **but it does not prove \(A_F=M\)**. Any attempt to use a fixed finite number of hallways alone confronts FR3 and the external connected four-hallway example of area \(>M\): a sharp proof still requires continuum geometry, a paid clipping budget or a genuinely complete local structural theorem.

## New hand theorem: midpoint area certificates with a uniform rational error

[BH1--BH3](box-area-lipschitz-hand-certificate.md) turn the canonical-offset speed improvement into a **strictly proved finite-box certification rule**, not just a timing claim. For the four \((3,4,5)\)-normal hallway pairs in \(B=[0,5]\times[0,1]\), let \(E\) be an eight-offset box, \(m=\mathrm{mid}(E)\), and \(C(E)\) the intersection of the **unions of every hallway placement within each parameter interval**. Then
\[
\boxed{0\le|C(E)|-|C(m)|\le\frac{168}{5}\,\max_i \operatorname{width}(E_i).}
\]
The hand proof places every newly allowed point in one of the four **one-sided thin wall strips** per hallway and integrates their maximum possible area across the \(5\times1\) window. The precise coefficient-weighted bound is (BH.7), with four weights \(19/5\) and four \(23/5\). It holds for all real translations and all contact topologies.

Consequently a finite rational partition of CP's exhaustive trimmed root gives a **fully hand-justified global connected-component bound** \(G\le T\) if every center's exactly computed **total** polygon area plus its BH strip penalty is at most \(T\). No polygon connectivity test is needed for **this more conservative** certificate type. GC connectedification proves that the *global* supremum of total actual placement area equals \(G\), hence **for every rational \(T>G\) such a finite exact midpoint certificate exists**; the algorithm terminates in principle. This is a completeness theorem for *strict* thresholds, not an assertion that \(G=M\) or that a practical search is fast at \(T=1.765\).

**Concrete exact local application:** around O'Keefe's high-area rational offset witness (after shifting x by +3), take every offset within \(1/4000\) of the center. BH1 bounds **every placement in this entire eight-dimensional region** by
\[
|C(E)|\le29375197301/16800000000<7/4.
\]
An independent seven-polygon exact rational clipping goes further and computes the entire inflated box area
\[
|C(E)|=4159492073/2400000000<87/50=1.74.
\]
This is a **local box certificate only**; the four-angle **global** optimum remains \(>M\).

[BH4](box-area-lipschitz-hand-certificate.md) combines the earlier FR2 exact finite-angle enclosure and D1 finite critical-face enumeration to make the unrestricted **full conventional two-turn value a computable real in principle**: for even \(n\), exact finite maxima \(A_n\in\mathbb Q(\sqrt2)\) satisfy \(A_n/(1+6/n)^2\le A_F\le A_n\) with bracket width \(<24/n\). Finite termination is proved mathematically, but the time required can be astronomical. This does not automatically extend to arbitrary partial turns or prove Romik's exact conjecture.

The [source](computer-assisted/check_box_area_modulus.py) and [record](computer-assisted/box-area-modulus-checks.json) passed **101 exact rational assertions** (32 general boxes plus the exact rational witness/local-box checks), in **0.0731 s** internally under a five-second timeout; executed bytes match the committed Git blob \`a1d54a46d0ea0c90bead358e7bf1d9d1ca2e61d3\`. These finite checks support arithmetic only. No large optimizer, Lean compilation, or published certificate rerun.

## Concrete improvement to external computer-assisted method: canonical-support pruning

[CP1](canonical-support-certificate-pruning.md) is a **lossless global search-domain reduction** for the same eight-offset four-angle connected-component relaxation used in O'Keefe's certified \(353/200\) bound. For any connected component of a finite hallway intersection, first translate its attained left/bottom extrema to zero and **tighten every hallway outer wall to the actual support of that component**. The old inner disjunction remains satisfied, so every original connected competitor has a canonical counterpart of no smaller area. The reduction needs no extra sofa curvature or full-turn assumption. It changes the *search representation*, not the mathematical value being optimized.

In the original 3–4–5 hallway coordinate order, a support-tight competitor's offsets must lie in the rational root intervals
\[
[-1,18/5],[-1,-1/5],[-1,14/5],[-1,-2/5],
[-2/5,18/5],[-1,-1/5],[-1/5,14/5],[-1,-2/5].
\]
The product volume fraction relative to the source's original root is exactly
\[
\boxed{10925/118013952\approx9.25738\cdot10^{-5}.}
\]
Further linear **joint support-subadditivity** inequalities among all eight angles yield cheap branch rejections. A bounded exact regression gives **405** potentially compatible boxes out of **65,536** boxes at a uniform four-piece-per-coordinate subdivision; this is necessary-condition pruning, not an area certification of those 405 boxes. [Checker](computer-assisted/check_canonical_offset_pruning.py); [exact run record](computer-assisted/canonical-offset-pruning-checks.json) (executed Git blob \`9fd13ef92be9bf9201b761aa27721c4edd56e471\`, about 0.0125 seconds, no CI/Lean or large certificate).

**Practical checker architecture:** (1) prove CP1 as a reduction from arbitrary *connected components* to support-tight placements; (2) search the small canonical rectangle, rejecting rationally impossible support cells before polygon clipping; (3) on remaining cells, reuse exact **whole-box hallway unions**, valid rational polygon-area bounds, and degenerate-aware component checks as in the external checker; (4) for partial turns at target area below \(5/3\), keep the **motion-angle reach case** explicit. A useful conditional strengthening uses incoming height \(H\) and outgoing span \(q\): proper \(53.13^\circ\) reach follows if \(|S|>\max(\sqrt2 H,5Hq/3)\), so a hypothetical \(|S|>M\) reaches it whenever \(Hq\le49/50\).

**Important limits:** root-box *volume* is not elapsed time; we have not rerun the external 436-million-leaf proof, produced a new \(<1.765\) upper certificate, or proved sharp \(M\). The same four-angle relaxation contains a connected rational configuration with area \(\approx1.73172>M\). No amount of support pruning removes **that genuine finite configuration** from the global maximum. A sharp theorem still needs more angles and/or a continuum residual comparison.

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
