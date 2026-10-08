# Ambidextrous sofa research — current handoff

**The sharp value M is not proved for general full-turn or partial-turn bodies.** The latest continuation proves a complete global midpoint-hallway upper bound, extends it to arbitrary handed motions and actual incoming heights, and gives a compact finite-offset reduction with an explicit finite-to-continuum error bound. This is not another special reference family, but its constant is still larger than M.

Repository: `vltanh/lean4-moving-sofa`.
Branch: `research/ambidextrous-pen-and-paper`.
Draft PR: #3; base `main`.
Baseline of this continuation: `47fdd36ffffc54207e3c96a4cd268ac7e84eb3eb`.
Current substantive source/check checkpoint before this handoff: `e2a30cf22ae9041827132438172235e6e38c9c38`.
Query the live tip before continuing and preserve intervening work.

## New original hand bound for exact four-hallway certificates (BH)

Read [box-area-lipschitz-hand-certificate.md](box-area-lipschitz-hand-certificate.md). **Neither sharp frontier is closed.** The user requested turning CP's measured pruning into a hand theorem. The response is a self-contained analytic bound: for any 8D rational or real offset box \(E\) and its midpoint \(m\), the original external four 3–4–5 hallways in \([0,5]\times[0,1]\) satisfy
\[
\boxed{0\le |C(E)|-|C(m)|\le\tfrac{168}{5}\max_i\operatorname{width}(E_i).}
\]
The **full exact weighted bound** BH.7 uses four coefficients \(19/5\) and four \(23/5\). The proof observes that newly allowed points lie in one-sided strips adjacent to the two outer and two inner wall lines of at least one hallway, then slices these strips in orthonormal coordinates. No contact classification, connectedness hypothesis, curvature bound, or numerical quadrature is needed. It is a global theorem about the **finite-hallway relaxation**, not a new global bound on the sofa constant.

**Finite rational certificate rule:** if the canonical-support root from CP1 is covered by boxes whose midpoint total intersection areas plus exact BH width penalties are all \(\le T\), then *every* connected four-hallway competitor has area \(\le T\). Thanks to our GC4 result equating the global total-area supremum with the connected-component supremum for actual fixed hallway placements, such a finite certificate necessarily exists for every **strict rational** \(T>G\). It may involve an impractically large grid; \(T=G\) is not guaranteed. For full conventional turns, the earlier FR2+D1 finite-mesh proof similarly gives a computable real optimum, with rigorous interval width \(<24/n\) from a finite exact \(n\)-mesh optimization in \(\mathbb Q(\sqrt2)\). This is **computability in principle**, not a claim that the Romik value M is correct.

**Nontrivial concrete eight-dimensional region:** the original four-hallway rational witness has midpoint area \(29092957301/16800000000\). On the box in which **every offset varies independently by at most \(1/4000\)**, BH bounds the entire inflated envelope by \(29375197301/16800000000<7/4\); independent exact clipping computes it as \(4159492073/2400000000<87/50\). This is local, not a global bound below 1.765; the same four-hallway global relaxation has configurations with area above M.

**Validation:** [rational checker](computer-assisted/check_box_area_modulus.py) and [record](computer-assisted/box-area-modulus-checks.json), **101 exact rational assertions** including 32 general boxes, 7-polygon witness and full-box fraction; a short five-second-capped run took 0.0731s internally. Executed source matches Git blob \`a1d54a46d0ea0c90bead358e7bf1d9d1ca2e61d3\`. The continuum BH1 inequality is a hand proof; finite runs do not verify it for all boxes. No long computation, CI, Lean/Lake compilation, dependency installation or manuscript build.

## Latest bounded runtime benchmark of CP search-space trimming

[Measured A/B benchmark](canonical-pruning-bounded-benchmark.md): the same independently implemented floating-point four-hallway polygon/component evaluator, original vs CP1 canonical root vs CP1 root plus CP9--CP11 support pruning. **Both searches complete at loose thresholds:**
- at T=2.6, original 15,905 nodes/2.3103s vs trimmed 255/0.04635s, **approximately 50x search-loop speedup**;
- at T=2.5, original 21,009 nodes/3.1417s vs trimmed 407/0.07471s, **approximately 42x**.
- Full Python process wall time at T=2.6 (including Shapely import) is **2.98s original versus 0.72s trimmed**, only about **4.1x**; separate import startup dominates tiny trimmed workloads.
- **At T=1.765 no variant completed under the 2.4-second cap**. The released 436-million-leaf proof was not rerun. Neither 42x nor 50x is a benchmark at that difficult threshold.

The independent evaluator was checked against O'Keefe's rational connected four-hallway witness: area \(29\,092\,957\,301/16\,800\,000\,000\) reproduced to floating roundoff, seven nonempty pieces. An initial affine-coefficient bug was caught by this test and fixed **before** recorded benchmark timings. The delivered \`canonical_pruning_benchmark.zip\` provides the corrected reproducible script, output record, README and SHA-256 hashes. **No leaf was exact-certified**, so the completed trees are discovery results, not mathematical improvements to the global 1.765 bound. The CP1 hand theorem justifies normalization, but a future certificate checker must explicitly verify that reduction and all exact box leaves.

## Latest verified mathematical improvement: canonical-support certificate pruning

[CP1 and the exact pruning test](canonical-support-certificate-pruning.md) give an **exhaustive but far smaller** search region for the global eight-offset four-angle finite relaxation of O'Keefe, *without* assuming full turns, cap regularity or reference proximity. Normalize each connected component of a placed-hallway intersection so its left and bottom extrema are at zero, with \(W\le5\) and height \(H\le1\), then reset every hallway's two offsets to **its actual component support minus one**. The component remains in all four newly tightened hallways, so the maximum possible connected-component area is unchanged. These new canonical offsets obey eight explicit rational ranges whose 8D product volume is **exactly \(10925/118013952\approx0.00925738\%\)** of the original free-offset root box. Convex-support subadditivity, opposite-normal widths and reflection-paired support inequalities give further rational box rejection.

At uniform four-way splitting of each original coordinate, the exact standard-library test rejects all but **405 of 65,536 boxes**, using only *necessary* support inequalities. It also tests 54 rational finite point sets. The executed source bytes match Git blob \`9fd13ef92be9bf9201b761aa27721c4edd56e471\`, source SHA-256 \`b5b9195f152168790ac7cc4f1decf7240ac918b10c989cd5a3297f5e1cb44453\`; a fresh run passed under five seconds in about **0.01254 seconds**. See [checker](computer-assisted/check_canonical_offset_pruning.py) and [record](computer-assisted/canonical-offset-pruning-checks.json). No optimizer or large checker was run; these are checks of finite necessary constraints, **not** of \(G\le1.765\), let alone \(G\le M\).

This is a new ***certificate design*** rather than an improved area constant. A correct future proof checker must first justify CP1; arbitrarily dropping old offset boxes without its canonical representation would be unsound. Then prune infeasible canonical-support boxes before exact polygon clipping, and keep degenerate-contact/component logic for inflated offset-box unions. Our existing gap-compression theorem further gives equality of the **global** finite-hallway supremum using *total* actual intersection area versus *largest component*, but that does **not** allow using total area of an inflated parameter-box union in place of the paper's component bound.

The external \(353/200\) global upper theorem remains available and improves our coarse \(2\sqrt2-1\). The same four-hallway relaxation has an independently replayed **connected** configuration of area \(1.73172\ldots>M\); even perfect search-domain trimming cannot make those four angles sharp. For arbitrary partial turns, reaching the larger \(\arcsin(4/5)\) angle at a threshold below \(5/3\) is not unconditional. The height/outgoing-width refined gate in CP allows it if \(|S|>\max(\sqrt2H,5Hq/3)\), in particular for \(|S|>M\) with \(Hq\le49/50\). General full-turn and partial-turn sharpness remain **unproved** and PR stays draft.

## Immediate external-method finding — rigorous 353/200 bound, sharp value still open

The user pointed to [devinokeefe/ambidextrous-sofa-bounds](https://github.com/devinokeefe/ambidextrous-sofa-bounds). Read [external-four-hallway-certified-bound-review.md](external-four-hallway-certified-bound-review.md) for the comparison and precise provenance. Its paper *Upper bounds for the ambidextrous moving sofa problem* gives **the global bound \(353/200=1.765\)**, for arbitrary ambidextrous sofas sharing one starting position, via four \((3,4,5)\) rational-angle hallway placements and a large exact search-tree certificate. A Lean **conditional** soundness theorem and a reported compiled Lean checker acceptance accompany it; C and Python exact-checker logs independently report accepting 436,160,442 leaves. **We did not rerun the 1.74-GB certificate**; this is an attributed externally verified result, not our own newly executed certificate or an independent referee report. It improves the earlier \(2\sqrt2-1\) global bound but remains strictly above Romik's \(M\approx1.644955\).

Its main methodological transfer is a tighter **per-parameter-box union of entire \(L\)-hallways**, with exact rational polygon splitting and **largest connected-component** leaf tests; degenerate touching polygons cannot be discarded. This is stronger than relying only on a fixed outer rectangle and lower-bound forbidden quadrants in D3. An untrusted floating-point tree search is separated from a verified exact checker. The source provides an exhaustive eight-offset root box, not selected sampled positions.

**Two sharpness barriers:** (a) these same four hallways admit a rational **connected** configuration of area \(29\,092\,957\,301/16\,800\,000\,000\approx1.73172>M\), so subdividing their parameter box further cannot reach M; (b) the elementary angle-reach argument for arbitrary partial turns only guarantees the larger \(53.13^\circ\) angle when an assumed counterexample has area \(>5/3\), but \(M<83/50<5/3\). Full turns supply the angle regardless, but do not resolve (a). The earlier FR3 finite-angle nonsharpness result is consistent with this independent example.

**Research consequence:** use 353/200 as the current source-verified *global* upper benchmark; borrow the component-aware rational box certificate for credible whole-region exclusions, and reserve a sharp **continuum local/structural** argument for the reference residual. Do not restart its 20-minute Lean or 5-hour Python checks under our short execution limit, blindly replicate huge certificates, or confuse a finite relaxation with a fully moving sofa. Neither full-turn sharpness nor general partial-turn sharpness is closed.

## 1. Instructions and verification boundary

The user wants closure, not accumulation of peripheral calculations. Prioritize an actual universal upper comparison, elimination of a possible maximizing configuration, or a complete reduction of the remaining optimization. Keep scripts under external five/ten-second limits where practical, never over 30 seconds without new authorization. **No CI, Lean/Lake compilation, dependency installation or manuscript build.** Commit substantive positive and negative findings with `[skip ci]` under this directory. Unrestricted uniqueness remains deferred; keep PR #3 open and draft until the sharp theorem is actually proved.

All written arguments remain self-reviewed rather than independently refereed or kernel-verified. Exact checks of finite arithmetic are not continuum proof verification. The older proof files and original uploaded packages are preserved; this handoff does not independently validate their long dependency chains.

## 2. A complete finite global optimization is now solved by hand

Read [midpoint-hallways-global-bound.md](midpoint-hallways-global-bound.md), labels MH.

Rotate coordinates to u=(x+y)/sqrt(2), v=(-x+y)/sqrt(2). Arbitrary lower and upper midpoint hallway placements enclose a rectangle [0,P] times [0,Q] after translation and impose

`(u>=P-1 or v>=Q-1) and (u<=1 or v<=1)`.

The incoming unit strip is a diagonal band of sum-coordinate width sqrt(2), with arbitrary position. The proof handles **every real P,Q and band position**, not a collection of boxes. If both dimensions are at least two, only two unit corner squares survive. If one dimension is between one and two, divide into two 1-by-q corner rectangles and a middle strip. The exact largest band intersection of each rectangle and a one-variable monotonicity calculation give

$$\boxed{|S|\le2\sqrt2-1.}$$

This is the exact maximum of the two-midpoint relaxation. A pair of clipped unit squares attains it in that relaxation. No full-motion feasibility of the equality polygon is asserted. The numerical constant was previously mentioned in the discussion; no novelty claim is made for it. Here the proof is self-contained and analytic.

## 3. The bound also covers general partial motions, without completing them

Read [midpoint-bound-general-motions.md](midpoint-bound-general-motions.md), labels GH.

For actual common incoming height H<=1 the same calculation gives

$$\boxed{|S|\le B(H):=2\sqrt2 H-H^2\le2\sqrt2-1.}$$

No original full-turn assumption is needed. A wrong-way midpoint hallway has horizontal fibers of length sqrt(2), so its intersection with the incoming strip has area at most sqrt(2)H. The incoming and outgoing strips likewise bound area by H/|cos(omega)|, where omega is the lifted terminal frame angle. Therefore a body exceeding sqrt(2)H must, by continuity, visit the **proper** midpoint in each handed motion. The complete MH placement bound applies. Bodies below that threshold already satisfy B(H).

This proves the coarse upper bound across both general motion classes, with no monotonic-rotation or symmetry premise. It does not prove Romik's smaller area M.

A hypothetical counterexample above M must have

$$H>\sqrt2-\sqrt{2-M}$$

in every *available* common incoming orientation (approximately 0.818357, for orientation only). The theorem therefore closes the sharp area target for all incoming heights at or below that exact threshold. It does not justify an unproved reorientation of a partial-turn body.

MH/GH do not use WV, Gerver's theorem, the regularity of a maximizing cap, or a computer certificate.

## 4. A compact global finite-to-full reduction with an explicit error

Read [full-turn-compact-finite-reduction.md](full-turn-compact-finite-reduction.md), labels FR.

At the rational frame u=(3/5,4/5), v=(-4/5,3/5), a surviving point must have x>=r-3 or x<=l+2. Connectedness therefore bounds horizontal width by five; for a disconnected set its projection has measure at most five, and GC compresses the gaps to obtain that width without area loss for canonical envelopes. After translation all relevant connected representatives lie in [0,5] times [0,1], with diameter below six.

This compactness and the closed support-depth inequalities prove **attainment of the full-turn unpenalized maximum A_F**. Thus FV's actual-maximizer premise has a direct justification independent of weighted-cap attainment.

For even n, let

`Theta_n = {2 atan(j/n): j=0,...,n} union {pi/4}`,

and include both Theta_n and pi+Theta_n hallway families. Their entire finite relaxation has a compact parameter box: h(0)=W in [0,5], h(pi)=0, h(pi/2)=H in [0,1], h(3pi/2)=0, all other wall offsets in [-6,6]. GC shows this box loses no finite-envelope area even when the original envelope is disconnected. Let A_n be the **global** maximum over this box, not the output of an untrusted local optimizer.

The offset objective is continuous piecewise quadratic on finitely many polyhedral line-arrangement cells, including their boundaries. D1's critical-face method is applicable in principle. No complete enumeration or global solve of these larger finite problems was run.

For N(r)=((1-r^2)/(1+r^2),2r/(1+r^2)),

`|N(r)-N(q)| = 2|r-q|/sqrt((1+r^2)(1+q^2)) <= 2|r-q|`.

Every intervening frame is within 1/n in each normal of a sampled frame. Since support depths are diameter-Lipschitz, uniform shrinking by `(1+6/n)^(-1)` turns any connected sampled candidate into a genuine full-turn body. Hence

$$\boxed{A_n/(1+6/n)^2\le A_F\le A_n\le2\sqrt2-1.}$$

This is a rigorous convergence modulus, not a mesh experiment. Connected shrunk finite maximizers have subsequences converging to an actual full-turn maximizer. Their limiting curvature/contact structure is still not established.

**Important limit:** every finite orientation-only relaxation has optimum strictly above M. On a retained curved outer reference arc, choose a point on none of the finitely many wall lines. A small disk around it lies inside the sampled envelope and adds positive area outside the reference. Thus merely refining a finite placement mesh and waiting for its exact optimum to become <=M cannot close the theorem. An analytic limiting estimate or a sharp residual theorem is still needed.

## 5. Latest GC/FV reduction remains central

[GC](horizontal-gap-compression.md) preserves every safe support depth under nondecreasing horizontal contractions while height is at most one. Collapsing empty projection gaps preserves area; filling vertical fibers preserves the conventional hallway constraints and yields connectedness. Canonical envelopes retain their total area under this process.

[FV](full-turn-unconstrained-envelope-variation.md) therefore permits arbitrary continuous free-offset comparisons at an actual unpenalized full-turn maximizer. Perturbations need not retain a proposed hull, stay connected, or keep all fibers nonempty. At nondegenerate finite arrangements the balance is **visible outer length = visible inner length**. It does not replace visible length by the full convex-hull edge length. Wall ties, hidden facets and nonsmooth continuum limits remain real structural issues. FR supplies attainment and the legitimate finite maximizing sequence, not that final regularity theorem.

## 6. The sharp target and previous directions

For actual compatible full-turn cap pairs with nonempty fibers,

$$|E|=\Psi(U)+\Psi(V)+G,\qquad
\Delta(U)+\Delta(V)-G=M-|E|.$$

Thus proving G<=Delta(U)+Delta(V) is exactly the missing full-turn value theorem. The written WV value and SR/AF functional calibration do not pay G by themselves; AS's aggregate bound is stronger and is also unproved globally. The new universal upper bound leaves the interval

$$M\le A_F\le2\sqrt2-1,$$

not equality at its lower end.

Read [four-direction-first-pass-review.md](four-direction-first-pass-review.md) for the earlier parallel attempts. D1's critical-face reduction, D2's spatially allocated forbidden unions, and D3's robust finite boxes remain relevant to the compact problems FR now specifies completely. D4's width-aware completion allowance remains relevant to a sharp partial-turn proof. A global coarse midpoint estimate is not a complete sharp covering.

Candidate-functional CF5 global concavity is false, including positive-top-face caps of width just above two; see [the exact counterexample](candidate-functional-concavity-counterexample.md). The disconnected cap-pair example remains true; GC repairs it by changing the body, not by claiming the original intersection was connected.

The minimum-width identity G_s=T_s+C_s-sW is valid, but the universal sign G_s<=0 is false even near the reference; MS/NR are mandatory controls. MF overlap, FO's regular-face budget, and SM/SB's scale-family margin/bridge retain their hypotheses. Body/cap averaging, global curvature repair, half-height admission, face matching and affine normalization all have existing negative controls. Do not reopen a disproved shortcut under a new name.

## 7. Actual executed checks

`computer-assisted/check_midpoint_hallways.py` passed 1,296 rational offset/band cases, six exact equality cases and 30 rectangle-concentration cases under an external five-second cap; internal time about 0.132 seconds. Source Git blob: `602bf6ddd50775b134f27dc654dcda9dbfa449ee`.

`computer-assisted/check_finite_to_full.py` passed 124 rational normal-distance cases and 60 diameter-point cases under five seconds; internal time about 0.0054 seconds. Source Git blob: `1640af659cbe89c07d169cf4f03b76c2fff216db`.

Both executed sources match their committed blobs. The combined record is `computer-assisted/global-midpoint-and-mesh-checks.json`. The first midpoint checker attempt had a variable-name TypeError, corrected before the passing runs; it produced no mathematical result. No global A_n solve was run. No CI or Lean/Lake compilation was used.

## 8. Next acceptance criterion

Use the actual global finite/continuum maximizer comparison to prove a structure or area inequality that identifies the limit as M. Alternatively, use exact finite boxes with a **proved sharp continuum residual theorem**. Do not present finite-angle upper values, ordinary sample maxima, or another conditional family as closure. The exact general full-turn and partial-turn optimality statements and independent review remain outstanding.
