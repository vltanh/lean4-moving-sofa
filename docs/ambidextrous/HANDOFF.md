# Ambidextrous sofa research — current handoff

**The sharp value M is not proved for general full-turn or partial-turn bodies.** The new coupled support-clipping hand bound is \(2\sqrt2-1-1/51\) for arbitrary continuous ambidextrous turns. This supersedes our intermediate \(1/90\), \(1/175\), and \(10^{-9}\) hand gaps but remains numerically weaker than O'Keefe's externally certified \(353/200=1.765\). Romik's sharp value remains open. The other finite-to-continuum and box-area results are independent.

Repository: `vltanh/lean4-moving-sofa`.
Branch: `research/ambidextrous-pen-and-paper`.
Draft PR: #3; base `main`.
Baseline of this continuation: `47fdd36ffffc54207e3c96a4cd268ac7e84eb3eb`.
Current substantive source/check checkpoint before this handoff: `e2a30cf22ae9041827132438172235e6e38c9c38`.
Query the live tip before continuing and preserve intervening work.

## New exact local theorem for the still-missing full-turn 1.65 premise (NL1)

Read [full statement, hand reduction and directed-integer certificate](one-sixth-fullturn-near-reference-certificate.md), [source](computer-assisted/certified_near_reference_165.py), and [record](computer-assisted/near-reference-165-checks.json).

Let \(A_F\) be the complete-two-quarter-turn supremum. **The global premise \(A_F\le33/20=1.65\) is still UNPROVED.** However we now exclude **every** full-turn sofa with actual hull within Hausdorff distance \(7/10000\) of Romik's normalized centered hull \(K_*\), measured in one common incoming unit-strip frame, with no competitor symmetry/smoothness/curvature or aligned-face hypotheses:
\[
\boxed{|S|\le
\frac{412456005949545207}{250000000000000000}
=1.649824023798180828\ldots<1.65.}
\]
The argument samples **511 rational angles per complete turn** \((\cos t,\sin t)=((512^2-j^2)/(512^2+j^2),2\cdot512j/(512^2+j^2))\), uses exact interval radicals to enclose the reference supports from the cubic root, and then bounds **all real x**, not just sampled abscissas, with 100,000 cells of exact directed integer wall heights. The proof derives actual lower and upper full-turn support-depth constraints and their robust reflected counterparts even for asymmetric bodies. The resulting *integer* slice-length sum is **70,505,300,162,315,420**, with exact cell width \(23,400,000/10^{12}\). The final fraction is an *upper* Riemann sum and proves the local theorem. Independent fine-grid and original reference-support diagnostics are sanity checks only. The checker ran in about 0.57 seconds under a five-second cap; its exact executed SHA-256 is \`1133b23716ed9579107b53c4923b7bb3461ea83f7e8a8cebc8db9721371e24f3\`, Git blob \`aadd12d6d0bfa59187e869325cf0c42d2bf3ad7c\`, matching the committed source. No Lean build/CI/optimizer or long certificate was run. Finite proof arithmetic remains self-reviewed, not independently kernel verified.

**Consequence for the global premise:** The separate analytic AW result already excludes incoming horizontal width \(\le2\) by \(41/25=1.64\). NL1 also excludes the **whole 0.0007 reference-hull neighborhood**. An area-\(>1.65\) full-turn counterexample must have width \(>2\), a nonreference support distance \(>7/10000\), and is not in the already solved aligned-positive-face class FAS. That remaining compact, nonaligned/point-face outer domain must still receive a **complete global proof**, e.g. certified finite-angle upper boxes with CP support pruning and V virtual hallway constraints. A finite or local optimizer alone is not a proof. Once the missing \(A_F\le1.65\) is genuinely established, the existing JT comparison yields \(\mu_A\le1.66172<2\sqrt2-7/6\). None of these local statements makes that conditional conclusion unconditional.

## Stronger coupled hand bound JD1: the complete \(1/51\) deficit, with both clipping cases

**Read [the full hand argument](two-sided-clipping-dual-hand-bound.md).** Every compact connected common-starting-position ambidextrous sofa admits the computer-free bound
\[
\boxed{|S|\le2\sqrt2-1-\frac1{51}\approx1.8088192816.}
\]
This includes arbitrary continuous nonmonotone **partial turns** via the earlier proper-angle reach theorem, and the conventional complete-quarter subclass. It supersedes JH1's \(1/90\) and QT1's \(1/175\). It remains **weaker than the external certified 1.765 bound** and does not prove optimality of \(M=1.644955\ldots\).

The key algebra is the exact near-equality geometry of the two opposing \(45^\circ\) hallways. For \(x=P-2,y=Q-2,h=c-2\), where \(P,Q\) are their enclosing rectangle widths and c the incoming diagonal-band center,
\[
B-|F|=\frac{x^2+y^2}{2}+2(h-(x+y)/2)^2,\quad B=2\sqrt2-1.
\]
JD rigorously derives the domain for this identity whenever \(|S|>B-1/51\), including zero-area connectors at exactly width two. The third proper lower hallway at \(\arcsin(3/5)\) forces disjoint missing tip areas \((s_A^2+s_D^2)/14\) plus a central forbidden wedge of full area \(N^2/700\). **Both** potential losses of wedge material outside the incoming band are retained: the lower-band correction \(\Delta_+^2/16\), and the above-\(y=1\) correction \(\Theta_+^2/14\).

For \(C=62-40\sqrt2=N+x-7y+7s_A+s_D\), the combined positive quadratic is
\[
Q_0=N^2/700+(x^2+y^2)/2+(s_A^2+s_D^2)/14+2\omega^2,\quad
\omega=h-(x+y)/2.
\]
Weighted orthogonal projection supplies the **identity**, not just an inequality,
\[
Q_0=C^2/1500+\|z-z_*\|^2_{\rm weighted}.
\]
The lower-band error is **automatically paid by this variance**: its affine functional's squared dual norm is \(31/2<16\), and its value at the quadratic minimizer is strictly negative. If the upper clipping \(\Theta_+\) is inactive, \(B-|S|\ge C^2/1500>(38/7)^2/1500>1/51\). If \(\Theta_+>0\), its minimizer value is \(<-29/20\), forcing extra variance at least \(841/45600\); combined with separate explicit bounds \(\Delta_+<2/5,\Theta_+<17/50\) yields
\[
B-|S|>\frac{1107821}{55860000}
=\frac1{51}+\frac{212957}{949620000}.
\]
If the wedge's width \(N\le0\), the two actual tip-score losses alone already exceed the threshold. All cases contradict \(|S|>B-1/51\). No numerical optimization or computer premise enters.

**Exact checks and trust boundary.** The [byte-matched checker](computer-assisted/check_two_sided_clipping_dual.py) and [run record](computer-assisted/two-sided-clipping-dual-checks.json) passed **33 rational comparisons and 96 polynomial-identity cases (129 total)** under a five-second cap, taking about **0.002475 seconds**. The executed SHA-256 is \`eb935ecb52f5808dff06e6fe83a7ae72312a9c1af10b76c8695d26cd2bf0aa49\`, Git blob \`1ae2a7cb3f01f5f13e0a2e184914504ba620344e\`, matching the committed source. The first checker draft incorrectly demanded *strict* inequality for two exact rational endpoint equalities; those were corrected before the passing run. These **finite tests do not verify the continuum hand proof**. No CI, Lean/Lake build, manuscript build, installs or long search was run.

**Remaining mathematical frontier:** JD1 excludes a broader near-maximal three-hallway region than JH, but does not control the full continuously rotating envelope near Romik's candidate. The known connected finite four-hallway witness of area 1.73172...>M and the general partial-turn angle-reach limit remain. Do not present JD1 as optimality or as outperforming the externally certified 1.765.

## Latest substantial hand improvement — an explicit \(1/90\) three-hallway deficit

Read the complete new [JH1 paper proof](coupled-three-hallway-hand-bound.md). **The hand-proved global ambidextrous upper bound has improved to**
\[
\boxed{\mu_{\rm ambi}\le 2\sqrt2-1-\frac1{90}<1.817317}
\]
for **all common-starting-position ambidextrous sofas**, including arbitrary continuous partial or nonmonotone turns, as well as for the full-turn subclass. The proof is **without computer assistance**: two \(45^\circ\) hallways and one earlier \(36.87^\circ\) lower hallway; no numerical optimizer, finite-angle certificate, assumed curvature, cap regularity or reference-proximity input. It improves the original tiny TH \(10^{-9}\) gain by over **eleven million times**, and supersedes both TH and the intermediate independent QT \(1/175\) result.

**Exact structure.** If a sofa's area lies within \(\epsilon=1/90\) of the two-midpoint maximum \(B=2\sqrt2-1\), the \(45^\circ\) geometry forces an exact quadratic area-loss identity
\[
B-|F|=\frac{(P-2)^2+(Q-2)^2}{2}
 +2\left(c-\frac{P+Q}{2}\right)^2.
\]
A *careful* preliminary estimate establishes its domain, including when one width equals 2 and a zero-area connector links the two lobes. The true sofa must leave two tip triangles, of areas \(s_A^2/14,s_D^2/14\), unfilled. Actual retained support points determine \(s_A,s_D\) and force a central forbidden third-hallway wedge of area \(N^2/700\), less at most an **explicit** under-band clipping term \((\Delta_+)^2/16\). The exact algebraic relation
\[
C=N+x-7y+7s_A+s_D,\quad C=62-40\sqrt2
\]
and weighted Cauchy--Schwarz give the deficit
\[
B-|S|\ge\frac{C^2}{1500}-\frac{(\Delta_+)^2}{16}
>
\frac{39667}{3528000}>\frac1{90},
\]
a contradiction. The rational comparison margin is \(467/3528000\). In the near-maximal region, \(\Delta_+<11/30\). The earlier error of omitting necessary connectedness at a zero-area join is **not repeated**: the disconnected shortcut is used only if both outer rectangle dimensions strictly exceed two.

**Validation:** [rational checker](computer-assisted/check_coupled_three_hallway.py) and [run record](computer-assisted/coupled-three-hallway-checks.json) report **21 exact rational inequalities and 27 independent polynomial identity instances**, 48 successful checks, in about **0.0008 seconds** under a five-second cap. Executed source Git blob is \`5043e06dbeda5e73e766bf313e47286a3bd5c0a7\`, SHA-256 \`a2b1ff44b79a3c12b079826c0a96d8001515698d61739dfa427b060713062973\`, matching the committed source. The earlier exact local stability identity was independently tested on **76** finite polygon configurations. None of these finite checks replaces the continuum hand proof or an independent referee.

**Critical limitation:** This remains numerically weaker than Devin O'Keefe's external computer-certified \(\mu_{\rm ambi}\le353/200=1.765\), and **does not prove** Romik's sharp \(M\approx1.6449552184\), nor uniqueness. It *does* show a materially stronger hand-proof mechanism: pay the actual missing material in **all three** geometric regions jointly, instead of charging the same entire area-loss allowance to each isolated witness. No CI, Lean/Lake compilation, installation, manuscript build or long search was performed. PR #3 remains open and draft.

## New general computer-free bound: three hallways eliminate the 45° equality shape

[TH1](strict-hand-three-hallway-bound.md) proves, by hand and **without a finite-angle certificate search**, that **every** compact connected common-starting-position ambidextrous sofa—including arbitrary continuous partial motions—satisfies
\[
\boxed{|S|\le2\sqrt2-1-10^{-9}.}
\]
The same bound holds for full-turn sofas. This is a strictly better **pure hand bound** than the earlier \(2\sqrt2-1\), but remains far weaker than the **externally computer-certified** \(353/200=1.765\) and does not establish Romik's \(M\approx1.644955\). It is not presented as a new best numerical world bound.

The proof uses the two opposite proper 45° hallways to enclose every candidate in a rectangle with two opposing forbidden corners, intersected with a diagonal band. If a *connected* sofa had area greater than \(B-10^{-9}\), \(B=2\sqrt2-1\), the exact triangular density of the unit-square sum coordinate forces both rectangle widths within \(1/50\) of two and the band center within \(1/100\) of two. Three explicit **positive-area rational rectangles** must each contain some sofa point, because omitting any would lose more area than the presumed \(10^{-9}\) deficit. The first two points force **both actual support depths** at the third to exceed one for the rational normal pair \((4/5,3/5),(-3/5,4/5)\). No proper \(36.87^\circ\) hallway can contain that sofa. Every ambidextrous motion of area above this threshold must visit both proper 45° frames by GH/O'Keefe's wrong-way-angle argument, and the lower motion crosses the intermediate 36.87° angle by continuity.

**Critical audited edge case:** when one of the two 45° rectangle widths equals **exactly 2**, a *zero-area connector line* can join the two corner lobes. The final TH proof explicitly retains it; only the case **both widths strictly above 2** gives separated components. The connector has zero area, so the quantitative corner-square mass argument covers the equality-width case without falsely discarding it.

The companion [ten-plus-one exact rational arithmetic checks](computer-assisted/check_strict_hand_three_hallway.py) are supplementary; **the proof is the displayed hand geometry**, not those checks. TH is a useful example of incorporating CP actual-support obstructions and BH-style **area stability** into a global hand exclusion, rather than a claim that BH's box modulus alone makes the four-angle problem sharp. The known connected four-angle area witness \(1.73172\ldots>M\) still prevents any four-angle-only route to Romik optimality.

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
