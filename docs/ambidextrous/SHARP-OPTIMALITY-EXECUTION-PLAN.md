# Sharp ambidextrous moving-sofa optimality — controlling execution plan

**ACTIVE plan · October 9, 2026.** This document, not the historical [ROADMAP.md](ROADMAP.md), sets the priorities for draft [PR #3](https://github.com/vltanh/lean4-moving-sofa/pull/3). The [CONSOLIDATED-RESEARCH-HANDOFF.md](CONSOLIDATED-RESEARCH-HANDOFF.md) remains the authoritative record of what has and has not been proved.

**Honest baseline.** Romik's construction has proven area
\[
M=1+4Y^2+\arctan Y\approx1.64495521842544,\qquad 4Y^3+3Y-1=0.
\]
Unrestricted optimality, uniqueness, and exclusion of above-M bodies **are not proved** by the branch. Local stability, convex-only bounds, support classifications and numerical screens are not global sharp progress. The externally established bound \(353/200=1.765\) remains stronger than the branch's own coarse global bound.

## One non-negotiable final theorem

We must prove the sharp bound for **one connected physical shape** negotiating the *two distinct unit right-angle corridors*, from a common incoming orientation, with arbitrary continuous rotations including backtracking, subunit vertical height and **two independently partially completed turns**, using the actual outgoing straight-arm strips. No assumed reflection symmetry, contact pattern, curvature cap or full-turn completion.

The [OS1 original-motion signed formulation](original-motion-signed-convex-domain.md), *subject to Gate 0's independent audit*, converts that task to a single compact parameter domain. For every compact convex \(K\subset B=[-5/2,5/2]\times[0,1]\), write its projection \(I=[l,r]\), width \(W=r-l\), its two downward cap upper roofs \(A_U,A_V\), their outer deficits \(d_U=1-A_U,\ d_V=1-A_V\), and the exact positive swept-niche roofs \(n_{K;\alpha},n_{\rho K;\gamma}\) at independently visited angles \(\alpha,\gamma\). The true lower/upper whole-body outgoing strip barriers are \(e_{K;\alpha},e_{\rho K;\gamma}\).

Define the **complete joint ordinary-loss charge**
\[
\boxed{
\mathcal L(K,\alpha,\gamma)=
\int_I\left[
\max\{d_V,n_{K;\alpha},e_{K;\alpha}\}
+\max\{d_U,n_{\rho K;\gamma},e_{\rho K;\gamma}\}
\right]\,dx.
}\tag{PLAN.1}
\]
The exact **signed** envelope area is
\[
\boxed{\mathscr V(K,\alpha,\gamma)=W-\mathcal L(K,\alpha,\gamma).}\tag{PLAN.2}
\]
For auxiliary hulls with empty fibers, ordinary envelope area is the integral of the **positive part** of the fiber length, not the signed expression. For an actual connected feasible sofa its canonical envelope has every projected fiber nonempty, so the signed and ordinary expressions agree.

**The sole target theorem**, for all \(K\subset B\) and independently \(\alpha,\gamma\in[\pi/4,\pi/2]\), is
\[
\boxed{\mathcal L(K,\alpha,\gamma)\ge W-M.}\tag{PLAN.3 — UNPROVED}
\]
Given a fully audited OS1 equivalence, this proves unrestricted \(\mu_{\rm amb}\le M\); Romik supplies the reverse inequality, hence equality. A direct bound for every physically admissible sofa is an equally acceptable substitute, but must actually cover arbitrary original motions rather than a named subclass.

**No shortcut is presumed.** General signed Minkowski concavity has a rigorous counterexample even with height one, one-turn weighted concavity fails on known rectangular families, unrestricted curvature domination is not established, and no reference perturbation theorem controls distant opposite-end hulls. Do not use those false or unproved global premises.

## Gate 0 — independently audit the bridge to original motions

**Status: PASS (October 9, 2026; written mathematical audit, externally unrefereed).** The standalone [Gate 0 end-to-end proof](original-motion-global-bridge-gate0-audit.md) rederives the genuine wrong-way angular reach, exact two outgoing strips, common-hull tightening, empty-fiber signed correction, width-five compact box, and area-preserving horizontal gap compression for **both independent partial turns**. It proves the complete supremum equality \(\mu_{\mathrm{amb}}=\sup_{K,\alpha,\gamma}\mathscr V(K,\alpha,\gamma)\) on the planned parameter domain. It also gives a genuine unit-height high-area tilted top-cut family with **positive ambient clipping**, confirming the max/min accounting is indispensable. Note 9's older niche subtraction was **correct** because it had already defined both niches as **\(K\)-clipped** sets; an earlier suspicion of an error in that identity was a notation misunderstanding, not a discovered counterexample. The new independent proof is self-reviewed and open to external mathematical scrutiny.

**Gate 0 is no longer the active workstream. The next active proof obligation is Gate 1, the global full-turn sharp ordinary-area charge.** Before invoking the global variational target as a final proof, independently rederive and check:

- the correct-handed and terminal-angle reduction for arbitrary motions with area near or above M, including **the two actual outgoing strip normals** (GH / Note 10);
- canonical supporting-hallway tightening and both positive niche envelopes, including all end-angle conventions (OS1);
- the **max/min vertical fiber identities**, sign of the empty-fiber correction, and why a connected actual body has no empty projected fiber (OS1);
- area-preserving **horizontal-gap compression** for arbitrary auxiliary disconnected envelopes while retaining BOTH turning families AND outgoing strips (GC4);
- the fixed compact hull box, and exact reference equality \( \mathscr V(K_*,\pi/2,\pi/2)=M\).

**Adversarial checks, not proofs by sampling:** test the formulas against an auxiliary rectangle with empty central fibers, a disconnected full-turn envelope, a nonsymmetric opposite-end-face polygon, a genuine partial-turn triangle with its outgoing strip, and Romik. If a dependency fails, **repair the target and prove the correction** before continuing. No claim that a long self-reviewed chain was independently audited when it was only cited.

**Gate 0 PASS:** short, stand-alone checked proof of the actual-geometry-to-PLAN.3 value implication, or an exact counterexample and corrected theorem. **Gate 0 FAIL:** an essential implication is false and no valid replacement exists. This becomes the immediate research priority, not an invitation to switch to another local sofa class.

## Gate 1 — global sharp FULL-TURN area (THE FIRST UNRESOLVED PROOF GATE)

**Status: ACTIVE — sharp global full-turn bound UNPROVED. CURRENT focus: G1.SD2 spatial one-cap dual value theorem; historical facet oracle is verification only.** Gate 0 was marked PASS after a *self-reviewed* end-to-end written audit; external checking is still required. Gate 2 (arbitrary partial angles/outgoing strips) remains blocked. We are working on **Gate 1 only** until its exact acceptance condition is met or a mathematically decisive obstruction forces a documented revision.

### CURRENT REORIENTATION (October 9): Gate 1's **one active claim** is a sharp spatial one-cap value theorem

The earlier G1.2 approach "enumerate and integrate all polygonal facet sweeps" has **a calculation oracle but no global inequality**, and unrestricted polygon facet counts have no finite cutoff. It is now a **verification resource**, **not** the active proof mechanism. Merely extending the exact evaluator will not move the sharp area bound.

The [new Gate 1 spatial-dual note](gate1-spatial-dual-height-width-compactness.md) proves a globally sharp-at-Romik **ordinary-fiber upper relaxation**: for any actual connected full-turn hull with upper and vertically reflected lower caps U,V, of common horizontal projection I=[l,r], W=r-l, choose the width-dependent middle half \(J=[l+W/4,r-W/4]\), and put
\[
\mathcal P(U)=\int_{I\setminus J}A_U(x)\,dx-\int_J n_U(x)\,dx.
\]
Here \(A_U\) is the true upper convex cap roof, and \(n_U\) is the **complete continuous-angle inner-wall two-ray niche roof**, not a chosen one-angle shadow. Pointwise dropping **outer** deficits on J and **niche** deficits outside J gives
\[
\boxed{|S|\le\mathcal P(U)+\mathcal P(V),\qquad
\mathcal P(U_*)=M/2.}\tag{G1.SD1}
\]
Both niches are charged once, all clipped portions are handled by the original max/min fiber bounds, and the relaxation has **exact equality** at Romik.

**The ONE ACTIVE universal lemma to prove or falsify is**
\[
\boxed{\mathcal P(U)\stackrel{?}{\le}M/2
\quad\text{for every downward convex height-one one-turn cap }U.}
\tag{G1.SD2 — ACTIVE, NOT PROVED}
\]
It is **strictly stronger than** the necessary coupled G1.2 inequality. If valid, G1.SD1 immediately **passes Gate 1 for all genuine complete turns**, including arbitrary height/asymmetry/many-facet hulls; no global separate \(G\) clipping inequality is needed. If an **exact** convex cap with \(\mathcal P(U)>M/2\) is proved, abandon this **one-cap dual** immediately and return to the actual joint max G1.2—such a cap alone is **not** an area-\(>M\) sofa. An inconclusive screen is not a counterexample or a PASS.

**Global reduction already proved, not the value:** upward cap Minkowski extrusion increases exterior score by \(\varepsilon W/2\) and increases middle niche by at most \(\varepsilon W/2\), so only height **one** needs testing. A real inner-corner witness at \(t=\pi/4\) gives
\[
\boxed{n_U(x)\ge(W/2-\sqrt2-|x-x_{\mathrm{mid}}|)_+,}
\]
making every cap of width \(W\ge6\) too low-valued to reach \(M/2\); the trivial exterior bound excludes \(W\le8/5\). The spatial score is Hausdorff-continuous on the remaining bounded downward-cap class, so its **global maximum is attained** by a cap with \(8/5<W<6\), of possibly nonsmooth boundary. See SD2–SD3 for the full proofs, not an assumed compactness or curvature cap.

**NEW GLOBAL NECESSARY CANONICAL FORM (MID2, proved October 9):** [gate1-global-middle-chord-canonicalization.md](gate1-global-middle-chord-canonicalization.md) proves a nonlocal **score-improving** map from *every* downward convex cap to a height-one cap with the **entire width-dependent middle-half upper roof affine**. Intersect U with the upper half-plane beneath the chord joining its roof at the two endpoints of J: concavity leaves **both charged exterior wings unchanged**, but can only lower every entire moving-ray niche. Then vertically extrude to exact height one, using SD2 without score loss. Thus
\[
\boxed{\sup_{\text{all caps}}\mathcal P
=\sup_{\substack{\text{height-one caps}\\A|_J\ {\rm affine}}}\mathcal P.}
\tag{G1.SD-MID2 — PASS}
\]
The candidate is fixed by this transformation. **This does not establish \(\mathcal P_{\max}=M/2\) or pass Gate 1**, but is a genuine global maximizer-domain reduction within the ONE current proof claim. The middle facet may be **tilted**, with its height-one maximum on an exterior wing. Do not silently assume it is flat, centered, or admits a candidate contact chart. The **current mathematically necessary next step** is to derive the complete *first-variation and niche-exposure balance of the two charged exterior wings* on this canonical domain, and use it to force the *sharp global value*, not another local no-gain family.

**NEW FINITE GLOBAL-MAXIMIZER EXPOSURE LAWS (FE1, not yet the continuum sharp theorem):** [gate1-spatial-exposure-moving-window-variation.md](gate1-spatial-exposure-moving-window-variation.md) derives **exact first-order stationarity** for the finite-angle *spatial P* maximizing polygon, not the older weighted \(\Psi\) optimizer. Pushing a floating facet gives charged **exterior-only** facet length \(\ell_j^{\rm wing}\le\tau_j^{\rm middle}+o(1)\), where the inner-wall measure is exposed **inside J**, not over the whole ambient niche. Moving an axis wall moves J's endpoints and yields the **correct nonconstant** side-face pressures
\[
e_R\le\tfrac34(A+n)(j_+)-\tfrac14(A+n)(j_-)+o(1),\qquad
e_L\le\tfrac34(A+n)(j_-)-\tfrac14(A+n)(j_+)+o(1).
\]
At the reference these are tight equalities \(1/2=3/4-1/4\), but for arbitrary caps they are **not** the constant one-half width-penalty terms of the separately solved \(\Psi\) problem. Summing exposed graph **horizontal projections** gives the finite polygon restriction
\(
|\{x\in J:n_n(x)=0\}|\le T_{\rm wing}+o(1)
\),
where \(T_{\rm wing}\) is the horizontal top-face length outside J. **DO NOT pass this to the full niche by naive uniform roof convergence:** zero sets of nonnegative functions are not semicontinuous in the required direction. A real *full-continuum exposure/curvature and zero-level projection* theorem, incorporating the affine middle roof MID2, is still missing. This is the precisely identified Gate 1 obstruction on the active scalar proof route, not a new named-shape class.

**NEW GLOBAL MAXIMIZER WING-REGULARITY (RG2–RG3, written proof, Oct 9):** [gate1-spatial-maximizer-wing-curvature-regularity.md](gate1-spatial-maximizer-wing-curvature-regularity.md) upgrades MID2 and finite charged-exposure FE1 into a **selection theorem for an actual global maximizer of \(\mathcal P\)**. A grid-polygon penalized selection targeting the chosen affine-middle global maximizer gives convergence despite arbitrary initial irregular support. The neighboring-inner-ray bound plus exterior-only facet stationarity yields
\[
\ell_{n,j}\le (6B+6)\delta+b_{n,j}+\ell^{\rm middle}_{n,j}.
\]
As the limit's entire middle roof is affine, middle lengths of facets with normals outside its normal \(\theta_c\) vanish. Thus all wing curvature singular-continuous parts and wing atoms vanish: the chosen optimizer has a \(W^{2,\infty}\) upper support on open-quarter arcs away from the central facet and top normal. Moreover the sharper *globally necessary nonlinear* source-curvature constraints hold a.e.:
\[
\boxed{\rho_f(t)\le\kappa(q(t)),\quad\rho_g(t)\le\kappa(p(t)),\quad
\kappa(z)=\max\{|z|,(1+|z|)/2\}.}
\]
The **sharp corridor bound \(\rho\le1\) does NOT follow** until a genuinely *spatial-score*-valid global balance forces \(|p|,|q|\le1\); old weighted \(\Psi\) conditions (including constant half-length end faces) **cannot be imported**. The central affine facet may be tilted and may coexist with a top face away from J. **The exact remaining sharp Gate 1 step is a whole-angle, window-weighted niche exposure/equality plus the global maximizer value, not another cap-class exclusion.** No improvement of the unrestricted upper bound or Gate 1 PASS is claimed.

**NEW GLOBAL MAXIMIZER FACET-PINNING LAW (TF3, Oct 9; Gate 1 still OPEN):** [gate1-spatial-tilted-facet-pinning.md](gate1-spatial-tilted-facet-pinning.md) proves that any chosen maximizer of \(\mathcal P\) after MID2, whose middle roof \(A(x)=a+s x\) has \(s\ne0\), **must have two strict slope jumps exactly at the moving middle-window endpoints**:
\[
\boxed{A'_-(j_-)>s>A'_+(j_+).}
\]
The proof is global-in-caps and uses **all real inner-wall ray angles**, not a local Romik contact phase: the tilted central facet's outer normal \(n_c=(-s,1)/\sqrt{1+s^2}\) has its *inner shifted wall strictly below the entire baseline on J*, by margin \(1-1/\sqrt{1+s^2}>0\). A small outer-wing bump changing support only in a safe normal arc leaves \(n_U|_J\) **exactly unchanged** while increasing charged wing area. Thus a tilted central facet cannot extend into a charged wing or meet either wing tangentially. **A \(C^1\) junction at either middle-window endpoint forces \(s=0\) and \(A\equiv1\) on J.** The global proof includes the exact all-angle rational triangle check \(\mathcal P(U_\varepsilon)-\mathcal P(U)=3\varepsilon/7>0\). 

This is a new necessary condition at the **global scalar maximizer**, not another candidate-neighborhood exclusion. **It does NOT exclude possible tilted facets with two genuine pinned corners**; such caps and arbitrary smooth wing exposure remain. No bound \(\mathcal P\le M/2\), improvement of the unrestricted upper bound or Gate 1 PASS is inferred. **Next:** determine whether pinned tilted extrema can be excluded *by the true spatial exposure balance*, and characterize the horizontal-facet case without importing \(\Psi\)'s different stationarity law.

**Research method within this exact active claim:** work **directly at a global maximizer of \(\mathcal P\)** using cap-support variations and the **full** niche exposure balance. Try to derive necessary global contact/curvature/face conditions that force \(\mathcal P\le M/2\), without assuming the Romik phase chart. Test any claimed structure immediately on exact adversarial caps. The known \(\mathcal P\) **Minkowski concavity** conjecture is false ([CN](candidate-functional-concavity-counterexample.md)): do **not** try Jensen or a generic interpolation tangent argument. Existing curvature repair proofs for the *different* weighted \(\Psi\) objective cannot be copied without rechecking the spatial exposure weights and moving J endpoints.

**Hard stopping rule:** If the global maximizer cannot be characterized, state the exact unresolved first-variation/exposure inequality—not another infinite series of local shape cases. Gate 1 remains **ACTIVE** until G1.SD2 is fully proved or the *original* coupled G1.2 is otherwise settled. The exact finite polygon oracle and facet-triangle reduction stay available only for mathematically meaningful adversarial verification.

### G1.0 Fix the objective and the domain; don't mix actual and auxiliary hulls

For a **genuine compact connected both-full-turn sofa** \(S\), put \(K=\operatorname{conv}S\), its horizontal projection \(I=[l,r]\) of width \(W\), its actual upper/lower convex roofs \(A_K,B_K\), their downward-cap deficits
\[
d_U(x)=1-A_K(x),\qquad d_V(x)=B_K(x),
\]
and the complete lower/upper two-ray forbidden roofs \(n_-(x),n_+(x)\). Each niche uses the **supremum over every real angle \(0<t<\pi/2\)**, with both attached rays of the **physical moving sharp inner corner**; do not replace it with a corner shadow, one selected ray, a finite-angle grid, or a signed untruncated niche.

The exact surviving full-turn fiber has length
\[
\ell(x)=1-\max\{d_V(x),n_-(x)\}-\max\{d_U(x),n_+(x)\}\ge0
\]
because every x in I occurs in connected S. Hence, with the **actual ordinary-area** niche removals
\[
\mathcal N_-(K)=\int_I(n_-(x)-B_K(x))_+dx,\quad
\mathcal N_+(K)=\int_I(n_+(x)-(1-A_K(x)))_+dx,
\]
we have **exactly**
\[
\boxed{|E_{\rm full}(K)|=|K|-\mathcal N_-(K)-\mathcal N_+(K).}\tag{G1.1}
\]
Here the two \(\mathcal N\) are clipped to K, and nonempty fibers ensure they do not overlap inside K. No need for unit vertical span, reflection symmetry, or an assumed face arrangement. The **one sharp objective** is
\[
\boxed{\mathcal N_-(K)+\mathcal N_+(K)\ge |K|-M
\qquad\text{for EVERY genuine feasible both-full-turn }K.}
\tag{G1.2 — OPEN}
\]

**Coverage logic:** If G1.2 holds for all actual feasible K, it bounds every genuine full-turn body. Conversely any arbitrary auxiliary K has a possibly disconnected canonical envelope with ordinary area \(|E_{\rm full}(K)|\ge\mathscr S(K)\). Gate 0's area-preserving gap compression converts that envelope to an actual connected full-turn sofa, so **G1.2 for all feasible actual hulls bounds the signed full-turn supremum too**. This is not a claim that the auxiliary K itself retains its exposed extreme points. Do not assume actual-hull theorems for incompatible auxiliary hulls.

### G1.1 PASSED in written audit: full-ray facet triangles and globally feasible polygonal-hull density

[PG.1–PG.12](gate1-facet-audit-and-feasible-polygon-density.md) independently checks the **actual-hull** one-angle oblique triangle, including both physical moving inner rays, correct upper-roof clipping, and a concrete **genuinely feasible oblique-facet** test with exact positive area. The audit corrects one overstrong claim in FT: a cut cannot *contain* a facet endpoint but its base **can terminate there** at zero height; this needs no strict endpoint clearance. Crucially, **PG1 proves every connected full-turn sofa is area-approximable from below by an actual connected full-turn sofa built from finitely many rectangles plus vertical joining segments, whose **actual convex hull is a finite polygon**. It uses true entire-ray survivor fibers, finite horizontal-gap compression and vertical filling; smoothing an arbitrary hull is not claimed feasible. Therefore the sharp full-turn value theorem is **equivalent** to the exact facet-sweep inequality PG.12 for **all finite genuine polygonal hulls**, without separately handling singular boundaries, countably many facets or a curvature cap.

**G1.1 status: PASS as a self-reviewed written derivation, external mathematical review pending. G1.2 remains ACTIVE and UNPROVED.** The polygonal coverage reduction does **not** itself bound area and gives no uniform upper bound on polygon complexity.

### Historical original G1.1 statement (retained for exact definitions)

The recent [FT1–FT8 facet-triangle argument](global-facet-triangle-niche-decomposition.md) supplies the intended **global geometric input**, subject to an independent adversarial audit. At each proper lower angle t, the roof
\[
q_t(x)=\min\left\{
\frac{h_K(u_t)-1-x\cos t}{\sin t},
\frac{h_K(v_t)-1+x\sin t}{\cos t}
\right\}
\]
is concave. Since the lower hull roof \(B_K\) is convex, \(\{x:q_t(x)>B_K(x)\}\) is an interval. Every lower extreme point of K survives the actual motions and therefore cannot be inside a forbidden cut. The proposed lemma says **every nonempty one-angle cut is one true triangle with its base on a straight exposed lower hull facet and apex at the moving physical sharp corner**. The upper hand is its vertical reflection.

For a base facet \(B_K(x)=mx+c\), at apex \((\xi_t,\eta_t)\) and gap \(h_t=\eta_t-m\xi_t-c>0\), the exact proposed one-angle area is
\[
\boxed{|K\cap Q_t|=\frac{h_t^2}{2}
\left(\frac1{\tan t-m}+\frac1{\cot t+m}\right)}
\tag{G1.3}
\]
when \(-\cot t<m<\tan t\). The identity must be checked at exposed-face endpoints, upper-roof clipping, zero-area limits and nonsmooth junctions **before** it is a proof dependency.

Crucially we **never sum G1.3 over angles**: those triangles can overlap arbitrarily. Write \(\mathcal F_-\) and \(\mathcal F_+\) for the at-most-countable exposed **lower** and **upper** facets of the actual hull. The full union of all t-rays on one lower facet F has the exact fiber height
\[
n_F(x)=\left[\sup_{0<t<\pi/2}
(q_t(x)-B_F(x))\right]_+,
\quad x\in I_F.
\]
If the audited facet identity passes, it gives
\[
\boxed{\mathcal N_-(K)=\sum_{F\in\mathcal F_-}\int_{I_F}n_F(x)dx,
\qquad
\mathcal N_+(K)=\sum_{F\in\mathcal F_+}\int_{I_F}n_F^+(x)dx.}
\tag{G1.4}
\]

**G1.1 PASS:** independently checked geometry and measurability of G1.3–G1.4 for every genuine full-turn hull, including multi-peak/disconnected angular activity and oblique supporting facets. **A failed hypothesis or wrong sign must be corrected now, not buried in later assumptions.**

### Historical G1.2 support → facet-sweep target (PAUSED as proof mechanism; still the exact necessary full-turn bound)

The exact original Gate 1 coupled acceptance inequality remains, for **all actual feasible K**,
\[
\boxed{
\sum_{F\in\mathcal F_-}\int_{I_F}n_F(x)\,dx
+\sum_{F\in\mathcal F_+}\int_{I_F}n_F^+(x)\,dx
\ge
\int_I[A_K(x)-B_K(x)]\,dx-M.}
\tag{G1.5 — UNPROVED}
\]

By the passed global PG1 reduction, **one may and should first prove this for all actual polygonal full-turn hulls** with finitely many faces; the resulting sharp inequality would pass to all full-turn bodies by area density, without assuming polygonal circumscription preserves feasibility. There is no uniform bound on the number or slopes of the faces. Build **one quantitative outer-support-to-carved-facet charge**, using the *actual* moving corners and both attached rays. Outer curvature/face support data determine their trajectories; the resulting **union** of triangular cuts is charged exactly once on each exposed facet. A valid certificate must quantify the gained hull material against lost true niche area, including oblique facets, all contact switches, positive curvature atoms, and unknown facet count.

**Necessary calibration:** At Romik's exact hull both sides of G1.5 are equal. The same certificate must remain valid for the *genuinely asymmetric value-dense opposite-end-face class*; one cannot assume both horizontal faces align, that the niche is confined to the center, or that the outer support has curvature <=1. A universal fixed-price-per-triangle lemma that loses Romik equality or double-counts overlapping angular cuts is not a candidate.

**Proof target:** derive an explicit nonnegative **integrated remainder or dual transport certificate** for the *difference* between the left and right sides of G1.5. A rearrangement based on a single stationary Romik contact chart is not enough. Whether a transport can be made without active-contact regularity is the first real open mathematical question. We do not promote a heuristic lower bound as G1.5.

**Alternative equivalent syntax, not a second project:** The exact signed identity \(\mathscr S=\Psi(U)+\Psi(V)+G\) makes the same requirement \((M/2-\Psi(U))+(M/2-\Psi(V))\ge G\) for genuine full-turn compatible cap pairs. The \(\Psi\le M/2\) theorem has a long self-reviewed dependency chain. This equivalence may be used to **audit a proposed transport proof**; it is **not** a license to assume the missing clipping budget or re-start a separate weighted one-turn optimization.

### G1.2 rejected sharp-charge mechanism: **finite fixed-angle packing loses positive area at Romik**

[ANG1–ANG3](gate1-no-fixed-angle-weighted-sharp-charge.md) proves an exact negative control on a natural proposed support-to-facet transport: at Romik's middle exposed-corner chart there is a **positive-length** interval of abscissae with a **strict unique globally maximizing physical inner-ray angle**. Every finite collection of angles therefore misses positive ordinary niche area *at the exact equality candidate*. More generally, for any **finite fixed nonnegative measure** \(\mu\) over angles whose pointwise cut multiplicity satisfies \(\int1_{\{p\in Q_t\}}d\mu(t)\le1\) almost everywhere, Tonelli and the unique-contact graph give
\[
\boxed{\int |K_*\cap Q_t|\,d\mu(t)<|N_*(K_*)|.}
\]
Thus a **position-independent, pointwise no-overcounting weighted average of one-angle facet-triangle areas cannot give a sharp Gate 1 certificate**. This does **not** disprove any x-dependent or contact-dependent transport, nor any genuinely global coupled loss inequality. **Gate 1 remains ACTIVE, not passed**. The proof's only use is to reject a specifically false route to exact Romik equality; do not count it as an improved upper bound or a new excluded sofa class.

### G1.2 finite whole-angle algebraic oracle (PASS as a calculation theorem; **NOT** the sharp area charge)

[EO1–EO6](gate12-exact-whole-angle-polygonal-niche-oracle.md) now provide a **globally quantified exact continuous-angle calculation** for any rational polygonal hull: the positive one-turn niche at any x is the maximum of at most \(8(2N+1)\) candidates, arising from actual outer-support vertex switches, unit-circle inner-ray tangencies or **physical sharp-corner ties**. The last satisfy a quartic polynomial in \(\tan(t/2)\), including folded corner paths. The complete two-hand envelope (including empty-fiber corrections) has a finite semialgebraic decomposition, and its exact **ordinary area** is a finite elementary combination of algebraic numbers and algebraic coefficients times arctangents of algebraic numbers. This eliminates any need to approximate turning angles when **evaluating one polygon's true niche union**.

EO3 strengthens the existing actual-feasible polygonal density to **rational** finite-vertex bodies. EO6 adds the first explicit **uniform shape-independent polygonal approximation error**: for every full-turn sofa S in the audited fixed hull box and every n, there is an *actual feasible* rational polygon-hull sofa with at most \(4n\) vertices and area \(\ge |S|-21/n-230\sqrt{5/n}\). This holds with high curvature, asymmetry, arbitrary contact switches, and even subunit incoming height; it is an exact direct application of both true all-angle sweeps and monotone gap compression.

**THIS DOES NOT PASS G1.2.** The exact finite evaluator has **not** supplied the required uniform positive lower bound G1.5 on the carved area for *every n and every admissible rational polygon*. An unbounded enumeration of exact polygon checks cannot establish the inequality. The only active proof target remains G1.5/PG.12; no claim of a new numerical upper bound or candidate optimality is made.

### G1.3 Adversarial verification and exhaustive case coverage (before any PASS)

Every claimed candidate for G1.5 must survive at least:
- **Romik equality**, with complete true niche and exact outer hull; any strictly positive reference deficit invalidates a supposedly sharp certificate.
- **Opposite-end positive top/bottom faces** including the exact fully feasible diagonal parallelogram and **arbitrarily near-M** opposite-face approximants. A fixed positive penalty for asymmetric face displacement is known to be impossible.
- **Oblique exposed lower/upper facets**, high-curvature outer flanks and multifold/multipeak moving-corner trajectories; one-angle facet cuts need not have horizontal bases.
- **Tilted top/bottom shavings of Romik**, whose **ambient** niches partly lie *outside* their new outer hulls. Use only truly K-clipped ordinary areas.
- **Full-turn rectangular hulls** with reverse moving-corner activation and exact width-dependent niche areas; distinguish actual feasible unit-height rectangles from an incompatible width-two auxiliary rectangle with empty central fibers.
- **Subunit-height actual sofas** (do not invoke unsupported height padding), and **point/edge atoms**. Any appeal to a value-dense class needs a legitimate limiting theorem.

**Coverage shortcut permitted only with proof:** [PD3](full-turn-positive-face-density.md) claims all full-turn values can be approached by unit-height actual full-turn sofas with positive **opposite-end** horizontal faces, after rounding, shaving and justified reorientation. Independently audit its full chain *if* G1.5 is proved for that class alone. A uniform sharp bound on that genuinely value-dense class would then pass G1 through the limit. Otherwise **prove G1.5 on all actual full-turn hulls directly**; do not let the PD3 audit become an unrelated research line.

The [SD3/SD6 signed-continuity and smooth-auxiliary-density theorem](global-signed-fiber-continuity-and-smooth-density.md) is available for justified limits on the **auxiliary signed hull domain**. Its smooth hulls need *not* be feasible, so **do not apply G1.3's actual-hull facet theorem to arbitrary smooth auxiliary hulls**. This prevents mixing two incompatible quantifier domains.

### G1.4 Closure criterion, exact result required to change the gate

**Gate 1 PASS if and only if** we have a complete independently auditable derivation \(|S|\le M\) for **every** genuine connected two-full-turn sofa, including all incoming heights, asymmetries, nonsmooth facets and positive/negative empty-fiber distinctions; or a proved sharp inequality on a rigorously area-value-dense class plus its limiting argument. Show exact Romik equality. The conditional statement “if G1.5 holds then Gate 1 passes” **does not count**.

**Gate 1 FAIL/BLOCKED:** If a proposed payment lemma is false, exhibit the exact counterexample and repair or change the one chosen charge while retaining G1.2; do not claim progress from a false universal claim. If no payment is proved, report specifically which outer-support increment cannot be charged to which full facet-sweep union. No return to convex-only upper bounds, candidate-local classes, tangency samples or global Jensen shortcuts already disproved.

**After—and ONLY after—Gate 1 PASS:** activate Gate 2, restoring independent partial terminal angles and outgoing *whole-body* strips in PLAN.1. Passing Gate 1 does not silently complete partial turns and is not the final unrestricted sofa proof.

## Gate 2 — original PARTIAL turns with their two outgoing strips

**Status: BLOCKED.** Extend the **same joint charge** to all independent \((\alpha,\gamma)\) in the original OS1 domain, including any subunit height; alternatively prove a valid no-loss reduction from *every* original partial motion to a class controlled by Gate 1.

**Must not assume** a partial turn can always be extended to \(90^\circ\) in the same orientation. Exact counterexamples show zero-loss in-place completion fails. Saved early or late niche area must be compared with actual outgoing-strip losses in the **joint max**, not as independent signed deficits.

**Gate 2 PASS:** PLAN.3 or equivalent for the entire original motion domain and a complete deduction \(\mu_{\rm amb}\le M\). **NOT PASS:** only turns near \(90^\circ\), the known rough endpoint-angle exclusions, or results requiring a Romik-neighborhood support chart.

## Gate 3 — equality, uniqueness and independent review

**Status: UNSTARTED.** Only after the unrestricted sharp value is proved, analyze whether every equality sofa has Romik's hull, complete terminal angles and actual area. Equality in any signed/support interpolation is not enough without connectedness and actual-hull retention. Prove uniqueness **separately**, if it is true.

Compile one self-contained manuscript, with all key equations and reduction proofs exposed for independent mathematical review. No claim of Lean verification, automated kernel proof, or externally accepted publication.

## Rules for every subsequent research turn

1. **One active gate, one active global lemma.** Work Gate 0, then Gate 1, then Gate 2, then Gate 3. Do not start a new local deformation program when blocked.
2. **Report truthfully:** exact claim tested; what would settle it; proof or counterexample; remaining obstruction; **whether the unrestricted bound actually improved**.
3. **Strict commit filter:** commit only corrections to an indispensable global dependency, globally quantified proof steps, rigorous falsification of a needed global lemma, a certified *unrestricted* area improvement stronger than the known public upper bound, or a complete sharp proof. No paper padding, repeated convex estimates, or random-search artifacts.
4. **No made-up progress:** a negative result or failed attack can be useful, but is not presented as making the sharp bound closer. Count *passed gates*, not commits.
5. **Fixed stopping rule:** if the active inequality remains unproved after targeted falsification, report its exact missing measure or geometry estimate. Any change of mechanism must give a specific mathematical reason for abandoning the prior one, while preserving PLAN.3 as the north-star theorem.
6. **No deferred work promise:** perform current-session work and report the result; never assert background progress or promise a delivery date.
7. **Repository discipline:** [PR #3](https://github.com/vltanh/lean4-moving-sofa/pull/3), branch research/ambidextrous-pen-and-paper; all research commits marked [skip ci]; no CI, Lean/Lake, or original Lean library changes.

## Current gate status (updated October 9, 2026)

| Gate | Status | Concrete missing step |
|---|---|---|
| 0 — original-motion bridge | **PASS** (written audit) | End-to-end audit in original-motion-global-bridge-gate0-audit.md; still subject to external review |
| 1 — coupled full-turn loss | **ACTIVE: G1.1 passed; G1.2 sharp charge unproved** | Full physical facet-triangle audit and actual-feasible polygonal value-density in PG1 are complete as written; the **universal finite-polygon facet union area inequality PG.12 / G1.5** is still missing |
| 2 — complete original partial motions | **BLOCKED** | No sharp charge for both independent outgoing strips together with visited partial niches |
| 3 — equality/uniqueness | **UNSTARTED** | Requires unrestricted area theorem first |

**Definition of meaningful progress:** a passed gate, a global theorem that removes an indispensable gap, or a correct falsification requiring a documented change in the global strategy. Everything else is supporting research.
