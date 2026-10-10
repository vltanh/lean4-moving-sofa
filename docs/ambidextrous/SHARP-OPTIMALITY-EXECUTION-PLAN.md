# Sharp ambidextrous moving-sofa optimality — controlling execution plan

**ACTIVE plan · October 10, 2026.** This document, not the historical [ROADMAP.md](ROADMAP.md), sets the priorities for draft [PR #3](https://github.com/vltanh/lean4-moving-sofa/pull/3). The [CONSOLIDATED-RESEARCH-HANDOFF.md](CONSOLIDATED-RESEARCH-HANDOFF.md) remains the authoritative record of what has and has not been proved.

**Honest baseline.** Romik's construction has proven area
\[
M=1+4Y^2+\arctan Y\approx1.64495521842544,\qquad 4Y^3+3Y-1=0.
\]
Unrestricted optimality, uniqueness, and exclusion of above-M bodies with arbitrary partial turns **are not proved** by the branch. **Gate 1's complete-turn sharp bound is now proved at the written-proof level**, with its ordinary one-turn dependency explicit. Gate 2's partial-turn joint charge remains the first unresolved theorem. Local stability, convex-only bounds, support classifications and numerical screens do not settle that theorem.

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

**Gates 0 and 1 have passed their written-proof acceptance conditions. Gate 2 is now the first unresolved proof obligation.** The following Gate 0 audit requirements record the accepted bridge and remain relevant when using it. Before invoking the global variational target as a final proof, independently rederive and check:

- the correct-handed and terminal-angle reduction for arbitrary motions with area near or above M, including **the two actual outgoing strip normals** (GH / Note 10);
- canonical supporting-hallway tightening and both positive niche envelopes, including all end-angle conventions (OS1);
- the **max/min vertical fiber identities**, sign of the empty-fiber correction, and why a connected actual body has no empty projected fiber (OS1);
- area-preserving **horizontal-gap compression** for arbitrary auxiliary disconnected envelopes while retaining BOTH turning families AND outgoing strips (GC4);
- the fixed compact hull box, and exact reference equality \( \mathscr V(K_*,\pi/2,\pi/2)=M\).

**Adversarial checks, not proofs by sampling:** test the formulas against an auxiliary rectangle with empty central fibers, a disconnected full-turn envelope, a nonsymmetric opposite-end-face polygon, a genuine partial-turn triangle with its outgoing strip, and Romik. If a dependency fails, **repair the target and prove the correction** before continuing. No claim that a long self-reviewed chain was independently audited when it was only cited.

**Gate 0 PASS:** short, stand-alone checked proof of the actual-geometry-to-PLAN.3 value implication, or an exact counterexample and corrected theorem. **Gate 0 FAIL:** an essential implication is false and no valid replacement exists. This becomes the immediate research priority, not an invitation to switch to another local sofa class.

## Gate 1 — global sharp FULL-TURN area

**Status: PASS (October 10, 2026; written mathematical proof, external review and Lean verification outstanding).** The [complete Gate 1 theorem](gate1-sharp-full-turn-closure.md) proves the universal scalar value \(\mathcal P(U)\le M/2\) and deduces \(|S|\le M\) for every genuine connected both-full-turn sofa, with exact Romik equality. The signed full-turn charge is also bounded on the entire auxiliary convex-hull domain. The [dependency and coverage audit](gate1-dependency-coverage-audit.md) checks all case boundaries and the order of the geometric and ordinary-area inputs.

The final [reflected-tail projection](gate1-tilted-reflected-tail-and-projection.md) proves \(T>0\) and \(n(-C)=0\) without either whole-wing unit-curvature premise. The [height reduction](gate1-tilted-final-height-reduction.md) forces \(h<1/20\); the [small-height theorem](gate1-tilted-small-height-exclusion.md) excludes every \(0<h\le509/10000\), with overlap. Together with the complete horizontal theorem and earlier width cuts, these exhaust the selected canonical global maximizer. The external ordinary one-turn theorem and the existing exact Gerver enclosure \(G_0=22199/10000\) remain explicit dependencies.

**Gate 1 is closed. Gate 2's independent partial turns and outgoing strips remain unproved.** The full-turn theorem does not imply a no-loss completion of an arbitrary partial turn, unrestricted ambidextrous optimality, or uniqueness.

### Completed scalar theorem (introduced October 9; proved October 10)

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

**The completed universal scalar theorem is**
\[
\boxed{\mathcal P(U)\le M/2
\quad\text{for every downward convex height-one one-turn cap }U.}
\tag{G1.SD2 — PROVED}
\]
This theorem is **strictly stronger than** the necessary coupled G1.2 inequality. Height extrusion extends it to every cap of height at most one. The completed scalar proof and G1.SD1 **pass Gate 1 for all genuine complete turns**, including arbitrary height, asymmetry and nonsmooth or many-facet hulls. The original coupled niche-loss inequality follows without an additional separate clipping estimate. See G1C1–G1C2 for the exact proof and scope.

### Historical development of Gate 1

The dated progress notes and original acceptance-route discussion below retain the intermediate obligations as they stood when written. Statements that a subtheorem alone did not pass Gate 1 describe those earlier checkpoints. **The completed proof and current status above supersede every earlier ACTIVE, OPEN, or remaining-obligation description in this Gate 1 history.** The mathematical arguments remain linked for audit.

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
The candidate is fixed by this transformation. **This does not establish \(\mathcal P_{\max}=M/2\) or pass Gate 1**, but is a genuine global maximizer-domain reduction within the ONE current proof claim. The middle facet may be **tilted**; MID2 alone does not locate its top. The subsequent TF4 top-insertion theorem below places the height-one maximum at its higher J endpoint. Do not assume the facet is flat, centered, or admits a candidate contact chart. The necessary next step is to turn the complete *first-variation and niche-exposure balance of the two charged exterior wings* into the *sharp global value*.

**FINITE GLOBAL-MAXIMIZER EXPOSURE LAWS (FE1, corrected for zero end faces):** [gate1-spatial-exposure-moving-window-variation.md](gate1-spatial-exposure-moving-window-variation.md) derives the finite-angle *spatial P* conditions. Pushing a floating facet gives charged **exterior-only** facet length \(\ell_j^{\rm wing}\le\tau_j^{\rm middle}+o(1)\), where the inner-wall measure is exposed **inside J**. The original unconditional axis derivative was false: at a zero end face the axis wall is redundant, and moving it does not change the actual width or J. Two exact examples are now recorded in FE. For positive end faces the moving-window derivatives remain valid; the unconditional finite inequalities require positive parts:
\[
e_R\le\bigl(\tfrac34(A+n)(j_+)-\tfrac14(A+n)(j_-)+o(1)\bigr)_+,\qquad
e_L\le\bigl(\tfrac34(A+n)(j_-)-\tfrac14(A+n)(j_+)+o(1)\bigr)_+.
\]
At the reference these are tight equalities \(1/2=3/4-1/4\), but for arbitrary caps they are **not** the constant one-half width-penalty terms of the separately solved \(\Psi\) problem. Summing exposed graph **horizontal projections** gives the finite polygon restriction
\(
|\{x\in J:n_n(x)=0\}|\le T_{\rm wing}+o(1)
\),
where \(T_{\rm wing}\) is the horizontal top-face length outside J. **DO NOT pass this to the full niche by naive uniform roof convergence:** zero sets of nonnegative functions are not semicontinuous in the required direction. EP1–EP3 below supply exact continuum endpoint complementarity and limiting exposure moments. The new LH/CH results use those weak measures directly, prove positive pressures, and exclude excess curvature at nonpositive corner height without assuming ordinary continuum arclength convergence. The tilted sharp value remains open.

**NEW GLOBAL MAXIMIZER WING-REGULARITY (RG2–RG3, written proof, Oct 9):** [gate1-spatial-maximizer-wing-curvature-regularity.md](gate1-spatial-maximizer-wing-curvature-regularity.md) upgrades MID2 and finite charged-exposure FE1 into a **selection theorem for an actual global maximizer of \(\mathcal P\)**. A grid-polygon penalized selection targeting the chosen affine-middle global maximizer gives convergence despite arbitrary initial irregular support. The neighboring-inner-ray bound plus exterior-only facet stationarity yields
\[
\ell_{n,j}\le (6B+6)\delta+b_{n,j}+\ell^{\rm middle}_{n,j}.
\]
As the limit's entire middle roof is affine, middle lengths of facets with normals outside its normal \(\theta_c\) vanish. Thus all wing curvature singular-continuous parts and wing atoms vanish: the chosen optimizer has a \(W^{2,\infty}\) upper support on open-quarter arcs away from the central facet and top normal. Moreover the sharper *globally necessary nonlinear* source-curvature constraints hold a.e.:
\[
\boxed{\rho_f(t)\le\kappa(q(t)),\quad\rho_g(t)\le\kappa(p(t)),\quad
\kappa(z)=\max\{|z|,(1+|z|)/2\}.}
\]
The **sharp corridor bound \(\rho\le1\) does NOT follow** until a genuinely *spatial-score*-valid global balance forces \(|p|,|q|\le1\); old weighted \(\Psi\) conditions (including constant half-length end faces) **cannot be imported**. The central affine facet may be tilted; TF4 now forces its top to meet J at the higher endpoint. EP1–EP3 below refine the window-weighted limiting exposure balance but do not provide the missing visibility/velocity/value estimate. No improvement of the unrestricted upper bound or Gate 1 PASS is claimed.

**NEW GLOBAL MAXIMIZER FACET-PINNING LAW (TF3, Oct 9; Gate 1 still OPEN):** [gate1-spatial-tilted-facet-pinning.md](gate1-spatial-tilted-facet-pinning.md) proves that any chosen maximizer of \(\mathcal P\) after MID2, whose middle roof \(A(x)=a+s x\) has \(s\ne0\), **must have two strict slope jumps exactly at the moving middle-window endpoints**:
\[
\boxed{A'_-(j_-)>s>A'_+(j_+).}
\]
The proof is global-in-caps and uses **all real inner-wall ray angles**, not a local Romik contact phase: the tilted central facet's outer normal \(n_c=(-s,1)/\sqrt{1+s^2}\) has its *inner shifted wall strictly below the entire baseline on J*, by margin \(1-1/\sqrt{1+s^2}>0\). A small outer-wing bump changing support only in a safe normal arc leaves \(n_U|_J\) **exactly unchanged** while increasing charged wing area. Thus a tilted central facet cannot extend into a charged wing or meet either wing tangentially. **A \(C^1\) junction at either middle-window endpoint forces \(s=0\) and \(A\equiv1\) on J.** The global proof includes the exact all-angle rational triangle check \(\mathcal P(U_\varepsilon)-\mathcal P(U)=3\varepsilon/7>0\). 

This is a new necessary condition at the **global scalar maximizer**, not another candidate-neighborhood exclusion. **It does NOT exclude possible tilted facets with two genuine pinned corners**; such caps and arbitrary smooth wing exposure remain. No bound \(\mathcal P\le M/2\), improvement of the unrestricted upper bound or Gate 1 PASS is inferred. **Next:** determine whether pinned tilted extrema can be excluded *by the true spatial exposure balance*, and characterize the horizontal-facet case without importing \(\Psi\)'s different stationarity law.

**GLOBAL ENDPOINT AND EXPOSURE UPDATE (EP1–EP3; sharp VALUE still open):** [gate1-global-endpoint-complementarity.md](gate1-global-endpoint-complementarity.md) repairs FE's zero-face error by actual inward trimming and proves, at every height-one global score maximizer,
\[
e_R=(C_R)_+,\quad e_L=(C_L)_+,\qquad
C_R=(3q_+-q_-)/4,\quad C_L=(3q_--q_+)/4,\quad q_\pm=(A+n)(j_\pm).
\]
Horizontal erosion \(U\cap(U\mp\varepsilon e_x)\), admissible even with a point top, then proves exact cosine-weighted **limiting finite-exposure defects** \(\int\cos\theta\,d(\nu_R-\omega_R)=(-C_R)_+\), \(\int(-\cos\theta)\,d(\nu_L-\omega_L)=(-C_L)_+\), with \(\nu_Q\ge\omega_Q\). Here \(\omega\) is charged outer-wing curvature; \(\nu\) is a weak limit of finite middle-niche exposures, **not automatically the arclength of the actual positive full niche**. Every nonnegative-pressure quarter has exact limiting measure equality.

The exact [TF4](gate1-spatial-tilted-facet-pinning.md) map inserts a height-one point at the nearer J endpoint when the top is disjoint from J; it **strictly increases exterior reward without changing any charged niche**, so every maximizer's top meets J. A tilted canonical maximizer reaches height one at its higher endpoint. EP3 initially forced both pressures positive in the horizontal-middle case and the higher-side pressure positive in the tilted case. The October 10 LH1 exclusion below now removes the possible low-side nonpositive-pressure branch as well.

### October 10: positive pressures and the complete horizontal value theorem

[**LH1–LH3**](gate1-global-positive-pressure-and-wing-identity.md) prove that every canonical cap with lower middle-endpoint height at most one half has
\[
\mathcal P<31233/39200<4/5<M/2.
\]
Thus every canonical global maximizer has **both endpoint pressures and both end heights strictly positive**. EP gives exact limiting source equality on both quarters, \(\nu=\omega\). A finite-graph Green identity, with the moving-window boundary terms retained, then proves the stationary law
\[
\boxed{2\mathcal P=L_{\rm wing},\qquad\max_J n\le(e_R+e_L)/2.}
\]
Here \(L_{\rm wing}\) includes any horizontal top segment outside J and excludes vertical end faces. No identification of weak finite exposure with ordinary positive niche arclength is assumed.

[**CH1–CH7**](gate1-spatial-maximizer-curvature-and-horizontal-value.md) remove the nonpositive-height excess-curvature obstruction, transfer same-sign shadowing to the actual spatial maximizer, and prove that a horizontal maximizer of width \(W\ge2\) has top face exactly J. In that branch, **one globally unit-curvature quarter forces both**, by a spatial-window-valid visible-source flux argument. The general signed-roof identity and AF calibration then give the sharp value through
\[
W_H=\frac4{35}\sqrt{523+2\sqrt{701}}.
\]
For a tilted maximizer with \(W\le8/3\), CH7 proves unit curvature on the entire quarter without the central-facet atom, with the facet's exact derivative jump included.

[**HW1 — complete horizontal theorem**](gate1-horizontal-maximizer-sharp-value.md) now proves
\[
\boxed{A|_J\text{ horizontal at a canonical global maximizer}
\quad\Longrightarrow\quad\mathcal P\le M/2.}
\]
All horizontal widths are covered. [SW1](gate1-horizontal-short-width-exclusion.md) excludes \(W\le2\) by three actual angles. HW first excludes \(C=W/4\ge13/15\), then proves full one-turn feasibility in the remaining range. Exact kernel estimates and a seven-row rational certificate exclude \(8571/12500\le C\le4/5\), using only the previously recorded Gerver bound \(G\le22199/10000\). Two disjoint extra niche half-triangles at \(\pi/8,3\pi/8\) exclude \(4/5\le C\le13/15\). The overlap with CH is exact, so no horizontal width is omitted. The finite checker evaluates the displayed rational inequalities only; it is not a sampled-angle or numerical-search premise.

### October 10: the remaining tilted width and height domain

[**TS1/GAP1 and TW2**](gate1-tilted-width-exclusions.md) now prove the strict score bound \(\mathcal P<41/50<M/2\) for all canonical caps with \(W\le1001/500\), and for all canonical positive-pressure caps with \(16/5\le W<6\). The short theorem requires no endpoint law or curvature bound. The wide theorem uses only the already proved positive-pressure endpoint equations. Three actual niche angles, their genuine companion walls, and ordinary exterior deficit triangles supply the payment; the entire niche and its window clipping are retained.

The same note's **INT1–INT3** prove the exact intermediate bound. Put \(a=W/2=2C\), \(h=1-A(j_-)\), and \(k=\sqrt2-1\), after reflection. Then
\[
\mathcal P\le1-\frac{(a-\sqrt2)^2}{2}
-\frac{2a}{4a-h}(k+h/2)^2.
\]
The proof maximizes a globally concave two-support relaxation, including the mandatory tilted exterior deficit and all \(45^\circ\) window-clipping terms. Its critical point is proved interior and unclipped. Thus every remaining tilted canonical global maximizer obeys
\[
\boxed{\frac{1001}{2000}<C<\frac45,\qquad0<h<\frac{17}{50},}
\qquad
\boxed{(2C-\sqrt2)^2+\frac{8C}{8C-h}(k+h/2)^2\le\frac9{25}.}
\]

### October 10: no tilted maximizer with two unit-curvature wings

[**TU.1–TU.24**](gate1-tilted-unit-wing-exclusion.md) now excludes the entire tilted stationary branch under the two regular-wing bounds \(u,v\le1\). The ordered contacts and positive graph are deduced from those bounds. A separate no-ghost proof establishes the exact finite-source projection law through the low-side zero-height gap, and positivity of the limiting source measures upgrades the local graph flux bounds to equalities. The proof retains every possible ordering of the floor and window crossings; it imposes no candidate contact chart.

If T is the high-side top overhang, \(\epsilon=1-A(j_-)\), and \(z=n(j_+)\), the resulting contact-energy identity and bounds are
\[
6CT=\frac{(z-\epsilon)(2-\epsilon-z)}4+R_B-R_D,
\qquad R_D\ge0,\quad R_B\le2T/3,\quad z\le4T/3.
\]
Positive tilt forces T>0. The right side is at most \(4T/3\), contradicting \(6CT>3T\) for \(C>1/2\). Hence **every remaining above-reference global scalar maximizer must have a nonunit regular wing**. A hypothesis of this theorem is not a conclusion about all maximizers.

### October 10: the first-unit tilted branch is fully excluded

[**GF.1–GF.17**](gate1-tilted-first-wing-exclusion.md) removes the companion-unit hypothesis entirely. The [first-wing structural lemmas](gate1-tilted-first-wing-structure.md) and [joint finite-source audit](gate1-tilted-folded-source-occupations.md) give exact fractional source occupations, including arbitrary measurable ties and companion folds. The first companion-floor crossing must precede the first nonunit episode. Its displacement S may exceed the global niche-gap displacement T; the resulting energy correction `(S-T)((S+T)/2-3C)` is nonpositive. The remaining fold loss is bounded explicitly, producing `6CT<=97T/48<3T`. Thus **no remaining tilted maximizer can have first-wing curvature at most one**. CH7 now excludes all C<=2/3, without any unit premise on the other wing.

The [initial-floor energy test](gate1-tilted-initial-floor-energy.md) strengthens CH7. With d=3C and B=e_R-1+h, the two exact sufficient inequalities are `d^2+B^2<=5` and `d^2+B^2+B(1-h)-d*sqrt(h(2-h))<=4`. A short rational certificate proves them for `2/3<C<=18/25` and `3/100<=h<17/50`. GF excludes that entire strip.

The [full additional niche triangles](gate1-tilted-full-triangle-width-cut.md) improve the width ceiling to C<37/50. On this smaller domain, [positive-corner confinement](gate1-tilted-corner-confinement.md) proves a genuine connected one-turn survivor and the corresponding exact ordinary-area inequality. The [early first-excess theorem](gate1-tilted-first-excess-ends-early.md) further proves `u<=1` on `t>=11/15`, strictly before every positive endpoint tangency. It gives `n(C)<=CT/sqrt(1-C^2)` and `J_f<1/40` for the first-wing exterior leakage moment.

**Precise remaining obligation:** exclude or sharply bound a **tilted canonical global maximizer with first-wing curvature above one**, with `2/3<C<37/50`, `0<h<21/100`, and the exact INT width–height restriction above. IE8 and the first-wing theorem exclude the entire strip `h>=21/100` across all remaining widths. If `C<=18/25`, necessarily `h<3/100`. Both pressures and end faces are positive, the two strict corners are pinned to J, and `2P=L_wing` holds. The cap-minus-niche survivor is now proved to be a connected one-turn sofa. Use the endpoint-tail estimates and ordinary one-turn bound to close this last width/tilt region. This is the only remaining alternative for an above-reference scalar maximizer; it does **not** pass Gate 1 or activate Gate 2.

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
\tag{G1.2 — PROVED VIA G1C1–G1C2}
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
\tag{G1.5 — PROVED VIA G1C1–G1C2}
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

### G1.4 Closure criterion — met October 10, 2026

The [completed theorem and exact reference equality](gate1-sharp-full-turn-closure.md) meet the criterion below. The [audit](gate1-dependency-coverage-audit.md) records the complete quantifier domain, all boundary cases, and the explicit ordinary one-turn dependency.

**Gate 1 PASS if and only if** we have a complete independently auditable derivation \(|S|\le M\) for **every** genuine connected two-full-turn sofa, including all incoming heights, asymmetries, nonsmooth facets and positive/negative empty-fiber distinctions; or a proved sharp inequality on a rigorously area-value-dense class plus its limiting argument. Show exact Romik equality. The conditional statement “if G1.5 holds then Gate 1 passes” **does not count**.

**Gate 1 FAIL/BLOCKED:** If a proposed payment lemma is false, exhibit the exact counterexample and repair or change the one chosen charge while retaining G1.2; do not claim progress from a false universal claim. If no payment is proved, report specifically which outer-support increment cannot be charged to which full facet-sweep union. No return to convex-only upper bounds, candidate-local classes, tangency samples or global Jensen shortcuts already disproved.

**After—and ONLY after—Gate 1 PASS:** activate Gate 2, restoring independent partial terminal angles and outgoing *whole-body* strips in PLAN.1. Passing Gate 1 does not silently complete partial turns and is not the final unrestricted sofa proof.

## Gate 2 — original PARTIAL turns with their two outgoing strips

**Status: ACTIVE — UNPROVED; first unresolved gate after the completed Gate 1 theorem.** Extend the **same joint charge** to all independent \((\alpha,\gamma)\) in the original OS1 domain, including any subunit height; alternatively prove a valid no-loss reduction from *every* original partial motion to a class controlled by Gate 1.

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

## Current gate status (updated October 10, 2026)

| Gate | Status | Concrete missing step |
|---|---|---|
| 0 — original-motion bridge | **PASS** (written audit) | End-to-end audit in original-motion-global-bridge-gate0-audit.md; still subject to external review |
| 1 — coupled full-turn loss | **PASS** (written proof) | G1C1 proves the universal cap value; G1C2 gives the complete-turn sharp area and exact reference equality. Dependency and coverage audit accepted; external review and Lean verification outstanding. |
| 2 — complete original partial motions | **ACTIVE, UNPROVED** | No sharp charge for both independent outgoing strips together with visited partial niches; full-turn completion cannot be assumed |
| 3 — equality/uniqueness | **UNSTARTED** | Requires unrestricted area theorem first |

**Definition of meaningful progress:** a passed gate, a global theorem that removes an indispensable gap, or a correct falsification requiring a documented change in the global strategy. Everything else is supporting research.
