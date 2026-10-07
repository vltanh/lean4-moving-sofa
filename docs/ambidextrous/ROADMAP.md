# Active roadmap: remaining global comparisons and testable alternatives

**The unrestricted full-turn and partial-turn problems are both still open.** CB constructs a regular tail background only under explicit input and face-compatibility tests. SPB supplies a direct ordinary-area enclosure but not its sharp maximum. FS supplies finite sufficient criteria for a safe strip bridge but does not prove all competitive partial-turn bodies meet them. Unrestricted uniqueness remains deferred.

Read [HANDOFF.md](HANDOFF.md), [constructed-background-review.md](constructed-background-review.md), and [spatial-half-partition-bound.md](spatial-half-partition-bound.md). All results are written and self-reviewed; the historical proof chain has not been independently refereed or kernel-verified.

## 1. Acceptance criterion and execution policy

Prove |S|<=M for one attained unrestricted maximizer, where

$$M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.$$

Do not require unrestricted equality classification first. Prefer hand proofs. Computers may reject a proposed step or test an attack direction in brief runs: maximum 30 seconds per invocation, preferably external five/ten-second limits. No long search or iterative refinement campaign without a new instruction. **No CI, Lean/Lake compilation, dependency installation or manuscript build.** Commit substantive positive and negative findings with `[skip ci]`, under docs/ambidextrous, preserving concurrent work.

## 2. Constructive background route: what is no longer merely assumed

[CB](complementary-tail-background.md) constructs a background B from U by taking a projective lower convex envelope with curvature ceiling one half in two top-normal windows. The input still needs:

- a regular unit-curvature middle and differentiable outer joins;
- a half-height rectangle and full niche height at most one half;
- domination by the explicitly written half-curvature arc matching each outer-end value and derivative.

The construction yields nonnegative repair e=h_B-h_U and

$$e(2\rho_B-1)=0.$$

It therefore pays the CT tail comparison without separately requiring rho_B>=1/2 everywhere. The smooth-fit barrier is what prevents new middle atoms. A short-window bound derives the contact signs, tail separation and half-height niche of the output. The one-cap result is

$$\Psi(B)-\Psi(U)\ge\int_{a_B}^{b_B}(1-A_U)dx.$$

Two such backgrounds with matching face intervals give |E|<=M through the existing SR/AF comparison. **Matching is not automatic.** Neither regularity of an arbitrary middle nor the half-height geometry or smooth-fit barrier is proved for general competitors. An unrestricted proof through this route must resolve those genuine admission conditions, not simply repeat the convex-envelope construction.

The earlier MT/ME and CT theorems remain available on their stated domains. MT/ME retain a quantitative middle deficit and allow signed rough tails with reference collars. CT permits more general inward changes with its lower tail-density condition. HC shows why that condition cannot be removed for arbitrary unrelated backgrounds. CB replaces it only through its constructed complementarity.

## 3. Direct spatial alternative: no missing area linkage, but an open maximum

[SPB1](spatial-half-partition-bound.md) partitions I=[l,r] into its middle half J and exterior quarters. For the actual upper/reflected-lower caps and their actually visited niche roofs, define

$$\mathcal P_J(U)=\int_{I\setminus J}A_U-\int_J n_U.$$

Discard outer constraints on J and niche constraints outside J. For the actual nonempty-fiber envelope,

$$|S|\le|E|\le\mathcal P_J(U)+\mathcal P_J(V).$$

The complete difference is the explicit sum of nonnegative fiber terms in SPB.4. The bound is exact on the reference. This is an already proved ordinary-area comparison, not an auxiliary functional whose geometric linkage is postponed.

The sharp scalar bound P_J(U)<=M/2 is **unproved**. With full niches,

$$\mathcal P_J(U)=\Psi(U)+\int_J(1-A_U)+\int_{I\setminus J}n_U,$$

so WV2 does not establish it. A universal scalar bound on relevant caps, or a coupled bound using pair compatibility, would directly close full-turn optimality. That is a possible alternative to background admission, not an additional completed result.

The bounded prescribed tests and six-iteration discovery run did not establish a maximum. The reference discretization already has a small positive bias, and no sampled excess is a rigorous counterexample. Do not run an indefinite optimizer or claim the cap problem is solved because no violation appeared.

## 4. Partial turns: finite safe-bridge admission

[FS](finite-strip-bridge-criterion.md) gives a finite exact test for the full SI bridge. Two width bounds A,B<=1 at normals separated by delta have a safe intervening sine-interpolation envelope if, writing c=cos(delta), s=sin(delta)>0,

$$B\le Ac\quad\text{or}\quad A\le Bc\quad\text{or}\quad A^2+B^2-2cAB\le s^2.$$

A finite chain of such tests supplies the continuum safe-strip hypothesis. In particular one additional strip suffices if

$$w((\alpha+\pi-\gamma)/2)\le\cos((\pi-\alpha-\gamma)/2).$$

These conditions produce full turns for the same body with no area change. They are not known for every competitor. Failure of FS is not proof of an unsafe bridge, and refinement alone is not guaranteed to certify every actually safe bridge. The unsafe-width-bump configurations remain an unresolved geometric/area class.

SPB applies directly to partial bodies only with their visited niches. Substituting full niches is an unjustified strengthening unless completion has been proved. The terminal-strip inequalities couple the two hull caps and must be retained by any direct partial-turn optimization.

## 5. A feasible actual-body variation, and why it does not close either frontier

[PV](actual-maximizer-parallel-volume.md) proves that every diameter-one convex template C gives a feasible deformation `(S+tC)/(1+t)` preserving the original angular intervals, including partial turns. At an attained actual maximum,

$$|S+tC|\le(1+t)^2|S|.$$

The disk case and compactly supported deformations imply finite distributional perimeter with P(S)<=4|S|. This does not imply hull curvature regularity or optimality from the converse inequality.

[RT](convex-template-rounding-obstruction.md) proves all these classical first variations are strictly negative at the reference, uniformly in C, and remain negative on sufficiently small prescribed asymmetric tip cuts. Those cuts are suboptimal. Thus the entire family does not provide an automatic local improvement in the remaining near-reference configurations. Other selective deformations are not ruled out; neither a uniform finite step size nor all larger steps are classified.

## 6. Global domain reductions retained

RR/PD/PS show that the full-turn supremum equals the supremum over saturated positive opposite-end faces. The subclass can approximate the reference and need not attain its supremum. There is no fixed positive gap below M over the whole class. A proof only about an attained maximum inside that nonclosed subclass is insufficient.

FAS proves the full-turn aligned positive-face class; RS proves the reflection-symmetric incoming class; SCG/CSF give further retained-point sufficient tests. No unrestricted symmetric-maximizer theorem is available. AW-W/SW/AL are analytic width restrictions, while AM/TE are earlier restricted computer certificates rather than a full sharp covering.

WV2 supplies the signed one-turn value in its written dependency chain. Its source-flux and regularity arguments remain independent-review points; it is not permission to assume weighted maximality for a two-turn cap. The newer tail comparisons invoke SR/AF only on admitted regular backgrounds.

The general full-turn identity remains

$$|E|=\Psi(U)+\Psi(V)+G,\quad G\ge0.$$

CB/CT/MT pay G on their domains. SPB avoids this particular unpaid term by a different proved relaxation, whose sharp bound must still be established. Neither route currently covers arbitrary opposite-face bodies.

## 7. Failure controls and checks

Retain RA, MCA, AF4, GR1, AX1/SAT1, SAC2, SC3, TR1, AO1, FF and HC. Averaging actual bodies or caps, saturation, face filling and curvature repair did not automatically preserve area upper bounds. The old occupancy LP has structural fractional barriers. A finite grid is not a certified neighborhood or a proof of continuous motion.

The latest exact checker ran under five seconds in about 0.0216 seconds internally and matches its committed Git blob. It checks algebra and finite instances, not continuum admission. All exploratory runs were short. Two regular-cap pair samples had negative fibers and must not be described as feasible sofas. The new partition run ended at its fixed six-iteration limit and did not establish convergence or any global upper bound.

## 8. Next-session discipline

Choose one precise missing implication: CB admission or output-face compatibility; a sharp SPB bound on the actual admissible domain; or a partial-turn completion/area theorem retaining its endpoint constraints. Review the relevant written proof before using it. Do not introduce a new detached calibration or silently replace any hypothesis with reference proximity.

Both global problems and independent verification remain unfinished. Keep scripts bounded, records honest and commits substantive. PR #3 remains open and draft until the unrestricted ordinary-area upper bound is actually proved.
