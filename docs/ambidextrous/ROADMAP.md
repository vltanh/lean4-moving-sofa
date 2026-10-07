# Active roadmap: sharp full-turn area and the audited completion margin

**Neither optimality frontier is closed.** The uploaded partial-turn completion package is useful and has been integrated with a stronger circular-corner estimate. It gives a quantitative relation between partial and full signed fibers, not a proof that the same body completes or that a sharp area margin is automatic. The main unresolved issue remains a universal ordinary-area comparison. Uniqueness is deferred.

Read [HANDOFF.md](HANDOFF.md), [partial-turn-package-audit.md](partial-turn-package-audit.md), and [circular-corner-completion-bound.md](circular-corner-completion-bound.md). All new statements are written and self-reviewed, not independently refereed or kernel-verified.

## 1. Goal and execution policy

The reference value is

$$M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.$$

The full-turn target is |S|<=M for every connected feasible body with both complete conventional quarter turns. The earlier RR/PD/PS reduction preserves its supremum inside the canonically saturated positive opposite-end-face class, which need not attain its supremum. That class has no uniform strict gap below M.

The latest user instruction authorizes incorporating the new partial-turn package if it helps bridge to full turns. Keep the work tied to this quantitative bridge rather than launch a separate broad partial-turn campaign.

Prefer hand proofs. Short diagnostic invocations are limited to at most 30 seconds, preferably five/ten seconds; no unbounded refinement or optimizer campaign. Commit substantive positive and negative findings with `[skip ci]` under `docs/ambidextrous/`. **No CI, Lean/Lake compilation, dependency installation or manuscript build.** Preserve concurrent edits and keep PR #3 draft while the global value is unproved.

## 2. What the new bridge actually proves

For a conventional lower exit alpha=pi/2-epsilon, the body lies in two supporting unit strips. Their lower and upper intersections are A and D. After translating A to zero,

$$D=(k,1),\qquad k=\tan(\varepsilon/2).$$

The new theorem CC1 identifies the worst first-wall missing region as the part of the tangent triangle outside the unit disk centered at D. Its exact area is

$$\boxed{\lambda(\varepsilon)=k-\arctan k
=\tan(\varepsilon/2)-\varepsilon/2.}$$

The supplied PC triangle allowance was tau=k^2 sin(epsilon)/2. Their difference is (epsilon-sin(epsilon))/2. Thus the new leading cubic coefficient is 1/24 rather than 1/8. This is the exact area of the stated relaxation, not a claim that an actual feasible body fills it.

Let ell_vis be the nonnegative fiber length of the actual visited envelope, and ell the possibly negative signed full-turn length. Then

$$\ell_{vis}=\ell+\xi_-+\xi_+,$$
$$\Xi:=\int(\xi_-+\xi_+)\le\lambda(\varepsilon)+\lambda(\varepsilon').$$

CC2 gives

$$|S|\le\int\ell+\Xi
\le\int\ell+\lambda(\varepsilon)+\lambda(\varepsilon').$$

With Z=integral(-ell)_+, the actual completed set has area integral ell+Z, and its area loss from the visited envelope is exactly Xi-Z. This distinguishes full signed area, ordinary completed area and actual lost material.

The existing TE bound gives k<=21/79 in the competitive regime, hence an illustrative per-turn allowance about 0.006008415 rather than the old 0.017543826. The geometric theorem does not use TE; only this numerical range does.

## 3. The package does not supply the required closure step

A connected full-turn theorem alone would at best give an upper bound M on a **connected** completed competitor. The completed set here may be disconnected. Bounding its separate components does not bound their total area by M. Even if its total area were bounded by M, adding a positive completion allowance would not prove |S|<=M.

A sufficient signed-margin theorem is

$$\int_I\ell\le M-\lambda(\varepsilon)-\lambda(\varepsilon'),$$

on the intended actual competitive partial-turn hulls. The weaker exact target is integral ell<=M-Xi. Neither is proved. The uniform-lambda target is stronger than needed and must itself be tested; it is not a corollary of full-turn optimality.

The original PC6's literal all-hulls/all-angles statement with tau is false on a radius-one-half disk with very small supplied turns. This does not refute its intended competitive-angle restriction, but that restriction must be explicit. Its numerical near-reference family is not a proved asymptotic family: finite vertex retention and sampled nonempty fibers do not certify continuous motions.

[IC1](exact-in-place-completion-obstruction.md) supplies an independent rigorous example with small deficit: the triangle with vertices (0,0), (1/10,1), (-1,20/99) has lower angle pi/2-2 arctan(1/10) and a full upper turn, but a missing lower angle excludes positive area. Its area is only 101/198. It establishes nonzero in-place loss, not a competitive obstruction or impossibility of a different initial orientation.

## 4. Full-turn sharpness remains the central missing inequality

For actual full-turn caps U,V with nonempty fibers,

$$|E|=\Psi(U)+\Psi(V)+G,$$
$$\Delta(U)+\Delta(V)-G=M-|E|,\qquad \Delta(U)=M/2-\Psi(U).$$

Thus G<=Delta(U)+Delta(V) is exactly the desired full-turn optimum, not an already plausible auxiliary lemma that can be inserted without proof. WV2 bounds the individual signed objectives in its written chain, but does not pay G.

AS supplies the direct stronger relaxation

$$|E|\le C(U,V)=W-\int\max(d_U+d_V,n_U+n_V).$$

Its sharp global bound C<=M remains unproved. The exact switching remainder R obeys

$$C-|E|=R\ge0$$

only when full fibers are nonempty. On a partial hull, the correct relation is C-|E_full|=R-Z. The signed identity integral ell=C-R is always the useful algebraic form. Do not silently transplant a bound proved only for actual full-turn hulls to a partial hull with empty full fibers.

The useful new direction is a sharp comparison that retains endpoint-strip information and supplies the completion margin; the circular bound tells exactly how small that allowance can be taken. It does not identify or prove the needed global comparison.

## 5. Prior approaches and constraints remain in force

**Background route.** TC/MT/ME/CT/CB give proved clipping budgets on explicit admitted classes, including rough tail changes of regular backgrounds. General middle regularity, half-height geometry and common output-face compatibility are not known for arbitrary competitors. CGA gives a genuine low-area saturated full-turn counterexample to unconditional inclusion-based common-face backgrounds. NM gives near-reference half-height rectangle failures. These hypotheses cannot be obtained merely from proximity or a threshold below M.

**Hull symmetry route.** HS proves an exact positive convex-hull reflection energy, not a nonnegative surviving-area gain. The changed forbidden area still needs to be paid. Symmetrized envelopes can lose unit vertical span; the known RS2 theorem has an actual unit-span premise. Near-reference examples rule out a uniform retained fraction of hull gain and a linear area penalty in missing vertical span. AN refutes a universal determinant-one affine normalizer. A symmetry route must prove its missing ordinary-area and normalization statements.

**Existing cases.** FAS and RS2 retain their aligned-face and specified symmetry bounds. RR/PD/PS preserve the full-turn supremum but do not give a uniform strict gap or an attained maximizer in their positive-face subclass. AM/TE are scoped exact certificates, not a complete global covering. The newer CC/IC hand proofs do not depend on the long WV chain, Gerver's upper bound or those certificates.

Keep RA, MCA, AF4, GR1, AX1/SAT1, SAC2, SC3, TR1, AO1, FF and HC as negative controls. Repair, averaging, saturation, reference proximity and support-energy gain are not substitutes for actual-area enclosure.

## 6. Numerical and exact checks

The original uploaded checker reproduced unchanged in 2.35 seconds under a ten-second cap. Its first apparent completion loss is negative, illustrating non-nested mesh bias. The retained corrected replay adds samples **only in the missing interval**, keeps the visited grid unchanged, and checks the exact signed-fiber identities numerically. It ran in 2.90 seconds; all four approximate losses are nonnegative and below lambda. These remain diagnostics, not geometric certificates.

The new standard-library exact checker ran under five seconds in about 0.155 seconds. It checks the triangle polynomial coefficientwise and rational depth, tangent, cone and signed-fiber identities. The execution record and committed source hashes agree. The archive is retained unchanged with full provenance in the reproduction bundle; the committed wrapper reconstructs both original and modified runs from that explicit input.

## 7. Next-session rule

Read the package audit and CC before using the new bridge. Do not interpret a cubic allowance as paid area loss or claim the package closes partial turns. Continue with a specific sharp ordinary-area comparison or a valid component/margin theorem that addresses the remaining quantifiers. Do not re-maximize an already calibrated detached functional, or launch a long search for a fixed gap in the entire opposite-face class. Independent review and both global optimality conclusions remain unfinished.
