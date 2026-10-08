# Audit of the uploaded partial-turn completion package

**Status.** The package supplies a useful geometric bridge, not a completed partial-turn or full-turn optimum. Its corner localization and signed-fiber accounting are valid with the stated small-deficit hypotheses. A companion note will sharpen its triangular completion allowance to a circular-corner allowance. Neither connectedness of the completed set nor the required sharp area margin is supplied by the package.

Baseline read from PR #3: `2dc739c569cea34c6d5275345a7f389ccb3593fb`. The supplied archive is `partial-turn-completion-package.zip`, SHA-256 `03dffee9b89a6cecb359b8b5c49d6284952f466bc34f7a3a21ceaa28636b1a81`. No author name was supplied; attribution here is to the user-provided package, not a claim that its PC arguments were originated in this continuation.

## 1. Provenance and fresh replay

The four original files have SHA-256 hashes:

- `docs/ambidextrous/partial-turn-completion.md`: `9153a783c44cbdec11fe9a5c651943af8658216c16b963db4b3afdd07f3a7706`.
- `computer-assisted/partial-turn-completion/README.md`: `5d2db8ff82cb218b2efe7dfc7afa109fdf323205765e8a9f7c12e84aaf364f36`.
- `computer-assisted/partial-turn-completion/check_partial_turn_completion.py`: `2f80073b434dafc42418556ac96f2408e00feb61a19d9dd8cfd0a37fd8ffa0d1`.
- `computer-assisted/partial-turn-completion/partial-turn-completion-checks.json`: `4677933ec5a83587d5aa1e84cc09be3061c3a025ec4cf52f0f51de8a4696e13e`.

The original checker was read before execution and replayed unchanged under an external **ten-second** limit. It finished in 2.35 seconds internally on Python 3.13.5. Its 126 rational angle checks passed, and all four floating-point rows exactly matched the supplied record in this runtime, apart from the recorded runtime/version fields. The uploaded source hash matches its author's record. This is reproduction, not independent verification of the numerical geometry. The original author record remains separate from the new replay.

## 2. Useful mathematics in PC0--PC4

For a conventional lower turn ending at alpha = pi/2 - epsilon, the actual body fits its incoming unit strip and its terminal unit strip. Their intersection is a parallelogram. If A is the intersection of their lower lines and D the intersection of their upper lines, then, after translation,

`A=(0,0), D=(tan(epsilon/2),1)`.

For every missing index t in [alpha,pi/2], the outer support is at most D dot n_t. Therefore any newly forbidden point above the actual hull floor lies in the fixed small corner region identified by PC2. The second inner-wall condition can be discarded for an upper bound on that loss. The same argument reflected vertically handles the other turn. This is an actual ordinary-area comparison, not a cap-functional calibration.

PC0 also supplies a valid transport of the same body along its connected component of feasible incoming strips, subject to the explicitly used positive-angle/high-area assumptions. This permits choosing a unit-span representative for the competitive problem without anisotropic scaling.

PC4 correctly retains signed fiber length when full completion creates empty fibers. With full niche roofs n_U,n_V and hull deficits d_U,d_V, put

`ell = 1-max(d_U,n_V)-max(d_V,n_U)`.

Then `integral ell = C-R` algebraically, even when ell is negative. The actual completed set instead has area `integral max(ell,0)`. These two quantities must not be identified. The valid consequence is

`area(S) <= C-R + tau(epsilon)+tau(epsilon')`

and also the weaker set-area bound with `area(E_full)` in place of `C-R`. Calling these two formulations equivalent is unnecessary; the latter follows from the former.

## 3. Qualifications required before using the package as a theorem

**Completion is not a connected-sofa construction.** Deleting the late forbidden sets may leave empty fibers or disconnected components. A theorem bounding connected full-turn sofas by M would not by itself bound the sum of the areas of all those components. The signed-fiber form avoids pretending a new competitor has been constructed, but requires a sharp bound on that signed expression for the wider class of partial-turn hulls.

**A positive error still needs a margin.** Even a proved `area(E_full)<=M` would yield only `area(S)<=M+tau(epsilon)+tau(epsilon')`. The missing negative margin is a genuine new obligation, not supplied by the localization.

**PC3 supplies inequalities, not exact alignment.** Its conclusion `r-1 <= c <= b` in the specified face case does not say `c=r-1`. The prose that locates the chord exactly at r-1 is stronger than the displayed proof. The face lemma is useful as a localization only.

**The numerical family is not certified.** Part B checks finitely many angles, nonempty fibers on a finite grid, and hull-vertex retention with tolerance 0.0002. Those checks do not establish continuous full or partial motions or exact hull identity. In particular its first row reports a negative completion loss, about -6.50e-7, although adding constraints cannot increase the exact area. The lower and full angle meshes are not nested; this alone allows that numerical sign error. The sampled trend does not prove an asymptotic family of non-completable bodies or a no-gap theorem. These conclusions require a separate analytic construction.

**PC6 needs its intended competitive/small-deficit scope.** Its literal statement for every unit-span partial-turn hull is false with the original triangular allowance. Take a disk of radius one half and choose both supplied turning magnitudes alpha=gamma=2 arctan(1/100). It fits every strip and hallway, so its completed set is still the disk, of area pi/4. With epsilon=pi/2-alpha, the sum of the two triangular allowances equals

`(99/101)^2 * (9999/10001) > 19/20`.

The elementary reference estimate Y<3/10 and arctan(Y)<Y gives M<83/50. Thus `M-2tau(epsilon)<71/100<pi/4`, contradicting that unqualified PC6. This low-area, large-deficit example does **not** refute the intended competitive version using TE1. It shows why that scope must be written explicitly. Nor does it refute a different sufficient margin using a sharper or actual completion loss.

## 4. Immediate improvement and the remaining frontier

The triangular allowance is not the exact area of the worst missing first-wall region. The union is a tangent-circle corner region, with area

`lambda(epsilon) = tan(epsilon/2) - epsilon/2 = epsilon^3/24 + O(epsilon^5)`.

A separate self-contained proof is supplied in the companion circular-corner note. This is asymptotically one third of PC's triangular allowance, which starts at epsilon^3/8. At the existing TE endpoint bound, the respective per-turn allowances are approximately 0.006008415 and 0.017543826. These decimals are illustrations; the proofs use the exact expressions.

The practical bridge is therefore sharper than the package states, but still requires a global full-turn sharp bound and an appropriate completion margin or component argument. No unrestricted closure is claimed. All new geometric arguments are pen and paper; numerical replay is supplementary. No CI, Lean/Lake compilation, dependency installation, manuscript build or long search was used.
