# \(P_J\) sharp-value research handoff (no Lean formalization)

**Primary question.** Can the exact ordinary-area enclosure

\[
|S|\le P_J(U)+P_J(V)
\]

from [SPB](spatial-half-partition-bound.md) be sharpened into
\(P_J(U)\le M/2\) on all cap pairs arising from competitive complete
two-turn sofas, or on some proved larger cap class? The stronger
**all-caps** inequality has neither been proved nor refuted here.
Its truth must be tested, not assumed.

**Historical correction.** The false premise is *global Minkowski
concavity* CF5 of \(P_J\), not SPB's ordinary-area upper enclosure.
[CN](candidate-functional-concavity-counterexample.md) gives an
exact counterexample to concavity, including positive top-face caps.
Therefore **do not** restart the argument
"global concavity + reference stationarity implies sharp value."
The existence of a strict local Hessian does not restore that
global concavity premise.

## New P_J results on this branch

1. [PJ-CUT](spatial-half-partition-reference-cut-certificate.md):
   use TC's paired reference circular-tail losses to prove
   \(P_J(U)\le M/2\) for *all* allowed inward convex top-normal
   cuts, with an explicit nonnegative exterior-roof remainder.
   This is a corollary of the earlier TC result, made into a
   sharp spatial-functional statement.
2. [PJ-TN](spatial-half-partition-two-sided-top-normal.md):
   **new signed-support extension**. A cap need not contain or
   be contained in the reference. If its upper support agrees
   exactly with the reference outside an angular top-normal
   window and the cap lies in the same unit rectangle, the
   exterior roof gain at \(b+d\) is bounded by the niche gain
   at \(b-d\), with a reflected counterpart. Reference
   unaffected directions pay the rest. The result includes
   sign-changing top-normal support perturbations; it does
   **not** admit arbitrary Hausdorff-close caps.
3. [PJ-MID](spatial-half-partition-middle-arc-variation.md):
   the exact quadratic change for a smooth compactly supported
   source variation on one middle curved reference arc is
   \(\varepsilon^2[\tfrac12\int\phi^2-\int\phi'^2]\).
   The calculation **must** count the moving two-wall corner.
   Omitting it yields a false nonzero first variation.
4. [PJ-COUP](spatial-half-partition-coupled-middle-variation.md):
   for simultaneous smooth perturbations \((\phi,\psi)\)
   of both middle arcs, the exact branch-stable quadratic
   form is

   \[
   Q(\phi,\psi)=\tfrac12\int(\phi^2+\psi^2)
   -\int(\phi'^2+\psi'^2+\phi\psi').
   \]

   The signed cross term is essential, but Dirichlet
   coercivity gives \(Q\le-\frac58
   \int(\phi'^2+\psi'^2)\). This is local
   strict stability **only on the reference contact chart**.

The four analytic notes are self-reviewed mathematical arguments,
not independently refereed or Lean-kernel checked. Their exact
claims must keep their listed contact, support, and domain
hypotheses; none is an unrestricted sharp optimum theorem.

## Bounded diagnostic, not a certificate

[check_pj_middle_diagnostic.py](computer-assisted/check_pj_middle_diagnostic.py)
computes the perturbed reference exterior roofs and full
turning-niche approximations on a deterministic angle/x-grid,
and compares observed changes with the exact quadratic form
for three choices of middle-support perturbation (one arc,
both signs, and opposite signs). The short local run of the
corresponding script passed all six residual thresholds;
largest observed absolute residual was under \(4\times10^{-7}\).
This **only** checks a discretized diagnostic: finite-angle
sampling underestimates the niche and does not prove a
continuum inequality. No byte-identity claim about the committed
file's execution, numerical upper-bound certificate, or CI run
is made.


## October 8 correction: the zero-slack class was already covered for value

[PJ-ZS1](spatial-half-partition-zero-slack-admission.md) isolates
two explicit sufficient support barriers and a centered top-face
condition that imply \(n_U=0\) outside \(J\) and \(A_U=1\) on \(J\).
By the already proved **algebraic identity** SPB.5,
\(P_J(U)=\Psi(U)\), and hence the written weighted-cap theorem
WV2 (subject to its independent review) gives
\(P_J(U)\le M/2\) for this class, even without curvature or
contact regularity.

This is a significant **priority correction**:
the small, curvature-safe middle-arc variations covered by PJ-MID
and PJ-COUP retain these zero-slack features, so their *sharp value*
was not a new missing case. Their second-variation formulas give
quantitative local stability, but cannot replace a theorem
controlling **top-face displacement and positive niche leakage**.

[PJ-ADM](spatial-half-partition-middle-arc-explicit-admissibility.md)
provides a conservative, exact curvature safety range
\(|\varepsilon|\le1/2000\) for the explicit compact
sin-fourth-power bumps. This is not by itself a global contact
visibility proof. The untouched reference arcs include
**zero-curvature portions**; do not upgrade global nonnegative
curvature to a strict lower bound.

The new research target should therefore be the precise
nonnegative error
\[
R(U)=\int_J(1-A_U)+\int_{I\setminus J}n_U,
\]
especially for positive opposite-end faces where the
top-face endpoints can jump even as support functions converge.
One must pay \(R(U)\) using a proved sharp weighted deficit
or exploit *coupled* cap-pair compatibility and SPB's slack.
No theorem in the current notes establishes that payment
universally. The exact global sharp value and the
partial-motion bridge remain open.

## Exact full-turn gap ledger (the proof still missing)

For the two downward caps \(U,V\) of an **actual connected
complete-turn body**, with nonempty canonical-envelope fibers,
let

\[
\begin{aligned}
\Delta_U&=M/2-\Psi(U)\ge0,\quad
\Delta_V=M/2-\Psi(V)\ge0,\\
R_U&=P_J(U)-\Psi(U)
=\int_J(1-A_U)+\int_{I\setminus J}n_U\ge0,\\
R_V&=P_J(V)-\Psi(V)\ge0,\\
\Lambda&=P_J(U)+P_J(V)-|E|\ge0,
\end{aligned}
\]

where \(\Lambda\) is **exactly** the four positive-part
spatial-partition terms of SPB.4, and
\(S\subseteq E\) is the canonical full-turn envelope.
Then pure algebra gives

\[
\boxed{M-|E|=\Delta_U+\Delta_V+\Lambda-R_U-R_V.}
\tag{PJ-LEDGER.1}
\]

Thus the sufficient ordinary-area inequality for
complete-turn optimality is

\[
\boxed{R_U+R_V\le\Delta_U+\Delta_V+\Lambda.}
\tag{PJ-LEDGER.2}
\]

This criterion is *equivalent* to the desired
\(|E|\le M\) for the indicated actual full-turn data, not a
newly proved global estimate. Using only WV2
(\(\Delta_U,\Delta_V\ge0\)) is insufficient because
the two \(R\) terms may be positive. The stronger
separate-cap inequality \(R_U\le\Delta_U\) for every
admissible cap would suffice, but may be more than needed;
the nonnegative pairwise slack \(\Lambda\) can pay a
scalar violation. Crucially, this exact accounting retains
the spatial clipping interaction instead of silently
dropping it.

Any honest claim of unrestricted sharp optimality must
also supply a **separate partial-turn argument**; this
ledger uses complete full turning niches.

## Exact remaining gates for the sharp-value strategy

**A. Audit the new local identities independently.**
In particular verify the active reference contact chart used
by PJ-MID/PJ-COUP at all interior angles, continuity at the
two switches, the correct orientation of each niche branch,
and the companion-wall clearance used by PJ-TN. A passing
floating-point diagnostic is not a proof of branch admission.

**B. Extend local stability beyond its present separated modes.**
The current theorems cover exact top-normal support agreement
and independent compactly supported smooth middle-arc
deformations **separately**. A generic near-reference cap
simultaneously changes these supports, moves the top-face
and width, and can shift contact-switch angles. Prove an
ordinary-area deficit that controls all cross corrections;
do not add the existing isolated deficits without a
justified superposition theorem.

**C. Falsify or establish the scalar P_J value on far caps.**
Optimize the true full continuous-angle niche, not a
sampled under-approximation, on structured asymmetric caps.
For a claimed counterexample supply certified **upper**
niche enclosures plus exact exterior-roof area.
For a claimed inequality supply a whole-domain upper
certificate or a complete analytic argument. Fixed-width
concavity was *not* proved by the bounded exploratory screens;
lack of a sampled violation is not evidence of a global theorem.

**D. If scalar sharpness fails, switch to a coupled comparison.**
SPB's actual area bound remains correct on its stated
actual-connected-full-turn domain even if \(P_J\le M/2\)
fails for an individual cap. A coupled cap-pair deficit
could exploit compatibility and retain the known nonnegative
spatial-partition slack SPB.4. It must not silently replace
visited partial-turn niches by full niches.

**E. Keep the final unrestricted motion bridge separate.**
A sharp comparison for complete turns alone does not prove
the same for arbitrary partial motions. No area-free partial
completion is assumed.

## Priority

Next mathematical work: **contact-switch/top-face local deficit
including interaction with the two smooth arc perturbations**,
in parallel with a deliberately bounded adversarial search
for an all-caps scalar counterexample. Defer uniqueness,
Lean formalization, and further optimization of the unrelated
numerical target until the value linkage is validated.

This file records the current written research boundary and
does not claim an externally reviewed solution.
