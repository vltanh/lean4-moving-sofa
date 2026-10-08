# Error absorption: a verified transfer, and the unproved global extension

This is a check of the method from PR #8 on a class where the ordinary-area comparison has already been proved. It does not broaden that class or assume a global maximizing body belongs to it. Its point is to show exactly how a **positive** enclosure error can coexist with, and be controlled in, a valid stability argument.

Use the reflected first-quarter protected perturbations of Notes 40–41 and [AF4](adaptive-functional-enclosure-counterexample.md), with their already verified feasible envelopes S and repaired envelopes S_c. All axis supports are unchanged, so the horizontal width is exactly the candidate width. The argument below is for that stated family; no singular or arbitrary-contact extension is silently added.

## 1. The geometric error is bounded by the ordinary deficit

Let u>=0 be the repair increment on its protected interval J, with u in H^1_0(J). The previously proved comparison supplies

\[
|S_c|\leq M_A,\qquad
|S_c|-|S|=2\int_J(1-q-u)u+\int_Ju'^2,
\]

where the class is small enough that 1-q-u>=0 on J. Thus, putting epsilon=M_A-|S|,

\[
\varepsilon\geq\int_Ju'^2\geq0.
\tag{EA.1}
\]

Independently, AF4 proves the exact ordinary-area error

\[
E=|S|-\widetilde{\mathcal Q}(h_K)=\int_J(u'^2-u^2)\geq0.
\]

The sign follows from the Dirichlet inequality because J has length less than pi. Combining the two identities gives

\[
\boxed{0\leq E\leq\varepsilon,\qquad
0\leq M_A-\widetilde{\mathcal Q}(h_K)=\varepsilon+E\leq2\varepsilon.}
\tag{EA.2}
\]

This is not the false inequality E<=0. It retains the positive fold error and pays for it using an actual feasible-area improvement.

## 2. A square-root hull estimate with an explicit constant

At the unchanged candidate width, the unique fixed-width auxiliary optimizer H_{a_*} is the centered candidate profile. Horizontal centering applies the same translation to K and K_*, because their axis supports agree. Equation (SD.6) therefore gives

\[
\|h_K-h_{K_*}\|_\infty^2
\leq\frac{4\pi}{7}\,[M_A-\widetilde{\mathcal Q}(h_K)].
\]

**Corollary EA1 (hull stability on the already verified repair family).**

\[
\boxed{d_H(K,K_*)\leq\sqrt{\frac{8\pi}{7}}\,\sqrt{M_A-|S|}.}
\tag{EA.3}
\]

**Proof.** Use (EA.2) and the equality between Euclidean Hausdorff distance of compact convex sets and uniform distance of their support functions. For completeness, a support bound h_K<=h_{K_*}+delta means K is contained in K_*+delta B_2 by their supporting half-planes; the reverse bound gives the other directed inclusion. Conversely either inclusion bounds the corresponding supports. This proves the equality used here. QED.

The estimate compares **hulls**, not the original nonconvex bodies. No claim is made that Hausdorff closeness of hulls alone controls holes or the actual sofa boundary. PR #8's separate nonconvex recovery step is relevant precisely because that distinction matters.

## 3. The global implication that is still missing

For an arbitrary feasible body the identity remains

\[
M_A-|S|=D-E,\qquad D=M_A-\widetilde{\mathcal Q}(h_K)\geq0.
\]

The implication E<=M_A-|S| used in (EA.2) came from a **proved repair on this family**. It cannot be inferred from functional stability, feasibility, or proximity of areas alone. For a hypothetical improving body, its right side would be negative while E must be nonnegative, so assuming that estimate globally would already assume a decisive part of optimality.

A genuinely global repair/enclosure estimate is still required. This check shows that the method is internally consistent on the counterexample family and provides a quantitative conclusion there without discarding its positive error. It does not locate unrestricted maximizers in that family.

The proof uses the pinned PR #8 audit only as methodological guidance; its constants and body class are those of the present branch. No CI, Lean/Lake compilation, numerical experiment, or computer algebra was used. The underlying research arguments remain self-reviewed rather than independently verified.
