# Gate 1: exact global middle-chord reduction for the sharp spatial one-cap value

**Date:** October 9, 2026. **Status:** A new unconditional **global value-preserving/score-improving operation** on **every** downward convex one-turn cap. It applies to arbitrary non-symmetric, nonsmooth, multipeak, high-curvature bodies and full continuous two-ray inner-wall sweeps. It proves that the [SD.3 sharp one-cap scalar maximization](gate1-spatial-dual-height-width-compactness.md) can be restricted **without loss of supremum** to height-one caps whose convex upper roofs are **affine on the entire width-dependent central half** of their horizontal projection. It is **not** a sharp value theorem or an unrestricted moving-sofa optimality result. Gate 1 remains **ACTIVE, NOT PASSED**.

This is a global operation on arbitrary cap data, not a perturbation around Romik. It is specific to the spatial one-cap score and **must not be claimed area-improving for an actual two-handed sofa**.

## 1. A chord cut changes only the uncharged middle roof

Let U be any nonempty compact convex downward-closed cap contained in \(\mathbb R\times[0,1]\), with nondegenerate horizontal projection \(I=[l,r]\) and width \(W>0\). Its concave upper-roof function is \(A(x)\ge0\). Define
\[
j_-=l+W/4,\qquad j_+=r-W/4,\qquad J=[j_-,j_+].
\tag{MID.1}
\]
Both \(j_\pm\) belong to the *interior* of I, so \(A(j_\pm)>0\) when U has positive area; degenerate zero-area caps are harmless and can be excluded at a positive global maximizer. Put
\[
\ell(x)
=A(j_-)+\frac{A(j_+)-A(j_-)}{j_+-j_-}(x-j_-).
\tag{MID.2}
\]

**Lemma MID1 (global chord ordering).** Every concave \(A:I\to\mathbb R\) satisfies
\[
A(x)\ge\ell(x)\quad (x\in J),\qquad
A(x)\le\ell(x)\quad(x\in I\setminus J).
\tag{MID.3}
\]

**Proof.** The first assertion is exactly concavity above a chord. For \(x<j_-\), write \(j_-=(1-s)x+sj_+\) with \(0<s<1\). Concavity gives \(A(j_-)\ge(1-s)A(x)+sA(j_+)\); solve for \(A(x)\le\ell(x)\). The right exterior interval follows by exchanging the endpoints. In particular \(\ell(x)\ge A(x)\ge0\) outside J and \(\ell(x)\ge0\) inside J as a convex combination of nonnegative chord heights. \(\square\)

Define the actual compact convex **chord-clipped cap**
\[
\boxed{U^\flat=U\cap\{(x,y):y\le\ell(x)\}.}\tag{MID.4}
\]
It retains the same full baseline \(I\times\{0\}\), hence the same projection I and width W; it is downward closed and convex. Its upper roof is precisely
\[
\boxed{
A^\flat(x)=
\begin{cases}
A(x),&x\notin J,\\
\ell(x),&x\in J.
\end{cases}
}\tag{MID.5}
\]
Thus **all charged outer roof area** in the spatial score,
\(\int_{I\setminus J}A(x)dx\), is **identical** before and after chord clipping.

## 2. The *entire physical moving-wall niche* cannot grow

For every lower-turn angle \(0<t<L=\pi/2\) write
\[
u_t=(\cos t,\sin t),\quad v_t=(-\sin t,\cos t),\quad
q_{U,t}(x)=\min\left(
\frac{h_U(u_t)-1-x\cos t}{\sin t},
\frac{h_U(v_t)-1+x\sin t}{\cos t}
\right).
\tag{MID.6}
\]
The complete positive two-ray niche roof is
\(n_U(x)=\max(0,\sup_{0<t<L}q_{U,t}(x))\).
Because \(U^\flat\subseteq U\), the genuine convex **outer supports** satisfy \(h_{U^\flat}(n)\le h_U(n)\) for **all** directions n. Therefore both attached inner-ray heights weakly decrease for **every** t and x:
\[
q_{U^\flat,t}(x)\le q_{U,t}(x),\qquad
\boxed{n_{U^\flat}(x)\le n_U(x)\quad\text{for every }x.}
\tag{MID.7}
\]
This includes the physical corner path, arbitrary switches of the maximizing angle, and any number of disconnected angular superlevel components. We do **not** assume a stable contact order or smoothness.

For the width-dependent spatial score
\[
\mathcal P(U)=\int_{I\setminus J}A_U(x)\,dx-\int_Jn_U(x)\,dx
\]
the two exact facts MID.5 and MID.7 give
\[
\boxed{
\mathcal P(U^\flat)-\mathcal P(U)
=\int_J[n_U(x)-n_{U^\flat}(x)]dx\ge0.
}\tag{MID.8}
\]
No ambient niche is incorrectly subtracted from a two-handed hull here: \(\mathcal P\) is a **one-cap dual score**, not an ordinary physical sofa area, and its use as a global *upper relaxation* is justified separately by [SD1](gate1-spatial-dual-height-width-compactness.md).

## 3. Restore unit height without losing the score

The clipped cap may have maximal vertical coordinate \(H^\flat\in(0,1]\). Let
\[
\varepsilon=1-H^\flat\ge0,\qquad
\boxed{U^\sharp=U^\flat+[0,\varepsilon]e_y.}\tag{MID.9}
\]
The upper roof is \(A^\sharp=A^\flat+\varepsilon\); it is still **affine on J**. Both inner-wall supports gain precisely \(\varepsilon\sin t,\varepsilon\cos t\), so each full ray roof \(q_{U^\sharp,t}(x)=q_{U^\flat,t}(x)+\varepsilon\). Taking max with zero gives
\[
0\le n_{U^\sharp}(x)-n_{U^\flat}(x)\le\varepsilon.
\]
The exterior charged roof increases by \(\varepsilon|I\setminus J|=\varepsilon W/2\), while the middle charged niche increases by at most \(\varepsilon|J|=\varepsilon W/2\). Consequently
\[
\boxed{
\mathcal P(U^\sharp)\ge\mathcal P(U^\flat)\ge\mathcal P(U).
}\tag{MID.10}
\]
The transformed U-sharp is again a compact convex downward cap of **exact height one** and the **same width W**, and has one affine upper segment across all of J. The operation is explicit and does not invoke an optimizer, a curvature cap, a chosen ray witness, or a feasibility-preserving deformation of the *actual physical sofa*.

## 4. A necessary sharp-value reduction of the entire infinite-dimensional problem

Define the canonical subclass
\[
\mathcal C_{\rm chord}=
\{U:\ U\text{ is downward compact convex, has height 1, width }W>0,\ 
 A_U|_{[l+W/4,r-W/4]}\text{ is affine}\}.
\tag{MID.11}
\]

**Theorem MID2 (exact supremum reduction).**
\[
\boxed{
\sup_{\text{all downward convex height}\le1\text{ caps }U}\mathcal P(U)
=
\sup_{U\in\mathcal C_{\rm chord}}\mathcal P(U).
}\tag{MID.12}
\]
Furthermore, because [SD3](gate1-spatial-dual-height-width-compactness.md) establishes attainment of the original scalar supremum in the range \(8/5<W<6\), the supremum on \(\mathcal C_{\rm chord}\) is **also attained**. In particular, **at least one global maximizer** of the spatial score has an **entire affine middle-half outer roof**.

**Proof.** The right-hand supremum is bounded by the left because the canonical subclass is contained in the original. Conversely MID.10 explicitly assigns to every cap of positive width a member \(U^\sharp\in\mathcal C_{\rm chord}\) with at least the same score; the width-zero case contributes zero and cannot improve the positive reference score. Taking suprema proves equality. Apply the construction to an attained global cap optimizer from SD3; its resulting canonical cap is still a global maximizer, proving attainment. \(\square\)

**Geometric interpretation.** The central upper roof of the cap is not rewarded anywhere in the spatial objective; reducing that roof without altering either exterior wing can only lower the *complete* moving-inner-ray niche. Convexity allows exactly one **maximal** reduction: replace the entire uncharged central curved roof by its supporting-endpoint chord. The candidate Romik cap already has its middle-half roof equal to its horizontal top face, so the transformation fixes the exact equality witness. The global competitor may have a **tilted** central facet and a height-one maximum on an exterior wing. One **cannot** assert the facet is horizontal or coincides with the top face, nor that it creates a feasible two-handed sofa; neither claim follows from MID2.

## 5. What actually remains for Gate 1

The stronger universal inequality [SD.3](gate1-spatial-dual-height-width-compactness.md),
\[
\boxed{\mathcal P(U)\stackrel{?}{\le}M/2,}
\]
is still **unproved**. MID2 proves that it suffices to establish it for caps with a *single straight entire central upper facet*; the left and right outer flanks remain arbitrary concave curves, and the niche remains the supremum over the full angular continuum. Arbitrary high curvature, contact switching and opposite-end geometry are **not** excluded by the reduction.

This is an indispensable **global maximizer-domain** simplification for the exact Gate 1 active value theorem, not another near-Romik shape-class upper bound. It should be used as a preparatory lemma for **first-variation/exposure balance on the two charged exterior wings**. Without a global sharp value inequality, Gate 1 does not pass and the unrestricted upper bound does not improve.

**No CI, Lean/Lake, numerical optimizer as proof, or global sharp area claim.** All inequalities above follow from concavity, support monotonicity and the exact extrusion formula.
