# A certified \(3/2\) upper bound for every **convex** ambidextrous sofa

**Date:** October 8, 2026. **Status:** A complete self-contained pen-and-paper geometric reduction plus a **finite exact rational certificate**, not independently refereed or Lean-verified. It improves the preceding moving-inner-corner program from **feasibility-only restrictions** to a quantitative **ordinary-area theorem on a large geometric class**. No global sharp theorem, assertion that arbitrary sofas are convex, or new above-Romik sofa is claimed.

**Main theorem CV1.** Every compact convex planar sofa that can pass through both left- and right-handed unit-width right-angle corridors, from the same incoming orientation and by arbitrary continuous motions (including partial turns, rotations with backtracking, and nonmonotone paths), has
\[
\boxed{|S|\le\frac{31}{20}=1.5<1.6449552184\ldots=M.}\tag{CV.1}
\]
In fact, every compact convex body satisfying the **common incoming unit strip plus just the two canonical opposite \(45^\circ\) hallway positions** already obeys CV.1. The last stronger statement needs neither continuous motion data nor terminal strip conditions. For the original sofa conclusion, the independently established *proper \(45^\circ\) reach for area \(>\sqrt2\)* from [GH](midpoint-bound-general-motions.md) supplies those two positions.

The proof works precisely with the user's suggested **outer supporting walls and their forced sharp inner corners**, then accounts for the safe side of *both attached inner-wall rays* via convex separation. It does not use the old \(G\le\Delta_U+\Delta_V\) inequality, any Romik contact chart, or convexity of the **outer hull of a nonconvex sofa**.

## 1. Opposite \(45^\circ\) corners turn convex safety into two support halfplanes

Use perpendicular, area-preserving coordinates
\[
U=(x+y)/\sqrt2,\qquad V=(-x+y)/\sqrt2,\qquad
y=(U+V)/\sqrt2.
\tag{CV.2}
\]
Let \(C\) be a compact **convex** sofa meeting the two actual \(45^\circ\) canonical hallway constraints. Translate its minimum U and V coordinates to zero and let its **actual** support widths in these two directions be
\[
P=\max_C U,\qquad Q=\max_C V.
\]
The two sharp corners of the lower and upper hallway frames, with *outer walls support-tightened to the actual body*, impose exactly
\[
\begin{aligned}
0\le U\le P,\qquad&0\le V\le Q,\\
U\ge P-1\quad&\text{or}\quad V\ge Q-1,\\
U\le1\quad&\text{or}\quad V\le1.
\end{aligned}\tag{CV.3}
\]
This is the earlier diagonal L-geometry [DU.1](diagonal-width-upper-bound.md), now used together with **convexity of the sofa itself** rather than convexity of its outer hull alone.

**Lemma CV2 (support-line separation).** Since \(C\) is convex, there exist \(\lambda,\mu\in[0,1]\), possibly different, such that *every point* \((U,V)\in C\) satisfies both
\[
\boxed{\begin{aligned}
\lambda U+(1-\lambda)V
&\ge\lambda(P-1)+(1-\lambda)(Q-1),\\
\mu U+(1-\mu)V&\le1.
\end{aligned}}\tag{CV.4}
\]

**Proof.** Translate the first inner forbidden quadrant to the open negative orthant:
\(\{(U-(P-1),V-(Q-1)):U<P-1,\ V<Q-1\}\). Its intersection with the compact convex image of C is empty by CV.3. A separating linear functional may be chosen in the nonnegative dual orthant, since the forbidden orthant extends arbitrarily far in both negative directions. Normalize its two nonnegative coefficients to sum to one. This gives the first line of CV.4. Apply the same elementary convex separation to the forbidden open northeast quadrant \(\{U>1,V>1\}\) to get the second line. The result also holds when either body just touches the sharp corner, because the forbidden quadrants are open. \(\square\)

The **incoming strip** \(0\le y\le1\) adds a diagonal band
\[
\boxed{z\le U+V\le z+\sqrt2}\tag{CV.5}
\]
for some \(z\), which may be unknown. It follows that C is contained in the intersection of a rectangle, two **corner-derived support halfplanes**, and one diagonal band. Every hull and motion parameter except the four scalars \((P,Q,\lambda,\mu)\) has now disappeared from this **upper-area relaxation**; the band translation will be maximized over exactly, not discretized.

## 2. An elementary **compact** parameter domain

We only need consider a hypothetical C with \(|C|>3/2\).

At a fixed U (or V), the incoming diagonal band intersects the line in length at most \(\sqrt2\). Thus Fubini gives
\[
|C|\le\sqrt2\min(P,Q).
\]
Since \(3/2>\sqrt2\), both actual widths satisfy \(P,Q>1\).

If both \(P,Q>2\), distributing the two safe-wall disjunctions in CV.3 leaves only the two **positively separated unit squares**
\[
[P-1,P]\times[0,1],\qquad[0,1]\times[Q-1,Q].
\]
The connected C must lie in one, contradicting its *actual* widths \(P,Q>2\). Therefore
\[
\min(P,Q)\le2.
\]
Furthermore, because \(P=w_C(U)\), \(Q=w_C(V)\), and \(\operatorname{width}_C(U+V)\le\sqrt2\),
\[
P\le Q+\sqrt2,\qquad Q\le P+\sqrt2.
\]
Hence
\[
\boxed{1<P,Q\le2+\sqrt2<4.}\tag{CV.6}
\]
This argument uses only the two \(45^\circ\) corners, connectedness, and the incoming strip. It does **not** import a full-turn width theorem, a positive-area regularity argument, or an arbitrary numerical cutoff.

Thus a contradiction to CV.1 must correspond to one point in the **fixed rational parameter box**
\[
\boxed{(P,Q,\lambda,\mu)\in[1,4]^2\times[0,1]^2.}\tag{CV.7}
\]

## 3. An exact enclosing polygon for every rational parameter box

Let a rational parameter box be
\[
\mathcal B=[P_0,P_1]\times[Q_0,Q_1]\times
[\lambda_0,\lambda_1]\times[\mu_0,\mu_1].
\]
Set
\[
\bar\lambda=\frac{\lambda_0+\lambda_1}{2},\quad
\delta_\lambda=\frac{\lambda_1-\lambda_0}{2},
\quad
\bar\mu=\frac{\mu_0+\mu_1}{2},\quad
\delta_\mu=\frac{\mu_1-\mu_0}{2},\quad R=\max(P_1,Q_1).
\]
For every \(C\) admitted by some parameters in this box, \(0\le U\le P_1\), \(0\le V\le Q_1\), and
\[
\boxed{\begin{aligned}
\bar\lambda U+(1-\bar\lambda)V
&\ge\bar\lambda(P_0-1)+(1-\bar\lambda)(Q_0-1)
-\delta_\lambda(|P_0-Q_0|+R),\\
\bar\mu U+(1-\bar\mu)V&\le1+\delta_\mu R.
\end{aligned}}\tag{CV.8}
\]
Indeed \(|U-V|\le R\); replacing the varying support weights by their midpoints costs at most \(\delta_\lambda R,\delta_\mu R\), while replacing the lower P,Q values by \(P_0,Q_0\) costs at most \(\delta_\lambda|P_0-Q_0|\). Both displayed inequalities are **valid outward relaxations** of CV.4. No assumed optimizer or floating-point support evaluation is needed.

Let \(\mathcal P_{\mathcal B}\) be the rational convex polygon obtained by clipping \([0,P_1]\times[0,Q_1]\) with these **two** rational halfplanes. Then \(C\subseteq\mathcal P_{\mathcal B}\).

Set
\[
d=\frac{283}{200}>\sqrt2
\quad(283^2=80089>80000=2\cdot200^2).
\]
For an arbitrary polygon \(\mathcal P\), define the **unrestricted strip-position maximum**
\[
\boxed{\Phi_d(\mathcal P)=
\max_{a\in\mathbb R}
|\mathcal P\cap\{a\le U+V\le a+d\}|.}
\tag{CV.9}
\]
Enlarging the true incoming strip band to the rational width \(d\) gives the exact upper bound
\[
\boxed{|C|\le\Phi_d(\mathcal P_{\mathcal B}).}\tag{CV.10}
\]

### Why \(\Phi_d\) is computable in finitely many rational operations

For a convex rational polygon, let \(z=U+V\) and let \(g(z)\) be the length of its vertical-in-U section at fixed z. The transformation \((U,V)\mapsto(U,z)\) has determinant one. Therefore
\[
\Phi_d(\mathcal P)=\max_a\int_a^{a+d}g(z)\,dz.
\]
The function \(g\) is **piecewise affine with rational breakpoints**, exactly the sums \(U_i+V_i\) of the polygon's vertices. (On an interval between vertex heights, the two cross-section endpoints traverse fixed polygon edges linearly.)

Consequently
\[
\frac{d}{da}\int_a^{a+d}g(z)\,dz=g(a+d)-g(a)
\]
is affine on every interval cut out by the finitely many breakpoints
\[
\{\,z_i,\ z_i-d\,\}.
\]
The maximum is thus at a breakpoint or at the unique interior zero of that affine derivative, if present; where the derivative vanishes identically the endpoints suffice. **All** these candidate band positions and all integrated areas are **rational**. The checker evaluates them **exactly**, so no angular or strip-position sampling enters the certificate. Lower-dimensional clipped polygons have zero area.

## 4. Complete exhaustive rational certificate

The stronger (3/2) bound supersedes the earlier (31/20) certificate; the geometric reduction and parameter domain are unchanged. The [self-contained exact checker](computer-assisted/check_convex_two_corner_area.py) subdivides the whole root box CV.7 by repeatedly bisecting the coordinate with the largest **normalized width**:
\[
\frac{P_1-P_0}{3},\
\frac{Q_1-Q_0}{3},\
\lambda_1-\lambda_0,\
\mu_1-\mu_0.
\]
At each box, it accepts the box if either its trivial band-area bound \(d\min(P_1,Q_1)\), its whole enclosing polygon area, or the **exact rational maximum** CV.9 is at most \(3/2\). Otherwise it bisects and covers the box by its two children. **Every accepted box is a sound upper-area enclosure for every parameter tuple inside it.**

The independent, executed standard-library Python Fraction replay gave:
\[
\boxed{
\begin{array}{l|r}
\text{Total visited parameter boxes}&100\,161\\
\text{Certified terminal boxes}&50\,079\\
\text{Maximum subdivision depth}&24\\
\text{Unresolved leaves}&0\\
\text{Largest computed accepted exact upper}&
3/2.
\end{array}}\tag{CV.11}
\]
There is no optimizer, no random search, no geometric interpolation without a proved error term, and no need for CI or Lean. A finite tree of rational area inequalities covers **every** real point of the root parameter domain. The code additionally uses the sound strip bound (d\min(\operatorname{width}_U\mathcal P,\operatorname{width}_V\mathcal P)) before the exact band maximization. It includes independent closed-form regression tests for a unit square, a \(1\times3\) rectangle, an isosceles right triangle, and a symmetric double-corner polygon to guard against missed band-position maxima.

With CV.6 and CV.10–CV.11, assuming \(|C|>3/2\) gives
\[
3/2<|C|\le\Phi_d(\mathcal P_{\mathcal B})\le3/2
\]
for the leaf containing its actual parameter tuple, a contradiction. This proves the **two-\(45^\circ\) finite-position convex-body theorem**.

Finally, if a genuinely ambidextrous **convex** sofa had area \(>3/2\), then its area would exceed \(\sqrt2\). The valid actual-motion wrong-way exclusion and terminal-strip reach argument in [GH Section 3](midpoint-bound-general-motions.md) forces both proper \(45^\circ\) hallway positions to have been visited, without assuming monotone or complete turns. The just-proved finite-position inequality then yields a contradiction. **This proves CV1.**

For the comparison with Romik, [Note 10](10-wrong-angle-exclusion.md) establishes \(M>8/5>3/2\) directly from the positive cubic root bounds; no numerical approximation to \(M\) is needed.

## 5. What this does and does not establish

**Established:** Every true convex ambidextrous sofa has area **strictly less** than Romik's existing feasible nonconvex candidate, with a comfortable rational gap \(M-3/2>1/20\). The result applies to *all original motion histories*, not just globally maximized convex shapes. It is an honest **ordinary-area** theorem from the same moving corner and outer-wall contact geometry proposed by the user.

**Not established:** The **convex hull of a nonconvex sofa need not itself avoid the forbidden inner quadrants**. Indeed Romik's actual corner lies strictly inside his convex hull at the \(45^\circ\) frame. Therefore CV1 cannot be applied to the convex hull of Romik or to a hypothetical larger sofa. No convexification, symmetrization, or patching argument is offered to turn the original unrestricted optimality problem into the convex case; doing so would falsely eliminate the reference. The original global sharp upper bound \(M\) remains open.

**Further mathematical target:** Extend the support-line separation used in CV2 to the **safe convex components** of the *carved*, nonconvex sofa, while paying the area of branches/concave niche material lost in each decomposition. Alternatively, derive a global weighted certificate from the continuum of corner trajectories that bounds the complete **nonconvex surviving area** rather than only the area of a single convex component. This is a concrete next proof problem in the user's intended **outer wall + moving corner first** framework, not a restatement of the old clipped-cap inequality.
