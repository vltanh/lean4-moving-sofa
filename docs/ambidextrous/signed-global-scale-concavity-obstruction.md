# Global signed-objective Minkowski concavity fails even at fixed turn angles

**Status (2026-10-08):** Exact mathematical falsification of the next proposed global Jensen step for the joint signed-fiber program [SJ1](signed-joint-convex-domain-global-value.md), [OS1](original-motion-signed-convex-domain.md). In contrast to [TA1](terminal-angle-concavity-obstruction.md), which varies the terminal angles, **both angles here stay fixed at exactly \(90^\circ\)**. In contrast to [PM1](pinching-failure-of-global-envelope-concavity.md), **every input and interpolated body is an actual connected, smooth, feasible two-full-turn sofa** and has no niche, clipping, or pinch. What fails is the *unrestricted-scale* concavity of the signed area functional on the larger convex hull domain.

The example is low-area. It does **not** disprove concavity under an *additional fixed-height normalization*, show any sofa beats Romik, or prove the conjectured sharp bound. Its importance is to rule out a direct global Jensen argument on the precise **unrestricted convex domain** used in the newly committed value-equivalence theorems, before attempting its difficult contact Euler equations.

## 1. A genuine smooth Minkowski segment of complete two-turn sofas

Let \(B_2\) be the Euclidean closed unit disk and \(c=(0,1/2)\). For \(1/8\le r\le1/4\) define
\[
\boxed{K_r=c+rB_2.}\tag{SCX.1}
\]
All are compact, connected, strictly convex smooth bodies inside the normalized incoming strip \([0,1]\) and the fixed horizontal box \([-5/2,5/2]\). Their incoming vertical span is \(2r\le1/2\), so neither the hull's vertical extremes nor its horizontal width are fixed across the interpolation. Their actual support functions satisfy \(h_{K_r}(n)=c\cdot n+r\) for every unit normal \(n\).

For every \(p\in K_r\) and **every unit normal \(n\)**,
\[
0\le h_{K_r}(n)-p\cdot n
=\sup_{q\in K_r}(q-p)\cdot n
\le\operatorname{diam}(K_r)=2r\le\frac12<1.
\tag{SCX.2}
\]
Therefore at **every possible canonical supporting hallway orientation**, *both* inner-wall safety inequalities hold, not just one. Its incoming and both outgoing whole-body strip widths are \(2r<1\). Support continuity and the canonical placements produce full proper motions around both handed right-angle corners, with the required incoming and outgoing straight-arm translations.

In particular \(E_{\pi/2,\pi/2}(K_r)=K_r\), every signed fiber is nonnegative, no niche is present, and
\[
\boxed{\mathscr S(K_r)
=\mathscr V(K_r,\pi/2,\pi/2)
=|K_r|=\pi r^2.}\tag{SCX.3}
\]
The Minkowski segment of disks is exact:
\[
\frac12(K_{1/8}+K_{1/4})=K_{3/16}.
\]
Consequently
\[
\begin{aligned}
\mathscr S(K_{3/16})
-\frac{\mathscr S(K_{1/8})+\mathscr S(K_{1/4})}{2}
&=\pi\left(\frac9{256}-\frac12\left(\frac1{64}+\frac1{16}\right)\right)\\
&=\boxed{-\frac{\pi}{256}<0.}
\end{aligned}\tag{SCX.4}
\]
This proves:

**Theorem SCX1 (global fixed-angle signed Minkowski concavity is false).** Neither the signed full-turn functional \(\mathscr S\) nor the original-motion signed functional \(\mathscr V\) with terminal angles held at \((\pi/2,\pi/2)\) is concave on the entire Minkowski-convex domain of **all** compact convex hulls contained in \([-5/2,5/2]\times[0,1]\). The failure already occurs on a smooth one-dimensional family of actual feasible hulls with absolutely continuous open-quarter curvature density \(r<1/2\).

## 2. Why height normalization cannot simply be imposed afterward

The cause of SCX.4 is ordinary **quadratic area scaling** along a family whose horizontal and vertical span both change. It does not rule out a concavity theorem on a fixed-height slice.

However, a proof reducing every actual or signed maximizing body to exactly unit incoming vertical span is **not available**. The exact [VP1](vertical-padding-ordinary-area-obstruction.md) example shows that **unconditional vertical Minkowski padding can *decrease* the ordinary full-turn sofa area**, even for connected and symmetric sources. In that family the actual canonical fibers are nonempty throughout, so its signed and ordinary full-envelope areas agree, and the same failure applies to signed area monotonicity.

Thus one cannot dismiss SCX1 by silently restricting SJ1/OS1 to height-one bodies. Such a restriction may be legitimate for **global area maximizers**, but would require a separate theorem.

For reference, the convex-hull area alone is concave along a Minkowski segment with a *fixed vertical span and fixed vertical extrema*: the planar support-area formula gives a second derivative \(\int(v^2-v'^2)\,d\theta\), where \(v=h_1-h_0\) vanishes at the two vertical normals. The Dirichlet Wirtinger inequality on the two semicircles (each of length \(\pi\)) gives \(\int v^2\le\int v'^2\). This **does not** prove that *signed surviving sofa area* is concave on that slice—the moving inner-wall sweeps must still be accounted for.

**Research consequence.** A genuinely universal joint-area proof must find a sharp **nonconcave global calibration**, a separate rigorously admissible height normalization followed by a suitable fixed-height theorem, or another monotonicity/duality principle. Merely appealing to a “convex hull parameter domain,” to ordinary Brunn–Minkowski, or to the earlier signed support functional's concavity under stronger fixed traces does not establish SCX.4 with the opposite sign. The sharp Romik value and arbitrary partial-turn upper bound remain unproved.
