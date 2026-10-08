# Exact failure of joint terminal-angle concavity — without any niches or pinches

**Date:** October 8, 2026. **Status:** A short analytic obstruction to a naive Jensen proof of the [OS1](original-motion-signed-convex-domain.md) global signed-area formulation. The signed joint ordinary-fiber objective is **not concave in the terminal angles**, even when the convex hull \(K\) is fixed, both full-turn niches vanish identically, and every envelope fiber is nonempty. This is **not** a sofa larger than Romik, and does **not** address a possible concavity theorem in the hull-support variable with the terminal angles **fixed**.

No CI, Lean, sampled-angle feasibility claim or floating integration is used.

## 1. A rational rectangle whose full-turn niches vanish

Let
\[
\boxed{K=[-3/8,3/8]\times[0,1],\quad W=3/4.}\tag{TA.1}
\]
It is convex, connected, has height one, and has horizontal reflection symmetry and vertical reflection symmetry about \(y=1/2\).

For any lower canonical turn angle \(t\in[0,\pi/2]\), abbreviate \(c=\cos t,s=\sin t\). The two outer supports are
\[
h_K(u_t)=\frac W2c+s,\qquad
h_K(v_t)=\frac W2s+c.
\]
Its forbidden inner-quadrant roof at every horizontal abscissa is bounded above by the inner-corner height
\[
C_y(t)=Wsc+1-s-c.
\]
Putting \(z=s+c\in[1,\sqrt2]\) and using \(2sc=z^2-1\) gives
\[
C_y(t)=(z-1)\left(\frac W2(z+1)-1\right).
\]
Since \(W=3/4\) and
\[
\frac38(1+\sqrt2)<1
\quad\Longleftrightarrow\quad
3\sqrt2<5,
\]
the corner height is **nonpositive for all turning angles**. Every lower forbidden quadrant therefore lies at heights \(y\le0\); the *entire* positive lower full-niche roof is identically zero. The same holds for the upper-handed niche by vertical reflection:
\[
\boxed{n_{K;\alpha}(x)=n_{\rho K;\gamma}(x)=0
\quad\text{for all }\alpha,\gamma\le\pi/2,\ x\in[-W/2,W/2].}\tag{TA.2}
\]
This covers the continuum of angles, not merely finitely many samples.

## 2. Fix one full turn and vary the other actual outgoing angle

Keep the upper-handed terminal magnitude **fully turned** at \(\gamma=\pi/2\), and vary the lower-handed terminal magnitude
\(\alpha\in[\pi/4,\pi/2]\). The upper outgoing whole-body strip is redundant; its roof is \(1\) everywhere. The lower terminal outgoing strip, however, has the exact lower barrier from OS.2,
\[
e_\alpha(x)=\frac{(W/2-x)\cos\alpha+\sin\alpha-1}{\sin\alpha}.
\]
Put
\[
d(\alpha)=\frac{1-\sin\alpha}{\cos\alpha}
=\frac{\cos\alpha}{1+\sin\alpha},\qquad
C(\alpha)=\cot\alpha.
\]
Then
\[
e_\alpha(x)=C(\alpha)\,[W/2-x-d(\alpha)].
\]
On \([\pi/4,\pi/2]\), \(0\le d(\alpha)\le\sqrt2-1<W=3/4\).
Hence \(e_\alpha(x)>0\) precisely on the left subinterval of width \(W-d(\alpha)\), and \(e_\alpha(x)\le W\cot\alpha\le3/4<1\). Every surviving fiber is therefore a **nonempty interval** \([\max(0,e_\alpha(x)),1]\).

Integrating the *actual signed fiber length*, which equals the ordinary envelope length here, gives the **exact analytic identity**
\[
\begin{aligned}
\mathscr V(K,\alpha,\pi/2)
&=\int_{-W/2}^{W/2}[1-\max(0,e_\alpha(x))]dx\\
&=\boxed{W-\frac12\cot\alpha
\left(W-\frac{\cos\alpha}{1+\sin\alpha}\right)^2.}
\end{aligned}\tag{TA.3}
\]
It holds on the entire closed angular interval, by continuity at \(\alpha=\pi/2\). No geometric mass is hidden in an empty fiber, a clipped niche, or an overlapping forbidden sweep.

Each full envelope in TA.3 is a **compact connected genuine sofa with the specified partial lower/full upper motions**: it is a vertical interval bundle with full horizontal projection, fits the complete canonical angle intervals by definition, and satisfies the whole-body outgoing straight-arm strips. The physical entrance and exit translations append as in [OS1](original-motion-signed-convex-domain.md). Its **actual convex hull** need not equal the original auxiliary rectangle \(K\); this is not assumed.

## 3. The second derivative is strictly positive at an exact rational direction

Let
\[
F(\alpha)=\mathscr V(K,\alpha,\pi/2),\qquad
r(\alpha)=W-d(\alpha),\qquad C(\alpha)=\cot\alpha.
\]
The derivatives simplify to
\[
d'=-\frac1{1+\sin\alpha},\qquad
r'=\frac1{1+\sin\alpha},\qquad
r''=-\frac{\cos\alpha}{(1+\sin\alpha)^2},
\]
\[
C'=-\frac1{\sin^2\alpha},\qquad
C''=\frac{2\cos\alpha}{\sin^3\alpha},
\]
and therefore
\[
\boxed{
F''(\alpha)=-\frac12
\left[C''r^2+4C'rr'+2C((r')^2+rr'')\right].
}\tag{TA.4}
\]

Choose
\[
\alpha_0=\arctan(4/3)
=2\arctan(1/2)\in(\pi/4,\pi/2).
\]
At \(\alpha_0\),
\[
\sin\alpha_0=4/5,\ \cos\alpha_0=3/5,\ 
r=5/12,\ C=3/4,\ C'=-25/16,\ C''=75/32,\
r'=5/9,\ r''=-5/27.
\]
Direct substitution gives
\[
\begin{aligned}
F''(\alpha_0)
&=-\frac12\left[
\frac{625}{1536}-\frac{625}{432}+\frac{25}{72}
\right]\\
&=\boxed{\frac{9575}{27648}>0.}
\end{aligned}\tag{TA.5}
\]
The identity is a rational-arithmetic calculation; [the checker](computer-assisted/check_terminal_angle_concavity.py) verifies the derivatives independently.

**Theorem TA1 (signed objective not jointly concave).** The [OS1](original-motion-signed-convex-domain.md) exact signed joint-area objective \(\mathscr V(K,\alpha,\gamma)\) is **not concave** on its domain \(K\in\mathcal K_B\), \(\pi/4\le\alpha,\gamma\le\pi/2\): its restriction to the fixed convex hull TA.1 and fixed upper terminal angle \(\gamma=\pi/2\) has strictly **positive** second derivative at the interior angle \(\alpha_0\). The conclusion already holds in the complete absence of forbidden-niche mass and fiber pinches.

## 4. Correct narrowed sharp-proof target

The global equivalence OS1 and its monotone admission repair OS2 **remain valid**. TA1 only excludes the shortcut “the objective is jointly concave on the convex parameter product; verify candidate stationarity and conclude globally.” A *fixed-terminal-angle* concavity theorem in the convex hull support variable is **not** refuted. Such a theorem, if true, would still leave the independent **nonconcave terminal-angle optimization**:
\[
\sup_{\pi/4\le\alpha,\gamma\le\pi/2}
\ \sup_{K\in\mathcal K_B}\mathscr V(K,\alpha,\gamma).
\]
It is not permissible to maximize this expression by an interior Euler equation in both angles without controlling its boundaries and all global stationary branches. A different globally calibrated joint inequality could also bypass concavity entirely.

The example has width \(3/4\) and area at most \(3/4\), far below Romik's value. It neither bounds high-area competitors nor produces a sofa exceeding \(M\). No numerical-search result is a premise, and unrestricted optimality remains open.
