# Every Romik-competitive sofa must carve a robust positive-area niche from its actual convex hull

**Date: October 8, 2026. Status:** A new **unrestricted original-sofa** quantitative consequence of the certified **convex-sofa area upper bound \(31/20\)** [CV1](convex-sofa-two-corner-area-certificate.md), combined with the already proved area-dependent width normalization [PTW1](partial-turn-three-point-width.md). This holds for **arbitrary connected**, possibly nonsmooth, asymmetric, partial-turn or backtracking ambidextrous sofas. It requires **no false convexification** and no weighted two-cap clipping inequality. It is not a proof of \(|S|\le M\) or uniqueness.

**Theorem NC1 (mandatory robust inner-corner niche).** Let \(S\) be a compact connected ambidextrous sofa in a common incoming unit-width orientation, with \(|S|\ge M\), where
\[
M=1+4Y^2+\arctan Y,\qquad 4Y^3+3Y-1=0,\quad Y>0,
\]
and write \(K=\operatorname{conv}S\). Then:

1. For **at least one** of the two actually visited opposite-handed \(45^\circ\) canonical frames, there is a point \(q\in K\) such that **both** of its outward supporting-wall depths exceed \(103/100\):
   \[
   \boxed{
   h_K(n_1)-q\cdot n_1>\frac{103}{100},\qquad
   h_K(n_2)-q\cdot n_2>\frac{103}{100}.
   }\tag{NC.1}
   \]
   Here \(n_1,n_2\) are that frame's perpendicular **physical hallway** outer normals, with the opposite-handed pair interpreted in the actual (unreflected) body coordinates. These are support-depth, not separate one-wall distance, inequalities.
2. The canonical forbidden quadrant at **that one fixed \(45^\circ\) angle** contains a small positively homothetic **copy of the whole actual convex hull**, lying inside \(K\), of exact area \(|K|/10000\). Therefore
   \[
   \boxed{|K\setminus S|\ge\frac{|K|}{10000}>\frac1{6250}.}\tag{NC.2}
   \]
   Thus *every* sofa reaching the reference area has a provably positive **ordinary area gap to its own convex hull**, independently of niche topology, full-turn completion or contact pattern.
3. For any compact **convex body** \(C\) fitting both opposite \(45^\circ\) supporting hallways in the same incoming orientation, its Hausdorff distance from \(K\) obeys
   \[
   \boxed{d_{\mathrm H}(K,C)\ge\frac3{200}.}\tag{NC.3}
   \]
   The same holds after optimizing over horizontal/vertical translations of \(C\), since support depths are translation-invariant.

The constants are deliberately simple rational choices, **not** claimed sharp. In particular \(|K\setminus S|\) refers to actual material missing from the convex hull of **the same** sofa, not to the convex hull of an auxiliary cap or to separate one-turn signed deficits.

## 1. Exact cubic-root arithmetic supplies a strict 3% margin

Set \(x=149/500\). Then
\[
4x^3+3x-1=-4551/31250000<0,
\]
and the cubic is strictly increasing on \([0,\infty)\), so \(Y>x\).
The function \(z\mapsto1+4z^2+\arctan z\) is strictly increasing for \(z>0\). For \(0<x<1\), the alternating arctangent series gives
\[
\arctan x>x-\frac{x^3}{3}+\frac{x^5}{5}-\frac{x^7}{7}.
\]
Direct Fraction reduction proves the exact rational comparison
\[
\begin{aligned}
M
&>1+4x^2+x-\frac{x^3}{3}+\frac{x^5}{5}-\frac{x^7}{7}\\
&=\frac{328879}{200000}
 +\frac{72188080152239353}{164062500000000000000}
>\frac{31}{20}\left(\frac{103}{100}\right)^2
=\frac{328879}{200000}.
\end{aligned}\tag{NC.4}
\]
This is independently replayed in the tiny [Fraction audit](computer-assisted/check_mandatory_nonconvexity_budget.py).

## 2. If neither corner cuts deeply enough, shrink the *entire convex hull*

The body \(S\) has area \(> \sqrt2\), so the original-motion proper-angle argument [GH](midpoint-bound-general-motions.md) guarantees that **both** proper \(45^\circ\) frames have actually been visited. Canonical support tightening applies to their **actual convex hull** \(K\).

For the lower frame and the opposite-handed frame separately, define the worst depth
\[
D_\pm(K)=\max_{q\in K}
\min\{h_K(n_{\pm,1})-q\cdot n_{\pm,1},
       h_K(n_{\pm,2})-q\cdot n_{\pm,2}\}.
\tag{NC.5}
\]
Compactness guarantees the maxima are attained. Suppose that **both** \(D_-(K)\) and \(D_+(K)\) were at most \(103/100\). The uniformly shrunk convex body
\[
K'=\frac{100}{103}K
\]
has each support depth multiplied by \(100/103\), so it fits **both opposite \(45^\circ\) canonical supporting hallways**. Its incoming vertical span is also at most one. The new exact **convex two-corner theorem CV1** therefore yields
\[
\frac{10000}{10609}|K|=|K'|\le\frac{31}{20},
\quad\text{hence}\quad
|K|\le\frac{31}{20}\left(\frac{103}{100}\right)^2<M,
\]
contradicting \(|K|\ge|S|\ge M\). So one \(D_\pm(K)>103/100\). The maximizing point \(q\) for that frame satisfies **both** depths \(>103/100\), proving NC.1.

This is the precise reason a genuinely area-competitive sofa **cannot have an almost-turnable convex hull**: the inner-wall carving is necessarily robust, not a negligible point defect.

## 3. Turn a forbidden point into a whole **forbidden copy of the hull**

The original-motion width theorem [PTW1](partial-turn-three-point-width.md), valid above \(\sqrt2\), gives horizontal width \(W(S)\le2\sqrt2\). The vertical span is at most one, hence
\[
\operatorname{diam}(K)\le\sqrt{W(S)^2+1}\le3.
\tag{NC.6}
\]
For the point \(q\in K\) from NC.1, define the one-percent homothetic image
\[
\boxed{K_q=\left\{q+\frac{p-q}{100}:p\in K\right\}.}\tag{NC.7}
\]
Since \(K\) is convex, **every point of \(K_q\) belongs to \(K\)**. For either of the two selected hallway normals \(n_i\) and any \(p\in K\),
\[
\begin{aligned}
h_K(n_i)-\left(q+\frac{p-q}{100}\right)\cdot n_i
&=h_K(n_i)-q\cdot n_i-\frac1{100}(p-q)\cdot n_i\\
&>\frac{103}{100}-\frac{\operatorname{diam}(K)}{100}\\
&\ge1.
\end{aligned}\tag{NC.8}
\]
Thus **the entire positive-area convex copy \(K_q\)** is contained in one actual canonical **open forbidden quadrant**. The real sofa \(S\) avoids this quadrant by support tightening at the visited frame, so
\[
K_q\subseteq K\setminus S,\qquad
|K\setminus S|\ge |K_q|=\frac{|K|}{10000}
\ge\frac{|S|}{10000}\ge\frac{M}{10000}>
\frac{8/5}{10000}=\frac1{6250}.
\]
No regularity, inradius estimate, or assumption that the offending point \(q\) lies in the interior of \(K\) is required. The **homothety about \(q\)** works even when \(q\) is an extreme point or lies on an exposed edge.

## 4. Robust separation from genuinely convex corner-compatible bodies

Let \(C\) be any compact convex body satisfying both opposite \(45^\circ\) canonical hallway positions, in the same fixed incoming orientation. Suppose \(d_{\mathrm H}(K,C)=\varepsilon<3/200\). Pick \(q'\in C\) with \(|q-q'|\le\varepsilon\). For any unit normal \(n\), Hausdorff distance gives \(|h_K(n)-h_C(n)|\le\varepsilon\). At the violated frame,
\[
h_C(n_i)-q'\cdot n_i
\ge h_K(n_i)-q\cdot n_i-2\varepsilon
>1+\frac3{100}-2\varepsilon>1.
\]
This violates its claimed canonical hallway feasibility. Therefore the Hausdorff distance cannot be smaller than \(3/200\). Translation invariance of the support-depth definition permits the same proof for any translate \(C+a\). This proves NC.3.

## 5. Scope and next task

The combined CV1/NC1 result *quantitatively excludes the convex or almost-convex branch of the original unrestricted problem*: any sofa area at least Romik's candidate must carve a **fixed positive ordinary-area portion** of its own hull, already forced at one proper diagonal angle. This is a global theorem across arbitrary original motions, not only fully turning or reference-symmetric ones.

However the lower bound \(1/6250\) is tiny compared with the reference's actual swept niche. It is a **necessary** condition, not an upper bound on \(|S|\), and it does not by itself rule out an asymmetric competitor of area \(>M\). The further difficulty is to **optimize the area of the connected nonconvex union left after carving** in terms of the *continuum* of actual outer-wall contacts and their attached corner rays. A natural next mathematical step is to derive a quantitatively controlled decomposition of a candidate sofa into **corner-safe convex pieces**, where the new CV1 bound can be applied without double-counting areas or incorrectly convexifying the whole sofa.

No CI, Lean/Lake build, numerical global optimizer or proof of unrestricted optimality is claimed.
