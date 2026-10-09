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

## 5. An exact **continuous outer-hull-versus-niche area penalty**, not just a fixed lower margin

The numerical constants in NC1 can be replaced by a **general coercive inequality**. This expresses the area-cost of nonconvexity as an explicit function of the **outer hull's area and diameter**, without any reference to Romik's contact phases.

**Theorem NC2 (two-corner convexity-defect coercivity).** Let \(S\) be any compact measurable body in a common incoming strip of height at most one, fitting the **two opposite proper \(45^\circ\) canonical hallway positions** after support tightening to its true convex hull \(K=\operatorname{conv}S\). The body itself need *not* be convex or connected. Put
\[
A_K=|K|,\qquad D=\operatorname{diam}(K),
\qquad C=\frac{10}{7}.
\]
For positive area \(A_K>0\), the ordinary convexity deficit satisfies
\[
\boxed{
|K\setminus S|\ge
\frac{A_K}{D^2}
\left(\sqrt{\frac{A_K}{C}}-1\right)_+^{\!2}.
}\tag{NC.9}
\]
For \(A_K\le C\) the right side is zero by convention. In equivalent area-majorant form,
\[
\boxed{
|S|\le A_K-
\frac{A_K}{D^2}
\left(\sqrt{\frac{A_K}{10/7}}-1\right)_+^{\!2}.
}\tag{NC.10}
\]
This is valid for **every** pair of opposite \(45^\circ\) poses and every compact sofa geometry, not just near Romik. For an original above-\(\sqrt2\) ambidextrous sofa, the existing motion reach theorem supplies the required two poses automatically.

**Proof.** For either handed frame \(d=\pm\), write its two actual outer unit normals \(n_{d,1},n_{d,2}\), and define
\[
\Lambda_d(K)=\max_{q\in K}
\min\{h_K(n_{d,1})-q\cdot n_{d,1},
       h_K(n_{d,2})-q\cdot n_{d,2}\},\quad
\Lambda=\max(\Lambda_-,\Lambda_+).
\]
Both maxima exist because \(K\) is compact. Every support depth lies in \([0,D]\), so \(0\le\Lambda\le D\).

If \(\Lambda\le1\), the **entire convex hull** fits both of the canonical hallway positions, since every point has at least one safe inner-wall inequality at each frame. It also fits the incoming strip. CV1's exact **two-position** theorem gives \(A_K\le C\), so the claimed inequality has zero right side and is trivial.

If \(\Lambda>1\), shrink the **convex hull itself** uniformly by \(1/\Lambda\). All canonical depths scale by that factor, so the shrunk compact convex body fits both opposite frames and the incoming strip, whence CV1 yields
\[
\boxed{A_K/\Lambda^2\le C,\qquad
\Lambda\ge\sqrt{A_K/C}.}\tag{NC.11}
\]

Choose a frame \(d\) and \(q\in K\) attaining \(\Lambda\). **Both** depths of \(q\) in that frame are at least \(\Lambda>1\). For each
\[
0<t<\frac{\Lambda-1}{D}<1,
\]
the homothetic copy \(K_{q,t}=q+t(K-q)\) lies inside \(K\) by convexity. For every \(p\in K\) and either normal \(n_{d,i}\),
\[
h_K(n_{d,i})-\bigl(q+t(p-q)\bigr)\cdot n_{d,i}
\ge \Lambda-tD>1.
\]
Thus the **entire** positive-area copy \(K_{q,t}\) lies inside one **open forbidden quadrant** of the actual support-tightened hallway, and so it is disjoint from the genuine sofa S. Its area is \(t^2A_K\), yielding
\[
|K\setminus S|\ge t^2A_K.
\]
Take \(t\uparrow(\Lambda-1)/D\) to obtain
\[
|K\setminus S|\ge\frac{A_K}{D^2}(\Lambda-1)^2.
\]
Combine with NC.11; if \(A_K\le C\) the positive-part bound remains trivial, and if \(A_K>C\) then
\(\Lambda-1\ge\sqrt{A_K/C}-1>0\).
This proves NC.9. Since \(S\subseteq K\) and both are measurable,
\(|S|=A_K-|K\setminus S|\), proving NC.10. \(\square\)

**Interpretation.** The inequality supplies exactly the type of **outer-area growth must create inner-wall shadow area** charge suggested by the user's geometric strategy, but presently only relative to the best *convex* two-corner bound \(C=31/20\), not yet relative to the sharp Romik candidate \(M\). It accounts for **actual carved ordinary area**, rather than two separate one-turn signed deficits; it tolerates any forbidden-region overlap and arbitrarily partial or backtracking histories when the two midpoint poses are visited.

The original fixed numerical NC1 is a weaker rational specialization when \(A_K\ge M\), combined with \(D\le3\). NC2 gives a continuous, scale-sensitive inequality for every hull, including ones far above or below the reference area. It **does not** imply \(|S|\le M\) because high-area convex hulls can pay the relatively small compulsory niche budget and still leave an area larger than \(M\).

## 6. Stronger mandatory niche from the exact \(3/2\) convex certificate

The independent rational certificate [CV1 (updated)](convex-sofa-two-corner-area-certificate.md) has now improved the **entire convex** two-corner area upper bound from \(31/20\) to \(C=3/2\). That immediately strengthens NC1 substantially. The old, valid 3%-depth and \(1/6250\) statements remain above as historical weaker bounds; the following result supersedes them.

**Theorem NC3 (4.7%-depth and \(1/2500\)-area gap).** Every genuine compact connected ambidextrous sofa satisfying \(|S|\ge M\), in a common incoming unit strip, has an actual convex hull \(K\) with these three properties:

\[
\boxed{
\begin{gathered}
\exists\text{ a visited proper }45^\circ\text{ hallway frame and }q\in K:\\
h_K(n_1)-q\cdot n_1>\frac{1047}{1000},\qquad
h_K(n_2)-q\cdot n_2>\frac{1047}{1000};\\[2pt]
|K\setminus S|\ge\frac{2209}{9000000}|K|
>\boxed{\frac1{2500}};\\
d_{\mathrm H}(K,C)\ge\frac{47}{2000}
\quad\text{for every convex }C\text{ fitting both opposite proper }45^\circ\text{ poses.}
\end{gathered}
}\tag{NC.12}
\]
The Hausdorff statement remains true after any translation of \(C\). It is a necessary nonconvexity bound, not a sofa-area optimality theorem.

**Proof.** As in NC1, both correct-handed \(45^\circ\) frames are visited because \(|S|\ge M>\sqrt2\). The exact root/arctangent comparison in Section 1 gives
\[
M>
\frac{328879}{200000}
>
\frac32\left(\frac{1047}{1000}\right)^2
=\frac{3288627}{2000000};
\qquad M>\frac{41}{25}.
\tag{NC.13}
\]
(The middle comparison follows by writing \(328879/200000=3288790/2000000>3288627/2000000\).)

If every point of \(K\) had minimum depth at most \(1047/1000\) in each of the two frames, then shrinking **the whole convex hull** by \(1000/1047\) would make it fit both supporting L hallways and the incoming strip. Its area would be at least
\(M(1000/1047)^2>3/2\), contradicting the now **fully certified** CV1 theorem. Thus there is a point \(q\in K\) for which both depths in one visited frame exceed \(1047/1000\).

The competitive original-motion horizontal-width bound PTW1 yields \(D=\operatorname{diam}K\le3\). Set \(t=47/3000\). The convex homothetic copy
\(q+t(K-q)\) stays inside \(K\), and every point \(q+t(p-q)\) of that copy has both forbidden depths strictly greater than
\[
\frac{1047}{1000}-\frac{47}{3000}D
\ge\frac{1047}{1000}-\frac{47}{1000}=1.
\]
Hence the whole copy lies in one **open actual forbidden inner-wall quadrant** at a genuinely visited angle and is disjoint from \(S\). Its area is \(t^2|K|=(2209/9000000)|K|\). Since \(|K|\ge|S|\ge M>41/25\),
\[
|K\setminus S|>
\frac{2209}{9000000}\frac{41}{25}
=\frac{90569}{225000000}
>\frac{90000}{225000000}
=\frac1{2500}.
\]
Finally, the support function is 1-Lipschitz in Hausdorff distance and each witness point can be paired within that distance. If a genuinely corner-compatible convex \(C\) were within \(47/2000\) of \(K\), the two depths at a nearby point would exceed \(1047/1000-2(47/2000)=1\), impossible. Translation does not change the support-depth argument. \(\square\)

This improvement is a **strictly stronger global quantitative theorem** than NC1 and requires no convexity of the actual sofa. Nonetheless its compulsory missing-hull area \(\approx0.0004\) remains far below the real Romik niches: it cannot replace the full continuous swept-ray area analysis required for sharp optimality.

## 7. Further strengthening from the certified \(10/7\) convex bound

The final independent exhaustive rational [CV1](convex-sofa-two-corner-area-certificate.md) replay improves the convex two-corner bound again, from \(3/2\) to
\[
C=\frac{10}{7}=1.428571\ldots
\]
with **378,771** parameter boxes, **189,376** certified leaves, maximum depth **32**, no unresolved boxes. This yields the strongest unconditional **actual-sofa** nonconvexity budget obtained here.

**Theorem NC4 (7.3%-depth; mandatory missing ordinary area \(>1/1030\)).** Every genuine compact connected ambidextrous sofa \(S\) with \(|S|\ge M\) has actual convex hull \(K\) satisfying
\[
\boxed{
\begin{gathered}
\exists\text{ a genuinely visited proper }45^\circ\text{ frame and }q\in K:\
h_K(n_1)-q\cdot n_1>\frac{1073}{1000},\quad
h_K(n_2)-q\cdot n_2>\frac{1073}{1000};\\[3pt]
|K\setminus S|\ge\frac{5329}{9000000}|K|
>\boxed{\frac1{1030}};\\[3pt]
d_{\mathrm H}(K,C)\ge\frac{73}{2000}
\quad\text{for every compact convex two-45-degree-compatible }C
\text{ (including its translates).}
\end{gathered}}\tag{NC.14}
\]

**Proof.** The lower rational root bracket \(Y>149/500\) and alternating arctangent lower bound in NC.4 give the *exact* strict inequality
\[
M >
1+4(149/500)^2+\left[(149/500)-(149/500)^3/3
+(149/500)^5/5-(149/500)^7/7\right]
>
\frac{10}{7}\left(\frac{1073}{1000}\right)^2
=\frac{1151329}{700000}.
\tag{NC.15}
\]
The final comparison is checked exactly by the [Fraction replay](computer-assisted/check_mandatory_nonconvexity_budget.py), with no rounded value of \(M\) used.

Both proper \(45^\circ\) frames must be visited since \(|S|\ge M>\sqrt2\). If the maxima over \(q\in K\) of both-wall minimum support depth in *each* frame were at most \(1073/1000\), then the *entire convex hull* scaled by \(1000/1073\) would fit the incoming strip and both diagonal hallway positions. Its area would be at least
\(M(1000/1073)^2>10/7\), contradicting the certified convex CV1 theorem. Hence at least one visited frame contains a point \(q\in K\) with both support depths \(>1073/1000\).

The established competitive-width theorem PTW1 gives \(D=\operatorname{diam}K\le3\). Use the exact homothety ratio
\(t=73/3000\). Every \(p\in K\) produces a retained-hull point
\(q+t(p-q)\in K\) whose two depths both exceed
\[
\frac{1073}{1000}-tD
\ge\frac{1073}{1000}-\frac{73}{1000}=1.
\]
Thus the entire copy \(q+t(K-q)\) is **strictly forbidden at one actual hallway position** and is disjoint from \(S\). Its ordinary area is \(t^2|K|=(5329/9000000)|K|\). Since \(M>41/25\), we have
\[
|K\setminus S|>
\frac{5329}{9000000}\frac{41}{25}
=\frac{218489}{225000000}
>\frac1{1030},
\]
where the last strict rational comparison is \(218489\cdot1030=225043670>225000000\). The Hausdorff bound follows as in NC3 from the 1-Lipschitz support function and a matching hull point: a convex compatible body within \(73/2000\) would have a point with both unsafe depths exceeding \(1073/1000-2(73/2000)=1\). \(\square\)

This is roughly six times the former \(1/6250\) area-gap constant, and it improves the mandatory worst-depth excess from 3% to 7.3%. The more informative continuous all-area penalty NC.9–NC.10 also now uses \(C=10/7\) rather than the older \(31/20\) or \(3/2\). These are genuine **unrestricted necessary inequalities**; they still do **not** imply the Romik sharp upper bound because actual sofas may have convex hulls of substantially larger area and can lose much more area to their continuous inner-corner sweep.

## 8. Scope and next task

The combined CV1/NC1 result *quantitatively excludes the convex or almost-convex branch of the original unrestricted problem*: any sofa area at least Romik's candidate must carve a **fixed positive ordinary-area portion** of its own hull, already forced at one proper diagonal angle. This is a global theorem across arbitrary original motions, not only fully turning or reference-symmetric ones.

However the lower bound \(1/6250\) is tiny compared with the reference's actual swept niche. It is a **necessary** condition, not an upper bound on \(|S|\), and it does not by itself rule out an asymmetric competitor of area \(>M\). The further difficulty is to **optimize the area of the connected nonconvex union left after carving** in terms of the *continuum* of actual outer-wall contacts and their attached corner rays. A natural next mathematical step is to derive a quantitatively controlled decomposition of a candidate sofa into **corner-safe convex pieces**, where the new CV1 bound can be applied without double-counting areas or incorrectly convexifying the whole sofa.

No CI, Lean/Lake build, numerical global optimizer or proof of unrestricted optimality is claimed.
