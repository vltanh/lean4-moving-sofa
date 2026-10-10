# Every complementary pair of moving corners constrains two perpendicular hull widths

**Date:** 2026-10-08. **Status:** A new *continuum directional-width necessary condition* for the ambidextrous moving sofa problem, extending the **previously known single-\(45^\circ\) width gate** [DU2](diagonal-width-upper-bound.md). It is an exact outer-wall-plus-moving-inner-corner argument, independent of area integration, curvature, contact order, symmetry and full-turn completion. No optimality proof or larger feasible sofa is claimed.

The new, broader [two moving-corner packing inequalities](two-moving-corner-packing.md) also apply to **noncomplementary** pairs. An exact rational pentagon with *outer hull area larger than Romik's \(M\)* passes **every complementary directional-width test** but fails one noncomplementary corner-pair test, with its two individual one-pose carved hulls remaining separately connected. This demonstrates genuine extra information beyond simply imposing DU2 at every rotation angle.

## 1. Opposite-handed complementary poses share one rotated outer rectangle

Normalize the common incoming orientation to \(0\le y\le1\). Let \(S\) be compact and **connected**, with actual convex hull \(K=\operatorname{conv}S\). Suppose the conventional lower motion visits \(t\in(0,\pi/2)\), and the independently conventional upper motion visits **the complementary magnitude**
\[
s=\pi/2-t.
\]

Put \(u=(\cos t,\sin t)\), \(v=(-\sin t,\cos t)\) and introduce rotated coordinates
\[
U=p\cdot u,\quad V=p\cdot v.
\]
Let \(U_{\min},U_{\max},V_{\min},V_{\max}\) denote the **actual** support extrema of \(K\), and write
\[
P=U_{\max}-U_{\min}=w_K(u),\qquad
Q=V_{\max}-V_{\min}=w_K(v).
\tag{CD.1}
\]
Canonical outer-wall tightening, which preserves every feasible point, puts \(S\) inside the rotated rectangle
\[
[U_{\min},U_{\max}]\times[V_{\min},V_{\max}].
\]

At the lower \(t\)-hallway corner, the two attached inner-wall rays enforce
\[
U\ge U_{\max}-1\quad\text{or}\quad
V\ge V_{\max}-1.
\]
The upper at \(s=\pi/2-t\), reflected back into the original incoming frame, has outward normals **\(-v,-u\)** in reverse order. Its corner therefore enforces the **opposite** disjunction
\[
U\le U_{\min}+1\quad\text{or}\quad
V\le V_{\min}+1.
\]
This identity is exact for every \(t\), not just \(t=\pi/4\). It uses the physical **sharp corners and both attached inner rays**, not outer-wall constraints alone.

Translate the rotated coordinate minima to zero. Every point of \(S\) consequently lies in
\[
D(P,Q)=\left\{(U,V)\in[0,P]\times[0,Q]:
\begin{array}{l}
U\ge P-1\ \text{or}\ V\ge Q-1,\\
U\le1\ \text{or}\ V\le1
\end{array}
\right\}.
\tag{CD.2}
\]

## 2. All-angle complementary-width theorem

**Theorem CD1.** Whenever both complementary hallway positions just described are visited by a compact connected ambidextrous sofa, its actual convex hull obeys
\[
\boxed{\min\{w_K(u_t),w_K(v_t)\}\le2.}\tag{CD.3}
\]

**Proof.** Suppose \(P>2\) and \(Q>2\). Distribute the two safe-wall alternatives in CD.2. The choices \(U\ge P-1\) and \(U\le1\) are incompatible, as are \(V\ge Q-1\) and \(V\le1\). The two remaining possible combinations give **exactly**
\[
D(P,Q)=
([P-1,P]\times[0,1])
\ \cup\
([0,1]\times[Q-1,Q]).
\tag{CD.4}
\]
Because \(P-1>1\) and \(Q-1>1\), these two closed unit squares are **positively separated**. A connected \(S\) must lie wholly in one square, and hence its actual support widths in *both* \(u,v\) coordinates would be at most one. But these actual widths are \(P,Q>2\), a contradiction. Therefore at least one is at most two. \(\square\)

The older [DU2](diagonal-width-upper-bound.md) proves only \(t=\pi/4\). **CD1 holds for every complementary pair actually visited**. In particular a sofa with both full conventional turns satisfies
\[
\boxed{
\forall\,t\in[0,\pi/2],\quad
\min\{w_K(u_t),w_K(v_t)\}\le2.
}\tag{CD.5}
\]
Endpoint cases follow by continuity; at \(t=0,\pi/2\) the incoming unit-height condition also gives the claim.

**Competitive *partial* turns are covered on a uniform interval.** For conventional reduced endpoint magnitudes \(\alpha,\gamma\le\pi/2\), both \(t\) and \(\pi/2-t\) are visited whenever
\[
\pi/2-\gamma\le t\le\alpha.
\tag{CD.6}
\]
The existing proper-angle reduction [Note 8–10](08-common-hull-tightening.md) ensures that any original ambidextrous body with \(|S|>M\) has such proper partial turns, with the outgoing whole-body strips. The two-strip determinant bound gives
\[
|S|\le\sec\alpha,\quad |S|\le\sec\gamma.
\]
Because \(M>8/5\), a hypothetical sofa with \(|S|>M\) has
\[
\alpha,\gamma>\theta_0:=\arccos(5/8)>\pi/4.
\]
Thus it must satisfy the **whole interval** of support inequalities
\[
\boxed{
\min\{w_K(u_t),w_K(v_t)\}\le2
\quad
\forall\,t\in[\pi/2-\theta_0,\theta_0].
}\tag{CD.7}
\]
This includes asymmetric, partially turning and backtracking original motions. No unproved completion to full \(90^\circ\) turns is used.

The interval \([\pi/2-\theta_0,\theta_0]\) is about \(38.68^\circ\) to \(51.32^\circ\), **not** just one diagonal frame. CD.7 does not by itself bound the sofa's area by \(M\).

## 3. Rational pentagon: the \(45^\circ\) test passes but another complementary pair fails

Take
\[
K=\operatorname{conv}
\{(-13/10,9/10),\,(-1,1/10),\,(3/5,0),\,
(13/10,7/10),\,(1/4,1)\}.
\tag{CD.8}
\]
The vertices occur in counterclockwise order; \(|K|=189/100\). At \(45^\circ\), its two diagonal raw coordinate spans are \(29/10\) and \(14/5\). The smaller normalized diagonal width is \(14/(5\sqrt2)<2\) because \(196<200\). Thus **DU2 passes**.

But at the exact rational **complementary angles**
\[
(\cos t,\sin t)=(20/29,21/29),\qquad
(\cos s,\sin s)=(21/29,20/29),
\]
the two perpendicular actual widths are
\[
\boxed{w_K(u_t)=w_K(v_t)=293/145>2.}\tag{CD.9}
\]
CD1 therefore rules out this hull for any connected sofa visiting those two positions. The full two-moving-corner tent calculation gives the stronger explicit empty-fiber surplus \(\frac1{35}>0\), with all individual extreme vertices still safe at the two separate poses. This is a short exact certificate excluding a **hypothetical** above-\(M\) outer hull, not a sofa exceeding \(M\).

## 4. Noncomplementary moving corners are strictly stronger than *all* width tests

A more discriminating rational hull is the convex hexagon \(H\) with vertices in counterclockwise order
\[
\boxed{
\begin{aligned}
&(-61/50,48/125),\quad(-147/500,0),\\
&(136/125,13/500),\quad(61/50,213/500),\\
&(149/125,897/1000),\quad(-263/500,1).
\end{aligned}}\tag{CD.10}
\]
Its area is exactly
\[
\boxed{|H|=1902703/10^6>M.}\tag{CD.11}
\]
The last comparison follows rigorously from the reference cubic: \(Y<3/10\), \(\arctan Y<Y\), so \(M=1+4Y^2+\arctan Y<83/50<1902703/10^6\). **The polygon is an impossible proposed outer hull, not a larger feasible sofa.**

### 4a. A finite, exact certificate that *every complementary-width gate passes*

The horizontal projection of \(H\) has width \(61/25=2.44\), and its vertical span is one. Therefore its diameter is less than three, by the enclosing rectangle bound
\[
\operatorname{diam}(H)^2\le(61/25)^2+1<9.
\]
The width function \(w_H(n)=\sup_{p,q\in H}(p-q)\cdot n\) is diameter-Lipschitz in the unit normal. In particular
\[
F(t)=\min\{w_H(u_t),w_H(v_t)\}
\]
is \(3\)-Lipschitz in turning angle.

Choose **all 257 rational half-angle parameters** \(q_j=j/256\), \(0\le j\le256\), and their exact rational unit normals
\[
(\cos t_j,\sin t_j)=
\left(\frac{1-q_j^2}{1+q_j^2},
\frac{2q_j}{1+q_j^2}\right).
\]
For each, evaluate the maximum and minimum of the scalar products **over all six rational vertices**. All values are exact fractions; the [replay checker](computer-assisted/check_complementary_corner_widths.py) verifies
\[
\boxed{\max_{0\le j\le256} F(t_j)
=\frac{4866293}{2468500}<\frac{99}{50}.}\tag{CD.12}
\]
Every \(t\in[0,\pi/2]\) has a half-angle parameter within \(1/(2\cdot256)\) of a mesh node. Because \(d(2\arctan q)/dq\le2\), its turning-angle distance is at most \(1/256\). Hence by the rigorous Lipschitz bound
\[
\boxed{
F(t)\le\frac{4866293}{2468500}+\frac3{256}
=2-\frac{2673873}{157984000}<2
\quad\text{for **every real** }t.
}\tag{CD.13}
\]
This is a small, globally valid rational continuum certificate, **not an interpolation from untrusted floating-angle samples**. It demonstrates that \(H\) passes **all** complementary-pose width inequalities CD.5.

### 4b. A single noncomplementary pair nonetheless forces an empty column

Choose the lower frame \((\cos t,\sin t)=(3/5,4/5)\) and the **independent reflected upper** frame \((\cos s,\sin s)=(20/29,21/29)\). These two positive angles are *not* complementary. The exact inner corner data from the same actual outer supports are
\[
c^-(t)=
\left(\frac{591}{6250},\frac{1469}{3125}\right),
\qquad
c^+(s)=
\left(\frac{3827}{42050},\frac{228147}{420500}\right).
\tag{CD.14}
\]
Both abscissae are in the hull projection; the two tents overlap beyond the unit strip at their optimally aligned column by
\[
\boxed{
\max_x(T^-_t(x)+T^+_s(x))-1
=\frac{2431}{262500}>0.
}\tag{CD.15}
\]
The exact lower-corner and upper-corner mismatch penalty is \(37312/11038125\). Thus every body navigating these two poses must have an **empty horizontal interval** near that column, contradicting connectedness together with the proposed actual hull \(H\).

The obstruction is not an extreme vertex collision: at each **separate** pose all six hull vertices have a strict safety margin, at least \(18/625>0\) and \(1053/14500>0\) respectively. Each individually carved **single-pose** envelope separately retains the hull and has nonempty connected interval fibers over the full projection; the rational maximum of (forbidden tent roof minus reflected or actual outer roof) is respectively
\[
-\frac{10581061}{21475000}<0,\qquad
-\frac{65405631}{145282750}<0.
\]
**Only combining the two noncomplementary corner tents destroys a full fiber.**

This is a precise **independence theorem**: the whole continuum of perpendicular-width conditions CD.5 (not merely DU2 at \(45^\circ\)) plus individually safe selected corner placements does **not** guarantee joint two-handed corner compatibility. The general unequal-angle packing inequalities [CP1](two-moving-corner-packing.md) carry genuinely additional constraints on a hypothetical competitive-size hull.

## 5. Implication for a sharp area proof

CD.7 gives a continuum of necessary constraints purely on the **outer hull's perpendicular directional widths** for every above-\(M\) original competitor, including partial turns. CP1 then supplies strictly stronger unequal-angle constraints coupling the two moving sharp corners. They are useful for exact global support-data pruning **before** integrating any forbidden niche area.

But the known Romik candidate has a strictly sub-half-height whole-angle corner ceiling (less than \(13/30\)), so these nonpinching constraints are **not active at its reference solution**. Neither CD1 nor CP1 alone can supply a sharp area upper bound. Closing optimality still requires an ordinary-area bound that accounts for the full union of the **inner-wall ray envelopes**, in terms of the outer-wall contact curves. We have **not** proved this globally or removed the independent partial-turn optimization. No CI, Lean/Lake compilation or claimed larger sofa is involved.
