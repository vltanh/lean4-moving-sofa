# Certified 1.65 full-turn exclusion near Romik's hull

**Exact local theorem (NL1).** Normalize Romik's convex hull \(K_*=\operatorname{conv}\Sigma\) with its horizontal projection centered on \(x=0\) and vertical span \([0,1]\). Let S be any compact full-conventional-two-turn feasible sofa in the same incoming frame, with \(0\le y\le1\) and \(K=\operatorname{conv}S\). If
\[
\boxed{d_H(K,K_*)\le7/10000,}
\]
then
\[
\boxed{|S|\le
\frac{412456005949545207}{250000000000000000}
=1.649824023798180828\ldots<33/20=1.65.}\tag{NL.1}
\]
**This is not the general full-turn bound.** It is a local ordinary-area certificate valid for *arbitrary nonsmooth, asymmetric, disconnected-fiber, point-face or clipping perturbations* satisfying the stated support-distance premise. A full-turn body with area \(>1.65\) must lie **outside** this neighborhood. Combined with the earlier analytic AW bound \(|S|<41/25=1.64\) for incoming horizontal width \(\le2\), such a counterexample must have both width \(>2\) and Hausdorff distance \(>7/10000\) from \(K_*\). Nonalignment/degenerate-face configurations remain.

The hand proof of the reduction and the deterministic integer certificate are below. The checker is self-reviewed, not Lean-kernel verified or independently refereed; no global optimizer is used. Labels NL are local.

## 1. Reference support data as exact algebraic intervals

Let \(Y\) be the positive root of \(4Y^3+3Y-1=0\), \(\beta=\arctan Y\), and
\[
m=\frac{\sqrt{1+Y^2}}{3Y},\qquad
R=\frac{\cos\beta}{\cos(3\pi/8-3\beta/2)}.
\]
For first-upper-quarter normals \(n_t=(c,s)\), \(n_t^\perp=(-s,c)\), the centered reference support values \(f_*,g_*\) are exactly
\[
(f_*,g_*)=
\begin{cases}
(mc+s/2,\;ms/2+c/2+1/2),&t\le\beta,\\
(R\cos(t/2+\pi/8)+s/2,\;
 R\sin(t/2+\pi/8)+c/2),&\beta\le t\le\pi/2-\beta,\\
(mc/2+s/2+1/2,\;ms+c/2),&t\ge\pi/2-\beta.
\end{cases}\tag{NL.2}
\]
These are Romik's explicit convex-hull supports after shifting its x-coordinate by \(1-m\). The reference hull is symmetric under \(y\mapsto1-y\), so the supports of the reflected-upper normals are \(f_*-s,g_*-c\).

For \(n=512\) and \(j=1,\ldots,511\), take
\[
c_j=\frac{n^2-j^2}{n^2+j^2},\quad
s_j=\frac{2nj}{n^2+j^2},\quad
t_j=2\arctan(j/n).
\tag{NL.3}
\]
All sampled normals are rational. The checker isolates Y by the exact polynomial signs
\[
298035818991/10^{12}<Y<298035818993/10^{12},
\]
uses positive-radical formulas with directed integer square roots and exact rational division to bound every \(f_j^*,g_j^*\), and finds
\[
1167049816544/10^{12}\le m\le1167049816555/10^{12},
\quad
1302051691595/10^{12}\le R\le1302051691636/10^{12}.
\tag{NL.4}
\]
The sine/cosine halves in the middle phase are computed algebraically from
\(\cos(t_j/2)=n/\sqrt{n^2+j^2}\), \(\sin(t_j/2)=j/\sqrt{n^2+j^2}\),
\(\sin(\pi/8)=\sqrt{2-\sqrt2}/2\),
\(\cos(\pi/8)=\sqrt{2+\sqrt2}/2\).
Phase membership is checked by exact rational comparisons of \(\tan t_j\) with the isolated Y and \(1/Y\).

## 2. True two-turn surviving area is bounded by one robust slice formula

Set \(\eta=7/10000\). Write \(Q=10^{12}\) and let \(f_j^\pm,g_j^\pm\) be directed integer support enclosures:
\(f_j^-/Q\le f_j^*\le f_j^+/Q\), likewise for g.

At each actual lower-turn sample, support-tightening moves the two outer walls to the actual support and can only weaken the inner disjunction. Every sofa point (x,y) obeys
\[
y\le\min\{(f_j^S-c_jx)/s_j,\ (g_j^S+s_jx)/c_j\},
\quad
y\ge\min\{(f_j^S-1-c_jx)/s_j,\ (g_j^S-1+s_jx)/c_j\}.
\]
Since the actual supports differ from the reference by at most \(\eta\), the upper roof is bounded by \(U(x)\), the minimum over j of the two expressions with \(f_j^+/Q+\eta,g_j^+/Q+\eta\) and 1; its forbidden-niche lower threshold is at least \(N(x)\), the maximum over j of the minimum of the two expressions with \(f_j^-/Q-\eta,g_j^-/Q-\eta\) and zero.

The reflected upper-turn supports are within \(\eta\) of \(f_j^*-s_j,g_j^*-c_j\). Their safe outer and inner walls give
\[
\max\{N(x),1-U(x)\}\le y\le
\min\{U(x),1-N(x)\}.
\]
Thus **even for asymmetric S**
\[
\boxed{|S|\le\int_{-117/100}^{117/100}
[\,2\min(U(x),1-N(x))-1\,]_+dx.}
\tag{NL.5}
\]
The x-box is valid since \(m+\eta<117/100\). No assertion of S's fiber connectedness is needed.

## 3. Exact continuum upper sum with 100,000 rational x-cells

Partition \([-117/100,117/100]\) into \(100000\) equal cells, each of length
\(23400000/Q\). Let \(X_i=Qx_i\) be the integer endpoint coordinates.
At angle j let \(D=n^2+j^2\), \(C=n^2-j^2>0\), \(T=2nj>0\), and \(E=Q\eta=700000000\).

On the entire cell \([x_i,x_{i+1}]\), a valid *upper* integer bound \(U_i\ge QU(x)\) is the minimum of Q and, over all frames, the directed ceilings
\[
\left\lceil\frac{(f_j^++E)D-CX_i}{T}\right\rceil,
\qquad
\left\lceil\frac{(g_j^++E)D+TX_{i+1}}{C}\right\rceil.
\tag{NL.6}
\]
A valid *lower* integer bound \(N_i\le QN(x)\) is the maximum of zero and, over all frames, the minima of the directed floors
\[
\left\lfloor\frac{(f_j^--E-Q)D-CX_{i+1}}{T}\right\rfloor,
\qquad
\left\lfloor\frac{(g_j^--E-Q)D+TX_i}{C}\right\rfloor.
\tag{NL.7}
\]
Endpoint choices follow directly from the monotonicities of these affine wall heights in x. Therefore every vertical slice of S over this whole cell has length at most
\[
L_i/Q,\qquad L_i=\max(0,2\min(U_i,Q-N_i)-Q).
\]
All operations are exact signed integer floors, ceilings, minimums, maximums and additions; no point sampling substitutes for a continuum bound. The finite run returns
\[
\sum_{i=0}^{99999}L_i=\boxed{70505300162315420}.
\tag{NL.8}
\]
Its upper Riemann sum is consequently **exactly**
\[
|S|\le\frac{23400000}{Q^2}\sum_iL_i
=\frac{412456005949545207}{250000000000000000}<33/20.
\]
That proves NL1, subject to checking the finite integer certificate. All Numpy integer products fit signed 64-bit bounds; Python rational operations isolate the algebraic support constants. A separate 200000-cell run returned the slightly smaller conservative upper 1.649800674720464.

## 4. What is missing for the user's global full-turn premise

The global theorem \(A_F\le33/20\) is **not** a consequence of NL1. To prove it, one must exclude the remaining compact domain of full-turn hulls of width \(>2\) and support distance \(>7/10000\) from \(K_*\). This can be attacked with a **complete exact rational** branch-and-bound over canonical hull support coordinates, using CP support-tightening, the exact *whole-hallway union per box* from the external O'Keefe method, and virtual intermediate-angle support bounds V1--V3. Every leaf must be excluded by a proved inequality or the exact area upper check. A convenient numerical local maximizer or a small partial cover does not suffice.

Alternatively, FR2 supplies a direct sufficient certificate: prove \(A_n\le33/20\) for **one** even n by a global exact computation of the n-mesh relaxation. The known finite-mesh convergence does not prove that any particular n will satisfy this bound.

Once \(A_F\le33/20\) is proved, the existing JT partial-to-full transfer gives \(\mu_A\le41543/25000=1.66172<2\sqrt2-7/6\). Both implications are rigorous under their stated dependencies; the missing globally certified full-turn upper bound has not yet been produced.

All new code/notes are under docs/ambidextrous, [skip ci]; no CI, Lean build, dependency installation or huge certificate was performed.
