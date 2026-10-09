# Exact unit-height counterexample to Minkowski concavity of the **signed** full-two-turn sofa area

**Research status (October 9, 2026).** This is a self-contained, exact analytic **negative theorem**. It falsifies the strong hypothesis that the **signed full-two-turn area** is globally Minkowski-concave merely after fixing the incoming vertical span to one. More sharply, the failure happens along a one-dimensional family of compact **genuinely feasible**, **connected**, **canonically saturated**, full-two-turn sofas, all with **actual unit-height rectangular convex hulls**, **no clipping**, and **no empty fibers**. The result is not a sofa larger than Romik's value and does **not** falsify star-concavity *specifically anchored at Romik*. The unrestricted sharp upper bound and global star comparison remain unproved.

This removes a potential invalid shortcut from the exact [SJ1](signed-joint-convex-domain-global-value.md) signed full-turn value problem: height-one convex-hull area is Minkowski-concave, but the **signed surviving sofa area** is not. Thus one cannot finish global optimality by invoking unconstrained fixed-height signed-area Jensen/concavity together with the Romik directional derivative.

## 1. A genuine one-parameter Minkowski line of actual full-turn sofas

For \(W\in[2(\sqrt2-1),1]\), consider the convex rectangle
\[
\boxed{K_W=[-W/2,W/2]\times[0,1].}\tag{RCX.1}
\]
These hulls have **exactly** the same vertical extrema and satisfy
\[
\boxed{(1-\lambda)K_{W_0}+\lambda K_{W_1}
=K_{(1-\lambda)W_0+\lambda W_1}.}\tag{RCX.2}
\]
Their first two upper support values, for
\(u_t=(\cos t,\sin t)\), \(v_t=(-\sin t,\cos t)\), are
\[
f_W(t)=\frac W2\cos t+\sin t,\qquad
g_W(t)=\frac W2\sin t+\cos t.
\tag{RCX.3}
\]
The lower-turn inner moving corner therefore has
\[
\boxed{
\begin{aligned}
\xi_W(t)&=\frac W2\cos2t+\sin t-\cos t,\\
\eta_W(t)&=W\sin t\cos t+1-\sin t-\cos t.
\end{aligned}}\tag{RCX.4}
\]
Set \(L=\pi/2\) and \(z=\sin t+\cos t\). The corner height factors as
\[
\boxed{\eta_W(t)=(z-1)\left[\frac W2(z+1)-1\right].}\tag{RCX.5}
\]
The expression is convex as a function of \(z\in[1,\sqrt2]\). Its maximum is \(\max(0,W/2+1-\sqrt2)\), strictly less than \(1/2\) for every \(W\le1\). Therefore the **entire** lower forbidden sweep lies strictly below \(y=1/2\), and the vertically reflected upper forbidden sweep lies strictly above \(y=1/2\). The canonical full-turn envelope \(S_W=E_{\pi/2,\pi/2}(K_W)\) has **nonempty interval fibers at every horizontal coordinate**, each containing the full central midline point \((x,1/2)\). Thus \(S_W\) is compact, connected and supports both entire conventional \(90^\circ\) motions (with incoming and outgoing straight arms).

Moreover **every one of the rectangle's four vertices survives both entire turn families**. For the lower turn, the right-bottom vertex \((W/2,0)\) has first-wall support depth exactly \(\sin t\le1\), and the left-bottom vertex \((-W/2,0)\) has second-wall depth exactly \(\cos t\le1\). The corresponding upper vertices have zero depth in one outer-normal direction; vertical reflection gives the other handed turn. The same lower-angle first/second tests also protect the upper vertices (their depths are no larger than the corresponding bottom depths). Thus all four vertices are retained; therefore
\[
\boxed{\operatorname{conv}S_W=K_W.}\tag{RCX.6}
\]
These are **actual** feasible hulls, not support data whose saturation changes their hull.

## 2. The **complete continuum niche** is a reverse moving-corner graph

Put \(s=\sin t,\ c=\cos t\) and
\[
p(t)=f_W'(t)-g_W(t)+1=1-Ws>0,\qquad
q(t)=g_W'(t)+f_W(t)-1=Wc-1<0
\]
for \(0<W<1\) and \(0<t<L\). Their endpoint limits are nonnegative/nonpositive at \(W=1\).

The moving corner's horizontal derivative is
\[
\boxed{\xi_W'(t)=c+s-2Wsc>0,}\tag{RCX.7}
\]
since \(2Wsc\le2sc\le1<c+s\) in the interior. Its endpoint values are
\[
\xi_W(0)=W/2-1\le-W/2,\qquad
\xi_W(L)=1-W/2\ge W/2.
\]
Consequently every horizontal coordinate \(x\in[-W/2,W/2]\) has one and only one associated angle \(t_x\in[0,L]\) with \(\xi_W(t_x)=x\).

The two inner-wall height functions at that x are
\[
R_t(x)=1+(W/2-x)\cot t-\csc t,\qquad
D_t(x)=1+(W/2+x)\tan t-\sec t.
\tag{RCX.8}
\]
For \(x>\xi_W(t)\) their minimum is \(R_t(x)\); for \(x<\xi_W(t)\) it is \(D_t(x)\). Differentiate with t:
\[
R_t'(x)=\frac{x-(W/2-\cos t)}{\sin^2t},\qquad
D_t'(x)=\frac{x-(-W/2+\sin t)}{\cos^2t}.
\tag{RCX.9}
\]
By the corner-contact identities
\[
\xi_W-(W/2-c)=p(t)s>0,\qquad
\xi_W-(-W/2+s)=q(t)c<0,
\]
the first branch is strictly **increasing** as \(t\uparrow t_x\), while the second branch is strictly **decreasing** for \(t>t_x\). So the **actual supremum over every angle** is attained at the unique *moving two-wall corner* \(t_x\):
\[
\boxed{n_W(x)=(\eta_W(t_x))_+.}\tag{RCX.10}
\]
No frozen contact chart, sampled angle, curvature cap, or unproved corner-exposure statement is used: the derivatives prove global activity for every real angle and every x.

For \(W\in(2(\sqrt2-1),1)\), \(\eta_W(t)>0\) exactly for
\[
\boxed{t\in(t_0(W),L-t_0(W)),\qquad
\sin t_0+\cos t_0=\frac2W-1,\quad
0<t_0<\pi/4.}\tag{RCX.11}
\]
At the zeros, \(W=2/(1+\sin t_0+\cos t_0)\), giving
\[
\xi_W(t_0)=-\frac W2(\cos t_0-\sin t_0),\qquad
\xi_W(L-t_0)=+\frac W2(\cos t_0-\sin t_0).
\]
Both lie **inside** the actual rectangular projection. Hence changing variables \(x=\xi_W(t)\) gives the *exact complete-niche area*:
\[
\boxed{
N(W)=\int_{t_0(W)}^{L-t_0(W)}
\eta_W(t)\,\xi_W'(t)\,dt.
}\tag{RCX.12}
\]
The full two-hand signed area has **no clipping or pinching correction**:
\[
\boxed{\mathscr S(K_W)=|S_W|=W-2N(W).}\tag{RCX.13}
\]

## 3. Its area is **strictly convex** as \(W\uparrow1\)

Let \(A(t)=sc\), \(z(t)=s+c\). The integrand in RCX.12 is
\[
\eta_W\xi_W'
=\bigl(WA+1-z\bigr)\bigl(z-2WA\bigr).
\]
The integral over the **entire** angular quarter has a simple exact value:
\[
\boxed{
P(W):=\int_0^L\eta_W\xi_W'\,dt
=-\frac{\pi}{8}W^2+W+1-\frac\pi2.
}\tag{RCX.14}
\]
This is obtained by expanding the product and using
\(\int_0^{\pi/2}\sin^2t\cos^2t\,dt=\pi/16\); the remaining integrals are elementary. The whole-quarter integral counts the negative early and late corner heights, so it is **not** \(N(W)\) for \(W<1\).

Write \(\varepsilon=1-W\) and assume \(0<\varepsilon\le1/1000\).
The corner ordinate is
\[
\eta_W(t)=(1-\sin t)(1-\cos t)-\varepsilon\sin t\cos t.
\]
Its unique positive-height starting angle satisfies \(t_0<3\varepsilon\): at \(t=3\varepsilon\le3/1000\), the elementary inequalities
\[
1-\sin t>9/10,\qquad 1-\cos t>2t^2/5,\qquad sc\le t
\]
imply
\[
\eta_W(3\varepsilon)>
(9/10)(2/5)(3\varepsilon)^2-
\varepsilon(3\varepsilon)
=\frac6{25}\varepsilon^2>0.
\]
For \(0<t<t_0\) (and symmetrically for \(L-t_0<t<L\)),
\[
|\eta_W(t)|\le t^2/2+\varepsilon t
\le\frac{15}{2}\varepsilon^2,\qquad
0<\xi_W'(t)<2.
\]
The combined angular length of these two omitted signed tails is less than \(6\varepsilon\). Their integrand is **negative**, hence
\[
\boxed{
0\le R_N(W):=N(W)-P(W)\le90\varepsilon^3
\qquad(1-10^{-3}\le W\le1).
}\tag{RCX.15}
\]
It follows that, with the explicit quadratic
\[
Q(W):=\frac\pi4W^2-W+\pi-2,
\]
the **true connected two-turn sofa area** satisfies
\[
\boxed{|S_W|=\mathscr S(K_W)=Q(W)-2R_N(W).}\tag{RCX.16}
\]

Now choose the three **rational widths**
\[
W_-=1-\frac2{10000}=\frac{4999}{5000},\quad
W_0=1-\frac1{10000}=\frac{9999}{10000},\quad
W_+=1.
\]
Equation RCX.2 gives **exactly**
\[
K_{W_0}=\frac12(K_{W_-}+K_{W_+}).
\]
For the quadratic Q,
\[
\frac{Q(W_-)+Q(W_+)}2-Q(W_0)
=\frac\pi4\left(\frac1{10000}\right)^2.
\]
Use the nonnegativity and uniform bound RCX.15, with \(\varepsilon_-=2/10000\):
\[
\begin{aligned}
&\frac{\mathscr S(K_{W_-})+\mathscr S(K_{W_+})}{2}
-\mathscr S(K_{W_0})\\
&=\frac\pi4\left(\frac1{10000}\right)^2
-R_N(W_-)+2R_N(W_0)\\
&\ge\left(\frac\pi4-\frac{720}{10000}\right)
\frac1{10000^2}\\
&>\boxed{\frac{678}{1000}\frac1{10000^2}>0},
\end{aligned}\tag{RCX.17}
\]
where the final strict comparison uses only the elementary inequality \(\pi>3\). **This is an exact positive rationally certified midpoint-Jensen defect** for the *signed full-turn area on a Minkowski chord between actual, connected, unit-height, full-turn sofa hulls*. No numerical quadrature, approximate angles or optimization is used in the proof.

For orientation only, at the square \(W=1\),
\[
\boxed{|S_1|=\mathscr S(K_1)=\frac{5\pi}4-3\approx0.9269908.}\tag{RCX.18}
\]
This is well below Romik's candidate \(M\) and is not a competing optimal sofa.

## 4. Logical conclusion and **remaining proof target**

**Theorem RCX1 (global signed fixed-height concavity is FALSE).**
\[
\boxed{
\mathscr S\!\left(\frac12(K_{4999/5000}+K_1)\right)
<
\frac{\mathscr S(K_{4999/5000})+\mathscr S(K_1)}2.
}\tag{RCX.19}
\]
All three hulls arise from connected, genuine **both-full-turn** sofas with *actual unit-height hulls*, and all their signed and ordinary areas agree. The same calculation refutes fixed-height Minkowski concavity of the **one-turn weighted cap functional** \(\Psi(C)=|C|-|N(C)|-W(C)/2\) on its normalized cap domain: on the rectangle cap \(C_W=K_W\), \(\Psi(C_W)=W/2-N(W)\) has a strictly positive midpoint defect.

Thus a proof of sharp ambidextrous optimality **cannot** be obtained by a general fixed-height Minkowski concavity theorem plus a derivative certificate at Romik. Earlier random screens reported no negative Jensen gap because their shapes and resolutions failed to resolve this **small but exact** curvature sign change.

**Not ruled out:** the strictly weaker *star-concavity from the specific Romik hull \(K_*\)* on the fixed-height domain. Every chord in RCX.19 is between *non-Romik* rectangles. A star-concavity proof could still be possible, but it must exploit **global structure of the reference** rather than an arbitrary-pair Jensen theorem, and it still would not cover subunit-span or genuine partial-turn motions. Even global first-order stationarity at \(K_*\) does not by itself prove that star-concavity holds at finite interpolation distances.

**Proof boundary unchanged:** Neither unrestricted upper bound \(M\) nor uniqueness is established, and no above-\(M\) sofa is constructed. The result is a definite rejection of a proposed global proof step, not another near-reference class exclusion. No CI, Lean/Lake compilation, high-cost optimizer, or numeric area estimate is used as a proof premise.
