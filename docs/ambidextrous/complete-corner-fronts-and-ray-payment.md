# Complete inner-corner sweep by horizontal fronts: a global formula and an exact Romik ray-payment

**Date:** October 8, 2026. **Research status:** A universal, nonconvex **ordinary-area** construction from the user's suggested **outer-wall contacts and moving sharp inner corner**. It requires no imposed curvature cap, reflection symmetry, one-peak angular profile, contact order, exposed-corner assumption, or full-quarter completion of a partial motion. It (i) decomposes the *entire continuous inner-wall sweep* into its actual horizontal connected components, not just sampled angles, (ii) proves a global lower bound on removed area from vertical projections of the actual corner path, (iii) gives a further explicit **positive inner-ray surcharge** that must not be discarded, and (iv) evaluates the corner-shadow area of Romik's reference in a genuinely **closed analytic form**.

**This does not prove** Romik's unrestricted optimality. It shows in exact ordinary area why the moving **corner trajectory by itself** is not sufficient: at Romik, the inner-wall rays remove more than \(729/40000\) additional area **per handed turn** outside every vertical corner shadow, and the true additional amount is about \(0.03844029048\) per turn. No unproved full/partial completion, convexification of the sofa, or \(G\)-inequality is used.

Related existing results: [OC](outer-wall-and-moving-corner-first.md) establishes the corner and individual tent formulas; [DC2](pr7-double-crossing-area-transfer.md) handles horizontal-slice connectivity **only under a single-peak angular hypothesis**; [SR1](curvature-only-signed-roof.md) handles signed niche area **under curvature domination**; [FV1](full-turn-unconstrained-envelope-variation.md) permits disconnected full-turn envelopes for global variational comparisons. The construction here is an **unconditional geometric area identity**, with exact components even when the superlevel angle set has arbitrarily many components. It does not claim these familiar coarea/Fubini principles to be inventions.

## 1. The outer support fixes the moving corner and its attached inner rays

Let \(K\subset\mathbb R\times[0,H]\) be any nonempty compact convex hull, \(0<H\le1\), with horizontal projection \(I\). Let \(T_-\subset(0,\pi/2)\) be a **visited lower-turn angle interval**, not assumed to be a complete quarter. Write
\[
u_t=(\cos t,\sin t),\quad v_t=(-\sin t,\cos t),\quad
c^-(t)=(h_K(u_t)-1)u_t+(h_K(v_t)-1)v_t
       =(\xi_t,\eta_t).
\tag{CF.1}
\]
Its open forbidden quadrant is exactly
\[
Q_t^-=
\{(x,y):y<\eta_t-\tan t\,(\xi_t-x)_+
                         -\cot t\,(x-\xi_t)_+\}.
\]
For a *fixed horizontal height \(y\)*, the quadrant section is empty when \(y\ge\eta_t\), and otherwise is the **open interval**
\[
\boxed{
(Q_t^-)_y=
\bigl(\,\xi_t-(\eta_t-y)\cot t,\
       \xi_t+(\eta_t-y)\tan t\,\bigr)
\quad(y<\eta_t).
}\tag{CF.2}
\]
For the upper-handed turn, reflect the proposed hull through the horizontal midline,
\(\rho_H(x,y)=(x,H-y)\), apply exactly the same formulas to \(\rho_HK\) with its independently visited positive angle interval \(T_+\), and reflect the resulting forbidden sweep back. The two turning histories are not coupled by an assumed common rotation angle.

The horizontal slice of the outer convex hull itself is the compact interval \(K_y=[L_K(y),R_K(y)]\), possibly a singleton.

## 2. Universal horizontal-front decomposition, with **arbitrary** angular topology

For any \(0<y<H\), let
\[
\mathcal T_y=\{t\in T_-:\eta_t>y\}.
\tag{CF.3}
\]
Because the actual support function and corner path are continuous, this is open in the angular interval. It is a **countable disjoint union of open intervals** \(\mathcal T_y=\bigcup_j J_j(y)\), with no one-peak or finite-switch assumption.

For each connected component \(J=J_j(y)\), define
\[
\boxed{\begin{aligned}
\ell_J(y)&=\inf_{t\in J}
  [\xi_t-(\eta_t-y)\cot t],\\
r_J(y)&=\sup_{t\in J}
  [\xi_t+(\eta_t-y)\tan t].
\end{aligned}}\tag{CF.4}
\]

**Theorem CF1 (all-topology front formula).** For **every** compact convex \(K\) and every continuous conventional visited turning interval, the whole-continuum forbidden sweep \(W_-=\bigcup_{t\in T_-}Q_t^-\) has section
\[
\boxed{
(W_-)_y=\bigcup_{j}(\ell_{J_j(y)}(y),r_{J_j(y)}(y)).
}\tag{CF.5}
\]
Intervals from different angular components may themselves overlap or connect and must be merged as a **set union**, not added with multiplicity. With \(W_+\) the reflected opposite-handed sweep, its complete **ordinary removed area inside the actual proposed hull** is
\[
\boxed{
|K\cap(W_-\cup W_+)|
=\int_0^H
\left|K_y\cap\Big((W_-)_y\cup(W_+)_y\Big)\right|\,dy.
}\tag{CF.6}
\]
Consequently the ordinary two-sweep **canonical envelope** has area
\[
|K\setminus(W_-\cup W_+)|
=|K|-\int_0^H\left|K_y\cap((W_-)_y\cup(W_+)_y)\right|dy.
\tag{CF.7}
\]
For original **partial** motions the separate whole-body outgoing-strip constraints must still be intersected with this angular envelope; this can only decrease surviving ordinary area. CF.7 is not an unearned full-turn completion.

**Proof.** At height \(y\), every \(t\in\mathcal T_y\) contributes the nonempty open interval CF.2. As \(t\) varies inside one component \(J\), the two endpoints vary **continuously**; the interval has positive length, so nearby intervals intersect. A union of a connected continuously varying family of nonempty intervals with local overlap is a connected open set of the real line, hence a single open interval. Its left and right endpoints are exactly the infimum and supremum in CF.4. Taking the union over components proves CF.5.

The angular sweep is a union of open subsets of the plane and hence measurable. The outer hull is measurable, and the standard section form of Fubini gives CF.6. The ordinary set subtraction identity gives CF.7. **No convexity of the surviving sofa and no absence of clipped rays is assumed.** \(\square\)

This removes the **single-component/one-peak premise** of the older DC2 front formula, at the price of retaining the countable interval union whenever multiple components are genuinely present.

## 3. A universal **vertical moving-corner shadow**, valid before tracing the ray flanks

Define the **vertical corner shadow** below the actual inner-corner trajectory
\[
\boxed{
\mathcal C_-=
\{(\xi_t,y):t\in T_-,\ 0\le y<\eta_t\}.
}\tag{CF.8}
\]
At the same \(x=\xi_t\), the vector from the moving corner to the shadow point is exactly \((\xi_t,y)-c^-(t)=(0,y-\eta_t)\). Its two inner-wall normal differences are
\[
((\xi_t,y)-c^-(t))\cdot u_t=(y-\eta_t)\sin t<0,\qquad
((\xi_t,y)-c^-(t))\cdot v_t=(y-\eta_t)\cos t<0.
\] Thus **every point of the vertical corner shadow lies inside an actual open inner forbidden quadrant**:
\[
\boxed{\mathcal C_-\subseteq W_- .}\tag{CF.9}
\]
In particular every genuine sofa \(S\subseteq K\) satisfying the visited lower and upper canonical hallways obeys
\[
\boxed{
|S|\le |K|-
\bigl|K\cap(\mathcal C_-\cup\rho_H\mathcal C_+)\bigr|.
}\tag{CF.10}
\]
This is a *single joint ordinary-area upper bound* determined solely by the two forced corner trajectories and the outer hull, without separately adding two overlapping niche deficits. It remains a valid **upper relaxation**, generally strict because the attached **inner rays** remove additional area outside the vertical corner shadow.

The shadow's exact horizontal slice is the continuous-image set
\[
\boxed{
(\mathcal C_-)_y=\{\xi_t:t\in\mathcal T_y\}
=\bigcup_j \xi(J_j(y)).
}\tag{CF.11}
\]
Each connected angular component gives a single **horizontal interval of corner abscissae**. This yields a computable area lower bound for the full niche
\[
\boxed{
|K\cap W_-|\ge
\int_0^H
\left|K_y\cap\bigcup_j\xi(J_j(y))\right|dy.
}\tag{CF.12}
\]
It remains valid even when some corner arcs fold back horizontally, have infinitely many switches, or never expose the full niche boundary.

**General monotone-arc corollary.** If on an interval \([a,b]\subset T_-\) the abscissa \(\xi_t\) is strictly monotone, the ordinate \(\eta_t\) is nonnegative, and the entire downward corner graph \(\{(\xi_t,y):0\le y\le\eta_t\}\) lies inside \(K\), then that single arc alone forces ordinary removed area at least
\[
\boxed{
\int_a^b \eta_t\,|\xi_t'|\,dt.
}\tag{CF.13}
\]
This follows by the **injective** coordinate change \(x=\xi_t\), not by falsely counting area with multiplicity. It is a directly usable **quadratic corner-path integral in the outer supports and their first derivatives**; proving this lower bound does *not* require that the corner arc is an *exposed maximizer* of the full forbidden roof.

## 4. A universal explicit **ray-flank surcharge** beyond every corner shadow

The user specifically wanted the **outer wall and sharp corner first**, followed by the full inner-wall carving. The next lemma accounts for an actual positive portion that CF.10 misses.

Write
\[
X_-=\inf_{t\in T_-}\xi_t,\qquad
X_+=\sup_{t\in T_-}\xi_t.
\]
These may be finite for every compact interior angular family; for the complete conventional quarter they are finite by continuity of \(c_K\) on the closed angular interval.

Choose one **actually visited** angle \(t_0\in T_-\) with corner \((\xi,\eta)\), \(\eta>0\), and suppose that the full physical one-angle forbidden-triangle **bounding rectangle**
\[
\boxed{
[\xi-\eta\cot t_0,\xi+\eta\tan t_0]\times[0,\eta]
\subseteq K.
}\tag{CF.14}
\]
This is a *sufficient* nonclipping hypothesis, verified for Romik's reference below; it is not assumed for arbitrary hulls.

Define
\[
d_L=\bigl(\eta\cot t_0-(\xi-X_-)\bigr)_+,\qquad
d_R=\bigl(\eta\tan t_0-(X_+-\xi)\bigr)_+.
\tag{CF.15}
\]

**Theorem CF2 (outer-ray payment).** Under CF.14,
\[
\boxed{
|K\cap W_-|
\ge|K\cap\mathcal C_-|
+\frac{d_L^2}{2\cot t_0}
+\frac{d_R^2}{2\tan t_0}.
}\tag{CF.16}
\]

**Proof.** By CF.11 the entire corner shadow lies above horizontal abscissae in \([X_-,X_+]\). At angle \(t_0\), the forbidden horizontal interval at height \(y\) extends to the left to
\(\xi-(\eta-y)\cot t_0\) and to the right to \(\xi+(\eta-y)\tan t_0\), for \(0\le y<\eta\). Its portions *outside* \([X_-,X_+]\) are disjoint from the entire corner shadow; by CF.14 they remain **inside the actual convex hull**. The left excess width at height \(y\) is precisely \((d_L-y\cot t_0)_+\), the right excess is \((d_R-y\tan t_0)_+\). Integrating these **two distinct ordinary-area triangles** gives \(d_L^2/(2\cot t_0)\) and \(d_R^2/(2\tan t_0)\). They are part of \(K\cap W_-\) but not \(K\cap\mathcal C_-\), establishing CF.16. \(\square\)

For arbitrary clipped hulls one may instead integrate the **actual intersection** of these two explicit ray triangles with \(K_y\), retaining exactly the same disjointness. The fully contained formula CF.16 is written separately to avoid making a false global nonclipping claim.

## 5. A **closed exact integral formula** for Romik's vertical corner shadow

Use Romik's horizontally centered and vertically symmetric one-turn reference outer cap. Put
\[
Y>0,\quad4Y^3+3Y-1=0,\qquad
\beta=\arctan Y,\quad m=\frac1{3\sin\beta},\quad
R=\frac{\cos\beta}{\sin(3\beta/2+\pi/8)},\quad L=\pi/2.
\tag{CF.17}
\]
The explicit reference upper support is [RH.2](romik-horizontal-misalignment-sharp-bound.md). Its lower inner-corner path \(c_*(t)=(\xi(t),\eta(t))\) is
\[
(\xi,\eta)=
\begin{cases}
\left(m-\frac{3m}{2}\sin^2t-\cos t+\frac12\sin t,\ 
\frac{3m}{2}\sin t\cos t+\frac12-\sin t-\frac12\cos t\right),
&0\le t\le\beta,\\[4pt]
\left(R\cos(3t/2+\pi/8)+\sin t-\cos t,\ 
R\sin(3t/2+\pi/8)+\frac12-\sin t-\cos t\right),
&\beta\le t\le L-\beta,\\
(-\xi(L-t),\,\eta(L-t)),
&L-\beta\le t\le L.
\end{cases}\tag{CF.18}
\]

The established [double-crossing theorem DC1](pr7-double-crossing-area-transfer.md) proves that \(\eta(t)\) increases strictly from zero to its maximum
\[
H_*=\eta(L/2)=R+\frac12-\sqrt2
\]
at \(L/2=\pi/4\), then decreases symmetrically to zero. The first-phase derivative satisfies
\[
\xi'(t)=-3m\sin t\cos t+\sin t+\frac12\cos t,
\quad
\xi''(t)=-3m\cos2t+\cos t-\frac12\sin t<0
\quad(0\le t\le\beta),
\tag{CF.19}
\]
since \(m>1,\ \beta<3/10,\ \cos(2\beta)>4/5\). At \(t=0\), \(\xi'(0)=1/2>0\); at \(t=\beta\), because \(3m\sin\beta=1\),
\[
\xi'(\beta)=\sin\beta-\frac12\cos\beta
=\cos\beta(Y-1/2)<0.
\]
Thus there is **one unique** \(\tau\in(0,\beta)\) with \(\xi'(\tau)=0\). On the reference middle arc \(p=f'-g+1\le0\le q=g'+f-1\) and
\(\xi'=p\cos t-q\sin t<0\) from \(\beta\) to \(L/2\). Reflection gives the entire horizontal path: it increases to the unique global maximum \(X_*=\xi(\tau)\), decreases to its negative, then rises toward the final endpoint.

At a height \(0<y<H_*\), the set \(\{t:\eta(t)>y\}\) is a *single angle interval* symmetric about \(\pi/4\). Therefore its corner projection is exactly \([-X(y),X(y)]\), with
\[
X(y)=
\begin{cases}
X_* ,&0<y\le\eta(\tau),\\
\xi(t_y),&\eta(\tau)<y<H_*,\quad\eta(t_y)=y,\quad t_y\in(\tau,\pi/4).
\end{cases}
\]
The full vertical corner shadow lies inside the reference's common central rectangle \([-m/2,m/2]\times[0,1]\). Its **entire actual ordinary area, per hand**, is exactly
\[
\boxed{
\mathscr C_*=
2\int_0^{H_*}X(y)\,dy
=-2\int_{\tau}^{\pi/4}\eta(t)\xi'(t)\,dt.
}\tag{CF.20}
\]
This is an **area formula for a genuine continuum of inner-corner positions**, not a discrete-angle proxy and not a false assertion that all moving corners are exposed niche boundary points.

### Closed elementary antiderivatives — no numerical integration is required

Set \(A=3m/2\). On \(0\le t\le\beta\), define
\[
\begin{aligned}
F_1(t)={}&A^2\left(\frac t4-\frac{\sin4t}{16}\right)
-A\sin^3t+\frac A2\cos^3t
+\frac{5t}{8}-\frac{3\sin2t}{16}
-\frac{\cos2t}{4}\\
&-\frac A4\cos2t+\frac{\cos t}{2}-\frac{\sin t}{4}.
\end{aligned}
\tag{CF.21}
\]
On \(\beta\le t\le\pi/4\), define
\[
\begin{aligned}
F_2(t)={}&\left(\frac{3R^2}{4}+1\right)t
-\frac{R^2}{4}\sin(3t+\pi/4)
+\frac{\sqrt2R}{2}\cos(5t/2-\pi/8)\\
&+\frac{5\sqrt2R}{2}\cos(t/2+3\pi/8)
-\frac12\cos2t
-\frac R2\cos(3t/2+\pi/8)
+\frac{\cos t-\sin t}{2}.
\end{aligned}\tag{CF.22}
\]
Direct trigonometric differentiation gives
\(F_1'(t)=-\eta(t)\xi'(t)\) on the first phase, and
\(F_2'(t)=-\eta(t)\xi'(t)\) on the middle phase. Hence the **closed exact expression** is
\[
\boxed{
\mathscr C_*
=2\bigl[F_1(\beta)-F_1(\tau)
       +F_2(\pi/4)-F_2(\beta)\bigr].
}\tag{CF.23}
\]
The parameter \(\tau=\arctan z\) is itself exactly specified by the **positive** root in \((0,\tan\beta)\) of
\[
(2z+1)^2(1+z^2)=36m^2 z^2,\qquad
(2z+1)\sqrt{1+z^2}=6mz,
\tag{CF.24}
\]
with the positive unsquared sign retained. Thus CF.23 contains **only algebraic numbers, trigonometric functions of algebraically defined angles, and their inverse-angle values**; it is not a numerically sampled niche estimate.

For orientation, direct high-precision evaluation of the displayed exact formulas gives
\[
\tau\approx0.2029888005710,\quad
X_*\approx0.2172340410702,\quad
\boxed{\mathscr C_*\approx0.1457529066040}.
\tag{CF.25, numerical diagnostic}
\]

## 6. At Romik the **inner-wall rays must remove substantial extra area**

Here is a **completely rational strict lower bound**, independent of the numerical CF.25 diagnostic.

The exact reference bounds in [RH.3](romik-horizontal-misalignment-sharp-bound.md) give \(29/25<m<117/100\), \(\beta<3/10\), and \(R>32/25\). Also \(\cos t>19/20\) on \([0,\beta]\), since
\(\cos\beta\ge1-\beta^2/2>191/200>19/20\). On this first phase, CF.18 and \(1-\cos t=\sin^2t/(1+\cos t)\) show
\[
\begin{aligned}
\xi(t)
&=m-1+\frac12\sin t
-\left(\frac{3m}{2}-\frac1{1+\cos t}\right)\sin^2t\\
&<\frac{17}{100}+\frac12\sin t-\frac65\sin^2t\\
&\le\frac{17}{100}+\frac5{96}
=\frac{533}{2400}<\frac9{40}.
\end{aligned}\tag{CF.26}
\]
The coefficient \(3m/2-20/39>6/5\) is a direct rational comparison. On the reference middle arc \(\xi\) is strictly decreasing from \(\xi(\beta)\) to zero, and reflection bounds the last arc. Therefore
\[
\boxed{X_*=\max_{0\le t\le\pi/2}|\xi(t)|<9/40.}\tag{CF.27}
\]
Moreover \(\sqrt2<71/50\) and \(R>32/25\) give
\[
\boxed{H_*=R+1/2-\sqrt2>9/25.}\tag{CF.28}
\]

At \(t=\pi/4\), the actual forbidden interval at height \(0\le y<H_*\) is simply
\[
\boxed{(-(H_*-y),\,H_*-y).}\tag{CF.29}
\]
For every \(0\le y<H_*-X_*\), the fixed-angle interval extends **beyond the entire corner-shadow projection \([-X(y),X(y)]\subseteq[-X_*,X_*]\)** by at least \(H_*-X_*-y\) on **each** side. All this material is inside the reference common rectangle because \(H_*<1/2<m/2\); thus no outer-hull clipping can destroy it.

Apply CF2 with \(t_0=\pi/4,\ \xi=0,\ X_-=-X_*,X_+=X_*\). The resulting **additional ordinary removed area per handed turn** is at least
\[
\boxed{
|K_*\cap W_-|-\mathscr C_*
\ge(H_*-X_*)^2
>\left(\frac9{25}-\frac9{40}\right)^2
=\frac{729}{40000}.
}\tag{CF.30}
\]
The opposite upper-handed turn is its reflection. The two complete reference niches are vertically separated because \(H_*<1/2\). Therefore the total **ray-only surcharge beyond both corner shadows** is strictly larger than
\[
\boxed{\frac{729}{20000}=0.03645.}\tag{CF.31}
\]

For quantitative context, Romik's known full surviving area is
\(M=1+4Y^2+\arctan Y\). His reference downward outer cap has exact area
\[
|U_*|=\frac12\int_0^{\pi/2}
\bigl(f^2-f'^2+g^2-g'^2\bigr)dt,
\qquad |K_*|=2|U_*|-2m,
\]
and the true **per-handed niche** is
\(N_*=(|K_*|-M)/2\).
Evaluating those elementary exact support integrals gives
\[
\begin{aligned}
|K_*|&\approx2.013341612603,\\
N_*&\approx0.184193197089,\\
\mathscr C_*&\approx0.145752906604,\\
N_*-\mathscr C_*&\approx0.038440290485.
\end{aligned}
\tag{CF.32, numerical diagnostics}
\]
Thus **about 79.1%** of each *complete* reference niche is forced simply by the moving corner's vertical shadow, while **about 20.9%** comes from the attached ray-envelope flanks. The rigorous positive lower bound CF.30–CF.31 does **not** rely on these decimals.

In particular define the *corner-shadow-only area majorant*
\[
\mathcal B_{\rm corner}(K_*)=|K_*|-2\mathscr C_*.
\]
Then
\[
\boxed{
\mathcal B_{\rm corner}(K_*)-M
=2(N_*-\mathscr C_*)
>\frac{729}{20000}>0.
}\tag{CF.33}
\]
This is a decisive **negative control**: a proposed globally sharp calibration which counts *only vertical corner trajectories*, even for perfectly regular symmetric supports, already **fails to attain equality at Romik**. The **full attached inner-wall ray envelopes** must be quantitatively charged. The correct user's outer-wall/corner-first strategy must include *both* contributions, not return to corner points alone.

## 7. The corner's height superlevels genuinely disconnect on **fully feasible, saturated** sofas

The arbitrary-angular-component clause of CF1 is **not** a technical generality needed only for nonsensical support data. The following rational six-vertex body shows that the moving-corner **height itself need not have one peak**, even for a compact connected full-two-turn sofa with its **actual** convex hull retained.

Let
\[
\boxed{
K_{\rm mp}=\operatorname{conv}\left\{
\begin{array}{lll}
(-7761/10000,\ 1/2),&(-141/1000,\ 0),&
(7761/10000,\ 1/2),\\
(6409/10000,\ 8956/10000),&
(439/10000,\ 1),&
(-5523/10000,\ 8306/10000)
\end{array}\right\}.
}\tag{CF.34}
\]
The listed vertices are in counterclockwise order with all six successive determinants positive. Its horizontal width is \(W=7761/5000\), vertical span exactly one, and it contains the entire segment \([-W/2,W/2]\times\{1/2\}\).

**Whole-angle midline survival.** For *every* lower-turn angle, use the bounding rectangle \([-W/2,W/2]\times[0,1]\) to estimate the height of the actual inner corner:
\[
\eta_K(t)
\le W\sin t\cos t+1-\sin t-\cos t.
\]
Writing \(z=\sin t+\cos t\in[1,\sqrt2]\), the right side is
\[
\frac W2(z^2-1)+1-z,
\]
a convex quadratic in \(z\). Its maximum on this interval is
\(\max\{0,1+W/2-\sqrt2\}<1/2\), because the **exact rational inequality**
\((W+1)^2<8\) is true. The same bound holds after vertically reflecting the hull. Therefore neither complete forbidden sweep reaches the midline at *any* x. Since that midline segment lies in \(K_{\rm mp}\), the canonical two-handed envelope
\[
S_{\rm mp}=E_{\rm full}(K_{\rm mp})
\]
has nonempty interval fibers for its **full** horizontal projection, all meeting the same midline. It is compact, connected and completes both full conventional quarter turns.

**Its actual hull is retained at every corner.** For each of the six vertices, check its support depths in every lower and vertically reflected upper frame. The exact rational [checker](computer-assisted/check_multipeak_fullturn_corner.py) evaluates, at all \(q=k/1024\), the perpendicular unit normals
\[
u_q=\left(\frac{1-q^2}{1+q^2},\frac{2q}{1+q^2}\right),
\qquad v_q=(-u_{q,y},u_{q,x}).
\]
The largest \(\min(\text{two support depths})\) over **all vertices and samples** is exactly
\[
\frac{159570959}{164440625}
\quad\text{(lower turn)},\qquad
\frac{3847331}{4181690}
\quad\text{(vertically reflected upper turn)}.
\tag{CF.35}
\]
Since \(W^2+1<4\), the polygon's diameter is **strictly less than two**. Each support-depth function, hence its minimum at a fixed vertex, is therefore 2-Lipschitz in turning angle. Every real angle in \([0,\pi/2]\) is within \(1/1024\) of a rational sample (use \(t=2\arctan q\) and \(dt/dq\le2\)). Both displayed exact rational maxima plus \(2/1024\) remain **strictly below one**. Therefore all six extreme vertices survive the **whole angular continuum of both complete turns**, proving
\[
\boxed{\operatorname{conv}S_{\rm mp}=K_{\rm mp}.}\tag{CF.36}
\]
This is a genuine sofa with **its own** hull, not merely an auxiliary support profile.

**Its positive corner heights have separated peaks.** At the three rational half-angle parameters \(q=k/32\), \(k=15,17,18\), direct support maxima give
\[
\boxed{
\begin{aligned}
\eta_{K_{\rm mp}}(2\arctan(15/32))
&=\frac{369409793}{7800005000}>\frac{43}{1000},\\
\eta_{K_{\rm mp}}(2\arctan(17/32))
&=\frac{87276483}{2154961250}<\frac{43}{1000},\\
\eta_{K_{\rm mp}}(2\arctan(18/32))
&=\frac{6228683}{141961250}>\frac{43}{1000}.
\end{aligned}}\tag{CF.37}
\]
By continuity, the **positive-height** superlevel set
\[
\boxed{\{t\in(0,\pi/2):\eta_{K_{\rm mp}}(t)>43/1000\}}
\tag{CF.38}
\]
has at least **two disjoint connected components**.

**Theorem CF3 (no universal one-peak reduction from actual full-turn feasibility).** The complete full-two-turn, compact connected, canonically saturated, actual-hull class does **not** imply unimodality of the moving inner corner's height, or connectedness of all its positive-height angular superlevel sets, even at exact unit incoming vertical span. Thus the all-component interval union in CF1 cannot universally be replaced by a single pair of front endpoints merely from feasibility, convexity of the **outer hull**, connectedness of the sofa, or exact horizontal-fiber survival.

This specific example has relatively small area and does **not** refute a one-peak theorem confined to globally maximizing or necessarily **area-\(>M\)** hulls. The stronger near-reference version, involving smooth support perturbations while keeping the reference outer contacts, is considered separately; it cannot be inferred from this finite-vertex example.

## 8. Next genuinely sharp inequality

CF1 is an exact universal decomposition of the entire **ordinary swept inner niche** into horizontal front components. CF2 provides a truly geometric ray surcharge over and above the corner shadow. CF.20–CF.23 give a new **explicit exact reference calibration** of the part caused by the moving corner itself, and CF.30 gives a substantial **certified strictly positive reference payment by its attached inner rays**.

To prove the actual sharp global upper bound, one would have to show that the sum of the **actual outer-area loss and the complete clipped inner-ray loss** in CF.6 is enough for *all* alternative convex outer-support/corner paths, including asymmetric configurations and the independently terminally stopped partial turns. Neither CF1 nor CF2 alone supplies this comparison.

Do **not** replace CF.6 by a sum over angular components without accounting for horizontal overlap; do **not** discard any incoming-strip or outgoing-strip condition; do **not** interpret the numerical diagnostics CF.25/CF.32 as a global area certificate. The unrestricted Romik optimum and uniqueness remain open. No CI, Lean/Lake build or long optimizer forms part of the analytic arguments.
