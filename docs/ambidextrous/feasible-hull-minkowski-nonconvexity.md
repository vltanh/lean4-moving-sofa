# Exact nonconvexity of actual feasible full-turn hull supports

**Status (October 8, 2026):** An exact **global-domain negative control** on a proposed signed-area Jensen proof. Two genuine compact *convex* ambidextrous sofas, each performing both complete conventional quarter turns, with the same fixed horizontal width, unit vertical span, and four axis supports, have a Minkowski midpoint that **cannot be the actual convex hull of any full-turn sofa** in the same incoming orientation. This does not refute concavity of the signed total-fiber area on the larger space of *all* normalized convex hulls, and it is not a larger sofa.

The independently reproducible all-angle rational checker is [check_feasible_hull_minkowski_nonconvexity.py](computer-assisted/check_feasible_hull_minkowski_nonconvexity.py).

## 1. Two convex, continuously feasible input bodies

Let \(J(x,y)=(-x,y)\), and define
\[
\begin{aligned}
A&=(-3/4,319/500),&B&=(-1493/10000,0),\\
C&=(3/4,409/500),&D&=(161/2500,1),\\
P&=\operatorname{conv}\{A,B,C,D\}.
\end{aligned}\tag{FH.1}
\]
The vertices are counterclockwise with strictly positive successive cross products, so \(P\) is a convex quadrilateral, connected and compact. Its horizontal projection is \([-3/4,3/4]\), vertical projection \([0,1]\), and the exact shoelace area is
\[
\boxed{|P|=730767/1000000.}\tag{FH.2}
\]

For \(t\in[0,\pi/2]\), put \(u_t=(\cos t,\sin t)\), \(v_t=(-\sin t,\cos t)\), and
\[
d_P(t)=\max_{p\in P}\min\{h_P(u_t)-p\cdot u_t,\ h_P(v_t)-p\cdot v_t\}.
\tag{FH.3}
\]
The canonical supporting lower-turn hallway contains \(P\) exactly when \(d_P(t)\le1\). The upper-handed version is equivalent, by vertical reflection, to the lower-turn test on \(P'=\{(x,-y):(x,y)\in P\}\).

**Exact spatial check.** For each fixed pair of orthogonal normals, any interior point of a convex polygon can be pushed in direction \(-(u+v)\) to its boundary, increasing *both* support depths because \((u+v)\cdot u=(u+v)\cdot v=1\). On an edge, the minimum of the two affine depths is piecewise affine, with its maximum at an endpoint or where the two depths cross. Therefore checking every vertex and every edge crossing gives the **exact maximum over all real points in the entire polygon**. For rational normals and vertices all these calculations are rational.

Put \(N=1024\), and for \(k=0,\ldots,N\) take
\[
u_k=\left(\frac{N^2-k^2}{N^2+k^2},\frac{2Nk}{N^2+k^2}\right),
\qquad v_k=(-u_{k,y},u_{k,x}),\qquad t_k=2\arctan(k/N).
\]
The exact Fraction checker computes
\[
\begin{array}{c|c|c}
T&\max_k d_T(t_k)&k\text{ attaining maximum}\\\hline
P&156127/160225&50\\
P'&260569/271125&1024
\end{array}\tag{FH.4}
\]
The exact diameter bound is
\[
\operatorname{diam}(P)^2=2853/1250<4.
\tag{FH.5}
\]
For every point of a fixed compact body, support depth in a unit normal is diameter-Lipschitz in that normal. The minimum over two normals and maximum over points preserve this bound; both normals rotate at unit speed. Thus \(d_P(t)\) and \(d_{P'}(t)\) are **2-Lipschitz** in \(t\). Every \(q=\tan(t/2)\in[0,1]\) is within \(1/(2N)\) of a rational node \(k/N\), and \(2\arctan(q)\) has derivative at most two. Hence the distance to a node is at most \(1/N\) in angle, proving **for the whole real angular continuum**:
\[
\boxed{
d_P(t)\le156127/160225+2/1024<1,\qquad
d_{P'}(t)\le260569/271125+2/1024<1.
}\tag{FH.6}
\]
Support continuity yields both complete canonical motion paths, with their straight arms appended. This is a genuine convex two-full-turn sofa, not a finite-angle surrogate. Its horizontal reflection \(JP\) also completes both turns: \(J\) exchanges the ordered walls at complementary angles \(t\leftrightarrow\pi/2-t\), separately for each handedness. The two convex feasible bodies \(P,JP\) have identical supports at all four axis normals.

## 2. The averaged hull cannot be the actual hull of any feasible sofa

Set
\[
K=(P+JP)/2.
\tag{FH.7}
\]
The exact Minkowski average contains
\[
O=(0,0),\qquad
R=(3/4,91/125),\qquad
L=(-3/4,91/125).
\tag{FH.8}
\]
Indeed \(O=(B+JB)/2\), \(R=(C+JA)/2\), and \(L=JR\). Moreover \(O\) is the **unique** bottom point of \(K\): each summand's exposed bottom face is a singleton, and support faces add under Minkowski sums.

At the rational orthonormal pair
\[
u=(3/5,4/5),\quad v=(-4/5,3/5),
\]
its two support depths at \(O\) satisfy
\[
h_K(u)-O\cdot u\ge R\cdot u
=\boxed{2581/2500>1},\qquad
h_K(v)-O\cdot v\ge L\cdot v
=\boxed{648/625>1}.
\tag{FH.9}
\]
Thus \(O\) is strictly inside a mandatory lower-turn forbidden quadrant for the *support-tightened* hallway of \(K\).

If a compact sofa \(S\) had \(\operatorname{conv}S=K\), then \(O\) would necessarily belong to \(S\), since it is the unique lowest hull point (equivalently every extreme point of the convex hull of a compact set lies in the set). Its canonical support offsets would be those of \(K\). At the mandatory rational angle the two support depths of \(O\) exceed one, so no placement with that frame can contain \(S\), by canonical support tightening. This is a contradiction.

**Theorem FH1 (nonconvexity of actual-hull admission).** Among compact connected bodies completing both conventional right-angle turns in a common incoming strip, the collection of their **actual convex hull supports** is not closed under Minkowski averaging, *even when both endpoints are convex sofas, all axis supports are fixed, and the incoming vertical span equals one*.

The assertion is stronger than the elementary fact that the convex midpoint **body itself** fails feasibility. Here the midpoint **cannot be the hull of any feasible nonconvex body either**. Saturating it by deleting its forbidden points may produce a connected two-turn body with a larger area, but its *actual hull* must differ from \(K\) because the unique lowest point is lost. No ordinary-area monotonicity, or failure thereof, is claimed.

### Quantitative loss of vertical span after mandatory saturation

The obstruction is not confined to the single point \(O\). Every vertex \(p=(x,y)\) of the input \(P\) obeys the exact wedge inequality
\[
\bigl|x+1493/10000\bigr|\le\frac65\,y.
\tag{FH.11}
\]
(The largest nontrivial ratio is \((3/4+1493/10000)/(409/500)=8993/8180<6/5\).)
By convexity, FH.11 holds throughout \(P\). Any midpoint of \(p\in P\) and \(Jq\in JP\) therefore satisfies
\[
|x_{\mathrm{mid}}|
=\frac12|p_x-q_x|
\le\frac35(p_y+q_y)
=\frac65y_{\mathrm{mid}}.
\]
Hence the entire averaged convex hull \(K\) lies in the **double cone** \(|x|\le6y/5\).

Consider any \(p=(x,y)\in K\) with \(0\le y\le1/50\). At the same rational orthogonal frame \(u=(3/5,4/5)\), \(v=(-4/5,3/5)\), FH.11 gives
\[
p\cdot u\le\frac{38}{25}y\le\frac{38}{1250},
\qquad
p\cdot v\le\frac{39}{25}y\le\frac{39}{1250}.
\]
Using the already established support witnesses in FH.9,
\[
\begin{aligned}
h_K(u)-p\cdot u&\ge
2581/2500-38/1250=\boxed{501/500>1},\\
h_K(v)-p\cdot v&\ge
648/625-39/1250=\boxed{1257/1250>1}.
\end{aligned}\tag{FH.12}
\]
Thus **every point in the entire bottom strip** \(K\cap\{y\le1/50\}\) is forbidden by one and the same full-turn frame, with uniform rational margins.

Meanwhile \(K\) contains the full vertical segment \(\{0\}\times[0,1]\), because the exposed bottom and top Minkowski faces contain respectively \((0,0)\) and \((0,1)\). At \(p=(0,1/2)\) its support depth in *any* unit normal is at most
\[
\frac34|n_x|+\frac12|n_y|\le\frac{\sqrt{13}}4<1
\]
using only \(K\subset[-3/4,3/4]\times[0,1]\). Consequently \(p\) survives **both entire turns**, so the saturated full-turn envelope \(E(K)\) is nonempty.

We have proved the **quantitative** claim
\[
\boxed{
\varnothing\ne E(K)\subset K\cap\{y>1/50\},
\qquad
\operatorname{span}_y E(K)<49/50.
}\tag{FH.13}
\]
The strict final inequality follows from compactness of \(E(K)\) and its exclusion of the closed band \(y\le1/50\), while its top never exceeds one. Thus even mandatory canonical saturation after averaging cannot preserve incoming **unit span** here. No assertion is made that \(E(K)\) itself remains connected; any connectedification from GC preserves the smaller span.

This gives a second explicit, fully rational check on the vertical-span caveat in the [HS/SEC hull-reflection program](hull-reflection-symmetrization-budget.md), now starting from an **already convex and fully feasible** source body. It is still far below competitive area and does not disprove area monotonicity of the saturated envelope.

## 3. Implication for the new signed-area strategy

A proposed Jensen proof cannot assert that Minkowski interpolation between *actual feasible hull support functions* stays in that same class, then use area optimality or Euler equations at every interpolant. FH1 supplies an exact counterexample to this indispensable convex-domain premise. One can still consider **all** normalized convex hulls and their canonical envelopes as a larger interpolation domain, or use the [raw offset variation](full-turn-unconstrained-envelope-variation.md), whose comparison is valid despite hull loss. But then the pinching and clipping terms must remain in the objective, and a sharp area theorem on that larger domain is entirely unproved.

Unlike the older [RA1](reflection-averaging-obstruction.md), which averaged nonconvex surviving sofas, this example begins with **two convex, fully feasible** bodies. It also differs from the vertical/horizontal Steiner-fiber counterexamples [US](unit-span-steiner-fiber-counterexample.md): the operation is a genuine Minkowski midpoint of **convex hull support functions**. Both inputs have area only \(730767/1000000<M\), so a convexity assertion restricted to hypothetical *competitive-area* maximizing hulls is not refuted. No CI, Lean/Lake formalization or numerical area upper-bound search forms part of this proof.
