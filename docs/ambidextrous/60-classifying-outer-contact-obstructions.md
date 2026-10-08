# 60. A diffuse outer contact is a unit-width contact or a corner coincidence

This classifies part of the obstruction to the global curvature argument. It does not assume a smooth support function or a fixed contact pattern. Together with Note 59, it shows that ordinary single-wall coincidence cannot carry the unresolved nonatomic curvature excess.

Throughout, S is compact, K=conv(S) has nonempty interior, and the original body is feasible for the canonical hallway placements under consideration. The two angular intervals may be partial. The open forbidden sweeps are W_- and W_+, and W is their union.

## 60.1 Closed contact is attained by some quadrant

For each placement use an ordered orthonormal frame (u_t,v_t), of the appropriate handedness, and define

\[
Q_t=\{z:z\cdot u_t<h_K(u_t)-1,\ z\cdot v_t<h_K(v_t)-1\}.
\]

The frames and support values depend continuously on a compact parameter interval. Therefore

\[
\overline{\bigcup_tQ_t}=\bigcup_t\overline{Q_t}.
\tag{60.1}
\]

**Proof.** One inclusion follows from Q_t being a subset of the union. For the other, take points z_j in Q_{t_j} tending to z and pass to a convergent subsequence of the parameters. Continuity gives the two non-strict inequalities at the limit. Conversely a point satisfying both non-strict inequalities at a fixed t is approximated by subtracting epsilon(u_t+v_t), which makes both inequalities strict. QED.

Thus if an extreme point P of K touches the closure of a sweep, it touches a specific closed quadrant. It cannot lie in that quadrant's open interior, because every extreme point of conv(S) belongs to compact S (Lemma 45).

## 60.2 Regular boundary points with extreme points on both sides

Call a boundary point P regular for this argument if it has a unique outer unit normal n, is not in the relative interior of an exposed edge, and is not an endpoint of such an edge. At such a point, extreme boundary points approach P from both boundary directions, with limiting chord directions equal to the two directions of the tangent line.

To verify the extreme-point assertion, recall that any nonextreme boundary point lies in the relative interior of an exposed edge, as in Note 27. If an entire one-sided boundary neighborhood had no extreme points, it would have to lie in one such edge: different maximal edges are separated by extreme endpoints. This would make P an edge endpoint or an edge-interior point, excluded by definition. The tangent assertion is the usual one-sided secant characterization of a unique supporting line for a convex boundary, and follows equally by representing the boundary locally as the graph of a convex function differentiable at P.

These regular points account for the nonatomic curvature measure up to a null set. Indeed exposed edges contribute atoms; their endpoints are countable and have zero arclength; and points with nonunique outer normal have zero boundary arclength. Pushforward of the remaining boundary arclength by its normal is exactly the nonatomic part of the surface-area measure, up to those null sets.

## 60.3 A single active inner wall forces width one

**Theorem 110 (single-wall contact classification).** Let P be a regular point as above. Suppose, for one placement,

\[
P\cdot u=h_K(u)-1,\qquad P\cdot v<h_K(v)-1.
\tag{60.2}
\]

Then u=-n and the width of K in direction n is exactly one. The same conclusion holds with u and v exchanged.

**Proof.** The second inequality is strict, so it remains strict at all points sufficiently close to P. Extreme boundary points close to P belong to S and cannot enter Q. They must therefore satisfy z dot u >= P dot u. Choose sequences of such points approaching P from the two boundary directions. Their normalized chord directions tend to tau and -tau, where tau is tangent to the unique supporting line. Dividing the inequalities by the chord lengths gives tau dot u>=0 and -tau dot u>=0. Thus u is perpendicular to the tangent and u=+n or -n.

The choice u=n is impossible: support attainment at P gives P dot n=h_K(n), whereas (60.2) would give h_K(n)=h_K(n)-1. Therefore u=-n. Substituting P dot(-n)=-h_K(n) into (60.2) gives h_K(n)+h_K(-n)=1. QED.

The proof does not claim that the hull itself avoids the quadrant. Only nearby extreme points are used, since those are guaranteed to belong to the actual feasible body.

## 60.4 The remaining contact is exactly a corner

If neither wall in a quadrant contact is strict, both are equalities. The contact point is its canonical inner corner

\[
P=c_K(u,v)=(h_K(u)-1)u+(h_K(v)-1)v.
\tag{60.3}
\]

Combining (60.1) and Theorem 110 gives the following alternative at almost every nonatomic-curvature normal:

\[
\boxed{
P\notin\overline W,
\quad\text{or}\quad w_K(n)=1,
\quad\text{or}\quad P=c_K(u_t,v_t)\text{ for some placement}.
}
\tag{60.4}
\]

Multiple contacts are allowed; any one of the non-corner contacts supplies the width-one conclusion. The assertion does not require a unique active angle.

By Theorem 109, the width-one alternative already has no singular-continuous curvature and has absolutely continuous curvature density at most one. Hence the unresolved nonatomic excess cannot be attributed merely to a single active inner wall. Outside strictly clear outer points, it must occur among corner coincidences, apart from a curvature-null set.

This is only a classification of **outer-boundary** obstruction. A change at a clear outer point can still affect a pinching fiber elsewhere; the fiber condition in Note 58 has not been removed by this argument.

## 60.5 A blocking corner uses separated support normals

Suppose K is contained in a radius-R disk about the chosen origin, P is exposed with normal n, and P=c_K(u,v). Then

\[
|n-u|\geq\frac1{2R},\qquad |n-v|\geq\frac1{2R}.
\tag{60.5}
\]

**Proof.** Since h_K(n)=P dot n and h_K(u)-P dot u=1,

\[
1=h_K(u)-h_K(n)+P\cdot(n-u)
\leq2R|n-u|.
\]

Use the Lipschitz bound for support on the unit circle and |P|<=R. The other inequality is identical. QED.

If |w_K(n)-1|>=delta>0, the same comparison with -n gives |u+n|,|v+n|>=delta/(2R).

Thus a sufficiently narrow support perturbation near n leaves the corner of an already identified blocking quadrant unchanged: its two defining normals lie outside the window. This does **not** mean the obstruction disappears. It emphasizes that these constraints couple separated normals rather than being an omitted local derivative term.

## 60.6 Revised structural target

The new width-level lemma and classification are global statements. They narrow the nonlinear contact problem without introducing a candidate neighborhood:

- width-one diffuse contacts need no additional curvature proof;
- strict outer clearance is covered by the existing singular-density repair when its fiber condition also holds;
- the unresolved outer-contact part is localized to hull/corner coincidences and exposed-edge phenomena.

No zero-mass assertion is made for the corner-coincidence set, and no atom is excluded solely by this classification. A global argument still has to address these configurations and the remaining density bound, endpoint angles, and contact order.

Only written mathematical arguments were used. No CI, Lean/Lake compilation, numerical experiment, or computer algebra was run.
