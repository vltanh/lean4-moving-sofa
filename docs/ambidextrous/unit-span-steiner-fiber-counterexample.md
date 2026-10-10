# Unit-span Steiner-fiber centering is not a full-turn reduction

**Status:** Exact negative control on a proposed *universal geometric operation*. The original connected body has incoming vertical span **exactly one** and has both complete conventional 90-degree turns. Vertically recentering its individual interval fibers, without changing their lengths, destroys the canonical full-turn feasibility inequalities **in that same incoming orientation**. This is *not* a sofa larger than Romik's, and no claim is made that the centered image cannot turn in some other incoming orientation. No Lean formalization.

The rational verifier is [check_unit_span_steiner_failure.py](computer-assisted/check_unit_span_steiner_failure.py). The remaining endpoint claims have elementary symbolic proofs below; they are not extrapolations from samples.

## 1. An actual connected two-turn body of unit span

Use incoming strip (0\le y\le1), and put
\[
A=(0,90/113),\quad B=(180/113,100/113),\quad
C=(180/113,0),\quad D=(135/113,0),
\]
\[
P=\operatorname{conv}\{A,B,C,D\},\qquad
Q=(1/2,1),\qquad
F=(1/2,90/113+1/36).
\]
Define the fixed body
\[
\boxed{S=P\cup[F,Q].}\tag{US1.1}
\]
Here ([F,Q]) is a vertical segment joining the upper edge of (P) at (x=1/2). Hence (S) is compact, connected, and has **interval vertical fibers**, horizontal projection ([0,180/113]), and exact vertical projection ([0,1]). The segment has zero ordinary area; the shoelace formula gives
\[
\boxed{|S|=|P|=11025/12769<1<M.}\tag{US1.2}
\]
It is nonconvex: its convex hull would fill some forbidden points and is not substituted for (S).

For (t\in[0,\pi/2]), let (u=(c,s)=(\cos t,\sin t)), (v=(-s,c)), and let (h) be the support of **the actual set (S)** (equivalently its convex hull). Define
\[
D_S(t)=\max_{p\in S}
\min\{h(u)-p\cdot u,\ h(v)-p\cdot v\}.\tag{US1.3}
\]
The complete supporting lower turn exists exactly when (D_S(t)\le1) at every angle. The upper turn is obtained by testing (S'=\{(x,-y):(x,y)\in S\}) in the same lower-turn formula. Translation from reflection about (y=1/2) does not change support depths.

### 1a. Exact rational certificate away from endpoints

Set (N=1024), (q_k=k/N), and
\[
u_k=\left(\frac{N^2-k^2}{N^2+k^2},
\frac{2Nk}{N^2+k^2}\right),\qquad
v_k=(-u_{k,y},u_{k,x}).
\]
All computations are rational. For (S), check (k=0,\ldots,931); for (S'), check (k=40,\ldots,931). The checker obtains
\[
\begin{array}{c|c|c}
&\max_k D(k)&k\text{ of maximum}\\\hline
S&558331328328/563365224367&412\\
S'&4563598711716/4579343959705&668
\end{array}
\]
Both maxima are **strictly below (997/1000)**. The checker takes the maximum over both convex components, namely (P) and ([F,Q]), with **the common support of all of (S)**. On each component, the minimum of two affine depths attains its maximum at an original vertex or at an edge crossing where the two depths tie. These points are evaluated *exactly*, so no sample of spatial positions is involved.

The squared diameter of the five-point support hull is (40500/12769<4). Consequently each depth, their pointwise minimum, and the maximum over (S) are (2)-Lipschitz in (t); the same holds for (S'). Since (t=2\arctan q) has derivative at most two on ([0,1]), every covered (q) is within angle (1/N) of a verified rational direction. Thus throughout
\[
0\le q\le 10/11\quad\text{for }S,\qquad
1/25\le q\le10/11\quad\text{for }S',
\]
the **continuum** maximum is at most
\[
\boxed{997/1000+2/1024=63933/64000<1.}\tag{US1.4}
\]
The cutpoints are covered because (40=\lfloor1024/25\rfloor) and (931=\lceil10240/11\rceil).

### 1b. Upper angles: an exact, unsampled one-wall partition

Suppose (q=\tan(t/2)\ge10/11). Then
\[
\tan t\ge220/21>247/26,\qquad
0\le c\le21/220.
\]
For (S), direct comparison of its five support vertices gives
\[
h_S(u)=Q\cdot u=\tfrac12c+s,\qquad
h_S(v)=A\cdot v=\tfrac{90}{113}c.
\]
If (p=(x,y)\in S) has (x\ge1/2), its first depth is
\[
(1/2-x)c+(1-y)s\le s\le1.
\]
For (x\le1/2), its second depth is at most
\[
(90/113)c+(1/2)s\le
\sqrt{(90/113)^2+1/4}<1.
\]
So (D_S(t)\le1) for the complete upper-angle tail.

For the reflected (S'), the support values in this angular range are
\[
h_{S'}(u)=(180/113)c,\qquad
h_{S'}(v)=-(90/113)c.
\]
If (x\le3/4), use (y\ge-1) to bound its second depth by
\[
3/4+(23/113)(21/220)=4782/6215<1.
\]
If (x\ge3/4), the point necessarily lies in the reflected quadrilateral, where (y\ge-100/113). Its first depth is at most
\[
100/113+(180/113-3/4)(21/220)
=96001/99440<1.
\]
Thus (D_{S'}(t)<1) on that tail as well.

### 1c. The small-angle reflected endpoint, where equality is genuine

For (S') only, let (0\le q\le1/25), so (0\le\tan t\le25/312<26/247=2/19). The reflected support in direction (v) is attained at (D'=(135/113,0)), and the **minimum** (v)-projection of the actual nonconvex body (S') is attained at (Q'=(1/2,-1)). Both assertions follow by comparing the five rational vertices; the restrictive comparison is (B'\cdot v\ge Q'\cdot v), equivalent to (\tan t\le26/247). Every point is therefore protected by the **second wall alone**, because
\[
h_{S'}(v)-p\cdot v
\le D'\cdot v-Q'\cdot v
=c-(135/113-1/2)s\le1.\tag{US1.5}
\]
This covers (t=0), at which the maximum is exactly one and a strict-grid-only argument would be invalid.

Combining US1.4 and the two analytic endpoint arguments proves **both complete turns for the same actual connected (S)**. Continuity of the canonical support hallway follows from continuity of (h_S); incoming and outgoing straight translations append at the two axis endpoints. No finite-angle surrogate is being called a feasible motion.

## 2. Vertical fiber centering loses feasibility

For a compact set with interval fibers (S_x=[b(x),a(x)]), define its centered-fiber image
\[
\mathfrak C S=\bigcup_x\{x\}\times
[-(a(x)-b(x))/2,(a(x)-b(x))/2].
\]
This operation preserves ordinary area by Fubini. It also preserves fiber connectedness in this example.

Because $P\subset S$, every centered interval of $P$ is contained in the centered interval of $S$ with the same abscissa. Thus
\[
\mathfrak C P\subseteq\mathfrak C S.
\]
Direct linear interpolation on the four edges gives the **convex** centered polygon
\[
\mathfrak C P=\operatorname{conv}\left\{
(0,0),(135/113,\pm195/452),(180/113,\pm50/113)
\right\}.
\]
At the rational unit normal pair
\[
u=(3/5,4/5),\qquad v=(-4/5,3/5)
\]
and the point in the lower-left edge
\[
z=(26640/27007,-9620/27007)\in\mathfrak C P,
\]
the two supports of (\mathfrak C P) are (h(u)=148/113) and (h(v)=0). Therefore
\[
h_{\mathfrak C P}(u)-z\cdot u
=h_{\mathfrak C P}(v)-z\cdot v
=\boxed{27084/27007>1}.\tag{US1.6}
\]
Support monotonicity and (\mathfrak C P\subseteq\mathfrak C S) make **both** depths at (z) at least this large in the centered image of the actual sofa. Hence that image violates a required canonical supporting hallway at this angle.

## 3. Scope and research consequence

**US1 (exact negative control).** Area-preserving vertical-fiber centering does **not** preserve complete supporting two-turn feasibility in the inherited incoming frame, even when the original connected body has interval fibers, exact incoming vertical span one, and genuine complete turns of both handedness.

Vertical-fiber centering enforces **up–down** reflection symmetry, not the **left–right** reflection assumed in RS2. This counterexample rules out its unconditional use as a two-cap balancing operation, not a direct application of RS2. It does **not** establish that the centered image has no other possible incoming orientation; no such statement is required to reject preservation of the original canonical constraints. It also does not rule out a special theorem at maximal-area bodies. The example has area below one, far from Romik's $M$.

No new area bound, counterexample above (M), or Lean formalization is claimed. The exact-arithmetic checker certifies the interior-angle inequalities, diameter, and offending rational support depths; the endpoint comparison and the general canonical-motion implication remain explicit pen-and-paper proof steps.

## 4. Horizontal Steiner symmetrization fails too — this time directly for left–right symmetry

The same certified full-turn body furnishes a simpler, exact obstruction to the **horizontal** Steiner operation that might otherwise reduce unrestricted competitors to the left–right symmetric class RS2.

For a body with measurable horizontal sections, replace the section at each ordinate $y$ by the **centered interval of the same one-dimensional measure**; retain a centered point if its original section is nonempty but has zero length. Denote this horizontal rearrangement by $\mathfrak H S$. Fubini gives $|\mathfrak H S|=|S|$. The operation preserves the incoming vertical projection $[0,1]$ and produces left–right reflection symmetry.

The section of $P$ at height $y$ has right endpoint $180/113$, and its left endpoint equals
\[
x_{\mathrm L}(y)=
\begin{cases}
135/113-\frac32y,&0\le y\le90/113,\\
18(y-90/113),&90/113\le y\le100/113.
\end{cases}
\]
Therefore its horizontal Steiner image is the convex pentagon
\[
\boxed{\mathfrak H P=
\operatorname{conv}\left\{
(\pm45/226,0),\
(\pm90/113,90/113),\
(0,100/113)\right\}.}\tag{US2.1}
\]
The added vertical segment $[F,Q]$ has zero horizontal-sectional measure. Thus its rearrangement merely extends the central top point vertically:
\[
\boxed{\mathfrak H S=\mathfrak H P\ \cup\
(\{0\}\times[100/113,1]).}\tag{US2.2}
\]
This is a **compact connected** unit-span body, is left–right symmetric, and has exactly the original area $11025/12769$. In particular the rearrangement fails for geometric, not connectedness or area, reasons.

At the genuine quarter-turn midpoint choose $u=(1,1)/\sqrt2$, $v=(-1,1)/\sqrt2$, and $z=(0,0)\in\mathfrak H S$. The two top vertices $(\pm90/113,90/113)$ yield
\[
h_{\mathfrak H S}(u)\ge\frac{180}{113\sqrt2},
\qquad
h_{\mathfrak H S}(v)\ge\frac{180}{113\sqrt2}.
\]
Since
\[
180^2=32400>25538=2\cdot113^2,
\]
both depths at $z$ are **strictly larger than one**:
\[
\boxed{h_{\mathfrak H S}(u)-z\cdot u>1,\qquad
h_{\mathfrak H S}(v)-z\cdot v>1.}\tag{US2.3}
\]
No placement with these fixed orthogonal normals can contain $\mathfrak H S$, by the canonical support-tightening necessity. Thus $\mathfrak H S$ cannot perform a complete conventional lower quarter turn in the inherited incoming frame. The original $S$ does perform **both** such full turns.

**US2 (exact universal-operator obstruction).** Horizontal Steiner symmetrization cannot be used as an area-preserving, complete-turn-feasibility-preserving reduction to RS2, **even with exact unit incoming span and connected vertically convex source fibers**. This also identifies the correct left–right symmetry axis: US1's vertical-fiber centering addresses up–down balance, while US2's horizontal-fiber centering addresses RS2 directly.

Neither theorem excludes a **competitive-area or maximizing-body-only** symmetrization theorem: $|S|<1$. Neither proves unrestricted Romik optimality, supplies a larger sofa, or restricts possible alternative incoming orientations of the transformed sets.
