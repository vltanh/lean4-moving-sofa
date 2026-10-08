# The precise width-two Gerver/intersection/filling construction

**Question.** Can one optimize two one-turn Gerver-type shapes in a width-two
hallway, intersect the lower- and upper-handed survivors, and remove
a central unit-height filling to obtain a sharp width-one
ambidextrous sofa?

**Answer.** There are **two exact, valid constructions** and one
fundamental nonimplication:

1. Intersecting two width-two one-turn sofas and scaling **uniformly**
   by \(1/2\) produces a width-one two-turn set (choose a connected
   component if needed). When both width-two halves are simply scaled
   Gerver sofas, this is algebraically the *same* as intersecting
   width-one Gerver sofas; widening adds no new degree of freedom.
2. Starting with genuine width-one one-turn survivors, **vertically
   filling each by a unit segment**, intersecting in a width-two
   hallway and then **eroding by the same segment** returns *exactly*
   their original width-one intersection. On the compatible
   nonempty-fiber class, the widened intersection gains exactly
   the area of a one-by-\(W\) central rectangle.
3. An **arbitrary** width-two Gerver-type sofa need not be the
   vertical filling of any feasible width-one sofa. Even if its
   set-theoretic vertical erosion is nonempty and connected,
   erosion need not preserve hallway feasibility. The explicit
   rectangle counterexample SQ shows that this failure can
   spuriously produce an area greater than Romik's \(M\).

The useful new mathematical feature is a **commutation identity**
showing exactly where the extra filled-in material comes from and
why it cannot be optimized independently of the two underlying
turning shapes. It is **not** a proof of the unrestricted
ambidextrous sharp optimum, and it does not invoke Lean or
numerical global bounds.

## 1. Scaling two width-two Gerver sofas is valid but tautological

Let \(G\) be any unit-width one-turn sofa, such as
Gerver's optimal one-turn sofa; \(2G\) is its isotropic
dilation and is feasible in a width-two hallway.
Put
\[
\rho_1(x,y)=(x,1-y),\qquad
\rho_2(x,y)=(x,2-y).
\]
For any real horizontal offset \(d\), direct set algebra gives
\[
\boxed{
\tfrac12\bigl[(2G)\cap
   \bigl(\rho_2(2G)+(2d,0)\bigr)\bigr]
= G\cap\bigl(\rho_1G+(d,0)\bigr).
}
\tag{DGL.1}
\]

Every point of the right side follows both canonical
one-turn motion families because it is in each one-turn
survivor; when the intersection is connected it is a
legitimate unit-width two-turn sofa. If it is disconnected,
one must select a connected component or invoke a separately
proved suitable gap-compression theorem. No disconnected
union is silently called one rigid connected sofa.

Equation DGL.1 proves **no advantage arises merely from scaling
Gerver to width two**. The intersection is exactly a width-one
one-turn-pair intersection in disguise.

## 2. Vertical Minkowski filling is genuinely one-way feasible

Let \(I_t=\{0\}\times[0,t]\), \(t\ge0\).
For a compact set A, point p∈A, q∈I_t,
and a unit normal n, the actual support depths satisfy
\[
\begin{aligned}
D_{A+I_t}(p+q,n)
&=D_A(p,n)+D_{I_t}(q,n),\\
0\le D_{I_t}(q,n)&\le t|n_y|\le t.
\end{aligned}
\tag{DGL.2}
\]

Consequently every inner-wall alternative safe at width one
remains safe at width \(1+t\). Incoming and outgoing
straight-strip widths also increase by at most t.
Support continuity gives genuine continuous widened
motions in the same handed directions.
Thus **every unit-width one-turn survivor**
becomes a width-\(1+t\) one-turn survivor under this
Minkowski addition, and the same is true for both turns.
This is the one-way vertical-extrusion principle SQ2.

## 3. Filling both turns, then intersecting, commutes with erosion

Suppose A and B are compact one-turn survivors written
in **the same body coordinates** with nonempty vertical
fibers consisting of closed intervals or the empty set.
For the ambidextrous application, A is the lower survivor
and B is the reflected upper survivor.
Write
\[
A_x=[a_-(x),a_+(x)],\quad
B_x=[b_-(x),b_+(x)]
\]
where these fibers are nonempty.

For any set K define its exact **Minkowski erosion**
\[
K\ominus I_t:=\{p\in\mathbb R^2:p+I_t\subseteq K\}.
\]
On each nonempty interval fiber,
\[
(A+I_t)_x=[a_-(x),a_+(x)+t],
\]
and therefore
\[
\boxed{(A+I_t)\ominus I_t=A.}\tag{DGL.3}
\]
This holds on every fiber, including degenerate point fibers;
empty fibers remain empty.

Erosion *always distributes over intersection*:
\[
(K\cap L)\ominus I_t
=(K\ominus I_t)\cap(L\ominus I_t)
\]
by the definition of set containment.
Combining this with DGL.3 gives the crucial identity
\[
\boxed{
\bigl[(A+I_t)\cap(B+I_t)\bigr]\ominus I_t
=A\cap B.
}
\tag{DGL.4}
\]

No assumption of symmetry, smoothness, curvature, face alignment,
or even nonempty original overlap is needed for this identity.

Let \(\ell(x)=\max(a_-,b_-)\) and
\(u(x)=\min(a_+,b_+)\). On an abscissa where
the two original fibers overlap (\(u\ge\ell\)),
\[
\begin{aligned}
(A\cap B)_x&=[\ell(x),u(x)],\\
\bigl((A+I_t)\cap(B+I_t)\bigr)_x
&=[\ell(x),u(x)+t].
\end{aligned}
\tag{DGL.5}
\]

Therefore, **if every original paired fiber overlaps
over their common horizontal projection \(J\) of length W**,
and both sets have projection exactly J, then
\[
\boxed{
(A+I_t)\cap(B+I_t)=(A\cap B)+I_t,
\qquad
\left|(A+I_t)\cap(B+I_t)\right|
=|A\cap B|+tW.
}
\tag{DGL.6}
\]

The area identity is simply Fubini: every nonempty vertical
fiber has length increased by exactly t. The condition holds
for the canonical complete-two-turn envelope of an *actual
compact connected sofa S whose hull has projection J*:
S has a point at every abscissa of J, hence the two one-turn
survivors have overlapping intervals at every such abscissa.

**If some fibers do not originally intersect, DGL.6 is
not true.** At a fixed x let the original signed overlap
be \(g=u-\ell<0\), even though both individual intervals
are nonempty. Then the widened intersection has length
\[
\bigl(t+g\bigr)_+,
\]
which can be positive when \(-t<g<0\), despite the original
intersection being empty. This is **ghost central filling**:
new width-two area created by filling two incompatible
one-turn slices. Erosion by I_t removes it, as DGL.4
guarantees, but simply dividing widened area by a scale
or subtracting \(tW\) **would count it incorrectly**.
This is another form of the two-turn interaction problem,
not a new free-area gain.

## 4. Why an arbitrary width-two Gerver half cannot be eroded safely

The converse of DGL.2 is false. The already certified
hand rectangle calculation
[ SQ1–SQ2 and counterexample ](double-width-fill-and-squeeze-audit.md)
supplies a particularly clear example:
\[
A_2=[0,37/20]\times[0,19/10]
\]
has both complete motions in width two, and is literally
the Minkowski sum
\[
A_2=\underbrace{[0,37/20]\times[0,9/10]}_{A_1}
+I_1.
\]
Nevertheless the eroded core \(A_1=A_2\ominus I_1\)
fails even the width-one \(45^\circ\) hallway condition.
Its area is \(333/200=1.665>M\), but it is **not**
a feasible width-one sofa.

Thus the property "width-two feasible" plus
"exactly a vertical unit-segment extrusion"
still does *not* imply that the eroded body
is width-one feasible. Any use of a scaled
width-two Gerver optimum, or of two such optima
after intersection, requires an **additional
angle-by-angle reverse-feasibility condition**.

## 5. A potentially useful width-two variational formulation

For a genuine width-one *one-turn* convex cap U of
horizontal width W whose full niche satisfies
\(N(U)\subseteq U\), its survivor
\(T_U=U\setminus N(U)\) has vertical interval
fibers over its full horizontal projection.
By DGL.2 and Fubini,
\[
|\widetilde T_U|=|T_U|+W,\qquad
\widetilde T_U=T_U+I_1.
\]

Consequently the **exact** width-penalized
one-turn objective appearing in the branch
satisfies
\[
\boxed{
\Psi(U)=|U|-|N(U)|-\frac W2
=|\widetilde T_U|-\frac{3W}{2}.
}
\tag{DGL.7}
\]

This shows what a meaningfully "expanded Gerver" problem
should optimize: **ordinary area of a reversible
width-two one-turn extrusion minus \(3W/2\)**,
not ordinary area of an arbitrary width-two one-turn sofa.
The distinction is essential: plain Gerver optimality
maximizes ordinary one-turn area, whereas the width
penalty changes the endpoint shape and selects
the Romik-type cap in the previously studied
weighted one-turn problem (subject to its written
dependency chain and independent review).

For two genuine width-one one-turn survivors with
compatible nonempty fibers, DGL.6 reads at t=1
\[
\boxed{
|E_{\rm wide}|=|E_{\rm unit}|+W.
}
\tag{DGL.8}
\]
Hence **proving the sharp width-one bound \(M\)
is exactly equivalent to proving**
\[
\boxed{
|E_{\rm wide}|\le M+W
}
\tag{DGL.9}
\]
on the subclass of width-two intersections obtained
by extruding both originally feasible width-one halves,
with complete fiber compatibility.

DGL.9 might conceivably admit a more intuitive
"central rectangle + two wings" hand proof,
but as stated it is an **equivalent unsolved inequality**,
not an independently established new bound.
The ordinary width-two Gerver theorem cannot
be substituted for DGL.9, because it optimizes
a much larger set and omits both the reversibility
constraint and the shared-width penalty.

## 6. Research decision

**Promising:** formulate a sharp overlap/area bound on the
reversibly extruded width-two class directly in the
widened corridor; the central rectangle is then an
*exact* object, not an imagined freely fillable region.

**Not promising by itself:** intersect two ordinary
scaled Gerver sofas and isotropically halve them
(DGL.1 is tautological), or erode arbitrary
width-two Gerver maximizers and assume
unit-width feasibility (the rectangle gives an
exact counterexample).

**Specific new gate:** find a geometric feature of
the \(\widetilde T_U\) and \(\widetilde T_V\)
extruded survivors ensuring the sharp inequality
DGL.9 *without* assuming their original
halves have aligned top/bottom faces. In the
existing cap variables this is precisely where
the ordinary-area clipping correction must be
paid. Failure to bound that correction is
not resolved by the larger hallway alone.

No unrestricted proof, numerical area search,
Lean formalization or CI run is claimed.
