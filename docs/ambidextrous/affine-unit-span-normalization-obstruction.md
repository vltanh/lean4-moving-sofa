# A sharp full-quarter rectangle test, and failure of affine unit-span normalization

**Scope.** This supplies an exact geometric negative control for the hull-reflection symmetrization program HS. A left-right reflection-symmetric convex body with vertical span below one may complete both conventional quarter turns, while the natural **area-preserving** affine normalization \( (x,y)\mapsto (h x,y/h) \) destroys its full-turn feasibility. Thus after convex-hull reflection followed by saturation loses the vertical unit span, one cannot repair the loss by that determinant-one stretching operation. The example has area below the reference and is not a counterexample to optimality. Labels AN are local.

## 1. Exact full-quarter feasibility criterion for a rectangular body

Let
\[
R_{W,h}=[-W/2,W/2]\times[0,h],
\quad 0<h\le1,\quad W\ge h.
\]
It is compact, convex, connected, and invariant under left-right reflection. The same set is also invariant under reflection across its horizontal midline \(y=h/2\).

**Theorem AN1.** This rectangle admits **both complete canonical conventional quarter turns** in a unit-width hallway if and only if
\[
\boxed{\frac W2+h\le\sqrt2.}\tag{AN.1}
\]

**Proof.** At a lower-turn angle \(t\in[0,\pi/2]\), write \(c=\cos t\), \(s=\sin t\), \(u=(c,s)\), \(v=(-s,c)\). For a point \(p=(x,y)\) of the rectangle, let \(q=x+W/2\in[0,W]\). The two canonical support depths, using the actual rectangle supports, are
\[
d_u(p)=c(W-q)+s(h-y),
\qquad d_v(p)=s q+c(h-y).
\]
The hallway inner-wall disjunction holds precisely when \(\min(d_u,d_v)\le1\). Both depths decrease as \(y\) increases, so the worst points are on the bottom edge \(y=0\).

For each interior \(t\), the first depth decreases affinely with \(q\), and the second increases affinely. Their crossing is
\[
q_*=\frac{cW+h(s-c)}{s+c}.
\]
Since \(W\ge h\), one has \(0\le q_*\le W\). Its common value is the maximum of their minimum along the edge:
\[
\boxed{\max_{p\in R_{W,h}}\min(d_u(p),d_v(p))
=\frac{Wsc+h}{s+c}.}\tag{AN.2}
\]
This extends continuously to both endpoint angles, giving the correct maximal depth \(h\).

Set \(z=s+c\in[1,\sqrt2]\), so \(sc=(z^2-1)/2\). Then the right side becomes
\[
\frac W2 z+\frac{h-W/2}{z}.
\]
Its derivative is
\(W/2-(h-W/2)/z^2\), which is nonnegative for \(z\ge1\) when \(W\ge h\). Hence its maximum is attained at \(t=\pi/4\) and equals
\[
\frac{W/2+h}{\sqrt2}.
\]
Therefore **every** lower quarter-turn hallway contains the rectangle exactly when (AN.1) holds. At \(t=0\) and \(t=\pi/2\), the required incoming/outgoing straight strips have normal vertical span \(h\le1\). The canonical support corner translates continuously, so these pointwise containments give an actual complete motion.

Reflection \(y\mapsto h-y\) exchanges the lower and upper turning conventions without changing the rectangular body. Consequently the same test is necessary and sufficient for the upper full turn. QED.

The condition is sharp; a failure of (AN.1) has an explicit witness at \(t=\pi/4\), the midpoint of the lower horizontal side. It is a pointwise forbidden-quadrant witness, not merely a width or hull-area estimate.

## 2. A determinant-one normalization that fails

Choose
\[
W=\frac95,\qquad h=\frac12,
\qquad R=[-9/10,9/10]\times[0,1/2].
\]
The original condition is
\[
\frac{W}{2}+h=\frac9{10}+\frac12=\frac75<\sqrt2,
\]
since \(49<50\) after squaring. Thus \(R\) is a genuinely **left-right symmetric body with both full turns** and actual area \(9/10\).

Now apply the area-preserving diagonal linear map
\[
T_h(x,y)=(h x,y/h).
\]
Its determinant is one, and its image has vertical span **exactly one** and horizontal width \(W'=hW=9/10\). At \(t=\pi/4\), its bottom-edge midpoint \(p=(0,0)\) has equal canonical support depths
\[
d_u(p)=d_v(p)=\frac{W'/2+1}{\sqrt2}
=\frac{29}{20\sqrt2}>1,
\]
because \(29^2=841>800\). This point lies in the open canonical forbidden quadrant. By the canonical support-tightening lemma (Note 8), no alternative translation at that orientation makes the image fit. Thus \(T_hR\) does **not** possess the required full conventional quarter turns.

**Corollary AN2.** Full-turn feasibility of an x-reflection-symmetric body with incoming vertical span \(h<1\) is not preserved by the general determinant-one vertical stretch/horizontal compression \(T_h\). The operation does preserve area and x-symmetry, but neither property compensates for the lost turning clearance.

The example is not competitive: its area \(9/10<M\), and no conclusion about an area-aware *competitive-only* normalization or a different nonaffine operation follows. It does, however, invalidate a universal normalization shortcut that would otherwise have been needed to apply the earlier unit-span symmetry theorem RS2 to the symmetrized hull envelope from HS.

## 3. Consequence for the current full-turn problem

HS supplies a positive, exact Dirichlet-energy gain for symmetrizing a convex hull, but the removed forbidden-area increment is not globally paid. Its exact double-tip-cut construction also shows that the full-turn envelope of the symmetrized hull can have **vertical span strictly below one**, so RS2 does not automatically apply.

AN2 now shows why a natural determinant-one correction to that span cannot be silently inserted. The two missing statements remain distinct:

1. An ordinary-area inequality comparing the original actual full-turn envelope with the symmetrized-hull envelope.
2. A valid sharp bound on x-symmetric full-turn envelopes with possibly subunit vertical span, or another **proved feasible** normalizing operation.

Neither is established here. The full-turn maximum remains unproved.

This is a pen-and-paper proof. A prescribed, five-second-capped rectangle-grid calculation first suggested the counterexample; the exact algebra in AN.1--AN.2 replaces that diagnostic and is the mathematical proof. No CI, Lean/Lake compilation, dependency installation, manuscript build, or large search was used.

## 4. These rectangular obstructions are all strictly subcritical

The full-turn rectangle criterion also implies a sharp area bound on this entire family:
\[
|R_{W,h}|=Wh\le2h(\sqrt2-h)
=1-2(h-1/\sqrt2)^2\le1.
\tag{AN.3}
\]
Equality occurs at \(h=1/\sqrt2,\ W=\sqrt2\), for which AN.1 is an equality and \(W\ge h\) holds.

Thus no rectangle in the range \(W\ge h\) can challenge Romik's area \(M>8/5\), despite their usefulness as exact tests of full-quarter feasibility and of proposed area-preserving normalizers. The statement does not extend to all convex or all nonconvex ambidextrous bodies; it is confined to the specified rectangles.
