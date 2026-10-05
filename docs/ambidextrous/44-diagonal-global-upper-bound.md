# 44. An explicit unrestricted bound from the two diagonal positions

This note changes scale: rather than assuming regularity and deriving a sharp functional, it solves a small geometric relaxation exactly. It proves the unrestricted upper bound 2sqrt(2)-1 using just the incoming strip and one diagonal position for each turn. No curvature, contact-order, symmetry, or full-quarter-endpoint hypothesis is imposed.

The ingredients are elementary rectangle sections and the previously proved angle reduction. No novelty or best-known-bound claim is made. The argument is written in full rather than relying on a numerical finite-angle optimization.

## 44.1 Diagonal coordinates turn the two hallways into a rectangle with opposite corners removed

Write T=sqrt(2), and use the orthonormal coordinates

\[
u=(x+y)/T,\qquad v=(-x+y)/T.
\]

A lower-turn hallway at angle pi/4 has upper outer bounds u<=U, v<=V, and its inner disjunction is u>=U-1 or v>=V-1. An upper-turn hallway at angle -pi/4 has lower outer bounds u>=u_0, v>=v_0, and its inner disjunction is u<=u_0+1 or v<=v_0+1. These statements follow directly by taking scalar products with the two fixed-handedness frames in Note 8.

Translate the coordinates by (u_0,v_0), and set W=U-u_0, H=V-v_0. Their intersection is

\[
D(W,H)=\{(u,v)\in[0,W]\times[0,H]:
(u\geq W-1\ \text{or}\ v\geq H-1),
\ (u\leq1\ \text{or}\ v\leq1)\}.
\tag{44.1}
\]

If either extent is negative the intersection is empty. The incoming horizontal strip of width at most one is contained in a strip

\[
J_s=\{s\leq u+v\leq s+T\}
\tag{44.2}
\]

for some s. Rotation preserves area. The original body is therefore a connected subset of D(W,H) intersect J_s whenever both diagonal angles are visited.

For canonical placements, W and H are the actual widths of the common hull in the two diagonal directions. The estimates below do not need that extra fact.

## 44.2 The largest portion of a short rectangle inside a diagonal strip

**Lemma 84 (rectangle strip estimate).** Let 0<=a<=1. A translate of the rectangle [0,1] times [0,a] has at most m(a) area in any strip of the form (44.2), where

\[
m(a)=a-\frac14(1+a-T)_+^2.
\tag{44.3}
\]

For a=1 the maximizing strip is uniquely the strip centered on the rectangle center in the u+v coordinate.

**Proof.** Under the map t=u+v, the rectangle's section density is the convolution of the indicators of [0,1] and [0,a]. It is symmetric about (1+a)/2, nondecreasing before that point, and nonincreasing afterwards: this can also be read directly as the length of [0,1] intersect [t-a,t]. Integrating this density over an interval of fixed length T is maximized by centering that interval. One verification differentiates the interval integral: its derivative is the density at the right endpoint minus the density at the left endpoint, with the indicated sign on either side of the centered position.

If 1+a<=T, the full rectangle fits and the maximum is a. Otherwise the centered strip removes two right isosceles corner triangles, each with leg (1+a-T)/2. This leg is at most a because a>T-1 and T>1. Their total area is (1+a-T)^2/4, proving (44.3). For a=1 the density is strictly increasing/decreasing on its two nonzero sides and T<2, so any nonzero shift reduces the integral. QED.

A horizontal rectangle of height b, regardless of its width, contributes at most Tb to (44.2): on each v-section the permitted u interval has length at most T.

## 44.3 Connectedness disposes of the large-rectangle exception

Exchange u and v if necessary so W>=H. If H<=1, the whole outer rectangle contributes at most TH<=T, with no need to inspect its removed corners.

If H>2, also W>2. In that case (44.1) is the disjoint union

\[
[W-1,W]\times[0,1]
\quad\text{and}\quad
[0,1]\times[H-1,H].
\tag{44.4}
\]

These two compact sets have positive separation. Every connected subset is contained in one of them, so its area is at most one. This is the one place in this estimate where bounding the total disconnected envelope would be incorrect.

It remains to consider 1<H<=2, with W>=H. Up to common boundaries, D(W,H) is the disjoint union of

\[
[0,W]\times[H-1,1],
\quad [W-1,W]\times[0,H-1],
\quad [0,1]\times[1,H].
\tag{44.5}
\]

The first rectangle has height 2-H. Each of the other two has side lengths 1 and H-1. This decomposition remains valid when W>2; when H=2 the middle rectangle is a line segment and contributes zero area.

Consequently every measurable subset of D(W,H) intersect J_s has area at most

\[
U(H)=T(2-H)+2m(H-1)
=2T-2+(2-T)H-\frac12(H-T)_+^2.
\tag{44.6}
\]

For 1<=H<=T this is increasing and ends at 4T-4. For T<=H<=2 it simplifies to

\[
\boxed{U(H)=2T-1-\frac12(2-H)^2.}
\tag{44.7}
\]

Thus its maximum on [1,2] is 2T-1, attained only at H=2. The comparison 4T-4<2T-1 is equivalent to 2T<3.

## 44.4 The unrestricted theorem

**Theorem 85 (two-diagonal upper bound).** Every compact connected ambidextrous body in the posed problem of Note 1 has

\[
\boxed{|S|\leq2\sqrt2-1.}
\tag{44.8}
\]

**Proof.** Bodies of area at most T already satisfy the bound, since T<2T-1. If |S|>T, Theorem 30 supplies correctly signed canonical monotone witnesses with endpoint magnitudes alpha,gamma in (0,pi/2]. The two-strip inequality (8.9) shows alpha,gamma>pi/4: otherwise |S|<=sec(pi/4)=T. Both diagonal positions are therefore visited. Apply the rectangle reduction and the three cases in Sections 44.2–44.3. QED.

This is an area bound for every competitor, not merely a structural theorem for maximizers. It uses neither Theorem 65 nor its regularity hypotheses, and it does not identify the optimal sofa. The exact value of this relaxation is larger than M.

## 44.5 Equality in the relaxation

**Proposition 86 (the unique diagonal equality envelope).** Equality at 2T-1 for a compact connected subset of the three-position relaxation forces, after the diagonal-coordinate translation,

\[
W=H=2,\qquad s=2-T/2,
\]

and the body is exactly

\[
E_0=\bigl([0,1]\times[1,2]\ \cup\ [1,2]\times[0,1]\bigr)
\cap\{|u+v-2|\leq T/2\}.
\tag{44.9}
\]

**Proof.** The strict inequalities in the previous cases and (44.7) force H=2. The two remaining rectangles are unit squares. Equality in their individual strip bounds requires the same strip to be centered on each square. Their u+v center coordinates are 2 and W, respectively. By the uniqueness clause of Lemma 84, W=2 and s=2-T/2.

The set E_0 consists of two positive-area convex polygons touching at (1,1). It is connected, compact and regular closed. A closed subset of it having the same area must equal it by Lemma 4. Conversely the displayed E_0 meets the two hallway and strip conditions and has area 2m(1)=2T-1. QED.

The equality shape has only been shown to satisfy these three positions. The next note tests it against an additional angle, rather than treating equality in a finite relaxation as a complete motion.

All calculations here are analytic. No CI, Lean, numerical search, or CAS was used.
