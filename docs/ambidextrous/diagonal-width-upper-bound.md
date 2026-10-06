# A complementary upper bound on the width of every competitive body

The analytic width exclusion AW-W puts a maximizing body above horizontal width two. This note supplies a useful opposite bound without curvature or smoothness. The two diagonal hallway positions and connectedness imply

\[
W\leq1+2\sqrt2<4.
\]

This is not an area bound or a curvature theorem. It gives a compact width interval for an auxiliary estimate that includes repair costs.

## 1. The two actual diagonal widths cannot both exceed two

Let S be compact and connected, K=conv(S), and suppose both canonical diagonal hallway positions are feasible: the lower turn at pi/4 and the upper turn at -pi/4. Use the orthonormal coordinates

\[
u=(x+y)/\sqrt2,\qquad v=(-x+y)/\sqrt2.
\]

The lower hallway imposes upper support bounds u<=u_max and v<=v_max and the inner disjunction

\[
u\geq u_{\max}-1\quad\text{or}\quad v\geq v_{\max}-1.
\]

The upper hallway imposes lower support bounds u>=u_min,v>=v_min and the other inner disjunction

\[
u\leq u_{\min}+1\quad\text{or}\quad v\leq v_{\min}+1.
\]

These are the **actual** extrema of K, because the placements were support-tightened. Put A=u_max-u_min and B=v_max-v_min. Translate the two coordinate minima to zero. If A>2 and B>2, distributing the disjunctions shows that their intersection is exactly

\[
[A-1,A]\times[0,1]\quad\cup\quad[0,1]\times[B-1,B].
\tag{DU.1}
\]

The two rectangles have positive separation. A connected S must lie in one of them. Its actual widths in both diagonal coordinates are then at most one, contradicting A>2 and B>2. Therefore

\[
\boxed{\min\{w_K((1,1)/\sqrt2),w_K((-1,1)/\sqrt2)\}\leq2.}
\tag{DU.2}
\]

This argument is stronger than bounding the total area of the disconnected relaxation: it uses that K is the hull of the connected body, not an arbitrary larger outer set.

## 2. Convert the diagonal width to the incoming horizontal width

Assume S is contained in a horizontal strip of height at most one. Thus w_K(e_y)<=1. For the first diagonal normal n=(e_x+e_y)/sqrt(2), the identity e_x=sqrt(2)n-e_y and subadditivity of width give

\[
w_K(e_x)\leq\sqrt2\,w_K(n)+w_K(e_y).
\]

The other diagonal gives the same estimate from e_x=e_y-sqrt(2)n. Use whichever diagonal satisfies (DU.2).

**Theorem DU1 (horizontal width bound).** Every compact connected body satisfying the incoming strip and both canonical diagonal positions obeys

\[
\boxed{W\leq1+2\sqrt2<4.}
\tag{DU.3}
\]

The strict comparison with four follows from sqrt(2)<3/2. No constraint on the original translations or a symmetry assumption was used.

## 3. Applicability to the unrestricted maximizing problem

For an ambidextrous body with area greater than sqrt(2), the earlier canonical angle reduction gives correctly signed motions. If either reduced endpoint magnitude were at most pi/4, the two endpoint unit strips would bound its area by sec(pi/4)=sqrt(2). Consequently both diagonal positions are actually visited. DU1 applies to every such body's incoming normalization.

Combining with AW-W and the candidate area M>41/25, every global maximizer in an incoming unit-span normalization has

\[
\boxed{2<W\leq1+2\sqrt2<4.}
\tag{DU.4}
\]

This uses only canonicalization, connectedness, unit-strip geometry and the independently written analytic width exclusion. It does not use the disputed ordinary-area enclosure by the adaptive functional.

The upper bound narrows a scalar domain; it does not localize the shape near Romik, impose the curvature cap, or complete the original problem. The argument is entirely pen-and-paper and needs no computer-assisted covering.
