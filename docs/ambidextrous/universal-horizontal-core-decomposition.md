# Universal horizontal-segment decomposition of every convex downward one-turn cap

**Theorem UHCD1 (not a maximizer theorem).** Let \(U\) be any
nonempty compact convex *downward-closed* unit-height
one-turn cap with horizontal projection \(I=[l,r]\)
of width \(W=r-l\), bottom edge \(I\times\{0\}\),
and horizontal top face \(J=[a,b]\times\{1\}\),
of length \(T=b-a\ge0\).
There exists a **canonical compact convex downward cap**
\(C(U)\) with horizontal width \(W-T\), height one,
a **singleton top face at \((a,1)\)**,
and bottom edge \([l,r-T]\times\{0\}\), such that

\[
\boxed{U=C(U)+([0,T]\times\{0\}).}
\tag{UHCD.1}
\]

Thus **every** one-turn convex cap has a genuine
horizontal rectangular segment summand equal to
its top-face length, without any assumption of
maximality, curvature bounds, reflection symmetry,
one-turn niche height, or motion feasibility.
The core is canonical after the convention
that the horizontal interval being removed
starts at zero. Its area satisfies

\[
\boxed{|U|=|C(U)|+T.}
\tag{UHCD.2}
\]

If additionally the upper roof of U satisfies
\(A_U(x)\ge h\) on its entire projection
for some \(0\le h<1\), then there is a
canonical convex downward **short core**
\(V(U,h)\) of height \(1-h\) and width \(W-T\)
with singleton top face at \((a,1-h)\) such that

\[
\boxed{
U=V(U,h)+([0,T]\times[0,h]),\qquad
|U|=|V(U,h)|+(1-h)T+hW.
}
\tag{UHCD.3}
\]

Taking \(h=1/2\) recovers the geometric
decomposition from HF2 but **without** using
any property of a weighted one-turn maximizer.
HF2 adds the *nontrivial maximizing-specific*
assertions \(A_U\ge1/2\) and \(T=W/2\);
the Minkowski decomposition itself is
an elementary convex-geometric fact.

## 1. Construct the horizontal-eroded core

Every horizontal slice of U is a compact interval

\[
U_y=[L(y),R(y)],\qquad 0\le y\le1.
\]

Convexity of U implies \(L(y)\) is a convex
function of y and \(R(y)\) a concave function:
interpolating points on left or right slice
boundaries provides their defining inequalities.

Downward closure implies
\[
U_{y'}\subseteq U_y\qquad(0\le y<y'\le1).
\]
Because the whole top face [a,b] lies in
every lower slice,
\[
R(y)-L(y)\ge b-a=T.
\]
Define a compact set by the explicit slice formula
\[
\boxed{C(U)_y=[L(y),R(y)-T].}
\tag{UHCD.4}
\]
Each slice is nonempty. Its left boundary remains
convex, its right boundary is concave; therefore
the resulting set is convex. Both boundaries
remain nested as y increases, so the set is
downward closed. Compactness follows from
closedness of U and the slice inequalities, or
from the identity below and Hausdorff limits.

Adding the horizontal segment [0,T] increases
**each** slice back to [L(y),R(y)]:
\[
C(U)_y+[0,T]=[L(y),R(y)].
\]
Consequently \(C(U)+([0,T]\times\{0\})=U\).
At height y=1 the core slice is [a,a];
at height y=0 it is [l,r-T]. Therefore
it has the advertised top and bottom
geometry and width W−T.

Each horizontal slice grows in length
by exactly T under the Minkowski addition.
Fubini across y∈[0,1] yields
\[
|U|=|C(U)|+T,
\]
with no differentiability assumption.
The slice construction also proves uniqueness
among downward convex cores satisfying
the exact sum UHCD.1: the interval endpoints
must be \(L(y)\) and \(R(y)-T\).

## 2. Add any genuine vertical filling

Suppose the cap's upper roof obeys
\(A_U\ge h\) over all x in I. This is
equivalent to \(I\times[0,h]\subset U\).

For each y≤h the horizontal slice U_y=I;
hence from UHCD.4 the core has
\(C(U)_y=[l,r-T]\) for all 0≤y≤h.
In other words, C(U) contains its full
bottom rectangle of height h.

Define \(V(U,h)\) by translating the
upper slices of C(U) down by h:
\[
V(U,h)_z=C(U)_{z+h},
\qquad 0\le z\le1-h.
\tag{UHCD.5}
\]
Because the slices of C(U) are convex and
nested and its lowest h slices are identical,
this V is again compact, convex and
downward closed. Section-by-section,
\[
C(U)=V(U,h)+([0,h]e_y).
\]
Substituting into UHCD.1 and using the
commutativity/associativity of Minkowski sums
proves the first identity in UHCD.3.

Write \(L_C=W-T\) for the width of C.
Adding a vertical segment of height h to
V increases its area by \(hL_C\), because
each nonempty vertical fiber is extended by
h and V has full projection of length L_C.
Adding the horizontal segment of length
T to C increases its area by T across
vertical span one. Thus
\[
|U|=|V|+h(W-T)+T
=|V|+(1-h)T+hW,
\]
proving UHCD.3. QED.

## 3. A general pair-of-cores exact area reduction

Take two such independent caps U,D with the
same horizontal projection I of width W,
both of height one and downward closed.
Let their top horizontal face lengths be
\(T_U,T_D\), possibly different, and
write the canonical **point-top** cores
\(C_U=C(U),C_D=C(D)\).
Let \(A_U,A_D\) be the respective cap roofs,
and let \(n_U,n_D\) be their full positive
turning-niche roofs. Consider an *actual
compact connected complete-two-turn* sofa S
whose upper/lower canonical caps are U and D,
so its fully supported canonical envelope
\[
E=(U\setminus N(U))\cap
  \rho(D\setminus N(D))
\]
has nonempty vertical fibers at every x∈I,
as does S.

The outer common convex hull has fiber
\([1-A_D(x),A_U(x)]\), hence area
\(|U|+|D|-W\). Relative to that outer
fiber, the effective lower and upper
niche losses are respectively
\[
(n_U+A_D-1)_+,\qquad
(n_D+A_U-1)_+.
\]
They cannot overlap inside the true
nonempty E fiber. Therefore

\[
\boxed{\begin{aligned}
|S|\le|E|
={}&|C_U|+|C_D|+T_U+T_D-W\\
&-\int_I[(n_U+A_D-1)_+
+(n_D+A_U-1)_+]\,dx.
\end{aligned}}
\tag{UHCD.6}
\]

This is a **global ordinary-area identity**
for actual connected full-turn sofa data
with arbitrary positive (or point)
top/bottom faces, without assuming that
either original cap has half-height flanks,
low niches or matched top-face positions.
The only uses of *actual* motion are the
canonical support constraints and
nonempty vertical fibers; no signed
curve-area formula is invoked.

The sharp \(M\) value would follow if every
such pair obeyed the **still-unproved**
effective-niche lower bound
\[
\boxed{
\int_I[(n_U+A_D-1)_+
+(n_D+A_U-1)_+]\,dx
\ge |C_U|+|C_D|+T_U+T_D-W-M.
}
\tag{UHCD.7}
\]
This is a *larger* and genuinely
competitive domain than the half-height,
equal-top-length class in RCE.3.
It does not solve the sharp value merely
by renaming the missing inequality.

## 4. How this advances the user’s Gerver/intersection idea

The earlier [HF2](one-turn-half-width-top-face.md)
proved the rectangular decomposition only for
signed one-turn maximizers, because it needed
maximizer-specific properties to show half-height
filling and the exact ratio T=W/2.

UHCD1 shows the *horizontal* structural
summand is in fact **universal for all convex
downward caps** with positive upper faces.
Consequently, one cannot reject the
“curved core + horizontal central rectangle”
approach simply because an arbitrary competitor
might lack a rectangular segment summand:
it never lacks that **horizontal** summand
when its horizontal top face has positive length.

The genuine remaining admission questions
are different:
1. Does a putative better sofa force a
   **positive vertical** filling thickness
   (especially h=1/2) for *both* caps?
   UHCD1 does not prove this.
2. Can two independently shaped point-top
   cores be compared sharply using their
   **effective niche** cost UHCD.6?
   This is not provided by separate Gerver
   optimality or by Minkowski averaging:
   EAC1 supplies a counterexample to the
   naive averaged-Ψ inequality.
3. For unrestricted partial turns, may
   only the **visited** niches be subtracted;
   the full-niche identity UHCD.6 is not
   a substitute without completion.

By [PD3](full-turn-positive-face-density.md),
the whole full-turn supremum can be approximated
from below by actual two-turn sofas with
*positive top and bottom exposed faces*.
Hence both horizontal summands in this new
representation may be required strictly
positive in a **value-reduction** argument.
This does **not** imply the corresponding
vertical filler height is 1/2, nor solve
their shared ordinary-area inequality.

No numerical grid, solver, Lean formalization,
CI or independent referee review is used.
All new identities follow from convexity,
horizontal slicing and the actual
canonical-envelope fiber formula.
