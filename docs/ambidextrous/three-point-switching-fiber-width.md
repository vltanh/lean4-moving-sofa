# A three-point switching bound on *every* central fiber

**Status.** New direct geometric hand theorem for complete conventional
left-and-right quarter turns. It uses neither Romik's reference shape,
a one-cap functional, curvature bounds, contact pattern, symmetrization,
a sampled hallway relaxation, nor computer optimization.

**Results.** Every compact **connected** sofa with both full conventional
quarter-turn motions from a common incoming unit-width strip has
horizontal width

\[
\boxed{W\le 2\sqrt2.}\tag{TSW.1}
\]

This improves the branch's previous general full-turn width bound
\(W\le1+2\sqrt2\) from DU1 / \(W\le5\) from FR1.
The bound is sharp for a horizontal line segment of length
\(2\sqrt2\) (a zero-area full-turn sofa). Moreover every central
vertical fiber has an explicit height bound based only on the
distances to two horizontal extreme *points*.

The statements below do **not** establish the sharp ordinary-area
bound \(M=1.644955\ldots\). Partial-turn sofas require a separate
endpoint-angle argument.

## 1. Geometry and the switching square

Translate the common incoming strip to \(0\le y\le H\le1\).
Let \(S\) be nonempty, compact, connected and feasible for
every canonical conventional lower and upper quarter-turn
hallway angle \(t\in[0,\pi/2]\). Write
\([l,r]=\operatorname{proj}_x S\), \(W=r-l\).
Compactness supplies extreme points

\[
P=(l,y_L),\qquad Q=(r,y_R)
\quad\text{in }S.
\tag{TSW.2}
\]

For every \(x\in(l+1,r-1)\), connectedness means the vertical
fiber \(S_x\) is nonempty; compactness gives actual points

\[
p_-=(x,y_-),\qquad p_+=(x,y_+)\in S,
\quad y_-=\min S_x,\quad y_+=\max S_x.
\tag{TSW.3}
\]

Let \(R=r-x>1,\ L=x-l>1\), and denote the true
support function of \(S\) by \(h_S\).

For the lower turn, the two normal vectors are
\(u_t=(\cos t,\sin t)\) and \(v_t=(-\sin t,\cos t)\).
For each actual point \(p\in S\), feasibility requires

\[
h_S(u_t)-p\!\cdot u_t\le1
\quad\text{or}\quad
h_S(v_t)-p\!\cdot v_t\le1.
\tag{TSW.4}
\]

The sets of \(t\) satisfying the two inequalities are closed
and cover \([0,\pi/2]\). At \(t=0\), the first depth of
\(p_-\) is at least \(R>1\), so only the second alternative
can hold. At \(t=\pi/2\), the second depth is at least
\(L>1\), so only the first can hold. The two closed
subsets covering a connected interval must intersect.

Therefore an *interior switch angle* \(\theta\in(0,\pi/2)\)
exists for \(p_-\), where **both** support depths are at most
one. Testing those inequalities against the retained extreme
points \(P,Q\) gives

\[
\begin{aligned}
y_R-y_-&\le F_R(\theta):=
\frac{1-R\cos\theta}{\sin\theta},\\
y_L-y_-&\le F_L(\theta):=
\frac{1-L\sin\theta}{\cos\theta}.
\end{aligned}
\tag{TSW.5}
\]

The upper full turn becomes a lower turn on reflecting all
actual points by \((x,y)\mapsto(x,H-y)\).
Apply the same switching argument to the *reflected*
top fiber point \(p_+\). There is another, independent
interior angle \(\varphi\in(0,\pi/2)\) with

\[
\begin{aligned}
y_+-y_R&\le F_R(\varphi),\\
y_+-y_L&\le F_L(\varphi).
\end{aligned}
\tag{TSW.6}
\]

No assumption equates \(\theta\) and \(\varphi\).
In particular one cannot replace their actual turning
motions by the same imagined square position.

## 2. Pointwise fiber height bound

Let \(d_S(x)=y_+-y_-\ge0\). Adding the *two* inequalities
in TSW.5 and the *two* in TSW.6 cancels the unknown
heights \(y_L,y_R\):

\[
2d_S(x)\le G_{L,R}(\theta)+G_{L,R}(\varphi),
\quad
G_{L,R}(t)=F_R(t)+F_L(t).
\tag{TSW.7}
\]

A single rational trigonometric expression emerges:

\[
\boxed{
G_{L,R}(t)=
\frac{\sin t+\cos t-R\cos^2t-L\sin^2t}
{\sin t\cos t}.
}
\tag{TSW.8}
\]

Thus, **without any smoothness of \(S\) or its hull**,

\[
\boxed{
0\le d_S(x)\le
\sup_{0<t<\pi/2}G_{x-l,r-x}(t).
}
\tag{TSW.9}
\]

Here in the subscript on the right the first argument
means \(L=x-l\) and the second \(R=r-x\); in the
formula TSW.8 the coefficients are respectively attached
to \(\sin^2t\) and \(\cos^2t\).
The strict endpoint divergences for \(L,R>1\) make the
supremum a finite maximum in the open interval.

In particular, if the right side is negative, **no**
actual fiber \(S_x\) can exist. This is a direct
three-point obstruction strengthened by the presence
of both opposite-handed complete turns.

## 3. Improved universal horizontal width bound

If \(W\le2\), the claim TSW.1 is trivial. Otherwise
take the midpoint \(x=(l+r)/2\), which belongs to the
projection by connectedness. Then \(L=R=D=W/2>1\),
and TSW.8 simplifies to

\[
G_{D,D}(t)=
\frac{\sin t+\cos t-D}{\sin t\cos t}.
\tag{TSW.10}
\]

Since \(\sin t+\cos t\le\sqrt2\),
if \(D>\sqrt2\), every \(G_{D,D}(t)<0\),
contradicting TSW.9 and \(d_S(x)\ge0\).
Consequently \(D\le\sqrt2\), i.e.

\[
\boxed{W\le2\sqrt2.}
\]

At equality \(W=2\sqrt2\), TSW.9 forces the
midpoint fiber to have height zero. Moreover the switch
angles in TSW.7 must both be \(\pi/4\); there
\(F_D(\pi/4)=0\) for both walls.
TSW.5--TSW.6 then force the extreme points \(P,Q\)
and the unique midpoint-fiber point to have the *same*
vertical coordinate. This is an additional equality
rigidity for the three retained anchors, not a proof
that the entire sofa is a line segment.

## 4. Exact midpoint thickness profile

There is also a convenient explicit height ceiling
as a function of the full horizontal width \(W\).

For \(D=W/2\in(1,\sqrt2]\), put
\(z=\sin t+\cos t\in(1,\sqrt2]\).
Since \(\sin t\cos t=(z^2-1)/2\),

\[
G_{D,D}(t)=g_D(z):=\frac{2(z-D)}{z^2-1}.
\tag{TSW.11}
\]

Differentiating gives

\[
g_D'(z)=\frac{2(2Dz-z^2-1)}
{(z^2-1)^2}.
\tag{TSW.12}
\]

The only critical point greater than \(1\) is
\(z_+=D+\sqrt{D^2-1}\).
The maximum lies at \(z_+\) if
\(z_+\le\sqrt2\) and at \(\sqrt2\)
otherwise. The threshold \(z_+=\sqrt2\)
is \(D=3/(2\sqrt2)\). At the critical
point \(g_D(z_+)=1/z_+=D-\sqrt{D^2-1}\).
Therefore

\[
\boxed{
d_S((l+r)/2)\le
\begin{cases}
D-\sqrt{D^2-1},
  &1<D\le 3/(2\sqrt2),\\[3pt]
2(\sqrt2-D)=2\sqrt2-W,
  &3/(2\sqrt2)\le D\le\sqrt2.
\end{cases}}
\tag{TSW.13}
\]

The bound concerns *the vertical spread of actual
points*, not the convex-hull thickness. An unoccupied
vertical gap cannot be treated as sofa area. For connected
full-turn sofas the midpoint fiber is nonempty, but
it is not assumed vertically filled.

The ceiling can be combined with \(d_S(x)\le H\le1\).
Its significance is a quantitative center bottleneck
for wide full-turn competitors; it is not yet a
global area estimate.

## 5. The width constant is sharp for a zero-area sofa

Take the horizontal line segment

\[
S=[-\sqrt2,\sqrt2]\times\{0\}.
\]

At lower-frame angle \(t\), a point at abscissa \(x\)
has inner-wall support depths
\((\sqrt2-x)\cos t\) and \((x+\sqrt2)\sin t\).
It is safe if at least one is at most one.

A point violating both would require

\[
x<\sqrt2-\frac1{\cos t},
\qquad
x>\frac1{\sin t}-\sqrt2.
\]

These strict inequalities are incompatible because
\(\frac1{\cos t}+\frac1{\sin t}\ge2\sqrt2\)
(AM--GM, equality at \(t=\pi/4\)).
Hence *every* point of \(S\) survives the canonical
lower hallway at every turn angle.
Horizontal reflection of the geometry gives the
same upper-handed property. The support-tightened
hallway offsets depend continuously on \(t\);
append the straight incoming/outgoing translations to
obtain the two complete motions. The segment is
connected, compact, and has width \(2\sqrt2\) and
area zero. This proves sharpness of the **width**
constant, not of a positive-area upper bound.

## 6. Research consequence and limits

Unlike another finite-angle numerical bound, TSW.1
gives an **exact universal normalization**
\([0,2\sqrt2]\times[0,H]\) for the full-turn class.
Unlike previous reference-neighborhood results, it is
global, ignores the Romik shape and does not assume
hull curvature, symmetry, or contact order. Its proof
uses only four support tests on two actual vertical
fiber points, the true horizontal extrema, and a
closed-set switching argument.

A proposed global ordinary-area bound would still have
to estimate the height of fibers *throughout* the
projection, including the two outer strips of total
width two, and handle the partial-turn case. No claim
of \(A\le M\) or a new globally best area constant
is made here. No Lean, CI, long search or numerical
optimizer was used. The argument is pen and paper,
subject to independent review.
