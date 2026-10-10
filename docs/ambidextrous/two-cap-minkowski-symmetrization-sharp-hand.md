# A genuine sharp two-cap Minkowski symmetrization theorem (no Romik neighborhood)

**Theorem MSY1 (global-in-shape, local-in-pair structural reduction).**
Let S be **any compact connected sofa** with both *complete
conventional* right-angle turns from the same incoming
unit-height strip. Suppose its actual convex hull K has
vertical span one and horizontal projection I=[l,r],
with width W=r−l>2.

Let U,V be the two **actual downward canonical one-turn
caps** obtained from the upper hull boundary and the
vertically reflected lower hull boundary of S. They share
horizontal projection I and height one. Let
\(f_X(t)=h_X((\cos t,\sin t))\),
\(g_X(t)=h_X((-\sin t,\cos t))\)
for \(X\in\{U,V\}\), \(0<t<L=\pi/2\).

Assume there are \(\eta,\lambda\) satisfying
\[
\boxed{0<\eta\le1,\qquad
0<\lambda\le\frac{7\eta}{100}}
\tag{MSY.1}
\]
such that:

1. Each upper-quarter curvature distribution is
   **absolutely continuous with density**
   \(0\le f_X''+f_X,\ g_X''+g_X\le1-\eta\) a.e.
   on the two open quarters. Top-normal atoms and
   horizontal-axis edge atoms are permitted.
2. The two parents' second derivatives are
   **close to each other, not necessarily to Romik**:
   \[
   \boxed{\|(f_U-f_V)''\|_\infty,\
   \|(g_U-g_V)''\|_\infty\le\lambda.}
   \tag{MSY.2}
   \]

Let \(\bar U=(U+V)/2\) be their **true Minkowski
average** as convex caps, not a pointwise average
of the surviving nonconvex sofas.
Let
\[
E_{UV}=(U\setminus N(U))\cap
\rho(V\setminus N(V)),\qquad
\rho(x,y)=(x,1-y).
\]
Here all N are **complete positive-height one-turn niches**.

Then the following is a **true ordinary-area inequality**
for the actual sofa:
\[
\boxed{
|S|\le|E_{UV}|
\le 2\Psi(\bar U)\le M,
}
\tag{MSY.3}
\]
where \(\Psi(X)=|X|-|N(X)|-W/2\) is the
signed width-penalized one-turn functional,
and \(M\) is Romik's exact candidate area.
The final inequality is the already written
[WV2](one-turn-weighted-value.md) value theorem;
equivalently it follows from AF3 and the
curvature-dominated signed-roof identity SR1.
Those historical chains are self-reviewed
and not independently refereed or Lean-verified.

Even more, if U,V additionally have full
lower half-height rectangles and their positive
niche roofs are at most one half, then
\[
\boxed{
|E_{UV}|\le
|(\bar U\setminus N(\bar U))
\cap\rho(\bar U\setminus N(\bar U))|.
}
\tag{MSY.4}
\]
Both sides are **genuine connected complete-two-turn
sofas**. Thus within this class the actual
Minkowski average *is* an area-nondecreasing
**identical-parent replacement**, which is the
specific structural goal suggested by the
Gerver/Romik overlap construction.

The hypothesis controls the difference between
**the two parents**, not their distance from
Romik's profile. It therefore covers a genuine
unbounded-in-reference-shape family, unlike the
earlier ASS1 local theorem. It does **not**
claim the same operation works for arbitrary
distant pairs: PII2 proves simple selection of
either parent fails, and EAC1 refutes the
unqualified averaged-Ψ inequality.

## 1. Niche confinement and an exact cubic clipping bound

Let \([a_X,b_X]\) be the height-one top face
of cap X. The first/second support derivatives
give \(a_X=-g_X'(0+)\), \(b_X=-f_X'(L-)\).
The positive sine-kernel solution of
\(f_X''+f_X=\rho_f\),
\(g_X''+g_X=\rho_g\), together with
\(0\le\rho\le1-\eta\), gives
\[
\begin{aligned}
g_X(t)&\le1-a_X\sin t-\eta(1-\cos t),\\
f_X(t)&\le1+b_X\cos t-\eta(1-\sin t).
\end{aligned}
\tag{MSY.5}
\]
Consequently the full positive turning niche
of each cap lies inside its own top-face interval.
At its endpoints the continuum single-wall
maximization from
[UFC1](general-unequal-face-cubic-clipping.md)
gives
\[
\boxed{
n_X(a_X+d),\, n_X(b_X-d)
\le d^2/\eta\qquad(0\le d\le\eta).
}
\tag{MSY.6}
\]

The top-face endpoint differences are
\[
d_a:=|a_U-a_V|=|(g_U-g_V)'(0)|,\quad
d_b:=|b_U-b_V|=|(f_U-f_V)'(L)|.
\tag{MSY.7}
\]
Because f_U−f_V and g_U−g_V have zero
endpoint values at 0 and L (same width
and height), the elementary Lipschitz
derivative estimate yields
\[
\boxed{d_a,d_b\le \lambda L/2<\lambda<\eta.}
\tag{MSY.8}
\]

For the **actual connected** sofa, the
full canonical envelope E_UV has
nonempty interval fibers over I:
S projects onto all of I and S⊂E_UV.
Thus the exact ordinary-area identity
[OT1](one-turn-reduction.md) gives
\[
\boxed{|E_{UV}|=\Psi(U)+\Psi(V)+G}
\tag{MSY.9}
\]
with
\[
G=\int_I[\min(n_U,1-A_V)+
          \min(n_V,1-A_U)]\,dx\ge0.
\]

Each positive-niche roof is supported
inside its own top face. Consequently
the two integrands can be nonzero only
on the **four end slivers** where those
top faces fail to coincide, and the
tip bound MSY.6 integrates to
\[
\boxed{
0\le G\le\frac{d_a^3+d_b^3}{3\eta}.
}
\tag{MSY.10}
\]
This is the unequal-face UFC1 estimate;
it does not presume the same face length
or the same turning-contact chart.

## 2. Strong Jensen gain from the signed one-turn functional

For W>2, the two axis-angle forbidden
quadrants cover the entire horizontal
line by at least one zero-roof branch.
Hence the **signed** niche roof of
[SR1](curvature-only-signed-roof.md)
is nonnegative everywhere and equals
the actual positive full-niche roof.
The unit-curvature-gap assumptions allow
the signed roof identity SR1 to be applied,
so the exact fixed-width analytic
one-turn functional [AF1](adaptive-functional-global-calibration.md)
satisfies
\[
\Psi(X)=F(f_X,g_X)-W/2
\quad(X=U,V,\bar U).
\tag{MSY.11}
\]
The midpoint cap is convex, has the same
width and height, and inherits
\(0\le\rho\le1-\eta\).

Set
\[
v=f_U-f_V,\quad w=g_U-g_V,\qquad
y(t)=e^{-it/2}(v(t)+iw(t)).
\]
Both v,w vanish at the two quarter
endpoints. The exact strong concavity
of F from [AF1/SD1](stability-fixed-width-deficit.md)
gives the **true Jensen gap**
\[
\begin{aligned}
J&:=2\Psi(\bar U)-\Psi(U)-\Psi(V)\\
&\ge\frac7{64}\int_0^L|y'(t)|^2dt.
\end{aligned}
\tag{MSY.12}
\]
This includes the nonnegative Bregman
remainders at all source-sign switches;
no stable contact chart is assumed.

Dirichlet on a quarter interval gives
\(\|y\|_2\le\|y'\|_2/2\), while
\(v'+iw'=e^{it/2}(y'+iy/2)\).
Thus
\[
\|v'+iw'\|_2\le\tfrac54\|y'\|_2,
\]
and the Jensen gap has the
explicit whole-profile coercivity
\[
\boxed{
J\ge\frac7{100}
\int_0^L(|v'|^2+|w'|^2)\,dt.
}
\tag{MSY.13}
\]

## 3. A cubic *difference* trace cost pays clipping

Because \(|v''|,|w''|\le\lambda\)
and v,w have zero endpoint values,
the elementary trace inequality
in [S2C.14](smooth-two-cap-sharp-neighborhood.md)
applies to v near L and w near zero.
For any u with \(|u''|\le\lambda\),
\[
\int_0^L|u'|^2dt
\ge\frac{|u'(0)|^3}{3\lambda},
\qquad
\int_0^L|u'|^2dt
\ge\frac{|u'(L)|^3}{3\lambda}.
\tag{MSY.14}
\]
These two inequalities are applied to
**different components**, w for the
left endpoint, v for the right endpoint,
so the energy is not double-counted.
Consequently
\[
\boxed{
J\ge\frac7{300\lambda}(d_a^3+d_b^3).
}
\tag{MSY.15}
\]
The numerical condition \(\lambda\le
7\eta/100\) now gives
\[
\frac7{300\lambda}\ge\frac1{3\eta}.
\]
Combine MSY.10 and MSY.15:
\[
\boxed{G\le J.}\tag{MSY.16}
\]

Substitute into the exact ordinary-area
identity MSY.9:
\[
|E_{UV}|=\Psi(U)+\Psi(V)+G
\le 2\Psi(\bar U)\le M.
\]
Since S⊂E_UV, this proves MSY.3
*without* assuming the common horizontal
midline belongs to S or to its envelope.

## 4. Genuine identical-parent construction under midline assumptions

Assume also \(I\times[0,1/2]\subset U,V\)
and \(n_U,n_V\le1/2\).
Their Minkowski average contains the
same half-height rectangle. Its
inner-corner height at every angle is
the average of the parents' inner-corner
heights (the support values are linear
under Minkowski interpolation).
Every parent corner is ≤1/2 because
its full niche roof is ≤1/2; if an
individual corner lay above 1/2,
that corner's open quadrant would contain
points of height >1/2. Thus the average
niche also has height ≤1/2.

The average cap's positive niche is
confined inside its own top face by
MSY.5 (its top face interval is the
Minkowski average of the two top
face intervals). Its one-turn survivor
contains the entire horizontal midline,
with nonempty interval vertical fibers
over I; the same is true after vertical
reflection. Their intersection
\(E_{\bar U,\bar U}\) is therefore a
**connected complete two-turn sofa**, and
self clipping vanishes exactly:
\[
\boxed{|E_{\bar U,\bar U}|=2\Psi(\bar U).}
\tag{MSY.17}
\]
Together with MSY.3, this proves
the constructive pair-to-identical
area improvement MSY.4.

Even though the operation fails if
one simply chooses either original
parent (PII2), the averaged parent
works in this rigorously bounded
curvature-difference regime.

## 5. Mathematical acceptance boundary

This is a **positive structural theorem
directly addressing the unequal-parent
Gerver overlap conjecture**:
the self-pair of the true Minkowski
average dominates the mixed pair,
provided the two parents are sufficiently
close **to each other in second derivative**
and both have a strict subunit open-quarter
curvature gap.

Nothing here assumes that the parents
are close to Romik's explicit shape;
the same result holds for arbitrary
underlying common cap shapes and
arbitrary top-face locations/lengths
compatible with the hypotheses.

However a general optimal ambidextrous
sofa need not satisfy strict curvature
domination, the quantitative parent
second-derivative closeness or the
complete-turn assumption. Even if it
does, the independent analytic
AF/SD/SR identity/calibration chains
require review. These gaps prevent
upgrading MSY3 or MSY4 to a proof of
the unrestricted sharp conjecture.

The \(7/100\) constant is a conservative
Poincaré/triangle estimate, not asserted
optimal. A future global proof might
relax the small-difference condition
using the **full nonnegative Bregman
contact terms** omitted from MSY.13
or an exact cap-pair area majorant.
No numeric area search, Lean
formalization, CI or independent
referee check is part of this proof.
