# Sharp local optimality for **actual full-turn sofas** without midline saturation

**Theorem ASS1 (direct ordinary-area theorem).**
Let S be **any compact connected** ambidextrous sofa following
both complete conventional quarter turns in a shared incoming
unit-height strip. Assume its actual convex hull K has vertical
span one and horizontal projection **exactly**
\[
I=[-m,m],\qquad
m=\sqrt{1+Y^2}/(3Y),\quad
4Y^3+3Y-1=0,\quad Y>0.
\]
Let U and V be the two **actual downward canonical caps**
obtained respectively from the top hull roof of K and the
vertical reflection of its bottom hull roof. On their respective
upper quarters write
\(f_j(t)=h_j(\cos t,\sin t)\) and
\(g_j(t)=h_j(-\sin t,\cos t)\), \(0\le t\le\pi/2\)
for \(j\in\{U,V\}\).

Let \(f_*,g_*\) be the centered Romik reference-cap
support functions. Suppose only the **second-derivative**
near-reference bounds
\[
\boxed{
f_j-f_*,\ g_j-g_*\in W^{2,\infty}(0,\pi/2),
\qquad
\|(f_j-f_*)''\|_\infty,\
\|(g_j-g_*)''\|_\infty\le10^{-3}
}
\tag{ASS.1}
\]
hold for each j independently.

There is **no hypothesis** that K contains the
horizontal midline across its full projection, or that
either cap contains the lower half-height rectangle.
No symmetry, face alignment, common top-face *length*,
one-turn contact-chart stability or curvature-atom
hypothesis beyond ASS.1 is imposed.

Let \(J_j=[a_j,b_j]\) be the actual exposed top face of
the j-th downward cap; set
\(a_*=-m/2,\ b_*=m/2\).
Then the **ordinary planar area of S itself** satisfies

\[
\boxed{
|S|\le M-\frac{100}{3}
\sum_{j\in\{U,V\}}
\bigl(|a_j-a_*|^3+|b_j-b_*|^3\bigr)
\le M,
}
\tag{ASS.2}
\]
where \(M=1+4Y^2+\arctan Y\) is the exact
Romik reference area.

Equality implies **both actual hull caps equal \(U_*\)**.
Together with reference regular closedness, equality
then identifies S with the Romik reference sofa
(up to the fixed normalization).

This is a **genuine local sharp theorem for actual connected
full-turn competitors**, not merely an upper bound on
artificially constructed midline-saturated intersections.
It handles independent arbitrary smooth shape changes,
top-face displacements and mismatched top-face lengths
within an explicit \(W^{2,\infty}\) bound.

It does **not** establish unrestricted ambidextrous
optimality: it fixes the projection width exactly,
requires strong curvature-profile closeness, and
assumes genuinely complete turns. The old AF/SD/SR
analytic inputs are written, self-reviewed proofs
but not independently refereed or Lean-verified.

## 1. Why no half-height rectangle is needed for actual sofas

Let \(K=\operatorname{conv}S\).
For each x∈I let A_U(x),A_V(x) be the two
downward cap roofs, and n_U(x),n_V(x)
their full positive turning-niche roofs.

The canonical full-turn saturation E has the
actual vertical section
\[
E_x=\left[
\max(n_U(x),1-A_V(x)),
\ \min(A_U(x),1-n_V(x))
\right].
\tag{ASS.3}
\]

Since S is connected, its horizontal projection is
the entire interval I. Each S_x is nonempty,
and S⊂E by canonical support tightening.
Therefore **every E_x is a nonempty interval**.
This is exactly the hypothesis of OT1, without
requiring \((x,1/2)\in E_x\).

Elementary interval arithmetic now proves the
full **ordinary-area** identity
\[
\boxed{
|S|\le|E|
=\Psi(U)+\Psi(V)+G,
\quad
G=\int_I[
\min(n_U,1-A_V)+
\min(n_V,1-A_U)]\,dx\ge0.
}
\tag{ASS.4}
\]

This formula retains the clipping correction G,
and its nonnegativity is not silently reversed.

## 2. The smooth-neighborhood assumptions give the same exact
## curvature and face-tip controls as S2C

The endpoint values of every difference
\(v=f_j-f_*, w=g_j-g_*\) vanish, because the
horizontal projection and vertical span
are fixed. With ε=10⁻³,
the elementary zero-endpoint second-derivative
barrier gives
\[
\|v\|_\infty,\|w\|_\infty
\le\frac{\varepsilon L^2}{8}
<\frac{\varepsilon}{2},
\quad
|v'(0)|,|v'(L)|,|w'(0)|,|w'(L)|
\le\frac{\varepsilon L}{2}<\varepsilon,
\quad L=\pi/2.
\tag{ASS.5}
\]

Reference open-quarter curvature satisfies
\(0\le\rho_*\le7/8\). Actual hull convexity
provides nonnegative curvature, and ASS.1
excludes new open-quarter singular atoms.
Hence
\[
\boxed{0\le\rho_j=f_j''+f_j,\ g_j''+g_j
\le7/8+3\varepsilon/2<9/10.}
\tag{ASS.6}
\]
The reference inner-corner height is everywhere
strictly below 13/30; its perturbation is
at most ε, so the true full niches stay below 1/2.
The positive-sine Green formula, or the
proof of UFC1, further gives
\[
\boxed{
\operatorname{supp}n_j\subseteq J_j,\qquad
n_j(a_j+d),\ n_j(b_j-d)\le10d^2
\quad(0\le d\le1/10).
}
\tag{ASS.7}
\]
The face endpoints are the support derivative traces
\(a_j=-g_j'(0)\), \(b_j=-f_j'(L)\),
so \(|a_j-a_*|,|b_j-b_*|<\varepsilon\).
Both face intervals remain nondegenerate and overlap;
their endpoint discrepancies are \(<2\varepsilon\).
All the sliver tip bounds therefore apply.

## 3. Compare the cubic clipping cost with the cubic trace deficit

Because n_U,n_V are supported inside their respective
top faces, the integrand of G in ASS.4 is nonzero
only on the parts of one top face **outside the other**.
No assumption about the sign of a niche or support
perturbation is needed. Integrating ASS.7 on
the two opposite end slivers, as in UFC1, gives
\[
\boxed{
0\le G\le\frac{10}{3}
\left(|a_U-a_V|^3+|b_U-b_V|^3\right)
\le\frac{40}{3}\sum_j
(|a_j-a_*|^3+|b_j-b_*|^3).
}
\tag{ASS.8}
\]

For each cap, W>2 ensures the signed wall roof
from SR1 has a zero branch at every abscissa
from one of the two axis-angle quadrants.
The exact signed-roof integral is consequently
the actual positive full-niche area.
Thus the **existing** AF fixed-width functional
and SD energy apply to \(\Psi(U),\Psi(V)\) without
any no-clipping assumption about their *pair*.

Put
\(\Delta_j=M/2-\Psi(j)\).
As derived fully in S2C.12–S2C.15,
the fixed-width Dirichlet coercivity and
the elementary boundary trace estimate
\[
\int_0^L|u'|^2\ge |u'(0)|^3/(3\varepsilon)
\quad\text{when }u(0)=u(L)=0,\ 
\|u''\|_\infty\le\varepsilon
\]
give
\[
\boxed{
\Delta_j\ge
\frac{140}{3}
\bigl(|a_j-a_*|^3+|b_j-b_*|^3\bigr).
}
\tag{ASS.9}
\]

Substitute ASS.8 and ASS.9 into ASS.4:
\[
\begin{aligned}
M-|S|&\ge M-|E|
=\Delta_U+\Delta_V-G\\
&\ge
\frac{100}{3}\sum_j
(|a_j-a_*|^3+|b_j-b_*|^3).
\end{aligned}
\]
This is ASS.2.

If all four face endpoints coincide with reference,
the niche-clipping term G vanishes **exactly**,
and the strict fixed-width energy SD1 shows
that both one-turn deficits vanish only when the
two complete cap supports coincide with reference.
Then E is Romik's reference, and equality of
the area of a compact subset S⊂E with E's area
forces S=E by regular closedness. QED.

## 4. The exact boundary of the proof

This theorem removes the potentially artificial
**midline-saturation assumption** of S2C1
*for actual geometric competitors*. Its
strong regularity norm and fixed width remain
unproved admission conditions at a global
maximizer. It cannot be upgraded to Hausdorff
or area-neighborhood optimality merely from
compactness: skinny new facets and moving
switching angles need not satisfy ASS.1.

The substantive new fact is that **the positive
two-turn clipping correction is paid by the
individual weighted deficits throughout an
explicit infinite-dimensional regularity
neighborhood, even without common midline,
aligned faces or asymmetric-cap suppression**.
No Lean, CI, optimizer or numerical mesh
was used, and unrestricted full/partial-turn
optimality is not claimed.
