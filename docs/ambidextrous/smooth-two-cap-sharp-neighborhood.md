# A genuinely infinite-dimensional **sharp** two-cap neighborhood around Romik

**Theorem S2C1 (explicit \(W^{2,\infty}\) neighborhood; hand proof).**
Let \(Y>0\) be the root of \(4Y^3+3Y-1=0\), set
\[
m=\frac{\sqrt{1+Y^2}}{3Y},\qquad
M=1+4Y^2+\arctan Y,\qquad L=\pi/2,
\]
and let \(U_*\) be the centered downward Romik one-turn
reference cap of height 1 and projection
\(I=[-m,m]\), with upper-quarter support functions
\[
f_*(t)=h_{U_*}(\cos t,\sin t),\qquad
g_*(t)=h_{U_*}(-\sin t,\cos t)
\quad(0\le t\le L).
\]

Take **any two independently chosen convex downward caps**
\(U_1,U_2\subseteq I\times[0,1]\), each of the same
horizontal projection I and height one, and **each containing**
the complete half-height rectangle
\[
I\times[0,1/2]\subseteq U_j.
\tag{S2C.1}
\]
Let their support functions \(f_j,g_j\) satisfy, separately
on the two open upper quarters,
\[
\boxed{
f_j-f_*,\ g_j-g_*\in W^{2,\infty}(0,L),\quad
\|(f_j-f_*)''\|_\infty,\
\|(g_j-g_*)''\|_\infty\le\frac1{1000}.
}
\tag{S2C.2}
\]

The endpoint values of the differences are automatically zero:
\(f_j(0)=g_j(L)=m,\ f_j(L)=g_j(0)=1\).
The caps need **not** be reflection symmetric, share their
top-face interval or top-face *length*, have the same curvature
density, or share turning-contact topology.

Put
\[
E=(U_1\setminus N(U_1))\cap
   \rho(U_2\setminus N(U_2)),
\qquad \rho(x,y)=(x,1-y).
\]
Then E is a compact connected sofa with **both full
conventional quarter-turn motions**. Writing
\(J_j=[a_j,b_j]\times\{1\}\) for their genuinely
exposed top faces and
\(J_*=[a_*,b_*]=[-m/2,m/2]\), the **exact sharp
ordinary-area inequality** is

\[
\boxed{
|E|\le M-\frac{100}{3}
\sum_{j=1}^2
\left(|a_j-a_*|^3+|b_j-b_*|^3\right)
\le M.
}
\tag{S2C.3}
\]

If at least one parent differs from \(U_*\), then
\(\boxed{|E|<M}\); equality occurs precisely for
\(U_1=U_2=U_*\), whose intersection is Romik's sofa.

This **infinite-dimensional** sharp result handles
independent smooth support deformations of both
Gerver-like one-turn parents, *including independently
moving and changing-length top faces*.
It is stronger in deformation dimension than the
previous two-parameter core-shear theorem SCR1.
It does **not** assert that all Hausdorff-near or
all actual maximizing sofas satisfy S2C.1–S2C.2:
the second-derivative bound is a genuine, stronger
local regularity hypothesis. Shifted contact switches,
new narrow facets, variable incoming width and partial
motions are not automatically admitted.

The proof uses existing **written** AF1/SD1
fixed-width strong concavity, SR1 signed-niche
identity and explicit candidate constants, plus the
new geometric [UFC1](general-unequal-face-cubic-clipping.md)
law. Those historical analytic dependencies are
self-reviewed and **not independently refereed or
Lean-kernel checked**. Everything after the named
inputs is an explicit elementary hand argument.

## 1. The C² bound controls the entire support, not just curvature

Let \(\varepsilon=1/1000\).
For either cap and quarter set \(v=f_j-f_*\),
\(w=g_j-g_*\).
Both v,w have zero endpoint values,
because the upper strip and horizontal projection
are fixed. The elementary second-derivative
barriers for \(u(0)=u(L)=0\),
\(|u''|\le\varepsilon\), are
\[
\boxed{
|u(t)|\le\frac\varepsilon2t(L-t)
\le\frac{\varepsilon L^2}{8}<\frac\varepsilon2.
}
\tag{S2C.4}
\]
For instance \(\pm(\varepsilon/2)t(L-t)\)
are upper and lower comparison functions:
subtract them from u, use the respective
sign of their second derivatives, and apply
convexity/concavity to their zero-endpoint
difference. This holds for weak \(W^{2,\infty}\)
derivatives.

The derivative u' is \(\varepsilon\)-Lipschitz,
and \(\int_0^L u'=0\). Consequently
\[
\boxed{|u'(0)|,\ |u'(L)|\le\varepsilon L/2<\varepsilon.}
\tag{S2C.5}
\]
Indeed if u'(0)>0 then
\(u'(t)\ge u'(0)-\varepsilon t\);
integrating forces \(u'(0)\le\varepsilon L/2\),
and the other three signs/endpoints follow
by sign and parameter reversal.

The reference open-upper-quarter curvature
densities satisfy \(0\le\rho_*\le7/8\),
including the zero-density straight-arc
subintervals. Convexity of each U_j supplies
nonnegative curvature measure.
The difference condition S2C.2 and S2C.4 give
\[
\begin{aligned}
\rho_{j,f}&=f_j''+f_j
\le \frac78+\varepsilon+\frac\varepsilon2
<\frac9{10},\\
\rho_{j,g}&=g_j''+g_j
\le\frac9{10}.
\end{aligned}
\tag{S2C.6}
\]
All open-quarter curvature is absolutely
continuous, since the reference and the
differences are \(W^{2,\infty}\).
Thus both competitors satisfy the strict
curvature-gap premise of UFC1 with
\[
\boxed{\eta=1/10.}
\tag{S2C.7}
\]

## 2. Their full niches remain below the common midline and within their top faces

The reference inner-corner height is
bounded above by \(13/30\) at **every**
conventional quarter-turn angle, by the
explicit Romik support calculation.
At each angle this corner ordinate is
\[
c_y=(f-1)\sin t+(g-1)\cos t,
\]
so S2C.4 yields
\[
|c_{j,y}-c_{*,y}|
\le(|v|+|w|)<\varepsilon.
\]
Therefore
\[
\boxed{
\sup_t c_{j,y}(t)<13/30+1/1000<1/2.
}
\tag{S2C.8}
\]
Every point of a lower forbidden quadrant
is below its own corner; hence the complete
positive niche roofs satisfy \(0\le n_j<1/2\).

Let \(J_j=[a_j,b_j]\) be the top face.
The one-sided upper-normal support derivatives
are
\[
\boxed{a_j=-g_j'(0+),\qquad b_j=-f_j'(L-).}
\tag{S2C.9}
\]
From S2C.5,
\[
\boxed{
|a_j-a_*|,\ |b_j-b_*|<\varepsilon.
}
\tag{S2C.10}
\]
In particular both top faces are positive
intervals containing a common long central
subinterval, their endpoint differences are
at most \(2\varepsilon<\eta\), and
the length of either top face may differ
from the reference value.

The curvature bound S2C.6 gives the exact
one-wall baseline-intercept inequalities,
for all \(0<t<L\),
\[
g_j(t)-1\le-a_j\sin t-\eta(1-\cos t),
\]
\[
f_j(t)-1\le b_j\cos t-\eta(1-\sin t).
\]
Thus no **positive** lower niche point
lies left of \(a_j\) or right of \(b_j\).
This proves
\[
\boxed{\operatorname{supp}(n_j)\subseteq J_j}
\tag{S2C.11}
\]
without assuming an active contact chart or a
particular curvature phase pattern.

Because \(A_j(x)\ge1/2\) by S2C.1 and
\(n_j(x)\le1/2\) by S2C.8, both one-turn
survivors and their reflected intersection
contain the entire midline
\(I\times\{1/2\}\). Their vertical sections
are nonempty intervals. Hence E is compact,
connected and admits both complete canonical
one-turn motions by continuity of the actual
parent support functions.

## 3. A trace inequality charges the moving top faces with cubic deficit

Use the written fixed-width sharp energy identity SD1
for the pair \((f_j,g_j)\) and reference
\((f_*,g_*)\) at fixed horizontal width \(2m\).
The positive curvature gap ensures the signed
roof of each cap equals its true full
positive niche roof: the signed roof is
nonnegative for W>2 because the two
axis-angle quadrants furnish a roof-zero
branch at every abscissa, and the signed
identity SR1 applies. Thus
\[
\Delta_j:=M/2-\Psi(U_j)
=F(f_*,g_*)-F(f_j,g_j)
\ge\frac7{32}\int_0^L |y_j'(t)|^2dt,
\tag{S2C.12}
\]
where
\[
z_j(t)=v(t)+iw(t),\qquad
y_j(t)=e^{-it/2}z_j(t),\quad
z_j(0)=z_j(L)=0 .
\]
Dirichlet on length \(L=\pi/2\)
gives \(\|y_j\|_2\le\frac12\|y_j'\|_2\).
As \(z_j'=e^{it/2}(y_j'+iy_j/2)\),
\[
\|z_j'\|_2\le\frac54\|y_j'\|_2,
\]
and hence the **explicit** strong estimate
\[
\boxed{
\Delta_j\ge
\frac7{50}\int_0^L
\left(|v'|^2+|w'|^2\right)dt.
}
\tag{S2C.13}
\]

We now prove a useful *cubic boundary trace* inequality.
For any real u∈\(W^{2,\infty}(0,L)\)
with u(0)=u(L)=0 and
\(\|u''\|_\infty\le\varepsilon\),
put \(s=|u'(0)|\).
By S2C.5, \(s/\varepsilon\le L/2\).
After changing sign if necessary,
\(u'(t)\ge s-\varepsilon t\ge0\)
for \(0\le t\le s/\varepsilon\), so
\[
\int_0^L |u'(t)|^2dt
\ge\int_0^{s/\varepsilon}
(s-\varepsilon t)^2dt
=\frac{s^3}{3\varepsilon}.
\tag{S2C.14}
\]
The same holds with \(|u'(L)|\)
after reversing the parameter.
Apply this to w at t=0 and v at t=L,
whose traces are the **two top-face
endpoint displacements** from S2C.9:
\[
\boxed{
\Delta_j\ge\frac7{150\varepsilon}
\bigl(|a_j-a_*|^3+|b_j-b_*|^3\bigr)
=\frac{140}{3}
\bigl(|a_j-a_*|^3+|b_j-b_*|^3\bigr).
}
\tag{S2C.15}
\]

This is a genuinely **infinite-dimensional**
energy bound: no perturbation direction or
finite contact chart is fixed, and a
boundary-layer change is charged
according to its unavoidable L²
derivative energy.

## 4. Cubic clipping loses strictly less than the endpoint deficit

The ordinary two-cap fiber identity gives
\[
\boxed{
|E|=\Psi(U_1)+\Psi(U_2)+G,
\quad G\ge0.
}
\tag{S2C.16}
\]
No two niches are assumed to be disjoint
in the entire ambient plane: nonempty
true interval fibers and the parent
midline ensure that their **effective**
positive portions are disjoint inside
the outer intersection.

Apply the unequal-face UFC1 tip theorem
with \(\eta=1/10\), using S2C.6–S2C.11.
Since each endpoint mismatch is \(<2\varepsilon<\eta\),

\[
\boxed{
G\le\frac{10}{3}
\left(|a_1-a_2|^3+|b_1-b_2|^3\right).
}
\tag{S2C.17}
\]

For any real x,y,
\[
|x-y|^3\le(|x|+|y|)^3
\le4(|x|^3+|y|^3),
\]
the last step being convexity of
the cube function on nonnegative reals.
With \(a_*,b_*\) as origins, this gives
\[
\boxed{
G\le\frac{40}{3}
\sum_{j=1}^{2}
(|a_j-a_*|^3+|b_j-b_*|^3).
}
\tag{S2C.18}
\]

Combine S2C.15–S2C.18:
\[
\begin{aligned}
M-|E|
&=\Delta_1+\Delta_2-G\\
&\ge
\left(\frac{140}{3}-\frac{40}{3}\right)
\sum_{j=1}^2
(|a_j-a_*|^3+|b_j-b_*|^3)\\
&=\boxed{\frac{100}{3}
\sum_{j=1}^2(|a_j-a_*|^3+|b_j-b_*|^3).}
\end{aligned}
\]
This proves S2C.3.

If every endpoint displacement vanishes,
then J_1=J_2=J_* and the niches are
confined to that shared face by S2C.11,
so \(G=0\). The **strict** fixed-width
concavity AF1/SD1 then says
\(\Delta_j=0\) only if
\(f_j=f_*,g_j=g_*\) everywhere,
hence \(U_j=U_*\).
Thus equality in the area bound
occurs exactly for the two identical
reference parents. QED.

## 5. Explicit nontrivial families inside the theorem

The allowed support class is not empty beyond \(U_*\), and
it genuinely contains competitors with **independently moving
left and right top-face endpoints**, not merely deformations
with unchanged flat faces.

Use the reference phase formulas: on
\(L-\beta<t<L\), the first-quarter curvature is
\(\rho_{*,f}=1/2\), and on \(0<t<\beta\), the
second-quarter curvature is \(\rho_{*,g}=1/2\).
Put \(t_0=L-\beta/2\), \(t_1=\beta/2\), and
\[
\phi_R(t)=
\begin{cases}(t-t_0)^3(L-t),&t_0\le t\le L,\\
0,&0\le t<t_0,\end{cases}
\]
\[
\phi_L(t)=
\begin{cases}t(t_1-t)^3,&0\le t\le t_1,\\
0,&t_1<t\le L.\end{cases}
\]
Both belong to \(W^{2,\infty}\), have zero endpoint
values, and match the unchanged support in \(C^2\)
at their interior patch boundaries. But
\[
\phi_R'(L)=-(\beta/2)^3,\qquad
\phi_L'(0)=(\beta/2)^3.
\]

For arbitrary sufficiently small independent real
parameters \(\lambda_j,\mu_j\), define cap quarter
supports by
\[
f_j=f_*+\lambda_j\phi_R,\qquad
g_j=g_*+\mu_j\phi_L
\quad(j=1,2).
\tag{S2C.19}
\]
The perturbation curvature is supported only
where the reference density is *strictly*
\(1/2\), so choosing the coefficients small
retains nonnegative curvature; the top-normal
atom remains positive, and the axis-normal
end edges are unchanged. The resulting global
support is therefore a genuine compact
convex downward one-turn cap. Its two end
roof heights remain \(1/2\); concavity of
the roof gives \(A_j(x)\ge1/2\) over the
whole projection.

The top-face endpoints move **independently**:
\[
\boxed{
a_j=a_*-\mu_j(\beta/2)^3,\quad
b_j=b_*+\lambda_j(\beta/2)^3.
}
\tag{S2C.20}
\]
The face length therefore changes by
\((\lambda_j+\mu_j)(\beta/2)^3\),
and its center changes by
\((\lambda_j-\mu_j)(\beta/2)^3/2\).
With all four parameters small enough that
S2C.2 holds, S2C.3 applies to these
**actual two-turn bodies**. They may have
unequal face lengths, displaced opposite
faces and independent nonsymmetric outer
curvatures, proving the theorem is a
substantive shape-family result rather
than a statement whose hypotheses
force both caps to equal the reference.

## 6. What this improves and what it does not

Unlike SCR1 (which treated one
two-parameter family of fixed curved
core shears), S2C1 allows
**arbitrary independently chosen
\(W^{2,\infty}\)-small perturbations**
of both complete upper support
functions, changing their smooth
curvature density, top-face positions,
top-face lengths and full niche
contact geometries.
The actual two-cap area and
connectivity are retained throughout.
The significant new mechanism is
a **cubic trace-energy inequality
that pays for the two opposite
face mismatches without imposing
horizontal reflection symmetry**.

It is **not** an unrestricted local
stability theorem in Hausdorff distance
or among all convex hulls, since
the small **second-derivative** norm
and full lower half-height rectangle
are strong geometric admission
conditions. It does not establish
that every true two-turn optimizer
has this structure, nor does it
handle arbitrary width variation,
new curvature atoms or partial
turns. No claim of global optimality
or uniqueness is made.

The analytic inputs AF/SD/SR,
the candidate curvature and
inner-corner estimates are written
historical dependencies, not
independently audited or
Lean-certified mathematical facts.
No Lean formalization, CI,
large optimization, or numerical
upper-bound certificate was run.
