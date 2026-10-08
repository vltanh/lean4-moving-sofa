# A strict *sharp* hand theorem for two independently sheared Romik cores

**Theorem SCR1 (genuinely asymmetric curved-core sharp stability).**
Let \(Y\) be the positive zero of
\(4Y^3+3Y-1\), put \(\beta=\arctan Y\),
\[
T=\frac{\sqrt{1+Y^2}}{3Y},\qquad
R_0=\frac{\cos\beta}
{\sin(3\beta/2+\pi/8)},\qquad
M=1+4Y^2+\arctan Y,
\]
and let \(U_*\) be Romik's centered
downward one-turn reference cap.
Translate it horizontally to
projection \([0,2T]\) and write the
**exact rectangular-core decomposition**
from [HF2](one-turn-half-width-top-face.md)
as
\[
U_0=V_0+
\bigl([0,T]\times[0,\tfrac12]\bigr),
\tag{SCR.1}
\]
where \(V_0\) is convex, has bottom base
\([0,T]\times\{0\}\), height \(1/2\),
width T and the **unique top point**
\((T/2,1/2)\).

For any real \(\delta\), define the
*horizontal shear of the curved core*
\[
A_\delta(x,y)=(x+2\delta y,y),
\quad
V_\delta=A_\delta V_0,\qquad
U_\delta=V_\delta+
\bigl([0,T]\times[0,\tfrac12]\bigr).
\tag{SCR.2}
\]

For **any two independent shear parameters**
\[
\boxed{|\delta_1|,|\delta_2|\le1/2000}
\]
form the actual two-turn intersection
\[
E_{\delta_1,\delta_2}
=(U_{\delta_1}\setminus N(U_{\delta_1}))
\cap\rho(U_{\delta_2}\setminus N(U_{\delta_2})),
\quad\rho(x,y)=(x,1-y).
\]

Then E is compact, connected and feasible
for both **full conventional 90-degree turns**
from the same incoming unit corridor, and

\[
\boxed{
|E_{\delta_1,\delta_2}|
\le M-\frac3{250}(\delta_1^2+\delta_2^2)
\le M.
}
\tag{SCR.3}
\]

Equality occurs at \(\delta_1=\delta_2=0\),
where E is exactly Romik's reference sofa.
Thus **every nonzero deformation in this
explicit two-parameter curved and potentially
asymmetric family has strictly smaller area
than the sharp target**.

This is a pen-and-paper strict *local*
sharp theorem for Gerver-like curved
core-plus-rectangle data. It uses the
written fixed-width signed calibration
[AF1/SD1](stability-fixed-width-deficit.md)
and [SR1](curvature-only-signed-roof.md),
and the independently proved **cubic
ordinary clipping bound**
[CCC1](curved-core-cubic-clipping-hand-bound.md).
Those older analytic chains have not
received independent referee or Lean
verification. Nothing here asserts
that arbitrary ambidextrous sofas are
small shears of the reference. The
unrestricted sharp conjecture remains open.

## 1. The sheared core keeps its exact width and half-height rectangle

The explicit first and last support
phases of the reference show that the
point \((T,0)\) supports V_0 at
normal \((\cos\beta,\sin\beta)\),
while \((0,0)\) supports at
\((-\cos\beta,\sin\beta)\).
In both directions the core support
equals the relevant bottom endpoint's
dot product. Hence every point (x,y)
of V_0 satisfies the **exact wedge**
\[
\boxed{Yy\le x\le T-Yy.}
\tag{SCR.4}
\]

For \(|\delta|\le1/100\), we have
\(2|\delta|<Y\). The shear therefore
preserves
\[
0\le x+2\delta y\le T
\qquad((x,y)\in V_0).
\]
It leaves the whole bottom segment
\([0,T]\times\{0\}\) fixed.
Thus V_\delta has exact horizontal
projection \([0,T]\), height 1/2,
and top point \((T/2+\delta,1/2)\).
Consequently U_\delta is a genuine
height-one downward convex cap
with the **fixed** projection [0,2T],
the complete half-height rectangle
\([0,2T]\times[0,1/2]\), and
top face
\[
\boxed{J_\delta=[T/2+\delta,3T/2+\delta].}
\tag{SCR.5}
\]

Convexity, presence of the full
bottom segment, and support
additivity imply downward closure:
every point of U_\delta is joined
vertically to its bottom point
in the same convex set.

## 2. Global strict curvature gap and low niche height

The reference cap has no
open-upper-quarter singular curvature
and its density satisfies
\(0\le\rho_*\le7/8\).
The curved core V_0 has the same
open-quarter curvature because the
rectangle contributes only
axis-normal atoms.

Under the nonsingular shear
\(A_\delta\) with determinant one,
the radius-of-curvature density at
unit normal n transforms as
\[
\rho_{V_\delta}(n)
=\frac{\rho_{V_0}(n')}
{|A_\delta^Tn|^3},
\qquad
n'=\frac{A_\delta^Tn}{|A_\delta^Tn|},
\tag{SCR.6}
\]
on the smooth or a.e. nonsmooth
outer arcs. Straight corner-normal
intervals remain intervals of zero
density; the bottom-facet atom stays
at the downward vertical normal,
and the rectangular summand introduces
only axis-normal atoms.
The whole upper semicircle therefore
retains absolutely continuous
open-quarter curvature, with
\[
\rho_{U_\delta}\le
\frac{7/8}{(1-2|\delta|)^3}
\le \frac{7/8}{(49/50)^3}
<\frac{15}{16}.
\tag{SCR.7}
\]
The final inequality follows from
\(14{,}000{,}000<14{,}117{,}880\)
by exact cross multiplication.
Thus each U_\delta satisfies CCC1's
strict curvature premise with
\(\eta=1/16\).

Moreover every point of V_0 moves by
at most \(|\delta|\), because its height
is at most 1/2. Consequently the unit-normal
support functions of U_\delta and U_0
differ by at most \(|\delta|\).
The corresponding canonical inner
corner's vertical coordinate is
linear in the two supports with
coefficients s,c≥0, so it changes
by at most
\((s+c)|\delta|\le2|\delta|\).
The explicitly established Romik
corner bound
\(\max c_{0,y}<13/30\) therefore gives
\[
\boxed{\max c_{\delta,y}
<13/30+1/50<1/2
\quad(|\delta|\le1/100).}
\tag{SCR.8}
\]
Every forbidden positive niche lies
below its corner, hence
\[
0\le n_{U_\delta}(x)<1/2.
\tag{SCR.9}
\]

The strict curvature gap also gives
**top-face niche confinement with no
assumed contact pattern**:
using the positive sine kernel and
the top endpoint derivatives as in
[CCC.5–CCC.8](curved-core-cubic-clipping-hand-bound.md),
\[
f(t)-1\le b_\delta\cos t
-\eta(1-\sin t),\qquad
g(t)-1\le-a_\delta\sin t
-\eta(1-\cos t).
\]
Thus for x≥b_\delta the *first*
inner-wall roof is nonpositive,
and for x≤a_\delta the *second*
roof is nonpositive, at **every**
turn angle. Therefore
\[
\boxed{\operatorname{supp} n_{U_\delta}
\subseteq J_\delta.}
\tag{SCR.10}
\]

These statements hold for arbitrary
signs of the two shear parameters,
not merely outward perturbations.

## 3. The actual two-turn shape is compact, connected and feasible

Each U_\delta contains the whole
incoming half-height rectangle and
its niche lies below 1/2.
Its one-turn survivor has interval
vertical sections
\([n_\delta(x),A_\delta(x)]\)
containing y=1/2 at every x.
The intersection of the lower survivor
with the upper reflected survivor
therefore has nonempty interval
sections containing the same midline,
over all x∈[0,2T].
Its union is connected.

Every point of the intersection
satisfies the **complete** canonical
support-tightened lower turning
family of its first parent cap
and the complete reflected upper
family of the second. Support continuity
provides their actual continuous rigid
motions; both use the same incoming
orientation and unit-height strip.
So this is a valid connected
ambidextrous sofa, not a mere
pair of incompatible corridor
snapshots.

## 4. The weighted one-turn deficit is *quadratic* in a shear

This step is the reason the new
cubic clipping bound is useful.
The reference U_0 is the unique
maximizer, at its fixed width,
of the **signed adaptive one-turn**
functional F from [AF1](adaptive-functional-global-calibration.md).
The signed-roof identity
[SR1](curvature-only-signed-roof.md)
applies to each U_\delta because
\(0\le\rho<1\).
Here the width is \(2T>2\), so
the two axis-angle forbidden
quadrants already contribute
roof zero over every horizontal
abscissa; the *signed* roof is
nonnegative. Therefore its signed
integral equals the **actual**
full positive niche area and
\[
\boxed{
\Psi(U_\delta)=F(f_\delta,g_\delta)-T,
\qquad
\Psi(U_0)=M/2.
}
\tag{SCR.11}
\]

Translate all profiles by the
**same horizontal vector** (−T,0)
to meet AF's centered fixed-width
endpoint convention. The differences
f_\delta−f_0 and g_\delta−g_0
are unchanged by this centering.
By the exact fixed-width energy
[SD1](stability-fixed-width-deficit.md),
\[
\boxed{
\Delta_\delta:=M/2-\Psi(U_\delta)
\ge\frac7{4\pi}
|f_\delta(\pi/4)-f_0(\pi/4)|^2.
}
\tag{SCR.12}
\]

We now give an **explicit nonzero
support displacement**, rather than
assuming strictness from uniqueness.
On the reference curved core's
middle support arc,
\[
h_{V_0}(n_t)
=R_0\cos(t/2+\pi/8)
\qquad(\beta<t<\pi/2-\beta).
\tag{SCR.13}
\]
At \(t=\pi/4\), its unique exposed
point has y-coordinate
\[
y_*=
h_{V_0}(\pi/4)\sin(\pi/4)
+h'_{V_0}(\pi/4)\cos(\pi/4)
=\frac{R_0}{4}>\frac14.
\tag{SCR.14}
\]

For \(n=(1,1)/\sqrt2\),
\[
h_{V_\delta}(n)=
h_{V_0}(A_\delta^Tn),\qquad
A_\delta^Tn=(1,1+2\delta)/\sqrt2.
\]
Its direction angle
\(\theta_\delta=\arctan(1+2\delta)\)
stays inside the strict middle
support arc when
\(|\delta|\le1/100\), and
\[
|\theta_\delta-\pi/4|\le2|\delta|.
\]
Along that arc, the exposed
reference point's vertical
coordinate has angular derivative
\(\rho_{V_0}(\theta)\cos\theta\),
of absolute value at most 7/8.
Thus its y-coordinate remains
\[
y(\theta_\delta)\ge
R_0/4-\tfrac78(2/100)
>R_0/5>1/5.
\tag{SCR.15}
\]
The middle strict inequality
uses \(R_0>1\), and the final
one is immediate.

Differentiate the support with
respect to the shear: by the
unique exposed-point envelope
derivative,
\[
\frac{d}{d\delta}
h_{V_\delta}(n)
=\sqrt2\,y(\theta_\delta)
>\sqrt2/5>1/4.
\]
The rectangle summand R_T is
independent of δ, so this is
also the derivative of
\(f_\delta(\pi/4)\).
Integrating between zero and δ,
for either sign, gives
\[
\boxed{
|f_\delta(\pi/4)-f_0(\pi/4)|
\ge |\delta|/4.
}
\tag{SCR.16}
\]

Combine SCR.12–SCR.16 and
the rational bound \(\pi<22/7\):
\[
\boxed{
\Delta_\delta\ge
\frac7{64\pi}\delta^2
>\frac1{30}\delta^2.
}
\tag{SCR.17}
\]
This strict, explicitly positive
**quadratic** weighted deficit is
derived from an actual curved
support displacement. It is not
a free assumption about arbitrary
asymmetric competitors.

## 5. Pay the entire cubic clipping correction

Put \(a_i=T/2+\delta_i\), so the
two actual top faces are
\([a_i,a_i+T]\). Set
\(d=|\delta_1-\delta_2|\).
Because the two parents have the
same projection and satisfy
SCR.7–SCR.10, the exact
ordinary-area two-cap identity
OT1 and the cubic hand theorem
CCC1 give
\[
\begin{aligned}
|E_{\delta_1,\delta_2}|
&=\Psi(U_{\delta_1})+
\Psi(U_{\delta_2})+G,\\
0\le G&\le\frac{2d^3}{3(1/16)}
=\frac{32}{3}d^3.
\end{aligned}
\tag{SCR.18}
\]

For \(|\delta_i|\le\varepsilon=1/2000\),
we have \(d\le2\varepsilon<1/16\),
and
\[
d^3\le
(2\varepsilon)\,d^2
\le4\varepsilon(\delta_1^2+\delta_2^2),
\]
using \((x-y)^2\le2(x^2+y^2)\).
Thus
\[
\boxed{
G\le\frac{128}{3}\varepsilon
(\delta_1^2+\delta_2^2)
=\frac8{375}(\delta_1^2+\delta_2^2).
}
\tag{SCR.19}
\]

The two genuine one-turn deficits
by SCR.17 add to more than
\((\delta_1^2+\delta_2^2)/30\).
Subtract the entire positive G:
\[
\begin{aligned}
M-|E|
&=\Delta_{\delta_1}
+\Delta_{\delta_2}-G\\
&\ge
\left(\frac1{30}-\frac8{375}\right)
(\delta_1^2+\delta_2^2)\\
&=\boxed{\frac3{250}
(\delta_1^2+\delta_2^2).}
\end{aligned}
\tag{SCR.20}
\]
This proves the quantitative
sharp inequality SCR.3,
with equality at the undeformed
Romik sofa.

## 6. Why this is not the global conjecture

The theorem covers **actual smooth
curved cores**, not just polygonal
or triangular toy cores, and permits
two **independent** nonzero shears.
The two caps have different top
faces, so the positive clipping
term cannot simply be set to zero;
the cubic-vs-quadratic mechanism
pays for it rigorously.

But it only covers shears
\(|\delta_i|\le1/2000\) of **one fixed
Romik core**. An unrestricted
optimal sofa may have a very
different core, may lack the
rectangular-core decomposition,
may have curvature atoms, may
have an arbitrary face displacement,
or may offer only partial original
turns. No reduction to the
two-shear family has been proved.

This local theorem's historical
inputs AF1, SD1, SR1 and the
Romik support constants remain
self-reviewed in the repository.
No independent refereeing,
Lean/Lake compilation, CI or
numerical global upper-bound
search was carried out.
