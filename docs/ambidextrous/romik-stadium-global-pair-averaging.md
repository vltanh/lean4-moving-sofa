# Sharp pair-to-identical averaging along the entire Romik–stadium arc

**Theorem RSA1 (nonlocal sharp Gerver-like pair comparison).**
Let \(Y>0\) solve \(4Y^3+3Y-1=0\), let
\(\beta=\arctan Y\), and put
\[
m=\frac{\sqrt{1+Y^2}}{3Y},\quad
b_*=\frac m2,\quad W=2m,\quad
M=1+4Y^2+\arctan Y.
\]
Let \(U_*\) be Romik's **actual centered downward
one-turn cap** of projection \(I=[-m,m]\).
Let \(C\) be the centered *circular-stadium*
downward one-turn cap with the same projection,
defined by its upper support functions
\[
\boxed{
f_C(t)=(m-\tfrac12)\cos t+\tfrac12+\tfrac12\sin t,\quad
g_C(t)=(m-\tfrac12)\sin t+\tfrac12+\tfrac12\cos t.
}
\tag{RSA.1}
\]
Its top face is
\([-(m-\tfrac12),m-\tfrac12]\), and its
whole bottom half-height rectangle is present.

For every \(s,t\in[0,1]\), put
\[
U_s=(1-s)U_*+sC,\qquad
U_t=(1-t)U_*+tC,\qquad
\bar U=U_{(s+t)/2}.
\]
These are **true Minkowski combinations of
convex one-turn caps**, not formal interpolation
of two nonconvex survivors.

Define the actual complete-two-turn envelopes
\[
E_{st}=(U_s\setminus N(U_s))
\cap\rho(U_t\setminus N(U_t)),
\qquad \rho(x,y)=(x,1-y).
\]
All E_st are compact connected sofas with both
complete conventional quarter turns.
For the **entire real parameter square** \([0,1]^2\),

\[
\boxed{
|E_{st}|
\le |E_{\bar U,\bar U}|
-\frac1{6000}(s-t)^2
\le M-\frac1{6000}(s-t)^2
\le M.
}
\tag{RSA.2}
\]

If \(s\ne t\) the identical-parent
Minkowski average is a *strict* area
improvement over the mixed original.
If s=t>0, the unchanged identical-pair
area is still strictly below M, by the
unique fixed-width signed one-turn
maximizer property AF1/AF3.
Thus the only equality case is s=t=0,
Romik's reference.

This gives a **nonperturbative sharp-area
symmetrization** from two independently chosen
Gerver-like one-turn parents across a complete
interpolation from Romik to a substantially
different circular cap.
It goes beyond the small-parent-difference
condition of [MSY1](two-cap-minkowski-symmetrization-sharp-hand.md),
which is not assumed here.

The cap shape family is still restricted to
a **one-dimensional Minkowski arc** for each
of the two independently chosen parents.
No full-space sharp optimality or
generic curvature-domination theorem is
claimed. The exact F Jensen coefficient
and sharp cap value use the repo's written
AF/SD/SR analytic chains, still awaiting
independent referee verification.

## 1. All interpolants have the same circular end arcs

Both U_* and C have projection [-m,m],
height one and the full bottom half-height
rectangle. Their true Minkowski interpolants
inherit these properties.

Write \(b_s=b_*+s d_0\), where
\[
\boxed{
d_0=(m-\tfrac12)-b_*=\frac{m-1}{2}.
}
\tag{RSA.3}
\]
The exact top-face interval of U_s is
\([-b_s,b_s]\).

Romik's support formulas [RH.2]
and RSA.1 imply that on the **entire
right top-normal tail**
\[
L-\beta\le \theta\le L,\qquad L=\pi/2,
\]
the first support of U_s is
\[
\boxed{
f_s(\theta)=
b_s\cos\theta+\tfrac12+\tfrac12\sin\theta.
}
\tag{RSA.4}
\]
On the **left top-normal tail**
\(0\le\theta\le\beta\), its companion
support is
\[
\boxed{
g_s(\theta)=
b_s\sin\theta+\tfrac12+\tfrac12\cos\theta.
}
\tag{RSA.5}
\]
The remaining source arcs depend on s,
but their curvature densities lie
in [0,7/8] by convexity of the
support-curvature measure:
Romik's open-quarter densities
are in [0,7/8], and C has
constant density 1/2.

The exact rational bounds recorded
in [RH.3](romik-horizontal-misalignment-sharp-bound.md)
give
\[
\boxed{1.16<m<1.17,\qquad
1.28<R_0<1.31,\qquad
\sin\beta>7/25.}
\tag{RSA.6}
\]
Thus \(0<d_0<17/200=.085<
\frac12\sin\beta\).
Every top-face mismatch
\(\delta=d_0|s-t|\) is therefore
contained entirely inside the
**common circular tails**.

## 2. Exact circular notch-tip *upper* bound without contact order

For a fixed U_s, the roof of its
second inner forbidden wall is
\[
L_\theta(x)=
\frac{g_s(\theta)-1+x\sin\theta}{\cos\theta}.
\]
For any cap with open curvature
\(\rho_g\le1\), the derivative formula
[SR.5](curvature-only-signed-roof.md) is
\[
\frac{\partial L_\theta(x)}{\partial\theta}
=\frac{x-D_x(\theta)}{\cos^2\theta},
\quad
D_x'(\theta)=(1-\rho_g(\theta))\cos\theta\ge0.
\tag{RSA.7}
\]
Consequently \(L_\theta(x)\) is
unimodal in \(\theta\): it increases
until \(D_x(\theta)\) reaches x and
then decreases. This conclusion is
independent of the companion first
wall and its contact-switch pattern.

On the left tail RSA.5,
\(D_x(\theta)=-b_s+\tfrac12\sin\theta\).
For \(x=-b_s+d\),
\(0\le d\le d_0<\frac12\sin\beta\),
the stationary angle
\(\theta=\arcsin(2d)\) belongs to
the common early tail and is the
**global maximizer** of this
single wall over all turning angles.
Substitution into RSA.5 gives the
exact maximum
\[
\boxed{
\sup_{0<\theta<L} L_\theta(-b_s+d)
=\frac12-\sqrt{\frac14-d^2}
=:q(d).
}
\tag{RSA.8}
\]

The niche roof is the supremum of
the *minimum* of the two actual
inner-wall roofs, so it cannot
exceed the maximum of either wall.
Thus
\[
n_s(-b_s+d)\le q(d).
\]
By horizontal symmetry of every U_s,
the same bound holds at the right tip:
\[
\boxed{
n_s(b_s-d)\le q(d)\qquad(0\le d\le d_0).
}
\tag{RSA.9}
\]
No candidate-specific exposed-contact
chart has been assumed.

In addition, the support formula
RSA.4 produces an **actual exposed
circular outer flank**:
for \(0\le d\le d_0\),
\[
\boxed{
1-A_s(b_s+d)=q(d),\qquad
1-A_s(-b_s-d)=q(d).
}
\tag{RSA.10}
\]
Indeed at normal angle \(\theta\in[L-\beta,L]\)
the exposed point of the radius-1/2
circle about \((b_s,1/2)\) has coordinates
\((b_s+\frac12\cos\theta,
  \frac12+\frac12\sin\theta)\).
Its horizontal excursion ranges from
0 to \(\frac12\sin\beta>d_0\).
The downward cap roof therefore
coincides with this circle over
the asserted strips. Horizontal
reflection handles the left flank.

## 3. Integrate the *true effective clipping* in a mismatch

Assume s≤t, so \(J_s\subseteq J_t\).
The positive full niches of these
curvature-dominated caps are confined
to their corresponding top faces by
the sine-kernel baseline argument
of UFC1. The exact two-cap ordinary
area identity is
\[
|E_{st}|=\Psi(U_s)+\Psi(U_t)+G_{st},
\]
with
\[
G_{st}=\int_I\min(n_s,1-A_t)
+\min(n_t,1-A_s)\,dx.
\]

The first integrand vanishes identically:
n_s is supported on J_s, where A_t=1.
The second integrand can live only on
the two flanking strips \(J_t\setminus J_s\),
each of length
\(\delta=d_0(t-s)\).

In each strip parameterize x so the
distance from the **larger** top-face
endpoint inward is \(z\in[0,\delta]\).
Then RSA.9 and RSA.10 give the
pointwise *ordinary clipped* bound
\[
\min(n_t(x),1-A_s(x))
\le\min(q(z),q(\delta-z)).
\]
For \(0\le z\le d_0<1/10\),
\[
q(z)=\frac{z^2}{1/2+\sqrt{1/4-z^2}}
<\frac{50}{49}z^2
<\frac{11}{10}z^2,
\tag{RSA.11}
\]
since \(\sqrt{1/4-z^2}>
\sqrt{6/25}>12/25\).

Integrating both strips, with no
double-counted niche union, yields
\[
\begin{aligned}
0\le G_{st}
&\le 2\int_0^\delta
\min(q(z),q(\delta-z))\,dz\\
&<\frac{11}{5}\int_0^\delta
\min(z^2,(\delta-z)^2)dz\\
&=\frac{11}{60}\delta^3\\
&<\boxed{\frac{54043}{480000000}(s-t)^2.}
\end{aligned}
\tag{RSA.12}
\]
The last inequality uses
\(\delta=d_0|s-t|\),
\(|s-t|\le1\), \(d_0<17/200\).
This is a **global two-parent
clipping certificate** along
the whole Minkowski segment,
not a numerical sampled-angle
estimate.

## 4. An exact fixed-width Jensen margin beats clipping

The Romik and stadium caps have
identical horizontal projection,
so the fixed-width AF1 concavity
applies along the entire segment.
At \(\theta=\pi/4\), the first
support functions differ by
\[
f_C(\pi/4)-f_*(\pi/4)=
\frac12+\frac{m-1/2-R_0}{\sqrt2}.
\]
By RSA.6 and \(\sqrt2>7/5\),
\[
\boxed{
f_C(\pi/4)-f_*(\pi/4)
>\frac12-\frac{13}{28}
=\frac1{28}>\frac1{30}.
}
\tag{RSA.13}
\]

For arbitrary s,t, the support
difference is exactly
\(f_s-f_t=(s-t)(f_C-f_*)\).
Let \(\mathcal J_{st}\) denote the
Jensen gain in **the signed one-turn
area functional**,
\[
\mathcal J_{st}=
2\Psi(U_{(s+t)/2})
-\Psi(U_s)-\Psi(U_t).
\]
Because all open-quarter curvatures
are ≤7/8<1 and W>2, SR1's
signed roof equals the true positive
full niche roof. Thus the strict
concavity of AF1 gives, with
\(y=e^{-i\theta/2}((f_s-f_t)+i(g_s-g_t))\),
\[
\mathcal J_{st}
\ge\frac7{64}\int_0^L|y'|^2d\theta.
\]

The fixed-endpoint Dirichlet trace
inequality at \(\theta=L/2=\pi/4\)
is
\[
|y(L/2)|^2\le\frac L4\int|y'|^2.
\]
Using RSA.13 gives
\[
\begin{aligned}
\mathcal J_{st}
&\ge\frac7{64}\frac4L
|f_s(L/2)-f_t(L/2)|^2\\
&>\frac7{8\pi}\frac{(s-t)^2}{900}\\
&>\boxed{\frac{49}{158400}(s-t)^2,}
\end{aligned}
\tag{RSA.14}
\]
where \(\pi<22/7\).

An exact rational comparison yields
\[
\boxed{
\frac{49}{158400}
-\frac{54043}{480000000}
>\frac1{6000}.
}
\tag{RSA.15}
\]
Consequently \(\mathcal J_{st}-G_{st}\)
is at least \((s-t)^2/6000\).
Use the exact ordinary two-cap area
identity and the existing full
one-turn sharp value WV2:
\[
\begin{aligned}
|E_{st}|
&=\Psi(U_s)+\Psi(U_t)+G_{st}\\
&\le2\Psi(U_{(s+t)/2})-\frac{(s-t)^2}{6000}\\
&=|E_{\bar U,\bar U}|-\frac{(s-t)^2}{6000}\\
&\le M-\frac{(s-t)^2}{6000}.
\end{aligned}
\]
This proves RSA.2.

## 5. Admissibility and the actual turning motions

Both parents contain the entire
half-height lower rectangle.
The complete forbidden corner
of any Minkowski interpolation
is the corresponding convex
combination of Romik's and the
stadium's corner heights at the
same angle. Romik has maximum
corner height <13/30. For the
stadium, the exact corner height is
\[
C_{y,C}(\theta)=
(2m-1)\sin\theta\cos\theta+
\tfrac12-\tfrac12(\sin\theta+\cos\theta).
\]
As a function of
\(z=\sin\theta+\cos\theta\in[1,\sqrt2]\)
this expression is increasing,
so its maximum occurs at
\(\theta=\pi/4\) and equals
\(m-\sqrt2/2<.47<1/2\),
using RSA.6 and \(\sqrt2>7/5\).

Thus all parent full niches remain
strictly below the horizontal midline.
Every one-turn survivor, and every
pairwise two-turn intersection E_st,
has interval vertical sections
containing y=1/2 across the entire
projection [-m,m]. All E_st are
compact connected and follow both
**complete continuous conventional
turning motions** given by the
actual parent support functions.
They are not merely full-niche
area expressions unaccompanied by
feasible turning paths.

## 6. What the theorem does not prove

RSA1 is **strictly stronger than a
near-reference Taylor theorem**
along this specific Minkowski arc:
s and t vary arbitrarily over
[0,1], including pairing the full
Romik cap against the full stadium
cap. No small norm difference is
assumed and no angular-contact
chart is frozen.

It remains a restricted family.
An arbitrary competitor is not
known to lie on this segment, even
after an area-preserving operation;
the caps of an arbitrary moving
sofa may have unequal widths,
curvature atoms or positive niche
leakage. RSA1 therefore does **not**
prove the unrestricted Romik
optimality conjecture or uniqueness.

The correct globally relevant
candidate remains [MSY1]
(two-cap-minkowski-symmetrization-sharp-hand.md):
a proof that the true Minkowski
average pays for the mixed-pair
clipping gain. RSA1 supplies a
nontrivial whole-family positive
example using the **exact Romik
circular flank and niche-tip
geometry**.
No numerical optimizer or
computer area certificate is part
of the proof; AF/SD/SR/WV written
analytic chains remain
independently unreviewed.
