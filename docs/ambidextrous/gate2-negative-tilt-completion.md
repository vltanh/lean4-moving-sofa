# Gate 2: exact completion for the larger negative middle tilts

**October 10, 2026. Written mathematical reduction; Gate 2 remains open.**
This note closes a whole branch of the selected partial-cap maximizer
domain using the completed Gate 1 value. It uses the exact
[used-support saturation](gate2-partial-cap-domain-reductions.md), not an
assumed full-turn extension of an original physical body.

Write \(L=\pi/2\), \(I=[-2C,2C]\), \(J=[-C,C]\), and use the walls,
partial roof \(q_{U,\alpha}\), and spatial score \(\mathcal P_\alpha\) of
[PD.1–PD.3](gate2-partial-cap-domain-reductions.md). We compare the actual
partial cap score with the full cap score on this same cap. Labels NT are
local.

## 1. The selected negative-tilt geometry

Let \((U,\alpha)\) be a height-one global cap-and-angle maximizer in the
PD3 canonical form, with \(\alpha<L\) and a strictly negative middle slope:

\[
A(-C)=1,\qquad A(C)=1-h,\qquad h>0.
\tag{NT.1}
\]

The middle-facet normal is

\[
\theta_0=L-\arctan\frac{h}{2C}.
\tag{NT.2}
\]

The right endpoint of the height-one top face is exactly \((-C,1)\).
Indeed, the negative affine slope makes \(A(x)<1\) for \(x>-C\), while
PD4 gives the top point at \(-C\). Therefore, if \(\alpha\ge\theta_0\),
all missing first supports are attained at this point:

\[
h_U(\cos t,\sin t)=-C\cos t+\sin t
\qquad(\alpha<t<L).
\tag{NT.3}
\]

If instead \(\alpha<\theta_0\), PD5 shows that there is no charged wing
curvature on \((\alpha,L)\). The middle facet, at normal \(\theta_0\),
cannot extend to the right of \(C\): a positive extension would itself
be charged curvature in this unused open arc. Its right endpoint is
therefore \((C,1-h)\). On either side of its single normal atom the
supporting point is constant, giving

\[
h_U(\cos t,\sin t)=
\begin{cases}
C\cos t+(1-h)\sin t,&\alpha<t<\theta_0,\\
-C\cos t+\sin t,&\theta_0<t<L.
\end{cases}
\tag{NT.4}
\]

At \(\theta_0\) these expressions agree; at \(\alpha\) the first has the
correct support value by continuity, whether or not a terminal facet is
present. No regularity of the used normal arcs or source identity is
needed here.

## 2. Dominate every missing first wall

**Theorem NT1.** In the domain above, either of the conditions

\[
\alpha\ge\theta_0
\qquad\text{or}\qquad h\ge1-\sin\alpha
\tag{NT.5}
\]

implies

\[
\boxed{n_U(x)\le q_{U,\alpha}(x)\quad(x\in J),
\qquad\mathcal P_\alpha(U)\le\mathcal P_L(U)\le M/2.}
\tag{NT.6}
\]

For NT.3, the missing first wall is

\[
R_t(x)=(-C-x)\cot t+1-\csc t\le0
\qquad(x\in J).
\]

Every corresponding two-wall niche value is at most this first wall,
so no missing positive niche is created. This proves NT.6 when
\(\alpha\ge\theta_0\).

Otherwise use NT.4. The part \(t\ge\theta_0\) is again nonpositive.
For \(\alpha\le t\le\theta_0\), put \(z=C-x\in[0,2C]\). The missing
first wall is

\[
F_z(t)=1-h+\frac{z\cos t-1}{\sin t},\qquad
F_z'(t)=\frac{\cos t-z}{\sin^2t}.
\tag{NT.7}
\]

If \(z\ge\cos\alpha\), this derivative is nonpositive for all
\(t\ge\alpha\). Thus \(F_z(t)\le F_z(\alpha)=R_\alpha(x)\).

If \(0\le z\le\cos\alpha<1\), the maximum of \(F_z\) over the larger
interval \([\alpha,L]\) is attained at \(t=\arccos z\), with the endpoint
interpretation at \(z=0\). Its value is

\[
1-h-\sqrt{1-z^2}\le1-h-\sin\alpha.
\tag{NT.8}
\]

This is nonpositive under the second condition in NT.5. Hence every
missing first wall is at most \(\max\{0,R_\alpha(x)\}\), and every missing
two-wall minimum is at most the same quantity. The already visited
angles are included in \(q_{U,\alpha}\). This proves the first inequality
in NT.6 pointwise. Subtract its middle integral from the unchanged
exterior reward and apply Gate 1 to obtain the two score inequalities.

This is a comparison between cap functionals in a proved maximizer
normal form. It does not assert that every partial-motion physical body
can be completed in place.

## 3. The exact remaining negative-tilt region

An above-reference selected partial-cap maximizer with negative middle
slope must therefore satisfy both

\[
\boxed{0<h<1-\sin\alpha,
\qquad\alpha< L-\arctan\frac{h}{2C}.}
\tag{NT.9}
\]

In terms of the missing angle \(\varepsilon=L-\alpha\), this gives the
explicit small-height restriction

\[
0<h<1-\cos\varepsilon\le\varepsilon^2/2.
\tag{NT.10}
\]

There is also an exact localization of every possible failure of the
pointwise comparison. Under NT.9, NT.7–NT.8 show that any point where a
missing first wall exceeds both zero and the terminal first wall must
satisfy

\[
\sqrt{2h-h^2}<C-x<\cos\alpha.
\tag{NT.11}
\]

Indeed, \(C-x\ge\cos\alpha\) is covered by the monotonicity in NT.7,
and a positive value in NT.8 requires
\(1-h>\sqrt{1-(C-x)^2}\), equivalent to the strict lower bound in
NT.11. Thus the uncharged missing contribution is confined to this
explicit right-hand subinterval of \(J\); it is not asserted to vanish
there.

The remaining small negative tilt, the horizontal middle, and every
positive middle tilt still require the terminal-source sharp value
argument. NT1 removes the other negative-tilt cases from that global
obligation without assuming endpoint pressure, a curvature cap, or
ordinary survivor feasibility.
