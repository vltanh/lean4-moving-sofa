# Gate 2: an all-width terminal-angle exclusion

**October 10, 2026. Written mathematical proof, independently audited
within this research session.** The actual 45-degree
two-wall niche together with the whole outgoing first wall excludes a
further terminal-angle interval, uniformly over the entire downward-cap
domain. All floor, window, and wall-switch clipping is retained. No
stationary curvature law, terminal source occupation, reflection symmetry
of the partial objective, or numerical search enters this argument.

Write

\[
M=1+4Y^2+\arctan Y,\qquad 4Y^3+3Y=1,\quad Y>0.
\]

**Theorem AT1.** For every compact downward convex cap of height at most
one, with its own middle-half window, and every
\(\pi/4\le\alpha\le\arctan(8/3)\),

\[
\boxed{\mathcal P_\alpha(U)<\frac{5259}{6400}
<\frac{411}{500}<\frac M2.}
\tag{AT.1}
\]

Here \(\mathcal P_\alpha\) is exactly PD.1–PD.3 in
[the partial-domain reductions](gate2-partial-cap-domain-reductions.md),
including its **whole outgoing first wall**. In particular, any cap with
score at least \(M/2\) has \(\alpha>\arctan(8/3)\). This is an
individual scalar-cap exclusion; it does not close Gate 2's remaining
partial-angle interval or by itself impose this lower bound separately
on the two angles of a common-hull competitor.

## 1. Reduction and the three actual supports

PD.6–PD.15 supply height extrusion, middle-chord reduction, coercivity,
attainment, and top insertion. The attainment proof also applies with
\(\alpha\) fixed: if a cap has score greater than \(41/50\), the
fixed-angle maximum is attained inside the same compact width interval.
Its canonical representative has height one, an affine middle roof, and
a top face meeting the middle window. Thus, a hypothetical cap with score
at least \(5259/6400\) yields such a canonical fixed-angle maximizer
with at least the same score. It suffices to rule out that maximizer.
No maximization in the angle is needed.

Center the projection and introduce the parameters

\[
I=[-2C,2C],\quad J=[-C,C],\quad
K=\sqrt2-1,\quad \kappa=\cot\alpha,\quad
d=\frac{\kappa}{1+\sqrt{1+\kappa^2}}.
\tag{AT.2}
\]

The previously proved outgoing-only estimate handles
\(\alpha\le\arctan(5/4)\). For the new interval it suffices to take

\[
\frac38\le\kappa\le\frac45,\qquad
\kappa d=\sqrt{1+\kappa^2}-1,\qquad
\kappa=\frac{2d}{1-d^2},\qquad 0<d<K.
\tag{AT.3}
\]

Use the actual supports to define

\[
u=\max_U(x+y)-1,\quad v=\max_U(-x+y)-1,\quad
b=\max_U\left(x+\frac{y-1}{\kappa}\right).
\tag{AT.4}
\]

The three outer support lines are
\(1+u-x\), \(1+v+x\), and \(1-\kappa(x-b)\). The actual outgoing
inner wall is \(\kappa(b-d-x)\). Consequently

\[
\begin{aligned}
A(x)&\le \min\{1,1+u-x,1+v+x,1-\kappa(x-b)\},\\
q_{U,\alpha}(x)&\ge
\max\{0,\min(u-K-x,v-K+x),\kappa(b-d-x)\}.
\end{aligned}
\tag{AT.5}
\]

The 45-degree angle is genuinely visited throughout the new interval.
Only the displayed lower bound on the true niche is used.

There is an essential compatibility condition between the two first
supports:

\[
\boxed{b\le u\le 2(1-\kappa)C+\kappa b,
\qquad u,v,b\le2C.}
\tag{AT.6}
\]

Indeed, \(y\le1\) and \(\kappa<1\) give
\(x+(y-1)/\kappa\le x+y-1\), hence \(b\le u\). At a point attaining
\(u\),

\[
\kappa b\ge\kappa x+y-1=u-(1-\kappa)x
\ge u-2(1-\kappa)C.
\]

The remaining upper bounds follow directly from the containing box.

Since the middle is affine and its top meets \(J\), either
\(A(-C)=1\) or \(A(C)=1\). The first alternative gives
\(v\ge C\) and \(u,b\ge-C\); the second gives \(u,b\ge C\) and
\(v\ge-C\). These alternatives will be handled directly.

## 2. Two preliminary width cuts

### 2.1 The 45-degree relaxation alone handles \(C\le49/100\)

Put

\[
g_C(z)=\int_C^{2C}(x-z)_+\,dx
=\frac{(2C-z)_+^2-(C-z)_+^2}{2}.
\]

For this paragraph only, the 45-degree relaxation is reflection
invariant, so label the high endpoint as the left one. Then
\(v\in[C,2C]\), \(u\in[-C,2C]\), and the support bounds give

\[
P_{45}\le F_{45}(u,v):=2C-g_C(u)-g_C(v)
-\int_{-C}^C[\min(u-K-x,v-K+x)]_+\,dx.
\tag{AT.7}
\]

This function is concave on that rectangle. Here is a clipping-inclusive
verification which will also be used below. For an integrated maximum of
two affine lines with different spatial slopes, the moving intersection
contributes the nonnegative second variation

\[
\frac{(\hbox{difference of varied intercepts})^2}
{|\hbox{difference of spatial slopes}|}.
\tag{AT.8}
\]

An integrated minimum has the opposite sign. These formulas follow by
integrating the triangle swept out by the moving intersection. A switch
outside the integration interval contributes zero. The resulting
integrals are continuously differentiable and piecewise quadratic in
the intercepts, so checking their quadratic second variations on the
open pieces also checks concavity across all clipping boundaries.

For the loss \(2C-F_{45}\), the sole negative term can occur at an
exposed tent apex inside \(J\); it is
\(- (\xi-\eta)^2/2\), for variations \((\xi,\eta)\) of \((u,v)\).
The left outer switch supplies \(\eta^2\). If \(u>C\), the right
outer switch supplies \(\xi^2\). If \(u\le C\) and the apex is
positively exposed, its falling side meets the floor at
\(u-K\in(-C,C)\), supplying \(\xi^2\) instead. Thus the loss has
nonnegative second variation; cases without an exposed interior apex
already have only nonnegative terms. Boundary parameters follow by
continuity.

For \(C\ge K/2\), the common critical point
\(u=v=C+K/2\) lies in the rectangle. Its positive tent is contained in
\(J\), and AT.7 is at most

\[
2C-2(C-K/2)^2.
\tag{AT.9}
\]

For \(C<K/2\), the trivial bound \(P_{45}\le2C<K\) suffices. The
right side of AT.9 increases up to \(C=49/100\), and

\[
\frac{49}{50}-\frac12\left(\frac{49}{50}-K\right)^2
<\frac{41}{50}.
\tag{AT.10}
\]

For an exact check, \(\sqrt2<99/70\) gives
\(49/50-K=99/50-\sqrt2>2\sqrt2/5\). Hence every remaining
canonical cap has \(C>49/100\).

### 2.2 For \(\kappa\ge3/5\), the outgoing wall handles \(C\le1/2\)

The outgoing-only calculation PD.16 gives, for every cap,

\[
\mathcal P_\alpha\le(1+\sqrt{1+\kappa^2})C-2\kappa C^2.
\tag{AT.11}
\]

For \(C\le1/2\) and \(3/5\le\kappa\le4/5\), this expression
increases with \(C\); at \(C=1/2\) it decreases with \(\kappa\).
Therefore it is at most

\[
\frac{2+\sqrt{34}}{10}<\frac45.
\tag{AT.12}
\]

It remains to consider

\[
\begin{cases}
C>49/100,&3/8\le\kappa\le3/5,\\
C>1/2,&3/5\le\kappa\le4/5.
\end{cases}
\tag{AT.13}
\]

## 3. The exact finite-support relaxation and the high-right case

For \(b\le u\), write

\[
x_0=\frac{u-\kappa b}{1-\kappa},\qquad
Q_C(u,b)=\int_C^{2C}\max\{0,x-u,\kappa(x-b)\}\,dx
=\kappa g_C(b)+(1-\kappa)g_C(x_0).
\tag{AT.14}
\]

The identity follows from \(b\le u\le x_0\): the three successive
active pieces are zero, \(\kappa(x-b)\), and \(x-u\), with any
pieces outside \([C,2C]\) automatically clipped by \(g_C\).

Define

\[
\begin{aligned}
N(u,v,b)&=\int_{-C}^C
\max\{0,\min(u-K-x,v-K+x),\kappa(b-d-x)\}\,dx,\\
F(u,v,b)&=2C-g_C(v)-Q_C(u,b)-N(u,v,b).
\end{aligned}
\tag{AT.15}
\]

In either high-endpoint alternative the left exterior majorant in AT.5
is \(\min(1,1+v+x)\), and the right exterior majorant is
\(1-\max(0,x-u,\kappa(x-b))\). Thus
\(\mathcal P_\alpha\le F\).

Suppose first that the high endpoint is on the right and \(v<C\).
Increase \(v\) to \(C\), keeping \(u,b\) fixed. This is a variation
of the relaxation; it need not preserve realizability by a cap. The
charged left exterior reward increases at rate \(C\). The derivative
of \(N\) is the length of the interval on which the rising tent line
\(v-K+x\) is exposed. Put

\[
p=\frac{u-v}{2},\quad e=b-d,\quad
x_L=\frac{\kappa e-v+K}{1+\kappa}.
\tag{AT.16}
\]

Every such exposed point lies between \(x_L\) and \(p\), so its
length is at most \((p-x_L)_+\). Since \(u\le2C\), \(v\le C\),
and \(b\ge C\),

\[
p-x_L\le
\frac{(3-\kappa)C+2\kappa d-2K}{2(1+\kappa)}<C.
\tag{AT.17}
\]

The strict inequality uses \(\kappa>1/3\) and \(\kappa d<K\).
Hence \(F\) strictly increases until \(v=C\). All of AT.6 is
preserved. It is therefore enough to bound \(F\) on the convex domain

\[
\boxed{D_C=\{C\le v\le2C,\ -C\le b\le2C,
\ b\le u\le2(1-\kappa)C+\kappa b\}.}
\tag{AT.18}
\]

This also contains the original high-left alternative. No reflection of
the partial objective has been used.

## 4. Two convex domains cover the useful part of the relaxation

Put

\[
a=u-K,\quad c=v-K,\quad e=b-d,\quad
Y_0=(1+\kappa)C+K-v+\kappa(b-d).
\tag{AT.19}
\]

Thus \(Y_0\ge0\) means \(x_L\ge-C\). Define the two convex sets

\[
D_1=D_C\cap\{a\le C\},\qquad
D_2=D_C\cap\{Y_0\ge0\}.
\tag{AT.20}
\]

**Lemma AT2.** The function \(F\) is concave on each of \(D_1,D_2\).

**Proof.** Work at generic parameters in the relative interiors of the
finite quadratic pieces, and use variations \((\xi,\eta,\zeta)\)
of \((u,v,b)\). As in AT.8, all switches of the positive niche
contribute nonnegative second variations except an exposed tent apex
\(p=(u-v)/2\) inside \(J\). If there is no such apex, the loss
\(2C-F=g_C(v)+Q_C+N\) is already convex on that piece. Otherwise the
only negative term is

\[
-\frac{(\xi-\eta)^2}{2}.
\tag{AT.21}
\]

Throughout the interior of \(D_C\), the left outer switch contributes
\(\eta^2\). The complete compensation is as follows.

**On \(D_1\).** If \(a\ge e\), the exposed falling tent meets the
floor at \(x=a\in(-C,C)\). This contributes \(\xi^2\).
If \(a<e\), it instead meets the terminal wall at

\[
x_R=\frac{a-\kappa e}{1-\kappa}\in(p,C),
\]

which contributes \((\xi-\kappa\zeta)^2/(1-\kappa)\).
For \(e<C\), the subsequently exposed terminal wall meets the floor
at \(e\in(-C,C)\), contributing \(\kappa\zeta^2\). For
\(e>C\), instead \(b=e+d\in(C,2C)\), and the outer right
height/terminal switch at \(b\) supplies the same contribution.
In both cases

\[
\frac{(\xi-\kappa\zeta)^2}{1-\kappa}
+\kappa\zeta^2\ge\xi^2.
\tag{AT.22}
\]

Thus the positive contributions include \(\xi^2+\eta^2\), which
dominate AT.21.

**On \(D_2\), outside \(D_1\).** Now \(u>C+K\). Consequently
\(C<x_0<2C\), so the outer terminal/45-degree switch contributes
\((\xi-\kappa\zeta)^2/(1-\kappa)\).
If \(c+e>0\), the rising tent meets the terminal wall at
\(x_L\in(-C,p)\); this contributes
\((\eta-\kappa\zeta)^2/(1+\kappa)\). The inequality

\[
\frac{(\xi-\kappa\zeta)^2}{1-\kappa}
+\frac{(\eta-\kappa\zeta)^2}{1+\kappa}
\ge\frac{(\xi-\eta)^2}{2}
\tag{AT.23}
\]

cancels AT.21.

If \(c+e<0\), the rising tent instead emerges from the floor at
\(-c>e\). The support compatibility and \(u>C+K\) give

\[
\kappa(e+C)\ge u-(2-3\kappa)C-\kappa d
>(3\kappa-1)C+K-\kappa d>0.
\tag{AT.24}
\]

Hence \(-C<e<-c<p\). The terminal/floor switch at \(e\) supplies
\(\kappa\zeta^2\), and the rising-tent/floor switch at \(-c\)
supplies \(\eta^2\). AT.22 again supplies \(\xi^2\), cancelling
the only negative term.

All remaining switch terms are nonnegative. The affine spatial slopes
\(0,1,-1,-\kappa\) are distinct, so ties have zero spatial measure;
the integrals in AT.15 are continuously differentiable and piecewise
quadratic in the parameters. The verified nonnegative second variations
therefore prove convexity of the loss on each convex set, including all
degenerate switch and window boundary cases by continuity. This proves
the lemma. \(\square\)

## 5. A common critical point, with all its clipping checked

Define

\[
\begin{aligned}
b_*&=\frac{K+d}{2},\\
u_*&=(1-\kappa)C+\frac K2+\frac{\kappa d}{2},\\
v_*&=(1+\kappa)C+\frac K2-\frac{\kappa d}{2}.
\end{aligned}
\tag{AT.25}
\]

Its relevant switch positions are

\[
\begin{aligned}
x_{0,*}&=C+K/2,&x_{L,*}&=K/2-C,\\
p_*&=-\kappa(C-d/2),&e_*&=(K-d)/2,\\
a_*&=u_*-K.&&
\end{aligned}
\tag{AT.26}
\]

The only potentially delicate clipping condition is \(a_*\ge e_*\).
The exact identities in AT.3 and \(K^2=1-2K\) give

\[
a_*-e_*=(1-\kappa)(C-1/2)
+\frac{(K-d)^2}{2(1+d)}.
\tag{AT.27}
\]

This is positive for \(C\ge1/2\). For
\(C>49/100\), \(3/8\le\kappa\le3/5\), use
\(K>41/100\), \(d<7/25\), and \(1-\kappa\le5/8\). They give

\[
a_*-e_*>-\frac1{160}+\frac{169}{25600}
=\frac9{25600}>0.
\tag{AT.28}
\]

Here \(d\le(\sqrt{34}-5)/3<7/25\), because
\(\sqrt{34}<146/25\). Thus AT.13 proves the required clipping in
every remaining case.

We have \(b_*<C\), \(C<x_{0,*}<2C\), and

\[
-C<x_{L,*}<p_*<0<e_*<a_*<C.
\tag{AT.29}
\]

For example \(p_*-x_{L,*}=a_*>0\),
\(a_*-p_*=C-K/2>0\), and \(C>d/2\); these identities check the
displayed ordering. Also \(2C-v_*=a_*>0\),
\(v_*-C=\kappa(C-d/2)+K/2>0\), and
\(u_*-b_*=(1-\kappa)(C-d/2)>0\). Together with the value of
\(x_{0,*}\), these show that the point is in the interior of
\(D_C\). It lies in both \(D_1,D_2\), since
\(a_*<C\) and \(Y_{0,*}=(1+\kappa)K/2>0\).

The outer first-45-degree, second-45-degree, and terminal horizontal
exposure lengths are respectively

\[
C-K/2,\qquad a_*,\qquad K/2.
\]

By AT.29 the corresponding niche exposure lengths are exactly the same:
\(a_*-p_*\), \(p_*-x_{L,*}\), and \(x_{L,*}+C\).
Consequently all three first derivatives of \(F\) vanish at AT.25.
Lemma AT2 proves that this point maximizes \(F\) on each of
\(D_1,D_2\).

For the value, put \(z=C-K/2\), \(s=\kappa(C-d/2)\). Direct
integration over the displayed intervals gives

\[
\begin{aligned}
g_C(v_*)&=(z-s)^2/2,\\
Q_C(u_*,b_*)&=\kappa(3C^2/2-Cb_*)+(1-\kappa)z^2/2,\\
N(u_*,v_*,b_*)&=z^2-s^2/2+Ks/2+\kappa K^2/8.
\end{aligned}
\]

Their sum is \(2z^2+Ks\). Thus on \(D_1\cup D_2\),

\[
\boxed{F\le F_*:=2C-2(C-K/2)^2-\kappa K(C-d/2).}
\tag{AT.30}
\]

## 6. The complement is strictly below \(319/400\)

Suppose \((u,v,b)\in D_C\setminus(D_1\cup D_2)\). Then
\(u>C+K\) and \(Y_0<0\). Combining the latter with AT.6 gives

\[
v-u>(3\kappa-1)C+K-\kappa d>0.
\tag{AT.31}
\]

In particular \(u,v>C+K\), so both ends of the 45-degree tent are
strictly positive. Its apex belongs to \((-C,C)\), since
\(u,v\in(C+K,2C]\). Dropping the outgoing support and charge only
enlarges the relaxation. With \(h=(u+v)/2\), exact 45-degree
integration therefore gives

\[
F\le 2C-2C^2+2KC-(h-C)^2.
\tag{AT.32}
\]

Moreover, AT.31 implies

\[
h-C>\frac{3K}{2}-\frac{\kappa d}{2}>\frac9{20},
\tag{AT.33}
\]

using \(K>2/5\) and
\(\kappa d\le\sqrt{41}/5-1<3/10\). Finally
\(1+K=\sqrt2\), so

\[
2(1+K)C-2C^2\le1.
\]

Equations AT.32–AT.33 prove

\[
\boxed{F<1-(9/20)^2=319/400.}
\tag{AT.34}
\]

This completes all parameter and clipping cases in \(D_C\).

## 7. Exact optimization in width and angle

Completing the square in \(C\) in AT.30 gives the unrestricted bound

\[
F_*\le B(\kappa):=
\frac12+\frac K2+\frac K2\sqrt{1+\kappa^2}
-\frac{\kappa(1-K)}2+\frac{\kappa^2K^2}{8}.
\tag{AT.35}
\]

The maximizing width for this quadratic is
\(C=1/2+K(2-\kappa)/4\); no assumption that a cap realizes the
critical supports or this width is required for the upper bound.
On \([3/8,4/5]\),

\[
\begin{aligned}
B'(\kappa)
&=\frac{K\kappa}{2\sqrt{1+\kappa^2}}
-\frac{1-K}{2}+\frac{\kappa K^2}{4}\\
&\le\frac{2K}{5}-\frac{1-K}{2}+\frac{K^2}{5}
=\frac{5K-3}{10}<0.
\end{aligned}
\tag{AT.36}
\]

Hence the largest value occurs at \(\kappa=3/8\), where

\[
B(3/8)=\frac{169}{512}
+\frac{K(167+16\sqrt{73})}{256}.
\tag{AT.37}
\]

The exact rational bounds \(K<29/70\) and
\(\sqrt{73}<171/20\) now give

\[
B(3/8)<\frac{169}{512}
+\frac{29(167+16\cdot171/20)}{70\cdot256}
=\frac{5259}{6400}
=\frac{411}{500}-\frac9{32000}.
\tag{AT.38}
\]

All other cases were bounded strictly below \(41/50\), \(4/5\),
or \(319/400\), each smaller than \(5259/6400\). The earlier
outgoing-only theorem covers the initial interval
\([\pi/4,\arctan(5/4)]\) by a value below \(41/50\).
Fixed-angle attainment and the canonical reduction in Section 1 therefore
prove the universal first inequality of AT.1.

For the exact reference comparison, the same elementary argument as
G1C.6 in [the Gate 1 closure](gate1-sharp-full-turn-closure.md), now with
\(a=149/500\), gives

\[
4a^3+3a-1=-\frac{4551}{31250000}<0,\qquad
\frac M2>\frac{1+4a^2+a-a^3/3}{2}
=\frac{616648051}{750000000}>
\frac{411}{500}.
\tag{AT.39}
\]

This proves AT1. \(\square\)

## 8. Scope

The theorem is a universal bound over all widths and both canonical tilt
orientations for the specified terminal-angle interval. The use of an
attained canonical cap is a proof reduction for a hypothetical high
score, not an additional hypothesis on the input cap. The only finite
angles used are the actual 45-degree niche angle and the actual outgoing
angle; no finite-angle approximation of the remaining niche is asserted.

The remaining sufficient scalar inequality is still
\(\mathcal P_\alpha(U)\le M/2\) for
\(\arctan(8/3)<\alpha<\pi/2\). Gate 1 supplies the endpoint
\(\alpha=\pi/2\). Gate 2 remains open until all remaining partial
angles and their implications for the original common-hull problem are
proved. This note is a written argument, without Lean/Lake execution or
CI verification.
