# Gate 2: global reductions for the partial-turn spatial cap objective

**October 10, 2026. Written mathematical reductions.** These results
extend the domain reductions behind [Gate 1](gate1-sharp-full-turn-closure.md)
to a partial niche with its **actual whole-body outgoing strip**. They
prove attainment, a canonical middle facet, top localization from either
side, and a complete low-terminal-angle exclusion on the enlarged cap
domain. They do not prove the remaining sharp scalar value or Gate 2.

Labels PD are local. The geometric bridge and signed-fiber convention are
those of [Gate 0](original-motion-global-bridge-gate0-audit.md). No
horizontal-reflection invariance of the partial objective is assumed.

## 1. The exact objective and its sufficient implication

Let \(L=\pi/2\), and let \(U\subset\mathbb R\times[0,1]\) be a nonempty
compact downward convex cap. Write its horizontal projection as
\(I=[l,r]\), its roof as \(A_U\), and put

\[
W=r-l,\qquad J=[l+W/4,r-W/4].
\]

For \(0<t<L\), define

\[
\begin{aligned}
R_{U,t}(x)
&=\frac{h_U(\cos t,\sin t)-1-x\cos t}{\sin t},\\
S_{U,t}(x)
&=\frac{h_U(-\sin t,\cos t)-1+x\sin t}{\cos t}.
\end{aligned}
\tag{PD.1}
\]

For \(\pi/4\le\alpha<L\), the full positive constraint is

\[
q_{U,\alpha}(x)=
\max\left\{
0,\ \sup_{0<t<\alpha}\min\{R_{U,t}(x),S_{U,t}(x)\},
\ R_{U,\alpha}(x)
\right\}.
\tag{PD.2}
\]

The last term is the lower boundary of the actual outgoing straight
arm, a whole first wall. A terminal two-wall minimum would be an
insufficient replacement. At \(\alpha=L\), set \(q_{U,L}=n_U\), the
full positive niche. The limiting outgoing wall is
\(h_U(e_y)-1\le0\), so it is redundant.

The partial spatial score is

\[
\mathcal P_\alpha(U)=
\int_{I\setminus J}A_U(x)\,dx-\int_Jq_{U,\alpha}(x)\,dx.
\tag{PD.3}
\]

A zero-width cap has score zero.

For an arbitrary auxiliary convex hull \(K\) in the unit incoming strip,
let \(U,V\) be its upper and reflected-lower downward caps. Their upward
supports are exactly those used by the lower and upper canonical
motions. The signed full constraint at independent terminal magnitudes
\(\alpha,\gamma\in[\pi/4,L]\) is

\[
\ell(x)=1-\max\{1-A_V(x),q_{U,\alpha}(x)\}
          -\max\{1-A_U(x),q_{V,\gamma}(x)\}.
\]

On \(J\), discard the outer deficits; on \(I\setminus J\), discard the
niche and terminal deficits. Since both sets have length \(W/2\),

\[
\boxed{\int_I\ell(x)\,dx
\le\mathcal P_\alpha(U)+\mathcal P_\gamma(V).}
\tag{PD.4}
\]

For a genuine compact connected feasible body \(S\), its actual hull
has no empty projected survivor fiber, so
\(|S|\le\int_I\ell\). For auxiliary hulls the integral remains signed.
Consequently the universal bound

\[
\mathcal P_\alpha(U)\le M/2
\qquad\text{for every such cap and every }\alpha\in[\pi/4,L]
\tag{PD.5 — OPEN}
\]

would pass Gate 2. It is a sufficient scalar theorem. Gate 1 proves its
endpoint \(\alpha=L\), and the results below reduce the remaining domain.

## 2. Height extrusion and the middle chord

**Theorem PD1 (height-one reduction).** If \(U\) has height \(H\le1\)
and \(0\le\varepsilon\le1-H\), then

\[
U^\varepsilon=U+(\{0\}\times[0,\varepsilon])
\quad\Longrightarrow\quad
\mathcal P_\alpha(U^\varepsilon)\ge\mathcal P_\alpha(U).
\tag{PD.6}
\]

Indeed, both upper supports in PD.1 increase by their vertical normal
component times \(\varepsilon\). Hence each attached wall increases by
\(\varepsilon\), and the terminal wall does likewise. Taking the maximum
with zero gives

\[
0\le q_{U^\varepsilon,\alpha}-q_{U,\alpha}\le\varepsilon.
\]

The roof rises by exactly \(\varepsilon\) on the exterior wings.
Their measure equals that of \(J\), proving PD.6. The same argument
applies at \(\alpha=L\). The projection and the angle are unchanged.

**Theorem PD2 (affine middle).** For each cap and each fixed terminal
angle, there is a height-one cap with the same projection, an affine
roof on \(J\), and score at least the original score.

To prove this, let \(a(x)\) be the affine line joining the original roof
at the two endpoints of \(J\), and put

\[
U^c=U\cap\{(x,y):y\le a(x)\}.
\]

Concavity gives \(A_U\ge a\) on \(J\) and \(A_U\le a\) outside \(J\).
The chord is nonnegative on \(J\), and outside \(J\) it is at least the
nonnegative original roof. Thus \(U^c\) remains a downward convex cap
with the same projection. Its two charged exterior wings are unchanged.
Its smaller supports can only decrease both attached walls and the
terminal whole wall, so \(q_{U^c,\alpha}\le q_{U,\alpha}\). Therefore
its score does not decrease. Apply PD1 to restore exact height one;
the middle roof remains affine.

In particular, this procedure preserves global maximality when applied
to a global maximizer. No sign of the chord slope has been selected.

## 3. Width coercivity and joint attainment

Translate horizontally so that \(I=[-W/2,W/2]\). The two floor endpoints
give, at the actual angle \(t=\pi/4\),

\[
\left[\min\{R_{U,\pi/4}(x),S_{U,\pi/4}(x)\}\right]_+
\ge (W/2-\sqrt2-|x|)_+.
\]

For \(\alpha>\pi/4\) this angle is visited. For \(\alpha=\pi/4\),
the outgoing first wall dominates its two-wall minimum. Thus for every
allowed terminal angle,

\[
q_{U,\alpha}(x)\ge(W/2-\sqrt2-|x|)_+.
\tag{PD.7}
\]

The trivial exterior bound gives \(\mathcal P_\alpha\le W/2\). For
\(W\ge6\), the tent in PD.7 is positive throughout \(J\), so

\[
\mathcal P_\alpha(U)
\le \frac{1+\sqrt2}{2}W-\frac3{16}W^2
\le 3\sqrt2-\frac{15}{4}<\frac45.
\tag{PD.8}
\]

The quadratic decreases for \(W\ge6\), and the last strict comparison
follows, for example, from \(\sqrt2<3/2\). Caps with \(W\le8/5\)
also have score at most \(4/5\).

The reference cap at \(\alpha=L\) has score \(M/2>41/50\), as established
exactly in [G1C.6](gate1-sharp-full-turn-closure.md). Hence every global
maximizer of the joint cap-and-angle problem has

\[
\boxed{\frac85<W<6.}
\tag{PD.9}
\]

Here is the continuity needed for attainment, including the endpoint
\(\alpha=L\). On a fixed box
\([-B,B]\times[0,1]\), uniformly for \(x\in[-B,B]\),

\[
\begin{aligned}
\bigl[\min\{R_{U,t}(x),S_{U,t}(x)\}\bigr]_+
&\le 2B\min\{\tan t,\cot t\},\\
(R_{U,\alpha}(x))_+&\le2B\cot\alpha.
\end{aligned}
\tag{PD.10}
\]

For example,
\(h_U(-\sin t,\cos t)\le B\sin t+\cos t\), so
\(S_{U,t}(x)\le(B+x)\tan t+1-\sec t\le2B\tan t\).
The other bounds follow in the same way.

The first inequality makes the two omitted angular tails uniformly
small. On a closed interior angular interval, Hausdorff convergence of
caps gives uniform convergence of both support functions and wall
heights. The maximum of a continuous function over
\([\eta,\min(\alpha,L-\eta)]\) varies continuously with its upper
endpoint. The second inequality makes the positive terminal wall tend
uniformly to zero as \(\alpha\uparrow L\). These facts prove uniform
convergence of \(q_{U_n,\alpha_n}\) on the fixed horizontal box whenever
\(U_n\to U\) in Hausdorff distance and \(\alpha_n\to\alpha\).

The endpoints of \(I\) and \(J\) also converge, being expressions in
horizontal supports. The middle niche integral is therefore continuous.
The exterior roof integral is
\[
|U|-|U\cap(J\times\mathbb R)|.
\]
Area of bounded planar convex sets is Hausdorff-continuous; moving the
two vertical cuts does not change this conclusion. Equivalently, use
almost-everywhere convergence of convex-set indicators and the cuts.
If the limiting cap is degenerate, its area and the areas of the
approximating caps tend to zero. Thus the full score is continuous.

**Theorem PD3 (attainment).** The joint supremum of
\(\mathcal P_\alpha(U)\) over all downward caps in the unit-height strip
and \(\alpha\in[\pi/4,L]\) is attained. One may choose a height-one
maximizer satisfying PD.9 whose entire middle roof is affine.

Indeed, after horizontal centering and PD1, it suffices to maximize on
the compact class of height-one downward convex caps in
\([-3,3]\times[0,1]\), with centered projection, and the compact angle
interval. Blaschke compactness and the preceding continuity give a
maximizer; PD.8–PD.9 and PD2 give the stated refinements. Degenerate caps
are harmless in the compactification.

## 4. The top meets the middle window from either side

**Theorem PD4 (top insertion).** At every height-one global maximizer,
the horizontal top face intersects \(J\).

Suppose first that the left endpoint \(a\) of the top face is strictly
to the right of \(j_+=r-W/4\). Adjoin the point \(p=(j_+,1)\) and take
the convex downward hull. Its projection and height are unchanged.
For every upward normal \(n=(n_x,n_y)\) with \(n_x\ge0\), the old point
\((a,1)\) dominates \(p\), so that support is unchanged. If a support
with \(n_x<0\) changes, the new support is \(p\cdot n\), and for
\(x\in J\), \(y\ge0\),

\[
p\cdot n-1-(x,y)\cdot n
=(j_+-x)n_x+(1-y)n_y-1\le0.
\tag{PD.11}
\]

Thus every newly changed inner second wall is nonpositive throughout
the positive middle half-strip. Both its old and new quadrant make no
positive contribution there. All first-wall supports, including the
terminal one, are unchanged. Hence \(q_{U,\alpha}|_J\) is unchanged.
The new top plateau on \([j_+,a]\) strictly increases the charged
exterior area, a contradiction.

If the right endpoint \(b\) of the top face is strictly to the left of
\(j_-=l+W/4\), instead insert \(p=(j_-,1)\). All upward supports with
\(n_x\le0\) are unchanged. Every changed support with \(n_x>0\) satisfies

\[
p\cdot n-1-(x,y)\cdot n
=(j_--x)n_x+(1-y)n_y-1\le0
\qquad(x\in J,\ y\ge0).
\tag{PD.12}
\]

This covers the changed first walls and, specifically, the outgoing
whole first wall. They remain nonpositive on \(J\); the middle
constraint is again unchanged. The newly filled top plateau on
\([b,j_-]\) strictly increases exterior reward. This is the second
contradiction.

For an affine-middle maximizer, a positive middle slope therefore has
height one at \(j_+\), and a negative slope has height one at \(j_-\).
A horizontal middle roof equals one throughout \(J\). The two tilted
cases are separate alternatives; no horizontal reflection of the
partial objective has been invoked.

## 5. Saturation by precisely the used supports

For a cap \(U\) at fixed terminal angle, define

\[
U^{\rm sat}
=(I\times[0,1])\cap
\bigcap_{0\le t\le\alpha}
\left\{
z:\ z\cdot(\cos t,\sin t)\le h_U(\cos t,\sin t),\
z\cdot(-\sin t,\cos t)\le h_U(-\sin t,\cos t)
\right\}.
\tag{PD.13}
\]

**Theorem PD5 (used-support saturation).** This is a compact downward
convex cap containing \(U\), with the same projection, height, and all
used upper supports. In particular,

\[
q_{U^{\rm sat},\alpha}=q_{U,\alpha},
\qquad
\mathcal P_\alpha(U^{\rm sat})\ge\mathcal P_\alpha(U).
\tag{PD.14}
\]

Every normal used in PD.13 has nonnegative vertical component, so
downward closure is preserved. The floor segment over \(I\) remains
inside. Inclusion gives one support inequality, and the defining
halfplanes give the reverse inequality in each used direction. The top
normal occurs at \(t=0\) in the second family, fixing the height.
Thus every wall in PD.2 is unchanged, proving PD.14.

At a global maximizer, saturation cannot increase the exterior roof
anywhere on an open charged interval: continuity would produce a
strict area increase. Consequently it preserves both exterior wings
and, by their one-sided limits, their endpoints. If the original middle
roof is the chord \(a(x)\), it follows that

\[
\boxed{U=U^{\rm sat}\cap\{(x,y):y\le a(x)\}.}
\tag{PD.15}
\]

This is an exact description of a selected affine-middle maximizer.
In the open unused normal arcs
\[
(\alpha,L)\quad\text{and}\quad(L+\alpha,\pi),
\]
the only possible nonzero upper curvature measure is the atom of the
uncharged central facet, if its normal belongs to one of these arcs.
There is no charged wing curvature there. To see this without assuming
regularity, first consider \(U^{\rm sat}\). Compactness of its family of
defining normals ensures that every boundary point has an active
defining constraint. At boundary-arclength almost every point the outer
normal is unique, and hence equals the normal of any active constraint.
Every such normal is a used normal or an axis normal. Its upper
curvature measure therefore vanishes on the unused open arcs.

The original maximizing cap has the same charged wings as
\(U^{\rm sat}\), so their wing curvature measures agree. Any remaining
curvature of the original cap within these arcs comes from its affine
middle roof and is the central-facet atom. Equivalently, on each
component away from that possible central normal, the supporting point
is constant and the support satisfies \(h''+h=0\). A vertex can have
an entire unused interval in its normal cone; it contributes no
boundary length or curvature measure on that interval.

This statement does not eliminate possible terminal facets at the
endpoints of the used normal intervals, and does not identify a weak
finite niche-source limit with ordinary continuum arclength.

## 6. An exact low-terminal-angle exclusion

This bound holds for every cap, with no maximizing or canonical-form
hypothesis. Center \(I=[-2C,2C]\), let \(\alpha<L\), and put
\[
a=\cot\alpha>0,\qquad
H=\frac{h_U(\cos\alpha,\sin\alpha)}{\sin\alpha}.
\]

The upper support gives \(A_U(x)\le H-a x\), and the outgoing wall gives
\(q_{U,\alpha}(x)\ge H-\csc\alpha-a x\). Bound the left exterior reward
by \(C\), bound the right exterior reward by this support line, and
charge only the left half of \(J\). The uncharged niche remainder is
nonnegative. Therefore

\[
\begin{aligned}
\mathcal P_\alpha(U)
&\le C+\int_C^{2C}(H-a x)\,dx
-\int_{-C}^0(H-\csc\alpha-a x)\,dx\\
&=(1+\csc\alpha)C-2\cot\alpha\,C^2\\
&\le\boxed{\frac{(1+\csc\alpha)^2}{8\cot\alpha}}.
\end{aligned}
\tag{PD.16}
\]

The cancellation is valid even when the affine niche lower bound is
negative on part of its integration interval.

For \(a\in[4/5,1]\), the final expression is
\((1+\sqrt{1+a^2})^2/(8a)\). Its derivative has the sign of
\[
(\sqrt{1+a^2}-2)(\sqrt{1+a^2}+1)<0.
\]
Since \(\sqrt{41}<641/100\), this proves

\[
\boxed{
\pi/4\le\alpha\le\arctan(5/4)
\ \Longrightarrow\
\mathcal P_\alpha(U)\le\frac{33+5\sqrt{41}}{80}
<\frac{1301}{1600}<\frac{41}{50}<\frac M2.}
\tag{PD.17}
\]

At \(\alpha=\pi/4\), PD.16 gives \((3+2\sqrt2)/8\).

## 7. The exact remaining scalar domain

If PD.5 is false, PD3 supplies a selected canonical global maximizer
with score greater than \(M/2\), for which

\[
\frac85<W<6,\qquad
\arctan(5/4)<\alpha<\pi/2,
\qquad
\operatorname{height}(U)=1,\qquad A_U|_J\text{ is affine}.
\tag{PD.18}
\]

The strict upper angular endpoint follows from the proved Gate 1
theorem; the strict lower endpoint follows from PD.17. Its top meets
\(J\), and PD.15 describes its charged wings using precisely the visited
supports. The middle roof may be horizontal or tilted in either
direction. Neither a first-unit curvature bound, a positive-pressure
law, a full-turn exposure identity, nor a derivative formula ignoring
terminal ties has been imported into this domain.

Bounding this remaining scalar maximum would suffice for Gate 2 via
PD.4. The reductions themselves do not supply that bound.
