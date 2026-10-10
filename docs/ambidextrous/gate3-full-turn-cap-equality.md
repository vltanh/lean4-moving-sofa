# Gate 3: equality in the universal full-turn cap theorem

**October 10, 2026. Written mathematical proof.** This note classifies
every equality cap in [G1C1](gate1-sharp-full-turn-closure.md), including
the original caps before middle-chord clipping or height extrusion. The
classification is an exact identity of compact sets. It does not assume
that the input cap is canonical, has unit height, is symmetric, or has
regular curvature.

The proof uses the completed Gate 1 value theorem and its maximizing-cap
exclusions, followed by the equality statement of
[AF3](adaptive-functional-global-calibration.md). The ordinary one-turn
area theorem remains a dependency of those Gate 1 exclusions. No equality
case of that external theorem is needed: every branch in which it is
used ends in a strict contradiction. Proper terminal angles and recovery
of an original physical body are separate equality questions.

## 1. Domain and exact reference normalization

Put

\[
L=\frac\pi2,\qquad
4Y^3+3Y-1=0,\quad Y>0,\qquad
\beta=\arctan Y,\qquad s=\sin\beta,
\]
\[
M=1+4Y^2+\arctan Y,\qquad
a_*=\frac1{3s},\qquad C_*=\frac{a_*}{2},\qquad
k=1-a_*.
\tag{CE.1}
\]

Let \(h_*\) denote the displayed reference profile in
[Note 14, equations 14.2–14.3](14-sharp-quadratic-calibration.md).
That displayed profile has horizontal endpoint support values
\(h_*(0)=1\) and \(h_*(\pi)=2a_*-1\), so it is not centered.
Define

\[
\bar h_*(\theta)=h_*(\theta)-k\cos\theta.
\tag{CE.2}
\]

Both horizontal endpoint values of \(\bar h_*\) are \(a_*\).
Let \(U_*\) be the centered downward reference cap: its upper support
function is \(\bar h_*|_{[0,\pi]}\), and its lower boundary is its
full horizontal baseline. Its existence as a genuine compact convex
cap, and its reference score, are proved in
[AR3](one-turn-arm-reduction.md) and
[SD1](gate1-spatial-dual-height-width-compactness.md).

For an arbitrary nonempty compact downward convex cap
\(U\subset\mathbb R\times[0,1]\), let \(I=[l,r]\) be its actual
horizontal projection, \(W=r-l\), \(A_U\) its roof, and
\(J=[l+W/4,r-W/4]\). Its full positive niche and spatial score are

\[
n_U(x)=\left[\sup_{0<t<L}\min\left\{
\frac{h_U(\cos t,\sin t)-1-x\cos t}{\sin t},
\frac{h_U(-\sin t,\cos t)-1+x\sin t}{\cos t}
\right\}\right]_+,
\]
\[
P(U)=\int_{I\setminus J}A_U(x)\,dx-\int_J n_U(x)\,dx.
\tag{CE.3}
\]

Here “downward” means that every vertical fiber is an interval beginning
at height zero. In particular the cap contains \(I\times\{0\}\).
The zero-width case has score zero and cannot attain \(M/2\).

## 2. Every prescribed canonical equality cap enters the Gate 1 proof

A canonical cap has height one and a roof affine on all of its middle
interval \(J\), as in [MID.11](gate1-global-middle-chord-canonicalization.md).
The following quantifier is essential for equality recovery.

**Prescribed-cap observation.** Every canonical global maximizer can be
used as the target of the finite selections and all subsequent necessary
conditions in Gate 1.

Indeed, fix such a cap \(V\), translate it strictly inside the artificial
horizontal box, and use the penalty
\(\eta_nD_n(\,·\,,V)^2\) from
[RG, Section 2](gate1-spatial-maximizer-wing-curvature-regularity.md).
The comparison with the grid circumscription of this same \(V\) gives
\(D_n(V_n,V)^2\le e_n/\eta_n\to0\). Thus the selected polygons converge
to this prescribed cap. The vanishing-middle-curvature argument RG1
uses only the affinity of this cap's middle roof. The proofs of
RG2–RG3, [EP1–EP2](gate1-global-endpoint-complementarity.md), and the later
spatial necessary conditions therefore apply to \(V\) itself.
Although RG2 was stated as an existence theorem, its proof does not
select one favored canonical maximizer at the expense of others.

Now suppose \(V\) is canonical and \(P(V)=M/2\). G1C1 makes \(V\)
a global maximizer on the entire cap domain. The complete tilted
coverage in [G1C, Sections 3–5](gate1-sharp-full-turn-closure.md) excludes
every nonzero middle slope. These arguments use the maximizing lower
bound \(P(V)\ge M/2>41/50\), not the stronger and unavailable premise
\(P(V)>M/2\). Their strict contradictions consequently apply at equality.

For a horizontal canonical maximizer, the strict short and wide
exclusions in [HW](gate1-horizontal-maximizer-sharp-value.md) leave

\[
\frac12<C=\frac W4<\frac{8571}{12500}<C_H,
\qquad C_H=\frac1{35}\sqrt{523+2\sqrt{701}}.
\tag{CE.4}
\]

The entire surviving range is inside CH6. The actual spatial laws
[CH2 and CH4–CH6](gate1-spatial-maximizer-curvature-and-horizontal-value.md)
therefore give:

- the top face is exactly \(J\times\{1\}\);
- the two open-quarter supports have regular curvature densities at
  most one;
- the full positive niche is confined to \(J\);
- the sharp comparison CH.26 holds for these actual supports.

All these conclusions concern the chosen cap \(V\), and no
stationarity law for the different weighted functional is imported.

## 3. The functional equality identifies the canonical cap

**Theorem CE1 (canonical equality).** A canonical cap \(V\) has
\(P(V)=M/2\) if and only if it is a horizontal translate of \(U_*\).

**Proof.** Translate the projection to \([-a,a]\), where
\(a=W/2=2C>1\), and write

\[
f(t)=h_V(\cos t,\sin t),\qquad
g(t)=h_V(-\sin t,\cos t),\qquad 0\le t\le L.
\]

The exact endpoint data are
\(f(0)=g(L)=a\) and \(f(L)=g(0)=1\). Thus
\((f,g)\in X_a\) in the notation of AF. By CE.4 and CH.26,

\[
\frac M2=P(V)\le F(f,g)-a\le\frac M2.
\tag{CE.5}
\]

To apply AF3's equality statement directly to this pair, define a real
periodic profile \(\widehat h\) by

\[
\widehat h(t)=f(t),\qquad
\widehat h(t+L)=g(t),
\]
\[
\widehat h(-t)=f(t)-\sin t,\qquad
\widehat h(-t-L)=g(t)-\cos t,
\qquad 0\le t\le L.
\tag{CE.6}
\]

The endpoint values make these formulas agree at \(0,\pm L,\pm\pi\),
so \(\widehat h\) is a real \(2\pi\)-periodic \(H^1\) function.
It has \(\widehat h(L)=1\), \(\widehat h(3L)=0\), and horizontal
width \(2a>1\). The reflected half in AF's definition equals the
original pair. Consequently CE.5 gives

\[
\widetilde{\mathcal Q}(\widehat h)=2F(f,g)-2a=M.
\tag{CE.7}
\]

No assertion that this auxiliary lower-half extension is a convex
support function is needed: AF3 is proved on the full real \(H^1\)
profile domain. Its equality statement gives
\(\widehat h=h_*+b\cos\theta\) for a real \(b\).
The continuous representatives of these \(H^1\) functions agree
pointwise, so this also identifies the actual upper supports at every
normal, not merely almost everywhere.
The two horizontal endpoint values are both \(a\), while those of
\(h_*\) are \(1\) and \(2a_*-1\). Therefore
\(a=a_*\) and \(b=a_*-1=-k\). In particular the actual upper support
function of the centered cap \(V\) is \(\bar h_*\).

A downward compact convex cap is the intersection of \(\{y\ge0\}\)
with its upper supporting halfplanes, including the two horizontal
axis normals. To see why the remaining lower normals add no data,
their support is attained on the full baseline: lowering a point to
height zero increases its scalar product with such a normal. Equality
of all the upper supports therefore gives the exact identity
\(V=U_*\). Undo the initial horizontal translation.

Conversely, the reference has score \(M/2\), and horizontal
translation preserves CE.3. \(\square\)

In particular every canonical equality cap has

\[
A_V=1\text{ on }J,\qquad
n_V(j_-)=n_V(j_+)=0.
\tag{CE.8}
\]

The niche endpoint statement also follows directly before AF equality:
CH Section 7 places every positive two-wall point strictly between the
two endpoints of \(J\). The niche is continuous, by the endpoint-angle
truncation argument in SD3.

## 4. Exact height-extrusion deficit

The weak monotonicity used for Gate 1 has a stronger identity suitable
for recovering equality.

**Lemma CE2 (extrusion deficit).** Let \(V\) be a downward cap of
positive width, let \(\varepsilon\ge0\), and suppose
\(W=V+[0,\varepsilon]e_y\) still has height at most one. The two caps
have the same projection \(I\) and middle interval \(J\), and

\[
\boxed{\quad n_V=(n_W-\varepsilon)_+,\qquad
P(W)-P(V)=\int_J(\varepsilon-n_W(x))_+\,dx.\quad}
\tag{CE.9}
\]

If \(n_W\) is continuous and vanishes at either endpoint of \(J\),
then \(\varepsilon>0\) makes this score difference strictly positive.

**Proof.** Minkowski addition of the vertical segment raises the roof
by \(\varepsilon\) and adds \(\varepsilon n_y\) to each upward
support. Both raw inner-wall heights consequently rise by precisely
\(\varepsilon\), for every parameter and abscissa. If \(r_V\) is
their signed angular supremum, then
\(n_W=(r_V+\varepsilon)_+\) and
\(n_V=(r_V)_+=((r_V+\varepsilon)_+-\varepsilon)_+\).
This proves the first identity, including where the signed supremum is
negative.

The charged exterior area increases by \(\varepsilon|I\setminus J|\).
Since \(|I\setminus J|=|J|\),

\[
\begin{aligned}
P(W)-P(V)
&=\varepsilon|J|-\int_J\bigl[n_W-(n_W-\varepsilon)_+\bigr]\,dx\\
&=\int_J(\varepsilon-n_W)_+\,dx.
\end{aligned}
\]

For the strict assertion, continuity next to an endpoint where
\(n_W=0\) gives a positive-length subinterval on which
\(n_W<\varepsilon/2\). The displayed integral is then positive.
\(\square\)

## 5. Recovery of every original equality cap

**Theorem CE3 (universal full-turn equality).** For every nonempty
compact downward convex cap \(U\subset\mathbb R\times[0,1]\),

\[
\boxed{\qquad P(U)=\frac M2
\quad\Longleftrightarrow\quad
U=U_*+(b,0)\text{ for some }b\in\mathbb R.\qquad}
\tag{CE.10}
\]

**Proof.** Assume equality. The cap has positive width and positive
area. Perform the exact [MID](gate1-global-middle-chord-canonicalization.md)
construction on this original cap. If \(\ell\) is the chord of its
roof between the endpoints of \(J\), put

\[
V=U\cap\{y\le\ell(x)\},\qquad
\varepsilon=1-\max_{(x,y)\in V}y,\qquad
W=V+[0,\varepsilon]e_y.
\tag{CE.11}
\]

The projection and middle interval are unchanged. The roof of \(V\)
agrees pointwise with that of \(U\) outside \(J\); on \(J\) it is
the chord \(\ell\). All outer supports decrease under the cut, so
the complete niche weakly decreases. MID.10 and the already proved
universal bound therefore give

\[
\frac M2=P(U)\le P(V)\le P(W)\le\frac M2.
\tag{CE.12}
\]

Every term is equal. The cap \(W\) is canonical, so CE1 identifies it
as a horizontal translate of \(U_*\). In particular CE.8 holds.
The extrusion deficit CE.9 and \(P(W)=P(V)\) force
\(\varepsilon=0\); otherwise the deficit is strictly positive on an
interval next to either middle endpoint. Thus \(W=V\), and its roof
is one throughout \(J\).

Finally \(V\subseteq U\subset\mathbb R\times[0,1]\) forces the
original roof to be one on \(J\) as well. Outside \(J\), the chord
cut already preserved that roof pointwise. Hence \(U=V=W\) as compact
sets. This proves the forward implication. The converse was included
in CE1. \(\square\)

The proof does not claim that middle-chord clipping is always strictly
improving. It can preserve the score on other inputs. What removes that
possible non-rigidity at the sharp value is the recovered unit-height
plateau, together with the original height ceiling.

## 6. Reference data available to later equality arguments

**Corollary CE4.** In the centered normalization, every full-turn
equality cap has

\[
I=[-a_*,a_*],\qquad J=[-C_*,C_*],\qquad
\text{top}=J\times\{1\},\qquad
A(-a_*)=A(a_*)=\frac12.
\tag{CE.13}
\]

Its two regular source curvatures have the exact end intervals

\[
f''+f=0,\quad g''+g=\frac12
\quad(0<t<\beta),
\]
\[
f''+f=\frac12,\quad g''+g=0
\quad(L-\beta<t<L).
\tag{CE.14}
\]

These follow from Note 14's explicit first and last pieces; the
centering term has zero curvature. The endpoint heights follow from
\(f'(0)=1/2\) and \(g'(L)=-1/2\). Both the top location and the
reflection symmetry are conclusions of equality, not assumptions on
the input cap.

The argument is for the cap functional. Passing from an equality body
to its two caps, excluding proper terminal angles, and using any
vanishing ordinary-area defects still require their own exact
arguments. In particular an almost-everywhere equality of arbitrary
compact bodies is not upgraded to set equality by CE3 alone.
