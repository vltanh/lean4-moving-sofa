# Global positive endpoint pressures and the stationary wing identity

**October 10, 2026. Written proof, independently audited within this research session. Gate 1 remains open.** This note removes the nonpositive-pressure branch left by [EP1–EP3](gate1-global-endpoint-complementarity.md). It proves a strict ordinary-area bound for every canonical cap whose lower middle endpoint has height at most one half, then derives exact positive endpoint pressures and a stationary exterior-wing length identity at every canonical global maximizer. The proof uses the actual full niche; no prescribed contact chart, curvature upper bound, or physical two-handed feasibility is assumed.

The selected finite exposure measures remain distinct from ordinary arclength of the limiting positive niche. All limiting statements below use weak source measures, uniform support convergence, or lower semicontinuity of total variation.

## Theorem LH1: a strict global low-height exclusion

Let U be any downward convex height-one cap whose roof A is affine on the middle half of its projection. Suppose its higher middle endpoint has height one and its lower middle endpoint has height at most one half. Then
\[
\boxed{\mathcal P(U)<\frac{31233}{39200}<\frac45.}
\tag{LH.1}
\]
The strict first inequality may be weakened to a non-strict one if preferred. In particular such a cap cannot be a global maximizer, since the reference value is \(M/2>4/5\).

Combined with EP3, this excludes **every nonpositive endpoint pressure** at a canonical global maximizer. Both end faces are then strictly positive, and both limiting finite-exposure measures equal the charged outer-wing curvature measures.

## 1. Normalize and bound both charged roofs

Reflect horizontally if needed and center the projection:
\[
I=[-2C,2C],\quad J=[-C,C],\quad C>0,\quad
A(C)=1,\quad A(-C)=a\le1/2.
\]
The central slope is \(s=(1-a)/(2C)\). For the left wing, write \(x=-2C+z\), \(0\le z\le C\). Concavity below the extension of the middle chord gives
\[
A(-2C+z)\le \frac{3a-1}{2}+\frac{1-a}{2C}z
\le \frac14+\frac{z}{4C}.
\tag{LH.2}
\]
The last affine expression is increasing in a at every z in [0,C], so replacing a by 1/2 is valid. On the right wing \(A\le1\). Thus the entire charged exterior reward R obeys
\[
R:=\int_{I\setminus J}A\le\frac{3C}{8}+C=\frac{11C}{8}.
\tag{LH.3}
\]
For \(C\le1/2\), this already gives \(P\le11/16<4/5\). Henceforth take \(C\ge1/2\).

Let
\[
m_R=\max_U(x+y)=2C+u,\qquad
m_L=\max_U(-x+y)=2C+v.
\]
The two baseline endpoints and the high point (C,1) imply
\[
\max(0,1-C)\le u\le1.
\tag{LH.4}
\]
Also
\[
0\le v\le1/4.
\tag{LH.5}
\]
For the upper bound in LH.5: on the left wing, LH.2 gives
\[
-x+A(x)\le2C+1/4-\left(1-\frac1{4C}\right)z\le2C+1/4.
\]
On J, the roof is at most its a=1/2 affine majorant \(3/4+x/(4C)\); since \(C\ge1/2\), \(-x+A(x)\) is bounded by \(C+1/2\le2C+1/4\). On the right wing it is at most \(1-C\le2C+1/4\). The left baseline endpoint gives the lower bound.

The actual support constraints improve the reward bound. On the right wing, setting z=2C-x,
\[
A(x)\le\min\{1,u+z\},\quad0\le z\le C.
\]
Since \(1-u\le C\), integration gives
\[
R_R\le C-\frac{(1-u)^2}{2}.
\tag{LH.6}
\]
On the left wing,
\[
A(-2C+z)\le
\min\left\{v+z,\frac14+\frac{z}{4C}\right\}.
\]
Put \(k=1-1/(4C)\), so \(1/2\le k<1\). The two lines cross at \(z_0=(1/4-v)/k\le C\): indeed \(1/4-v\le1/4\le C-1/4=kC\). Integrating the missing triangle gives
\[
R_L\le\frac{3C}{8}-\frac{(1/4-v)^2}{2k}
\le\frac{3C}{8}-\frac{(1/4-v)^2}{2}.
\tag{LH.7}
\]
Consequently
\[
\boxed{R\le\frac{11C}{8}
-\frac{(1-u)^2}{2}
-\frac{(1/4-v)^2}{2}.}
\tag{LH.8}
\]

## 2. Use the genuine full two-ray niche at one exact angle

At t=pi/4 the two actual ray roofs are
\[
m_R-\sqrt2-x,\qquad m_L-\sqrt2+x.
\]
Thus the full positive niche satisfies
\[
n_U(x)\ge (h-|x-d|)_+,\qquad
h=2C+\frac{u+v}{2}-\sqrt2,\quad d=\frac{u-v}{2}.
\tag{LH.9}
\]
Because \(u\le1\), \(v\le1/4\), and \(C\ge1/2\), the tent apex d lies in J.

For now suppose \(1/2\le C\le23/20\). One tent tail cannot reach the endpoint because
\[
h-C-d=C+v-\sqrt2\le7/5-\sqrt2<0.
\]
Exact integration of the positive tent over J gives
\[
\int_J n_U\ge h_+^2-\frac12 z_+^2,\qquad z=C+u-\sqrt2.
\tag{LH.10}
\]
If h is nonpositive then z is also nonpositive, so the formula still holds. Hence P is at most
\[
F(C,u,v)=\frac{11C}{8}
-\frac{(1-u)^2}{2}
-\frac{(1/4-v)^2}{2}
-h_+^2+\frac12z_+^2.
\tag{LH.11}
\]

## 3. Unclipped tent case

Suppose z<=0. Write \(x_0=1-u\), \(y_0=1/4-v\), and
\[
H=2C+5/8-\sqrt2>0,\qquad h=H-(x_0+y_0)/2.
\]
Since \(x_0,y_0\ge0\), Cauchy's elementary inequality gives, with \(w=(x_0+y_0)/2\),
\[
\frac{x_0^2+y_0^2}{2}+(H-w)_+^2
\ge w^2+(H-w)_+^2\ge H^2/2.
\]
The last inequality follows by completing the square for w<=H, and by \(w^2\ge H^2\) for w>=H. Therefore
\[
F\le \frac{11C}{8}-\frac12(2C+5/8-\sqrt2)^2.
\]
Complete the square in C, or put \(H=2C+5/8-\sqrt2\), to obtain the global bound
\[
\boxed{F\le\frac{11\sqrt2}{16}-\frac{99}{512}
<\frac{2827}{3584}<\frac45,}
\tag{LH.12}
\]
using \(\sqrt2<10/7\). No optimization over a finite sample is involved.

## 4. Clipped tent case

For fixed C,v, the z>0 range begins at \(u_0=\sqrt2-C\). This threshold is larger than the feasible lower bound \(\max(0,1-C)\), and for the current C range lies below 1 whenever the clipped range is nonempty. In this range h>0 and
\[
\frac{\partial F}{\partial u}
=1-u-h+z=1-C-\frac{u+v}{2},
\qquad
\frac{\partial^2 F}{\partial u^2}=-1/2.
\tag{LH.13}
\]
Hence the maximum on \([u_0,1]\) is either the boundary u_0, already covered by LH.12, or the stationary point
\[
u_*=2-2C-v.
\]
Because C>=1/2 and v>=0, \(u_*\le1\); the upper endpoint cannot furnish another case. For the stationary point to belong to the clipped region, it is necessary that
\[
C+v\le2-\sqrt2=:D.
\tag{LH.14}
\]
Thus \(C\le D\) and \(v\le D-1/2=3/2-\sqrt2\). In particular
\[
1/4-v\ge\sqrt2-5/4>0.
\]
The tent integral and right-roof deficit are nonnegative, so at that stationary point they may be discarded from the upper bound:
\[
F(C,u_*,v)\le
\frac{11D}{8}-\frac12(\sqrt2-5/4)^2
=\frac{31}{32}-\frac{\sqrt2}{8}.
\]
Consequently
\[
\boxed{F(C,u_*,v)<\frac{127}{160}<\frac45,}
\tag{LH.15}
\]
using \(\sqrt2>7/5\). This covers every clipped case, including a stationary point coinciding with the boundary.

## 5. All larger widths

For \(C\ge23/20\), use the baseline endpoints alone in the same genuine pi/4 niche:
\[
n_U(x)\ge(2C-\sqrt2-|x|)_+.
\]
Together with LH.3, this gives
\[
P\le
\begin{cases}
\displaystyle \frac{11C}{8}-(2C-\sqrt2)^2,
&23/20\le C\le\sqrt2,\\[1ex]
\displaystyle \left(\frac{11}{8}+2\sqrt2\right)C-3C^2,
&C\ge\sqrt2.
\end{cases}
\tag{LH.16}
\]
Both expressions are strictly decreasing on their respective stated ranges, and they agree at C=sqrt2. For the first, the derivative is \(11/8-4(2C-\sqrt2)<0\) already at C=23/20; for the second it is \(11/8+2\sqrt2-6C<0\) at C=sqrt2 and thereafter. Therefore the maximal bound in this entire large-width range is at 23/20. Using \(\sqrt2<99/70\),
\[
P\le\frac{253}{160}-(23/10-\sqrt2)^2
<\frac{253}{160}-(31/35)^2
=\boxed{\frac{31233}{39200}<\frac45.}
\tag{LH.17}
\]
The gap is exact: \(4/5-31233/39200=127/39200\).

The small-width bound 11/16 and middle-width bounds in LH.12 and LH.15 are all below 31233/39200 as well. This proves LH.1.

## 6. Consequence for the full global maximizing domain

**Theorem LH2 (strictly positive pressures).** Every canonical global maximizer of the spatial score has both endpoint pressures strictly positive and both limiting finite-exposure measures equal to its charged wing curvature measures.

[MID2](gate1-global-middle-chord-canonicalization.md) and [TF4](gate1-spatial-tilted-facet-pinning.md) select a canonical maximizer whose middle roof is affine and whose higher endpoint is at height one. If its lower endpoint were at most one half, LH.1 would contradict the reference lower value \(M/2>4/5\). Thus every such tilted maximizer has
\[
A(j_{\rm low})>1/2.
\]
[EP3](gate1-global-endpoint-complementarity.md) says a nonpositive lower-side pressure forces
\(q_{\rm low}=A(j_{\rm low})+n(j_{\rm low})\le1/2\), which is impossible. The higher-side pressure is already positive by EP3. Hence both pressures are strictly positive, both end heights are positive by EP1, and EP2 gives both full limiting finite-exposure measure equalities.

In the horizontal case both pressures are already strictly positive by EP3. Thus, writing \(\omega_R,\omega_L\) for the actual charged curved-wing normal measures and \(\nu_R,\nu_L\) for the weak limits of selected finite middle-niche source exposures, the global conclusion is
\[
\boxed{C_R=e_R>0,\qquad C_L=e_L>0,\qquad
\nu_R=\omega_R,\quad\nu_L=\omega_L.}
\tag{LH.18}
\]
The central affine facet and the horizontal top face are omitted from these open-quarter wing measures. A tilted maximizer may still have a positive horizontal top segment extending from its high middle endpoint into that exterior wing. Top insertion does not imply a point top.

## 7. Exact clipped Green identity at a global maximizer

Let \(U\) be a canonical global maximizer and return to the general
coordinates \(I=[l,r]\), \(J=[j_-,j_+]\). Write
\[
O=\int_{I\setminus J}A,\qquad N_J=\int_Jn,\qquad
A_\pm=A(j_\pm),\quad n_\pm=n(j_\pm),\quad q_\pm=A_\pm+n_\pm.
\]
Put \(\omega=\omega_R+\omega_L\), \(\nu=\nu_R+\nu_L\), and let
\(T_{\rm wing}\) be the horizontal length of the height-one top face
outside J. The actual upper-boundary arclength above the charged wings,
excluding the vertical end faces, is
\[
L_{\rm wing}=\omega((0,\pi))+T_{\rm wing}.
\tag{LH.19}
\]

For an upper graph with outward normal \(\theta\), the support line
identity gives
\(h\,ds=(A-xA')\,dx\). Integrating separately on the two wings,
and separating the horizontal top segments, yields
\[
2O=\int h\,d\omega+T_{\rm wing}
+r e_R-l e_L+j_-A_--j_+A_+.
\tag{LH.20}
\]
This is integration by parts on monotone convex-boundary arcs. The
vertical end faces are represented by the displayed endpoint terms,
and are not counted again in \(\omega\).

For a selected finite polygon, every positive exposed niche segment
is supported by a line at signed distance \(h_n(\theta)-1\).
The same graph identity on that segment is
\[
(h_n(\theta)-1)\,ds=(n_n-xn_n')\,dx.
\]
Summing all positive segments in the moving \(J_n\), with the floor
segments contributing zero, gives the exact finite identity
\[
2\int_{J_n}n_n
=\int(h_n-1)\,d\nu_n-j_-^{(n)}n_n(j_-^{(n)})
+j_+^{(n)}n_n(j_+^{(n)}).
\]
[RG](gate1-spatial-maximizer-wing-curvature-regularity.md) and
[EP](gate1-global-endpoint-complementarity.md) give uniform support
and niche convergence, convergence of J endpoints, and weak convergence
of the bounded source exposure measures. Their endpoint estimates
exclude lost atoms at the omitted axis and top normals. Therefore
\[
2N_J=\int(h-1)\,d\nu-j_-n_-+j_+n_+.
\tag{LH.21}
\]
No equality between \(\nu\) and ordinary arclength of the actual
continuum niche graph is needed for this passage.

By LH2, \(\nu=\omega\). Subtract LH.21 from LH.20:
\[
2\mathcal P(U)=L_{\rm wing}+r e_R-l e_L+j_-q_--j_+q_+.
\]
The definitions of the middle endpoints and pressures give exactly
\[
j_-q_--j_+q_+=lC_L-rC_R.
\]
Using \(e_R=C_R\), \(e_L=C_L\), all four boundary terms cancel.

**Theorem LH3 (stationary wing identity).** Every canonical global
maximizer satisfies
\[
\boxed{2\mathcal P(U)=L_{\rm wing}.}
\tag{LH.22}
\]
In particular the length includes a possible top overhang. Omitting
that horizontal contribution would give the wrong identity for a
tilted cap whose top extends into a charged wing.

## 8. A height bound that survives zero-height exposure loss

Put
\[
S=A_-+A_+,\qquad E=e_R+e_L,\qquad Z=n_-+n_+.
\]
At a canonical maximizer the top meets J. Each exterior roof is
monotone toward its middle endpoint, including a possible horizontal
top portion. Hence its total vertical rise on the two wings is
\[
\int|\cos\theta|\,d\omega=S-E.
\tag{LH.23}
\]
For each finite positive niche graph the exact source decomposition
gives
\[
\operatorname{TV}(n_n|_{J_n})
=\int|\cos\theta|\,d\nu_n.
\]
Uniform convergence, after affinely identifying \(J_n\) with J, and
lower semicontinuity of total variation imply
\[
\operatorname{TV}(n|_J)\le\int|\cos\theta|\,d\nu
=S-E.
\tag{LH.24}
\]
The maximum of the continuous roof is attained. Going from the left
endpoint to a maximizing point and then to the right endpoint gives
\(2\max_J n-Z\le\operatorname{TV}(n|_J)\). Meanwhile the sum of
the two endpoint pressure equalities says \(E=(S+Z)/2\).
Consequently
\[
\boxed{\max_{x\in J}n_U(x)\le\frac{e_R+e_L}{2}.}
\tag{LH.25}
\]
This is a bound on the charged middle niche. It is not a bound on
the full niche outside J, nor an assertion that zero-height source
exposure disappears. It holds for horizontal and tilted canonical
maximizers alike.

## 9. Remaining sharp-value obligation

LH1–LH3 remove every nonpositive-pressure case from the full canonical
maximizing domain, give exact source measure equality on both quarters,
and provide the stationary length and middle-height identities. The
remaining caps have lower middle endpoint height strictly above one
half. Their middle facet can still be tilted, and source curvature
can still exceed one on regular arcs.

[The curvature and horizontal-value note](gate1-spatial-maximizer-curvature-and-horizontal-value.md)
uses these laws together with the exact short-width exclusion. A sharp
bound on all remaining wide and tilted maximizers is still required
before \(\mathcal P\le M/2\), and therefore Gate 1, can be marked
proved. No Lean/Lake build or CI is part of this written argument.
