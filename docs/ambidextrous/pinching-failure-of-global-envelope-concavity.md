# Pinching destroys global Minkowski concavity of ordinary full-turn envelope area

**Date:** 2026-10-08. **Status:** An exact, self-contained negative control on a genuinely global proof mechanism. Even after fixing *all four axis supports*, restricting to convex hulls with **upper/lower quarter curvature strictly below one**, and using **both complete conventional 90° turns**, the **total ordinary area** of the canonical envelope is not concave along Minkowski segments. The counterexample is symbolic; no finite-angle or floating-point integration enters its proof.

This does **not** refute Romik optimality: all example values are below the reference, and a source envelope on the nonconcave side has **empty central fibers and is disconnected**. The [horizontal gap-compression theorem](horizontal-gap-compression.md) converts that disconnected envelope into a different connected full-turn sofa of identical total area, which is why disconnected raw envelopes legitimately occur in the [unconstrained maximal-envelope variation](full-turn-unconstrained-envelope-variation.md). The theorem does not refute a concavity assertion restricted to actual hulls of connected two-turn bodies with nonempty surviving fibers.

## 1. A true Minkowski segment with fixed axis supports

Fix \(W=12/5\). For \(0<r<1/2\) put
\[
a=\frac65-r,\qquad d=\frac12-r,
\quad
K_r=\bigl([-a,a]\times[-d,d]\bigr)+rB_2+(0,\tfrac12),
\tag{PM.1}
\]
where \(B_2\) is the closed Euclidean unit disk.

Every \(K_r\) is convex, invariant under both reflections, has the *same* horizontal projection \([-6/5,6/5]\) and vertical projection \([0,1]\). Minkowski addition of rectangles and Euclidean disks shows **exactly**
\[
\boxed{\frac12(K_{r_-}+K_{r_+})=K_{(r_-+r_+)/2}.}\tag{PM.2}
\]
Unlike a family of plain horizontal capsules with changing height, this is an actual **fixed-axis-support** Minkowski segment.

Its upper-quarter supports, using \(u_t=(c,s)\), \(v_t=(-s,c)\), are
\[
f_r(t)=a c+(1-r)s+r,\qquad
g_r(t)=a s+(1-r)c+r,\quad 0\le t\le L=\pi/2.
\tag{PM.3}
\]
Their curvature densities are exactly \(f_r''+f_r=g_r''+g_r=r\in(0,1/2)\) on the open quarters. The common top/bottom horizontal face is \(J_r=[-a,a]\), of length \(2a>1\).

For an interior lower-turn angle, the canonical forbidden quadrant has roof
\[
w_{r,t}(x)=\min\left(
\frac{f_r(t)-1-xc}{s},\
\frac{g_r(t)-1+xs}{c}
\right).
\]
Let \(n_r(x)=\max\{0,\sup_{0<t<L}w_{r,t}(x)\}\). Directly from PM.3,
\[
f_r(t)-1-xc=(a-x)c+(1-r)(s-1)\le0\quad(x\ge a),
\]
and similarly \(g_r(t)-1+xs=(a+x)s+(1-r)(c-1)\le0\) for \(x\le-a\). Thus the *entire* positive niche is supported inside \(J_r\), **without** an asserted contact pattern or clipping assumption.

## 2. Ordinary area has one explicit nonnegative pinching correction

Let \(E_r=E_{\mathrm{full}}(K_r)\) be the full lower/upper canonical envelope, interpreted as a possibly disconnected union. By vertical reflection symmetry the upper forbidden niche is the vertical reflection of the lower niche. Outside \(J_r\), both positive niches vanish and \(E_r\) equals the outer hull. Over \(J_r\), the outer hull has the **whole** vertical fiber \([0,1]\); the two forbidden roofs cut it down to
\[
(E_r)_x=[n_r(x),1-n_r(x)]\quad\text{if }n_r(x)\le1/2,
\]
and leave an **empty** fiber when \(n_r(x)>1/2\). Therefore the exact ordinary-area identity is
\[
\boxed{
|E_r|=Q(r)+P(r),\qquad
Q(r)=|K_r|-2\int_{-a}^{a}n_r(x)\,dx,\qquad
P(r)=\int_{-a}^{a}(2n_r(x)-1)_+\,dx.
}\tag{PM.4}
\]
There is no dropped interaction or signed-area approximation: \(P\) corrects the over-subtraction from *two overlapping forbidden sweeps*. It is zero for nonempty central fibers and positive once they pinch apart.

The convex area is elementary (rectangle plus round margins):
\[
|K_r|=W+(\pi-4)r^2.
\tag{PM.5}
\]

## 3. The signed term \(Q(r)\) is smooth, by an explicit whole-niche formula

Put \(d_0=1-r\), \(k=d_0/(2a)\). In a neighborhood of the critical \(r\) introduced below, \(0<k<1/\sqrt2\). The two contact velocities are
\[
p=f_r'-g_r+1=d_0-2a\sin t,\qquad
q=g_r'+f_r-1=2a\cos t-d_0.
\]
Their unique zeros are
\[
t_a=\arcsin k<L/2,\qquad t_b=\arccos k>L/2.
\]
The first- and second-wall tangency abscissae are
\[
B_x(t)=a-d_0\cos t,\qquad
D_x(t)=-a+d_0\sin t,
\]
both strictly increasing. Their wall-height derivatives are
\[
\partial_t R_t(x)=\frac{x-B_x(t)}{\sin^2t},\qquad
\partial_t L_t(x)=\frac{x-D_x(t)}{\cos^2t}.
\]
The inner corner is
\[
x_r(t)=a\cos2t+d_0(\sin t-\cos t),\qquad
y_r(t)=a\sin2t+d_0(1-\sin t-\cos t).
\tag{PM.6}
\]
Its derivative satisfies \(x_r'(t)=p(t)\cos t-q(t)\sin t<0\) on \([t_a,t_b]\), using \(p\le0\le q\) there.

For \(t\in[t_a,t_b]\), the corner lies between its two wall-tangency abscissae: \(D_x(t)\le x_r(t)\le B_x(t)\). At \(x=x_r(t)\), every earlier second-wall roof is at most the current one (because \(D_x\) increases), and every later first-wall roof is at most the current one (because \(B_x\) increases). Hence the inner corner is the **global**, not merely stationary, roof maximizer at that \(x\).

For \(x\in[b_r,a]\), where \(b_r=B_x(t_a)=a-d_0\cos t_a>0\), the first-wall roof has its unique global maximum at the parameter \(t\ge t_a\) with \(B_x(t)=x\). The companion wall is strictly above it because \(p(t)\le0\); hence the resulting positive niche roof is
\[
n_r(x)=d_0-\sqrt{d_0^2-(a-x)^2}.
\]
The negative half is its horizontal reflection. For \(0\le x\le b_r\), \(n_r(x)=y_r(t)\) with \(x=x_r(t)\), \(t_a\le t\le L/2\). These formulas cover **every angle** and **every \(x\in J_r\)**.

Consequently the full one-turn niche area is exactly
\[
\boxed{
\int_{-a}^{a}n_r(x)\,dx
=2\int_{t_a(r)}^{L/2}
 y_r(t)\bigl(-x_r'(t)\bigr)\,dt
+2\int_0^{d_0\cos t_a(r)}
\bigl(d_0-\sqrt{d_0^2-z^2}\bigr)\,dz.
}\tag{PM.7}
\]
Every integrand and endpoint is analytic in \(r\) near the critical value, since \(0<k<1/\sqrt2\), \(d_0>0\), and \(\cos t_a<1\). Therefore \(Q(r)\) is \(C^2\) there. In particular for some finite constant \(C\), all sufficiently small \(\varepsilon>0\) satisfy
\[
\boxed{\left|Q(r_c)-\frac{Q(r_c-\varepsilon)+Q(r_c+\varepsilon)}2\right|\le C\varepsilon^2.}\tag{PM.8}
\]
No weighted-cap maximizing theorem, hidden regularity assertion, or analytic Romik calibration is imported.

## 4. A superquadratic-in-variation pinch is born at one exact parameter

For any angle \(t\), the forbidden-corner ordinate is \(y_r(t)\) in PM.6. Put \(z=\sin t+\cos t\in[1,\sqrt2]\). Since \(2\sin t\cos t=z^2-1\),
\[
y_r(t)=a(z^2-1)+d_0(1-z),
\]
a strictly **convex** quadratic in \(z\). Its maximum is therefore at \(z=1\) (value zero) or \(z=\sqrt2\) (at \(t=L/2\)), with value
\[
H(r)=a+(1-r)(1-\sqrt2)
=\frac{11}{5}-\sqrt2-(2-\sqrt2)r.
\tag{PM.9}
\]
Define
\[
\boxed{r_c=\frac{17/10-\sqrt2}{2-\sqrt2}.}\tag{PM.10}
\]
Rational square comparisons yield \(12/25<r_c<1/2\). By PM.9, \(H(r_c)=1/2\); for every \(r\ge r_c\), every niche point lies below \(1/2\), so
\[
\boxed{P(r)=0\quad(r_c\le r\le1/2).}\tag{PM.11}
\]

For \(r=r_c-\varepsilon\), set \(\delta=(2-\sqrt2)\varepsilon>0\). The center corner at \(t=L/2\) satisfies
\[
x_r(L/2)=0,\qquad y_r(L/2)=1/2+\delta,\qquad y_r'(L/2)=0.
\]
Here is a **uniform, exact** lower bound on its nearby curved roof. For \(12/25\le r\le1/2\) and \(|t-L/2|\le1/20\), use \(7/10\le a\le18/25\), \(1/2\le d_0\le13/25\), \(\sin2t\ge199/200\), and \(\sin t+\cos t\le3/2\). Then
\[
x_r'(t)=-2a\sin2t+d_0(\sin t+\cos t)
\le-\frac{613}{1000}<-\frac12,
\]
\[
|y_r''(t)|\le4a+d_0(\sin t+\cos t)
\le\frac{183}{50}<4.
\]
Thus the corner-x map covers \([-1/40,1/40]\) monotonically in this angle interval. For every \(|x|\le1/40\), choose its unique matching corner parameter. The mean-value theorem gives \(|t-L/2|\le2|x|\); Taylor's theorem gives
\[
\boxed{n_r(x)\ge y_r(t(x))\ge\frac12+\delta-8x^2.}\tag{PM.12}
\]
Choose \(\varepsilon\) small enough that \(r_c-\varepsilon>12/25\) and \(\sqrt{\delta/16}\le1/40\). On
\(|x|\le\sqrt{\delta/16}\), PM.12 yields \(2n_r(x)-1\ge\delta\). Consequently
\[
\boxed{
P(r_c-\varepsilon)
\ge\int_{-\sqrt{\delta/16}}^{\sqrt{\delta/16}}\delta\,dx
=\frac12(2-\sqrt2)^{3/2}\varepsilon^{3/2}.
}\tag{PM.13}
\]

This nonnegative correction is **order at least \(\varepsilon^{3/2}\)**, while the smooth signed-area second difference is only order \(\varepsilon^2\).

## 5. Exact failure of ordinary-envelope concavity

Take \(K_-=K_{r_c-\varepsilon}\), \(K_0=K_{r_c}\), and \(K_+=K_{r_c+\varepsilon}\) with \(\varepsilon>0\) sufficiently small. By PM.2, \(K_0=(K_-+K_+)/2\), and **all four axis supports agree**. From PM.4, PM.8, PM.11 and PM.13,
\[
\begin{aligned}
|E(K_0)|-\frac{|E(K_-)|+|E(K_+)|}{2}
&=Q(r_c)-\frac{Q(r_c-\varepsilon)+Q(r_c+\varepsilon)}2
-\frac{P(r_c-\varepsilon)}2\\
&\le C\varepsilon^2
-\frac14(2-\sqrt2)^{3/2}\varepsilon^{3/2}
<0
\end{aligned}
\]
for every sufficiently small positive \(\varepsilon\). Therefore
\[
\boxed{
|E((K_-+K_+)/2)|
<\frac{|E(K_-)|+|E(K_+)|}{2}.
}\tag{PM.14}
\]

**Theorem PM1 (fixed-axis, curvature-controlled failure of global concavity).** The unpenalized **ordinary total two-turn envelope area** is **not** Minkowski-concave on the domain of convex bodies having horizontal width \(12/5\), unit vertical span, equal positive top and bottom faces, both reflection symmetries, and constant open-quarter support-curvature \(r<1/2\).

**Mandatory scope qualification.** For \(r<r_c\), a whole small interval of central \(x\)-fibers is empty, so \(E(K_-)\) itself is **disconnected**. The theorem is about the **total canonical envelope functional on convex hulls**, which is exactly the unconstrained object optimized in FV1 after GC connectedification. It does **not** disprove concavity on a separately defined domain of *actual compatible same-hull connected* sofas with nonempty fibers. Such a restricted statement would require its own proof and would still not settle partial turns.

Numerical integration of the explicit PM.7 formula and the corner pinch formula provides a consistency check: \(r_c\approx0.4878679656\), and already at \(\varepsilon=0.001\) the midpoint concavity defect is approximately \(-1.12\times10^{-5}\). These floating values are **not part of the proof**.

## 6. Implication for a fresh sharp strategy

A proof based on unconstrained stationarity [FV1] **cannot** add the assertion that its entire raw envelope objective is globally Minkowski-concave merely because the *signed* quarter functional is strictly concave. The smooth signed component \(Q\) is concave in this family; the physical ordinary-area **pinch correction \(P\)** changes the variational geometry.

Any genuinely universal joint-area calibration must handle both:
1. **Clipped/overlapping niches** where two forbidden sweeps charge the same material; and
2. **Pinches and disconnected envelopes** whose area contains a positive-part correction.

Both are ordinary-area phenomena, but PM1 requires no reference to the old two-cap deficit \(G\) and no unproved global maximality hypothesis. It is a falsification of a whole global proof technique, not a new weak numerical upper bound or a claimed optimal sofa.
