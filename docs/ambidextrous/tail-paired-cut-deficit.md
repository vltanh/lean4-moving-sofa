# A direct clipping budget for arbitrary cuts near the top normal

**Scope.** This proves the exact missing-sign comparison on an infinite-dimensional class of independently cut upper and lower reference caps. The cuts may introduce facets, remove a top face, or lower the height; no differentiability or curvature bound is imposed on them. The proof pairs saved niche area with lost *outer-flank* area. It does not claim that every competitor belongs to this class or has this normalization. Labels TC are local.

Baseline: `eede8343b503db2c8a772e86ed086d6614cb9b18`. The only special geometric input is the explicit reference cap and its active circular tails from Notes 14/18 and the reference construction. The weighted-maximizer proof WV, its source-flux limit, and Gerver's upper bound are **not** used. All new arguments are pen and paper and remain subject to independent review.

## 1. Reference geometry and the allowed cut domain

Center Romik's reference in 0<=y<=1. Let m=1/(3 sin(beta)), where beta=arctan(Y) and 4Y^3+3Y-1=0 with Y>0. Its horizontal projection is I=[-m,m], and the horizontal hull faces are [a,b]=[-m/2,m/2]. Write U_* for the downward reference cap, A_* for its upper roof, and n_* for its nonnegative full niche roof. The actual reference has fibers [max(n_*,1-A_*),min(A_*,1-n_*)]. In particular

$$
A_*\ge1/2,\qquad 0\le n_*\le1/2,\qquad n_*=0\text{ outside }[a,b],
$$

and its area M equals 2 Psi(U_*), where Psi(U)=|U|-|N(U)|-|I|/2. This equality is an explicit reference calculation, not an optimality assumption.

Put L=pi/2. Fix 0<eta<beta and let D=(sin eta)/2. The right circular tail and adjacent outer flank have, for 0<=d<=D,

$$
A_*(b+d)=1/2+\sqrt{1/4-d^2},\qquad
n_*(b-d)=1/2-\sqrt{1/4-d^2}.\tag{TC.1}
$$

At t=L-arcsin(2d), the first wall attains the niche value at b-d, and the same outer support line attains the cap roof at b+d. Its companion wall is at least as high as the niche value. The left statements are the horizontal reflections. The four small intervals adjacent to a,b are disjoint because eta<beta and m>1.

Away from the two inner tail intervals

$$J=(a,a+D)\cup(b-D,b),$$

every positive reference niche value has an attaining turn parameter in [eta,L-eta]. This is precisely the candidate's initial circular tail, middle corner, and final circular tail decomposition. Endpoint/baseline exceptions are null sets and do not affect area.

An allowed cut cap U is a compact convex downward-closed body satisfying

$$I\times[0,1/2]\subseteq U\subseteq U_*,$$

and, for its upper support h_U,

$$
\boxed{h_U(\theta)=h_*(\theta)
\quad\text{on }[0,L-\eta]\cup[L+\eta,\pi].}\tag{TC.2}
$$

Thus only supports close to the vertical top normal may decrease. U need not touch y=1 and its top face need not have positive length. All allowed caps have the same horizontal projection I. A second cap V may be cut independently under the same conditions; no reflection relation between U and V is assumed.

## 2. A pointwise tail-loss inequality

Let A_U and n_U denote the cap and full niche roofs. Support monotonicity gives n_U<=n_*. Define the nonnegative support defect u(t)=h_*(t)-h_U(t) on the right affected quarter.

**Lemma TC1 (right tail).** For 0<d<D, put t=L-arcsin(2d). Then

$$
\boxed{
0\le n_*(b-d)-n_U(b-d)
\le\frac{u(t)}{\sin t}
\le A_*(b+d)-A_U(b+d).
}\tag{TC.3}
$$

**Proof.** At the outer point x=b+d, the actual support inequality for U gives

$$A_U(x)\le\frac{h_U(t)-x\cos t}{\sin t}
=A_*(x)-\frac{u(t)}{\sin t}.$$

At the inner point x=b-d, the first inner-wall height is

$$R_U(t,x)=\frac{h_U(t)-1-x\cos t}{\sin t}
=n_*(x)-\frac{u(t)}{\sin t}.$$

The companion support is h_U(t+L). Since eta<beta<pi/4 and t in (L-eta,L), its normal is outside the changed top-normal interval. Hence this companion support equals the reference support. Its wall height is at least the old active first-wall height n_*(x), and therefore at least R_U(t,x). The quadrant at this *single known reference parameter* supplies

$$n_U(x)\ge\max(0,R_U(t,x)).$$

This proves the middle inequality; the first is support monotonicity and the last was the outer support test. No claim that this parameter remains the new global maximizing parameter is needed. QED.

Horizontal reflection proves the left-tail analogue, pairing a+d with a-d. The cap itself is not assumed symmetric. Different admissible cuts of V satisfy exactly the same inequalities.

## 3. All niche savings occur in those two tails

For an x outside J with n_*(x)>0, take an attaining parameter in [eta,L-eta]. Its two normal angles are in [eta,L-eta] and [L+eta,pi-eta], where TC.2 leaves both supports unchanged. Therefore the old positive niche point is still approached by that same quadrant, giving n_U(x)>=n_*(x). The reverse inequality follows from U subset U_*.

Consequently n_U=n_* almost everywhere outside J. Integrate TC.3 and its reflection. The pairing x=b-d <-> b+d, and x=a+d <-> a-d, preserves the one-dimensional measure dx. Thus

$$
\boxed{|N(U_*)|-|N(U)|
\le\int_{a-D}^{a}(A_*-A_U)dx+
\int_b^{b+D}(A_*-A_U)dx.}\tag{TC.4}
$$

These two integrals count lost cap material on the outer flanks, outside the horizontal face. They do not count the interior hull region below the face that was already missing from the nonconvex reference.

## 4. A stronger one-cap deficit bound

Define Delta(U)=M/2-Psi(U), using the explicit identity Psi(U_*)=M/2. Because widths are unchanged,

$$\Delta(U)=|U_*|-|U|-\bigl(|N(U_*)|-|N(U)|\bigr).$$

The cap-area loss is integral_I(A_*-A_U). By TC.4 the niche saving is paid entirely on the two exterior flank strips. Over [a,b], A_*=1. Every other cap loss is nonnegative. Hence:

**Theorem TC2 (face-loss budget).** For every allowed cut cap,

$$
\boxed{\Delta(U)\ge\int_a^b(1-A_U(x))\,dx\ge0.}\tag{TC.5}
$$

The right side is the amount of convex cap material removed directly beneath the old horizontal face. It is exactly the budget needed below for clipping. This is stronger than merely knowing Delta>=0 for these caps, and it is proved without the global weighted theorem.

## 5. Two independent cuts: the clipping term is paid

Let rho(x,y)=(x,1-y), and define the actual two-turn envelope

$$E=(U\setminus N(U))\cap\rho(V\setminus N(V)).$$

The fiber is

$$[\max(n_U,1-A_V),\ \min(A_U,1-n_V)].$$

Since A_U,A_V>=1/2 and n_U,n_V<=n_*<=1/2, every fiber over I is nonempty and contains height one half. E is compact and connected. Its two canonical full-turn witnesses follow directly from its definition: for each turn it satisfies the cap's outer supporting inequalities and avoids its full niche; the endpoint strips have width at most one. No extra full-turn or actual-hull hypothesis is inserted.

For these nonempty fibers the exact two-cap identity is

$$|E|=\Psi(U)+\Psi(V)+G,$$

$$G=\int_I\bigl[\min(n_U,1-A_V)+\min(n_V,1-A_U)\bigr]dx.\tag{TC.6}$$

Both niche roofs vanish outside [a,b]. Hence

$$G\le\int_a^b(1-A_V+1-A_U)dx\le\Delta(U)+\Delta(V)$$

by TC.5. Therefore:

**Theorem TC3 (independent top-normal cuts).**

$$
\boxed{G\le\Delta(U)+\Delta(V),\qquad |E|\le M.}\tag{TC.7}
$$

Every compact body contained in E has the same area upper bound. The caps need not coincide, have matching faces, be smooth, or have a curvature density. Their niches may change active parameters and develop non-reference contact patterns; the proof uses only lower tests at unchanged reference parameters.

## 6. Interpretation and remaining boundary

This treats arbitrary convex cuts localized in an angular neighborhood of the vertical top normal of each cap, not merely one linear cut or a one-parameter asymptotic family. It includes sufficiently shallow independent upper and lower axis cuts of the reference, even when top or bottom faces collapse to points or move to different tips. The affine cut family is justified separately in the continuation note.

It does **not** treat arbitrary perturbations outside the angular window, arbitrary outward hull changes, or every saturated opposite-face body. Nor does it prove entry of every maximizer into this domain. Consequently it is a sharp ordinary-area case theorem and an explicit clipping-budget mechanism, not unrestricted optimality.

No computer assistance is needed for TC.3--TC.7. A short diagnostic may check the displayed circle identities, but cannot verify admission of an arbitrary cap. No CI, Lean/Lake compilation, dependency installation, manuscript build or long numerical search is used.
