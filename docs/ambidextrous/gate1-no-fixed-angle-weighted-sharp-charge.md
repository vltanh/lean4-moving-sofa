# Gate 1 no-go: fixed angular packings cannot give a **sharp** facet-sweep charge

**October 9, 2026 · Status:** An exact negative result for a specifically proposed **GLOBAL** Gate 1 proof mechanism. A finite or countably weighted average of one-angle forbidden triangle areas, certified by a *pointwise no-double-counting condition*, is **strictly smaller** than the true complete niche area already at Romik's equality hull. Thus **no such weighted-angle scheme can establish the sharp value \(M\)**. A correct global payment must instead use the **full positional envelope** \(\sup_t\), or weights depending on the position/active contact (or another non-pointwise global transport).

This is **not the sharp Gate 1 inequality** and does not eliminate more feasible sofa classes or improve the unrestricted upper bound. It is a rigorous falsification of an attempted route to [G1.5](SHARP-OPTIMALITY-EXECUTION-PLAN.md), not a new completion claim. No finite-angle sampling or numerical calculation enters the proof.

## 1. The reference has a continuum of uniquely exposed inner corners

Let \(K_*\) be Romik's actual ambidextrous hull, \(U_*\) its upper downward cap, \(I=[-m,m]\), and \(b=m/2\). Its true positive lower full-turn niche is
\[
N_*=\{(x,y):0<y<n_*(x)\}.
\]
It lies inside the common horizontal face interval \([-b,b]\), so every niche point lies inside the actual hull; see [RH.5–RH.6](romik-horizontal-misalignment-sharp-bound.md).

Write, for \(0<t<L=\pi/2\),
\[
R_t(x)=\frac{f_*(t)-1-x\cos t}{\sin t},\quad
D_t(x)=\frac{g_*(t)-1+x\sin t}{\cos t},\quad
q_t(x)=\min\{R_t(x),D_t(x)\}.
\]
The physical inner corner is
\[
C_t=(\xi_t,\eta_t)=(f_*(t)-1)u_t+(g_*(t)-1)v_t.
\]
The reference has a nonempty compact middle angular interval
\[
J\Subset(\beta,\pi/2-\beta),\quad\beta=\arctan Y,
\]
on which the contact velocities are strictly \(p=f_*'-g_*+1<0<q=g_*'+f_*-1\), the moving-corner x-coordinate \(\xi_t\) is strictly decreasing and \(\eta_t>0\). These inequalities follow from the explicit reference support formulas ([RH.2](romik-horizontal-misalignment-sharp-bound.md), [PJ-MID](spatial-half-partition-middle-arc-variation.md)). Shrink J to preserve strict margins; its image \(X=\xi(J)\) has positive length.

**Lemma ANG1 (unique global angular exposure).** For every \(t\in J\), the *entire continuum* roof \(s\mapsto q_s(\xi_t)\) has a **strict unique global maximum** at \(s=t\):
\[
\boxed{
n_*(\xi_t)=q_t(\xi_t)=\eta_t>0,\qquad
q_s(\xi_t)<\eta_t\quad\forall\,s\in(0,L)\setminus\{t\}.
}\tag{ANG.1}
\]

**Proof.** Define the two stationary-wall abscissae
\[
B_x(s)=\xi_s-p(s)\sin s,\qquad
D_x(s)=\xi_s-q(s)\cos s.
\]
The exact support-curvature bounds \(0\le f_*''+f_*\le1\), \(0\le g_*''+g_*\le1\) on the entire quarter yield
\[
B_x'(s)=(1-\rho_f(s))\sin s\ge0,\qquad
D_x'(s)=(1-\rho_g(s))\cos s\ge0.
\]
At \(s=t\), strict \(p(t)<0<q(t)\) implies
\[
D_x(t)<\xi_t<B_x(t).
\]
The exact ray-height derivatives at fixed x are
\[
\partial_sR_s(x)=\frac{x-B_x(s)}{\sin^2s},\qquad
\partial_sD_s(x)=\frac{x-D_x(s)}{\cos^2s}.
\]
For any \(s<t\), \(D_x(s)\le D_x(t)<\xi_t\), so \(D_s(\xi_t)\) is strictly increasing for all \(s<t\) and is strictly smaller than \(D_t(\xi_t)\). Thus
\(q_s(\xi_t)\le D_s(\xi_t)<D_t(\xi_t)=\eta_t\).
For any \(s>t\), \(B_x(s)\ge B_x(t)>\xi_t\), so \(R_s(\xi_t)\) is strictly decreasing for \(s>t\), whence
\(q_s(\xi_t)\le R_s(\xi_t)<R_t(\xi_t)=\eta_t\).
At the meeting corner both rays have the same height. This proves ANG.1 **globally**, including source angles outside the middle chart. \(\square\)

## 2. No finite list of angles can be sharp, even just on the equality hull

**Corollary ANG2.** For every finite set \(F\subset(0,L)\),
\[
\boxed{
\left|K_*\cap\bigcup_{t\in F}Q_t(K_*)\right|
<
\left|K_*\cap\bigcup_{0<t<L}Q_t(K_*)\right|
=|N_*|.
}\tag{ANG.2}
\]

**Proof.** For all x in the positive-length interval X except the finite set \(\xi(F\cap J)\), the maximum among finitely many selected ray roofs is strictly less than the true positive roof \(n_*(x)\) by ANG.1. Both are continuous in x on this compact interior interval (a finite maximum of continuous roofs, and the whole positive roof's uniform endpoint clearance). Thus at each such x an entire positive-height vertical interval is missing from the finite union, **inside K***. Fubini gives strictly positive total missing ordinary area. \(\square\)

In particular a method that bounds the complete niche from below using only **finitely many** exact hallway-angle constraints cannot yield \(|K_*|-2|N_*|=M\) with equality. Merely increasing a finite angular sample may approximate M but never prove the exact sharp value with that sample alone.

## 3. Even a finite **measure** on angles cannot provide a sharp pointwise-packed average

The failure is not restricted to an ordinary finite set.

For an arbitrary **finite nonnegative Borel measure** \(\mu\) on the angular quarter, put
\[
\kappa_\mu(x,y)=
\int_{(0,L)}
\mathbf1_{\{(x,y)\in Q_t(K_*)\}}\,d\mu(t).
\]
Suppose a proposed global-area argument uses the **pointwise no-overcounting condition**
\[
\boxed{\kappa_\mu(x,y)\le1
\quad\text{for a.e. }(x,y)\in N_* .}\tag{ANG.3}
\]
This is precisely what would justify replacing the *area of the union* by the weighted sum of one-angle triangle areas as a **lower bound**.

**Theorem ANG3 (every finite pointwise-packed angular payment leaves positive slack).**
\[
\boxed{
\int_{(0,L)}|K_*\cap Q_t(K_*)|\,d\mu(t)
=\int_{N_*}\kappa_\mu(x,y)\,dx\,dy
<|N_*| .
}\tag{ANG.4}
\]

**Proof.** By Tonelli, the equality is exact. A finite measure has at most countably many atoms. Since the x-coordinate map \(t\mapsto\xi_t\) is strictly monotone on J, for almost every \(x\in X\) its unique active parameter \(t(x)\in J\) is **not an atom** of \(\mu\).

Fix any such x. For \(y<n_*(x)\), the angular active set
\[
A_{x,y}=\{t\in(0,L):q_t(x)>y\}
\]
decreases as \(y\uparrow n_*(x)\). The joint continuity of the *positive* two-wall roofs including the endpoint angles, the compactness of \([0,L]\), and the **unique** maximizer ANG.1 imply that the nested sets concentrate on \(\{t(x)\}\): for every open angular neighborhood V of \(t(x)\), they lie inside V once y is sufficiently close to the roof. Consequently, by finiteness and continuity from above of \(\mu\),
\[
\lim_{y\uparrow n_*(x)}\kappa_\mu(x,y)
=\mu(\{t(x)\})=0.
\]
Thus there is a positive-length vertical interval **just below** the roof on which \(\kappa_\mu(x,y)<1/2\). As the reference middle niche lies inside K* and has positive roof over X, Fubini shows
\[
\int_{N_*}[1-\kappa_\mu(x,y)]dx\,dy>0.
\]
Use ANG.3 and Tonelli to obtain the strict inequality in ANG.4. \(\square\)

The same conclusion holds for the vertically reflected upper-turn niche. Therefore **fixed angular weights with pointwise multiplicity ≤1 cannot pay all of Romik's complete two-handed niche area**. This statement does **not** rule out a *position-dependent* measure \(\mu_x\), a calibrated coarea/transport argument involving active contact charts, signed weights with separate compensating terms, or any truly global area inequality of a different form.

## 4. Consequence for the ONE Gate 1 proof direction

The currently required theorem is still, for every genuine connected full-turn sofa hull K,
\[
\boxed{|K|-\mathcal N_-(K)-\mathcal N_+(K)\le M
\quad\text{(Gate 1 remains OPEN).}}
\]

The pointwise-packed fixed-angular-average method ANG.3 is rigorously rejected as a **sharp** certificate. It loses positive area even on the unique explicitly calibrated equality witness, and an upper bound obtained by substituting its weighted triangular payment cannot be at most M there. The only promising *facet-sweep* certificate within the controlling roadmap must charge the **complete positional envelope** \(n_F(x)=\sup_t(q_t(x)-B_F(x))_+\) without a strictly lossy global averaging step.

No new unrestricted upper bound, closing sharp inequality, verified above-M sofa, CI, Lean/Lake formalization or independent journal refereeing is claimed.
