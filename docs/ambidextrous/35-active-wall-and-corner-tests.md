# 35. Active-wall curvature and the moving-corner derivative

This note begins the structural calculation rather than assuming its conclusion. It proves local contact tests without assuming the curvature cap. It also records why differentiating a maximum of minima while freezing its active angle is invalid.

All statements below concern interior angles and smooth local contact data. They do not regularize an arbitrary maximizer, justify a disconnected variation, or dispose of exposed-edge atoms. Compare Romik's local contact analysis, [Section 3](https://arxiv.org/html/1606.08111v3#S3), and the repository's exact roof formulas in Note 17.

## 35.1 Notation without a curvature restriction

Let L=pi/2. On an interior angle interval let f(t)=h_K(t), g(t)=h_K(t+L) be C^2 support functions of a convex hull K in 0<=y<=1. Put

\[
\rho_f=f''+f,\quad\rho_g=g''+g,\quad
p=f'-g+1,\quad q=g'+f-1,
\]

\[
c=(f-1)\mu+(g-1)\nu,\quad B=c+p\nu,\quad D=c-q\mu.
\]

No inequalities rho<=1 or p<=q are imposed. At a fixed horizontal coordinate x the forbidden quadrant has height

\[
\min\{R_t(x),L_t(x)\},\qquad
R_t(x)=\frac{f(t)-1-x\cos t}{\sin t},\quad
L_t(x)=\frac{g(t)-1+x\sin t}{\cos t}.
\]

The lower sweep roof, when bounded above in the incoming strip, is the positive part of the supremum of these minima. Direct differentiation gives

\[
\partial_tR_t(x)=\frac{x-B_x(t)}{\sin^2t},\quad
\partial_tL_t(x)=\frac{x-D_x(t)}{\cos^2t},
\]

\[
B_x'=(1-\rho_f)\sin t,\quad
D_x'=(1-\rho_g)\cos t,
\quad R_t(x)-L_t(x)=\frac{c_x(t)-x}{\sin t\cos t}.
\tag{35.1}
\]

## 35.2 The curvature cap holds at a smooth single-wall contact

**Lemma 70 (active tangency test).** Suppose an interior parameter t supplies a positive-height local maximum of min(R_s(x),L_s(x)) as s varies, and R_t(x)<L_t(x). Then

\[
x=B_x(t),\qquad p(t)<0,\qquad\rho_f(t)\leq1.
\tag{35.2}
\]

If the local maximum has strictly negative second derivative, rho_f(t)<1. With the two walls exchanged, a contact with L_t(x)<R_t(x) has

\[
x=D_x(t),\qquad q(t)>0,\qquad\rho_g(t)\leq1.
\tag{35.3}
\]

**Proof.** Strict separation of the two roof values persists near t, so the minimum is just the smaller smooth function there. Its derivative must vanish. Equation (35.1) identifies x=B_x(t), and then

\[
\partial_t^2R_t(x)=\frac{\rho_f(t)-1}{\sin t}.
\]

The second derivative is nonpositive at a local maximum. At B=c+p nu, strict satisfaction of the companion inner-wall inequality is exactly p<0. The other case uses the second derivative (rho_g-1)/cos(t) and q>0. QED.

This is a necessary condition at an **active tangency**, not on the entire outer boundary. A normal with rho>1 can still affect the niche through its corner. Concluding the global curvature cap from (35.2) alone would lose that contribution.

## 35.3 Two orientations of a transverse corner contact

Suppose x=c_x(t), c_x'(t) is nonzero, and the corner gives a local maximum of the minimum of the wall heights. Since c'=p mu+q nu,

\[
c_x'=p\cos t-q\sin t,\qquad
\partial_tR_t(x)=p/\sin t,\quad
\partial_tL_t(x)=q/\cos t.
\]

**Lemma 71 (corner signs).** If c_x'<0, then p<=0<=q. If c_x'>0, then q<=0<=p. For a strictly transverse peak with nonzero one-sided derivatives the inequalities are strict.

**Proof.** If c_x'<0, R-L changes from positive to negative: the minimum uses L before the meeting and R afterwards. A local maximum requires the left derivative nonnegative and the right derivative nonpositive. If c_x'>0 the roles reverse. QED.

Call the first orientation standard and the second reverse. Neither can be discarded from an unrestricted roof calculation merely by naming the candidate's standard orientation.

For a positive-height reverse corner there is a useful strict size bound. The two outer support contacts are

\[
A=c+\mu+p\nu,\qquad C=c+\nu-q\mu.
\]

They belong to K and hence have y-coordinate at most one. Therefore

\[
p\leq\frac{1-c_y-\sin t}{\cos t}<1,
\qquad
-q\leq\frac{1-c_y-\cos t}{\sin t}<1.
\tag{35.4}
\]

Here p>=0 and -q>=0, and the final strict inequalities use c_y>0 and sin(t)+cos(t)>1. These are local geometric bounds, not a global contact-order theorem.

## 35.4 The active angle moves in a support variation

Vary f,g by f+epsilon v and g+epsilon w. At a transverse corner graph, solve c_epsilon,x(t_epsilon(x))=x by the implicit-function theorem. Then

\[
\dot F(x)=\frac{p(t)w(t)-q(t)v(t)}{c_x'(t)},
\qquad x=c_x(t).
\tag{35.5}
\]

**Proof.** The corner displacement at fixed t is delta c=v mu+w nu. Differentiating its x-coordinate equation gives dot t=-delta c_x/c_x'. Thus dot F=delta c_y-c_y' delta c_x/c_x'. Its numerator is det(c',delta c)=p w-q v. QED.

For a standard corner arc, integration in increasing x reverses the angular orientation and gives the niche-area variation

\[
\int(qv-pw)\,dt.
\tag{35.6}
\]

For a reverse arc the contribution is its negative. At a smooth R tangency the envelope derivative is v/sin(t); with dx=(1-rho_f)sin(t)dt its area contribution is

\[
\int(1-\rho_f)v\,dt.
\tag{35.7}
\]

The L tangency analog is integral (1-rho_g)w. Moving chart endpoints cancel when the adjacent roof pieces have the same height at a join; a finite-chart derivative needs that matching and the usual local stability assumptions. Coincident contact continua are not covered by this calculation.

## 35.5 A counterexample to a tempting max-min derivative rule

Consider

\[
F(\varepsilon)=\max_{-1\leq t\leq1}\min(t+\varepsilon,-t).
\]

For |epsilon|<2, the maximum is at t=-epsilon/2 and F(epsilon)=epsilon/2. At epsilon=0 the only maximizing parameter is t=0. But taking the smaller of the two epsilon-derivatives at that fixed parameter gives min(1,0)=0, not 1/2.

Thus a rule of the form "maximize the minimum of the derivatives at the old active parameters" is false for a maximum of minima. The crossing parameter must be allowed to move. Equation (35.5) is the corresponding correction for a transverse sofa corner.

The explicit counterexample rules out one possible shortcut in the pending nonsmooth variation argument. It does not rule out directional derivatives with the moving-angle/contact conditions handled correctly.
