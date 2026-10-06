# The exact leading deficit of the saturated axis-cut family

This resolves the sign deliberately left open in SAT1. The fully saturated axis-cut examples remain strictly below Romik's area, but by order tau^(3/2), not order tau. They still disprove the proposed corrected enclosure, including after saturation.

The calculation uses only the candidate's explicit circular arcs and elementary one-wall envelope maximization. It does not use unrestricted optimality. Labels SAC are local. The candidate arc formulas are the ones derived from Romik's construction in Notes 14 and 18; the general saturation argument is in [SAT1](saturation-does-not-rescue-repair.md).

## 1. Normalize the face interval and describe the actual cut

Translate the candidate so its top and bottom face endpoints have abscissae 0 and m, where

$$
m=\frac1{3\sin\beta},\qquad 4\tan^3\beta+3\tan\beta-1=0,
\qquad 1<m<4/3.
$$

Its horizontal width is 2m. Put L=pi/2. On a fixed neighborhood of L, the two upper-quarter supports are

$$
f_*(t)=\frac12+m\cos t+\frac12\sin t,
\qquad g_*(t)=\frac m2\sin t+\frac12\cos t.
\tag{SAC.1}
$$

The right outer support point and right inner tangency are, with z=L-t,

$$
A_*(t)=(m+\tfrac12\sin z,\ \tfrac12(1+\cos z)),
$$
$$
B_*(t)=(m-\tfrac12\sin z,\ \tfrac12(1-\cos z)).
\tag{SAC.2}
$$

Let H_tau be y+tau x<=1 and K_tau=K_* intersect H_tau. Write S_tau=Sigma intersect H_tau and T_tau=E(K_tau), its complete canonical saturation. SAT1 proves that T_tau is connected and feasible, contains S_tau, and has convex hull K_tau.

For small tau>0, the right intersection of the cutting line with the outer arc is

$$
P=(m+\tfrac12\sin z,\ Y),\qquad Y=\tfrac12(1+\cos z),
$$

where z>0 is small and

$$
\tau=\frac{1-\cos z}{2m+\sin z}.
\tag{SAC.3}
$$

Set delta=arctan(tau) and t_P=L-z, t_tau=L-delta. In particular z>delta for small tau, and z/(2 sqrt(m tau)) tends to one. The cut-hull support on the affected quarter is exactly

$$
f_\tau(t)=
\begin{cases}
f_*(t),&t\leq t_P,\\
P\cdot\mu_t,&t_P\leq t\leq t_\tau,\\
\sin t,&t_\tau\leq t\leq L.
\end{cases}
\tag{SAC.4}
$$

The first join is a tangency; the second has an exposed-edge atom. All other quarters are unchanged. This follows directly from the boundary of the convex intersection: it consists of the old boundary, the segment from (0,1) to P, and its endpoints.

## 2. Only one lower-niche tail can change

Write R_t(x)=(f(t)-1-x cos(t))/sin(t), L_t(x)=(g(t)-1+x sin(t))/cos(t). The positive lower niche roof is the maximum of zero and sup_t min(R_t,L_t).

Because f_tau<=f_* and g is unchanged, the lower niche can only shrink. The upper niche is unchanged, since its two support quarters are unchanged. The convex hull's lower boundary is unchanged, since the cut lies strictly above y=1/2 throughout the fixed projection for small tau.

The old roof pieces other than the terminal B arc have their active parameters in a fixed compact interval below t_P. They are therefore unchanged wherever they were active. On the terminal B arc, define

$$
x_B=m-\tfrac12\sin z,\qquad x_P=m+\tfrac12\sin z,
\qquad D=\sqrt{1-Y^2},\qquad x_Z=x_P-D.
\tag{SAC.5}
$$

For small z, x_B<x_Z<m, and all these abscissae lie strictly in the candidate's terminal-tail neighborhood and in (0,m).

**Lemma SAC1 (the changed roof).** The old and new positive lower roofs agree outside [x_B,m]. On this interval they are

$$
F_*(x)=\frac12-\sqrt{\frac14-(x-m)^2},
$$
$$
F_\tau(x)=
\begin{cases}
Y-\sqrt{1-(x-x_P)^2},&x_B\leq x\leq x_Z,\\
0,&x_Z\leq x\leq m.
\end{cases}
\tag{SAC.6}
$$

**Proof.** On [t_P,t_tau], f_tau=P dot mu, so its single-wall envelope is the lower arc of the unit circle centered at P: its stationary point has x=x_P-cos(t) and height Y-sin(t). The component p=f_tau'-g+1 is strictly negative uniformly on this short interval for small z; its limit is -m/2. Therefore the companion L wall is strictly higher at every such tangency. The unit-circle envelope is consequently a genuine min-wall roof, not just an upper relaxation.

For x>=x_B, every unchanged earlier R line has value at most R_{t_P}(x). Indeed the reference B_x is nondecreasing and B_x(t)<=x_B for t<=t_P, so the identity partial_t R_t=(x-B_x(t))/sin^2(t) gives that maximum. The new family includes t_P and is no smaller than that line at its maximum. On [t_tau,L), (SAC.4) instead gives R_t(x)=1-csc(t)-x cot(t)<0 for x>0, so this part contributes no positive roof. The axis constraint supplies height zero.

The positive portion of the unit-circle envelope ends exactly at x_Z. Its stationary parameters up to this endpoint lie strictly between t_P and t_tau for small z: cos(t) ranges from sin(z) to D, both of order z, whereas cos(t_tau) is of order z^2. Thus no stationary point used in (SAC.6) lies outside the specified support piece. For x between x_Z and m the maximum of that family is nonpositive (or decreases to a nonpositive endpoint value), so the positive roof is zero.

For x<x_B the old active tail parameter, or old core/left-tail parameter, is unchanged; since the new niche is a subset of the old one, this proves equality there. For x>=m the old positive niche is absent, hence so is the new one. These observations prove the claim. QED.

No curvature cap is imposed on K_tau in this proof. Its atom is explicitly retained in (SAC.4).

## 3. Exact gain and exact loss

The only new material in T_tau relative to S_tau is the recovered lower-niche tail in (SAC.6). It lies close to y=0 and is disjoint from the cut and the unchanged upper niche. Its area G(z) is

$$
G(z)=\int_{x_B}^m F_*(x)\,dx-\int_{x_B}^{x_Z}F_\tau(x)\,dx.
\tag{SAC.7}
$$

The two integrals are respectively

$$
\frac{2\sin z-\sin z\cos z-z}{8}
$$

and

$$
Y(\sin z-D)-\frac12[\sin z\cos z+z-DY-\arccos Y].
\tag{SAC.8}
$$

These follow by the elementary antiderivative of sqrt(R^2-x^2), with R=1/2 and R=1. In particular G(z)>0 for small z, also clear from the strict change in the two roof arcs.

The original cut removes material only near the two height-one tips. In a fixed neighborhood of either tip, the candidate's top boundary is the upper arc of a circle of radius 1/2. This uses an outer-hull arc on one side and a reflected inner-niche arc on the other, with matching circle centers. The rest of the boundary is a fixed positive distance below one. The lower boundary is separated from these tips. For small tau the removed regions are therefore exactly the two circular caps, not pieces of an unverified hull-area loss.

Let

$$
C(v)=\frac14(v-\sin v\cos v).
$$

At the left tip the line passes through the tip, and its cap half-angle relative to the outward normal is delta. At the right tip the half-angle is z-delta by (SAC.3). Thus

$$
M-|S_\tau|=C(\delta)+C(z-\delta).
\tag{SAC.9}
$$

The lower recovery and these upper losses are disjoint. Combining (SAC.7)-(SAC.9) gives an exact ordinary-area identity:

$$
\boxed{M-|T_\tau|=C(\delta)+C(z-\delta)-G(z).}
\tag{SAC.10}
$$

## 4. The leading coefficient is positive

There is a simple way to extract the sign without cancellation among inverse trigonometric formulas. Set a=z/2 and rescale x=m+a X on the shrinking lower-tail interval. Uniformly on bounded X intervals, the old roof divided by a^2 tends to X^2, while the new one tends to

$$
\left(\frac{(1-X)^2}{2}-1\right)_+.
$$

Its endpoint limits are X=-1 and X=1-sqrt(2). Hence, by elementary uniform convergence and integration,

$$
\lim_{z\downarrow0}\frac{G(z)}{(z/2)^3}
=\int_{-1}^{1-\sqrt2}\frac{(X+1)^2}{2}\,dX
 +\int_{1-\sqrt2}^{0}X^2\,dX
=\frac{3-2\sqrt2}{3}.
\tag{SAC.11}
$$

Also C(v)=v^3/6+O(v^5), delta=O(z^2), and (z/2)^3/(m tau)^(3/2) tends to one by (SAC.3). Equation (SAC.10) therefore proves:

**Theorem SAC2 (strict deficit after full saturation).** For sufficiently small positive tau,

$$
|T_\tau|<M,
$$

and more precisely

$$
\boxed{
\lim_{\tau\downarrow0}\frac{M-|T_\tau|}{\tau^{3/2}}
=\frac{1+2\sqrt2}{3}\,m^{3/2}>0.
}
\tag{SAC.12}
$$

This establishes the sign without invoking the conjectured optimal value. Replacing T_tau by the actual candidate gives an area improvement of precisely this leading order, but that comparison is proved only for this family.

## 5. What the calculation rules out

SAT1's corrected-functional failure survives: its claimed energy charge is of order tau, while (SAC.12) is only of order tau^(3/2). In particular, saturation does not convert the failed global budget into a valid one.

There also cannot be a universal positive constant c, even restricted to these saturated near-candidate bodies, such that

$$
M-|T|\geq c\int_0^L|h_T'-h_*'|^2\,dt.
$$

Indeed, on t_tau<t<L the two derivative traces differ by -m+O(sqrt(tau)) as in AX1, over an interval of length arctan(tau). The integral is at least a positive constant times tau, whereas (SAC.12) is o(tau). The actual set and hull remain close, but the transfer of a long axis face to a nearby non-axis normal carries an energy not proportional to ordinary missing area.

This is an explicit stress test for the next global proof: auxiliary tail variables or an exposed-face term must retain this distinction. It does not invalidate the earlier calibration on its stated domain or prove a competing sofa exceeds M.

The proof above is analytic. A separate numerical check of the cap-integral formulas and their limiting coefficient was used as a diagnostic, not as the justification for (SAC.12). No CI or Lean/Lake compilation was used. The candidate dependencies and this argument remain subject to independent review.
