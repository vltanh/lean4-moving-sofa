# A saturated shadow-clipping obstruction to the derivative-free repair budget

This tests the ordinary-area premise of AB.5 before using any further calibration. The premise is false, even with the genuine shared anchors of AB1, both full turns, canonical saturation, candidate width, and areas tending to the candidate value from below. The obstruction is **clipping**, not adverse contact velocities or the derivative-energy charge already rejected by AX1.

The argument is analytic. Its candidate inputs are the explicit terminal circular arcs of Notes 14 and 18, also written out in SAC.1--SAC.2. The only general repair input is the definition of the least quarter-curvature majorant R in GM2; its action on the present family is proved directly by a Dirichlet comparison. The actual-area calculation uses elementary slicing, and the signed-roof identity is invoked only for a profile satisfying its curvature hypotheses. None of the statements below proves unrestricted optimality or uniqueness.

## 1. A curvature-dominated outer set, defined explicitly

Translate the candidate Sigma so its top and bottom hull faces have interval [0,m], where

$$
m=\frac1{3\sin\beta},\qquad 1<m<4/3.
$$

Its horizontal projection is [-m/2,3m/2] and its width is 2m. Put L=pi/2. On the candidate's final upper-quarter phase,

$$
f_*(t)=\tfrac12+m\cos t+\tfrac12\sin t,
\qquad g_*(t)=\tfrac m2\sin t+\tfrac12\cos t.
\tag{SC.1}
$$

Choose z>0 sufficiently small that L-z remains inside this phase. Define

$$
s=\sin z,\quad c=\cos z,\quad Y=(1+c)/2,
\quad D=\sqrt{1-Y^2},
$$
$$
x_P=m+s/2,\quad x_Z=x_P-D,
\quad P=(x_P,Y),
\quad t_0=L-z,\quad t_1=L-\arccos Y.
\tag{SC.2}
$$

For small z, 0<x_Z<m<x_P and t_0<t_1<L. Replace only the first upper quarter by

$$
\bar f_z(t)=
\begin{cases}
f_*(t),&t\leq t_0,\\
P\cdot\mu_t,&t_0\leq t\leq t_1,\\
1+x_Z\cos t,&t_1\leq t\leq L.
\end{cases}
\tag{SC.3}
$$

Keep g_* and the entire lower semicircle unchanged. Denote the full support by bar h_z.

**Lemma SC1 (a convex outer set).** This is the support of a compact convex body bar K_z contained in K_*=conv(Sigma). It has the same four axis supports as K_*, and its open-quarter curvature is dominated by angular measure.

**Proof.** P is the candidate's outer support point at t_0, so the first join matches value and derivative. The identities cos(t_1)=D, sin(t_1)=Y and P=(x_Z,0)+(D,Y) give matching at the second join as well. On the changed pieces the curvature densities are respectively the original density 1/2, zero, and one. The right endpoint of the top face changes from m to x_Z; its length remains positive. All other axis jumps are unchanged and nonnegative. Thus the periodic curvature measure is nonnegative, giving a convex support function.

The vertex support P dot mu is at most h_*. On the last piece put d=L-t. Its difference from the reference is

$$
\bar f_z-f_*=(x_Z-m)\sin d+\tfrac12(1-\cos d).
$$

After division by sin(d)>0 this is x_Z-m+(1/2)tan(d/2), increasing in d. At d=arccos Y its value is nonpositive because this piece matches the vertex support; hence the whole piece is below h_*. At d=0 the difference is zero. Inclusion in K_* and equality of the four axis supports follow. QED.

The changed outer boundary is a unit-circle arc centered at (x_Z,0), running from its top (x_Z,1) to P, followed by the unchanged candidate outer flank. The interval of normals [t_0,t_1] supports the vertex P, not an additional arc.

## 2. Its full envelope is a feasible connected body

Let F_* be the candidate's positive lower niche roof. On the terminal tail near x=m,

$$
F_*(x)=\tfrac12-\sqrt{\tfrac14-(x-m)^2}\quad(x\leq m).
\tag{SC.4}
$$

The positive lower roof associated with bar h_z is unchanged except on [x_B,m], where x_B=m-s/2. There it is

$$
\bar F_z(x)=
\begin{cases}
Y-\sqrt{1-(x-x_P)^2},&x_B\leq x\leq x_Z,\\
0,&x_Z\leq x\leq m.
\end{cases}
\tag{SC.5}
$$

Here is a direct contact check. On [t_0,t_1] the first support is P dot mu, so its one-wall stationary envelope is the displayed unit-circle arc. Its contact velocity p=f'-g+1 is strictly negative on this short interval, since its limiting value is 1-3m/2<0. The other wall therefore does not cut off the stationary height. On [t_1,L] the first-wall tangency point is the constant point (x_Z,0), adding no positive roof. All earlier positive roof pieces have their old active parameters and remain unchanged. The derivative identity partial_t R_t(x)=(x-B_x(t))/sin^2(t), with the now nondecreasing B_x, verifies the global maximum rather than merely a stationary contact. This is also the specialization of the signed-roof calculation to these three pieces.

Only upper-semicycle supports were changed, so the upper-turn sweep is the original reflected candidate sweep. Since bar h_z<=h_*, the lower sweep can only shrink. Both sweeps stay on their original opposite sides of the midline. Let

$$
B_z=\bar K_z\setminus\bigl(W_-(\bar K_z)\cup W_+(\bar K_z)\bigr).
\tag{SC.6}
$$

The two horizontal extreme points of K_* at height 1/2 are unchanged, so bar K_z contains the entire midline segment across its projection. That segment avoids both sweeps. Every vertical fiber of B_z is an interval meeting this segment. Thus B_z is compact and path connected. Its defining canonical placements give both complete quarter-turn motions. The point (0,1), the bottom endpoints (0,0),(m,0), and the horizontal extreme points all survive; its incoming span is still one and its horizontal width is still 2m.

No assertion that bar K_z is the body's actual hull has been made. In fact it is not: its top point (x_Z,1) lies strictly inside the unchanged upper niche.

## 3. The actual hull repairs back to precisely this outer set

Write H_z=conv(B_z) and h_z=h_{H_z}.

**Lemma SC2 (same repair, and actual canonical saturation).**

$$
R(H_z)=\bar K_z,
\qquad B_z=\mathcal E(H_z).
\tag{SC.7}
$$

In particular the example satisfies the actual-hull and saturation premises, not only a fixed external witness construction.

**Proof.** On the first upper quarter, all bar K_z support points with normals t<=t_0 lie on unchanged outer flank to the right of P. Their abscissae exceed m, so the upper niche is absent there; their ordinates are at least 1/2, so the lower niche is absent too. P itself survives, giving the support for every t in [t_0,t_1]. Thus h_z=bar h_z on [0,t_1]. The left upper flank and all lower outer flanks survive as well, and the retained face endpoints attain the top and bottom supports. Hence h_z=bar h_z everywhere except possibly (t_1,L).

The function bar f_z satisfies bar f_z''+bar f_z=1 on [t_1,L]. Any support majorant k>=h_z with k''+k<=1 has endpoint values at least bar f_z at t_1 and L. The positive Dirichlet Green kernel for -d^2/dt^2-1 on an interval of length less than pi gives k>=bar f_z there. On the rest of the circle k>=h_z=bar h_z. Since bar h_z itself is a curvature-dominated majorant of h_z, this proves it is the least one, that is R(H_z)=bar K_z.

For the saturation claim, the lower positive roof in (SC.5) is attained by parameters at most t_1, where the actual hull support is unchanged. Elsewhere its unchanged positive pieces also have unaltered parameters. Tightening the support from bar h_z to h_z can only lower this roof, so the retained attaining parameters force exact equality of the two positive roofs. The upper roof is unchanged identically. Therefore their full swept removals inside the incoming strip are the same. Since B_z is contained in H_z and H_z is contained in bar K_z, saturation inside H_z produces exactly B_z. QED.

## 4. A strictly positive ordinary-area error with favorable velocities

The lower niche (SC.5) is contained in bar K_z: it is over the bottom-face interval [0,m], is below the candidate's strict midline margin, and the changed upper boundary stays well above it. The upper niche, however, extends outside bar K_z near x=m. Let bar T_z(x) be the upper boundary of bar K_z. It equals sqrt(1-(x-x_Z)^2) on [x_Z,x_P].

The signed roofs are nonnegative because the common horizontal width exceeds two; the axis quadrants already cover the baseline. Apply the signed-roof identity SR1, whose curvature hypotheses hold by SC1. Subtracting the two **actual** niche areas gives the exact identity

$$
\boxed{|B_z|-\widetilde{\mathcal Q}(\bar h_z)
=\int_{x_Z}^{m}\min\{F_*(x),1-\bar T_z(x)\}\,dx>0.}
\tag{SC.8}
$$

Indeed the lower niche contributes its full signed area. At each x in [0,m], the actual upper niche length is (F_*(x)-(1-bar T_z(x)))_+, whereas its full signed length is F_*(x). Their difference is the displayed minimum. The two niches are disjoint, so no overlap correction is missing. Both terms of the minimum are strictly positive for x in (x_Z,m), proving the strict sign without an asymptotic argument.

The actual repair u_z=bar h_z-h_z is nonnegative, has zero axis values, and is supported only in (t_1,L). It is nonzero, because the unique bar K_z outer support point near its right top endpoint is hidden by the upper niche. All the shared anchor inequalities of AB1 hold, since H_z is an actual nested convex hull with the same axis supports; its horizontal witnesses have height 1/2.

On the support of this increment,

$$
\bar q_z=g_*'+\bar f_z-1
=(x_Z+m/2)\cos t-\tfrac12\sin t<0
$$

for small z. Thus the derivative-free expression AB.4 is simply

$$
\mathcal J_0(\bar h_z;u_z)
=\widetilde{\mathcal Q}(\bar h_z)-\int u_z
<\widetilde{\mathcal Q}(\bar h_z)<|B_z|.
\tag{SC.9}
$$

**Theorem SC3 (failure of shared-budget ordinary enclosure).** The first inequality proposed in AB.5 is false even for genuine shared-anchor repairs of fully saturated, full-turn, connected bodies of the candidate's width. This failure has no adverse velocity q>1 and no derivative-energy charge. Dropping that charge or adding AB1's constraints does not repair the geometric comparison.

The second, analytic calibration in AB.5 is a separate question; proving it would not undo (SC.9).

## 5. These examples are below the candidate, not counterexamples to it

For completeness the sign of |B_z|-M can also be determined without assuming optimality. Put a=z/2 and k=sqrt(2)-1. Then (x_Z-m)/a tends to -k.

On the changed upper support interval, write d=L-t=a X. The rescaled support difference (bar f_z-f_*)/a^2 tends uniformly to

$$
w(X)=
\begin{cases}
-kX+X^2/4,&0\leq X\leq\sqrt2,\\
-(1-X/2)^2,&\sqrt2\leq X\leq2.
\end{cases}
$$

Its first derivatives converge after the corresponding scaling on these two pieces. Both reference and perturbed contacts remain in the final phase p<0,q<0. The exact quadratic expansion at the candidate therefore gives

$$
M-\widetilde{\mathcal Q}(\bar h_z)
=\int_{t_0}^{L}\bigl[(\bar f_z'-f_*')^2-(\bar f_z-f_*)^2\bigr]dt.
$$

Its ratio to a^3 tends to

$$
\int_0^2 w'(X)^2dX=\sqrt2-4/3.
\tag{SC.10}
$$

The clipping integral in (SC.8), divided by a^3, tends to

$$
\int_{-k}^{0}\min\{X^2,(X+k)^2/2\}\,dX
=\frac{29\sqrt2-41}{3}>0.
\tag{SC.11}
$$

The two quadratic graphs meet at X=-k^2. Splitting there gives (SC.11) by polynomial integration. Its positive sign follows from 2*29^2=1682>1681=41^2. Subtracting (SC.11) from (SC.10) yields

$$
\boxed{M-|B_z|=\frac{37-26\sqrt2}{24}\,z^3+o(z^3)>0.}
\tag{SC.12}
$$

Here 37^2=1369>1352=2*26^2 proves positivity. Consequently |B_z| tends to M from below while (SC.9) fails. No fixed area threshold below M rescues that enclosure.

The circle formulas also give a direct independent evaluation: subtract the upper loss

$$
\int_{x_Z}^{x_P}
\left[\tfrac12+\sqrt{\tfrac14-(x-m)^2}
-\sqrt{1-(x-x_Z)^2}\right]_+dx
$$

from M and add the lower-tail area recovered in (SC.5). This agrees with (SC.8)--(SC.12); the separate diagnostic script checks this agreement numerically, not as a premise of the proof.

## 6. Consequence for the PR #9 transfer

PR #9 separates a geometric majorant from its coercive calibration. SC3 is precisely a failure of the first part, even after removing the known energy objection and retaining the new anchor information. The route cannot be completed by more work on the sharp maximum of this same expression.

A successful enclosure must retain the actual auxiliary tail/body intersection area or an equivalent clipping term. The existence of a zero-deficit theorem for Gerver, or a calibrated Romik profile functional, does not make that term nonpositive. This note stops this proposed shortcut; it does not replace it by an unproved global theorem.

No CI or Lean/Lake compilation was used. The proof is written and self-reviewed, with explicit earlier dependencies; it is not an independent audit of the entire branch.
