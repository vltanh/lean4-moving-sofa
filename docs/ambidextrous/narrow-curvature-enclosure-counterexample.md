# Narrow-hull counterexample: curvature domination alone does not make the adaptive functional an area bound

This tests the remaining sign in Corollary SR2 rather than presuming it is favorable. The example is a **convex** compact body with two full conventional motions, unit vertical span, and curvature measure dominated by dt on every open quarter. Nevertheless its ordinary area is strictly larger than the adaptive functional evaluated on its actual hull.

It does not contradict the sharp bound M: its area is smaller than M. It shows that the clipping term in the narrow class is a real geometric error even without excessive curvature. In particular, the width qualification of Theorem CW4 cannot simply be deleted from its enclosure argument.

Labels NC1 onward are separate from the other notes. All calculations below are exact; no numerical experiment or computer algebra is used.

## N.1 The convex body and its support

Set

\[
m=8/15,\qquad k=1-m=7/15,\qquad a=(1+m)/2=23/30,
\qquad L=\pi/2.
\]

On the upper quarters define

\[
f(t)=1+(a-1)\cos t,\qquad
 g(t)=\cos t+a\sin t.
\tag{N.1}
\]

Extend h(t)=f(t), h(t+L)=g(t) to the lower half by central symmetry about (0,1/2): h(t+pi)=h(t)-sin t. This is the support function of a convex body K with top and bottom faces

\[
[-a,a-1]\times\{1\},\qquad [1-a,a]\times\{0\}.
\]

Its upper-right flank is a unit quarter-circle centered at (a-1,0), and its lower-left flank is a unit quarter-circle centered at (1-a,1). The other two open quarters represent the corner points (-a,1) and (a,0). Equivalently, its top and bottom graphs are

\[
t_K(x)=\begin{cases}1,&-a\leq x\leq a-1,\\
\sqrt{1-(x-(a-1))^2},&a-1\leq x\leq a,
\end{cases}
\]

\[
b_K(x)=\begin{cases}1-\sqrt{1-(x-(1-a))^2},&-a\leq x\leq1-a,\\
0,&1-a\leq x\leq a.
\end{cases}
\tag{N.2}
\]

These form a convex body with nonempty interior. One verification is the support construction: the four open-quarter curvature densities are 1,0,1,0 in circular order, the top and bottom normal atoms have mass m>0, and the horizontal-normal derivative jumps vanish. Thus h+h'' is a nonnegative curvature measure and the displayed supporting curves attain h. The graphs also verify the geometry directly.

The body has vertical span one, horizontal width 2a=23/15, and

\[
\boxed{|K|=m+\pi/2-1=\pi/2-7/15.}
\tag{N.3}
\]

Indeed the integral of the top graph is m+pi/4 and that of the bottom graph is 1-pi/4. The curvature cap on every open quarter is satisfied; the two permitted axis atoms are the horizontal faces.

## N.2 The complete lower motion is feasible

The lower-turn velocities are

\[
p(t)=1-\cos t-m\sin t,\qquad
q(t)=m\cos t-\sin t.
\tag{N.4}
\]

Put beta=arctan(m)=2 arctan(1/4), so sin(beta)=8/17 and cos(beta)=15/17. Their signs are:

- p<0 on (0,2beta), p>0 on (2beta,L);
- q>0 on (0,beta), q<0 on (beta,L).

The B curve is the constant point (a-1,0). The D curve is

\[
D(t)=(-a+\sin t,\ 1-\cos t).
\tag{N.5}
\]

By the signed-roof graph calculation, the only positive lower-roof pieces are D for 0<=t<=beta and the standard corner c for beta>=t>=0. The remaining reverse corner segment, 2beta<=t<=L, is below the baseline: its height is

\[
c_y(t)=\cos t\,[m\sin t+\cos t-1]\leq0.
\]

The positive pieces lie over the top-face interval [-a,a-1]. We check each lies at or below the **actual lower boundary of K**, so no point of K is removed.

For the D piece, write s=sin t<=8/17<1/2. At x=-a+s, the lower boundary in (N.2) has height 1-sqrt(2s-s^2). The D height is 1-sqrt(1-s^2), which is no larger because s<=1/2. Thus D lies below b_K.

For the corner piece let C=(1-a,1), the center of the lower-left flank circle. Its coordinates in the moving frame give

\[
|c(t)-C|^2=(k\cos t+\sin t)^2+(1-\sin t)^2.
\tag{N.6}
\]

This is at least one for every 0<=t<=L. Here is an exact sufficient estimate. With s=sin t<1,

\[
\begin{aligned}
|c-C|^2-1
&=k^2(1-s^2)+2ks\sqrt{1-s^2}-2s(1-s)\\
&\geq(1-s)\left[2ks^2+(k^2+2k-2)s+k^2\right],
\end{aligned}
\tag{N.7}
\]

using sqrt((1+s)/(1-s))>=1+s. At k=7/15, the quadratic in brackets has positive leading coefficient and discriminant

\[
(-191/225)^2-8(7/15)^3=-4679/50625<0.
\]

It is therefore positive for every real s. At s=1 equality in (N.6) is immediate.

On the standard corner segment, c_x is between -a+sin(beta) and a-1, hence in the lower-left circular flank's projection. Also c_y<=m/2<1. Equation (N.6) consequently says c_y<=1-sqrt(1-(c_x-(1-a))^2)=b_K(c_x): it is the point below the circle, not the one above it. Thus the corner piece also lies below K.

The signed-roof theorem includes the complete continuum of parameters, not just the two displayed contact curves as a guessed ansatz. Alternatively its activity checks specialize here to B_x constant and D_x strictly increasing with the sign intervals (N.4). Axis constraints add only baseline height zero. We have therefore proved W_- intersect K is empty for the **whole** lower canonical motion.

## N.3 The upper motion is feasible too

The body K is centrally symmetric about (0,1/2), so its reflection in y=1/2 is its reflection in x=0. Reflection in x=0 sends mu_t,nu_t to nu_{L-t},mu_{L-t}, respectively. Exchanging these two frame vectors does not change a forbidden quadrant or its outer inequalities. Hence the full lower canonical envelope of the horizontally reflected body is the horizontal reflection of the full lower envelope of K, with parameter reversed.

The lower feasibility just proved therefore holds for rho K as well. Reflecting back gives the upper motion of K. At the full-turn endpoints the outgoing normal is vertical up to sign, so its width is one; the incoming strip condition also holds. The support-dependent placements are continuous and give proper rotations and translations. No reflection of the physical body is inserted into either motion.

**Proposition NC1 (a genuinely feasible curvature-dominated example).** K itself, not a disconnected relaxation or a body with a different hull, is a compact convex ambidextrous sofa with both full conventional turns and the stated curvature cap.

## N.4 Exact adaptive-functional value

The two signed niche integrals are equal by the reflection/parameter symmetry just described. On the lower half, direct expansion gives

\[
I=\frac\pi8(m^2+3)-\frac m2-1,
\]

\[
\int_0^L\min(p,0)^2=(3+m^2)\beta-3m,
\qquad
\int_0^L\max(q,0)^2=\frac{1+m^2}{2}\beta-\frac m2.
\tag{N.8}
\]

For example, the p integral runs from 0 to 2beta and expands (1-cos t-m sin t)^2; the q integral runs from 0 to beta and expands (m cos t-sin t)^2. The identities sin(2beta)=2m/(1+m^2) and cos(2beta)=(1-m^2)/(1+m^2) simplify their endpoint terms to -3m and -m/2. The determinant formula in (A.1) gives the displayed I by integrating sin², cos², sin cos, sin and cos separately.

Consequently the signed lower-roof area is

\[
J=-I+\tfrac12\int p_-^2+\tfrac12\int q_+^2
=1-\frac{5m}{4}-\frac\pi8(m^2+3)+\frac{7+3m^2}{4}\arctan m.
\]

At m=8/15 this is

\[
J=\frac13-\frac{739\pi}{1800}+\frac{589}{300}\,2\arctan(1/4)>0.
\tag{N.9}
\]

Its strict sign has a rational certificate. Since arctan(1/4)>1/4-(1/4)^3/3=47/192 and pi<22/7,

\[
J>\frac13-\frac{8129}{6300}+\frac{27683}{28800}
=\frac{853}{201600}>0.
\tag{N.10}
\]

The arctangent inequality follows by integrating 1/(1+x²)>1-x² for x>0; no numerical evaluation is used.

The actual niches inside K are empty by NC1, but their **signed ambient** integrals are positive. Therefore

\[
\boxed{|K|-\widetilde{\mathcal Q}(h_K)=2J>
\frac{853}{100800}>0.}
\tag{N.11}
\]

This is precisely a positive clipping-minus-negative-roof error in (S.7). The negative part of the signed roof does not pay for all clipping in this example.

## N.5 What this rules out, and what it does not

The following proposed implication is false:

> Curvature domination on the open quarters, unit span, horizontal width at least one, and full ambidextrous feasibility imply ordinary-area enclosure by the adaptive functional.

NC1 and (N.11) disprove it even for a convex body. Thus AF3 plus curvature domination cannot be combined by simply deleting the contact or clipping analysis. The wide theorem CW4 is unaffected because this example has width 23/15<2.

The example has area pi/2-7/15<M, so it is **not** a counterexample to Romik's optimality. Nor does it disprove an enclosure or a different sharp comparison specifically for global maximizers. It shows that a proof for that remaining class must use additional information, not a universally false geometric identity.

The earlier high-curvature AF4 example is a different obstruction. This one has no excess open-quarter curvature; its error is solely the actual clipping and signed-roof balance. Both failures are retained.

All work is pen-and-paper with the explicitly cited earlier roof identity. No CI, Lean/Lake compilation, numerical experiment, computer algebra, or manuscript build was used. The calculations and the earlier dependencies remain subject to independent review.
