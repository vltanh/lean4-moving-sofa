# 16. Moving contact switches: a sharp adaptive functional on a convex domain

Fixing the candidate's switching angles is not harmless. This note replaces the fixed switches by positive/negative parts, proves a global maximization theorem for the resulting functional on an explicit convex domain, and gives a concrete algebraic counterexample to the fixed-switch comparison.

The geometric interpretation as actual niche area is established for a restricted class in the next notes. No unrestricted sofa theorem is asserted here.

## 16.1 A convex monotone-velocity domain

Let C be the following class of normalized periodic support-variable functions h. Both for h and for h^rho, require f(t)=h(t), g(t)=h(t+L) to belong to H^2(0,L), and let

\[
p=f'-g+1,\qquad q=g'+f-1.
\]

Require:

\[
p\text{ and }q\text{ are strictly decreasing on }[0,L],
\]

\[
p(0)>0>p(L),\qquad q(0)>0>q(L),\qquad p(t)\leq q(t)\text{ for every }t.
\tag{16.1}
\]

Keep h(L)=1 and h(-L)=0. Strict decrease means the pairwise inequality p(t_1)>p(t_2) for t_1<t_2, not a uniform pointwise derivative bound. Every condition is affine or a linear inequality on h, so C is convex. Convexity of a body is a separate condition; the algebraic theorem is valid on this larger function domain.

For each half there are unique zeros a(h),b(h) in (0,L), and p<=q gives a(h)<=b(h). The zeros for h and h^rho need not agree. Thus this domain permits nonsymmetric independent support perturbations.

## 16.2 Adaptive contact loss

Define

\[
\widetilde F(h)=C(h)+I(h)
-\frac12\int_0^L\min(p_h,0)^2
-\frac12\int_0^L\max(q_h,0)^2,
\]

\[
\widetilde{\mathcal Q}(h)
=\widetilde F(h)+\widetilde F(h^\rho)-h(0)-h(\pi).
\tag{16.2}
\]

On C the two integration domains are exactly [a(h),L] and [0,b(h)], respectively. The switching points are allowed to move with h.

**Theorem 39 (adaptive concavity).** Let h_0,h_1 be in C, let delta=h_1-h_0, and let h_lambda=(1-lambda)h_0+lambda h_1. Then

\[
\frac{d^2}{d\lambda^2}\widetilde{\mathcal Q}(h_\lambda)
=-2\left[B_{a(h_\lambda),b(h_\lambda)}(\delta)
+B_{a(h_\lambda^\rho),b(h_\lambda^\rho)}(\delta^\rho)\right]\leq0.
\tag{16.3}
\]

In particular the functional is concave on C, with strictness modulo horizontal translations.

**Proof.** The derivative of min(x,0)^2/2 is min(x,0), and its second derivative away from zero is the indicator of x<0. The corresponding statements hold for max(x,0)^2/2. Along a segment in C, each p and q has just one zero, a set of t-measure zero. The derivatives can therefore be taken under the integrals by dominated convergence; the perturbations are bounded on the compact interval because f,g are H^2. No switch-endpoint term occurs because the squared function is zero at a switch.

The resulting second derivative is exactly the fixed-contact homogeneous quadratic with the current switching intervals. Theorem 34 applies because the two zeros are ordered and interior. This gives (16.3). Its kernel is the horizontal-translation support difference on each half; the two constants must agree at theta=0. QED.

## 16.3 The candidate belongs to the domain

For h_* from Note 14 its velocity components are

\[
(p_*,q_*)=
\begin{cases}
(\tfrac12-2A\sin t,\ 2A\cos t-1),&0\leq t\leq\beta,\\
(1-\tfrac32R\sin(t/2+\pi/8),\
\tfrac32R\cos(t/2+\pi/8)-1),&\beta\leq t\leq b,\\
(1-2A\sin t,\ 2A\cos t-\tfrac12),&b\leq t\leq L.
\end{cases}
\tag{16.4}
\]

Both functions strictly decrease, as is seen by differentiation on each phase and continuity at the joins. Their endpoint values have the signs in (16.1). On the early and late phases,

\[
q_*-p_*=2A(\sin t+\cos t)-3/2>0,
\]

because A>3/4 and sin(t)+cos(t)>=1. On the middle phase this difference is \(\frac32R(\sin\phi+\cos\phi)-2\), with phi=t/2+pi/8; its minimum is at the two symmetric endpoints, where it is already positive by the adjoining formula. Reflection leaves h_* unchanged. Thus h_* is in C, with switches beta and b=L-beta.

## 16.4 Exact global value and equality in this function domain

**Theorem 40 (sharp adaptive maximum).** For every h in C,

\[
\widetilde{\mathcal Q}(h)\leq M,
\]

with equality exactly for h=h_*+a cos(theta). More precisely, with delta=h-h_* and h_lambda=h_*+lambda delta,

\[
\begin{aligned}
M-\widetilde{\mathcal Q}(h)=2\int_0^1(1-\lambda)\bigl[
&B_{a(h_\lambda),b(h_\lambda)}(\delta)\\
+&B_{a(h_\lambda^\rho),b(h_\lambda^\rho)}(\delta^\rho)
\bigr]d\lambda.
\end{aligned}
\tag{16.5}
\]

**Proof.** At h_* the active intervals are exactly beta and b, so the adaptive functional has the same value M and first derivative zero as the fixed-contact functional in Theorem 37. Integrate (16.3) twice along the segment, which remains in C by convexity. This proves (16.5). If delta is not a common horizontal translation, the sum of the two B terms is strictly positive at every lambda by Theorem 34, and its weighted integral is positive. Translation gives equality by direct substitution. QED.

This is a genuine global maximization theorem on C, not just a stationary-point calculation or a symmetric perturbation test. Whether the common hull of every optimizing sofa belongs to C has not been proved.

## 16.5 An explicit negative result for fixed switches

For epsilon>0 consider

\[
h_\varepsilon(\theta)=h_*(\theta)-\varepsilon|\cos\theta|.
\tag{16.6}
\]

For all sufficiently small epsilon this lies in C. On the upper quarters,

\[
p_\varepsilon=p_*+2\varepsilon\sin t,
\qquad q_\varepsilon=q_*-2\varepsilon\cos t.
\tag{16.7}
\]

The strict signs, decrease, and positive gap q_*-p_* persist: on the early/late phases the relevant derivative coefficient changes from 2A to 2A-2epsilon; on the compact middle phase the negative derivatives have a positive margin. The endpoint inequalities and the gap persist for sufficiently small epsilon as well.

At beta, p_epsilon=2epsilon sin(beta)>0, so its zero a_epsilon is **later** than beta. At b, q_epsilon=-2epsilon cos(b)<0, so its zero b_epsilon is **earlier** than b. The two new switches remain ordered. Since h_epsilon is reflection invariant,

\[
\boxed{
\widetilde{\mathcal Q}(h_\varepsilon)
-\mathcal Q_{\beta,b}(h_\varepsilon)
=\int_\beta^{a_\varepsilon}p_\varepsilon^2
+\int_{b_\varepsilon}^{b}q_\varepsilon^2>0.
}
\tag{16.8}
\]

The fixed functional counts squared contact loss on intervals where the actual sign-selected contact is absent. It therefore lies strictly **below** the adaptive one. This is not a loss of optimality of the candidate: Theorem 40 still bounds the adaptive value strictly below M for epsilon>0.

For small epsilon, h_epsilon is also a convex support function. The curvature densities on the open quarter intervals are unchanged by subtracting epsilon|cos(theta)|; the only change is to reduce each horizontal exposed-face length at the vertical normals by 2epsilon. Those lengths are initially 4A/3, so they remain positive for epsilon<2A/3. The geometric construction in the later restricted theorem shows that these functions give actual feasible connected bodies. Thus the moving-switch issue is not merely a formal perturbation of unrealizable variables.

## 16.6 Remaining geometric conditions

The adaptive theorem removes one obstruction, not all of them. To interpret its value as surviving area one still needs an appropriate niche-boundary description, control of clipping by the opposite half of the hull, and coverage of any shape/angle restrictions. The next note proves the boundary description under explicit curvature and monotonicity hypotheses.
