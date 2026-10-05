# Adaptive-functional supplement: fixed-width concavity and the global calibration

This supplement reexamines the sharp functional itself, rather than adding geometric hypotheses to an optimizer. The first step below proves strict concavity after fixing the horizontal support values, **without** curvature domination or a contact-order assumption. It also derives a globally Lipschitz, piecewise linear Hamiltonian system for the unique fixed-width optimizer.

The comparison of this functional with an actual sofa's area is a separate issue. In particular, a functional maximum is not an unrestricted moving-sofa theorem. Labels AF1 onward are independent of the concurrently developed numbered notes and of the WG width-gate labels.

## A.1 Definition on unrestricted support profiles

Set L=pi/2. Let h be a real, 2pi-periodic H^1 function with

\[
h(L)=1,\qquad h(3L)=0.
\]

It need not be a convex support function. Define h^rho(t)=h(-t)+sin(t). On an upper half write f(t)=h(t), g(t)=h(t+L), for 0<=t<=L, and put

\[
p=f'-g+1,\qquad q=g'+f-1,
\quad p_-=\min(p,0),\quad q_+=\max(q,0).
\]

For a pair f,g define

\[
\begin{aligned}
F(f,g)=\frac12\int_0^L\bigl[&f^2+g^2-f'^2-g'^2
 +(f-1)^2+(g-1)^2\\
 &+(f-1)g'-(g-1)f'
 -p_-^2-q_+^2\bigr]dt.
\end{aligned}
\tag{A.1}
\]

This is exactly the half-functional C+I minus the two sign-selected contact losses from Note 16. The full adaptive functional is

\[
\mathcal A(h)=F(f,g)+F(f_\rho,g_\rho)-h(0)-h(\pi).
\tag{A.2}
\]

The letter A here denotes this **functional**, not the ordinary area of a body. For a convex support function it is the same quantity previously denoted tilde Q. The exact integral definition (A.1)-(A.2) is used throughout this supplement.

Adding a horizontal translation mode b cos(theta) changes neither functional: p and q are unchanged; the half support-area cross term is an endpoint term [b h sin(theta)] from 0 to pi; and the signed corner-area cross term is b/2 times the difference of the corner heights at the two ends, both zero. Thus we may center the horizontal supports so that

\[
h(0)=h(\pi)=a,\qquad 2a=h(0)+h(\pi).
\]

For a genuine hull in a unit-height strip, any body inside it has area at most its horizontal width 2a. Therefore profiles with 2a<=1 cannot belong to a competitive body of area greater than one. The eventual calibration will concern a>=1/2.

## A.2 Strict concavity on a fixed-width affine space

Let

\[
X_a=\{(f,g)\in H^1(0,L)^2:
 f(0)=g(L)=a,\ f(L)=g(0)=1\}.
\tag{A.3}
\]

For the difference of two members write z=v+iw. Both components vanish at both endpoints. The negative homogeneous quadratic part of the unpenalized C+I functional is

\[
B_0(v,w)=\frac12\int_0^L
\left[|z'|^2-2|z|^2-\operatorname{Im}(\overline z z')\right]dt.
\]

With y(t)=exp(-it/2)z(t), completing the square gives

\[
\boxed{B_0(v,w)=\frac12\int_0^L
\left[|y'|^2-\frac94|y|^2\right]dt.}
\tag{A.4}
\]

The Dirichlet inequality on an interval of length L=pi/2 is
\(\int|y'|^2\geq4\int|y|^2\). For completeness, on compactly supported smooth real functions it follows by expanding the nonnegative integral of (y'-2 cot(2t)y)^2 and integrating by parts; density extends the inequality to H^1_0, and applying it to real and imaginary parts gives the complex version. Consequently

\[
B_0(v,w)\geq\frac7{32}\int_0^L|y'|^2,
\tag{A.5}
\]

which controls the H^1 norm of (v,w). The negative contact losses in (A.1) are concave because x -> min(x,0)^2 and x -> max(x,0)^2 are convex and their arguments depend affinely on f,g.

**Lemma AF1 (unique fixed-width maximizer).** For every real a, F attains a unique maximum on X_a. No sign, curvature, convex-body, or feasibility conditions are required. Its maximizer obeys

\[
f(t)=g(L-t).
\tag{A.6}
\]

**Proof.** Equations (A.4)-(A.5) prove strict, indeed uniform, concavity on X_a. After subtracting an affine boundary lift, they also give a coercive negative quadratic bound; the remaining linear terms are bounded by the H^1 norm. The subtracted contact losses are nonnegative before subtraction and cannot spoil this upper coercive bound.

A maximizing sequence is therefore bounded in H^1. Pass to a weak H^1 subsequence and a strong L^2 subsequence. The area and cross terms without squared derivatives pass to the limit; the negative squared-derivative and negative convex contact-loss integrals are weakly upper semicontinuous. Endpoint traces are preserved, so a maximizer exists. Strict concavity makes it unique.

The map (f(t),g(t)) -> (g(L-t),f(L-t)) preserves X_a and F. It sends p to -q(L-t) and q to -p(L-t), interchanging the two squared losses. The signed corner integral is invariant because spatial reflection and parameter reversal each reverse its orientation. Uniqueness therefore implies (A.6). QED.

For a fixed a, the two halves in (A.2) lie in the same affine space X_a and can be optimized independently. Thus

\[
\mathcal A(h)\leq\Phi(a):=2\max_{X_a}F-2a.
\tag{A.7}
\]

Equality requires both half-profiles to equal the unique maximizer. This is symmetry of a **function-space optimizer**, not a claim that averaging two feasible sofas preserves feasibility.

## A.3 The fixed-width Euler system

The positive/negative-part squared functions are continuously differentiable, so the first variation of F is valid on H^1. At its fixed-width maximizer the weak Euler equations are

\[
f''+f+q+(p_-)' -q_+=0,
\qquad
 g''+g-p+p_-+(q_+)'=0.
\tag{A.8}
\]

Introduce continuous momentum variables

\[
P=p+p_-,\qquad Q=q+q_+.
\]

Initially these are L^2 functions. Equation (A.8) gives their distributional derivatives in L^2, and hence P,Q are H^1 and continuous. Their inverse relations to p,q are Lipschitz. Substituting p=f'-g+1 and q=g'+f-1 gives

\[
\boxed{
P'=-1-b(Q),\qquad Q'=-1+c(P),
}
\tag{A.9}
\]

where

\[
b(Q)=\begin{cases}Q/2&Q\geq0,\\2Q&Q\leq0,\end{cases}
\qquad
c(P)=\begin{cases}2P&P\geq0,\\P/2&P\leq0.\end{cases}
\]

The right-hand side is globally Lipschitz. Thus the momenta are C^1, the velocities p,q are Lipschitz, and f,g are C^1 with Lipschitz first derivatives. No regularity of a physical optimizer has been assumed to obtain this regularity of the auxiliary variational optimizer.

The reflection identity (A.6) becomes

\[
Q(t)=-P(L-t).
\tag{A.10}
\]

The boundary fluxes of F are

\[
\Pi_f=-f'-\tfrac12(g-1)-p_-,\qquad
\Pi_g=-g'+\tfrac12(f-1)-q_+.
\]

At 0 and L the anchored values imply Pi_f(0)=-P(0), Pi_g(L)=-Q(L). Therefore, at an interior stationary point of the full fixed-width value when a is also free,

\[
0=2\bigl(P(0)-Q(L)\bigr)-2=4P(0)-2,
\]

or

\[
\boxed{P(0)=1/2,\qquad Q(L)=-1/2.}
\tag{A.11}
\]

This boundary calculation follows by varying the common endpoint value a in both halves; it does not differentiate a contact-switch location or freeze one. At a global maximum with a>1/2 the variation is admissible in the function space in both directions.

## A.4 Hamiltonian form

Define

\[
H(P,Q)=U(P)-P+V(Q)+Q,
\]

\[
U(P)=\begin{cases}P^2&P\geq0,\\P^2/4&P\leq0,\end{cases}
\qquad
V(Q)=\begin{cases}Q^2/4&Q\geq0,\\Q^2&Q\leq0.\end{cases}
\tag{A.12}
\]

Then (A.9) is P'=-H_Q, Q'=H_P. The Hamiltonian is C^1, strictly convex and coercive. Its only equilibrium is (1/2,-1/2), and it is invariant under (P,Q)->(-Q,-P).

About this equilibrium, put X=P-1/2 and Y=Q+1/2. Each secant slope of c and b lies between 1/2 and 2, so along a nonstationary solution its polar angle satisfies

\[
\frac12\leq\frac{XQ'-YP'}{X^2+Y^2}\leq2.
\tag{A.13}
\]

A nonminimal Hamiltonian level is a compact strictly convex closed curve. The solution traverses it with positive angular speed. In particular a full period is at least pi. This observation will rule out additional complete revolutions when imposing the interval length L=pi/2.

At this commit the fixed-width variational problem and the critical-point system are established. The global-in-width classification and exact maximum will be added after its boundary and orbit cases are checked. The geometric comparison with sofa area remains a separate, unproved unrestricted assertion.

No CI, Lean/Lake compilation, numerical experiment, or computer algebra was used.
