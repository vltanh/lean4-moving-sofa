# Adaptive-functional supplement: the sharp wide-profile maximum without curvature or contact assumptions

This supplement closes the **function-space maximization problem** for the adaptive functional on all normalized real H^1 profiles of horizontal width at least one. Neither curvature domination, convexity of a profile, nor contact order is assumed. The proof fixes width first, uses strict concavity on that fiber, and then classifies a two-dimensional Hamiltonian system to optimize over width.

**This is not an unrestricted sofa-area theorem.** Comparing the ordinary area of a feasible body with this functional remains a separate geometric obligation. Its value is not defined to be ordinary area outside the classes where that equality has actually been proved.

Labels AF1–AF3 are independent of the numbered notes and of the WG width-gate labels. The candidate value and explicit matched profile are the ones calculated in Note 14; their identification with Romik's construction is attributed there. No novelty or independent verification claim is made.

## A.1 Definition on unrestricted profiles

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

This is the half-functional C+I minus the two sign-selected contact losses from Note 16. The full adaptive functional is

\[
\widetilde{\mathcal Q}(h)
=F(f,g)+F(f_\rho,g_\rho)-h(0)-h(\pi).
\tag{A.2}
\]

The exact integral definition is used throughout. For a convex support function it is the same quantity as in the earlier notes; it is not automatically the body's area.

Adding b cos(theta) changes neither functional: p and q are unchanged; the half support-area cross term is the endpoint term [b h sin(theta)] from 0 to pi; and the signed corner-area cross term is b/2 times the difference of the corner heights at the two ends, both zero. We may therefore center the horizontal support values as

\[
h(0)=h(\pi)=a,\qquad 2a=h(0)+h(\pi).
\]

For a genuine hull in a unit-height strip, any body inside it has area at most its horizontal width 2a. Thus a competitive body of area greater than one has a>1/2. The calibration below covers a>=1/2.

## A.2 Strict concavity at fixed width

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

The Dirichlet inequality on an interval of length L=pi/2 is integral |y'|^2 >= 4 integral |y|^2. For compactly supported smooth real functions it follows by expanding the nonnegative integral of (y'-2 cot(2t)y)^2 and integrating by parts. Density extends the inequality to H^1_0, and real and imaginary parts give the complex version. Therefore

\[
B_0(v,w)\geq\frac7{32}\int_0^L|y'|^2,
\tag{A.5}
\]

which controls the H^1 norm of (v,w). The negative contact losses are concave because min(x,0)^2 and max(x,0)^2 are convex and their arguments are affine in f,g.

**Lemma AF1 (unique fixed-width maximizer).** For every real a, F attains a unique maximum on X_a. No sign, curvature, convex-body, or feasibility conditions are required. Its maximizer satisfies

\[
f(t)=g(L-t).
\tag{A.6}
\]

**Proof.** Equations (A.4)-(A.5) prove uniform strict concavity on X_a. Subtract an affine boundary lift. The unpenalized part has a coercive negative quadratic bound plus a bounded linear term; subtracting the nonnegative contact losses preserves that bound.

A maximizing sequence is bounded in H^1. Pass to a weak H^1 and strong L^2 subsequence. Cross terms involving one derivative pass to the limit by strong-weak pairing. Negative squared-derivative terms and negative convex contact losses are weakly upper semicontinuous. Trace conditions pass to the limit. A maximum exists and strict concavity makes it unique.

The transformation (f(t),g(t)) -> (g(L-t),f(L-t)) preserves X_a and F. It sends p to -q(L-t) and q to -p(L-t), interchanging the two losses. The signed corner integral is invariant because spatial reflection and parameter reversal each reverse orientation. Uniqueness gives (A.6). QED.

For a fixed a, both halves of (A.2) belong to X_a and may be optimized independently. Consequently

\[
\widetilde{\mathcal Q}(h)\leq\Phi(a):=2\max_{X_a}F-2a.
\tag{A.7}
\]

Equality requires both halves to be the unique maximizer. This is symmetry of an auxiliary function-space optimizer, not a claim that averaging feasible bodies preserves feasibility.

## A.3 The Euler system has globally Lipschitz momenta

The contact-loss functions are continuously differentiable. The weak Euler equations at the fixed-width maximizer are

\[
f''+f+q+(p_-)' -q_+=0,
\qquad g''+g-p+p_-+(q_+)'=0.
\tag{A.8}
\]

Set

\[
P=p+p_-,\qquad Q=q+q_+.
\]

Initially P,Q are L^2. Their distributional derivatives from (A.8) are in L^2, so they are H^1 and continuous. Their inverse relations to p,q are Lipschitz. Substitution gives

\[
\boxed{P'=-1-b(Q),\qquad Q'=-1+c(P),}
\tag{A.9}
\]

where

\[
b(Q)=\begin{cases}Q/2&Q\geq0,\\2Q&Q\leq0,\end{cases}
\qquad
c(P)=\begin{cases}2P&P\geq0,\\P/2&P\leq0.\end{cases}
\]

The right side is globally Lipschitz. Thus P,Q are C^1, p,q are Lipschitz, and f,g are C^1 with Lipschitz first derivatives. This regularity concerns the auxiliary optimizer, not a general feasible hull.

Reflection (A.6) gives

\[
Q(t)=-P(L-t).
\tag{A.10}
\]

The boundary fluxes of F are

\[
\Pi_f=-f'-\tfrac12(g-1)-p_-,\qquad
\Pi_g=-g'+\tfrac12(f-1)-q_+.
\]

In particular Pi_f(0)=-P(0), Pi_g(L)=-Q(L). At an interior maximum where the common horizontal endpoint a is also free, varying a in both halves gives

\[
0=2(P(0)-Q(L))-2=4P(0)-2.
\]

Hence

\[
\boxed{P(0)=1/2,\qquad Q(L)=-1/2.}
\tag{A.11}
\]

This is an actual endpoint variation in the function space. No switching angle was frozen or differentiated as an independent coordinate.

## A.4 Hamiltonian form and the period bound

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

Then (A.9) is P'=-H_Q, Q'=H_P, and H is constant along each solution. It is C^1, strictly convex, and coercive, with unique minimum at (1/2,-1/2). It is invariant under (P,Q)->(-Q,-P).

Put X=P-1/2, Y=Q+1/2. Each secant slope of c and b is between 1/2 and 2, so along a nonstationary orbit its polar angle satisfies

\[
\frac12\leq\frac{XQ'-YP'}{X^2+Y^2}\leq2.
\tag{A.13}
\]

A nonminimal level of H is a compact strictly convex closed curve, traversed with strictly positive angular speed. Its full period is at least pi. Therefore an orbit on an interval of length L=pi/2 cannot make an additional full revolution between a prescribed pair of points on that level.

## A.5 All stationary widths are classified

Let v=Q(0). By (A.10)-(A.11), a stationary full profile starts at (1/2,v) and ends at (-v,-1/2). These two points lie on the same H level. For v not equal to -1/2, they differ by a positive quarter revolution about (1/2,-1/2). The first transit is the only possible one in time L, by the period bound.

**Case 1: v<=0.** If v=-1/2 the orbit is stationary. Otherwise the entire first quarter transit stays in P>=0,Q<=0. There the equations are P'=-1-2Q, Q'=-1+2P, a rotation of angular speed two about the equilibrium. Its transit time is pi/4, not L. Additional full periods are too long.

The stationary orbit has p=1/2,q=-1/2. Solving f'=g-1/2, g'=1/2-f with the four boundary conditions gives a=1/2 and

\[
f(t)=\tfrac12+\tfrac12\sin t,\qquad
 g(t)=\tfrac12+\tfrac12\cos t.
\tag{A.14}
\]

This is the radius-one-half disk profile.

**Case 2: v>0 and the orbit reaches Q=0 first.** Put r=1+v/2. In the initial quadrant P>0,Q>0,

\[
P(t)=\tfrac12-r\sin t,\qquad Q(t)=-2+2r\cos t.
\tag{A.15}
\]

If 1<r<=sqrt(5)/2, put d=sqrt(r^2-1) in (0,1/2]. The first segment takes time arctan(d), ending at (1/2-d,0). The intermediate P>=0,Q<=0 arc has angular speed two and takes time pi/4-arctan(2d). By reflection the final segment has the same duration as the first. The total is

\[
T(d)=2\arctan d+\pi/4-\arctan(2d).
\]

Its derivative is 6d^2/((1+d^2)(1+4d^2)), so

\[
T(d)\leq T(1/2)=2\arctan(1/2)<\pi/2.
\tag{A.16}
\]

This case cannot supply the required length L.

**Case 3: the orbit reaches P=0 first.** Now r>=sqrt(5)/2 and

\[
\beta=\arcsin(1/(2r)),\qquad0<\beta\leq\arctan(1/2).
\]

The initial segment ends at (0,z), where z=cot(beta)-2>=0. In P<=0,Q>=0 the motion is a rotation of speed 1/2 about (2,-2). It proceeds to (-z,0), taking time

\[
\pi-4\arctan(2\tan\beta).
\]

The last segment is the reflected first segment. Thus

\[
T(\beta)=2\beta+\pi-4\arctan(2\tan\beta).
\tag{A.17}
\]

This formula agrees with (A.16) at the boundary r=sqrt(5)/2. Its derivative is

\[
T'(\beta)=-\frac6{1+4\tan^2\beta}<0.
\]

Its endpoint values range from the limit pi as beta tends to zero down to 2 arctan(1/2). Exactly one beta gives T=L. For that beta,

\[
2\arctan(2Y)=\pi/4+\arctan Y,\qquad Y=\tan\beta\in(0,1/2).
\]

The double-angle tangent identity, with its positive denominators on this interval at the required solution, gives

\[
\boxed{4Y^3+3Y-1=0.}
\tag{A.18}
\]

The cubic is strictly increasing, so the solution is unique.

**Lemma AF2 (classification of full stationary profiles).** An interior stationary width for the optimized full functional is either the disk width a=1/2 or the centered candidate width

\[
a_*=\frac1{3\sin\beta},
\]

with beta determined by (A.18). In the second case the whole profile is the centered candidate profile of Note 14.

**Proof.** The cases above exhaust v. In Case 3 the candidate's matched momenta have exactly the same initial values: P(0)=1/2 and Q(0)=1/sin(beta)-2. Uniqueness for the globally Lipschitz system (A.9) identifies P,Q, hence p,q, on the whole interval. Two pairs f,g with the same p,q differ by a solution of v'=w, w'=-v. Since g(0) is fixed their difference is (b cos(t),-b sin(t)), the horizontal translation mode. Requiring f(0)=g(L)=a forces b=0 between two centered pairs. The centered candidate has width a_* by the formulas in Note 14, so it is the only second profile. Case 1 gave the disk, and Case 2 is impossible. QED.

The candidate's piecewise curvature jumps are allowed here. The momenta, not second derivatives of support functions, are the continuous variables in the classification.

## A.6 The width boundary and large-width escape are controlled

A global maximum over a>=1/2 exists; this is not assumed just because stationary points have been classified.

At a=1/2 the disk pair (A.14) satisfies the fixed-width Euler equations. By Lemma AF1 it is the unique fixed-width maximizer. Direct substitution gives

\[
\Phi(1/2)=\pi/2-1/2<M.
\tag{A.19}
\]

For the strict comparison it suffices to use pi<4 and the already proved M>8/5 from Note 10.

For large a put phi=pi/8, tau=tan(phi)>0, R=a/cos(phi), B=1-a tau. The explicit pair

\[
f_a(t)=R\cos(t/2+\phi)+B\sin t,
\qquad
 g_a(t)=R\sin(t/2+\phi)+B\cos t
\tag{A.20}
\]

belongs to X_a. If a>=2/(3tau), it has

\[
p=1-\tfrac32R\sin(t/2+\phi)\leq0,
\qquad q=\tfrac32R\cos(t/2+\phi)-1\geq0.
\]

It satisfies (A.8), equivalently the P<=0,Q>=0 part of (A.9). Lemma AF1 therefore identifies it as the unique fixed-width maximizer for every such a.

This explicit pair depends affinely on a. Differentiating its value and integrating by parts, the interior Euler terms vanish and the boundary fluxes give

\[
\Phi'(a)=4P(0)-2=6-12\tau a.
\]

Consequently on this whole tail

\[
\Phi(a)=-6\tau a^2+6a+C\longrightarrow-\infty.
\tag{A.21}
\]

This calculation uses the explicit tail optimizer, not an unproved envelope differentiability assertion.

On a bounded interval of widths, the coercive estimate in the proof of AF1 is uniform after choosing boundary lifts bounded in H^1. A sequence maximizing the full functional therefore has a subsequence with convergent a, weak H^1 halves and strong L^2 halves. The same upper-semicontinuity argument as before attains the maximum. Equation (A.21) rules out escape to infinite width. Thus a global maximum on a>=1/2 is attained.

## A.7 The completed wide-profile theorem

**Theorem AF3 (unrestricted adaptive calibration for wide profiles).** Let h be any real 2pi-periodic H^1 function satisfying

\[
h(\pi/2)=1,\qquad h(3\pi/2)=0,
\qquad h(0)+h(\pi)\geq1.
\]

Then

\[
\boxed{\widetilde{\mathcal Q}(h)\leq
 M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.}
\tag{A.22}
\]

Equality holds exactly when h=h_*+b cos(theta), where h_* is the explicit candidate support profile in Note 14 and b is real.

**Proof.** Center the horizontal endpoint values using the translation invariance in Section A.1. At fixed width, Lemma AF1 and (A.7) reduce the maximum to two identical halves with the reflection symmetry (A.6). Section A.6 gives an attained maximum over a>=1/2. Its value is at least M because the explicit candidate belongs to this function domain and its adaptive value was evaluated exactly in Note 14 as cot(beta)-2+beta=M.

The width boundary has smaller value by (A.19). Hence a maximizing width is interior, so the natural boundary condition (A.11) applies. Lemma AF2 leaves only the candidate: the disk has a=1/2 and smaller value. Therefore the global maximum is M.

At equality the width must be a_*, and strict fixed-width concavity forces each half to equal the candidate half. Undoing horizontal centering gives exactly the stated translation family. Conversely those profiles attain M by translation invariance. QED.

This theorem has **no convexity, curvature cap, contact-order, monotone-contact, or feasible-motion hypothesis** on h. Its width restriction is explicit and automatic for the normalized hull of any body with area greater than one.

One nonnegative decomposition of the deficit is

\[
M-\widetilde{\mathcal Q}(h)
=\bigl(M-\Phi(a)\bigr)
+\bigl(F_a-F(f,g)\bigr)
+\bigl(F_a-F(f_\rho,g_\rho)\bigr),
\tag{A.23}
\]

where F_a=max_{X_a}F. Each term is nonnegative for a>=1/2. The last two have the strict concavity control from (A.4)-(A.5). No claim of a quantified geometric distance estimate is made for the first term here.

## A.8 What this does not prove about actual sofas

Theorem AF3 strengthens the **functional** side of the proof. It does not supply

\[
|S|\leq\widetilde{\mathcal Q}(h_{\operatorname{conv}S}).
\tag{A.24}
\]

That inequality is not part of the definition of the functional. In the established curvature/contact class it follows from the exact niche-profile and no-clipping arguments. Outside that class, signed envelope contributions and omitted exposure corrections must be checked; they cannot be removed by the present maximization theorem.

Thus one possible route is now to prove (A.24) for an attained global maximizer, or an appropriate area-dominating comparison, without deriving all of the old sufficient support conditions. Such a result has **not** been proved in this supplement. To recover unrestricted uniqueness it must apply to every maximizer or retain an equality-recovery argument.

In particular, regularity of the auxiliary fixed-width optimizer in AF1 says nothing about regularity of an arbitrary area-maximizing hull. The two optimization problems must not be silently identified.

All steps here are written pen-and-paper arguments with self-review. No CI, Lean/Lake compilation, numerical experiment, computer algebra, or manuscript build was used. The unrestricted sofa proof remains unfinished.
