# A quantitative width certificate for the auxiliary functional

This develops the previously unquantified width term in (SD.8). It gives an explicit family of exact fixed-width optimizers, a scalar coercivity estimate, and a rational error budget for the narrow-width ordinary-area problem. It does not presume that ordinary sofa area is enclosed by the auxiliary functional.

Dependencies: the definition of F and its fixed-width strict concavity in [AF1](adaptive-functional-global-calibration.md), and the already calibrated value M_A and candidate width a_*. The new formulas, sign checks, and bounds are proved below. No numerical optimization or computer algebra is used.

## 1. An explicit one-parameter family of width optimizers

Let L=pi/2. For 0<beta<pi/4 set

\[
s=\sin\beta,\quad c=\cos\beta,\quad
T=\beta/2+\pi/8,\quad C=\cot T,
\]

\[
a=\frac{2cC+s}{3},\qquad
k=\frac{1-c}{2}+Cs,\qquad
R=\frac{2}{3\sin T},\qquad B=\frac{1+k}{3},\qquad b=L-\beta.
\tag{SW.1}
\]

Define the upper pair by

\[
(f,g)=
\begin{cases}
(a\cos t+k\sin t,\ \tfrac a2\sin t+\tfrac12\cos t+\tfrac12),&0\leq t\leq\beta,\\
(R\cos(t/2+\pi/8)+B\sin t,\ R\sin(t/2+\pi/8)+B\cos t),&\beta\leq t\leq b,\\
(\tfrac a2\cos t+\tfrac12\sin t+\tfrac12,\ a\sin t+k\cos t),&b\leq t\leq L.
\end{cases}
\tag{SW.2}
\]

**Lemma SW1 (exact fixed-width optimizer).** The pair in (SW.2) is the unique maximizer of F on X_a. The map beta to a is strictly decreasing, with limiting range

\[
\frac1{\sqrt2}<a<\frac23\cot(\pi/8).
\tag{SW.3}
\]

**Proof.** The endpoint conditions are f(0)=g(L)=a and f(L)=g(0)=1. The formulas have f(t)=g(L-t). To check matching at beta, use

\[
\tfrac32a=\tfrac12s+Cc,\qquad
k-\tfrac12=-\tfrac12c+Cs,\qquad
R\sin T=\tfrac23,\quad R\cos T=\tfrac23C.
\]

Substitution in (SW.2) makes both values and both first derivatives agree. Reflection gives the matching at b.

On the early phase put d=beta-t. Direct substitution in p=f'-g+1 and q=g'+f-1 yields

\[
p(t)=\tfrac12(1-\cos d)+C\sin d>0\quad(t<\beta),
\]

\[
q(t)=-1+\tfrac12\sin d+C\cos d>0.
\]

For the second sign, the function one half sin(d)+C cos(d) is positive and concave on [0,beta]; its endpoint values are C>1 and 3a/2>1. The latter follows from a>=1/sqrt(2)>2/3. On the middle phase,

\[
p=1-\tfrac32R\sin(t/2+\pi/8)\leq0,
\quad q=\tfrac32R\cos(t/2+\pi/8)-1\geq0.
\]

The late signs follow by p(L-t)=-q(t). Hence the active contact intervals are exactly [beta,L] for p_- and [0,b] for q_+.

On the three open phases the pair solves, respectively,

\[
f''+f=0,\quad g''+g=\tfrac12;
\]

\[
2f''-g'+f=0,\quad2g''+f'+g=0;
\]

\[
f''+f=\tfrac12,\quad g''+g=0.
\]

These are the Euler equations of F with those active intervals. The derivative fluxes match because p(beta)=0 and q(b)=0; ordinary first derivatives already match. Integration by parts therefore gives DF[v,w]=0 for every zero-endpoint H^1 variation. AF1's strict concavity identifies this stationary pair as the unique global maximizer on X_a, not just a critical point of a chosen contact ansatz.

Finally C'=-(1+C^2)/2 gives

\[
a'(\beta)=-\frac C3(2s+cC)<0.
\tag{SW.4}
\]

The endpoint values at beta=pi/4 and beta=0 give (SW.3). QED.

Convexity or feasibility of the assembled profile has not been used. The point of AF1 is that stationarity of this verified pair identifies the entire fixed-width variational maximum, even among profiles with different contact sets.

## 2. Curvature of the scalar value function

Let Phi(a)=2 max_Xa F-2a. Along (SW.2), the endpoint flux formula gives

\[
\Phi'(a)=4k-2.
\tag{SW.5}
\]

Indeed the free f(0) and g(L) each contribute k to dF/da; the other endpoint values stay fixed. The profile is differentiable in H^1 with respect to its parameter on compact subintervals of (0,pi/4): all pieces vary smoothly and their values and first derivatives match at moving joins. Thus this is a chain-rule calculation, not an assumed differentiability of an abstract maximum.

Since

\[
k'(\beta)=C\left(c-\frac12Cs\right),
\]

one obtains

\[
\Phi''(a)=-12\frac{c-\tfrac12Cs}{2s+cC}.
\tag{SW.6}
\]

Here beta<=T<=pi/4 gives Cs<=c; also s<=c and C<=cot(pi/8)=1+sqrt(2)<5/2. Therefore

\[
\boxed{-\Phi''(a)\geq\frac43}
\tag{SW.7}
\]

on (SW.3). In detail the numerator is at least c/2 and the denominator is at most (2+C)c<(9/2)c.

At the candidate beta=beta_* the free-width condition is k=1/2. Substituting in (SW.1) gives a_*=1/(3 sin(beta_*)), and the calibrated value is Phi(a_*)=M_A. Both lie inside the interval above. Twice integrating (SW.7) from a_* proves

\[
\boxed{M_A-\Phi(a)\geq\frac23(a-a_*)^2.}
\tag{SW.8}
\]

Combined with SD1–SD3, for any centered normalized profile with half-width in (SW.3),

\[
M_A-\widetilde{\mathcal Q}(h)
\geq\frac23(a-a_*)^2+\frac7{4\pi}\|h-H_a\|_\infty^2.
\tag{SW.9}
\]

This is a quantitative width-and-shape certificate on a specified interval, with no ordinary-area assumption.

## 3. A rational gap for half-widths between 4/5 and one

Put beta_0=pi/8 and s_0=sin(pi/8). The half-angle identity gives C_0 c_0=1+s_0, so

\[
a_0=a(\beta_0)=\frac23+s_0>1,
\]

\[
4k_0-2=\frac{2(3s_0-1)(s_0+1)}{c_0}.
\tag{SW.10}
\]

The elementary bound s_0>3/8 follows by squaring: (2-sqrt(2))/4>9/64 is equivalent to sqrt(2)<23/16, and 2<529/256. Therefore

\[
a_0-1>\frac1{24},\qquad 4k_0-2>\frac{11}{32}.
\]

For 4/5<=a<=1, the associated beta is greater than beta_0. Since k'(beta)>0, (SW.5) implies Phi'(x)>=4k_0-2 for a<=x<=a_0. AF3 supplies M_A>=Phi(a_0). Consequently

\[
\boxed{\widetilde{\mathcal Q}(h)\leq\Phi(a)
<M_A-\frac{11}{768}\qquad(4/5\leq a\leq1).}
\tag{SW.11}
\]

The bound is conservative and not claimed sharp. Its significance is that it is an explicit deficit throughout the entire potentially competitive narrow-width range, not merely at a single test width.

## 4. Exact implication for the missing narrow-sofa theorem

Let S be a body in the incoming unit-height strip, with actual hull width W<=2 and E(S)=|S|-Q_tilde(h_K). If W<=8/5, then |S|<=8/5<M_A immediately. Otherwise 8/5<W<=2, so its centered half-width is in the range of (SW.11).

It follows that any hypothetical narrow body with |S|>=M_A must satisfy

\[
\boxed{E(S)>\frac{11}{768}.}
\tag{SW.12}
\]

Thus the concrete geometric statement

\[
E(S)\leq11/768\quad\text{for all relevant bodies with }8/5<W\leq2
\]

would close the narrow-width gate. That statement has **not** been proved here. The existing narrow counterexample lies below this width range and is not discarded; a high-width counterexample to the proposed error budget would invalidate that route without contradicting SW1–SW3.

The stability transfer has turned the unquantified scalar width deficit into a numerical-free exact certificate. The unresolved object is the ordinary-area error E, not the scalar maximization. No CI, Lean/Lake compilation, numerical experiment, or computer algebra was used.
