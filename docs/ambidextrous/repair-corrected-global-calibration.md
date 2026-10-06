# A sharp calibration that includes adverse repair-contact work

The global least curvature majorant need not increase ordinary sofa area: GR1 gives an exact feasible counterexample. This note does not ignore that loss. It proves that an explicit **repair-corrected** functional still has the sharp maximum M, even when some final contact velocities are larger than one.

The theorem is global on its stated function space. It uses no smallness, curvature cap, convexity, prescribed contact order, or activation-set assumption on the input profile. An ordinary-area comparison with this new functional remains a geometric obligation, stated separately at the end. The labels AC are local to this note.

## 1. Definition of the corrected model

Put L=pi/2. Let h be a real 2pi-periodic H^1 function with

\[
h(L)=1,\quad h(3L)=0,\quad h(0)+h(pi)=2a\geq2.
\]

Use h and h^rho(theta)=h(-theta)+sin(theta) for the two upper-half pairs f,g as in AF. For each pair set

\[
p=f'-g+1,\qquad q=g'+f-1,\qquad p_-:=\min(p,0),\quad q_+:=\max(q,0).
\]

Independently on each half choose nonnegative u,v in H^1_0(0,L). They are proposed repair increments; they are not presumed to come from a feasible geometric operation. Define

\[
B_+(u,v)=\frac12\int_0^L(u'^2+v'^2+uv'-vu')dt
\]

and

\[
\boxed{\mathcal J(h;\mathbf u)=\widetilde{\mathcal Q}(h)
-\sum_{\rm halves}\int_0^L[(1-q_+)u+(1+p_-)v]dt
-\sum_{\rm halves}B_+(u,v).}
\tag{AC.1}
\]

The linear integral can be negative: no condition q<=1 or p>=-1 is assumed. This is important for the example in GR1. Horizontal translation of h leaves p,q and both functionals unchanged, so center the axis supports as h(0)=h(pi)=a.

**Theorem AC1 (global corrected calibration).** For every profile and increments just specified,

\[
\boxed{\mathcal J(h;\mathbf u)\leq M.}
\tag{AC.2}
\]

Equality holds exactly when h is Romik's profile up to horizontal translation and every repair increment is zero.

The proof occupies Sections 2--5. It depends on AF1--AF3 and the explicitly solved fixed-width family SW1, not on ordinary-area enclosure by either functional.

## 2. Fixed-width deficit absorbs the cross terms

Let (f_a,g_a) be the unique half-profile optimizer at width 2a, let F_a be its value, and put Phi(a)=2F_a-2a. Let p_a,q_a be its velocities. Write delta f=f-f_a, delta g=g-g_a; they vanish at both endpoints.

The exact fixed-width expansion from SD1 is

\[
F_a-F(f,g)=B_0(\delta f,\delta g)
+\int D_-(p,p_a)+D_+(q,q_a),
\tag{AC.3}
\]

where B_0 is the nonnegative Dirichlet gauge energy from AF1, and D_plus and D_minus are the Bregman remainders of x_+^2/2 and x_-^2/2. A direct check of the two signs gives

\[
D_+(x,y)\geq\tfrac12(x_+-y_+)^2,
\qquad D_-(x,y)\geq\tfrac12(x_--y_-)^2.
\tag{AC.4}
\]

Completing squares, for u,v>=0,

\[
D_+(q,q_a)+(1-q_+)u
\geq(1-(q_a)_+)u-\tfrac12u^2,
\]

\[
D_-(p,p_a)+(1+p_-)v
\geq(1+(p_a)_-)v-\tfrac12v^2.
\tag{AC.5}
\]

These are pointwise inequalities. They do not differentiate the support of u,v or a contact-switching set.

Let

\[
b(a)=\max\{0,\|(q_a)_+\|_\infty-1,\|(p_a)_-\|_\infty-1\}.
\]

Combining (AC.3)--(AC.5), the deficit of the corrected **half** functional is bounded below by

\[
-b(a)\int(u+v)+B_+(u,v)-\tfrac12\int(u^2+v^2).
\tag{AC.6}
\]

The nonnegative B_0 term and the completed squares have only been dropped for this lower estimate.

## 3. A universal bound on the adverse contact credit

Put y(t)=e^{it/2}(u(t)+iv(t)). Then

\[
B_+(u,v)-\tfrac12\int(u^2+v^2)
=\frac12\int\left(|y'|^2-\frac54|y|^2\right)
\geq\frac{11}{32}\int|y'|^2.
\tag{AC.7}
\]

The last step is the Dirichlet inequality with first eigenvalue four on [0,pi/2].

For a nonnegative w in H^1_0(0,L), integration by parts against t(L-t)/2 and Cauchy--Schwarz give

\[
\int_0^L w\leq\sqrt{L^3/12}\,\|w'\|_2.
\]

Apply this to |y|, whose weak derivative has absolute value at most |y'|, and use u+v<=sqrt(2)|y|. If R=||y'||_2, (AC.6) is at least

\[
\frac{11}{32}R^2-b(a)\sqrt{L^3/6}\,R
\geq-\frac{4L^3}{33}b(a)^2.
\]

Adding both halves yields the fully explicit bound

\[
\boxed{\mathcal J(h;\mathbf u)
\leq\Phi(a)+\frac{\pi^3}{33}b(a)^2.}
\tag{AC.8}
\]

Notice pi^3/33<1; the elementary estimate pi<22/7 suffices. Thus the derivative energy pays for adverse linear work with a coefficient strictly smaller than one. This does not assert that the uncorrected geometric repair has positive area gain.

## 4. The exact fixed-width family controls that credit globally

The candidate half-width is a_*=1/(3 sin(beta_*)), and 1<a_*<4/3. For example Y=tan(beta_*)>2/7 gives a_*<sqrt(53)/6<4/3, while Y<1/3 gives a_*>1.

We claim, for every a>=1,

\[
b(a)\leq(3a/2-2)_+.
\tag{AC.9}
\]

Here are the needed checks from the explicit fixed-width solutions, including both width ranges.

For 1<=a<2/(3 tau), where tau=tan(pi/8)=sqrt(2)-1, use SW1's parameter beta and C=cot(beta/2+pi/8). The half-profile is symmetric, so p_a(L-t)=-q_a(t). Its early-phase q is

\[
q_a(t)=-1+\tfrac12\sin(\beta-t)+C\cos(\beta-t).
\]

For a<=a_*, beta>=beta_* and C<=C_*. Thus q_a is at most sqrt(C_*^2+1/4)-1 on this phase. At the candidate k=1/2 implies tan(beta_*)=1/(2C_*), so this bound is exactly 3a_*/2-1<1. The middle q decreases from C-1 and the late q is negative, so the same bound controls its positive part everywhere.

For a>=a_* in this family, k<=1/2. The early-phase equations give q'=p-1/2<=0, because p decreases from k. The middle and late q also decrease. Therefore max q=q(0)=3a/2-1. Reflection gives the same bound for -min p.

On the remaining tail a>=2/(3 tau), the explicit all-contact optimizer in AF A.6 has decreasing q with q(0)=3a/2-1, and p(L-t)=-q(t). This proves (AC.9) on the entire wide-profile range.

Define

\[
\Gamma(a)=\Phi(a)+(3a/2-2)^2\qquad(a\geq4/3).
\]

It is strictly decreasing there. A short exact calculation proves this without any numerical estimate of Phi. In the SW1 range,

\[
\Gamma'(a)=4k+\tfrac92a-8.
\]

Substitute SW1's expressions and put z=tan(beta/2). After multiplying by the positive denominator (tau+z)(1+z^2), its numerator is

\[
\boxed{(3-8\tau)-12\tau z^2+(3\tau-4)z^3<0.}
\tag{AC.10}
\]

Every coefficient has the asserted sign, since 3/8<tau<1/2 and z>=0. On the all-contact tail AF gives Phi'(a)=6-12 tau a, and hence

\[
\Gamma'(a)=(9/2-12\tau)a<0.
\]

The two formulas match at their common endpoint. Consequently

\[
\Gamma(a)\leq\Gamma(4/3)=\Phi(4/3)<M.
\tag{AC.11}
\]

The final strict inequality follows from AF3's unique maximizing width a_*<4/3.

## 5. Proof of AC1 and exact equality

For 1<=a<=4/3, (AC.9) gives b(a)=0, so (AC.8) gives J<=Phi(a)<=M. For a>4/3, (AC.8), pi^3/33<1, and (AC.11) give J<M. Thus equality is possible only at a=a_*.

At a_*, both coefficients 1-(q_a)_+ and 1+(p_a)_- have a uniformly positive lower bound, since max q_a=-min p_a=3a_*/2-1<1. Retaining those coefficients in (AC.5), rather than replacing them by zero, shows that equality forces all u,v to vanish. The remaining fixed-width deficit then forces both halves to be the unique optimizer by AF1. Undoing horizontal centering gives exactly the candidate translation family. Conversely that family with zero increments attains M. This proves AC1.

## 6. A geometric consequence that includes the counterexample

Suppose K is the actual hull of a feasible body S, bar K is a second normalized hull of the same width W>=2, and its upper-quarter support increases are u,v>=0 with zero endpoints. Assume:

- the surviving repaired body has area at most Q_tilde(bar h);
- the complete ordinary-area gain is the standard-corner accounting RC1, summed over the two halves, with no omitted clipping, endpoint, disconnected-component, or other boundary term.

Then RC1 gives

\[
|S|\leq\widetilde{\mathcal Q}(\bar h)
-\sum\int[(1-\bar q)u+(1+\bar p)v]-\sum B_+(u,v)
\leq\mathcal J(\bar h;\mathbf u)\leq M.
\tag{AC.12}
\]

The middle inequality uses bar q<=bar q_+ and bar p>=bar p_-. It does not require either velocity to be bounded by one. Thus a repair whose actual area gain is negative can still provide a valid sharp upper comparison after its contact cost is included.

The family GR1 satisfies these accounting hypotheses with one nonzero u: its loss is precisely the one computed there. AC1 bounds it without incorrectly declaring its outward repair area improving. More generally (AC.12) removes the sign and small-amplitude requirements from this **specified** standard-corner repair route. Equality forces zero increments and the candidate support. When S is contained in the resulting candidate envelope, the earlier regular-closed recovery gives exact body equality.

**Remaining geometric boundary.** No claim is made that every wide maximizing hull admits the accounting hypotheses in this section. Side-only changes have different mass terms; altered corner orientations, clipping, partial endpoint angles, and changes of feasible component cannot be silently assigned RC1's formula. The global operator GM2 solves the construction of a curvature majorant, and AC1 solves a corrected analytic maximum, but their unrestricted geometric linkage is still unproved. This note is not an unrestricted optimality theorem.
