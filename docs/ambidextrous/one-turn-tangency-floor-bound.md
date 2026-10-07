# Endpoint control confines the niche beneath the top face

**Scope.** For every global maximizer of the signed one-turn objective Psi, this proves that its full positive-height niche lies horizontally strictly between its top-face endpoints. The proof uses the already derived 9/4 endpoint-arm bound, not the unproved bound two or the saturated exposure ODE. It also removes clipping in the symmetric two-turn body constructed from this maximizer. It does not compare that body with every unrestricted ambidextrous competitor or compute max Psi.

Labels TF are local. Baseline: `03280a04151b0cf1a15c24b705f9aad4e12b28a0`. Dependencies are the written WR1, the same-sign estimates and component argument AR7/AR5', PT3, and TS1--TS2. All statements here remain subject to independent review.

## 1. Data from the preceding maximizing-cap arguments

Put L=pi/2. For a maximizing cap U, let f(t)=h_U(t), g(t)=h_U(t+L), and

$$
p=f'-g+1,\quad q=g'+f-1,\quad u=f''+f,\quad v=g''+g.
$$

The functions p,q are Lipschitz and u,v are bounded measurable, with

$$
p'=u-1-q,\qquad q'=v-1+p,
$$
$$
p(0)=1/2,\quad q(L)=-1/2,\quad p\le1,\quad q\ge-1,
$$
$$
0\le u\le\kappa(q),\qquad0\le v\le\kappa(p),
\quad \kappa(z)=\max\{|z|,(1+|z|)/2\}.
\tag{TF.1}
$$

On {p>0,q>0}, AR7 gives u=0 and v<=1/2. The reflected estimates hold on {p<0,q<0}. PT3 removes the point-top exception in TS2, giving

$$q(0)\le5/4,\qquad -p(L)\le5/4.\tag{TF.2}$$

For later use, every positive-q component that starts at a positive time has q<=1/8. Here is the short component argument. On q>0, TF.1 gives p'<=-1/2. As long as p>=0, AR7 gives p'<=-1 and q'<=p-1/2, so after a component starts with q=0 and p<=1, its positive increase is at most integral_0^(1/2)(1/2-s)ds=1/8. Once p<0, q'<=-1/2, so q cannot increase further. Thus any point with q>=1 belongs to the initial component, where q>0 throughout the preceding time interval.

## 2. A comparison lemma for a controlled oscillator

Define the continuous nondecreasing 1-Lipschitz function

$$
\phi(p)=\begin{cases}
-1,&p\le-1,\\
(p-1)/2,&-1\le p\le0,\\
p-1/2,&p\ge0.
\end{cases}
$$

On q>0 the preceding estimates imply q'<=phi(p). At p=0 the same inequality follows from v<=kappa(0)=1/2.

Let the reference functions r,s solve

$$r'=-1-s,\qquad s'=\phi(r),\qquad r(0)=1/2,\ s(0)=5/4.\tag{TF.3}$$

**Lemma TF1.** On the initial positive-q component, for t<=L,

$$
q(t)\le s(t)+\int_0^t\sin(t-z)u(z)dz
\le s(t)+\sin t\int_0^t u(z)\cos z\,dz.
\tag{TF.4}
$$

**Proof.** Put x=p-r and y=q-s. For a measurable a(t) in [0,1] and eta(t)>=0,

$$x'=u-y,\qquad y'=a(t)x-\eta(t),\qquad x(0)=0,\ y(0)\le0.$$

Here a is the secant slope of phi and eta=phi(p)-q'. For the homogeneous system x'=-y, y'=a x, the response in y to initial (x,y)=(1,0) lies between zero and sin(t-z) for an elapsed time at most pi/2. Indeed x''+a x=0 and

$$x(t)=\cos(t-z)+\int_z^t\sin(t-w)(1-a(w))x(w)dw.$$

A first-zero argument gives x>=0 on this interval. Hence y=-x'>=0 and differentiation of the display gives y<=sin(t-z).

For initial (x,y)=(0,1), write X=-x. Then X''+aX=0, X(z)=0, X'(z)=1, and the corresponding sine-kernel formula gives X>=0 and

$$y=X'\ge\cos(t-z)\ge0.$$

Variation of constants therefore bounds the contribution of u by the first kernel, while -eta and the nonpositive initial y contribute nonpositively. This proves the first inequality. The second uses sin(t-z)<=sin(t)cos(z) for 0<=z<=t<=pi/2. All arguments hold for bounded measurable a by the integral equations; no differentiability of a is used. QED.

This is a comparison for differential inequalities. It does not assert that the actual cap follows TF.3 or the saturated system SP.5.

## 3. An elementary strict bound for the reference trajectory

The following small rational estimates avoid a numerical integration of TF.3. Since phi>=-1, s(t)>=5/4-t>-1 on [0,L]. Thus r decreases throughout that interval, and s is nonincreasing.

While r>=0,

$$r(t)=1/2-(9/4)\sin t,\qquad s(t)=-1+(9/4)\cos t.$$

The first zero of r is beta0=arcsin(2/9). Put Q0=sqrt(77)/4. Thereafter, while -1<=r<=0 and z=(t-beta0)/sqrt(2),

$$r=1-\cos z-\sqrt2 Q0\sin z,\qquad s+1=Q0\cos z-\sin z/\sqrt2.$$

Take z0=21/100. This time is before r reaches -1: on 0<=z<=z0 the displayed r is greater than -(3/2)(9/4)z0=-567/800>-1. Its derivative has the decreasing sign on this interval. Also

$$\beta0<9/40,\qquad\sqrt2<99/70,$$

so t0=beta0+sqrt(2)z0<261/500<pi/6. The first comparison follows from

$$9/40-(9/40)^3/6-2/9=1013/1152000>0.$$

For the last, the elementary sine upper bound x-x^3/6+x^5/120 at x=261/500 is less than 1/2, and sine is increasing there.

Using Q0<351/160, 1/sqrt(2)>7/10, sqrt(2)Q0>14/5, and the alternating sine/cosine bounds at z0 gives

$$s(t0)\le1-\delta_0,\qquad r(t0)\le-2808141/5000000<-1/2,$$

where

$$\delta_0=46588123/128000000000>0.$$

For example the exact upper bound for s(t0)+1 is

$$
\frac{351}{160}\left(1-\frac{z0^2}{2}+\frac{z0^4}{24}\right)
-\frac7{10}\left(z0-\frac{z0^3}{6}\right)
=2-\delta_0.
$$

For t>=pi/6, r(t)<-1/2 and therefore s'(t)<=-3/4. Moreover

$$\frac d{dt}[\sin t(\sin t-1/2)]=(2\sin t-1/2)\cos t\le3/4.$$

If cos(t)>=1/2, use 2sin(t)cos(t)<=1; otherwise use cos(t)<=1/2 and 2sin(t)-1/2<=3/2. Consequently

$$
\boxed{s(t)+\sin t(\sin t-1/2)\le1-\delta_0\quad(pi/6\le t\le L).}
\tag{TF.5}
$$

Only elementary integral equations and explicit rational Taylor bounds occur in this calculation.

## 4. The first single-wall tangency cannot fall below the floor

Let

$$b(t)=(f(t)-1)\sin t+f'(t)\cos t.$$

This is the vertical coordinate of the first-wall tangency B=(f-1)mu+f'nu. It satisfies

$$b(0)=1/2,\quad b(L)=0,\quad b'=(u-1)\cos t,$$
$$b(t)=1/2-\sin t+\int_0^t u(z)\cos z\,dz.\tag{TF.6}$$

Suppose b(t)<=0 and q(t)>=1. By the component observation in Section 1, TF.4 applies. TF.6 forces t>=pi/6 and integral_0^t u cos<=sin(t)-1/2. Equations TF.4--TF.5 then give q(t)<=1-delta0, a contradiction. Hence

$$b(t)\le0\quad\Longrightarrow\quad q(t)<1.\tag{TF.7}$$

On any open interval where b<0, TF.1 and q>=-1 imply u<=1, so b'<=0. Such a negative component cannot return to zero, contradicting either its endpoint or b(L)=0. Thus b>=0.

In fact b>0 for t<L. If b(t0)=0 at an interior time, then q(t0)<1. The cap's positive top-face length T also gives q(t0)+1>=T cos(t0)>0: test the right top endpoint against the second support point, whose abscissa is no larger than the left top endpoint and whose height is at most one. Thus -1<q(t0)<1. By continuity, kappa(q)<1 uniformly near t0. Equation TF.6 then makes b strictly decreasing through zero, contradicting nonnegativity.

Horizontal reflection exchanges p,q with -q(L-t),-p(L-t), so the same proof applies to the other wall.

**Theorem TF2 (positive tangency heights).** Every signed weighted maximizing cap satisfies

$$
\boxed{
(f-1)\sin t+f'\cos t>0,\qquad
(g-1)\cos t-g'\sin t>0\quad(0<t<L).
}
\tag{TF.8}
$$

This is not unit curvature: derivatives of these positive functions may have either sign.

## 5. Confinement of the full niche and exact symmetric area

Let [x_tl,x_tr] be the top face. The two baseline wall intercepts are

$$R_0(t)=(f(t)-1)/\cos t,\qquad L_0(t)=(1-g(t))/\sin t.$$

Their derivatives are respectively b(t)/cos^2(t) and the second expression in TF.8 divided by sin^2(t), both positive. Their endpoint limits give

$$R_0(t)<-f'(L)=x_{tr},\qquad L_0(t)>-g'(0)=x_{tl}.$$

Every full-niche point (x,y) with y>=0 satisfies x<R_0(t) and x>L_0(t) for one witnessing interior angle. Therefore:

**Corollary TF3 (no horizontal leakage beyond the top face).**

$$\boxed{N(U)\subset (x_{tl},x_{tr})\times[0,1/2].}\tag{TF.9}$$

The vertical bound is TS1 plus PT3. The horizontal conclusion is new here and does not identify which tangent or corner arcs are exposed.

For the symmetric two-turn construction S_U of TS.13, let a be the upper cap roof and n the full niche roof. Now n>0 implies a=1, so its clipping correction vanishes:

$$\boxed{|S_U|=2\Psi(U).}\tag{TF.10}$$

The body is compact and connected through y=1/2 by ST1 and TS1. The two vertical segments over x_tl,x_tr survive entirely; outside the top-face interval n=0. It follows that its actual convex hull is exactly U intersect rho(U), where rho reflects y in 1/2, with aligned top and bottom faces. This is an actual-body statement, not an equality between signed quantities.

TF.10 concerns the symmetric body made from a weighted maximizer. It is not a proof that every ambidextrous body has such a representation, nor that its general clipping term is zero. The sharp value max Psi=M/2 and unrestricted optimality are not claimed.

No long computation, CI, or Lean/Lake compilation is used. A separate short rational-arithmetic check of Section 3 is supplementary to its written proof.
