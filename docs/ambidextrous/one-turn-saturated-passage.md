# Exact first-passage times for the proposed saturated arm system

Section 9 of the uploaded [arm-reduction proposal](one-turn-arm-reduction.md) tested first-passage monotonicity numerically. This note proves that particular ODE claim analytically, including its two high-arm regimes. **It does not prove that an actual maximizing cap obeys this ODE.** The exact exposure law, activity information and its geometric admissibility remain missing inputs. Labels SP are local.

## 1. The system being analyzed

Start at p(0)=1/2, q(0)=q0>=0. On the three successive sign regions, prescribe

$$
\begin{array}{c|cc}
&\rho_f&\rho_g\\
p>0,\ q>0&0&1/2\\
p<0<q&\kappa(q)&\kappa(p)\\
p<0,\ q<0&1/2&0
\end{array}
$$

with kappa(z)=max(|z|,(1+|z|)/2), and on the reverse region p>=0,q<=0 prescribe rho_f=-q, rho_g=p. In every region,

$$
p'=\rho_f-1-q,\qquad q'=\rho_g-1+p.
\tag{SP.1}
$$

The solution is obtained by the explicit region flows below. The crossings that occur are transverse except at the common boundary case, which has the indicated continuous limiting solution. Values of the vector field at an isolated switching time do not affect these absolutely continuous solutions.

Let tau(q0) be the **first** time q reaches -1/2. We are not imposing support-height closure or any maximality condition on this ODE calculation.

## 2. Low initial arms: the reverse region

Put r=1+q0 and q_c=sqrt(5)/2-1. In the initial positive-positive region,

$$
p(t)=1/2-r\sin t,\qquad q(t)=-1+r\cos t.
\tag{SP.2}
$$

For 0<=q0<=q_c, q reaches zero before p does. Put d=sqrt(r^2-1), so 0<=d<=1/2. The first segment lasts arctan(d) and ends at (1/2-d,0). The reverse-region flow rotates about (1/2,-1/2) with angular speed two. Its segment to (0,d-1/2) lasts pi/4-arctan(2d). The final negative-negative segment is the reflected initial one and lasts arctan(d).

Therefore

$$
\boxed{\tau(q0)=2\arctan d+\pi/4-\arctan(2d).}
\tag{SP.3}
$$

Its derivative with respect to d is

$$
\frac{6d^2}{(1+d^2)(1+4d^2)}\ge0,
$$

strictly positive for d>0. This range has tau<=2 arctan(1/2)<pi/2. At q0=0 the reverse flow starts immediately, giving tau=pi/4.

## 3. The standard quadrant has a separable conserved quantity

For q0>=q_c, p reaches zero first. Define

$$
v=\sqrt{(1+q0)^2-1/4}-1\ge0,
\qquad \beta_0=\arctan\frac1{2(1+v)}.
\tag{SP.4}
$$

The first segment lasts beta0 and ends at (p,q)=(0,v). In the standard quadrant put x=-p>=0 and y=q>=0. Then

$$
x'=m(y),\qquad y'=-m(x),\qquad
m(u)=\begin{cases}(1+u)/2,&0\le u\le1,\\1,&u\ge1.\end{cases}
\tag{SP.5}
$$

If

$$
J(u)=\begin{cases}u/2+u^2/4,&0\le u\le1,\\u-1/4,&u\ge1,\end{cases}
$$

then J(x)+J(y)=J(v) is conserved. Both coordinates are monotone along the arc from (0,v) to (v,0), so there are no hidden returns or extra revolutions. Reflection supplies a final negative-negative segment of duration beta0, ending at (p,q)=(-q0,-1/2). The second component decreases strictly during that last segment, making this the first passage to -1/2.

## 4. The three exact standard-quadrant durations

Write B(v) for the time from (0,v) to (v,0) in SP.5.

**Case 0<=v<=1.** Both coordinates stay below one. The shifted pair (x+1,y+1) rotates with speed 1/2, giving

$$B(v)=4\arctan(1+v)-\pi.$$

**Case 1<=v<=7/4.** Initially x'=1 and y' = -(1+x)/2, so y=v-x/2-x^2/4. It reaches y=1 when

$$x=a=\sqrt{4v-3}-1\in[0,1].$$

This initial segment lasts a. The middle arc, from (a,1) to (1,a), has both coordinates below one and duration pi-4 arctan((a+1)/2). The final segment lasts a by reflection. Thus

$$B(v)=2(\sqrt{4v-3}-1)+\pi-4\arctan\frac{\sqrt{4v-3}}2.$$

**Case v>=7/4.** The first segment reaches x=1 at time one, with y=v-3/4>=1. Both derivatives then have magnitude one until y=1, a duration v-7/4. The reflected final segment lasts one. Hence

$$B(v)=v+1/4.$$

All three formulas agree at v=1 and v=7/4. In particular

$$
\boxed{\tau(q0)=2\arctan\frac1{2(1+v)}+B(v)\quad(q0\ge q_c).}
\tag{SP.6}
$$

## 5. Monotonicity is analytic, not a grid observation

For 0<=v<=1, differentiation of SP.6 gives

$$
\frac{d\tau}{dv}
=\frac4{1+(1+v)^2}-\frac4{1+4(1+v)^2}>0.
$$

For 1<=v<=7/4, put u=sqrt(4v-3) in [1,2]. Then

$$
B'(v)=\frac{4u}{u^2+4}\ge4/5,
\qquad
\left|\frac{d(2\beta_0)}{dv}\right|\le4/17.
$$

Thus d tau/dv>0. For v>=7/4, B'=1 and the negative derivative of 2beta0 has magnitude strictly less than one. Since v increases strictly with q0, SP.3 and SP.6 together prove strict monotonicity on q0>=0.

Let Y be the positive root of 4Y^3+3Y-1=0, beta=arctan(Y), and q_star=1/(2 sin(beta))-1. Its v_star=cot(beta)/2-1 lies in (0,1). The cubic, with 0<Y<1/2 and the corresponding angle ranges, gives

$$
2\arctan(2Y)=\pi/4+\arctan Y.
$$

Substitution in SP.6 gives tau(q_star)=pi/2. Strict monotonicity proves:

**Theorem SP1 (unique prescribed passage time).** For the stated saturated piecewise ODE and q0>=0,

$$
\boxed{\tau(q0)=\pi/2\quad\Longleftrightarrow\quad q0=q_*.}
\tag{SP.7}
$$

In particular q0>1 cannot have its first passage at pi/2. This is a theorem about the hypothesized ODE, not a proof excluding such arms in the actual geometric optimization.

## 6. What remains before this can be used in the cap proof

The uploaded proposal explicitly left four issues: differentiability of niche area under its variation, identification of the exposure measure, global activity in the presence of folds, and ODE monotonicity. SP1 resolves only the last one. The finite top-shortening theorem TS1 obtains a different consequence without assuming differentiability, but does not supply exact exposure balance.

Even if the maximizing-cap ODE were justified and the signed maximum computed, a separate two-turn ordinary-area comparison must control clipping. None of the earlier positive corrections is discarded by SP1. All computations in this note are elementary analytic formulas. Floating-point comparison against the package's fifty passage times is a diagnostic only. No CI or Lean/Lake compilation was used.
