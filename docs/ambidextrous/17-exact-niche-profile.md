# 17. Exact niche profiles under explicit curvature hypotheses

This note supplies the geometric interpretation missing from the adaptive functional. It proves a complete description of a single swept niche in the upper half-plane, without assuming the contact picture in advance. It then identifies exactly how clipping by the common convex hull changes that area.

The hypotheses below are restrictions, not consequences yet proved for arbitrary maximizing sofas. In particular, a curvature bound on each quarter and the monotone-velocity conditions of Note 16 remain substantive geometric assumptions.

## 17.1 Hypotheses and contact curves

Let K be a compact convex body of vertical span one, normalized between y=0 and y=1. Put L=pi/2 and

\[
f(t)=h_K(t),\qquad g(t)=h_K(t+L),\qquad
p=f'-g+1,\qquad q=g'+f-1.
\]

Assume f,g are C^1 and piecewise C^2 on [0,L], with finitely many pieces. Suppose

\[
0\leq\rho_f:=f''+f<1,\qquad
0\leq\rho_g:=g''+g<1
\tag{17.1}
\]

on each open smooth piece. Assume also the conditions of (16.1): p,q strictly decrease, have opposite endpoint signs, and p<=q. Let a and b be their unique zeros, so 0<a<=b<L.

For the lower full quarter turn define

\[
c=(f-1)\mu+(g-1)\nu,\qquad
B=c+p\nu,\qquad D=c-q\mu.
\tag{17.2}
\]

The sweep is the open set

\[
W=\bigcup_{0\leq t\leq L}
\{z:z\cdot\mu_t<f(t)-1,\ z\cdot\nu_t<g(t)-1\}.
\tag{17.3}
\]

Direct differentiation gives

\[
B'=(\rho_f-1)\nu,
\qquad D'=(1-\rho_g)\mu.
\tag{17.4}
\]

Consequently B_x and D_x strictly increase, B_y strictly decreases in the interior, and D_y strictly increases in the interior. These statements follow by integrating the derivatives across the finitely many pieces, not by assuming differentiability at their joins.

The top exposed face of K has endpoints

\[
\ell=-g'(0),\qquad r=-f'(L).
\tag{17.5}
\]

In particular D(0)=(ell,0), B(L)=(r,0), B(a)=c(a), and D(b)=c(b). These identities explain why the horizontal projection of the niche is linked to the **top** face, although the niche is removed from below.

## 17.2 The profile theorem

**Theorem 41 (three-piece swept profile).** There is a continuous nonnegative function F on [ell,r], positive on its interior and zero at its endpoints, such that

\[
W\cap\{y>0\}
=\{(x,y):\ell<x<r,\ 0<y<F(x)\}.
\tag{17.6}
\]

Its graph, in order of increasing x, is:

- D(t), with t increasing from 0 to b;
- c(t), with t decreasing from b to a;
- B(t), with t increasing from a to L.

If a=b, the middle graph consists of just the common joining point. No other envelope arcs or self-overlaps above the baseline occur.

**Proof.** For 0<t<L, the upper height allowed by the forbidden quadrant at a fixed x is the minimum of

\[
R_t(x)=\frac{f(t)-1-x\cos t}{\sin t},\qquad
L_t(x)=\frac{g(t)-1+x\sin t}{\cos t}.
\]

Thus the sweep's height threshold is the supremum over t of min(R_t,L_t). Differentiation gives the two useful identities

\[
\partial_tR_t(x)=\frac{x-B_x(t)}{\sin^2t},\qquad
\partial_tL_t(x)=\frac{x-D_x(t)}{\cos^2t}.
\tag{17.7}
\]

Both B_x and D_x strictly increase by (17.4).

For x between c_x(a) and r, choose the unique t in [a,L] with B_x(t)=x. Equation (17.7) shows that R_t(x) is the global maximum of R_s(x) over s. At B(t) the first wall inequality is an equality, and its second coordinate is g(t)-1+p(t)<=g(t)-1, because p(t)<=0. Thus min(R_t,L_t)=B_y(t). No other parameter can give a larger minimum, since it cannot give a larger R. Endpoint values follow by continuity.

Similarly, for x between ell and c_x(b), the unique t in [0,b] with D_x(t)=x maximizes L_t(x). The other wall inequality holds because q(t)>=0. The threshold is therefore D_y(t).

On [a,b], p<=0 and q>=0, so

\[
c_x'=p\cos t-q\sin t\leq0,
\]

with strict decrease if a<b. For x between c_x(b) and c_x(a), choose t_0 with c_x(t_0)=x. Since

\[
D_x(t_0)=x-q(t_0)\cos t_0\leq x,
\qquad B_x(t_0)=x-p(t_0)\sin t_0\geq x,
\]

monotonicity in (17.7) shows L_t(x)<=L_{t_0}(x) for t<=t_0 and R_t(x)<=R_{t_0}(x) for t>=t_0. Both values at t_0 equal c_y(t_0). Hence the threshold on the middle piece is precisely the corner curve.

If x<ell, the function L_t(x) is decreasing and its limit at zero is g(0)-1=0. If x>r, R_t(x) is increasing and its limit at L is f(L)-1=0. Thus there is no forbidden part above zero outside [ell,r]. The endpoint quadrants at t=0,L likewise lie below y=0 and add no positive-height part.

The joining points agree because p(a)=q(b)=0. The side heights are positive away from the baseline by (17.4). On the middle interval,

\[
c_y''=p'\sin t+p\cos t+q'\cos t-q\sin t\leq0
\]

almost everywhere; this uses monotone decrease of p,q and their signs there. Hence c_y lies above the chord between its positive endpoint heights. The graph is continuous, is positive in its interior, and returns to the baseline only at ell,r. Openness of the sweep gives the strict inequalities in (17.6). QED.

This proof obtains the contact combinatorics from inequalities; it does not posit the candidate's switching angles. The switches can differ for a body and its reflection.

## 17.3 The area enclosed by the profile

Let

\[
J(K)=\{(x,y):\ell\leq x\leq r,\ 0\leq y\leq F(x)\}.
\]

Boundary conventions do not affect its area. Its positively oriented boundary runs along B from L down to a, then c from a to b, then D from b down to 0, and finally along the baseline from ell to r. Applying (13.4)–(13.5), all switch and baseline endpoint terms vanish. Thus

\[
\boxed{
|J(K)|=-I(h_K)
+\frac12\int_a^L p^2\,dt
+\frac12\int_0^b q^2\,dt.
}
\tag{17.8}
\]

The integrals equal the negative/positive-part expressions in Note 16. Equation (17.8) is an **ambient profile area**, not yet necessarily the area of the niche inside K.

## 17.4 The clipping deficit has the unfavorable sign

Let N=K intersect W. Since K lies in y>=0,

\[
|N|=|J(K)\cap K|,
\qquad
|J(K)|-|N|=|J(K)\setminus K|\geq0.
\tag{17.9}
\]

Suppose, in addition, K is the convex hull of a connected feasible body for this canonical full-turn motion. Every x in the horizontal projection of K then occurs in that body, so F(x) cannot exceed the upper boundary of K over [ell,r]. In particular F<=1 there. Writing b_K(x) for the lower boundary of K, Fubini gives

\[
|J(K)\setminus K|
=\int_\ell^r\min\{F(x),b_K(x)\}\,dx.
\tag{17.10}
\]

This term vanishes when the whole profile lies in K; otherwise it is positive. For two separated profiles the exact surviving area is consequently

\[
|E_K|=\widetilde{\mathcal Q}(h_K)
+|J(K)\setminus K|
+|\rho J(\rho K)\setminus K|.
\tag{17.11}
\]

So the sharp adaptive inequality in Theorem 40 is not automatically an upper bound for actual area. The missing clipping terms enter with a **plus** sign. This records the remaining geometric obstruction explicitly instead of hiding it in the word "niche."

## 17.5 A sufficient condition that eliminates clipping

**Lemma 42 (aligned exposed faces).** Suppose K has identical horizontal intervals [ell,r] as its top and bottom exposed faces. If it is the hull of a connected feasible body for both full conventional turns, then both profile regions in (17.11) are contained in K. Hence

\[
|E_K|=\widetilde{\mathcal Q}(h_K).
\tag{17.12}
\]

**Proof.** Convexity gives \([\ell,r]\times[0,1]\subseteq K\). Theorem 41 locates the entire lower profile over [ell,r]. Feasibility and connectedness give F<=1, so this profile lies in that rectangle. Apply the same argument to rho K for the upper profile. Equation (17.11) then gives the asserted equality. QED.

The aligned-face hypothesis is not reflection symmetry of the whole hull. It permits different upper and lower curved boundaries. Nor has it been proved for an arbitrary maximizing hull. It provides an explicit restricted class where the algebraic maximum becomes a genuine area theorem.
