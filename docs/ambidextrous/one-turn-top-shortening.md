# A finite top-shortening comparison for the signed one-turn objective

This extracts a useful consequence from Section 9 of the uploaded arm-reduction proposal without assuming differentiability of niche area, a finite contact decomposition, or a saturated exposure ODE. It concerns the signed one-turn objective, **not** arbitrary ambidextrous maximizers. Labels TS are local.

The normalized cap U is compact, convex, downward closed in 0<=y<=1, and reaches height one. Write W for its horizontal width, T for the length of its top face, and N(U) for its full positive-height niche, as in PA.1. Define

$$
\Psi(U)=|U|-|N(U)|-W/2,
\qquad H_N(U)=\max\bigl(0,\max_{0\le t\le\pi/2}c_{U,y}(t)\bigr).
\tag{TS.1}
$$

H_N is the supremum height of the full niche, with zero for an empty niche. Indeed every open forbidden quadrant lies below its corner, and points immediately below any positive-height corner belong to that quadrant. At the two endpoint angles the corner height is zero. No assertion that N(U) lies inside U is used.

## 1. Remove a horizontal segment as an actual cap operation

Suppose T>0. For 0<epsilon<T, every horizontal section of U at 0<=y<=1 is an interval [l(y),r(y)] of length at least T: downward closure retains the entire top-face projection on every such section. Define U_minus by the sections

$$
[\ell(y),r(y)-\varepsilon].
$$

The left boundary is convex and the right boundary concave, so U_minus is compact and convex. Their monotonicities in height preserve downward closure. Its top has length T-epsilon>0 and height one. Directly from its horizontal sections,

$$
U=U_{\rm minus}+[0,\varepsilon]e_x,
\quad |U|-|U_{\rm minus}|=\varepsilon,
\quad W(U)-W(U_{\rm minus})=\varepsilon.
\tag{TS.2}
$$

Thus this is a genuine admissible cap contraction, not formal subtraction of support functions. A horizontal renormalization afterward does not alter the objective.

Its supports satisfy

$$
h_U(\theta)=h_{U_{\rm minus}}(\theta)
+\varepsilon\max(\cos\theta,0).
\tag{TS.3}
$$

On a conventional lower-turn quarter this says f=f_minus+epsilon cos(t) and g=g_minus. Consequently

$$
c_{U_{\rm minus},y}(t)=c_{U,y}(t)-\varepsilon\sin t\cos t,
$$

and

$$
H_N(U_{\rm minus})\ge H_N(U)-\varepsilon/2.
\tag{TS.4}
$$

## 2. The full niche gains at least a rectangular strip

For any normalized cap V and epsilon>=0,

$$
\boxed{N(V)+[0,\varepsilon]e_x\subseteq N(V+[0,\varepsilon]e_x).}
\tag{TS.5}
$$

To check this, let z belong to a forbidden quadrant of V at an interior angle t, and let 0<=xi<=epsilon. Put mu=(cos t,sin t), nu=(-sin t,cos t). Then

$$
(z+\xi e_x)\cdot\mu<h_V(t)-1+\varepsilon\cos t,
$$

$$
(z+\xi e_x)\cdot\nu<h_V(t+\pi/2)-1,
$$

because the second scalar product decreases by xi sin(t). These are exactly the forbidden inequalities for the enlarged cap, and vertical height is unchanged.

For every bounded nonempty open subset A of a line,

$$
|A+[0,\varepsilon]|\ge |A|+\varepsilon.
\tag{TS.6}
$$

For a finite union of intervals this follows by merging overlapping enlarged intervals: there is a contribution epsilon from the last right endpoint and nonnegative contributions from any remaining gaps. Approximate a bounded open set from within by finite interval unions and pass to the supremum. This proof needs neither convexity nor connectedness of A.

At every 0<y<H_N(V), the horizontal niche section is bounded, open and nonempty. Applying TS.6 there and integrating by Fubini, TS.5 implies

$$
|N(V+[0,\varepsilon]e_x)|-|N(V)|
\ge\varepsilon H_N(V).
\tag{TS.7}
$$

This is a **lower bound for full niche growth**, not equality or an estimate of clipped surviving area. It remains valid for multiple components and changing contact types.

## 3. A quantitative improvement when the niche is too tall

Combine TS.2 and TS.7 with V=U_minus. One obtains

$$
\begin{aligned}
\Psi(U_{\rm minus})-\Psi(U)
&=|N(U)|-|N(U_{\rm minus})|-\varepsilon/2\\
&\ge\varepsilon\bigl(H_N(U_{\rm minus})-1/2\bigr)\\
&\ge\varepsilon\bigl(H_N(U)-1/2-\varepsilon/2\bigr).
\end{aligned}
\tag{TS.8}
$$

**Theorem TS1 (positive top face forces a half-height niche).** Every global maximizer of Psi whose top face has positive length satisfies

$$
\boxed{H_N(U)\le1/2.}
\tag{TS.9}
$$

If H_N(U)>1/2 and T>0, choosing

$$
\varepsilon=\min\{T/2,\ H_N(U)-1/2\}
$$

gives an explicit strict improvement of at least epsilon(H_N(U)-1/2)/2 by TS.8. This contradicts maximality. The proof does not use WR regularity or the value of the optimal objective.

Let P be the attained maximum of PA2. For every cap with T>0 and H_N(U)>1/2 the same finite comparison yields

$$
P-\Psi(U)\ge
\tfrac12\min\{T/2,H_N(U)-1/2\}\,(H_N(U)-1/2).
\tag{TS.10}
$$

P is not replaced by the unproved M/2 in this estimate.

## 4. Consequences for the remaining endpoint arm problem

At a Psi-maximizer, ST1 gives a(x)>=1/2 on its full projection. If T>0, TS1 therefore shows that its full niche lies in its cap. The one-turn surviving fibers all contain height 1/2, so U minus N(U) is compact and connected. This proves niche containment for this stated class; it does not compute Psi.

WR1 supplies an extreme point (x_R,1/2) and a top-face endpoint (x_tl,1). Let d=x_R-x_tl. Test those two points in the support bounds at an interior angle t. With c=cos t and s=sin t,

$$
f(t)\ge x_Rc+\tfrac12s,
\qquad g(t)\ge-x_{tl}s+c.
$$

It follows that

$$
c_{U,y}(t)\ge dsc+\tfrac12s^2+c^2-s-c.
\tag{TS.11}
$$

Use the exact rational direction (c,s)=(4/5,3/5) and H_N<=1/2. Since

$$
\tfrac12s^2+c^2-s-c=-29/50,
$$

TS.11 gives (12/25)d-29/50<=1/2, hence d<=9/4. Reflect horizontally for the other arm.

**Corollary TS2.** Every Psi-maximizer with T>0 satisfies

$$
\boxed{x_R-x_{tl}\le9/4,\qquad x_{tr}-x_L\le9/4.}
\tag{TS.12}
$$

This is weaker than the uploaded sufficient bound EA2, whose threshold is two. It is not rounded down to that threshold. Combined with AR5', it confines any possible remaining curvature excess in this class to endpoint arm values in (2,9/4].

The two top-face endpoints themselves give at t=pi/4

$$
H_N\ge T/2+1-\sqrt2,
$$

so also T<=2sqrt(2)-1. This bound is an ancillary consequence, not a replacement for EA2.

## 5. A direct two-turn construction and its retained clipping

For a positive-top-face weighted maximizer, reflect U in y=1/2 and intersect the two canonical surviving bodies. If a is the upper roof of U and n is its full niche roof, then a>=1/2 and 0<=n<=1/2. The resulting fibers are

$$
[\max\{n,1-a\},\ \min\{a,1-n\}],
$$

all containing 1/2. This produces a compact connected ambidextrous body S_U following both full canonical turns. Its ordinary area is exactly

$$
\boxed{|S_U|=2\Psi(U)+2\int\min(n,1-a)\,dx\ge2\Psi(U).}
\tag{TS.13}
$$

Thus a weighted maximizing cap with T>0 and Psi>M/2 would give an actual ambidextrous competitor larger than M, not merely an auxiliary numerical excess. No such cap is supplied. Conversely, an upper bound on Psi alone does not remove the nonnegative integral in TS.13. This formula is the symmetric case of the previously audited two-cap accounting, not a universal enclosure with its sign reversed.

## 6. What remains unproved

TS1 does not show that every weighted maximizer has T>0. A point top face cannot be shortened by TS.2. Nor do TS1--TS2 supply EA2, exact exposure balance, or the asserted saturated ODE. The current value-only task would need EA2 for one attained maximizer, or a different valid sharp comparison.

The result is specific to the signed one-turn objective. The two-turn geometry, positive clipping, and the other canonical-wing admission conditions are not removed by it. All new claims here have analytic proofs; numerical checks of examples are supplementary. No CI or Lean/Lake compilation was used.
