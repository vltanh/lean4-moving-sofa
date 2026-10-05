# 30. Weak curvature bounds still give an exact, unclipped niche area

This note removes the strict-curvature obstacle left in Section 23.4. It does not approximate feasible bodies by feasible Minkowski interpolations. Instead it proves the profile geometry directly when the curvature densities may equal one, and controls clipping by retention of exposed-face endpoints.

The full-turn and contact-inequality hypotheses remain explicit.

## 30.1 Weak contact ordering

Let K be a convex body between y=0 and y=1 with vertical span one. For both h_K and h_K^rho, assume the quarter functions f,g belong to H^2(0,L), L=pi/2, and

\[
0\leq\rho_f=f''+f\leq1,\qquad
0\leq\rho_g=g''+g\leq1\quad\text{a.e.},
\qquad p=f'-g+1\leq q=g'+f-1.
\tag{30.1}
\]

As in Note 23, these bounds give W^{2,infinity} regularity on each quarter. The identities

\[
p'=\rho_f-1-q,\qquad q'=\rho_g-1+p
\]

imply that e^t p and e^(-t)q are nonincreasing. The endpoint formulas give p(0)>=0 and q(L)<=0; p<=q supplies the other weak signs.

Choose

\[
a=\inf\{t:p(t)\leq0\},\qquad
b=\sup\{t:q(t)\geq0\}.
\tag{30.2}
\]

Both sets are nonempty, 0<=a<=b<=L, p(a)=q(b)=0, p<=0 on [a,L], and q>=0 on [0,b]. The definitions also cover p=q=0 identically: then a=0 and b=L.

On [a,b], p<=0<=q implies p'<=0 and q'<=0 a.e. If p vanishes on a nontrivial interval on which q>=0, then p'=0 and rho_f=1+q<=1 force q=0 there; similarly for q. Both curvatures equal one and the corner is constant on such a common zero interval. Thus extended zero sets produce a degenerate contact point, not an unaccounted extra moving arc.

## 30.2 The profile theorem with plateaus

Retain the curves c,B,D and the face endpoints ell=-g'(0), r=-f'(L) from Note 17. Their derivatives satisfy

\[
B'=(\rho_f-1)\nu,\qquad D'=(1-\rho_g)\mu.
\]

Thus B_x and D_x are nondecreasing; B_y is nonincreasing and D_y nondecreasing. Whenever B_x is constant on an interior parameter interval, rho_f=1 a.e. there, so B_y is also constant. The same holds for D. On the middle interval c_x is nonincreasing; if c_x is constant on an interval, then p=q=0 a.e. and c_y is constant as well.

**Lemma 62 (degenerate three-piece roof).** The open lower sweep above y=0 has a continuous nonnegative roof F over the top-face interval [ell,r]. Its graph is D from 0 to b, then c from b down to a, then B from a to L, with constant portions identified as single points. Its positive set

\[
P=\{x\in[\ell,r]:F(x)>0\}
\]

is an interval, possibly empty. No positive-height portion of the sweep lies outside [ell,r].

**Proof.** The wall-height identities (17.7) remain valid. Nondecreasing B_x gives the same global-maximization argument for the right wall as in Theorem 41; choose any parameter with B_x(t)=x. Its height does not depend on that choice because flat abscissa portions are constant points. The left wall is identical. On the middle part, the inequalities D_x(t)<=c_x(t)<=B_x(t) give the same comparison on the two sides of the selected parameter. Constant corner portions again have a unique height.

The endpoint arguments outside [ell,r] use x<ell<=D_x(t) and x>r>=B_x(t), so they need no strict curvature. All adjoining points agree since p(a)=q(b)=0. The side heights are nonnegative by their monotonicity and their zero baseline endpoints. On [a,b], the a.e. inequality c_y''<=0 follows as in Note 17, so its height is nonnegative and its positive set is an interval in parameter. Combining with the nondecreasing left side and nonincreasing right side proves that P is an interval. The continuous monotone graph parametrizations give continuity of F, including degenerate pieces. QED.

The area identity still holds:

\[
|J|=-I(h_K)+\frac12\int_0^L\min(p,0)^2
+\frac12\int_0^L\max(q,0)^2,
\tag{30.3}
\]

where |J| denotes the area under F above the baseline. The absolutely continuous determinant identities in Notes 13 and 23 apply unchanged. Their endpoint terms vanish even for a=0 or b=L, and constant/zero-height pieces contribute zero. A simple Jordan boundary is not required: monotone graph integration computes the area directly.

## 30.3 The positive roof must sit over the bottom face

Now assume K=conv(S), where S is compact and connected and follows both canonical full turns. Let I_t=[ell,r] be the top face interval, I_b=[ell_b,r_b] the bottom one, and put

\[
x_0=h_K(0)-1.
\]

The integrated curvature and endpoint-contact inequalities give

\[
\ell\leq x_0\leq r,
\qquad \ell_b\leq x_0\leq r_b.
\tag{30.4}
\]

For example x_0-ell=q(0)>=0 and
\(r-x_0=1-\int_0^L\rho_f\sin t\,dt\geq0\).
Apply the same formulas to rho K for the bottom face.

**Lemma 63 (positive-profile containment).** The positive set P of the lower roof is contained in I_b.

**Proof.** First suppose p(0)>0. Then q(0)>=p(0)>0. At x=x_0 the right wall-height function tends to p(0) as t decreases to zero, while the left one equals q(0)t+o(t). Both are positive for sufficiently small positive t, so F(x_0)>0.

Both endpoints of the bottom exposed face belong to S by Lemma 45. If either endpoint's x-coordinate belonged to P, its baseline point would lie inside the open lower sweep, contradicting feasibility. Since P is an interval, I_b contains x_0, and F(x_0)>0, these two endpoint exclusions force P to lie in I_b.

Next suppose p(0)=0. The endpoint formula forces rho_f=1 a.e. on the whole first quarter, hence f(t)=1+x_0 cos(t) and r=x_0. If q(0)=0 as well, then ell=x_0=r and P is empty.

If q(0)>0, then p'=-q and q is positive near zero. Consequently c_y(t)>0 and c_x(t)<x_0 for small positive t, with c_x(t) tending to x_0. Thus P contains points arbitrarily close to x_0 from the left.

The rightmost exposed face of K has upper height f'(0)=0. Since K lies in y>=0, its lower height is also zero. Reflection therefore gives p_rho(0)=1. The reflected contact inequality gives q_rho(0)>=1, so ell_b<=x_0-1. The reflected curvature integral then forces rho_{f_rho}=0 a.e., giving r_b=h_K(0)=x_0+1. Hence I_b contains a neighborhood of x_0 and meets P. The same extreme-endpoint exclusion and interval argument again imply P is contained in I_b. QED.

This proof does not claim equality of the two face intervals in the degenerate cases. It proves exactly the containment needed for area.

## 30.4 No positive clipping loss remains

For x in P, the bottom face gives (x,0) in K. Connectedness and the common-hull property imply that S has a point over every x in the horizontal projection of K. Since that point avoids the downward sweep, its height is at least F(x). Convexity then places the whole vertical segment from (x,0) to (x,F(x)) in K.

Thus the positive-height part of J is contained in K. Any zero-height baseline pieces outside K have area zero. Therefore

\[
|J\setminus K|=0.
\tag{30.5}
\]

Reflection proves the corresponding upper statement. The two swept niches are already disjoint inside K by Theorem 24. Combining (30.3) and (30.5) gives the exact area identity

\[
\boxed{|E_K|=\widetilde{\mathcal Q}(h_K).}
\tag{30.6}
\]

This proves the geometric identity with weak curvature bounds, without assuming face alignment and without presuming that an interpolated hull remains feasible.

## 30.5 Scope

The full-quarter-turn, H^2, and p<=q hypotheses remain. This note repairs the strict-to-weak curvature gap, not the unrestricted structural reduction. In particular it does not apply to the high-frequency bodies of Note 28, whose curvature genuinely exceeds one.
