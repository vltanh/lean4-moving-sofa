# Signed-roof supplement: curvature domination without contact order

This proves an exact signed niche formula under the curvature bound alone. In particular, p<=q is **not needed** for the wall-envelope calculation once reverse corner arcs and the part of the roof below the baseline are retained. It then separates ordinary-area clipping from that negative signed area.

The result concerns full conventional quarter turns. It does not derive a curvature bound or full turns for an unrestricted maximizer. Its final sharp corollary applies to a stated geometric class with aligned exposed faces, not to every sofa. Labels SR1 onward are separate from the other supplements.

## S.1 Hypotheses and the signed roof

Let L=pi/2. Suppose f,g belong to W^{2,infinity}(0,L), with

\[
f(L)=g(0)=1,\qquad
0\leq f''+f\leq1,\quad0\leq g''+g\leq1\quad\text{a.e.}
\tag{S.1}
\]

No inequality between p=f'-g+1 and q=g'+f-1 is imposed. On 0<t<L set

\[
R_t(x)=\frac{f(t)-1-x\cos t}{\sin t},\qquad
L_t(x)=\frac{g(t)-1+x\sin t}{\cos t}.
\]

Let W be the union of the lower forbidden quadrants, including the axis-angle quadrants. Its vertical sections are downward open half-lines. Write their finite thresholds as

\[
F(x)=\sup\{y:(x,y)\in W\}.
\tag{S.2}
\]

Equivalently, take the supremum of min(R_t,L_t) over interior angles, and include the value zero when x<f(0)-1 or x>1-g(L), as supplied by the two axis quadrants. Endpoint equalities in x do not affect any area integral. This F is the **signed** roof: it can be negative. The roof of W above the incoming baseline is F_+=max(F,0), not F itself.

Put

\[
c=(f-1)\mu+(g-1)\nu,\quad
B=c+p\nu=(f-1)\mu+f'\nu,
\quad D=c-q\mu=(g-1)\nu-g'\mu,
\]

and

\[
\ell=-g'(0),\quad r=-f'(L),\quad
x_0=f(0)-1,\quad x_1=1-g(L).
\]

The derivatives are

\[
B'=(\rho_f-1)\nu,\qquad D'=(1-\rho_g)\mu.
\tag{S.3}
\]

Thus B_x and D_x are nondecreasing, with B_x(0)=x_0, B_x(L)=r, D_x(0)=ell, D_x(L)=x_1. Also B_y>=0 and D_y>=0, using B_y(L)=D_y(0)=0.

For x<ell, L_t(x) is nonincreasing in t and has limiting value zero at t=0. For x>r, R_t(x) is nondecreasing and has limiting value zero at t=L. Consequently

\[
\{F>0\}\subseteq[\ell,r].
\tag{S.4}
\]

The axis quadrants give F>=0 off [x_0,x_1] when x_0<x_1. Therefore F is zero outside a bounded interval containing ell,r,x_0,x_1. It is bounded there: it is at most max_t c_y(t), or zero where an axis quadrant contributes, and it is bounded below by the finite roof value at t=L/2. Its signed integral is well-defined.

## S.2 Curvature makes both parameter families unimodal

The exact wall derivatives are

\[
\partial_tR_t(x)=\frac{x-B_x(t)}{\sin^2t},\qquad
\partial_tL_t(x)=\frac{x-D_x(t)}{\cos^2t}.
\tag{S.5}
\]

For fixed x, each family is nondecreasing up to its maximum set and nonincreasing afterwards. In particular its superlevel sets in t are intervals. The same is true of their minimum, whose superlevel sets are intersections of those intervals.

First assume strict curvature inequalities and analytic functions, with p and q not identically zero. Their zero sets on the closed interval can be taken finite by analytic extension; arbitrarily small homogeneous perturbations eliminate the identically-zero cases. Then B_x,D_x strictly increase on the open interval. The signed roof has the following complete list of nonconstant graph pieces:

- B(t) for p(t)<0, traversed with increasing t;
- D(t) for q(t)>0, traversed with increasing t;
- c(t) for p(t)<0<q(t), traversed with **decreasing** t;
- c(t) for q(t)<0<p(t), traversed with **increasing** t.

The last pieces are reverse corners. They must not be discarded just because the candidate uses the standard orientation.

Here is a direct verification of completeness and activity. At B(t), R has its global maximum and p<0 makes its companion L value larger. Thus min(R,L) attains the roof there. The D statement is identical with q>0. At a standard corner x=c_x(t), D_x(t)<=x<=B_x(t). For parameters s<=t, monotonicity of D_x bounds L_s(x) by L_t(x); for s>=t, monotonicity of B_x bounds R_s(x) by R_t(x). Both agree at the corner, proving global activity. At a reverse corner B_x(t)<=x<=D_x(t); use R for s<=t and L for s>=t instead.

Conversely, an interior maximizer with unequal wall heights must be a stationary point of the smaller wall, hence a B or D point with the indicated companion sign. At equal heights, the one-sided maximum test gives one of the two opposite-sign corner cases. Axis maxima lie at height zero and contribute no signed graph area. Except for finitely many joining heights/abscissae, the strictly unimodal families give a unique active parameter; a maximum interval would force a wall to be constant on a parameter interval. Thus the pieces cover the signed graph once, not with multiplicity. The finite analytic zero sets partition them into ordinary monotone graph arcs.

## S.3 Exact signed area, including reverse corners

Let

\[
I(f,g)=\frac12\int_0^L\det(c,c')\,dt.
\]

**Theorem SR1 (signed roof identity).** Under (S.1),

\[
\boxed{\int_{\mathbb R}F(x)\,dx
=-I(f,g)+\frac12\int_0^L\min(p,0)^2\,dt
+\frac12\int_0^L\max(q,0)^2\,dt.}
\tag{S.6}
\]

There is no contact-order assumption and no claim that the left side is a nonnegative area.

**Proof in the strict analytic case.** Since F is zero off a bounded interval, its graph integral is one half of integral (F-xF')dx. An increasing graph parametrization Z=(X,Y) contributes minus one half of integral det(Z,Z'); a decreasing parametrization contributes the opposite sign when written with increasing t.

Let i_p=1_{p<0}, i_q=1_{q>0}, and let chi be 1 on the standard corner set, -1 on the reverse corner set, and zero on the two equal-sign sets. The graph decomposition gives

\[
2\int F=-\int i_p\det(B,B')-\int i_q\det(D,D')+\int\chi\det(c,c').
\]

The elementary identity chi=i_p+i_q-1 holds away from the finite zero sets. The determinant identities are

\[
\det(B,B')=\det(c,c')-p^2+[(f-1)p]',
\]

\[
\det(D,D')=\det(c,c')-q^2+[(g-1)q]'.
\]

Insert them. The coefficient of det(c,c') is exactly -1. Every sign-interval endpoint derivative term vanishes: an interior endpoint has p=0 or q=0; at L, f-1=0; at 0, g-1=0. The only other potential terms do not occur because p(0)>=0 and q(L)<=0. Those two signs follow from

\[
p(0)=1-\int_0^L\rho_f\cos t\,dt,\qquad
q(L)=-1+\int_0^L\rho_g\sin t\,dt.
\]

The remaining terms give (S.6).

**Passage to weak bounds.** Approximate each bounded density rho in L^1 by real analytic densities in (0,1), and solve f''+f=rho_f and g''+g=rho_g with the original endpoint values. The Dirichlet operator on length L has a bounded Green kernel and derivative kernel, so these solutions converge in C^1. A vanishing homogeneous adjustment, preserving f(L)=g(0)=1, avoids identically-zero p,q without changing the density bounds. Each resulting analytic formula extends past the closed interval; hence the sign sets are finite unions of intervals unless identically zero, which was excluded.

The right side of (S.6) converges by C^1 convergence. For the left side, all roofs have common bounded support and a common finite bound. On every compact interior angular interval their wall functions converge uniformly for bounded x. Near an axis, the corner heights are uniformly O(t) or O(L-t); when an endpoint quadrant applies it contributes zero, and otherwise, away from the two limiting endpoint abscissae, the appropriate wall tends to minus infinity. This proves pointwise roof convergence except possibly at those two abscissae. Dominated convergence gives the signed integral identity. This limiting step concerns wall envelopes, not presumed feasibility of interpolated convex bodies. QED.

## S.4 Exact ordinary-area error with no contact condition

Now let K=conv(S) for a compact connected body following both canonical full conventional quarter turns. Normalize K to vertical span one and assume its curvature measure is dominated by dt on the four open quarters. Axis faces are permitted. Suppose its horizontal width is at least one.

Apply SR1 to h_K and h_K^rho, and write F_-,F_+ for the two signed roofs, the second in reflected coordinates. Let b_K(x),t_K(x) be the lower and upper hull boundary functions on its projection I. The positive lower roof is supported on the top-face interval; the positive reflected roof is supported on the bottom-face interval. Their possible negative parts also lie in I: x_0=h_K(0)-1 and x_1=1-h_K(pi) belong to I when the horizontal width is at least one.

Every x in I occurs in S. Thus F_-(x)<=t_K(x) and F_+(x)<=1-b_K(x). The two niches are disjoint inside K by the connected vertical-barrier argument. Their actual areas are

\[
|N_-|=\int_I(F_--b_K)_+\,dx,\qquad
|N_+|=\int_I(F_+-(1-t_K))_+\,dx.
\]

Let E_K be the full saturation, which contains S. Define

\[
C_{\rm clip}=\int_I\min((F_-)_+,b_K)
+\min((F_+)_+,1-t_K)\,dx,
\]

\[
C_{\rm neg}=\int_I(F_-)_-+(F_+)_-\,dx,
\]

where a_- here means max(-a,0), a nonnegative **magnitude**, not the signed min convention used for p in (S.6).

**Corollary SR2 (all remaining error is explicit).**

\[
\boxed{|E_K|-\widetilde{\mathcal Q}(h_K)=C_{\rm clip}-C_{\rm neg}.}
\tag{S.7}
\]

**Proof.** The signed roof identity writes the adaptive functional as |K|-integral F_--integral F_+. Subtract the actual niche areas above and use a-(a-b)_+=min(a,b), with b>=0. Splitting a into its positive and negative parts gives (S.7). QED.

Thus the sole remaining signed-roof error **within this full-turn curvature-dominated class** is positive clipping offset by negative roof area. Contact order is not required for (S.7). Nothing here asserts C_clip<=C_neg for every such hull.

## S.5 A sharp geometric corollary without contact order

**Corollary SR3 (aligned-face comparison).** Under S.4, suppose the top and bottom exposed faces of K are the same horizontal interval. Then

\[
|S|\leq|E_K|\leq\widetilde{\mathcal Q}(h_K)\leq M,
\]

with equality exactly for a body congruent to Romik's candidate.

**Proof.** The positive lower roof is supported on the top-face interval by (S.4). On this interval b_K=0 because the bottom face is identical. The reflected statement gives t_K=1 on the positive upper roof interval. Hence C_clip=0. Equation (S.7) gives the middle inequality. Apply AF3, whose only additional width condition was assumed. At equality AF3 identifies the hull support up to horizontal translation. Canonical saturation then identifies E_K with the candidate, and its regular closedness gives equality of the original closed body S with E_K as in Lemma 4. The candidate attains equality by the existing construction. QED.

The contact inequality p<=q is not an assumption of this corollary. Full turns and the other stated geometric conditions remain assumptions. A common face interval of length greater than one supplies full turns for competitive bodies by the elementary outgoing-width gate, but that face-length assertion is not inferred here for arbitrary optimizers.

## S.6 A feasible reverse-contact example really lies outside the old contact domain

Let K be a disk of radius 1/2 centered at (0,1/2), Minkowski-added to the horizontal segment [-3/10,3/10]. Its support is

\[
h(t)=\tfrac12+\tfrac12\sin t+\tfrac3{10}|\cos t|.
\]

All open-quarter curvature densities equal 1/2 and its top and bottom faces are [-3/10,3/10]. On the upper quarters,

\[
p(t)=\tfrac12-\tfrac35\sin t,\qquad
q(t)=\tfrac35\cos t-\tfrac12.
\]

At t=pi/4, p>0>q, since 3sqrt(2)/5<1. Thus the contact-order condition fails on a nonempty interval. The corner height is

\[
c_y=\tfrac3{10}\sin2t+\tfrac12(1-\sin t-\cos t)<\tfrac3{10}<\tfrac12.
\]

Its positive roof is confined to the common face interval. Reflection puts the upper roof above height 7/10, so the two removed regions are separated and the whole central envelope has nonempty interval fibers. Outside the face interval no positive niche is removed; the convex flanks and face endpoints survive. Its compact connected canonical envelope is therefore a genuine full-turn ambidextrous body with hull K, to which SR3 applies although p<=q fails.

This example does not attain M. It shows that the removal of the contact hypothesis from the signed-roof theorem is substantive, rather than a change of wording within the old class.

## S.7 Remaining scope

SR1 closes the signed wall-envelope calculation with curvature domination and arbitrary contact signs. SR2 records the exact ordinary-area correction, and SR3 disposes of it when faces align. None proves the curvature bound, face alignment, or endpoint completion for every unrestricted maximizer.

The next geometric question in this reduced class is the sign of C_clip-C_neg, not a need to reimpose p<=q merely to derive the signed formula. A violating sign would be a counterexample to that enclosure route, not automatically to candidate optimality. No such sign is claimed without proof.

These are written pen-and-paper arguments with self-review. No CI, Lean/Lake compilation, numerical experiment, computer algebra, or manuscript build was used.
