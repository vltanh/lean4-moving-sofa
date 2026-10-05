# 20. Face alignment is forced in the regular contact class

The explicit face-alignment assumption in Theorem 44 can be removed. This note derives it from feasibility, the common-hull property, and the other curvature/velocity hypotheses. Consequently the clipping terms in Note 17 vanish automatically in that class.

This closes a real geometric gap within the restricted program; it does not prove that every unrestricted optimizer has the curvature and velocity properties used here.

## 20.1 Extreme points of the hull must belong to the body

**Lemma 45 (extreme-point retention).** If S is compact in the plane and K=conv(S), every extreme point of K belongs to S. In particular the two endpoints of any nondegenerate exposed face of K belong to S.

**Proof.** Every point of conv(S) is a finite convex combination of points of S. If the point is extreme, every point with positive coefficient in that combination must equal it; hence it belongs to S. An endpoint of an exposed face is extreme in that face and therefore extreme in K: any segment of K having that endpoint as an interior point would lie in the same supporting line, contradicting extremality within the face. QED.

Thus it is not enough for an envelope to be feasible and have positive area. When K is asserted to be its convex hull, no extreme point of K can have been removed by an open forbidden sweep.

## 20.2 The two exposed-face intervals necessarily overlap

Suppose h_K and h_K^rho satisfy the regularity, curvature, and velocity conditions of Section 18.1, without assuming face alignment. Let

\[
I_t=[\ell_t,r_t],\qquad I_b=[\ell_b,r_b]
\]

be the horizontal intervals of the top and bottom faces. Let x_max=h_K(0), which is unchanged by rho.

For the upper half, the outer support point A(t)=f(t)mu_t+f'(t)nu_t has

\[
A_x(0)=x_{\max},\quad A_x(L)=r_t,
\quad A_x'=-\rho_f\sin t.
\]

Therefore the strict curvature bound gives

\[
x_{\max}-r_t=\int_0^L\rho_f\sin t\,dt<1,
\qquad r_t>x_{\max}-1.
\tag{20.1}
\]

The endpoint velocity sign gives

\[
q(0)=g'(0)+f(0)-1=x_{\max}-1-\ell_t>0,
\qquad \ell_t<x_{\max}-1.
\tag{20.2}
\]

Apply the same two equations to rho K, whose top face is the original bottom face. The result is

\[
\boxed{x_{\max}-1\in\operatorname{int}I_t\cap\operatorname{int}I_b.}
\tag{20.3}
\]

In particular the two intervals cannot be disjoint or merely touch. This argument does not use a lower bound on the horizontal width, an area threshold, or reflection symmetry.

## 20.3 Feasibility rules out unequal overlapping intervals

**Theorem 46 (forced alignment).** Let S be compact and connected, K=conv(S), and suppose its two canonical full quarter-turn motions are feasible. Assume all the regularity, curvature, and velocity hypotheses of Section 18.1 except face alignment. Then

\[
I_t=I_b.
\tag{20.4}
\]

**Proof.** Theorem 41 says that the lower sweep has strictly positive profile height at every x in the interior of I_t. Consequently every baseline point (x,0) with x in int(I_t) lies in that open sweep and cannot belong to S. By Lemma 45, both endpoints (ell_b,0) and (r_b,0) of the bottom exposed face belong to S. Hence neither endpoint of I_b lies in int(I_t).

Apply the same argument to rho S: neither endpoint of I_t lies in int(I_b). But (20.3) supplies a point in both interiors. Two closed nondegenerate intervals with overlapping interiors, and with no endpoint of either interval in the other's interior, must be equal. For example, if their left endpoints differed, the larger left endpoint would lie in the other interval's interior; equality of left endpoints followed by unequal right endpoints gives the same contradiction on the right. Thus I_t=I_b. QED.

The use of strict positivity in the profile theorem is important: zero-area or boundary-only contact would not by itself exclude an extreme point. Here the point lies in an open forbidden quadrant, so it is genuinely infeasible.

## 20.4 An enlarged completed theorem

Let R_0 be the class obtained from R in Section 18.1 by deleting condition 4, the explicit alignment hypothesis. All other conditions remain, including full quarter turns, piecewise regularity, curvature densities below one, and the monotone ordered velocities.

**Corollary 47 (optimality and uniqueness on R_0).** For every S in R_0,

\[
|S|\leq M,
\]

with equality exactly for bodies congruent to Romik's candidate Sigma_*. This class does not assume symmetry, aligned faces, or fixed contact switches.

**Proof.** Theorem 46 supplies alignment, so S belongs to R and Theorem 44 applies. The candidate belongs to the class by the explicit verification in Note 18. QED.

In particular, for every viable common hull in R_0 the exact area of its full saturation is the adaptive functional, not that functional plus an uncontrolled clipping term:

\[
|E_K|=\widetilde{\mathcal Q}(h_K).
\]

## 20.5 What this does and does not repair

The clipping formula (17.11) is correct as a general identity. What changes is that its positive correction cannot occur for a **feasible common hull satisfying both sets of regular contact hypotheses**. A convex test function or independently chosen outer hull may fail the extreme-point-retention condition and need not enjoy this conclusion.

The remaining unrestricted reduction must still address partial turning angles and establish, or replace, the regularity/curvature/velocity conditions. Alignment is no longer a separate missing hypothesis once those conditions are available. This update should prevent the older ledger's alignment obstacle from being mistaken for an unresolved issue inside R_0.
