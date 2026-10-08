# 56. An atom-rounding improvement at a general maximizer, away from actual obstructions

This is a maximizer-specific geometric step, not another comparison restricted to a candidate neighborhood. It needs no smoothness or curvature cap on the original hull, and the two motions may have partial endpoints. It proves that a certain exposed-edge atom cannot occur at a global maximizer.

Its two remaining geometric qualifications are explicit: a subsegment of the exposed edge must be strictly clear of the swept niches, and the surviving fibers near the affected corner abscissa must have positive clearance. Masked/coincident edges and pinching configurations are not covered. These are precisely the kinds of constraints retained by the finite normal-cone calculation.

## 56.1 A short circular replacement around any curvature atom

Let h be the support function of a compact convex body and suppose its curvature measure sigma=h+h'' has an atom of mass m>0 at an interior angle t_0. Choose epsilon>0 sufficiently small that J=[t_0-epsilon,t_0+epsilon] is in the desired open angular interval and

\[
2\varepsilon<\pi,\qquad \varepsilon<\pi/4,
\qquad m>2\sin\varepsilon.
\]

On J let f_c solve

\[
f_c''+f_c=1,
\qquad f_c(t_0\pm\varepsilon)=h(t_0\pm\varepsilon).
\tag{56.1}
\]

Leave h unchanged outside J and denote the resulting periodic function by h_c. Put u=h_c-h.

**Lemma 103 (convex outward replacement).** The function h_c is a convex-body support function, u>=0, and u is zero outside J. The input may have other atoms or singular-continuous curvature in J. As epsilon tends to zero,

\[
u(t_0)=\frac m2\varepsilon+o(\varepsilon),
\qquad\|u\|_\infty=O(\varepsilon),
\]

\[
f_c'(t_0)=\frac{h'_-(t_0)+h'_+(t_0)}2+o(1).
\tag{56.2}
\]

**Proof.** On J the difference satisfies, distributionally,

\[
(-d^2/dt^2-1)u=\sigma-dt,
\qquad u=0\text{ at the endpoints}.
\]

The Dirichlet Green kernel of this operator on an interval of length less than pi is positive:

\[
G(t,s)=\frac{\sin(t_<-a)\sin(b-t_>)}{\sin(b-a)},
\quad a=t_0-\varepsilon,\ b=t_0+\varepsilon.
\]

This follows by solving the homogeneous equation on either side of s and giving the derivative a jump of -1. Since sigma>=m delta_{t_0}, u is bounded below by the solution with that one atom in place of sigma. Writing r=t-t_0, that solution is

\[
v(r)=\frac{\cos\varepsilon-\cos r+(m/2)\sin(\varepsilon-|r|)}{\cos\varepsilon}.
\]

For 0<=|r|<=epsilon,

\[
\cos r-\cos\varepsilon
\leq\sin\varepsilon\,\sin(\varepsilon-|r|).
\]

This is the sine-subtraction identity, or follows by dividing the two half-angle formulas. Thus v>=0, strictly in the interior under the displayed choice of epsilon, and u>=0.

On the open replacement interval the new curvature is dt. At the left endpoint, u=0 and u>=0 imply u'_+>=0; at the right endpoint u'_-<=0. Consequently gluing f_c to h only adds nonnegative derivative jumps, in addition to any old endpoint atoms. Outside J the curvature is unchanged. The full curvature measure of h_c is therefore nonnegative, and the supporting-half-plane construction used in Lemma 43 gives a compact convex body K_c with this support. Since h_c>=h, K is contained in K_c.

For the asymptotics, write H=h(t_0), a_-=h'_-(t_0), a_+=h'_+(t_0), with a_+-a_-=m. The endpoint expansions are H-a_- epsilon+o(epsilon) and H+a_+ epsilon+o(epsilon). The solution is 1+A cos(r)+B sin(r), with

\[
A=\frac{h(t_0-\varepsilon)+h(t_0+\varepsilon)-2}{2\cos\varepsilon},
\quad B=\frac{h(t_0+\varepsilon)-h(t_0-\varepsilon)}{2\sin\varepsilon}.
\]

These give (56.2). They also bound f_c and its derivative uniformly on J, using the Lipschitz bound for h, and hence give the stated uniform O(epsilon) difference. QED.

The replacement generally creates two new endpoint atoms. It is **not** a map into the curvature-dominated class. Its purpose here is an infinitesimal area improvement, not completion of the whole structural reduction.

## 56.2 The one-wall envelope is exactly preserved

Work first on an interior first-quarter interval of a lower canonical turn, so f(t)=h(t) is replaced and g(t)=h(t+pi/2) is unchanged. The two roof lines are

\[
R_t(x)=\frac{f(t)-1-x\cos t}{\sin t},
\qquad L_t(x)=\frac{g(t)-1+x\sin t}{\cos t}.
\]

The replacement f_c=1+A cos(t)+B sin(t) makes R_c an affine function of s=-cot(t), for each fixed x. Since f_c>=f and the endpoint values agree,

\[
\sup_{t\in J}R_t(x)
=\sup_{t\in J}R_{c,t}(x)
=\max\{R_a(x),R_b(x)\}.
\tag{56.3}
\]

Indeed R_c>=R, an affine function attains its maximum over the s-interval at an endpoint, and both old endpoint values are still present. The L family is unchanged. This alone does not say that the **minimum of the two walls** is unchanged.

## 56.3 All niche change is confined to a narrow corner band

Let

\[
c_x(t)=(f(t)-1)\cos t-(g(t)-1)\sin t,
\]

and let c_{c,x} be its replacement. Let I_epsilon be the smallest interval containing both functions' ranges on J. Their common limiting center is x_0=c_x(t_0). Since support functions are Lipschitz, (56.2) gives

\[
I_\varepsilon\subseteq[x_0-C\varepsilon,x_0+C\varepsilon]
\tag{56.4}
\]

for a fixed constant C depending on the original hull and t_0, not on epsilon.

**Lemma 104 (quadratic niche-area cost).** The old and new complete lower swept roofs agree outside I_epsilon. Inside it their difference is nonnegative and O(epsilon), uniformly in x. In any fixed vertical strip, the possible loss of previously surviving body area is therefore O(epsilon squared).

**Proof.** The identity

\[
R_t(x)-L_t(x)=\frac{c_x(t)-x}{\sin t\cos t}
\]

holds for both supports. To the left of I_epsilon, the minimum on J is L throughout, hence is unchanged. To its right, the minimum on J is R throughout; equation (56.3), including the same endpoint values, shows that its supremum is unchanged. Outside J all constraints are unchanged. Taking the supremum over the full motion interval proves roof equality outside I_epsilon.

Within the band, raising f can only raise min(R,L), by at most ||u||_infinity/min_J sin(t)=O(epsilon). Supremum preserves this estimate. The band's width is O(epsilon), proving the area estimate by vertical integration. This does not require a differentiable roof, a unique active angle, or a fixed contact pattern. QED.

For a second-quarter g replacement, use s=tan(t): the L family becomes affine, R is unchanged, and the same proof exchanges the left and right cases. Reflection gives the upper-turn versions. Only one support window is changed; no symmetric competitor is assumed.

## 56.4 A strict exposed-edge gain has first order

Let the edge at normal t_0 have endpoints

\[
P_-=H\mu_{t_0}+a_-\nu_{t_0},\qquad
P_+=H\mu_{t_0}+a_+\nu_{t_0},
\]

of distance m. By (56.2), K_c has a support point with outward displacement (m/2)epsilon+o(epsilon) from the old edge and tangential coordinate approaching its midpoint. The convex hull of this point with the old edge is contained in K_c.

Consequently, above **any fixed compact subsegment of the relative interior of that edge**, this triangle contributes an area at least c epsilon outside K, for some c>0 and all sufficiently small epsilon. This follows from the elementary linear height profile of a triangle: away from its two base endpoints, its height is a fixed positive fraction of the apex height. Its apex stays away from those base endpoints.

Suppose such a subsegment is disjoint from the closures of both original swept niches. It then has a positive distance from those closed sets. Choose a smaller subsegment whose x-projection stays away from x_0; this is possible because t_0 is away from the axis normals, so its edge has a nonzero horizontal projection. For small epsilon, the added thin triangular portion is still clear of the old niches, and its x-projection is outside I_epsilon. Lemma 104 says the changed niche is identical there, and the opposite-turn niche is unchanged. The whole added portion survives.

Thus there is a retained area gain c epsilon, while the total possible loss from the old body is at most C' epsilon squared.

## 56.5 The admissibility hypothesis and the maximizer conclusion

Let S be a saturated canonical envelope with hull K, for two correctly signed motions (possibly partial). Require that J avoid every incoming and outgoing strip normal as well as the axis normals, so all endpoint widths are unchanged by the replacement.

Assume either the corner abscissa x_0 has positive distance from the horizontal projection of K, or there are a neighborhood U of x_0 and a number eta>0 such that every old surviving fiber over x in U intersect proj_x(K) has length at least eta.

This is a **geometric clearance condition on S**, not proximity to Romik's candidate.

**Theorem 105 (atomic improvement without candidate proximity).** Under that clearance condition and the strictly clear exposed-edge condition of Section 56.4, S is not a global area maximizer. The replacement gives a compact connected feasible body S_epsilon, with the same endpoint angles, such that

\[
|S_\varepsilon|-|S|\geq c\varepsilon-C'\varepsilon^2>0
\]

for sufficiently small positive epsilon.

**Proof.** Let S_epsilon be the full envelope inside K_c using its canonical placements at the same angular intervals. Outside I_epsilon the old surviving fibers are retained because K_c contains K and the roofs there are unchanged. If the band meets the old projection, its old fiber gap is at least eta; the lower roof rises by only O(epsilon), the upper niche is unchanged, and the outer hull has enlarged. Thus its new fibers remain nonempty for small epsilon. The x-extrema of K are unchanged because the support modification vanishes near the horizontal normals. Every fiber over that same projection is therefore a nonempty interval, so compactness and the interval-fiber argument give connectedness.

The defining supporting hallways contain the new body throughout both old motion intervals. All endpoint strip widths are unchanged; hence it is feasible for those complete motions. It need not retain K_c as its actual hull, and no such assertion is needed for this area comparison. Section 56.4 supplies the positive first-order added region, and Lemma 104 bounds all old-area loss quadratically. This proves the strict improvement. QED.

A nonsaturated global maximizer can first be replaced by its same-hull canonical saturation of equal area, using the established reduction. Thus the conclusion applies to the hull of any global maximizer whenever the two explicitly stated clearance conditions hold.

If the atom's normal is not used by any inner wall and is not pinned at an endpoint, the inner sweeps do not change at all. A strictly clear edge subsegment then gives the same improvement without a corner-band clearance assumption.

## 56.6 Precise scope of the progress

The theorem proves a structural exclusion at **arbitrary** maximizers, including partial-turn ones, with no assumed smoothness and no candidate contact ansatz. It is different from the protected-candidate repair in Notes 47–48.

It does not yet exclude an atom whose edge is fully masked or has only coincident niche contact, or whose affected corner band contains a pinching connection. These are not suppressed as negligible because they have zero area: the finite normal-cone calculation shows why their first-order feasibility restrictions can matter. Nor does this operation address diffuse curvature above one, singular-continuous curvature, the contact-order inequalities, or completion of partial endpoint angles.

The sign separation is the useful new mechanism: the clear exposed-edge gain is first order in the angular window, while the moved corner removes only a second-order amount of area. The operation was performed on the actual nonsmooth support and checked against both complete motions, not justified by an unproved smooth approximation.

No CI, Lean, numerical experiment, or computer algebra was used. The result is a written pen-and-paper proof subject to independent review.
