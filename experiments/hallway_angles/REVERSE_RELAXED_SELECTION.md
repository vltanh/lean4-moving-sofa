# A reverse-cap relaxation with admissible finite variations

**Analytic proof draft.** This supplies a variational domain for the discrete estimates without pretending that arbitrary perturbations preserve connected sofa feasibility. It does not use the desired all-obtuse optimality conclusion. Its compactness, support-interpolation, and first-variation details remain explicit review targets. No CI or Lean build is used.

Fix 0<e<pi/2 and an actual strip height 0<w<=1. Use the reverse normals n_+(s)=(sin s,cos s), n_-(s)=(sin s,-cos s). A right cap is the intersection of the strip [-w/2,w/2] with its supporting half-planes at these normals for 0<s<=e. It is unbounded to the LEFT. Its right boundary is a concave graph x=F(y). The two support profiles are h_+,h_- and h_+(0)=h_-(0)=w/2.

## 1. Define the objective before using feasibility

For 0<phi<e, psi=e-phi, put

    B_phi(y)=min{[h_+(phi)-1-y cos phi]/sin phi,
                  [h_-(psi)-1+y cos psi]/sin psi},
    B_h(y)=sup_(0<phi<e) B_phi(y).

Define the signed cap/niche objective

    J_w(h)=integral_(-w/2)^(w/2) [F(y)-B_h(y)]dy.       (1)

The integrand need not be nonnegative for a general relaxed cap. No feasibility or connectedness of {B_h<=x<=F} is imposed. This is deliberate.

For an ACTUAL compact connected reverse sofa S of actual height w, canonicalization is feasible at every phi. Every horizontal fiber is nonempty, because the vertical projection of a connected compact set is the full interval. Each such fiber is contained in [B_h(y),F(y)], with h the actual hull supports. Hence

    area(S)<=J_w(h).                                   (2)

Thus an upper bound on the relaxed objective suffices for the sofa problem. We do not need to vary the original feasible sofa or preserve its connectedness during relaxation.

For regular profiles the cap integral in (1) is exactly the quadratic cap expression in REVERSE_CAP_AREA.md. We use that expression on the H^1 completion described below.

## 2. A priori bounds and a suitable completion

Let s=sin(e/2), c=cos(e/2), and let C_mid=(X,Z) be the canonical corner of the two midpoint supports. The actual support relation in a height-w strip gives |Z|<=w/2. At the midpoint,

    B_mid(y)=X-(c/s)|y-Z|,
    F(y)<=B_mid(y)+1/s.                                (3)

Therefore J_w<=w/s, independently of the cap's horizontal extent. Normalize X=0 for the existence argument.

Equation (3) bounds the cap to the right by a constant depending only on e,w. A support point at either midpoint normal has both coordinates bounded, since its support value is 1+-cZ and its ordinate lies in the strip. Its projections give a uniform lower bound for every active support value. Thus |h_+|,|h_-|<=H_e,w. Moreover B_h>=B_mid gives a uniform lower bound for the niche integral. The opposite estimate B_h<=X_max follows from h_+(phi)<=X_max sin phi+(w/2)cos phi and w<=1, and its lower counterpart. Hence B_h is bounded throughout the strip.

The cap identity has the form

    Cap(h)=1/2 integral(h_+^2+h_-^2-h_+'^2-h_-'^2)
                  +a fixed quadratic expression in h_+(e),h_-(e).

Consequently a positive lower bound on J_w gives a uniform H^1 bound on both profiles. The constants may depend on this FIXED e and w. No uniform compactness as e tends to pi/2 is needed.

Take the H^1 closure of these compatible right-cap profiles, with the fixed strip traces and X=0. The profile class is convex under addition of support functions and scaling by nonnegative weights with sum one: the associated Minkowski combinations have the same vertical span, and the same allowed normal arcs and complementary vertex gap. Its norm closure is therefore weakly closed. Bounded sequences have weak H^1 and uniform subsequential limits.

An intermediate limit may fail to attain its topmost ordinate at a finite abscissa. This is permitted in the completion; it is not silently called a compact convex body. At every strictly positive active normal its contact point remains bounded, so the limiting profile is the actual support of the corresponding right cap there. The later curvature argument restores finite endpoint derivatives and endpoint contacts.

For completeness, the cap identity still represents integral F on this completion. Circumscribe by nested finite normal fans and use the limiting support values. On an active normal cell the circumscribed support is the sine interpolation of its endpoint values. Such interpolation converges strongly in H^1 to any H^1 profile as the mesh vanishes; this follows by comparison with piecewise-linear H^1 interpolation and the uniformly O(delta^2) difference of their shape functions. The right boundaries decrease pointwise to F in the open strip. They have the fixed midpoint upper bound in (3). Monotone convergence applied to that bound minus the boundaries, together with the strongly converging quadratic identity, gives the claimed integral formula and finiteness.

## 3. The relaxed maximum is attained

Cap is weakly upper semicontinuous: the support L2 and trace terms converge, and the derivative-square terms have the negative sign. For the niche, every fixed interior angle yields a continuous affine/minimum expression under uniform support convergence. Taking the supremum gives pointwise lower semicontinuity of B_h. Its uniform midpoint lower bound permits Fatou's lemma. Thus J_w is upper semicontinuous on every bounded positive superlevel set.

There is a positive competitor: uniformly scale the explicit reverse sofa to height w, use its actual hull supports, and apply (2). It follows that the relaxed maximum is positive. The bounds of Section 2 and weak compactness then give an attained maximizing profile h_*.

This is attainment in the relaxed support space, not an assumption that an arbitrary cap-minus-niche set is a feasible connected sofa.

## 4. Persistent penalties select a specified relaxed maximizer

Use nested equally spaced dyadic fans, containing phi=e/2 at every stage and both terminal normals e. Define J_n by the actual finite right cap minus the finite supremum of the sampled B_phi. Include endpoints when convenient; their forbidden wedges miss the strip and do not change that supremum. The midpoint estimate still gives J_n<=w/s.

Enumerate the active sampled supports by first occurrence, with positive persistent weights whose sum is at most one. For a fixed maximizing target h_* set

    P_n(h)=sum_(j<=n) weight_j |h(t_j)-h_*(t_j)|^2.

The two midpoint observations retain positive weights. If J_n-P_n is at least a fixed positive recovery value, then P_n is bounded, so those observations bound X and Z without imposing a horizontal normalization on the finite variation. The arguments of Section 2 again give bounded support values and a uniform H^1 bound. At fixed n, these bounds make the finite supporting-height superlevel set compact. Its objective is continuous, including zero-length facets, so J_n-P_n has an exact maximizer.

The circumscribed target polygon has the same supports as h_* at the sampled normals, hence penalty zero, larger cap area, and no larger sampled niche envelope. It is a recovery competitor with J_n>=J_w(h_*).

For a selected sequence, weak H^1 cap upper semicontinuity and persistent dense-angle witnesses give

    limsup J_n(h_n)<=J_w(h_limit).

A nearby angle from one fixed coarse fan suffices for each strict niche witness; that angle remains in every finer fan. Comparing with the zero-penalty recovery shows P_n(h_n)->0. Every fixed positive-weight observation converges to its target value. Separation by dense support values identifies every subsequential limit with h_*. Thus h_n converges uniformly to the specified h_*, with uniform H^1 bounds.

## 5. The finite facet inequalities are admissible in this domain

Move a positive floating facet outward by distance t>0, at fixed n. The new right cap contains the old one. Every unchanged support constraint still attains its old value; the moved line retains a facet for small t. Thus exactly ONE sampled support changes by t. No feasible-sofa perturbation is being asserted.

The signed cap integral has first derivative sigma, the facet length. The finite niche supremum has first derivative tau, the length of the exposed part of that inner-wall ray within the strip. This can be seen by truncating far to the left at fixed n: both areas are finite polygon areas, the moving boundary contributes its exposed length, and vertex changes contribute O(t^2). Distinct normals do not introduce a positive-length coincident moving boundary. The truncation cancels from J_n.

Writing eta_n=max|h_n-h_*|, finite penalized maximality therefore gives

    sigma_n(t_j)<=tau_n(t_j)+2 eta_n weight_j.          (4)

For a zero-length facet the inequality is automatic. The total nonnegative error in (4) tends to zero. This supplies exactly the stationary-sequence hypothesis of REVERSE_DISCRETE_CURVATURE_REPAIR.md for the relaxed maximizer.

## 6. Regularity without presupposing bounded facet jumps

The repaired two-neighbor estimate gives at every floating normal

    sigma_n<=C_e delta_n(1+|b_n^-|+|b_n^+|)+epsilon_n.

The sampled one-sided arms have uniformly bounded weighted L2 sums. Indeed on each polygon support cell h_n''=-h_n; the endpoint derivative differs from its interior values by at most H delta_n. Thus delta_n times the squared endpoint derivative is bounded by a constant times the cell integral of |h_n'|^2 plus O(delta_n^3). Canonical corner values are bounded by the already bounded supports. Summing proves the asserted arm bound, including cells next to the endpoints.

Spread the floating curvature atoms over their adjacent cells. The resulting measures have L2-bounded majorants plus errors of total mass tending to zero. Their weak limits therefore have L2 densities on the active open arcs, with no concentration from floating atoms at either endpoint. Hence h_*'' is L2 there and its first derivative has continuous finite endpoint traces. This restores actual endpoint contacts in the completed cap.

Only now localize by arm signs as in REVERSE_DISCRETE_CURVATURE_REPAIR.md. The strip-contact inequality excludes two simultaneously nonpositive arms. The limiting local law and opposite-support inequalities then give

    0<=r_+,r_-<=1/(1-cos e).                           (5)

No isolated-tangency evaluation or assumed O(delta) facet jump is used.

## 7. Terminal facets vanish

At phi=e the other inner normal is the lower strip normal, with threshold w/2-1. Its forbidden wedge requires y>1-w/2, outside the actual strip because w<=1. Similarly the phi=0 wedge misses the strip. Thus moving either terminal outer support facet changes no sampled niche area. The finite variation argument gives

    sigma_n(terminal)<=2 eta_n weight_terminal ->0.

Endpoint derivatives pass to their one-sided limits: the floating mass within an endpoint interval of length r is O(sqrt(r))+o(1) by the L2 majorant, and the support values converge uniformly. The derivative on the complementary normal gap is determined continuously by the two terminal support values. Therefore the limiting terminal derivative jump is zero.

There are no other allowed normals between the two terminal normals. With neither terminal facet present, the two active support arcs meet the same vertex. This proves the endpoint hypothesis of REVERSE_TERMINAL_KERNEL.md for the relaxed maximizer.

## 8. What remains in this proof route

The relaxed maximizer now satisfies the global terminal identities, the curvature ceiling, and the convex integral inequalities from REVERSE_TERMINAL_KERNEL.md. A verified arm-positivity or inside-strip crossing certificate for that integral relaxation would make the old quadratic area majorant apply to this maximizer throughout the remaining obtuse range.

The passage from signed relaxed maxima to actual sofas is then the upper comparison (2), not an unproved preservation of feasible connected perturbations. Exact equality recovery still uses the existing explicit candidate and quadratic rigidity proofs. Until the remaining integral certificate is complete and the analytic argument is independently reviewed, this note is not a vetted all-obtuse optimality theorem.
