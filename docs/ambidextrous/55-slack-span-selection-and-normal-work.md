# 55. Allowing slack span gives an admissible inward direction and a normal-work bound

The exact-span equality in the original finite selector unnecessarily excludes inward homotheties. This note removes that equality at the **selection stage**, proves a strictly clearing canonical homothety, and uses it to bound the work of the constraint normals in Theorem 99.

The conclusion is not that the normals vanish. It is a finite, uniform bound on an explicitly identified combination of them. Full-turn endpoints, the curvature cap, and contact order remain unproved for arbitrary maximizers.

## 55.1 A selector with the same limiting optimum and more admissible variations

Use the same box B, threshold A_0=8/5, endpoint range, and dyadic angular samples as in Note 32. Define F_n^le by dropping only the requirement that the body's vertical span be **exactly** one. Bodies must still lie in B, whose vertical coordinates run from zero to one, and must obey the sampled canonical hallways and outgoing width bounds. In particular their incoming vertical span is at most one.

**Proposition 101 (slack-span selection).** The compactness, finite-value convergence, deterministic-penalty selection, and error estimates of Notes 32, 38, and 39 hold for this enlarged class, with its own finite upper values v_n^le. Every prescribed normalized maximizing hull can still be selected.

**Proof.** The new span condition is closed (and is already implied by the box), so the compactness proof is unchanged. Every genuinely feasible normalized competitive body still belongs to every finite class. A compact limit satisfying the dense canonical constraints and endpoint widths is an unrestricted feasible body: exact span is not required for the endpoint-arm lemma or the canonical motion. Thus the finite maxima decrease to the same unrestricted value V.

The scaling repair of Theorem 76 requires width at most one, not equality; it therefore gives the same inequality v_n^le<=(1+e_n)^2 V and the same explicit relaxation error. The zero-penalty target comparison and the sampled-support Lipschitz estimate are unchanged. Finite-envelope component saturation preserves all recorded supporting heights, including both vertical normals, so it preserves the relaxed span condition. Consequently the polygonal selector and the estimates of Theorem 78 apply with v_n^le in place of v_n. QED.

No reorientation or subsequent restoration of span is inserted into a derivative. The limiting target hull can have span one while its finite competitors have smaller span. This avoids introducing an uncontrolled rotation just to satisfy an unnecessary equality.

## 55.2 A canonical homothety gains inner-wall clearance

Let C be a member of the slack-span finite class F_n^le, with |C|>A_0, whose canonical finite-angle envelope in K=conv(C) is C itself. In particular it satisfies the box and endpoint-width constraints. A selected saturated optimizer has these properties, because |C|>=V>=M>A_0. The correctly signed angles may be partial. Choose o in B and, for 0<s<1, put

\[
\lambda=1-s,\qquad K_s=o+\lambda(K-o),
\qquad C_s=E_n(K_s),
\]

where E_n uses the same canonical finite angles and endpoint normals as before.

**Lemma 102 (inward saturation with a clearance margin).** Under these hypotheses, for all sufficiently small positive s, C_s is an admissible slack-span finite competitor, has convex hull K_s, and

\[
o+\lambda(C-o)\subseteq C_s,
\qquad |C_s|\geq\lambda^2|C|.
\tag{55.1}
\]

Every point of the smaller copy of C has clearance at least s from at least one inner-wall inequality of each sampled quadrant, in the units of its normal coordinate. In particular

\[
\bigl((o+\lambda(C-o))+sB_2\bigr)\cap K_s\subseteq C_s.
\tag{55.2}
\]

**Proof.** For an original retained point p, each canonical forbidden quadrant has at least one normal u for which p dot u>=h_K(u)-1. With p_s=o+lambda(p-o),

\[
p_s\cdot u-[h_{K_s}(u)-1]
=\lambda[p\cdot u-h_K(u)+1]+s\geq s.
\tag{55.3}
\]

Thus p_s avoids every new open quadrant, and any displacement of norm at most s still avoids at least that inner inequality. Intersect with K_s for the outer constraints. This proves (55.2) and the first inclusion in (55.1).

The smaller copy is connected and has convex hull K_s. Its horizontal projection is therefore the same interval as that of K_s. Every vertical fiber of E_n(K_s) is an interval containing a point of that smaller copy; the finite version of Theorem 26 proves that the entire E_n(K_s) is connected. Since it contains the smaller copy and lies in K_s, its convex hull is exactly K_s. All endpoint widths scale by lambda and are at most one. The box is convex and contains o, so K_s lies in B. Its area remains above A_0 for sufficiently small s because lambda squared times |C| tends to |C|>A_0. The area bound follows by containment. QED.

Taking o in the interior of B also makes all box contacts strictly slack. The proof is independent of the mesh and does not assume a differentiable boundary or strict original neck clearance. Its geometric containment and connectedness conclusions work for the complete canonical angular intervals too whenever they are already feasible, but it does not extend their endpoints.

## 55.3 No interior zero-height neck survives this saturation

Suppose K has nonempty interior. For every x strictly between the horizontal extrema of K_s, the fiber of C_s has positive length.

To prove this, choose p_s in the smaller copy of C with abscissa x. The vertical fiber of K_s at an interior abscissa is a nondegenerate interval. A small segment of that fiber lies within distance s of p_s, even if p_s is its top or bottom endpoint. Equation (55.2) retains that segment. Thus a point connection at an interior abscissa is thickened by the inward operation.

This does not prove that the **unscaled maximizer** has no pinching connection. The operation can lose area by shrinking the hull, and its quantified cost must be retained.

## 55.4 The one-sided area cost is uniformly bounded

Let C_n be a slack-span penalized selector from Proposition 101. Use o at the center of B, and denote R_n=max_{p in K_n}|p-o|, uniformly bounded by a box constant R. Along the inward saturated family, the support distance from K_n is at most sR. The finite-optimizer inequality therefore gives

\[
|C_{n,s}|-|C_n|\leq\kappa_n R s.
\]

Together with (55.1),

\[
\boxed{-2|C_n|\leq
\left.\frac{d}{ds}|C_{n,s}|\right|_{s=0+}
\leq\kappa_n R.}
\tag{55.4}
\]

The derivative exists: in the fixed finite arrangement, a short homothetic ray lies in one of finitely many polyhedral charts and the area along it is a quadratic polynomial. The lower bound also follows by a lower right derivative without using this fact.

The bound is on the saturated area's derivative, not just on the area of a smaller copy. The latter gives the lower comparison; saturation can recover some of the lost area.

## 55.5 What this controls in the multiplier equation

Use an incident chart containing that short inward ray and the exact multiplier identity (53.1). Let v be its supporting-height velocity. It preserves the chart's equality conditions; its active inequalities satisfy Dc_j[v]>=0. Taking the scalar product of (53.1) with v gives

\[
\sum_j\mu_j Dc_j[v]
=\kappa_n\sum_k\theta_kD\ell_k[v]-DF[v]
\leq\kappa_nR+2|C_n|.
\tag{55.5}
\]

Every summand on the left is nonnegative. Therefore any specified group of rows normalized so that Dc_j[v]>=a>0 satisfies

\[
\sum_{j\text{ in that group}}\mu_j
\leq\frac{2|C_n|+\kappa_nR}{a}.
\tag{55.6}
\]

For example, a retained-vertex clearance

\[
c(z)=P(z)\cdot u-h_{K(z)}(u)+1
\]

has Dc[v]=1 when it is zero, because the polygon vertex and its supports undergo the same homothety; this is (55.3). An active terminal-width slack 1-w_K(u) likewise has inward derivative one. These normalized rows cannot carry unbounded total multiplier mass in this representation.

The formula is deliberately called a **normal-work bound**, not a bound for every individual chart multiplier. Rows with Dc_j[v]=0, including some incidence bookkeeping equalities/inequalities, are not controlled by (55.5). Nor does bounded positive mass imply that the mass tends to zero. Neck-gap rows need their own normalization and analysis before assigning them a uniform a.

## 55.6 Exact consequence for the global program

The finite selector can now be chosen so that a canonical inward variation is genuinely admissible, removes interior zero-width necks, retains its hull, and has a controlled first-order cost. It also supplies a nontrivial bound on selected constraint multipliers. This is more than declaring an arbitrary support perturbation admissible by a formal smoothing step.

However, the cost in (55.4) is of order s, not o(s). It cannot be discarded to conclude unconstrained stationarity at the original selector. The unrestricted curvature/contact theorem still requires eliminating or exploiting the remaining normal terms, and the endpoint-angle argument is separate. No claim of global optimality or uniqueness is made here.

All arguments are pen-and-paper; no CI, Lean, numerical experiment, or computer algebra was used.
