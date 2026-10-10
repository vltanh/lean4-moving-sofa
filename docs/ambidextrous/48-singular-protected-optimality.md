# 48. Protected local optimality for arbitrary convex support measures

The local theorem now permits singular curvature and uses only uniform support proximity. It is still restricted to angular windows fixed away from the axis normals and switching neighborhoods. This distinction from unrestricted Hausdorff-local optimality remains explicit.

The proof below extends Theorem 83 rather than assuming that smooth approximants are feasible or critical. Every repair is performed on the actual input support function and its actual curvature measure.

## 48.1 The geometric neighborhood

Fix the finite smaller/buffer window pairs of Section 42.4. Each buffer lies strictly inside one candidate phase and away from 0,beta,b=pi/2-beta,pi/2. The reference wall obstacle is strongly convex on each buffer where nonzero perturbations are possible.

Let h be the support function of a compact convex body K. Assume

\[
h=h_*\quad\text{outside the smaller windows},\qquad
\|h-h_*\|_\infty\text{ is sufficiently small}.
\tag{48.1}
\]

The four open quarters may be changed independently. No smoothness, absolute continuity, or upper bound is imposed on the input curvature measure sigma_K=h+h''. The support of a convex body is Lipschitz; its derivative has bounded variation locally, and sigma_K is nonnegative.

Perturbations supported strictly in a zero-curvature phase vanish by Section 47.5. On all remaining windows, Lemma 90 makes both derivative traces uniformly close to their candidate values. Thus all the strict inequalities used in Section 42.4 persist, even at derivative jumps:

- the applicable signs p<0 or q>0 on changed contact windows;
- the strict B_x and D_x bounds separating the side envelopes from the middle graph;
- a strictly negative middle c_x derivative;
- positive corner heights below the midline and baseline intercepts strictly inside the common face interval.

The values and derivative traces at all axis normals are unchanged. Hence the top and bottom exposed faces remain the candidate interval [ell,r], of length 4A/3>1. Convexity puts the entire rectangle [ell,r] times [0,1] inside K.

## 48.2 The two-wall roof remains the verified hybrid roof

The proof in Section 41.3 can be made directly with these nonsmooth inputs.

**Middle graph.** The corner c is Lipschitz. Its almost-everywhere derivative satisfies c_x'=p cos(t)-q sin(t)<=-kappa<0 on [beta,b], for a fixed kappa after reducing the neighborhood. Hence c_x has a Lipschitz inverse on this interval. The inequalities D_x<=x_b for parameters up to b and B_x>=x_a for parameters from beta onwards hold for both derivative traces. The wall-height derivatives in (35.1) therefore have the required signs almost everywhere. Since the wall heights are absolutely continuous on compact interior parameter intervals, integrating those signs proves exactly the same middle max-min comparison as before.

**Side envelopes.** On the right portion, the R supremum is attained at an interior parameter in [beta,pi/2]. At a possible nondifferentiable maximum, semiconvexity of R as a function of its parameter gives left derivative <= right derivative. The local-maximum inequalities give the reverse ordering around zero. Both derivatives are therefore zero. This identifies x=B_x at that parameter and supplies p<0, so the companion wall does not cut off the maximum. Thus the actual right roof is the R supremum even when the input has curvature atoms. The left argument uses L, q>0, and D_x in the same way.

Semiconvexity here follows from sigma_f>=0 or sigma_g>=0: after division by a positive sine/cosine on a compact window, the distributional second derivative has a nonnegative singular part and a bounded-below density. Outside the perturbed windows the reference argument applies. Endpoint and switching neighborhoods are unchanged.

**Outside the face interval.** The same one-sided B_x,D_x bounds prove that no positive niche extends beyond [ell,r]. Corner-height and baseline-intercept margins confine the lower sweep above the baseline to the retained rectangle below y=1/2; the upper sweep is handled independently in reflected coordinates and stays above y=1/2.

It follows that the canonical envelope E_h is compact, connected, feasible for both full turns, and retains the whole hull K. Its vertical fibers have a uniform gap around the midline in the central rectangle. Outside that rectangle the convex flanks and all extreme points survive. No input curvature cap was used to establish this geometry.

## 48.3 Direct measure-level area accounting

Repair each nontrivial window by Lemma 91, successively. A repaired global support function remains convex: its curvature measure is nonnegative everywhere, with unchanged endpoint neighborhoods. The supporting-half-plane proof of Lemma 43 extends using the measure variation-of-constants formula, or equivalently one checks the same inequalities with the one-sided support derivatives. Thus the intended repaired support values are attained, not merely imposed as redundant half-plane bounds.

Every interpolation in an individual repair is a convex combination of its two support functions. Lemmas 90–91 ensure that the finite sequence and its interpolations remain in the same protected geometric neighborhood. Their envelopes are therefore genuinely feasible by Section 48.2.

For a first-wall increment u=f_c-f, expansion of the support-area integral gives the one-half hull gain

\[
\int u\,d\sigma_f+\frac12\int(u^2-u'^2)\,dt.
\tag{48.2}
\]

On a middle window the corner curve is Lipschitz with strictly monotone abscissa. Its area can be integrated by its signed determinant, or by horizontal slicing and change of variables. Direct integration by parts for the absolutely continuous coordinates gives niche gain

\[
\int qu\,dt+\frac12\int u^2\,dt.
\]

The R supremum is unchanged by convexification and D depends only on g, so these are all changing niche terms. Substitute the measure identity (47.4) in (48.2) and subtract. The actual one-half gain is

\[
\Delta|E|=\int(1-q-u)u\,dt+\frac12\int u'^2\,dt.
\tag{48.3}
\]

The g-window gain is integral (1+p-v)v plus one half of integral v'^2. On a side-only window the gain is integral (1-w/2)w plus one half of integral w'^2, with no corner term. Thus all formulas (42.2)–(42.4) remain valid, including singular curvature mass through (48.2).

No derivatives of curvature measures or omitted jump terms are involved: the only measure pairing is explicitly retained and evaluated by (47.4).

## 48.4 The extended theorem

**Theorem 92 (protected uniform-support optimality with singular inputs).** There is a uniform support neighborhood in (48.1) such that every convex h in it has

\[
|E_h|\leq M,
\]

with equality exactly when h=h_*. If w_j are the nonnegative successive repair increments, then for a constant c>0 depending only on the fixed reference windows,

\[
M-|E_h|\geq\sum_j\left(c\int w_j\,dt+
\frac12\int w_j'^2\,dt\right).
\tag{48.4}
\]

In particular, any nonzero singular curvature measure in these windows makes the body strictly suboptimal.

**Proof.** Candidate margins q_*<1 and p_*>-1 in the middle windows, together with the trace estimates and small repair size, make all the coefficients in Section 48.3 uniformly positive. Sum the actual area gains. The final support has curvature measure dominated by dt on every open quarter and retains p<q for both halves, by uniform trace closeness and the candidate's positive contact gap. Its feasible envelope therefore falls under Theorem 65.

If any repair is nonzero its positive increment integral makes the gain strict. If every repair vanishes, the original support already satisfies that theorem. Equality forces a horizontal translate of h_*, and the unchanged axis support values force the translation to be zero. Conversely h_* gives the candidate of area M.

Any original singular curvature in a window prevents measure domination there and therefore forces a nonzero repair by Section 47.4. QED.

## 48.5 This also applies to originally unrestricted motions with these hulls

Let S be any compact connected ambidextrous body whose hull support satisfies (48.1), without assuming that its original witnesses were full turns. If |S|<=sqrt(2), the desired bound is already strict. Otherwise use the general canonical angle reduction. Because the hull retains the rectangle [ell,r] times [0,1] with r-ell>1, its width in a direction (cos theta,sin theta) is at least

\[
(r-\ell)|\cos\theta|+|\sin\theta|>1
\quad\text{for }|\theta|<\pi/2.
\]

The strict inequality follows from concavity of the displayed expression on [0,pi/2] and its endpoint values r-ell>1 and one. Thus an outgoing unit strip in the reduced angular range is possible only at an endpoint magnitude pi/2. The wrong-sign theorem selects the conventional signs for this area. Hence S is contained in E_h and Theorem 92 bounds its area.

At equality E_h is the candidate, and its regular closedness plus containment and equal area give S=E_h by Lemma 4.

The remaining locality restriction is important: (48.1) fixes entire neighborhoods of the axis and switching normals. It does not place an arbitrary maximizing hull in this neighborhood, and it does not establish a global curvature theorem. It does remove input smoothness, C¹ proximity as an assumption, and the exclusion of singular curvature from the previously proved protected-arc result.
