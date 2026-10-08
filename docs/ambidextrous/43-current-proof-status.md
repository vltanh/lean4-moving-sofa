# 43. Current proof status after the active-contact and repair calculations

**The unrestricted optimality and uniqueness problem is not closed.** This is the current ledger. Notes 7, 24, and 34 are historical snapshots. In particular, the unknown sign recorded in Notes 28 and 34 for the high-curvature near-candidate family has now been resolved in Note 41.

All results are written proofs with self-review, not independent refereeing or Lean verification. The new results depend where indicated on earlier branch theorems, especially the sharp functional and Theorem 65. No novelty or priority claim is made.

## 43.1 Two complementary geometric theorems

### The global theorem on a specified curvature/contact class

[Theorem 65](31-closed-curvature-class-theorem.md) remains the branch's global area-and-uniqueness result under explicit geometric hypotheses. It applies to a normalized full-turn common hull whose curvature measure is dominated by dtheta on the open quarters and whose two contact inequalities p<=q hold. It gives

\[
|S|\leq M=1+4Y^2+\arctan Y,
\qquad4Y^3+3Y-1=0,\quad Y>0,
\]

with equality exactly for Romik's candidate. This theorem does not cover all unrestricted maximizers because its structural hypotheses have not been derived for all of them.

### A new local theorem without an input curvature cap

[Theorem 83](42-independent-arc-repairs.md) handles independent, nonsymmetric, arbitrarily oscillatory convex support perturbations of the candidate in fixed protected arc windows. The perturbations are C^1-small, supported away from axis normals and switching neighborhoods, and need not have curvature bounded by one.

An explicit convex-minorant operation raises the support on each excessive-curvature interval, repairs the curvature bound, preserves the relevant wall envelope, and accounts exactly for the changing corner area. Each nonzero repair strictly increases the actual feasible body area. The repaired body falls under Theorem 65. Hence the original body has area at most M, with equality only for the unperturbed candidate.

This is not a general Hausdorff-local optimality theorem: the protected-window and C^1 conditions remain. It is nevertheless outside the input class of Theorem 65 because the original curvature can exceed one by a fixed amount or more.

## 43.2 A previously unresolved negative family is now fully classified

The bodies S_n in Note 28 are feasible, full-turn, reflection-symmetric, have the candidate's aligned faces, and satisfy p<q, yet their curvature exceeds one on open intervals and their areas tend to M. They still refute any fixed suboptimal area-threshold version of the desired curvature reduction.

[Note 41](41-resolving-the-high-curvature-family.md) now proves the additional conclusion

\[
\boxed{|S_n|<M\quad\text{for all sufficiently large }n.}
\]

The proof does not estimate their areas numerically. It constructs a strictly improving feasible repair and bounds the repaired body by M. Thus this family is not a counterexample to candidate optimality, and the old "sign not determined" statements are superseded.

## 43.3 What the repair actually does

For a first-quarter wall use

\[
s=-\cot t,\qquad\phi(s)=(1-f(t))/\sin t.
\]

Then phi''=(1-rho_f)sin^3(t). Replacing phi by its greatest convex minorant produces f_c>=f with 0<=rho_f,c<=1. The supremum of the R wall-height family is unchanged, while the other contact path D is fixed algebraically.

It would be wrong to infer that the entire niche is unchanged: the corner graph moves. For a one-half repair u=f_c-f in the standard middle regime, the exact actual-area gain is

\[
\Delta |E|=\int(1-q-u)u+\tfrac12\int u'^2.
\]

For a g repair the corresponding expression is integral (1+p-v)v plus one half of integral v'^2. In a protected side-only regime there is no corner cost, and the gain is integral (1-w/2)w plus one half of integral w'^2.

The candidate has strict margins q<1 and p>-1 in the relevant middle windows. These formulas therefore yield a positive gain there. The independent repairs retain the common face rectangle and keep the two niches separated. The hybrid max-min roof description is proved in Notes 41–42, not inferred solely from a one-wall convexification identity.

The resulting deficit controls the repair increments. It is not claimed to be a global distance-to-candidate stability estimate when every repair increment vanishes.

## 43.4 A regular-critical curvature calculation is also completed

[Notes 35–37](37-excluding-buried-endpoint-corners.md) give a different, maximality-based result.

A smooth active R tangency necessarily has rho_f<=1, but an inactive tangency can still contribute through its corner. At a regular critical point the correct local equations are

\[
(1+b)\rho_f=b+\chi q,\qquad
(1+d)\rho_g=d-\chi p
\]

where applicable on positive-curvature sets. Here b,d record active tangencies and chi records standard, reverse, or absent corner contact. The moving-angle derivative is included.

These equations and the strip geometry imply that an excessive-curvature interval can only reach an endpoint. The endpoint pattern would put the limiting corner strictly inside another forbidden quadrant, contradicting its actual boundary activity. Theorem 75 therefore derives the curvature cap in the stated regular critical-point model.

**Important scope limit:** Section 36.1 assumes C^2 quarter supports across the interval, stable contact charts, no omitted clipping/touching terms, and admissibility of the tested two-sided variations. The candidate itself has curvature jumps at phase joins; simply applying the smooth argument across such jumps is not justified. Neither are singular curvature measures or exposed-edge atoms covered. Thus Theorem 75 is not already a measure-level theorem for every maximizer. The geometric repair in Notes 40–42 is a separate operation and does not require the perturbed bodies to be critical points.

## 43.5 The finite-angle relaxation now has an explicit rate

[Theorem 76](38-quantitative-angle-completion.md) applies to any bounded connected sampled body, without smoothness or contact assumptions. If its canonical constraints are sampled with maximum angular gap Delta and its radius is at most R, then

\[
\frac{S}{1+R\Delta}
\]

satisfies both complete motions between the same endpoint angles. The proof keeps the exact outer support bounds and repairs the possible inner-disjunction error by a uniform scaling and explicit translations.

For the exact finite-angle maximum v_n with N=2^n, let

\[
e_n=R_B(\pi/2)/N,
\qquad R_B=\sqrt{4+2\sqrt2}.
\]

Then Corollary 77 proves

\[
\boxed{V\leq v_n\leq(1+e_n)^2V.}
\]

No v_n has been computed in this pass. The bound gives a rate for the exact variational quantities, not a claimed numerical upper bound equal to M. It fills the gaps between sampled angles, not the gap between a partial endpoint and pi/2.

[Theorem 78](39-effective-maximizer-selection.md) now selects any prescribed maximizing hull with the deterministic penalty kappa_n=N^-1/2. The hull error is explicitly O(N^-1/2). Scaling the selected polygons as above gives **genuinely full-motion feasible polygons** whose areas differ from V by O(N^-1).

The finite optimizers retain a variational error bounded by kappa_n times sampled support displacement. The scaled polygons are not claimed to be optimizers themselves. Control of the support amplification of a proposed variation remains an obligation.

## 43.6 New negative findings and failed shortcuts

- Differentiating max_t min(A_t,B_t) at the old active angle can give the wrong derivative. Note 35 gives the exact example max_t min(t+epsilon,-t)=epsilon/2; the frozen-angle rule gives zero instead.
- An active-tangency curvature test alone does not control normals whose corners remain active. The regular calculation explicitly includes them.
- Preserving the supremum of one affine wall family does not automatically preserve the complete niche. The repair proof separately verifies the min-wall roof and retains the corner-area cost.
- The finite-angle scaling repair loses area of first order in its constraint error. That loss cannot be discarded when claiming stationarity of an originally inadmissible support variation.
- The C^2 critical-point argument cannot be extended across curvature jumps, hidden atoms, or changing contact topology merely by calling them limits. Those passages remain unproved.

Earlier counterexamples remain part of the record: frozen candidate switches fail even for feasible near-candidate bodies; the raw partition functional is not concave on its entire witness relaxation; and signed corner area alone is not a niche-area bound.

## 43.7 The unrestricted gap, stated without substitution

The general reductions already prove attainment, unit-span normalization, correct-sign canonical motions, connected separated common-hull saturation, and selection of every maximizing hull. This pass adds an explicit selection rate and a regular/local curvature repair.

The remaining unrestricted structural conclusion would still need to establish, or replace with a covering sharp comparison:

1. full quarter-turn endpoints for every relevant maximizer rather than just the existing variable endpoint angles;
2. curvature-measure domination, including singular/atomic and contact-degenerate cases;
3. the two contact-order inequalities, with all required variations genuinely admissible and with errors controlled in the selected finite-angle limit.

The new local theorem does not put every maximizer in a protected candidate neighborhood. The new smooth critical-point theorem does not supply missing regularity. The quantitative repair does not eliminate the cost of infeasible variations. None of these substitutions has been made.

For optimality, a structural result for one global maximizer would suffice. Exact uniqueness requires it for every maximizer or an equality-preserving recovery argument. The selection theorem continues to target any prescribed maximizing hull for precisely that reason.

## 43.8 Self-review and execution

The review checked the sign and orientation of both corner derivatives, the reverse-corner strip bounds, and the endpoint Taylor coefficients. It checked the upper-hallway translation in the finite-angle repair separately from the lower one, and retained endpoint arm inclusions. The penalty and scaling errors are assigned to the correct unscaled/scaled bodies.

For the convex-minorant repair, endpoint gluing, nonnegative repaired curvature, C^1 control, and equality of the one-wall suprema are proved. The actual two-wall roof is checked independently. The hull-area change and corner-area change are subtracted before any positivity claim; the independent g repair and side-only formulas have their own signs and factors.

All new files and updates are Markdown under docs/ambidextrous. No CI was requested or used. No Lean/Lake compilation, dependency installation, numerical experiment, CAS calculation, or manuscript build was performed. Every research commit carries `[skip ci]`. The existing manuscript, Lean sources, dependencies, and workflow definitions remain unchanged. The PR remains open and draft because the unrestricted proof is not complete.
