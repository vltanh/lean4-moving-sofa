# 24. Current proof ledger: completed restricted theorem, not unrestricted closure

This ledger supersedes the first-pass task list in Note 7. Earlier notes are retained as a chronological research record; later notes explicitly repair, strengthen, or reject routes proposed earlier.

**Status:** the exact quadratic/adaptive maximization problem and a geometric optimality-and-uniqueness theorem on an explicit support-function class are proved in writing. The unrestricted ambidextrous sofa problem is **not** proved in this branch. No Lean compilation, CI, numerical experiment, or computer algebra was used.

"Proved" below means a supplied pen-and-paper proof with self-review, not independent refereeing or formal verification. No priority or novelty claim is made for these results.

## 24.1 The strongest geometric theorem actually established

[Theorem 52](23-sobolev-geometric-theorem.md) applies to a compact connected body S with common hull K, normalized to vertical span one. It assumes:

- both canonical full conventional quarter-turn motions are feasible;
- on both h_K and h_K^rho, the quarter functions f(t)=h(t), g(t)=h(t+pi/2) are H^2 and satisfy

\[
0\leq f''+f<1,\qquad0\leq g''+g<1\quad\text{a.e.},
\qquad f'-g+1\leq g'+f-1.
\]

Then

\[
|S|\leq M=1+4Y^2+\arctan Y,
\qquad 4Y^3+3Y-1=0,\quad Y>0,
\]

with equality exactly for bodies congruent to Romik's candidate.

The theorem does **not** assume symmetric competitors, preselected contact switches, aligned exposed faces, ordinary monotonicity of both velocity components, or finitely many analytic pieces. Those extra assumptions were removed in Notes 16, 20, 22, and 23.

## 24.2 What is proved for arbitrary competitive bodies

For every body with area greater than sqrt(2), Notes 8–10 and 15 prove:

```text
arbitrary independent two-turn motions
  -> a common incoming pose
  -> a congruent representative of vertical span exactly one
  -> one common convex hull K
  -> canonical support-determined motions
  -> monotone angular intervals [0,alpha] and [-gamma,0]
     with 0<alpha,gamma<=pi/2
  -> disjoint lower and upper niches inside K
  -> compact connected vertically convex saturation E_K
     containing the original body and having the same hull K
  -> |E_K| = |K| - |N_-| - |N_+|
```

The wrong-sign cases have area at most sqrt(2), strictly below M. Angular backtracking and independent translation paths are therefore no longer the principal variables for competitive bodies. A single support function and two endpoint angles remain.

**Not supplied by this chain:** alpha=gamma=pi/2, or the support-curvature/contact inequalities of Theorem 52. A partial-turn endpoint still obeys only the two-strip restriction |S|<=sec(alpha) or sec(gamma), giving alpha,gamma>=arccos(1/M) at candidate area.

## 24.3 The exact functional and its equality mechanism

Put L=pi/2 and

\[
p=f'-g+1,\qquad q=g'+f-1,
\quad I(h)=\tfrac12\int_0^L\det(c_h,c_h'),
\]

where c_h=(f-1)mu+(g-1)nu. The adaptive functional is

\[
\widetilde{\mathcal Q}(h)
=|K|+I(h)+I(h^\rho)
-\frac12\sum_{j\in\{h,h^\rho\}}
\left[\int_0^L\min(p_j,0)^2+\int_0^L\max(q_j,0)^2\right]
\]

when h is a convex-body support function. In the larger function domain, |K| means its support integral rather than an assumed geometric body.

The fixed-contact Hessian has the exact sum-of-squares factorization (13.10), whose kernel is only a horizontal translation. The candidate is stationary against all normalized support variations, not just symmetric ones. Its functional value was evaluated exactly in Note 14 as cot(beta)-2+beta=M.

For the adaptive version the contact zeros move with h. The integrated deficit in Theorems 40 and 50 is a positive weighted integral of those same Hessian forms. Therefore equality still forces h=h_*+a cos(theta).

The geometric profile theorem computes the actual swept boundary from wall-envelope inequalities. Feasible common hulls retain their exposed-face endpoints, forcing alignment in the regular class; this eliminates clipping. Finally regular closedness of the identified candidate turns area equality and containment into exact set equality.

## 24.4 Positive results and scope

| Result | Written conclusion | Scope |
|---|---|---|
| 19–23 | Simultaneous support tightening, angle erasure, same-hull saturation, two-strip bound | General posed two-turn motions |
| 24–26 | Vertical-barrier separation and connected full saturation | Correct angular sectors; no regularity or maximizer assumption |
| 27–30 | Wrong-sign area <=sqrt(2), covering separated-hull reduction | All bodies that could equal or exceed M |
| 31–35 | Explicit quadratic square kernels and strict concavity modulo translation | Stated normalized function spaces; not automatically area bounds |
| 36–37 | Exact candidate matching, stationarity, value M, fixed-quadratic rigidity | All normalized H^1 perturbations for this quadratic |
| 38 | Unit-span normalization by an in-arm rotation | Bodies of area >1; no dilation |
| 39–40 | Sharp adaptive maximization with moving switches | Initial monotone-velocity convex domain |
| 41–44 | Exact three-piece profile, candidate feasibility/area, restricted body uniqueness | Explicit regular/contact/alignment hypotheses |
| 45–47 | Face alignment forced by feasible common-hull retention | Removes the separate alignment hypothesis |
| 48 | Visible-side first variation | Transverse finite configurations; admissibility remains separate |
| 49–52 | Weaker contact domain, Sobolev profile extension, strongest geometric theorem | Full turns plus the displayed curvature/contact conditions |

## 24.5 Negative findings retained in the branch

| Tempting shortcut | Recorded obstruction |
|---|---|
| Drop the niche overlap from surviving area | Wrong sign: overlap has a plus sign. Notes 2–3 repair it with a partition. |
| Use signed corner area as a niche-area lower bound | Radius-1/2 disk: niches inside K are empty but the signed corner loop has positive area. Note 11. |
| Maximize the naive concave quadratic over all normalized convex bodies | A rectangle has value greater than M but is not a viable connected common hull. Note 12. |
| Assume the raw partition area is concave in natural witness variables | Reflected Hammersley family has P''>0 on its disconnected-envelope range. Note 11. |
| Expect reflected semicircular paths to attain the candidate | The whole ansatz is solved exactly; its maximum C+1/pi is strictly below M. Note 11. |
| Freeze the candidate's contact switches | Actual feasible S_epsilon with areas tending to M satisfy |S_epsilon|>Q_fixed(h_epsilon). Notes 16 and 19. |
| Infer full-angle completion from continuity of widths | Allowed strip orientations can have separate components; the explicit diamond defeats that width-only inference. Note 15. |
| Import full-edge single-turn balance unchanged | A canonical finite-angle example hides the middle of an outer edge while retaining connectedness and the entire hull. The correct derivative uses visible edge length. Note 21. |
| Remove strict curvature hypotheses by algebraic interpolation alone | Minkowski interpolation has not been shown to preserve the required geometric feasibility and component behavior. Note 23. |

The strongest negative test is the near-candidate family: a high-area threshold and local proximity do not repair the fixed-switch majorant. The adaptive construction is a proved replacement on its stated domain, not merely a suggested fix.

## 24.6 Self-review performed on the new proof chain

**Normalization and coverage.** The body stays fixed during support tightening; both paths use the same hull. The angle-erasure argument uses a continuous lift and the intermediate value theorem, retaining variable endpoints. Unit-span normalization is a proper in-arm rotation plus translation, not an unproved stretch.

**Signs and connectivity.** Disjointness is established over the actual horizontal projection of a connected body. The common hull has the same projection. The full envelope is connected by interval fibers, not by assuming intersections preserve connectedness. Every double-subtraction identity specifies why overlap is absent.

**Quadratic algebra.** The width term introduced by affine reflection is retained. The subtraction of selected contact squares is justified by the exact tail factorization, not assumed to preserve concavity. Singular-looking endpoint terms vanish by the stated H^1 trace estimate. The candidate calibration includes switching fluxes and all four endpoint terms.

**Moving switches.** The squared terms vanish at their switching points, and their zero sets have measure zero on the relevant segments. The second-derivative and integrated-gap arguments therefore do not discard an endpoint contribution. The counterexample tests the distinction between fixed and moving switches directly.

**Geometry.** The niche roof is proved by maximizing the minimum of the two wall-height functions. No three-phase boundary is assumed for a general function in the theorem's class. Clipping is first recorded with its positive sign, and is only then eliminated by the proved extreme-point/face-alignment argument. The Sobolev extension uses integrated almost-everywhere identities, not pointwise C^2 assumptions.

**Equality.** The kernel identifies the hull up to translation. Canonical saturation then identifies the body envelope. Exact equality with the original closed body uses the separately proved regular closedness of the candidate; zero area loss alone is not equated with set equality.

## 24.7 Precise unrestricted tasks still missing

A valid unrestricted conclusion requires either a covering comparison with the class of Theorem 52, or a new certificate that covers the excluded configurations. The outstanding questions are:

1. Why can every relevant maximizing body, or an area-dominating representative, be given full quarter-turn endpoints rather than merely the variable endpoints already proved?
2. Why does a relevant maximizer have the required absolutely continuous support curvature in the open quarters, bounded by one, and satisfy p<=q for both halves? The visible-side balance obstruction must be addressed in any direct variation argument.
3. How are degenerate equality/limit cases handled if a non-strict curvature theorem rather than the current strict one is obtained?

For an area-dominating replacement, optimality may follow without preserving the original body. Exact uniqueness additionally needs a containment/equality-recovery argument. Alternatively, a proof phrased only for global maximizers must establish attainment and apply its structural conclusion to **every** maximizer, not only a specially selected one.

No claim is made that these tasks are routine or already resolved. Conversely, the branch no longer lacks the sharp constant, a concrete functional, its global maximization on a defined domain, or its equality analysis: those parts have been completed.

## 24.8 Execution and provenance

All edits remain Markdown under docs/ambidextrous. The existing manuscript, Lean sources, dependency files, and workflow definitions are unchanged. All research commits include `[skip ci]`. No CI run was requested or used; no Lean/Lake compilation, dependency installation, CAS calculation, numerical experiment, or manuscript build was performed.

Romik's explicit path motivates and identifies the candidate. Baek's sharp-majorant method and the repository's uniqueness manuscript motivate the proof organization. This is not a comprehensive literature or priority review. The PR remains draft because the unrestricted geometric reduction and independent proof review are unfinished.
