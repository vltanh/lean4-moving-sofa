# 57. Focused structural status after Notes 52–58

**The unrestricted proof is not closed.** This pass did not improve the coarse global numerical bound or broaden the protected-candidate theorem again. It worked directly on finite variations and obtained maximizer-specific exclusions for atoms and singular-continuous curvature, with their actual geometric obstructions stated.

This is the current research-entry ledger. Note 51 remains the preceding full inventory; Notes 7, 24, 34, and 43 are earlier snapshots. All results are pen-and-paper arguments with self-review, not independent verification. The full earlier proof chain has not been independently audited in this pass.

## 57.1 Maximizer-specific exclusions, without candidate proximity

[Theorem 105](56-atomic-improvement-away-from-obstructions.md) does not assume proximity to Romik, full quarter turns, smoothness, or an input curvature cap. Consider an exposed-edge atom at a floating normal in a canonical motion. If a compact subsegment of that edge is strictly clear of the closures of both swept niches, and the surviving fibers near its corresponding inner-corner abscissa have a uniform positive gap (or that abscissa lies away from the body's projection), then the body is **not** globally maximizing.

The proof replaces the support on a short angular interval by the solution of f_c''+f_c=1 with the same endpoint values. A positive Green-kernel calculation proves f_c>=f and verifies convex gluing even for singular input curvature. The relevant one-wall supremum is preserved exactly. The two-wall niche can change, but only over an x-band of width O(epsilon), by a height O(epsilon). Its area cost is O(epsilon squared), while a clear portion of the old edge gains a triangle of area at least c epsilon. Thus

\[
|S_\varepsilon|-|S|\geq c\varepsilon-C\varepsilon^2>0.
\]

[Theorem 107](58-singular-curvature-away-from-obstructions.md) extends this mechanism to nonatomic singular-density points. On suitable radii r, with central curvature mass m(r), one has m(r)/r tending to infinity and a local doubling bound. The replacement gains hull area at least c m(r)^2 r, while the changed corner costs at most C m(r)r^2:

\[
|S_c|-|S|\geq c m(r)^2r-Cm(r)r^2>0.
\]

Here the unique exposed point must be strictly clear of the two niches, and the affected fibers need the stated clearance unless the changed corner lies below the incoming strip or outside the horizontal projection. Standard Radon-measure differentiation shows that the required density scales occur at almost every point of the singular-continuous curvature measure. Thus a maximizing hull has no such singular mass in this unobstructed geometry.

These are actual admissible improvements at general bodies, not critical-point equations with unproved variations. They leave masked/coincident contacts and pinching connections unresolved. The circular replacement can create endpoint atoms; it is not falsely described as putting the whole hull into the curvature-dominated class. Nor does exclusion of singular mass establish the sharp bound on the remaining absolutely continuous density.

## 57.2 The finite variational passage is now explicit

| Component | Result | What it does not say |
|---|---|---|
| Inner-radius and support control | Lemma 95 and Theorem 96 give a uniform inner disk and d_H(K_s,K)<=RC|s|/r. | The surviving component need not retain K_s automatically. |
| Selection error | Corollary 97 makes the penalty error O(N^(-1/2)) for bounded-speed hull-preserving variations. | It does not make an inadmissible variation feasible. |
| Exact finite chart | Lemma 98 encodes fixed-angle geometry, hull retention, and nonempty fibers by finitely many polyhedral charts, with quadratic area. | The union of charts is not one convex feasible set. |
| Necessary optimality | Theorem 99 gives a normal-cone multiplier equation, including degenerate contacts. | The constraint terms are not part of the vanishing selection penalty. |
| Area-derivative compactness | Theorem 100 gives a mesh-independent Lipschitz bound away from the axis normals and bounded signed derivative measures. | A bounded weak limit need not be zero or absolutely continuous. |
| Admissible clearing direction | Proposition 101 and Lemma 102 allow slack span in the selector and make inward canonical saturation admissible. | The inward operation has a first-order area cost. |
| Normal-work control | Equation (55.5) bounds the multiplier work along that direction. | Bounded multiplier mass is not vanishing mass; zero-work chart rows remain uncontrolled. |

The distinction between vertex displacement and Hausdorff displacement matters: small angular mesh gaps do not produce an intrinsic N-factor in the supporting-polygon estimate. That particular obstacle from Note 39 has been removed for the specified hull-preserving variations.

## 57.3 The exact remaining normal terms

On an incident feasible chart, write F_n for its area polynomial and E_n for its equality-constraint matrix. The selected maximum satisfies

\[
\nabla F_n
=\kappa_n r_n-\sum_j\mu_{n,j}\nabla c_{n,j}+E_n^T\lambda_n,
\qquad\mu_{n,j}\geq0,
\]

where r_n is an active penalty subgradient and c_{n,j}>=0 are active chart/feasibility inequalities. The symbol E_n here is a matrix, not the geometric envelope used elsewhere.

The penalty coefficient tends to zero. The contact multipliers have **not** been shown to do so. The inward direction v_n gives only

\[
\sum_j\mu_{n,j}Dc_{n,j}[v_n]
\leq2|C_n|+\kappa_n R.
\]

A finite polygon example in Note 53 shows a positive connectivity multiplier at a point connection despite hull retention and no penalty. It is not a canonical sofa counterexample, but it refutes the purely formal inference from finite maximality to unconstrained balance.

Artificial chart walls also require care: a multiplier on a line-ordering choice is not automatically a physical pressure. The comparison must account for all incident admissible charts, not select one convenient polynomial extension and call its gradient zero. The bounds proved here do not settle those geometric normal terms.

## 57.4 What is still needed for either unrestricted theorem

The sharp theorem on the stated class remains [Theorem 65](31-closed-curvature-class-theorem.md). To use it at an unrestricted maximizer, the unproved structural conclusions remain:

1. full-quarter endpoint angles, or an alternative sharp comparison for partial endpoints;
2. domination of the complete open-quarter curvature measure by dtheta, including obstructed singular contacts and the bound on absolutely continuous curvature;
3. both contact-order inequalities.

A structural theorem for one attained maximizer would settle the value. The corresponding theorem for every maximizer, or an equality-preserving comparison, is needed for exact uniqueness. Existing arbitrary-hull selection continues to preserve that distinction.

This pass does not establish those conclusions. The new results narrow the singular-curvature problem to actual masking/coincidence and clearance obstructions, rather than assuming away all singular measures. They do not justify calling the unrestricted proof nearly complete.

## 57.5 Audit and corrections

The Green kernel has positive sign because the replacement interval has length below pi. The new support is above the old support and endpoint derivative jumps are nonnegative. The one-wall supremum is checked by its affine transformed form, and the complete min-wall roof is checked separately. The changing roof is confined to the union of old and new corner-abscissa ranges.

For an atom the retained first-order triangle is chosen over a strictly clear edge subsegment away from the shrinking corner band. For a nonatomic singular point, all added hull points converge to the unique exposed point. The possible equality of its abscissa with the inner corner is handled explicitly: then the corner lies strictly below the incoming strip and its changed quadrants do not remove strip area. The quadratic niche-loss estimate is compared to the singular-density hull gain before asserting an improvement.

The mass estimate uses the middle-half Green-kernel lower bound, a local doubling scale, and the measure pairing in the exact support-area expansion. No singular term is dropped. The standard differentiation theorem used to obtain almost-everywhere singular-density scales is cited separately in Note 58; none of the present sofa results was compiled in Lean.

For the finite estimates, the inner disk can have a center depending on n but has a uniformly positive radius. The raw total-envelope area estimate is kept distinct from a connected-component estimate. Inward saturation preserves the old endpoint angles and has a first-order cost. The hypotheses of Lemma 102 now explicitly require a member of the finite class with area strictly above its threshold.

During this audit, the unnecessarily strict text V>M in Notes 52, 53, and 55 was corrected to the justified V>=M. Only M>8/5 is used to keep the selection threshold inactive. Neither equality nor strict inequality between the unknown optimum V and M has been established by this pass.

## 57.6 Execution

Every change is Markdown under docs/ambidextrous. All commits include `[skip ci]`. No CI, Lean/Lake compilation, dependency installation, numerical experiment, computer algebra, or manuscript build was used. The PR remains open and draft, with no merge or unrestricted-completion claim.
