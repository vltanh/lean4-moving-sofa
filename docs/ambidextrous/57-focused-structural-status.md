# 57. Focused structural status after Notes 52–56

**The unrestricted proof is not closed.** This pass did not improve the coarse global numerical bound or broaden the protected-candidate theorem again. It worked directly on finite variations and obtained a new atom-improvement result at general maximizers, with its actual obstructions stated.

This is the current research-entry ledger. Note 51 remains the preceding full inventory; Notes 7, 24, 34, and 43 are earlier snapshots. All results are pen-and-paper arguments with self-review, not independent verification. The full earlier proof chain has not been independently audited in this pass.

## 57.1 A genuine maximizer-specific geometric exclusion

[Theorem 105](56-atomic-improvement-away-from-obstructions.md) does not assume proximity to Romik, full quarter turns, smoothness, or an input curvature cap. Consider an exposed-edge atom at a floating normal in a canonical motion. If:

- a compact subsegment of the edge is strictly clear of the closures of both swept niches; and
- the surviving fibers near its corresponding inner-corner abscissa have a uniform positive gap (or that abscissa lies away from the body's projection),

then the body is **not** globally maximizing.

The proof replaces the support on an arbitrarily short angular interval by the solution of f_c''+f_c=1 with the same endpoint values. A positive Green-kernel calculation proves f_c>=f and verifies convex gluing even for singular input curvature. The operation preserves the relevant one-wall supremum exactly.

The two-wall niche can change, but only over an x-band of width O(epsilon), by a height O(epsilon). Its area cost is O(epsilon squared). A strictly clear portion of the original edge produces a retained triangular area gain of order epsilon. The clearance condition preserves connectivity, and all endpoint widths stay unchanged. Therefore

\[
|S_\varepsilon|-|S|\geq c\varepsilon-C\varepsilon^2>0.
\]

This is an actual admissible improvement at a general body, not a critical-point equation with unproved variations. It leaves masked/coincident edge atoms and atoms tied to pinching connections unresolved. The replacement creates endpoint atoms and is not falsely described as putting the whole hull into the curvature-dominated class.

## 57.2 The finite variational passage is now explicit

The following parts of that passage are written out:

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

On an incident feasible chart, the selected maximum satisfies

\[
\nabla A_n
=\kappa_n r_n
-\sum_j\mu_{n,j}\nabla c_{n,j}+A_n^{\mathrm{eq},T}\lambda_n,
\qquad \mu_{n,j}\geq0,
\]

where r_n is an active penalty subgradient, c_{n,j}>=0 are active chart/feasibility inequalities, and A_n^eq records equality constraints. The notation A_n for the area gradient is unrelated to that equality matrix.

The penalty coefficient tends to zero. The contact multipliers have **not** been shown to do so. The inward direction v_n gives only

\[
\sum_j\mu_{n,j}Dc_{n,j}[v_n]
\leq2|C_n|+\kappa_n R.
\]

A finite polygon example in Note 53 shows a positive connectivity multiplier at a point connection despite hull retention and no penalty. It is not a canonical sofa counterexample, but it refutes the proposed purely formal inference from finite maximality to unconstrained balance.

Artificial chart walls also require care: a multiplier on a line-ordering choice is not automatically a physical pressure. The comparison must account for all incident admissible charts, not select one convenient polynomial extension and call its gradient zero.

## 57.4 What is still needed for either unrestricted theorem

The sharp theorem on the stated class remains [Theorem 65](31-closed-curvature-class-theorem.md). To use it at an unrestricted maximizer, the unproved structural conclusions remain:

1. full-quarter endpoint angles, or an alternative sharp comparison for partial endpoints;
2. domination of the complete open-quarter curvature measure by dtheta, including the obstructed atoms and diffuse/singular-continuous cases not covered by Theorem 105;
3. both contact-order inequalities.

A structural theorem for one attained maximizer would settle the value. The corresponding theorem for every maximizer, or an equality-preserving comparison, is needed for exact uniqueness. Existing arbitrary-hull selection continues to preserve that distinction.

This pass does not establish those conclusions, and the new atom theorem is not a substitute for them. It narrows a portion of the singular-curvature problem to actual masking/coincidence and clearance obstructions, rather than assuming away all singular measures.

## 57.5 Audit of the new operation

The Green kernel has positive sign because the replacement interval has length below pi. The new support is above the old support and the endpoint derivative jumps are nonnegative. The one-wall supremum is checked by its affine transformed form, and the complete min-wall roof is checked separately. The changing roof is confined to the union of old and new corner-abscissa ranges, which has width O(epsilon) without smoothness.

The retained first-order triangle is chosen over a strictly clear edge subsegment whose x-projection avoids the shrinking corner band. The loss estimate counts any clipping conservatively as lost old area. Connectivity is proved from actual fiber clearance, not from continuity of area. The final competitor need not retain the intended enlarged hull, and the proof does not assume that unnecessary conclusion.

For the finite estimates, the inner disk may have a center depending on n, but its radius is uniformly positive. The raw total-envelope area estimate is kept distinct from a connected-component estimate. The relaxed selector drops only exact span; all genuine width and box constraints remain. Inward saturation preserves the original endpoint angles rather than completing them.

## 57.6 Execution

Every change is Markdown under docs/ambidextrous. All commits include `[skip ci]`. No CI, Lean/Lake compilation, dependency installation, numerical experiment, computer algebra, or manuscript build was used. The PR remains open and draft, with no merge or unrestricted-completion claim.
