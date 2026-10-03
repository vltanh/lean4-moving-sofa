module

public import MovingSofaOptimality.Gerver.Defs

/-!
# Enclosures of the parameters of Gerver's sofa

`GerverBounds P` collects intervals of width `2 · 10⁻⁷` around Romik's numerical values (his Table 1)
for the parameters that are not fixed exactly by his equations. The numerical verifications of
Gerver's sofa assume `GerverBounds P` together with `P.IsSolution`; `MovingSofaOptimality.External.Romik`
proves that every solution in the box satisfies these bounds.
-/

@[expose] public section

open Real Set

namespace MovingSofaOptimality

namespace GerverParams

/-- Enclosures of the parameters of Gerver's sofa. -/
structure Bounds (P : GerverParams) : Prop where
  φ_mem : P.φ ∈ Icc (0.039177264 : ℝ) 0.039177465
  θ_mem : P.θ ∈ Icc (0.681301409 : ℝ) 0.68130161
  a₁_mem : P.a₁ ∈ Icc (1.210322322 : ℝ) 1.210322523
  b₁_mem : P.b₁ ∈ Icc (-0.527624699 : ℝ) (-0.527624498)
  b₂_mem : P.b₂ ∈ Icc (0.920258285 : ℝ) 0.920258486
  c₁_mem : P.c₁ ∈ Icc (0.626045422 : ℝ) 0.626045623
  κ₂₁_mem : P.κ₂.1 ∈ Icc (-0.919179393 : ℝ) (-0.919179192)
  κ₂₂_mem : P.κ₂.2 ∈ Icc (0.472406519 : ℝ) 0.47240672
  κ₃₁_mem : P.κ₃.1 ∈ Icc (-0.61376333 : ℝ) (-0.613763129)
  κ₃₂_mem : P.κ₃.2 ∈ Icc (0.889626379 : ℝ) 0.88962658
  κ₄₁_mem : P.κ₄.1 ∈ Icc (-0.308347267 : ℝ) (-0.308347066)
  κ₄₂_mem : P.κ₄.2 ∈ Icc (0.472406519 : ℝ) 0.47240672
  κ₅₁_mem : P.κ₅.1 ∈ Icc (-1.017204137 : ℝ) (-1.017203936)
  κ₅₂_mem : P.κ₅.2 ∈ Icc (0.2499999 : ℝ) 0.2500001

end GerverParams

end MovingSofaOptimality
