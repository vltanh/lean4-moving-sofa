module

public import MovingSofa.Balanced.BalancedMaximumSofa
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Horizontal side lengths (§4.1)

Definition 4.1.1 (`def:wedge-gap-infimum`), Lemma 4.1.1 (`lem:wedge-gap-limit`), Theorem 4.1.2
(`thm:balanced-polygon-sofa-ineq`), Theorem 4.1.3 (`thm:surface-area-weak-convergence`, Schneider
Theorem 4.2.1) and Theorem 4.1.4 (`thm:balanced-maximum-sofa-ineq`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace MovingSofa

/-- `w_K° = inf_{t ∈ (0, ω)} w_K(t)` (Definition 4.1.1, `def:wedge-gap-infimum`). -/
noncomputable def wedgeGapWInf (K : Set (ℝ × ℝ)) (ω : ℝ) : ℝ := ⨅ t : Ioo 0 ω, wedgeGapW K t

/-- `z_K° = inf_{t ∈ (0, ω)} z_K(t)` (Definition 4.1.1). -/
noncomputable def wedgeGapZInf (K : Set (ℝ × ℝ)) (ω : ℝ) : ℝ := ⨅ t : Ioo 0 ω, wedgeGapZ K ω t

/-- **Lemma 4.1.1** (`lem:wedge-gap-limit`). For caps `K, K'` with rotation angle `ω < π/2` at
Hausdorff distance `ε`, `|w_K° - w_{K'}°| ≤ (1 + sec ω) ε`. -/
theorem lemma4_1_1 {K K' : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω < π / 2) (hK : IsCap K ω)
    (hK' : IsCap K' ω) :
    |wedgeGapWInf K ω - wedgeGapWInf K' ω| ≤ (1 + 1 / cos ω) * hausdorffDist K K' := by
  sorry

/-- **Theorem 4.1.2** (`thm:balanced-polygon-sofa-ineq`). For a maximum polygon cap with rotation
angle `ω < π/2`, `w_K° ≤ σ_K(π/2)` and `z_K° ≤ σ_K(ω)`. -/
theorem theorem4_1_2 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap Θ K)
    (hω : Θ.ω < π / 2) :
    wedgeGapWInf K Θ.ω ≤ sigmaAt K (π / 2) ∧ wedgeGapZInf K Θ.ω ≤ sigmaAt K Θ.ω := by
  sorry

/-- **Theorem 4.1.3** (`thm:surface-area-weak-convergence`, Schneider Theorem 4.2.1). If convex bodies
`K_n` converge to `K` in the Hausdorff distance, then `σ_{K_n} → σ_K` weakly as measures on `S¹`:
for every continuous `2π`-periodic `f`, `∫_{[0, 2π)} f dσ_{K_n} → ∫_{[0, 2π)} f dσ_K`. -/
theorem theorem4_1_3 {Ks : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)} (hKs : ∀ n, IsConvexBody (Ks n))
    (hK : IsConvexBody K) (hlim : HausdorffTendsto Ks K) {f : ℝ → ℝ} (hf : Continuous f)
    (hper : Function.Periodic f (2 * π)) :
    Tendsto (fun n => ∫ t in Ico 0 (2 * π), f t ∂(sigma (Ks n))) atTop
      (𝓝 (∫ t in Ico 0 (2 * π), f t ∂(sigma K))) := by
  sorry

/-- **Theorem 4.1.4** (`thm:balanced-maximum-sofa-ineq`). For `ω < π/2`, a balanced maximum cap
satisfies `σ_K(π/2) ≥ w_K°` and `σ_K(ω) ≥ z_K°`. -/
theorem theorem4_1_4 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsBalancedMaxCap K ω) (hω : ω < π / 2) :
    wedgeGapWInf K ω ≤ sigmaAt K (π / 2) ∧ wedgeGapZInf K ω ≤ sigmaAt K ω := by
  sorry

end MovingSofa
