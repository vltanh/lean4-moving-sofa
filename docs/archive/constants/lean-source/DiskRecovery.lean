module

public import MovingSofaStability.EuclideanDisks
public import MovingSofaStability.DeficitBudget

/-!
# Exact-disk missing-area recovery

Uncompiled proof source. The older square-based lemma remains unchanged.
This version uses the entire radius left after erosion and the exact Euclidean
disk area. Finiteness is retained when converting volume to real area.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory MovingSofaOptimality

namespace MovingSofaStability

/-- If the surviving interior disk has more area than the missing set, some
point of S must occur at the requested scale. Neither S nor G is convex. -/
theorem directedClose_of_missing_disk {G U S : Set Point}
    {κ r₀ r ρ a η : ℝ}
    (hρ : 0 < ρ) (hρ₀ : ρ ≤ r₀) (ha : 0 ≤ a)
    (hballs : HasInteriorBalls G κ r₀)
    (herosion : euclideanErosion r G ⊆ U)
    (har : a + r ≤ κ * ρ) (haρ : a ≤ κ * ρ)
    (hUf : volume U ≠ ⊤) (hmissing : area (U \ S) ≤ η)
    (hsmall : η < π * a ^ 2) : DirectedClose ρ G S := by
  intro p hp
  by_contra hnone
  obtain ⟨z, hz⟩ := hballs p hp ρ hρ hρ₀
  have hins : euclideanBall z a ⊆ euclideanErosion r G :=
    ball_subset_erosion (fun q hq => (hz hq).1) har
  have hsub : openEuclideanBall z a ⊆ U \ S := by
    intro q hq
    have hqball : q ∈ euclideanBall z a := (show euclideanDist z q < a from hq).le
    have hqG := hz (hqball.trans haρ)
    refine ⟨herosion (hins hqball), ?_⟩
    intro hqS
    exact hnone ⟨q, hqS, hqG.2⟩
  have harea := area_mono_of_finite hsub (volume_ne_top_of_subset sdiff_subset hUf)
  rw [area_openEuclideanBall z ha] at harea
  exact (not_lt_of_ge (harea.trans hmissing)) hsmall

/-- No arbitrary half-radius reserve is necessary: use kappa*rho-r exactly. -/
theorem directedClose_of_residual_radius {G U S : Set Point}
    {κ r₀ r ρ η : ℝ}
    (hρ : 0 < ρ) (hρ₀ : ρ ≤ r₀) (hr : 0 ≤ r) (hroom : r < κ * ρ)
    (hballs : HasInteriorBalls G κ r₀)
    (herosion : euclideanErosion r G ⊆ U)
    (hUf : volume U ≠ ⊤) (hmissing : area (U \ S) ≤ η)
    (hsmall : η < π * (κ * ρ - r) ^ 2) : DirectedClose ρ G S := by
  apply directedClose_of_missing_disk hρ hρ₀ (sub_nonneg.mpr hroom.le)
    hballs herosion _ _ hUf hmissing hsmall <;> linarith

/-- Express the exact-disk condition as a sum of an erosion radius and an
area radius. This is the point where the split deficit is useful. -/
theorem residual_radius_area_condition {κ ρ r η : ℝ}
    (hη : 0 ≤ η) (hroom : r + sqrt (η / π) < κ * ρ) :
    r < κ * ρ ∧ η < π * (κ * ρ - r) ^ 2 := by
  have hs := sqrt_nonneg (η / π)
  have hsq := sq_sqrt (div_nonneg hη pi_pos.le)
  have hmul : π * (η / π) = η := by field_simp
  have hgap : 0 < κ * ρ - r := by linarith
  have hslt : sqrt (η / π) < κ * ρ - r := by linarith
  have hsq_lt : η / π < (κ * ρ - r) ^ 2 := by nlinarith
  have hp := mul_lt_mul_of_pos_left hsq_lt pi_pos
  exact ⟨by linarith, by linarith⟩

end MovingSofaStability
