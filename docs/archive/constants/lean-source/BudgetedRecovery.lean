module

public import MovingSofaStability.OrthogonalErosion
public import MovingSofaStability.DiskRecovery
public import MovingSofaStability.RefinedConstantAlgebra

/-!
# Two-budget recovery for actual sets

Uncompiled proof source. The reverse-distance theorem supplies the whole disk
argument at coefficient 80 from explicit local geometric hypotheses. It does
not pretend those hypotheses have already been specialized to Gerver in Lean.
The area transfer theorem avoids using the global Hausdorff coefficient.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory MovingSofaOptimality

namespace MovingSofaStability

/-- Reverse distance at coefficient 80. The cap and missing set cannot both
spend the full original deficit. Smoothness of either set is unnecessary. -/
theorem reverse_distance_split_budget_80 {K₀ K S : Set Point} {r₀ ε e k δ : ℝ}
    (h₀ : IsCap K₀ (π / 2)) (hK : IsCap K (π / 2))
    (hballs : HasInteriorBalls (capShape K₀) (10 / 271) r₀)
    (hε : 0 < ε) (he : 0 ≤ e) (heε : e ≤ ε)
    (hk0 : 0 ≤ k) (hk : k ≤ 1001 / 500)
    (hδ : 0 ≤ δ) (hδbound : δ ≤ k * sqrt e)
    (hclose : UpperSupportClose δ K K₀)
    (hscale : 80 * sqrt ε ≤ r₀)
    (hmissing : area (capShape K \ S) ≤ 2 * (ε - e)) :
    DirectedClose (80 * sqrt ε) (capShape K₀) S := by
  let r := sqrt 2 * δ
  let η := 2 * (ε - e)
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hsqr : sqrt (η / π) = sqrt (2 / π) * sqrt (ε - e) := by
    have heq : η / π = (2 / π) * (ε - e) := by dsimp [η]; ring
    rw [heq, sqrt_mul (div_nonneg (by norm_num) pi_pos.le)]
  have hroom : r + sqrt (η / π) < (10 / 271) * (80 * sqrt ε) := by
    have hcap := mul_le_mul_of_nonneg_left hδbound (sqrt_nonneg (2 : ℝ))
    rw [hsqr]
    have hbudget := recovery_budget_80 hε he heε hk0 hk
    dsimp [r]
    nlinarith
  obtain ⟨hradius, harea⟩ := residual_radius_area_condition hη hroom
  apply directedClose_of_residual_radius
    (show 0 < 80 * sqrt ε by positivity) hscale
    (show 0 ≤ r by dsimp [r]; positivity) hradius hballs
    (reference_erosion_subset_sqrt_two hδ h₀ hK hclose)
    (volume_ne_top_of_subset sdiff_subset hK.2.1.2.1.measure_lt_top.ne)
    hmissing harea

/-- Exact finite-area identity for symmetric difference. -/
theorem symmetricDifferenceArea_eq_deficit_add_surplus {S G : Set Point}
    (hS : MeasurableSet S) (hG : MeasurableSet G)
    (hSf : volume S ≠ ⊤) (hGf : volume G ≠ ⊤) :
    symmetricDifferenceArea S G = area G - area S + 2 * area (S \ G) := by
  have hdis : Disjoint (S \ G) (G \ S) := by
    rw [Set.disjoint_left]
    rintro p ⟨hpS, hpG⟩ ⟨hpG', _⟩
    exact hpG hpG'
  unfold symmetricDifferenceArea
  rw [area_union_of_disjoint hdis (hG.diff hS)
    (volume_ne_top_of_subset sdiff_subset hSf)
    (volume_ne_top_of_subset sdiff_subset hGf)]
  rw [area_sdiff_balance hS hG hSf hGf]
  ring

/-- The envelope surplus and its own excess over Gerver suffice for area
recovery. No Hausdorff estimate for the original sofa is used. -/
theorem symmetricDifferenceArea_via_envelope {S U G : Set Point} {ε g v : ℝ}
    (hS : MeasurableSet S) (hU : MeasurableSet U) (hG : MeasurableSet G)
    (hSf : volume S ≠ ⊤) (hUf : volume U ≠ ⊤) (hGf : volume G ≠ ⊤)
    (hε : area G - area S = ε)
    (hgain : area (S \ U) ≤ g) (hexcess : area (U \ G) ≤ v) :
    symmetricDifferenceArea S G ≤ ε + 2 * g + 2 * v := by
  have hsub : S \ G ⊆ (S \ U) ∪ (U \ G) := by
    intro p hp
    by_cases hpU : p ∈ U
    · exact Or.inr ⟨hpU, hp.2⟩
    · exact Or.inl ⟨hp.1, hpU⟩
  have hdis : Disjoint (S \ U) (U \ G) := by
    rw [Set.disjoint_left]
    rintro p ⟨_, hpU⟩ ⟨hpU', _⟩
    exact hpU hpU'
  have hleftf := volume_ne_top_of_subset (sdiff_subset : S \ U ⊆ S) hSf
  have hrightf := volume_ne_top_of_subset (sdiff_subset : U \ G ⊆ U) hUf
  have hfinite : volume ((S \ U) ∪ (U \ G)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hleftf, hrightf⟩) (measure_union_le _ _)
  have hbound := area_mono_of_finite hsub hfinite
  rw [area_union_of_disjoint hdis (hU.diff hG) hleftf hrightf] at hbound
  rw [symmetricDifferenceArea_eq_deficit_add_surplus hS hG hSf hGf, hε]
  linarith

/-- The explicit area coefficient follows once the convex parallel layer and
reference roof band have bounded the envelope's excess. -/
theorem symmetricDifferenceArea_204_of_cap_excess {S U G : Set Point}
    {ε e k δ : ℝ}
    (hS : MeasurableSet S) (hU : MeasurableSet U) (hG : MeasurableSet G)
    (hSf : volume S ≠ ⊤) (hUf : volume U ≠ ⊤) (hGf : volume G ≠ ⊤)
    (hεeq : area G - area S = ε) (hε : 0 ≤ ε)
    (he : 0 ≤ e) (heε : e ≤ ε)
    (hk0 : 0 ≤ k) (hk : k ≤ 1001 / 500)
    (hδ : 0 ≤ δ) (hδbound : δ ≤ k * sqrt e)
    (hgain : area (S \ U) ≤ ε - e)
    (hexcess : area (U \ G) ≤ (203 / 4) * δ + 4 * δ ^ 2)
    (hsmall : sqrt ε ≤ 1 / 50) :
    symmetricDifferenceArea S G ≤ 204 * sqrt ε := by
  have harea := symmetricDifferenceArea_via_envelope hS hU hG hSf hUf hGf hεeq hgain hexcess
  apply symmetric_difference_budget_204 hε he heε hk0 hk hδ hδbound
    (g := ε - e) le_rfl _ hsmall
  nlinarith

end MovingSofaStability
