module

public import MovingSofaStability.FourArcCoercivity

/-!
# Cap support coercivity from the actual Mamikon deficit

The analytic hypotheses are discharged for convex supports and the four square
integrals are identified with the existing cap energy. The resulting coefficient
80 is deliberately non-sharp; it suffices for the unrestricted theorem's
existence of a square-root constant.

This is not the separate sharp 2 sec(phi) result. No kernel norm identity,
residual integrability, or squared support bound is assumed in the final lemmas.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- Convex support differences satisfy every analytic hypothesis of coercivity. -/
theorem capDifference_data {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (K₀ K₁ : ConvexBodySet) (h₀ : IsCap K₀.1 (π / 2)) (h₁ : IsCap K₁.1 (π / 2)) :
    FourResidualData φ (capDifference K₀.1 K₁.1) (capDifferenceDeriv K₀.1 K₁.1) := by
  have hp := pi_pos
  have hp0 := hφ.1
  have hp4 := hφ.2
  obtain ⟨i₁, s₁⟩ := tangent_capDifference_integrable (T := π / 2) (a := 0) (b := φ)
    hp0 (by linarith) (by linarith) (by linarith) K₀ K₁
  obtain ⟨i₂, s₂⟩ := corner_capDifference_integrable (a := φ) (b := π / 2 - φ)
    (by linarith) (by linarith) K₀ K₁
  obtain ⟨i₃, s₃⟩ := tangent_capDifference_integrable (T := π - φ)
    (a := π / 2 - φ) (b := π / 2)
    (by linarith) (by linarith) (by linarith) (by linarith) K₀ K₁
  obtain ⟨i₄, s₄⟩ := tangent_capDifference_integrable (T := π) (a := π / 2) (b := π)
    (by linarith) (by linarith) (by linarith) le_rfl K₀ K₁
  refine ⟨capDifference_continuous K₀.2 K₁.2, ?_, ?_, ?_,
    (intervalIntegrable_iff_integrableOn_Icc_of_le hp0.le).2 i₁,
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 i₂,
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 i₃,
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 i₄,
    (intervalIntegrable_iff_integrableOn_Icc_of_le hp0.le).2 s₁,
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 s₂,
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 s₃,
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 s₄⟩
  · intro t ht
    exact pinned_support_rightDerivative K₀.2 K₁.2 t
  · change pinnedDifference (fun t => supp K₁.1 t - supp K₀.1 t) (π / 2) = 0
    rw [pinnedDifference_top, h₁.2.2.2.1, h₀.2.2.2.1, sub_self]
  · exact pinnedDifference_pi _

/-- The tangent residual square integral is twice the geometric difference energy. -/
theorem tangent_arcSquare_eq_energy {a b T : ℝ}
    (hab : a < b) (haT : T - π < a) (hbT : b ≤ T) (K₀ K₁ : ConvexBodySet) :
    arcSquare a b (tangentResidual T (capDifference K₀.1 K₁.1)
      (capDifferenceDeriv K₀.1 K₁.1)) =
      2 * displacementEnergy a b (fun K => tangentParam K.1 T) K₀ K₁ := by
  unfold arcSquare displacementEnergy halfSquareIntegral
  rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  have he : (∫ t in Ioo a b,
      tangentResidual T (capDifference K₀.1 K₁.1) (capDifferenceDeriv K₀.1 K₁.1) t ^ 2) =
      ∫ t in Ioo a b, (displacement K₀.1 (tangentParam K₀.1 T) t -
        displacement K₁.1 (tangentParam K₁.1 T) t) ^ 2 := by
    apply integral_congr_ae
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro t ht
    have htT : t < T := ht.2.trans_le hbT
    have hs : sin (T - t) ≠ 0 :=
      (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [ht.1])).ne'
    dsimp only
    rw [capDifference, capDifferenceDeriv, tangentResidual_pinned _ _ _ _ hs]
    simp only [opt_g]
    rw [← tangent_displacement_sub htT]
    ring
  rw [he]
  ring

/-- The corresponding middle-arc identity has no singular tangent endpoint. -/
theorem corner_arcSquare_eq_energy {a b : ℝ} (hab : a ≤ b) (K₀ K₁ : ConvexBodySet) :
    arcSquare a b (cornerResidual (capDifference K₀.1 K₁.1) (capDifferenceDeriv K₀.1 K₁.1)) =
      2 * displacementEnergy a b (fun K => outerCorner K.1) K₀ K₁ := by
  unfold arcSquare displacementEnergy halfSquareIntegral
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  have he : (∫ t in Ioo a b,
      cornerResidual (capDifference K₀.1 K₁.1) (capDifferenceDeriv K₀.1 K₁.1) t ^ 2) =
      ∫ t in Ioo a b, (displacement K₀.1 (outerCorner K₀.1) t -
        displacement K₁.1 (outerCorner K₁.1) t) ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      dsimp only
      rw [capDifference, capDifferenceDeriv, cornerResidual_pinned]
      simp only [opt_g]
      rw [← outer_displacement_sub K₀.1 K₁.1 t]
      ring
  rw [he]
  ring

/-- The analytic residual energy and the four Mamikon integrals are identical. -/
theorem fourResidualEnergy_eq_capEnergy {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (K₀ K₁ : ConvexBodySet) :
    fourResidualEnergy φ (capDifference K₀.1 K₁.1) (capDifferenceDeriv K₀.1 K₁.1) =
      capResidualEnergy φ K₀ K₁ := by
  have hp := pi_pos
  have hp0 := hφ.1
  have hp4 := hφ.2
  have e₁ := tangent_arcSquare_eq_energy (a := 0) (b := φ) (T := π / 2)
    hp0 (by linarith) (by linarith) K₀ K₁
  have e₂ := corner_arcSquare_eq_energy (a := φ) (b := π / 2 - φ) (by linarith) K₀ K₁
  have e₃ := tangent_arcSquare_eq_energy (a := π / 2 - φ) (b := π / 2) (T := π - φ)
    (by linarith) (by linarith) (by linarith) K₀ K₁
  have e₄ := tangent_arcSquare_eq_energy (a := π / 2) (b := π) (T := π)
    (by linarith) (by linarith) le_rfl K₀ K₁
  unfold fourResidualEnergy capResidualEnergy
  rw [e₁, e₂, e₃, e₄, show π / 2 + (π / 2 - φ) = π - φ by ring]
  ring

/-- Unconditional support coercivity for two normalized nonsmooth caps. -/
theorem capDifference_le_energy {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (K₀ K₁ : ConvexBodySet) (h₀ : IsCap K₀.1 (π / 2)) (h₁ : IsCap K₁.1 (π / 2))
    {t : ℝ} (ht : t ∈ Icc 0 π) :
    |capDifference K₀.1 K₁.1 t| ≤ 80 * sqrt (capResidualEnergy φ K₀ K₁) := by
  have h := four_arc_coercivity hφ (capDifference_data hφ K₀ K₁ h₀ h₁) ht
  rwa [fourResidualEnergy_eq_capEnergy hφ K₀ K₁] at h

/-- The support bound on the genuinely enlarged Q domain. No coercivity hypothesis remains. -/
theorem wide_cap_support_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) {t : ℝ} (ht : t ∈ Icc 0 π) :
    |capDifference P.cap x.1.1.1 t| ≤ 80 * sqrt (area (gerverSofa P) - wideUpperQ P.φ x) := by
  have h := capDifference_le_energy (GerverParams.gm_φ_mem_Ioo hP hbox)
    (wideGerverTriple hP hbox).1.1 x.1.1 (wideGerverTriple hP hbox).2.1 x.2.1 ht
  have he := wide_capResidualEnergy_le_deficit hP hbox x
  exact h.trans (mul_le_mul_of_nonneg_left (sqrt_le_sqrt he) (by norm_num))

/-- In the old Ki class, the real sofa-area deficit controls the cap support directly. -/
theorem ki_cap_support_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set (ℝ × ℝ)} (hK : IsKi K) {t : ℝ} (ht : t ∈ Icc 0 π) :
    |capDifference P.cap K t| ≤ 80 * sqrt (area (gerverSofa P) - sofaArea (π / 2) K) := by
  have h := wide_cap_support_bound hP hbox (toWideTriple (kiExtensionTriple hbox.1 hK)) ht
  have ha := theorem8_2_4 hbox.1 hK
  have hdef : area (gerverSofa P) -
      wideUpperQ P.φ (toWideTriple (kiExtensionTriple hbox.1 hK)) ≤
      area (gerverSofa P) - sofaArea (π / 2) K := by
    change area (gerverSofa P) - upperQ P.φ K (rightBody P.φ K) (leftBody P.φ K) ≤ _
    linarith
  exact h.trans (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hdef) (by norm_num))

end MovingSofaStability
