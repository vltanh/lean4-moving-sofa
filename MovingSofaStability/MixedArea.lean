module

public import MovingSofaStability.WideConcavity

/-!
# Mixed-area first variation without atom-free endpoints

The source mixed-area symmetry argument removed the atoms at 0 and 2*pi using
Ki. Here those atoms are retained: periodicity makes their endpoint
contributions equal. The integration-by-parts theorem already applies to
arbitrary convex bodies.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality

namespace MovingSofaStability

/-- Swapping the included endpoint of an interval preserves the integral when
the two singleton contributions agree. Atoms need not vanish. -/
theorem integral_Ico_eq_Ioc_of_endpoint_balance (μ : Measure ℝ)
    [IsLocallyFiniteMeasure μ] {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : Continuous f) (he : μ.real {a} * f a = μ.real {b} * f b) :
    (∫ t in Ico a b, f t ∂μ) = ∫ t in Ioc a b, f t ∂μ := by
  have hsplit : Ico a b = Ioo a b ∪ {a} := by
    ext t
    simp only [mem_Ico, mem_union, mem_Ioo, mem_singleton_iff]
    constructor
    · intro ht
      rcases eq_or_lt_of_le ht.1 with h | h
      · exact Or.inr h.symm
      · exact Or.inl ⟨h, ht.2⟩
    · rintro (ht | rfl)
      · exact ⟨ht.1.le, ht.2⟩
      · exact ⟨le_rfl, hab⟩
  have hint : IntegrableOn f (Icc a b) μ :=
    hf.continuousOn.integrableOn_compact isCompact_Icc
  have hia : IntegrableOn f ({a} : Set ℝ) μ :=
    hint.mono_set (by intro t ht; rw [mem_singleton_iff.mp ht]; exact ⟨le_rfl, hab.le⟩)
  have hib : IntegrableOn f ({b} : Set ℝ) μ :=
    hint.mono_set (by intro t ht; rw [mem_singleton_iff.mp ht]; exact ⟨hab.le, le_rfl⟩)
  rw [hsplit, ← Ioo_union_right hab,
    setIntegral_union (by simp) (measurableSet_singleton _) (hint.mono_set Ioo_subset_Icc_self) hia,
    setIntegral_union (by simp) (measurableSet_singleton _) (hint.mono_set Ioo_subset_Icc_self) hib,
    integral_singleton, integral_singleton, smul_eq_mul, smul_eq_mul, he]

/-- Periodic support/curvature pairs have equal endpoint contributions. -/
theorem mixedArea_Ico_eq_Ioc {K₁ K₂ : Set (ℝ × ℝ)}
    (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂) :
    (∫ t in Ico 0 (2 * π), supp K₁ t ∂(sigma K₂)) =
      ∫ t in Ioc 0 (2 * π), supp K₁ t ∂(sigma K₂) := by
  have hμ : sigma K₂ {2 * π} = sigma K₂ {0} := by
    have h := sigma_periodic h₂ ({0} : Set ℝ)
    simpa only [image_singleton, zero_add] using h
  have hs : supp K₁ (2 * π) = supp K₁ 0 := by
    simpa only [zero_add] using supp_add_two_pi K₁ 0
  apply integral_Ico_eq_Ioc_of_endpoint_balance (sigma K₂)
    (by linarith [pi_pos]) h₁.continuous_supp
  rw [hs]
  change (sigma K₂ {0}).toReal * supp K₁ 0 =
    (sigma K₂ {2 * π}).toReal * supp K₁ 0
  rw [hμ]

/-- Symmetry of mixed area for arbitrary convex bodies. -/
theorem mixedArea_symm {K₁ K₂ : Set (ℝ × ℝ)}
    (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂) :
    opt_Bs (Ico 0 (2 * π)) K₁ K₂ = opt_Bs (Ico 0 (2 * π)) K₂ K₁ := by
  have key : ∀ {L₁ L₂ : Set (ℝ × ℝ)}, IsConvexBody L₁ → IsConvexBody L₂ →
      opt_Bs (Ico 0 (2 * π)) L₁ L₂ =
        -(∫ t in (0 : ℝ)..(2 * π), opt_g L₁ t * opt_g L₂ t) +
          ∫ t in (0 : ℝ)..(2 * π), supp L₁ t * supp L₂ t := by
    intro L₁ L₂ hL₁ hL₂
    have hs : supp L₁ (2 * π) = supp L₁ 0 := by
      simpa only [zero_add] using supp_add_two_pi L₁ 0
    unfold opt_Bs
    rw [mixedArea_Ico_eq_Ioc hL₁ hL₂,
      opt_supp_ibp hL₁ hL₂ (by linarith [pi_pos] : (0 : ℝ) ≤ 2 * π),
      opt_g_two_pi, hs]
    ring
  rw [key h₁ h₂, key h₂ h₁]
  have e1 : (∫ t in (0 : ℝ)..(2 * π), opt_g K₂ t * opt_g K₁ t) =
      ∫ t in (0 : ℝ)..(2 * π), opt_g K₁ t * opt_g K₂ t := by
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  have e2 : (∫ t in (0 : ℝ)..(2 * π), supp K₂ t * supp K₁ t) =
      ∫ t in (0 : ℝ)..(2 * π), supp K₁ t * supp K₂ t := by
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [e1, e2]

/-- The area first variation on the full convex-body domain. -/
theorem area_firstVariation_convex (K Ks : ConvexBodySet) :
    convexBodyDomain.dirDeriv (fun C => area C.1) K Ks =
      ∫ t in Ico 0 (2 * π), (supp Ks.1 t - supp K.1 t) ∂(sigma K.1) := by
  have hf : (fun C : ConvexBodySet => area C.1) =
      fun C => (1 / 2) * ∫ t in Ico 0 (2 * π), supp C.1 t ∂(sigma C.1) :=
    funext fun C => theorem7_1_3 C.2
  refine ((congrArg (fun f => convexBodyDomain.dirDeriv f K Ks) hf).trans
    (lemma7_1_4 convexBodyDomain
      ((cvx_integral_supp_sigma_bilin (Metric.isBounded_Ico 0 (2 * π))).const_mul (1 / 2))
      K Ks)).trans ?_
  have hsymm := mixedArea_symm K.2 Ks.2
  simp only [opt_Bs] at hsymm
  rw [hsymm]
  have hiK : IntegrableOn (supp K.1) (Ico 0 (2 * π)) (sigma K.1) :=
    (K.2.continuous_supp.continuousOn.integrableOn_compact
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * π)))).mono_set Ico_subset_Icc_self
  have hiKs : IntegrableOn (supp Ks.1) (Ico 0 (2 * π)) (sigma K.1) :=
    (Ks.2.continuous_supp.continuousOn.integrableOn_compact
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * π)))).mono_set Ico_subset_Icc_self
  rw [integral_sub hiKs hiK]
  ring

/-- For normalized caps the lower semicircle contributes nothing, even with atoms. -/
theorem area_firstVariation_caps (K Ks : ConvexBodySet)
    (hK : IsCap K.1 (π / 2)) (hKs : IsCap Ks.1 (π / 2)) :
    convexBodyDomain.dirDeriv (fun C => area C.1) K Ks =
      ∫ t in Icc 0 π, (supp Ks.1 t - supp K.1 t) ∂(sigma K.1) := by
  rw [area_firstVariation_convex]
  apply opt_Ico_eq_Icc hK (Ks.2.continuous_supp.sub K.2.continuous_supp)
  rw [Pi.sub_apply, hKs.2.2.2.2.2.1, hK.2.2.2.2.2.1, sub_self]

end MovingSofaStability
