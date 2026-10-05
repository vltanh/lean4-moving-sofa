module

public import MovingSofaStability.WideFirstVariation

/-!
# Gerver's certificate on the enlarged nonsmooth domain

Uncompiled proof source. Only the fixed reference sofa supplies regularity.
The competing triple has arbitrary convex bodies and a normalized cap, with
no injectivity or curvature-density assumption. Gerver's existing measure
identity cancels the core contribution in the first variation.

This proves the algebraic maximum and exact quadratic deficit. Applying it to
a sofa still requires the geometric canonical-triple and local upper-bound
lemmas: they are not assumed to follow from this algebraic certificate.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness
open GerverParams

namespace MovingSofaStability

def wideGerverTriple {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) : WideTriple P.φ :=
  toWideTriple (gerverTriple hP hbox)

/-- First-variation sign towards every enlarged-domain competitor. -/
theorem gerver_wide_firstVariation_nonpos {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) (xs : WideTriple P.φ) :
    (wideDomain P.φ).dirDeriv (wideUpperQ P.φ) (wideGerverTriple hP hbox) xs ≤ 0 := by
  obtain ⟨h1, -, -, -, h4, -, -, -⟩ := theorem8_4_3_two hP hbox
  rw [wide_reference_firstVariation (gm_φ_mem_Ioo hP hbox)
    (wideGerverTriple hP hbox) xs (gerverTriple hP hbox).2.1 h4.symm h1.symm]
  have hL : InWideL P.φ xs.1.1.1 xs.1.2.1.1 xs.1.2.2.1 := xs.2
  have hKs : IsConvexBody xs.1.1.1 := xs.1.1.2
  have hBs : IsConvexBody xs.1.2.1.1 := xs.1.2.1.2
  have hDs : IsConvexBody xs.1.2.2.1 := xs.1.2.2.2
  have hK := gm_isConvexBody_cap hP hbox
  have hB := gm_isConvexBody_B hP hbox
  have hD := gm_isConvexBody_D hP hbox
  have h01 := gm_φ_pos hP
  have h12 := gm_φ_lt_θ hP
  have h23 := gm_θ_lt_c hP
  have h34 := gm_c_lt_d hP
  have h45 := gm_d_lt hP
  have hpi := pi_pos
  set f : ℝ → ℝ := fun t => supp xs.1.1.1 t - supp P.cap t with hf
  set gB : ℝ → ℝ := fun t => suppBreve xs.1.2.1.1 t -
    suppBreve (rightBody P.φ P.cap) t with hgB
  set gD : ℝ → ℝ := fun t => suppBreve xs.1.2.2.1 t -
    suppBreve (leftBody P.φ P.cap) t with hgD
  have hfc : Continuous f :=
    (continuous_supp hKs.2.1).sub (continuous_supp hK.2.1)
  have hgBc : Continuous gB :=
    ((continuous_supp hBs.2.1).comp (continuous_id.add continuous_const)).sub
      ((continuous_supp hB.2.1).comp (continuous_id.add continuous_const))
  have hgDc : Continuous gD :=
    ((continuous_supp hDs.2.1).comp (continuous_id.add continuous_const)).sub
      ((continuous_supp hD.2.1).comp (continuous_id.add continuous_const))
  set Sι := Icc P.φ (π / 2 - P.φ) ∪ Icc (P.φ + π / 2) (π - P.φ) with hSι
  set ι := (iota P.cap).restrict Sι
  set β := (sigmaBreve (rightBody P.φ P.cap)).restrict (Ico (π / 2 - P.θ) (π / 2))
  set δ := (sigmaBreve (leftBody P.φ P.cap)).restrict (Ioc (π / 2) (π / 2 + P.θ))
  set τ := (sigma P.cap).restrict {π / 2}
  have hdec : (sigma P.cap).restrict (Icc 0 π) = ι + β + δ + τ := gm_sigma_decomp hP hbox
  have iσ : ∀ g : ℝ → ℝ, Continuous g → Integrable g ((sigma P.cap).restrict (Icc 0 π)) :=
    fun g hg => hg.continuousOn.integrableOn_compact isCompact_Icc
  have leι : ι ≤ ι + β + δ + τ :=
    Measure.le_add_right (Measure.le_add_right (Measure.le_add_right le_rfl))
  have leβ : β ≤ ι + β + δ + τ :=
    Measure.le_add_right (Measure.le_add_right (Measure.le_add_left le_rfl))
  have leδ : δ ≤ ι + β + δ + τ := Measure.le_add_right (Measure.le_add_left le_rfl)
  have leτ : τ ≤ ι + β + δ + τ := Measure.le_add_left le_rfl
  have iι : Integrable f ι := (iσ f hfc).mono_measure (by rw [hdec]; exact leι)
  have iβ : ∀ g : ℝ → ℝ, Continuous g → Integrable g β :=
    fun g hg => (iσ g hg).mono_measure (by rw [hdec]; exact leβ)
  have iδ : ∀ g : ℝ → ℝ, Continuous g → Integrable g δ :=
    fun g hg => (iσ g hg).mono_measure (by rw [hdec]; exact leδ)
  have iτ : Integrable f τ := (iσ f hfc).mono_measure (by rw [hdec]; exact leτ)
  have eI1 : (∫ t in Icc 0 π, f t ∂(sigma P.cap)) =
      (∫ t, f t ∂ι) + (∫ t, f t ∂β) + (∫ t, f t ∂δ) := by
    rw [hdec, integral_add_measure ((iι.add_measure (iβ f hfc)).add_measure (iδ f hfc)) iτ,
      integral_add_measure (iι.add_measure (iβ f hfc)) (iδ f hfc),
      integral_add_measure iι (iβ f hfc)]
    have he : ∫ t, f t ∂τ = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro t ht
      rw [mem_singleton_iff] at ht
      simp only [hf, ht, hL.1.2.2.2.1, gm_supp_cap_pi_div_two hP hbox, sub_self]
    rw [he, add_zero]
  have eI2 : (∫ t in Sι, f t * iFun P.cap t) = ∫ t, f t ∂ι := by
    have hS : Sι ⊆ Icc 0 π := by
      rintro t (ht | ht) <;> exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hm : Measurable (fun t => ENNReal.ofReal (iFun P.cap t)) := by
      unfold iFun
      exact (Measurable.ite measurableSet_Iic
        (gm_measurable_dot (measurable_deriv _) (by unfold vvec; fun_prop))
        (gm_measurable_dot ((measurable_deriv _).comp (measurable_id.sub_const _))
          (by unfold uvec; fun_prop)).neg).ennreal_ofReal
    rw [show ι = (volume.restrict Sι).withDensity (fun t => ENNReal.ofReal (iFun P.cap t)) from
        gm_iota_restrict (measurableSet_Icc.union measurableSet_Icc) hS,
      integral_withDensity_eq_integral_toReal_smul hm
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply setIntegral_congr_fun (measurableSet_Icc.union measurableSet_Icc)
    intro t ht
    have hpos : 0 ≤ iFun P.cap t := by
      rcases ht with ht | ht
      · have hlo : t ∈ Ioo 0 (π / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
        rw [iFun, ite_eq_left hlo.2.le]
        exact ((theorem6_1_2 hP hbox).2.2 t hlo).2.le
      · have hτ : t - π / 2 ∈ Ioo 0 (π / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
        rw [iFun, ite_eq_right (not_le.2 (by linarith [ht.1]))]
        linarith [((theorem6_1_2 hP hbox).2.2 _ hτ).1]
    simp only [ENNReal.toReal_ofReal hpos, smul_eq_mul, mul_comm]
  have eI3 : (∫ t in Ioo P.φ (π / 2), gB t ∂(sigmaBreve (rightBody P.φ P.cap))) =
      ∫ t, gB t ∂β := by
    rw [gm_sigmaBreve_B_restrict hP hbox]
  have eI4 : (∫ t in Ioo (π / 2) (π / 2 + (π / 2 - P.φ)), gD t
      ∂(sigmaBreve (leftBody P.φ P.cap))) = ∫ t, gD t ∂δ := by
    rw [gm_sigmaBreve_D_restrict hP hbox]
  change (∫ t in Icc 0 π, f t ∂(sigma P.cap)) - (∫ t in Sι, f t * iFun P.cap t) +
      (∫ t in Ioo P.φ (π / 2), gB t ∂(sigmaBreve (rightBody P.φ P.cap))) +
      (∫ t in Ioo (π / 2) (π / 2 + (π / 2 - P.φ)), gD t
        ∂(sigmaBreve (leftBody P.φ P.cap))) ≤ 0
  rw [eI1, eI2, eI3, eI4]
  have kB : (∫ t, f t ∂β) + (∫ t, gB t ∂β) ≤ 0 := by
    rw [← integral_add (iβ f hfc) (iβ gB hgBc)]
    apply setIntegral_nonpos measurableSet_Ico
    intro t ht
    have h1 := hL.2.2.2.2.2.1 t ⟨by linarith [ht.1], ht.2.le⟩
    have h2 := (theorem8_4_3_three hP hbox).2 t ⟨ht.1, ht.2.le⟩
    simp only [hf, hgB, suppBreve]
    rw [add_comm t π]
    linarith
  have kD : (∫ t, f t ∂δ) + (∫ t, gD t ∂δ) ≤ 0 := by
    rw [← integral_add (iδ f hfc) (iδ gD hgDc)]
    apply setIntegral_nonpos measurableSet_Ioc
    intro t ht
    have h1 := hL.2.2.2.2.2.2.2.2.1 (t - π / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h2 := (theorem8_4_3_three hP hbox).1 (t - π / 2)
      ⟨show (0 : ℝ) ≤ t - π / 2 by linarith [ht.1],
        show t - π / 2 ≤ P.θ by linarith [ht.2]⟩
    rw [show π / 2 + (t - π / 2) = t by ring,
      show 3 * π / 2 + (t - π / 2) = t + π by ring] at h1 h2
    simp only [hf, hgD, suppBreve]
    linarith
  linarith

/-- Gerver maximizes the ORIGINAL Q on all nonsmooth feasible triples. -/
theorem wideUpperQ_le_gerver {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) (x : WideTriple P.φ) :
    wideUpperQ P.φ x ≤ wideUpperQ P.φ (wideGerverTriple hP hbox) :=
  (wide_maximum_iff_firstVariation (gm_φ_mem_Ioo hP hbox) (wideGerverTriple hP hbox)).2
    (gerver_wide_firstVariation_nonpos hP hbox) x

@[simp] theorem wideGerver_value {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    wideUpperQ P.φ (wideGerverTriple hP hbox) = area (gerverSofa P) :=
  gerver_upperQL_eq_area hP hbox

/-- Dual slack on the enlarged domain. Its sign is established, not assumed. -/
def wideDualSlack {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) : ℝ :=
  -(wideDomain P.φ).dirDeriv (wideUpperQ P.φ) (wideGerverTriple hP hbox) x

theorem wideDualSlack_nonneg {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) : 0 ≤ wideDualSlack hP hbox x :=
  neg_nonneg.mpr (gerver_wide_firstVariation_nonpos hP hbox x)

/-- The exact deficit is dual slack plus quadratic energy, without a Taylor error. -/
theorem wide_deficit_identity {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    area (gerverSofa P) - wideUpperQ P.φ x = wideDualSlack hP hbox x +
      segmentEnergy (wideDomain P.φ) (wideUpperQ P.φ) (wideGerverTriple hP hbox) x := by
  have h := deficit_eq_neg_dirDeriv_add_energy (wideDomain P.φ)
    (wideUpperQ_quadratic (gm_φ_mem_Ioo hP hbox)) (wideGerverTriple hP hbox) x
  simpa only [wideGerver_value, wideDualSlack] using h

theorem wide_energy_le_deficit {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    segmentEnergy (wideDomain P.φ) (wideUpperQ P.φ) (wideGerverTriple hP hbox) x ≤
      area (gerverSofa P) - wideUpperQ P.φ x := by
  rw [wide_deficit_identity hP hbox x]
  exact le_add_of_nonneg_left (wideDualSlack_nonneg hP hbox x)

end MovingSofaStability
