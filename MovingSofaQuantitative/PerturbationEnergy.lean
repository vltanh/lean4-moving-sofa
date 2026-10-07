module

public import MovingSofaQuantitative.SymmetricCapPerturbation
public import MovingSofaQuantitative.ResidualAlgebra

/-!
# Exact residual energy of the constructed cap

Uncompiled proof source. The support identity is exact at positive amplitudes.
Uniqueness of right derivatives identifies the actual support derivatives, and
integrability is inherited from Mamikon's theorem for the constructed cap.
No independently asserted energy formula is attached to an abstract profile.
-/

@[expose] public section
noncomputable section

open Real Set Filter Topology MeasureTheory
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative
namespace HalfCapProfile

variable {φ : ℝ} (F : HalfCapProfile φ)

def symmetricDerivative (t : ℝ) : ℝ :=
  if t < π / 2 then F.first t else -F.first (π - t)

def pinnedProfile := pinnedDifference F.symmetricValue
def pinnedProfileDerivative := pinnedDerivative F.symmetricValue F.symmetricDerivative

theorem symmetricValue_eq_join : F.symmetricValue =
    rightJoin (π / 2) F.value (fun t => F.value (π - t)) := by
  funext t
  unfold symmetricValue rightJoin
  split_ifs <;> try rfl
  · have he : t = π / 2 := by linarith
    subst t
    congr 1
    ring
  · exfalso
    linarith

theorem symmetricValue_continuous : Continuous F.symmetricValue := by
  rw [F.symmetricValue_eq_join]
  exact continuous_rightJoin F.continuous_value
    (F.continuous_value.comp (continuous_const.sub continuous_id))
    (by congr 1; ring)

theorem symmetricValue_rightDeriv (t : ℝ) :
    HasDerivWithinAt F.symmetricValue (F.symmetricDerivative t) (Ioi t) t := by
  rw [F.symmetricValue_eq_join]
  apply rightDeriv_rightJoin (fun u => (F.derivative u).hasDerivWithinAt)
  intro u
  convert ((F.derivative (π - u)).comp u ((hasDerivAt_id u).const_sub π)).hasDerivWithinAt using 1 <;> ring

theorem pinnedProfile_rightDeriv (t : ℝ) :
    HasDerivWithinAt F.pinnedProfile (F.pinnedProfileDerivative t) (Ioi t) t := by
  convert (F.symmetricValue_rightDeriv t).add
    ((hasDerivAt_cos t).hasDerivWithinAt.const_mul (F.symmetricValue π)) using 1 <;>
    simp only [pinnedProfile, pinnedProfileDerivative, pinnedDifference, pinnedDerivative] <;> ring

@[simp] theorem symmetricValue_top : F.symmetricValue (π / 2) = 0 := by
  simp only [symmetricValue, if_pos le_rfl, F.top_zero]

@[simp] theorem symmetricValue_zero : F.symmetricValue 0 = F.value 0 := by
  simp [symmetricValue, pi_pos.le]

@[simp] theorem symmetricValue_pi : F.symmetricValue π = F.value 0 := by
  simp [symmetricValue, not_le.mpr (show π / 2 < π by linarith [pi_pos])]

end HalfCapProfile

/-- Right derivatives of two profiles agreeing on the upper arc agree at every
interior point; corners do not require a two-sided derivative. -/
theorem rightDerivative_eq_of_upper_profile {f df g dg : ℝ → ℝ}
    (hf : ∀ t ∈ Ioo (0 : ℝ) π, HasDerivWithinAt f (df t) (Ioi t) t)
    (hg : ∀ t ∈ Ioo (0 : ℝ) π, HasDerivWithinAt g (dg t) (Ioi t) t)
    (he : EqOn f g (Icc (0 : ℝ) π)) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) π) : df t = dg t := by
  have hh : HasDerivWithinAt g (df t) (Ioi t) t := by
    apply (hf t ht).congr_of_eventuallyEq
    · have hn : Ioo (0 : ℝ) π ∈ 𝓝[Ioi t] t :=
        mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds ht)
      filter_upwards [hn] with u hu
      exact he (Ioo_subset_Icc_self hu)
    · exact he (Ioo_subset_Icc_self ht)
  exact hh.unique (uniqueDiffWithinAt_Ioi t) (hg t ht)

theorem arcSquare_eq_smul_on {a b c : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (he : ∀ t ∈ Ioo a b, f t = c * g t) :
    arcSquare a b f = c ^ 2 * arcSquare a b g := by
  unfold arcSquare
  rw [intervalIntegral_eq_of_eqOn_Ioo hab (f := fun t => f t ^ 2)
    (g := fun t => c ^ 2 * g t ^ 2) (fun t ht => by rw [he t ht]; ring),
    intervalIntegral.integral_const_mul]

theorem integrable_unscale_on {a b c : ℝ} (hab : a ≤ b) (hc : c ≠ 0)
    {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume a b)
    (he : ∀ t ∈ Ioo a b, f t = c * g t) : IntervalIntegrable g volume a b := by
  apply intervalIntegrable_of_eqOn_Ioo hab (hf.div_const c)
  intro t ht
  rw [he t ht]
  field_simp [hc]

/-- An exact scalar profile for the support difference of the actual cap. -/
theorem perturbedCap_pinned_support {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (F : HalfCapProfile P.φ) {τ : ℝ} (hτ : 0 ≤ τ) (hsmall : τ ≤ F.safeAmplitude)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) π) :
    capDifference P.cap (perturbedCap hP hbox F τ hτ hsmall).1 t = τ * F.pinnedProfile t := by
  unfold capDifference pinnedDifference HalfCapProfile.pinnedProfile
  rw [perturbedCap_support hP hbox F τ hτ hsmall ht,
    perturbedCap_support hP hbox F τ hτ hsmall ⟨pi_pos.le, le_rfl⟩]
  ring

/-- Mamikon integrability and the exact energy identity are simultaneous. -/
theorem perturbedCap_data_energy {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (F : HalfCapProfile P.φ) {τ : ℝ} (hτ : 0 < τ) (hsmall : τ ≤ F.safeAmplitude) :
    FourResidualData P.φ F.pinnedProfile F.pinnedProfileDerivative ∧
      capResidualEnergy P.φ (wideGerverTriple hP hbox).1.1
        (perturbedCap hP hbox F τ hτ.le hsmall) =
      τ ^ 2 * fourResidualEnergy P.φ F.pinnedProfile F.pinnedProfileDerivative := by
  let K := perturbedCap hP hbox F τ hτ.le hsmall
  let f := capDifference P.cap K.1
  let df := capDifferenceDeriv P.cap K.1
  have hφ := GerverParams.gm_φ_mem_Ioo hP hbox
  obtain ⟨hdata, henergy⟩ := capDifference_data hφ
    (wideGerverTriple hP hbox).1.1 K (wideGerverTriple hP hbox).2.1
    (perturbedCap_isCap hP hbox F τ hτ.le hsmall)
  have hs : ∀ t ∈ Icc (0 : ℝ) π, f t = τ * F.pinnedProfile t :=
    fun t ht => perturbedCap_pinned_support hP hbox F hτ.le hsmall ht
  have hd : ∀ t ∈ Ioo (0 : ℝ) π, df t = τ * F.pinnedProfileDerivative t := by
    intro t ht
    exact rightDerivative_eq_of_upper_profile hdata.rightDeriv
      (fun u _ => (F.pinnedProfile_rightDeriv u).const_mul τ) (fun t ht => hs t ht) ht
  have htangent {T t : ℝ} (hT : T ∈ Icc (0 : ℝ) π) (ht : t ∈ Ioo (0 : ℝ) π) :
      tangentResidual T f df t = τ * tangentResidual T F.pinnedProfile F.pinnedProfileDerivative t := by
    unfold tangentResidual
    rw [hs T hT, hs t (Ioo_subset_Icc_self ht), hd t ht]
    ring
  have hcorner {t : ℝ} (ht : t ∈ Ioo P.φ (π / 2 - P.φ)) :
      cornerResidual f df t = τ * cornerResidual F.pinnedProfile F.pinnedProfileDerivative t := by
    unfold cornerResidual
    rw [hs (t + π / 2) ⟨by linarith [ht.1, hφ.1, pi_pos], by linarith [ht.2, hφ.1]⟩,
      hd t ⟨by linarith [ht.1, hφ.1], by linarith [ht.2, hφ.1, pi_pos]⟩]
    ring
  have h1 : ∀ t ∈ Ioo (0 : ℝ) P.φ, tangentResidual (π / 2) f df t =
      τ * tangentResidual (π / 2) F.pinnedProfile F.pinnedProfileDerivative t := by
    intro t ht
    exact htangent ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
      ⟨ht.1, by linarith [ht.2, hφ.2, pi_pos]⟩
  have h3 : ∀ t ∈ Ioo (π / 2 - P.φ) (π / 2), tangentResidual (π - P.φ) f df t =
      τ * tangentResidual (π - P.φ) F.pinnedProfile F.pinnedProfileDerivative t := by
    intro t ht
    exact htangent ⟨by linarith [hφ.2, pi_pos], by linarith [hφ.1]⟩
      ⟨by linarith [ht.1, hφ.2, pi_pos], by linarith [ht.2, pi_pos]⟩
  have h4 : ∀ t ∈ Ioo (π / 2) π, tangentResidual π f df t =
      τ * tangentResidual π F.pinnedProfile F.pinnedProfileDerivative t := by
    intro t ht
    exact htangent ⟨pi_pos.le, le_rfl⟩ ⟨by linarith [ht.1, pi_pos], ht.2⟩
  have horder2 : P.φ ≤ π / 2 - P.φ := by linarith [hφ.2]
  have horder3 : π / 2 - P.φ ≤ π / 2 := by linarith [hφ.1]
  have horder4 : π / 2 ≤ π := by linarith [pi_pos]
  have square_eq {a b : ℝ} {r s : ℝ → ℝ} (he : ∀ t ∈ Ioo a b, r t = τ * s t) :
      ∀ t ∈ Ioo a b, r t ^ 2 = τ ^ 2 * s t ^ 2 := by
    intro t ht
    rw [he t ht]
    ring
  refine ⟨⟨F.symmetricValue_continuous.add
      (continuous_cos.const_mul (F.symmetricValue π)),
    fun t _ => F.pinnedProfile_rightDeriv t,
    by simp [HalfCapProfile.pinnedProfile, pinnedDifference, F.symmetricValue_top],
    by simp [HalfCapProfile.pinnedProfile],
    integrable_unscale_on hφ.1.le hτ.ne' hdata.first h1,
    integrable_unscale_on horder2 hτ.ne' hdata.middle hcorner,
    integrable_unscale_on horder3 hτ.ne' hdata.third h3,
    integrable_unscale_on horder4 hτ.ne' hdata.last h4,
    integrable_unscale_on hφ.1.le (pow_ne_zero 2 hτ.ne') hdata.first_sq (square_eq h1),
    integrable_unscale_on horder2 (pow_ne_zero 2 hτ.ne') hdata.middle_sq (square_eq hcorner),
    integrable_unscale_on horder3 (pow_ne_zero 2 hτ.ne') hdata.third_sq (square_eq h3),
    integrable_unscale_on horder4 (pow_ne_zero 2 hτ.ne') hdata.last_sq (square_eq h4)⟩, ?_⟩
  rw [← henergy]
  unfold fourResidualEnergy
  rw [arcSquare_eq_smul_on hφ.1.le h1, arcSquare_eq_smul_on horder2 hcorner,
    arcSquare_eq_smul_on horder3 h3, arcSquare_eq_smul_on horder4 h4]
  ring

/-- Every admitted half-profile has genuine square-integrable residuals. -/
theorem halfCapProfile_data {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (F : HalfCapProfile P.φ) : FourResidualData P.φ F.pinnedProfile F.pinnedProfileDerivative :=
  (perturbedCap_data_energy hP hbox F F.safeAmplitude_pos le_rfl).1

end MovingSofaQuantitative
