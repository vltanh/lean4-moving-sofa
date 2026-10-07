module

public import MovingSofaQuantitative.AuxiliaryPenalties

/-!
# Actual auxiliary supports in the cap's translation convention

Uncompiled proof source. The functions are defined from the two genuine convex
auxiliary bodies, not chosen independently. Shifting their normal by pi and
using the opposite horizontal translation keeps each paired wall slack invariant.
The energy identities retain the factor two from Mamikon's formula.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability

namespace MovingSofaQuantitative

/-- Auxiliary support difference at normal pi+t, in the same geometric frame
as a cap difference whose added cosine coefficient is a. -/
def auxiliaryDifference (B₀ B₁ : Set Point) (a t : ℝ) : ℝ :=
  supp B₁ (π + t) - supp B₀ (π + t) - a * cos t

def auxiliaryDerivative (B₀ B₁ : Set Point) (a t : ℝ) : ℝ :=
  opt_g B₁ (π + t) - opt_g B₀ (π + t) + a * sin t

theorem auxiliaryDifference_continuous (B₀ B₁ : ConvexBodySet) (a : ℝ) :
    Continuous (auxiliaryDifference B₀.1 B₁.1 a) := by
  exact ((B₁.2.continuous_supp.comp (continuous_const.add continuous_id)).sub
    (B₀.2.continuous_supp.comp (continuous_const.add continuous_id))).sub
    (continuous_cos.const_mul a)

theorem auxiliaryDifference_rightDeriv (B₀ B₁ : ConvexBodySet) (a t : ℝ) :
    HasDerivWithinAt (auxiliaryDifference B₀.1 B₁.1 a)
      (auxiliaryDerivative B₀.1 B₁.1 a t) (Ioi t) t := by
  have hi : HasDerivWithinAt (fun s : ℝ => π + s) 1 (Ioi t) t :=
    ((hasDerivAt_id t).const_add π).hasDerivWithinAt
  have hm : MapsTo (fun s : ℝ => π + s) (Ioi t) (Ici (π + t)) :=
    fun s hs => by change π + t ≤ π + s; linarith [hs]
  have h₀ := (hasDerivWithinAt_supp_right B₀.2 (π + t)).comp t hi hm
  have h₁ := (hasDerivWithinAt_supp_right B₁.2 (π + t)).comp t hi hm
  convert (h₁.sub h₀).sub ((hasDerivAt_cos t).const_mul a).hasDerivWithinAt using 1
  · rfl
  · simp only [auxiliaryDerivative, opt_g, mul_one]
    ring

/-- Normal shifting and simultaneous horizontal translation leave the tangent
residual unchanged on every nonsingular point. -/
theorem auxiliaryResidual_shift (B₀ B₁ : Set Point) (a T t : ℝ)
    (hs : sin (T - t) ≠ 0) :
    tangentResidual T (auxiliaryDifference B₀ B₁ a) (auxiliaryDerivative B₀ B₁ a) t =
      tangentResidual (π + T) (capDifference B₀ B₁) (capDifferenceDeriv B₀ B₁) (π + t) := by
  have hc : cos T = cos t * cos (T - t) - sin t * sin (T - t) := by
    rw [← cos_add, add_sub_cancel]
  unfold tangentResidual auxiliaryDifference auxiliaryDerivative
    capDifference capDifferenceDeriv pinnedDifference pinnedDerivative
  rw [show π + T - (π + t) = T - t by ring]
  simp only [cos_add_pi, cos_pi_add, sin_add_pi, sin_pi_add]
  field_simp [hs]
  linear_combination (supp B₁ π - supp B₀ π - a) * hc

/-- The auxiliary L2 data and its exact energy, transported from the integrated
Mamikon theorem. An isolated singular endpoint is removed by the open-arc API. -/
theorem auxiliaryResidual_data (B₀ B₁ : ConvexBodySet) (s : ℝ)
    {a b T : ℝ} (hab : a < b) (hb : b < a + π) (haT : T - π < a) (hbT : b ≤ T) :
    IntervalIntegrable (tangentResidual T (auxiliaryDifference B₀.1 B₁.1 s)
      (auxiliaryDerivative B₀.1 B₁.1 s)) volume a b ∧
    IntervalIntegrable (fun t => tangentResidual T (auxiliaryDifference B₀.1 B₁.1 s)
      (auxiliaryDerivative B₀.1 B₁.1 s) t ^ 2) volume a b ∧
    arcSquare a b (tangentResidual T (auxiliaryDifference B₀.1 B₁.1 s)
      (auxiliaryDerivative B₀.1 B₁.1 s)) =
      2 * displacementEnergy (π + a) (π + b)
        (fun B => tangentParam B.1 (π + T)) B₀ B₁ := by
  let R := tangentResidual (π + T) (capDifference B₀.1 B₁.1) (capDifferenceDeriv B₀.1 B₁.1)
  let r := tangentResidual T (auxiliaryDifference B₀.1 B₁.1 s) (auxiliaryDerivative B₀.1 B₁.1 s)
  obtain ⟨hi, hi2, he⟩ := tangent_capDifference_integrable
    (a := π + a) (b := π + b) (T := π + T)
    (by linarith) (by linarith) (by linarith) (by linarith) B₀ B₁
  have hshift : IntervalIntegrable (fun t => R (π + t)) volume a b := by
    simpa only [add_sub_cancel_left] using hi.comp_add_left π
  have hshift2 : IntervalIntegrable (fun t => R (π + t) ^ 2) volume a b := by
    simpa only [add_sub_cancel_left] using hi2.comp_add_left π
  have hr : ∀ t ∈ Ioo a b, r t = R (π + t) := by
    intro t ht
    exact auxiliaryResidual_shift B₀.1 B₁.1 s T t
      (sin_pos_of_pos_of_lt_pi (by linarith [ht.2]) (by linarith [ht.1])).ne'
  have hir : IntervalIntegrable r volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le] at hshift ⊢
    exact hshift.congr_fun (fun t ht => (hr t ht).symm) measurableSet_Ioo
  have hir2 : IntervalIntegrable (fun t => r t ^ 2) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le] at hshift2 ⊢
    exact hshift2.congr_fun (fun t ht => by rw [hr t ht]) measurableSet_Ioo
  refine ⟨hir, hir2, ?_⟩
  change arcSquare a b r = _
  have hint : arcSquare a b r = ∫ t in a..b, R (π + t) ^ 2 := by
    unfold arcSquare
    rw [intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hab.le,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun t ht => by rw [hr t ht]
  rw [hint]
  have htranslate : (∫ t in a..b, R (π + t) ^ 2) =
      ∫ t in (π + a)..(π + b), R t ^ 2 := by
    simpa only [add_comm] using intervalIntegral.integral_comp_add_right (fun t => R t ^ 2) π
  rw [htranslate]
  exact he

def rightAuxiliaryProfile {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) : ℝ → ℝ :=
  auxiliaryDifference (wideGerverTriple hP hbox).1.2.1.1 x.1.2.1.1
    (supp x.1.1.1 π - supp P.cap π)

def leftAuxiliaryProfile {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) : ℝ → ℝ :=
  auxiliaryDifference (wideGerverTriple hP hbox).1.2.2.1 x.1.2.2.1
    (supp x.1.1.1 π - supp P.cap π)

def rightWallSlack {P : GerverParams} (x : WideTriple P.φ) (t : ℝ) : ℝ :=
  1 - supp x.1.1.1 t - supp x.1.2.1.1 (π + t)

def leftWallSlack {P : GerverParams} (x : WideTriple P.φ) (t : ℝ) : ℝ :=
  1 - supp x.1.1.1 t - supp x.1.2.2.1 (π + t)

theorem rightWallSlack_nonneg {P : GerverParams} (x : WideTriple P.φ)
    {t : ℝ} (ht : t ∈ Icc P.φ (π / 2)) : 0 ≤ rightWallSlack x t := by
  have h := x.2.2.2.2.2.2.1 t ht
  unfold rightWallSlack
  linarith

theorem leftWallSlack_nonneg {P : GerverParams} (x : WideTriple P.φ)
    {t : ℝ} (ht : t ∈ Icc (π / 2) (π - P.φ)) : 0 ≤ leftWallSlack x t := by
  have h := x.2.2.2.2.2.2.2.2.2.1 (t - π / 2)
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [show π / 2 + (t - π / 2) = t by ring,
    show 3 * π / 2 + (t - π / 2) = π + t by ring] at h
  unfold leftWallSlack
  linarith

/-- Both profiles vanish at the top; the two cut contacts are exact. -/
theorem auxiliaryProfile_contacts {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    rightAuxiliaryProfile hP hbox x (π / 2) = 0 ∧
    leftAuxiliaryProfile hP hbox x (π / 2) = 0 ∧
    rightAuxiliaryProfile hP hbox x P.φ = -capDifference P.cap x.1.1.1 P.φ ∧
    leftAuxiliaryProfile hP hbox x (π - P.φ) = -capDifference P.cap x.1.1.1 (π - P.φ) := by
  have h := inWideL_supp x.2
  have hG := inWideL_supp (wideGerverTriple hP hbox).2
  simp only [rightAuxiliaryProfile, leftAuxiliaryProfile, auxiliaryDifference,
    capDifference, pinnedDifference, cos_pi_div_two, mul_zero, sub_zero,
    show π + π / 2 = 3 * π / 2 by ring,
    show π + (π - P.φ) = 3 * π / 2 + (π / 2 - P.φ) by ring]
  rw [h.1, hG.1, h.2.1, hG.2.1, h.2.2.1, hG.2.2.1, h.2.2.2, hG.2.2.2]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- On the reference active arc, the actual wall gap is precisely minus the
paired profile. No assumption about zero dual slack has yet been made. -/
theorem rightProfile_on_active {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) {t : ℝ} (ht : t ∈ Icc (π / 2 - P.θ) (π / 2)) :
    rightAuxiliaryProfile hP hbox x t =
      -capDifference P.cap x.1.1.1 t - rightWallSlack x t := by
  have h := (theorem8_4_3_three hP hbox).2 t ht
  unfold rightAuxiliaryProfile auxiliaryDifference capDifference pinnedDifference rightWallSlack
  change supp x.1.2.1.1 (π + t) - supp (rightBody P.φ P.cap) (π + t) -
      (supp x.1.1.1 π - supp P.cap π) * cos t = _
  linarith

theorem leftProfile_on_active {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) {t : ℝ} (ht : t ∈ Icc (π / 2) (π / 2 + P.θ)) :
    leftAuxiliaryProfile hP hbox x t =
      -capDifference P.cap x.1.1.1 t - leftWallSlack x t := by
  have h := (theorem8_4_3_three hP hbox).1 (t - π / 2)
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [show π / 2 + (t - π / 2) = t by ring,
    show 3 * π / 2 + (t - π / 2) = π + t by ring] at h
  unfold leftAuxiliaryProfile auxiliaryDifference capDifference pinnedDifference leftWallSlack
  change supp x.1.2.2.1 (π + t) - supp (leftBody P.φ P.cap) (π + t) -
      (supp x.1.1.1 π - supp P.cap π) * cos t = _
  linarith

end MovingSofaQuantitative
