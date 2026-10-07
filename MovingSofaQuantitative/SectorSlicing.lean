module

public import MovingSofaQuantitative.ActualSetRecovery
public import MovingSofaQuantitative.SectorBudget
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Cartesian integration of the surviving sector

Uncompiled proof source. The recovery region is split into a triangular strip
and a circular segment, with disjoint open ranges of the first coordinate.
The circular primitive follows the elementary calculation in Mathlib's
Archive/Wiedijk100Theorems/AreaOfACircle.lean (James Arthur, Benjamin Davidson,
Andrew Souther; Apache-2.0). No polar Jacobian or numerical quadrature is used.
The two regions omit boundaries, which is harmless for a lower area witness.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability

namespace MovingSofaQuantitative

def circleHeight (ρ x : ℝ) : ℝ := sqrt (ρ ^ 2 - x ^ 2)

def circlePrimitive (ρ x : ℝ) : ℝ :=
  ρ ^ 2 * arcsin (ρ⁻¹ * x) + x * circleHeight ρ x

/-- The derivative is needed only in the interior of the disk's projection. -/
theorem circlePrimitive_hasDerivAt {ρ x : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ Ioo (-ρ) ρ) :
    HasDerivAt (circlePrimitive ρ) (2 * circleHeight ρ x) x := by
  have hrad : 0 < ρ ^ 2 - x ^ 2 := sub_pos_of_lt (sq_lt_sq' hx.1 hx.2)
  have hlo : -(1 : ℝ) < ρ⁻¹ * x := by
    have := mul_lt_mul_of_pos_left hx.1 (inv_pos.mpr hρ)
    simpa [inv_mul_cancel₀ hρ.ne'] using this
  have hhi : ρ⁻¹ * x < 1 := by
    have := mul_lt_mul_of_pos_left hx.2 (inv_pos.mpr hρ)
    simpa [inv_mul_cancel₀ hρ.ne'] using this
  convert (((hasDerivAt_const x (ρ ^ 2)).mul
    ((hasDerivAt_arcsin hlo.ne' hhi.ne).comp x
      ((hasDerivAt_const x ρ⁻¹).mul (hasDerivAt_id x)))).add
    ((hasDerivAt_id x).mul
      ((((hasDerivAt_id x).pow 2).const_sub (ρ ^ 2)).sqrt hrad.ne'))) using 1
  · rfl
  · have hs : sqrt (ρ ^ 2 - x ^ 2) ^ 3 =
        (ρ ^ 2 - x ^ 2) * sqrt (ρ ^ 2 - x ^ 2) := by
      rw [pow_three, ← mul_assoc, mul_self_sqrt hrad.le]
    simp only [circleHeight]
    field_simp
    simp (disch := positivity)
    field

/-- The semicircular cross-section integral, including the singular end by
continuity of the primitive and an interior derivative theorem. -/
theorem integral_circleHeight {ρ a b : ℝ} (hρ : 0 < ρ)
    (ha : -ρ ≤ a) (hab : a ≤ b) (hb : b ≤ ρ) :
    (∫ x in a..b, 2 * circleHeight ρ x) = circlePrimitive ρ b - circlePrimitive ρ a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
  · unfold circlePrimitive circleHeight
    fun_prop
  · intro x hx
    exact circlePrimitive_hasDerivAt hρ
      ⟨ha.trans_lt hx.1, hx.2.trans_le hb⟩
  · exact (show Continuous (fun x => 2 * circleHeight ρ x) by
      unfold circleHeight
      fun_prop).intervalIntegrable a b

/-- A continuous positive strip has twice its height integral as area. -/
theorem area_symmetric_strip {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : Continuous f) (hpos : ∀ x ∈ Ioo a b, 0 ≤ f x) :
    area (regionBetween (fun x => -f x) f (Ioo a b)) =
      ∫ x in a..b, 2 * f x := by
  have hi : IntegrableOn f (Ioo a b) := hf.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have he := volume_regionBetween_eq_integral hi.neg hi measurableSet_Ioo
    (fun x hx => neg_le_self (hpos x hx))
  have hI : (∫ x in Ioo a b, (f - fun x => -f x) x) = ∫ x in a..b, 2 * f x := by
    rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x _
    simp only [Pi.sub_apply]
    ring
  have hnonneg : 0 ≤ ∫ x in a..b, 2 * f x := by
    rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_nonneg measurableSet_Ioo fun x hx => mul_nonneg (by norm_num) (hpos x hx)
  change (volume _).toReal = _
  rw [Measure.volume_eq_prod, he, hI, ENNReal.toReal_ofReal hnonneg]

/-- Slicing above a linear floor gives a triangle of base b-a and height f(b). -/
theorem area_linear_strip {a b m : ℝ} (hab : a ≤ b) (hm : 0 ≤ m) :
    area (regionBetween (fun x => -(m * (x - a))) (fun x => m * (x - a)) (Ioo a b)) =
      m * (b - a) ^ 2 := by
  rw [area_symmetric_strip hab (by fun_prop)
    (fun x hx => mul_nonneg hm (sub_nonneg.mpr hx.1.le))]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => m * (x - a) ^ 2)
    (f' := fun x => 2 * (m * (x - a)))
    (fun x _ => by
      convert (((hasDerivAt_id x).sub_const a).pow 2).const_mul m using 1 <;> ring)
    ((show Continuous (fun x => 2 * (m * (x - a))) by fun_prop).intervalIntegrable a b)
  simpa using hFTC

/-- The rightmost circular segment has area rho^2*a-rho^2*sin(a)*cos(a). -/
theorem area_circular_segment {ρ a : ℝ} (hρ : 0 < ρ) (ha : a ∈ Icc 0 (π / 2)) :
    area (regionBetween (fun x => -circleHeight ρ x) (circleHeight ρ)
      (Ioo (ρ * cos a) ρ)) = ρ ^ 2 * (a - sin a * cos a) := by
  have hc : 0 ≤ cos a := cos_nonneg_of_mem_Icc ⟨by linarith [ha.1, pi_pos], ha.2⟩
  have hs : 0 ≤ sin a := sin_nonneg_of_mem_Icc ⟨ha.1, by linarith [ha.2, pi_pos]⟩
  have hproj : ρ * cos a ≤ ρ := by nlinarith [cos_le_one a]
  rw [area_symmetric_strip hproj (by unfold circleHeight; fun_prop)
    (fun _ _ => sqrt_nonneg _), integral_circleHeight hρ (by nlinarith) hproj le_rfl]
  have hroot : circleHeight ρ (ρ * cos a) = ρ * sin a := by
    apply (sq_eq_sq₀ (sqrt_nonneg _) (mul_nonneg hρ.le hs)).mp
    unfold circleHeight
    rw [sq_sqrt (by nlinarith [sin_sq_add_cos_sq a])]
    nlinarith [sin_sq_add_cos_sq a]
  have harc : arcsin (cos a) = π / 2 - a := by
    rw [← sin_pi_div_two_sub]
    exact arcsin_sin (by linarith [ha.2, pi_pos]) (by linarith [ha.1])
  simp only [circlePrimitive, circleHeight, sub_self, sqrt_zero, mul_zero]
  rw [show ρ⁻¹ * ρ = 1 from inv_mul_cancel₀ hρ.ne', arcsin_one,
    show ρ⁻¹ * (ρ * cos a) = cos a by rw [← mul_assoc, inv_mul_cancel₀ hρ.ne', one_mul],
    harc]
  change ρ ^ 2 * (π / 2) - (ρ ^ 2 * (π / 2 - a) + ρ * cos a * circleHeight ρ (ρ * cos a)) = _
  rw [hroot]
  ring

/-- Region-between constructions with disjoint horizontal intervals are disjoint. -/
theorem strips_disjoint {a b c : ℝ} (f g : ℝ → ℝ) :
    Disjoint (regionBetween (fun x => -f x) f (Ioo a b))
      (regionBetween (fun x => -g x) g (Ioo b c)) := by
  rw [Set.disjoint_left]
  intro p hp hq
  exact (not_lt_of_ge hp.1.2.le) hq.1.1

/-- Add areas of bounded measurable regions without relying on totalized
`ENNReal.toReal` for an infinite measure. -/
theorem area_union_disjoint_compact_bounds {A B K : Set Point}
    (hK : IsCompact K) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAK : A ⊆ K) (hBK : B ⊆ K) (hdis : Disjoint A B) :
    area (A ∪ B) = area A + area B := by
  have hfin : volume K ≠ ⊤ := hK.isBounded.measure_lt_top.ne
  have hAf := volume_ne_top_of_subset hAK hfin
  have hBf := volume_ne_top_of_subset hBK hfin
  unfold area
  rw [measure_union hdis hB, ENNReal.toReal_add hAf hBf]

end MovingSofaQuantitative
