module

public import MovingSofaStability.SharpKernelNorms

/-!
# Sharp evaluation of the four residuals

Uncompiled proof source. Kernel norms and residual energies are kept separate.
The two pieces of r4 on the middle arc are recombined using their disjoint
integration intervals, so the same energy is not counted twice.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory

namespace MovingSofaStability

section Evaluation

variable {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
variable {f df : ℝ → ℝ} (H : FourResidualData φ f df)
-- The statements below do not mention these hypotheses, so each theorem includes the ones
-- it uses explicitly.

include H in
theorem sharp_last_control {t : ℝ} (ht : t ∈ Icc (π / 2) π) :
    SquareControl (f t) (-sin t * cos t) (arcSquare (π / 2) π (tangentResidual π f df)) := by
  by_cases htπ : t = π
  · simpa only [htπ, H.left_zero, sin_pi, neg_zero, zero_mul] using
      SquareControl.zero
        (arcSquare_nonneg (by linarith [pi_pos] : π / 2 ≤ π) (tangentResidual π f df))
  have htt : t ∈ Ico (π / 2) π := ⟨ht.1, lt_of_le_of_ne ht.2 htπ⟩
  have hs : ∀ u ∈ Icc (π / 2) t, sin u ≠ 0 := by
    intro u hu
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.1, pi_pos]) (hu.2.trans_lt htt.2)).ne'
  have hk : ContinuousOn (fun u => 1 / sin u) (Icc (π / 2) t) :=
    continuousOn_const.div continuous_sin.continuousOn hs
  have hI := (integral_square_control ht.1 hk
    (intervalIntegrable_subinterval H.last le_rfl ht.1 ht.2)
    (intervalIntegrable_subinterval H.last_sq le_rfl ht.1 ht.2)).smul (-sin t)
  have hn : (-sin t) ^ 2 * (∫ u in (π / 2)..t, (1 / sin u) ^ 2) = -sin t * cos t := by
    simpa only [neg_sq] using last_kernel_norm htt
  rw [← sharp_last_formula H htt, hn] at hI
  exact hI.mono_energy (arcSquare_mono H.last_sq le_rfl ht.1 ht.2)

include hφ H in
theorem sharp_third_control {t : ℝ} (ht : t ∈ Icc (π / 2 - φ) (π / 2)) :
    SquareControl (f t) (sin t * cos t + 2 * tan φ * cos t ^ 2)
      (arcSquare (π / 2 - φ) (π / 2) (tangentResidual (π - φ) f df) +
        arcSquare (π / 2) π (tangentResidual π f df)) := by
  have hp0 := hφ.1
  have hp4 := hφ.2
  have hpi := pi_pos
  have hs : ∀ u ∈ Icc t (π / 2), sin (π - φ - u) ≠ 0 := by
    intro u hu
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.2]) (by linarith [hu.1, ht.1])).ne'
  have hk : ContinuousOn (fun u => 1 / sin (π - φ - u)) (Icc t (π / 2)) :=
    continuousOn_const.div (by fun_prop) hs
  have hI := (integral_square_control ht.2 hk
    (intervalIntegrable_subinterval H.third ht.1 ht.2 le_rfl)
    (intervalIntegrable_subinterval H.third_sq ht.1 ht.2 le_rfl)).smul (sin (π - φ - t))
  have hT := (sharp_last_control H (t := π - φ)
    ⟨by linarith, by linarith⟩).smul (-(cos t / cos φ))
  have he := hT.add hI
  rw [← sharp_third_formula hφ H ht, third_evaluation_norm hφ ht] at he
  apply he.mono_energy
  have hsub := arcSquare_mono H.third_sq ht.1 ht.2 le_rfl
  linarith

include hφ H in
theorem sharp_middle_control {t : ℝ} (ht : t ∈ Icc φ (π / 2 - φ)) :
    SquareControl (f t) (cos t * (2 / cos φ - sin t))
      (arcSquare φ (π / 2 - φ) (cornerResidual f df) +
        arcSquare (π / 2 - φ) (π / 2) (tangentResidual (π - φ) f df) +
        arcSquare (π / 2) π (tangentResidual π f df)) := by
  have hp0 := hφ.1
  have hp4 := hφ.2
  have hpi := pi_pos
  have hb : π / 2 - φ ≤ π / 2 := by linarith
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hT : π - φ ≤ π := by linarith
  have hvT : π / 2 ≤ π - φ := by linarith
  have hvt : π / 2 ≤ π / 2 + t := by linarith
  have hvtT : π / 2 + t ≤ π - φ := by linarith [ht.2]
  have hs3 : ∀ u ∈ Icc (π / 2 - φ) (π / 2), sin (π - φ - u) ≠ 0 := by
    intro u hu
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.2]) (by linarith [hu.1])).ne'
  have hs4 : ∀ u ∈ Icc (π / 2) (π - φ), sin u ≠ 0 := by
    intro u hu
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.1]) (by linarith [hu.2])).ne'
  have hk3 : ContinuousOn (fun u => 1 / sin (π - φ - u)) (Icc (π / 2 - φ) (π / 2)) :=
    continuousOn_const.div (by fun_prop) hs3
  have hk4L : ContinuousOn (fun u => 1 / sin u) (Icc (π / 2) (π / 2 + t)) :=
    continuousOn_const.div continuous_sin.continuousOn
      (fun u hu => hs4 u ⟨hu.1, hu.2.trans hvtT⟩)
  have hk4R : ContinuousOn (tailKernel (1 / cos φ)) (Icc (π / 2 + t) (π - φ)) :=
    (continuousOn_const.add continuous_cos.continuousOn).div continuous_sin.continuousOn
      (fun u hu => hs4 u ⟨hvt.trans hu.1, hu.2⟩)
  have c2 := integral_unit_square_control ht.2
    (intervalIntegrable_subinterval H.middle ht.1 ht.2 le_rfl)
    (intervalIntegrable_subinterval H.middle_sq ht.1 ht.2 le_rfl)
  have c3 := integral_square_control hb hk3 H.third H.third_sq
  have c4L := (integral_square_control hvt hk4L
    (intervalIntegrable_subinterval H.last le_rfl hvt (hvtT.trans hT))
    (intervalIntegrable_subinterval H.last_sq le_rfl hvt (hvtT.trans hT))).smul (1 / cos φ - sin t)
  have c4R := integral_square_control hvtT hk4R
    (intervalIntegrable_subinterval H.last hvt hvtT hT)
    (intervalIntegrable_subinterval H.last_sq hvt hvtT hT)
  have c4 := c4L.add c4R
  rw [arcSquare_split (intervalIntegrable_subinterval H.last_sq le_rfl hvT hT) hvt hvtT] at c4
  have he := (c2.add c3).add c4
  have hrec := sharp_middle_formula hφ H ht
  have hvalue : f t =
      ((∫ u in t..(π / 2 - φ), cornerResidual f df u) +
        (∫ u in (π / 2 - φ)..(π / 2), (1 / sin (π - φ - u)) * tangentResidual (π - φ) f df u)) +
      ((1 / cos φ - sin t) *
        (∫ u in (π / 2)..(π / 2 + t), (1 / sin u) * tangentResidual π f df u) +
        (∫ u in (π / 2 + t)..(π - φ), tailKernel (1 / cos φ) u * tangentResidual π f df u)) := by
    rw [hrec]
    ring
  rw [← hvalue, middle_evaluation_norm hφ ht] at he
  apply he.mono_energy
  have h2 := arcSquare_mono H.middle_sq ht.1 ht.2 le_rfl
  have h4 := arcSquare_mono H.last_sq le_rfl hvT hT
  linarith

include hφ H in
theorem sharp_first_control {t : ℝ} (ht : t ∈ Icc 0 φ) :
    SquareControl (f t) (cos t ^ 2 * (2 * (1 / cos φ) ^ 2 - tan t))
      (2 * fourResidualEnergy φ f df) := by
  have hp0 := hφ.1
  have hp4 := hφ.2
  have hpi := pi_pos
  have hmid := (sharp_middle_control hφ H (t := φ) ⟨le_rfl, by linarith⟩).smul (cos t / cos φ)
  have hk : ContinuousOn (fun u => 1 / cos u) (Icc t φ) :=
    continuousOn_const.div continuous_cos.continuousOn (fun u hu =>
      (cos_pos_of_mem_Ioo ⟨by linarith [hu.1, ht.1], by linarith [hu.2]⟩).ne')
  have hI := (integral_square_control ht.2 hk
    (intervalIntegrable_subinterval H.first ht.1 ht.2 le_rfl)
    (intervalIntegrable_subinterval H.first_sq ht.1 ht.2 le_rfl)).smul (cos t)
  have he := hmid.add hI
  have hvalue : f t = (cos t / cos φ) * f φ + cos t *
      (∫ u in t..φ, (1 / cos u) * tangentResidual (π / 2) f df u) := by
    rw [sharp_first_formula hφ H ht]
    ring
  rw [← hvalue, first_evaluation_norm hφ ht] at he
  apply he.mono_energy
  have hsub := arcSquare_mono H.first_sq ht.1 ht.2 le_rfl
  unfold fourResidualEnergy
  linarith

include hφ H in
/-- The actual square-integral norm at every evaluation point. -/
theorem sharp_green_control {t : ℝ} (ht : t ∈ Icc 0 π) :
    SquareControl (f t) (greenNormSquared φ t) (2 * fourResidualEnergy φ f df) := by
  have hp0 := hφ.1
  have hp4 := hφ.2
  have hpi := pi_pos
  have e1 := arcSquare_nonneg hp0.le (tangentResidual (π / 2) f df)
  have e2 := arcSquare_nonneg (by linarith : φ ≤ π / 2 - φ) (cornerResidual f df)
  have e3 := arcSquare_nonneg (by linarith : π / 2 - φ ≤ π / 2) (tangentResidual (π - φ) f df)
  have e4 := arcSquare_nonneg (by linarith : π / 2 ≤ π) (tangentResidual π f df)
  by_cases h1 : t ≤ φ
  · simpa only [greenNormSquared, ite_eq_left h1] using sharp_first_control hφ H ⟨ht.1, h1⟩
  by_cases h2 : t ≤ π / 2 - φ
  · have hc := sharp_middle_control hφ H ⟨(not_le.mp h1).le, h2⟩
    have henergy : arcSquare φ (π / 2 - φ) (cornerResidual f df) +
        arcSquare (π / 2 - φ) (π / 2) (tangentResidual (π - φ) f df) +
        arcSquare (π / 2) π (tangentResidual π f df) ≤ 2 * fourResidualEnergy φ f df := by
      unfold fourResidualEnergy
      linarith
    simpa only [greenNormSquared, ite_eq_right h1, ite_eq_left h2] using hc.mono_energy henergy
  by_cases h3 : t ≤ π / 2
  · have hc := sharp_third_control hφ H ⟨(not_le.mp h2).le, h3⟩
    have henergy : arcSquare (π / 2 - φ) (π / 2) (tangentResidual (π - φ) f df) +
        arcSquare (π / 2) π (tangentResidual π f df) ≤ 2 * fourResidualEnergy φ f df := by
      unfold fourResidualEnergy
      linarith
    simpa only [greenNormSquared, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3] using
      hc.mono_energy henergy
  · have hc := sharp_last_control H ⟨(not_le.mp h3).le, ht.2⟩
    have henergy :
        arcSquare (π / 2) π (tangentResidual π f df) ≤ 2 * fourResidualEnergy φ f df := by
      unfold fourResidualEnergy
      linarith
    simpa only [greenNormSquared, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3] using
      hc.mono_energy henergy

include hφ H in
/-- The coefficient is 2/cos(phi), not the earlier non-sharp 80. -/
theorem sharp_four_arc_coercivity {t : ℝ} (ht : t ∈ Icc 0 π) :
    |f t| ≤ (2 / cos φ) * sqrt (fourResidualEnergy φ f df) := by
  have hc := (sharp_green_control hφ H ht).mono_kernel (greenNormSquared_le hφ ht)
  apply green_evaluation_from_squared hφ
  nlinarith only [hc.bound]

end Evaluation
end MovingSofaStability
