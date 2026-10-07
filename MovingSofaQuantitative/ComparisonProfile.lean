module

public import MovingSofaQuantitative.ResidualAlgebra
public import MovingSofaQuantitative.CenteredKernel

/-!
# The endpoint representer as an actual four-arc function

Uncompiled proof source. This is a continuous, piecewise trigonometric function
with its specified RIGHT derivative. Its residuals, not just its displayed
values, are identified. The cuts at phi, pi/2, and pi-phi may have derivative
jumps. Interval integrals ignore their endpoint values, not their one-sided
limits. All reciprocal-sine kernels are restricted away from pi.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaStability

namespace MovingSofaQuantitative

def comparisonPiece (φ : ℝ) : Fin 6 → ℝ → ℝ
  | 0 => trigAffine 0 (2 * (1 / cos φ) ^ 2) (-1)
  | 1 => trigAffine (1 / cos φ) ((1 / cos φ) ^ 2) (-1)
  | 2 => trigAffine 0 ((1 / cos φ) ^ 2 + (1 / cos φ) * sin φ) 0
  | 3 => trigAffine 0 ((1 / cos φ) * (1 / cos φ - sin φ)) 0
  | 4 => trigAffine (1 / cos φ) ((1 / cos φ) ^ 2) (-1)
  | 5 => trigAffine 0 0 (-1)

def comparisonPieceDeriv (φ : ℝ) : Fin 6 → ℝ → ℝ
  | 0 => trigAffineDeriv (2 * (1 / cos φ) ^ 2) (-1)
  | 1 => trigAffineDeriv ((1 / cos φ) ^ 2) (-1)
  | 2 => trigAffineDeriv ((1 / cos φ) ^ 2 + (1 / cos φ) * sin φ) 0
  | 3 => trigAffineDeriv ((1 / cos φ) * (1 / cos φ - sin φ)) 0
  | 4 => trigAffineDeriv ((1 / cos φ) ^ 2) (-1)
  | 5 => trigAffineDeriv 0 (-1)

def comparisonProfile (φ : ℝ) : ℝ → ℝ :=
  rightJoin φ (comparisonPiece φ 0)
    (rightJoin (π / 2 - φ) (comparisonPiece φ 1)
      (rightJoin (π / 2) (comparisonPiece φ 2)
        (rightJoin (π / 2 + φ) (comparisonPiece φ 3)
          (rightJoin (π - φ) (comparisonPiece φ 4) (comparisonPiece φ 5)))))

def comparisonDerivative (φ : ℝ) : ℝ → ℝ :=
  rightJoin φ (comparisonPieceDeriv φ 0)
    (rightJoin (π / 2 - φ) (comparisonPieceDeriv φ 1)
      (rightJoin (π / 2) (comparisonPieceDeriv φ 2)
        (rightJoin (π / 2 + φ) (comparisonPieceDeriv φ 3)
          (rightJoin (π - φ) (comparisonPieceDeriv φ 4) (comparisonPieceDeriv φ 5)))))

private theorem comparison_matches {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    comparisonPiece φ 0 φ = comparisonPiece φ 1 φ ∧
    comparisonPiece φ 1 (π / 2 - φ) = comparisonPiece φ 2 (π / 2 - φ) ∧
    comparisonPiece φ 2 (π / 2) = comparisonPiece φ 3 (π / 2) ∧
    comparisonPiece φ 3 (π / 2 + φ) = comparisonPiece φ 4 (π / 2 + φ) ∧
    comparisonPiece φ 4 (π - φ) = comparisonPiece φ 5 (π - φ) := by
  have hc := (cap_angle_parameters hφ).1.ne'
  have hunit := sin_sq_add_cos_sq φ
  have hunitc := congrArg (fun x : ℝ => cos φ * x) hunit
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [comparisonPiece, trigAffine, cos_pi_div_two_sub, sin_pi_div_two_sub,
      cos_add, sin_add, cos_pi_div_two, sin_pi_div_two, cos_pi_sub, sin_pi_sub] <;>
    field_simp [hc] <;> nlinarith [hunit, hunitc]

theorem comparisonProfile_continuous {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    Continuous (comparisonProfile φ) := by
  have h01 := (comparison_matches hφ).1
  have h12 := (comparison_matches hφ).2.1
  have h23 := (comparison_matches hφ).2.2.1
  have h34 := (comparison_matches hφ).2.2.2.1
  have h45 := (comparison_matches hφ).2.2.2.2
  have hp (i : Fin 6) : Continuous (comparisonPiece φ i) := by
    fin_cases i <;> exact continuous_trigAffine _ _ _
  have hab : φ < π / 2 - φ := by linarith [hφ.2]
  have hbc : π / 2 - φ < π / 2 := by linarith [hφ.1]
  have hcd : π / 2 < π / 2 + φ := by linarith [hφ.1]
  have hde : π / 2 + φ < π - φ := by linarith [hφ.2]
  have h5 := continuous_rightJoin (hp 4) (hp 5) h45
  have h4 := continuous_rightJoin (hp 3) h5 (by simpa [rightJoin, hde] using h34)
  have h3 := continuous_rightJoin (hp 2) h4 (by simpa [rightJoin, hcd] using h23)
  have h2 := continuous_rightJoin (hp 1) h3 (by simpa [rightJoin, hbc] using h12)
  exact continuous_rightJoin (hp 0) h2 (by simpa [rightJoin, hab] using h01)

theorem comparisonProfile_rightDeriv (φ t : ℝ) :
    HasDerivWithinAt (comparisonProfile φ) (comparisonDerivative φ t) (Ioi t) t := by
  have hp (i : Fin 6) (u : ℝ) :
      HasDerivWithinAt (comparisonPiece φ i) (comparisonPieceDeriv φ i u) (Ioi u) u := by
    fin_cases i <;> exact (hasDerivAt_trigAffine _ _ _ u).hasDerivWithinAt
  exact rightDeriv_rightJoin (hp 0)
    (fun u => rightDeriv_rightJoin (hp 1)
      (fun u => rightDeriv_rightJoin (hp 2)
        (fun u => rightDeriv_rightJoin (hp 3)
          (fun u => rightDeriv_rightJoin (hp 4) (hp 5) u) u) u) u) t

/-- The strictly joined function equals the closed-form covariance, including
all five cut values. -/
theorem comparisonProfile_eq_covariance {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) (t : ℝ) :
    comparisonProfile φ t = greenCovariance φ t := by
  have hc := (cap_angle_parameters hφ).1.ne'
  have hunit := sin_sq_add_cos_sq φ
  have hunitc := congrArg (fun x : ℝ => cos φ * x) hunit
  unfold comparisonProfile rightJoin greenCovariance
  simp only [comparisonPiece, trigAffine]
  split_ifs <;> try ring
  all_goals first
    | (exfalso; linarith [hφ.1, hφ.2, pi_pos])
    | (have he : t = φ := by linarith; subst t; field_simp [hc]; ring)
    | (have he : t = π / 2 - φ := by linarith; subst t;
       simp only [cos_pi_div_two_sub, sin_pi_div_two_sub];
       field_simp [hc]; nlinarith [hunit, hunitc])
    | (have he : t = π / 2 := by linarith; subst t;
       simp [cos_pi_div_two, sin_pi_div_two])
    | (have he : t = π / 2 + φ := by linarith; subst t;
       simp only [cos_add, sin_add, cos_pi_div_two, sin_pi_div_two];
       field_simp [hc]; nlinarith [hunit, hunitc])
    | (have he : t = π - φ := by linarith; subst t;
       simp only [cos_pi_sub, sin_pi_sub]; field_simp [hc]; ring)

@[simp] theorem comparisonProfile_zero {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    comparisonProfile φ 0 = 2 * (1 / cos φ) ^ 2 := by
  simp [comparisonProfile, rightJoin, comparisonPiece, trigAffine, hφ.1]

@[simp] theorem comparisonProfile_top {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    comparisonProfile φ (π / 2) = 0 := by
  rw [comparisonProfile_eq_covariance hφ]
  have h1 : ¬π / 2 ≤ φ := by linarith [hφ.2, pi_pos]
  have h2 : ¬π / 2 ≤ π / 2 - φ := by linarith [hφ.1]
  simp [greenCovariance, h1, h2]

@[simp] theorem comparisonProfile_pi {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    comparisonProfile φ π = 0 := by
  have h1 : ¬π < φ := by linarith [hφ.2, pi_pos]
  have h2 : ¬π < π / 2 - φ := by linarith [hφ.1, pi_pos]
  have h3 : ¬π < π / 2 := by linarith [pi_pos]
  have h4 : ¬π < π / 2 + φ := by linarith [hφ.2, pi_pos]
  have h5 : ¬π < π - φ := by linarith [hφ.1]
  simp [comparisonProfile, rightJoin, comparisonPiece, trigAffine, h1, h2, h3, h4, h5]

@[simp] theorem comparisonProfile_terminal {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    comparisonProfile φ (π - φ) = -sin φ := by
  have h1 : ¬π - φ < φ := by linarith [hφ.2, pi_pos]
  have h2 : ¬π - φ < π / 2 - φ := by linarith [pi_pos]
  have h3 : ¬π - φ < π / 2 := by linarith [hφ.2, pi_pos]
  have h4 : ¬π - φ < π / 2 + φ := by linarith [hφ.2]
  simp [comparisonProfile, rightJoin, comparisonPiece, trigAffine, h1, h2, h3, h4]

/-- Residual on the first arc. -/
theorem comparison_first {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) (ht : t ∈ Ioo 0 φ) :
    tangentResidual (π / 2) (comparisonProfile φ) (comparisonDerivative φ) t = 1 / cos t := by
  have hc : cos t ≠ 0 := (cos_pos_of_mem_Ioo
    ⟨by linarith [ht.1, pi_pos], by linarith [ht.2, hφ.2, pi_pos]⟩).ne'
  rw [tangentResidual, comparisonProfile_top hφ]
  simp only [comparisonProfile, comparisonDerivative, rightJoin, if_pos ht.2,
    comparisonPiece, comparisonPieceDeriv, trigAffine, trigAffineDeriv,
    cos_pi_div_two_sub, sin_pi_div_two_sub]
  field_simp [hc]
  linear_combination sin_sq_add_cos_sq t

/-- The shifted middle residual is exactly the constant sec(phi). -/
theorem comparison_middle {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ht : t ∈ Ioo φ (π / 2 - φ)) :
    cornerResidual (comparisonProfile φ) (comparisonDerivative φ) t = 1 / cos φ := by
  have h0 : ¬t < φ := not_lt.mpr ht.1.le
  have hshift0 : ¬t + π / 2 < φ := by linarith [ht.1, pi_pos]
  have hshift1 : ¬t + π / 2 < π / 2 - φ := by linarith [ht.1, hφ.1]
  have hshift2 : ¬t + π / 2 < π / 2 := by linarith [ht.1, hφ.1]
  have hshift3 : ¬t + π / 2 < π / 2 + φ := by linarith [ht.1]
  have hshift4 : t + π / 2 < π - φ := by linarith [ht.2]
  simp only [cornerResidual, comparisonProfile, comparisonDerivative, rightJoin,
    if_neg h0, if_pos ht.2, if_neg hshift0, if_neg hshift1, if_neg hshift2,
    if_neg hshift3, if_pos hshift4, comparisonPiece, comparisonPieceDeriv,
    trigAffine, trigAffineDeriv, cos_add_pi_div_two, sin_add_pi_div_two]
  ring

/-- Residual on the third arc. -/
theorem comparison_third {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ht : t ∈ Ioo (π / 2 - φ) (π / 2)) :
    tangentResidual (π - φ) (comparisonProfile φ) (comparisonDerivative φ) t =
      (1 / cos φ) / sin (π - φ - t) := by
  have hc := (cap_angle_parameters hφ).1.ne'
  have hs : sin (π - φ - t) ≠ 0 := (sin_pos_of_pos_of_lt_pi
    (by linarith [ht.2, hφ.2, pi_pos]) (by linarith [ht.1, pi_pos])).ne'
  have h0 : ¬t < φ := by linarith [ht.1, hφ.2]
  have h1 : ¬t < π / 2 - φ := not_lt.mpr ht.1.le
  have htrig : cos t * cos (π - φ - t) - sin t * sin (π - φ - t) = -cos φ := by
    rw [← cos_add, add_sub_cancel, cos_pi_sub]
  rw [tangentResidual, comparisonProfile_terminal hφ]
  simp only [comparisonProfile, comparisonDerivative, rightJoin, if_neg h0, if_neg h1,
    if_pos ht.2, comparisonPiece, comparisonPieceDeriv, trigAffine, trigAffineDeriv]
  field_simp [hc, hs]
  linear_combination -(1 + sin φ * cos φ) * htrig

/-- The first piece of the last residual; this interval stays away from pi. -/
theorem comparison_last_left {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ht : t ∈ Ioo (π / 2) (π / 2 + φ)) :
    tangentResidual π (comparisonProfile φ) (comparisonDerivative φ) t =
      ((1 / cos φ) * (1 / cos φ - sin φ)) / sin t := by
  have hs : sin t ≠ 0 := (sin_pos_of_pos_of_lt_pi
    (by linarith [ht.1, pi_pos]) (by linarith [ht.2, hφ.2, pi_pos])).ne'
  have h0 : ¬t < φ := by linarith [ht.1, hφ.2, pi_pos]
  have h1 : ¬t < π / 2 - φ := by linarith [ht.1, hφ.1]
  have h2 : ¬t < π / 2 := not_lt.mpr ht.1.le
  rw [tangentResidual_left (comparisonProfile_pi hφ)]
  simp only [comparisonProfile, comparisonDerivative, rightJoin, if_neg h0, if_neg h1,
    if_neg h2, if_pos ht.2, comparisonPiece, comparisonPieceDeriv, trigAffine, trigAffineDeriv]
  field_simp [hs]
  linear_combination ((1 / cos φ) * (1 / cos φ - sin φ)) * sin_sq_add_cos_sq t

/-- The common tail kernel on the second piece of the last residual. -/
theorem comparison_last_middle {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ht : t ∈ Ioo (π / 2 + φ) (π - φ)) :
    tangentResidual π (comparisonProfile φ) (comparisonDerivative φ) t =
      (1 / cos φ) * tailKernel (1 / cos φ) t := by
  have hs : sin t ≠ 0 := (sin_pos_of_pos_of_lt_pi
    (by linarith [ht.1, hφ.1, pi_pos]) (by linarith [ht.2, hφ.1])).ne'
  have h0 : ¬t < φ := by linarith [ht.1, pi_pos]
  have h1 : ¬t < π / 2 - φ := by linarith [ht.1, hφ.1]
  have h2 : ¬t < π / 2 := by linarith [ht.1, hφ.1]
  have h3 : ¬t < π / 2 + φ := not_lt.mpr ht.1.le
  rw [tangentResidual_left (comparisonProfile_pi hφ)]
  simp only [comparisonProfile, comparisonDerivative, rightJoin, if_neg h0, if_neg h1,
    if_neg h2, if_neg h3, if_pos ht.2, comparisonPiece, comparisonPieceDeriv,
    trigAffine, trigAffineDeriv, tailKernel]
  field_simp [hs]
  linear_combination ((1 / cos φ) ^ 2) * sin_sq_add_cos_sq t

/-- The residual vanishes on the final arc; no improper csc integral at pi is used. -/
theorem comparison_last_right {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ht : t ∈ Ioo (π - φ) π) :
    tangentResidual π (comparisonProfile φ) (comparisonDerivative φ) t = 0 := by
  have hs : sin t ≠ 0 := (sin_pos_of_pos_of_lt_pi
    (by linarith [ht.1, hφ.2, pi_pos]) ht.2).ne'
  have h0 : ¬t < φ := by linarith [ht.1, hφ.2, pi_pos]
  have h1 : ¬t < π / 2 - φ := by linarith [ht.1, pi_pos]
  have h2 : ¬t < π / 2 := by linarith [ht.1, hφ.2, pi_pos]
  have h3 : ¬t < π / 2 + φ := by linarith [ht.1, hφ.2]
  have h4 : ¬t < π - φ := not_lt.mpr ht.1.le
  rw [tangentResidual_left (comparisonProfile_pi hφ)]
  simp only [comparisonProfile, comparisonDerivative, rightJoin, if_neg h0, if_neg h1,
    if_neg h2, if_neg h3, if_neg h4, comparisonPiece, comparisonPieceDeriv,
    trigAffine, trigAffineDeriv]
  field_simp [hs]
  ring

/-- The comparison profile really belongs to the same data class as cap supports. -/
theorem comparisonProfile_data {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    FourResidualData φ (comparisonProfile φ) (comparisonDerivative φ) := by
  have h01 : (0 : ℝ) ≤ φ := hφ.1.le
  have h12 : φ ≤ π / 2 - φ := by linarith [hφ.2]
  have h23 : π / 2 - φ ≤ π / 2 := by linarith [hφ.1]
  have h34 : π / 2 ≤ π / 2 + φ := by linarith [hφ.1]
  have h45 : π / 2 + φ ≤ π - φ := by linarith [hφ.2]
  have h56 : π - φ ≤ π := by linarith [hφ.1]
  have hs : ∀ u ∈ Icc (π / 2) (π - φ), sin u ≠ 0 := fun u hu =>
    (sin_pos_of_pos_of_lt_pi (by linarith [hu.1, pi_pos]) (by linarith [hu.2, hφ.1])).ne'
  have hc : ∀ u ∈ Icc 0 φ, cos u ≠ 0 := fun u hu =>
    (cos_pos_of_mem_Ioo ⟨by linarith [hu.1, pi_pos], by linarith [hu.2, hφ.2, pi_pos]⟩).ne'
  have ht : ∀ u ∈ Icc (π / 2 - φ) (π / 2), sin (π - φ - u) ≠ 0 := fun u hu =>
    (sin_pos_of_pos_of_lt_pi (by linarith [hu.2, hφ.2, pi_pos]) (by linarith [hu.1, pi_pos])).ne'
  have c1 : ContinuousOn (fun u => 1 / cos u) (Icc 0 φ) :=
    continuousOn_const.div continuous_cos.continuousOn hc
  have c3 : ContinuousOn (fun u => (1 / cos φ) / sin (π - φ - u))
      (Icc (π / 2 - φ) (π / 2)) := continuousOn_const.div (by fun_prop) ht
  have c4a : ContinuousOn (fun u => ((1 / cos φ) * (1 / cos φ - sin φ)) / sin u)
      (Icc (π / 2) (π / 2 + φ)) := continuousOn_const.div continuous_sin.continuousOn
        (fun u hu => hs u ⟨hu.1, hu.2.trans h45⟩)
  have c4b : ContinuousOn (fun u => (1 / cos φ) * tailKernel (1 / cos φ) u)
      (Icc (π / 2 + φ) (π - φ)) := continuousOn_const.mul
        ((continuousOn_const.add continuous_cos.continuousOn).div continuous_sin.continuousOn
          (fun u hu => hs u ⟨h34.trans hu.1, hu.2⟩))
  have transfer {a b : ℝ} (hab : a ≤ b) {r k : ℝ → ℝ}
      (hk : ContinuousOn k (Icc a b)) (he : EqOn r k (Ioo a b)) :
      IntervalIntegrable r volume a b ∧ IntervalIntegrable (fun u => r u ^ 2) volume a b :=
    ⟨intervalIntegrable_of_eqOn_Ioo hab (hk.intervalIntegrable_of_Icc hab) he,
      intervalIntegrable_of_eqOn_Ioo hab ((hk.pow 2).intervalIntegrable_of_Icc hab)
        (fun u hu => congrArg (fun x : ℝ => x ^ 2) (he hu))⟩
  have i1 := transfer h01 c1 (fun u hu => comparison_first hφ hu)
  have i2 := transfer h12 (continuousOn_const : ContinuousOn (fun _ : ℝ => 1 / cos φ) _)
    (fun u hu => comparison_middle hφ hu)
  have i3 := transfer h23 c3 (fun u hu => comparison_third hφ hu)
  have i4a := transfer h34 c4a (fun u hu => comparison_last_left hφ hu)
  have i4b := transfer h45 c4b (fun u hu => comparison_last_middle hφ hu)
  have i4c := transfer h56 (continuousOn_const : ContinuousOn (fun _ : ℝ => 0) _)
    (fun u hu => comparison_last_right hφ hu)
  exact ⟨comparisonProfile_continuous hφ, fun t _ => comparisonProfile_rightDeriv φ t,
    comparisonProfile_top hφ, comparisonProfile_pi hφ,
    i1.1, i2.1, i3.1, (i4a.1.trans i4b.1).trans i4c.1,
    i1.2, i2.2, i3.2, (i4a.2.trans i4b.2).trans i4c.2⟩

end MovingSofaQuantitative
