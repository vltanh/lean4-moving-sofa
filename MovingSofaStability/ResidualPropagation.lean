module

public import MovingSofaStability.ResidualMass

/-!
# Stable propagation of the support residual equations

Uncompiled proof source. The last-arc integrating factor has an apparent
singularity at pi. Its evaluation kernel is a contraction: sin(t)/sin(u) <= 1
for pi/2 <= u <= t < pi. Thus its first moment is enough for a uniform bound;
no exchange of two improper integrals or claimed sharp kernel norm is needed.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory

namespace MovingSofaStability

/-- Restrict an interval-integrable function to an ordered subinterval. -/
theorem intervalIntegrable_subinterval {a b c d : ℝ} {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    IntervalIntegrable f volume c d := by
  apply hf.mono_set
  rw [uIcc_of_le hcd, uIcc_of_le (hac.trans (hcd.trans hdb))]
  exact Icc_subset_Icc hac hdb

/-- A continuous reciprocal can multiply a residual on any nonsingular compact arc. -/
theorem residual_div_sin_integrable {a b T : ℝ} {r : ℝ → ℝ}
    (hab : a ≤ b) (hr : IntervalIntegrable r volume a b)
    (hs : ∀ t ∈ Icc a b, sin (T - t) ≠ 0) :
    IntervalIntegrable (fun t => r t / sin (T - t)) volume a b := by
  have hc : ContinuousOn (fun t => 1 / sin (T - t)) (Icc a b) :=
    continuousOn_const.div ((continuous_const.sub continuous_id).sin.continuousOn) hs
  simpa only [one_div, div_eq_mul_inv] using
    hr.mul_continuousOn (by simpa only [uIcc_of_le hab] using hc)

/-- Propagation on an arc whose sine denominator is at least one half. -/
theorem tangent_regular_arc_bound {f df : ℝ → ℝ} {a b T : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hs : ∀ t ∈ Icc a b, (1 / 2 : ℝ) ≤ sin (T - t))
    (hr : IntervalIntegrable (tangentResidual T f df) volume a b) :
    |f a| ≤ 2 * |f b| + 3 * |f T| + 2 * arcMass a b (tangentResidual T f df) := by
  have hs0 : ∀ t ∈ Icc a b, 0 < sin (T - t) := fun t ht => by linarith [hs t ht]
  have hsn : ∀ t ∈ Icc a b, sin (T - t) ≠ 0 := fun t ht => (hs0 t ht).ne'
  have hi := residual_div_sin_integrable hab hr hsn
  have hrec := tangent_reconstruct_left hab hf hd hsn hi
  have hk : ContinuousOn (fun t => 1 / sin (T - t)) (Icc a b) :=
    continuousOn_const.div ((continuous_const.sub continuous_id).sin.continuousOn) hsn
  have hweight : ∀ t ∈ Icc a b, |1 / sin (T - t)| ≤ (2 : ℝ) := by
    intro t ht
    rw [abs_of_pos (one_div_pos.mpr (hs0 t ht))]
    exact (div_le_iff₀ (hs0 t ht)).2 (by linarith [hs t ht])
  have hI : |∫ t in a..b, tangentResidual T f df t / sin (T - t)| ≤
      2 * arcMass a b (tangentResidual T f df) := by
    simpa only [one_div, div_eq_mul_inv] using weighted_integral_le_mass hab hr hk hweight
  have hb0 := hs0 b ⟨hab, le_rfl⟩
  have hq : |tangentQuotient T f b| ≤ 2 * (|f b| + |f T|) := by
    unfold tangentQuotient
    rw [abs_div, abs_of_pos hb0]
    apply (div_le_iff₀ hb0).2
    have hn : |f b - f T * cos (T - b)| ≤ |f b| + |f T| := by
      calc
        _ ≤ |f b| + |f T * cos (T - b)| := abs_sub _ _
        _ ≤ _ := by
          rw [abs_mul]
          exact add_le_add_left
            (by simpa only [mul_one] using
              mul_le_mul_of_nonneg_left (abs_cos_le_one (T - b)) (abs_nonneg (f T))) _
    have hh := hs b ⟨hab, le_rfl⟩
    nlinarith [abs_nonneg (f b), abs_nonneg (f T)]
  have hc : |f T * cos (T - a)| ≤ |f T| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (abs_cos_le_one _) (abs_nonneg _)).trans_eq (mul_one _)
  have hsin : |sin (T - a) *
      (tangentQuotient T f b + ∫ t in a..b, tangentResidual T f df t / sin (T - t))| ≤
      |tangentQuotient T f b| + |∫ t in a..b, tangentResidual T f df t / sin (T - t)| := by
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_right (abs_sin_le_one _)
      (abs_nonneg _)).trans_eq (one_mul _)).trans (abs_add_le _ _)
  rw [hrec]
  have htriangle := abs_add_le (f T * cos (T - a))
    (sin (T - a) * (tangentQuotient T f b +
      ∫ t in a..b, tangentResidual T f df t / sin (T - t)))
  linarith

/-- Sine is decreasing on the upper-left quarter circle. -/
theorem sin_antitone_upper_quarter {u t : ℝ}
    (hu : π / 2 ≤ u) (hut : u ≤ t) (ht : t ≤ π) : sin t ≤ sin u := by
  have h := cos_le_cos_of_nonneg_of_le_pi
    (x := u - π / 2) (y := t - π / 2)
    (by linarith) (by linarith [pi_pos]) (by linarith)
  simpa only [cos_sub_pi_div_two] using h

/-- Uniform control on the entire last arc, including its singular endpoint. -/
theorem last_arc_mass_bound {f df : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (π / 2) π))
    (hd : ∀ t ∈ Ioo (π / 2) π, HasDerivWithinAt f (df t) (Ioi t) t)
    (hv : f (π / 2) = 0) (hπ : f π = 0)
    (hr : IntervalIntegrable (tangentResidual π f df) volume (π / 2) π)
    {t : ℝ} (ht : t ∈ Icc (π / 2) π) :
    |f t| ≤ arcMass (π / 2) π (tangentResidual π f df) := by
  by_cases htπ : t = π
  · rw [htπ, hπ, abs_zero]
    exact arcMass_nonneg (by linarith [pi_pos]) _
  have htlt : t < π := lt_of_le_of_ne ht.2 htπ
  have hspos : ∀ u ∈ Icc (π / 2) t, 0 < sin u := by
    intro u hu
    exact sin_pos_of_pos_of_lt_pi (by linarith [hu.1, pi_pos]) (hu.2.trans_lt htlt)
  have hsn : ∀ u ∈ Icc (π / 2) t, sin (π - u) ≠ 0 := by
    intro u hu
    rw [sin_pi_sub]
    exact (hspos u hu).ne'
  have hrt := intervalIntegrable_subinterval hr le_rfl ht.1 ht.2
  have hi := residual_div_sin_integrable ht.1 hrt hsn
  have hrec := tangent_reconstruct_right ht.1 (hf.mono (Icc_subset_Icc le_rfl ht.2))
    (fun u hu => hd u ⟨hu.1, hu.2.trans_le ht.2⟩) hsn hi
  have hq : tangentQuotient π f (π / 2) = 0 := by
    simp [tangentQuotient, hv, hπ]
  rw [hπ, zero_mul, zero_add, hq, zero_sub, sin_pi_sub] at hrec
  have he : sin t * (∫ u in (π / 2)..t, tangentResidual π f df u / sin (π - u)) =
      ∫ u in (π / 2)..t, tangentResidual π f df u * (sin t / sin u) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [sin_pi_sub]
    ring
  have hrec' : f t = -(∫ u in (π / 2)..t,
      tangentResidual π f df u * (sin t / sin u)) := by
    calc
      f t = -(sin t * (∫ u in (π / 2)..t, tangentResidual π f df u / sin (π - u))) := by
        rw [hrec]
        ring
      _ = _ := congrArg Neg.neg he
  have hk : ContinuousOn (fun u => sin t / sin u) (Icc (π / 2) t) :=
    continuousOn_const.div continuous_sin.continuousOn (fun u hu => (hspos u hu).ne')
  have hbound : ∀ u ∈ Icc (π / 2) t, |sin t / sin u| ≤ (1 : ℝ) := by
    intro u hu
    have hp := hspos u hu
    have htpos := hspos t ⟨ht.1, le_rfl⟩
    rw [abs_of_pos (div_pos htpos hp)]
    exact (div_le_one hp).2 (sin_antitone_upper_quarter hu.1 hu.2 ht.2)
  rw [hrec', abs_neg]
  exact (weighted_integral_le_mass ht.1 hrt hk hbound).trans
    (by simpa only [one_mul] using arcMass_mono (f := tangentResidual π f df)
      le_rfl ht.1 ht.2 hr)

end MovingSofaStability
