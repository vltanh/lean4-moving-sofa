module

public import MovingSofaQuantitative.ResidualAlgebra
public import MovingSofaQuantitative.FullQConsequences

/-!
# Endpoint control from L1 mass and L2 derivative energy

Uncompiled proof source. The interval length is optimized only after proving
the estimate for every positive length. This prevents an endpoint value from
being inferred solely from a small integral of a nonnegative function.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaStability

namespace MovingSofaQuantitative

/-- Cauchy--Schwarz on an actual subinterval, using the full derivative energy. -/
theorem integral_subinterval_abs_le {a b t : ℝ} (ht : t ∈ Icc a b)
    {d : ℝ → ℝ} (hd : IntervalIntegrable d volume a b)
    (hd2 : IntervalIntegrable (fun u => d u ^ 2) volume a b)
    {B : ℝ} (hB : 0 ≤ B) (henergy : arcSquare a b d ≤ B ^ 2) :
    |∫ u in a..t, d u| ≤ sqrt (b - a) * B := by
  have hi := intervalIntegrable_subinterval hd le_rfl ht.1 ht.2
  have hi2 := intervalIntegrable_subinterval hd2 le_rfl ht.1 ht.2
  have hcs := integral_square_control ht.1
    (k := fun _ => 1) continuousOn_const hi hi2
  have hcs' : |∫ u in a..t, d u| ≤ sqrt (t - a) * sqrt (arcSquare a t d) := by
    simpa using hcs.abs_bound
  have he := (arcSquare_mono hd2 le_rfl ht.1 ht.2).trans henergy
  have hr : sqrt (arcSquare a t d) ≤ B := by
    have hh := sqrt_le_sqrt he
    simpa only [sqrt_sq hB] using hh
  exact hcs'.trans (mul_le_mul (sqrt_le_sqrt (by linarith [ht.2])) hr
    (sqrt_nonneg _) (sqrt_nonneg _))

/-- Average mass plus square-root length times derivative energy bounds the
left endpoint. The right-derivative hypotheses remain explicit. -/
theorem endpoint_average_bound {a b : ℝ} (hab : a < b) {f d : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivWithinAt f (d t) (Ioi t) t)
    (hd : IntervalIntegrable d volume a b)
    (hd2 : IntervalIntegrable (fun u => d u ^ 2) volume a b)
    {A B : ℝ} (hB : 0 ≤ B) (hmass : (∫ t in a..b, f t) ≤ A)
    (henergy : arcSquare a b d ≤ B ^ 2) :
    f a ≤ A / (b - a) + sqrt (b - a) * B := by
  have hpoint : ∀ t ∈ Icc a b, f a - sqrt (b - a) * B ≤ f t := by
    intro t ht
    have hit := intervalIntegrable_subinterval hd le_rfl ht.1 ht.2
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
      (hf.mono (Icc_subset_Icc_right ht.2))
      (fun u hu => hderiv u ⟨hu.1, hu.2.trans_le ht.2⟩) hit
    have hcs := integral_subinterval_abs_le ht hd hd2 hB henergy
    rw [hFTC] at hcs
    linarith [(abs_le.mp hcs).1]
  have hi := hf.intervalIntegrable_of_Icc hab.le
  have havg := intervalIntegral.integral_mono_on hab.le
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f a - sqrt (b - a) * B) volume a b)
    hi hpoint
  simp only [intervalIntegral.integral_const, smul_eq_mul] at havg
  have hlen : 0 < b - a := sub_pos.mpr hab
  have hdiv : f a - sqrt (b - a) * B ≤ A / (b - a) := by
    apply (le_div_iff₀ hlen).2
    nlinarith only [havg, hmass]
  linarith

/-- The optimized scalar remainder at the exact cube-root scale. -/
theorem endpoint_cube_root_arithmetic {Δ : ℝ} (hΔ : 0 < Δ) :
    (8 * Δ) / Δ ^ (1 / 3 : ℝ) + sqrt (Δ ^ (1 / 3 : ℝ)) * (8 * sqrt Δ) =
      16 * Δ ^ (2 / 3 : ℝ) := by
  have hfirst : Δ / Δ ^ (1 / 3 : ℝ) = Δ ^ (2 / 3 : ℝ) := by
    calc
      _ = Δ ^ (1 : ℝ) / Δ ^ (1 / 3 : ℝ) := by rw [rpow_one]
      _ = Δ ^ ((1 : ℝ) - 1 / 3) := (rpow_sub hΔ _ _).symm
      _ = _ := by congr 1; norm_num
  have hsecond : sqrt (Δ ^ (1 / 3 : ℝ)) * sqrt Δ = Δ ^ (2 / 3 : ℝ) := by
    rw [sqrt_eq_rpow, ← rpow_mul hΔ.le, sqrt_eq_rpow, ← rpow_add hΔ]
    congr 1
    norm_num
  calc
    _ = 8 * (Δ / Δ ^ (1 / 3 : ℝ)) + 8 * (sqrt (Δ ^ (1 / 3 : ℝ)) * sqrt Δ) := by ring
    _ = _ := by rw [hfirst, hsecond]; ring

/-- For Delta<=1/512 the selected interval fits inside an available length 1/8. -/
theorem cube_root_fits_eighth {Δ : ℝ} (hΔ : 0 ≤ Δ) (hsmall : Δ ≤ 1 / 512) :
    Δ ^ (1 / 3 : ℝ) ≤ 1 / 8 := by
  calc
    _ ≤ ((1 / 8 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by
      apply rpow_le_rpow hΔ _ (by norm_num)
      norm_num at hsmall ⊢
      exact hsmall
    _ = 1 / 8 := by
      rw [← rpow_natCast (1 / 8 : ℝ) 3, ← rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)]
      norm_num

/-- The endpoint estimate at Delta^(1/3). Its geometric application must supply
the genuine L1 slack and derivative-energy bounds on this interval. -/
theorem endpoint_slack_from_energy {a Δ : ℝ} (hΔ : 0 < Δ) {f d : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a (a + Δ ^ (1 / 3 : ℝ))))
    (hdiff : ∀ t ∈ Ioo a (a + Δ ^ (1 / 3 : ℝ)), HasDerivWithinAt f (d t) (Ioi t) t)
    (hd : IntervalIntegrable d volume a (a + Δ ^ (1 / 3 : ℝ)))
    (hd2 : IntervalIntegrable (fun t => d t ^ 2) volume a (a + Δ ^ (1 / 3 : ℝ)))
    (hmass : (∫ t in a..(a + Δ ^ (1 / 3 : ℝ)), f t) ≤ 8 * Δ)
    (henergy : arcSquare a (a + Δ ^ (1 / 3 : ℝ)) d ≤ 64 * Δ) :
    f a ≤ 16 * Δ ^ (2 / 3 : ℝ) := by
  have hlen : 0 < Δ ^ (1 / 3 : ℝ) := rpow_pos_of_pos hΔ _
  have hB : 0 ≤ 8 * sqrt Δ := by positivity
  have henergy' : arcSquare a (a + Δ ^ (1 / 3 : ℝ)) d ≤ (8 * sqrt Δ) ^ 2 := by
    rw [mul_pow, sq_sqrt hΔ.le]
    norm_num
    exact henergy
  have h := endpoint_average_bound (by linarith : a < a + Δ ^ (1 / 3 : ℝ))
    hf hdiff hd hd2 hB hmass henergy'
  rw [add_sub_cancel_left, endpoint_cube_root_arithmetic hΔ] at h
  exact h

end MovingSofaQuantitative
