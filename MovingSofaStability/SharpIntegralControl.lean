module

public import MovingSofaStability.FourArcCoercivity

/-!
# Quadratic control of linear residual functionals

Combining independent residual intervals adds the squared kernel norms, rather
than adding their square roots. This is the Cauchy--Schwarz step lost in the
earlier coefficient-80 proof.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory

namespace MovingSofaStability

/-- A scalar evaluation with kernel square norm k and residual square norm e. -/
structure SquareControl (value k e : ℝ) : Prop where
  kernel_nonneg : 0 ≤ k
  energy_nonneg : 0 ≤ e
  bound : value ^ 2 ≤ k * e

theorem SquareControl.zero {e : ℝ} (he : 0 ≤ e) : SquareControl 0 0 e :=
  ⟨le_rfl, he, by simp⟩

theorem SquareControl.abs_bound {v k e : ℝ} (h : SquareControl v k e) :
    |v| ≤ sqrt k * sqrt e := by
  have hs := sqrt_le_sqrt h.bound
  simpa only [sqrt_sq_eq_abs, sqrt_mul h.kernel_nonneg] using hs

/-- Independent square norms add without a factor of two. -/
theorem SquareControl.add {v w k l e f : ℝ}
    (h : SquareControl v k e) (h' : SquareControl w l f) :
    SquareControl (v + w) (k + l) (e + f) := by
  refine ⟨add_nonneg h.kernel_nonneg h'.kernel_nonneg,
    add_nonneg h.energy_nonneg h'.energy_nonneg, ?_⟩
  have hc := four_term_sq_le (sqrt k) (sqrt l) 0 0 (sqrt e) (sqrt f) 0 0
  simp only [sq_sqrt h.kernel_nonneg, sq_sqrt h'.kernel_nonneg,
    sq_sqrt h.energy_nonneg, sq_sqrt h'.energy_nonneg,
    zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] at hc
  have hv := (abs_add_le v w).trans (add_le_add h.abs_bound h'.abs_bound)
  have hn : 0 ≤ sqrt k * sqrt e + sqrt l * sqrt f := by positivity
  nlinarith [abs_nonneg (v + w), sq_abs (v + w)]

theorem SquareControl.smul {v k e : ℝ} (h : SquareControl v k e) (a : ℝ) :
    SquareControl (a * v) (a ^ 2 * k) e := by
  refine ⟨mul_nonneg (sq_nonneg a) h.kernel_nonneg, h.energy_nonneg, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left h.bound (sq_nonneg a)
  nlinarith

theorem SquareControl.mono_energy {v k e E : ℝ} (h : SquareControl v k e)
    (he : e ≤ E) : SquareControl v k E :=
  ⟨h.kernel_nonneg, h.energy_nonneg.trans he,
    h.bound.trans (mul_le_mul_of_nonneg_left he h.kernel_nonneg)⟩

theorem SquareControl.mono_kernel {v k K e : ℝ} (h : SquareControl v k e)
    (hk : k ≤ K) : SquareControl v K e :=
  ⟨h.kernel_nonneg.trans hk, h.energy_nonneg,
    h.bound.trans (mul_le_mul_of_nonneg_right hk h.energy_nonneg)⟩

/-- The actual weighted integral has its actual squared kernel norm. -/
theorem integral_square_control {a b : ℝ} (hab : a ≤ b) {k r : ℝ → ℝ}
    (hk : ContinuousOn k (Icc a b))
    (hr : IntervalIntegrable r volume a b)
    (hr2 : IntervalIntegrable (fun t => r t ^ 2) volume a b) :
    SquareControl (∫ t in a..b, k t * r t)
      (∫ t in a..b, k t ^ 2) (arcSquare a b r) := by
  have hk2 : IntervalIntegrable (fun t => k t ^ 2) volume a b :=
    (hk.pow 2).intervalIntegrable_of_Icc hab
  have hkr : IntervalIntegrable (fun t => k t * r t) volume a b :=
    hr.continuousOn_mul (by rwa [uIcc_of_le hab])
  have ki := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hk2
  have ri := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hr2
  have kri := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hkr
  refine ⟨intervalIntegral.integral_nonneg hab (fun t _ => sq_nonneg (k t)),
    arcSquare_nonneg hab r, ?_⟩
  unfold arcSquare
  simp only [intervalIntegral.integral_of_le hab]
  exact integral_mul_sq_le (volume.restrict (Ioc a b)) ki ri kri

/-- The energy over a subinterval is bounded by the full arc energy. -/
theorem arcSquare_mono {a b c d : ℝ} {r : ℝ → ℝ}
    (hr2 : IntervalIntegrable (fun t => r t ^ 2) volume a b)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) : arcSquare c d r ≤ arcSquare a b r := by
  have hab : a ≤ b := hac.trans (hcd.trans hdb)
  have haci := intervalIntegrable_subinterval hr2 le_rfl hac (hcd.trans hdb)
  have hcdi := intervalIntegrable_subinterval hr2 hac hcd hdb
  have hdbi := intervalIntegrable_subinterval hr2 (hac.trans hcd) hdb le_rfl
  have hsum : arcSquare a b r = arcSquare a c r + arcSquare c d r + arcSquare d b r := by
    unfold arcSquare
    rw [intervalIntegral.integral_add_adjacent_intervals haci hcdi,
      intervalIntegral.integral_add_adjacent_intervals (haci.trans hcdi) hdbi]
  rw [hsum]
  linarith [arcSquare_nonneg hac r, arcSquare_nonneg hdb r]

/-- Split energy at an interior point without counting the same residual twice. -/
theorem arcSquare_split {a b c : ℝ} {r : ℝ → ℝ}
    (hr2 : IntervalIntegrable (fun t => r t ^ 2) volume a b)
    (hac : a ≤ c) (hcb : c ≤ b) :
    arcSquare a c r + arcSquare c b r = arcSquare a b r := by
  unfold arcSquare
  exact intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_subinterval hr2 le_rfl hac hcb)
    (intervalIntegrable_subinterval hr2 hac hcb le_rfl)

/-- The unweighted evaluation is useful on the middle residual interval. -/
theorem integral_unit_square_control {a b : ℝ} (hab : a ≤ b) {r : ℝ → ℝ}
    (hr : IntervalIntegrable r volume a b)
    (hr2 : IntervalIntegrable (fun t => r t ^ 2) volume a b) :
    SquareControl (∫ t in a..b, r t) (b - a) (arcSquare a b r) := by
  have h := integral_square_control hab (k := fun _ => 1) continuousOn_const hr hr2
  simpa using h

end MovingSofaStability
