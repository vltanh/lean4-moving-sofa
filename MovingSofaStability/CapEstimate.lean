module

public import MovingSofaStability.Basic
public import MovingSofaStability.Deficit

/-!
# From the energies to the cap; the coercive certificate

The pinned difference `f` of the support functions of two caps satisfies a residual equation on
each of the four arcs `[0, φ]`, `[φ, π/2 - φ]`, `[π/2 - φ, π/2]` and `[π/2, π]` of Gerver's cap,
and the square integrals of the residuals are the energies of the deficit. Integrating the residual
equations writes `f(t)` as a sum of integrals of kernels times residuals; the exact square integrals
of the kernels bound `|f(t)|` by `2 sec φ` times the square root of the energy
(`sharp_four_arc_coercivity`). Bounds on support functions become Euclidean distances between caps
(`sharp_wide_cap_distance_bound`, `sharp_ki_cap_distance_bound`). With the maximum of `𝒬`, this is
the coercive certificate (`coercive_certificate`).
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter
open scoped Pointwise
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-!
## Integrating the residual equations

Support functions of convex bodies have right derivatives at every normal, also where the
curvature measure has atoms, so the residual equations are integrated by the fundamental theorem of
calculus for right derivatives, on compact arcs where the integrating factor `1 / sin (T - t)` is
bounded.
-/

/-- The right derivative of the tangent quotient is the weighted tangent residual. -/
theorem hasDerivWithinAt_tangentQuotient {f df : ℝ → ℝ} {T t : ℝ}
    (hd : HasDerivWithinAt f (df t) (Ioi t) t) (hs : sin (T - t) ≠ 0) :
    HasDerivWithinAt (tangentQuotient T f)
      (-tangentResidual T f df t / sin (T - t)) (Ioi t) t := by
  have hu : HasDerivWithinAt (fun s : ℝ => T - s) (-1) (Ioi t) t := by
    simpa using ((hasDerivAt_id t).const_sub T).hasDerivWithinAt
  convert (hd.sub (hu.cos.const_mul (f T))).div hu.sin hs using 1
  · rfl
  · unfold tangentResidual
    simp only [Pi.sub_apply]
    field_simp
    linear_combination f T * sin_sq_add_cos_sq (T - t)

/-- The integral of a weighted tangent residual is a difference of tangent quotients. -/
theorem tangent_quotient_integral {f df : ℝ → ℝ} {a b T : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hs : ∀ t ∈ Icc a b, sin (T - t) ≠ 0)
    (hi : IntervalIntegrable (fun t => tangentResidual T f df t / sin (T - t)) volume a b) :
    (∫ t in a..b, tangentResidual T f df t / sin (T - t)) =
      tangentQuotient T f a - tangentQuotient T f b := by
  have hcont : ContinuousOn (tangentQuotient T f) (Icc a b) :=
    (hf.sub (by fun_prop)).div (by fun_prop) hs
  have hderiv : ∀ t ∈ Ioo a b, HasDerivWithinAt (tangentQuotient T f)
      (-(tangentResidual T f df t / sin (T - t))) (Ioi t) t := fun t ht => by
    simpa only [neg_div] using
      hasDerivWithinAt_tangentQuotient (hd t ht) (hs t (Ioo_subset_Icc_self ht))
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont hderiv hi.neg
  rw [intervalIntegral.integral_neg] at h
  linarith

/-- Integrating a tangent residual backwards from the right end of a nonsingular arc. -/
theorem tangent_reconstruct_left {f df : ℝ → ℝ} {a b T : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hs : ∀ t ∈ Icc a b, sin (T - t) ≠ 0)
    (hi : IntervalIntegrable (fun t => tangentResidual T f df t / sin (T - t)) volume a b) :
    f a = f T * cos (T - a) + sin (T - a) *
      (tangentQuotient T f b + ∫ t in a..b, tangentResidual T f df t / sin (T - t)) := by
  rw [tangent_quotient_integral hab hf hd hs hi]
  unfold tangentQuotient
  field_simp [hs a ⟨le_rfl, hab⟩]
  ring

/-- Integrating a tangent residual forwards from the left end of a nonsingular arc. -/
theorem tangent_reconstruct_right {f df : ℝ → ℝ} {a b T : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hs : ∀ t ∈ Icc a b, sin (T - t) ≠ 0)
    (hi : IntervalIntegrable (fun t => tangentResidual T f df t / sin (T - t)) volume a b) :
    f b = f T * cos (T - b) + sin (T - b) *
      (tangentQuotient T f a - ∫ t in a..b, tangentResidual T f df t / sin (T - t)) := by
  rw [tangent_quotient_integral hab hf hd hs hi]
  unfold tangentQuotient
  field_simp [hs b ⟨hab, le_rfl⟩]
  ring

/-- Integrating the corner residual, which has no integrating factor. -/
theorem corner_reconstruct {f df : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hdf : IntervalIntegrable df volume a b)
    (hshift : IntervalIntegrable (fun t => f (t + π / 2)) volume a b) :
    f a = f b - (∫ t in a..b, f (t + π / 2)) +
      ∫ t in a..b, cornerResidual f df t := by
  unfold cornerResidual
  rw [intervalIntegral.integral_sub hshift hdf,
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hf hd hdf]
  ring

/-!
## The residuals of two caps

`capDifference K₀ K₁` is the difference of the support functions of `K₁` and `K₀`, pinned to vanish
at `π`. Its tangent and corner residuals are differences of Mamikon displacements
(`tangent_displacement_sub`, `outer_displacement_sub`), so Mamikon's theorem makes them square
integrable, and their square integrals are twice the displacement energies of the deficit.
-/

/-- The difference of the support functions of two convex bodies, pinned to vanish at `π`. -/
def capDifference (K₀ K₁ : Set (ℝ × ℝ)) : ℝ → ℝ :=
  pinnedDifference (fun t => supp K₁ t - supp K₀ t)

/-- The right derivative of `capDifference K₀ K₁`. -/
def capDifferenceDeriv (K₀ K₁ : Set (ℝ × ℝ)) : ℝ → ℝ :=
  pinnedDerivative (fun t => supp K₁ t - supp K₀ t)
    (fun t => opt_g K₁ t - opt_g K₀ t)

/-- The square integral of a residual over an arc. -/
def arcSquare (a b : ℝ) (f : ℝ → ℝ) : ℝ := ∫ t in a..b, f t ^ 2

theorem arcSquare_nonneg {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) : 0 ≤ arcSquare a b f :=
  intervalIntegral.integral_nonneg_of_forall hab fun _ => sq_nonneg _

/-- The hypotheses of the four-arc estimate: `f` is continuous with right derivative `df` on
`(0, π)`, vanishes at `π/2` and `π`, and on each of the arcs `[0, φ]`, `[φ, π/2 - φ]`,
`[π/2 - φ, π/2]` and `[π/2, π]` its residual and the square of the residual are integrable. -/
structure FourResidualData (φ : ℝ) (f df : ℝ → ℝ) : Prop where
  continuous : Continuous f
  rightDeriv : ∀ t ∈ Ioo (0 : ℝ) π, HasDerivWithinAt f (df t) (Ioi t) t
  top_zero : f (π / 2) = 0
  left_zero : f π = 0
  first : IntervalIntegrable (tangentResidual (π / 2) f df) volume 0 φ
  middle : IntervalIntegrable (cornerResidual f df) volume φ (π / 2 - φ)
  third : IntervalIntegrable (tangentResidual (π - φ) f df) volume (π / 2 - φ) (π / 2)
  last : IntervalIntegrable (tangentResidual π f df) volume (π / 2) π
  first_sq : IntervalIntegrable (fun t => tangentResidual (π / 2) f df t ^ 2) volume 0 φ
  middle_sq : IntervalIntegrable (fun t => cornerResidual f df t ^ 2) volume φ (π / 2 - φ)
  third_sq : IntervalIntegrable (fun t => tangentResidual (π - φ) f df t ^ 2)
    volume (π / 2 - φ) (π / 2)
  last_sq : IntervalIntegrable (fun t => tangentResidual π f df t ^ 2) volume (π / 2) π

/-- Half the sum of the square integrals of the four residuals. -/
def fourResidualEnergy (φ : ℝ) (f df : ℝ → ℝ) : ℝ :=
  (arcSquare 0 φ (tangentResidual (π / 2) f df) +
   arcSquare φ (π / 2 - φ) (cornerResidual f df) +
   arcSquare (π / 2 - φ) (π / 2) (tangentResidual (π - φ) f df) +
   arcSquare (π / 2) π (tangentResidual π f df)) / 2

/-- A residual equal on an arc to a difference of Mamikon displacements is square integrable there,
and its square integral is twice the displacement energy. -/
theorem residual_of_displacement {a b : ℝ} (hab : a < b) (hb : b < a + π)
    {z : ConvexBodySet → ℝ → ℝ × ℝ} (hz : ∀ K, IsCBV (z K) a b)
    (hzl : ∀ K, ∀ t ∈ Icc a b, z K t ∈ suppLine K.1 t) {K₀ K₁ : ConvexBodySet} {r : ℝ → ℝ}
    (hr : ∀ t ∈ Ioo a b, r t = displacement K₁.1 (z K₁) t - displacement K₀.1 (z K₀) t) :
    IntervalIntegrable r volume a b ∧ IntervalIntegrable (fun t => r t ^ 2) volume a b ∧
      arcSquare a b r = 2 * displacementEnergy a b z K₀ K₁ := by
  have hM := fun K : ConvexBodySet => theorem7_4_1 K.2 hab hb (hz K) (hzl K)
  obtain ⟨C₀, hC₀⟩ := (hM K₀).2.1
  obtain ⟨C₁, hC₁⟩ := (hM K₁).2.1
  set D := fun t => displacement K₁.1 (z K₁) t - displacement K₀.1 (z K₀) t
  have hm : AEStronglyMeasurable D (volume.restrict (Icc a b)) :=
    ((hM K₁).1.sub (hM K₀).1).aestronglyMeasurable
  have hD : ∀ t ∈ Icc a b, |D t| ≤ C₁ + C₀ := fun t ht =>
    (abs_sub _ _).trans (add_le_add (hC₁ t ht) (hC₀ t ht))
  have hi : IntegrableOn D (Icc a b) := Integrable.of_bound hm (C₁ + C₀)
    (ae_restrict_of_forall_mem measurableSet_Icc hD)
  have hi2 : IntegrableOn (fun t => D t ^ 2) (Icc a b) :=
    Integrable.of_bound (hm.pow 2) ((C₁ + C₀) ^ 2)
      (ae_restrict_of_forall_mem measurableSet_Icc fun t ht => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hD t ht) 2)
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2
      ((hi.mono_set Ioo_subset_Icc_self).congr_fun (fun t ht => (hr t ht).symm) measurableSet_Ioo),
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2
      ((hi2.mono_set Ioo_subset_Icc_self).congr_fun (fun t ht => by simp only [hr t ht, D])
        measurableSet_Ioo), ?_⟩
  have he : (∫ t in Ioo a b, r t ^ 2) =
      ∫ t in Ioo a b, (displacement K₀.1 (z K₀) t - displacement K₁.1 (z K₁) t) ^ 2 :=
    setIntegral_congr_fun measurableSet_Ioo fun t ht => by simp only [hr t ht]; ring
  unfold arcSquare displacementEnergy halfSquareIntegral
  rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo, he]
  ring

/-- On an arc `[a, b] ⊆ (T - π, T]`, the tangent residual of the pinned support difference is
square integrable, with square integral twice the energy of the tangent displacements. -/
theorem tangent_capDifference_integrable {a b T : ℝ}
    (hab : a < b) (hb : b < a + π) (haT : T - π < a) (hbT : b ≤ T) (K₀ K₁ : ConvexBodySet) :
    IntervalIntegrable (tangentResidual T (capDifference K₀.1 K₁.1)
        (capDifferenceDeriv K₀.1 K₁.1)) volume a b ∧
      IntervalIntegrable (fun t => tangentResidual T (capDifference K₀.1 K₁.1)
        (capDifferenceDeriv K₀.1 K₁.1) t ^ 2) volume a b ∧
      arcSquare a b (tangentResidual T (capDifference K₀.1 K₁.1) (capDifferenceDeriv K₀.1 K₁.1)) =
        2 * displacementEnergy a b (fun K => tangentParam K.1 T) K₀ K₁ := by
  refine residual_of_displacement hab hb (fun K => (theorem8_3_1 K.2 haT hab.le hbT).1)
    (fun K t ht => ?_) fun t ht => ?_
  · rcases (ht.2.trans hbT).lt_or_eq with htT | rfl
    · simpa only [tangentParam, htT, ↓reduceIte] using vint_mem_line_left K.1 t T
    · simp only [tangentParam, lt_irrefl, ↓reduceIte]
      exact dot_vminus_uvec K.1 _
  · have hs : sin (T - t) ≠ 0 :=
      (sin_pos_of_pos_of_lt_pi (by linarith [ht.2]) (by linarith [ht.1])).ne'
    rw [capDifference, capDifferenceDeriv, tangentResidual_pinned _ _ _ _ hs]
    exact (tangent_displacement_sub (ht.2.trans_le hbT)).symm

/-- On an arc `[a, b]` with `b < a + π`, the corner residual of the pinned support difference is
square integrable, with square integral twice the energy of the outer-corner displacements. -/
theorem corner_capDifference_integrable {a b : ℝ} (hab : a < b) (hb : b < a + π)
    (K₀ K₁ : ConvexBodySet) :
    IntervalIntegrable (cornerResidual (capDifference K₀.1 K₁.1)
        (capDifferenceDeriv K₀.1 K₁.1)) volume a b ∧
      IntervalIntegrable (fun t => cornerResidual (capDifference K₀.1 K₁.1)
        (capDifferenceDeriv K₀.1 K₁.1) t ^ 2) volume a b ∧
      arcSquare a b (cornerResidual (capDifference K₀.1 K₁.1) (capDifferenceDeriv K₀.1 K₁.1)) =
        2 * displacementEnergy a b (fun K => outerCorner K.1) K₀ K₁ :=
  residual_of_displacement hab hb (fun K => opt_outerCorner_cbv K.2 a b)
    (fun K t _ => inj_dot_outerCorner_uvec K.1 t) fun t _ => by
      rw [capDifference, capDifferenceDeriv, cornerResidual_pinned]
      exact (outer_displacement_sub K₀.1 K₁.1 t).symm

/-- The pinned support difference of two right-angle caps satisfies the hypotheses of the four-arc
estimate, and half the sum of the square integrals of its residuals is the cap energy. -/
theorem capDifference_data {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (K₀ K₁ : ConvexBodySet) (h₀ : IsCap K₀.1 (π / 2)) (h₁ : IsCap K₁.1 (π / 2)) :
    FourResidualData φ (capDifference K₀.1 K₁.1) (capDifferenceDeriv K₀.1 K₁.1) ∧
      fourResidualEnergy φ (capDifference K₀.1 K₁.1) (capDifferenceDeriv K₀.1 K₁.1) =
        capResidualEnergy φ K₀ K₁ := by
  obtain ⟨hφ0, hφ4⟩ := hφ
  have := pi_pos
  obtain ⟨i₁, s₁, e₁⟩ := tangent_capDifference_integrable (T := π / 2) (a := 0) (b := φ)
    hφ0 (by linarith) (by linarith) (by linarith) K₀ K₁
  obtain ⟨i₂, s₂, e₂⟩ := corner_capDifference_integrable (a := φ) (b := π / 2 - φ)
    (by linarith) (by linarith) K₀ K₁
  obtain ⟨i₃, s₃, e₃⟩ := tangent_capDifference_integrable (T := π - φ) (a := π / 2 - φ)
    (b := π / 2) (by linarith) (by linarith) (by linarith) (by linarith) K₀ K₁
  obtain ⟨i₄, s₄, e₄⟩ := tangent_capDifference_integrable (T := π) (a := π / 2) (b := π)
    (by linarith) (by linarith) (by linarith) le_rfl K₀ K₁
  refine ⟨⟨(K₁.2.continuous_supp.sub K₀.2.continuous_supp).add (continuous_cos.const_mul _),
    fun t _ => ?_, ?_, pinnedDifference_pi _, i₁, i₂, i₃, i₄, s₁, s₂, s₃, s₄⟩, ?_⟩
  · convert (((hasDerivWithinAt_supp_right K₁.2 t).sub (hasDerivWithinAt_supp_right K₀.2 t)).mono
      Ioi_subset_Ici_self).add
      ((hasDerivAt_cos t).const_mul (supp K₁.1 π - supp K₀.1 π)).hasDerivWithinAt using 1
    · rfl
    · simp only [capDifferenceDeriv, pinnedDerivative, opt_g]
      ring
  · rw [capDifference, pinnedDifference_top, h₁.2.2.2.1, h₀.2.2.2.1, sub_self]
  · rw [fourResidualEnergy, capResidualEnergy, e₁, e₂, e₃, e₄,
      show π / 2 + (π / 2 - φ) = π - φ by ring]
    ring

/-!
## Square control of weighted integrals

`SquareControl v k e` says that `v² ≤ k e`, for a value `v` with kernel square norm `k` and residual
energy `e`. By Cauchy–Schwarz an integral of a kernel times a residual has such a control, and
controls with disjoint residual energies add.
-/

/-- A value `v` with kernel square norm `k` and residual energy `e`: `v² ≤ k e`. -/
structure SquareControl (value k e : ℝ) : Prop where
  kernel_nonneg : 0 ≤ k
  energy_nonneg : 0 ≤ e
  bound : value ^ 2 ≤ k * e

theorem SquareControl.zero {e : ℝ} (he : 0 ≤ e) : SquareControl 0 0 e :=
  ⟨le_rfl, he, by simp⟩

theorem SquareControl.abs_bound {v k e : ℝ} (h : SquareControl v k e) :
    |v| ≤ sqrt k * sqrt e := by
  simpa only [sqrt_sq_eq_abs, sqrt_mul h.kernel_nonneg] using sqrt_le_sqrt h.bound

/-- Controls with disjoint residual energies add, by Cauchy–Schwarz in two terms. -/
theorem SquareControl.add {v w k l e f : ℝ}
    (h : SquareControl v k e) (h' : SquareControl w l f) :
    SquareControl (v + w) (k + l) (e + f) := by
  refine ⟨add_nonneg h.kernel_nonneg h'.kernel_nonneg,
    add_nonneg h.energy_nonneg h'.energy_nonneg, ?_⟩
  have hc := four_term_sq_le (sqrt k) (sqrt l) 0 0 (sqrt e) (sqrt f) 0 0
  simp only [sq_sqrt h.kernel_nonneg, sq_sqrt h'.kernel_nonneg, sq_sqrt h.energy_nonneg,
    sq_sqrt h'.energy_nonneg, zero_mul, zero_pow two_ne_zero, add_zero] at hc
  have hv := (abs_add_le v w).trans (add_le_add h.abs_bound h'.abs_bound)
  calc (v + w) ^ 2 = |v + w| ^ 2 := (sq_abs _).symm
    _ ≤ (sqrt k * sqrt e + sqrt l * sqrt f) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hv 2
    _ ≤ (k + l) * (e + f) := hc

theorem SquareControl.smul {v k e : ℝ} (h : SquareControl v k e) (a : ℝ) :
    SquareControl (a * v) (a ^ 2 * k) e :=
  ⟨mul_nonneg (sq_nonneg a) h.kernel_nonneg, h.energy_nonneg, by
    rw [mul_pow, mul_assoc]; exact mul_le_mul_of_nonneg_left h.bound (sq_nonneg a)⟩

theorem SquareControl.mono_energy {v k e E : ℝ} (h : SquareControl v k e)
    (he : e ≤ E) : SquareControl v k E :=
  ⟨h.kernel_nonneg, h.energy_nonneg.trans he,
    h.bound.trans (mul_le_mul_of_nonneg_left he h.kernel_nonneg)⟩

theorem SquareControl.mono_kernel {v k K e : ℝ} (h : SquareControl v k e)
    (hk : k ≤ K) : SquareControl v K e :=
  ⟨h.kernel_nonneg.trans hk, h.energy_nonneg,
    h.bound.trans (mul_le_mul_of_nonneg_right hk h.energy_nonneg)⟩

/-- Cauchy–Schwarz: the integral of a continuous kernel times a residual is controlled by the square
integrals of the kernel and of the residual. -/
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
  refine ⟨intervalIntegral.integral_nonneg hab fun t _ => sq_nonneg (k t),
    arcSquare_nonneg hab r, ?_⟩
  simp only [arcSquare, intervalIntegral.integral_of_le hab]
  exact integral_mul_sq_le (volume.restrict (Ioc a b)) hk2.1 hr2.1 hkr.1

/-- The energy over a subarc is at most the energy over the arc. -/
theorem arcSquare_mono {a b c d : ℝ} {r : ℝ → ℝ}
    (hr2 : IntervalIntegrable (fun t => r t ^ 2) volume a b)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) : arcSquare c d r ≤ arcSquare a b r :=
  intervalIntegral.integral_mono_interval hac hcd hdb
    (Eventually.of_forall fun _ => sq_nonneg _) hr2

/-- Restrict an interval-integrable function to an ordered subinterval. -/
theorem intervalIntegrable_subinterval {a b c d : ℝ} {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    IntervalIntegrable f volume c d :=
  hf.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le hac (hcd.trans hdb))
    (mem_uIcc_of_le (hac.trans hcd) hdb))

/-- A residual divided by a sine that does not vanish on the arc is integrable. -/
theorem residual_div_sin_integrable {a b T : ℝ} {r : ℝ → ℝ}
    (hab : a ≤ b) (hr : IntervalIntegrable r volume a b)
    (hs : ∀ t ∈ Icc a b, sin (T - t) ≠ 0) :
    IntervalIntegrable (fun t => r t / sin (T - t)) volume a b := by
  simpa only [div_eq_mul_inv] using hr.mul_continuousOn (by
    rw [uIcc_of_le hab]
    exact ContinuousOn.inv₀ (by fun_prop) hs)

/-!
## Exact square integrals of the kernels

The kernels are `1 / sin u`, `1 / cos u`, `1 / sin (T - u)` and the tail kernel
`(A + cos u) / sin u`; their square integrals over compact arcs where the denominators do not
vanish have closed forms.
-/

/-- The fundamental theorem of calculus on a compact arc where the primitive is differentiable. -/
private theorem integral_eq_sub_of_hasDerivAt_Icc {F f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ u ∈ Icc a b, HasDerivAt F (f u) u) (hf : ContinuousOn f (Icc a b)) :
    (∫ u in a..b, f u) = F b - F a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hF u (by rwa [uIcc_of_le hab] at hu)) (hf.intervalIntegrable_of_Icc hab)

theorem hasDerivAt_cotangent {u : ℝ} (hs : sin u ≠ 0) :
    HasDerivAt (fun u => cos u / sin u) (-(1 / sin u) ^ 2) u := by
  convert (hasDerivAt_cos u).div (hasDerivAt_sin u) hs using 1
  field_simp
  linear_combination sin_sq_add_cos_sq u

theorem cosecant_sq_integral {a b : ℝ} (hab : a ≤ b) (hs : ∀ u ∈ Icc a b, sin u ≠ 0) :
    (∫ u in a..b, (1 / sin u) ^ 2) = cos a / sin a - cos b / sin b := by
  rw [integral_eq_sub_of_hasDerivAt_Icc hab (f := fun u => (1 / sin u) ^ 2)
    (F := fun u => -(cos u / sin u))
    (fun u hu => by simpa only [neg_neg] using (hasDerivAt_cotangent (hs u hu)).fun_neg)
    ((continuousOn_const.div continuous_sin.continuousOn hs).pow 2)]
  ring

theorem secant_sq_integral {a b : ℝ} (hab : a ≤ b) (hc : ∀ u ∈ Icc a b, cos u ≠ 0) :
    (∫ u in a..b, (1 / cos u) ^ 2) = tan b - tan a :=
  integral_eq_sub_of_hasDerivAt_Icc hab
    (fun u hu => by simpa only [one_div_pow] using hasDerivAt_tan (hc u hu))
    ((continuousOn_const.div continuous_cos.continuousOn hc).pow 2)

theorem shifted_cosecant_sq_integral {a b T : ℝ} (hab : a ≤ b)
    (hs : ∀ u ∈ Icc a b, sin (T - u) ≠ 0) :
    (∫ u in a..b, (1 / sin (T - u)) ^ 2) =
      cos (T - b) / sin (T - b) - cos (T - a) / sin (T - a) :=
  integral_eq_sub_of_hasDerivAt_Icc hab (F := fun u => cos (T - u) / sin (T - u))
    (fun u hu => by
      convert (hasDerivAt_cotangent (hs u hu)).comp u ((hasDerivAt_id u).const_sub T) using 1
      · rfl
      · ring)
    ((continuousOn_const.div (by fun_prop) hs).pow 2)

/-- The tail kernel `(A + cos u) / sin u`, through which the last residual enters the middle arc. -/
def tailKernel (A u : ℝ) : ℝ := (A + cos u) / sin u

/-- A primitive of the square of the tail kernel. -/
def tailKernelPrimitive (A u : ℝ) : ℝ :=
  -(A ^ 2 + 1) * (cos u / sin u) - 2 * A * (1 / sin u) - u

theorem hasDerivAt_tailKernel (A : ℝ) {u : ℝ} (hs : sin u ≠ 0) :
    HasDerivAt (tailKernel A) (-(1 + A * cos u) / sin u ^ 2) u := by
  convert ((hasDerivAt_cos u).const_add A).div (hasDerivAt_sin u) hs using 1
  · rfl
  · field_simp
    linear_combination sin_sq_add_cos_sq u

theorem tailKernel_sq_integral (A : ℝ) {a b : ℝ} (hab : a ≤ b)
    (hs : ∀ u ∈ Icc a b, sin u ≠ 0) :
    (∫ u in a..b, tailKernel A u ^ 2) = tailKernelPrimitive A b - tailKernelPrimitive A a := by
  refine integral_eq_sub_of_hasDerivAt_Icc hab (fun u hu => ?_)
    (((continuousOn_const.add continuous_cos.continuousOn).div
      continuous_sin.continuousOn hs).pow 2)
  have hsu := hs u hu
  convert (((hasDerivAt_cotangent hsu).const_mul (-(A ^ 2 + 1))).sub
    (((hasDerivAt_const u (1 : ℝ)).div (hasDerivAt_sin u) hsu).const_mul (2 * A))).sub
    (hasDerivAt_id u) using 1
  · rfl
  · unfold tailKernel
    field_simp
    linear_combination sin_sq_add_cos_sq u

/-- The square integral of the last-arc kernel up to `t`. -/
theorem last_kernel_norm {t : ℝ} (ht : t ∈ Ico (π / 2) π) :
    sin t ^ 2 * (∫ u in (π / 2)..t, (1 / sin u) ^ 2) = -sin t * cos t := by
  have hs : ∀ u ∈ Icc (π / 2) t, sin u ≠ 0 := fun u hu =>
    (sin_pos_of_pos_of_lt_pi (by linarith [hu.1, pi_pos]) (hu.2.trans_lt ht.2)).ne'
  rw [cosecant_sq_integral ht.1 hs, cos_pi_div_two, sin_pi_div_two, zero_div, zero_sub]
  field_simp [hs t ⟨ht.1, le_rfl⟩]

/-!
## The kernel norms on the four arcs

At a point `t` of each arc, the squared norms of the kernels that represent `f(t)` add up to the
closed form `greenNormSquared φ t`, which is at most `2 sec² φ`.
-/

/-- For `0 < φ < π / 4`: `cos φ > 0`, `sec φ ≥ 1`, `tan φ ≥ 0` and `sec² φ = 1 + tan² φ`. -/
theorem cap_angle_parameters {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    0 < cos φ ∧ 1 ≤ 1 / cos φ ∧ 0 ≤ tan φ ∧
      (1 / cos φ) ^ 2 = 1 + tan φ ^ 2 := by
  have hc : 0 < cos φ :=
    cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, pi_pos], by linarith [hφ.2, pi_pos]⟩
  refine ⟨hc, one_le_one_div hc (cos_le_one φ),
    tan_nonneg_of_nonneg_of_le_pi_div_two hφ.1.le (by linarith [hφ.2, pi_pos]), ?_⟩
  rw [div_pow, one_pow, ← inv_one_add_tan_sq hc.ne', one_div, inv_inv]

/-- On a short arc `[0, φ]` with `φ < π / 4`, `cos t ≥ 1 / 2`. -/
theorem cos_ge_half_of_small {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ht : t ∈ Icc 0 φ) : (1 / 2 : ℝ) ≤ cos t := by
  have hφ1 : φ < 1 := by linarith [hφ.2, pi_lt_four]
  nlinarith [one_sub_sq_div_two_le_cos (x := t), ht.1, ht.2]

/-- The square integral of the third-arc kernel over the whole third arc. -/
theorem third_full_kernel_norm {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    (∫ u in (π / 2 - φ)..(π / 2), (1 / sin (π - φ - u)) ^ 2) = tan φ := by
  have hs : ∀ u ∈ Icc (π / 2 - φ) (π / 2), sin (π - φ - u) ≠ 0 := fun u hu =>
    (sin_pos_of_pos_of_lt_pi (by linarith [hu.2, hφ.2, pi_pos])
      (by linarith [hu.1, hφ.1, pi_pos])).ne'
  rw [shifted_cosecant_sq_integral (by linarith [hφ.1]) hs]
  simp only [show π - φ - π / 2 = π / 2 - φ by ring, show π - φ - (π / 2 - φ) = π / 2 by ring,
    cos_pi_div_two_sub, sin_pi_div_two_sub, cos_pi_div_two, sin_pi_div_two,
    zero_div, sub_zero, tan_eq_sin_div_cos]

/-- On the third arc, the kernel norm of the value at `π - φ` on the last arc and the third-arc
kernel norm add up to `greenNormSquared`. -/
theorem third_evaluation_norm {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ht : t ∈ Icc (π / 2 - φ) (π / 2)) :
    (-(cos t / cos φ)) ^ 2 * (-sin (π - φ) * cos (π - φ)) +
      sin (π - φ - t) ^ 2 *
        (∫ u in t..(π / 2), (1 / sin (π - φ - u)) ^ 2) =
      sin t * cos t + 2 * tan φ * cos t ^ 2 := by
  have hc : cos φ ≠ 0 := (cap_angle_parameters hφ).1.ne'
  have hs : ∀ u ∈ Icc t (π / 2), sin (π - φ - u) ≠ 0 := fun u hu =>
    (sin_pos_of_pos_of_lt_pi (by linarith [hu.2, hφ.2, pi_pos])
      (by linarith [hu.1, ht.1, pi_pos])).ne'
  have hst := hs t ⟨le_rfl, ht.2⟩
  rw [shifted_cosecant_sq_integral ht.2 hs, show π - φ - π / 2 = π / 2 - φ by ring,
    cos_pi_div_two_sub, sin_pi_div_two_sub, sin_pi_sub, cos_pi_sub, tan_eq_sin_div_cos]
  field_simp
  rw [show π - φ - t = π - (φ + t) by ring, sin_pi_sub, cos_pi_sub, sin_add, cos_add]
  linear_combination cos t * (cos φ * sin t + cos t * sin φ) * sin_sq_add_cos_sq φ

/-- On the middle arc, the kernel norms of the middle, third and last residuals add up to
`greenNormSquared`; the last residual enters by two kernels on disjoint subarcs. -/
theorem middle_evaluation_norm {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ht : t ∈ Icc φ (π / 2 - φ)) :
    (π / 2 - φ - t) + (∫ u in (π / 2 - φ)..(π / 2), (1 / sin (π - φ - u)) ^ 2) +
      (1 / cos φ - sin t) ^ 2 * (∫ u in (π / 2)..(π / 2 + t), (1 / sin u) ^ 2) +
      (∫ u in (π / 2 + t)..(π - φ), tailKernel (1 / cos φ) u ^ 2) =
      cos t * (2 / cos φ - sin t) := by
  have hcφ : cos φ ≠ 0 := (cap_angle_parameters hφ).1.ne'
  have hsφ : sin φ ≠ 0 := (sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2, pi_pos])).ne'
  have hct : cos t ≠ 0 :=
    (cos_pos_of_mem_Ioo ⟨by linarith [ht.1, hφ.1, pi_pos], by linarith [ht.2, hφ.1]⟩).ne'
  have hs : ∀ u ∈ Icc (π / 2) (π - φ), sin u ≠ 0 := fun u hu =>
    (sin_pos_of_pos_of_lt_pi (by linarith [hu.1, pi_pos]) (by linarith [hu.2, hφ.1])).ne'
  rw [third_full_kernel_norm hφ,
    cosecant_sq_integral (by linarith [ht.1, hφ.1])
      fun u hu => hs u ⟨hu.1, by linarith [hu.2, ht.2]⟩,
    tailKernel_sq_integral _ (by linarith [ht.2])
      fun u hu => hs u ⟨by linarith [hu.1, ht.1, hφ.1], hu.2⟩]
  simp only [tailKernelPrimitive, sin_pi_sub, cos_pi_sub, sin_add, cos_add, sin_pi_div_two,
    cos_pi_div_two, one_mul, zero_mul, add_zero, zero_div, zero_sub, tan_eq_sin_div_cos]
  field_simp
  linear_combination 2 * cos φ * cos t * sin_sq_add_cos_sq φ +
    2 * cos φ * sin φ * (cos φ * sin t - 2) * sin_sq_add_cos_sq t

/-- On the first arc, the kernel norm of the value at `φ` on the middle arc and the first-arc kernel
norm add up to `greenNormSquared`. -/
theorem first_evaluation_norm {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ht : t ∈ Icc 0 φ) :
    cos t ^ 2 * ((1 / cos φ) ^ 2 * (cos φ * (2 / cos φ - sin φ)) +
      ∫ u in t..φ, (1 / cos u) ^ 2) =
      cos t ^ 2 * (2 * (1 / cos φ) ^ 2 - tan t) := by
  have hcφ := (cap_angle_parameters hφ).1.ne'
  rw [secant_sq_integral ht.2 fun u hu => (cos_pos_of_mem_Ioo
    ⟨by linarith [hu.1, ht.1, pi_pos], by linarith [hu.2, hφ.2, pi_pos]⟩).ne',
    tan_eq_sin_div_cos φ]
  field_simp
  ring

/-- The closed form of the squared kernel norm at `t ∈ [0, π]`, one formula on each arc. -/
def greenNormSquared (φ t : ℝ) : ℝ :=
  if t ≤ φ then cos t ^ 2 * (2 * (1 / cos φ) ^ 2 - tan t)
  else if t ≤ π / 2 - φ then cos t * (2 / cos φ - sin t)
  else if t ≤ π / 2 then sin t * cos t + 2 * tan φ * cos t ^ 2
  else -sin t * cos t

/-- The squared kernel norm is at most `2 sec² φ`, its value at `0`. -/
theorem greenNormSquared_le {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ht : t ∈ Icc 0 π) : greenNormSquared φ t ≤ 2 * (1 / cos φ) ^ 2 := by
  obtain ⟨hcφ, hA, htanφ, hAid⟩ := cap_angle_parameters hφ
  have hs : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2
  have hcost : cos t ^ 2 ≤ 1 := by nlinarith [sin_sq_add_cos_sq t]
  unfold greenNormSquared
  split_ifs with h1 h2 h3
  · nlinarith [mul_nonneg (sq_nonneg (cos t))
      (tan_nonneg_of_nonneg_of_le_pi_div_two ht.1 (by linarith [hφ.2, pi_pos]))]
  · have hct : 0 ≤ cos t :=
      cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, pi_pos], by linarith [hφ.1]⟩
    rw [div_eq_mul_one_div 2]
    nlinarith [mul_nonneg hct hs, cos_le_one t]
  · nlinarith [sin_sq_add_cos_sq t, sq_nonneg (sin t - cos t), sq_nonneg (tan φ - 1 / 2)]
  · nlinarith [sin_sq_add_cos_sq t, sq_nonneg (sin t + cos t)]

/-!
## The four-arc estimate

Integrating the residual equations from `f(π/2) = f(π) = 0` writes `f(t)` on each arc as a sum of
integrals of kernels times residuals; the last residual enters the middle arc through the tail
kernel, by a product integration. The kernel norms then bound `|f(t)|` by `2 sec φ` times the
square root of the residual energy.
-/

section FourArcs

variable {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) {f df : ℝ → ℝ} (h : FourResidualData φ f df)

include h in
/-- The formula for `f` on the last arc. -/
theorem sharp_last_formula {t : ℝ} (ht : t ∈ Ico (π / 2) π) :
    f t = -sin t * (∫ u in (π / 2)..t, (1 / sin u) * tangentResidual π f df u) := by
  have hs : ∀ u ∈ Icc (π / 2) t, sin (π - u) ≠ 0 := fun u hu => by
    rw [sin_pi_sub]
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.1, pi_pos]) (hu.2.trans_lt ht.2)).ne'
  have he := tangent_reconstruct_right ht.1 h.continuous.continuousOn
    (fun u hu => h.rightDeriv u ⟨by linarith [hu.1, pi_pos], hu.2.trans ht.2⟩) hs
    (residual_div_sin_integrable ht.1
      (intervalIntegrable_subinterval h.last le_rfl ht.1 ht.2.le) hs)
  simp only [tangentQuotient, h.top_zero, h.left_zero, sin_pi_sub, zero_mul, sub_zero, zero_div,
    zero_add, zero_sub] at he
  simp only [one_div_mul_eq_div]
  linear_combination he

include hφ h in
/-- The formula for `f` on the third arc, from its value at `π - φ` on the last arc. -/
theorem sharp_third_formula {t : ℝ} (ht : t ∈ Icc (π / 2 - φ) (π / 2)) :
    f t = -(cos t / cos φ) * f (π - φ) + sin (π - φ - t) *
      (∫ u in t..(π / 2), (1 / sin (π - φ - u)) * tangentResidual (π - φ) f df u) := by
  have hc : cos φ ≠ 0 := (cap_angle_parameters hφ).1.ne'
  have hs : ∀ u ∈ Icc t (π / 2), sin (π - φ - u) ≠ 0 := fun u hu =>
    (sin_pos_of_pos_of_lt_pi (by linarith [hu.2, hφ.2, pi_pos])
      (by linarith [hu.1, ht.1, pi_pos])).ne'
  have he := tangent_reconstruct_left ht.2 h.continuous.continuousOn
    (fun u hu => h.rightDeriv u
      ⟨by linarith [hu.1, ht.1, hφ.2, pi_pos], by linarith [hu.2, pi_pos]⟩) hs
    (residual_div_sin_integrable ht.2 (intervalIntegrable_subinterval h.third ht.1 ht.2 le_rfl) hs)
  have hcos : cos (π - φ - t) * cos φ - sin (π - φ - t) * sin φ = -cos t := by
    rw [← cos_add, show π - φ - t + φ = π - t by ring, cos_pi_sub]
  simp only [tangentQuotient, h.top_zero, show π - φ - π / 2 = π / 2 - φ by ring,
    cos_pi_div_two_sub, sin_pi_div_two_sub] at he
  simp only [one_div_mul_eq_div]
  rw [he]
  field_simp
  linear_combination f (π - φ) * hcos

include hφ h in
/-- The formula for `f` on the first arc, from its value at `φ` on the middle arc. -/
theorem sharp_first_formula {t : ℝ} (ht : t ∈ Icc 0 φ) :
    f t = cos t * ((1 / cos φ) * f φ +
      ∫ u in t..φ, (1 / cos u) * tangentResidual (π / 2) f df u) := by
  have hs : ∀ u ∈ Icc t φ, sin (π / 2 - u) ≠ 0 := fun u hu => by
    rw [sin_pi_div_two_sub]
    exact (cos_pos_of_mem_Ioo
      ⟨by linarith [hu.1, ht.1, pi_pos], by linarith [hu.2, hφ.2, pi_pos]⟩).ne'
  have he := tangent_reconstruct_left ht.2 h.continuous.continuousOn
    (fun u hu => h.rightDeriv u ⟨by linarith [hu.1, ht.1], by linarith [hu.2, hφ.2, pi_pos]⟩)
    hs (residual_div_sin_integrable ht.2
      (intervalIntegrable_subinterval h.first ht.1 ht.2 le_rfl) hs)
  simp only [tangentQuotient, h.top_zero, zero_mul, zero_add, sub_zero, sin_pi_div_two_sub] at he
  simp only [one_div_mul_eq_div]
  exact he

include h in
/-- Product integration of the last residual against the tail kernel: since `f(π) = 0`, the tangent
residual on the last arc is `cot u · f(u) - f'(u)`. -/
theorem tail_product_integral (A : ℝ) {a b : ℝ}
    (ha : π / 2 ≤ a) (hab : a ≤ b) (hb : b < π) :
    (∫ u in a..b, f u) = tailKernel A a * f a - tailKernel A b * f b -
      ∫ u in a..b, tailKernel A u * tangentResidual π f df u := by
  have hs : ∀ u ∈ Icc a b, sin u ≠ 0 := fun u hu =>
    (sin_pos_of_pos_of_lt_pi (by linarith [hu.1, pi_pos]) (hu.2.trans_lt hb)).ne'
  have hk : ContinuousOn (tailKernel A) (Icc a b) :=
    (continuousOn_const.add continuous_cos.continuousOn).div continuous_sin.continuousOn hs
  have hkr : IntervalIntegrable (fun u => tailKernel A u * tangentResidual π f df u) volume a b :=
    (intervalIntegrable_subinterval h.last ha hab hb.le).continuousOn_mul
      (by simpa only [uIcc_of_le hab] using hk)
  have hf : IntervalIntegrable (fun u => -f u) volume a b :=
    (h.continuous.intervalIntegrable a b).neg
  have hd : ∀ u ∈ Ioo a b, HasDerivWithinAt (fun u => tailKernel A u * f u)
      (-f u - tailKernel A u * tangentResidual π f df u) (Ioi u) u := by
    intro u hu
    have hsu := hs u (Ioo_subset_Icc_self hu)
    convert (hasDerivAt_tailKernel A hsu).hasDerivWithinAt.mul
      (h.rightDeriv u ⟨by linarith [hu.1, pi_pos], hu.2.trans hb⟩) using 1
    rw [tangentResidual_left h.left_zero]
    unfold tailKernel
    field_simp
    linear_combination -(f u) * sin_sq_add_cos_sq u
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (hk.mul h.continuous.continuousOn) hd (hf.sub hkr)
  rw [intervalIntegral.integral_sub hf hkr, intervalIntegral.integral_neg] at he
  simp only [Pi.mul_apply] at he
  linarith

include hφ h in
/-- The formula for `f` on the middle arc. The last residual enters through the third-arc value at
`π / 2 - φ` and through the product integral of `f` over `[π / 2 + t, π - φ]`, and the two
occurrences are combined before any estimate. -/
theorem sharp_middle_formula {t : ℝ} (ht : t ∈ Icc φ (π / 2 - φ)) :
    f t = (∫ u in t..(π / 2 - φ), cornerResidual f df u) +
      (∫ u in (π / 2 - φ)..(π / 2), (1 / sin (π - φ - u)) * tangentResidual (π - φ) f df u) +
      (1 / cos φ - sin t) * (∫ u in (π / 2)..(π / 2 + t), (1 / sin u) * tangentResidual π f df u) +
      (∫ u in (π / 2 + t)..(π - φ), tailKernel (1 / cos φ) u * tangentResidual π f df u) := by
  have ⟨hφ0, hφ4⟩ := hφ
  have hpi := pi_pos
  have hcφ : cos φ ≠ 0 := (cap_angle_parameters hφ).1.ne'
  have hsφ : sin φ ≠ 0 := (sin_pos_of_pos_of_lt_pi hφ0 (by linarith)).ne'
  have hct : cos t ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [ht.1], by linarith [ht.2]⟩).ne'
  have hshift : IntervalIntegrable (fun u => f (u + π / 2)) volume t (π / 2 - φ) :=
    (h.continuous.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hdf : IntervalIntegrable df volume t (π / 2 - φ) := by
    simpa only [cornerResidual, sub_sub_cancel] using
      hshift.sub (intervalIntegrable_subinterval h.middle ht.1 ht.2 le_rfl)
  have hrec := corner_reconstruct ht.2 h.continuous.continuousOn
    (fun u hu => h.rightDeriv u ⟨by linarith [hu.1, ht.1], by linarith [hu.2]⟩) hdf hshift
  have hthird := sharp_third_formula hφ h (t := π / 2 - φ) ⟨le_rfl, by linarith⟩
  have hlast := sharp_last_formula h (t := π / 2 + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have htail := tail_product_integral h (1 / cos φ)
    (a := π / 2 + t) (b := π - φ) (by linarith [ht.1]) (by linarith [ht.2]) (by linarith)
  have hT : tailKernel (1 / cos φ) (π - φ) = tan φ := by
    simp only [tailKernel, sin_pi_sub, cos_pi_sub, tan_eq_sin_div_cos]
    field_simp
    linear_combination -sin_sq_add_cos_sq φ
  have hstart : tailKernel (1 / cos φ) (π / 2 + t) = (1 / cos φ - sin t) / cos t := by
    simp only [tailKernel, sin_add, cos_add, sin_pi_div_two, cos_pi_div_two, one_mul, zero_mul,
      add_zero, zero_sub]
    ring
  have hIshift : (∫ u in t..(π / 2 - φ), f (u + π / 2)) = ∫ u in (π / 2 + t)..(π - φ), f u := by
    rw [intervalIntegral.integral_comp_add_right f (π / 2)]
    congr 1 <;> ring
  simp only [show π - φ - (π / 2 - φ) = π / 2 by ring,
    sin_pi_div_two, cos_pi_div_two_sub, one_mul] at hthird
  simp only [sin_add, sin_pi_div_two, cos_pi_div_two, one_mul, zero_mul, add_zero] at hlast
  rw [hIshift, htail, hT, hstart, hthird, hlast, tan_eq_sin_div_cos] at hrec
  rw [hrec]
  field_simp
  ring

include h in
/-- The control of `f(t)` on the last arc. -/
theorem sharp_last_control {t : ℝ} (ht : t ∈ Icc (π / 2) π) :
    SquareControl (f t) (-sin t * cos t) (arcSquare (π / 2) π (tangentResidual π f df)) := by
  rcases ht.2.lt_or_eq with htπ | rfl
  · have hs : ∀ u ∈ Icc (π / 2) t, sin u ≠ 0 := fun u hu =>
      (sin_pos_of_pos_of_lt_pi (by linarith [hu.1, pi_pos]) (hu.2.trans_lt htπ)).ne'
    have hk : ContinuousOn (fun u => 1 / sin u) (Icc (π / 2) t) :=
      continuousOn_const.div continuous_sin.continuousOn hs
    have hI := (integral_square_control ht.1 hk
      (intervalIntegrable_subinterval h.last le_rfl ht.1 ht.2)
      (intervalIntegrable_subinterval h.last_sq le_rfl ht.1 ht.2)).smul (-sin t)
    rw [← sharp_last_formula h ⟨ht.1, htπ⟩, neg_sq, last_kernel_norm ⟨ht.1, htπ⟩] at hI
    exact hI.mono_energy (arcSquare_mono h.last_sq le_rfl ht.1 ht.2)
  · simpa only [h.left_zero, sin_pi, neg_zero, zero_mul] using
      SquareControl.zero (arcSquare_nonneg (by linarith [pi_pos]) (tangentResidual π f df))

include hφ h in
/-- The control of `f(t)` on the third arc. -/
theorem sharp_third_control {t : ℝ} (ht : t ∈ Icc (π / 2 - φ) (π / 2)) :
    SquareControl (f t) (sin t * cos t + 2 * tan φ * cos t ^ 2)
      (arcSquare (π / 2 - φ) (π / 2) (tangentResidual (π - φ) f df) +
        arcSquare (π / 2) π (tangentResidual π f df)) := by
  have hs : ∀ u ∈ Icc t (π / 2), sin (π - φ - u) ≠ 0 := fun u hu =>
    (sin_pos_of_pos_of_lt_pi (by linarith [hu.2, hφ.2, pi_pos])
      (by linarith [hu.1, ht.1, pi_pos])).ne'
  have hk : ContinuousOn (fun u => 1 / sin (π - φ - u)) (Icc t (π / 2)) :=
    continuousOn_const.div (by fun_prop) hs
  have hI := (integral_square_control ht.2 hk
    (intervalIntegrable_subinterval h.third ht.1 ht.2 le_rfl)
    (intervalIntegrable_subinterval h.third_sq ht.1 ht.2 le_rfl)).smul (sin (π - φ - t))
  have hT := (sharp_last_control h (t := π - φ)
    ⟨by linarith [hφ.2, pi_pos], by linarith [hφ.1]⟩).smul (-(cos t / cos φ))
  have he := hT.add hI
  rw [← sharp_third_formula hφ h ht, third_evaluation_norm hφ ht] at he
  exact he.mono_energy (by linarith [arcSquare_mono h.third_sq ht.1 ht.2 le_rfl])

include hφ h in
/-- The control of `f(t)` on the middle arc. -/
theorem sharp_middle_control {t : ℝ} (ht : t ∈ Icc φ (π / 2 - φ)) :
    SquareControl (f t) (cos t * (2 / cos φ - sin t))
      (arcSquare φ (π / 2 - φ) (cornerResidual f df) +
        arcSquare (π / 2 - φ) (π / 2) (tangentResidual (π - φ) f df) +
        arcSquare (π / 2) π (tangentResidual π f df)) := by
  have ⟨hφ0, hφ4⟩ := hφ
  have hpi := pi_pos
  have hvt : π / 2 ≤ π / 2 + t := by linarith [ht.1]
  have hvtT : π / 2 + t ≤ π - φ := by linarith [ht.2]
  have hs4 : ∀ u ∈ Icc (π / 2) (π - φ), sin u ≠ 0 := fun u hu =>
    (sin_pos_of_pos_of_lt_pi (by linarith [hu.1]) (by linarith [hu.2])).ne'
  have hk3 : ContinuousOn (fun u => 1 / sin (π - φ - u)) (Icc (π / 2 - φ) (π / 2)) :=
    continuousOn_const.div (by fun_prop) fun u hu =>
      (sin_pos_of_pos_of_lt_pi (by linarith [hu.2]) (by linarith [hu.1])).ne'
  have hk4L : ContinuousOn (fun u => 1 / sin u) (Icc (π / 2) (π / 2 + t)) :=
    continuousOn_const.div continuous_sin.continuousOn
      fun u hu => hs4 u ⟨hu.1, hu.2.trans hvtT⟩
  have hk4R : ContinuousOn (tailKernel (1 / cos φ)) (Icc (π / 2 + t) (π - φ)) :=
    (continuousOn_const.add continuous_cos.continuousOn).div continuous_sin.continuousOn
      fun u hu => hs4 u ⟨hvt.trans hu.1, hu.2⟩
  have c2 : SquareControl (∫ u in t..(π / 2 - φ), cornerResidual f df u) (π / 2 - φ - t)
      (arcSquare t (π / 2 - φ) (cornerResidual f df)) := by
    simpa using integral_square_control ht.2 (k := fun _ => 1) continuousOn_const
      (intervalIntegrable_subinterval h.middle ht.1 ht.2 le_rfl)
      (intervalIntegrable_subinterval h.middle_sq ht.1 ht.2 le_rfl)
  have c3 := integral_square_control (by linarith) hk3 h.third h.third_sq
  have c4L := (integral_square_control hvt hk4L
    (intervalIntegrable_subinterval h.last le_rfl hvt (by linarith))
    (intervalIntegrable_subinterval h.last_sq le_rfl hvt (by linarith))).smul (1 / cos φ - sin t)
  have c4R := integral_square_control hvtT hk4R
    (intervalIntegrable_subinterval h.last hvt hvtT (by linarith))
    (intervalIntegrable_subinterval h.last_sq hvt hvtT (by linarith))
  have hsplit : arcSquare (π / 2) (π / 2 + t) (tangentResidual π f df) +
      arcSquare (π / 2 + t) (π - φ) (tangentResidual π f df) =
      arcSquare (π / 2) (π - φ) (tangentResidual π f df) :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_subinterval h.last_sq le_rfl hvt (by linarith))
      (intervalIntegrable_subinterval h.last_sq hvt hvtT (by linarith))
  have he := ((c2.add c3).add c4L).add c4R
  rw [← sharp_middle_formula hφ h ht, middle_evaluation_norm hφ ht] at he
  exact he.mono_energy (by
    linarith [arcSquare_mono h.middle_sq ht.1 ht.2 le_rfl,
      arcSquare_mono h.last_sq le_rfl (hvt.trans hvtT) (by linarith)])

include hφ h in
/-- The control of `f(t)` on the first arc. -/
theorem sharp_first_control {t : ℝ} (ht : t ∈ Icc 0 φ) :
    SquareControl (f t) (cos t ^ 2 * (2 * (1 / cos φ) ^ 2 - tan t))
      (2 * fourResidualEnergy φ f df) := by
  have hmid := (sharp_middle_control hφ h (t := φ)
    ⟨le_rfl, by linarith [hφ.2, pi_pos]⟩).smul (1 / cos φ)
  have hk : ContinuousOn (fun u => 1 / cos u) (Icc t φ) :=
    continuousOn_const.div continuous_cos.continuousOn fun u hu =>
      (cos_pos_of_mem_Ioo ⟨by linarith [hu.1, ht.1, pi_pos], by linarith [hu.2, hφ.2, pi_pos]⟩).ne'
  have hI := integral_square_control ht.2 hk
    (intervalIntegrable_subinterval h.first ht.1 ht.2 le_rfl)
    (intervalIntegrable_subinterval h.first_sq ht.1 ht.2 le_rfl)
  have he := (hmid.add hI).smul (cos t)
  rw [← sharp_first_formula hφ h ht, first_evaluation_norm hφ ht] at he
  exact he.mono_energy (by
    unfold fourResidualEnergy
    linarith [arcSquare_mono h.first_sq ht.1 ht.2 le_rfl])

include hφ h in
/-- The control of `f(t)` at every `t ∈ [0, π]`, by the closed-form kernel norm. -/
theorem sharp_green_control {t : ℝ} (ht : t ∈ Icc 0 π) :
    SquareControl (f t) (greenNormSquared φ t) (2 * fourResidualEnergy φ f df) := by
  have hpi := pi_pos
  have e1 := arcSquare_nonneg hφ.1.le (tangentResidual (π / 2) f df)
  have e2 := arcSquare_nonneg (by linarith [hφ.2] : φ ≤ π / 2 - φ) (cornerResidual f df)
  have e3 := arcSquare_nonneg (by linarith [hφ.1] : π / 2 - φ ≤ π / 2)
    (tangentResidual (π - φ) f df)
  have e4 := arcSquare_nonneg (by linarith : π / 2 ≤ π) (tangentResidual π f df)
  have hE : 2 * fourResidualEnergy φ f df =
      arcSquare 0 φ (tangentResidual (π / 2) f df) +
        arcSquare φ (π / 2 - φ) (cornerResidual f df) +
        arcSquare (π / 2 - φ) (π / 2) (tangentResidual (π - φ) f df) +
        arcSquare (π / 2) π (tangentResidual π f df) := by
    unfold fourResidualEnergy
    ring
  unfold greenNormSquared
  split_ifs with h1 h2 h3
  · exact sharp_first_control hφ h ⟨ht.1, h1⟩
  · exact (sharp_middle_control hφ h ⟨(not_le.mp h1).le, h2⟩).mono_energy (by linarith)
  · exact (sharp_third_control hφ h ⟨(not_le.mp h2).le, h3⟩).mono_energy (by linarith)
  · exact (sharp_last_control h ⟨(not_le.mp h3).le, ht.2⟩).mono_energy (by linarith)

include hφ h in
/-- **The four-arc estimate.** `|f(t)| ≤ 2 sec φ √E` on `[0, π]`, where `E` is the residual
energy. -/
theorem sharp_four_arc_coercivity {t : ℝ} (ht : t ∈ Icc 0 π) :
    |f t| ≤ (2 / cos φ) * sqrt (fourResidualEnergy φ f df) := by
  have hc := (sharp_green_control hφ h ht).mono_kernel (greenNormSquared_le hφ ht)
  exact abs_le_mul_sqrt_of_sq_le (div_nonneg zero_le_two (cap_angle_parameters hφ).1.le)
    (hc.bound.trans_eq (by ring))

end FourArcs

/-!
## From support bounds to Euclidean distances

The parallel body `K + rB` of a convex body `K` has support function `h_K + r`, so a bound on the
difference of the support functions of two convex bodies gives, for every point of each, a point of
the other within Euclidean distance `r`.
-/

/-- The Euclidean norm is continuous. -/
theorem continuous_norm2 : Continuous (norm2 : Point → ℝ) := by
  unfold norm2 dot
  fun_prop

/-- The Euclidean norm is absolutely homogeneous. -/
theorem norm2_smul (a : ℝ) (p : Point) : norm2 (a • p) = |a| * norm2 p := by
  rw [norm2, norm2, dot_smul_left, dot_smul_right, ← mul_assoc, ← sq, sqrt_mul (sq_nonneg a),
    sqrt_sq_eq_abs]

/-- The first coordinate is at most the Euclidean norm. -/
theorem abs_fst_le_norm2 (p : Point) : |p.1| ≤ norm2 p :=
  abs_le_sqrt (by rw [dot, sq]; exact le_add_of_nonneg_right (mul_self_nonneg _))

/-- The second coordinate is at most the Euclidean norm. -/
theorem abs_snd_le_norm2 (p : Point) : |p.2| ≤ norm2 p :=
  abs_le_sqrt (by rw [dot, sq]; exact le_add_of_nonneg_left (mul_self_nonneg _))

/-- The product (sup) norm is at most the Euclidean norm. -/
theorem product_norm_le_norm2 (p : Point) : ‖p‖ ≤ norm2 p := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (abs_fst_le_norm2 p) (abs_snd_le_norm2 p)

/-- The Euclidean norm is at most twice the product (sup) norm. -/
theorem norm2_le_two_product_norm (p : Point) : norm2 p ≤ 2 * ‖p‖ := by
  have h₁ := pow_le_pow_left₀ (norm_nonneg _) (norm_fst_le p) 2
  have h₂ := pow_le_pow_left₀ (norm_nonneg _) (norm_snd_le p) 2
  rw [Real.norm_eq_abs, sq_abs] at h₁ h₂
  rw [norm2, sqrt_le_left (by positivity), dot]
  nlinarith

/-- The closed Euclidean disk of radius `r` about the origin. -/
def euclideanDisk (r : ℝ) : Set Point := {p | norm2 p ≤ r}

/-- A closed Euclidean disk of nonnegative radius is a convex body. -/
theorem euclideanDisk_isConvexBody {r : ℝ} (hr : 0 ≤ r) : IsConvexBody (euclideanDisk r) := by
  refine ⟨⟨0, by simpa only [euclideanDisk, mem_ofPred_eq, norm2_zero] using hr⟩,
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
      (isClosed_le continuous_norm2 continuous_const) fun p hp =>
        ⟨abs_le.mp ((abs_fst_le_norm2 p).trans hp), abs_le.mp ((abs_snd_le_norm2 p).trans hp)⟩,
    fun p hp q hq a b ha hb hab => ?_⟩
  have h := norm2_add_le (a • p) (b • q)
  rw [norm2_smul, norm2_smul, abs_of_nonneg ha, abs_of_nonneg hb] at h
  change norm2 (a • p + b • q) ≤ r
  nlinarith [mul_le_mul_of_nonneg_left (show norm2 p ≤ r from hp) ha,
    mul_le_mul_of_nonneg_left (show norm2 q ≤ r from hq) hb]

/-- The Minkowski sum of two convex bodies is a convex body. -/
theorem convexBody_add {K L : Set Point} (hK : IsConvexBody K) (hL : IsConvexBody L) :
    IsConvexBody (K + L) :=
  ⟨hK.1.add hL.1, hK.2.1.add hL.2.1, hK.2.2.add hL.2.2⟩

/-- The parallel body `K + rB` has support function `h_K + r`. -/
theorem supp_add_euclideanDisk {K : Set Point} (hK : IsConvexBody K)
    {r : ℝ} (hr : 0 ≤ r) (t : ℝ) : supp (K + euclideanDisk r) t = supp K t + r := by
  obtain ⟨p, hp, hps⟩ := exists_dot_eq_supp hK.2.1 hK.1 t
  apply supp_eq_of_mem (convexBody_add hK (euclideanDisk_isConvexBody hr)).2.1
  · rintro _ ⟨q, hq, z, hz, rfl⟩
    rw [dot_add_left]
    exact add_le_add (dot_le_supp hK.2.1 hq t) ((dot_uvec_le_norm2 z t).trans hz)
  · refine ⟨p, hp, r • uvec t, ?_, rfl⟩
    change norm2 (r • uvec t) ≤ r
    rw [norm2_smul, norm2_uvec, mul_one, abs_of_nonneg hr]
  · rw [dot_add_left, hps, dot_smul_left, dot_uvec_self, mul_one]

/-- If `h_S ≤ h_T + r`, every point of the compact set `S` is within Euclidean distance `r` of a
point of the convex body `T`. -/
theorem directedClose_of_support_le {S T : Set Point} (hS : IsCompact S)
    (hT : IsConvexBody T) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ t, supp S t ≤ supp T t + r) : DirectedClose r S T := by
  intro p hp
  obtain ⟨q, hq, z, hz, rfl⟩ := (mem_iff_forall_dot_le_supp
    (convexBody_add hT (euclideanDisk_isConvexBody hr)) p).2 fun t => by
      rw [supp_add_euclideanDisk hT hr]
      exact (dot_le_supp hS hp t).trans (h t)
  refine ⟨q, hq, ?_⟩
  change norm2 (q + z - q) ≤ r
  rwa [add_sub_cancel_left]

/-- Convex bodies whose support functions differ by at most `r` are within Euclidean Hausdorff
distance `r`. -/
theorem euclideanClose_of_support_bound {K L : Set Point}
    (hK : IsConvexBody K) (hL : IsConvexBody L) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ t, |supp K t - supp L t| ≤ r) : EuclideanClose r K L :=
  ⟨directedClose_of_support_le hK.2.1 hL hr fun t => by linarith [(abs_le.mp (h t)).2],
    directedClose_of_support_le hL.2.1 hK hr fun t => by linarith [(abs_le.mp (h t)).1]⟩

/-!
## All normals, and the translated reference cap

On the lower half circle of normals a right-angle cap is supported by an endpoint of its base, so a
bound on `capDifference K₀ K₁` over `[0, π]` holds at every normal. `capDifference K₀ K₁` is the
difference of the support functions of `K₁` and of `K₀` translated horizontally so that their
leftmost points have the same abscissa.
-/

/-- On the lower-right quarter of normals a right-angle cap is supported by the right end of its
base. -/
theorem cap_lower_right_support {K : Set Point} (hK : IsCap K (π / 2)) {t : ℝ}
    (hs : sin t ≤ 0) (hc : 0 ≤ cos t) : supp K t = supp K 0 * cos t := by
  refine supp_eq_of_mem hK.2.1.2.1 (fun p hp => ?_) (opt_cap_A_mem hK) (by simp [dot, uvec])
  have hx := mul_le_mul_of_nonneg_right (opt_cap_fst_le hK hp).2 hc
  have hy := mul_nonpos_of_nonneg_of_nonpos (inj_cap_strip hK hp).1 hs
  simp only [dot, uvec]
  linarith

/-- On the lower-left quarter of normals a right-angle cap is supported by the left end of its
base. -/
theorem cap_lower_left_support {K : Set Point} (hK : IsCap K (π / 2)) {t : ℝ}
    (hs : sin t ≤ 0) (hc : cos t ≤ 0) : supp K t = -supp K π * cos t := by
  refine supp_eq_of_mem hK.2.1.2.1 (fun p hp => ?_) (opt_cap_C_mem hK) (by simp [dot, uvec])
  have hx := mul_le_mul_of_nonpos_right (opt_cap_fst_le hK hp).1 hc
  have hy := mul_nonpos_of_nonneg_of_nonpos (inj_cap_strip hK hp).1 hs
  simp only [dot, uvec]
  linarith

/-- Every unit vector with nonnegative ordinate is `uvec s` for some `s ∈ [0, π]`. -/
theorem upper_normal_representative (t : ℝ) (hs : 0 ≤ sin t) :
    ∃ s ∈ Icc (0 : ℝ) π, uvec s = uvec t ∧ cos s = cos t := by
  have hc : cos (arccos (cos t)) = cos t := cos_arccos (neg_one_le_cos t) (cos_le_one t)
  have hsn : sin (arccos (cos t)) = sin t := by rw [sin_arccos, ← sin_sq, sqrt_sq hs]
  exact ⟨arccos (cos t), ⟨arccos_nonneg _, arccos_le_pi _⟩,
    by ext <;> simp only [uvec, hc, hsn], hc⟩

/-- A bound on `|capDifference K₀ K₁|` over `[0, π]` holds at every normal. -/
theorem capDifference_bound_all {K₀ K₁ : Set Point}
    (h₀ : IsCap K₀ (π / 2)) (h₁ : IsCap K₁ (π / 2)) {R : ℝ}
    (hupper : ∀ t ∈ Icc (0 : ℝ) π, |capDifference K₀ K₁ t| ≤ R) (t : ℝ) :
    |capDifference K₀ K₁ t| ≤ R := by
  have h0 := hupper 0 ⟨le_rfl, pi_pos.le⟩
  rcases le_or_gt 0 (sin t) with hs | hs
  · obtain ⟨s, hsi, hu, hc⟩ := upper_normal_representative t hs
    have hd : capDifference K₀ K₁ s = capDifference K₀ K₁ t := by
      simp only [capDifference, pinnedDifference, supp, hu, hc]
    exact hd ▸ hupper s hsi
  rcases le_or_gt 0 (cos t) with hc | hc
  · have he : capDifference K₀ K₁ t = capDifference K₀ K₁ 0 * cos t := by
      simp only [capDifference, pinnedDifference, cap_lower_right_support h₀ hs.le hc,
        cap_lower_right_support h₁ hs.le hc, cos_zero]
      ring
    rw [he, abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one t)).trans h0
  · have he : capDifference K₀ K₁ t = 0 := by
      simp only [capDifference, pinnedDifference, cap_lower_left_support h₀ hs.le hc.le,
        cap_lower_left_support h₁ hs.le hc.le]
      ring
    rw [he, abs_zero]
    exact (abs_nonneg _).trans h0

/-- The horizontal translation that gives the reference cap `K₀` the leftmost abscissa of `K₁`. -/
def capReferenceShift (K₀ K₁ : Set Point) : Point := (-(supp K₁ π - supp K₀ π), 0)

/-- The reference cap `K₀` translated horizontally so that its leftmost abscissa is that of
`K₁`. -/
def shiftedReferenceCap (K₀ K₁ : Set Point) : Set Point :=
  (fun p => p + capReferenceShift K₀ K₁) '' K₀

/-- `capDifference K₀ K₁` is the difference of the support functions of `K₁` and of the translated
reference cap. -/
theorem capDifference_eq_shifted_support {K₀ K₁ : Set Point}
    (h₀ : IsConvexBody K₀) (t : ℝ) :
    capDifference K₀ K₁ t = supp K₁ t - supp (shiftedReferenceCap K₀ K₁) t := by
  rw [shiftedReferenceCap, supp_translate K₀ _ t h₀.2.1 h₀.1]
  simp only [capDifference, pinnedDifference, capReferenceShift, dot, uvec]
  ring

/-- A bound on `|capDifference K₀ K₁|` over `[0, π]` bounds the Euclidean Hausdorff distance from
`K₁` to the translated reference cap. -/
theorem cap_euclideanClose_of_upper_support {K₀ K₁ : Set Point}
    (h₀ : IsCap K₀ (π / 2)) (h₁ : IsCap K₁ (π / 2)) {R : ℝ}
    (hupper : ∀ t ∈ Icc (0 : ℝ) π, |capDifference K₀ K₁ t| ≤ R) :
    EuclideanClose R K₁ (shiftedReferenceCap K₀ K₁) :=
  euclideanClose_of_support_bound (L := shiftedReferenceCap K₀ K₁) h₁.2.1
    (nef_isConvexBody_translate h₀.2.1 (capReferenceShift K₀ K₁))
    ((abs_nonneg _).trans (hupper 0 ⟨le_rfl, pi_pos.le⟩)) fun t => by
      rw [← capDifference_eq_shifted_support h₀.2.1 t]
      exact capDifference_bound_all h₀ h₁ hupper t

/-- With equal leftmost abscissas, the translated reference cap is the reference cap. -/
theorem shiftedReferenceCap_eq_of_left_support {K₀ K₁ : Set Point}
    (h : supp K₁ π = supp K₀ π) : shiftedReferenceCap K₀ K₁ = K₀ := by
  simp [shiftedReferenceCap, capReferenceShift, h, Prod.mk_zero_zero]

/-!
## The cap distance bounds

The cap energy is at most the deficit of `𝒬` on the enlarged domain of triples, and, for a cap of
Baek's class `Kᵢ`, at most its sofa-area deficit.
-/

/-- For two right-angle caps, `|capDifference K₀ K₁|` is at most `2 sec φ` times the square root of
the cap energy on `[0, π]`. -/
theorem sharp_capDifference_le_energy {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (K₀ K₁ : ConvexBodySet) (h₀ : IsCap K₀.1 (π / 2)) (h₁ : IsCap K₁.1 (π / 2))
    {t : ℝ} (ht : t ∈ Icc 0 π) :
    |capDifference K₀.1 K₁.1 t| ≤ (2 / cos φ) * sqrt (capResidualEnergy φ K₀ K₁) := by
  obtain ⟨hd, he⟩ := capDifference_data hφ K₀ K₁ h₀ h₁
  rw [← he]
  exact sharp_four_arc_coercivity hφ hd ht

/-- The support bound for the cap of a triple of the enlarged domain, by the deficit of `𝒬`. -/
theorem sharp_wide_cap_support_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) {t : ℝ} (ht : t ∈ Icc 0 π) :
    |capDifference P.cap x.1.1.1 t| ≤
      (2 / cos P.φ) * sqrt (area (gerverSofa P) - wideUpperQ P.φ x) := by
  have hφ := GerverParams.gm_φ_mem_Ioo hP hbox
  have hc := (cap_angle_parameters hφ).1
  refine (sharp_capDifference_le_energy hφ (wideGerverTriple hP hbox).1.1 x.1.1
    (wideGerverTriple hP hbox).2.1 x.2.1 ht).trans ?_
  gcongr
  exact wide_capResidualEnergy_le_deficit hP hbox x

/-- The support bound for a cap of Baek's class `Kᵢ`, by the sofa-area deficit. -/
theorem sharp_ki_cap_support_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hK : IsKi K) {t : ℝ} (ht : t ∈ Icc 0 π) :
    |capDifference P.cap K t| ≤
      (2 / cos P.φ) * sqrt (area (gerverSofa P) - sofaArea (π / 2) K) := by
  have hc := (cap_angle_parameters (GerverParams.gm_φ_mem_Ioo hP hbox)).1
  refine (sharp_wide_cap_support_bound hP hbox
    (toWideTriple (kiExtensionTriple hbox.1 hK)) ht).trans ?_
  gcongr
  exact theorem8_2_4 hbox.1 hK

/-- **The cap estimate on the enlarged domain.** The cap of a triple `x` lies within Euclidean
Hausdorff distance `(2 / cos φ) √(|G| - 𝒬(x))` of Gerver's cap translated horizontally. -/
theorem sharp_wide_cap_distance_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    EuclideanClose ((2 / cos P.φ) * sqrt (area (gerverSofa P) - wideUpperQ P.φ x))
      x.1.1.1 (shiftedReferenceCap P.cap x.1.1.1) :=
  cap_euclideanClose_of_upper_support (wideGerverTriple hP hbox).2.1 x.2.1
    fun _ ht => sharp_wide_cap_support_bound hP hbox x ht

/-- **The cap estimate for Baek's class `Kᵢ`.** A cap `K` of `Kᵢ` lies within Euclidean Hausdorff
distance `(2 / cos φ) √(|G| - A)` of Gerver's cap translated horizontally, where
`A = sofaArea (π / 2) K` is the area of the sofa of `K`. -/
theorem sharp_ki_cap_distance_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hK : IsKi K) :
    EuclideanClose ((2 / cos P.φ) * sqrt (area (gerverSofa P) - sofaArea (π / 2) K))
      K (shiftedReferenceCap P.cap K) :=
  cap_euclideanClose_of_upper_support (wideGerverTriple hP hbox).2.1 hK.1
    fun _ ht => sharp_ki_cap_support_bound hP hbox hK ht

/-- For `φ ∈ [0.039, 0.04]`, `2 / cos φ ≤ 2500 / 1249 < 1001 / 500`. -/
theorem cap_constant_lt_2002 {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) :
    2 / cos φ ≤ 2500 / 1249 ∧ 2 / cos φ < 1001 / 500 := by
  have hc : (1249 / 1250 : ℝ) ≤ cos φ := by
    nlinarith [one_sub_sq_div_two_le_cos (x := φ), hφ.1, hφ.2]
  have hbound : 2 / cos φ ≤ 2500 / 1249 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  exact ⟨hbound, hbound.trans_lt (by norm_num)⟩

/-- The cap estimate on the enlarged domain with the rational coefficient `1001 / 500`. -/
theorem wide_cap_distance_bound_2002 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    EuclideanClose ((1001 / 500) * sqrt (area (gerverSofa P) - wideUpperQ P.φ x))
      x.1.1.1 (shiftedReferenceCap P.cap x.1.1.1) :=
  (sharp_wide_cap_distance_bound hP hbox x).mono
    (mul_le_mul_of_nonneg_right (cap_constant_lt_2002 hbox.1).2.le (sqrt_nonneg _))

/-- The cap estimate for Baek's class `Kᵢ` with the rational coefficient `1001 / 500`. -/
theorem ki_cap_distance_bound_2002 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hK : IsKi K) :
    EuclideanClose ((1001 / 500) * sqrt (area (gerverSofa P) - sofaArea (π / 2) K))
      K (shiftedReferenceCap P.cap K) :=
  (sharp_ki_cap_distance_bound hP hbox hK).mono
    (mul_le_mul_of_nonneg_right (cap_constant_lt_2002 hbox.1).2.le (sqrt_nonneg _))

/-!
## The coercive certificate

One estimate for Baek's upper bound `𝒬` on the enlarged domain of triples carries optimality,
uniqueness and stability: `𝒬(x) ≤ |G|` (`wideUpperQ_le_gerver`, from the concavity of `𝒬` and its
first variation at Gerver's triple), together with the cap estimate
`sharp_wide_cap_distance_bound`. The first part bounds the value of a maximizing right-angle cap,
which gives optimality (`MovingSofaExtremal.gerver_sofa_optimal`). At zero deficit the second part
says that such a cap is a translate of Gerver's cap, which gives uniqueness
(`MovingSofaExtremal.image_eq_gerver_of_volume_eq`). At small deficit both parts give the local
estimate of the stability theorem (`nearby_cap_distance`, `unrestricted_stability`).
-/

/-- **The coercive certificate.** For every triple `x` of the enlarged domain, Baek's upper bound
satisfies `𝒬(x) ≤ |G|`, and the cap of `x` lies within Euclidean Hausdorff distance
`(2 / cos φ) √(|G| - 𝒬(x))` of Gerver's cap translated horizontally. -/
theorem coercive_certificate {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    wideUpperQ P.φ x ≤ area (gerverSofa P) ∧
      EuclideanClose ((2 / cos P.φ) * sqrt (area (gerverSofa P) - wideUpperQ P.φ x))
        x.1.1.1 (shiftedReferenceCap P.cap x.1.1.1) :=
  ⟨(wideUpperQ_le_gerver hP hbox x).trans_eq (wideGerver_value hP hbox),
    sharp_wide_cap_distance_bound hP hbox x⟩

end MovingSofaStability
