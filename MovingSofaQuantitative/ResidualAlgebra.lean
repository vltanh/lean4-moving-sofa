module

public import MovingSofaQuantitative.PiecewiseCalculus

/-!
# Linear combinations and polarization of the actual residuals

Uncompiled proof source. The bilinear form is the sum of the four actual arc
integrals. It is not a separately supplied quadratic model. Square-integrable
residuals have integrable products by the pointwise Young inequality.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter
open MovingSofaStability

namespace MovingSofaQuantitative

@[simp] theorem tangentResidual_sub_smul (T a : ℝ) (f df g dg : ℝ → ℝ) (t : ℝ) :
    tangentResidual T (fun u => f u - a * g u) (fun u => df u - a * dg u) t =
      tangentResidual T f df t - a * tangentResidual T g dg t := by
  unfold tangentResidual
  ring

@[simp] theorem cornerResidual_sub_smul (a : ℝ) (f df g dg : ℝ → ℝ) (t : ℝ) :
    cornerResidual (fun u => f u - a * g u) (fun u => df u - a * dg u) t =
      cornerResidual f df t - a * cornerResidual g dg t := by
  unfold cornerResidual
  ring

/-- Young's inequality supplies product integrability from two L2 functions. -/
theorem integrable_product_of_squares {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f g : X → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hg2 : Integrable (fun x => g x ^ 2) μ) :
    Integrable (fun x => f x * g x) μ := by
  apply ((hf2.add hg2).div_const 2).mono' (hf.mul hg)
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x)]

theorem intervalIntegrable_product_of_squares {a b : ℝ} (hab : a ≤ b)
    {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hf2 : IntervalIntegrable (fun t => f t ^ 2) volume a b)
    (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume a b) :
    IntervalIntegrable (fun t => f t * g t) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab] at hf hg hf2 hg2 ⊢
  exact integrable_product_of_squares hf.aestronglyMeasurable hg.aestronglyMeasurable hf2 hg2

/-- Closure under a linear combination, including its squared integrability. -/
theorem intervalIntegrable_sub_smul_sq {a b : ℝ} (hab : a ≤ b)
    {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hf2 : IntervalIntegrable (fun t => f t ^ 2) volume a b)
    (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume a b) (c : ℝ) :
    IntervalIntegrable (fun t => f t - c * g t) volume a b ∧
      IntervalIntegrable (fun t => (f t - c * g t) ^ 2) volume a b := by
  have hfg := intervalIntegrable_product_of_squares hab hf hg hf2 hg2
  refine ⟨hf.sub (hg.const_mul c), ?_⟩
  have hh := (hf2.sub (hfg.const_mul (2 * c))).add (hg2.const_mul (c ^ 2))
  have he : (fun t => f t ^ 2 - (2 * c) * (f t * g t) + c ^ 2 * g t ^ 2) =
      (fun t => (f t - c * g t) ^ 2) := funext fun _ => by ring
  rwa [he] at hh

/-- Exact polarization on one arc, with every integral justified. -/
theorem arcSquare_sub_smul {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (hf2 : IntervalIntegrable (fun t => f t ^ 2) volume a b)
    (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume a b) (c : ℝ) :
    arcSquare a b (fun t => f t - c * g t) =
      arcSquare a b f - 2 * c * (∫ t in a..b, f t * g t) + c ^ 2 * arcSquare a b g := by
  have hfg := intervalIntegrable_product_of_squares hab hf hg hf2 hg2
  unfold arcSquare
  calc
    _ = ∫ t in a..b, f t ^ 2 - (2 * c) * (f t * g t) + c ^ 2 * g t ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hf2.sub (hfg.const_mul _)) (hg2.const_mul _),
        intervalIntegral.integral_sub hf2 (hfg.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- The unhalved residual pairing: on the diagonal this is twice the energy. -/
def residualPair (φ : ℝ) (f df g dg : ℝ → ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..φ, tangentResidual (π / 2) f df t * tangentResidual (π / 2) g dg t) +
  (∫ t in φ..(π / 2 - φ), cornerResidual f df t * cornerResidual g dg t) +
  (∫ t in (π / 2 - φ)..(π / 2), tangentResidual (π - φ) f df t * tangentResidual (π - φ) g dg t) +
  (∫ t in (π / 2)..π, tangentResidual π f df t * tangentResidual π g dg t)

theorem residualPair_self (φ : ℝ) (f df : ℝ → ℝ) :
    residualPair φ f df f df = 2 * fourResidualEnergy φ f df := by
  simp only [residualPair, fourResidualEnergy, arcSquare, pow_two]
  ring

theorem residualPair_comm (φ : ℝ) (f df g dg : ℝ → ℝ) :
    residualPair φ f df g dg = residualPair φ g dg f df := by
  unfold residualPair
  congr 1 <;> try congr 1 <;> try congr 1 <;>
    apply intervalIntegral.integral_congr <;> intro t _ <;> ring

/-- The actual data class is closed under subtraction of a comparison profile. -/
theorem fourResidualData_sub_smul {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {f df g dg : ℝ → ℝ} (hf : FourResidualData φ f df) (hg : FourResidualData φ g dg)
    (c : ℝ) : FourResidualData φ (fun t => f t - c * g t) (fun t => df t - c * dg t) := by
  have h1 := intervalIntegrable_sub_smul_sq hφ.1.le hf.first hg.first hf.first_sq hg.first_sq c
  have h2 := intervalIntegrable_sub_smul_sq (by linarith [hφ.2] : φ ≤ π / 2 - φ)
    hf.middle hg.middle hf.middle_sq hg.middle_sq c
  have h3 := intervalIntegrable_sub_smul_sq (by linarith [hφ.1] : π / 2 - φ ≤ π / 2)
    hf.third hg.third hf.third_sq hg.third_sq c
  have h4 := intervalIntegrable_sub_smul_sq (by linarith [pi_pos] : π / 2 ≤ π)
    hf.last hg.last hf.last_sq hg.last_sq c
  refine ⟨hf.continuous.sub (hg.continuous.const_mul c),
    (fun t ht => (hf.rightDeriv t ht).sub ((hg.rightDeriv t ht).const_mul c)),
    by simp [hf.top_zero, hg.top_zero], by simp [hf.left_zero, hg.left_zero],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [tangentResidual_sub_smul] using h1.1
  · simpa only [cornerResidual_sub_smul] using h2.1
  · simpa only [tangentResidual_sub_smul] using h3.1
  · simpa only [tangentResidual_sub_smul] using h4.1
  · simpa only [tangentResidual_sub_smul] using h1.2
  · simpa only [cornerResidual_sub_smul] using h2.2
  · simpa only [tangentResidual_sub_smul] using h3.2
  · simpa only [tangentResidual_sub_smul] using h4.2

/-- Polarization is for the exact energy used in the integrated cap theorem. -/
theorem fourResidualEnergy_sub_smul {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {f df g dg : ℝ → ℝ} (hf : FourResidualData φ f df) (hg : FourResidualData φ g dg)
    (c : ℝ) :
    fourResidualEnergy φ (fun t => f t - c * g t) (fun t => df t - c * dg t) =
      fourResidualEnergy φ f df - c * residualPair φ f df g dg +
        c ^ 2 * fourResidualEnergy φ g dg := by
  unfold fourResidualEnergy
  simp only [tangentResidual_sub_smul, cornerResidual_sub_smul]
  rw [arcSquare_sub_smul hφ.1.le hf.first hg.first hf.first_sq hg.first_sq,
    arcSquare_sub_smul (by linarith [hφ.2] : φ ≤ π / 2 - φ)
      hf.middle hg.middle hf.middle_sq hg.middle_sq,
    arcSquare_sub_smul (by linarith [hφ.1] : π / 2 - φ ≤ π / 2)
      hf.third hg.third hf.third_sq hg.third_sq,
    arcSquare_sub_smul (by linarith [pi_pos] : π / 2 ≤ π)
      hf.last hg.last hf.last_sq hg.last_sq]
  unfold residualPair
  ring

theorem fourResidualEnergy_nonneg' {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (f df : ℝ → ℝ) : 0 ≤ fourResidualEnergy φ f df := by
  unfold fourResidualEnergy
  positivity [arcSquare_nonneg hφ.1.le (tangentResidual (π / 2) f df),
    arcSquare_nonneg (by linarith [hφ.2] : φ ≤ π / 2 - φ) (cornerResidual f df),
    arcSquare_nonneg (by linarith [hφ.1] : π / 2 - φ ≤ π / 2) (tangentResidual (π - φ) f df),
    arcSquare_nonneg (by linarith [pi_pos] : π / 2 ≤ π) (tangentResidual π f df)]

end MovingSofaQuantitative
