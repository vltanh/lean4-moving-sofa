module

public import MovingSofaUniquenessFC.ReferenceExistence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The integral reference radius is the paper's contact-curve density

The reference uses left-hand values at its four junctions; the convenient
right derivative of the paper contact curve uses right-hand values. These
functions are proved equal almost everywhere, not incorrectly pointwise.
Integrability is proved before applying the fundamental theorem of calculus.
All scripts are uncompiled.
-/

@[expose] public section
noncomputable section

open Set Real Filter Topology MeasureTheory MovingSofaOptimality MovingSofaOptimality.GerverParams

namespace MovingSofaUniquenessFC.Reference

private theorem intervalIntegrable_ite {p : ℝ → Prop} [DecidablePred p]
    (hp : MeasurableSet {t | p t}) {f g : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun t => if p t then f t else g t) volume a b := by
  have he : (fun t => if p t then f t else g t) =
      fun t => ({t | p t} : Set ℝ).indicator f t + ({t | p t} : Set ℝ)ᶜ.indicator g t := by
    funext t
    by_cases ht : p t <;> simp [ht]
  rw [he]
  exact ⟨(hf.1.indicator hp).add (hg.1.indicator hp.compl),
    (hf.2.indicator hp).add (hg.2.indicator hp.compl)⟩

namespace Data

/-- The same piecewise radius, with right values at the four breakpoints. -/
def rightRadius (D : Data) (t : ℝ) : ℝ :=
  if t < D.φ then 1 / 2
  else if t < D.θ then (1 + D.A + t - D.φ) / 2
  else if t < π / 2 - D.θ then D.A + t - D.φ
  else if t < π / 2 - D.φ then
    D.B - (π / 2 - t - D.φ) * (1 + D.A) / 2 - (π / 2 - t - D.φ) ^ 2 / 4
  else 0

/-- This equality holds for every parameter tuple, before imposing equations. -/
theorem rightRadius_eq_phase (D : Data) (t : ℝ) :
    D.rightRadius t = (D.toPaper.gs_phase (D.toPaper.gs_ridx t)).ρC t := by
  sorry

/-- Changing finitely many assigned junction values does not change an integral. -/
theorem radius_ae_rightRadius (D : Data) : D.radius =ᵐ[volume] D.rightRadius := by
  have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ D.φ := by rw [ae_iff]; simp
  have h2 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ D.θ := by rw [ae_iff]; simp
  have h3 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ π / 2 - D.θ := by rw [ae_iff]; simp
  have h4 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ π / 2 - D.φ := by rw [ae_iff]; simp
  filter_upwards [h1, h2, h3, h4] with t ht1 ht2 ht3 ht4
  simp only [radius, rightRadius, le_iff_lt_or_eq, ht1, ht2, ht3, ht4, or_false]

/-- Each branch of a radius times a continuous weight is continuous. -/
theorem rightRadius_mul_integrable (D : Data) {w : ℝ → ℝ} (hw : Continuous w)
    (a b : ℝ) : IntervalIntegrable (fun t => D.rightRadius t * w t) volume a b := by
  simp only [rightRadius, ite_mul]
  apply intervalIntegrable_ite measurableSet_Iio
  · exact ((continuous_const.mul hw)).intervalIntegrable a b
  · apply intervalIntegrable_ite measurableSet_Iio
    · exact ((by fun_prop : Continuous fun t : ℝ => (1 + D.A + t - D.φ) / 2).mul hw).intervalIntegrable a b
    · apply intervalIntegrable_ite measurableSet_Iio
      · exact ((by fun_prop : Continuous fun t : ℝ => D.A + t - D.φ).mul hw).intervalIntegrable a b
      · apply intervalIntegrable_ite measurableSet_Iio
        · exact ((by fun_prop : Continuous fun t : ℝ =>
            D.B - (π / 2 - t - D.φ) * (1 + D.A) / 2 - (π / 2 - t - D.φ) ^ 2 / 4).mul hw).intervalIntegrable a b
        · simp

theorem radius_mul_integrable (D : Data) {w : ℝ → ℝ} (hw : Continuous w)
    (a b : ℝ) : IntervalIntegrable (fun t => D.radius t * w t) volume a b := by
  have he : (fun t => D.rightRadius t * w t) =ᵐ[volume] (fun t => D.radius t * w t) := by
    filter_upwards [D.radius_ae_rightRadius] with t ht
    rw [ht]
  exact ⟨(D.rightRadius_mul_integrable hw a b).1.congr (ae_restrict_of_ae he),
    (D.rightRadius_mul_integrable hw a b).2.congr (ae_restrict_of_ae he)⟩

theorem integral_radius_eq_rightRadius (D : Data) (w : ℝ → ℝ) (a b : ℝ) :
    (∫ t in a..b, D.radius t * w t) = ∫ t in a..b, D.rightRadius t * w t := by
  have he : (fun t => D.radius t * w t) =ᵐ[volume] (fun t => D.rightRadius t * w t) := by
    filter_upwards [D.radius_ae_rightRadius] with t ht
    rw [ht]
  unfold intervalIntegral
  congr 1 <;> apply integral_congr_ae <;> exact ae_restrict_of_ae he

/-- The contact curve's right derivative uses the reconstructed radius exactly. -/
theorem contactC_right_deriv {D : Data} (hD : D.Valid) (t : ℝ) :
    HasDerivWithinAt (contactC D.toPaper.path)
      (-D.rightRadius t • uvec t) (Ioi t) t := by
  sorry

/-- Integrate the contact curve in each coordinate. The right-derivative
version of FTC includes all phase breakpoints without differentiability there. -/
theorem contactC_integrals {D : Data} (hD : D.Valid) (a b : ℝ) :
    (∫ t in a..b, D.radius t * cos t) =
        (contactC D.toPaper.path a).1 - (contactC D.toPaper.path b).1 ∧
    (∫ t in a..b, D.radius t * sin t) =
        (contactC D.toPaper.path a).2 - (contactC D.toPaper.path b).2 := by
  sorry

end Data
end MovingSofaUniquenessFC.Reference
