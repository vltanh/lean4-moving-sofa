module

public import MovingSofaStability.TrigKernelIntegrals

/-!
# Exact four-arc reconstruction

Uncompiled proof source. The middle interval is coupled to the last interval.
A product derivative combines these contributions before estimating them. This
avoids both Fubini and the loss from estimating the two occurrences of f(T)
separately.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory

namespace MovingSofaStability

section Reconstruction

variable {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
variable {f df : ℝ → ℝ} (h : FourResidualData φ f df)

theorem sharp_last_formula {t : ℝ} (ht : t ∈ Ico (π / 2) π) :
    f t = -sin t * (∫ u in (π / 2)..t, (1 / sin u) * tangentResidual π f df u) := by
  sorry

theorem sharp_third_formula {t : ℝ} (ht : t ∈ Icc (π / 2 - φ) (π / 2)) :
    f t = -(cos t / cos φ) * f (π - φ) + sin (π - φ - t) *
      (∫ u in t..(π / 2), (1 / sin (π - φ - u)) * tangentResidual (π - φ) f df u) := by
  sorry

theorem sharp_first_formula {t : ℝ} (ht : t ∈ Icc 0 φ) :
    f t = cos t * ((1 / cos φ) * f φ +
      ∫ u in t..φ, (1 / cos u) * tangentResidual (π / 2) f df u) := by
  sorry

/-- Product integration replaces a double integral. The reference endpoint
f(pi) is zero, so its tangent residual is cot(u)*f(u)-f'(u). -/
theorem tail_product_integral (A : ℝ) {a b : ℝ}
    (ha : π / 2 ≤ a) (hab : a ≤ b) (hb : b < π) :
    (∫ u in a..b, f u) = tailKernel A a * f a - tailKernel A b * f b -
      ∫ u in a..b, tailKernel A u * tangentResidual π f df u := by
  sorry

/-- The common r4 kernel is combined before taking any norm. -/
theorem sharp_middle_formula {t : ℝ} (ht : t ∈ Icc φ (π / 2 - φ)) :
    f t = (∫ u in t..(π / 2 - φ), cornerResidual f df u) +
      (∫ u in (π / 2 - φ)..(π / 2), (1 / sin (π - φ - u)) * tangentResidual (π - φ) f df u) +
      (1 / cos φ - sin t) * (∫ u in (π / 2)..(π / 2 + t), (1 / sin u) * tangentResidual π f df u) +
      (∫ u in (π / 2 + t)..(π - φ), tailKernel (1 / cos φ) u * tangentResidual π f df u) := by
  sorry

end Reconstruction
end MovingSofaStability
