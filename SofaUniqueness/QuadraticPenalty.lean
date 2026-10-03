module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact variation of the centered quadratic penalty

The fixed selector from `FixedPenaltySelection` has derivative
`2 * integral (h_K-h_target) H` along a support perturbation H. The error is
therefore small because the selected supports converge to the target, not
because an independently chosen penalty coefficient tends to zero.

For a floating sine hat with integral of its absolute value at most C*delta,
the bound here is 2*C*eta*delta, where eta bounds the support difference.
For a pinned perturbation with a uniform bound on that integral it is O(eta).
The square-integrability hypotheses are explicit throughout.

Uncompiled source; no admissions or decision tactics.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter

namespace SofaUniqueness

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) {d H : X → ℝ}

/-- The exact quadratic polynomial for a support perturbation. -/
theorem quadraticPenalty_line (ε : ℝ)
    (hd : Integrable (fun x => d x ^ 2) μ)
    (hH : Integrable (fun x => H x ^ 2) μ)
    (hdH : Integrable (fun x => d x * H x) μ) :
    (∫ x, (d x + ε * H x) ^ 2 ∂μ) =
      (∫ x, d x ^ 2 ∂μ) + 2 * ε * (∫ x, d x * H x ∂μ) +
        ε ^ 2 * (∫ x, H x ^ 2 ∂μ) := by
  calc
    (∫ x, (d x + ε * H x) ^ 2 ∂μ) =
        ∫ x, d x ^ 2 + (2 * ε) * (d x * H x) + ε ^ 2 * H x ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = _ := by
      rw [integral_add (hd.add (hdH.const_mul (2 * ε))) (hH.const_mul (ε ^ 2)),
        integral_add hd (hdH.const_mul (2 * ε))]
      simp only [integral_const_mul]

/-- In particular, there is no unspecified remainder in the penalty variation. -/
theorem quadraticPenalty_hasDerivAt_zero
    (hd : Integrable (fun x => d x ^ 2) μ)
    (hH : Integrable (fun x => H x ^ 2) μ)
    (hdH : Integrable (fun x => d x * H x) μ) :
    HasDerivAt (fun ε : ℝ => ∫ x, (d x + ε * H x) ^ 2 ∂μ)
      (2 * ∫ x, d x * H x ∂μ) 0 := by
  have heq : (fun ε : ℝ => ∫ x, (d x + ε * H x) ^ 2 ∂μ) =
      (fun ε => (∫ x, d x ^ 2 ∂μ) + 2 * ε * (∫ x, d x * H x ∂μ) +
        ε ^ 2 * (∫ x, H x ^ 2 ∂μ)) :=
    funext fun ε => quadraticPenalty_line μ ε hd hH hdH
  rw [heq]
  have hc := hasDerivAt_const (0 : ℝ) (∫ x, d x ^ 2 ∂μ)
  have hl : HasDerivAt (fun ε : ℝ => 2 * ε * (∫ x, d x * H x ∂μ))
      (2 * ∫ x, d x * H x ∂μ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const
      (∫ x, d x * H x ∂μ)
  have hq : HasDerivAt (fun ε : ℝ => ε ^ 2 * (∫ x, H x ^ 2 ∂μ)) 0 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (∫ x, H x ^ 2 ∂μ)
  simpa using (hc.add hl).add hq

/-- Uniform support closeness controls the first variation by the L1 size
of the perturbation. This also applies to the asymmetric extreme sine hats. -/
theorem quadraticPenalty_derivative_bound {η : ℝ} (hη : 0 ≤ η)
    (hclose : ∀ᵐ x ∂μ, |d x| ≤ η)
    (hH : Integrable H μ) (hdH : Integrable (fun x => d x * H x) μ) :
    |2 * ∫ x, d x * H x ∂μ| ≤ 2 * η * (∫ x, |H x| ∂μ) := by
  have habs : |∫ x, d x * H x ∂μ| ≤ ∫ x, |d x * H x| ∂μ := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (fun x => d x * H x))
  have hmono : (∫ x, |d x * H x| ∂μ) ≤ η * (∫ x, |H x| ∂μ) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hdH.abs (hH.abs.const_mul η)
    filter_upwards [hclose] with x hx
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg (H x))
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith

/-- The local coefficient used for a floating facet. -/
theorem quadraticPenalty_facet_bound {η C δ : ℝ}
    (hη : 0 ≤ η) (hclose : ∀ᵐ x ∂μ, |d x| ≤ η)
    (hH : Integrable H μ) (hdH : Integrable (fun x => d x * H x) μ)
    (hhat : (∫ x, |H x| ∂μ) ≤ C * δ) :
    |2 * ∫ x, d x * H x ∂μ| ≤ 2 * C * η * δ := by
  have h := quadraticPenalty_derivative_bound μ hη hclose hH hdH
  have hmul := mul_le_mul_of_nonneg_left hhat (show 0 ≤ 2 * η by positivity)
  calc
    |2 * ∫ x, d x * H x ∂μ| ≤ 2 * η * (∫ x, |H x| ∂μ) := h
    _ ≤ 2 * η * (C * δ) := hmul
    _ = 2 * C * η * δ := by ring

/-- Summing mesh-local errors keeps the support-distance factor eta.
In particular no inverse mesh size survives. -/
theorem quadraticPenalty_total_error (n : ℕ) (η C δ L : ℝ)
    (hmesh : (n : ℝ) * δ = L) :
    (n : ℝ) * (2 * C * η * δ) = 2 * C * η * L := by
  rw [← hmesh]
  ring

end SofaUniqueness
