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
  sorry

/-- Propagation on an arc whose sine denominator is at least one half. -/
theorem tangent_regular_arc_bound {f df : ℝ → ℝ} {a b T : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hs : ∀ t ∈ Icc a b, (1 / 2 : ℝ) ≤ sin (T - t))
    (hr : IntervalIntegrable (tangentResidual T f df) volume a b) :
    |f a| ≤ 2 * |f b| + 3 * |f T| + 2 * arcMass a b (tangentResidual T f df) := by
  sorry

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
  sorry

end MovingSofaStability
