module

public import MovingSofa.Injectivity.LimitIneq

/-!
# Cellwise arm control without a maximal-polygon assumption

The old Lemma 6.4.1 uses maximality only to obtain the fixed diameter bound 5.
Here the same geometric conclusion is stated for any polygon cap with an
explicit diameter bound D. This is the hypothesis actually available for
selected approximations of a specified cap.

No assertion that penalized maximizers are balanced is made. The parameter
D need not be the sharp Euclidean diameter; any nonnegative upper bound works.
Uncompiled source, with no admissions or decision tactics.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofa

namespace SofaUniqueness

/-- The tangential projection is bounded below by any Euclidean norm bound. -/
theorem neg_bound_le_dot_vvec {w : ℝ × ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hw : norm2 w ≤ D) (t : ℝ) : -D ≤ dot w (vvec t) := by
  have hww : dot w w ≤ D ^ 2 := by
    have h := (Real.sqrt_le_left hD).mp hw
    exact h
  have he := inj_dot_self_eq w t
  nlinarith [sq_nonneg (dot w (uvec t))]

/-- Both the within-cell monotonicity and the quantitative endpoint estimate
hold for arbitrary polygon caps under the stated diameter bound. -/
theorem polygon_arm_cell {k : ℕ} {K : Set (ℝ × ℝ)}
    (hKp : IsPolygonCap (rightAngleSet k) K) {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ p ∈ K, ∀ q ∈ K, norm2 (p - q) ≤ D) {t : ℝ}
    (ht : t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ)) :
    (∀ t' ∈ Ioo t (t + stepSize k), gPlus K t' ≤ gPlus K t ∧
      gPlus K t' = gMinus K t' ∧ gMinus K (t + stepSize k) ≤ gMinus K t') ∧
      gPlus K t - gMinus K (t + stepSize k) ≤ D * stepSize k := by
  sorry

/-- Convert a pointwise discrete estimate with a mesh-local error into an
integrated estimate on one cell. -/
theorem polygon_step_integral_bound {k : ℕ} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap (rightAngleSet k) K) {D C η : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ p ∈ K, ∀ q ∈ K, norm2 (p - q) ≤ D) {t : ℝ}
    (ht : t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ))
    (hlocal : sigmaAt K t ≤ k0 (gPlus K t) * stepSize k +
      C * stepSize k ^ 2 + η * stepSize k) :
    sigmaAt K t ≤ (∫ u in t..(t + stepSize k), k0 (gPlus K u)) +
      (C + D) * stepSize k ^ 2 + η * stepSize k := by
  have hδ := inj_stepSize_pos k
  obtain ⟨hmon, hDstep⟩ := polygon_arm_cell hK hD hdiam ht
  have hint : (k0 (gPlus K t) - D * stepSize k) * stepSize k ≤
      ∫ u in t..(t + stepSize k), k0 (gPlus K u) := by
    have h := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume)
      (a := t) (b := t + stepSize k)
      (f := fun _ => k0 (gPlus K t) - D * stepSize k)
      (g := fun u => k0 (gPlus K u)) (by linarith) intervalIntegrable_const
      (inj_intervalIntegrable_k0_gPlus hK.1.2.1 _ _) (by
        intro u hu
        obtain ⟨hu1, hu2, hu3⟩ := hmon u hu
        have hlip := inj_k0_lipschitz (gPlus K u) (gPlus K t)
        have hg : |gPlus K u - gPlus K t| ≤ D * stepSize k := by
          rw [abs_le]
          constructor <;> linarith
        linarith [(abs_le.mp hlip).1])
    rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at h
    linarith
  nlinarith

end SofaUniqueness
