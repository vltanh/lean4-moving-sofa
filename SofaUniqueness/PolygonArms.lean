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
  have hKc : IsConvexBody K := hKp.1.2.1
  have hδ := inj_stepSize_pos k
  have hn := inj_two_pow_mul_stepSize k
  obtain ⟨hc, hs, _, _, _⟩ := inj_step_trig k
  obtain ⟨m, hm, htm⟩ := inj_grid_of_mem ht
  obtain ⟨hAK, hA1, hA2, hA3⟩ := inj_polygon_consecutive hKp (m := m) (by omega) htm
  obtain ⟨hCK, hC1, hC2, hC3⟩ := inj_polygon_consecutive hKp
    (m := 2 ^ (k + 1) + m) (by omega) (a := t + π / 2)
    (by rw [htm, ← hn]; push_cast; ring)
  have hsinne : sin (t + stepSize k - t) ≠ 0 := by
    rw [add_sub_cancel_left]
    exact hs.ne'
  have hsinne' : sin (t + π / 2 + stepSize k - (t + π / 2)) ≠ 0 := by
    rw [add_sub_cancel_left]
    exact hs.ne'
  set A := vint K t (t + stepSize k) with hAdef
  set C := vint K (t + π / 2) (t + π / 2 + stepSize k) with hCdef
  have hsuppA : ∀ s ∈ Icc t (t + stepSize k), supp K s = dot A (uvec s) := by
    intro s hs'
    rcases eq_or_lt_of_le hs'.1 with rfl | h1
    · exact (vint_mem_line_left K _ _).symm
    rcases eq_or_lt_of_le hs'.2 with rfl | h2
    · exact (vint_mem_line_right K hsinne).symm
    · exact (hA3 s ⟨h1, h2⟩).1
  have hsuppC : ∀ s ∈ Icc t (t + stepSize k),
      supp K (s + π / 2) = dot C (uvec (s + π / 2)) := by
    intro s hs'
    rcases eq_or_lt_of_le hs'.1 with rfl | h1
    · exact (vint_mem_line_left K _ _).symm
    rcases eq_or_lt_of_le hs'.2 with rfl | h2
    · rw [show t + stepSize k + π / 2 = t + π / 2 + stepSize k by ring]
      exact (vint_mem_line_right K hsinne').symm
    · exact (hC3 (s + π / 2) ⟨by linarith, by linarith⟩).1
  set G : ℝ → ℝ := fun s => dot (A - C) (uvec s) with hG
  have hgt : gPlus K t = G t := by
    rw [gPlus, dot_sub_left, inj_dot_outerCorner_uvec, cPlus, hC1,
      hsuppA t ⟨le_rfl, by linarith⟩]
    exact (dot_sub_left _ _ _).symm
  have hgtd : gMinus K (t + stepSize k) = G (t + stepSize k) := by
    rw [gMinus, dot_sub_left, inj_dot_outerCorner_uvec, cMinus,
      show t + stepSize k + π / 2 = t + π / 2 + stepSize k by ring, hC2,
      hsuppA (t + stepSize k) ⟨by linarith, le_rfl⟩]
    exact (dot_sub_left _ _ _).symm
  have hgs : ∀ s ∈ Ioo t (t + stepSize k), gPlus K s = G s ∧ gMinus K s = G s := by
    intro s hs'
    have hC := hC3 (s + π / 2) ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
    constructor
    · rw [gPlus, dot_sub_left, inj_dot_outerCorner_uvec, cPlus, hC.2.1,
        hsuppA s ⟨hs'.1.le, hs'.2.le⟩]
      exact (dot_sub_left _ _ _).symm
    · rw [gMinus, dot_sub_left, inj_dot_outerCorner_uvec, cMinus, hC.2.2,
        hsuppA s ⟨hs'.1.le, hs'.2.le⟩]
      exact (dot_sub_left _ _ _).symm
  have hGd : ∀ s, HasDerivAt G (dot (A - C) (vvec s)) s :=
    fun s => inj_hasDerivAt_dot_uvec (A - C) s
  have hGneg : ∀ s ∈ Icc t (t + stepSize k), dot (A - C) (vvec s) ≤ 0 := by
    intro s hs'
    rw [dot_sub_left, ← uvec_add_pi_div_two, ← hsuppC s hs']
    linarith [dot_le_supp hKc.2.1 hAK (s + π / 2)]
  have hGD : ∀ s, -D ≤ dot (A - C) (vvec s) :=
    fun s => neg_bound_le_dot_vvec hD (hdiam A hAK C hCK) s
  have hGc : Continuous G := by
    simp only [hG, dot, uvec]
    fun_prop
  have hanti : AntitoneOn G (Icc t (t + stepSize k)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hGc.continuousOn
      (fun s _ => (hGd s).differentiableAt.differentiableWithinAt)
    intro s hs'
    rw [interior_Icc] at hs'
    rw [(hGd s).deriv]
    exact hGneg s ⟨hs'.1.le, hs'.2.le⟩
  have hmono : MonotoneOn (fun s => G s + D * s) (Icc t (t + stepSize k)) := by
    have hd : ∀ s, HasDerivAt (fun s => G s + D * s)
        (dot (A - C) (vvec s) + D) s := by
      intro s
      have h := (hGd s).add ((hasDerivAt_id' s).const_mul D)
      rw [mul_one] at h
      exact h
    apply monotoneOn_of_deriv_nonneg (f := fun s => G s + D * s)
      (convex_Icc _ _) (hGc.add (continuous_const.mul continuous_id)).continuousOn
      (fun s _ => (hd s).differentiableAt.differentiableWithinAt)
    intro s _
    rw [(hd s).deriv]
    linarith [hGD s]
  have htI : t ∈ Icc t (t + stepSize k) := ⟨le_rfl, by linarith⟩
  have htdI : t + stepSize k ∈ Icc t (t + stepSize k) := ⟨by linarith, le_rfl⟩
  refine ⟨fun t' ht' => ?_, ?_⟩
  · have ht'I : t' ∈ Icc t (t + stepSize k) := ⟨ht'.1.le, ht'.2.le⟩
    obtain ⟨hp, hm'⟩ := hgs t' ht'
    refine ⟨?_, by rw [hp, hm'], ?_⟩
    · rw [hp, hgt]
      exact hanti htI ht'I ht'.1.le
    · rw [hm', hgtd]
      exact hanti ht'I htdI ht'.2.le
  · rw [hgt, hgtd]
    have h := hmono htI htdI (by linarith)
    linarith

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
