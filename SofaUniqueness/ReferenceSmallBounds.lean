module

public import SofaUniqueness.ReferenceResiduals

/-!
# Uniform bounds on the analytically localized angle triangle

The only transcendental estimates are the elementary bounds for sine and
cosine and pi < 16/5. The numerator bound is obtained by integrating a signed
derivative comparison in the ordinary fundamental calculus sense, not by
running a root-search certificate. The inequalities are deliberately loose.
Uncompiled source.
-/

@[expose] public section
noncomputable section

open Set Real

namespace SofaUniqueness.Reference

def baseNumerator (t : ℝ) : ℝ := (t - 1) * cos t - sin t + 1

def numeratorMajorant (t : ℝ) : ℝ := t ^ 2 / 2 - t ^ 3 / 3

theorem baseNumerator_deriv (t : ℝ) :
    HasDerivAt baseNumerator ((1 - t) * sin t) t := by
  convert (((((hasDerivAt_id t).sub_const 1).mul (hasDerivAt_cos t)).sub
    (hasDerivAt_sin t)).add_const 1) using 1 <;> simp only [baseNumerator] <;> ring

theorem numeratorMajorant_deriv (t : ℝ) :
    HasDerivAt numeratorMajorant (t * (1 - t)) t := by
  convert ((hasDerivAt_pow 2 t).div_const 2).sub ((hasDerivAt_pow 3 t).div_const 3)
    using 1 <;> simp only [numeratorMajorant] <;> ring

theorem baseNumerator_le_majorant {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 4 / 5) :
    baseNumerator t ≤ numeratorMajorant t := by
  have hd (u : ℝ) : HasDerivAt (fun u => numeratorMajorant u - baseNumerator u)
      ((1 - u) * (u - sin u)) u := by
    apply ((numeratorMajorant_deriv u).sub (baseNumerator_deriv u)).congr_deriv
    ring
  have hm : MonotoneOn (fun u => numeratorMajorant u - baseNumerator u) (Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun u _ => (hd u).continuousAt.continuousWithinAt
    · exact fun u _ => (hd u).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      rw [(hd u).deriv]
      exact mul_nonneg (by linarith [hu.2]) (sub_nonneg.mpr (sin_le hu.1.le))
  have h := hm ⟨le_rfl, ht0⟩ ⟨ht0, le_rfl⟩ ht0
  simp only [numeratorMajorant, baseNumerator, sin_zero, cos_zero] at h
  nlinarith

theorem baseNumerator_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 4 / 5) :
    baseNumerator t ≤ 3 / 20 := by
  have hm : MonotoneOn numeratorMajorant (Icc 0 (4 / 5)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun u _ => (numeratorMajorant_deriv u).continuousAt.continuousWithinAt
    · exact fun u _ => (numeratorMajorant_deriv u).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      rw [(numeratorMajorant_deriv u).deriv]
      exact mul_nonneg hu.1.le (by linarith [hu.2])
  have h := hm ⟨ht0, ht1⟩ ⟨by norm_num, le_rfl⟩ ht1
  have hbase := baseNumerator_le_majorant ht0 ht1
  norm_num [numeratorMajorant] at h
  linarith

theorem num_nonneg {φ θ : ℝ} (hφ : 0 ≤ φ) (ho : φ ≤ θ) (ht : θ ≤ π / 4) :
    0 ≤ num φ θ := by
  have hm : MonotoneOn (num φ) (Icc φ θ) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun t _ => (num_theta_deriv φ t).continuousAt.continuousWithinAt
    · exact fun t _ => (num_theta_deriv φ t).differentiableAt.differentiableWithinAt
    · intro t ht'
      rw [interior_Icc] at ht'
      rw [(num_theta_deriv φ t).deriv]
      apply mul_nonneg
      · unfold gap
        linarith [pi_lt_four, ht'.2]
      · exact sin_nonneg_of_nonneg_of_le_pi (hφ.trans ht'.1.le)
          (by linarith [ht'.2, pi_pos])
  have hc := cos_le_one φ
  have hs := (triangle_trig hφ ho ht).1
  have hdiag : 0 ≤ num φ φ := by unfold num; nlinarith
  exact hdiag.trans (hm ⟨le_rfl, ho⟩ ⟨ho, le_rfl⟩ ho)

structure SmallBounds (φ θ : ℝ) : Prop where
  sin_phi : sin φ ∈ Icc (0 : ℝ) (1 / 20)
  cos_phi : cos φ ∈ Icc (499 / 500 : ℝ) 1
  sin_theta : sin θ ∈ Icc (0 : ℝ) (4 / 5)
  cos_theta : cos θ ∈ Icc (7 / 10 : ℝ) 1
  trig_sum : 1 ≤ cos θ + sin θ
  gap_mem : gap φ θ ∈ Icc (0 : ℝ) (4 / 5)
  slope_mem : slope φ θ ∈ Icc (1 : ℝ) (7 / 5)
  den_mem : den φ θ ∈ Icc (199 / 100 : ℝ) (23 / 10)
  A_mem : reconstructedA φ θ ∈ Icc (0 : ℝ) (4 / 25)
  B_mem : reconstructedB φ θ ∈ Icc (7 / 10 : ℝ) 2
  frame_mem : frameDen φ θ ∈ Icc (9 / 10 : ℝ) 1
  remainder_pos : 0 < remainder φ θ

/-- Bounds on the whole small-phi triangle, not only at zeros. -/
theorem smallBounds {φ θ : ℝ} (hp0 : 0 ≤ φ) (hp1 : φ ≤ 1 / 20)
    (ho : φ ≤ θ) (ht : θ ≤ π / 4) : SmallBounds φ θ := by
  obtain ⟨hs0, hsc, hc0, hcc, hts0, htc0, hsum⟩ := triangle_trig hp0 ho ht
  have hs1 : sin φ ≤ 1 / 20 := (sin_le hp0).trans hp1
  have hc1 : (499 / 500 : ℝ) ≤ cos φ := by
    have h := one_sub_sq_div_two_le_cos (x := φ)
    nlinarith
  have hθ0 : 0 ≤ θ := hp0.trans ho
  have hθ1 : θ ≤ 4 / 5 := by linarith [pi_lt_d2]
  have hts1 : sin θ ≤ 4 / 5 := (sin_le hθ0).trans hθ1
  have htc1 : (7 / 10 : ℝ) ≤ cos θ := by
    have horder := cos_le_cos_of_nonneg_of_le_pi hθ0
      (show π / 4 ≤ π by linarith [pi_pos]) ht
    rw [cos_pi_div_four] at horder
    have hsqrt := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hsqrt0 := sqrt_nonneg (2 : ℝ)
    nlinarith
  have hd0 : 0 ≤ gap φ θ := sub_nonneg.mpr ho
  have hd1 : gap φ θ ≤ 4 / 5 := by unfold gap; linarith
  have hk0 : 1 ≤ slope φ θ := by unfold slope; linarith
  have hk1 : slope φ θ ≤ 7 / 5 := by unfold slope gap at *; linarith
  have hD0 : (199 / 100 : ℝ) ≤ den φ θ := by unfold den; linarith [cos_le_one θ]
  have hD1 : den φ θ ≤ 23 / 10 := by unfold den; linarith [cos_le_one φ]
  have hDpos : 0 < den φ θ := by linarith
  have hN0 := num_nonneg hp0 ho ht
  have hN1 : num φ θ ≤ 3 / 10 := by
    have hbase := baseNumerator_le hθ0 hθ1
    have hneg : 0 ≤ φ * cos θ := mul_nonneg hp0 htc0.le
    have he : num φ θ = baseNumerator θ - φ * cos θ + 3 * sin φ := by
      unfold num baseNumerator
      ring
    rw [he]
    linarith
  have hA0 : 0 ≤ reconstructedA φ θ := div_nonneg hN0 hDpos.le
  have hA1 : reconstructedA φ θ ≤ 4 / 25 := by
    apply (div_le_iff₀ hDpos).mpr
    linarith
  have hoff0 := offset_nonneg hp0 ho ht
  have hoffLow : (7 / 10 : ℝ) ≤ offset φ θ := by
    unfold offset
    have hδ := sub_nonneg.mpr ho
    nlinarith [sq_nonneg (θ - φ), pi_gt_three]
  have hoffHigh : offset φ θ ≤ 8 / 5 := by
    unfold offset
    change 0 ≤ θ - φ at hd0
    change θ - φ ≤ 4 / 5 at hd1
    have hsq : (θ - φ) ^ 2 ≤ 2 * (θ - φ) := by nlinarith
    linarith [pi_lt_d2]
  have hAB : reconstructedA φ θ * slope φ θ ≤ (4 / 25 : ℝ) * (7 / 5) :=
    mul_le_mul hA1 hk1 (by linarith) (by norm_num)
  have hB0 : (7 / 10 : ℝ) ≤ reconstructedB φ θ := by
    have hm := mul_nonneg hA0 (show 0 ≤ slope φ θ by linarith)
    unfold reconstructedB
    linarith
  have hB1 : reconstructedB φ θ ≤ 2 := by unfold reconstructedB; linarith
  have hJs : slope φ θ * sin φ ≤ (7 / 5 : ℝ) * (1 / 20) :=
    mul_le_mul hk1 hs1 hs0 (by norm_num)
  have hJ0 : (9 / 10 : ℝ) ≤ frameDen φ θ := by unfold frameDen; linarith
  have hJ1 : frameDen φ θ ≤ 1 := by
    have hm := mul_nonneg (show 0 ≤ slope φ θ by linarith) hs0
    unfold frameDen
    linarith [cos_le_one φ]
  refine ⟨⟨hs0, hs1⟩, ⟨hc1, cos_le_one _⟩, ⟨hts0, hts1⟩,
    ⟨htc1, cos_le_one _⟩, hsum, ⟨hd0, hd1⟩, ⟨hk0, hk1⟩,
    ⟨hD0, hD1⟩, ⟨hA0, hA1⟩, ⟨hB0, hB1⟩, ⟨hJ0, hJ1⟩, ?_⟩
  unfold remainder
  linarith

end SofaUniqueness.Reference
