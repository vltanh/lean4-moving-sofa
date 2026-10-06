module

public import MovingSofaStability.LocalArmMargins

/-!
# Core monotonicity without differentiating through curvature atoms

Uncompiled proof source. The one-sided fundamental theorem bounds increments
by a constant derivative bound; no integrability or continuity of the competing
right derivative is presumed. This is enough for a strictly monotone core graph
and for the local cut-separation argument.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality

namespace MovingSofaStability

def cornerRightVelocity (K : Set Point) (t : ℝ) : Point :=
  -(fPlus K t - 1) • uvec t + (gPlus K t - 1) • vvec t

theorem corner_hasRightDeriv {K : Set Point} (hK : IsCap K (π / 2)) (t : ℝ) :
    HasDerivWithinAt (innerCorner K) (cornerRightVelocity K t) (Ioi t) t :=
  (theorem6_2_3_right hK).2.mono Ioi_subset_Ici_self

/-- Project a vector right derivative onto a fixed unit normal. -/
theorem hasRightDeriv_dot_uvec {x dx : ℝ → Point} {t d : ℝ}
    (h : HasDerivWithinAt x (dx t) (Ioi t) t) :
    HasDerivWithinAt (fun s => dot (x s) (uvec d)) (dot (dx t) (uvec d)) (Ioi t) t := by
  sorry

/-- The constant comparison version of the one-sided fundamental theorem. -/
theorem right_derivative_increment_le {f df : ℝ → ℝ} {a b B : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hB : ∀ t ∈ Ioo a b, df t ≤ B) : f b - f a ≤ B * (b - a) := by
  have h := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab hf hd
    (φ := fun _ => B) (continuousOn_const.integrableOn_compact isCompact_Icc) hB
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h

theorem right_derivative_increment_ge {f df : ℝ → ℝ} {a b B : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hB : ∀ t ∈ Ioo a b, B ≤ df t) : B * (b - a) ≤ f b - f a := by
  sorry

theorem sin_add_cos_ge_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (π / 2)) :
    1 ≤ sin t + cos t := by
  have hs := sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, pi_pos])
  have hc := cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, pi_pos], ht.2⟩
  have h := sin_sq_add_cos_sq t
  nlinarith [sin_le_one t, cos_le_one t]

/-- The core's horizontal velocity has a uniform strictly negative upper bound. -/
theorem CoreArmMargin.velocity_fst_le {K : Set Point} (hK : IsCap K (π / 2))
    {a b c t : ℝ} (h : CoreArmMargin K a b c) (hc : 0 ≤ c)
    (ht : t ∈ Icc a b) (hti : t ∈ Icc (0 : ℝ) (π / 2)) :
    (cornerRightVelocity K t).1 ≤ -c := by
  obtain ⟨hf, -, hg, -⟩ := h.oneSided hK ht
  have hs := sin_nonneg_of_nonneg_of_le_pi hti.1 (by linarith [hti.2, pi_pos])
  have hcos := cos_nonneg_of_mem_Icc ⟨by linarith [hti.1, pi_pos], hti.2⟩
  have hfc := mul_le_mul_of_nonneg_right (show c ≤ fPlus K t - 1 by linarith) hcos
  have hgs := mul_le_mul_of_nonneg_right (show c ≤ gPlus K t - 1 by linarith) hs
  have hcprod := mul_le_mul_of_nonneg_left (sin_add_cos_ge_one hti) hc
  simp only [cornerRightVelocity, Prod.fst_add, Prod.smul_fst, smul_eq_mul, uvec_fst, vvec_fst]
  nlinarith

/-- Every core chord has a definite horizontal decrease. -/
theorem CoreArmMargin.horizontal_decrease {K : Set Point} (hK : IsCap K (π / 2))
    {a b c : ℝ} (h : CoreArmMargin K a b c) (hc : 0 ≤ c)
    (ha : 0 ≤ a) (hb : b ≤ π / 2) {u v : ℝ}
    (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u ≤ v) :
    (innerCorner K v).1 - (innerCorner K u).1 ≤ -c * (v - u) := by
  apply right_derivative_increment_le huv (opt_innerCorner_continuous hK.2.1).fst.continuousOn
    (fun t ht => (corner_hasRightDeriv hK t).fst)
  intro t ht
  exact h.velocity_fst_le hK hc ⟨hu.1.trans ht.1.le, ht.2.le.trans hv.2⟩
    ⟨ha.trans (hu.1.trans ht.1.le), (ht.2.le.trans hv.2).trans hb⟩

theorem CoreArmMargin.strictAnti_core {K : Set Point} (hK : IsCap K (π / 2))
    {a b c : ℝ} (h : CoreArmMargin K a b c) (hc : 0 < c)
    (ha : 0 ≤ a) (hb : b ≤ π / 2) :
    StrictAntiOn (fun t => (innerCorner K t).1) (Icc a b) := by
  intro u hu v hv huv
  have hdec := h.horizontal_decrease hK hc.le ha hb hu hv huv.le
  have hneg : -c * (v - u) < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos hc) (sub_pos.mpr huv)
  linarith

/-- Projection onto an earlier cut normal decreases at a fixed rate. -/
theorem CoreArmMargin.right_cut_velocity {K : Set Point} (hK : IsCap K (π / 2))
    {a b c t d : ℝ} (h : CoreArmMargin K a b c) (hc : 0 ≤ c)
    (ht : t ∈ Icc a b) (hangle : t - d ∈ Icc (0 : ℝ) (π / 2)) :
    dot (cornerRightVelocity K t) (uvec d) ≤ -c := by
  obtain ⟨hf, -, hg, -⟩ := h.oneSided hK ht
  have hs := sin_nonneg_of_nonneg_of_le_pi hangle.1 (by linarith [hangle.2, pi_pos])
  have hcos := cos_nonneg_of_mem_Icc ⟨by linarith [hangle.1, pi_pos], hangle.2⟩
  have he : dot (cornerRightVelocity K t) (uvec d) =
      -(fPlus K t - 1) * cos (t - d) - (gPlus K t - 1) * sin (t - d) := by
    simp only [cornerRightVelocity, dot_add_left, dot_smul_left, dot_uvec_uvec, dot_vvec_uvec']
    rw [show d - t = -(t - d) by ring, sin_neg]
    ring
  have hm1 := mul_le_mul_of_nonneg_right (show c ≤ fPlus K t - 1 by linarith) hcos
  have hm2 := mul_le_mul_of_nonneg_right (show c ≤ gPlus K t - 1 by linarith) hs
  have hm3 := mul_le_mul_of_nonneg_left (sin_add_cos_ge_one hangle) hc
  rw [he]
  nlinarith

/-- Projection onto the left cut normal increases when approaching the cut from the left. -/
theorem CoreArmMargin.left_cut_velocity {K : Set Point} (hK : IsCap K (π / 2))
    {a b c t d : ℝ} (h : CoreArmMargin K a b c) (hc : 0 ≤ c)
    (ht : t ∈ Icc a b) (hangle : d - t ∈ Icc (0 : ℝ) (π / 2)) :
    c ≤ dot (cornerRightVelocity K t) (uvec (d + π / 2)) := by
  obtain ⟨hf, -, hg, -⟩ := h.oneSided hK ht
  have hs := sin_nonneg_of_nonneg_of_le_pi hangle.1 (by linarith [hangle.2, pi_pos])
  have hcos := cos_nonneg_of_mem_Icc ⟨by linarith [hangle.1, pi_pos], hangle.2⟩
  have he : dot (cornerRightVelocity K t) (uvec (d + π / 2)) =
      (fPlus K t - 1) * sin (d - t) + (gPlus K t - 1) * cos (d - t) := by
    simp only [cornerRightVelocity, dot_add_left, dot_smul_left, dot_uvec_uvec, dot_vvec_uvec']
    rw [show t - (d + π / 2) = -(d - t) - π / 2 by ring,
      cos_sub_pi_div_two, sin_neg,
      show d + π / 2 - t = (d - t) + π / 2 by ring, sin_add_pi_div_two]
    ring
  have hm1 := mul_le_mul_of_nonneg_right (show c ≤ fPlus K t - 1 by linarith) hs
  have hm2 := mul_le_mul_of_nonneg_right (show c ≤ gPlus K t - 1 by linarith) hcos
  have hm3 := mul_le_mul_of_nonneg_left (sin_add_cos_ge_one hangle) hc
  rw [he]
  nlinarith

end MovingSofaStability
