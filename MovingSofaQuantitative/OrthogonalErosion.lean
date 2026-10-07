module

public import MovingSofaStability.Margins

/-!
# Orthogonal erosion for actual cap-minus-niche sets

Uncompiled proof source. The two wall corrections are orthogonal, so their
combined displacement is sqrt(2)*delta, rather than 2*delta. The conclusion
is inclusion of actual eroded sets, not of their convex hulls.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability

namespace MovingSofaQuantitative

theorem norm2_orthogonal_sq (a b t : ℝ) :
    norm2 (a • uvec t + b • vvec t) ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm2_sq]
  simp only [dot_add_left, dot_add_right, dot_smul_left, dot_smul_right,
    dot_uvec_self, dot_vvec_self, dot_uvec_vvec, dot_vvec_uvec]
  ring

theorem norm2_equal_orthogonal {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) :
    norm2 (δ • uvec t + δ • vvec t) = sqrt 2 * δ := by
  have hn := norm2_nonneg (δ • uvec t + δ • vvec t)
  have hp : 0 ≤ sqrt 2 * δ := mul_nonneg (sqrt_nonneg _) hδ
  apply (sq_eq_sq₀ hn hp).mp
  rw [norm2_orthogonal_sq, mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Orthogonal wall corrections give the exact erosion constant sqrt(2). -/
theorem orthogonal_reference_erosion {δ : ℝ} (hδ : 0 ≤ δ) {K₀ K : Set Point}
    (h₀ : IsCap K₀ (π / 2)) (hK : IsCap K (π / 2))
    (hclose : UpperSupportClose δ K K₀) :
    euclideanErosion (sqrt 2 * δ) (capShape K₀) ⊆ capShape K := by
  have hroot : (1 : ℝ) ≤ sqrt 2 := by
    nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sqrt_nonneg (2 : ℝ)]
  have hδr : δ ≤ sqrt 2 * δ := by nlinarith only [mul_nonneg (sub_nonneg.mpr hroot) hδ]
  intro p hp
  have hpK : p ∈ K := by
    refine (cap_mem_iff_upper hK p).2
      ⟨h₀.snd_nonneg (hp p (by rw [euclideanDist_self]; positivity)).1, fun t ht => ?_⟩
    have hq := (hp (p + δ • uvec t) (by
      rw [euclideanDist, sub_add_cancel_left, norm2_neg, norm2_smul, norm2_uvec,
        abs_of_nonneg hδ, mul_one]
      exact hδr)).1
    have hs := dot_le_supp h₀.2.1.2.1 hq t
    rw [dot_add_left, dot_smul_left, dot_uvec_self, mul_one] at hs
    linarith [(abs_le.mp (hclose t ht)).1]
  refine ⟨hpK, fun hn => ?_⟩
  obtain ⟨_, t, ht, hu, hv⟩ := (mem_niche_iff_slacks K p).1 hn
  have hq := hp (p - δ • uvec t - δ • vvec t) (by
    rw [euclideanDist,
      show p - (p - δ • uvec t - δ • vvec t) = δ • uvec t + δ • vvec t by abel,
      norm2_equal_orthogonal hδ])
  have hU := (abs_le.mp (hclose t ⟨ht.1.le, by linarith [ht.2, pi_pos]⟩)).2
  have hV := (abs_le.mp (hclose (t + π / 2)
    ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩)).2
  simp only [innerSlackU, innerSlackV] at hu hv
  refine hq.2 ((mem_niche_iff_slacks K₀ _).2 ⟨h₀.snd_nonneg hq.1, t, ht, ?_, ?_⟩) <;>
    simp only [innerSlackU, innerSlackV, dot_sub_left, dot_smul_left, dot_uvec_self,
      dot_vvec_uvec, dot_uvec_vvec, dot_vvec_self] <;> linarith

end MovingSofaQuantitative
