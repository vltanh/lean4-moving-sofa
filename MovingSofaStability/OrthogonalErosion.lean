module

public import MovingSofaStability.CapShape

/-!
# Orthogonality improves the erosion allowance

Uncompiled proof source. The two inner hallway normals are orthonormal, so
moving by minus delta times both normals costs sqrt(2)*delta, not 2*delta.
This theorem applies to the actual cap-minus-niche sets of arbitrary normalized
caps. It does not assume injectivity, smoothness, or a reference-specific roof.
-/

@[expose] public section
noncomputable section

open Real Set MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

theorem norm2_frame_diagonal {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) :
    norm2 (δ • uvec t + δ • vvec t) = sqrt 2 * δ := by
  have hn := norm2_sq (δ • uvec t + δ • vvec t)
  simp only [dot_add_left, dot_add_right, dot_smul_left, dot_smul_right,
    dot_uvec_self, dot_vvec_self, dot_uvec_vvec, dot_vvec_uvec,
    mul_one, mul_zero, add_zero, zero_add] at hn
  have hs : sqrt (2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num)
  have hnonneg : 0 ≤ sqrt (2 : ℝ) * δ := mul_nonneg (sqrt_nonneg _) hδ
  nlinarith [norm2_nonneg (δ • uvec t + δ • vvec t)]

/-- Closed-ball erosion in the Euclidean metric. Both the cap and the niche
are handled, including the floor and the zero-error case. -/
theorem reference_erosion_subset_sqrt_two {δ : ℝ} (hδ : 0 ≤ δ)
    {K₀ K : Set Point} (h₀ : IsCap K₀ (π / 2)) (hK : IsCap K (π / 2))
    (hclose : UpperSupportClose δ K K₀) :
    euclideanErosion (sqrt 2 * δ) (capShape K₀) ⊆ capShape K := by
  have hs : sqrt (2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num)
  have hroot : 1 ≤ sqrt (2 : ℝ) := by nlinarith [sqrt_nonneg (2 : ℝ)]
  have hδradius : δ ≤ sqrt 2 * δ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hroot hδ
  intro p hp
  have hp0 : p ∈ capShape K₀ := hp p (by
    simpa only [euclideanDist_self] using mul_nonneg (sqrt_nonneg (2 : ℝ)) hδ)
  have hpK : p ∈ K := by
    apply (cap_mem_iff_upper hK p).2
    refine ⟨h₀.snd_nonneg hp0.1, ?_⟩
    intro t ht
    have hd : euclideanDist p (p + δ • uvec t) ≤ sqrt 2 * δ := by
      change norm2 (p - (p + δ • uvec t)) ≤ _
      rw [show p - (p + δ • uvec t) = -(δ • uvec t) by abel,
        norm2_neg, norm2_smul, norm2_uvec, mul_one, abs_of_nonneg hδ]
      exact hδradius
    have hq := (hp (p + δ • uvec t) hd).1
    have hsupport := dot_le_supp h₀.2.1.2.1 hq t
    rw [dot_add_left, dot_smul_left, dot_uvec_self, mul_one] at hsupport
    have herr := (abs_le.mp (hclose t ht)).1
    linarith
  refine ⟨hpK, ?_⟩
  intro hn
  obtain ⟨_, t, ht, hu, hv⟩ := (mem_niche_iff_slacks K p).1 hn
  let q := p - δ • uvec t - δ • vvec t
  have hd : euclideanDist p q ≤ sqrt 2 * δ := by
    change norm2 (p - (p - δ • uvec t - δ • vvec t)) ≤ _
    rw [show p - (p - δ • uvec t - δ • vvec t) = δ • uvec t + δ • vvec t by abel]
    exact (norm2_frame_diagonal hδ t).le
  have hq := hp q hd
  have herrU := (abs_le.mp (hclose t ⟨ht.1.le, by linarith [ht.2, pi_pos]⟩)).2
  have herrV := (abs_le.mp (hclose (t + π / 2)
    ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩)).2
  have eqU : innerSlackU K₀ t q = innerSlackU K t p + supp K t - supp K₀ t - δ := by
    simp only [innerSlackU, q, dot_sub_left, dot_smul_left, dot_uvec_self, dot_vvec_uvec]
    ring
  have eqV : innerSlackV K₀ t q = innerSlackV K t p +
      supp K (t + π / 2) - supp K₀ (t + π / 2) - δ := by
    simp only [innerSlackV, q, dot_sub_left, dot_smul_left, dot_uvec_vvec, dot_vvec_self]
    ring
  apply hq.2
  exact (mem_niche_iff_slacks K₀ q).2
    ⟨h₀.snd_nonneg hq.1, t, ht, by rw [eqU]; linarith, by rw [eqV]; linarith⟩

end MovingSofaStability
