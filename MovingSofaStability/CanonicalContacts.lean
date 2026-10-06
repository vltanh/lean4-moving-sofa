module

public import MovingSofaStability.CapWidthGeometry

/-!
# Canonical tail contacts without global injectivity

Uncompiled proof source. The topmost-point proof of the source endpoint
contact theorem needs only a cap, a cut foot in that cap, and one strict
arm inequality at the cut. Those sufficient hypotheses are exposed here.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality

namespace MovingSofaStability

/-- The right canonical body touches its cut line from a single strict g-arm inequality. -/
theorem canonical_right_contact {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set Point} (hcap : IsCap K (π / 2)) (hW : wRight φ K ∈ K)
    (hg : 1 < gPlus K φ) :
    ∃ p ∈ rightBody φ K, dot p (uvec φ) = supp K φ - 1 := by
  have hφ0 := hφ.1
  have hφ4 := hφ.2
  have hpi := pi_pos
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcb := hcap.2.1
  let L := K ∩ line φ (supp K φ - 1)
  have hWL : wRight φ K ∈ L := by
    refine ⟨hW, ?_⟩
    simp only [line, mem_ofPred_eq, opt_wRight_eq, dot, uvec, zero_mul, add_zero]
    field_simp [hc.ne']
  obtain ⟨p, ⟨hpK, hpl⟩, hpmax⟩ := (hcb.2.1.inter_right (isClosed_line _ _)).exists_isMaxOn
    ⟨_, hWL⟩ (continuous_dot (vvec φ)).continuousOn
  have hpl' : dot p (uvec φ) = supp K φ - 1 := hpl
  obtain ⟨θ, hθ, hpθ⟩ := opt_exists_normal_of_isMax hcb hpK hpl'
    (fun q hq hql => hpmax ⟨hq, hql⟩)
  have hp2 := inj_cap_strip hcap hpK
  have hθ2 : θ ≤ φ + π / 2 := by
    by_contra hnot
    have hgt := not_le.mp hnot
    let c := vplus K (φ + π / 2)
    have hcK : c ∈ K := (vplus_mem_edge hcb _).1
    have h1 : dot p (uvec (φ + π / 2)) ≤ dot c (uvec (φ + π / 2)) := by
      rw [show dot c (uvec (φ + π / 2)) = supp K (φ + π / 2) from dot_vplus_uvec K _]
      exact dot_le_supp hcb.2.1 hpK _
    have h2 : dot c (uvec θ) ≤ dot p (uvec θ) := by
      rw [hpθ]
      exact dot_le_supp hcb.2.1 hcK _
    have ep := dot_uvec_eq_cos_add_sin p θ φ
    have ec := dot_uvec_eq_cos_add_sin c θ φ
    rw [← uvec_add_pi_div_two] at ep ec
    have hcos : cos (θ - φ) < 0 :=
      cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [hθ.2])
    have hsin : 0 ≤ sin (θ - φ) := sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    have key : dot p (uvec φ) ≤ dot c (uvec φ) := by
      nlinarith [mul_le_mul_of_nonneg_left h1 hsin]
    have hg' := hg
    rw [inj_gPlus_eq, vvec_add_pi_div_two, dot_neg_right] at hg'
    change 1 < supp K φ + -dot c (uvec φ) at hg'
    linarith
  refine ⟨p, ⟨hpK, ?_⟩, hpl'⟩
  simp only [mem_iInter₂]
  intro s hs
  change supp K s - 1 ≤ dot p (uvec s)
  rcases le_or_gt s θ with hsθ | hsθ
  · rcases eq_or_lt_of_le hθ.1 with hθφ | hθφ
    · have he : s = φ := le_antisymm (hθφ ▸ hsθ) hs.1
      rw [he]
      linarith
    · have hI := opt_supp_interp hcb hs.1 hsθ (by linarith)
      have hE := dot_uvec_comb p φ θ s
      have hsinpos : 0 < sin (θ - φ) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have hmono : sin (θ - s) ≤ sin (θ - φ) :=
        sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith [hs.1])
      have hs1 : 0 ≤ sin (s - φ) := sin_nonneg_of_nonneg_of_le_pi (by linarith [hs.1]) (by linarith)
      rw [hpθ, hpl'] at hE
      nlinarith
  · have hθπ : θ < π / 2 := hsθ.trans_le hs.2
    have hI := opt_supp_interp hcb hsθ.le hs.2 (by linarith [hθ.1])
    have hE := dot_uvec_comb p θ (π / 2) s
    rw [hcap.2.2.2.1] at hI
    rw [hpθ, dot_uvec_pi_div_two] at hE
    have hcpos : 0 < sin (π / 2 - θ) := by
      rw [sin_pi_div_two_sub]
      exact cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθπ⟩
    have hmono : sin (s - θ) ≤ sin (π / 2 - θ) :=
      sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith [hθ.1]) (by linarith [hs.2])
    have hs1 : 0 ≤ sin (s - θ) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθ.1, hs.2])
    nlinarith [mul_le_mul_of_nonneg_left hp2.2 hs1, mul_nonneg hs1 hp2.1]

/-- The left canonical contact requires only the matching f-arm inequality. -/
theorem canonical_left_contact {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set Point} (hcap : IsCap K (π / 2)) (hZ : zLeft φ K ∈ K)
    (hf : 1 < fMinus K (π / 2 - φ)) :
    ∃ p ∈ leftBody φ K, dot p (vvec (π / 2 - φ)) = supp K (π / 2 - φ + π / 2) - 1 := by
  sorry

end MovingSofaStability
