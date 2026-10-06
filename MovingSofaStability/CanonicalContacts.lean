module

public import MovingSofaStability.CapWidthGeometry

/-!
# Canonical tail contacts without global injectivity

The topmost-point proof of the source endpoint contact theorem needs only a cap,
a cut foot in that cap, and one strict arm inequality at the cut. Those
sufficient hypotheses are exposed here.
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
  have hφ0 := hφ.1
  have hφ4 := hφ.2
  have hpi := pi_pos
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcb := hcap.2.1
  let L := K ∩ {q | dot q (vvec (π / 2 - φ)) = supp K (π / 2 - φ + π / 2) - 1}
  have hLc : IsCompact L := hcb.2.1.inter_right (isClosed_eq (continuous_dot _) continuous_const)
  have hZL : zLeft φ K ∈ L := by
    refine ⟨hZ, ?_⟩
    simp only [mem_ofPred_eq, opt_zLeft_eq, dot, vvec, sin_pi_div_two_sub, zero_mul, add_zero,
      show π / 2 - φ + π / 2 = π - φ by ring]
    field_simp [hc.ne']
    ring
  obtain ⟨p, ⟨hpK, hpl⟩, hpmax⟩ :=
    hLc.exists_isMaxOn ⟨_, hZL⟩ (continuous_dot (uvec (π / 2 - φ))).continuousOn
  have hpl' : dot p (vvec (π / 2 - φ)) = supp K (π / 2 - φ + π / 2) - 1 := hpl
  have hu : ∀ q : Point, dot q (uvec (-φ)) = -dot q (vvec (π / 2 - φ)) := by
    intro q
    simp only [dot, uvec, vvec, cos_neg, sin_neg, sin_pi_div_two_sub, cos_pi_div_two_sub]
    ring
  have hv : ∀ q : Point, dot q (vvec (-φ)) = dot q (uvec (π / 2 - φ)) := by
    intro q
    simp only [dot, uvec, vvec, cos_neg, sin_neg, sin_pi_div_two_sub, cos_pi_div_two_sub]
    ring
  obtain ⟨θ, hθ, hpθ⟩ := opt_exists_normal_of_isMax hcb hpK (α := -φ)
    (c := -(supp K (π / 2 - φ + π / 2) - 1)) (by rw [hu, hpl])
    (fun q hq hql => by
      rw [hv, hv]
      apply hpmax ⟨hq, ?_⟩
      change dot q (vvec (π / 2 - φ)) = _
      rw [hu] at hql
      linarith)
  have hp2 := inj_cap_strip hcap hpK
  have hθ2 : π / 2 - φ ≤ θ := by
    by_contra hnot
    have hgt := not_le.mp hnot
    let a := vminus K (π / 2 - φ)
    have haK : a ∈ K := (vminus_mem_edge hcb _).1
    have h1 : dot p (uvec (π / 2 - φ)) ≤ dot a (uvec (π / 2 - φ)) := by
      rw [show dot a (uvec (π / 2 - φ)) = supp K (π / 2 - φ) from dot_vminus_uvec K _]
      exact dot_le_supp hcb.2.1 hpK _
    have h2 : dot a (uvec θ) ≤ dot p (uvec θ) := by rw [hpθ]; exact dot_le_supp hcb.2.1 haK θ
    have ep := dot_uvec_eq_cos_add_sin p θ (π / 2 - φ)
    have ea := dot_uvec_eq_cos_add_sin a θ (π / 2 - φ)
    have hcos : 0 ≤ cos (θ - (π / 2 - φ)) :=
      cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith⟩
    have hsin : sin (θ - (π / 2 - φ)) < 0 :=
      sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith [hθ.1])
    have key : dot p (vvec (π / 2 - φ)) ≤ dot a (vvec (π / 2 - φ)) := by
      nlinarith [mul_le_mul_of_nonneg_left h1 hcos]
    have hf' := hf
    rw [inj_fMinus_eq] at hf'
    change 1 < supp K (π / 2 - φ + π / 2) - dot a (vvec (π / 2 - φ)) at hf'
    linarith
  have hp1 : dot p (uvec (π - φ)) = supp K (π - φ) - 1 := by
    rw [show π - φ = π / 2 - φ + π / 2 by ring, uvec_add_pi_div_two]
    exact hpl
  have key : ∀ t ∈ Icc (π / 2) (π - φ), supp K t - 1 ≤ dot p (uvec t) := by
    intro t ht
    rcases le_or_gt θ t with hθt | hθt
    · rcases eq_or_lt_of_le hθ.2 with hθe | hθe
      · have he : t = π - φ := le_antisymm ht.2 (by linarith)
        rw [he]
        linarith
      · have hI := opt_supp_interp hcb hθt ht.2 (by linarith)
        have hE := dot_uvec_comb p θ (π - φ) t
        have hsinpos : 0 < sin (π - φ - θ) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
        have hmono : sin (t - θ) ≤ sin (π - φ - θ) :=
          sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith [ht.2])
        have hs1 : 0 ≤ sin (π - φ - t) := sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.2]) (by linarith [ht.1])
        rw [hpθ, hp1] at hE
        nlinarith
    · have hθπ : π / 2 < θ := ht.1.trans_lt hθt
      have hI := opt_supp_interp hcb ht.1 hθt.le (by linarith [hθ.2])
      have hE := dot_uvec_comb p (π / 2) θ t
      rw [hcap.2.2.2.1] at hI
      rw [hpθ, dot_uvec_pi_div_two] at hE
      have hsinpos : 0 < sin (θ - π / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ.2])
      have hmono : sin (θ - t) ≤ sin (θ - π / 2) :=
        sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith [hθ.2]) (by linarith [ht.1])
      have hs1 : 0 ≤ sin (θ - t) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθ.2, ht.1])
      have hs2 : 0 ≤ sin (t - π / 2) := sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht.2])
      nlinarith [mul_le_mul_of_nonneg_left hp2.2 hs1, mul_nonneg hs1 hp2.1]
  refine ⟨p, ⟨hpK, ?_⟩, hpl⟩
  simp only [mem_iInter₂]
  intro s hs
  change supp K (s + π / 2) - 1 ≤ dot p (uvec (s + π / 2))
  exact key _ ⟨by linarith [hs.1], by linarith [hs.2]⟩

end MovingSofaStability
