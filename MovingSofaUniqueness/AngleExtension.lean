module

public import MovingSofaOptimality.Angle.RightAngle

/-!
# Proposition 4: the pinned bounds give a right-angle motion

Let `S` be a monotone sofa of rotation angle `ω ∈ [arcsec(11/5), π/2)` and area at least `11/5`,
whose cap `K` satisfies the pinned bounds (19) of note 20. Then the points `O`, `o_ω - v_0` and
`o_ω - u_ω` lie in the closure of one inner quadrant `Q_K⁻(t)` of `K` (`consumed_of_pinned`), so
`S` has width at most one in every direction `u_t` with `t ∈ [ω, π/2]`, and the copy of `S`
rotated by `π/2 - ω` has a right-angle motion (`right_angle_motion_of_pinned_bounds`, by the motion
`right_angle_motion_of_width` of the proof of Theorem 1.5.2). This is Proposition 4 of note 20; the
geometry is that of Baek's Theorems 4.2.5 and 1.5.2.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

/-- For `ω ∈ [arcsec(11/5), π/2)`, a cap of sofa area at least `11/5` with the pinned bounds (19)
has an inner quadrant `Q_K⁻(t)`, `t ∈ (0, ω)`, whose closure contains `O`, `o_ω - v_0` and
`o_ω - u_ω`. -/
theorem consumed_of_pinned {K : Set (ℝ × ℝ)} {ω : ℝ}
    (hω : ω ∈ Ico arcsec22 (π / 2)) (hcap : IsCap K ω)
    (harea : (2.2 : ℝ) ≤ sofaArea ω K)
    (hw : wedgeGapWInf K ω ≤ sigmaAt K (π / 2))
    (hz : wedgeGapZInf K ω ≤ sigmaAt K ω) :
    ∃ t ∈ Ioo 0 ω, (0, 0) ∈ closure (qMinus K t) ∧
      oPt ω - vvec 0 ∈ closure (qMinus K t) ∧
      oPt ω - uvec ω ∈ closure (qMinus K t) := by
  obtain ⟨hc, hc5, hs, hs1, h4⟩ := ang_omega_facts hω
  have hω0 : 0 ≤ ω := by linarith [pi_pos]
  have hω2 := hω.2
  -- Step 1: `K` reaches the line at distance `dMin ω + cOmega ω` in the direction `u_0` or
  -- `u_{ω + π/2}`; otherwise it lies in the clipped region, whose area is too small (Lemma 4.2.2).
  have hlarge : dMin ω + cOmega ω ≤ supp K 0 ∨
      dMin ω + cOmega ω ≤ supp K (ω + π / 2) := by
    by_contra h
    rw [not_or, not_le, not_le] at h
    obtain ⟨h1, h2⟩ := h
    have hsub : K ⊆ clippedRegion ω (dMin ω) := by
      intro p hp
      refine ⟨⟨IsCap.subset_para hcap hp, ?_⟩, ?_⟩
      · exact (dot_le_supp hcap.2.1.2.1 hp 0).trans h1.le
      · exact (dot_le_supp hcap.2.1.2.1 hp (ω + π / 2)).trans h2.le
    have hfin : volume (clippedRegion ω (dMin ω)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        ((measure_mono fun p hp => hp.1.1).trans (ang_volume_para_le hc))
    have hKR : area K ≤ area (clippedRegion ω (dMin ω)) :=
      ENNReal.toReal_mono hfin (measure_mono hsub)
    have hn : 0 ≤ area (niche K ω) := ENNReal.toReal_nonneg
    have hclip := lemma4_2_2 hω
    unfold sofaArea at harea
    linarith
  -- Step 2: in the first case Baek's argument applies to `K`, in the second to its reflection.
  rcases hlarge with h | h
  · obtain ⟨h1, h2, h3⟩ := ang_consumed_of_supp_zero hω hcap hw h
    exact ⟨π / 2 - ω, ⟨by linarith, by linarith⟩,
      subset_closure h1, subset_closure h2, subset_closure h3⟩
  · have h' : dMin ω + cOmega ω ≤ supp (mirrorCap K ω) 0 := by
      rw [proposition2_5_4_supp, sub_zero]
      exact h
    have hw' : wedgeGapWInf (mirrorCap K ω) ω ≤
        sigmaAt (mirrorCap K ω) (π / 2) := by
      rw [ang_wedgeGapWInf_mirror, ang_sigmaAt_mirror hcap,
        show ω + π / 2 - π / 2 = ω by ring]
      exact hz
    obtain ⟨h1, h2, h3⟩ :=
      ang_consumed_of_supp_zero hω (proposition2_5_4_isCap hcap) hw' h'
    have m1 := ang_mirror_mem_qMinus h1
    have m2 := ang_mirror_mem_qMinus h2
    have m3 := ang_mirror_mem_qMinus h3
    obtain ⟨hP1, hP2, -, -⟩ := proposition4_2_1 ⟨hω0, hω.2⟩
    rw [hP1, cn_mirror_smul, ang_mirror_uvec_zero, ← hP2] at m2
    rw [hP2, cn_mirror_smul, ang_mirror_vvec, ← hP1] at m3
    have hm0 : mirror ω ((0 : ℝ), (0 : ℝ)) = (0, 0) := by simp [mirror]
    rw [hm0] at m1
    exact ⟨ω - (π / 2 - ω), ⟨by linarith, by linarith⟩,
      subset_closure m1, subset_closure m3, subset_closure m2⟩

/-- A monotone sofa of angle `ω ∈ [arcsec(11/5), π/2)` and area at least `11/5`, whose cap satisfies
the pinned bounds (19), has a right-angle motion after a rotation by `π/2 - ω`. -/
theorem right_angle_motion_of_pinned_bounds {S : Set (ℝ × ℝ)} {ω : ℝ}
    (hS : IsMonotoneSofa S ω) (hω : ω ∈ Ico arcsec22 (π / 2))
    (harea : (2.2 : ℝ) ≤ area S)
    (hw : wedgeGapWInf (capOf S ω) ω ≤ sigmaAt (capOf S ω) (π / 2))
    (hz : wedgeGapZInf (capOf S ω) ω ≤ sigmaAt (capOf S ω) ω) :
    IsMovingSofaWithAngle (rot (π / 2 - ω) '' S) (π / 2) := by
  have hmove := hS.isMovingSofaWithAngle
  have hcap : IsCap (capOf S ω) ω := theorem2_4_1 hS.1 hmove hS.isStandardPosition
  have harea' : (2.2 : ℝ) ≤ sofaArea ω (capOf S ω) := by rwa [theorem2_5_10 hS]
  obtain ⟨t₀, ht₀, h1, h2, h3⟩ := consumed_of_pinned hω hcap harea' hw hz
  obtain ⟨hP1, hP2, -, -⟩ := proposition4_2_1 ⟨hS.1.1.le, hω.2⟩
  rw [hP1] at h2
  rw [hP2] at h3
  refine right_angle_motion_of_width hmove hω.2 fun p hp q hq t ht => ?_
  rw [theorem2_4_3 hS] at hp hq
  exact ang_width_le_one ⟨hS.1.1, hω.2⟩ hcap ht₀ h1 h2 h3 hp.1 hq ht

end MovingSofaUniqueness
