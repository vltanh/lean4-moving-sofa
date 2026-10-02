module

public import MovingSofa.Angle.RightAngle

/-!
# Shape-preserving angular extension from the two pinned inequalities

This generalizes the existing proofs of Theorems 4.2.5 and 1.5.2 by exposing
exactly the pinned-edge hypotheses that they use. In particular no balanced
maximum cap is substituted for the specified sofa. All geometry below comes
from the existing, non-maximality-dependent lemmas in `Angle.RightAngle`.

The scripts are uncompiled. They contain no admissions or external evaluation.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory MovingSofa

namespace SofaUniqueness.Draft

/-- The consumed triangle conclusion requires the pinned inequalities, not
balancedness of the cap. -/
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
  have hlarge : dMin ω + cOmega ω ≤ supp K 0 ∨
      dMin ω + cOmega ω ≤ supp K (ω + π / 2) := by
    by_contra h
    rw [not_or, not_le, not_le] at h
    obtain ⟨h1, h2⟩ := h
    have hsub : K ⊆ clippedRegion ω (dMin ω) := by
      intro p hp
      refine ⟨⟨ang_cap_subset_para hcap hp, ?_⟩, ?_⟩
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
    rw [hP1, ang_mirror_smul, ang_mirror_uvec_zero, ← hP2] at m2
    rw [hP2, ang_mirror_smul, ang_mirror_vvec, ← hP1] at m3
    have hm0 : mirror ω ((0 : ℝ), (0 : ℝ)) = (0, 0) := by simp [mirror]
    rw [hm0] at m1
    exact ⟨ω - (π / 2 - ω), ⟨by linarith, by linarith⟩,
      subset_closure m1, subset_closure m3, subset_closure m2⟩

/-- A motion with angle `ω` extends to a right-angle motion whenever the SAME
sofa has width at most one in all additional directions. -/
theorem right_angle_motion_of_width {S : Set (ℝ × ℝ)} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) (hω : ω < π / 2)
    (hwidth : ∀ p ∈ S, ∀ q ∈ S, ∀ t ∈ Icc ω (π / 2),
      dot (p - q) (uvec t) ≤ 1) :
    ∃ a : ℝ, IsMovingSofaWithAngle (rot a '' S) (π / 2) := by
  obtain ⟨hcl, hconn, θ, c, hm⟩ := hS
  have hSc : IsCompact S :=
    isCompact_of_isMovingSofa ⟨ω, hcl, hconn, θ, c, hm⟩
  obtain ⟨R, hR⟩ := hSc.isBounded.exists_norm_le
  set β := π / 2 - ω with hβ
  have hβ0 : 0 < β := by linarith
  set φf : ℝ → ℝ := fun s => β * max 0 (1 - 3 * s) with hφf
  set lf : ℝ → ℝ := fun s => max 0 (min 1 (3 * s - 1)) with hlf
  set τf : ℝ → ℝ := fun s => max 0 (min 1 (3 * s - 2)) with hτf
  set e : ℝ → ℝ × ℝ := fun φ =>
    (1 - 2 * R, supp S (π / 2 - φ + π)) with he
  have hφc : Continuous φf := by rw [hφf]; fun_prop
  have hlc : Continuous lf := by rw [hlf]; fun_prop
  have hτc : Continuous τf := by rw [hτf]; fun_prop
  have hec : Continuous e := by
    rw [he]
    exact continuous_const.prodMk ((continuous_supp hSc).comp (by fun_prop))
  have hτmaps : MapsTo τf (Icc 0 1) (Icc 0 1) := fun s _ =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hτ0 : τf 0 = 0 := by simp only [hτf]; norm_num
  have hτ1 : τf 1 = 1 := by simp only [hτf]; norm_num
  have hφ0 : φf 0 = β := by simp only [hφf]; norm_num
  have hφ1 : φf 1 = 0 := by simp only [hφf]; norm_num
  have hl0 : lf 0 = 0 := by simp only [hlf]; norm_num
  have hl1 : lf 1 = 1 := by simp only [hlf]; norm_num
  have hphase := fun φ (hφ : φ ∈ Icc 0 β) p (hp : p ∈ S) =>
    ang_phase_one hSc hR hwidth hφ hp
  refine ⟨β, ?_, ?_, fun s => θ (τf s) - β + φf s,
    fun s => (1 - lf s) • e (φf s) + lf s • c (τf s),
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [ang_image_rot]
    exact hcl.preimage (ang_continuous_rot _)
  · exact hconn.image _ (ang_continuous_rot _).continuousOn
  · exact ((hm.continuousOn_angle.comp hτc.continuousOn hτmaps).sub
      continuousOn_const).add hφc.continuousOn
  · exact ((continuous_const.sub hlc).smul (hec.comp hφc)).continuousOn.add
      (hlc.continuousOn.smul
        (hm.continuousOn_shift.comp hτc.continuousOn hτmaps))
  · simp only [hτ0, hφ0, hm.angle_zero]
    ring
  · simp only [hτ1, hφ1, hm.angle_one, hβ]
    ring
  · rintro _ ⟨q, hq, rfl⟩
    simp only [hτ0, hφ0, hl0, hm.angle_zero, sub_zero, one_smul,
      zero_smul, add_zero]
    rw [show (0 : ℝ) - β + β = 0 by ring, rot_zero]
    exact hphase β ⟨hβ0.le, le_rfl⟩ q hq
  · rintro s hs _ ⟨q, hq, rfl⟩
    rw [← rot_add,
      show θ (τf s) - β + φf s + β = θ (τf s) + φf s by ring]
    rcases le_or_gt s (1 / 3) with hs1 | hs1
    · have hτ : τf s = 0 := by
        simp only [hτf]
        rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      have hl : lf s = 0 := by
        simp only [hlf]
        rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      have hφ : φf s ∈ Icc 0 β := by
        simp only [hφf]
        rw [max_eq_right (by linarith)]
        constructor <;> nlinarith [hs.1]
      rw [hτ, hl, hm.angle_zero, zero_add, sub_zero, one_smul,
        zero_smul, add_zero]
      exact Or.inl (hphase _ hφ q hq)
    rcases le_or_gt s (2 / 3) with hs2 | hs2
    · have hτ : τf s = 0 := by
        simp only [hτf]
        rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      have hφ : φf s = 0 := by
        simp only [hφf]
        rw [max_eq_left (by linarith), mul_zero]
      have hl : lf s ∈ Icc (0 : ℝ) 1 :=
        ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
      rw [hτ, hφ, hm.angle_zero, add_zero, rot_zero]
      left
      have ha := hphase 0 ⟨le_rfl, hβ0.le⟩ q hq
      rw [rot_zero] at ha
      have hb := hm.start q hq
      rw [hm.angle_zero, rot_zero] at hb
      exact ang_horizSide_combo ha hb hl.1 hl.2
    · have hφ : φf s = 0 := by
        simp only [hφf]
        rw [max_eq_left (by linarith), mul_zero]
      have hl : lf s = 1 := by
        simp only [hlf]
        rw [min_eq_left (by linarith), max_eq_right zero_le_one]
      rw [hφ, hl, add_zero, sub_self, zero_smul, zero_add, one_smul]
      exact hm.inside (τf s) (hτmaps hs) q hq
  · rintro _ ⟨q, hq, rfl⟩
    rw [← rot_add,
      show θ (τf 1) - β + φf 1 + β = θ (τf 1) + φf 1 by ring]
    simp only [hτ1, hφ1, hl1, add_zero, sub_self, zero_smul,
      zero_add, one_smul]
    exact hm.finish q hq

/-- The specified monotone sofa extends to a right-angle motion from pinned
bounds on its own cap. No balancedness assumption is used. -/
theorem right_angle_motion_of_pinned_bounds {S : Set (ℝ × ℝ)} {ω : ℝ}
    (hS : IsMonotoneSofa S ω) (hω : ω ∈ Ico arcsec22 (π / 2))
    (harea : (2.2 : ℝ) ≤ area S)
    (hw : wedgeGapWInf (capOf S ω) ω ≤ sigmaAt (capOf S ω) (π / 2))
    (hz : wedgeGapZInf (capOf S ω) ω ≤ sigmaAt (capOf S ω) ω) :
    ∃ a : ℝ, IsMovingSofaWithAngle (rot a '' S) (π / 2) := by
  have hωI := hS.1
  have hmove : IsMovingSofaWithAngle S ω := by
    obtain ⟨hω', T, hT, hstd, hEq⟩ := hS
    rw [hEq]
    exact (theorem2_3_2 hω' hT hstd).1
  have hstdS : IsStandardPosition S ω := by
    obtain ⟨hω', T, hT, hstd, hEq⟩ := hS
    rw [hEq]
    exact (theorem2_3_2 hω' hT hstd).2.1
  have hcap : IsCap (capOf S ω) ω := theorem2_4_1 hωI hmove hstdS
  have hSK : S = capOf S ω \ niche (capOf S ω) ω := theorem2_4_3 hS
  have harea' : (2.2 : ℝ) ≤ sofaArea ω (capOf S ω) := by
    rw [theorem2_5_10 hS]
    exact harea
  obtain ⟨t₀, ht₀, h1, h2, h3⟩ := consumed_of_pinned hω hcap harea' hw hz
  obtain ⟨hP1, hP2, -, -⟩ := proposition4_2_1 ⟨hωI.1.le, hω.2⟩
  rw [hP1] at h2
  rw [hP2] at h3
  apply right_angle_motion_of_width hmove hω.2
  intro p hp q hq t ht
  rw [hSK] at hp hq
  exact ang_width_le_one ⟨hωI.1, hω.2⟩ hcap ht₀ h1 h2 h3 hp.1 hq ht

end SofaUniqueness.Draft
