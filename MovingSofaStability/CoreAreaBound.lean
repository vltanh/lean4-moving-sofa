module

public import MovingSofaStability.CoreRegionGeometry
public import MovingSofaStability.TerminalBookkeeping

/-!
# The local core-area inequality

Uncompiled proof source. The core is a continuous Lipschitz graph with a
strictly positive height. Its under-graph region and two endpoint triangles
are disjoint subsets of the middle niche. Their areas give the same signed
curve bound as Baek's smooth proof.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality

namespace MovingSofaStability

/-- Core-area lower bound under the exact geometric hypotheses used locally. -/
theorem positive_core_area_le {φ c : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set Point} (hK : IsCap K (π / 2))
    (hcore : CoreArmMargin K φ (π / 2 - φ) c) (hc : 0 < c)
    (hsep : CutSeparated φ K)
    (hheight : ∀ t ∈ Icc φ (π / 2 - φ), 0 < (innerCorner K t).2) :
    segArea (wRight φ K) (xRight φ K) + curveArea (innerCorner K) φ (π / 2 - φ) +
      segArea (xLeft φ K) (zLeft φ K) ≤
      area ((niche K (π / 2) \ hRight φ K) \ hLeft φ K) := by
  have hpi := pi_pos
  have hφ0 := hφ.1
  have hφ4 := hφ.2
  have hcos : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsin : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  have hab : φ < π / 2 - φ := by linarith
  have hbv : π / 2 - φ < π / 2 := by linarith
  set b := π / 2 - φ with hb
  set τ := sin φ / cos φ with hτ_def
  set w := (supp K φ - 1) / cos φ with hw_def
  set z := (1 - supp K (π - φ)) / cos φ with hz_def
  set XR := (innerCorner K φ).1
  set YR := (innerCorner K φ).2
  set XL := (innerCorner K b).1
  set YL := (innerCorner K b).2
  have hτ : 0 < τ := div_pos hsin hcos
  have hYR : 0 < YR := hheight φ ⟨le_rfl, hab.le⟩
  have hYL : 0 < YL := hheight b ⟨hab.le, le_rfl⟩
  have hanti := hcore.strictAnti_core hK hc hφ0.le hbv.le
  have hX : XL < XR := hanti ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
  have hw : w = XR + YR * τ := by
    have he := (cn_innerCorner_dot K φ).1
    simp only [dot, uvec] at he
    rw [hw_def, hτ_def, div_eq_iff hcos.ne', add_mul, mul_assoc, div_mul_cancel₀ _ hcos.ne']
    linarith
  have hz : z = XL - YL * τ := by
    have he := opt_innerCorner_dot_v K b
    have hsb : sin b = cos φ := by rw [hb, sin_pi_div_two_sub]
    have hcb : cos b = sin φ := by rw [hb, cos_pi_div_two_sub]
    rw [show b + π / 2 = π - φ by rw [hb]; ring] at he
    simp only [dot, vvec, hsb, hcb] at he
    rw [hz_def, hτ_def, div_eq_iff hcos.ne', sub_mul, mul_assoc, div_mul_cancel₀ _ hcos.ne']
    linarith
  let C : Set Point := (fun q : Point => ((innerCorner K q.1).1, (innerCorner K q.1).2 - q.2)) ''
    {q : Point | q.1 ∈ Ioo φ b ∧ 0 < q.2 ∧ q.2 < (innerCorner K q.1).2}
  let R : Set Point := {p | 0 < p.2 ∧ p.2 < YR ∧ XR + 0 * p.2 < p.1 ∧ p.1 < w + -τ * p.2}
  let L : Set Point := {p | 0 < p.2 ∧ p.2 < YL ∧ z + τ * p.2 < p.1 ∧ p.1 < XL + 0 * p.2}
  let I : ℝ := ∫ t in φ..b, -(cornerRightVelocity K t).1 * (innerCorner K t).2
  have hI : 0 ≤ I := by
    dsimp only [I]
    rw [intervalIntegral.integral_of_le hab.le]
    apply setIntegral_nonneg measurableSet_Ioc
    intro t ht
    have ht' : t ∈ Icc φ b := ⟨ht.1.le, ht.2⟩
    have hv := hcore.velocity_fst_le hK hc.le ht'
      ⟨hφ0.le.trans ht.1.le, ht.2.trans hbv.le⟩
    exact mul_nonneg (by linarith) (hheight t ht').le
  have vC : volume C = ENNReal.ofReal I := by
    simpa only [add_zero] using volume_under_core_graph hK hab hcore hc hφ0.le hbv.le
      (H := 0) (by simpa only [add_zero] using hheight)
  have vR : volume R = ENNReal.ofReal (τ * YR ^ 2 / 2) := by
    have hn : ∀ y ∈ Ioo (0 : ℝ) YR, XR + 0 * y ≤ w + -τ * y := by
      intro y hy
      rw [hw]
      nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr hy.2.le)]
    rw [opt_volume_hregion hYR.le hn, hw]
    congr 1
    ring
  have vL : volume L = ENNReal.ofReal (τ * YL ^ 2 / 2) := by
    have hn : ∀ y ∈ Ioo (0 : ℝ) YL, z + τ * y ≤ XL + 0 * y := by
      intro y hy
      rw [hz]
      nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr hy.2.le)]
    rw [opt_volume_hregion hYL.le hn, hz]
    congr 1
    ring
  have hCfst : ∀ p ∈ C, XL < p.1 ∧ p.1 < XR := by
    rintro p ⟨⟨t, s⟩, ⟨ht, -, -⟩, rfl⟩
    exact ⟨hanti ⟨ht.1.le, ht.2.le⟩ ⟨hab.le, le_rfl⟩ ht.2,
      hanti ⟨le_rfl, hab.le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1⟩
  have hdisjR : Disjoint C R := Set.disjoint_left.mpr fun p hp hq => by
    have hx := hCfst p hp
    have hr := hq.2.2.1
    linarith
  have hdisjL : Disjoint (C ∪ R) L := Set.disjoint_left.mpr fun p hp hq => by
    have hl := hq.2.2.2
    rcases hp with hp | hp
    · have hx := hCfst p hp; linarith
    · have hr := hp.2.2.1; linarith
  have hopen : ∀ a b A B D E : ℝ,
      IsOpen {p : Point | a < p.2 ∧ p.2 < b ∧ A + B * p.2 < p.1 ∧ p.1 < D + E * p.2} := by
    intro a b A B D E
    exact (isOpen_lt continuous_const continuous_snd).inter
      ((isOpen_lt continuous_snd continuous_const).inter
        ((isOpen_lt (by fun_prop) continuous_fst).inter (isOpen_lt continuous_fst (by fun_prop))))
  have vUnion : volume (C ∪ R ∪ L) = volume C + volume R + volume L := by
    rw [measure_union hdisjL (hopen 0 YL z τ XL 0).measurableSet,
      measure_union hdisjR (hopen 0 YR XR 0 w (-τ)).measurableSet]
  have hsub : C ∪ R ∪ L ⊆ (niche K (π / 2) \ hRight φ K) \ hLeft φ K := by
    intro p hp
    have key : 0 ≤ p.2 ∧ p ∉ hRight φ K ∧ p ∉ hLeft φ K ∧
        ∃ t ∈ Ioo (0 : ℝ) (π / 2), p ∈ qMinus K t := by
      rcases hp with (hp | hp) | hp
      · obtain ⟨⟨t, s⟩, ⟨ht, hs0, hsY⟩, rfl⟩ := hp
        obtain ⟨hR, hL, hq⟩ := separated_core_below hφ hsep ht hs0
        exact ⟨by dsimp only; linarith, hR, hL,
          t, ⟨hφ0.trans ht.1, ht.2.trans hbv⟩, hq⟩
      · obtain ⟨hy0, hyR, hxR, hxw⟩ := hp
        have hR : p ∉ hRight φ K := (opt_notMem_hRight_iff hcos K p).2 (by linarith)
        obtain ⟨hL, hq⟩ := separated_right_triangle hφ hsep (by linarith) hyR hR
        exact ⟨hy0.le, hR, hL, φ, ⟨hφ0, by linarith⟩, hq⟩
      · obtain ⟨hy0, hyL, hxz, hxL⟩ := hp
        have hL : p ∉ hLeft φ K := (opt_notMem_hLeft_iff hcos K p).2 (by linarith)
        obtain ⟨hR, hq⟩ := separated_left_triangle hφ hsep (by linarith) hyL hL
        exact ⟨hy0.le, hR, hL, b, ⟨by linarith, hbv⟩, hq⟩
    obtain ⟨hy0, hR, hL, t, ht, hq⟩ := key
    refine ⟨⟨⟨?_, mem_iUnion₂.mpr ⟨t, ht, hq⟩⟩, hR⟩, hL⟩
    simpa [fan, halfPlus, dot_uvec_pi_div_two] using hy0
  have hfinite : volume ((niche K (π / 2) \ hRight φ K) \ hLeft φ K) ≠ ⊤ :=
    volume_ne_top_of_subset (sdiff_subset.trans sdiff_subset)
      (nef_niche_isBounded hK).measure_lt_top.ne
  have harea := area_mono_of_finite hsub hfinite
  have aUnion : area (C ∪ R ∪ L) = I + τ * YR ^ 2 / 2 + τ * YL ^ 2 / 2 := by
    unfold area
    rw [vUnion, vC, vR, vL,
      ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
        ENNReal.ofReal_ne_top,
      ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hI, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)]
  have hCA := core_curveArea_rightVelocity hK hab.le
  have hsegR : segArea (wRight φ K) (xRight φ K) = w * YR / 2 := by
    simp only [opt_wRight_eq, xRight, segArea, cross]
    ring
  have hsegL : segArea (xLeft φ K) (zLeft φ K) = -YL * z / 2 := by
    simp only [opt_zLeft_eq, xLeft, segArea, cross]
    ring
  rw [hsegR, hsegL, hCA]
  have he : w * YR / 2 + ((XL * YL - XR * YR) / 2 + I) + -YL * z / 2 = area (C ∪ R ∪ L) := by
    rw [aUnion, hw, hz]
    ring
  rw [he]
  exact harea

end MovingSofaStability
