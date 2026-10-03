module

public import MovingSofa.Injectivity.DiscreteIneq

/-!
# Curvature estimates for penalized polygon maximizers

The inner-ray geometry in the proof of Theorem 6.3.3 does not require
maximality or balancedness. We first extract its estimate for tau, rather than
replacing tau by sigma. A one-sided defect sigma<=tau+e is then sufficient for

  sigma(t) <= k0(gPlus(t))*delta + (D+4)*delta^2 + e.

Here D is an arbitrary uniform arm bound. Thus the diameter bound for specially
chosen exact maximizers is not applied to the specified-cap approximations.
The geometric proof follows `inj_sigmaAt_le_geom`, retaining its endpoint and
zero-measure singleton cases but removing its use of Theorem 3.4.9.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofa

namespace SofaUniqueness

/-- The inner-ray estimate holds for every polygon cap. -/
theorem polygon_tau_le_geom {k : ℕ} {K : Set (ℝ × ℝ)}
    (hKp : IsPolygonCap (rightAngleSet k) K)
    {t : ℝ} (ht : t ∈ (rightAngleSet k).angles) :
    tau (rightAngleSet k) K t ≤
      max (max (tan (stepSize k) * (gMinus K t - 1 + tan (stepSize k / 2)))
        (tan (stepSize k) * (1 - gPlus K t + tan (stepSize k / 2)))) 0 +
      max (2 * tan (stepSize k / 2) - sigmaAt K t) 0 := by
  obtain ⟨hc, hs, htan, hT0, hT⟩ := inj_step_trig k
  have htI := (rightAngleSet k).subset t ht
  simp only [inj_rightAngleSet_ω] at htI
  have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [htI.1, pi_pos], htI.2⟩
  have hlen := (lemma3_4_5_one hKp ht).2.1
  set s₀ := supp K (t + π / 2) - 1 with hs₀
  set s₁ := (supp K (t + π / 2 - stepSize k) - 1 - (supp K t - 1) * sin (stepSize k)) /
    cos (stepSize k) with hs₁
  set s₁' := (supp K (t + π / 2 + stepSize k) - 1 + (supp K t - 1) * sin (stepSize k)) /
    cos (stepSize k) with hs₁'
  set sp := (supp K (t + stepSize k) - 1 - (supp K t - 1) * cos (stepSize k)) / sin (stepSize k)
    with hsp
  set sm := ((supp K t - 1) * cos (stepSize k) - supp K (t - stepSize k) + 1) / sin (stepSize k)
    with hsm
  set z₀ := -((supp K t - 1) * sin t) / cos t with hz₀
  set Q := {s : ℝ | (supp K t - 1) • uvec t + s • vvec t ∈
    frontier (polyNiche (rightAngleSet k) K) ∩ wallBVec K t} with hQ
  have hτ : tau (rightAngleSet k) K t = (volume Q).toReal := by
    rw [← hlen, lineLength]
  have hincl : Q ⊆ ((Icc (min s₁ s₁') s₀ ∪ {s₀}) ∪ Icc sp sm) ∪ {z₀} := by
    intro s hsQ
    obtain ⟨hxF, hxW⟩ := hsQ
    have hsW : s ≤ s₀ := inj_mem_wallBVec.1 hxW
    by_cases hD1 : (supp K t - 1) • uvec t + s • vvec t ∈ halfD K (t - stepSize k)
    · have : s ∈ Icc s₁ s₀ := by
        rw [← inj_param_minus hc]
        exact ⟨hxW, hD1⟩
      exact Or.inl (Or.inl (Or.inl ⟨le_trans (min_le_left _ _) this.1, this.2⟩))
    by_cases hD2 : (supp K t - 1) • uvec t + s • vvec t ∈ halfD K (t + stepSize k)
    · have : s ∈ Icc s₁' s₀ := by
        rw [← inj_param_plus hc]
        exact ⟨hxW, hD2⟩
      exact Or.inl (Or.inl (Or.inl ⟨le_trans (min_le_right _ _) this.1, this.2⟩))
    by_cases hD0 : (supp K t - 1) • uvec t + s • vvec t ∈ halfD K t
    · rw [inj_mem_halfD, sub_self, sin_zero, cos_zero] at hD0
      exact Or.inl (Or.inl (Or.inr (le_antisymm hsW (by linarith))))
    have hx2 := inj_frontier_niche_snd (inj_rightAngleSet_ω k) hxF
    have hx2e : ((supp K t - 1) • uvec t + s • vvec t).2 = (supp K t - 1) * sin t + s * cos t := by
      simp [uvec, vvec]
    rcases hx2.lt_or_eq with hx2 | hx2
    · left
      right
      have hB : ∀ u, (u ∈ (rightAngleSet k).angles ∨ u = 0 ∨ u = π / 2) →
          (supp K t - 1) • uvec t + s • vvec t ∉ halfD K u →
          (supp K t - 1) • uvec t + s • vvec t ∈ halfB K u := by
        intro u hu hnD
        have hq := inj_not_mem_qMinus hKp hxF hx2 hu
        rw [proposition2_2_2_qMinus] at hq
        simp only [mem_inter_iff, halfMinusOpen, mem_ofPred_eq, not_and_or, not_lt] at hq
        rcases hq with hq | hq
        · exact hq
        · exact absurd hq hnD
      have h1 := hB (t + stepSize k) ((inj_angles_succ ht).elim Or.inl (fun h => Or.inr (Or.inr h))) hD2
      have h2 := hB (t - stepSize k) ((inj_angles_pred ht).elim Or.inl (fun h => Or.inr (Or.inl h))) hD1
      rw [inj_mem_halfB] at h1 h2
      have e1 : t - (t + stepSize k) = -stepSize k := by ring
      have e2 : t + stepSize k - t = stepSize k := by ring
      have e3 : t - (t - stepSize k) = stepSize k := by ring
      have e4 : t - stepSize k - t = -stepSize k := by ring
      rw [e1, e2, cos_neg] at h1
      rw [e3, e4, sin_neg] at h2
      constructor
      · rw [hsp, div_le_iff₀ hs]
        linarith
      · rw [hsm, le_div_iff₀ hs]
        linarith
    · right
      rw [mem_singleton_iff, hz₀, eq_div_iff hct.ne']
      rw [hx2e] at hx2
      linarith
  have hvol : volume Q ≤ ENNReal.ofReal (s₀ - min s₁ s₁') + ENNReal.ofReal (sm - sp) := by
    calc
      volume Q ≤ volume (((Icc (min s₁ s₁') s₀ ∪ {s₀}) ∪ Icc sp sm) ∪ {z₀}) := measure_mono hincl
      _ ≤ volume ((Icc (min s₁ s₁') s₀ ∪ {s₀}) ∪ Icc sp sm) + volume ({z₀} : Set ℝ) :=
        measure_union_le _ _
      _ ≤ (volume (Icc (min s₁ s₁') s₀) + volume ({s₀} : Set ℝ)) + volume (Icc sp sm) + 0 := by
        rw [measure_singleton]
        gcongr
        exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ = ENNReal.ofReal (s₀ - min s₁ s₁') + ENNReal.ofReal (sm - sp) := by
        rw [measure_singleton, Real.volume_Icc, Real.volume_Icc, add_zero, add_zero]
  have hreal : tau (rightAngleSet k) K t ≤ max (s₀ - min s₁ s₁') 0 + max (sm - sp) 0 := by
    rw [hτ]
    calc
      (volume Q).toReal ≤ (ENNReal.ofReal (s₀ - min s₁ s₁') + ENNReal.ofReal (sm - sp)).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩) hvol
      _ = _ := by
        rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
          ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  rw [← max_sub_sub_left, inj_param_minus_length hKp ht, inj_param_plus_length hKp ht,
    inj_polygon_sigmaAt_eq hKp ht] at hreal
  exact hreal

/-- Robust version of the discrete curvature estimate, with an arbitrary arm
bound and an explicit nonnegative stationarity error. -/
theorem polygon_curvature_with_defect {k : ℕ} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap (rightAngleSet k) K)
    {t D e : ℝ} (ht : t ∈ (rightAngleSet k).angles)
    (hD : 0 ≤ D) (hgD : gPlus K t ≤ D) (he : 0 ≤ e)
    (hdefect : sigmaAt K t ≤ tau (rightAngleSet k) K t + e) :
    sigmaAt K t ≤ k0 (gPlus K t) * stepSize k + (D + 4) * stepSize k ^ 2 + e := by
  have hgeom := polygon_tau_le_geom hK ht
  have hKc : IsConvexBody K := hK.1.2.1
  have hg0 : 0 ≤ gPlus K t := (inj_arm_nonneg hKc t).2.2.1
  have hgmp : gMinus K t ≤ gPlus K t := by
    have h := (proposition2_1_2 hKc (t + π / 2)).2
    have hσ0 : 0 ≤ sigmaAt K (t + π / 2) := ENNReal.toReal_nonneg
    rw [gMinus, gPlus, dot_sub_left, dot_sub_left, cPlus, cMinus, h,
      dot_add_left, dot_smul_left, vvec_add_pi_div_two, dot_neg_left, dot_uvec_self]
    linarith
  have hδ := inj_stepSize_pos k
  have hδ4 := inj_stepSize_le k
  have hδ1 : stepSize k ≤ 1 := by linarith [pi_le_four]
  obtain ⟨_, _, htan0, hT0, _⟩ := inj_step_trig k
  have htan := inj_tan_le hδ.le hδ4
  have hT := inj_tan_le (x := stepSize k / 2) (by linarith) (by linarith)
  set δ := stepSize k
  set T := tan (δ / 2)
  set M := |gPlus K t - 1|
  have hM0 : 0 ≤ M := abs_nonneg _
  have hMD : M ≤ D + 1 := by
    rw [show M = |gPlus K t - 1| from rfl, abs_le]
    constructor <;> linarith
  have hMg : gMinus K t - 1 ≤ M := (by linarith : gMinus K t - 1 ≤ gPlus K t - 1).trans
    (le_abs_self (gPlus K t - 1))
  have hMg' : 1 - gPlus K t ≤ M := by
    change 1 - gPlus K t ≤ |gPlus K t - 1|
    rw [abs_sub_comm]
    exact le_abs_self _
  have hfirst : max (max (tan δ * (gMinus K t - 1 + T))
      (tan δ * (1 - gPlus K t + T))) 0 ≤ δ * M + (D + 3) * δ ^ 2 := by
    have hTδ : T ≤ δ := by nlinarith
    have hprod : tan δ * (M + T) ≤ (δ + δ ^ 2) * (M + δ) :=
      mul_le_mul htan (by linarith) (by positivity) (by positivity)
    have hrest : (δ + δ ^ 2) * (M + δ) ≤ δ * M + (D + 3) * δ ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hMD (sq_nonneg δ)
      have hcube := mul_le_mul_of_nonneg_right hδ1 (sq_nonneg δ)
      nlinarith
    have hb := hprod.trans hrest
    refine max_le (max_le ?_ ?_) (by positivity)
    · exact (mul_le_mul_of_nonneg_left (by linarith : gMinus K t - 1 + T ≤ M + T) htan0.le).trans hb
    · exact (mul_le_mul_of_nonneg_left (by linarith : 1 - gPlus K t + T ≤ M + T) htan0.le).trans hb
  have hk : M ≤ k0 (gPlus K t) := le_max_left _ _
  have hk' : (M + 1) / 2 ≤ k0 (gPlus K t) := le_max_right _ _
  have hkδ := mul_le_mul_of_nonneg_left hk hδ.le
  have hkδ' := mul_le_mul_of_nonneg_left hk' hδ.le
  rcases le_total (2 * T - sigmaAt K t) 0 with hcase | hcase
  · change tau (rightAngleSet k) K t ≤ _ + max (2 * T - sigmaAt K t) 0 at hgeom
    rw [max_eq_right hcase] at hgeom
    nlinarith [sq_nonneg δ]
  · change tau (rightAngleSet k) K t ≤ _ + max (2 * T - sigmaAt K t) 0 at hgeom
    rw [max_eq_left hcase] at hgeom
    have hDsq := mul_nonneg (show 0 ≤ D + 4 by linarith) (sq_nonneg δ)
    nlinarith [sq_nonneg δ]

end SofaUniqueness
