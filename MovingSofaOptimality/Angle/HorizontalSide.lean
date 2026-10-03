module

public import MovingSofaOptimality.Balanced.BalancedMaximumSofa
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Horizontal side lengths (§4.1)

Definition 4.1.1 (`def:wedge-gap-infimum`), Lemma 4.1.1 (`lem:wedge-gap-limit`), Theorem 4.1.2
(`thm:balanced-polygon-sofa-ineq`), Theorem 4.1.3 (`thm:surface-area-weak-convergence`, Schneider
Theorem 4.2.1) and Theorem 4.1.4 (`thm:balanced-maximum-sofa-ineq`).

**Proofs.** Theorem 4.1.2 bounds the part of the polygon niche on the `x`-axis (Lemma 3.4.5 (2))
by the wedge endpoints `W_K(t)`, `t ∈ Θ`, and uses balancedness (Theorem 3.4.9); the `z`-part is
the same argument on the line `l(ω, 0)` (instead of the mirror symmetry used in the paper), and the
`z`-part of Theorem 4.1.4 uses the analogue of Lemma 4.1.1 for the left wedge gaps. Theorem 4.1.3
is proved by integration by parts against the Stieltjes function `sigmaFun` for `C¹` integrands,
dominated convergence (the vertices `v_{K_n}⁺(t)` converge at every `t` where `K` has no edge) and
uniform approximation by averages over short intervals. Theorem 4.1.4 uses the upper
semicontinuity of edge lengths directly: `σ_K(t) sin δ ≤ h_K(t + δ) + h_K(t - δ) - 2 h_K(t) cos δ`,
and the right-hand side divided by `sin δ` tends to `σ_K(t)` as `δ → 0⁺`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace MovingSofaOptimality

/-- `w_K° = inf_{t ∈ (0, ω)} w_K(t)` (Definition 4.1.1, `def:wedge-gap-infimum`). -/
noncomputable def wedgeGapWInf (K : Set (ℝ × ℝ)) (ω : ℝ) : ℝ := ⨅ t : Ioo 0 ω, wedgeGapW K t

/-- `z_K° = inf_{t ∈ (0, ω)} z_K(t)` (Definition 4.1.1). -/
noncomputable def wedgeGapZInf (K : Set (ℝ × ℝ)) (ω : ℝ) : ℝ := ⨅ t : Ioo 0 ω, wedgeGapZ K ω t

/-! ### Helper lemmas -/

/-! ### Caps -/

/-- A point lies in a half-plane intersection if it lies in the supporting half-planes of the
normal angles. -/
lemma ang_mem_of_halfPlaneInter {K : Set (ℝ × ℝ)} {A : Set ℝ} (hK : IsHalfPlaneInter K A)
    (hne : K.Nonempty) {q : ℝ × ℝ} (hq : ∀ t ∈ A, dot q (uvec t) ≤ supp K t) : q ∈ K := by
  obtain ⟨ι, t, c, ht, rfl⟩ := hK
  refine mem_iInter.2 fun i => ?_
  have h1 : supp (⋂ i, halfMinus (t i) (c i)) (t i) ≤ c i :=
    supp_le_of_forall hne fun p hp => mem_iInter.1 hp i
  exact (hq (t i) (ht i)).trans h1

/-- `cos ω > 0` for a rotation angle `ω ∈ (0, π/2)`. -/
lemma ang_cos_pos_of_cap {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) (hω2 : ω < π / 2) : 0 < cos ω :=
  cos_pos_of_mem_Ioo ⟨by linarith [hω.1, pi_pos], hω2⟩

/-- The support function of a cap with `ω < π/2` is nonnegative at the normal angles `jSet ω` and
`ω + π`, `3π/2` of its defining half-planes. -/
lemma ang_cap_supp_nonneg {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (hω : ω < π / 2) {t : ℝ}
    (ht : t ∈ jSet ω ∪ {ω + π, 3 * π / 2}) : 0 ≤ supp K t := by
  have hcos := ang_cos_pos_of_cap hK.1 hω
  have hω0 := hK.1.1
  have hc := hK.2.1.2.1
  have hne := hK.2.1.1
  rcases ht with (ht | ht) | ht
  · -- `t ∈ [0, ω]`: a point of `K` on the `x`-axis
    obtain ⟨p, hp, hpt⟩ := exists_dot_eq_supp hc hne (3 * π / 2)
    rw [hK.2.2.2.2.2.1, dot_uvec_three_pi_div_two] at hpt
    have hp2 : p.2 = 0 := by linarith
    have h3 := (mem_para_iff.1 (hK.subset_para hp)).2.1
    simp only [dot, uvec, hp2, zero_mul, add_zero] at h3
    have hp1 : 0 ≤ p.1 := by
      by_contra h; rw [not_le] at h; nlinarith
    have hct : 0 ≤ cos t := cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
    calc (0 : ℝ) ≤ dot p (uvec t) := by simp only [dot, uvec, hp2, zero_mul, add_zero]; positivity
      _ ≤ supp K t := dot_le_supp hc hp t
  · -- `t ∈ [π/2, ω + π/2]`: a point of `K` on the line `l(ω, 0)`
    obtain ⟨p, hp, hpt⟩ := exists_dot_eq_supp hc hne (ω + π)
    rw [hK.2.2.2.2.1, dot_uvec_add_pi] at hpt
    have h0 : p.1 * cos ω + p.2 * sin ω = 0 := by simp only [dot, uvec] at hpt; linarith
    have hp2 := (mem_para_iff.1 (hK.subset_para hp)).1.1
    have hs : 0 ≤ sin (t - ω) := sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1])
      (by linarith [ht.2, hω0])
    have key : dot p (uvec t) * cos ω = p.2 * sin (t - ω) := by
      simp only [dot, uvec, sin_sub]; linear_combination (cos t) * h0
    have : 0 ≤ dot p (uvec t) := by
      by_contra h; rw [not_le] at h; nlinarith [mul_nonneg hp2 hs]
    exact this.trans (dot_le_supp hc hp t)
  · rcases ht with ht | ht
    · rw [ht, hK.2.2.2.2.1]
    · rw [ht, hK.2.2.2.2.2.1]

/-- The origin `O` lies in a cap with `ω < π/2`. -/
lemma ang_cap_origin_mem {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (hω : ω < π / 2) :
    ((0 : ℝ), (0 : ℝ)) ∈ K :=
  ang_mem_of_halfPlaneInter hK.2.2.2.2.2.2 hK.2.1.1 fun _ ht => by
    simpa [dot] using ang_cap_supp_nonneg hK hω ht

/-- The corner `(h_K(0), 0)` lies in a cap with `ω < π/2`. -/
lemma ang_cap_corner_mem {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (hω : ω < π / 2) :
    (supp K 0, (0 : ℝ)) ∈ K := by
  have hcos := ang_cos_pos_of_cap hK.1 hω
  have hω0 := hK.1.1
  have hc := hK.2.1.2.1
  have hne := hK.2.1.1
  have h00 : 0 ≤ supp K 0 := ang_cap_supp_nonneg hK hω (Or.inl (Or.inl ⟨le_rfl, hω0.le⟩))
  refine ang_mem_of_halfPlaneInter hK.2.2.2.2.2.2 hne fun t ht => ?_
  rcases ht with (ht | ht) | ht
  · obtain ⟨p, hp, hpt⟩ := exists_dot_eq_supp hc hne 0
    rw [dot_uvec_zero] at hpt
    have hp2 := (mem_para_iff.1 (hK.subset_para hp)).1.1
    have hst : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, pi_pos])
    calc dot (supp K 0, (0 : ℝ)) (uvec t) ≤ dot p (uvec t) := by
          simp only [dot, uvec, ← hpt, zero_mul, add_zero]; nlinarith [mul_nonneg hp2 hst]
      _ ≤ supp K t := dot_le_supp hc hp t
  · have hct : cos t ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le ht.1 (by linarith [ht.2, pi_pos])
    calc dot (supp K 0, (0 : ℝ)) (uvec t) ≤ 0 := by
          simp only [dot, uvec, zero_mul, add_zero]; nlinarith
      _ ≤ supp K t := ang_cap_supp_nonneg hK hω (Or.inl (Or.inr ht))
  · rcases ht with ht | ht
    · rw [ht, hK.2.2.2.2.1, dot_uvec_add_pi]
      simp only [dot, uvec, zero_mul, add_zero]; nlinarith
    · rw [ht, hK.2.2.2.2.2.1, dot_uvec_three_pi_div_two]; simp

/-- `tan(π/4 - ω/2) cos ω = 1 - sin ω`. -/
lemma ang_tan_mul_cos (ω : ℝ) (h : cos (π / 4 - ω / 2) ≠ 0) :
    tan (π / 4 - ω / 2) * cos ω = 1 - sin ω := by
  have e : (π / 2 - ω) / 2 = π / 4 - ω / 2 := by ring
  have := tan_half_mul_sin (δ := π / 2 - ω) (by rwa [e])
  rwa [e, sin_pi_div_two_sub, cos_pi_div_two_sub] at this

/-- `cos(π/4 - ω/2) > 0` for `ω ∈ [0, π/2]`. -/
lemma ang_cos_quarter_pos {ω : ℝ} (hω : ω ∈ Icc 0 (π / 2)) : 0 < cos (π / 4 - ω / 2) :=
  cos_pos_of_mem_Ioo ⟨by linarith [hω.2, pi_pos], by linarith [hω.1, pi_pos]⟩

/-! ### Wedge gaps -/

/-- `w_K(t) = h_K(0) - (h_K(t) - 1) / cos t`. -/
lemma ang_wedgeGapW_eq (K : Set (ℝ × ℝ)) (t : ℝ) :
    wedgeGapW K t = supp K 0 - (supp K t - 1) / cos t := by
  simp only [wedgeGapW, aMinus, wedgeW, dot_sub_left, dot_vminus_uvec]
  simp [dot, uvec]

lemma ang_cos_pos_of_mem_Icc {ω t : ℝ} (hω : ω < π / 2) (ht : t ∈ Icc 0 ω) : 0 < cos t :=
  cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩

/-- `w_K` is continuous on `[0, ω]`. -/
lemma ang_continuousOn_wedgeGapW {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {ω : ℝ}
    (hω : ω < π / 2) : ContinuousOn (wedgeGapW K) (Icc 0 ω) := by
  rw [funext (ang_wedgeGapW_eq K)]
  exact continuousOn_const.sub (((continuous_supp hK.2.1).sub continuous_const).continuousOn.div
    continuous_cos.continuousOn fun t ht => (ang_cos_pos_of_mem_Icc hω ht).ne')

lemma ang_bddBelow_wedgeGapW {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {ω : ℝ}
    (hω : ω < π / 2) : BddBelow (range fun t : Ioo 0 ω => wedgeGapW K t) := by
  refine (isCompact_Icc.bddBelow_image (ang_continuousOn_wedgeGapW hK hω)).mono ?_
  rintro _ ⟨t, rfl⟩
  exact ⟨t, Ioo_subset_Icc_self t.2, rfl⟩

/-- `w_K° ≤ w_K(t)` for `t ∈ (0, ω)`. -/
lemma ang_wedgeGapWInf_le {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {ω t : ℝ}
    (hω : ω < π / 2) (ht : t ∈ Ioo 0 ω) : wedgeGapWInf K ω ≤ wedgeGapW K t :=
  ciInf_le (ang_bddBelow_wedgeGapW hK hω) ⟨t, ht⟩

/-- A lower bound of `w_K` on `(0, ω)` is a lower bound of `w_K°`. -/
lemma ang_le_wedgeGapWInf {K : Set (ℝ × ℝ)} {ω a : ℝ} (hω : 0 < ω)
    (h : ∀ t ∈ Ioo 0 ω, a ≤ wedgeGapW K t) : a ≤ wedgeGapWInf K ω := by
  have : Nonempty (Ioo 0 ω) := ⟨⟨ω / 2, by constructor <;> linarith⟩⟩
  exact le_ciInf fun t => h t t.2

/-- `w_K° ≤ h_K(0)`: the wedge gap `w_K(t)` tends to `w_K(ω) = h_K(0)` as `t → ω⁻`. -/
lemma ang_wedgeGapWInf_le_supp_zero {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω)
    (hω : ω < π / 2) : wedgeGapWInf K ω ≤ supp K 0 := by
  have hω0 := hK.1.1
  have htend : Tendsto (wedgeGapW K) (𝓝[<] ω) (𝓝 (supp K 0)) := by
    have := ((ang_continuousOn_wedgeGapW hK.2.1 hω ω ⟨hω0.le, le_rfl⟩).mono
      Ioo_subset_Icc_self).tendsto
    rwa [nhdsWithin_Ioo_eq_nhdsLT hω0, ang_wedgeGapW_eq, hK.2.2.1, sub_self, zero_div,
      sub_zero] at this
  refine ge_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsLT hω0] with t ht using ang_wedgeGapWInf_le hK.2.1 hω ht

/-! ### The left wedge gaps -/

/-- `z_K(t) = h_K(ω + π/2) - (h_K(t + π/2) - 1) / cos (ω - t)`. -/
lemma ang_wedgeGapZ_eq (K : Set (ℝ × ℝ)) (ω t : ℝ) :
    wedgeGapZ K ω t = supp K (ω + π / 2) - (supp K (t + π / 2) - 1) / cos (ω - t) := by
  simp only [wedgeGapZ, cPlus, wedgeZ, dot_sub_left, dot_smul_left, dot_vvec_self, mul_one]
  rw [← uvec_add_pi_div_two, dot_vplus_uvec]

lemma ang_cos_sub_pos_of_mem_Icc {ω t : ℝ} (hω : ω < π / 2) (ht : t ∈ Icc 0 ω) :
    0 < cos (ω - t) :=
  cos_pos_of_mem_Ioo ⟨by linarith [ht.2, pi_pos, ht.1], by linarith [ht.1]⟩

/-- `z_K` is continuous on `[0, ω]`. -/
lemma ang_continuousOn_wedgeGapZ {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {ω : ℝ}
    (hω : ω < π / 2) : ContinuousOn (wedgeGapZ K ω) (Icc 0 ω) := by
  have hnum : Continuous fun t => supp K (t + π / 2) - 1 :=
    ((continuous_supp hK.2.1).comp (continuous_id.add continuous_const)).sub continuous_const
  rw [funext (ang_wedgeGapZ_eq K ω)]
  exact continuousOn_const.sub (hnum.continuousOn.div
    (continuous_cos.comp (continuous_const.sub continuous_id)).continuousOn
    fun t ht => (ang_cos_sub_pos_of_mem_Icc hω ht).ne')

lemma ang_bddBelow_wedgeGapZ {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {ω : ℝ}
    (hω : ω < π / 2) : BddBelow (range fun t : Ioo 0 ω => wedgeGapZ K ω t) := by
  refine (isCompact_Icc.bddBelow_image (ang_continuousOn_wedgeGapZ hK hω)).mono ?_
  rintro _ ⟨t, rfl⟩
  exact ⟨t, Ioo_subset_Icc_self t.2, rfl⟩

/-- `z_K° ≤ z_K(t)` for `t ∈ (0, ω)`. -/
lemma ang_wedgeGapZInf_le {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {ω t : ℝ}
    (hω : ω < π / 2) (ht : t ∈ Ioo 0 ω) : wedgeGapZInf K ω ≤ wedgeGapZ K ω t :=
  ciInf_le (ang_bddBelow_wedgeGapZ hK hω) ⟨t, ht⟩

/-- `z_K° ≤ h_K(ω + π/2)`: the wedge gap `z_K(t)` tends to `z_K(0) = h_K(ω + π/2)` as `t → 0⁺`. -/
lemma ang_wedgeGapZInf_le_supp {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω)
    (hω : ω < π / 2) : wedgeGapZInf K ω ≤ supp K (ω + π / 2) := by
  have hω0 := hK.1.1
  have htend : Tendsto (wedgeGapZ K ω) (𝓝[>] 0) (𝓝 (supp K (ω + π / 2))) := by
    have := ((ang_continuousOn_wedgeGapZ hK.2.1 hω 0 ⟨le_rfl, hω0.le⟩).mono
      Ioo_subset_Icc_self).tendsto
    rwa [nhdsWithin_Ioo_eq_nhdsGT hω0, ang_wedgeGapZ_eq, zero_add, hK.2.2.2.1, sub_self,
      zero_div, sub_zero] at this
  refine ge_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsGT hω0] with t ht using ang_wedgeGapZInf_le hK.2.1 hω ht

/-! ### Lemma 4.1.1 -/

/-- Two functions on `(0, ω)` that are bounded below and differ by at most `c` at every point have
infima that differ by at most `c`. -/
lemma ang_abs_iInf_sub_iInf_le {ω c : ℝ} (hω : 0 < ω) {f g : Ioo (0 : ℝ) ω → ℝ}
    (hf : BddBelow (range f)) (hg : BddBelow (range g)) (h : ∀ t, |f t - g t| ≤ c) :
    |(⨅ t, f t) - ⨅ t, g t| ≤ c := by
  have : Nonempty (Ioo (0 : ℝ) ω) := ⟨⟨ω / 2, by constructor <;> linarith⟩⟩
  have h1 : (⨅ t, g t) - c ≤ ⨅ t, f t :=
    le_ciInf fun t => by linarith [ciInf_le hg t, (abs_le.1 (h t)).1]
  have h2 : (⨅ t, f t) - c ≤ ⨅ t, g t :=
    le_ciInf fun t => by linarith [ciInf_le hf t, (abs_le.1 (h t)).2]
  rw [abs_le]
  constructor <;> linarith

/-- The pointwise estimate behind Lemma 4.1.1: the wedge gaps `a - (b - 1) / c` and
`a' - (b' - 1) / c` differ by at most `(1 + sec ω) ε` when `|a - a'| ≤ ε`, `|b - b'| ≤ ε` and
`c ≥ cos ω > 0`. -/
lemma ang_abs_gap_sub_le {a a' b b' c ε ω : ℝ} (hcos : 0 < cos ω) (hc : cos ω ≤ c)
    (ha : |a - a'| ≤ ε) (hb : |b - b'| ≤ ε) :
    |(a - (b - 1) / c) - (a' - (b' - 1) / c)| ≤ (1 + 1 / cos ω) * ε := by
  have hc0 : 0 < c := hcos.trans_le hc
  have hε : 0 ≤ ε := (abs_nonneg _).trans ha
  calc |(a - (b - 1) / c) - (a' - (b' - 1) / c)| = |(a - a') - (b - b') / c| := by
        congr 1; ring
    _ ≤ |a - a'| + |(b - b') / c| := abs_sub _ _
    _ = |a - a'| + |b - b'| / c := by rw [abs_div, abs_of_pos hc0]
    _ ≤ ε + ε / c := by gcongr
    _ ≤ ε + ε / cos ω := by gcongr
    _ = (1 + 1 / cos ω) * ε := by ring

/-- **Lemma 4.1.1** (`lem:wedge-gap-limit`). For caps `K, K'` with rotation angle `ω < π/2` at
Hausdorff distance `ε`, `|w_K° - w_{K'}°| ≤ (1 + sec ω) ε`. -/
theorem lemma4_1_1 {K K' : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω < π / 2) (hK : IsCap K ω)
    (hK' : IsCap K' ω) :
    |wedgeGapWInf K ω - wedgeGapWInf K' ω| ≤ (1 + 1 / cos ω) * hausdorffDist K K' := by
  refine ang_abs_iInf_sub_iInf_le hK.1.1 (ang_bddBelow_wedgeGapW hK.2.1 hω)
    (ang_bddBelow_wedgeGapW hK'.2.1 hω) fun t => ?_
  rw [ang_wedgeGapW_eq, ang_wedgeGapW_eq]
  exact ang_abs_gap_sub_le (ang_cos_pos_of_cap hK.1 hω)
    (cos_le_cos_of_nonneg_of_le_pi t.2.1.le (by linarith [pi_pos]) t.2.2.le)
    (abs_supp_sub_le_hausdorffDist hK.2.1 hK'.2.1 _)
    (abs_supp_sub_le_hausdorffDist hK.2.1 hK'.2.1 _)

/-- The analogue of Lemma 4.1.1 for the left wedge gaps: `|z_K° - z_{K'}°| ≤ (1 + sec ω) ε`. -/
lemma ang_abs_wedgeGapZInf_sub_le {K K' : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω < π / 2) (hK : IsCap K ω)
    (hK' : IsCap K' ω) :
    |wedgeGapZInf K ω - wedgeGapZInf K' ω| ≤ (1 + 1 / cos ω) * hausdorffDist K K' := by
  refine ang_abs_iInf_sub_iInf_le hK.1.1 (ang_bddBelow_wedgeGapZ hK.2.1 hω)
    (ang_bddBelow_wedgeGapZ hK'.2.1 hω) fun t => ?_
  rw [ang_wedgeGapZ_eq, ang_wedgeGapZ_eq]
  exact ang_abs_gap_sub_le (ang_cos_pos_of_cap hK.1 hω)
    (cos_le_cos_of_nonneg_of_le_pi (by linarith [t.2.2]) (by linarith [pi_pos])
      (by linarith [t.2.1]))
    (abs_supp_sub_le_hausdorffDist hK.2.1 hK'.2.1 _)
    (abs_supp_sub_le_hausdorffDist hK.2.1 hK'.2.1 _)

/-! ### Edge lengths -/

/-- For two points `p, q` of the edge `e_K(t)`, `(q - p) · v_t ≤ σ_K(t)`: the edge has length
`σ_K(t)`. -/
lemma ang_dot_sub_le_sigmaAt {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {t : ℝ} {p q : ℝ × ℝ}
    (hp : p ∈ edge K t) (hq : q ∈ edge K t) : dot (q - p) (vvec t) ≤ sigmaAt K t := by
  rw [sigmaAt_eq_dot_sub hK, dot_sub_left]
  linarith [dot_le_dot_vplus hK.2.1 hq, dot_vminus_le_dot hK.2.1 hp]

/-- The bottom edge `e_K(3π/2)` of a cap contains `O` and `(h_K(0), 0)`, so it has length at least
`h_K(0)`. -/
lemma ang_supp_zero_le_sigmaAt {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (hω : ω < π / 2) :
    supp K 0 ≤ sigmaAt K (3 * π / 2) := by
  have hline : ∀ x : ℝ, (x, (0 : ℝ)) ∈ suppLine K (3 * π / 2) := fun x => by
    simp [suppLine, line, dot_uvec_three_pi_div_two, hK.2.2.2.2.2.1]
  have h := ang_dot_sub_le_sigmaAt hK.2.1 ⟨ang_cap_origin_mem hK hω, hline 0⟩
    ⟨ang_cap_corner_mem hK hω, hline _⟩
  simpa [vvec_three_pi_div_two, dot] using h

/-- The part of the polygon niche on the `x`-axis lies in `(0, max_Θ W_K(t))`. -/
lemma ang_lineLength_polyNiche_le {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hω : Θ.ω < π / 2) {W : ℝ}
    (hW : ∀ t ∈ Θ.angles, (supp K t - 1) / cos t ≤ W) :
    lineLength (π / 2) 0 (polyNiche Θ K) ≤ max W 0 := by
  have hcos : 0 < cos Θ.ω := ang_cos_pos_of_cap Θ.hω hω
  unfold lineLength
  have hsub : {s : ℝ | (0 : ℝ) • uvec (π / 2) + s • vvec (π / 2) ∈ polyNiche Θ K} ⊆
      Ioc (-W) 0 := by
    intro s hs
    simp only [mem_ofPred_eq, zero_smul, zero_add, vvec_pi_div_two] at hs
    obtain ⟨⟨hf1, -⟩, hU⟩ := hs
    simp only [halfPlus, mem_ofPred_eq, dot, uvec, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hf1
    obtain ⟨t, ht, hq⟩ := mem_iUnion₂.1 hU
    rw [proposition2_2_2_qMinus] at hq
    obtain ⟨hq1, -⟩ := hq
    simp only [halfMinusOpen, mem_ofPred_eq, dot, uvec, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hq1
    have htt := Θ.subset t ht
    have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [htt.1, pi_pos], by linarith [htt.2]⟩
    have hWt := hW t ht
    rw [div_le_iff₀ hct] at hWt
    constructor
    · by_contra h
      rw [not_lt] at h
      nlinarith [mul_le_mul_of_nonneg_right h hct.le]
    · by_contra h
      rw [not_le] at h
      nlinarith [mul_pos h hcos]
  calc (volume {s : ℝ | (0 : ℝ) • uvec (π / 2) + s • vvec (π / 2) ∈ polyNiche Θ K}).toReal
      ≤ (volume (Ioc (-W) 0)).toReal :=
        ENNReal.toReal_mono (by simp [Real.volume_Ioc]) (measure_mono hsub)
    _ = max W 0 := by rw [Real.volume_Ioc, ENNReal.toReal_ofReal']; ring_nf

/-- For a polygon cap with `ω < π/2`, `w_K° ≤ τ_K(π/2)`. By Lemma 3.4.5 (2), `h_K(0) - τ_K(π/2)` is
at most the length `max(max_Θ W, 0)` of the niche on the `x`-axis, `W = (h_K(t) - 1) / cos t`,
while `w_K° ≤ h_K(0) - max(max_Θ W, 0)`. -/
lemma ang_wedgeGapWInf_le_tau {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) :
    wedgeGapWInf K Θ.ω ≤ tau Θ K (π / 2) := by
  obtain ⟨t₀, ht₀, hmax⟩ :=
    Θ.angles.exists_max_image (fun t => (supp K t - 1) / cos t) Θ.nonempty
  have hℓ := ang_lineLength_polyNiche_le (K := K) hω hmax
  have h352 := (lemma3_4_5_two hK (t := π / 2) (Or.inr rfl)).2
  rw [show π / 2 + π = 3 * π / 2 by ring] at h352
  have hσ := ang_supp_zero_le_sigmaAt hK.1 hω
  have h1 := ang_wedgeGapWInf_le_supp_zero hK.1 hω
  have h2 := ang_wedgeGapWInf_le hK.1.2.1 hω (Θ.subset t₀ ht₀)
  rw [ang_wedgeGapW_eq] at h2
  rcases le_total ((supp K t₀ - 1) / cos t₀) 0 with hW | hW
  · rw [max_eq_right hW] at hℓ
    linarith
  · rw [max_eq_left hW] at hℓ
    linarith

/-- The `w`-part of Theorem 4.1.2: `ang_wedgeGapWInf_le_tau`, with `τ_K(π/2) = σ_K(π/2)` by
balancedness (Theorem 3.4.9). -/
lemma ang_theorem4_1_2_w {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap Θ K)
    (hω : Θ.ω < π / 2) : wedgeGapWInf K Θ.ω ≤ sigmaAt K (π / 2) :=
  (theorem3_4_9 hK (π / 2) (Or.inr (Or.inr rfl))) ▸ ang_wedgeGapWInf_le_tau hK.1 hω

/-- The edge `e_K(ω + π)` of a cap contains `O` and `h_K(ω + π/2) v_ω`, so it has length at least
`h_K(ω + π/2)`. -/
lemma ang_supp_le_sigmaAt_add_pi {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (hω : ω < π / 2) :
    supp K (ω + π / 2) ≤ sigmaAt K (ω + π) := by
  have hE1 : supp K (ω + π / 2) • vvec ω ∈ edge K (ω + π) := by
    refine ⟨hK.corner_mem, ?_⟩
    show dot (supp K (ω + π / 2) • vvec ω) (uvec (ω + π)) = supp K (ω + π)
    rw [hK.2.2.2.2.1, dot_smul_left, dot_uvec_add_pi, dot_vvec_uvec]; ring
  have hE0 : ((0 : ℝ), (0 : ℝ)) ∈ edge K (ω + π) := by
    refine ⟨ang_cap_origin_mem hK hω, ?_⟩
    show dot ((0 : ℝ), (0 : ℝ)) (uvec (ω + π)) = supp K (ω + π)
    rw [hK.2.2.2.2.1]; simp [dot]
  have h := ang_dot_sub_le_sigmaAt hK.2.1 hE1 hE0
  rwa [dot_sub_left, vvec_add_pi, dot_neg_right, dot_neg_right, dot_smul_left, dot_vvec_self,
    show dot ((0 : ℝ), (0 : ℝ)) (vvec ω) = 0 by simp [dot], neg_zero, mul_one, zero_sub,
    neg_neg] at h

/-- The part of the polygon niche on the line `l(ω, 0)` lies in `[0, max_Θ Z_K(t))`. -/
lemma ang_lineLength_polyNiche_le_z {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hω : Θ.ω < π / 2) {Z : ℝ}
    (hZ : ∀ t ∈ Θ.angles, (supp K (t + π / 2) - 1) / cos (Θ.ω - t) ≤ Z) :
    lineLength Θ.ω 0 (polyNiche Θ K) ≤ max Z 0 := by
  have hcos : 0 < cos Θ.ω := ang_cos_pos_of_cap Θ.hω hω
  unfold lineLength
  have hsub : {s : ℝ | (0 : ℝ) • uvec Θ.ω + s • vvec Θ.ω ∈ polyNiche Θ K} ⊆ Ico 0 Z := by
    intro s hs
    simp only [mem_ofPred_eq, zero_smul, zero_add] at hs
    obtain ⟨⟨-, hf2⟩, hU⟩ := hs
    have hf2' : 0 ≤ dot (s • vvec Θ.ω) (uvec (π / 2)) := hf2
    rw [dot_uvec_pi_div_two] at hf2'
    simp only [Prod.smul_snd, vvec, smul_eq_mul] at hf2'
    obtain ⟨t, ht, hq⟩ := mem_iUnion₂.1 hU
    rw [proposition2_2_2_qMinus] at hq
    obtain ⟨-, hq2⟩ := hq
    have hq2' : dot (s • vvec Θ.ω) (uvec (t + π / 2)) < supp K (t + π / 2) - 1 := hq2
    rw [dot_smul_left, uvec_add_pi_div_two, dot_vvec_vvec] at hq2'
    have htt := Θ.subset t ht
    have hct : 0 < cos (Θ.ω - t) := ang_cos_sub_pos_of_mem_Icc hω ⟨htt.1.le, htt.2.le⟩
    have hZt := hZ t ht
    rw [div_le_iff₀ hct] at hZt
    constructor
    · by_contra h
      rw [not_le] at h
      nlinarith [mul_pos (neg_pos.2 h) hcos]
    · by_contra h
      rw [not_lt] at h
      nlinarith [mul_le_mul_of_nonneg_right h hct.le]
  calc (volume {s : ℝ | (0 : ℝ) • uvec Θ.ω + s • vvec Θ.ω ∈ polyNiche Θ K}).toReal
      ≤ (volume (Ico 0 Z)).toReal :=
        ENNReal.toReal_mono (by simp [Real.volume_Ico]) (measure_mono hsub)
    _ = max Z 0 := by rw [Real.volume_Ico, ENNReal.toReal_ofReal', sub_zero]

/-- For a polygon cap with `ω < π/2`, `z_K° ≤ τ_K(ω)`: the same argument on the line `l(ω, 0)`. -/
lemma ang_wedgeGapZInf_le_tau {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) :
    wedgeGapZInf K Θ.ω ≤ tau Θ K Θ.ω := by
  obtain ⟨t₀, ht₀, hmax⟩ :=
    Θ.angles.exists_max_image (fun t => (supp K (t + π / 2) - 1) / cos (Θ.ω - t)) Θ.nonempty
  have hℓ := ang_lineLength_polyNiche_le_z (K := K) hω hmax
  have h352 := (lemma3_4_5_two hK (t := Θ.ω) (Or.inl rfl)).2
  have hσ := ang_supp_le_sigmaAt_add_pi hK.1 hω
  have h1 := ang_wedgeGapZInf_le_supp hK.1 hω
  have h2 := ang_wedgeGapZInf_le hK.1.2.1 hω (Θ.subset t₀ ht₀)
  rw [ang_wedgeGapZ_eq] at h2
  rcases le_total ((supp K (t₀ + π / 2) - 1) / cos (Θ.ω - t₀)) 0 with hW | hW
  · rw [max_eq_right hW] at hℓ
    linarith
  · rw [max_eq_left hW] at hℓ
    linarith

/-- The `z`-part of Theorem 4.1.2: `ang_wedgeGapZInf_le_tau`, with `τ_K(ω) = σ_K(ω)` by
balancedness (Theorem 3.4.9). -/
lemma ang_theorem4_1_2_z {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap Θ K)
    (hω : Θ.ω < π / 2) : wedgeGapZInf K Θ.ω ≤ sigmaAt K Θ.ω :=
  (theorem3_4_9 hK Θ.ω (Or.inr (Or.inl rfl))) ▸ ang_wedgeGapZInf_le_tau hK.1 hω

/-! ### Mirror symmetry -/

/-- The reflection `t ↦ ω - t` of `(0, ω)`. -/
def ang_IooReflect (ω : ℝ) : Ioo (0 : ℝ) ω ≃ Ioo (0 : ℝ) ω where
  toFun t := ⟨ω - t, by constructor <;> linarith [t.2.1, t.2.2]⟩
  invFun t := ⟨ω - t, by constructor <;> linarith [t.2.1, t.2.2]⟩
  left_inv t := by ext; simp
  right_inv t := by ext; simp

/-- `w_{K^m}° = z_K°` for the mirror image `K^m` of `K` (Proposition 2.5.4). -/
lemma ang_wedgeGapWInf_mirror {K : Set (ℝ × ℝ)} {ω : ℝ} :
    wedgeGapWInf (mirrorCap K ω) ω = wedgeGapZInf K ω := by
  unfold wedgeGapWInf wedgeGapZInf
  calc ⨅ t : Ioo 0 ω, wedgeGapW (mirrorCap K ω) t
      = ⨅ t : Ioo 0 ω, wedgeGapZ K ω (ang_IooReflect ω t) := by
        congr 1; ext t; exact (proposition2_5_4_gaps (K := K) (ω := ω) t).1
    _ = ⨅ t : Ioo 0 ω, wedgeGapZ K ω t :=
        (ang_IooReflect ω).iInf_comp (g := fun s : Ioo 0 ω => wedgeGapZ K ω s)

/-- `σ_{K^m}(t) = σ_K(ω + π/2 - t)` for the mirror image `K^m` of a cap `K`. -/
lemma ang_sigmaAt_mirror {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (t : ℝ) :
    sigmaAt (mirrorCap K ω) t = sigmaAt K (ω + π / 2 - t) := by
  unfold sigmaAt
  rw [proposition2_5_4_sigma hK, Measure.map_apply (by fun_prop) (measurableSet_singleton t)]
  congr 2
  ext s
  simp only [mem_preimage, mem_singleton_iff]
  constructor <;> intro h <;> linarith

/-- **Theorem 4.1.2** (`thm:balanced-polygon-sofa-ineq`). For a maximum polygon cap with rotation
angle `ω < π/2`, `w_K° ≤ σ_K(π/2)` and `z_K° ≤ σ_K(ω)`. -/
theorem theorem4_1_2 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap Θ K)
    (hω : Θ.ω < π / 2) :
    wedgeGapWInf K Θ.ω ≤ sigmaAt K (π / 2) ∧ wedgeGapZInf K Θ.ω ≤ sigmaAt K Θ.ω :=
  ⟨ang_theorem4_1_2_w hK hω, ang_theorem4_1_2_z hK hω⟩

/-! ### Upper semicontinuity of edge lengths and weak convergence of `σ_K` -/

/-- `(v_K⁺(t) · v_t) sin δ ≤ h_K(t + δ) - h_K(t) cos δ`: the vertex `v_K⁺(t)` lies in the supporting
half-plane of angle `t + δ`. -/
lemma ang_dplus_mul_sin_le {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t δ : ℝ) :
    dot (vplus K t) (vvec t) * sin δ ≤ supp K (t + δ) - supp K t * cos δ := by
  have h := dot_le_supp hK.2.1 (vplus_mem_edge hK t).1 (t + δ)
  rw [dot_uvec_eq_cos_add_sin _ _ t, add_sub_cancel_left, dot_vplus_uvec] at h
  linarith

/-- `h_K(t) cos δ - h_K(t - δ) ≤ (v_K⁻(t) · v_t) sin δ`: the vertex `v_K⁻(t)` lies in the supporting
half-plane of angle `t - δ`. -/
lemma ang_le_dminus_mul_sin {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t δ : ℝ) :
    supp K t * cos δ - supp K (t - δ) ≤ dot (vminus K t) (vvec t) * sin δ := by
  have h := dot_le_supp hK.2.1 (vminus_mem_edge hK t).1 (t - δ)
  rw [dot_uvec_eq_cos_add_sin _ _ t, sub_sub_cancel_left, cos_neg, sin_neg,
    dot_vminus_uvec] at h
  linarith

/-- `σ_K(t) sin δ ≤ h_K(t + δ) + h_K(t - δ) - 2 h_K(t) cos δ` for a convex body `K`. -/
lemma ang_sigmaAt_mul_sin_le {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t δ : ℝ) :
    sigmaAt K t * sin δ ≤ supp K (t + δ) + supp K (t - δ) - 2 * supp K t * cos δ := by
  have h1 := ang_dplus_mul_sin_le hK t δ
  have h2 := ang_le_dminus_mul_sin hK t δ
  rw [sigmaAt_eq_dot_sub hK]
  linarith

/-- `t + δ → t⁺` as `δ → 0⁺`. -/
lemma ang_tendsto_add_nhdsGT (t : ℝ) :
    Tendsto (fun δ : ℝ => t + δ) (𝓝[>] 0) (𝓝[>] t) :=
  tendsto_nhdsWithin_iff.2
    ⟨((continuous_const.add continuous_id).tendsto' 0 t (add_zero t)).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun _ hδ => lt_add_of_pos_right t hδ⟩

/-- `t - δ → t⁻` as `δ → 0⁺`. -/
lemma ang_tendsto_sub_nhdsGT (t : ℝ) :
    Tendsto (fun δ : ℝ => t - δ) (𝓝[>] 0) (𝓝[<] t) :=
  tendsto_nhdsWithin_iff.2
    ⟨((continuous_const.sub continuous_id).tendsto' 0 t (sub_zero t)).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun _ hδ => sub_lt_self t hδ⟩

/-- `(1 - cos δ) / δ → 0` as `δ → 0⁺`: the derivative of `cos` at `0` is `0`. -/
lemma ang_tendsto_slope_cos : Tendsto (fun δ : ℝ => (1 - cos δ) / δ) (𝓝[>] 0) (𝓝 0) := by
  have h := (hasDerivAt_cos 0).tendsto_slope_zero_right.neg
  rw [sin_zero, neg_zero, neg_zero] at h
  refine h.congr fun δ => ?_
  simp only [zero_add, cos_zero, smul_eq_mul]
  field_simp
  ring

/-- `δ / sin δ → 1` as `δ → 0⁺`: the derivative of `sin` at `0` is `1`. -/
lemma ang_tendsto_div_sin : Tendsto (fun δ : ℝ => δ / sin δ) (𝓝[>] 0) (𝓝 1) := by
  have h := (hasDerivAt_sin 0).tendsto_slope_zero_right
  rw [cos_zero] at h
  have h' := h.inv₀ one_ne_zero
  rw [inv_one] at h'
  refine h'.congr fun δ => ?_
  simp only [zero_add, sin_zero, sub_zero, smul_eq_mul, mul_inv, inv_inv]
  ring

/-- `(h_K(t + δ) - h_K(t) cos δ) / sin δ → v_K⁺(t) · v_t` as `δ → 0⁺`. -/
lemma ang_tendsto_upper {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (fun δ => (supp K (t + δ) - supp K t * cos δ) / sin δ) (𝓝[>] 0)
      (𝓝 (dot (vplus K t) (vvec t))) := by
  have hA : Tendsto (fun δ : ℝ => (supp K (t + δ) - supp K t) / δ) (𝓝[>] 0)
      (𝓝 (dot (vplus K t) (vvec t))) := by
    have h := (hasDerivWithinAt_iff_tendsto_slope.1 (hasDerivWithinAt_supp_right hK t))
    rw [Ici_sdiff_left] at h
    have := h.comp (ang_tendsto_add_nhdsGT t)
    refine this.congr fun δ => ?_
    simp only [Function.comp_apply, slope_def_field, add_sub_cancel_left]
  have hlim := ang_tendsto_div_sin.mul (hA.add (ang_tendsto_slope_cos.const_mul (supp K t)))
  rw [mul_zero, add_zero, one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT pi_pos] with δ hδ
  have hs : sin δ ≠ 0 := (sin_pos_of_pos_of_lt_pi hδ.1 hδ.2).ne'
  have hd : δ ≠ 0 := hδ.1.ne'
  field_simp
  ring

/-- `(h_K(t) cos δ - h_K(t - δ)) / sin δ → v_K⁻(t) · v_t` as `δ → 0⁺`. -/
lemma ang_tendsto_lower {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (fun δ => (supp K t * cos δ - supp K (t - δ)) / sin δ) (𝓝[>] 0)
      (𝓝 (dot (vminus K t) (vvec t))) := by
  have hB : Tendsto (fun δ : ℝ => (supp K t - supp K (t - δ)) / δ) (𝓝[>] 0)
      (𝓝 (dot (vminus K t) (vvec t))) := by
    have h := (hasDerivWithinAt_iff_tendsto_slope.1 (hasDerivWithinAt_supp_left hK t))
    rw [Iic_sdiff_right] at h
    have := h.comp (ang_tendsto_sub_nhdsGT t)
    refine this.congr fun δ => ?_
    simp only [Function.comp_apply, slope_def_field, sub_sub_cancel_left]
    rw [div_neg, ← neg_div, neg_sub]
  have hlim := ang_tendsto_div_sin.mul (hB.sub (ang_tendsto_slope_cos.const_mul (supp K t)))
  rw [mul_zero, sub_zero, one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT pi_pos] with δ hδ
  have hs : sin δ ≠ 0 := (sin_pos_of_pos_of_lt_pi hδ.1 hδ.2).ne'
  have hd : δ ≠ 0 := hδ.1.ne'
  field_simp
  ring

/-- `(h_K(t + δ) + h_K(t - δ) - 2 h_K(t) cos δ) / sin δ → σ_K(t)` as `δ → 0⁺`. -/
lemma ang_tendsto_edge_quotient {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (fun δ => (supp K (t + δ) + supp K (t - δ) - 2 * supp K t * cos δ) / sin δ)
      (𝓝[>] 0) (𝓝 (sigmaAt K t)) := by
  rw [sigmaAt_eq_dot_sub hK]
  refine ((ang_tendsto_upper hK t).sub (ang_tendsto_lower hK t)).congr fun δ => ?_
  ring

/-- `F_K(2π) = F_K(0) + ∫₀^{2π} h_K` for the distribution function `F_K` of `σ_K`. -/
lemma ang_sigmaFun_two_pi (K : Set (ℝ × ℝ)) :
    sigmaFun K (2 * π) = sigmaFun K 0 + ∫ s in (0 : ℝ)..(2 * π), supp K s := by
  have h := vplus_add_two_pi K 0
  have hv := vvec_add_two_pi 0
  rw [zero_add] at h hv
  simp only [sigmaFun, h, hv, intervalIntegral.integral_same, add_zero]

/-- For a `C¹` function `g` with `g(0) = g(2π)`,
`∫_{[0, 2π)} g dσ_K = g(0) ∫₀^{2π} h_K - ∫₀^{2π} g' F_K`, where `F_K` is the distribution function
of `σ_K`. -/
lemma ang_integral_sigma_eq {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {g g' : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g') (hg0 : g 0 = g (2 * π)) :
    ∫ t in Ico 0 (2 * π), g t ∂(sigma K) =
      g 0 * (∫ s in (0 : ℝ)..(2 * π), supp K s) - ∫ t in (0 : ℝ)..(2 * π), g' t * sigmaFun K t := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  -- `∫_{[0, 2π)} = ∫_{(0, 2π]}` by periodicity
  have hint : IntegrableOn g (Icc 0 (2 * π)) (sigma K) :=
    hgc.continuousOn.integrableOn_compact isCompact_Icc
  have hIco : ∫ t in Icc 0 (2 * π), g t ∂(sigma K) =
      (∫ t in Ico 0 (2 * π), g t ∂(sigma K)) + ∫ t in ({2 * π} : Set ℝ), g t ∂(sigma K) := by
    rw [← Ico_union_right h2π, setIntegral_union (by simp) (measurableSet_singleton _)
      (hint.mono_set Ico_subset_Icc_self)
      (hint.mono_set (singleton_subset_iff.2 ⟨h2π, le_rfl⟩))]
  have hIoc : ∫ t in Icc 0 (2 * π), g t ∂(sigma K) =
      (∫ t in ({0} : Set ℝ), g t ∂(sigma K)) + ∫ t in Ioc 0 (2 * π), g t ∂(sigma K) := by
    rw [← Ioc_insert_left h2π, insert_eq, setIntegral_union (by simp) measurableSet_Ioc
      (hint.mono_set (singleton_subset_iff.2 ⟨le_rfl, h2π⟩)) (hint.mono_set Ioc_subset_Icc_self)]
  have hsing : ∫ t in ({2 * π} : Set ℝ), g t ∂(sigma K) =
      ∫ t in ({0} : Set ℝ), g t ∂(sigma K) := by
    rw [integral_singleton, integral_singleton, ← hg0]
    congr 1
    have := sigma_periodic hK {0}
    rw [image_singleton, zero_add] at this
    simp only [Measure.real, this]
  have hIP := integral_Ioc_stieltjes (sigmaStieltjes K) h2π hg hg'
  rw [← sigma_eq_measure, sigmaStieltjes_apply hK, sigmaStieltjes_apply hK] at hIP
  simp_rw [sigmaStieltjes_apply hK, smul_eq_mul, mul_comm (sigmaFun K _)] at hIP
  rw [ang_sigmaFun_two_pi, ← hg0] at hIP
  have : ∫ t in Ico 0 (2 * π), g t ∂(sigma K) = ∫ t in Ioc 0 (2 * π), g t ∂(sigma K) := by
    linarith
  rw [this, hIP]
  ring

/-! ### Convergence of the distribution functions -/

/-- At an angle where `K` has no edge, `v_{K_n}⁺(t) · v_t → v_K⁺(t) · v_t`. -/
lemma ang_tendsto_dplus {Ks : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)}
    (hKs : ∀ n, IsConvexBody (Ks n)) (hK : IsConvexBody K) (hlim : HausdorffTendsto Ks K) {t : ℝ}
    (ht : sigmaAt K t = 0) :
    Tendsto (fun n => dot (vplus (Ks n) t) (vvec t)) atTop (𝓝 (dot (vplus K t) (vvec t))) := by
  have hDm : dot (vminus K t) (vvec t) = dot (vplus K t) (vvec t) := by
    have := sigmaAt_eq_dot_sub hK t; rw [ht] at this; linarith
  rw [tendsto_order]
  constructor
  · intro a ha
    have hlow := ang_tendsto_lower hK t
    rw [hDm] at hlow
    obtain ⟨δ, hδa, hδ⟩ :=
      ((hlow.eventually (lt_mem_nhds ha)).and (Ioo_mem_nhdsGT pi_pos)).exists
    have hsin : 0 < sin δ := sin_pos_of_pos_of_lt_pi hδ.1 hδ.2
    have hconv : Tendsto (fun n => (supp (Ks n) t * cos δ - supp (Ks n) (t - δ)) / sin δ) atTop
        (𝓝 ((supp K t * cos δ - supp K (t - δ)) / sin δ)) :=
      (((tendsto_supp hKs hK hlim t).mul_const (cos δ)).sub
        (tendsto_supp hKs hK hlim (t - δ))).div_const _
    filter_upwards [hconv.eventually (lt_mem_nhds hδa)] with n hn
    have h1 := ang_le_dminus_mul_sin (hKs n) t δ
    have h2 := dot_vminus_le_dot_vplus (hKs n) t
    have h3 : (supp (Ks n) t * cos δ - supp (Ks n) (t - δ)) / sin δ ≤
        dot (vminus (Ks n) t) (vvec t) := by
      rw [div_le_iff₀ hsin]; exact h1
    linarith
  · intro b hb
    have hup := ang_tendsto_upper hK t
    obtain ⟨δ, hδb, hδ⟩ :=
      ((hup.eventually (gt_mem_nhds hb)).and (Ioo_mem_nhdsGT pi_pos)).exists
    have hsin : 0 < sin δ := sin_pos_of_pos_of_lt_pi hδ.1 hδ.2
    have hconv : Tendsto (fun n => (supp (Ks n) (t + δ) - supp (Ks n) t * cos δ) / sin δ) atTop
        (𝓝 ((supp K (t + δ) - supp K t * cos δ) / sin δ)) :=
      (((tendsto_supp hKs hK hlim (t + δ))).sub
        ((tendsto_supp hKs hK hlim t).mul_const (cos δ))).div_const _
    filter_upwards [hconv.eventually (gt_mem_nhds hδb)] with n hn
    have h1 := ang_dplus_mul_sin_le (hKs n) t δ
    have h3 : dot (vplus (Ks n) t) (vvec t) ≤
        (supp (Ks n) (t + δ) - supp (Ks n) t * cos δ) / sin δ := by
      rw [le_div_iff₀ hsin]; exact h1
    linarith

/-- `∫_a^b h_{K_n} → ∫_a^b h_K` when `K_n → K` in the Hausdorff distance. -/
lemma ang_tendsto_integral_supp {Ks : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)}
    (hKs : ∀ n, IsConvexBody (Ks n)) (hK : IsConvexBody K) (hlim : HausdorffTendsto Ks K)
    (a b : ℝ) :
    Tendsto (fun n => ∫ s in a..b, supp (Ks n) s) atTop (𝓝 (∫ s in a..b, supp K s)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun n => hausdorffDist (Ks n) K * |b - a|) atTop (𝓝 0) := by
    simpa using hlim.mul_const |b - a|
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0
  have hc1 := continuous_supp (hKs n).2.1
  have hc2 := continuous_supp hK.2.1
  rw [← intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => ?_
  rw [Real.norm_eq_abs]
  exact abs_supp_sub_le_hausdorffDist (hKs n) hK s

/-- At an angle where `K` has no edge, the distribution functions `F_{K_n}(t)` converge to
`F_K(t)`. -/
lemma ang_tendsto_sigmaFun {Ks : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)}
    (hKs : ∀ n, IsConvexBody (Ks n)) (hK : IsConvexBody K) (hlim : HausdorffTendsto Ks K) {t : ℝ}
    (ht : sigmaAt K t = 0) : Tendsto (fun n => sigmaFun (Ks n) t) atTop (𝓝 (sigmaFun K t)) :=
  (ang_tendsto_dplus hKs hK hlim ht).add (ang_tendsto_integral_supp hKs hK hlim 0 t)

/-- A bound `|F_K(t)| ≤ R (1 + |t|)` on the distribution function, for `|h_K| ≤ R`. -/
lemma ang_abs_sigmaFun_le {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {R : ℝ}
    (hR : ∀ s, |supp K s| ≤ R) (t : ℝ) : |sigmaFun K t| ≤ R * (1 + |t|) := by
  have h1 := ang_dplus_mul_sin_le hK t (π / 2)
  have h2 := ang_le_dminus_mul_sin hK t (π / 2)
  have h3 := dot_vminus_le_dot_vplus hK t
  rw [sin_pi_div_two, cos_pi_div_two] at h1 h2
  have hR1 := abs_le.1 (hR (t + π / 2))
  have hR2 := abs_le.1 (hR (t - π / 2))
  have hD : |dot (vplus K t) (vvec t)| ≤ R := by
    rw [abs_le]; constructor <;> linarith
  have hI : ‖∫ s in (0 : ℝ)..t, supp K s‖ ≤ R * |t - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => by
      rw [Real.norm_eq_abs]; exact hR s
  rw [Real.norm_eq_abs, sub_zero] at hI
  unfold sigmaFun
  calc |dot (vplus K t) (vvec t) + ∫ s in (0 : ℝ)..t, supp K s|
      ≤ |dot (vplus K t) (vvec t)| + |∫ s in (0 : ℝ)..t, supp K s| := abs_add_le _ _
    _ ≤ R + R * |t| := add_le_add hD hI
    _ = R * (1 + |t|) := by ring

/-- Dominated convergence for `∫₀^{2π} g' F_{K_n}`. -/
lemma ang_tendsto_integral_sigmaFun {Ks : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)}
    (hKs : ∀ n, IsConvexBody (Ks n)) (hK : IsConvexBody K) (hlim : HausdorffTendsto Ks K)
    {g' : ℝ → ℝ} (hg' : Continuous g') :
    Tendsto (fun n => ∫ t in (0 : ℝ)..(2 * π), g' t * sigmaFun (Ks n) t) atTop
      (𝓝 (∫ t in (0 : ℝ)..(2 * π), g' t * sigmaFun K t)) := by
  obtain ⟨R, hR⟩ := exists_abs_supp_le hK.2.1 hK.1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hg'.continuousOn (s := Icc 0 (2 * π)))
  have hev : ∀ᶠ n in atTop, ∀ s, |supp (Ks n) s| ≤ R + 1 := by
    filter_upwards [hlim.eventually (gt_mem_nhds one_pos)] with n hn s
    have h1 := abs_le.1 (abs_supp_sub_le_hausdorffDist (hKs n) hK s)
    have h2 := abs_le.1 (hR s)
    rw [abs_le]; constructor <;> linarith
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => C * ((R + 1) * (1 + 2 * π))) ?_ ?_ intervalIntegrable_const ?_
  · exact Eventually.of_forall fun n =>
      (hg'.measurable.mul (monotone_sigmaFun (hKs n)).measurable).aestronglyMeasurable
  · filter_upwards [hev] with n hn
    refine Eventually.of_forall fun x hx => ?_
    rw [uIoc_of_le (by positivity)] at hx
    have hb := ang_abs_sigmaFun_le (hKs n) hn x
    rw [abs_of_pos hx.1] at hb
    have hCx := hC x (Ioc_subset_Icc_self hx)
    rw [norm_mul, Real.norm_eq_abs]
    have hR0 : 0 ≤ R + 1 := (abs_nonneg _).trans (hn 0)
    have h1 : |sigmaFun (Ks n) x| ≤ (R + 1) * (1 + 2 * π) := hb.trans (by gcongr; exact hx.2)
    exact mul_le_mul hCx h1 (abs_nonneg _) ((norm_nonneg _).trans hCx)
  · have hsub : {t | sigmaAt K t ≠ 0} ⊆ {t | sigma K {t} ≠ 0} := fun t ht h =>
      ht (by simp [sigmaAt, h])
    have hnull := ((countable_sigma_singleton_ne K).mono hsub).measure_zero volume
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx _
    simp only [not_not] at hx
    exact tendsto_const_nhds.mul (ang_tendsto_sigmaFun hKs hK hlim hx)

/-! ### Approximation by `C¹` functions -/

/-- A continuous `2π`-periodic function is uniformly approximated on `[0, 2π]` by `C¹` functions
`g` with `g(0) = g(2π)`: its averages over short intervals. -/
lemma ang_exists_C1_approx {f : ℝ → ℝ} (hf : Continuous f) (hper : Function.Periodic f (2 * π))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g g' : ℝ → ℝ, (∀ x, HasDerivAt g (g' x) x) ∧ Continuous g' ∧ g 0 = g (2 * π) ∧
      ∀ x ∈ Icc 0 (2 * π), |f x - g x| ≤ ε := by
  have huc := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π + 1)).uniformContinuousOn_of_continuous
    hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨η, hη, hηf⟩ := huc ε hε
  set δ := min (η / 2) 1 with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) one_pos
  have hδη : δ < η := (min_le_left _ _).trans_lt (by linarith)
  have hδ1 : δ ≤ 1 := min_le_right _ _
  set Φ : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, f s with hΦ
  have hΦd : ∀ x, HasDerivAt Φ (f x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hgΦ : ∀ x, ∫ s in x..x + δ, f s = Φ (x + δ) - Φ x := fun x =>
    (intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _)).symm
  refine ⟨fun x => δ⁻¹ * ∫ s in x..x + δ, f s, fun x => δ⁻¹ * (f (x + δ) - f x), ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [hgΦ]
    have h1 : HasDerivAt (fun x => Φ (x + δ)) (f (x + δ)) x :=
      HasDerivAt.comp_add_const x δ (hΦd (x + δ))
    exact (h1.sub (hΦd x)).const_mul δ⁻¹
  · fun_prop
  · simp only
    congr 1
    have := intervalIntegral.integral_comp_add_right (fun s => f s) (a := 0) (b := δ) (2 * π)
    simp only [zero_add] at this
    rw [zero_add, add_comm (2 * π) δ, ← this]
    exact intervalIntegral.integral_congr fun s _ => (hper s).symm
  · intro x hx
    have hbound : ∀ s ∈ Set.uIoc x (x + δ), ‖f x - f s‖ ≤ ε := by
      intro s hs
      rw [uIoc_of_le (by linarith)] at hs
      have h1 : x ∈ Icc 0 (2 * π + 1) := ⟨hx.1, by linarith [hx.2]⟩
      have h2 : s ∈ Icc 0 (2 * π + 1) := ⟨by linarith [hx.1, hs.1], by linarith [hx.2, hs.2]⟩
      have h3 : dist x s < η := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith [hs.1])]; linarith [hs.2]
      exact (hηf x h1 s h2 h3).le
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hf.intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul, show x + δ - x = δ by ring,
      abs_of_pos hδ0, Real.norm_eq_abs] at hint
    have e : f x - δ⁻¹ * ∫ s in x..x + δ, f s = δ⁻¹ * (δ * f x - ∫ s in x..x + δ, f s) := by
      field_simp
    show |f x - δ⁻¹ * ∫ s in x..x + δ, f s| ≤ ε
    rw [e, abs_mul, abs_of_pos (inv_pos.2 hδ0)]
    calc δ⁻¹ * |δ * f x - ∫ s in x..x + δ, f s| ≤ δ⁻¹ * (ε * δ) := by gcongr
      _ = ε := by field_simp

/-! ### Theorem 4.1.3 -/

/-- Theorem 4.1.3 for `C¹` functions `g` with `g(0) = g(2π)`, by integration by parts
(`ang_integral_sigma_eq`). -/
lemma ang_tendsto_integral_sigma_of_C1 {Ks : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)}
    (hKs : ∀ n, IsConvexBody (Ks n)) (hK : IsConvexBody K) (hlim : HausdorffTendsto Ks K)
    {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g')
    (hg0 : g 0 = g (2 * π)) :
    Tendsto (fun n => ∫ t in Ico 0 (2 * π), g t ∂(sigma (Ks n))) atTop
      (𝓝 (∫ t in Ico 0 (2 * π), g t ∂(sigma K))) := by
  rw [ang_integral_sigma_eq hK hg hg' hg0]
  refine (((ang_tendsto_integral_supp hKs hK hlim 0 (2 * π)).const_mul (g 0)).sub
    (ang_tendsto_integral_sigmaFun hKs hK hlim hg')).congr fun n => ?_
  exact (ang_integral_sigma_eq (hKs n) hg hg' hg0).symm

/-- If `|f - g| ≤ η` on `[0, 2π]`, then `|∫ f dσ_L - ∫ g dσ_L| ≤ η σ_L([0, 2π))`. -/
lemma ang_abs_integral_sigma_sub_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) {η : ℝ}
    (hfg : ∀ x ∈ Icc 0 (2 * π), |f x - g x| ≤ η) (L : Set (ℝ × ℝ)) :
    |(∫ t in Ico 0 (2 * π), f t ∂(sigma L)) - ∫ t in Ico 0 (2 * π), g t ∂(sigma L)| ≤
      η * (sigma L (Ico 0 (2 * π))).toReal := by
  have hfi : IntegrableOn f (Ico 0 (2 * π)) (sigma L) :=
    (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ico_subset_Icc_self
  have hgi : IntegrableOn g (Ico 0 (2 * π)) (sigma L) :=
    (hg.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ico_subset_Icc_self
  rw [← integral_sub hfi hgi, ← Real.norm_eq_abs]
  exact norm_setIntegral_le_of_norm_le_const measure_Ico_lt_top fun x hx => by
    rw [Real.norm_eq_abs]; exact hfg x (Ico_subset_Icc_self hx)

/-- **Theorem 4.1.3** (`thm:surface-area-weak-convergence`, Schneider Theorem 4.2.1). If convex
bodies `K_n` converge to `K` in the Hausdorff distance, then `σ_{K_n} → σ_K` weakly as measures on
`S¹`: for every continuous `2π`-periodic `f`, `∫_{[0, 2π)} f dσ_{K_n} → ∫_{[0, 2π)} f dσ_K`. -/
theorem theorem4_1_3 {Ks : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)} (hKs : ∀ n, IsConvexBody (Ks n))
    (hK : IsConvexBody K) (hlim : HausdorffTendsto Ks K) {f : ℝ → ℝ} (hf : Continuous f)
    (hper : Function.Periodic f (2 * π)) :
    Tendsto (fun n => ∫ t in Ico 0 (2 * π), f t ∂(sigma (Ks n))) atTop
      (𝓝 (∫ t in Ico 0 (2 * π), f t ∂(sigma K))) := by
  -- Step 1: the total masses `σ_{K_n}([0, 2π))` converge (the case `f = 1`).
  have hmass : ∀ L : Set (ℝ × ℝ), ∫ t in Ico 0 (2 * π), (1 : ℝ) ∂(sigma L) =
      (sigma L (Ico 0 (2 * π))).toReal := fun L => by
    rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real]
  have hm := ang_tendsto_integral_sigma_of_C1 hKs hK hlim (fun x => hasDerivAt_const x (1 : ℝ))
    continuous_const rfl
  simp only [hmass] at hm
  -- Step 2: an `ε / 3` argument, with a `C¹` function `g` uniformly `η`-close to `f`.
  rw [Metric.tendsto_atTop]
  intro ε hε
  set M := (sigma K (Ico 0 (2 * π))).toReal with hM
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  set η := ε / (6 * (M + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨g, g', hg, hg', hg0, happrox⟩ := ang_exists_C1_approx hf hper hη0
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  have happ := ang_abs_integral_sigma_sub_le hf hgc happrox
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1
    (ang_tendsto_integral_sigma_of_C1 hKs hK hlim hg hg' hg0) (ε / 3) (by positivity)
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.1 hm 1 one_pos
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have e1 := happ (Ks n)
  have e2 := happ K
  have e3 := hN1 n (le_of_max_le_left hn)
  have e4 := hN2 n (le_of_max_le_right hn)
  rw [Real.dist_eq] at e3 e4 ⊢
  -- the two approximation errors add up to at most `ε / 3`, since `σ_{K_n}([0, 2π)) < M + 1`
  have hmn : (sigma (Ks n) (Ico 0 (2 * π))).toReal < M + 1 := by linarith [(abs_lt.1 e4).2]
  have hmn0 : 0 ≤ (sigma (Ks n) (Ico 0 (2 * π))).toReal := ENNReal.toReal_nonneg
  have hη1 : η * (sigma (Ks n) (Ico 0 (2 * π))).toReal + η * M ≤ ε / 3 := by
    calc η * (sigma (Ks n) (Ico 0 (2 * π))).toReal + η * M ≤ η * (2 * (M + 1)) := by nlinarith
      _ = ε / 3 := by rw [hη]; field_simp; ring
  set A := ∫ t in Ico 0 (2 * π), f t ∂(sigma (Ks n))
  set B := ∫ t in Ico 0 (2 * π), g t ∂(sigma (Ks n))
  set C := ∫ t in Ico 0 (2 * π), g t ∂(sigma K)
  set D := ∫ t in Ico 0 (2 * π), f t ∂(sigma K)
  have t1 := abs_sub_le A B D
  have t2 := abs_sub_le B C D
  rw [abs_sub_comm C D] at t2
  linarith

/-- If `a_n ≤ σ_{K_n}(t)`, `a_n → a` and `K_n → K`, then `a ≤ σ_K(t)` (upper semicontinuity of the
edge lengths). -/
lemma ang_le_sigmaAt_of_tendsto {Ks : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)}
    (hKs : ∀ n, IsConvexBody (Ks n)) (hK : IsConvexBody K) (hlim : HausdorffTendsto Ks K)
    {a : ℕ → ℝ} {a₀ t : ℝ} (ha : Tendsto a atTop (𝓝 a₀)) (hle : ∀ n, a n ≤ sigmaAt (Ks n) t) :
    a₀ ≤ sigmaAt K t := by
  have hQ : ∀ δ ∈ Ioo 0 π,
      a₀ ≤ (supp K (t + δ) + supp K (t - δ) - 2 * supp K t * cos δ) / sin δ := by
    intro δ hδ
    have hsin : 0 < sin δ := sin_pos_of_pos_of_lt_pi hδ.1 hδ.2
    have hconv := (((tendsto_supp hKs hK hlim (t + δ)).add
      (tendsto_supp hKs hK hlim (t - δ))).sub
      ((tendsto_supp hKs hK hlim t).const_mul 2 |>.mul_const (cos δ))).div_const (sin δ)
    refine le_of_tendsto_of_tendsto' ha hconv fun n => ?_
    have h2 := ang_sigmaAt_mul_sin_le (hKs n) t δ
    rw [le_div_iff₀ hsin]
    nlinarith [hle n]
  refine ge_of_tendsto (ang_tendsto_edge_quotient hK t) ?_
  filter_upwards [Ioo_mem_nhdsGT pi_pos] with δ hδ using hQ δ hδ

/-- **Theorem 4.1.4** (`thm:balanced-maximum-sofa-ineq`). For `ω < π/2`, a balanced maximum cap
satisfies `σ_K(π/2) ≥ w_K°` and `σ_K(ω) ≥ z_K°`. -/
theorem theorem4_1_4 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsBalancedMaxCap K ω) (hω : ω < π / 2) :
    wedgeGapWInf K ω ≤ sigmaAt K (π / 2) ∧ wedgeGapZInf K ω ≤ sigmaAt K ω := by
  obtain ⟨hω', hcap, k, Ks, -, hmax, hlim⟩ := hK
  have hcapn : ∀ i, IsCap (Ks i) ω := fun i => (hmax i).1.1
  have hcbn : ∀ i, IsConvexBody (Ks i) := fun i => (hcapn i).2.1
  have h0 : Tendsto (fun i => (1 + 1 / cos ω) * hausdorffDist (Ks i) K) atTop (𝓝 0) := by
    simpa using hlim.const_mul (1 + 1 / cos ω)
  constructor
  · have hw : Tendsto (fun i => wedgeGapWInf (Ks i) ω) atTop (𝓝 (wedgeGapWInf K ω)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun _ => norm_nonneg _) (fun i => lemma4_1_1 hω (hcapn i) hcap) h0
    exact ang_le_sigmaAt_of_tendsto hcbn hcap.2.1 hlim hw fun i => ang_theorem4_1_2_w (hmax i) hω
  · have hz : Tendsto (fun i => wedgeGapZInf (Ks i) ω) atTop (𝓝 (wedgeGapZInf K ω)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun _ => norm_nonneg _)
        (fun i => ang_abs_wedgeGapZInf_sub_le hω (hcapn i) hcap) h0
    exact ang_le_sigmaAt_of_tendsto hcbn hcap.2.1 hlim hz fun i => ang_theorem4_1_2_z (hmax i) hω

end MovingSofaOptimality
