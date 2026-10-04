module

public import MovingSofaOptimality.Angle.HorizontalSide
public import MovingSofaOptimality.Intro.RotationAngleBound
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Right rotation angle (§4.2) and Theorem 1.5.2

Proposition 4.2.1 (`pro:omega-gap`), Definitions 4.2.2–4.2.4, Lemmas 4.2.2–4.2.4, Theorem 4.2.5
(`thm:balanced-consumed`) and Theorem 1.5.2 (`thm:angle`). Definition 4.2.1 (right triangles with a
base and an angle) is only used in prose inside proofs and is not formalized.

**Reading of Lemma 4.2.4.** The paper states it for `ω ∈ [tan⁻¹(2.2), π/2)`; its proof treats
`ω ∈ [sec⁻¹(2.2), tan⁻¹(2.2))` as well, and Theorem 4.2.5 applies it on all of
`[sec⁻¹(2.2), π/2)`. We state it on `[sec⁻¹(2.2), π/2)`.

**Proofs.** Lemma 4.2.2 computes, by horizontal slices, the area of `R_{ω,d}` as at most the area
`sec ω` of `P_ω` minus the two corner triangles cut off by the clipping half-planes, each of area
`(tan ω - d)² cot ω / 2`. In Theorem 4.2.5 the case `h_K(ω + π/2) ≥ d_{ω,min} + c_ω` is reduced to
the case `h_K(0) ≥ d_{ω,min} + c_ω` by the mirror reflection of the cap (Proposition 2.5.4), using
the `z`-part of Theorem 4.1.4 for `K` in place of its `w`-part for the mirror image. Theorem 1.5.2
first rotates the sofa inside `H_L`, using that `S_ω` has width at most one in the directions `u_t`,
`t ∈ [ω, π/2]` (a consequence of Theorem 4.2.5: the width is `sin t` or `cos (t - ω)`), then
translates it to its initial position and follows its original movement; the three phases are glued
with clamped reparametrisations of `[0, 1]`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology

namespace MovingSofaOptimality

/-- `c_ω = tan((π/2 - ω)/2)` (Proposition 4.2.1). -/
noncomputable def cOmega (ω : ℝ) : ℝ := tan ((π / 2 - ω) / 2)

lemma ang_cOmega_eq (ω : ℝ) : cOmega ω = tan (π / 4 - ω / 2) := by
  unfold cOmega; congr 1; ring

/-- `c_ω cos ω = 1 - sin ω`. -/
lemma ang_cOmega_mul_cos {ω : ℝ} (hω : ω ∈ Icc 0 (π / 2)) : cOmega ω * cos ω = 1 - sin ω := by
  rw [ang_cOmega_eq]; exact ang_tan_mul_cos ω (ang_cos_quarter_pos hω).ne'

/-- `c_ω (1 + sin ω) = cos ω`. -/
lemma ang_cOmega_mul_one_add_sin {ω : ℝ} (hω : ω ∈ Ico 0 (π / 2)) :
    cOmega ω * (1 + sin ω) = cos ω := by
  have hc : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [hω.1, pi_pos], hω.2⟩
  refine mul_right_cancel₀ hc.ne' ?_
  rw [mul_right_comm, ang_cOmega_mul_cos ⟨hω.1, hω.2.le⟩]
  nlinarith [sin_sq_add_cos_sq ω]

lemma ang_cOmega_pos {ω : ℝ} (hω : ω ∈ Ico 0 (π / 2)) : 0 < cOmega ω := by
  rw [ang_cOmega_eq]
  exact tan_pos_of_pos_of_lt_pi_div_two (by linarith [hω.2]) (by linarith [hω.1, pi_pos])

/-- **Proposition 4.2.1** (`pro:omega-gap`). For `ω ∈ [0, π/2)`: `o_ω - v_0 = c_ω u_0`,
`o_ω - u_ω = c_ω v_ω`, the base `e_{P_ω}(3π/2)` of `P_ω` is the segment from `O` to `(sec ω, 0)`,
and `c_ω = sec ω - tan ω`. -/
theorem proposition4_2_1 {ω : ℝ} (hω : ω ∈ Ico 0 (π / 2)) :
    oPt ω - vvec 0 = cOmega ω • uvec 0 ∧ oPt ω - uvec ω = cOmega ω • vvec ω ∧
      edge (para ω) (3 * π / 2) = segment ℝ (0, 0) (1 / cos ω, 0) ∧
      cOmega ω = 1 / cos ω - tan ω := by
  have hc : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [hω.1, pi_pos], hω.2⟩
  have hk := ang_cOmega_mul_cos ⟨hω.1, hω.2.le⟩
  have hco := ang_cOmega_eq ω
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext <;> simp [oPt, vvec, uvec, hco]
  · have h2 := ang_cOmega_mul_one_add_sin hω
    ext <;> simp only [oPt, vvec, uvec, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul, ← hco]
    · linarith
    · linarith
  · have hsupp : supp (para ω) (3 * π / 2) = 0 := by
      apply IsGreatest.csSup_eq
      constructor
      · refine ⟨(0, 0), mem_para_iff.2 ⟨⟨le_rfl, zero_le_one⟩, by simp [dot], by simp [dot]⟩,
          by simp [dot, uvec_three_pi_div_two]⟩
      · rintro _ ⟨p, hp, rfl⟩
        show dot p (uvec (3 * π / 2)) ≤ 0
        rw [dot_uvec_three_pi_div_two]
        linarith [(mem_para_iff.1 hp).1.1]
    ext p
    rw [segment_eq_image']
    simp only [edge, suppLine, line, hsupp, mem_inter_iff, mem_ofPred_eq,
      dot_uvec_three_pi_div_two, mem_para_iff, mem_image, mem_Icc]
    constructor
    · rintro ⟨⟨⟨-, -⟩, h3, h4⟩, h5⟩
      have hp2 : p.2 = 0 := by linarith
      simp only [dot, uvec, hp2, zero_mul, add_zero] at h3 h4
      refine ⟨p.1 * cos ω, ⟨by positivity, h4⟩, ?_⟩
      ext
      · simp; field_simp
      · simp [hp2]
    · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
      have e : ((0 : ℝ), (0 : ℝ)) + θ • ((1 / cos ω, (0 : ℝ)) - (0, 0)) = (θ / cos ω, 0) := by
        ext <;> simp [div_eq_mul_inv]
      have hd : dot (θ / cos ω, (0 : ℝ)) (uvec ω) = θ := by
        simp only [dot, uvec, zero_mul, add_zero]; field_simp
      rw [e, hd]
      exact ⟨⟨⟨le_rfl, zero_le_one⟩, h0, h1⟩, by simp⟩
  · rw [tan_eq_sin_div_cos]; field_simp; linarith

/-- `d_{ω,min}`: `1.25` if `ω < tan⁻¹(2.2)` and `1.1` otherwise (Definition 4.2.2, `def:d-min`). -/
noncomputable def dMin (ω : ℝ) : ℝ := if ω < arctan 2.2 then 1.25 else 1.1

/-- `R_{ω,d} = P_ω ∩ H₋(0, d + c_ω) ∩ H₋(ω + π/2, d + c_ω)` (Definition 4.2.3,
`def:cap-clipped`). -/
def clippedRegion (ω d : ℝ) : Set (ℝ × ℝ) :=
  para ω ∩ halfMinus 0 (d + cOmega ω) ∩ halfMinus (ω + π / 2) (d + cOmega ω)

/-- Elementary bounds for `ω ∈ [sec⁻¹(2.2), π/2)`. -/
lemma ang_omega_facts {ω : ℝ} (hω : ω ∈ Ico arcsec22 (π / 2)) :
    0 < cos ω ∧ cos ω ≤ 5 / 11 ∧ 0 < sin ω ∧ sin ω < 1 ∧ π / 4 < ω := by
  have h0 : 0 < ω := ang_arcsec22_pos.trans_le hω.1
  have hc : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω.2⟩
  have hsc := sin_sq_add_cos_sq ω
  refine ⟨hc, ?_, sin_pos_of_pos_of_lt_pi h0 (by linarith [hω.2, pi_pos]), ?_,
    ang_pi_div_four_lt_arcsec22.trans_le hω.1⟩
  · rw [← ang_cos_arcsec22]
    exact cos_le_cos_of_nonneg_of_le_pi ang_arcsec22_pos.le (by linarith [hω.2, pi_pos]) hω.1
  · by_contra h
    rw [not_lt] at h
    nlinarith

/-- `sin ω ≥ 2.2 cos ω`, i.e. `tan ω ≥ 2.2`, for `ω ∈ [tan⁻¹(2.2), π/2)`. -/
lemma ang_tan_ge {ω : ℝ} (hω : ω ∈ Ico (arctan 2.2) (π / 2)) (hω0 : -(π / 2) < ω) :
    2.2 * cos ω ≤ sin ω := by
  have h := hω.1
  rwa [← arctan_tan hω0 hω.2, arctan_le_arctan_iff, tan_eq_sin_div_cos,
    le_div_iff₀ (cos_pos_of_mem_Ioo ⟨hω0, hω.2⟩)] at h

/-- `sin ω < 2.2 cos ω`, i.e. `tan ω < 2.2`, for `ω ∈ (-π/2, tan⁻¹(2.2))`. -/
lemma ang_tan_lt {ω : ℝ} (hω : ω < arctan 2.2) (hω0 : -(π / 2) < ω) (hω1 : ω < π / 2) :
    sin ω < 2.2 * cos ω := by
  have h := hω
  rwa [← arctan_tan hω0 hω1, arctan_lt_arctan_iff, tan_eq_sin_div_cos,
    div_lt_iff₀ (cos_pos_of_mem_Ioo ⟨hω0, hω1⟩)] at h

/-- The area of a region `A ⊆ ℝ × [a, b]` whose horizontal slice at height `y ∈ [a, b]` has length
`h(y)` is `∫_a^b h`. -/
lemma ang_volume_eq_ofReal_integral {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) {a b : ℝ}
    (hab : a ≤ b) {h : ℝ → ℝ} (hh : Continuous h) (h0 : ∀ y ∈ Icc a b, 0 ≤ h y)
    (hAy : ∀ p ∈ A, p.2 ∈ Icc a b)
    (hsl : ∀ y ∈ Icc a b, volume {x : ℝ | (x, y) ∈ A} = ENNReal.ofReal (h y)) :
    volume A = ENNReal.ofReal (∫ y in a..b, h y) := by
  have hsl' : ∀ y, volume {x : ℝ | (x, y) ∈ A} =
      (Icc a b).indicator (fun y => ENNReal.ofReal (h y)) y := by
    intro y
    by_cases hy : y ∈ Icc a b
    · rw [indicator_of_mem hy, hsl y hy]
    · rw [indicator_of_notMem hy, show {x : ℝ | (x, y) ∈ A} = ∅ from
        eq_empty_of_forall_notMem fun x hx => hy (hAy (x, y) hx), measure_empty]
  rw [ang_volume_eq_lintegral_slices hA]
  simp_rw [hsl']
  rw [lintegral_indicator measurableSet_Icc, intervalIntegral.integral_of_le hab,
    ← integral_Icc_eq_integral_Ioc, ofReal_integral_eq_lintegral_ofReal]
  · exact hh.integrableOn_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy using h0 y hy

/-- `∫_a^b (α + β y) dy = α (b - a) + β (b² - a²) / 2`. -/
lemma ang_integral_affine (α β a b : ℝ) :
    ∫ y in a..b, (α + β * y) = α * (b - a) + β * ((b ^ 2 - a ^ 2) / 2) := by
  have h1 : IntervalIntegrable (fun _ : ℝ => α) volume a b := intervalIntegrable_const
  have h2 : IntervalIntegrable (fun y : ℝ => β * y) volume a b :=
    (continuous_const.mul continuous_id).intervalIntegrable a b
  rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_id, smul_eq_mul]
  ring

/-- The area of `R_{ω,d}` is at most `sec ω - (tan ω - d)² cot ω` (the parallelogram `P_ω`
minus two corner triangles). -/
lemma ang_area_clippedRegion_le {ω d : ℝ} (hω : ω ∈ Ioo 0 (π / 2)) (hd : 1 ≤ d)
    (hdT : d * cos ω ≤ sin ω) :
    area (clippedRegion ω d) ≤ 1 / cos ω - (sin ω - d * cos ω) ^ 2 / (sin ω * cos ω) := by
  have hk : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [hω.1, pi_pos], hω.2⟩
  have hs : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω.1 (by linarith [hω.2, pi_pos])
  have hsk := sin_sq_add_cos_sq ω
  have hk1 : cos ω ≤ 1 := cos_le_one ω
  have hc := ang_cOmega_mul_cos ⟨hω.1.le, hω.2.le⟩
  set s := sin ω with hs_def
  set k := cos ω with hk_def
  set c := cOmega ω with hc_def
  have hc0 : 0 ≤ c := (ang_cOmega_pos ⟨hω.1.le, hω.2⟩).le
  set D := d + c with hD_def
  have hD1 : 1 ≤ D := by linarith
  set yh := 1 - d * k / s with hyh_def
  have hyh0 : 0 ≤ yh := by rw [hyh_def, sub_nonneg, div_le_one hs]; exact hdT
  have hyh1 : yh ≤ 1 := by
    have : 0 ≤ d * k / s := by positivity
    rw [hyh_def]; linarith
  have hDk : D * k = d * k + 1 - s := by rw [hD_def, add_mul, hc]; ring
  -- Step 1: the corner triangles `T_r` (right of the line `l(0, D)`) and `T_l` (left of the line
  -- `l(ω + π/2, D)`) of `P_ω`, each of area `(sin ω - d cos ω)² / (2 sin ω cos ω)`
  set Tr : Set (ℝ × ℝ) := {p | p.2 ∈ Icc 0 yh ∧ D < p.1 ∧ p.1 ≤ (1 - p.2 * s) / k} with hTr
  set Tl : Set (ℝ × ℝ) :=
    {p | p.2 ∈ Icc (D * k) 1 ∧ -(p.2 * s) / k ≤ p.1 ∧ p.1 < (p.2 * k - D) / s} with hTl
  have hmTr : MeasurableSet Tr := by
    refine (measurableSet_Icc.preimage measurable_snd).inter
      ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_le measurable_fst ?_))
    fun_prop
  have hmTl : MeasurableSet Tl := by
    refine (measurableSet_Icc.preimage measurable_snd).inter
      ((measurableSet_le ?_ measurable_fst).inter (measurableSet_lt measurable_fst ?_)) <;> fun_prop
  have vTr : volume Tr = ENNReal.ofReal ((s - d * k) ^ 2 / (2 * s * k)) := by
    rw [ang_volume_eq_ofReal_integral hmTr hyh0 (h := fun y => (1 / k - D) + (-s / k) * y)
      (by fun_prop) ?_ (fun p hp => hp.1) ?_, ang_integral_affine]
    · congr 1
      rw [hyh_def, hD_def, show c = (1 - s) / k by field_simp; linarith]
      field_simp
      ring
    · intro y hy
      have : y * s ≤ s - d * k := by
        have := hy.2; rw [hyh_def] at this
        have h2 := mul_le_mul_of_nonneg_right this hs.le
        rw [sub_mul, div_mul_cancel₀ _ hs.ne'] at h2; linarith
      have e : 1 / k - D + -s / k * y = (1 - y * s - D * k) / k := by field_simp; ring
      rw [e]; apply div_nonneg _ hk.le; rw [hDk]; linarith
    · intro y hy
      have : {x : ℝ | (x, y) ∈ Tr} = Ioc D ((1 - y * s) / k) := by
        ext x; simp [hTr, hy.1, hy.2]
      rw [this, Real.volume_Ioc]; congr 1; field_simp; ring
  have vTl : volume Tl = ENNReal.ofReal ((s - d * k) ^ 2 / (2 * s * k)) := by
    have hDk1 : D * k ≤ 1 := by rw [hDk]; linarith
    rw [ang_volume_eq_ofReal_integral hmTl hDk1 (h := fun y => -D / s + (1 / (s * k)) * y)
      (by fun_prop) ?_ (fun p hp => hp.1) ?_, ang_integral_affine]
    · congr 1
      have e1 : 1 - D * k = s - d * k := by rw [hDk]; ring
      have e2 : -D / s * (1 - D * k) + 1 / (s * k) * ((1 ^ 2 - (D * k) ^ 2) / 2) =
          (1 - D * k) ^ 2 / (2 * s * k) := by field_simp; ring
      rw [e2, e1]
    · intro y hy
      have e : -D / s + 1 / (s * k) * y = (y - D * k) / (s * k) := by field_simp; ring
      rw [e]; exact div_nonneg (by linarith [hy.1]) (by positivity)
    · intro y hy
      have : {x : ℝ | (x, y) ∈ Tl} = Ico (-(y * s) / k) ((y * k - D) / s) := by
        ext x; simp [hTl, hy.1, hy.2]
      rw [this, Real.volume_Ico]
      congr 1
      have e : (y * k - D) / s - -(y * s) / k = (y * (s ^ 2 + k ^ 2) - D * k) / (s * k) := by
        field_simp; ring
      rw [e, hsk]; field_simp; ring
  -- Step 2: `R_{ω,d}`, `T_r` and `T_l` are disjoint subsets of `P_ω`, which has area `sec ω`
  have hR : ∀ p ∈ clippedRegion ω d, p ∈ para ω ∧ p.1 ≤ D ∧ -(p.1 * s) + p.2 * k ≤ D := by
    rintro p ⟨⟨hp1, hp2⟩, hp3⟩
    refine ⟨hp1, ?_, ?_⟩
    · have : dot p (uvec 0) ≤ D := hp2
      rwa [dot_uvec_zero] at this
    · have : dot p (uvec (ω + π / 2)) ≤ D := hp3
      rw [uvec_add_pi_div_two] at this
      simp only [dot, vvec] at this; linarith
  have d1 : Disjoint (clippedRegion ω d) Tr := by
    rw [Set.disjoint_left]
    intro p hp hpT
    have := (hR p hp).2.1
    have := hpT.2.1
    linarith
  have d2 : Disjoint (clippedRegion ω d ∪ Tr) Tl := by
    rw [Set.disjoint_left]
    rintro p (hp | hp) hpT
    · have h1 := (hR p hp).2.2
      have h2 := hpT.2.2
      rw [lt_div_iff₀ hs] at h2
      linarith
    · have h1 := hp.2.1
      have h3 := hp.1.2
      have h2 := hpT.2.2
      rw [lt_div_iff₀ hs] at h2
      nlinarith
  have hU : volume (clippedRegion ω d ∪ Tr ∪ Tl) ≤ ENNReal.ofReal (1 / k) := by
    refine ang_volume_le_of_slices (lo := 0) (f := fun y => -(y * s) / k) (by fun_prop) ?_
    rintro p ((hp | hp) | hp)
    · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := mem_para_iff.1 (hR p hp).1
      simp only [dot, uvec] at h3 h4
      refine ⟨h1, by linarith, ?_, ?_⟩
      · rw [div_le_iff₀ hk]; linarith
      · rw [← add_div, le_div_iff₀ hk]; linarith
    · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
      refine ⟨h1, by linarith, ?_, ?_⟩
      · have : -(p.2 * s) / k ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg _ hk.le; nlinarith
        linarith
      · rw [← add_div]; convert h4 using 2; ring
    · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
      have hDk0 : 0 ≤ D * k := by positivity
      refine ⟨by linarith, by linarith, h3, ?_⟩
      rw [lt_div_iff₀ hs] at h4
      rw [← add_div, le_div_iff₀ hk]
      nlinarith
  -- Step 3: so `|R_{ω,d}| ≤ sec ω - 2 (sin ω - d cos ω)² / (2 sin ω cos ω)`
  rw [measure_union d2 hmTl, measure_union d1 hmTr, vTr, vTl] at hU
  have hfin : volume (clippedRegion ω d) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans le_self_add (le_trans le_self_add hU))
  have hA0 : 0 ≤ (s - d * k) ^ 2 / (2 * s * k) := by positivity
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hU
  rw [ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top,
    ENNReal.toReal_add hfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hA0,
    ENNReal.toReal_ofReal (by positivity)] at this
  unfold area
  have e : (s - d * k) ^ 2 / (s * k) = 2 * ((s - d * k) ^ 2 / (2 * s * k)) := by
    field_simp
  rw [e]
  linarith

/-- **Lemma 4.2.2** (`lem:cap-support-elementary-bound`). For `ω ∈ [sec⁻¹(2.2), π/2)`, the region
`R_{ω, d_{ω,min}}` has area less than `2.2`. -/
theorem lemma4_2_2 {ω : ℝ} (hω : ω ∈ Ico arcsec22 (π / 2)) :
    area (clippedRegion ω (dMin ω)) < 2.2 := by
  obtain ⟨hc, hc5, hs, hs1, h4⟩ := ang_omega_facts hω
  have hsc := sin_sq_add_cos_sq ω
  have hω' : ω ∈ Ioo 0 (π / 2) := ⟨by linarith [pi_pos], hω.2⟩
  have hsk : 0 < sin ω * cos ω := mul_pos hs hc
  have e : ∀ d : ℝ, 1 / cos ω - (sin ω - d * cos ω) ^ 2 / (sin ω * cos ω) =
      (sin ω - (sin ω - d * cos ω) ^ 2) / (sin ω * cos ω) := by
    intro d; field_simp
  by_cases hωb : ω < arctan 2.2
  · rw [dMin, ite_eq_left hωb]
    have hs2 : 96 / 121 ≤ sin ω ^ 2 := by nlinarith
    have hdT : 1.25 * cos ω ≤ sin ω := by nlinarith
    refine (ang_area_clippedRegion_le hω' (by norm_num) hdT).trans_lt ?_
    have ht := ang_tan_lt hωb (by linarith [pi_pos]) hω.2
    have hk2 : 25 / 146 < cos ω ^ 2 := by nlinarith
    have hsb : sin ω ≤ 0.9104 := by nlinarith
    have hskk : sin ω * cos ω ≤ cos ω := by nlinarith
    have key : sin ω - (sin ω - 1.25 * cos ω) ^ 2 < 2.2 * (sin ω * cos ω) := by nlinarith
    rw [e, div_lt_iff₀ hsk]
    linarith
  · rw [dMin, ite_eq_right hωb]
    have ht := ang_tan_ge ⟨not_lt.1 hωb, hω.2⟩ (by linarith [pi_pos])
    have hdT : 1.1 * cos ω ≤ sin ω := by nlinarith
    refine (ang_area_clippedRegion_le hω' (by norm_num) hdT).trans_lt ?_
    have key : sin ω - (sin ω - 1.1 * cos ω) ^ 2 < 2.2 * (sin ω * cos ω) := by
      nlinarith [mul_pos (sub_pos.2 hs1) (show (0 : ℝ) < 0.21 * sin ω + 1.21 by linarith)]
    rw [e, div_lt_iff₀ hsk]
    linarith

/-- The derivative of `cot = cos / sin` is `-1 / sin²`. -/
lemma ang_hasDerivAt_cos_div_sin {x : ℝ} (hs : sin x ≠ 0) :
    HasDerivAt (fun x => cos x / sin x) (-1 / sin x ^ 2) x := by
  convert (hasDerivAt_cos x).div (hasDerivAt_sin x) hs using 1
  field_simp
  linear_combination (sin_sq_add_cos_sq x)

/-- The first half of Lemma 4.2.3: for `d ≥ 1`, `(1 - d cot ω)²` is convex on `[π/4, π/2]`, as its
second derivative `2d (d - 2 sin ω cos ω + 2d cos² ω) / sin⁴ ω` is nonnegative there. -/
lemma ang_convexOn_sq_one_sub_cot {d : ℝ} (hd : 1 ≤ d) :
    ConvexOn ℝ (Icc (π / 4) (π / 2)) (fun ω => (1 - d * cot ω) ^ 2) := by
  have hint : interior (Icc (π / 4) (π / 2)) = Ioo (π / 4) (π / 2) := interior_Icc
  have hsin : ∀ x ∈ Icc (π / 4) (π / 2), 0 < sin x := fun x hx =>
    sin_pos_of_pos_of_lt_pi (by linarith [hx.1, pi_pos]) (by linarith [hx.2, pi_pos])
  have hf : (fun ω => (1 - d * cot ω) ^ 2) = fun ω => (1 - d * (cos ω / sin ω)) ^ 2 := by
    funext ω; rw [cot_eq_cos_div_sin]
  rw [hf]
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (f' := fun x => 2 * (1 - d * (cos x / sin x)) * (d / sin x ^ 2))
    (f'' := fun x => 2 * (d / sin x ^ 2) * (d / sin x ^ 2) +
      2 * (1 - d * (cos x / sin x)) * (d * (-2 * cos x / sin x ^ 3))) ?_ ?_ ?_ ?_
  · refine ContinuousOn.pow (continuousOn_const.sub (continuousOn_const.mul ?_)) 2
    exact continuous_cos.continuousOn.div continuous_sin.continuousOn fun x hx => (hsin x hx).ne'
  · -- the first derivative
    intro x hx
    rw [hint] at hx
    have hs : sin x ≠ 0 := (hsin x (Ioo_subset_Icc_self hx)).ne'
    refine HasDerivAt.hasDerivWithinAt ?_
    convert (((ang_hasDerivAt_cos_div_sin hs).const_mul d).const_sub 1).pow 2 using 1
    simp only [Nat.cast_ofNat]
    ring
  · -- the second derivative
    intro x hx
    rw [hint] at hx
    have hs : sin x ≠ 0 := (hsin x (Ioo_subset_Icc_self hx)).ne'
    have h3 : HasDerivAt (fun x => d / sin x ^ 2) (d * (-2 * cos x / sin x ^ 3)) x := by
      convert (((hasDerivAt_sin x).pow 2).inv (pow_ne_zero 2 hs)).const_mul d using 1
      · funext y; simp [div_eq_mul_inv]
      · simp only [Pi.pow_apply]
        field_simp
        ring
    refine HasDerivAt.hasDerivWithinAt ?_
    convert ((((ang_hasDerivAt_cos_div_sin hs).const_mul d).const_sub 1).const_mul 2).mul h3
      using 1
    ring
  · -- the second derivative is nonnegative
    intro x hx
    rw [hint] at hx
    have hs : 0 < sin x := hsin x (Ioo_subset_Icc_self hx)
    have hc : 0 ≤ cos x := cos_nonneg_of_mem_Icc ⟨by linarith [hx.1, pi_pos], hx.2.le⟩
    have key : 2 * (d / sin x ^ 2) * (d / sin x ^ 2) +
        2 * (1 - d * (cos x / sin x)) * (d * (-2 * cos x / sin x ^ 3)) =
        2 * d * (d - 2 * cos x * sin x + 2 * d * cos x ^ 2) / sin x ^ 4 := by
      field_simp
      ring
    rw [key]
    have hsc := sin_sq_add_cos_sq x
    have : 0 ≤ d - 2 * cos x * sin x + 2 * d * cos x ^ 2 := by
      nlinarith [sq_nonneg (sin x - cos x), sq_nonneg (cos x), mul_nonneg (sub_nonneg.2 hd)
        (sq_nonneg (cos x))]
    positivity

/-- The second half of Lemma 4.2.3: `cos² ω` is convex on `[π/4, π/2]`, as its second derivative
`-2 cos 2ω` is nonnegative there. -/
lemma ang_convexOn_cos_sq : ConvexOn ℝ (Icc (π / 4) (π / 2)) (fun ω => cos ω ^ 2) := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (f' := fun x => -sin (2 * x)) (f'' := fun x => -(2 * cos (2 * x))) ?_ ?_ ?_ ?_
  · exact (continuous_cos.pow 2).continuousOn
  · intro x _
    refine HasDerivAt.hasDerivWithinAt ?_
    convert (hasDerivAt_cos x).pow 2 using 1
    rw [sin_two_mul]; simp only [Nat.cast_ofNat]; ring
  · intro x _
    refine HasDerivAt.hasDerivWithinAt ?_
    convert ((hasDerivAt_id x).const_mul 2).sin.neg using 1
    · funext y; simp
    · simp; ring
  · intro x hx
    rw [interior_Icc] at hx
    have : cos (2 * x) ≤ 0 :=
      cos_nonpos_of_pi_div_two_le_of_le (by linarith [hx.1]) (by linarith [hx.2, pi_pos])
    linarith

/-- **Lemma 4.2.3** (`lem:calculation-convex`). For `d ≥ 1`, `(1 - d cot ω)²` and `cos² ω` are
convex on `[π/4, π/2]`. -/
theorem lemma4_2_3 {d : ℝ} (hd : 1 ≤ d) :
    ConvexOn ℝ (Icc (π / 4) (π / 2)) (fun ω => (1 - d * cot ω) ^ 2) ∧
      ConvexOn ℝ (Icc (π / 4) (π / 2)) (fun ω => cos ω ^ 2) :=
  ⟨ang_convexOn_sq_one_sub_cot hd, ang_convexOn_cos_sq⟩

/-- `r_y = 1 - d cot ω` (Definition 4.2.4, `def:calculation-variables`). -/
noncomputable def calcRy (ω d : ℝ) : ℝ := 1 - d * cot ω
/-- `g = √(1 - r_y²)` (Definition 4.2.4). -/
noncomputable def calcG (ω d : ℝ) : ℝ := Real.sqrt (1 - calcRy ω d ^ 2)
/-- `q_0 = o_ω - v_0 + d u_0` (Definition 4.2.4). -/
noncomputable def calcQ0 (ω d : ℝ) : ℝ × ℝ := oPt ω - vvec 0 + d • uvec 0
/-- `q_1 = o_ω - g u_0` (Definition 4.2.4). -/
noncomputable def calcQ1 (ω d : ℝ) : ℝ × ℝ := oPt ω - calcG ω d • uvec 0

lemma ang_sin_sq_arcsec22 : sin arcsec22 ^ 2 = 96 / 121 := by
  have := sin_sq_add_cos_sq arcsec22
  rw [ang_cos_arcsec22] at this; linarith

lemma ang_sin_arcsec22_pos : 0 < sin arcsec22 :=
  sin_pos_of_pos_of_lt_pi ang_arcsec22_pos (by linarith [ang_arcsec22_le_pi_div_two, pi_pos])

lemma ang_cos_sq_arctan22 : cos (arctan 2.2) ^ 2 = 25 / 146 := by
  rw [cos_sq_arctan]; norm_num

lemma ang_cot_arctan22 : cot (arctan 2.2) = 5 / 11 := by
  rw [← tan_inv_eq_cot, tan_arctan]; norm_num

lemma ang_arcsec22_lt_pi_div_two : arcsec22 < π / 2 := by
  unfold arcsec22; rw [arccos_lt_pi_div_two]; norm_num

lemma ang_arcsec22_lt_arctan22 : arcsec22 < arctan 2.2 := by
  have h1 : tan arcsec22 < 2.2 := by
    rw [tan_eq_sin_div_cos, ang_cos_arcsec22, div_lt_iff₀ (by norm_num)]
    nlinarith [ang_sin_sq_arcsec22, ang_sin_arcsec22_pos]
  have h2 := arctan_strictMono h1
  rwa [arctan_tan (by linarith [ang_arcsec22_pos, pi_pos]) ang_arcsec22_lt_pi_div_two] at h2

/-- `(1 - d_{ω,min} cot ω)² + 4 cos² ω < 1` on `[sec⁻¹(2.2), π/2)` (the inequality
`eqn:omega-calc` of Lemma 4.2.4). -/
lemma ang_omega_calc {ω : ℝ} (hω : ω ∈ Ico arcsec22 (π / 2)) :
    (1 - dMin ω * cot ω) ^ 2 + 4 * cos ω ^ 2 < 1 := by
  have hab := ang_arcsec22_lt_arctan22
  have ha4 : π / 4 < arcsec22 := ang_pi_div_four_lt_arcsec22
  have hb2 : arctan 2.2 < π / 2 := arctan_lt_pi_div_two _
  have hconv : ∀ d : ℝ, 1 ≤ d → ConvexOn ℝ (Icc (π / 4) (π / 2))
      (fun ω => (1 - d * cot ω) ^ 2 + 4 * cos ω ^ 2) := by
    intro d hd
    have h := lemma4_2_3 hd
    have := h.1.add (h.2.smul (show (0 : ℝ) ≤ 4 by norm_num))
    convert this using 1
  have hfb : ∀ d : ℝ, (1 - d * cot (arctan 2.2)) ^ 2 + 4 * cos (arctan 2.2) ^ 2 =
      (1 - d * (5 / 11)) ^ 2 + 4 * (25 / 146) := by
    intro d; rw [ang_cot_arctan22, ang_cos_sq_arctan22]
  by_cases hωb : ω < arctan 2.2
  · rw [dMin, ite_eq_left hωb]
    have hc := hconv 1.25 (by norm_num)
    have hseg : ω ∈ segment ℝ arcsec22 (arctan 2.2) := by
      rw [segment_eq_Icc hab.le]; exact ⟨hω.1, hωb.le⟩
    refine (hc.le_on_segment ⟨ha4.le, hab.le.trans hb2.le⟩ ⟨(ha4.trans hab).le, hb2.le⟩
      hseg).trans_lt (max_lt ?_ ?_)
    · -- the value at `sec⁻¹(2.2)`
      have hs := ang_sin_arcsec22_pos
      have hx : cot arcsec22 ^ 2 = 25 / 96 := by
        rw [cot_eq_cos_div_sin, div_pow, ang_cos_arcsec22, ang_sin_sq_arcsec22]; norm_num
      have hx0 : 0 < cot arcsec22 := by
        rw [cot_eq_cos_div_sin, ang_cos_arcsec22]; positivity
      show (1 - 1.25 * cot arcsec22) ^ 2 + 4 * cos arcsec22 ^ 2 < 1
      rw [ang_cos_arcsec22]
      nlinarith
    · show (1 - 1.25 * cot (arctan 2.2)) ^ 2 + 4 * cos (arctan 2.2) ^ 2 < 1
      rw [hfb]; norm_num
  · rw [dMin, ite_eq_right hωb]
    rw [not_lt] at hωb
    have hc := hconv 1.1 (by norm_num)
    have hfb' : (1 - 1.1 * cot (arctan 2.2)) ^ 2 + 4 * cos (arctan 2.2) ^ 2 < 1 := by
      rw [hfb]; norm_num
    have hfp : (1 - 1.1 * cot (π / 2)) ^ 2 + 4 * cos (π / 2) ^ 2 = 1 := by
      rw [cot_eq_cos_div_sin, cos_pi_div_two]; norm_num
    set l := (ω - arctan 2.2) / (π / 2 - arctan 2.2) with hl
    have hpos : 0 < π / 2 - arctan 2.2 := by linarith
    have hl0 : 0 ≤ l := div_nonneg (by linarith) hpos.le
    have hl1 : l < 1 := by rw [hl, div_lt_one hpos]; linarith [hω.2]
    have hωl : (1 - l) • arctan 2.2 + l • (π / 2) = ω := by
      have hne : π / 2 - arctan 2.2 ≠ 0 := hpos.ne'
      rw [smul_eq_mul, smul_eq_mul]
      calc (1 - l) * arctan 2.2 + l * (π / 2) = arctan 2.2 + l * (π / 2 - arctan 2.2) := by ring
        _ = arctan 2.2 + (ω - arctan 2.2) := by rw [hl, div_mul_cancel₀ _ hne]
        _ = ω := by ring
    have := hc.2 ⟨(ha4.trans hab).le, hb2.le⟩ ⟨by linarith [pi_pos], le_rfl⟩
      (show (0 : ℝ) ≤ 1 - l by linarith) hl0 (show 1 - l + l = 1 by ring)
    rw [hωl] at this
    simp only [smul_eq_mul] at this
    rw [hfp] at this
    nlinarith

/-- **Lemma 4.2.4** (`lem:calculation-inequalities`), on `ω ∈ [sec⁻¹(2.2), π/2)` (see the module
docstring). For `d ∈ [d_{ω,min}, tan ω]` with `r_y ≥ 0`:
(1) `(q_0 - (o_ω - v_0)) · u_{π/2 - ω} > 1`; (2) `(q_1 - (o_ω - u_ω)) · v_{π/2 - ω} > 1`. -/
theorem lemma4_2_4 {ω d : ℝ} (hω : ω ∈ Ico arcsec22 (π / 2)) (hd : d ∈ Icc (dMin ω) (tan ω))
    (hry : 0 ≤ calcRy ω d) :
    1 < dot (calcQ0 ω d - (oPt ω - vvec 0)) (uvec (π / 2 - ω)) ∧
      1 < dot (calcQ1 ω d - (oPt ω - uvec ω)) (vvec (π / 2 - ω)) := by
  obtain ⟨hc, hc5, hs, hs1, h4⟩ := ang_omega_facts hω
  have hsc := sin_sq_add_cos_sq ω
  constructor
  · have e : calcQ0 ω d - (oPt ω - vvec 0) = d • uvec 0 := by simp [calcQ0]
    rw [e, dot_smul_left, dot_uvec_uvec, show (0 : ℝ) - (π / 2 - ω) = -(π / 2 - ω) by ring,
      cos_neg, cos_pi_div_two_sub]
    by_cases hωb : ω < arctan 2.2
    · have hd1 : 1.25 ≤ d := by have := hd.1; rwa [dMin, ite_eq_left hωb] at this
      have hs2 : 96 / 121 ≤ sin ω ^ 2 := by nlinarith
      nlinarith
    · have hd1 : 1.1 ≤ d := by have := hd.1; rwa [dMin, ite_eq_right hωb] at this
      have ht := ang_tan_ge ⟨not_lt.1 hωb, hω.2⟩ (by linarith [pi_pos])
      have hs2 : 121 / 146 ≤ sin ω ^ 2 := by nlinarith
      nlinarith
  · have e : calcQ1 ω d - (oPt ω - uvec ω) = uvec ω - calcG ω d • uvec 0 := by
      simp only [calcQ1]; abel
    have hdot : dot (uvec ω - calcG ω d • uvec 0) (vvec (π / 2 - ω)) =
        sin ω ^ 2 - cos ω ^ 2 + calcG ω d * cos ω := by
      simp only [dot, uvec, vvec, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, sin_pi_div_two_sub, cos_pi_div_two_sub, cos_zero, sin_zero]
      ring
    rw [e, hdot]
    have hφ := ang_omega_calc hω
    have hcot : 0 < cot ω := by rw [cot_eq_cos_div_sin]; positivity
    have hdm : dMin ω ≤ d := hd.1
    have hry1 : calcRy ω d ≤ 1 - dMin ω * cot ω := by
      unfold calcRy; nlinarith
    have hr2 : calcRy ω d ^ 2 ≤ (1 - dMin ω * cot ω) ^ 2 := by nlinarith
    have hg : 2 * cos ω < calcG ω d := by
      unfold calcG
      rw [lt_sqrt (by positivity)]
      nlinarith
    nlinarith [mul_lt_mul_of_pos_right hg hc]

/-- The parallelogram `P_ω` has area at most `sec ω`. -/
lemma ang_volume_para_le {ω : ℝ} (hc : 0 < cos ω) :
    volume (para ω) ≤ ENNReal.ofReal (1 / cos ω) := by
  refine ang_volume_le_of_slices (lo := 0) (f := fun y => -(y * sin ω) / cos ω) (by fun_prop) ?_
  intro p hp
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := mem_para_iff.1 hp
  simp only [dot, uvec] at h3 h4
  refine ⟨h1, by linarith, ?_, ?_⟩
  · rw [div_le_iff₀ hc]; linarith
  · rw [← add_div, le_div_iff₀ hc]; linarith

/-- For a cap `K` with rotation angle `ω < π/2` and `t ∈ [0, ω]`, `h_K(t) ≤ r · u_t` where `r` is
the intersection of the lines `l_K(0)` and `l(ω, 1)`. -/
lemma ang_supp_le_corner {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (hω : ω < π / 2)
    {ry : ℝ} (hr : supp K 0 * cos ω + ry * sin ω = 1) {t : ℝ} (ht : t ∈ Icc 0 ω) :
    supp K t ≤ supp K 0 * cos t + ry * sin t := by
  have hω0 := hK.1.1
  have hs : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
  have hst : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, pi_pos])
  have hswt : 0 ≤ sin (ω - t) :=
    sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.2]) (by linarith [ht.1, pi_pos])
  refine supp_le_of_forall hK.2.1.1 fun p hp => ?_
  have hp0 : dot p (uvec 0) ≤ supp K 0 := dot_le_supp hK.2.1.2.1 hp 0
  have hpω := (mem_para_iff.1 (hK.subset_para hp)).2.2
  rw [dot_uvec_zero] at hp0
  simp only [dot, uvec] at hpω ⊢
  have key : sin ω * ((supp K 0 - p.1) * cos t + (ry - p.2) * sin t) =
      sin (ω - t) * (supp K 0 - p.1) +
        sin t * ((supp K 0 - p.1) * cos ω + (ry - p.2) * sin ω) := by
    rw [sin_sub]; ring
  have h1 : 0 ≤ sin (ω - t) * (supp K 0 - p.1) := mul_nonneg hswt (by linarith)
  have h2 : 0 ≤ sin t * ((supp K 0 - p.1) * cos ω + (ry - p.2) * sin ω) :=
    mul_nonneg hst (by linarith)
  have h3 : 0 ≤ (supp K 0 - p.1) * cos t + (ry - p.2) * sin t :=
    (mul_nonneg_iff_of_pos_left hs).1 (key ▸ add_nonneg h1 h2)
  linarith

/-- If `r - s = (g, r_y)` is a unit vector, the point `s = (h_K(0) - g, 0)` lies beyond every
`W_K(t)`, so `g ≤ w_K°`. -/
lemma ang_le_wedgeGapWInf_of_unit {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (hω : ω < π / 2)
    {ry g : ℝ} (hr : supp K 0 * cos ω + ry * sin ω = 1) (hg : g ^ 2 + ry ^ 2 = 1) :
    g ≤ wedgeGapWInf K ω := by
  refine ang_le_wedgeGapWInf hK.1.1 fun t ht => ?_
  have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
  have hsupp := ang_supp_le_corner hK hω hr ⟨ht.1.le, ht.2.le⟩
  have hX2 : (g * cos t + ry * sin t) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (g * sin t - ry * cos t), sin_sq_add_cos_sq t]
  have hunit : g * cos t + ry * sin t ≤ 1 := by nlinarith
  rw [ang_wedgeGapW_eq]
  have : (supp K t - 1) / cos t ≤ supp K 0 - g := by
    rw [div_le_iff₀ hct]; nlinarith
  linarith

/-- The point `o_ω - g u_0` lies in a cap when `0 ≤ g ≤ σ_K(π/2)`: it lies on the segment from the
vertex `v_K⁺(π/2) = v_K⁻(π/2) - σ_K(π/2) u_0` of the top edge to `o_ω`. -/
lemma ang_q1_mem {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (hω : ω < π / 2) {g : ℝ}
    (hg0 : 0 ≤ g) (hgσ : g ≤ sigmaAt K (π / 2)) : oPt ω - g • uvec 0 ∈ K := by
  have hcb := hK.2.1
  have hc : 0 < cos ω := ang_cos_pos_of_cap hK.1 hω
  have ho := oPt_dot_uvec ⟨hK.1.1.le, hω.le⟩
  have hvp := vplus_mem_edge hcb (π / 2)
  have hvm := vminus_mem_edge hcb (π / 2)
  -- both vertices of the top edge lie on the line `y = 1`
  have hvp2 : (vplus K (π / 2)).2 = 1 := by
    have := dot_vplus_uvec K (π / 2); rwa [dot_uvec_pi_div_two, hK.2.2.2.1] at this
  have hvm2 : (vminus K (π / 2)).2 = 1 := by
    have := dot_vminus_uvec K (π / 2); rwa [dot_uvec_pi_div_two, hK.2.2.2.1] at this
  -- `v_K⁻(π/2)` lies left of `o_ω` (as `K ⊆ P_ω`), and `v_K⁺(π/2)` lies `σ_K(π/2)` further left
  have hvm1 : (vminus K (π / 2)).1 ≤ tan (π / 4 - ω / 2) := by
    have h1 := (mem_para_iff.1 (hK.subset_para hvm.1)).2.2
    simp only [dot, uvec, hvm2, one_mul] at h1
    simp only [dot, uvec, oPt, one_mul] at ho
    nlinarith
  have hvp1 : (vplus K (π / 2)).1 = (vminus K (π / 2)).1 - sigmaAt K (π / 2) := by
    have := (proposition2_1_2 hcb (π / 2)).2
    rw [vvec_pi_div_two] at this
    rw [this]; simp; ring
  -- the segment from `v_K⁺(π/2)` to `o_ω` is horizontal and lies in `K`
  have hseg : segment ℝ (vplus K (π / 2)) (oPt ω) ⊆ K :=
    hcb.2.2.segment_subset hvp.1 (hK.oPt_mem hω)
  rw [← Prod.mk.eta (p := vplus K (π / 2)), hvp2, oPt, ← Prod.image_mk_segment_left,
    segment_eq_Icc (by linarith)] at hseg
  refine hseg ⟨tan (π / 4 - ω / 2) - g, ⟨by linarith, by linarith⟩, ?_⟩
  ext <;> simp [oPt, uvec]

/-- The three points `O, o_ω - v_0, o_ω - u_ω` lie in `Q_K⁻(π/2 - ω)` once `K` contains two
points `q₀, q₁` satisfying the inequalities of Lemma 4.2.4. -/
lemma ang_three_points_mem {K : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ico arcsec22 (π / 2))
    (hcK : IsCompact K) {q₀ q₁ : ℝ × ℝ} (hq0 : q₀ ∈ K) (hq1 : q₁ ∈ K)
    (h1 : 1 < dot (q₀ - (oPt ω - vvec 0)) (uvec (π / 2 - ω)))
    (h2 : 1 < dot (q₁ - (oPt ω - uvec ω)) (vvec (π / 2 - ω))) :
    ((0 : ℝ), (0 : ℝ)) ∈ qMinus K (π / 2 - ω) ∧ oPt ω - vvec 0 ∈ qMinus K (π / 2 - ω) ∧
      oPt ω - uvec ω ∈ qMinus K (π / 2 - ω) := by
  obtain ⟨hc, hc5, hs, hs1, h4⟩ := ang_omega_facts hω
  have hω0 : 0 ≤ ω := by linarith [pi_pos]
  obtain ⟨hP1, hP2, -, -⟩ := proposition4_2_1 ⟨hω0, hω.2⟩
  have hc0 := ang_cOmega_pos ⟨hω0, hω.2⟩
  rw [dot_sub_left] at h1 h2
  have hA : dot q₀ (uvec (π / 2 - ω)) ≤ supp K (π / 2 - ω) := dot_le_supp hcK hq0 _
  have hB : dot q₁ (uvec (π / 2 - ω + π / 2)) ≤ supp K (π / 2 - ω + π / 2) :=
    dot_le_supp hcK hq1 _
  rw [uvec_add_pi_div_two] at hB
  have mem : ∀ P : ℝ × ℝ, dot P (uvec (π / 2 - ω)) ≤ dot (oPt ω - vvec 0) (uvec (π / 2 - ω)) →
      dot P (vvec (π / 2 - ω)) ≤ dot (oPt ω - uvec ω) (vvec (π / 2 - ω)) →
      P ∈ qMinus K (π / 2 - ω) := by
    intro P hP1' hP2'
    rw [proposition2_2_2_qMinus]
    refine ⟨?_, ?_⟩
    · show dot P (uvec (π / 2 - ω)) < supp K (π / 2 - ω) - 1
      linarith
    · show dot P (uvec (π / 2 - ω + π / 2)) < supp K (π / 2 - ω + π / 2) - 1
      rw [uvec_add_pi_div_two]
      linarith
  have e1 : dot (oPt ω - vvec 0) (uvec (π / 2 - ω)) = cOmega ω * sin ω := by
    rw [hP1, dot_smul_left, dot_uvec_uvec, zero_sub, cos_neg, cos_pi_div_two_sub]
  have e2 : dot (oPt ω - uvec ω) (vvec (π / 2 - ω)) = cOmega ω * sin (2 * ω) := by
    rw [hP2, dot_smul_left, dot_vvec_vvec, show ω - (π / 2 - ω) = 2 * ω - π / 2 by ring,
      cos_sub_pi_div_two]
  have e3 : dot (oPt ω - vvec 0) (vvec (π / 2 - ω)) = -(cOmega ω * cos ω) := by
    rw [hP1, dot_smul_left, dot_uvec_vvec', zero_sub, sin_neg, sin_pi_div_two_sub]; ring
  have e4 : dot (oPt ω - uvec ω) (uvec (π / 2 - ω)) = cOmega ω * cos (2 * ω) := by
    rw [hP2, dot_smul_left, dot_vvec_uvec', show π / 2 - ω - ω = π / 2 - 2 * ω by ring,
      sin_pi_div_two_sub]
  have hs2 : 0 < sin (2 * ω) := by rw [sin_two_mul]; positivity
  have hc2 : cos (2 * ω) ≤ 0 :=
    cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith [hω.2, pi_pos])
  have hO : ∀ v : ℝ × ℝ, dot ((0 : ℝ), (0 : ℝ)) v = 0 := fun v => by simp [dot]
  refine ⟨mem _ ?_ ?_, mem _ le_rfl ?_, mem _ ?_ le_rfl⟩
  · rw [hO, e1]; positivity
  · rw [hO, e2]; positivity
  · rw [e2, e3]; nlinarith [mul_pos hc0 hc, mul_pos hc0 hs2]
  · rw [e1, e4]; nlinarith [mul_pos hc0 hs, mul_nonpos_of_nonneg_of_nonpos hc0.le hc2]

/-- The main step of Theorem 4.2.5, for a cap with `w_K° ≤ σ_K(π/2)` (Theorem 4.1.4) and
`h_K(0) ≥ d_{ω,min} + c_ω`. -/
lemma ang_consumed_of_supp_zero {K : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ico arcsec22 (π / 2))
    (hcap : IsCap K ω) (hw : wedgeGapWInf K ω ≤ sigmaAt K (π / 2))
    (h0 : dMin ω + cOmega ω ≤ supp K 0) :
    ((0 : ℝ), (0 : ℝ)) ∈ qMinus K (π / 2 - ω) ∧ oPt ω - vvec 0 ∈ qMinus K (π / 2 - ω) ∧
      oPt ω - uvec ω ∈ qMinus K (π / 2 - ω) := by
  obtain ⟨hc, hc5, hs, hs1, h4⟩ := ang_omega_facts hω
  have hω0 : 0 ≤ ω := by linarith [pi_pos]
  have hck := ang_cOmega_mul_cos ⟨hω0, hω.2.le⟩
  set d := supp K 0 - cOmega ω with hd_def
  -- the corner `q₀ = (h_K(0), 0)`
  have hq0K : (supp K 0, (0 : ℝ)) ∈ K := ang_cap_corner_mem hcap hω.2
  have hq0 : calcQ0 ω d = (supp K 0, 0) := by
    rw [calcQ0, (proposition4_2_1 ⟨hω0, hω.2⟩).1, hd_def]; ext <;> simp [uvec]
  have hq0P := (mem_para_iff.1 (hcap.subset_para hq0K)).2.2
  simp only [dot, uvec, zero_mul, add_zero] at hq0P
  have hdc : d * cos ω ≤ sin ω := by rw [hd_def]; nlinarith
  have hdmin : dMin ω ≤ d := by rw [hd_def]; linarith
  have hdtan : d ≤ tan ω := by rw [tan_eq_sin_div_cos, le_div_iff₀ hc]; exact hdc
  have hd0 : 0 ≤ d := by
    have : (0 : ℝ) < dMin ω := by unfold dMin; split_ifs <;> norm_num
    linarith
  have hry : calcRy ω d = 1 - d * cos ω / sin ω := by rw [calcRy, cot_eq_cos_div_sin]; ring
  have hry0 : 0 ≤ calcRy ω d := by rw [hry, sub_nonneg, div_le_one hs]; exact hdc
  have hry1 : calcRy ω d ≤ 1 := by
    rw [hry]; have : 0 ≤ d * cos ω / sin ω := by positivity
    linarith
  have hg2 : calcG ω d ^ 2 + calcRy ω d ^ 2 = 1 := by
    rw [calcG, sq_sqrt (by nlinarith)]; ring
  have hr : supp K 0 * cos ω + calcRy ω d * sin ω = 1 := by
    rw [hry]; field_simp; rw [hd_def]; linarith
  -- `g ≤ w_K° ≤ σ_K(π/2)`, so `q₁ ∈ K`
  have hgσ : calcG ω d ≤ sigmaAt K (π / 2) :=
    (ang_le_wedgeGapWInf_of_unit hcap hω.2 hr hg2).trans hw
  have hq1K : calcQ1 ω d ∈ K := ang_q1_mem hcap hω.2 (Real.sqrt_nonneg _) hgσ
  have hL := lemma4_2_4 hω ⟨hdmin, hdtan⟩ hry0
  rw [hq0] at hL
  exact ang_three_points_mem hω hcap.2.1.2.1 hq0K hq1K hL.1 hL.2

/-- The mirror reflection `M_ω` maps `Q_{K^m}⁻(t)` into `Q_K⁻(ω - t)`. -/
lemma ang_mirror_mem_qMinus {K : Set (ℝ × ℝ)} {ω t : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ qMinus (mirrorCap K ω) t) : mirror ω p ∈ qMinus K (ω - t) := by
  rw [proposition2_2_2_qMinus] at hp ⊢
  obtain ⟨h1, h2⟩ := hp
  have h1' : dot p (uvec t) < supp (mirrorCap K ω) t - 1 := h1
  have h2' : dot p (uvec (t + π / 2)) < supp (mirrorCap K ω) (t + π / 2) - 1 := h2
  rw [proposition2_5_4_supp] at h1' h2'
  refine ⟨?_, ?_⟩
  · show dot (mirror ω p) (uvec (ω - t)) < supp K (ω - t) - 1
    rw [cn_dot_mirror_uvec, show ω + π / 2 - (ω - t) = t + π / 2 by ring]
    rwa [show ω + π / 2 - (t + π / 2) = ω - t by ring] at h2'
  · show dot (mirror ω p) (uvec (ω - t + π / 2)) < supp K (ω - t + π / 2) - 1
    rw [cn_dot_mirror_uvec, show ω + π / 2 - (ω - t + π / 2) = t by ring,
      show ω - t + π / 2 = ω + π / 2 - t by ring]
    exact h1'

/-- `M_ω u_0 = v_ω`. -/
lemma ang_mirror_uvec_zero (ω : ℝ) : mirror ω (uvec 0) = vvec ω := by
  ext <;> simp [mirror, uvec, vvec, add_comm (π / 2) ω, cos_add_pi_div_two, sin_add_pi_div_two]

/-- `M_ω v_ω = u_0`. -/
lemma ang_mirror_vvec (ω : ℝ) : mirror ω (vvec ω) = uvec 0 := by
  have := sin_sq_add_cos_sq ω
  ext <;> simp [mirror, uvec, vvec, add_comm (π / 2) ω, cos_add_pi_div_two, sin_add_pi_div_two] <;>
    nlinarith

/-- **Theorem 4.2.5** (`thm:balanced-consumed`). Let `ω ∈ [sec⁻¹(2.2), π/2)` and let `K` be a
balanced maximum cap with rotation angle `ω` and `𝒜_ω(K) ≥ 2.2`. Then for some `t ∈ (0, ω)` the
three points `O`, `o_ω - v_0`, `o_ω - u_ω` lie in the closure of `Q_K⁻(t)`. -/
theorem theorem4_2_5 {K : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ico arcsec22 (π / 2))
    (hK : IsBalancedMaxCap K ω) (harea : 2.2 ≤ sofaArea ω K) :
    ∃ t ∈ Ioo 0 ω, (0, 0) ∈ closure (qMinus K t) ∧ oPt ω - vvec 0 ∈ closure (qMinus K t) ∧
      oPt ω - uvec ω ∈ closure (qMinus K t) := by
  have hcap : IsCap K ω := hK.2.1
  obtain ⟨hc, hc5, hs, hs1, h4⟩ := ang_omega_facts hω
  have hω0 : 0 ≤ ω := by linarith [pi_pos]
  have hω2 := hω.2
  -- `h_K(0)` or `h_K(ω + π/2)` is at least `d_{ω,min} + c_ω`, by Lemma 4.2.2
  have hlarge : dMin ω + cOmega ω ≤ supp K 0 ∨ dMin ω + cOmega ω ≤ supp K (ω + π / 2) := by
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
    have := lemma4_2_2 hω
    unfold sofaArea at harea
    linarith
  rcases hlarge with h | h
  · obtain ⟨h1, h2, h3⟩ := ang_consumed_of_supp_zero hω hcap (theorem4_1_4 hK hω2).1 h
    exact ⟨π / 2 - ω, ⟨by linarith, by linarith⟩, subset_closure h1, subset_closure h2,
      subset_closure h3⟩
  · -- the mirror image of `K` has `h(0) = h_K(ω + π/2)`
    have h' : dMin ω + cOmega ω ≤ supp (mirrorCap K ω) 0 := by
      rw [proposition2_5_4_supp, sub_zero]; exact h
    -- `w_{K^m}° = z_K° ≤ σ_K(ω) = σ_{K^m}(π/2)` by Theorem 4.1.4
    have hw' : wedgeGapWInf (mirrorCap K ω) ω ≤ sigmaAt (mirrorCap K ω) (π / 2) := by
      rw [ang_wedgeGapWInf_mirror, ang_sigmaAt_mirror hcap, show ω + π / 2 - π / 2 = ω by ring]
      exact (theorem4_1_4 hK hω2).2
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
    exact ⟨ω - (π / 2 - ω), ⟨by linarith, by linarith⟩, subset_closure m1, subset_closure m3,
      subset_closure m2⟩

/-- The closure of the open quadrant `Q_K⁻(t)` lies in the closed quadrant. -/
lemma ang_closure_qMinus_subset (K : Set (ℝ × ℝ)) (t : ℝ) :
    closure (qMinus K t) ⊆ {x | dot x (uvec t) ≤ supp K t - 1 ∧
      dot x (uvec (t + π / 2)) ≤ supp K (t + π / 2) - 1} := by
  refine closure_minimal ?_ ?_
  · intro x hx
    rw [proposition2_2_2_qMinus] at hx
    exact ⟨hx.1.le, hx.2.le⟩
  · exact (isClosed_le (continuous_dot _) continuous_const).inter
      (isClosed_le (continuous_dot _) continuous_const)

/-- If the three points `O, c_ω u_0, c_ω v_ω` lie in the closure of `Q_K⁻(t₀)`, then every point
`a u_0 + b v_ω` of `P_ω` with `a + b < c_ω` lies in the niche of `K`. -/
lemma ang_mem_niche_of_small {K : Set (ℝ × ℝ)} {ω t₀ : ℝ} (hω : ω ∈ Ioo 0 (π / 2))
    (ht₀ : t₀ ∈ Ioo 0 ω) (h1 : ((0 : ℝ), (0 : ℝ)) ∈ closure (qMinus K t₀))
    (h2 : cOmega ω • uvec 0 ∈ closure (qMinus K t₀))
    (h3 : cOmega ω • vvec ω ∈ closure (qMinus K t₀)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b < cOmega ω) : a • uvec 0 + b • vvec ω ∈ niche K ω := by
  have hc0 : 0 < cOmega ω := ang_cOmega_pos ⟨hω.1.le, hω.2⟩
  have hcosω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [hω.1, pi_pos], hω.2⟩
  have hsinω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω.1 (by linarith [hω.2, pi_pos])
  set c := cOmega ω
  obtain ⟨-, hO2⟩ := ang_closure_qMinus_subset K t₀ h1
  obtain ⟨hu1, hu2⟩ := ang_closure_qMinus_subset K t₀ h2
  obtain ⟨hv1, hv2⟩ := ang_closure_qMinus_subset K t₀ h3
  set α := supp K t₀ - 1
  set β := supp K (t₀ + π / 2) - 1
  -- `α, β > 0`
  have hct : 0 < cos t₀ :=
    cos_pos_of_mem_Ioo ⟨by linarith [ht₀.1, pi_pos], by linarith [ht₀.2, hω.2]⟩
  have hcωt : 0 < cos (ω - t₀) :=
    cos_pos_of_mem_Ioo ⟨by linarith [ht₀.2, pi_pos], by linarith [ht₀.1, hω.2]⟩
  have eu : dot (c • uvec 0) (uvec t₀) = c * cos t₀ := by
    rw [dot_smul_left, dot_uvec_uvec, zero_sub, cos_neg]
  have ev : dot (c • vvec ω) (uvec (t₀ + π / 2)) = c * cos (ω - t₀) := by
    rw [dot_smul_left, uvec_add_pi_div_two, dot_vvec_vvec]
  have hα : 0 < α := by rw [eu] at hu1; nlinarith [mul_pos hc0 hct]
  have hβ : 0 < β := by rw [ev] at hv2; nlinarith [mul_pos hc0 hcωt]
  refine ⟨⟨?_, ?_⟩, mem_iUnion₂.2 ⟨t₀, ht₀, ?_⟩⟩
  · show 0 ≤ dot (a • uvec 0 + b • vvec ω) (uvec ω)
    rw [dot_add_left, dot_smul_left, dot_smul_left, dot_uvec_uvec, dot_vvec_uvec', zero_sub,
      cos_neg, sub_self, sin_zero]
    nlinarith
  · show 0 ≤ dot (a • uvec 0 + b • vvec ω) (uvec (π / 2))
    rw [dot_uvec_pi_div_two]
    simp only [Prod.snd_add, Prod.smul_snd, uvec, vvec, smul_eq_mul, sin_zero, mul_zero,
      zero_add]
    positivity
  · rw [proposition2_2_2_qMinus]
    have e : a • uvec 0 + b • vvec ω = (a / c) • (c • uvec 0) + (b / c) • (c • vvec ω) := by
      rw [smul_smul, smul_smul, div_mul_cancel₀ _ hc0.ne', div_mul_cancel₀ _ hc0.ne']
    have hl : a / c + b / c < 1 := by rw [← add_div, div_lt_one hc0]; exact hab
    have hac : 0 ≤ a / c := div_nonneg ha hc0.le
    have hbc : 0 ≤ b / c := div_nonneg hb hc0.le
    rw [e]
    refine ⟨?_, ?_⟩
    · show dot ((a / c) • (c • uvec 0) + (b / c) • (c • vvec ω)) (uvec t₀) < α
      rw [dot_add_left, dot_smul_left (a / c) (c • uvec 0), dot_smul_left (b / c) (c • vvec ω)]
      nlinarith [mul_le_mul_of_nonneg_left hu1 hac, mul_le_mul_of_nonneg_left hv1 hbc]
    · show dot ((a / c) • (c • uvec 0) + (b / c) • (c • vvec ω)) (uvec (t₀ + π / 2)) < β
      rw [dot_add_left, dot_smul_left (a / c) (c • uvec 0), dot_smul_left (b / c) (c • vvec ω)]
      nlinarith [mul_le_mul_of_nonneg_left hu2 hac, mul_le_mul_of_nonneg_left hv2 hbc]

/-- `P_ω` lies below `o_ω` in the directions `u_t`, `t ∈ [ω, π/2]`. -/
lemma ang_dot_le_oPt {ω t : ℝ} (hω : ω ∈ Ioo 0 (π / 2)) (ht : t ∈ Icc ω (π / 2)) {p : ℝ × ℝ}
    (hp : p ∈ para ω) : dot p (uvec t) ≤ cOmega ω * cos t + sin t := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := mem_para_iff.1 hp
  have hc : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [hω.1, pi_pos], hω.2⟩
  have hck := ang_cOmega_mul_cos ⟨hω.1.le, hω.2.le⟩
  have hct : 0 ≤ cos t := cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, hω.1, pi_pos], ht.2⟩
  have hst : 0 ≤ sin (t - ω) :=
    sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht.2, hω.1, pi_pos])
  have key : cos ω * dot p (uvec t) = cos t * dot p (uvec ω) + sin (t - ω) * p.2 := by
    simp only [dot, uvec, sin_sub]; ring
  have e : cos ω * (cOmega ω * cos t + sin t) = cos t * 1 + sin (t - ω) * 1 := by
    rw [sin_sub]; linear_combination cos t * hck
  have : cos ω * dot p (uvec t) ≤ cos ω * (cOmega ω * cos t + sin t) := by
    rw [key, e]
    nlinarith [mul_le_mul_of_nonneg_left h4 hct, mul_le_mul_of_nonneg_left h2 hst]
  exact le_of_mul_le_mul_left this hc

/-- The width of `K \ 𝒩(K)` in the directions `u_t`, `t ∈ [ω, π/2]`, is at most one. -/
lemma ang_width_le_one {K : Set (ℝ × ℝ)} {ω t₀ : ℝ} (hω : ω ∈ Ioo 0 (π / 2)) (hK : IsCap K ω)
    (ht₀ : t₀ ∈ Ioo 0 ω) (h1 : ((0 : ℝ), (0 : ℝ)) ∈ closure (qMinus K t₀))
    (h2 : cOmega ω • uvec 0 ∈ closure (qMinus K t₀))
    (h3 : cOmega ω • vvec ω ∈ closure (qMinus K t₀)) {p q : ℝ × ℝ} (hp : p ∈ K)
    (hq : q ∈ K \ niche K ω) {t : ℝ} (ht : t ∈ Icc ω (π / 2)) : dot (p - q) (uvec t) ≤ 1 := by
  have hc : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [hω.1, pi_pos], hω.2⟩
  have hck := ang_cOmega_mul_cos ⟨hω.1.le, hω.2.le⟩
  have hck2 := ang_cOmega_mul_one_add_sin ⟨hω.1.le, hω.2⟩
  have hpo := ang_dot_le_oPt hω ht (IsCap.subset_para hK hp)
  obtain ⟨⟨hq1, hq2⟩, hq3, hq4⟩ := mem_para_iff.1 (hK.subset_para hq.1)
  set a := dot q (uvec ω) / cos ω with ha_def
  set b := q.2 / cos ω with hb_def
  have ha : 0 ≤ a := div_nonneg hq3 hc.le
  have hb : 0 ≤ b := div_nonneg hq1 hc.le
  have hqab : a • uvec 0 + b • vvec ω = q := by
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, uvec, vvec, cos_zero, ha_def, hb_def,
        dot]
      field_simp; ring
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, uvec, vvec, sin_zero, hb_def]
      field_simp; ring
  have hab : cOmega ω ≤ a + b := by
    by_contra h
    rw [not_le] at h
    have := ang_mem_niche_of_small hω ht₀ h1 h2 h3 ha hb h
    rw [hqab] at this
    exact hq.2 this
  have hqt : dot q (uvec t) = a * cos t + b * sin (t - ω) := by
    rw [← hqab, dot_add_left, dot_smul_left, dot_smul_left, dot_uvec_uvec, dot_vvec_uvec',
      zero_sub, cos_neg]
  have hct : 0 ≤ cos t := cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, hω.1, pi_pos], ht.2⟩
  have hst : 0 ≤ sin (t - ω) :=
    sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht.2, hω.1, pi_pos])
  rw [dot_sub_left, hqt]
  rcases le_total (cos t) (sin (t - ω)) with h | h
  · have : cOmega ω * cos t ≤ a * cos t + b * sin (t - ω) := by
      nlinarith [mul_le_mul_of_nonneg_left h hb, mul_le_mul_of_nonneg_right hab hct]
    linarith [sin_le_one t]
  · have : cOmega ω * sin (t - ω) ≤ a * cos t + b * sin (t - ω) := by
      nlinarith [mul_le_mul_of_nonneg_left h ha, mul_le_mul_of_nonneg_right hab hst]
    have e : cOmega ω * cos t + sin t - cOmega ω * sin (t - ω) = cos (t - ω) := by
      rw [sin_sub, cos_sub]; linear_combination cos t * hck2 - sin t * hck
    linarith [cos_le_one (t - ω)]

/-- The first phase of the movement of Theorem 1.5.2: the rotated sofa `R_φ(S)`, `φ ∈ [0, π/2 - ω]`,
fits in `H_L` after a translation depending continuously on `φ`. -/
lemma ang_phase_one {S : Set (ℝ × ℝ)} {ω R : ℝ} (hSc : IsCompact S) (hR : ∀ p ∈ S, ‖p‖ ≤ R)
    (hwidth : ∀ p ∈ S, ∀ q ∈ S, ∀ t ∈ Icc ω (π / 2), dot (p - q) (uvec t) ≤ 1)
    {φ : ℝ} (hφ : φ ∈ Icc 0 (π / 2 - ω)) {p : ℝ × ℝ} (hp : p ∈ S) :
    rot φ p + (1 - 2 * R, supp S (π / 2 - φ + π)) ∈ horizSide := by
  have hne : S.Nonempty := ⟨p, hp⟩
  have hy : (rot φ p).2 = dot p (uvec (π / 2 - φ)) := by
    simp only [rot, dot, uvec, cos_pi_div_two_sub, sin_pi_div_two_sub]; ring
  obtain ⟨q, hq, hqt⟩ := exists_dot_eq_supp hSc hne (π / 2 - φ + π)
  rw [dot_uvec_add_pi] at hqt
  have hpt := dot_le_supp hSc hp (π / 2 - φ + π)
  rw [dot_uvec_add_pi] at hpt
  have hw := hwidth p hp q hq (π / 2 - φ) ⟨by linarith [hφ.2], by linarith [hφ.1]⟩
  rw [dot_sub_left] at hw
  refine ⟨?_, ?_, ?_⟩
  · simp only [Prod.fst_add]
    have h1 : |p.1| ≤ R := (norm_fst_le p).trans (hR p hp)
    have h2 : |p.2| ≤ R := (norm_snd_le p).trans (hR p hp)
    have hc1 := abs_cos_le_one φ
    have hs1 := abs_sin_le_one φ
    have : (rot φ p).1 ≤ 2 * R := by
      simp only [rot]
      calc cos φ * p.1 - sin φ * p.2 ≤ |cos φ * p.1 - sin φ * p.2| := le_abs_self _
        _ ≤ |cos φ * p.1| + |sin φ * p.2| := abs_sub _ _
        _ = |cos φ| * |p.1| + |sin φ| * |p.2| := by rw [abs_mul, abs_mul]
        _ ≤ 1 * R + 1 * R := by gcongr
        _ = 2 * R := by ring
    linarith
  · simp only [Prod.snd_add]; rw [hy]; linarith
  · simp only [Prod.snd_add]; rw [hy]; linarith

/-- If `p + a` and `p + b` lie in `H_L`, so does `p + ((1 - l) a + l b)` for `l ∈ [0, 1]`. -/
lemma ang_horizSide_combo {p a b : ℝ × ℝ} {l : ℝ} (ha : p + a ∈ horizSide)
    (hb : p + b ∈ horizSide) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    p + ((1 - l) • a + l • b) ∈ horizSide := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  simp only [Prod.fst_add, Prod.snd_add] at ha1 ha2 ha3 hb1 hb2 hb3
  have h1l : 0 ≤ 1 - l := by linarith
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  · nlinarith [mul_le_mul_of_nonneg_left ha1 h1l, mul_le_mul_of_nonneg_left hb1 hl0]
  · nlinarith [mul_le_mul_of_nonneg_left ha2 h1l, mul_le_mul_of_nonneg_left hb2 hl0]
  · nlinarith [mul_le_mul_of_nonneg_left ha3 h1l, mul_le_mul_of_nonneg_left hb3 hl0]

/-- The image of a set under the rotation `R_a` is its preimage under `R_{-a}`. -/
lemma ang_image_rot (a : ℝ) (S : Set (ℝ × ℝ)) : rot a '' S = rot (-a) ⁻¹' S :=
  congrFun (image_eq_preimage_of_inverse (rot_neg_rot a) (rot_rot_neg a)) S

/-- If a moving sofa with rotation angle `ω < π/2` has width at most one in every direction `u_t`,
`t ∈ [ω, π/2]`, then its copy rotated by `π/2 - ω` has a movement with rotation angle `π/2`: it
first rotates back by `π/2 - ω` inside `H_L` (`ang_phase_one`). -/
theorem right_angle_motion_of_width {S : Set (ℝ × ℝ)} {ω : ℝ} (hS : IsMovingSofaWithAngle S ω)
    (hω : ω < π / 2) (hwidth : ∀ p ∈ S, ∀ q ∈ S, ∀ t ∈ Icc ω (π / 2), dot (p - q) (uvec t) ≤ 1) :
    IsMovingSofaWithAngle (rot (π / 2 - ω) '' S) (π / 2) := by
  obtain ⟨hcl, hconn, θ, c, hm⟩ := hS
  have hSc : IsCompact S := isCompact_of_isMovingSofa ⟨ω, hcl, hconn, θ, c, hm⟩
  obtain ⟨R, hR⟩ := hSc.isBounded.exists_norm_le
  set β := π / 2 - ω with hβ
  have hβ0 : 0 < β := by linarith
  -- the movement, in three phases glued by reparametrisations of `[0, 1]`: on `[0, 1/3]` it turns
  -- back by `β` to `S` inside `H_L` (`ang_phase_one`), on `[1/3, 2/3]` it slides along `H_L` to the
  -- start of the original movement, which it follows on `[2/3, 1]`
  set φf : ℝ → ℝ := fun s => β * max 0 (1 - 3 * s) with hφf
  set lf : ℝ → ℝ := fun s => max 0 (min 1 (3 * s - 1)) with hlf
  set τf : ℝ → ℝ := fun s => max 0 (min 1 (3 * s - 2)) with hτf
  set e : ℝ → ℝ × ℝ := fun φ => (1 - 2 * R, supp S (π / 2 - φ + π)) with he
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
  have hphase := fun φ (hφ : φ ∈ Icc 0 β) p (hp : p ∈ S) => ang_phase_one hSc hR hwidth hφ hp
  refine ⟨?_, ?_, fun s => θ (τf s) - β + φf s,
    fun s => (1 - lf s) • e (φf s) + lf s • c (τf s), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [ang_image_rot]; exact hcl.preimage (continuous_rot _)
  · exact hconn.image _ (continuous_rot _).continuousOn
  · exact ((hm.continuousOn_angle.comp hτc.continuousOn hτmaps).sub continuousOn_const).add
      hφc.continuousOn
  · exact ((continuous_const.sub hlc).smul (hec.comp hφc)).continuousOn.add
      (hlc.continuousOn.smul (hm.continuousOn_shift.comp hτc.continuousOn hτmaps))
  · simp only [hτ0, hφ0, hm.angle_zero]; ring
  · simp only [hτ1, hφ1, hm.angle_one, hβ]; ring
  · rintro _ ⟨q, hq, rfl⟩
    simp only [hτ0, hφ0, hl0, hm.angle_zero, sub_zero, one_smul, zero_smul, add_zero]
    rw [show (0 : ℝ) - β + β = 0 by ring, rot_zero]
    exact hphase β ⟨hβ0.le, le_rfl⟩ q hq
  · rintro s hs _ ⟨q, hq, rfl⟩
    rw [← rot_add, show θ (τf s) - β + φf s + β = θ (τf s) + φf s by ring]
    rcases le_or_gt s (1 / 3) with hs1 | hs1
    · -- first phase: rotation inside `H_L`
      have hτ : τf s = 0 := by
        simp only [hτf]; rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      have hl : lf s = 0 := by
        simp only [hlf]; rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      have hφ : φf s ∈ Icc 0 β := by
        simp only [hφf]
        rw [max_eq_right (by linarith)]
        constructor <;> nlinarith [hs.1]
      rw [hτ, hl, hm.angle_zero, zero_add, sub_zero, one_smul, zero_smul, add_zero]
      exact Or.inl (hphase _ hφ q hq)
    rcases le_or_gt s (2 / 3) with hs2 | hs2
    · -- second phase: translation inside `H_L`
      have hτ : τf s = 0 := by
        simp only [hτf]; rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      have hφ : φf s = 0 := by
        simp only [hφf]; rw [max_eq_left (by linarith), mul_zero]
      have hl : lf s ∈ Icc (0 : ℝ) 1 := ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
      rw [hτ, hφ, hm.angle_zero, add_zero, rot_zero]
      left
      have ha := hphase 0 ⟨le_rfl, hβ0.le⟩ q hq
      rw [rot_zero] at ha
      have hb := hm.start q hq
      rw [hm.angle_zero, rot_zero] at hb
      exact ang_horizSide_combo ha hb hl.1 hl.2
    · -- third phase: the original movement
      have hφ : φf s = 0 := by
        simp only [hφf]; rw [max_eq_left (by linarith), mul_zero]
      have hl : lf s = 1 := by
        simp only [hlf]; rw [min_eq_left (by linarith), max_eq_right zero_le_one]
      rw [hφ, hl, add_zero, sub_self, zero_smul, zero_add, one_smul]
      exact hm.inside (τf s) (hτmaps hs) q hq
  · rintro _ ⟨q, hq, rfl⟩
    rw [← rot_add, show θ (τf 1) - β + φf 1 + β = θ (τf 1) + φf 1 by ring]
    simp only [hτ1, hφ1, hl1, add_zero, sub_self, zero_smul, zero_add, one_smul]
    exact hm.finish q hq


/-- **Theorem 1.5.2** (`thm:angle`). A balanced maximum sofa `S_ω` of area at least `2.2` with
rotation angle `ω ∈ [sec⁻¹(2.2), π/2]` has a rotated copy admitting a movement with rotation angle
`π/2`. -/
theorem theorem1_5_2 {S : Set (ℝ × ℝ)} {ω : ℝ} (hS : IsBalancedMaxSofa S ω) (harea : 2.2 ≤ area S)
    (hω : ω ∈ Icc arcsec22 (π / 2)) : ∃ s : ℝ, IsMovingSofaWithAngle (rot s '' S) (π / 2) := by
  obtain ⟨hmono, hbal⟩ := hS
  -- if `ω = π/2` there is nothing to do
  rcases eq_or_lt_of_le hω.2 with heq | hlt
  · exact ⟨0, by simpa [rot_zero, ← heq] using hmono.isMovingSofaWithAngle⟩
  -- for `ω < π/2`, Theorem 4.2.5 makes the width of `S` in the directions `u_t`, `t ∈ [ω, π/2]`,
  -- at most one
  have hcap : IsCap (capOf S ω) ω := hbal.2.1
  have harea' : 2.2 ≤ sofaArea ω (capOf S ω) := by rw [theorem2_5_10 hmono]; exact harea
  obtain ⟨t₀, ht₀, h1, h2, h3⟩ := theorem4_2_5 ⟨hω.1, hlt⟩ hbal harea'
  obtain ⟨hP1, hP2, -, -⟩ := proposition4_2_1 ⟨hmono.1.1.le, hlt⟩
  rw [hP1] at h2
  rw [hP2] at h3
  refine ⟨_, right_angle_motion_of_width hmono.isMovingSofaWithAngle hlt fun p hp q hq t ht => ?_⟩
  rw [theorem2_4_3 hmono] at hp hq
  exact ang_width_le_one ⟨hmono.1.1, hlt⟩ hcap ht₀ h1 h2 h3 hp.1 hq ht

end MovingSofaOptimality
