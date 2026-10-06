module

public import MovingSofaStability.FloorCoverage

/-!
# Partial-angle shapes and the omitted wedges

The partial shape is an over-envelope of a sofa whose rotation stops at omega.
It need not be a full-angle moving sofa. The difference from the full-angle
shape is retained explicitly.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

def partialNiche (K : Set Point) (ω : ℝ) : Set Point :=
  {p | 0 ≤ p.2 ∧ ∃ t ∈ Ioo (0 : ℝ) ω, innerSlackU K t p < 0 ∧ innerSlackV K t p < 0}

def partialShape (K : Set Point) (ω : ℝ) : Set Point := K \ partialNiche K ω

def omittedWedges (K : Set Point) (ω : ℝ) : Set Point := partialShape K ω \ capShape K

@[simp] theorem partialNiche_rightAngle (K : Set Point) : partialNiche K (π / 2) = niche K (π / 2) := by
  ext p
  exact (mem_niche_iff_slacks K p).symm

@[simp] theorem partialShape_rightAngle (K : Set Point) : partialShape K (π / 2) = capShape K := by
  simp only [partialShape, partialNiche_rightAngle, capShape]

@[simp] theorem omittedWedges_rightAngle (K : Set Point) : omittedWedges K (π / 2) = ∅ := by
  simp only [omittedWedges, partialShape_rightAngle, sdiff_self]

theorem partialNiche_measurable (K : Set Point) (ω : ℝ) : MeasurableSet (partialNiche K ω) := by
  have he : partialNiche K ω = {p : Point | 0 ≤ p.2} ∩
      ⋃ t ∈ Ioo (0 : ℝ) ω, {p : Point | innerSlackU K t p < 0 ∧ innerSlackV K t p < 0} := by
    ext p
    simp only [partialNiche, mem_inter_iff, mem_ofPred_eq, mem_iUnion, exists_prop]
  rw [he]
  apply MeasurableSet.inter (isClosed_le continuous_const continuous_snd).measurableSet
  apply IsOpen.measurableSet
  apply isOpen_iUnion
  intro t
  apply isOpen_iUnion
  intro ht
  exact (isOpen_lt (f := fun p : Point => innerSlackU K t p)
    (by unfold innerSlackU dot; fun_prop) continuous_const).inter
    (isOpen_lt (f := fun p : Point => innerSlackV K t p)
      (by unfold innerSlackV dot; fun_prop) continuous_const)

theorem partialShape_measurable {K : Set Point} (hK : IsConvexBody K) (ω : ℝ) :
    MeasurableSet (partialShape K ω) :=
  hK.2.1.measurableSet.diff (partialNiche_measurable K ω)

theorem partialNiche_subset_niche (K : Set Point) {ω : ℝ} (hω : ω ≤ π / 2) :
    partialNiche K ω ⊆ niche K (π / 2) := by
  rintro p ⟨hy, t, ht, hu, hv⟩
  exact (mem_niche_iff_slacks K p).2 ⟨hy, t, ⟨ht.1, ht.2.trans_le hω⟩, hu, hv⟩

theorem capShape_subset_partialShape (K : Set Point) {ω : ℝ} (hω : ω ≤ π / 2) :
    capShape K ⊆ partialShape K ω := by
  rintro p ⟨hp, hn⟩
  exact ⟨hp, fun h => hn (partialNiche_subset_niche K hω h)⟩

theorem sofa_subset_partialShape {K S : Set Point} {ω : ℝ}
    (hSK : S ⊆ K)
    (hpartial : ∀ p ∈ S, ∀ t ∈ Icc (0 : ℝ) ω,
      0 ≤ max (innerSlackU K t p) (innerSlackV K t p)) :
    S ⊆ partialShape K ω := by
  intro p hp
  refine ⟨hSK hp, ?_⟩
  rintro ⟨-, t, ht, hu, hv⟩
  have he := hpartial p hp t ⟨ht.1.le, ht.2.le⟩
  exact (not_lt_of_ge he) (max_lt hu hv)

/-- An omitted point has a forbidden-wedge witness at or after the terminal angle. -/
theorem omittedWedges_witness {K : Set Point} {ω : ℝ} {p : Point}
    (hp : p ∈ omittedWedges K ω) :
    p ∈ K ∧ 0 ≤ p.2 ∧ ∃ t ∈ Ioo (0 : ℝ) (π / 2), ω ≤ t ∧
      innerSlackU K t p < 0 ∧ innerSlackV K t p < 0 := by
  have hn : p ∈ niche K (π / 2) := by
    by_contra h
    exact hp.2 ⟨hp.1.1, h⟩
  obtain ⟨hy, t, ht, hu, hv⟩ := (mem_niche_iff_slacks K p).1 hn
  have hωt : ω ≤ t := by
    by_contra h
    exact hp.1.2 ⟨hy, t, ⟨ht.1, not_le.mp h⟩, hu, hv⟩
  exact ⟨hp.1.1, hy, t, ht, hωt, hu, hv⟩

/-- The height of a late inner corner is linear in its distance from pi/2. -/
theorem late_corner_height {K : Set Point} (hK : IsCap K (π / 2)) {R : ℝ}
    (hR : 1 ≤ R) (hradius : ∀ p ∈ K, norm2 p ≤ R) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (π / 2)) :
    (innerCorner K t).2 ≤ (3 * R + 1) * (π / 2 - t) := by
  have hR0 : 0 ≤ R := by linarith
  have hs := support_angle_bound hK.2.1 hR0 hradius t (π / 2)
  rw [hK.2.2.2.1, abs_of_nonpos (sub_nonpos.mpr ht.2)] at hs
  have hfirst : supp K t - 1 ≤ 2 * R * (π / 2 - t) := by
    have he := (abs_le.mp hs).2
    linarith
  have hsecond := (abs_le.mp (support_abs_le_radius hK.2.1 hradius (t + π / 2))).2
  have hsin0 : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, pi_pos])
  have hcos0 : 0 ≤ cos t := cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, pi_pos], ht.2⟩
  have hcos : cos t ≤ π / 2 - t := by
    rw [← sin_pi_div_two_sub]
    exact sin_le (by linarith [ht.2])
  have h1 := mul_le_mul_of_nonneg_right hfirst hsin0
  have h2 := mul_le_mul_of_nonneg_left (sin_le_one t)
    (show 0 ≤ 2 * R * (π / 2 - t) from mul_nonneg (by linarith) (sub_nonneg.mpr ht.2))
  have h3 := mul_le_mul_of_nonneg_right (show supp K (t + π / 2) - 1 ≤ R + 1 by linarith) hcos0
  have h4 := mul_le_mul_of_nonneg_left hcos (show 0 ≤ R + 1 by linarith)
  rw [proposition2_2_2_innerCorner]
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, uvec_snd, vvec_snd]
  nlinarith

/-- All omitted wedges lie in a thin horizontal slab. -/
theorem omittedWedges_height {K : Set Point} (hK : IsCap K (π / 2)) {R ω : ℝ}
    (hR : 1 ≤ R) (hradius : ∀ p ∈ K, norm2 p ≤ R) :
    ∀ p ∈ omittedWedges K ω, p.2 ∈ Icc (0 : ℝ) ((3 * R + 1) * (π / 2 - ω)) := by
  intro p hp
  obtain ⟨-, hy, t, ht, hωt, hu, hv⟩ := omittedWedges_witness hp
  have hbelow := point_below_corner_of_negative_slacks ht hu hv
  have hc := late_corner_height hK hR hradius ⟨ht.1.le, ht.2.le⟩
  refine ⟨hy, ?_⟩
  have hm := mul_le_mul_of_nonneg_left (show π / 2 - t ≤ π / 2 - ω by linarith)
    (show 0 ≤ 3 * R + 1 by linarith)
  linarith

/-- Area of a nondegenerate closed rectangle, with all finiteness visible. -/
theorem area_closed_rectangle {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    area (Icc a b ×ˢ Icc c d) = (b - a) * (d - c) := by
  unfold area
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
    ENNReal.toReal_ofReal (sub_nonneg.mpr hcd)]

/-- Two endpoint windows of width 2 eta have total area at most 4 eta H. -/
theorem area_two_windows_le {E : Set Point} {a b η H : ℝ}
    (hη : 0 ≤ η) (hH : 0 ≤ H)
    (hsub : E ⊆ (Icc (a - η) (a + η) ×ˢ Icc (0 : ℝ) H) ∪
      (Icc (b - η) (b + η) ×ˢ Icc (0 : ℝ) H)) :
    area E ≤ 4 * η * H := by
  let A := Icc (a - η) (a + η) ×ˢ Icc (0 : ℝ) H
  let B := Icc (b - η) (b + η) ×ˢ Icc (0 : ℝ) H
  have hAf : volume A ≠ ⊤ := (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hBf : volume B ≠ ⊤ := (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have he := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hAf, hBf⟩)
    ((measure_mono hsub).trans (measure_union_le A B))
  rw [ENNReal.toReal_add hAf hBf] at he
  change area E ≤ area A + area B at he
  rw [area_closed_rectangle (by linarith) hH, area_closed_rectangle (by linarith) hH] at he
  nlinarith

end MovingSofaStability
