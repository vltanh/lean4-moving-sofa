module

public import MovingSofaStability.CornerAnalysis

/-!
# The nonsmooth core as a Lipschitz graph

A uniform horizontal-decrease estimate and a bounded right velocity imply a
finite chord slope. The graph is extended continuously outside its horizontal
interval by clamping, for use in an elementary right-derivative
change-of-variables argument.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality

namespace MovingSofaStability

/-- Continuous extension of a Lipschitz function on an interval by constant end values. -/
theorem continuous_clamped_roof {a b L : ℝ} {γ : ℝ → ℝ} (hab : a ≤ b) (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |γ x - γ y| ≤ L * |x - y|) :
    Continuous (fun x => γ (max a (min x b))) := by
  have hlip : LipschitzOnWith L.toNNReal γ (Icc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Real.dist_eq, Real.coe_toNNReal _ hL] using hLip x hx y hy
  exact hlip.continuousOn.comp_continuous
    (continuous_const.max (continuous_id.min continuous_const))
    (fun x => ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩)

/-- Uniform core-arm margins give a finite slope bound for every core chord. -/
theorem core_verticalSlopeBound {K : Set Point} (hK : IsCap K (π / 2))
    {a b c : ℝ} (hmargin : CoreArmMargin K a b c) (hc : 0 < c)
    (ha : 0 ≤ a) (hb : b ≤ π / 2) :
    ∃ L : ℝ, 0 ≤ L ∧ VerticalSlopeBound (innerCorner K '' Icc a b) L := by
  obtain ⟨B, hB, hvel⟩ := cornerRightVelocity_bound hK.2.1
  let L := B / c
  have hL : 0 ≤ L := div_nonneg hB hc.le
  have hLc : L * c = B := div_mul_cancel₀ _ hc.ne'
  have ordered : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v →
      |(innerCorner K u).2 - (innerCorner K v).2| ≤
        L * |(innerCorner K u).1 - (innerCorner K v).1| := by
    intro u hu v hv huv
    have hX := hmargin.horizontal_decrease hK hc.le ha hb hu hv huv
    have hY := corner_coordinate_chord_bound hK hvel u v
    rw [abs_of_nonpos (sub_nonpos.mpr huv)] at hY
    have hXorder : (innerCorner K v).1 ≤ (innerCorner K u).1 := by
      have hnon : -c * (v - u) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (sub_nonneg.mpr huv)
      linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hXorder)]
    have hbound : c * (v - u) ≤ (innerCorner K u).1 - (innerCorner K v).1 := by linarith
    have hm := mul_le_mul_of_nonneg_left hbound hL
    rw [← mul_assoc, hLc] at hm
    nlinarith
  refine ⟨L, hL, ?_⟩
  rintro p ⟨u, hu, rfl⟩ q ⟨v, hv, rfl⟩
  rcases le_total u v with huv | hvu
  · exact ordered u hu v hv huv
  · simpa only [abs_sub_comm] using ordered v hv u hu hvu

/-- A continuous full-line graph function agreeing with the entire core. -/
theorem exists_core_graph {K : Set Point} (hK : IsCap K (π / 2))
    {a b c : ℝ} (hab : a < b) (hmargin : CoreArmMargin K a b c) (hc : 0 < c)
    (ha : 0 ≤ a) (hb : b ≤ π / 2) :
    ∃ F : ℝ → ℝ, Continuous F ∧
      (∀ t ∈ Icc a b, F (innerCorner K t).1 = (innerCorner K t).2) ∧
      (∀ y ∈ Icc (innerCorner K b).1 (innerCorner K a).1,
        ∃ t ∈ Icc a b, (innerCorner K t).1 = y) := by
  have hanti := hmargin.strictAnti_core hK hc ha hb
  have hcX : ContinuousOn (fun t => (innerCorner K t).1) (Icc a b) :=
    (opt_innerCorner_continuous hK.2.1).fst.continuousOn
  have horder : (innerCorner K b).1 < (innerCorner K a).1 :=
    hanti ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
  obtain ⟨L, hL, hSlope⟩ := core_verticalSlopeBound hK hmargin hc ha hb
  have hrange : ∀ p ∈ innerCorner K '' Icc a b,
      p.1 ∈ Icc (innerCorner K b).1 (innerCorner K a).1 := by
    rintro p ⟨t, ht, rfl⟩
    exact ⟨hanti.antitoneOn ht ⟨hab.le, le_rfl⟩ ht.2,
      hanti.antitoneOn ⟨le_rfl, hab.le⟩ ht ht.1⟩
  have hcover : ∀ y ∈ Icc (innerCorner K b).1 (innerCorner K a).1,
      ∃ t ∈ Icc a b, (innerCorner K t).1 = y := by
    intro y hy
    exact intermediate_value_Icc' hab.le hcX hy
  obtain ⟨γ, hgraph, hLip⟩ := exists_roof_function hrange (by
    intro y hy
    obtain ⟨t, ht, he⟩ := hcover y hy
    exact ⟨innerCorner K t, mem_image_of_mem _ ht, he⟩) hSlope
  let F := fun y => γ (max (innerCorner K b).1 (min y (innerCorner K a).1))
  have hF : Continuous F := continuous_clamped_roof horder.le hL hLip
  refine ⟨F, hF, ?_, hcover⟩
  intro t ht
  have hp := hrange _ (mem_image_of_mem _ ht)
  have hy := ((hgraph _).1 (mem_image_of_mem _ ht)).2
  dsimp [F]
  rw [min_eq_left hp.2, max_eq_right hp.1]
  exact hy.symm

end MovingSofaStability
