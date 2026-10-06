module

public import MovingSofaStability.ConvexParallelArea

/-!
# Area distance from actual-set closeness

Uncompiled proof source. A convex parallel layer and a thin vertical niche
band control S minus G. The area deficit then controls the opposite difference.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open scoped Pointwise
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

theorem roof_gap_of_close_point {K : Set Point} {a b H L : ℝ} {γ : ℝ → ℝ}
    (h : CapRoofData K a b H L γ) {p q : Point} {d : ℝ}
    (hp : p ∈ niche K (π / 2)) (hq : q ∈ capShape K)
    (hd : euclideanDist p q ≤ d) : γ p.1 - p.2 ≤ (L + 1) * d := by
  rw [h.niche_eq] at hp
  have hx : |p.1 - q.1| ≤ d := (abs_fst_le_norm2 (p - q)).trans hd
  have hy : |p.2 - q.2| ≤ d := (abs_snd_le_norm2 (p - q)).trans hd
  have hy0 := h.cap.snd_nonneg hq.1
  have hroof : γ p.1 - q.2 ≤ L * d := by
    by_cases hqa : a ≤ q.1
    · by_cases hqb : q.1 ≤ b
      · have hqy : γ q.1 ≤ q.2 := by
          by_contra hn
          exact hq.2 (by rw [h.niche_eq]; exact ⟨⟨hqa, hqb⟩, hy0, not_le.mp hn⟩)
        have he := (abs_le.mp (h.roof_lipschitz p.1 hp.1 q.1 ⟨hqa, hqb⟩)).2
        have hm := mul_le_mul_of_nonneg_left hx h.slope_nonneg
        linarith
      · have hqb' : b < q.1 := not_le.mp hqb
        have he := (abs_le.mp (h.roof_lipschitz p.1 hp.1 b ⟨h.order.le, le_rfl⟩)).2
        rw [h.right_zero, sub_zero, abs_of_nonpos (sub_nonpos.mpr hp.1.2)] at he
        have hbd : b - p.1 ≤ d := by
          have he := (abs_le.mp hx).1
          linarith
        have hm := mul_le_mul_of_nonneg_left hbd h.slope_nonneg
        linarith
    · have hqa' : q.1 < a := not_le.mp hqa
      have he := (abs_le.mp (h.roof_lipschitz p.1 hp.1 a ⟨le_rfl, h.order.le⟩)).2
      rw [h.left_zero, sub_zero, abs_of_nonneg (sub_nonneg.mpr hp.1.1)] at he
      have had : p.1 - a ≤ d := by
        have he := (abs_le.mp hx).2
        linarith
      have hm := mul_le_mul_of_nonneg_left had h.slope_nonneg
      linarith
  have hdy := (abs_le.mp hy).1
  nlinarith

theorem area_continuous_band {F : ℝ → ℝ} (hF : Continuous F) {a b e : ℝ}
    (hab : a ≤ b) (he : 0 ≤ e) :
    area (regionBetween (fun x => F x - 2 * e) (fun x => F x + e) (Icc a b)) =
      3 * e * (b - a) := by
  sorry

theorem CapRoofData.outer_area_bound {K : Set Point} {a b H L : ℝ} {γ : ℝ → ℝ}
    (h : CapRoofData K a b H L γ) :
    ∃ A : ℝ, 0 < A ∧ ∀ S : Set Point, IsCompact S → ∀ d ∈ Ioc (0 : ℝ) 1,
      DirectedClose d S (capShape K) → area (S \ capShape K) ≤ A * d := by
  sorry

theorem symmetricDifferenceArea_eq {S G : Set Point} (hS : MeasurableSet S)
    (hG : MeasurableSet G) (hSf : volume S ≠ ⊤) (hGf : volume G ≠ ⊤) :
    symmetricDifferenceArea S G = area G - area S + 2 * area (S \ G) := by
  have hd : Disjoint (S \ G) (G \ S) := by
    rw [Set.disjoint_left]
    intro p hp hq
    exact hp.2 hq.1
  rw [symmetricDifferenceArea, area_union_of_disjoint hd (hG.diff hS)
    (volume_ne_top_of_subset sdiff_subset hSf) (volume_ne_top_of_subset sdiff_subset hGf),
    area_sdiff_balance hS hG hSf hGf]
  ring

theorem gerver_symmetricDifference_from_distance {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {C : ℝ} (hC : 0 < C) :
    ∃ Carea ε₀ : ℝ, 0 < Carea ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ∀ S : Set Point, IsCompact S → ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      ε = area (gerverSofa P) - area S →
      EuclideanClose (C * sqrt ε) S (gerverSofa P) →
        symmetricDifferenceArea S (gerverSofa P) ≤ Carea * sqrt ε := by
  obtain ⟨H, L, γ, hroof⟩ := gerver_roof_data hP hbox
  obtain ⟨A, hA, hbound⟩ := hroof.outer_area_bound
  obtain ⟨ε₀, hε₀, hε₀1, hsmall⟩ := exists_sqrt_threshold hC.le (show (0 : ℝ) < 1 by norm_num)
  let Carea := 1 + 2 * A * C
  refine ⟨Carea, ε₀ / 2, by dsimp [Carea]; positivity, by positivity, by linarith, ?_⟩
  intro S hS ε hε hεeq hclose
  have hεsmall : ε < ε₀ := by linarith [hε.2]
  have hdpos : 0 < C * sqrt ε := mul_pos hC (sqrt_pos.mpr hε.1)
  have hd1 := hsmall ε hε.1.le hεsmall
  have he := hbound S hS (C * sqrt ε) ⟨hdpos, hd1.le⟩
    (by simpa only [gerver_shape_eq hP hbox] using hclose.1)
  rw [gerver_shape_eq hP hbox] at he
  have hG := ms_isCompact_of_isMovingSofaWithAngle (GerverParams.gm_movingSofa_std hP hbox).1
  rw [symmetricDifferenceArea_eq hS.measurableSet hG.measurableSet hS.measure_lt_top.ne
    hG.measure_lt_top.ne, ← hεeq]
  have hs := self_le_sqrt_of_unit ⟨hε.1.le, hεsmall.le.trans hε₀1⟩
  dsimp [Carea]
  nlinarith

end MovingSofaStability
