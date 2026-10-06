module

public import MovingSofaStability.ConvexParallelArea

/-!
# Area distance from actual-set closeness

Uncompiled proof source. A point outside Gerver's cap lies in a convex parallel
layer. A point in its niche but close to the sofa lies in a thin vertical roof
band. These two regions control S minus G, and the area deficit controls the
opposite set difference. No continuity of nonconvex area is assumed.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open scoped Pointwise
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- A point in the niche and within distance d of the reference shape is at
most (L+1)d below its Lipschitz roof. -/
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

/-- A vertical band around a continuous graph has exactly its width times
its base length. The open band avoids any separate graph-null-set argument. -/
theorem area_continuous_band {F : ℝ → ℝ} (hF : Continuous F) {a b e : ℝ}
    (hab : a ≤ b) (he : 0 ≤ e) :
    area (regionBetween (fun x => F x - 2 * e) (fun x => F x + e) (Icc a b)) =
      3 * e * (b - a) := by
  have h1 : IntegrableOn (fun x => F x - 2 * e) (Icc a b) :=
    (hF.sub continuous_const).integrableOn_Icc
  have h2 : IntegrableOn (fun x => F x + e) (Icc a b) :=
    (hF.add continuous_const).integrableOn_Icc
  unfold area
  rw [volume_regionBetween_eq_integral h1 h2 measurableSet_Icc (fun x hx => by linarith)]
  have hi : (∫ x in Icc a b, (F x + e) - (F x - 2 * e)) = 3 * e * (b - a) := by
    have heq : (fun x => (F x + e) - (F x - 2 * e)) = fun _ : ℝ => 3 * e := by funext x; ring
    rw [heq, integral_const]
    simp only [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul]
    ring
  rw [hi, ENNReal.toReal_ofReal (by positivity)]

/-- The reference shape has an outer one-sided area modulus linear in actual
Euclidean distance. The original set S need not be convex or monotone. -/
theorem CapRoofData.outer_area_bound {K : Set Point} {a b H L : ℝ} {γ : ℝ → ℝ}
    (h : CapRoofData K a b H L γ) :
    ∃ A : ℝ, 0 < A ∧ ∀ S : Set Point, IsCompact S → ∀ d ∈ Ioc (0 : ℝ) 1,
      DirectedClose d S (capShape K) → area (S \ capShape K) ≤ A * d := by
  obtain ⟨A0, hA0, hparallel⟩ := exists_parallel_layer_constant h.cap.2.1
    (interior_nonempty_of_box h.order (by norm_num) h.rectangle)
  let A := A0 + 3 * (L + 1) * (b - a)
  have hA : 0 < A := by dsimp [A]; have := h.slope_nonneg; have := h.order; positivity
  let F : ℝ → ℝ := fun x => γ (min b (max a x))
  have hF : Continuous F := continuous_clamped_roof h.order.le h.slope_nonneg h.roof_lipschitz
  have hFeq : ∀ x ∈ Icc a b, F x = γ x := by
    intro x hx
    simp only [F, max_eq_right hx.1, min_eq_right hx.2]
  refine ⟨A, hA, ?_⟩
  intro S hS d hd hclose
  let E := S \ capShape K
  let Eout := E \ K
  let Ein := E ∩ K
  have hEf : volume E ≠ ⊤ := volume_ne_top_of_subset sdiff_subset hS.measure_lt_top.ne
  have hout : Eout ⊆ (K + euclideanDisk d) \ K := by
    rintro p ⟨⟨hpS, hpG⟩, hpK⟩
    obtain ⟨q, hq, hpq⟩ := hclose p hpS
    refine ⟨⟨q, hq.1, p - q, hpq, ?_⟩, hpK⟩
    abel
  have hareaOut := hparallel d ⟨hd.1.le, hd.2⟩ Eout hout
  let e := (L + 1) * d
  have he : 0 < e := mul_pos (by linarith [h.slope_nonneg]) hd.1
  let Band := regionBetween (fun x => F x - 2 * e) (fun x => F x + e) (Icc a b)
  have hin : Ein ⊆ Band := by
    rintro p ⟨⟨hpS, hpG⟩, hpK⟩
    have hpN : p ∈ niche K (π / 2) := by
      by_contra hn
      exact hpG ⟨hpK, hn⟩
    obtain ⟨q, hq, hpq⟩ := hclose p hpS
    have hgap := roof_gap_of_close_point h hpN hq hpq
    rw [h.niche_eq] at hpN
    refine ⟨hpN.1, ?_, ?_⟩
    · rw [hFeq p.1 hpN.1]
      change γ p.1 - 2 * e < p.2
      change γ p.1 - p.2 ≤ e at hgap
      linarith
    · rw [hFeq p.1 hpN.1]
      linarith [hpN.2.2]
  have hBandf : volume Band ≠ ⊤ := by
    have h1 := (hF.sub continuous_const).integrableOn_Icc (a := a) (b := b)
    have h2 := (hF.add continuous_const).integrableOn_Icc (a := a) (b := b)
    rw [show volume Band = ENNReal.ofReal
      (∫ x in Icc a b, (F x + e) - (F x - 2 * e)) from
        volume_regionBetween_eq_integral h1 h2 measurableSet_Icc (fun x hx => by linarith)]
    exact ENNReal.ofReal_ne_top
  have hareaIn := area_mono_of_finite hin hBandf
  rw [area_continuous_band hF h.order.le he.le] at hareaIn
  have hsplit := area_inter_add_sdiff (S := E) h.cap.2.1.2.1.measurableSet hEf
  change area Ein + area Eout = area E at hsplit
  dsimp [A, e] at *
  linarith

/-- The two directed differences sum to the symmetric-difference area. -/
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

/-- Actual-set Hausdorff recovery implies area-distance recovery at the same
square-root rate for Gerver's fixed reference geometry. -/
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
  refine ⟨Carea, by dsimp [Carea]; positivity, ε₀ / 2, by positivity,
    (by linarith), ?_⟩
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
