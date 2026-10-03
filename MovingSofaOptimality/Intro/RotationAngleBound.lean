module

public import MovingSofaOptimality.Monotone.SupportingHallway

/-!
# A first bound on the rotation angle (§1.5)

Theorem 1.5.1 (`thm:rotation-angle-simple-bound`, a modification of page 271 of Gerver's paper).

**Proof.** The area bounds are obtained by horizontal slices (`ang_volume_le_of_slices`): every
horizontal line meets a hallway rotated by `π/4` in a set of length `√2`, and meets a translate of
`V_ω` in a segment of length `sec ω`. For `ω > π/2` the movement is stopped when the sofa has turned
by `π/2` and is then translated horizontally into `V_L`.
-/

@[expose] public section

open Real Set MeasureTheory

namespace MovingSofaOptimality

/-- `sec⁻¹(2.2) = arccos(1/2.2)`. -/
noncomputable def arcsec22 : ℝ := arccos (1 / 2.2)

/-! ### Helper lemmas -/

/-- The area of a set of the plane, sliced horizontally. -/
lemma ang_volume_eq_lintegral_slices {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    volume A = ∫⁻ y, volume {x : ℝ | (x, y) ∈ A} := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hA]
  rfl

/-- A set whose horizontal slices have length at most `ℓ` and which lies in a horizontal strip of
width one has area at most `ℓ`. -/
lemma ang_volume_le_of_slices {S : Set (ℝ × ℝ)} {lo ℓ : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hS : ∀ p ∈ S, lo ≤ p.2 ∧ p.2 ≤ lo + 1 ∧ f p.2 ≤ p.1 ∧ p.1 ≤ f p.2 + ℓ) :
    volume S ≤ ENNReal.ofReal ℓ := by
  set A : Set (ℝ × ℝ) := {p | lo ≤ p.2 ∧ p.2 ≤ lo + 1 ∧ f p.2 ≤ p.1 ∧ p.1 ≤ f p.2 + ℓ} with hAdef
  have hSA : S ⊆ A := fun p hp => hS p hp
  have hA : MeasurableSet A := by
    apply IsClosed.measurableSet
    have h2 : Continuous fun p : ℝ × ℝ => p.2 := continuous_snd
    have h1 : Continuous fun p : ℝ × ℝ => p.1 := continuous_fst
    refine (isClosed_le continuous_const h2).inter ((isClosed_le h2 continuous_const).inter
      ((isClosed_le (hf.comp h2) h1).inter (isClosed_le h1 ((hf.comp h2).add continuous_const))))
  calc volume S ≤ volume A := measure_mono hSA
    _ = ∫⁻ y, volume {x : ℝ | (x, y) ∈ A} := ang_volume_eq_lintegral_slices hA
    _ ≤ ∫⁻ y, (Icc lo (lo + 1)).indicator (fun _ => ENNReal.ofReal ℓ) y := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ Icc lo (lo + 1)
        · rw [indicator_of_mem hy]
          calc volume {x : ℝ | (x, y) ∈ A} ≤ volume (Icc (f y) (f y + ℓ)) := by
                refine measure_mono fun x hx => ?_
                exact ⟨hx.2.2.1, hx.2.2.2⟩
            _ = ENNReal.ofReal ℓ := by rw [Real.volume_Icc]; ring_nf
        · rw [indicator_of_notMem hy]
          have : {x : ℝ | (x, y) ∈ A} = ∅ := by
            ext x
            simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, hAdef]
            intro hx
            exact hy ⟨hx.1, hx.2.1⟩
          rw [this, measure_empty]
    _ = ENNReal.ofReal ℓ * volume (Icc lo (lo + 1)) := lintegral_indicator_const measurableSet_Icc _
    _ = ENNReal.ofReal ℓ := by rw [Real.volume_Icc]; simp

/-- The real-valued form of `ang_volume_le_of_slices`. -/
lemma ang_area_le_of_slices {S : Set (ℝ × ℝ)} {lo ℓ : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hℓ : 0 ≤ ℓ)
    (hS : ∀ p ∈ S, lo ≤ p.2 ∧ p.2 ≤ lo + 1 ∧ f p.2 ≤ p.1 ∧ p.1 ≤ f p.2 + ℓ) :
    area S ≤ ℓ := by
  unfold area
  exact ENNReal.toReal_le_of_le_ofReal hℓ (ang_volume_le_of_slices hf hS)

lemma ang_cos_arcsec22 : cos arcsec22 = 5 / 11 := by
  unfold arcsec22; rw [cos_arccos] <;> norm_num

lemma ang_arcsec22_le_pi_div_two : arcsec22 ≤ π / 2 := by
  unfold arcsec22; rw [arccos_le_pi_div_two]; norm_num

lemma ang_arcsec22_pos : 0 < arcsec22 := by
  unfold arcsec22; rw [arccos_pos]; norm_num

lemma ang_pi_div_four_lt_arcsec22 : π / 4 < arcsec22 := by
  have h1 : cos arcsec22 < cos (π / 4) := by
    rw [ang_cos_arcsec22, cos_pi_div_four]
    have : (1.4 : ℝ) < √2 := by
      rw [show (1.4 : ℝ) = √(1.4 ^ 2) by rw [sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  by_contra h
  rw [not_lt] at h
  have := cos_le_cos_of_nonneg_of_le_pi ang_arcsec22_pos.le (by linarith [pi_pos]) h
  linarith

/-- Case `ω ≤ -π/4` of Theorem 1.5.1: the area bound `√2`. -/
lemma ang_area_le_sqrt_two {S : Set (ℝ × ℝ)} {c₀ c₁ : ℝ × ℝ}
    (h0 : ∀ p ∈ S, p + c₀ ∈ horizSide) (h1 : ∀ p ∈ S, rot (π / 4) p + c₁ ∈ hallway) :
    area S ≤ √2 := by
  have hr : (0 : ℝ) < √2 := by positivity
  have hr2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  refine ang_area_le_of_slices (lo := -c₀.2)
    (f := fun y => y + √2 * (min (-(√2 * y) + c₁.1 - c₁.2) 0 - c₁.1)) (by fun_prop) hr.le ?_
  intro p hp
  obtain ⟨-, hy0, hy1⟩ := h0 p hp
  simp only [Prod.snd_add] at hy0 hy1
  have hL := h1 p hp
  set X := (rot (π / 4) p + c₁).1 with hX
  set Y := (rot (π / 4) p + c₁).2 with hY
  have hX' : X = √2 / 2 * (p.1 - p.2) + c₁.1 := by
    simp only [hX, rot, cos_pi_div_four, sin_pi_div_four, Prod.fst_add]; ring
  have hY' : Y = √2 / 2 * (p.1 + p.2) + c₁.2 := by
    simp only [hY, rot, cos_pi_div_four, sin_pi_div_four, Prod.snd_add]; ring
  have hXY : X - Y = -(√2 * p.2) + c₁.1 - c₁.2 := by rw [hX', hY']; ring
  -- `m ≤ X ≤ m + 1` with `m = min (X - Y) 0`
  have hm : min (X - Y) 0 ≤ X ∧ X ≤ min (X - Y) 0 + 1 := by
    rcases hL with ⟨hx1, hy0', hy1'⟩ | ⟨hx0, hx1, hy1'⟩
    · refine ⟨(min_le_left _ _).trans (by linarith), ?_⟩
      rcases min_cases (X - Y) 0 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith
    · refine ⟨(min_le_right _ _).trans hx0, ?_⟩
      rcases min_cases (X - Y) 0 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith
  rw [hXY] at hm
  have hx : p.1 = p.2 + √2 * (X - c₁.1) := by
    rw [hX']; linear_combination (-(p.1 - p.2) / 2) * hr2
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · rw [hx]; nlinarith [hm.1]
  · rw [hx]; nlinarith [hm.2]

/-- Case `|ω| < sec⁻¹(2.2)` of Theorem 1.5.1: the area bound `sec ω`. -/
lemma ang_area_le_sec {S : Set (ℝ × ℝ)} {c₀ c₁ : ℝ × ℝ} {ω : ℝ} (hcos : 0 < cos ω)
    (h0 : ∀ p ∈ S, p + c₀ ∈ horizSide) (h1 : ∀ p ∈ S, rot (-ω) p + c₁ ∈ vertSide) :
    area S ≤ 1 / cos ω := by
  refine ang_area_le_of_slices (lo := -c₀.2) (f := fun y => (-c₁.1 - sin ω * y) / cos ω)
    (by fun_prop) (by positivity) ?_
  intro p hp
  obtain ⟨-, hy0, hy1⟩ := h0 p hp
  obtain ⟨hx0, hx1, -⟩ := h1 p hp
  simp only [Prod.fst_add, Prod.snd_add, rot, cos_neg, sin_neg] at hy0 hy1 hx0 hx1
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · rw [div_le_iff₀ hcos]; nlinarith
  · rw [← add_div, le_div_iff₀ hcos]; nlinarith

/-- Translating a point of `L` horizontally towards a point of `V_L` stays inside `L`. -/
lemma ang_hallway_translate {P : ℝ × ℝ} {δ l : ℝ} (hP : P ∈ hallway)
    (hP' : P + (δ, 0) ∈ vertSide) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) : P + (l * δ, 0) ∈ hallway := by
  obtain ⟨hx0', hx1', hy1'⟩ := hP'
  simp only [Prod.fst_add, Prod.snd_add, add_zero] at hx0' hx1' hy1'
  rcases hP with ⟨hx1, hy0, hy1⟩ | ⟨hx0, hx1, hy1⟩
  · left
    refine ⟨?_, ?_, ?_⟩ <;> simp only [Prod.fst_add, Prod.snd_add, add_zero]
    · nlinarith [mul_nonneg (sub_nonneg.2 hl1) (sub_nonneg.2 hx1),
        mul_nonneg hl0 (sub_nonneg.2 hx1')]
    · exact hy0
    · exact hy1
  · right
    refine ⟨?_, ?_, ?_⟩ <;> simp only [Prod.fst_add, Prod.snd_add, add_zero]
    · nlinarith [mul_nonneg (sub_nonneg.2 hl1) hx0, mul_nonneg hl0 hx0']
    · nlinarith [mul_nonneg (sub_nonneg.2 hl1) (sub_nonneg.2 hx1),
        mul_nonneg hl0 (sub_nonneg.2 hx1')]
    · exact hy1

/-- **Theorem 1.5.1** (`thm:rotation-angle-simple-bound`). A moving sofa of area at least `2.2`
admits a movement in `L` with rotation angle `ω ∈ [sec⁻¹(2.2), π/2]`. -/
theorem theorem1_5_1 {S : Set (ℝ × ℝ)} (hS : IsMovingSofa S) (harea : 2.2 ≤ area S) :
    ∃ ω ∈ Icc arcsec22 (π / 2), IsMovingSofaWithAngle S ω := by
  obtain ⟨ω, hcl, hconn, θ, c, hm⟩ := hS
  have hstart : ∀ p ∈ S, p + c 0 ∈ horizSide := by
    intro p hp; have := hm.start p hp; rwa [hm.angle_zero, rot_zero] at this
  -- the rotation angle is larger than `-π/4`
  have hω1 : -(π / 4) < ω := by
    by_contra h
    rw [not_lt] at h
    have hmem : π / 4 ∈ Icc (θ 0) (θ 1) := by
      rw [hm.angle_zero, hm.angle_one]; constructor <;> linarith [pi_pos]
    obtain ⟨s, hs, hθs⟩ := intermediate_value_Icc (zero_le_one' ℝ) hm.continuousOn_angle hmem
    have h1 : ∀ p ∈ S, rot (π / 4) p + c s ∈ hallway := by
      intro p hp; rw [← hθs]; exact hm.inside s hs p hp
    have h2 := ang_area_le_sqrt_two hstart h1
    have h3 : √2 < 2.2 := by
      rw [show (2.2 : ℝ) = √(2.2 ^ 2) by rw [sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  -- the rotation angle is at least `sec⁻¹(2.2)`
  have hω2 : arcsec22 ≤ ω := by
    by_contra h
    rw [not_le] at h
    have hcos : 5 / 11 < cos ω := by
      rw [← cos_abs, ← ang_cos_arcsec22]
      apply cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _)
        (by linarith [ang_arcsec22_le_pi_div_two, pi_pos])
      rw [abs_lt]; constructor <;> linarith [ang_pi_div_four_lt_arcsec22]
    have hfin : ∀ p ∈ S, rot (-ω) p + c 1 ∈ vertSide := by
      intro p hp; have := hm.finish p hp; rwa [hm.angle_one] at this
    have h2 := ang_area_le_sec (by linarith) hstart hfin
    have h3 : 1 / cos ω < 2.2 := by rw [div_lt_iff₀ (by linarith)]; linarith
    linarith
  by_cases hω3 : ω ≤ π / 2
  · exact ⟨ω, ⟨hω2, hω3⟩, hcl, hconn, θ, c, hm⟩
  rw [not_le] at hω3
  refine ⟨π / 2, ⟨ang_arcsec22_le_pi_div_two, le_rfl⟩, hcl, hconn, ?_⟩
  -- stop the movement when the sofa has rotated by `π/2`, then translate it into `V_L`
  obtain ⟨s₀, hs₀, hθs₀⟩ : ∃ s₀ ∈ Icc (0 : ℝ) 1, θ s₀ = -(π / 2) := by
    apply intermediate_value_Icc' (zero_le_one' ℝ) hm.continuousOn_angle
    rw [hm.angle_zero, hm.angle_one]; constructor <;> linarith [pi_pos]
  have hs₀1 : s₀ < 1 := by
    rcases eq_or_lt_of_le hs₀.2 with h | h
    · rw [h, hm.angle_one] at hθs₀; linarith
    · exact h
  have hpos : 0 < 1 - s₀ := by linarith
  set δ := (c 0).2 - (c s₀).1 with hδ
  have hmaps : MapsTo (fun s : ℝ => min s s₀) (Icc 0 1) (Icc 0 1) := fun s hs =>
    ⟨le_min hs.1 hs₀.1, (min_le_left _ _).trans hs.2⟩
  have hmin_cont : Continuous fun s : ℝ => min s s₀ := continuous_id.min continuous_const
  refine ⟨fun s => θ (min s s₀), fun s => c (min s s₀) + (max 0 ((s - s₀) / (1 - s₀)) * δ, 0),
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact hm.continuousOn_angle.comp hmin_cont.continuousOn hmaps
  · refine (hm.continuousOn_shift.comp hmin_cont.continuousOn hmaps).add ?_
    exact (Continuous.prodMk (by fun_prop) continuous_const).continuousOn
  · simp only [min_eq_left hs₀.1, hm.angle_zero]
  · simp only [min_eq_right hs₀.2, hθs₀]
  · intro p hp
    have hmx : max 0 ((0 - s₀) / (1 - s₀)) = 0 :=
      max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith [hs₀.1]) hpos.le)
    simp only [min_eq_left hs₀.1, hmx, zero_mul, Prod.mk_zero_zero, add_zero]
    exact hm.start p hp
  · intro s hs p hp
    by_cases hss : s ≤ s₀
    · have hmx : max 0 ((s - s₀) / (1 - s₀)) = 0 :=
        max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le)
      simp only [min_eq_left hss, hmx, zero_mul, Prod.mk_zero_zero, add_zero]
      exact hm.inside s hs p hp
    · rw [not_le] at hss
      have hl0 : 0 ≤ (s - s₀) / (1 - s₀) := div_nonneg (by linarith) hpos.le
      have hl1 : (s - s₀) / (1 - s₀) ≤ 1 := by rw [div_le_one hpos]; linarith [hs.2]
      simp only [min_eq_right hss.le, max_eq_right hl0, hθs₀]
      rw [← add_assoc]
      have hP := hm.inside s₀ hs₀ p hp
      rw [hθs₀] at hP
      refine ang_hallway_translate hP ?_ hl0 hl1
      have hy1 : (rot (-(π / 2)) p + c s₀).2 ≤ 1 := by
        rcases hP with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> exact h
      obtain ⟨-, hy0', hy1'⟩ := hstart p hp
      simp only [Prod.snd_add] at hy0' hy1'
      refine ⟨?_, ?_, ?_⟩ <;>
        simp only [Prod.fst_add, Prod.snd_add, rot, cos_neg, sin_neg, cos_pi_div_two,
          sin_pi_div_two, add_zero, hδ] at hy1 ⊢
      · linarith
      · linarith
      · linarith
  · intro p hp
    have hl : max 0 ((1 - s₀) / (1 - s₀)) = 1 := by rw [div_self hpos.ne']; norm_num
    simp only [min_eq_right hs₀.2, hl, one_mul, hθs₀]
    have hP := hm.inside s₀ hs₀ p hp
    rw [hθs₀] at hP
    have hy1 : (rot (-(π / 2)) p + c s₀).2 ≤ 1 := by
      rcases hP with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> exact h
    obtain ⟨-, hy0', hy1'⟩ := hstart p hp
    simp only [Prod.snd_add] at hy0' hy1'
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add, rot, cos_neg, sin_neg, cos_pi_div_two,
        sin_pi_div_two, add_zero, hδ] at hy1 ⊢
    · linarith
    · linarith
    · linarith

end MovingSofaOptimality
