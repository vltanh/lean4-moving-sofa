module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Interval arithmetic for the parameters of Gerver's sofa

Helper lemmas for the numerical part of `MovingSofa.Gerver.Romik`:

* elementary interval arithmetic (`rom_iv_add`, `rom_iv_mul`, …): each lemma derives an enclosure
  `x ∘ y ∈ [L, U]` from enclosures of `x` and `y` and rational side conditions on the endpoints,
  which `norm_num` checks;
* rigorous Taylor bounds for `cos` and `sin` on `[0, 1]` (alternating series), and from them
  enclosures of `cos` and `sin` on the box `[0.039, 0.04] × [0.68, 0.69]`, at the approximate
  solution `(φ₀, θ₀) = (0.0391773648, 0.6813015094)`, and on the square of radius `10⁻¹⁰` around it.
-/

@[expose] public section

open Real Set Finset

namespace MovingSofa

/-! ### Interval arithmetic -/

theorem rom_iv_self (x : ℝ) : x ∈ Icc x x := ⟨le_rfl, le_rfl⟩

theorem rom_iv_add {x y a b c d L U : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (h : L ≤ a + c ∧ b + d ≤ U) : x + y ∈ Icc L U :=
  ⟨by linarith [hx.1, hy.1, h.1], by linarith [hx.2, hy.2, h.2]⟩

theorem rom_iv_sub {x y a b c d L U : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (h : L ≤ a - d ∧ b - c ≤ U) : x - y ∈ Icc L U :=
  ⟨by linarith [hx.1, hy.2, h.1], by linarith [hx.2, hy.1, h.2]⟩

theorem rom_iv_neg {x a b L U : ℝ} (hx : x ∈ Icc a b) (h : L ≤ -b ∧ -a ≤ U) : -x ∈ Icc L U :=
  ⟨by linarith [hx.2, h.1], by linarith [hx.1, h.2]⟩

theorem rom_iv_div {x a b k L U : ℝ} (hx : x ∈ Icc a b) (h : 0 < k ∧ L ≤ a / k ∧ b / k ≤ U) :
    x / k ∈ Icc L U :=
  ⟨h.2.1.trans (div_le_div_of_nonneg_right hx.1 h.1.le),
    (div_le_div_of_nonneg_right hx.2 h.1.le).trans h.2.2⟩

theorem rom_iv_div2 {x y a b c d L U : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (h : 0 < c ∧ 0 ≤ a ∧ L ≤ a / d ∧ b / c ≤ U) : x / y ∈ Icc L U := by
  obtain ⟨hc, ha, hL, hU⟩ := h
  have hy0 : 0 < y := hc.trans_le hy.1
  refine ⟨hL.trans ?_, le_trans ?_ hU⟩
  · calc a / d ≤ a / y := div_le_div_of_nonneg_left ha hy0 hy.2
      _ ≤ x / y := div_le_div_of_nonneg_right hx.1 hy0.le
  · calc x / y ≤ b / y := div_le_div_of_nonneg_right hx.2 hy0.le
      _ ≤ b / c := div_le_div_of_nonneg_left (ha.trans (hx.1.trans hx.2)) hc hy.1

theorem rom_iv_mul_nn {x y a b c d L U : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (h : 0 ≤ a ∧ 0 ≤ c ∧ L ≤ a * c ∧ b * d ≤ U) : x * y ∈ Icc L U := by
  obtain ⟨ha, hc, hL, hU⟩ := h
  refine ⟨hL.trans (mul_le_mul hx.1 hy.1 hc (ha.trans hx.1)), ?_⟩
  exact (mul_le_mul hx.2 hy.2 (hc.trans hy.1) ((ha.trans hx.1).trans hx.2)).trans hU

theorem rom_mul_mem_corners {x y a b c d : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  obtain ⟨hax, hxb⟩ := hx
  obtain ⟨hcy, hyd⟩ := hy
  have k1 : min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y) := by
    rcases le_total 0 y with h | h
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hax h),
        (mul_le_mul_of_nonneg_right hxb h).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hxb h),
        (mul_le_mul_of_nonpos_right hax h).trans (le_max_left _ _)⟩
  have k2 : ∀ u : ℝ, min (u * c) (u * d) ≤ u * y ∧ u * y ≤ max (u * c) (u * d) := by
    intro u
    rcases le_total 0 u with h | h
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hcy h),
        (mul_le_mul_of_nonneg_left hyd h).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hyd h),
        (mul_le_mul_of_nonpos_left hcy h).trans (le_max_left _ _)⟩
  obtain ⟨ka1, ka2⟩ := k2 a
  obtain ⟨kb1, kb2⟩ := k2 b
  constructor
  · refine le_trans ?_ k1.1
    rcases min_choice (a * y) (b * y) with h | h <;> rw [h]
    · exact (min_le_left _ _).trans ka1
    · exact (min_le_right _ _).trans kb1
  · refine k1.2.trans ?_
    rcases max_choice (a * y) (b * y) with h | h <;> rw [h]
    · exact ka2.trans (le_max_left _ _)
    · exact kb2.trans (le_max_right _ _)

theorem rom_iv_mul {x y a b c d L U : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (h : (L ≤ a * c ∧ L ≤ a * d ∧ L ≤ b * c ∧ L ≤ b * d) ∧
      (a * c ≤ U ∧ a * d ≤ U ∧ b * c ≤ U ∧ b * d ≤ U)) : x * y ∈ Icc L U := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8⟩ := h
  obtain ⟨k1, k2⟩ := rom_mul_mem_corners hx hy
  exact ⟨le_trans (le_min (le_min h1 h2) (le_min h3 h4)) k1,
    k2.trans (max_le (max_le h5 h6) (max_le h7 h8))⟩

/-- Enlarge an enclosure. -/
theorem rom_iv_mono {x a b L U : ℝ} (hx : x ∈ Icc a b) (h : L ≤ a ∧ b ≤ U) : x ∈ Icc L U :=
  ⟨h.1.trans hx.1, hx.2.trans h.2⟩

/-! ### Taylor bounds for `cos` and `sin` -/

theorem rom_antitone_cos_terms {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Antitone (fun n : ℕ => x ^ (2 * n) / ((2 * n).factorial : ℝ)) := by
  refine antitone_nat_of_succ_le (fun n => ?_)
  have hx2 : x ^ (2 * (n + 1)) ≤ x ^ (2 * n) := pow_le_pow_of_le_one h0 h1 (by omega)
  have hf : ((2 * n).factorial : ℝ) ≤ ((2 * (n + 1)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hpos : (0 : ℝ) < ((2 * n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  exact div_le_div₀ (pow_nonneg h0 _) hx2 hpos hf

theorem rom_antitone_sin_terms {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Antitone (fun n : ℕ => x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) := by
  refine antitone_nat_of_succ_le (fun n => ?_)
  have hx2 : x ^ (2 * (n + 1) + 1) ≤ x ^ (2 * n + 1) := pow_le_pow_of_le_one h0 h1 (by omega)
  have hf : ((2 * n + 1).factorial : ℝ) ≤ ((2 * (n + 1) + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hpos : (0 : ℝ) < ((2 * n + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  exact div_le_div₀ (pow_nonneg h0 _) hx2 hpos hf

theorem rom_cos_tendsto (x : ℝ) : Filter.Tendsto
    (fun n => ∑ i ∈ range n, (-1) ^ i * (x ^ (2 * i) / ((2 * i).factorial : ℝ)))
    Filter.atTop (nhds (cos x)) := by
  simpa only [mul_div_assoc] using (Real.hasSum_cos x).tendsto_sum_nat

theorem rom_sin_tendsto (x : ℝ) : Filter.Tendsto
    (fun n => ∑ i ∈ range n, (-1) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)))
    Filter.atTop (nhds (sin x)) := by
  simpa only [mul_div_assoc] using (Real.hasSum_sin x).tendsto_sum_nat

theorem rom_cos_ge {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (k : ℕ) :
    ∑ i ∈ range (2 * k), (-1) ^ i * (x ^ (2 * i) / ((2 * i).factorial : ℝ)) ≤ cos x :=
  (rom_antitone_cos_terms h0 h1).alternating_series_le_tendsto (rom_cos_tendsto x) k

theorem rom_cos_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (k : ℕ) :
    cos x ≤ ∑ i ∈ range (2 * k + 1), (-1) ^ i * (x ^ (2 * i) / ((2 * i).factorial : ℝ)) :=
  (rom_antitone_cos_terms h0 h1).tendsto_le_alternating_series (rom_cos_tendsto x) k

theorem rom_sin_ge {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (k : ℕ) :
    ∑ i ∈ range (2 * k), (-1) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)) ≤ sin x :=
  (rom_antitone_sin_terms h0 h1).alternating_series_le_tendsto (rom_sin_tendsto x) k

theorem rom_sin_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (k : ℕ) :
    sin x ≤ ∑ i ∈ range (2 * k + 1), (-1) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)) :=
  (rom_antitone_sin_terms h0 h1).tendsto_le_alternating_series (rom_sin_tendsto x) k

/-! ### Enclosures of `π`, `cos` and `sin` -/

theorem rom_pi_mem6 : π ∈ Icc (3.141592 : ℝ) 3.141593 := ⟨pi_gt_d6.le, pi_lt_d6.le⟩

theorem rom_pi_mem20 : π ∈ Icc (3.14159265358979323846 : ℝ) 3.14159265358979323847 :=
  ⟨pi_gt_d20.le, pi_lt_d20.le⟩

/-- `cos` on `[0.039, 0.04]`. -/
theorem rom_cos_box {x : ℝ} (hx : x ∈ Icc (0.039 : ℝ) 0.04) :
    cos x ∈ Icc (0.9992001066 : ℝ) 1 := by
  refine ⟨?_, cos_le_one x⟩
  have h : (0.9992001066 : ℝ) ≤ cos 0.04 := by
    refine le_trans ?_ (rom_cos_ge (by norm_num) (by norm_num) 3)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  exact h.trans (cos_le_cos_of_nonneg_of_le_pi (by linarith [hx.1])
    (by linarith [pi_gt_three]) hx.2)

/-- `sin` on `[0.039, 0.04]`. -/
theorem rom_sin_box {x : ℝ} (hx : x ∈ Icc (0.039 : ℝ) 0.04) :
    sin x ∈ Icc (0.0389901142 : ℝ) 0.0399893342 := by
  have h1 : (0.0389901142 : ℝ) ≤ sin 0.039 := by
    refine le_trans ?_ (rom_sin_ge (by norm_num) (by norm_num) 3)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have h2 : sin 0.04 ≤ (0.0399893342 : ℝ) := by
    refine (rom_sin_le (by norm_num) (by norm_num) 3).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have hpi := pi_gt_three
  exact ⟨h1.trans (sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith [hx.2]) hx.1),
    (sin_le_sin_of_le_of_le_pi_div_two (by linarith [hx.1]) (by linarith) hx.2).trans h2⟩

/-- `cos` on `[0.68, 0.69]`. -/
theorem rom_cos_box' {x : ℝ} (hx : x ∈ Icc (0.68 : ℝ) 0.69) :
    cos x ∈ Icc (0.7712460149 : ℝ) 0.7775727188 := by
  have h1 : (0.7712460149 : ℝ) ≤ cos 0.69 := by
    refine le_trans ?_ (rom_cos_ge (by norm_num) (by norm_num) 3)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have h2 : cos 0.68 ≤ (0.7775727188 : ℝ) := by
    refine (rom_cos_le (by norm_num) (by norm_num) 3).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have hpi := pi_gt_three
  exact ⟨h1.trans (cos_le_cos_of_nonneg_of_le_pi (by linarith [hx.1]) (by linarith) hx.2),
    (cos_le_cos_of_nonneg_of_le_pi (by norm_num) (by linarith [hx.2]) hx.1).trans h2⟩

/-- `sin` on `[0.68, 0.69]`. -/
theorem rom_sin_box' {x : ℝ} (hx : x ∈ Icc (0.68 : ℝ) 0.69) :
    sin x ∈ Icc (0.628793024 : ℝ) 0.6365371823 := by
  have h1 : (0.628793024 : ℝ) ≤ sin 0.68 := by
    refine le_trans ?_ (rom_sin_ge (by norm_num) (by norm_num) 3)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have h2 : sin 0.69 ≤ (0.6365371823 : ℝ) := by
    refine (rom_sin_le (by norm_num) (by norm_num) 3).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have hpi := pi_gt_three
  exact ⟨h1.trans (sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith [hx.2]) hx.1),
    (sin_le_sin_of_le_of_le_pi_div_two (by linarith [hx.1]) (by linarith) hx.2).trans h2⟩

/-- `cos φ₀` for `φ₀ = 0.0391773648`. -/
theorem rom_cos_φ₀ :
    cos (0.0391773648 : ℝ) ∈ Icc (0.9992326651975322477872 : ℝ) 0.9992326651975323854325 := by
  constructor
  · refine le_trans ?_ (rom_cos_ge (by norm_num) (by norm_num) 2)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  · refine (rom_cos_le (by norm_num) (by norm_num) 2).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num

/-- `sin φ₀` for `φ₀ = 0.0391773648`. -/
theorem rom_sin_φ₀ :
    sin (0.0391773648 : ℝ) ∈ Icc (0.0391673435687965833708 : ℝ) 0.0391673435687965839701 := by
  constructor
  · refine le_trans ?_ (rom_sin_ge (by norm_num) (by norm_num) 2)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  · refine (rom_sin_le (by norm_num) (by norm_num) 2).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num

/-- `cos θ₀` for `θ₀ = 0.6813015094`. -/
theorem rom_cos_θ₀ :
    cos (0.6813015094 : ℝ) ∈ Icc (0.7767536803750504317898 : ℝ) 0.7767536803750505347834 := by
  constructor
  · refine le_trans ?_ (rom_cos_ge (by norm_num) (by norm_num) 4)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  · refine (rom_cos_le (by norm_num) (by norm_num) 4).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num

/-- `sin θ₀` for `θ₀ = 0.6813015094`. -/
theorem rom_sin_θ₀ :
    sin (0.6813015094 : ℝ) ∈ Icc (0.6298045093708156586206 : ℝ) 0.6298045093708156627483 := by
  constructor
  · refine le_trans ?_ (rom_sin_ge (by norm_num) (by norm_num) 4)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  · refine (rom_sin_le (by norm_num) (by norm_num) 4).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num

/-- Moving the argument of `cos` or `sin` by at most `r` moves the value by at most `r`. -/
theorem rom_lip_mem {f : ℝ → ℝ} (hf : ∀ x y, |f x - f y| ≤ |x - y|) {x x₀ r a b : ℝ}
    (hx : x ∈ Icc (x₀ - r) (x₀ + r)) (h₀ : f x₀ ∈ Icc a b) : f x ∈ Icc (a - r) (b + r) := by
  have h1 := hf x x₀
  have h2 : |x - x₀| ≤ r := abs_sub_le_iff.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have h3 := (abs_sub_le_iff.1 (h1.trans h2))
  exact ⟨by linarith [h₀.1, h3.2], by linarith [h₀.2, h3.1]⟩

/-- `cos` near `φ₀`. -/
theorem rom_cos_tiny {x : ℝ} (hx : x ∈ Icc (0.0391773647 : ℝ) 0.0391773649) :
    cos x ∈ Icc (0.9992326650975322477872 : ℝ) 0.9992326652975323854325 := by
  have h := rom_lip_mem (f := cos) abs_cos_sub_cos_le (x₀ := 0.0391773648) (r := 1e-10)
    (by norm_num at hx ⊢; exact hx) rom_cos_φ₀
  norm_num at h ⊢; exact h

/-- `sin` near `φ₀`. -/
theorem rom_sin_tiny {x : ℝ} (hx : x ∈ Icc (0.0391773647 : ℝ) 0.0391773649) :
    sin x ∈ Icc (0.0391673434687965833708 : ℝ) 0.0391673436687965839701 := by
  have h := rom_lip_mem (f := sin) abs_sin_sub_sin_le (x₀ := 0.0391773648) (r := 1e-10)
    (by norm_num at hx ⊢; exact hx) rom_sin_φ₀
  norm_num at h ⊢; exact h

/-- `cos` near `θ₀`. -/
theorem rom_cos_tiny' {x : ℝ} (hx : x ∈ Icc (0.6813015093 : ℝ) 0.6813015095) :
    cos x ∈ Icc (0.7767536802750504317898 : ℝ) 0.7767536804750505347834 := by
  have h := rom_lip_mem (f := cos) abs_cos_sub_cos_le (x₀ := 0.6813015094) (r := 1e-10)
    (by norm_num at hx ⊢; exact hx) rom_cos_θ₀
  norm_num at h ⊢; exact h

/-- `sin` near `θ₀`. -/
theorem rom_sin_tiny' {x : ℝ} (hx : x ∈ Icc (0.6813015093 : ℝ) 0.6813015095) :
    sin x ∈ Icc (0.6298045092708156586206 : ℝ) 0.6298045094708156627483 := by
  have h := rom_lip_mem (f := sin) abs_sin_sub_sin_le (x₀ := 0.6813015094) (r := 1e-10)
    (by norm_num at hx ⊢; exact hx) rom_sin_θ₀
  norm_num at h ⊢; exact h

end MovingSofa
