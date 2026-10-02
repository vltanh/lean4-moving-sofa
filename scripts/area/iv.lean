/-! ### Interval arithmetic

Each lemma derives an enclosure of `x ∘ y` from enclosures of `x` and `y`; the side conditions on
the (rational) endpoints are checked by `norm_num`. -/

theorem ga_iv_const (x : ℝ) : x ∈ Icc x x := ⟨le_rfl, le_rfl⟩

theorem ga_iv_add {x y a b c d L U : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (h : L ≤ a + c ∧ b + d ≤ U) : x + y ∈ Icc L U :=
  ⟨by linarith [hx.1, hy.1, h.1], by linarith [hx.2, hy.2, h.2]⟩

theorem ga_iv_sub {x y a b c d L U : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (h : L ≤ a - d ∧ b - c ≤ U) : x - y ∈ Icc L U :=
  ⟨by linarith [hx.1, hy.2, h.1], by linarith [hx.2, hy.1, h.2]⟩

theorem ga_iv_neg {x a b L U : ℝ} (hx : x ∈ Icc a b) (h : L ≤ -b ∧ -a ≤ U) : -x ∈ Icc L U :=
  ⟨by linarith [hx.2, h.1], by linarith [hx.1, h.2]⟩

theorem ga_iv_div {x a b k L U : ℝ} (hx : x ∈ Icc a b) (h : 0 < k ∧ L ≤ a / k ∧ b / k ≤ U) :
    x / k ∈ Icc L U :=
  ⟨h.2.1.trans (div_le_div_of_nonneg_right hx.1 h.1.le),
    (div_le_div_of_nonneg_right hx.2 h.1.le).trans h.2.2⟩

theorem ga_iv_mul_pp {x y a b c d L U : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (h : 0 ≤ a ∧ 0 ≤ c ∧ L ≤ a * c ∧ b * d ≤ U) : x * y ∈ Icc L U := by
  obtain ⟨ha, hc, hL, hU⟩ := h
  have hx0 : 0 ≤ x := ha.trans hx.1
  have hy0 : 0 ≤ y := hc.trans hy.1
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 hx.1) hy0, mul_nonneg ha (sub_nonneg.2 hy.1)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hx.2) hy0, mul_nonneg (hx0.trans hx.2) (sub_nonneg.2 hy.2)]

theorem ga_iv_mul_pn {x y a b c d L U : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (h : 0 ≤ a ∧ d ≤ 0 ∧ L ≤ b * c ∧ a * d ≤ U) : x * y ∈ Icc L U := by
  obtain ⟨ha, hd, hL, hU⟩ := h
  have hx0 : 0 ≤ x := ha.trans hx.1
  have hy0 : y ≤ 0 := hy.2.trans hd
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 hx.2) (neg_nonneg.2 hy0),
      mul_nonneg (hx0.trans hx.2) (sub_nonneg.2 hy.1)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hx.1) (neg_nonneg.2 hy0), mul_nonneg ha (sub_nonneg.2 hy.2)]

theorem ga_iv_mul_np {x y a b c d L U : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (h : b ≤ 0 ∧ 0 ≤ c ∧ L ≤ a * d ∧ b * c ≤ U) : x * y ∈ Icc L U := by
  obtain ⟨hb, hc, hL, hU⟩ := h
  have hx0 : x ≤ 0 := hx.2.trans hb
  have hy0 : 0 ≤ y := hc.trans hy.1
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 hx.1) hy0, mul_nonneg (neg_nonneg.2 (hx.1.trans hx0))
      (sub_nonneg.2 hy.2)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hx.2) hy0, mul_nonneg (neg_nonneg.2 hb) (sub_nonneg.2 hy.1)]

theorem ga_iv_mul_nn {x y a b c d L U : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (h : b ≤ 0 ∧ d ≤ 0 ∧ L ≤ b * d ∧ a * c ≤ U) : x * y ∈ Icc L U := by
  obtain ⟨hb, hd, hL, hU⟩ := h
  have hx0 : x ≤ 0 := hx.2.trans hb
  have hy0 : y ≤ 0 := hy.2.trans hd
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 hx.2) (neg_nonneg.2 hy0),
      mul_nonneg (neg_nonneg.2 hb) (sub_nonneg.2 hy.2)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hx.1) (neg_nonneg.2 hy0),
      mul_nonneg (neg_nonneg.2 (hx.1.trans hx0)) (sub_nonneg.2 hy.1)]

theorem ga_mul_mem_corners {x y a b c d : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
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

theorem ga_iv_mul {x y a b c d L U : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (h : (L ≤ a * c ∧ L ≤ a * d ∧ L ≤ b * c ∧ L ≤ b * d) ∧
      (a * c ≤ U ∧ a * d ≤ U ∧ b * c ≤ U ∧ b * d ≤ U)) : x * y ∈ Icc L U := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8⟩ := h
  obtain ⟨k1, k2⟩ := ga_mul_mem_corners hx hy
  exact ⟨le_trans (le_min (le_min h1 h2) (le_min h3 h4)) k1,
    k2.trans (max_le (max_le h5 h6) (max_le h7 h8))⟩

/-! ### Taylor bounds for `cos` and `sin` (alternating series) -/

theorem ga_antitone_cos_terms {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Antitone (fun n : ℕ => x ^ (2 * n) / ((2 * n).factorial : ℝ)) := by
  refine antitone_nat_of_succ_le (fun n => ?_)
  have hx2 : x ^ (2 * (n + 1)) ≤ x ^ (2 * n) := pow_le_pow_of_le_one h0 h1 (by omega)
  have hf : ((2 * n).factorial : ℝ) ≤ ((2 * (n + 1)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hpos : (0 : ℝ) < ((2 * n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  exact div_le_div₀ (pow_nonneg h0 _) hx2 hpos hf

theorem ga_antitone_sin_terms {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Antitone (fun n : ℕ => x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) := by
  refine antitone_nat_of_succ_le (fun n => ?_)
  have hx2 : x ^ (2 * (n + 1) + 1) ≤ x ^ (2 * n + 1) := pow_le_pow_of_le_one h0 h1 (by omega)
  have hf : ((2 * n + 1).factorial : ℝ) ≤ ((2 * (n + 1) + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hpos : (0 : ℝ) < ((2 * n + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  exact div_le_div₀ (pow_nonneg h0 _) hx2 hpos hf

theorem ga_cos_tendsto (x : ℝ) : Filter.Tendsto
    (fun n => ∑ i ∈ Finset.range n, (-1) ^ i * (x ^ (2 * i) / ((2 * i).factorial : ℝ)))
    Filter.atTop (nhds (cos x)) := by
  simpa only [mul_div_assoc] using (Real.hasSum_cos x).tendsto_sum_nat

theorem ga_sin_tendsto (x : ℝ) : Filter.Tendsto
    (fun n => ∑ i ∈ Finset.range n, (-1) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)))
    Filter.atTop (nhds (sin x)) := by
  simpa only [mul_div_assoc] using (Real.hasSum_sin x).tendsto_sum_nat

theorem ga_cos_ge {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (k : ℕ) :
    ∑ i ∈ Finset.range (2 * k), (-1) ^ i * (x ^ (2 * i) / ((2 * i).factorial : ℝ)) ≤ cos x :=
  (ga_antitone_cos_terms h0 h1).alternating_series_le_tendsto (ga_cos_tendsto x) k

theorem ga_cos_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (k : ℕ) :
    cos x ≤ ∑ i ∈ Finset.range (2 * k + 1), (-1) ^ i * (x ^ (2 * i) / ((2 * i).factorial : ℝ)) :=
  (ga_antitone_cos_terms h0 h1).tendsto_le_alternating_series (ga_cos_tendsto x) k

theorem ga_sin_ge {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (k : ℕ) :
    ∑ i ∈ Finset.range (2 * k), (-1) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)) ≤
      sin x :=
  (ga_antitone_sin_terms h0 h1).alternating_series_le_tendsto (ga_sin_tendsto x) k

theorem ga_sin_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (k : ℕ) :
    sin x ≤
      ∑ i ∈ Finset.range (2 * k + 1), (-1) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)) :=
  (ga_antitone_sin_terms h0 h1).tendsto_le_alternating_series (ga_sin_tendsto x) k

theorem ga_pi_mem : π ∈ Icc (3.14159265358 : ℝ) (3.14159265359 : ℝ) :=
  ⟨by linarith [pi_gt_d20], by linarith [pi_lt_d20]⟩
