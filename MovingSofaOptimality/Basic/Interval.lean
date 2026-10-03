module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Interval arithmetic and Taylor bounds for `cos` and `sin`

Tools for the numerical verifications of `MovingSofaOptimality.External.Romik.Num` and
`MovingSofaOptimality.Gerver.AreaBounds`, which enclose real numbers in intervals `[L, U]` with
decimal endpoints.

* **Interval steps** (`iv_add`, `iv_sub`, `iv_neg`, `iv_mul`, `iv_div`, …). Each lemma derives an
  enclosure `x ∘ y ∈ [L, U]` from enclosures `x ∈ [a, b]`, `y ∈ [c, d]` and a side condition on the
  rational numbers `a, b, c, d, L, U`, which `norm_num` checks. A generated proof is a chain of such
  steps, one per node of the expression tree of the quantity enclosed.
* **Taylor bounds** (`cos_mem_taylor`, `sin_mem_taylor`). For `0 ≤ x ≤ 1` the Taylor series of
  `cos x` and `sin x` are alternating series with decreasing terms, so their sums lie between any
  two consecutive partial sums; with the monotonicity of `cos` and `sin` on `[0, 1]`, this encloses
  `cos x` and `sin x` for `x` in a subinterval of `[0, 1]`.
-/

@[expose] public section

open Real Set

namespace MovingSofaOptimality

/-! ### Interval steps -/

/-- A number lies in the degenerate interval at itself. -/
theorem iv_const (x : ℝ) : x ∈ Icc x x := ⟨le_rfl, le_rfl⟩

/-- Enlarge an enclosure. -/
theorem iv_mono {x a b L U : ℝ} (hx : x ∈ Icc a b) (h : L ≤ a ∧ b ≤ U) : x ∈ Icc L U :=
  Icc_subset_Icc h.1 h.2 hx

theorem iv_add {x y a b c d L U : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (h : L ≤ a + c ∧ b + d ≤ U) : x + y ∈ Icc L U :=
  ⟨by linarith [hx.1, hy.1, h.1], by linarith [hx.2, hy.2, h.2]⟩

theorem iv_sub {x y a b c d L U : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (h : L ≤ a - d ∧ b - c ≤ U) : x - y ∈ Icc L U :=
  ⟨by linarith [hx.1, hy.2, h.1], by linarith [hx.2, hy.1, h.2]⟩

theorem iv_neg {x a b L U : ℝ} (hx : x ∈ Icc a b) (h : L ≤ -b ∧ -a ≤ U) : -x ∈ Icc L U :=
  ⟨by linarith [hx.2, h.1], by linarith [hx.1, h.2]⟩

/-- The quotient by a positive constant `k`. -/
theorem iv_div_const {x a b k L U : ℝ} (hx : x ∈ Icc a b) (h : 0 < k ∧ L ≤ a / k ∧ b / k ≤ U) :
    x / k ∈ Icc L U :=
  ⟨h.2.1.trans (div_le_div_of_nonneg_right hx.1 h.1.le),
    (div_le_div_of_nonneg_right hx.2 h.1.le).trans h.2.2⟩

/-- The quotient of a nonnegative number by a positive one: `x / y` increases with `x` and
decreases with `y`. -/
theorem iv_div {x y a b c d L U : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (h : 0 < c ∧ 0 ≤ a ∧ L ≤ a / d ∧ b / c ≤ U) : x / y ∈ Icc L U := by
  obtain ⟨hc, ha, hL, hU⟩ := h
  have hy0 : 0 < y := hc.trans_le hy.1
  refine ⟨hL.trans ?_, le_trans ?_ hU⟩
  · calc a / d ≤ a / y := div_le_div_of_nonneg_left ha hy0 hy.2
      _ ≤ x / y := div_le_div_of_nonneg_right hx.1 hy0.le
  · calc x / y ≤ b / y := div_le_div_of_nonneg_right hx.2 hy0.le
      _ ≤ b / c := div_le_div_of_nonneg_left (ha.trans (hx.1.trans hx.2)) hc hy.1

/-- The product of two nonnegative factors lies in `[a c, b d]`. -/
theorem iv_mul_nonneg {x y a b c d L U : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (h : 0 ≤ a ∧ 0 ≤ c ∧ L ≤ a * c ∧ b * d ≤ U) : x * y ∈ Icc L U := by
  obtain ⟨ha, hc, hL, hU⟩ := h
  exact ⟨hL.trans (mul_le_mul hx.1 hy.1 hc (ha.trans hx.1)),
    (mul_le_mul hx.2 hy.2 (hc.trans hy.1) (ha.trans (hx.1.trans hx.2))).trans hU⟩

/-- The product of a nonnegative and a nonpositive factor lies in `[b c, a d]`. -/
theorem iv_mul_nonneg_nonpos {x y a b c d L U : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (h : 0 ≤ a ∧ d ≤ 0 ∧ L ≤ b * c ∧ a * d ≤ U) : x * y ∈ Icc L U := by
  obtain ⟨ha, hd, hL, hU⟩ := h
  have hx0 : 0 ≤ x := ha.trans hx.1
  have hc : c ≤ 0 := hy.1.trans (hy.2.trans hd)
  exact ⟨hL.trans ((mul_le_mul_of_nonpos_right hx.2 hc).trans (mul_le_mul_of_nonneg_left hy.1 hx0)),
    ((mul_le_mul_of_nonneg_left hy.2 hx0).trans (mul_le_mul_of_nonpos_right hx.1 hd)).trans hU⟩

/-- The product of a nonpositive and a nonnegative factor lies in `[a d, b c]`. -/
theorem iv_mul_nonpos_nonneg {x y a b c d L U : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (h : b ≤ 0 ∧ 0 ≤ c ∧ L ≤ a * d ∧ b * c ≤ U) : x * y ∈ Icc L U := by
  obtain ⟨hb, hc, hL, hU⟩ := h
  rw [mul_comm]
  exact iv_mul_nonneg_nonpos hy hx ⟨hc, hb, by rwa [mul_comm], by rwa [mul_comm]⟩

/-- The product of two nonpositive factors lies in `[b d, a c]`. -/
theorem iv_mul_nonpos {x y a b c d L U : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (h : b ≤ 0 ∧ d ≤ 0 ∧ L ≤ b * d ∧ a * c ≤ U) : x * y ∈ Icc L U := by
  obtain ⟨hb, hd, hL, hU⟩ := h
  rw [← neg_mul_neg]
  exact iv_mul_nonneg (iv_neg hx ⟨le_rfl, le_rfl⟩) (iv_neg hy ⟨le_rfl, le_rfl⟩)
    ⟨neg_nonneg.2 hb, neg_nonneg.2 hd, by rwa [neg_mul_neg], by rwa [neg_mul_neg]⟩

/-- The product of two enclosed numbers lies between the least and the largest of the four products
of endpoints: `u ↦ u y` maps `[a, b]` into the interval between `a y` and `b y`, and each of these
lies between `u c` and `u d` for `u = a, b`. -/
theorem iv_mul {x y a b c d L U : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (h : (L ≤ a * c ∧ L ≤ a * d ∧ L ≤ b * c ∧ L ≤ b * d) ∧
      (a * c ≤ U ∧ a * d ≤ U ∧ b * c ≤ U ∧ b * d ≤ U)) : x * y ∈ Icc L U := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8⟩ := h
  have hy' : ∀ u, u * y ∈ uIcc (u * c) (u * d) := fun u => by
    rw [← image_const_mul_uIcc]; exact mem_image_of_mem _ (Icc_subset_uIcc hy)
  have hx' : x * y ∈ uIcc (a * y) (b * y) := by
    rw [← image_mul_const_uIcc]; exact mem_image_of_mem _ (Icc_subset_uIcc hx)
  exact uIcc_subset_Icc (uIcc_subset_Icc ⟨h1, h5⟩ ⟨h2, h6⟩ (hy' a))
    (uIcc_subset_Icc ⟨h3, h7⟩ ⟨h4, h8⟩ (hy' b)) hx'

/-! ### Taylor bounds for `cos` and `sin` -/

/-- For `0 ≤ x ≤ 1` the terms `x^(2n) / (2n)!` of the Taylor series of `cos x` decrease. -/
theorem antitone_cos_terms {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Antitone (fun n : ℕ => x ^ (2 * n) / ((2 * n).factorial : ℝ)) :=
  antitone_nat_of_succ_le fun n => div_le_div₀ (pow_nonneg h0 _)
    (pow_le_pow_of_le_one h0 h1 (by omega)) (by positivity)
    (by exact_mod_cast Nat.factorial_le (by omega))

/-- For `0 ≤ x ≤ 1` the terms `x^(2n+1) / (2n+1)!` of the Taylor series of `sin x` decrease. -/
theorem antitone_sin_terms {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Antitone (fun n : ℕ => x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) :=
  antitone_nat_of_succ_le fun n => div_le_div₀ (pow_nonneg h0 _)
    (pow_le_pow_of_le_one h0 h1 (by omega)) (by positivity)
    (by exact_mod_cast Nat.factorial_le (by omega))

/-- The partial sums `c_n(x) = ∑_{i < n} (-1)^i x^(2i) / (2i)!` tend to `cos x`. -/
theorem cos_taylor_tendsto (x : ℝ) : Filter.Tendsto
    (fun n => ∑ i ∈ Finset.range n, (-1) ^ i * (x ^ (2 * i) / ((2 * i).factorial : ℝ)))
    Filter.atTop (nhds (cos x)) := by
  simpa only [mul_div_assoc] using (Real.hasSum_cos x).tendsto_sum_nat

/-- The partial sums `s_n(x) = ∑_{i < n} (-1)^i x^(2i+1) / (2i+1)!` tend to `sin x`. -/
theorem sin_taylor_tendsto (x : ℝ) : Filter.Tendsto
    (fun n => ∑ i ∈ Finset.range n, (-1) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)))
    Filter.atTop (nhds (sin x)) := by
  simpa only [mul_div_assoc] using (Real.hasSum_sin x).tendsto_sum_nat

/-- `c_{2k}(x) ≤ cos x` for `0 ≤ x ≤ 1`. -/
theorem cos_ge_taylor {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (k : ℕ) :
    ∑ i ∈ Finset.range (2 * k), (-1) ^ i * (x ^ (2 * i) / ((2 * i).factorial : ℝ)) ≤ cos x :=
  (antitone_cos_terms h0 h1).alternating_series_le_tendsto (cos_taylor_tendsto x) k

/-- `cos x ≤ c_{2k+1}(x)` for `0 ≤ x ≤ 1`. -/
theorem cos_le_taylor {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (k : ℕ) :
    cos x ≤ ∑ i ∈ Finset.range (2 * k + 1), (-1) ^ i * (x ^ (2 * i) / ((2 * i).factorial : ℝ)) :=
  (antitone_cos_terms h0 h1).tendsto_le_alternating_series (cos_taylor_tendsto x) k

/-- `s_{2k}(x) ≤ sin x` for `0 ≤ x ≤ 1`. -/
theorem sin_ge_taylor {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (k : ℕ) :
    ∑ i ∈ Finset.range (2 * k), (-1) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)) ≤
      sin x :=
  (antitone_sin_terms h0 h1).alternating_series_le_tendsto (sin_taylor_tendsto x) k

/-- `sin x ≤ s_{2k+1}(x)` for `0 ≤ x ≤ 1`. -/
theorem sin_le_taylor {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (k : ℕ) :
    sin x ≤
      ∑ i ∈ Finset.range (2 * k + 1), (-1) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)) :=
  (antitone_sin_terms h0 h1).tendsto_le_alternating_series (sin_taylor_tendsto x) k

/-- **Taylor enclosure of `cos`.** If `0 ≤ a ≤ x ≤ b ≤ 1`, then `c_{2k}(b) ≤ cos x ≤ c_{2k+1}(a)`,
since `cos` decreases on `[0, 1]`. -/
theorem cos_mem_taylor {x a b : ℝ} (k : ℕ) (hx : x ∈ Icc a b) (ha : 0 ≤ a) (hb : b ≤ 1) :
    cos x ∈ Icc (∑ i ∈ Finset.range (2 * k), (-1) ^ i * (b ^ (2 * i) / ((2 * i).factorial : ℝ)))
      (∑ i ∈ Finset.range (2 * k + 1), (-1) ^ i * (a ^ (2 * i) / ((2 * i).factorial : ℝ))) := by
  have hpi := two_le_pi
  exact ⟨(cos_ge_taylor (ha.trans (hx.1.trans hx.2)) hb k).trans
      (cos_le_cos_of_nonneg_of_le_pi (ha.trans hx.1) (by linarith) hx.2),
    (cos_le_cos_of_nonneg_of_le_pi ha (by linarith [hx.2]) hx.1).trans
      (cos_le_taylor ha (hx.1.trans (hx.2.trans hb)) k)⟩

/-- **Taylor enclosure of `sin`.** If `0 ≤ a ≤ x ≤ b ≤ 1`, then `s_{2k}(a) ≤ sin x ≤ s_{2k+1}(b)`,
since `sin` increases on `[0, 1]`. -/
theorem sin_mem_taylor {x a b : ℝ} (k : ℕ) (hx : x ∈ Icc a b) (ha : 0 ≤ a) (hb : b ≤ 1) :
    sin x ∈ Icc
      (∑ i ∈ Finset.range (2 * k), (-1) ^ i * (a ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)))
      (∑ i ∈ Finset.range (2 * k + 1),
        (-1) ^ i * (b ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ))) := by
  have hpi := two_le_pi
  exact ⟨(sin_ge_taylor ha (hx.1.trans (hx.2.trans hb)) k).trans
      (sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith [hx.2]) hx.1),
    (sin_le_sin_of_le_of_le_pi_div_two (by linarith [hx.1]) (by linarith) hx.2).trans
      (sin_le_taylor (ha.trans (hx.1.trans hx.2)) hb k)⟩

end MovingSofaOptimality
