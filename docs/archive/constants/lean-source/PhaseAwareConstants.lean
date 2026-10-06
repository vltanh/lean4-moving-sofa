module

public import MovingSofaStability.RefinedConstantAlgebra

/-!
# Phase-aware reference arithmetic

Uncompiled proof source. These results are exact arithmetic and finite-dimensional
inequalities, not sampled estimates. The associated uniform C1 adaptive-angle
argument and reference geometric assembly are in analytic note 06; they are not
silently assumed to have been implemented by this file.
-/

@[expose] public section
noncomputable section

open Real Set MovingSofaOptimality

namespace MovingSofaStability

/-- Coefficients obtained by differentiating Romik's second phase. -/
theorem second_phase_velocity_enclosures {P : GerverParams} (h : P.Bounds)
    {t : ℝ} (ht : t ∈ Icc P.φ P.θ) :
    (59 / 625 : ℝ) ≤ t - 1 - 2 * P.b₁ ∧
      1 / 2 - t ^ 2 / 4 + P.b₁ * t + P.b₂ ≤ 7 / 5 := by
  have hphi := h.φ_mem
  have hb1 := h.b₁_mem
  have hb2 := h.b₂_mem
  have ht0 : 0 ≤ t := by linarith [ht.1, hphi.1]
  have ht39 : (39 / 1000 : ℝ) ≤ t := by linarith [ht.1, hphi.1]
  have hb1' : P.b₁ ≤ -(527 / 1000 : ℝ) := by linarith [hb1.2]
  have hprod := mul_le_mul_of_nonneg_right hb1' ht0
  constructor
  · linarith [ht.1, hphi.1, hb1.2]
  · nlinarith [sq_nonneg t, hb2.2]

/-- Elementary lower trigonometric bounds needed in the small-angle subinterval. -/
theorem small_phase_trig_budget {φ : ℝ}
    (hφ : φ ∈ Icc (0.039177264 : ℝ) 0.04) :
    (39 / 1000 : ℝ) < φ - φ ^ 3 / 6 := by
  have hφ0 : 0 ≤ φ := by linarith [hφ.1]
  have hφ2 : φ ^ 2 ≤ (0.04 : ℝ) ^ 2 := by nlinarith [hφ.2]
  have hφ3 := mul_le_mul_of_nonneg_right hφ2 hφ0
  nlinarith [hφ.1, hφ.2]

/-- The slope bound follows from coarse rational velocity/trigonometric bounds. -/
theorem phase_slope_small {a b s c : ℝ}
    (ha : (59 / 625 : ℝ) ≤ a) (hb0 : 0 ≤ b) (hb : b ≤ 7 / 5)
    (hs : (39 / 1000 : ℝ) ≤ s) (hs1 : s ≤ 1)
    (hc : (127 / 128 : ℝ) ≤ c) (hc1 : c ≤ 1) :
    |(-a) * s + b * c| ≤ (189 / 20) * (a * c + b * s) := by
  have ha0 : 0 ≤ a := by linarith
  have hcoef : (189 / 20 : ℝ) * (127 / 128) + 39 / 1000 ≤ (189 / 20) * c + s := by
    linarith
  have hfirst := mul_le_mul_of_nonneg_left hcoef ha0
  have hfirst' := mul_le_mul_of_nonneg_right ha
    (show 0 ≤ (189 / 20 : ℝ) * (127 / 128) + 39 / 1000 by norm_num)
  have hsecond := mul_le_mul_of_nonneg_left
    (show (189 / 20 : ℝ) * (39 / 1000) - 1 ≤ (189 / 20) * s - c by linarith) hb0
  have hsecond' := mul_le_mul_of_nonpos_right hb
    (show (189 / 20 : ℝ) * (39 / 1000) - 1 ≤ 0 by norm_num)
  have hupper : -a * s + b * c ≤ (189 / 20) * (a * c + b * s) := by nlinarith
  have hbc : 0 ≤ b * c := mul_nonneg hb0 (by linarith)
  have hbs : 0 ≤ b * s := mul_nonneg hb0 (by linarith)
  have has := mul_le_mul_of_nonneg_left hs1 ha0
  have hac := mul_le_mul_of_nonneg_left hc ha0
  exact abs_le.mpr ⟨by nlinarith, hupper⟩

/-- The adaptive hallway margin uses horizontal speed divided by frame speed. -/
theorem phase_transversality_small {a b s c : ℝ}
    (ha : (59 / 625 : ℝ) ≤ a) (hb0 : 0 ≤ b) (hb : b ≤ 7 / 5)
    (hs : (39 / 1000 : ℝ) ≤ s) (hc : (127 / 128 : ℝ) ≤ c) :
    (10 / 101) * (a + b) ≤ a * c + b * s := by
  have ha0 : 0 ≤ a := by linarith
  have h1 := mul_le_mul_of_nonneg_left
    (show (127 / 128 : ℝ) - 10 / 101 ≤ c - 10 / 101 by linarith) ha0
  have h2 := mul_le_mul_of_nonneg_right ha
    (show (0 : ℝ) ≤ 127 / 128 - 10 / 101 by norm_num)
  have h3 := mul_le_mul_of_nonneg_left
    (show (39 / 1000 : ℝ) - 10 / 101 ≤ s - 10 / 101 by linarith) hb0
  have h4 := mul_le_mul_of_nonpos_right hb
    (show (39 / 1000 : ℝ) - 10 / 101 ≤ 0 by norm_num)
  nlinarith

/-- Away from the short endpoint interval, positivity of the two trigonometric
coefficients alone supplies both estimates. -/
theorem phase_velocity_large {a b s c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs : s ∈ Icc (1 / 9 : ℝ) 1) (hc : c ∈ Icc (1 / 9 : ℝ) 1) :
    |-a * s + b * c| ≤ (189 / 20) * (a * c + b * s) ∧
      (10 / 101) * (a + b) ≤ a * c + b * s := by
  have h1 := mul_le_mul_of_nonneg_left hc.1 ha
  have h2 := mul_le_mul_of_nonneg_left hs.1 hb
  have h3 := mul_le_mul_of_nonneg_left hs.2 ha
  have h4 := mul_le_mul_of_nonneg_left hc.2 hb
  have has : 0 ≤ a * s := mul_nonneg ha (by linarith [hs.1])
  have hbc : 0 ≤ b * c := mul_nonneg hb (by linarith [hc.1])
  constructor
  · exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  · nlinarith

/-- Balancing the first variations is an exact identity, not a numerical fit. -/
theorem balanced_slack_rates {a b s c : ℝ} (hab : a + b ≠ 0) :
    -s + a * ((s - c) / (a + b)) = -(a * c + b * s) / (a + b) ∧
      -c - b * ((s - c) / (a + b)) = -(a * c + b * s) / (a + b) := by
  constructor <;> field_simp [hab] <;> ring

theorem adaptive_margin_gap : (0 : ℝ) < 10 / 101 - 5 / 51 ∧
    (10 / 101 : ℝ) - 5 / 51 = 5 / 5151 := by norm_num

/-- A sharper Euclidean cone estimate improves the interior-ball ratio. -/
theorem phase_roof_cone_bound {x y w : ℝ} (hw : 0 ≤ w)
    (hball : x ^ 2 + y ^ 2 ≤ w ^ 2) :
    (189 / 20) * |x| - y ≤ (951 / 100) * w := by
  have hc : ((189 / 20) * |x| - y) ^ 2 ≤
      ((189 / 20 : ℝ) ^ 2 + 1) * (x ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (|x| + (189 / 20) * y), sq_abs x]
  have hscale := mul_le_mul_of_nonneg_left hball
    (show 0 ≤ (189 / 20 : ℝ) ^ 2 + 1 by norm_num)
  nlinarith

/-- The wing contraction also uses Euclidean, rather than taxicab, distance. -/
theorem wing_center_distance_bound {x y : ℝ}
    (hx : |x| ≤ 3 / 4) (hy : |y| ≤ 3 / 4) :
    x ^ 2 + y ^ 2 ≤ (9 / 8 : ℝ) ^ 2 := by
  nlinarith [abs_nonneg x, abs_nonneg y, sq_abs x, sq_abs y]

theorem reverse_budget_31 {ε e k : ℝ}
    (hε : 0 < ε) (he : 0 ≤ e) (heε : e ≤ ε)
    (hk0 : 0 ≤ k) (hk : k ≤ 1001 / 500) :
    sqrt 2 * k * sqrt e + sqrt (2 / π) * sqrt (ε - e) <
      (100 / 1051) * (31 * sqrt ε) := by
  have hfrac : (2 / π : ℝ) < 2 / 3 := by
    apply (div_lt_iff₀ pi_pos).mpr
    linarith [pi_gt_three]
  have hcoeff : 2 * k ^ 2 + 2 / π < (737 / 250 : ℝ) ^ 2 := by nlinarith
  have h := split_sqrt_budget he heε (sqrt 2 * k) (sqrt (2 / π))
  rw [mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    sq_sqrt (div_nonneg (by norm_num) pi_pos.le)] at h
  have hlt := mul_lt_mul_of_pos_right hcoeff hε
  have hs := sqrt_nonneg ε
  have hs2 := sq_sqrt hε.le
  have hn : 0 ≤ sqrt 2 * k * sqrt e + sqrt (2 / π) * sqrt (ε - e) := by positivity
  have hbound : sqrt 2 * k * sqrt e + sqrt (2 / π) * sqrt (ε - e) <
      (737 / 250) * sqrt ε := by nlinarith
  have hrat : (737 / 250 : ℝ) < (100 / 1051) * 31 := by norm_num
  exact hbound.trans (by nlinarith [sqrt_pos.mpr hε])

theorem forward_budget_31 {ε e k B : ℝ}
    (hε : 0 < ε) (he : 0 ≤ e) (heε : e ≤ ε)
    (hk0 : 0 ≤ k) (hk : k ≤ 1001 / 500) (hB : 0 ≤ B)
    (hsmall : B * sqrt ε ≤ 1 / 2) :
    (51 / 5) * (k * sqrt e + B * (ε - e)) < 31 * sqrt ε := by
  have hs := sqrt_pos.mpr hε
  have hke := mul_le_mul_of_nonneg_left (sqrt_le_sqrt heε) hk0
  have hBe := mul_le_mul_of_nonneg_left (show ε - e ≤ ε by linarith) hB
  have hBsmall := mul_le_mul_of_nonneg_right hsmall hs.le
  have hs2 := sq_sqrt hε.le
  have hkl := mul_le_mul_of_nonneg_right hk hs.le
  nlinarith

/-- Tighter reference lengths enter only the direct excess-area calculation. -/
theorem reference_width_bounds_phase {P : GerverParams} (h : P.Bounds) :
    2 - 2 * P.κ₃.1 < (323 / 100 : ℝ) ∧
      2 * P.κ₃.1 + 4 * P.a₁ - 2 < (807 / 500 : ℝ) := by
  have ha := h.a₁_mem
  have hk := h.κ₃₁_mem
  constructor <;> linarith [ha.2, hk.1, hk.2]

theorem symmetric_difference_budget_100 {ε e k δ g d : ℝ}
    (hε : 0 ≤ ε) (he : 0 ≤ e) (heε : e ≤ ε)
    (hk0 : 0 ≤ k) (hk : k ≤ 1001 / 500)
    (hδ : 0 ≤ δ) (hδbound : δ ≤ k * sqrt e)
    (hgain : g ≤ ε - e)
    (harea : d ≤ ε + 2 * g + (62307 / 1250) * δ + 8 * δ ^ 2)
    (hsmall : sqrt ε ≤ 1 / 200) : d ≤ 100 * sqrt ε := by
  have hs := sqrt_nonneg ε
  have hs2 := sq_sqrt hε
  have hse2 := sq_sqrt he
  have hδ2 : δ ^ 2 ≤ k ^ 2 * e := by nlinarith [sqrt_nonneg e]
  have hk2 : k ^ 2 ≤ (401 / 100 : ℝ) := by nlinarith
  have hδ2' := hδ2.trans (mul_le_mul_of_nonneg_right hk2 he)
  have hδlinear : δ ≤ (1001 / 500) * sqrt ε :=
    hδbound.trans ((mul_le_mul_of_nonneg_left (sqrt_le_sqrt heε) hk0).trans
      (mul_le_mul_of_nonneg_right hk hs))
  have hd : d ≤ (62369307 / 625000) * sqrt ε + (827 / 25) * ε := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_right hsmall hs
  nlinarith

end MovingSofaStability
