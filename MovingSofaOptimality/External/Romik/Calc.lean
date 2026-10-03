module

public import MovingSofaOptimality.Basic.Interval
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Enclosures of `π`, `cos` and `sin` for the parameters of Gerver's sofa

The atoms `cos φ, sin φ, cos θ, sin θ, π` of the interval computations of
`MovingSofaOptimality.External.Romik.Num`, enclosed (by the Taylor bounds of
`MovingSofaOptimality.Basic.Interval`) in its three regimes:

* on the box `[0.039, 0.04] × [0.68, 0.69]` (`rom_cos_box`, `rom_sin_box`, `rom_cos_box'`,
  `rom_sin_box'`);
* at the approximate solution `(φ₀, θ₀) = (0.0391773648, 0.6813015094)` (`rom_cos_φ₀`, …);
* on the square of radius `10⁻¹⁰` around it (`rom_cos_tiny`, …), from the enclosures at
  `(φ₀, θ₀)` since `cos` and `sin` are `1`-Lipschitz.
-/

@[expose] public section

open Real Set

namespace MovingSofaOptimality

theorem rom_pi_mem6 : π ∈ Icc (3.141592 : ℝ) 3.141593 := ⟨pi_gt_d6.le, pi_lt_d6.le⟩

theorem rom_pi_mem20 : π ∈ Icc (3.14159265358979323846 : ℝ) 3.14159265358979323847 :=
  ⟨pi_gt_d20.le, pi_lt_d20.le⟩

/-! ### On the box -/

/-- `cos` on `[0.039, 0.04]`. -/
theorem rom_cos_box {x : ℝ} (hx : x ∈ Icc (0.039 : ℝ) 0.04) :
    cos x ∈ Icc (0.9992001066 : ℝ) 1 := by
  refine ⟨le_trans ?_ (cos_mem_taylor 3 hx (by norm_num) (by norm_num)).1, cos_le_one x⟩
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-- `sin` on `[0.039, 0.04]`. -/
theorem rom_sin_box {x : ℝ} (hx : x ∈ Icc (0.039 : ℝ) 0.04) :
    sin x ∈ Icc (0.0389901142 : ℝ) 0.0399893342 := by
  refine iv_mono (sin_mem_taylor 3 hx (by norm_num) (by norm_num)) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-- `cos` on `[0.68, 0.69]`. -/
theorem rom_cos_box' {x : ℝ} (hx : x ∈ Icc (0.68 : ℝ) 0.69) :
    cos x ∈ Icc (0.7712460149 : ℝ) 0.7775727188 := by
  refine iv_mono (cos_mem_taylor 3 hx (by norm_num) (by norm_num)) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-- `sin` on `[0.68, 0.69]`. -/
theorem rom_sin_box' {x : ℝ} (hx : x ∈ Icc (0.68 : ℝ) 0.69) :
    sin x ∈ Icc (0.628793024 : ℝ) 0.6365371823 := by
  refine iv_mono (sin_mem_taylor 3 hx (by norm_num) (by norm_num)) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-! ### At `(φ₀, θ₀)` -/

/-- `cos φ₀` for `φ₀ = 0.0391773648`. -/
theorem rom_cos_φ₀ :
    cos (0.0391773648 : ℝ) ∈ Icc (0.9992326651975322477872 : ℝ) 0.9992326651975323854325 := by
  refine iv_mono (cos_mem_taylor 2 (iv_const _) (by norm_num) (by norm_num)) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-- `sin φ₀` for `φ₀ = 0.0391773648`. -/
theorem rom_sin_φ₀ :
    sin (0.0391773648 : ℝ) ∈ Icc (0.0391673435687965833708 : ℝ) 0.0391673435687965839701 := by
  refine iv_mono (sin_mem_taylor 2 (iv_const _) (by norm_num) (by norm_num)) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-- `cos θ₀` for `θ₀ = 0.6813015094`. -/
theorem rom_cos_θ₀ :
    cos (0.6813015094 : ℝ) ∈ Icc (0.7767536803750504317898 : ℝ) 0.7767536803750505347834 := by
  refine iv_mono (cos_mem_taylor 4 (iv_const _) (by norm_num) (by norm_num)) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-- `sin θ₀` for `θ₀ = 0.6813015094`. -/
theorem rom_sin_θ₀ :
    sin (0.6813015094 : ℝ) ∈ Icc (0.6298045093708156586206 : ℝ) 0.6298045093708156627483 := by
  refine iv_mono (sin_mem_taylor 4 (iv_const _) (by norm_num) (by norm_num)) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-! ### Near `(φ₀, θ₀)` -/

/-- Moving the argument of a `1`-Lipschitz function such as `cos` or `sin` by at most `r` moves the
value by at most `r`. -/
theorem rom_lip_mem {f : ℝ → ℝ} (hf : ∀ x y, |f x - f y| ≤ |x - y|) {x x₀ r a b : ℝ}
    (hx : x ∈ Icc (x₀ - r) (x₀ + r)) (h₀ : f x₀ ∈ Icc a b) : f x ∈ Icc (a - r) (b + r) := by
  have hd : |x - x₀| ≤ r := abs_sub_le_iff.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have h := abs_sub_le_iff.1 ((hf x x₀).trans hd)
  exact ⟨by linarith [h₀.1, h.2], by linarith [h₀.2, h.1]⟩

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

end MovingSofaOptimality
