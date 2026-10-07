module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic

/-!
# Short rational Taylor bounds used by the sector certificate

Uncompiled proof source. All signs are obtained by integration of a derivative
of known sign. The arctangent polynomial is a global lower bound on the positive
half-line. No floating-point enclosure, external assertion or native evaluator
is an input to these inequalities.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory

namespace MovingSofaQuantitative

/-- The elementary integration step behind the alternating bounds. -/
theorem nonneg_from_derivative {f df : ℝ → ℝ} (h0 : f 0 = 0)
    (hd : ∀ t, HasDerivAt f (df t) t) (hc : Continuous df)
    (hn : ∀ t, 0 ≤ t → 0 ≤ df t) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (hc.intervalIntegrable 0 x)
  have hi : 0 ≤ ∫ t in (0 : ℝ)..x, df t :=
    intervalIntegral.integral_nonneg hx (fun t ht => hn t ht.1)
  rw [he, h0, sub_zero] at hi
  exact hi

def sinPoly3 (x : ℝ) := x - x ^ 3 / 6
def cosPoly4 (x : ℝ) := 1 - x ^ 2 / 2 + x ^ 4 / 24
def sinPoly5 (x : ℝ) := x - x ^ 3 / 6 + x ^ 5 / 120
def cosPoly6 (x : ℝ) := 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720
def sinPoly7 (x : ℝ) := x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040
def cosPoly8 (x : ℝ) := 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320

theorem hasDerivAt_sinPoly3 (x : ℝ) :
    HasDerivAt sinPoly3 (1 - x ^ 2 / 2) x := by
  convert (hasDerivAt_id x).sub (((hasDerivAt_id x).pow 3).div_const 6) using 1 <;>
    simp only [sinPoly3] <;> norm_num <;> ring

theorem hasDerivAt_cosPoly4 (x : ℝ) :
    HasDerivAt cosPoly4 (-sinPoly3 x) x := by
  convert (((hasDerivAt_const x (1 : ℝ)).sub
    (((hasDerivAt_id x).pow 2).div_const 2)).add
    (((hasDerivAt_id x).pow 4).div_const 24)) using 1 <;>
    simp only [cosPoly4, sinPoly3] <;> norm_num <;> ring

theorem hasDerivAt_sinPoly5 (x : ℝ) :
    HasDerivAt sinPoly5 (cosPoly4 x) x := by
  convert (hasDerivAt_sinPoly3 x).add
    (((hasDerivAt_id x).pow 5).div_const 120) using 1 <;>
    simp only [sinPoly5, sinPoly3, cosPoly4] <;> norm_num <;> ring

theorem hasDerivAt_cosPoly6 (x : ℝ) :
    HasDerivAt cosPoly6 (-sinPoly5 x) x := by
  convert (hasDerivAt_cosPoly4 x).sub
    (((hasDerivAt_id x).pow 6).div_const 720) using 1 <;>
    simp only [cosPoly6, cosPoly4, sinPoly5, sinPoly3] <;> norm_num <;> ring

theorem hasDerivAt_sinPoly7 (x : ℝ) :
    HasDerivAt sinPoly7 (cosPoly6 x) x := by
  convert (hasDerivAt_sinPoly5 x).sub
    (((hasDerivAt_id x).pow 7).div_const 5040) using 1 <;>
    simp only [sinPoly7, sinPoly5, cosPoly6, cosPoly4] <;> norm_num <;> ring

theorem hasDerivAt_cosPoly8 (x : ℝ) :
    HasDerivAt cosPoly8 (-sinPoly7 x) x := by
  convert (hasDerivAt_cosPoly6 x).add
    (((hasDerivAt_id x).pow 8).div_const 40320) using 1 <;>
    simp only [cosPoly8, cosPoly6, sinPoly7, sinPoly5] <;> norm_num <;> ring

theorem sinPoly3_le_sin {x : ℝ} (hx : 0 ≤ x) : sinPoly3 x ≤ sin x := by
  have h := nonneg_from_derivative
    (f := fun t => sin t - sinPoly3 t) (df := fun t => cos t - (1 - t ^ 2 / 2))
    (by simp [sinPoly3])
    (fun t => (hasDerivAt_sin t).sub (hasDerivAt_sinPoly3 t))
    (by fun_prop) (fun t _ => sub_nonneg.mpr one_sub_sq_div_two_le_cos) hx
  linarith

theorem cos_le_cosPoly4 {x : ℝ} (hx : 0 ≤ x) : cos x ≤ cosPoly4 x := by
  have h := nonneg_from_derivative
    (f := fun t => cosPoly4 t - cos t) (df := fun t => sin t - sinPoly3 t)
    (by simp [cosPoly4])
    (fun t => by
      convert (hasDerivAt_cosPoly4 t).sub (hasDerivAt_cos t) using 1 <;> ring)
    (by unfold sinPoly3; fun_prop)
    (fun t ht => sub_nonneg.mpr (sinPoly3_le_sin ht)) hx
  linarith

theorem sin_le_sinPoly5 {x : ℝ} (hx : 0 ≤ x) : sin x ≤ sinPoly5 x := by
  have h := nonneg_from_derivative
    (f := fun t => sinPoly5 t - sin t) (df := fun t => cosPoly4 t - cos t)
    (by simp [sinPoly5])
    (fun t => (hasDerivAt_sinPoly5 t).sub (hasDerivAt_sin t))
    (by unfold cosPoly4; fun_prop)
    (fun t ht => sub_nonneg.mpr (cos_le_cosPoly4 ht)) hx
  linarith

theorem cosPoly6_le_cos {x : ℝ} (hx : 0 ≤ x) : cosPoly6 x ≤ cos x := by
  have h := nonneg_from_derivative
    (f := fun t => cos t - cosPoly6 t) (df := fun t => sinPoly5 t - sin t)
    (by simp [cosPoly6])
    (fun t => by
      convert (hasDerivAt_cos t).sub (hasDerivAt_cosPoly6 t) using 1 <;> ring)
    (by unfold sinPoly5; fun_prop)
    (fun t ht => sub_nonneg.mpr (sin_le_sinPoly5 ht)) hx
  linarith

theorem sinPoly7_le_sin {x : ℝ} (hx : 0 ≤ x) : sinPoly7 x ≤ sin x := by
  have h := nonneg_from_derivative
    (f := fun t => sin t - sinPoly7 t) (df := fun t => cos t - cosPoly6 t)
    (by simp [sinPoly7])
    (fun t => (hasDerivAt_sin t).sub (hasDerivAt_sinPoly7 t))
    (by unfold cosPoly6; fun_prop)
    (fun t ht => sub_nonneg.mpr (cosPoly6_le_cos ht)) hx
  linarith

theorem cos_le_cosPoly8 {x : ℝ} (hx : 0 ≤ x) : cos x ≤ cosPoly8 x := by
  have h := nonneg_from_derivative
    (f := fun t => cosPoly8 t - cos t) (df := fun t => sin t - sinPoly7 t)
    (by simp [cosPoly8])
    (fun t => by
      convert (hasDerivAt_cosPoly8 t).sub (hasDerivAt_cos t) using 1 <;> ring)
    (by unfold sinPoly7; fun_prop)
    (fun t ht => sub_nonneg.mpr (sinPoly7_le_sin ht)) hx
  linarith

/-- The alternating polynomial used for the rational sector margin. -/
def atanPoly7 (x : ℝ) := x - x ^ 3 / 3 + x ^ 5 / 5 - x ^ 7 / 7

theorem hasDerivAt_atanPoly7 (x : ℝ) :
    HasDerivAt atanPoly7 (1 - x ^ 2 + x ^ 4 - x ^ 6) x := by
  convert (((hasDerivAt_id x).sub (((hasDerivAt_id x).pow 3).div_const 3)).add
    (((hasDerivAt_id x).pow 5).div_const 5)).sub
    (((hasDerivAt_id x).pow 7).div_const 7) using 1 <;>
    simp only [atanPoly7] <;> norm_num <;> ring

/-- The error has derivative x^8/(1+x^2), a manifestly nonnegative function. -/
theorem atanPoly7_le_arctan {x : ℝ} (hx : 0 ≤ x) : atanPoly7 x ≤ arctan x := by
  have h := nonneg_from_derivative
    (f := fun t => arctan t - atanPoly7 t)
    (df := fun t => t ^ 8 / (1 + t ^ 2)) (by simp [atanPoly7])
    (fun t => by
      convert (hasDerivAt_arctan t).sub (hasDerivAt_atanPoly7 t) using 1
      field_simp
      ring)
    (by fun_prop (disch := positivity))
    (fun t _ => div_nonneg (by positivity) (by positivity)) hx
  linarith

end MovingSofaQuantitative
