module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Quantitative stationarity without assuming balancedness

A one-sided quadratic expansion and penalized maximality bound the outward
first variation. A finite weighted endpoint identity then controls both signs
of a pinned defect. These are the algebraic steps needed for a specified
maximizer, whose approximating polygons are not unpenalized maxima.

All feasibility, area-expansion and penalty-expansion hypotheses are visible.
No existence or geometric regularity claim is hidden in these lemmas.
-/

@[expose] public section

open Set
open scoped BigOperators

namespace MovingSofaUniqueness

/-- A strictly positive first-order term cannot be bounded by a quadratic
remainder at every sufficiently small positive increment. -/
theorem le_zero_of_mul_le_sq {d C ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (h : ∀ ε ∈ Ioc (0 : ℝ) ε₀, d * ε ≤ C * ε ^ 2) : d ≤ 0 := by
  by_contra hnot
  have hd : 0 < d := lt_of_not_ge hnot
  let ε := min ε₀ (d / (2 * (|C| + 1)))
  have hC : 0 < |C| + 1 := by positivity
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hεle : ε ≤ ε₀ := min_le_left _ _
  have hεd : ε ≤ d / (2 * (|C| + 1)) := min_le_right _ _
  have hm : ε * (2 * (|C| + 1)) ≤ d :=
    (le_div_iff₀ (by positivity)).mp hεd
  have hbound := h ε ⟨hε, hεle⟩
  have habs : C ≤ |C| := le_abs_self C
  have hsmall : C * ε ^ 2 < d * ε := by
    nlinarith [mul_pos hε hε]
  exact (not_lt_of_ge hbound) hsmall

/-- Outward maximality of A-P implies DA<=DP. Quadratic remainders are
allowed for both functions; no differentiability API or uniform step size
across different polygons is required. -/
theorem firstVariation_le_penalty
    (A P : ℝ → ℝ) {d p C D ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hA : ∀ ε ∈ Ioc (0 : ℝ) ε₀, |A ε - A 0 - d * ε| ≤ C * ε ^ 2)
    (hP : ∀ ε ∈ Ioc (0 : ℝ) ε₀, |P ε - P 0 - p * ε| ≤ D * ε ^ 2)
    (hmax : ∀ ε ∈ Ioc (0 : ℝ) ε₀, A ε - P ε ≤ A 0 - P 0) : d ≤ p := by
  have h : d - p ≤ 0 := le_zero_of_mul_le_sq (C := C + D) hε₀ (by
    intro ε hε
    have ha := (abs_le.mp (hA ε hε)).1
    have hp := (abs_le.mp (hP ε hε)).2
    have hm := hmax ε hε
    nlinarith)
  linarith

/-- The penalty's absolute derivative bounds the positive objective defect. -/
theorem firstVariation_le_of_penalty_bound
    (A P : ℝ → ℝ) {d p C D ε₀ e : ℝ} (hε₀ : 0 < ε₀)
    (hA : ∀ ε ∈ Ioc (0 : ℝ) ε₀, |A ε - A 0 - d * ε| ≤ C * ε ^ 2)
    (hP : ∀ ε ∈ Ioc (0 : ℝ) ε₀, |P ε - P 0 - p * ε| ≤ D * ε ^ 2)
    (hmax : ∀ ε ∈ Ioc (0 : ℝ) ε₀, A ε - P ε ≤ A 0 - P 0)
    (hp : |p| ≤ e) : d ≤ e :=
  (firstVariation_le_penalty A P hε₀ hA hP hmax).trans
    ((le_abs_self p).trans hp)

/-- If signed defects sum to zero with nonnegative weights, their one-sided
upper bounds also control their negative parts. Crucially the denominator
below is the pinned weight, never a small extreme-cell sine. -/
theorem abs_weighted_defect_le {ι : Type*} (s : Finset ι)
    (w d e : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (he : ∀ i ∈ s, 0 ≤ e i) (hd : ∀ i ∈ s, d i ≤ e i)
    (hsum : (∑ i ∈ s, w i * d i) = 0) {k : ι} (hk : k ∈ s) :
    |w k * d k| ≤ ∑ i ∈ s, w i * e i := by
  classical
  have heach := Finset.single_le_sum (s := s) (f := fun i => w i * e i)
    (fun i hi => mul_nonneg (hw i hi) (he i hi)) hk
  have hgap := Finset.single_le_sum (s := s)
    (f := fun i => w i * (e i - d i))
    (fun i hi => mul_nonneg (hw i hi) (sub_nonneg.mpr (hd i hi))) hk
  simp_rw [mul_sub] at hgap
  rw [Finset.sum_sub_distrib, hsum, sub_zero] at hgap
  have hnonneg : 0 ≤ w k * e k := mul_nonneg (hw k hk) (he k hk)
  have hupper : w k * d k ≤ w k * e k :=
    mul_le_mul_of_nonneg_left (hd k hk) (hw k hk)
  rw [abs_le]
  constructor <;> linarith

/-- Quantitative pinned-facet estimate obtained from the endpoint identity. -/
theorem abs_defect_le_div {ι : Type*} (s : Finset ι)
    (w d e : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (he : ∀ i ∈ s, 0 ≤ e i) (hd : ∀ i ∈ s, d i ≤ e i)
    (hsum : (∑ i ∈ s, w i * d i) = 0) {k : ι} (hk : k ∈ s)
    (hwk : 0 < w k) : |d k| ≤ (∑ i ∈ s, w i * e i) / w k := by
  have h := abs_weighted_defect_le s w d e hw he hd hsum hk
  rw [abs_mul, abs_of_pos hwk] at h
  apply (le_div_iff₀ hwk).mpr
  simpa only [mul_comm] using h

end MovingSofaUniqueness
