module

public import Mathlib

/-!
# A two-point formula for quotienting one translation mode

Proof source, not yet compiled in this session.

The argument is independent of moving sofas. A family of scalar intervals has
nonempty intersection when every lower endpoint is below every upper endpoint
and one interval is bounded. This proves the exact two-point formula for the
uniform approximation of a bounded function by multiples of a fixed function.
The weights may vanish or change sign; zero weights are not divided by.

For support functions the weight is `cos`, restricted to the upper semicircle.
The cap/Euclidean-distance adapter is a separate result, not an assumption in
this theorem or an assertion that the full-Q coefficient has been checked.
-/

@[expose] public section
noncomputable section

open Set

namespace MovingSofaQuantitative

variable {ι : Type*}

/-- A radius attainable by subtracting one scalar multiple of a fixed mode. -/
def FitsTranslation (f w : ι → ℝ) (r : ℝ) : Prop :=
  ∃ a : ℝ, ∀ i, |f i - a * w i| ≤ r

/-- The obstruction imposed by two evaluations. A zero denominator gives zero;
indices of zero weight are still detected by pairing with a nonzero weight. -/
def pairScore (f w : ι → ℝ) (i j : ι) : ℝ :=
  |f i * w j - f j * w i| / (|w i| + |w j|)

/-- The supremum of the two-evaluation obstructions. -/
def quotientScore (f w : ι → ℝ) : ℝ :=
  sSup (Set.range fun ij : ι × ι => pairScore f w ij.1 ij.2)

/-- The infimum of nonnegative attainable radii. Nonemptiness and lower
boundedness are supplied in the exact-formula theorem below. -/
def quotientRadius (f w : ι → ℝ) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ FitsTranslation f w r}

theorem pairScore_nonneg (f w : ι → ℝ) (i j : ι) : 0 ≤ pairScore f w i j :=
  div_nonneg (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))

/-- A common approximating multiple satisfies every pairwise constraint. -/
theorem pairwise_of_fits {f w : ι → ℝ} {r : ℝ}
    (h : FitsTranslation f w r) (i j : ι) :
    |f i * w j - f j * w i| ≤ r * (|w i| + |w j|) := by
  obtain ⟨a, ha⟩ := h
  calc
    |f i * w j - f j * w i| =
        |(f i - a * w i) * w j - (f j - a * w j) * w i| := by congr 1; ring
    _ ≤ |(f i - a * w i) * w j| + |(f j - a * w j) * w i| := abs_sub _ _
    _ = |f i - a * w i| * |w j| + |f j - a * w j| * |w i| := by rw [abs_mul, abs_mul]
    _ ≤ r * |w j| + r * |w i| := add_le_add
      (mul_le_mul_of_nonneg_right (ha i) (abs_nonneg _))
      (mul_le_mul_of_nonneg_right (ha j) (abs_nonneg _))
    _ = r * (|w i| + |w j|) := by ring

private theorem normalized_pair_bound {x y u v r : ℝ} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : |x * v - y * u| ≤ r * (|u| + |v|)) :
    |x / u - y / v| ≤ r / |u| + r / |v| := by
  have hau : |u| ≠ 0 := abs_ne_zero.mpr hu
  have hav : |v| ≠ 0 := abs_ne_zero.mpr hv
  have he : x / u - y / v = (x * v - y * u) / (u * v) := by
    field_simp [hu, hv] <;> ring
  rw [he, abs_div, abs_mul]
  apply (div_le_iff₀ (mul_pos (abs_pos.mpr hu) (abs_pos.mpr hv))).2
  have hm : (r / |u| + r / |v|) * (|u| * |v|) = r * (|u| + |v|) := by
    field_simp [hau, hav] <;> ring
  rwa [hm]

/-- Exact feasibility criterion for a rank-one uniform approximation.
No compactness of the index set or continuity of the data is needed. -/
theorem fitsTranslation_iff_pairwise {f w : ι → ℝ}
    (hw : ∃ i, w i ≠ 0) (r : ℝ) :
    FitsTranslation f w r ↔
      ∀ i j, |f i * w j - f j * w i| ≤ r * (|w i| + |w j|) := by
  constructor
  · intro h i j
    exact pairwise_of_fits h i j
  · intro hp
    obtain ⟨i₀, hi₀⟩ := hw
    let J := {i : ι // w i ≠ 0}
    let lower : J → ℝ := fun i => f i / w i - r / |w i|
    let upper : J → ℝ := fun i => f i / w i + r / |w i|
    have hlu : ∀ i j : J, lower i ≤ upper j := by
      intro i j
      have hh := normalized_pair_bound i.property j.property (hp i j)
      have hh' := (abs_le.mp hh).2
      dsimp [lower, upper]
      linarith
    let L := Set.range lower
    have hLne : L.Nonempty := ⟨lower ⟨i₀, hi₀⟩, mem_range_self _⟩
    have hLbdd : BddAbove L := by
      refine ⟨upper ⟨i₀, hi₀⟩, ?_⟩
      rintro _ ⟨j, rfl⟩
      exact hlu j ⟨i₀, hi₀⟩
    refine ⟨sSup L, ?_⟩
    intro i
    by_cases hi : w i = 0
    · have hh := hp i i₀
      simp only [hi, mul_zero, sub_zero, abs_mul, abs_zero, zero_add] at hh
      have hf := (mul_le_mul_right (abs_pos.mpr hi₀)).mp hh
      simpa only [hi, mul_zero, sub_zero] using hf
    · let j : J := ⟨i, hi⟩
      have hlo : lower j ≤ sSup L := le_csSup hLbdd (mem_range_self j)
      have hup : sSup L ≤ upper j := by
        apply csSup_le hLne
        rintro _ ⟨k, rfl⟩
        exact hlu k j
      have hh : |f i / w i - sSup L| ≤ r / |w i| := by
        apply abs_le.mpr
        dsimp [lower, upper, j] at hlo hup
        constructor <;> linarith
      have hm := (le_div_iff₀ (abs_pos.mpr hi)).mp hh
      have he : f i - sSup L * w i = (f i / w i - sSup L) * w i := by
        field_simp [hi] <;> ring
      rw [he, abs_mul]
      exact hm

theorem pairScore_le_of_fits {f w : ι → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (h : FitsTranslation f w r) (i j : ι) : pairScore f w i j ≤ r := by
  have hn : 0 ≤ |w i| + |w j| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  rcases hn.eq_or_lt with hz | hp
  · simp only [pairScore, ← hz, div_zero]
    exact hr
  · exact (div_le_iff₀ hp).2 (pairwise_of_fits h i j)

theorem pairwise_of_pairScore_le {f w : ι → ℝ} {r : ℝ}
    (h : ∀ i j, pairScore f w i j ≤ r) (i j : ι) :
    |f i * w j - f j * w i| ≤ r * (|w i| + |w j|) := by
  have hn : 0 ≤ |w i| + |w j| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  rcases hn.eq_or_lt with hz | hp
  · have hi : w i = 0 := abs_eq_zero.mp (by
      linarith [abs_nonneg (w i), abs_nonneg (w j)])
    have hj : w j = 0 := abs_eq_zero.mp (by
      linarith [abs_nonneg (w i), abs_nonneg (w j)])
    simp [hi, hj]
  · exact (div_le_iff₀ hp).mp (h i j)

/-- The exact two-point formula, including existence of a best translation.
The boundedness hypothesis is discharged by continuity on the compact angular
interval in support-function applications. -/
theorem quotientRadius_eq_score_and_attained {f w : ι → ℝ}
    (hw : ∃ i, w i ≠ 0) {B : ℝ} (hB : ∀ i, |f i| ≤ B) :
    quotientRadius f w = quotientScore f w ∧
      0 ≤ quotientScore f w ∧ FitsTranslation f w (quotientScore f w) := by
  obtain ⟨i₀, hi₀⟩ := hw
  have hB0 : 0 ≤ B := (abs_nonneg (f i₀)).trans (hB i₀)
  have hfitB : FitsTranslation f w B := ⟨0, by simpa using hB⟩
  let V := Set.range fun ij : ι × ι => pairScore f w ij.1 ij.2
  have hVne : V.Nonempty := ⟨pairScore f w i₀ i₀, mem_range_self (i₀, i₀)⟩
  have hVbdd : BddAbove V := by
    refine ⟨B, ?_⟩
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact pairScore_le_of_fits hB0 hfitB i j
  have hscore : ∀ i j, pairScore f w i j ≤ quotientScore f w :=
    fun i j => le_csSup hVbdd (mem_range_self (i, j))
  have hnonneg : 0 ≤ quotientScore f w :=
    (pairScore_nonneg f w i₀ i₀).trans (hscore i₀ i₀)
  have hatt : FitsTranslation f w (quotientScore f w) :=
    (fitsTranslation_iff_pairwise ⟨i₀, hi₀⟩ _).2 (pairwise_of_pairScore_le hscore)
  refine ⟨le_antisymm ?_ ?_, hnonneg, hatt⟩
  · exact csInf_le ⟨0, fun _ hr => hr.1⟩ ⟨hnonneg, hatt⟩
  · apply le_csInf ⟨B, hB0, hfitB⟩
    rintro r ⟨hr, hfit⟩
    exact csSup_le hVne (by
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact pairScore_le_of_fits hr hfit i j)

/-- Subtracting a translation mode leaves every two-point obstruction unchanged. -/
theorem pairScore_sub_mode (f w : ι → ℝ) (a : ℝ) (i j : ι) :
    pairScore (fun i => f i - a * w i) w i j = pairScore f w i j := by
  have he : (f i - a * w i) * w j - (f j - a * w j) * w i =
      f i * w j - f j * w i := by ring
  simp only [pairScore, he]

/-- Opposite unit weights detect width error independently of alignment. -/
theorem endpoint_width_lower {f w : ι → ℝ} {r : ℝ}
    (h : FitsTranslation f w r) {i j : ι} (hi : w i = 1) (hj : w j = -1) :
    |f i + f j| / 2 ≤ r := by
  have hp := pairwise_of_fits h i j
  have he : f i * w j - f j * w i = -(f i + f j) := by rw [hi, hj]; ring
  rw [he, abs_neg, hi, hj] at hp
  norm_num at hp
  linarith

end MovingSofaQuantitative
