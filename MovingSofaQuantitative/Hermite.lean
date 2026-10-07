module

public import MovingSofaQuantitative.PiecewiseCalculus

/-!
# Exact cubic Hermite interpolation

Uncompiled proof source. The coefficients and endpoint data are real, so the
same construction applies to rational trial data and analytic matching slopes.
All derivative and curvature bounds are symbolic inequalities, not samples.
This module does not by itself assert that a perturbed support is convex.
-/

@[expose] public section
noncomputable section

open Real Set

namespace MovingSofaQuantitative

structure Cubic where
  a₀ : ℝ
  a₁ : ℝ
  a₂ : ℝ
  a₃ : ℝ

namespace Cubic

def value (p : Cubic) (z : ℝ) : ℝ := p.a₀ + p.a₁ * z + p.a₂ * z ^ 2 + p.a₃ * z ^ 3

def first (p : Cubic) (z : ℝ) : ℝ := p.a₁ + 2 * p.a₂ * z + 3 * p.a₃ * z ^ 2

def second (p : Cubic) (z : ℝ) : ℝ := 2 * p.a₂ + 6 * p.a₃ * z

def valueBound (p : Cubic) : ℝ := |p.a₀| + |p.a₁| + |p.a₂| + |p.a₃|
def firstBound (p : Cubic) : ℝ := |p.a₁| + 2 * |p.a₂| + 3 * |p.a₃|
def secondBound (p : Cubic) : ℝ := 2 * |p.a₂| + 6 * |p.a₃|

theorem hasDerivAt_value (p : Cubic) (z : ℝ) : HasDerivAt p.value (p.first z) z := by
  have h := (((hasDerivAt_const z p.a₀).add
    ((hasDerivAt_id z).const_mul p.a₁)).add
    ((hasDerivAt_pow 2 z).const_mul p.a₂)).add
    ((hasDerivAt_pow 3 z).const_mul p.a₃)
  convert h using 1 <;> simp only [value, first] <;> ring

theorem hasDerivAt_first (p : Cubic) (z : ℝ) : HasDerivAt p.first (p.second z) z := by
  have h := ((hasDerivAt_const z p.a₁).add
    ((hasDerivAt_id z).const_mul (2 * p.a₂))).add
    ((hasDerivAt_pow 2 z).const_mul (3 * p.a₃))
  convert h using 1 <;> simp only [first, second] <;> ring

theorem continuous_value (p : Cubic) : Continuous p.value :=
  continuous_iff_continuousAt.mpr fun z => (p.hasDerivAt_value z).continuousAt

theorem continuous_first (p : Cubic) : Continuous p.first :=
  continuous_iff_continuousAt.mpr fun z => (p.hasDerivAt_first z).continuousAt

theorem valueBound_nonneg (p : Cubic) : 0 ≤ p.valueBound := by unfold valueBound; positivity

theorem firstBound_nonneg (p : Cubic) : 0 ≤ p.firstBound := by unfold firstBound; positivity

theorem secondBound_nonneg (p : Cubic) : 0 ≤ p.secondBound := by unfold secondBound; positivity

private theorem mul_pow_bound (a : ℝ) {z : ℝ} (hz : z ∈ Icc 0 1) (n : ℕ) :
    |a * z ^ n| ≤ |a| := by
  rw [abs_mul, abs_pow, abs_of_nonneg hz.1]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hz.1 hz.2)

theorem abs_value_le (p : Cubic) {z : ℝ} (hz : z ∈ Icc 0 1) :
    |p.value z| ≤ p.valueBound := by
  have h1 := mul_pow_bound p.a₁ hz 1
  have h2 := mul_pow_bound p.a₂ hz 2
  have h3 := mul_pow_bound p.a₃ hz 3
  simpa only [pow_one] using
    ((abs_add_le (p.a₀ + p.a₁ * z + p.a₂ * z ^ 2) (p.a₃ * z ^ 3)).trans
      (add_le_add ((abs_add_le (p.a₀ + p.a₁ * z) (p.a₂ * z ^ 2)).trans
        (add_le_add ((abs_add_le p.a₀ (p.a₁ * z)).trans
          (add_le_add_left (by simpa only [pow_one] using h1) _)) h2)) h3))

theorem abs_first_le (p : Cubic) {z : ℝ} (hz : z ∈ Icc 0 1) :
    |p.first z| ≤ p.firstBound := by
  have h2 := mul_pow_bound (2 * p.a₂) hz 1
  have h3 := mul_pow_bound (3 * p.a₃) hz 2
  have ht := (abs_add_le (p.a₁ + 2 * p.a₂ * z) (3 * p.a₃ * z ^ 2)).trans
    (add_le_add (abs_add_le p.a₁ (2 * p.a₂ * z)) le_rfl)
  norm_num only [abs_mul, abs_ofNat, pow_one] at h2 h3
  unfold first firstBound
  linarith only [ht, h2, h3]

theorem abs_second_le (p : Cubic) {z : ℝ} (hz : z ∈ Icc 0 1) :
    |p.second z| ≤ p.secondBound := by
  have h3 := mul_pow_bound (6 * p.a₃) hz 1
  have ht := abs_add_le (2 * p.a₂) (6 * p.a₃ * z)
  norm_num only [abs_mul, abs_ofNat, pow_one] at h3 ht
  unfold second secondBound
  linarith only [h3, ht]

end Cubic

/-- The two physical slopes are scaled by the interval length before making
the normalized polynomial. -/
def hermiteCoefficients (h y₀ y₁ d₀ d₁ : ℝ) : Cubic :=
  ⟨y₀, h * d₀, 3 * (y₁ - y₀) - h * (2 * d₀ + d₁),
    2 * (y₀ - y₁) + h * (d₀ + d₁)⟩

def hermiteValue (a b y₀ y₁ d₀ d₁ t : ℝ) : ℝ :=
  (hermiteCoefficients (b - a) y₀ y₁ d₀ d₁).value ((t - a) / (b - a))

def hermiteFirst (a b y₀ y₁ d₀ d₁ t : ℝ) : ℝ :=
  (hermiteCoefficients (b - a) y₀ y₁ d₀ d₁).first ((t - a) / (b - a)) / (b - a)

def hermiteSecond (a b y₀ y₁ d₀ d₁ t : ℝ) : ℝ :=
  (hermiteCoefficients (b - a) y₀ y₁ d₀ d₁).second ((t - a) / (b - a)) / (b - a) ^ 2

@[simp] theorem hermiteValue_left (a b y₀ y₁ d₀ d₁ : ℝ) :
    hermiteValue a b y₀ y₁ d₀ d₁ a = y₀ := by
  simp [hermiteValue, hermiteCoefficients, Cubic.value]

@[simp] theorem hermiteValue_right {a b : ℝ} (hab : a ≠ b) (y₀ y₁ d₀ d₁ : ℝ) :
    hermiteValue a b y₀ y₁ d₀ d₁ b = y₁ := by
  have h : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  simp only [hermiteValue, div_self h, hermiteCoefficients, Cubic.value]
  ring

@[simp] theorem hermiteFirst_left {a b : ℝ} (hab : a ≠ b) (y₀ y₁ d₀ d₁ : ℝ) :
    hermiteFirst a b y₀ y₁ d₀ d₁ a = d₀ := by
  have h : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  simp [hermiteFirst, hermiteCoefficients, Cubic.first, h]

@[simp] theorem hermiteFirst_right {a b : ℝ} (hab : a ≠ b) (y₀ y₁ d₀ d₁ : ℝ) :
    hermiteFirst a b y₀ y₁ d₀ d₁ b = d₁ := by
  have h : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  simp only [hermiteFirst, div_self h, hermiteCoefficients, Cubic.first]
  field_simp [h]
  ring

theorem hermite_hasDerivAt (a b y₀ y₁ d₀ d₁ t : ℝ) :
    HasDerivAt (hermiteValue a b y₀ y₁ d₀ d₁) (hermiteFirst a b y₀ y₁ d₀ d₁ t) t := by
  have h := ((hermiteCoefficients (b - a) y₀ y₁ d₀ d₁).hasDerivAt_value
    ((t - a) / (b - a))).comp t (((hasDerivAt_id t).sub_const a).div_const (b - a))
  convert h using 1 <;> simp only [hermiteValue, hermiteFirst] <;> ring

theorem hermiteFirst_hasDerivAt (a b y₀ y₁ d₀ d₁ t : ℝ) :
    HasDerivAt (hermiteFirst a b y₀ y₁ d₀ d₁) (hermiteSecond a b y₀ y₁ d₀ d₁ t) t := by
  have h := (((hermiteCoefficients (b - a) y₀ y₁ d₀ d₁).hasDerivAt_first
    ((t - a) / (b - a))).comp t
    (((hasDerivAt_id t).sub_const a).div_const (b - a))).div_const (b - a)
  convert h using 1 <;> simp only [hermiteFirst, hermiteSecond] <;> ring

theorem hermite_coordinate_mem {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b) :
    (t - a) / (b - a) ∈ Icc (0 : ℝ) 1 := by
  exact ⟨div_nonneg (sub_nonneg.mpr ht.1) (sub_pos.mpr hab).le,
    (div_le_one (sub_pos.mpr hab)).mpr (by linarith [ht.2])⟩

/-- A single explicit finite bound controls the curvature perturbation over
the WHOLE interpolation interval. No mesh of derivative samples is used. -/
theorem hermite_curvature_bound {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    (y₀ y₁ d₀ d₁ : ℝ) :
    |hermiteSecond a b y₀ y₁ d₀ d₁ t + hermiteValue a b y₀ y₁ d₀ d₁ t| ≤
      (hermiteCoefficients (b - a) y₀ y₁ d₀ d₁).secondBound / (b - a) ^ 2 +
      (hermiteCoefficients (b - a) y₀ y₁ d₀ d₁).valueBound := by
  have hz := hermite_coordinate_mem hab ht
  let p := hermiteCoefficients (b - a) y₀ y₁ d₀ d₁
  have h2 : |hermiteSecond a b y₀ y₁ d₀ d₁ t| ≤ p.secondBound / (b - a) ^ 2 := by
    rw [hermiteSecond, abs_div, abs_of_nonneg (sq_nonneg _)]
    exact div_le_div_of_nonneg_right (p.abs_second_le hz) (sq_nonneg _)
  exact (abs_add_le _ _).trans (add_le_add h2 (p.abs_value_le hz))

/-- A uniform bound on the physical first derivative. -/
theorem hermite_first_bound {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    (y₀ y₁ d₀ d₁ : ℝ) :
    |hermiteFirst a b y₀ y₁ d₀ d₁ t| ≤
      (hermiteCoefficients (b - a) y₀ y₁ d₀ d₁).firstBound / (b - a) := by
  rw [hermiteFirst, abs_div, abs_of_pos (sub_pos.mpr hab)]
  exact div_le_div_of_nonneg_right
    ((hermiteCoefficients (b - a) y₀ y₁ d₀ d₁).abs_first_le (hermite_coordinate_mem hab ht))
    (sub_pos.mpr hab).le

end MovingSofaQuantitative
