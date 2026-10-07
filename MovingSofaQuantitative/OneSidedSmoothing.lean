module

public import MovingSofaQuantitative.SymmetricCapPerturbation
public import MovingSofaQuantitative.ComparisonPairing

/-!
# A concrete one-sided smoothing of the extremal cap direction

Uncompiled proof source. The patch is a sine plus a cubic bump, supported only
on the positive-curvature side of the cut. It matches both traces exactly.
The normal gap is never smoothed across. The resulting HalfCapProfile feeds
an already constructed actual convex cap; cap existence is not a hypothesis.
-/

@[expose] public section
noncomputable section

open Real Set Filter Topology MeasureTheory
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative
namespace OneSidedSmoothing

variable {φ η : ℝ}

def A (φ : ℝ) : ℝ := 1 / cos φ
def J (φ : ℝ) : ℝ := (A φ) ^ 2 * sin φ

def bump (φ η : ℝ) := hermiteValue φ (φ + η) 0 0 (J φ) 0
def bumpFirst (φ η : ℝ) := hermiteFirst φ (φ + η) 0 0 (J φ) 0
def bumpSecond (φ η : ℝ) := hermiteSecond φ (φ + η) 0 0 (J φ) 0

def piece (φ η : ℝ) : Fin 4 → ℝ → ℝ
  | 0 => fun t => sin t - (A φ) ^ 2 * cos t
  | 1 => fun t => sin t - A φ + bump φ η t
  | 2 => fun t => sin t - A φ
  | 3 => fun t => -A φ * sin φ * cos t

def first (φ η : ℝ) : Fin 4 → ℝ → ℝ
  | 0 => fun t => cos t + (A φ) ^ 2 * sin t
  | 1 => fun t => cos t + bumpFirst φ η t
  | 2 => cos
  | 3 => fun t => A φ * sin φ * sin t

def second (φ η : ℝ) : Fin 4 → ℝ → ℝ
  | 0 => fun t => -sin t + (A φ) ^ 2 * cos t
  | 1 => fun t => -sin t + bumpSecond φ η t
  | 2 => fun t => -sin t
  | 3 => fun t => A φ * sin φ * cos t

def joined (φ η : ℝ) (f : Fin 4 → ℝ → ℝ) : ℝ → ℝ :=
  rightJoin φ (f 0) (rightJoin (φ + η) (f 1) (rightJoin (π / 2 - φ) (f 2) (f 3)))

def joinedLeft (φ η : ℝ) (f : Fin 4 → ℝ → ℝ) : ℝ → ℝ :=
  leftJoin φ (f 0) (leftJoin (φ + η) (f 1) (leftJoin (π / 2 - φ) (f 2) (f 3)))

def value (φ η : ℝ) := joined φ η (piece φ η)
def deriv (φ η : ℝ) := joined φ η (first φ η)
def secondR (φ η : ℝ) := joined φ η (second φ η)
def secondL (φ η : ℝ) := joinedLeft φ η (second φ η)
def bound (φ η : ℝ) : ℝ := A φ + J φ * (10 / η + 4 * η)

theorem A_pos (hφ : φ ∈ Ioo 0 (π / 4)) : 0 < A φ :=
  one_div_pos.mpr (cap_angle_parameters hφ).1

theorem J_nonneg (hφ : φ ∈ Ioo 0 (π / 4)) : 0 ≤ J φ :=
  mul_nonneg (sq_nonneg _) (sin_nonneg_of_nonneg_of_le_pi hφ.1.le (by linarith [hφ.2, pi_pos]))

theorem derivative_piece (i : Fin 4) (t : ℝ) :
    HasDerivAt (piece φ η i) (first φ η i t) t := by
  fin_cases i
  · convert (hasDerivAt_sin t).sub ((hasDerivAt_cos t).const_mul ((A φ)^2)) using 1 <;> simp [piece, first] <;> ring
  · exact ((hasDerivAt_sin t).sub_const (A φ)).add (hermite_hasDerivAt _ _ _ _ _ _ _)
  · exact (hasDerivAt_sin t).sub_const (A φ)
  · convert (hasDerivAt_cos t).const_mul (-A φ * sin φ) using 1 <;> simp [piece, first] <;> ring

theorem derivative_first (i : Fin 4) (t : ℝ) :
    HasDerivAt (first φ η i) (second φ η i t) t := by
  fin_cases i
  · exact (hasDerivAt_cos t).add ((hasDerivAt_sin t).const_mul ((A φ)^2))
  · exact (hasDerivAt_cos t).add (hermiteFirst_hasDerivAt _ _ _ _ _ _ _)
  · exact hasDerivAt_cos t
  · exact (hasDerivAt_sin t).const_mul (A φ * sin φ)

theorem matches (hφ : φ ∈ Ioo 0 (π / 4)) (hη : 0 < η) :
    (piece φ η 0 φ = piece φ η 1 φ ∧ first φ η 0 φ = first φ η 1 φ) ∧
    (piece φ η 1 (φ + η) = piece φ η 2 (φ + η) ∧
      first φ η 1 (φ + η) = first φ η 2 (φ + η)) ∧
    (piece φ η 2 (π / 2 - φ) = piece φ η 3 (π / 2 - φ) ∧
      first φ η 2 (π / 2 - φ) = first φ η 3 (π / 2 - φ)) := by
  have hc := (cap_angle_parameters hφ).1.ne'
  have hne : φ ≠ φ + η := ne_of_lt (by linarith)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simp only [piece, bump, hermiteValue_left, add_zero, A]
    field_simp [hc]
    ring
  · simp only [first, bumpFirst, hermiteFirst_left hne, J]
  · simp only [piece, bump, hermiteValue_right hne, add_zero]
  · simp only [first, bumpFirst, hermiteFirst_right hne, add_zero]
  · simp only [piece, cos_pi_div_two_sub, sin_pi_div_two_sub, A]
    field_simp [hc]
    nlinarith [sin_sq_add_cos_sq φ]
  · simp only [first, sin_pi_div_two_sub, cos_pi_div_two_sub, A]
    field_simp [hc]

theorem joined_derivative (hφ : φ ∈ Ioo 0 (π / 4)) (hη : 0 < η)
    (hsep : φ + η < π / 2 - φ) (t : ℝ) : HasDerivAt (value φ η) (deriv φ η t) t := by
  have hm := matches hφ hη
  have h23 := hasDerivAt_rightJoin (derivative_piece 2) (derivative_piece 3) hm.2.2.1 hm.2.2.2
  have h12 := hasDerivAt_rightJoin (derivative_piece 1) h23
    (by simpa only [rightJoin, if_pos hsep] using hm.2.1.1)
    (by simpa only [rightJoin, if_pos hsep] using hm.2.1.2)
  apply hasDerivAt_rightJoin (derivative_piece 0) h12
  · simpa only [rightJoin, if_pos (show φ < φ + η by linarith)] using hm.1.1
  · simpa only [rightJoin, if_pos (show φ < φ + η by linarith)] using hm.1.2

theorem deriv_continuous (hφ : φ ∈ Ioo 0 (π / 4)) (hη : 0 < η)
    (hsep : φ + η < π / 2 - φ) : Continuous (deriv φ η) := by
  have hm := matches hφ hη
  have hc (i : Fin 4) : Continuous (first φ η i) :=
    continuous_iff_continuousAt.mpr fun t => (derivative_first i t).continuousAt
  have h23 := continuous_rightJoin (hc 2) (hc 3) hm.2.2.2
  have h12 := continuous_rightJoin (hc 1) h23
    (by simpa only [rightJoin, if_pos hsep] using hm.2.1.2)
  exact continuous_rightJoin (hc 0) h12
    (by simpa only [rightJoin, if_pos (show φ < φ + η by linarith)] using hm.1.2)

theorem second_right (t : ℝ) :
    HasDerivWithinAt (deriv φ η) (secondR φ η t) (Ici t) t := by
  have h := rightDeriv_rightJoin
    (fun u => (derivative_first (φ := φ) (η := η) 0 u).hasDerivWithinAt)
    (fun u => rightDeriv_rightJoin
      (fun v => (derivative_first 1 v).hasDerivWithinAt)
      (fun v => rightDeriv_rightJoin
        (fun w => (derivative_first 2 w).hasDerivWithinAt)
        (fun w => (derivative_first 3 w).hasDerivWithinAt) v) u) t
  have he : Ici t = insert t (Ioi t) := by ext u; simp only [mem_Ici, mem_insert_iff, mem_Ioi]; exact le_iff_eq_or_lt
  rw [he]
  exact h.insert

theorem second_left (hφ : φ ∈ Ioo 0 (π / 4)) (hη : 0 < η)
    (hsep : φ + η < π / 2 - φ) (t : ℝ) :
    HasDerivWithinAt (deriv φ η) (secondL φ η t) (Iic t) t := by
  have hm := matches hφ hη
  have h23 := leftDeriv_rightJoin hm.2.2.2
    (fun u => (derivative_first 2 u).hasDerivWithinAt)
    (fun u => (derivative_first 3 u).hasDerivWithinAt)
  have h12 := leftDeriv_rightJoin
    (by simpa only [rightJoin, if_pos hsep] using hm.2.1.2)
    (fun u => (derivative_first 1 u).hasDerivWithinAt) h23
  have h := leftDeriv_rightJoin
    (by simpa only [rightJoin, if_pos (show φ < φ + η by linarith)] using hm.1.2)
    (fun u => (derivative_first 0 u).hasDerivWithinAt) h12 t
  have he : Iic t = insert t (Iio t) := by ext u; simp only [mem_Iic, mem_insert_iff, mem_Iio]; exact le_iff_eq_or_lt
  rw [he]
  exact h.insert

/-- All scalar curvature bounds cover complete intervals, including their ends. -/
theorem piece_curvature_bound (hφ : φ ∈ Ioo 0 (π / 4)) (hη : 0 < η)
    (i : Fin 4) {t : ℝ} (hpatch : i = 1 → t ∈ Icc φ (φ + η)) :
    |second φ η i t + piece φ η i t| ≤ bound φ η := by
  have hA := A_pos hφ
  have hJ := J_nonneg hφ
  have hB : 0 ≤ J φ * (10 / η + 4 * η) := by positivity
  have hM : 0 ≤ bound φ η := by unfold bound; positivity
  fin_cases i
  · simpa [second, piece, bound] using hM
  · have hh := hermite_curvature_bound (show φ < φ + η by linarith)
      (hpatch rfl) (0 : ℝ) 0 (J φ) 0
    have hn : (hermiteCoefficients η 0 0 (J φ) 0).secondBound / η^2 +
        (hermiteCoefficients η 0 0 (J φ) 0).valueBound = J φ * (10 / η + 4 * η) := by
      simp only [hermiteCoefficients, Cubic.secondBound, Cubic.valueBound,
        sub_self, zero_mul, add_zero, zero_add, neg_mul, abs_neg,
        abs_mul, abs_of_nonneg hη.le, abs_of_nonneg hJ, abs_ofNat, abs_zero]
      field_simp [hη.ne']
      ring
    rw [show φ + η - φ = η by ring, hn] at hh
    have ht := (abs_add_le (-A φ) (bumpSecond φ η t + bump φ η t)).trans
      (add_le_add_left hh _)
    simpa only [piece, second, show -sin t + bumpSecond φ η t +
        (sin t - A φ + bump φ η t) = -A φ + (bumpSecond φ η t + bump φ η t) by ring,
      abs_neg, abs_of_pos hA, bound] using ht
  · simpa [second, piece, abs_of_pos hA, bound] using le_add_of_nonneg_right hB
  · simpa [second, piece] using hM

/-- The concrete profile already meets every condition required to construct
an actual cap. The amplitude is supplied by HalfCapProfile.safeAmplitude. -/
def profile (hφ : φ ∈ Ioo 0 (π / 4)) (hη : 0 < η)
    (hsep : φ + η < π / 2 - φ) : HalfCapProfile φ where
  value := value φ η
  first := deriv φ η
  secondR := secondR φ η
  secondL := secondL φ η
  curvatureBound := bound φ η
  bound_nonneg := by have hA := A_pos hφ; have hJ := J_nonneg hφ; unfold bound; positivity
  derivative := joined_derivative hφ hη hsep
  first_continuous := deriv_continuous hφ hη hsep
  second_right := second_right
  second_left := second_left hφ hη hsep
  top_zero := by
    have hpv : φ < π / 2 := by linarith [hφ.2, pi_pos]
    have he : φ + η < π / 2 := hsep.trans (by linarith [hφ.1])
    simp [value, joined, rightJoin, not_lt.mpr hpv.le, not_lt.mpr he.le,
      not_lt.mpr (show π / 2 - φ ≤ π / 2 by linarith [hφ.1]), piece]
  endpoint_up := by simp [deriv, joined, rightJoin, hφ.1, first]
  gap_right t ht := by simp [secondR, value, joined, rightJoin, ht.2, second, piece]
  gap_left t ht := by
    rcases ht.2.lt_or_eq with h | rfl
    · simp [secondL, value, joinedLeft, joined, leftJoin, rightJoin, h.le, h, second, piece]
    · have hm := (matches hφ hη).1.1
      simp only [secondL, joinedLeft, leftJoin, if_pos le_rfl,
        value, joined, rightJoin, lt_self_iff_false, if_false,
        if_pos (show φ < φ + η by linarith)]
      rw [← hm]
      simp [second, piece]
  central_right t ht := by
    unfold secondR value joined rightJoin
    split_ifs with h0 h1 h2
    all_goals first
      | exact piece_curvature_bound hφ hη _ (by intro hi; contradiction)
      | exact piece_curvature_bound hφ hη 1 (by intro _; exact ⟨ht.1, h1.le⟩)
  central_left t ht := by
    have hm := matches hφ hη
    unfold secondL joinedLeft leftJoin value joined rightJoin
    split_ifs with h0 h1 h2 h3 h4 h5
    all_goals first
      | (exfalso; linarith [ht.1, ht.2, hsep])
      | exact piece_curvature_bound hφ hη _ (by intro hi; contradiction)
      | exact piece_curvature_bound hφ hη 1 (by intro _; constructor <;> linarith)
      | (have he : t = φ := by linarith; subst t; rw [← hm.1.1]; exact piece_curvature_bound hφ hη 0 (by intro h; cases h))
      | (have he : t = φ + η := by linarith; subst t; rw [← hm.2.1.1]; exact piece_curvature_bound hφ hη 1 (by intro _; exact ⟨by linarith, le_rfl⟩))
      | (have he : t = π / 2 - φ := by linarith; subst t; rw [← hm.2.2.1]; exact piece_curvature_bound hφ hη 2 (by intro h; cases h))

@[simp] theorem profile_zero (hφ : φ ∈ Ioo 0 (π / 4)) (hη : 0 < η)
    (hsep : φ + η < π / 2 - φ) : (profile hφ hη hsep).value 0 = -(A φ)^2 := by
  simp [profile, value, joined, rightJoin, hφ.1, piece]

/-- The scalar support perturbation is zero off its one-sided patch relative
to the unsmoothed three-piece profile. This is used by the energy convergence. -/
def rawValue (φ : ℝ) := rightJoin φ (piece φ 0 0)
  (rightJoin (π / 2 - φ) (piece φ 0 2) (piece φ 0 3))

def rawDeriv (φ : ℝ) := rightJoin φ (first φ 0 0)
  (rightJoin (π / 2 - φ) (first φ 0 2) (first φ 0 3))

theorem value_eq_raw_off_patch (hη : 0 < η) (hsep : φ + η < π / 2 - φ)
    {t : ℝ} (ht : t ∉ Ico φ (φ + η)) : value φ η t = rawValue φ t := by
  unfold value rawValue joined rightJoin
  split_ifs <;> first | rfl | (exfalso; exact ht ⟨by linarith, by linarith⟩) | (exfalso; linarith)

theorem deriv_eq_raw_off_patch (hη : 0 < η) (hsep : φ + η < π / 2 - φ)
    {t : ℝ} (ht : t ∉ Ico φ (φ + η)) : deriv φ η t = rawDeriv φ t := by
  unfold deriv rawDeriv joined rightJoin
  split_ifs <;> first | rfl | (exfalso; exact ht ⟨by linarith, by linarith⟩) | (exfalso; linarith)

end OneSidedSmoothing
end MovingSofaQuantitative
