module

public import MovingSofaQuantitative.OneSidedSmoothing
public import MovingSofaQuantitative.LocalizedSquare

/-!
# The cap perturbation differs from the representer only on two short arcs

Uncompiled proof source. The error is identified as a function and through
uniqueness of its actual right derivative. Reflection uses the LEFT derivative
of the half-profile at a knot; otherwise the endpoint at pi-phi would be wrong.
-/

@[expose] public section
noncomputable section

open Real Set Filter Topology MeasureTheory
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative.OneSidedSmoothing

variable {φ η : ℝ}

def patch (φ η : ℝ) := rightJoin φ (fun _ => 0)
  (rightJoin (φ + η) (bump φ η) (fun _ => 0))

def patchFirst (φ η : ℝ) := rightJoin φ (fun _ => 0)
  (rightJoin (φ + η) (bumpFirst φ η) (fun _ => 0))

def patchFirstLeft (φ η : ℝ) := leftJoin φ (fun _ => 0)
  (leftJoin (φ + η) (bumpFirst φ η) (fun _ => 0))

def symmetricPatch (φ η t : ℝ) : ℝ :=
  if t ≤ π / 2 then patch φ η t else patch φ η (π - t)

def symmetricPatchDerivative (φ η : ℝ) := rightJoin (π / 2) (patchFirst φ η)
  (fun t => -patchFirstLeft φ η (π - t))

theorem patch_rightDeriv (t : ℝ) :
    HasDerivWithinAt (patch φ η) (patchFirst φ η t) (Ioi t) t :=
  rightDeriv_rightJoin (fun u => (hasDerivAt_const u 0).hasDerivWithinAt)
    (fun u => rightDeriv_rightJoin
      (fun v => (hermite_hasDerivAt _ _ _ _ _ _ v).hasDerivWithinAt)
      (fun v => (hasDerivAt_const v 0).hasDerivWithinAt) u) t

theorem patch_leftDeriv (hη : 0 < η) (t : ℝ) :
    HasDerivWithinAt (patch φ η) (patchFirstLeft φ η t) (Iio t) t := by
  have hne : φ ≠ φ + η := ne_of_lt (by linarith)
  have htail := leftDeriv_rightJoin
    (by exact hermiteValue_right hne 0 0 (J φ) 0)
    (fun v => (hermite_hasDerivAt _ _ _ _ _ _ v).hasDerivWithinAt)
    (fun v => (hasDerivAt_const v 0).hasDerivWithinAt)
  exact leftDeriv_rightJoin
    (by simp [rightJoin, show φ < φ + η by linarith, bump])
    (fun v => (hasDerivAt_const v 0).hasDerivWithinAt) htail t

theorem symmetricPatch_rightDeriv (hη : 0 < η) (t : ℝ) :
    HasDerivWithinAt (symmetricPatch φ η) (symmetricPatchDerivative φ η t) (Ioi t) t := by
  have he : symmetricPatch φ η = rightJoin (π / 2) (patch φ η)
      (fun t => patch φ η (π - t)) := by
    funext u
    unfold symmetricPatch rightJoin
    split_ifs <;> try rfl
    · have hu : u = π / 2 := by linarith
      subst u
      congr 1
      ring
    · exfalso
      linarith
  rw [he]
  apply rightDeriv_rightJoin patch_rightDeriv
  intro u
  have harg := ((hasDerivAt_id u).const_sub π).hasDerivWithinAt (s := Ioi u)
  have hmap : MapsTo (fun v : ℝ => π - v) (Ioi u) (Iio (π - u)) := by
    intro v hv
    change π - v < π - u
    linarith [hv]
  convert (patch_leftDeriv hη (π - u)).comp u harg hmap using 1 <;> ring

/-- Polynomial coefficients bound the entire bump, not finitely many samples. -/
theorem bump_bounds (hφ : φ ∈ Ioo 0 (π / 4)) (hη : 0 < η)
    {t : ℝ} (ht : t ∈ Icc φ (φ + η)) :
    |bump φ η t| ≤ 4 * J φ * η ∧ |bumpFirst φ η t| ≤ 8 * J φ := by
  have hJ := J_nonneg hφ
  have hz := hermite_coordinate_mem (show φ < φ + η by linarith) ht
  have hv := (hermiteCoefficients η 0 0 (J φ) 0).abs_value_le
    (by simpa only [add_sub_cancel_left] using hz)
  have hd := hermite_first_bound (show φ < φ + η by linarith) ht 0 0 (J φ) 0
  have hn₀ : (hermiteCoefficients η 0 0 (J φ) 0).valueBound = 4 * J φ * η := by
    simp only [hermiteCoefficients, Cubic.valueBound, sub_self, zero_mul,
      add_zero, zero_add, abs_zero, neg_mul, abs_neg, abs_mul,
      abs_of_nonneg hη.le, abs_of_nonneg hJ, abs_ofNat]
    ring
  have hn₁ : (hermiteCoefficients η 0 0 (J φ) 0).firstBound / η = 8 * J φ := by
    simp only [hermiteCoefficients, Cubic.firstBound, sub_self, zero_mul,
      add_zero, zero_add, abs_zero, neg_mul, abs_neg, abs_mul,
      abs_of_nonneg hη.le, abs_of_nonneg hJ, abs_ofNat]
    field_simp [hη.ne']
    ring
  refine ⟨?_, ?_⟩
  · simpa only [bump, hermiteValue, show φ + η - φ = η by ring, hn₀] using hv
  · simpa only [bumpFirst, show φ + η - φ = η by ring, hn₁] using hd

theorem patch_bounds (hφ : φ ∈ Ioo 0 (π / 4)) (hη : 0 < η) (t : ℝ) :
    |patch φ η t| ≤ 4 * J φ * η ∧
    |patchFirst φ η t| ≤ 8 * J φ ∧ |patchFirstLeft φ η t| ≤ 8 * J φ := by
  have hJ := J_nonneg hφ
  unfold patch patchFirst patchFirstLeft rightJoin leftJoin
  split_ifs <;> first
    | exact ⟨by positivity, by positivity, by positivity⟩
    | (have hb := bump_bounds hφ hη (t := t) (by constructor <;> linarith); aesop)

/-- The reflected patch has the same uniform value and derivative bounds. -/
theorem symmetricPatch_bounds (hφ : φ ∈ Ioo 0 (π / 4)) (hη : 0 < η) (t : ℝ) :
    |symmetricPatch φ η t| ≤ 4 * J φ * η ∧
    |symmetricPatchDerivative φ η t| ≤ 8 * J φ := by
  have h1 := patch_bounds hφ hη t
  have h2 := patch_bounds hφ hη (π - t)
  unfold symmetricPatch symmetricPatchDerivative rightJoin
  split_ifs <;> simp only [abs_neg] <;> aesop

theorem half_difference_patch (hη : 0 < η) (hsep : φ + η < π / 2 - φ) (t : ℝ) :
    value φ η t - rawValue φ t = patch φ η t := by
  unfold value rawValue patch joined rightJoin
  simp only [piece]
  split_ifs <;> first | ring | (exfalso; linarith)

/-- The unsmoothed half profile is the negative midpoint-centered representer. -/
theorem raw_comparison (hφ : φ ∈ Ioo 0 (π / 4)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (π / 2)) :
    rawValue φ t + comparisonProfile φ t - (A φ) ^ 2 * cos t = 0 := by
  rw [comparisonProfile_eq_covariance hφ]
  have hc := (cap_angle_parameters hφ).1.ne'
  have hunit := sin_sq_add_cos_sq φ
  unfold rawValue rightJoin greenCovariance
  simp only [piece, A]
  split_ifs <;> try ring
  all_goals first
    | (exfalso; linarith [ht.1, ht.2, hφ.1, hφ.2, pi_pos])
    | (have he : t = φ := by linarith; subst t; field_simp [hc]; ring)
    | (have he : t = π / 2 - φ := by linarith; subst t;
        simp only [cos_pi_div_two_sub, sin_pi_div_two_sub];
        field_simp [hc]; nlinarith [hunit])
    | (have he : t = π / 2 := by linarith; subst t; simp)

/-- Symmetry applies to the centered representer, not to the pinned one. -/
theorem comparison_centered_reflection (hφ : φ ∈ Ioo 0 (π / 4))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) π) :
    comparisonProfile φ t - (A φ) ^ 2 * cos t =
      comparisonProfile φ (π - t) - (A φ) ^ 2 * cos (π - t) := by
  rw [comparisonProfile_eq_covariance hφ, comparisonProfile_eq_covariance hφ]
  have hc := (cap_angle_parameters hφ).1.ne'
  have hunit := sin_sq_add_cos_sq φ
  unfold greenCovariance
  simp only [sin_pi_sub, cos_pi_sub, A]
  split_ifs <;> try ring
  all_goals first
    | (exfalso; linarith [ht.1, ht.2, hφ.1, hφ.2, pi_pos])
    | (have he : t = φ := by linarith; subst t; field_simp [hc]; ring)
    | (have he : t = π - φ := by linarith; subst t;
       simp only [sin_pi_sub, cos_pi_sub]; field_simp [hc]; ring)
    | (have he : t = π / 2 - φ := by linarith; subst t;
       simp only [cos_pi_div_two_sub, sin_pi_div_two_sub]; field_simp [hc]; nlinarith [hunit])
    | (have he : t = π / 2 + φ := by linarith; subst t;
       simp only [cos_add, sin_add, cos_pi_div_two, sin_pi_div_two]; field_simp [hc]; nlinarith [hunit])
    | (have he : t = π / 2 := by linarith; subst t; simp)

/-- This identifies the actual error, not merely its pointwise norm bound. -/
theorem error_value (hφ : φ ∈ Ioo 0 (π / 4)) (hη : 0 < η)
    (hsep : φ + η < π / 2 - φ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) π) :
    (profile hφ hη hsep).pinnedProfile t + comparisonProfile φ t = symmetricPatch φ η t := by
  let F := profile hφ hη hsep
  have hFπ : F.symmetricValue π = -(A φ)^2 := by
    rw [F.symmetricValue_pi]
    exact profile_zero hφ hη hsep
  change F.pinnedProfile t + comparisonProfile φ t = _
  unfold HalfCapProfile.pinnedProfile pinnedDifference
  rw [hFπ]
  by_cases htv : t ≤ π / 2
  · have hraw := raw_comparison hφ ⟨ht.1, htv⟩
    have hdiff := half_difference_patch hη hsep t
    simp only [HalfCapProfile.symmetricValue, symmetricPatch, if_pos htv]
    change value φ η t + -(A φ)^2 * cos t + comparisonProfile φ t = _
    linarith
  · have hu : π - t ∈ Icc (0 : ℝ) (π / 2) := ⟨by linarith [ht.2], by linarith⟩
    have hraw := raw_comparison hφ hu
    have href := comparison_centered_reflection hφ ht
    have hdiff := half_difference_patch hη hsep (π - t)
    simp only [HalfCapProfile.symmetricValue, symmetricPatch, if_neg htv]
    change value φ η (π - t) + -(A φ)^2 * cos t + comparisonProfile φ t = _
    linarith

/-- The derivative at a reflected knot is fixed by uniqueness of the right
one-sided derivative; it is not assigned by an informal symmetry argument. -/
theorem error_derivative {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {η : ℝ} (hη : 0 < η) (hsep : P.φ + η < π / 2 - P.φ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) π) :
    (profile (GerverParams.gm_φ_mem_Ioo hP hbox) hη hsep).pinnedProfileDerivative t +
      comparisonDerivative P.φ t = symmetricPatchDerivative P.φ η t := by
  have hφ := GerverParams.gm_φ_mem_Ioo hP hbox
  let F := profile hφ hη hsep
  exact rightDerivative_eq_of_upper_profile
    (fun u _ => (F.pinnedProfile_rightDeriv u).add (comparisonProfile_rightDeriv P.φ u))
    (fun u _ => symmetricPatch_rightDeriv hη u)
    (fun u hu => error_value hφ hη hsep hu) ht

end MovingSofaQuantitative.OneSidedSmoothing
