module

public import MovingSofaStability.CapEstimate
public import MovingSofaQuantitative.TranslationQuotient

/-!
# Midpoint normalization and horizontal cap alignment

Proof source, not yet compiled in this session. This module changes no existing
normalization. The original left-support pin remains in MovingSofaStability.
The centered and freely optimized translations below have separate names.

The support-to-distance adapter treats the lower normals explicitly, so a bound
on the upper semicircle is not silently confused with a bound on actual
nonconvex sets. The converse adapter is used only for convex caps.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability

namespace MovingSofaQuantitative

/-- Midpoint of the horizontal projection, not its left endpoint. -/
def horizontalMidpoint (S : Set Point) : ℝ := (supp S 0 - supp S π) / 2

/-- Center a scalar support difference by its two horizontal endpoint values. -/
def centerFunction (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  f t - ((f 0 - f π) / 2) * cos t

/-- The corresponding right derivative. -/
def centerDerivative (f df : ℝ → ℝ) (t : ℝ) : ℝ :=
  df t + ((f 0 - f π) / 2) * sin t

@[simp] theorem centerFunction_zero (f : ℝ → ℝ) :
    centerFunction f 0 = (f 0 + f π) / 2 := by simp [centerFunction]; ring

@[simp] theorem centerFunction_pi (f : ℝ → ℝ) :
    centerFunction f π = (f 0 + f π) / 2 := by simp [centerFunction]; ring

@[simp] theorem centerFunction_top (f : ℝ → ℝ) :
    centerFunction f (π / 2) = f (π / 2) := by simp [centerFunction]

/-- Centering is unchanged by adding an arbitrary horizontal translation mode. -/
theorem centerFunction_add_cos (f : ℝ → ℝ) (a t : ℝ) :
    centerFunction (fun u => f u + a * cos u) t = centerFunction f t := by
  simp only [centerFunction, cos_zero, cos_pi]
  ring

/-- Recentring the already centred function does nothing. -/
@[simp] theorem centerFunction_idempotent (f : ℝ → ℝ) (t : ℝ) :
    centerFunction (centerFunction f) t = centerFunction f t := by
  rw [centerFunction, centerFunction_zero, centerFunction_pi]
  ring

/-- The analytic formula in terms of the old pinned error. -/
theorem centerFunction_eq_pinned (f : ℝ → ℝ) (t : ℝ) :
    centerFunction f t = pinnedDifference f t - (pinnedDifference f 0 / 2) * cos t := by
  simp only [centerFunction, pinnedDifference, cos_zero]
  ring

/-- Centering does not change a nonsingular tangent residual. -/
theorem tangentResidual_centered (f df : ℝ → ℝ) (T t : ℝ)
    (hs : sin (T - t) ≠ 0) :
    tangentResidual T (centerFunction f) (centerDerivative f df) t =
      tangentResidual T f df t := by
  have h := tangentResidual_translation ((f 0 - f π) / 2) T t hs
  simp only [tangentResidual, centerFunction, centerDerivative] at h ⊢
  linear_combination -h

/-- Centering also preserves the shifted corner residual. -/
@[simp] theorem cornerResidual_centered (f df : ℝ → ℝ) (t : ℝ) :
    cornerResidual (centerFunction f) (centerDerivative f df) t = cornerResidual f df t := by
  simp only [cornerResidual, centerFunction, centerDerivative, cos_add_pi_div_two]
  ring

/-- The support error for an arbitrary horizontal translation of the reference. -/
def horizontalError (K₀ K₁ : Set Point) (a t : ℝ) : ℝ :=
  supp K₁ t - supp K₀ t - a * cos t

def horizontalReference (K : Set Point) (a : ℝ) : Set Point :=
  (fun p => p + (a, 0)) '' K

def centeredReference (K₀ K₁ : Set Point) : Set Point :=
  horizontalReference K₀ (horizontalMidpoint K₁ - horizontalMidpoint K₀)

def centeredCapDifference (K₀ K₁ : Set Point) : ℝ → ℝ :=
  centerFunction (fun t => supp K₁ t - supp K₀ t)

/-- If the horizontal midpoints already agree, the centered reference is the
untranslated reference cap. -/
theorem centeredReference_eq_of_midpoint {K₀ K₁ : Set Point}
    (hmid : horizontalMidpoint K₁ = horizontalMidpoint K₀) :
    centeredReference K₀ K₁ = K₀ := by
  unfold centeredReference horizontalReference
  rw [hmid, sub_self]
  ext p
  simp

/-- Centering a set relative to itself does nothing. -/
@[simp] theorem centeredReference_self (K : Set Point) :
    centeredReference K K = K :=
  centeredReference_eq_of_midpoint rfl

/-- A cap translated by `a` has its horizontal midpoint translated by
`a`; hence its midpoint-aligned reference is that *translated cap*,
not the unshifted reference. -/
theorem centeredReference_translate_eq {K : Set Point}
    (hK : IsConvexBody K) (a : ℝ) :
    centeredReference K (horizontalReference K a) = horizontalReference K a := by
  have hmid : horizontalMidpoint (horizontalReference K a) =
      horizontalMidpoint K + a := by
    unfold horizontalMidpoint horizontalReference
    rw [supp_translate K (a, 0) 0 hK.2.1 hK.1,
      supp_translate K (a, 0) π hK.2.1 hK.1]
    simp [dot, uvec]
    ring
  unfold centeredReference
  rw [hmid]
  simp

theorem centeredCapDifference_eq_error (K₀ K₁ : Set Point) (t : ℝ) :
    centeredCapDifference K₀ K₁ t =
      horizontalError K₀ K₁ (horizontalMidpoint K₁ - horizontalMidpoint K₀) t := by
  unfold centeredCapDifference centerFunction horizontalError horizontalMidpoint
  ring

theorem horizontalError_eq_support {K₀ K₁ : Set Point}
    (h₀ : IsConvexBody K₀) (a t : ℝ) :
    horizontalError K₀ K₁ a t = supp K₁ t - supp (horizontalReference K₀ a) t := by
  rw [horizontalReference, supp_translate K₀ _ t h₀.2.1 h₀.1]
  simp only [horizontalError, dot, uvec]
  ring

/-- Arbitrary-alignment support errors on the upper semicircle control ALL
normals of two caps. Both horizontal endpoints are needed. -/
theorem horizontalError_bound_all {K₀ K₁ : Set Point}
    (h₀ : IsCap K₀ (π / 2)) (h₁ : IsCap K₁ (π / 2)) {a R : ℝ}
    (hupper : ∀ t ∈ Icc (0 : ℝ) π, |horizontalError K₀ K₁ a t| ≤ R) (t : ℝ) :
    |horizontalError K₀ K₁ a t| ≤ R := by
  rcases le_or_gt 0 (sin t) with hs | hs
  · obtain ⟨s, hsi, hu, hc⟩ := upper_normal_representative t hs
    have he : horizontalError K₀ K₁ a s = horizontalError K₀ K₁ a t := by
      simp only [horizontalError, supp, hu, hc]
    exact he ▸ hupper s hsi
  rcases le_or_gt 0 (cos t) with hc | hc
  · have he : horizontalError K₀ K₁ a t = horizontalError K₀ K₁ a 0 * cos t := by
      simp only [horizontalError, cap_lower_right_support h₀ hs.le hc,
        cap_lower_right_support h₁ hs.le hc, cos_zero]
      ring
    rw [he, abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one t)).trans
      (hupper 0 ⟨le_rfl, pi_pos.le⟩)
  · have he : horizontalError K₀ K₁ a t = -horizontalError K₀ K₁ a π * cos t := by
      simp only [horizontalError, cap_lower_left_support h₀ hs.le hc.le,
        cap_lower_left_support h₁ hs.le hc.le, cos_pi]
      ring
    rw [he, abs_mul, abs_neg]
    exact (mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one t)).trans
      (hupper π ⟨pi_pos.le, le_rfl⟩)

/-- Upper support error at ANY chosen translation gives the Euclidean cap bound. -/
theorem cap_close_of_horizontalError {K₀ K₁ : Set Point}
    (h₀ : IsCap K₀ (π / 2)) (h₁ : IsCap K₁ (π / 2)) {a R : ℝ}
    (hupper : ∀ t ∈ Icc (0 : ℝ) π, |horizontalError K₀ K₁ a t| ≤ R) :
    EuclideanClose R K₁ (horizontalReference K₀ a) := by
  apply euclideanClose_of_support_bound h₁.2.1
    (nef_isConvexBody_translate h₀.2.1 (a, 0))
    ((abs_nonneg _).trans (hupper 0 ⟨le_rfl, pi_pos.le⟩))
  intro t
  rw [← horizontalError_eq_support h₀.2.1]
  exact horizontalError_bound_all h₀ h₁ hupper t

/-- The geometric adapter for the centered analytic estimate. It does not yet
prove the sec(phi) analytic estimate; that is a separate reconstruction result. -/
theorem cap_close_of_centered_support {K₀ K₁ : Set Point}
    (h₀ : IsCap K₀ (π / 2)) (h₁ : IsCap K₁ (π / 2)) {R : ℝ}
    (hupper : ∀ t ∈ Icc (0 : ℝ) π, |centeredCapDifference K₀ K₁ t| ≤ R) :
    EuclideanClose R K₁ (centeredReference K₀ K₁) := by
  apply cap_close_of_horizontalError h₀ h₁
  intro t ht
  rw [← centeredCapDifference_eq_error]
  exact hupper t ht

/-- Midpoint/top normalization of the ORIGINAL set, not of a replacement sofa. -/
def midpointNormalizedSofa (P : GerverParams) (S : Set Point) : Set Point :=
  Rigid.translate (horizontalMidpoint (gerverSofa P) - horizontalMidpoint S,
    1 - supp S (π / 2)) '' S

/-- The normalization preserves the original set's area. -/
theorem area_midpointNormalizedSofa (P : GerverParams) (S : Set Point) :
    area (midpointNormalizedSofa P S) = area S := Rigid.area_image _ _

/-- Hence it also preserves the sofa-area deficit. -/
theorem deficit_midpointNormalizedSofa (P : GerverParams) (S : Set Point) :
    sofaDeficit P (midpointNormalizedSofa P S) = sofaDeficit P S := by
  unfold sofaDeficit
  rw [area_midpointNormalizedSofa]

end MovingSofaQuantitative
