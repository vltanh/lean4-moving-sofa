module

public import MovingSofaStability.IntegralEstimates

/-!
# The four cap residuals and their integrating factor

Uncompiled proof source. The derivative argument is kept explicit rather than
silently using a derivative of a nonsmooth support function everywhere.
The algebraic support-displacement identities hold without smoothness.

The final absolutely-continuous reconstruction and the four Green-kernel
square-integral evaluations are separate proof obligations.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- Residual for the tangent-line term, with an explicit derivative value. -/
def tangentResidual (T : ℝ) (f df : ℝ → ℝ) (t : ℝ) : ℝ :=
  (f T - f t * cos (T - t)) / sin (T - t) - df t

/-- Residual for the outer-corner term. -/
def cornerResidual (f df : ℝ → ℝ) (t : ℝ) : ℝ :=
  f (t + π / 2) - df t

/-- Pin the left support: the translation coefficient is `-f π`. -/
def pinnedDifference (f : ℝ → ℝ) (t : ℝ) : ℝ := f t + f π * cos t

def pinnedDerivative (f df : ℝ → ℝ) (t : ℝ) : ℝ := df t - f π * sin t

@[simp] theorem pinnedDifference_pi (f : ℝ → ℝ) : pinnedDifference f π = 0 := by
  simp [pinnedDifference]

@[simp] theorem pinnedDifference_top (f : ℝ → ℝ) :
    pinnedDifference f (π / 2) = f (π / 2) := by
  simp [pinnedDifference]

theorem hasDerivAt_pinnedDifference {f df : ℝ → ℝ} {t : ℝ}
    (h : HasDerivAt f (df t) t) :
    HasDerivAt (pinnedDifference f) (pinnedDerivative f df t) t := by
  have h2 := h.add ((hasDerivAt_cos t).const_mul (f π))
  have he : pinnedDerivative f df t = df t + f π * -sin t := by
    simp only [pinnedDerivative]; ring
  rw [he]
  exact h2

theorem tangentResidual_add (T : ℝ) (f df g dg : ℝ → ℝ) (t : ℝ) :
    tangentResidual T (fun u => f u + g u) (fun u => df u + dg u) t =
      tangentResidual T f df t + tangentResidual T g dg t := by
  unfold tangentResidual
  ring

theorem tangentResidual_sub (T : ℝ) (f df g dg : ℝ → ℝ) (t : ℝ) :
    tangentResidual T (fun u => f u - g u) (fun u => df u - dg u) t =
      tangentResidual T f df t - tangentResidual T g dg t := by
  unfold tangentResidual
  ring

/-- Horizontal translations lie in the kernel of every tangent residual. -/
theorem tangentResidual_translation (a T t : ℝ) (hs : sin (T - t) ≠ 0) :
    tangentResidual T (fun u => a * cos u) (fun u => -a * sin u) t = 0 := by
  have hc : cos T = cos t * cos (T - t) - sin t * sin (T - t) := by
    rw [← cos_add]
    congr 1
    ring
  unfold tangentResidual
  beta_reduce
  rw [hc]
  field_simp
  ring

@[simp] theorem cornerResidual_translation (a t : ℝ) :
    cornerResidual (fun u => a * cos u) (fun u => -a * sin u) t = 0 := by
  simp only [cornerResidual, cos_add_pi_div_two]
  ring

/-- Pinning removes translation without changing a tangent residual. -/
theorem tangentResidual_pinned (T : ℝ) (f df : ℝ → ℝ) (t : ℝ)
    (hs : sin (T - t) ≠ 0) :
    tangentResidual T (pinnedDifference f) (pinnedDerivative f df) t =
      tangentResidual T f df t := by
  have h := tangentResidual_translation (f π) T t hs
  have he := tangentResidual_add T f df (fun u => f π * cos u)
    (fun u => -f π * sin u) t
  change tangentResidual T (fun u => f u + f π * cos u)
    (fun u => df u - f π * sin u) t = tangentResidual T f df t
  simp only [sub_eq_add_neg, neg_mul] at *
  rw [he, h, add_zero]

@[simp] theorem cornerResidual_pinned (f df : ℝ → ℝ) (t : ℝ) :
    cornerResidual (pinnedDifference f) (pinnedDerivative f df) t =
      cornerResidual f df t := by
  simp only [cornerResidual, pinnedDifference, pinnedDerivative, cos_add_pi_div_two]
  ring

/-- The algebraic residual is the difference of the actual tangent displacements.
No derivative-existence assumption is used here. -/
theorem tangent_displacement_sub {K₀ K₁ : Set (ℝ × ℝ)} {T t : ℝ} (ht : t < T) :
    displacement K₁ (tangentParam K₁ T) t - displacement K₀ (tangentParam K₀ T) t =
      tangentResidual T (fun u => supp K₁ u - supp K₀ u)
        (fun u => dot (vplus K₁ u) (vvec u) - dot (vplus K₀ u) (vvec u)) t := by
  rw [tangent_displacement_formula K₁ ht, tangent_displacement_formula K₀ ht]
  unfold tangentResidual
  ring

theorem outer_displacement_sub (K₀ K₁ : Set (ℝ × ℝ)) (t : ℝ) :
    displacement K₁ (outerCorner K₁) t - displacement K₀ (outerCorner K₀) t =
      cornerResidual (fun u => supp K₁ u - supp K₀ u)
        (fun u => dot (vplus K₁ u) (vvec u) - dot (vplus K₀ u) (vvec u)) t := by
  rw [outer_displacement_formula, outer_displacement_formula]
  unfold cornerResidual
  ring

/-- Explicit integrating factor. The target support `f T` is held constant. -/
def tangentQuotient (T : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (f t - f T * cos (T - t)) / sin (T - t)

/-- The nonzero-error version of the integrating-factor computation used for
uniqueness. It is valid at every point at which the input derivative exists. -/
theorem hasDerivAt_tangentQuotient {f df : ℝ → ℝ} {T t : ℝ}
    (hd : HasDerivAt f (df t) t) (hs : sin (T - t) ≠ 0) :
    HasDerivAt (tangentQuotient T f)
      (-tangentResidual T f df t / sin (T - t)) t := by
  have hu : HasDerivAt (fun s : ℝ => T - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub T
  have hquot := (hd.sub (hu.cos.const_mul (f T))).div hu.sin hs
  convert hquot using 1
  · rfl
  · dsimp only [tangentResidual]
    have hweighted : f T * (sin (T - t) ^ 2 + cos (T - t) ^ 2) = f T := by
      rw [sin_sq_add_cos_sq, mul_one]
    simp only [Pi.sub_apply]
    field_simp
    linear_combination hweighted

/-- The first interval's residual, after fixing the top support. -/
theorem tangentResidual_top {f df : ℝ → ℝ} (h : f (π / 2) = 0) (t : ℝ) :
    tangentResidual (π / 2) f df t = -tan t * f t - df t := by
  simp only [tangentResidual, h, zero_sub, cos_pi_div_two_sub,
    sin_pi_div_two_sub, tan_eq_sin_div_cos]
  ring

/-- The fourth interval's residual, after pinning the left support. -/
theorem tangentResidual_left {f df : ℝ → ℝ} (h : f π = 0) (t : ℝ) :
    tangentResidual π f df t = cos t / sin t * f t - df t := by
  simp only [tangentResidual, h, zero_sub, cos_pi_sub, sin_pi_sub]
  ring

end MovingSofaStability
