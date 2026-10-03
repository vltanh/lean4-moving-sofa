module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Convex.Segment

/-!
# Plane geometry

The plane `ℝ²` is represented by `ℝ × ℝ`. This file defines the orthonormal frame
`u_t = (cos t, sin t)`, `v_t = (-sin t, cos t)` (Definition `def:frame`), the dot and cross products,
the counterclockwise rotation `R_t` (`def:rotation-map`), lines `l(t, h)` (`def:line`), the four kinds
of half-planes `H_±(t, h)`, `H_±°(t, h)` (`def:half-plane`), and the area `|X|` (`def:area`).

Angles are real numbers; the paper's circle `S¹ = ℝ / 2πℤ` is only ever used through
representatives, so every function of an angle below is `2π`-periodic where the paper's is.
-/

@[expose] public section

open Real

namespace MovingSofaOptimality

/-- The unit vector `u_t = (cos t, sin t)` (`def:frame`). -/
noncomputable def uvec (t : ℝ) : ℝ × ℝ := (cos t, sin t)

/-- The unit vector `v_t = (-sin t, cos t)` (`def:frame`). -/
noncomputable def vvec (t : ℝ) : ℝ × ℝ := (-sin t, cos t)

/-- The dot product `p · q`. -/
def dot (p q : ℝ × ℝ) : ℝ := p.1 * q.1 + p.2 * q.2

/-- The cross product `p × q = p₁ q₂ - p₂ q₁` (`def:plane-cross-product`). -/
def cross (p q : ℝ × ℝ) : ℝ := p.1 * q.2 - p.2 * q.1

/-- The rotation `R_t` of the plane around the origin by the counterclockwise angle `t`
(`def:rotation-map`). -/
noncomputable def rot (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (cos t * p.1 - sin t * p.2, sin t * p.1 + cos t * p.2)

/-- The line `l(t, h) = {p : p · u_t = h}` with normal angle `t` (`def:line`). -/
def line (t h : ℝ) : Set (ℝ × ℝ) := {p | dot p (uvec t) = h}

/-- The closed half-plane `H₋(t, h) = {p : p · u_t ≤ h}` (`def:half-plane`). -/
def halfMinus (t h : ℝ) : Set (ℝ × ℝ) := {p | dot p (uvec t) ≤ h}

/-- The open half-plane `H₋°(t, h) = {p : p · u_t < h}` (`def:half-plane`). -/
def halfMinusOpen (t h : ℝ) : Set (ℝ × ℝ) := {p | dot p (uvec t) < h}

/-- The closed half-plane `H₊(t, h) = {p : p · u_t ≥ h}` (`def:half-plane`). -/
def halfPlus (t h : ℝ) : Set (ℝ × ℝ) := {p | h ≤ dot p (uvec t)}

/-- The open half-plane `H₊°(t, h) = {p : p · u_t > h}` (`def:half-plane`). -/
def halfPlusOpen (t h : ℝ) : Set (ℝ × ℝ) := {p | h < dot p (uvec t)}

/-- The area `|X|` of a subset of the plane (`def:area`): its Lebesgue measure, as a real number.
It is meaningful for bounded measurable sets, which are the only ones whose area the paper uses. -/
noncomputable def area (X : Set (ℝ × ℝ)) : ℝ := (MeasureTheory.volume X).toReal

/-- The length `𝓗¹(X ∩ l(t, c))` of the part of `X` on the line `l(t, c)` (Definition 2.1.11 restricted
to subsets of a line, which is the only way the paper uses `𝓗¹`): the Lebesgue measure of the
parameters `s` with `c u_t + s v_t ∈ X`. -/
noncomputable def lineLength (t c : ℝ) (X : Set (ℝ × ℝ)) : ℝ :=
  (MeasureTheory.volume {s : ℝ | c • uvec t + s • vvec t ∈ X}).toReal

/-- The Euclidean norm of a vector of the plane. -/
noncomputable def norm2 (p : ℝ × ℝ) : ℝ := Real.sqrt (dot p p)

/-- Say that `p₁` is further than `p₂` in the direction of `v` (`def:further-in-direction`). -/
def IsFurther (p₁ p₂ v : ℝ × ℝ) : Prop := dot p₂ v ≤ dot p₁ v

/-- Say that `p₁` is strictly further than `p₂` in the direction of `v` (`def:further-in-direction`). -/
def IsStrictlyFurther (p₁ p₂ v : ℝ × ℝ) : Prop := dot p₂ v < dot p₁ v

/-! ### Elementary identities -/

@[simp] lemma uvec_fst (t : ℝ) : (uvec t).1 = cos t := rfl
@[simp] lemma uvec_snd (t : ℝ) : (uvec t).2 = sin t := rfl
@[simp] lemma vvec_fst (t : ℝ) : (vvec t).1 = -sin t := rfl
@[simp] lemma vvec_snd (t : ℝ) : (vvec t).2 = cos t := rfl

lemma dot_comm (p q : ℝ × ℝ) : dot p q = dot q p := by unfold dot; ring

lemma dot_add_left (p q r : ℝ × ℝ) : dot (p + q) r = dot p r + dot q r := by
  unfold dot; simp only [Prod.fst_add, Prod.snd_add]; ring

lemma dot_add_right (p q r : ℝ × ℝ) : dot p (q + r) = dot p q + dot p r := by
  unfold dot; simp only [Prod.fst_add, Prod.snd_add]; ring

lemma dot_sub_left (p q r : ℝ × ℝ) : dot (p - q) r = dot p r - dot q r := by
  unfold dot; simp only [Prod.fst_sub, Prod.snd_sub]; ring

lemma dot_sub_right (p q r : ℝ × ℝ) : dot p (q - r) = dot p q - dot p r := by
  unfold dot; simp only [Prod.fst_sub, Prod.snd_sub]; ring

lemma dot_smul_left (a : ℝ) (p q : ℝ × ℝ) : dot (a • p) q = a * dot p q := by
  unfold dot; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

lemma dot_smul_right (a : ℝ) (p q : ℝ × ℝ) : dot p (a • q) = a * dot p q := by
  unfold dot; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

lemma dot_neg_left (p q : ℝ × ℝ) : dot (-p) q = -dot p q := by
  unfold dot; simp only [Prod.fst_neg, Prod.snd_neg]; ring

lemma dot_neg_right (p q : ℝ × ℝ) : dot p (-q) = -dot p q := by
  unfold dot; simp only [Prod.fst_neg, Prod.snd_neg]; ring

@[simp] lemma dot_zero_left (p : ℝ × ℝ) : dot 0 p = 0 := by simp [dot]
@[simp] lemma dot_zero_right (p : ℝ × ℝ) : dot p 0 = 0 := by simp [dot]

lemma cross_anticomm (p q : ℝ × ℝ) : cross p q = -cross q p := by unfold cross; ring

@[simp] lemma cross_self (p : ℝ × ℝ) : cross p p = 0 := by unfold cross; ring

lemma cross_add_left (p q r : ℝ × ℝ) : cross (p + q) r = cross p r + cross q r := by
  unfold cross; simp only [Prod.fst_add, Prod.snd_add]; ring

lemma cross_add_right (p q r : ℝ × ℝ) : cross p (q + r) = cross p q + cross p r := by
  unfold cross; simp only [Prod.fst_add, Prod.snd_add]; ring

lemma cross_smul_left (a : ℝ) (p q : ℝ × ℝ) : cross (a • p) q = a * cross p q := by
  unfold cross; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

lemma cross_smul_right (a : ℝ) (p q : ℝ × ℝ) : cross p (a • q) = a * cross p q := by
  unfold cross; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

@[simp] lemma dot_uvec_self (t : ℝ) : dot (uvec t) (uvec t) = 1 := by
  unfold dot uvec; linear_combination cos_sq_add_sin_sq t

@[simp] lemma dot_vvec_self (t : ℝ) : dot (vvec t) (vvec t) = 1 := by
  unfold dot vvec; linear_combination sin_sq_add_cos_sq t

@[simp] lemma dot_uvec_vvec (t : ℝ) : dot (uvec t) (vvec t) = 0 := by
  simp only [dot, uvec, vvec]; ring

@[simp] lemma dot_vvec_uvec (t : ℝ) : dot (vvec t) (uvec t) = 0 := by
  simp only [dot, uvec, vvec]; ring

lemma dot_uvec_uvec (s t : ℝ) : dot (uvec s) (uvec t) = cos (s - t) := by
  unfold dot uvec; rw [cos_sub]

lemma dot_vvec_vvec (s t : ℝ) : dot (vvec s) (vvec t) = cos (s - t) := by
  unfold dot vvec; rw [cos_sub]; ring

lemma dot_uvec_vvec' (s t : ℝ) : dot (uvec s) (vvec t) = sin (s - t) := by
  unfold dot uvec vvec; rw [sin_sub]; ring

lemma dot_vvec_uvec' (s t : ℝ) : dot (vvec s) (uvec t) = sin (t - s) := by
  unfold dot uvec vvec; rw [sin_sub]; ring

lemma uvec_add_pi_div_two (t : ℝ) : uvec (t + π / 2) = vvec t := by
  simp [uvec, vvec, cos_add_pi_div_two, sin_add_pi_div_two]

lemma vvec_add_pi_div_two (t : ℝ) : vvec (t + π / 2) = -uvec t := by
  ext <;> simp [uvec, vvec, cos_add_pi_div_two, sin_add_pi_div_two]

lemma uvec_add_pi (t : ℝ) : uvec (t + π) = -uvec t := by
  ext <;> simp [uvec, cos_add_pi, sin_add_pi]

lemma vvec_add_pi (t : ℝ) : vvec (t + π) = -vvec t := by
  ext <;> simp [vvec, cos_add_pi, sin_add_pi]

lemma uvec_add_two_pi (t : ℝ) : uvec (t + 2 * π) = uvec t := by
  simp [uvec, cos_add_two_pi, sin_add_two_pi]

lemma vvec_add_two_pi (t : ℝ) : vvec (t + 2 * π) = vvec t := by
  simp [vvec, cos_add_two_pi, sin_add_two_pi]

lemma cross_vvec (p : ℝ × ℝ) (t : ℝ) : cross p (vvec t) = dot p (uvec t) := by
  simp only [cross, dot, uvec, vvec]; ring

lemma cross_uvec (p : ℝ × ℝ) (t : ℝ) : cross p (uvec t) = -dot p (vvec t) := by
  simp only [cross, dot, uvec, vvec]; ring

/-- Every vector decomposes in the frame `(u_t, v_t)`. -/
lemma eq_dot_uvec_smul_add (p : ℝ × ℝ) (t : ℝ) :
    p = dot p (uvec t) • uvec t + dot p (vvec t) • vvec t := by
  have h := sin_sq_add_cos_sq t
  ext
  · simp only [dot, uvec, vvec, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    linear_combination (-p.1) * h
  · simp only [dot, uvec, vvec, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    linear_combination (-p.2) * h

@[simp] lemma rot_zero (p : ℝ × ℝ) : rot 0 p = p := by simp [rot]

lemma rot_add (s t : ℝ) (p : ℝ × ℝ) : rot (s + t) p = rot s (rot t p) := by
  simp only [rot, cos_add, sin_add]; ext <;> simp only <;> ring

lemma rot_uvec (s t : ℝ) : rot s (uvec t) = uvec (t + s) := by
  simp only [rot, uvec, cos_add, sin_add]; ext <;> simp only <;> ring

lemma rot_vvec (s t : ℝ) : rot s (vvec t) = vvec (t + s) := by
  simp only [rot, vvec, cos_add, sin_add]; ext <;> simp only <;> ring

lemma dot_rot_rot (t : ℝ) (p q : ℝ × ℝ) : dot (rot t p) (rot t q) = dot p q := by
  simp only [dot, rot]; linear_combination (p.1 * q.1 + p.2 * q.2) * sin_sq_add_cos_sq t

lemma rot_add_vec (t : ℝ) (p q : ℝ × ℝ) : rot t (p + q) = rot t p + rot t q := by
  simp only [rot, Prod.fst_add, Prod.snd_add]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

lemma rot_smul (t a : ℝ) (p : ℝ × ℝ) : rot t (a • p) = a • rot t p := by
  simp only [rot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ext <;> simp only [Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] <;> ring

lemma rot_neg_rot (t : ℝ) (p : ℝ × ℝ) : rot (-t) (rot t p) = p := by
  rw [← rot_add]; simp

lemma rot_rot_neg (t : ℝ) (p : ℝ × ℝ) : rot t (rot (-t) p) = p := by
  rw [← rot_add]; simp

lemma dot_rot_uvec (s t : ℝ) (p : ℝ × ℝ) : dot (rot s p) (uvec (t + s)) = dot p (uvec t) := by
  rw [← rot_uvec, dot_rot_rot]

end MovingSofaOptimality
