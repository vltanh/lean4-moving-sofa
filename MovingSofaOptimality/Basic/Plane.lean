module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Plane geometry

The plane `ℝ²` is represented by `ℝ × ℝ`. This file defines the orthonormal frame
`u_t = (cos t, sin t)`, `v_t = (-sin t, cos t)` (Definition `def:frame`), the dot and cross
products, the counterclockwise rotation `R_t` (`def:rotation-map`), lines `l(t, h)` (`def:line`),
the four kinds of half-planes `H_±(t, h)`, `H_±°(t, h)` (`def:half-plane`), and the area `|X|`
(`def:area`).

Angles are real numbers; the paper's circle `S¹ = ℝ / 2πℤ` is only ever used through
representatives, so every function of an angle below is `2π`-periodic where the paper's is.

The lemmas are grouped as follows: the algebra of the dot and cross products; identities of the
frame `(u_t, v_t)`, in particular at the angles `0, π/2, π, 3π/2` and in a rotated frame;
rotations; continuity and bounds; lines and half-planes; derivatives; the invariance of the area
under rotations and translations.
-/

@[expose] public section

open Real

namespace MovingSofaOptimality

/-! ### Definitions -/

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

/-- The length `𝓗¹(X ∩ l(t, c))` of the part of `X` on the line `l(t, c)` (Definition 2.1.11
restricted to subsets of a line, which is the only way the paper uses `𝓗¹`): the Lebesgue measure
of the parameters `s` with `c u_t + s v_t ∈ X`. -/
noncomputable def lineLength (t c : ℝ) (X : Set (ℝ × ℝ)) : ℝ :=
  (MeasureTheory.volume {s : ℝ | c • uvec t + s • vvec t ∈ X}).toReal

/-- The Euclidean norm of a vector of the plane. -/
noncomputable def norm2 (p : ℝ × ℝ) : ℝ := Real.sqrt (dot p p)

/-- Say that `p₁` is further than `p₂` in the direction of `v` (`def:further-in-direction`). -/
def IsFurther (p₁ p₂ v : ℝ × ℝ) : Prop := dot p₂ v ≤ dot p₁ v

/-- Say that `p₁` is strictly further than `p₂` in the direction of `v`
(`def:further-in-direction`). -/
def IsStrictlyFurther (p₁ p₂ v : ℝ × ℝ) : Prop := dot p₂ v < dot p₁ v

/-! ### The dot and cross products -/

@[simp] lemma uvec_fst (t : ℝ) : (uvec t).1 = cos t := rfl
@[simp] lemma uvec_snd (t : ℝ) : (uvec t).2 = sin t := rfl
@[simp] lemma vvec_fst (t : ℝ) : (vvec t).1 = -sin t := rfl
@[simp] lemma vvec_snd (t : ℝ) : (vvec t).2 = cos t := rfl

lemma dot_mk (p : ℝ × ℝ) (a b : ℝ) : dot p (a, b) = p.1 * a + p.2 * b := rfl

lemma dot_add_left (p q r : ℝ × ℝ) : dot (p + q) r = dot p r + dot q r := by
  simp only [dot, Prod.fst_add, Prod.snd_add]; ring

lemma dot_add_right (p q r : ℝ × ℝ) : dot p (q + r) = dot p q + dot p r := by
  simp only [dot, Prod.fst_add, Prod.snd_add]; ring

lemma dot_sub_left (p q r : ℝ × ℝ) : dot (p - q) r = dot p r - dot q r := by
  simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring

lemma dot_sub_right (p q r : ℝ × ℝ) : dot p (q - r) = dot p q - dot p r := by
  simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring

lemma dot_smul_left (a : ℝ) (p q : ℝ × ℝ) : dot (a • p) q = a * dot p q := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

lemma dot_smul_right (a : ℝ) (p q : ℝ × ℝ) : dot p (a • q) = a * dot p q := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

lemma dot_neg_left (p q : ℝ × ℝ) : dot (-p) q = -dot p q := by
  simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring

lemma dot_neg_right (p q : ℝ × ℝ) : dot p (-q) = -dot p q := by
  simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring

@[simp] lemma dot_zero_left (p : ℝ × ℝ) : dot 0 p = 0 := by simp [dot]
@[simp] lemma dot_zero_right (p : ℝ × ℝ) : dot p 0 = 0 := by simp [dot]

lemma cross_anticomm (p q : ℝ × ℝ) : cross p q = -cross q p := by unfold cross; ring

@[simp] lemma cross_self (p : ℝ × ℝ) : cross p p = 0 := by unfold cross; ring

lemma cross_add_left (p q r : ℝ × ℝ) : cross (p + q) r = cross p r + cross q r := by
  simp only [cross, Prod.fst_add, Prod.snd_add]; ring

lemma cross_add_right (p q r : ℝ × ℝ) : cross p (q + r) = cross p q + cross p r := by
  simp only [cross, Prod.fst_add, Prod.snd_add]; ring

lemma cross_smul_left (a : ℝ) (p q : ℝ × ℝ) : cross (a • p) q = a * cross p q := by
  simp only [cross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

lemma cross_smul_right (a : ℝ) (p q : ℝ × ℝ) : cross p (a • q) = a * cross p q := by
  simp only [cross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-! ### The frame `(u_t, v_t)` -/

@[simp] lemma dot_uvec_self (t : ℝ) : dot (uvec t) (uvec t) = 1 := by
  unfold dot uvec; linear_combination cos_sq_add_sin_sq t

@[simp] lemma dot_vvec_self (t : ℝ) : dot (vvec t) (vvec t) = 1 := by
  unfold dot vvec; linear_combination sin_sq_add_cos_sq t

@[simp] lemma dot_uvec_vvec (t : ℝ) : dot (uvec t) (vvec t) = 0 := by
  simp only [dot, uvec, vvec]; ring

@[simp] lemma dot_vvec_uvec (t : ℝ) : dot (vvec t) (uvec t) = 0 := by
  simp only [dot, uvec, vvec]; ring

/-- `u_s · u_t = cos (s - t)`. -/
lemma dot_uvec_uvec (s t : ℝ) : dot (uvec s) (uvec t) = cos (s - t) := by
  unfold dot uvec; rw [cos_sub]

/-- `v_s · v_t = cos (s - t)`. -/
lemma dot_vvec_vvec (s t : ℝ) : dot (vvec s) (vvec t) = cos (s - t) := by
  unfold dot vvec; rw [cos_sub]; ring

/-- `u_s · v_t = sin (s - t)`. -/
lemma dot_uvec_vvec' (s t : ℝ) : dot (uvec s) (vvec t) = sin (s - t) := by
  unfold dot uvec vvec; rw [sin_sub]; ring

/-- `v_s · u_t = sin (t - s)`. -/
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

/-- Every vector decomposes in the frame `(u_t, v_t)`: `p = (p · u_t) u_t + (p · v_t) v_t`. -/
lemma eq_dot_uvec_smul_add (p : ℝ × ℝ) (t : ℝ) :
    p = dot p (uvec t) • uvec t + dot p (vvec t) • vvec t := by
  have h := sin_sq_add_cos_sq t
  ext
  · simp only [dot, uvec, vvec, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    linear_combination (-p.1) * h
  · simp only [dot, uvec, vvec, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    linear_combination (-p.2) * h

/-- A point is determined by its coordinates in the frame `(u_t, v_t)`. -/
lemma eq_of_dot_frame {p q : ℝ × ℝ} {t : ℝ} (h1 : dot p (uvec t) = dot q (uvec t))
    (h2 : dot p (vvec t) = dot q (vvec t)) : p = q := by
  rw [eq_dot_uvec_smul_add p t, eq_dot_uvec_smul_add q t, h1, h2]

/-- `v_b` in the frame `(u_a, v_a)`. -/
lemma vvec_eq_frame (a b : ℝ) : vvec b = -sin (b - a) • uvec a + cos (b - a) • vvec a := by
  conv_lhs => rw [show b = (b - a) + a by ring]
  ext <;> simp only [uvec, vvec, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, sin_add, cos_add] <;> ring

/-! ### The frame at the coordinate axes -/

lemma uvec_zero : uvec 0 = (1, 0) := by simp [uvec]

lemma uvec_pi_div_two : uvec (π / 2) = (0, 1) := by simp [uvec]

lemma uvec_pi : uvec π = (-1, 0) := by simp [uvec]

lemma uvec_three_pi_div_two : uvec (3 * π / 2) = (0, -1) := by
  rw [show 3 * π / 2 = π / 2 + π by ring, uvec_add_pi, uvec_pi_div_two]; simp

lemma vvec_zero : vvec 0 = (0, 1) := by simp [vvec]

lemma vvec_pi_div_two : vvec (π / 2) = (-1, 0) := by simp [vvec]

lemma vvec_three_pi_div_two : vvec (3 * π / 2) = (1, 0) := by
  rw [show 3 * π / 2 = π / 2 + π by ring, vvec_add_pi, vvec_pi_div_two]; simp

lemma dot_uvec_zero (p : ℝ × ℝ) : dot p (uvec 0) = p.1 := by simp [dot, uvec]

lemma dot_uvec_pi_div_two (p : ℝ × ℝ) : dot p (uvec (π / 2)) = p.2 := by simp [dot, uvec]

lemma dot_uvec_pi (p : ℝ × ℝ) : dot p (uvec π) = -p.1 := by simp [dot, uvec_pi]

lemma dot_uvec_add_pi (p : ℝ × ℝ) (t : ℝ) : dot p (uvec (t + π)) = -dot p (uvec t) := by
  rw [uvec_add_pi, dot_neg_right]

lemma dot_uvec_three_pi_div_two (p : ℝ × ℝ) : dot p (uvec (3 * π / 2)) = -p.2 := by
  rw [show 3 * π / 2 = π / 2 + π by ring, dot_uvec_add_pi, dot_uvec_pi_div_two]

/-! ### Coordinates in a rotated frame -/

/-- The frame identity `p · u_s = cos (s - t) (p · u_t) + sin (s - t) (p · v_t)`. -/
lemma dot_uvec_eq_cos_add_sin (p : ℝ × ℝ) (s t : ℝ) :
    dot p (uvec s) = cos (s - t) * dot p (uvec t) + sin (s - t) * dot p (vvec t) := by
  conv_lhs => rw [show s = (s - t) + t by ring]
  simp only [dot, uvec, vvec, cos_add, sin_add]
  ring

/-- `sin (b - a) (p · u_s) = sin (b - s) (p · u_a) + sin (s - a) (p · u_b)`: the coordinate of `p`
in the direction `u_s` is determined by its coordinates in the directions `u_a` and `u_b`. -/
lemma dot_uvec_comb (p : ℝ × ℝ) (a b s : ℝ) :
    sin (b - a) * dot p (uvec s) =
      sin (b - s) * dot p (uvec a) + sin (s - a) * dot p (uvec b) := by
  simp only [dot, uvec, sin_sub]
  ring

/-- A vector orthogonal to `u_a` is a multiple of `v_a`. -/
lemma eq_smul_vvec_of_dot_uvec_eq_zero {w : ℝ × ℝ} {a : ℝ} (h : dot w (uvec a) = 0) :
    w = dot w (vvec a) • vvec a := by
  simpa [h] using eq_dot_uvec_smul_add w a

/-- Two points on the same line `l(t, h)` differ by a multiple of `v_t`. -/
lemma sub_eq_smul_vvec {p q : ℝ × ℝ} {t : ℝ} (h : dot p (uvec t) = dot q (uvec t)) :
    q - p = dot (q - p) (vvec t) • vvec t :=
  eq_smul_vvec_of_dot_uvec_eq_zero (by rw [dot_sub_left, h, sub_self])

/-- Two vectors with the same dot products against `u_a` and `u_b`, where `sin (b - a) ≠ 0`, are
equal. -/
lemma eq_of_dot_uvec_eq {p q : ℝ × ℝ} {a b : ℝ} (hab : sin (b - a) ≠ 0)
    (ha : dot p (uvec a) = dot q (uvec a)) (hb : dot p (uvec b) = dot q (uvec b)) : p = q := by
  -- `p - q` is orthogonal to `u_a`, so it is a multiple `c v_a`; and `c sin (b - a) = 0`
  have hw := eq_smul_vvec_of_dot_uvec_eq_zero (show dot (p - q) (uvec a) = 0 by
    rw [dot_sub_left, ha, sub_self])
  have hb' : dot (p - q) (uvec b) = 0 := by rw [dot_sub_left, hb, sub_self]
  rw [hw, dot_smul_left, dot_vvec_uvec'] at hb'
  rw [(mul_eq_zero.1 hb').resolve_right hab, zero_smul] at hw
  exact sub_eq_zero.1 hw

/-! ### Rotations -/

@[simp] lemma rot_zero (p : ℝ × ℝ) : rot 0 p = p := by simp [rot]

lemma rot_add (s t : ℝ) (p : ℝ × ℝ) : rot (s + t) p = rot s (rot t p) := by
  ext <;> simp only [rot, cos_add, sin_add] <;> ring

lemma rot_uvec (s t : ℝ) : rot s (uvec t) = uvec (t + s) := by
  ext <;> simp only [rot, uvec, cos_add, sin_add] <;> ring

lemma rot_vvec (s t : ℝ) : rot s (vvec t) = vvec (t + s) := by
  ext <;> simp only [rot, vvec, cos_add, sin_add] <;> ring

lemma rot_add_vec (t : ℝ) (p q : ℝ × ℝ) : rot t (p + q) = rot t p + rot t q := by
  ext <;> simp [rot] <;> ring

lemma rot_smul (t a : ℝ) (p : ℝ × ℝ) : rot t (a • p) = a • rot t p := by
  ext <;> simp [rot] <;> ring

lemma rot_neg_rot (t : ℝ) (p : ℝ × ℝ) : rot (-t) (rot t p) = p := by
  rw [← rot_add]; simp

lemma rot_rot_neg (t : ℝ) (p : ℝ × ℝ) : rot t (rot (-t) p) = p := by
  rw [← rot_add]; simp

/-- The rotation `R_t` is injective. -/
lemma rot_injective (t : ℝ) : Function.Injective (rot t) :=
  Function.LeftInverse.injective (rot_neg_rot t)

/-- `R_t (a, b) = a u_t + b v_t`. -/
lemma rot_pair (t a b : ℝ) : rot t (a, b) = a • uvec t + b • vvec t := by
  ext <;> simp [rot, uvec, vvec] <;> ring

/-- A point is `R_t` of its coordinates in the frame `(u_t, v_t)`. -/
lemma rot_frame_coords (t : ℝ) (q : ℝ × ℝ) : rot t (dot q (uvec t), dot q (vvec t)) = q := by
  rw [rot_pair]
  exact (eq_dot_uvec_smul_add q t).symm

lemma dot_rot_uvec_eq_fst (t : ℝ) (p : ℝ × ℝ) : dot (rot t p) (uvec t) = p.1 := by
  simp only [dot, rot, uvec]; linear_combination p.1 * sin_sq_add_cos_sq t

lemma dot_rot_vvec_eq_snd (t : ℝ) (p : ℝ × ℝ) : dot (rot t p) (vvec t) = p.2 := by
  simp only [dot, rot, vvec]; linear_combination p.2 * sin_sq_add_cos_sq t

/-! ### Continuity and norms -/

lemma continuous_uvec : Continuous uvec := by unfold uvec; fun_prop

lemma continuous_vvec : Continuous vvec := by unfold vvec; fun_prop

lemma continuous_rot (t : ℝ) : Continuous (rot t) := by unfold rot; fun_prop

/-- `p ↦ p · v` is continuous. -/
lemma continuous_dot (v : ℝ × ℝ) : Continuous fun p : ℝ × ℝ => dot p v := by
  unfold dot; fun_prop

/-- The dot product is jointly continuous. -/
lemma continuous_dot_pair : Continuous fun x : (ℝ × ℝ) × (ℝ × ℝ) => dot x.1 x.2 := by
  unfold dot; fun_prop

lemma continuousOn_dot {p : ℝ → ℝ × ℝ} {S : Set ℝ} (hp : ContinuousOn p S) (w : ℝ × ℝ) :
    ContinuousOn (fun t => dot (p t) w) S :=
  (continuous_dot w).comp_continuousOn hp

lemma continuous_dot_uvec (q : ℝ × ℝ) : Continuous (fun r => dot q (uvec r)) :=
  continuous_dot_pair.comp (continuous_const.prodMk continuous_uvec)

lemma continuousOn_cross {f g : ℝ → ℝ × ℝ} {S : Set ℝ} (hf : ContinuousOn f S)
    (hg : ContinuousOn g S) : ContinuousOn (fun t => cross (f t) (g t)) S := by
  unfold cross; fun_prop

/-- `t ↦ u_t` is `1`-Lipschitz (for the sup norm of `ℝ × ℝ`). -/
lemma lipschitz_uvec : LipschitzWith 1 uvec := by
  show LipschitzWith 1 fun x => (cos x, sin x)
  simpa using Real.lipschitzWith_cos.prodMk Real.lipschitzWith_sin

/-- `t ↦ v_t` is `1`-Lipschitz (for the sup norm of `ℝ × ℝ`). -/
lemma lipschitz_vvec : LipschitzWith 1 vvec := by
  show LipschitzWith 1 fun x => (-sin x, cos x)
  simpa using Real.lipschitzWith_sin.neg.prodMk Real.lipschitzWith_cos

/-- `‖u_t‖ ≤ 1` (for the sup norm of `ℝ × ℝ`). -/
lemma norm_uvec_le (t : ℝ) : ‖uvec t‖ ≤ 1 := by
  simp [Prod.norm_def, uvec, abs_cos_le_one, abs_sin_le_one]

/-- `‖v_t‖ ≤ 1` (for the sup norm of `ℝ × ℝ`). -/
lemma norm_vvec_le (t : ℝ) : ‖vvec t‖ ≤ 1 := by
  simp [Prod.norm_def, vvec, abs_cos_le_one, abs_sin_le_one]

/-- `|p · q| ≤ 2 ‖p‖ ‖q‖` for the sup norm of `ℝ × ℝ`. -/
lemma abs_dot_le (p q : ℝ × ℝ) : |dot p q| ≤ 2 * ‖p‖ * ‖q‖ := by
  have h1 : |p.1| ≤ ‖p‖ := norm_fst_le p
  have h2 : |p.2| ≤ ‖p‖ := norm_snd_le p
  have h3 : |q.1| ≤ ‖q‖ := norm_fst_le q
  have h4 : |q.2| ≤ ‖q‖ := norm_snd_le q
  calc |dot p q| ≤ |p.1| * |q.1| + |p.2| * |q.2| := by
        rw [dot, ← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ ‖p‖ * ‖q‖ + ‖p‖ * ‖q‖ := by gcongr
    _ = 2 * ‖p‖ * ‖q‖ := by ring

/-- `|p · u_t| ≤ |p.1| + |p.2|`. -/
lemma abs_dot_uvec_le (p : ℝ × ℝ) (t : ℝ) : |dot p (uvec t)| ≤ |p.1| + |p.2| := by
  calc |dot p (uvec t)| ≤ |p.1| * |cos t| + |p.2| * |sin t| := by
        rw [dot, ← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |p.1| * 1 + |p.2| * 1 := by gcongr <;> simp [abs_cos_le_one, abs_sin_le_one]
    _ = |p.1| + |p.2| := by ring

/-- `|p · u_s - q · u_s| ≤ 2 dist(p, q)`. -/
lemma abs_dot_uvec_sub_le (p q : ℝ × ℝ) (s : ℝ) :
    |dot p (uvec s) - dot q (uvec s)| ≤ 2 * dist p q := by
  rw [← dot_sub_left]
  refine (abs_dot_uvec_le _ s).trans ?_
  have h1 : |(p - q).1| ≤ dist p q := by simpa [dist_eq_norm] using norm_fst_le (p - q)
  have h2 : |(p - q).2| ≤ dist p q := by simpa [dist_eq_norm] using norm_snd_le (p - q)
  linarith

/-! ### Lines and half-planes -/

/-- `p ↦ p · v` is linear. -/
lemma isLinearMap_dot (v : ℝ × ℝ) : IsLinearMap ℝ fun p : ℝ × ℝ => dot p v :=
  ⟨fun p q => dot_add_left p q v, fun a p => dot_smul_left a p v⟩

/-- The dot product `p ↦ p · w` with a fixed vector, as a continuous linear map. -/
noncomputable def dotCLM (w : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  w.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + w.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

lemma dotCLM_apply (w p : ℝ × ℝ) : dotCLM w p = dot p w := by
  simp [dotCLM, dot]; ring

lemma isClosed_line (t h : ℝ) : IsClosed (line t h) :=
  isClosed_eq (continuous_dot _) continuous_const

lemma convex_line (t h : ℝ) : Convex ℝ (line t h) :=
  convex_hyperplane (isLinearMap_dot _) h

lemma isClosed_halfMinus (t h : ℝ) : IsClosed (halfMinus t h) :=
  isClosed_le (continuous_dot _) continuous_const

lemma isOpen_halfMinusOpen (t h : ℝ) : IsOpen (halfMinusOpen t h) :=
  isOpen_lt (continuous_dot _) continuous_const

lemma convex_halfMinus (t h : ℝ) : Convex ℝ (halfMinus t h) :=
  convex_halfSpace_le (isLinearMap_dot _) h

lemma isClosed_halfPlus (t h : ℝ) : IsClosed (halfPlus t h) :=
  isClosed_le continuous_const (continuous_dot _)

lemma convex_halfPlus (t h : ℝ) : Convex ℝ (halfPlus t h) :=
  convex_halfSpace_ge (isLinearMap_dot _) h

/-! ### Derivatives -/

/-- `d/dt u_t = v_t`. -/
lemma hasDerivAt_uvec (t : ℝ) : HasDerivAt uvec (vvec t) t :=
  (hasDerivAt_cos t).prodMk (hasDerivAt_sin t)

/-- `d/dt v_t = -u_t`. -/
lemma hasDerivAt_vvec (t : ℝ) : HasDerivAt vvec (-uvec t) t := by
  have e : -uvec t = (-cos t, -sin t) := by ext <;> simp [uvec]
  rw [e]
  exact (hasDerivAt_sin t).neg.prodMk (hasDerivAt_cos t)

lemma hasDerivAt_fst {p : ℝ → ℝ × ℝ} {p' : ℝ × ℝ} {t : ℝ} (hp : HasDerivAt p p' t) :
    HasDerivAt (fun t => (p t).1) p'.1 t :=
  HasFDerivAt.comp_hasDerivAt t (hasFDerivAt_fst (𝕜 := ℝ) (p := p t)) hp

lemma hasDerivAt_snd {p : ℝ → ℝ × ℝ} {p' : ℝ × ℝ} {t : ℝ} (hp : HasDerivAt p p' t) :
    HasDerivAt (fun t => (p t).2) p'.2 t :=
  HasFDerivAt.comp_hasDerivAt t (hasFDerivAt_snd (𝕜 := ℝ) (p := p t)) hp

/-- The product rule for the dot product, within a set. -/
lemma hasDerivWithinAt_dot' {f g : ℝ → ℝ × ℝ} {f' g' : ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' s t) (hg : HasDerivWithinAt g g' s t) :
    HasDerivWithinAt (fun x => dot (f x) (g x)) (dot f' (g t) + dot (f t) g') s t := by
  have h1 : HasDerivWithinAt (fun y => (f y).1) f'.1 s t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt t hf
  have h2 : HasDerivWithinAt (fun y => (f y).2) f'.2 s t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt t hf
  have h3 : HasDerivWithinAt (fun y => (g y).1) g'.1 s t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt t hg
  have h4 : HasDerivWithinAt (fun y => (g y).2) g'.2 s t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt t hg
  refine ((h1.mul h3).add (h2.mul h4)).congr_deriv ?_
  simp only [dot]; ring

/-- The product rule for the dot product. -/
lemma hasDerivAt_dot' {f g : ℝ → ℝ × ℝ} {f' g' : ℝ × ℝ} {t : ℝ} (hf : HasDerivAt f f' t)
    (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => dot (f s) (g s)) (dot f' (g t) + dot (f t) g') t :=
  hasDerivWithinAt_univ.1 (hasDerivWithinAt_dot' hf.hasDerivWithinAt hg.hasDerivWithinAt)

/-- The derivative of `y ↦ f(y) · w`, within a set. -/
lemma hasDerivWithinAt_dot {f : ℝ → ℝ × ℝ} {f' : ℝ × ℝ} {s : Set ℝ} {x : ℝ}
    (hf : HasDerivWithinAt f f' s x) (w : ℝ × ℝ) :
    HasDerivWithinAt (fun y => dot (f y) w) (dot f' w) s x :=
  (hasDerivWithinAt_dot' hf (hasDerivWithinAt_const x s w)).congr_deriv (by simp [dot])

/-- The derivative of `t ↦ p(t) · w` is `p'(t) · w`. -/
lemma hasDerivAt_dot {p : ℝ → ℝ × ℝ} {p' : ℝ × ℝ} {t : ℝ} (hp : HasDerivAt p p' t)
    (w : ℝ × ℝ) : HasDerivAt (fun t => dot (p t) w) (dot p' w) t := by
  unfold dot
  exact ((hasDerivAt_fst hp).mul_const w.1).add ((hasDerivAt_snd hp).mul_const w.2)

/-- The derivative of `r ↦ q · u_r` is `q · v_r`. -/
lemma hasDerivAt_dot_uvec (q : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun r => dot q (uvec r)) (dot q (vvec t)) t := by
  have := ((hasDerivAt_cos t).const_mul q.1).add ((hasDerivAt_sin t).const_mul q.2)
  convert this using 1
  · ext r; simp [dot, uvec]
  · simp [dot, vvec]

/-- The derivative of `r ↦ q · v_r` is `-q · u_r`. -/
lemma hasDerivAt_dot_vvec (q : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun r => dot q (vvec r)) (-dot q (uvec t)) t := by
  have := ((hasDerivAt_sin t).neg.const_mul q.1).add ((hasDerivAt_cos t).const_mul q.2)
  convert this using 1
  · ext r; simp [dot, vvec]
  · simp [dot, uvec]; ring

/-- The derivative of `s ↦ f(s) × g(s)`. -/
lemma hasDerivAt_cross {f g : ℝ → ℝ × ℝ} {f' g' : ℝ × ℝ} {t : ℝ} (hf : HasDerivAt f f' t)
    (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => cross (f s) (g s)) (cross f' (g t) + cross (f t) g') t := by
  have := ((hasDerivAt_fst hf).fun_mul (hasDerivAt_snd hg)).fun_sub
    ((hasDerivAt_snd hf).fun_mul (hasDerivAt_fst hg))
  convert this using 1 <;> simp only [cross]
  ring

/-- The derivative of `p s² + q s + r`. -/
lemma hasDerivAt_quad {f : ℝ → ℝ} {t d : ℝ} (p q r : ℝ)
    (hf : ∀ s, f s = p * s ^ 2 + q * s + r) (hd : d = 2 * p * t + q) :
    HasDerivAt f d t := by
  have := (((hasDerivAt_pow 2 t).const_mul p).add ((hasDerivAt_id t).const_mul q)).add_const r
  rw [show f = fun s => p * s ^ 2 + q * s + r from funext hf, hd]
  exact this.congr_deriv (by simp; ring)

/-- A continuous function with nonnegative right derivatives on `[a, b)` satisfies
`f a ≤ f b`. -/
lemma le_of_right_deriv_nonneg {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ∀ x ∈ Set.Ico a b, HasDerivWithinAt f (f' x) (Set.Ici x) x)
    (h : ∀ x ∈ Set.Ico a b, 0 ≤ f' x) : f a ≤ f b :=
  image_le_of_deriv_right_le_deriv_boundary (f' := fun _ => 0) continuousOn_const
    (fun x _ => hasDerivWithinAt_const x _ (f a)) le_rfl hf hf' h ⟨hab, le_rfl⟩

/-- A continuous function with nonpositive right derivatives on `[a, b)` satisfies
`f b ≤ f a`. -/
lemma le_of_right_deriv_nonpos {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ∀ x ∈ Set.Ico a b, HasDerivWithinAt f (f' x) (Set.Ici x) x)
    (h : ∀ x ∈ Set.Ico a b, f' x ≤ 0) : f b ≤ f a :=
  image_le_of_deriv_right_le_deriv_boundary hf hf' (B := fun _ => f a) le_rfl continuousOn_const
    (fun x _ => hasDerivWithinAt_const x _ (f a)) h ⟨hab, le_rfl⟩

/-- `tan (δ/2) sin δ = 1 - cos δ` when `cos (δ/2) ≠ 0`. -/
lemma tan_half_mul_sin {δ : ℝ} (h : cos (δ / 2) ≠ 0) : tan (δ / 2) * sin δ = 1 - cos δ := by
  obtain ⟨α, rfl⟩ : ∃ α, δ = 2 * α := ⟨δ / 2, by ring⟩
  rw [mul_div_cancel_left₀ _ two_ne_zero] at h ⊢
  rw [tan_eq_sin_div_cos, sin_two_mul, cos_two_mul]
  field_simp
  linear_combination 2 * sin_sq_add_cos_sq α

/-! ### Area -/

/-- A linear map of the plane with determinant `±1` preserves the Lebesgue measure. -/
lemma volume_preimage_linearMap {f : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ} (hf : |LinearMap.det f| = 1)
    (A : Set (ℝ × ℝ)) : MeasureTheory.volume (f ⁻¹' A) = MeasureTheory.volume A := by
  have : MeasureTheory.Measure.IsAddHaarMeasure (MeasureTheory.volume : MeasureTheory.Measure
    (ℝ × ℝ)) := MeasureTheory.Measure.prod.instIsAddHaarMeasure _ _
  rw [MeasureTheory.Measure.addHaar_preimage_linearMap _ (fun h => by simp [h] at hf), abs_inv,
    hf]
  simp

/-- The rotation `R_t` as a linear map. -/
noncomputable def rotLM (t : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ where
  toFun := rot t
  map_add' := rot_add_vec t
  map_smul' := rot_smul t

/-- `det R_t = 1`. -/
lemma det_rotLM (t : ℝ) : LinearMap.det (rotLM t) = 1 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, rotLM, rot]
  linear_combination cos_sq_add_sin_sq t

/-- Rotations preserve the Lebesgue measure. -/
lemma volume_preimage_rot (t : ℝ) (A : Set (ℝ × ℝ)) :
    MeasureTheory.volume (rot t ⁻¹' A) = MeasureTheory.volume A :=
  volume_preimage_linearMap (f := rotLM t) (by rw [det_rotLM, abs_one]) A

/-- Rotations preserve the Lebesgue measure. -/
lemma volume_image_rot (t : ℝ) (A : Set (ℝ × ℝ)) :
    MeasureTheory.volume (rot t '' A) = MeasureTheory.volume A := by
  rw [Set.image_eq_preimage_of_inverse (rot_neg_rot t) (rot_rot_neg t), volume_preimage_rot]

/-- Rotations preserve the area. -/
lemma area_image_rot (t : ℝ) (A : Set (ℝ × ℝ)) : area (rot t '' A) = area A := by
  rw [area, area, volume_image_rot]

/-- Translations preserve the Lebesgue measure. -/
lemma volume_preimage_add (A : Set (ℝ × ℝ)) (v : ℝ × ℝ) :
    MeasureTheory.volume ((fun p => p + v) ⁻¹' A) = MeasureTheory.volume A := by
  have : MeasureTheory.Measure.IsAddHaarMeasure (MeasureTheory.volume : MeasureTheory.Measure
    (ℝ × ℝ)) := MeasureTheory.Measure.prod.instIsAddHaarMeasure _ _
  exact MeasureTheory.measure_preimage_add_right _ v A

/-- Translations preserve the area. -/
lemma area_image_add (A : Set (ℝ × ℝ)) (v : ℝ × ℝ) : area ((fun p => p + v) '' A) = area A := by
  rw [area, area, Set.image_add_right, volume_preimage_add]

end MovingSofaOptimality
