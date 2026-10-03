module

public import Mathlib

/-!
# Gerver's four constants are unique

Formal-conjectures defines Gerver's sofa from the solution `(A, B, φ, θ)` of Gerver's system
`ABφθSpec` (Romik 2018, Equations (1)–(4)) on the domain `0 ≤ φ ≤ θ ≤ π/4`, `A, B ≥ 0`. This module
proves that the system has at most one solution (`spec_unique`), by elementary inequalities.
`Spec` is a copy of `ABφθSpec`: `ChallengeDefs`, which defines `ABφθSpec`, uses this result.

The angles determine `A` and `B` (`Spec.coefficients`). Every solution has `0 < φ < θ` and
`φ < 1/20` (`Spec.phi_lt_twentieth`). On that strip the third equation `F`, with `A` and `B`
expressed through the angles, decreases strictly in `φ` and increases in `θ`, while
`H = G + (9/10) F`, with `G` the second equation, decreases in `φ` and strictly in `θ`. So two
solutions have the same `θ`, and then the same `φ`.
-/

@[expose] public section
noncomputable section

open Real Set

namespace MovingSofaBridge

/-- Gerver's four constants `A`, `B`, `φ` and `θ`. -/
structure GerverConstants where
  A : ℝ
  B : ℝ
  φ : ℝ
  θ : ℝ

namespace GerverConstants

/-! ## Monotonicity on an interval from the sign of a derivative -/

section Monotonicity

variable {f f' : ℝ → ℝ} {a b : ℝ}

/-- A function with derivative `f'` on `[a, b]` and `f' ≥ 0` on `(a, b)` is monotone on `[a, b]`. -/
private theorem monotoneOn_Icc_of_hasDerivAt (hd : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Ioo a b, 0 ≤ f' t) : MonotoneOn f (Icc a b) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt) (by rwa [interior_Icc])

/-- A function with derivative `f'` on `[a, b]` and `f' > 0` on `(a, b)` is strictly monotone on
`[a, b]`. -/
private theorem strictMonoOn_Icc_of_hasDerivAt (hd : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Ioo a b, 0 < f' t) : StrictMonoOn f (Icc a b) :=
  strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc a b)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt) (by rwa [interior_Icc])

/-- A function with derivative `f'` on `[a, b]` and `f' ≤ 0` on `(a, b)` is antitone on `[a, b]`. -/
private theorem antitoneOn_Icc_of_hasDerivAt (hd : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Ioo a b, f' t ≤ 0) : AntitoneOn f (Icc a b) :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt) (by rwa [interior_Icc])

/-- A function with derivative `f'` on `[a, b]` and `f' < 0` on `(a, b)` is strictly antitone on
`[a, b]`. -/
private theorem strictAntiOn_Icc_of_hasDerivAt (hd : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Ioo a b, f' t < 0) : StrictAntiOn f (Icc a b) :=
  strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc a b)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt) (by rwa [interior_Icc])

end Monotonicity

/-! ## Trigonometric bounds -/

/-- Signs and orders of the sines and cosines on the domain `0 ≤ φ ≤ θ ≤ π/4`. -/
theorem triangle_trig {φ θ : ℝ} (hφ : 0 ≤ φ) (horder : φ ≤ θ) (hθ : θ ≤ π / 4) :
    0 ≤ sin φ ∧ sin φ ≤ cos φ ∧ 0 < cos φ ∧ cos θ ≤ cos φ ∧
      0 ≤ sin θ ∧ 0 < cos θ ∧ 1 ≤ cos θ + sin θ := by
  have hθ0 := hφ.trans horder
  have hpSin := sin_nonneg_of_nonneg_of_le_pi hφ (by linarith [pi_pos])
  have htSin := sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [pi_pos])
  have hpCos : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have htCos : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hpc : sin φ ≤ cos φ := by
    rw [← sin_pi_div_two_sub]
    exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) (by linarith) (by linarith)
  refine ⟨hpSin, hpc, hpCos, cos_le_cos_of_nonneg_of_le_pi hφ (by linarith [pi_pos]) horder,
    htSin, htCos, ?_⟩
  -- `(cos θ + sin θ)² = 1 + 2 sin θ cos θ ≥ 1`.
  nlinarith [sin_sq_add_cos_sq θ, mul_nonneg htSin htCos.le]

/-- `sin x ≥ 23/48` for `1/2 ≤ x ≤ π/4`, from `sin (1/2) ≥ 1/2 - 1/48`. -/
theorem sin_ge_of_half_le {x : ℝ} (hx : 1 / 2 ≤ x) (hx' : x ≤ π / 4) : (23 / 48 : ℝ) ≤ sin x := by
  have h := sin_ge_sub_cube (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hmono := sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) (by linarith [pi_pos]) hx
  linarith

/-- `0.707 ≤ cos (π/4) ≤ 0.708`. -/
theorem cos_pi_div_four_bounds :
    (707 / 1000 : ℝ) ≤ cos (π / 4) ∧ cos (π / 4) ≤ 708 / 1000 := by
  rw [cos_pi_div_four]
  have hsqrt := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt0 := sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith

/-!
## The reduced equation

Eliminating `B` and then `A` leaves one equation in the angles, `reducedQ φ θ = 0`
(`Spec.reduced_zero`), and expresses `A` and `B` through the angles (`Spec.coefficients`). The
elimination identities are those of Romik's system; compare RuifengCao/sofa-formal,
`Sofa/GerverConst.lean`.
-/

/-- Gerver's system `ABφθSpec` of formal-conjectures: the domain and the four equations. -/
def Spec (A B φ θ : ℝ) : Prop :=
  0 ≤ φ ∧ φ ≤ θ ∧ θ ≤ π / 4 ∧ 0 ≤ A ∧ 0 ≤ B ∧
  A * (θ.cos - φ.cos) - 2 * B * φ.sin
    + (θ - φ - 1) * θ.cos - θ.sin + φ.cos + φ.sin = 0 ∧
  A * (3 * θ.sin + φ.sin) - 2 * B * φ.cos
    + 3 * (θ - φ - 1) * θ.sin + 3 * θ.cos - φ.sin + φ.cos = 0 ∧
  A * φ.cos - (φ.sin + 1 / 2 - φ.cos / 2 + B * φ.sin) = 0 ∧
  (A + π / 2 - φ - θ) - (B - (θ - φ) * (1 + A) / 2 - (θ - φ)^2 / 4) = 0

/-- The constants solve Gerver's system. -/
def Valid (c : GerverConstants) : Prop := Spec c.A c.B c.φ c.θ

/-- The left side of the first equation of Gerver's system. -/
def eq1 (A B φ θ : ℝ) : ℝ :=
  A * (cos θ - cos φ) - 2 * B * sin φ +
    (θ - φ - 1) * cos θ - sin θ + cos φ + sin φ

/-- The left side of the second equation of Gerver's system. -/
def eq2 (A B φ θ : ℝ) : ℝ :=
  A * (3 * sin θ + sin φ) - 2 * B * cos φ +
    3 * (θ - φ - 1) * sin θ + 3 * cos θ - sin φ + cos φ

/-- The left side of the third equation of Gerver's system (it does not involve `θ`). -/
def eq3 (A B φ _θ : ℝ) : ℝ :=
  A * cos φ - (sin φ + 1 / 2 - cos φ / 2 + B * sin φ)

/-- The left side of the fourth equation of Gerver's system. -/
def eq4 (A B φ θ : ℝ) : ℝ :=
  (A + π / 2 - φ - θ) - (B - (θ - φ) * (1 + A) / 2 - (θ - φ)^2 / 4)

/-- `Spec` in terms of the four equations `eq1`, …, `eq4`. -/
theorem spec_iff {A B φ θ : ℝ} : Spec A B φ θ ↔
    0 ≤ φ ∧ φ ≤ θ ∧ θ ≤ π / 4 ∧ 0 ≤ A ∧ 0 ≤ B ∧
      eq1 A B φ θ = 0 ∧ eq2 A B φ θ = 0 ∧
      eq3 A B φ θ = 0 ∧ eq4 A B φ θ = 0 := Iff.rfl

/-- The denominator `D = 3 cos φ - cos θ`: a solution has `A = N / D`. -/
def den (φ θ : ℝ) : ℝ := 3 * cos φ - cos θ

/-- The numerator `N`: a solution has `A = N / D`. -/
def num (φ θ : ℝ) : ℝ :=
  (θ - φ) * cos θ + 3 * sin φ - sin θ - cos θ + 1

/-- The slope `k = 1 + (θ - φ)/2`: a solution has `B = A k + o`. -/
def slope (φ θ : ℝ) : ℝ := 1 + (θ - φ) / 2

/-- The offset `o`: a solution has `B = A k + o`. -/
def offset (φ θ : ℝ) : ℝ :=
  π / 2 - φ - θ + (θ - φ) / 2 + (θ - φ)^2 / 4

/-- The reduced function `Q` of the angles, which vanishes at every solution. -/
def reducedQ (φ θ : ℝ) : ℝ :=
  num φ θ * (cos φ - sin φ * slope φ θ) -
    den φ θ * (sin φ + 1 / 2 - cos φ / 2 + sin φ * offset φ θ)

/-- `A` as a function of the angles, `Â = N / D`. -/
def reconstructedA (φ θ : ℝ) : ℝ := num φ θ / den φ θ

/-- `B` as a function of the angles, `B̂ = Â k + o`. -/
def reconstructedB (φ θ : ℝ) : ℝ := reconstructedA φ θ * slope φ θ + offset φ θ

/-- The denominator `3 cos φ - cos θ` is positive on the domain. -/
theorem den_pos {φ θ : ℝ} (hφ : 0 ≤ φ) (horder : φ ≤ θ) (hθ : θ ≤ π / 4) : 0 < den φ θ := by
  obtain ⟨-, -, hc, hcc, -⟩ := triangle_trig hφ horder hθ
  unfold den
  linarith

/-- Subtracting twice equation three from equation one eliminates B. -/
theorem eliminate_B (A B φ θ : ℝ) :
    eq1 A B φ θ - 2 * eq3 A B φ θ = num φ θ - A * den φ θ := by
  unfold eq1 eq3 num den
  ring

/-- Equation four determines B once A and the angles are known. -/
theorem eliminate_eq4 (A B φ θ : ℝ) :
    eq4 A B φ θ = A * slope φ θ + offset φ θ - B := by
  unfold eq4 slope offset
  ring

/-- `reducedQ` as a combination of the equations. -/
theorem reducedQ_identity (A B φ θ : ℝ) :
    reducedQ φ θ = den φ θ * (eq3 A B φ θ - sin φ * eq4 A B φ θ) +
      (cos φ - sin φ * slope φ θ) * (eq1 A B φ θ - 2 * eq3 A B φ θ) := by
  unfold reducedQ den num slope offset eq1 eq3 eq4
  ring

/-- Every solution is a zero of the reduced function `reducedQ`. -/
theorem Spec.reduced_zero {A B φ θ : ℝ} (h : Spec A B φ θ) : reducedQ φ θ = 0 := by
  obtain ⟨-, -, -, -, -, h1, -, h3, h4⟩ := spec_iff.mp h
  rw [reducedQ_identity A B, h1, h3, h4]
  ring

/-- The two coefficients are uniquely reconstructed from the two angles. -/
theorem Spec.coefficients {A B φ θ : ℝ} (h : Spec A B φ θ) :
    A = reconstructedA φ θ ∧ B = reconstructedB φ θ := by
  obtain ⟨hφ, horder, hθ, -, -, h1, -, h3, h4⟩ := spec_iff.mp h
  have hA : A = reconstructedA φ θ := by
    rw [reconstructedA, eq_div_iff (den_pos hφ horder hθ).ne']
    linarith [eliminate_B A B φ θ]
  have hB := eliminate_eq4 A B φ θ
  rw [h4, hA] at hB
  exact ⟨hA, by unfold reconstructedB; linarith⟩

/-- There cannot be two different coefficient pairs at the same angles. -/
theorem coefficients_unique {A B A' B' φ θ : ℝ}
    (h : Spec A B φ θ) (h' : Spec A' B' φ θ) : A = A' ∧ B = B' :=
  ⟨h.coefficients.1.trans h'.coefficients.1.symm,
    h.coefficients.2.trans h'.coefficients.2.symm⟩

/-!
## The boundary of the domain

No solution has `φ = 0` or `φ = θ`.
-/

/-- `b(t) = (t - 1) cos t - sin t + 1`: the first equation at `φ = 0`, `A = 0`, and the
numerator `num 0 t`. -/
def baseNumerator (t : ℝ) : ℝ := (t - 1) * cos t - sin t + 1

/-- `b'(t) = (1 - t) sin t`. -/
theorem baseNumerator_deriv (t : ℝ) : HasDerivAt baseNumerator ((1 - t) * sin t) t :=
  (((((hasDerivAt_id' t).sub_const 1).mul (hasDerivAt_cos t)).sub
    (hasDerivAt_sin t)).add_const 1).congr_deriv (by ring)

/-- No solution has `φ = 0`. -/
theorem Spec.phi_pos {A B φ θ : ℝ} (h : Spec A B φ θ) : 0 < φ := by
  obtain ⟨hφ, horder, hθ, -, -, h1, h2, h3, h4⟩ := spec_iff.mp h
  refine hφ.lt_of_ne fun hφ0 => ?_
  subst hφ0
  -- With `φ = 0`, the third equation gives `A = 0`.
  have hA : A = 0 := by simpa [eq3] using h3
  -- `θ = 0` would give `B = 2` by the second equation, and then `π = 4` by the fourth.
  have hθpos : 0 < θ := by
    refine horder.lt_of_ne fun hθ0 => ?_
    subst hθ0
    have hB : B = 2 := by
      simp [eq2, hA] at h2
      linarith
    simp [eq4, hA, hB] at h4
    linarith [pi_lt_four]
  -- The first equation says `b(θ) = 0`, but `b(0) = 0` and `b` increases strictly on `[0, θ]`.
  have hmono : StrictMonoOn baseNumerator (Icc 0 θ) :=
    strictMonoOn_Icc_of_hasDerivAt (fun t _ => baseNumerator_deriv t) fun t ht =>
      mul_pos (by linarith [ht.2, pi_lt_four])
        (sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos]))
  have hb0 : baseNumerator 0 = 0 := by simp [baseNumerator]
  have hbθ : baseNumerator θ = 0 := by simpa [baseNumerator, eq1, hA] using h1
  exact (hmono ⟨le_rfl, hθpos.le⟩ ⟨hθpos.le, le_rfl⟩ hθpos).ne (hb0.trans hbθ.symm)

/-- No solution has `φ = θ`. -/
theorem Spec.phi_lt_theta {A B φ θ : ℝ} (h : Spec A B φ θ) : φ < θ := by
  have hφpos := h.phi_pos
  obtain ⟨-, horder, hθ, hA, -, h1, -, h3, h4⟩ := spec_iff.mp h
  refine horder.lt_of_ne fun heq => ?_
  subst θ
  have hsin : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφpos (by linarith [pi_pos])
  -- With `θ = φ`, the first equation is `-2 B sin φ = 0`, so `B = 0`.
  have hB : B = 0 := by
    refine (mul_eq_zero.mp (?_ : B * sin φ = 0)).resolve_right hsin.ne'
    unfold eq1 at h1
    linarith
  -- The fourth equation is then `A = 2φ - π/2 ≤ 0`, so `A = 0`.
  have hA0 : A = 0 := by
    unfold eq4 at h4
    rw [hB] at h4
    linarith
  -- And the third equation fails: `sin φ + (1 - cos φ)/2 > 0`.
  unfold eq3 at h3
  rw [hA0, hB] at h3
  linarith [cos_le_one φ]

/-!
## A first bound on `φ`

Every solution has `B ≥ A` and `φ < 1/2` (`Spec.phi_lt_half`).
-/

/-- The offset `o` is nonnegative on the domain. -/
theorem offset_nonneg {φ θ : ℝ} (horder : φ ≤ θ) (hθ : θ ≤ π / 4) : 0 ≤ offset φ θ := by
  unfold offset
  nlinarith [sq_nonneg (θ - φ), sub_nonneg.mpr horder]

/-- The fourth equation and the domain give `A ≤ B`. -/
theorem Spec.A_le_B {A B φ θ : ℝ} (h : Spec A B φ θ) : A ≤ B := by
  obtain ⟨-, ho, ht, hA, -, -, -, -, h4⟩ := spec_iff.mp h
  have he := eliminate_eq4 A B φ θ
  have hslope : 1 ≤ slope φ θ := by unfold slope; linarith
  linarith [mul_le_mul_of_nonneg_left hslope hA, offset_nonneg ho ht]

/-- An inequality between the angles that follows from the equations. -/
theorem Spec.angle_inequality {A B φ θ : ℝ} (h : Spec A B φ θ) :
    3 * sin φ ^ 2 - cos φ * sin φ ≤ (θ - φ) * (cos φ - sin φ) := by
  obtain ⟨hp, ho, ht, hA, -, h1, -, h3, -⟩ := spec_iff.mp h
  obtain ⟨hs, hsc, hc, hcc, -, -, hsum⟩ := triangle_trig hp ho ht
  have hcs : 0 ≤ cos φ - sin φ := sub_nonneg.mpr hsc
  -- The third equation and `A ≤ B` give `sin φ ≤ A (cos φ - sin φ)`.
  have hbase : sin φ ≤ A * (cos φ - sin φ) := by
    have hAB := mul_le_mul_of_nonneg_right h.A_le_B hs
    unfold eq3 at h3
    nlinarith [cos_le_one φ]
  -- Equations one and three give `2 A cos φ ≤ θ - φ + 3 sin φ`.
  have hsmall : 2 * A * cos φ ≤ θ - φ + 3 * sin φ := by
    have hid := eliminate_B A B φ θ
    rw [h1, h3] at hid
    have hm := mul_le_mul_of_nonneg_left hcc hA
    have hd : (θ - φ) * cos θ ≤ θ - φ := by
      simpa using mul_le_mul_of_nonneg_left (cos_le_one θ) (sub_nonneg.mpr ho)
    unfold num den at hid
    nlinarith
  have hleft := mul_le_mul_of_nonneg_left hbase (show 0 ≤ 2 * cos φ by positivity)
  have hright := mul_le_mul_of_nonneg_right hsmall hcs
  nlinarith

/-- Every solution has `φ < 1/2`. -/
theorem Spec.phi_lt_half {A B φ θ : ℝ} (h : Spec A B φ θ) : φ < 1 / 2 := by
  obtain ⟨hp, ho, ht, -, -, -, -, -, -⟩ := spec_iff.mp h
  obtain ⟨hs, hsc, -, -, -, -, -⟩ := triangle_trig hp ho ht
  by_contra! hφ
  have hslo := sin_ge_of_half_le hφ (ho.trans ht)
  have hδ : θ - φ ≤ 3 / 10 := by linarith [pi_lt_d2]
  have hprod : (θ - φ) * (cos φ - sin φ) ≤ (3 / 10) * (1 - sin φ) :=
    mul_le_mul hδ (sub_le_sub_right (cos_le_one φ) _) (sub_nonneg.mpr hsc) (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right (cos_le_one φ) hs
  -- So `3s² - (7/10)s - 3/10 ≤ 0` for `s = sin φ ≥ 23/48`, which is false.
  nlinarith [h.angle_inequality, sq_nonneg (sin φ - 23 / 48)]

/-!
## Derivatives of the reduced equation `reducedQ`

The partial derivatives of `reducedQ`. For `φ ≤ 1/2` its `φ`-derivative is negative
(`qPhi_neg`): it is bounded by an auxiliary function whose `θ`-derivative is a sum of nonpositive
terms and which is nonpositive on the diagonal.
-/

/-- The gap `g = θ - φ` between the angles. -/
def gap (φ θ : ℝ) : ℝ := θ - φ

/-- `J = cos φ - k sin φ`, the second factor of `reducedQ = N J - D Z`. -/
def frameDen (φ θ : ℝ) : ℝ := cos φ - slope φ θ * sin φ

/-- `Z = sin φ (1 + o) + (1 - cos φ)/2`, the fourth factor of `reducedQ = N J - D Z`. -/
def frameOffset (φ θ : ℝ) : ℝ :=
  sin φ * (1 + offset φ θ) + (1 - cos φ) / 2

/-- `m = g/2 + g²/4`, the offset `o` without its term `π/2 - φ - θ`. -/
def minOffset (φ θ : ℝ) : ℝ := gap φ θ / 2 + gap φ θ ^ 2 / 4

/-- The `φ`-derivative of `reducedQ`. -/
def qPhi (φ θ : ℝ) : ℝ :=
  -den φ θ * cos φ * offset φ θ -
    num φ θ * (sin φ / 2 + slope φ θ * cos φ) +
      3 * sin φ * frameOffset φ θ

/-- The `θ`-derivative of `reducedQ`. -/
def qTheta (φ θ : ℝ) : ℝ :=
  ((1 - gap φ θ) * frameDen φ θ - frameOffset φ θ) * sin θ +
    (3 * (1 - gap φ θ) * cos φ - 3 * sin φ + sin θ - 1) * sin φ / 2

/-- `qPhi` with the offset `o` replaced by `minOffset`: an upper bound for `qPhi`. -/
def qPhiMin (φ θ : ℝ) : ℝ :=
  -den φ θ * cos φ * minOffset φ θ -
    num φ θ * (sin φ / 2 + slope φ θ * cos φ) +
      3 * sin φ * (sin φ * (1 + minOffset φ θ) + (1 - cos φ) / 2)

/-- A manifest-sign form of the theta derivative of qPhiMin. -/
def qPhiMinTheta (φ θ : ℝ) : ℝ :=
  (-6 * gap φ θ * (cos φ ^ 2 - sin φ ^ 2) +
    6 * sin φ * (sin φ - cos φ) - 2 * cos φ ^ 2 +
    4 * cos φ * (cos θ - cos φ) - 2 * cos φ +
    cos φ * sin θ * (gap φ θ ^ 2 - 2) +
    2 * sin φ * sin θ * (gap φ θ - 1)) / 4

/-- `reducedQ = N J - D Z`. -/
theorem reducedQ_frame (φ θ : ℝ) :
    reducedQ φ θ = num φ θ * frameDen φ θ - den φ θ * frameOffset φ θ := by
  unfold reducedQ frameDen frameOffset
  ring

theorem num_phi_deriv (φ θ : ℝ) : HasDerivAt (fun p => num p θ) (den φ θ) φ := by
  have h := (((((hasDerivAt_id' φ).const_sub θ).mul_const (cos θ)).fun_add
    ((hasDerivAt_sin φ).const_mul 3)).sub_const (sin θ)).sub_const (cos θ) |>.add_const 1
  exact h.congr_deriv (by unfold den; ring)

theorem num_theta_deriv (φ θ : ℝ) :
    HasDerivAt (fun t => num φ t) ((1 - gap φ θ) * sin θ) θ := by
  have h := (((((hasDerivAt_id' θ).sub_const φ).fun_mul (hasDerivAt_cos θ)).add_const
    (3 * sin φ)).fun_sub (hasDerivAt_sin θ)).fun_sub (hasDerivAt_cos θ) |>.add_const 1
  exact h.congr_deriv (by unfold gap; ring)

theorem den_phi_deriv (φ θ : ℝ) : HasDerivAt (fun p => den p θ) (-3 * sin φ) φ :=
  (((hasDerivAt_cos φ).const_mul 3).sub_const (cos θ)).congr_deriv (by ring)

theorem den_theta_deriv (φ θ : ℝ) : HasDerivAt (fun t => den φ t) (sin θ) θ :=
  ((hasDerivAt_cos θ).const_sub (3 * cos φ)).congr_deriv (by ring)

theorem slope_phi_deriv (φ θ : ℝ) : HasDerivAt (fun p => slope p θ) (-1 / 2) φ :=
  ((((hasDerivAt_id' φ).const_sub θ).div_const 2).const_add 1).congr_deriv (by ring)

theorem slope_theta_deriv (φ θ : ℝ) : HasDerivAt (fun t => slope φ t) (1 / 2) θ :=
  ((((hasDerivAt_id' θ).sub_const φ).div_const 2).const_add 1).congr_deriv (by ring)

theorem offset_phi_deriv (φ θ : ℝ) :
    HasDerivAt (fun p => offset p θ) (-slope φ θ - 1 / 2) φ := by
  have hg := (hasDerivAt_id' φ).const_sub θ
  refine (((((hasDerivAt_id' φ).const_sub (π / 2)).sub_const θ).fun_add
    (hg.div_const 2)).fun_add ((hg.fun_pow 2).div_const 4)).congr_deriv ?_
  unfold slope
  norm_num
  ring

theorem offset_theta_deriv (φ θ : ℝ) :
    HasDerivAt (fun t => offset φ t) ((gap φ θ - 1) / 2) θ := by
  have hg := (hasDerivAt_id' θ).sub_const φ
  refine ((((hasDerivAt_id' θ).const_sub (π / 2 - φ)).fun_add
    (hg.div_const 2)).fun_add ((hg.fun_pow 2).div_const 4)).congr_deriv ?_
  unfold gap
  norm_num
  ring

theorem frameDen_phi_deriv (φ θ : ℝ) :
    HasDerivAt (fun p => frameDen p θ) (-sin φ / 2 - slope φ θ * cos φ) φ :=
  ((hasDerivAt_cos φ).fun_sub ((slope_phi_deriv φ θ).fun_mul (hasDerivAt_sin φ))).congr_deriv
    (by ring)

theorem frameDen_theta_deriv (φ θ : ℝ) :
    HasDerivAt (fun t => frameDen φ t) (-sin φ / 2) θ :=
  (((slope_theta_deriv φ θ).mul_const (sin φ)).const_sub (cos φ)).congr_deriv (by ring)

theorem frameOffset_phi_deriv (φ θ : ℝ) :
    HasDerivAt (fun p => frameOffset p θ)
      (cos φ * (1 + offset φ θ) - slope φ θ * sin φ) φ :=
  (((hasDerivAt_sin φ).fun_mul ((offset_phi_deriv φ θ).const_add 1)).fun_add
    (((hasDerivAt_cos φ).const_sub 1).div_const 2)).congr_deriv (by ring)

theorem frameOffset_theta_deriv (φ θ : ℝ) :
    HasDerivAt (fun t => frameOffset φ t) (sin φ * (gap φ θ - 1) / 2) θ :=
  ((((offset_theta_deriv φ θ).const_add 1).const_mul (sin φ)).add_const
    ((1 - cos φ) / 2)).congr_deriv (by ring)

/-- `qPhi` is the `φ`-derivative of `reducedQ`. -/
theorem reducedQ_phi_deriv (φ θ : ℝ) :
    HasDerivAt (fun p => reducedQ p θ) (qPhi φ θ) φ := by
  have hd := ((num_phi_deriv φ θ).mul (frameDen_phi_deriv φ θ)).sub
    ((den_phi_deriv φ θ).mul (frameOffset_phi_deriv φ θ))
  convert hd using 1
  · funext p
    exact reducedQ_frame p θ
  · unfold qPhi frameDen frameOffset
    ring

/-- `qTheta` is the `θ`-derivative of `reducedQ`. -/
theorem reducedQ_theta_deriv (φ θ : ℝ) :
    HasDerivAt (fun t => reducedQ φ t) (qTheta φ θ) θ := by
  have hd := ((num_theta_deriv φ θ).mul (frameDen_theta_deriv φ θ)).sub
    ((den_theta_deriv φ θ).mul (frameOffset_theta_deriv φ θ))
  convert hd using 1
  · funext t
    exact reducedQ_frame φ t
  · unfold qTheta gap frameDen frameOffset num den slope
    ring

/-- `qPhiMinTheta` is the `θ`-derivative of `qPhiMin`. -/
theorem qPhiMin_theta_deriv (φ θ : ℝ) :
    HasDerivAt (fun t => qPhiMin φ t) (qPhiMinTheta φ θ) θ := by
  have hg := (hasDerivAt_id' θ).sub_const φ
  have hm : HasDerivAt (fun t => minOffset φ t) (1 / 2 + gap φ θ / 2) θ := by
    refine ((hg.div_const 2).fun_add ((hg.fun_pow 2).div_const 4)).congr_deriv ?_
    unfold gap
    norm_num
    ring
  have h1 := ((den_theta_deriv φ θ).fun_neg.mul_const (cos φ)).fun_mul hm
  have h2 := (num_theta_deriv φ θ).fun_mul
    (((slope_theta_deriv φ θ).mul_const (cos φ)).const_add (sin φ / 2))
  have h3 := (((hm.const_add 1).const_mul (sin φ)).add_const ((1 - cos φ) / 2)).const_mul
    (3 * sin φ)
  refine ((h1.fun_sub h2).fun_add h3).congr_deriv ?_
  unfold qPhiMinTheta minOffset gap slope num den
  ring

/-- The `θ`-derivative of `qPhiMin` is negative on the domain. -/
theorem qPhiMinTheta_neg {φ θ : ℝ} (hφ : 0 ≤ φ) (horder : φ ≤ θ)
    (hθ : θ ≤ π / 4) : qPhiMinTheta φ θ < 0 := by
  obtain ⟨hs, hsc, hc, hcc, hts, -, -⟩ := triangle_trig hφ horder hθ
  have hg0 : 0 ≤ gap φ θ := sub_nonneg.mpr horder
  have hg1 : gap φ θ ≤ 1 := by unfold gap; linarith [pi_lt_four]
  have hsq : 0 ≤ cos φ ^ 2 - sin φ ^ 2 := by nlinarith
  have h0 : 0 ≤ gap φ θ * (cos φ ^ 2 - sin φ ^ 2) := mul_nonneg hg0 hsq
  have h1 : 0 ≤ sin φ * (cos φ - sin φ) := mul_nonneg hs (sub_nonneg.mpr hsc)
  have h2 : 0 ≤ cos φ * (cos φ - cos θ) := mul_nonneg hc.le (sub_nonneg.mpr hcc)
  have h3 : 0 ≤ cos φ * sin θ * (2 - gap φ θ ^ 2) :=
    mul_nonneg (mul_nonneg hc.le hts) (by nlinarith)
  have h4 : 0 ≤ sin φ * sin θ * (1 - gap φ θ) :=
    mul_nonneg (mul_nonneg hs hts) (by linarith)
  unfold qPhiMinTheta
  nlinarith [sq_nonneg (cos φ)]

/-- `qPhiMin` is nonpositive on the diagonal `θ = φ`. -/
theorem qPhiMin_diagonal_nonpos {φ : ℝ} (hφ : 0 ≤ φ) (hφu : φ ≤ π / 4) :
    qPhiMin φ φ ≤ 0 := by
  obtain ⟨hs, hsc, hc, -, -, -, -⟩ := triangle_trig hφ le_rfl hφu
  have he : qPhiMin φ φ = (sin φ - cos φ) * (1 - cos φ + 2 * sin φ) := by
    unfold qPhiMin minOffset gap num den slope
    ring
  rw [he]
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hsc) (by linarith [cos_le_one φ])

/-- `qPhi` is bounded by the auxiliary `qPhiMin`. -/
theorem qPhi_le_min {φ θ : ℝ} (hφ : 0 ≤ φ) (hφh : φ ≤ 1 / 2)
    (horder : φ ≤ θ) (hθ : θ ≤ π / 4) : qPhi φ θ ≤ qPhiMin φ θ := by
  obtain ⟨hs, -, hc, hcc, -, -, -⟩ := triangle_trig hφ horder hθ
  have hsHalf : sin φ ≤ 1 / 2 := (sin_le hφ).trans hφh
  have hcLower : (7 / 8 : ℝ) ≤ cos φ := by nlinarith [one_sub_sq_div_two_le_cos (x := φ)]
  have hden : 2 * cos φ ≤ den φ θ := by unfold den; linarith
  have hdenMul := mul_le_mul_of_nonneg_right hden hc.le
  have hcoeff : -den φ θ * cos φ + 3 * sin φ ^ 2 ≤ 0 := by nlinarith
  have hprod := mul_nonpos_of_nonpos_of_nonneg hcoeff (by linarith : 0 ≤ π / 2 - φ - θ)
  have he : qPhi φ θ - qPhiMin φ θ =
      (-den φ θ * cos φ + 3 * sin φ ^ 2) * (π / 2 - φ - θ) := by
    unfold qPhi qPhiMin frameOffset offset minOffset gap
    ring
  linarith

/-- The `φ`-derivative of `reducedQ` is negative for `φ ≤ 1/2`. -/
theorem qPhi_neg {φ θ : ℝ} (hφ : 0 ≤ φ) (hφh : φ ≤ 1 / 2)
    (horder : φ < θ) (hθ : θ ≤ π / 4) : qPhi φ θ < 0 := by
  have hanti : StrictAntiOn (qPhiMin φ) (Icc φ θ) :=
    strictAntiOn_Icc_of_hasDerivAt (fun t _ => qPhiMin_theta_deriv φ t) fun t ht =>
      qPhiMinTheta_neg hφ ht.1.le (ht.2.le.trans hθ)
  calc qPhi φ θ ≤ qPhiMin φ θ := qPhi_le_min hφ hφh horder.le hθ
    _ < qPhiMin φ φ := hanti ⟨le_rfl, horder.le⟩ ⟨horder.le, le_rfl⟩ horder
    _ ≤ 0 := qPhiMin_diagonal_nonpos hφ (horder.le.trans hθ)

/-!
## Every solution has `φ < 1/20`

`reducedQ` decreases in `φ`, and at `φ = 1/20` it increases in `θ` up to a negative value at
`θ = π/4`; so it has no zero with `φ ≥ 1/20` (`Spec.phi_lt_twentieth`).
-/

/-- Bounds on `sin (1/20)` and `cos (1/20)`. -/
theorem cut_trig :
    (499 / 10000 : ℝ) ≤ sin (1 / 20) ∧ sin (1 / 20) ≤ 1 / 20 ∧
      (499 / 500 : ℝ) ≤ cos (1 / 20) ∧ cos (1 / 20) ≤ 1 := by
  have hs := sin_ge_sub_cube (by norm_num : (0 : ℝ) ≤ 1 / 20)
  have hc := one_sub_sq_div_two_le_cos (x := (1 / 20 : ℝ))
  exact ⟨by linarith, sin_le (by norm_num), by linarith, cos_le_one _⟩

/-- Bounds on the factors `J` and `Z` of `reducedQ` on the segment `φ = 1/20`. -/
theorem cut_frame_bounds {θ : ℝ} (hl : (1 / 20 : ℝ) ≤ θ) (hu : θ ≤ π / 4) :
    (9 / 10 : ℝ) ≤ frameDen (1 / 20) θ ∧
      frameOffset (1 / 20) θ ≤ 151 / 1000 := by
  obtain ⟨hslo, hshi, hclo, hchi⟩ := cut_trig
  have hd1 : θ - 1 / 20 ≤ 3 / 4 := by linarith [pi_lt_d2]
  have hk1 : slope (1 / 20) θ ≤ 11 / 8 := by unfold slope; linarith
  have hoff : offset (1 / 20) θ ≤ 2 := by
    have hsq : (θ - 1 / 20) ^ 2 ≤ 2 * (θ - 1 / 20) := by nlinarith
    unfold offset
    linarith [pi_lt_four]
  have hp := mul_le_mul hk1 hshi (by linarith) (by norm_num : (0 : ℝ) ≤ 11 / 8)
  have hz : sin (1 / 20) * (1 + offset (1 / 20) θ) ≤ (1 / 20) * 3 :=
    mul_le_mul hshi (by linarith) (by linarith [offset_nonneg hl hu]) (by norm_num)
  constructor
  · unfold frameDen
    linarith
  · unfold frameOffset
    linarith

/-- On the segment `φ = 1/20`, `reducedQ` increases strictly in `θ`. -/
theorem qTheta_cut_pos {θ : ℝ} (hl : (1 / 20 : ℝ) ≤ θ) (hu : θ ≤ π / 4) :
    0 < qTheta (1 / 20) θ := by
  obtain ⟨hslo, hshi, hclo, hchi⟩ := cut_trig
  obtain ⟨hJ, hZ⟩ := cut_frame_bounds hl hu
  have hsθ : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos])
  have hd0 : 0 ≤ gap (1 / 20) θ := by unfold gap; linarith
  have hd1 : gap (1 / 20) θ ≤ 3 / 4 := by unfold gap; linarith [pi_lt_d2]
  -- The coefficient of `sin θ` is positive: `(1 - g) J - Z ≥ (1/4)(9/10) - 0.151`.
  have hUprod : (1 / 4 : ℝ) * (9 / 10) ≤ (1 - gap (1 / 20) θ) * frameDen (1 / 20) θ :=
    mul_le_mul (by linarith) hJ (by norm_num) (by linarith)
  have hU : 0 < (1 - gap (1 / 20) θ) * frameDen (1 / 20) θ - frameOffset (1 / 20) θ := by
    linarith
  -- The coefficient of `sin (1/20)` is positive: split at `θ = 1/2`.
  have hC : 0 < 3 * (1 - gap (1 / 20) θ) * cos (1 / 20) -
      3 * sin (1 / 20) + sin θ - 1 := by
    by_cases ht : θ ≤ 1 / 2
    · have hm : (11 / 20 : ℝ) * (499 / 500) ≤ (1 - gap (1 / 20) θ) * cos (1 / 20) :=
        mul_le_mul (by unfold gap; linarith) hclo (by norm_num) (by linarith)
      nlinarith
    · have hsθ' := sin_ge_of_half_le (not_le.mp ht).le hu
      have hm : (1 / 4 : ℝ) * (499 / 500) ≤ (1 - gap (1 / 20) θ) * cos (1 / 20) :=
        mul_le_mul (by linarith) hclo (by norm_num) (by linarith)
      nlinarith
  have hfirst := mul_nonneg hU.le hsθ
  have hsecond := mul_pos hC (by linarith : (0 : ℝ) < sin (1 / 20))
  unfold qTheta
  linarith

/-- `reducedQ` is negative at `(1/20, π/4)`. -/
theorem reducedQ_cut_boundary_neg : reducedQ (1 / 20) (π / 4) < 0 := by
  obtain ⟨hslo, hshi, hclo, hchi⟩ := cut_trig
  obtain ⟨hulo, huhi⟩ := cos_pi_div_four_bounds
  have hπlo : (314 / 100 : ℝ) < π := by linarith [pi_gt_d20]
  have hπhi : π < (3144 / 1000 : ℝ) := by linarith [pi_lt_d20]
  have hdlo : (147 / 200 : ℝ) ≤ gap (1 / 20) (π / 4) := by unfold gap; linarith
  have hdhi : gap (1 / 20) (π / 4) ≤ 92 / 125 := by unfold gap; linarith
  -- Step 1: `N ≤ 0.257`, as `N = (2 - g) cos (π/4) + 3 sin (1/20) - 1` at this point.
  have hN : num (1 / 20) (π / 4) ≤ 257 / 1000 := by
    have hm : (2 - (92 / 125 : ℝ)) * (707 / 1000) ≤
        (2 - gap (1 / 20) (π / 4)) * cos (π / 4) :=
      mul_le_mul (by linarith) hulo (by norm_num) (by linarith)
    unfold num
    rw [sin_pi_div_four, ← cos_pi_div_four]
    unfold gap at hm
    nlinarith
  -- Step 2: `D ≥ 2.286`.
  have hD : (2286 / 1000 : ℝ) ≤ den (1 / 20) (π / 4) := by
    unfold den
    linarith
  -- Step 3: `0.9 ≤ J ≤ 0.932`.
  have hJ0 := (cut_frame_bounds (θ := π / 4) (by linarith) le_rfl).1
  have hJ : frameDen (1 / 20) (π / 4) ≤ 932 / 1000 := by
    have hk : (1 + (147 / 200 : ℝ) / 2) ≤ slope (1 / 20) (π / 4) := by
      unfold slope gap at *
      linarith
    have hm := mul_le_mul hk hslo (by norm_num : (0 : ℝ) ≤ 499 / 10000) (by linarith)
    unfold frameDen
    nlinarith
  -- Step 4: `o ≥ 1.237`, so `Z ≥ 0.111`.
  have hoff : (1237 / 1000 : ℝ) ≤ offset (1 / 20) (π / 4) := by
    have he : offset (1 / 20) (π / 4) =
        3 * gap (1 / 20) (π / 4) / 2 + gap (1 / 20) (π / 4) ^ 2 / 4 := by
      unfold offset gap
      ring
    rw [he]
    nlinarith
  have hZ : (111 / 1000 : ℝ) ≤ frameOffset (1 / 20) (π / 4) := by
    have hm : (499 / 10000 : ℝ) * (1 + 1237 / 1000) ≤
        sin (1 / 20) * (1 + offset (1 / 20) (π / 4)) :=
      mul_le_mul hslo (by linarith) (by norm_num) (by linarith)
    unfold frameOffset
    linarith
  -- Step 5: `Q = N J - D Z ≤ 0.257 · 0.932 - 2.286 · 0.111 < 0`.
  have hNJ : num (1 / 20) (π / 4) * frameDen (1 / 20) (π / 4) ≤
      (257 / 1000 : ℝ) * (932 / 1000) :=
    calc
      _ ≤ (257 / 1000) * frameDen (1 / 20) (π / 4) :=
        mul_le_mul_of_nonneg_right hN (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left hJ (by norm_num)
  have hDZ : (2286 / 1000 : ℝ) * (111 / 1000) ≤
      den (1 / 20) (π / 4) * frameOffset (1 / 20) (π / 4) :=
    mul_le_mul hD hZ (by norm_num) (by linarith)
  rw [reducedQ_frame]
  linarith

/-- Every solution has `φ < 1/20`. -/
theorem Spec.phi_lt_twentieth {A B φ θ : ℝ} (h : Spec A B φ θ) : φ < 1 / 20 := by
  by_contra! hl
  have horder := h.phi_lt_theta
  have hθ : θ ≤ π / 4 := h.2.2.1
  -- `reducedQ` decreases in `φ` on `[1/20, φ]`, ...
  have hanti : AntitoneOn (fun p => reducedQ p θ) (Icc (1 / 20) φ) :=
    antitoneOn_Icc_of_hasDerivAt (fun p _ => reducedQ_phi_deriv p θ) fun p hp =>
      (qPhi_neg (by linarith [hp.1]) (hp.2.le.trans h.phi_lt_half.le) (hp.2.trans horder) hθ).le
  -- ... and increases in `θ` on the segment `φ = 1/20`, up to a negative value at `θ = π/4`.
  have hmono : MonotoneOn (reducedQ (1 / 20)) (Icc (1 / 20) (π / 4)) :=
    monotoneOn_Icc_of_hasDerivAt (fun t _ => reducedQ_theta_deriv (1 / 20) t) fun t ht =>
      (qTheta_cut_pos ht.1.le ht.2.le).le
  have hfirst : reducedQ φ θ ≤ reducedQ (1 / 20) θ := hanti ⟨le_rfl, hl⟩ ⟨hl, le_rfl⟩ hl
  have hsecond : reducedQ (1 / 20) θ ≤ reducedQ (1 / 20) (π / 4) :=
    hmono ⟨hl.trans horder.le, hθ⟩ ⟨hl.trans (horder.le.trans hθ), le_rfl⟩ hθ
  linarith [h.reduced_zero, reducedQ_cut_boundary_neg]

/-!
## The residuals `F` and `G`

`firstResidual` (`F`) and `secondResidual` (`G`) are the third and second equations with `A` and
`B` expressed through the angles, and `separatingResidual` is `H = G + (9/10) F`. Their partial
derivatives, with the common factor `C = 1 - A - (θ - φ)` of the `θ`-derivatives.
-/

/-- The common factor `C = 1 - Â - (θ - φ)` of the `θ`-derivatives of `F` and `G`. -/
def remainder (φ θ : ℝ) : ℝ := 1 - reconstructedA φ θ - gap φ θ

/-- `F`: the third equation with `A = Â` and `B = B̂`. -/
def firstResidual (φ θ : ℝ) : ℝ :=
  reconstructedA φ θ * cos φ - (reconstructedB φ θ + 1) * sin φ + (cos φ - 1) / 2

/-- `G`: the second equation with `A = Â` and `B = B̂`. -/
def secondResidual (φ θ : ℝ) : ℝ :=
  -3 * remainder φ θ * sin θ + (reconstructedA φ θ - 1) * sin φ +
    (1 - 2 * reconstructedB φ θ) * cos φ + 3 * cos θ

/-- `H = G + (9/10) F`, which decreases in both angles on the strip `φ ≤ 1/20`. -/
def separatingResidual (φ θ : ℝ) : ℝ := secondResidual φ θ + (9 / 10) * firstResidual φ θ

/-- `3 sin θ + sin φ - 2 k cos φ`, a factor of the derivatives of `G`. -/
def armCoefficient (φ θ : ℝ) : ℝ := 3 * sin θ + sin φ - 2 * slope φ θ * cos φ

/-- `∂F/∂φ`. -/
def firstPhi (φ θ : ℝ) : ℝ :=
  -reconstructedB φ θ * cos φ + reconstructedA φ θ * sin φ *
    (3 * cos φ + cos θ - 6 * slope φ θ * sin φ) / (2 * den φ θ)

/-- `(∂F/∂θ) / C`. -/
def firstThetaFactor (φ θ : ℝ) : ℝ :=
  sin θ * frameDen φ θ / den φ θ + sin φ / 2

/-- `∂G/∂φ`. -/
def secondPhi (φ θ : ℝ) : ℝ :=
  3 * reconstructedA φ θ * sin φ * armCoefficient φ θ / den φ θ +
    2 * reconstructedA φ θ * cos φ + 2 * reconstructedB φ θ * sin φ

/-- `(∂G/∂θ) / C`. -/
def secondThetaFactor (φ θ : ℝ) : ℝ :=
  sin θ * armCoefficient φ θ / den φ θ + cos φ - 3 * cos θ

/-- `F` is the third equation at `(Â, B̂)`. -/
theorem firstResidual_eq (φ θ : ℝ) :
    firstResidual φ θ = eq3 (reconstructedA φ θ) (reconstructedB φ θ) φ θ := by
  unfold firstResidual eq3
  ring

/-- `G` is the second equation at `(Â, B̂)`. -/
theorem secondResidual_eq (φ θ : ℝ) :
    secondResidual φ θ = eq2 (reconstructedA φ θ) (reconstructedB φ θ) φ θ := by
  unfold secondResidual eq2 remainder gap
  ring

/-- `F` and `H` vanish at every solution. -/
theorem Spec.residuals_zero {A B φ θ : ℝ} (h : Spec A B φ θ) :
    firstResidual φ θ = 0 ∧ separatingResidual φ θ = 0 := by
  obtain ⟨hA, hB⟩ := h.coefficients
  obtain ⟨-, -, -, -, -, -, h2, h3, -⟩ := spec_iff.mp h
  have hF : firstResidual φ θ = 0 := by rwa [firstResidual_eq, ← hA, ← hB]
  have hG : secondResidual φ θ = 0 := by rwa [secondResidual_eq, ← hA, ← hB]
  exact ⟨hF, by simp only [separatingResidual, hF, hG, mul_zero, add_zero]⟩

theorem reconstructedA_phi_deriv (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    HasDerivAt (fun p => reconstructedA p θ)
      (1 + 3 * reconstructedA φ θ * sin φ / den φ θ) φ := by
  apply ((num_phi_deriv φ θ).div (den_phi_deriv φ θ) hD).congr_deriv
  unfold reconstructedA
  field_simp
  ring

theorem reconstructedA_theta_deriv (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    HasDerivAt (fun t => reconstructedA φ t) (remainder φ θ * sin θ / den φ θ) θ := by
  apply ((num_theta_deriv φ θ).div (den_theta_deriv φ θ) hD).congr_deriv
  unfold remainder reconstructedA
  field_simp
  ring

theorem reconstructedB_phi_deriv (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    HasDerivAt (fun p => reconstructedB p θ)
      (slope φ θ * (3 * reconstructedA φ θ * sin φ / den φ θ) -
        (reconstructedA φ θ + 1) / 2) φ :=
  (((reconstructedA_phi_deriv φ θ hD).mul (slope_phi_deriv φ θ)).add
    (offset_phi_deriv φ θ)).congr_deriv (by ring)

theorem reconstructedB_theta_deriv (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    HasDerivAt (fun t => reconstructedB φ t)
      (slope φ θ * (remainder φ θ * sin θ / den φ θ) - remainder φ θ / 2) θ :=
  (((reconstructedA_theta_deriv φ θ hD).mul (slope_theta_deriv φ θ)).add
    (offset_theta_deriv φ θ)).congr_deriv (by unfold remainder; ring)

theorem firstResidual_phi_deriv (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    HasDerivAt (fun p => firstResidual p θ) (firstPhi φ θ) φ := by
  have hd := (((reconstructedA_phi_deriv φ θ hD).mul (hasDerivAt_cos φ)).sub
    (((reconstructedB_phi_deriv φ θ hD).add_const 1).mul (hasDerivAt_sin φ))).add
      (((hasDerivAt_cos φ).sub_const 1).div_const 2)
  apply hd.congr_deriv
  unfold firstPhi
  field_simp
  unfold den
  ring

theorem firstResidual_theta_deriv (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    HasDerivAt (fun t => firstResidual φ t)
      (remainder φ θ * firstThetaFactor φ θ) θ :=
  ((((reconstructedA_theta_deriv φ θ hD).mul_const (cos φ)).sub
    (((reconstructedB_theta_deriv φ θ hD).add_const 1).mul_const (sin φ))).add_const
      ((cos φ - 1) / 2)).congr_deriv (by unfold firstThetaFactor frameDen; ring)

theorem secondResidual_phi_deriv (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    HasDerivAt (fun p => secondResidual p θ) (secondPhi φ θ) φ := by
  have ha := reconstructedA_phi_deriv φ θ hD
  have hb := reconstructedB_phi_deriv φ θ hD
  have hr : HasDerivAt (fun p => remainder p θ)
      (-(3 * reconstructedA φ θ * sin φ / den φ θ)) φ :=
    ((ha.const_sub 1).sub ((hasDerivAt_id φ).const_sub θ)).congr_deriv (by ring)
  have hd := ((((hr.const_mul (-3)).mul_const (sin θ)).add
    ((ha.sub_const 1).mul (hasDerivAt_sin φ))).add
    (((hb.const_mul 2).const_sub 1).mul (hasDerivAt_cos φ))).add_const (3 * cos θ)
  apply hd.congr_deriv
  unfold secondPhi armCoefficient
  ring

theorem secondResidual_theta_deriv (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    HasDerivAt (fun t => secondResidual φ t)
      (remainder φ θ * secondThetaFactor φ θ) θ := by
  have ha := reconstructedA_theta_deriv φ θ hD
  have hb := reconstructedB_theta_deriv φ θ hD
  have hr : HasDerivAt (fun t => remainder φ t)
      (-remainder φ θ * sin θ / den φ θ - 1) θ :=
    ((ha.const_sub 1).sub ((hasDerivAt_id θ).sub_const φ)).congr_deriv (by ring)
  have hd := ((((hr.const_mul (-3)).mul (hasDerivAt_sin θ)).add
    ((ha.sub_const 1).mul_const (sin φ))).add
    (((hb.const_mul 2).const_sub 1).mul_const (cos φ))).add
      ((hasDerivAt_cos θ).const_mul 3)
  apply hd.congr_deriv
  unfold secondThetaFactor armCoefficient
  ring

/-- A denominator-free form of the last derivative factor. -/
theorem secondThetaFactor_identity (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    den φ θ * secondThetaFactor φ θ =
      3 + 3 * cos φ ^ 2 + sin φ * sin θ - 10 * cos φ * cos θ -
        2 * slope φ θ * cos φ * sin θ := by
  unfold secondThetaFactor armCoefficient
  field_simp [hD]
  unfold den
  linear_combination 3 * (sin_sq_add_cos_sq θ)

theorem separatingResidual_phi_deriv (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    HasDerivAt (fun p => separatingResidual p θ)
      (secondPhi φ θ + (9 / 10) * firstPhi φ θ) φ :=
  (secondResidual_phi_deriv φ θ hD).add ((firstResidual_phi_deriv φ θ hD).const_mul _)

theorem separatingResidual_theta_deriv (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    HasDerivAt (fun t => separatingResidual φ t)
      (remainder φ θ * (secondThetaFactor φ θ + (9 / 10) * firstThetaFactor φ θ)) θ :=
  ((secondResidual_theta_deriv φ θ hD).add
    ((firstResidual_theta_deriv φ θ hD).const_mul (9 / 10))).congr_deriv (by ring)

/-!
## Bounds on the strip `0 ≤ φ ≤ 1/20`, `φ ≤ θ ≤ π/4`

Elementary bounds on the sines and cosines, on `A` and `B`, and on the other quantities of the
derivatives, on the whole strip (`smallBounds`).
-/

/-- `b(t) ≤ 3/20` for `0 ≤ t ≤ 4/5`: `b(t) ≤ t²/2 - t³/3` by `cos t ≥ 1 - t²/2` and
`sin t ≥ t - t³/6`, and `t²/2 - t³/3 ≤ 56/375` there. -/
theorem baseNumerator_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 4 / 5) :
    baseNumerator t ≤ 3 / 20 := by
  have hcos := mul_le_mul_of_nonpos_left (one_sub_sq_div_two_le_cos (x := t))
    (by linarith : t - 1 ≤ 0)
  have hsin := sin_ge_sub_cube ht0
  have hmajorant : t ^ 2 / 2 - t ^ 3 / 3 ≤ 3 / 20 := by
    nlinarith [sq_nonneg (4 / 5 - t), mul_nonneg ht0 (sq_nonneg (4 / 5 - t))]
  unfold baseNumerator
  nlinarith

/-- The numerator `N` is nonnegative on the domain: it increases in `θ` from
`N(φ, φ) = 2 sin φ + 1 - cos φ ≥ 0`. -/
theorem num_nonneg {φ θ : ℝ} (hφ : 0 ≤ φ) (ho : φ ≤ θ) (ht : θ ≤ π / 4) :
    0 ≤ num φ θ := by
  have hm : MonotoneOn (num φ) (Icc φ θ) :=
    monotoneOn_Icc_of_hasDerivAt (fun t _ => num_theta_deriv φ t) fun t ht' =>
      mul_nonneg (by unfold gap; linarith [pi_lt_four, ht'.2])
        (sin_nonneg_of_nonneg_of_le_pi (hφ.trans ht'.1.le) (by linarith [ht'.2, pi_pos]))
  have hdiag : 0 ≤ num φ φ := by
    unfold num
    linarith [cos_le_one φ, (triangle_trig hφ ho ht).1]
  exact hdiag.trans (hm ⟨le_rfl, ho⟩ ⟨ho, le_rfl⟩ ho)

/-- Bounds on the strip `0 ≤ φ ≤ 1/20`, `φ ≤ θ ≤ π/4` on the quantities that enter the partial
derivatives of `F` and `G` (Table A.1 of Appendix A). -/
structure SmallBounds (φ θ : ℝ) : Prop where
  sin_phi : sin φ ∈ Icc (0 : ℝ) (1 / 20)
  cos_phi : cos φ ∈ Icc (499 / 500 : ℝ) 1
  sin_theta : sin θ ∈ Icc (0 : ℝ) (4 / 5)
  cos_theta : cos θ ∈ Icc (7 / 10 : ℝ) 1
  trig_sum : 1 ≤ cos θ + sin θ
  slope_mem : slope φ θ ∈ Icc (1 : ℝ) (7 / 5)
  den_mem : den φ θ ∈ Icc (199 / 100 : ℝ) (23 / 10)
  A_mem : reconstructedA φ θ ∈ Icc (0 : ℝ) (4 / 25)
  B_mem : reconstructedB φ θ ∈ Icc (7 / 10 : ℝ) 2
  frame_mem : frameDen φ θ ∈ Icc (9 / 10 : ℝ) 1
  remainder_pos : 0 < remainder φ θ

/-- The bounds of `SmallBounds` hold on the whole strip. -/
theorem smallBounds {φ θ : ℝ} (hp0 : 0 ≤ φ) (hp1 : φ ≤ 1 / 20)
    (ho : φ ≤ θ) (ht : θ ≤ π / 4) : SmallBounds φ θ := by
  obtain ⟨hs0, -, -, -, hts0, htc0, hsum⟩ := triangle_trig hp0 ho ht
  -- Sines and cosines.
  have hs1 : sin φ ≤ 1 / 20 := (sin_le hp0).trans hp1
  have hc1 : (499 / 500 : ℝ) ≤ cos φ := by nlinarith [one_sub_sq_div_two_le_cos (x := φ)]
  have hθ0 : 0 ≤ θ := hp0.trans ho
  have hθ1 : θ ≤ 4 / 5 := by linarith [pi_lt_d2]
  have hts1 : sin θ ≤ 4 / 5 := (sin_le hθ0).trans hθ1
  have htc1 : (7 / 10 : ℝ) ≤ cos θ := by
    linarith [cos_le_cos_of_nonneg_of_le_pi hθ0 (by linarith [pi_pos]) ht,
      cos_pi_div_four_bounds.1]
  -- The gap, the slope and the denominator.
  have hd1 : θ - φ ≤ 4 / 5 := by linarith
  have hk0 : 1 ≤ slope φ θ := by unfold slope; linarith
  have hk1 : slope φ θ ≤ 7 / 5 := by unfold slope; linarith
  have hD0 : (199 / 100 : ℝ) ≤ den φ θ := by unfold den; linarith [cos_le_one θ]
  have hD1 : den φ θ ≤ 23 / 10 := by unfold den; linarith [cos_le_one φ]
  have hDpos : 0 < den φ θ := by linarith
  -- The numerator: `0 ≤ N = b(θ) - φ cos θ + 3 sin φ ≤ 3/10`, so `0 ≤ Â ≤ 4/25`.
  have hN1 : num φ θ ≤ 3 / 10 := by
    have he : num φ θ = baseNumerator θ - φ * cos θ + 3 * sin φ := by
      unfold num baseNumerator
      ring
    rw [he]
    linarith [baseNumerator_le hθ0 hθ1, mul_nonneg hp0 htc0.le]
  have hA0 : 0 ≤ reconstructedA φ θ := div_nonneg (num_nonneg hp0 ho ht) hDpos.le
  have hA1 : reconstructedA φ θ ≤ 4 / 25 := by
    rw [reconstructedA, div_le_iff₀ hDpos]
    linarith
  -- The offset: `7/10 ≤ o ≤ 8/5`, so `7/10 ≤ B̂ ≤ 2`.
  have hoffLow : (7 / 10 : ℝ) ≤ offset φ θ := by
    unfold offset
    nlinarith [sq_nonneg (θ - φ), pi_gt_three, sub_nonneg.mpr ho]
  have hoffHigh : offset φ θ ≤ 8 / 5 := by
    have hsq : (θ - φ) ^ 2 ≤ 2 * (θ - φ) := by nlinarith
    unfold offset
    linarith [pi_lt_d2]
  have hAk : reconstructedA φ θ * slope φ θ ≤ (4 / 25 : ℝ) * (7 / 5) :=
    mul_le_mul hA1 hk1 (by linarith) (by norm_num)
  have hB0 : (7 / 10 : ℝ) ≤ reconstructedB φ θ := by
    unfold reconstructedB
    linarith [mul_nonneg hA0 (show 0 ≤ slope φ θ by linarith)]
  have hB1 : reconstructedB φ θ ≤ 2 := by unfold reconstructedB; linarith
  -- The factor `J = cos φ - k sin φ`.
  have hks : slope φ θ * sin φ ≤ (7 / 5 : ℝ) * (1 / 20) := mul_le_mul hk1 hs1 hs0 (by norm_num)
  have hJ0 : (9 / 10 : ℝ) ≤ frameDen φ θ := by unfold frameDen; linarith
  have hJ1 : frameDen φ θ ≤ 1 := by
    unfold frameDen
    linarith [cos_le_one φ, mul_nonneg (show 0 ≤ slope φ θ by linarith) hs0]
  refine ⟨⟨hs0, hs1⟩, ⟨hc1, cos_le_one _⟩, ⟨hts0, hts1⟩, ⟨htc1, cos_le_one _⟩, hsum,
    ⟨hk0, hk1⟩, ⟨hD0, hD1⟩, ⟨hA0, hA1⟩, ⟨hB0, hB1⟩, ⟨hJ0, hJ1⟩, ?_⟩
  -- The factor `C = 1 - Â - g ≥ 1 - 4/25 - 4/5`.
  unfold remainder gap
  linarith

/-!
## The signs of the partial derivatives

On the strip, `∂F/∂φ ≤ -2/3`, `0 ≤ (∂F/∂θ)/C ≤ 1/2`, `∂G/∂φ ≤ 3/5` and `(∂G/∂θ)/C ≤ -2/3`, where
`C > 0`. So `H` decreases in `φ` and strictly in `θ` (`separating_signs`).
-/

namespace SmallBounds

variable {φ θ : ℝ} (b : SmallBounds φ θ)
include b

private theorem den_pos : 0 < den φ θ := by linarith [b.den_mem.1]

private theorem A_sin_bounds :
    0 ≤ reconstructedA φ θ * sin φ ∧ reconstructedA φ θ * sin φ ≤ 1 / 125 :=
  ⟨mul_nonneg b.A_mem.1 b.sin_phi.1,
    (mul_le_mul b.A_mem.2 b.sin_phi.2 b.sin_phi.1 (by norm_num)).trans_eq (by norm_num)⟩

/-- `∂F/∂φ ≤ -2/3` on the strip. -/
theorem firstPhi_le : firstPhi φ θ ≤ -2 / 3 := by
  obtain ⟨has0, has1⟩ := b.A_sin_bounds
  have hks : 0 ≤ slope φ θ * sin φ :=
    mul_nonneg (by linarith [b.slope_mem.1]) b.sin_phi.1
  have hT : 3 * cos φ + cos θ - 6 * slope φ θ * sin φ ≤ 4 := by
    linarith [b.cos_phi.2, b.cos_theta.2]
  have hnum : reconstructedA φ θ * sin φ *
      (3 * cos φ + cos θ - 6 * slope φ θ * sin φ) ≤ 4 / 125 := by
    nlinarith [mul_le_mul_of_nonneg_left hT has0]
  have hcor : reconstructedA φ θ * sin φ *
      (3 * cos φ + cos θ - 6 * slope φ θ * sin φ) / (2 * den φ θ) ≤ 1 / 100 := by
    rw [div_le_iff₀ (show (0 : ℝ) < 2 * den φ θ by linarith [b.den_pos])]
    linarith [b.den_mem.1]
  have hmain : (7 / 10 : ℝ) * (499 / 500) ≤ reconstructedB φ θ * cos φ :=
    mul_le_mul b.B_mem.1 b.cos_phi.1 (by norm_num) (by linarith [b.B_mem.1])
  unfold firstPhi
  linarith

/-- `0 ≤ (∂F/∂θ)/C ≤ 1/2` on the strip. -/
theorem firstThetaFactor_bounds :
    0 ≤ firstThetaFactor φ θ ∧ firstThetaFactor φ θ ≤ 1 / 2 := by
  have hJ0 : 0 ≤ frameDen φ θ := by linarith [b.frame_mem.1]
  have hquot0 := div_nonneg (mul_nonneg b.sin_theta.1 hJ0) b.den_pos.le
  have hnum : sin θ * frameDen φ θ ≤ 4 / 5 := by
    nlinarith [mul_le_mul_of_nonneg_left b.frame_mem.2 b.sin_theta.1, b.sin_theta.2]
  have hquot : sin θ * frameDen φ θ / den φ θ ≤ 9 / 20 := by
    rw [div_le_iff₀ b.den_pos]
    linarith [b.den_mem.1]
  unfold firstThetaFactor
  constructor <;> linarith [b.sin_phi.1, b.sin_phi.2]

/-- `∂G/∂φ ≤ 3/5` on the strip. -/
theorem secondPhi_le : secondPhi φ θ ≤ 3 / 5 := by
  obtain ⟨has0, has1⟩ := b.A_sin_bounds
  have hH : armCoefficient φ θ ≤ 5 / 2 := by
    have hkc := mul_nonneg (by linarith [b.slope_mem.1] : 0 ≤ slope φ θ)
      (by linarith [b.cos_phi.1] : 0 ≤ cos φ)
    unfold armCoefficient
    linarith [b.sin_theta.2, b.sin_phi.2]
  have hnum : 3 * reconstructedA φ θ * sin φ * armCoefficient φ θ ≤ 3 / 50 := by
    nlinarith [mul_le_mul_of_nonneg_left hH
      (show 0 ≤ 3 * reconstructedA φ θ * sin φ by nlinarith)]
  have hquot : 3 * reconstructedA φ θ * sin φ * armCoefficient φ θ / den φ θ ≤ 1 / 25 := by
    rw [div_le_iff₀ b.den_pos]
    linarith [b.den_mem.1]
  have hac : reconstructedA φ θ * cos φ ≤ 4 / 25 := by
    nlinarith [mul_le_mul_of_nonneg_left b.cos_phi.2 b.A_mem.1, b.A_mem.2]
  have hbs : reconstructedB φ θ * sin φ ≤ 1 / 10 :=
    (mul_le_mul b.B_mem.2 b.sin_phi.2 b.sin_phi.1 (by norm_num)).trans_eq (by norm_num)
  unfold secondPhi
  linarith

/-- `(∂G/∂θ)/C ≤ -2/3` on the strip. -/
theorem secondThetaFactor_le : secondThetaFactor φ θ ≤ -2 / 3 := by
  have hD := b.den_pos
  have hid := secondThetaFactor_identity φ θ hD.ne'
  have hc0 : 0 ≤ cos φ := by linarith [b.cos_phi.1]
  have hcSq : cos φ ^ 2 ≤ 1 := by nlinarith [b.cos_phi.1, b.cos_phi.2]
  have hsmall : sin φ * sin θ ≤ sin θ / 20 := by
    nlinarith [mul_le_mul_of_nonneg_right b.sin_phi.2 b.sin_theta.1]
  have hcos : (499 / 50 : ℝ) * cos θ ≤ 10 * cos φ * cos θ := by
    nlinarith [mul_le_mul_of_nonneg_right b.cos_phi.1
      (show 0 ≤ cos θ by linarith [b.cos_theta.1])]
  have hkc : (499 / 500 : ℝ) ≤ slope φ θ * cos φ := by
    nlinarith [mul_le_mul_of_nonneg_right b.slope_mem.1 hc0, b.cos_phi.1]
  have hsin : (499 / 250 : ℝ) * sin θ ≤ 2 * slope φ θ * cos φ * sin θ := by
    nlinarith [mul_le_mul_of_nonneg_right hkc b.sin_theta.1]
  have hsum : (37849 / 5000 : ℝ) ≤ (499 / 50) * cos θ + (973 / 500) * sin θ := by
    nlinarith [b.trig_sum, b.cos_theta.1]
  -- `D · (∂G/∂θ)/C ≤ -1.5698` and `D ≤ 2.3`.
  have hnum : den φ θ * secondThetaFactor φ θ ≤ -7849 / 5000 := by nlinarith
  apply (mul_le_mul_iff_right₀ hD).mp
  nlinarith [b.den_mem.2]

/-- `H` decreases in `φ` and strictly in `θ`. -/
theorem separating_signs :
    secondPhi φ θ + (9 / 10) * firstPhi φ θ ≤ 0 ∧
      remainder φ θ * (secondThetaFactor φ θ + (9 / 10) * firstThetaFactor φ θ) < 0 := by
  have hF := b.firstPhi_le
  have hFt := b.firstThetaFactor_bounds.2
  have hG := b.secondPhi_le
  have hGt := b.secondThetaFactor_le
  exact ⟨by linarith, mul_neg_of_pos_of_neg b.remainder_pos (by linarith)⟩

end SmallBounds

/-!
## Uniqueness

If two solutions had `θ < θ'`, then `F(φ, θ') ≥ F(φ, θ) = 0` would force `φ ≤ φ'`, and then
`H(φ', θ') ≤ H(φ, θ') < H(φ, θ) = 0`, a contradiction (`angles_unique`, `spec_unique`).
-/

/-- On the strip, `F` decreases strictly in `φ`. -/
private theorem first_horizontal {b θ : ℝ}
    (hb1 : b ≤ 1 / 20) (hbθ : b ≤ θ) (hθ : θ ≤ π / 4) :
    StrictAntiOn (fun p => firstResidual p θ) (Icc 0 b) :=
  strictAntiOn_Icc_of_hasDerivAt
    (fun p hp => firstResidual_phi_deriv p θ (den_pos hp.1 (hp.2.trans hbθ) hθ).ne') fun p hp =>
      (smallBounds hp.1.le (hp.2.le.trans hb1) (hp.2.le.trans hbθ) hθ).firstPhi_le.trans_lt
        (by norm_num)

/-- On the strip, `F` increases in `θ`. -/
private theorem first_vertical {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1 / 20) :
    MonotoneOn (firstResidual φ) (Icc φ (π / 4)) :=
  monotoneOn_Icc_of_hasDerivAt
    (fun t ht => firstResidual_theta_deriv φ t (den_pos hφ0 ht.1 ht.2).ne') fun _ ht =>
      have b := smallBounds hφ0 hφ1 ht.1.le ht.2.le
      mul_nonneg b.remainder_pos.le b.firstThetaFactor_bounds.1

/-- On the strip, `H` decreases in `φ`. -/
private theorem separating_horizontal {b θ : ℝ}
    (hb1 : b ≤ 1 / 20) (hbθ : b ≤ θ) (hθ : θ ≤ π / 4) :
    AntitoneOn (fun p => separatingResidual p θ) (Icc 0 b) :=
  antitoneOn_Icc_of_hasDerivAt
    (fun p hp => separatingResidual_phi_deriv p θ (den_pos hp.1 (hp.2.trans hbθ) hθ).ne')
    fun _ hp =>
      (smallBounds hp.1.le (hp.2.le.trans hb1) (hp.2.le.trans hbθ) hθ).separating_signs.1

/-- On the strip, `H` decreases strictly in `θ`. -/
private theorem separating_vertical {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1 / 20) :
    StrictAntiOn (separatingResidual φ) (Icc φ (π / 4)) :=
  strictAntiOn_Icc_of_hasDerivAt
    (fun t ht => separatingResidual_theta_deriv φ t (den_pos hφ0 ht.1 ht.2).ne') fun _ ht =>
      (smallBounds hφ0 hφ1 ht.1.le ht.2.le).separating_signs.2

/-- Two solutions cannot have `θ < θ'`. -/
private theorem not_theta_lt {A B φ θ A' B' φ' θ' : ℝ}
    (h : Spec A B φ θ) (h' : Spec A' B' φ' θ') : ¬ θ < θ' := by
  intro htt
  have hp0 := h.phi_pos.le
  have hp1 := h.phi_lt_twentieth.le
  have hpθ := h.phi_lt_theta.le
  have ht1 : θ ≤ π / 4 := h.2.2.1
  have hp'0 := h'.phi_pos.le
  have hp'1 := h'.phi_lt_twentieth.le
  have ht'1 : θ' ≤ π / 4 := h'.2.2.1
  obtain ⟨hF, hH⟩ := h.residuals_zero
  obtain ⟨hF', hH'⟩ := h'.residuals_zero
  -- `F` increases in `θ`, so `F(φ, θ') ≥ F(φ, θ) = 0 = F(φ', θ')`; as `F` decreases strictly in
  -- `φ`, `φ ≤ φ'`.
  have hFθ : firstResidual φ θ ≤ firstResidual φ θ' :=
    first_vertical hp0 hp1 ⟨hpθ, ht1⟩ ⟨hpθ.trans htt.le, ht'1⟩ htt.le
  have hpp : φ ≤ φ' := by
    by_contra! hlt
    have hFφ : firstResidual φ θ' < firstResidual φ' θ' :=
      first_horizontal hp1 (hpθ.trans htt.le) ht'1 ⟨hp'0, hlt.le⟩ ⟨hp0, le_rfl⟩ hlt
    linarith
  -- `H` decreases in both angles: `0 = H(φ', θ') ≤ H(φ, θ') < H(φ, θ) = 0`.
  have hHθ : separatingResidual φ θ' < separatingResidual φ θ :=
    separating_vertical hp0 hp1 ⟨hpθ, ht1⟩ ⟨hpθ.trans htt.le, ht'1⟩ htt
  have hHφ : separatingResidual φ' θ' ≤ separatingResidual φ θ' :=
    separating_horizontal hp'1 h'.phi_lt_theta.le ht'1 ⟨hp0, hpp⟩ ⟨hp'0, le_rfl⟩ hpp
  linarith

/-- Two solutions have the same angles. -/
theorem angles_unique {A B φ θ A' B' φ' θ' : ℝ}
    (h : Spec A B φ θ) (h' : Spec A' B' φ' θ') : φ = φ' ∧ θ = θ' := by
  have ht : θ = θ' := le_antisymm (not_lt.mp (not_theta_lt h' h)) (not_lt.mp (not_theta_lt h h'))
  subst θ'
  -- At the same `θ`, `F` is injective in `φ`.
  have hb1 : max φ φ' ≤ 1 / 20 := max_le h.phi_lt_twentieth.le h'.phi_lt_twentieth.le
  have hbθ : max φ φ' ≤ θ := max_le h.phi_lt_theta.le h'.phi_lt_theta.le
  have heq : firstResidual φ θ = firstResidual φ' θ :=
    h.residuals_zero.1.trans h'.residuals_zero.1.symm
  exact ⟨(first_horizontal hb1 hbθ h.2.2.1).injOn ⟨h.phi_pos.le, le_max_left _ _⟩
    ⟨h'.phi_pos.le, le_max_right _ _⟩ heq, rfl⟩

/-- Gerver's system has at most one solution. -/
theorem spec_unique {A B φ θ A' B' φ' θ' : ℝ}
    (h : Spec A B φ θ) (h' : Spec A' B' φ' θ') :
    A = A' ∧ B = B' ∧ φ = φ' ∧ θ = θ' := by
  obtain ⟨rfl, rfl⟩ := angles_unique h h'
  obtain ⟨ha, hb⟩ := coefficients_unique h h'
  exact ⟨ha, hb, rfl, rfl⟩

end GerverConstants

end MovingSofaBridge
