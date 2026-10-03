module

public import Mathlib

/-!
# Gerver's four constants are unique

Formal-conjectures defines Gerver's sofa from the solution `(A, B, φ, θ)` of Gerver's system
`ABφθSpec` (Romik 2018, Equations (1)–(4)) on the domain `0 ≤ φ ≤ θ ≤ π/4`, `A, B ≥ 0`. This module
proves that the system has at most one solution (`spec_unique`), by elementary inequalities.
`Spec` is a copy of `ABφθSpec`: `ChallengeDefs`, which defines `ABφθSpec`, uses this result.

The angles determine `A` and `B` (`Spec.coefficients`). Every solution has `0 < φ < θ` and
`φ < 1/20` (`Spec.phi_lt_twentieth`). On that triangle the third equation `F`, with `A` and `B`
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

/-!
## The reduced equations

Eliminating `B` and then `A` leaves two equations in the angles, `reducedQ` and `reducedR`
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

def eq1 (A B φ θ : ℝ) : ℝ :=
  A * (cos θ - cos φ) - 2 * B * sin φ +
    (θ - φ - 1) * cos θ - sin θ + cos φ + sin φ

def eq2 (A B φ θ : ℝ) : ℝ :=
  A * (3 * sin θ + sin φ) - 2 * B * cos φ +
    3 * (θ - φ - 1) * sin θ + 3 * cos θ - sin φ + cos φ

def eq3 (A B φ _θ : ℝ) : ℝ :=
  A * cos φ - (sin φ + 1 / 2 - cos φ / 2 + B * sin φ)

def eq4 (A B φ θ : ℝ) : ℝ :=
  (A + π / 2 - φ - θ) - (B - (θ - φ) * (1 + A) / 2 - (θ - φ)^2 / 4)

theorem spec_iff {A B φ θ : ℝ} : Spec A B φ θ ↔
    0 ≤ φ ∧ φ ≤ θ ∧ θ ≤ π / 4 ∧ 0 ≤ A ∧ 0 ≤ B ∧
      eq1 A B φ θ = 0 ∧ eq2 A B φ θ = 0 ∧
      eq3 A B φ θ = 0 ∧ eq4 A B φ θ = 0 := Iff.rfl

def den (φ θ : ℝ) : ℝ := 3 * cos φ - cos θ

def num (φ θ : ℝ) : ℝ :=
  (θ - φ) * cos θ + 3 * sin φ - sin θ - cos θ + 1

def slope (φ θ : ℝ) : ℝ := 1 + (θ - φ) / 2

def offset (φ θ : ℝ) : ℝ :=
  π / 2 - φ - θ + (θ - φ) / 2 + (θ - φ)^2 / 4

def reducedQ (φ θ : ℝ) : ℝ :=
  num φ θ * (cos φ - sin φ * slope φ θ) -
    den φ θ * (sin φ + 1 / 2 - cos φ / 2 + sin φ * offset φ θ)

def reducedR (φ θ : ℝ) : ℝ :=
  num φ θ * (3 * sin θ + sin φ - 2 * cos φ * slope φ θ) +
    den φ θ * (3 * (θ - φ - 1) * sin θ + 3 * cos θ - sin φ + cos φ -
      2 * cos φ * offset φ θ)

def reconstructedA (φ θ : ℝ) : ℝ := num φ θ / den φ θ

def reconstructedB (φ θ : ℝ) : ℝ := reconstructedA φ θ * slope φ θ + offset φ θ

/-- The denominator `3 cos φ - cos θ` is positive on the domain. -/
theorem den_pos {φ θ : ℝ} (hφ : 0 ≤ φ) (horder : φ ≤ θ)
    (hθ : θ ≤ π / 4) : 0 < den φ θ := by
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo
    ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hmono : cos θ ≤ cos φ :=
    cos_le_cos_of_nonneg_of_le_pi hφ (by linarith [pi_pos]) horder
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

theorem reducedR_identity (A B φ θ : ℝ) :
    reducedR φ θ = den φ θ * (eq2 A B φ θ - 2 * cos φ * eq4 A B φ θ) +
      (3 * sin θ + sin φ - 2 * cos φ * slope φ θ) *
        (eq1 A B φ θ - 2 * eq3 A B φ θ) := by
  unfold reducedR den num slope offset eq1 eq2 eq3 eq4
  ring

/-- Every solution is a zero of the two reduced scalar equations. -/
theorem Spec.reduced_zero {A B φ θ : ℝ} (h : Spec A B φ θ) :
    reducedQ φ θ = 0 ∧ reducedR φ θ = 0 := by
  obtain ⟨_, _, _, _, _, h1, h2, h3, h4⟩ := spec_iff.mp h
  rw [reducedQ_identity A B, reducedR_identity A B, h1, h2, h3, h4]
  constructor <;> ring

/-- The two coefficients are uniquely reconstructed from the two angles. -/
theorem Spec.coefficients {A B φ θ : ℝ} (h : Spec A B φ θ) :
    A = reconstructedA φ θ ∧ B = reconstructedB φ θ := by
  obtain ⟨hφ, horder, hθ, _, _, h1, _, h3, h4⟩ := spec_iff.mp h
  have hD := den_pos hφ horder hθ
  have hid := eliminate_B A B φ θ
  rw [h1, h3] at hid
  have hmul : A * den φ θ = num φ θ := by linarith
  have hA : A = reconstructedA φ θ := by
    exact (eq_div_iff hD.ne').mpr hmul
  have hb := eliminate_eq4 A B φ θ
  rw [h4, hA] at hb
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

/-- No solution has `φ = 0`. -/
theorem Spec.phi_pos {A B φ θ : ℝ} (h : Spec A B φ θ) : 0 < φ := by
  obtain ⟨hφ, horder, hθ, hAnonneg, hBnonneg, h1, h2, h3, h4⟩ := spec_iff.mp h
  by_contra hnot
  have hφzero : φ = 0 := le_antisymm (le_of_not_gt hnot) hφ
  subst φ
  have hAzero : A = 0 := by simpa [eq3] using h3
  have hθpos : 0 < θ := by
    by_contra hn
    have hθzero : θ = 0 := le_antisymm (le_of_not_gt hn) horder
    subst θ
    have hBtwo : B = 2 := by
      simp [eq2, hAzero] at h2
      linarith
    have hπfour : π = 4 := by
      simp [eq4, hAzero, hBtwo] at h4
      linarith
    linarith [pi_lt_four]
  let f : ℝ → ℝ := fun t => (t - 1) * cos t - sin t + 1
  have hf' (t : ℝ) : HasDerivAt f ((1 - t) * sin t) t := by
    convert (((((hasDerivAt_id t).sub_const 1).mul (hasDerivAt_cos t)).sub
      (hasDerivAt_sin t)).add_const 1) using 1 <;> dsimp [f]
    ring
  have hθone : θ < 1 := by linarith [pi_lt_four]
  have hstrict : StrictMonoOn f (Icc 0 θ) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 θ)
    · exact fun t _ => (hf' t).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hf' t).deriv]
      apply mul_pos
      · linarith [ht.2]
      · exact sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
  have hzero : f 0 = 0 := by simp [f]
  have hlast : f θ = 0 := by
    simpa [f, eq1, hAzero] using h1
  have hlt := hstrict ⟨le_rfl, hθpos.le⟩ ⟨hθpos.le, le_rfl⟩ hθpos
  rw [hzero, hlast] at hlt
  exact (lt_irrefl (0 : ℝ)) hlt

/-- No solution has `φ = θ`. -/
theorem Spec.phi_lt_theta {A B φ θ : ℝ} (h : Spec A B φ θ) : φ < θ := by
  have hφpos := h.phi_pos
  obtain ⟨hφ, horder, hθ, hAnonneg, hBnonneg, h1, h2, h3, h4⟩ := spec_iff.mp h
  rcases lt_or_eq_of_le horder with hlt | heq
  · exact hlt
  · subst θ
    have hsin : 0 < sin φ :=
      sin_pos_of_pos_of_lt_pi hφpos (by linarith [pi_pos])
    have hid : eq1 A B φ φ = -2 * (B * sin φ) := by
      unfold eq1
      ring
    have hBprod : B * sin φ = 0 := by
      rw [hid] at h1
      linarith
    have hBzero : B = 0 := (mul_eq_zero.mp hBprod).resolve_right hsin.ne'
    have hAnonpos : A ≤ 0 := by
      unfold eq4 at h4
      rw [hBzero] at h4
      nlinarith
    have hAzero : A = 0 := le_antisymm hAnonpos hAnonneg
    have hc := cos_le_one φ
    simp only [eq3, hAzero, hBzero, zero_mul, add_zero] at h3
    exfalso
    linarith

/-!
## A first bound on `φ`

Every solution has `B ≥ A` and `φ < 1/2` (`Spec.phi_lt_half`).
-/

/-- Signs and orders of the sines and cosines on the domain. -/
theorem triangle_trig {φ θ : ℝ} (hφ : 0 ≤ φ) (horder : φ ≤ θ)
    (hθ : θ ≤ π / 4) :
    0 ≤ sin φ ∧ sin φ ≤ cos φ ∧ 0 < cos φ ∧ cos θ ≤ cos φ ∧
      0 ≤ sin θ ∧ 0 < cos θ ∧ 1 ≤ cos θ + sin θ := by
  have hθ0 := hφ.trans horder
  have hpL : φ ≤ π / 2 := by linarith [pi_pos]
  have htL : θ ≤ π / 2 := by linarith [pi_pos]
  have hpSin := sin_nonneg_of_nonneg_of_le_pi hφ (by linarith [pi_pos])
  have htSin := sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [pi_pos])
  have hpCos := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩ (x := φ)
  have htCos := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩ (x := θ)
  have hpc : sin φ ≤ cos φ := by
    have h := sin_le_sin_of_le_of_le_pi_div_two
      (x := φ) (y := π / 2 - φ) (by linarith [pi_pos])
      (by linarith) (by linarith)
    simpa only [sin_pi_div_two_sub] using h
  have hcOrder := cos_le_cos_of_nonneg_of_le_pi hφ (by linarith [pi_pos]) horder
  have hsum : 1 ≤ cos θ + sin θ := by
    have hsq := sin_sq_add_cos_sq θ
    have hmul : 0 ≤ sin θ * cos θ := mul_nonneg htSin htCos.le
    nlinarith
  exact ⟨hpSin, hpc, hpCos, hcOrder, htSin, htCos, hsum⟩

theorem offset_nonneg {φ θ : ℝ} (horder : φ ≤ θ) (hθ : θ ≤ π / 4) :
    0 ≤ offset φ θ := by
  unfold offset
  have hδ : 0 ≤ θ - φ := sub_nonneg.mpr horder
  nlinarith [sq_nonneg (θ - φ)]

/-- The fourth equation and the domain give `A ≤ B`. -/
theorem Spec.A_le_B {A B φ θ : ℝ} (h : Spec A B φ θ) : A ≤ B := by
  obtain ⟨hp, ho, ht, hA, hB, h1, h2, h3, h4⟩ := spec_iff.mp h
  have hoff := offset_nonneg ho ht
  have he := eliminate_eq4 A B φ θ
  rw [h4] at he
  have hslope : 1 ≤ slope φ θ := by unfold slope; linarith
  have hm := mul_le_mul_of_nonneg_left hslope hA
  linarith

/-- An inequality between the angles that follows from the equations. -/
theorem Spec.angle_inequality {A B φ θ : ℝ} (h : Spec A B φ θ) :
    3 * sin φ ^ 2 - cos φ * sin φ ≤ (θ - φ) * (cos φ - sin φ) := by
  obtain ⟨hp, ho, ht, hA, hB, h1, h2, h3, h4⟩ := spec_iff.mp h
  obtain ⟨hs, hsc, hc, hcc, hts, htc, hsum⟩ := triangle_trig hp ho ht
  have hab := h.A_le_B
  have hcs : 0 ≤ cos φ - sin φ := sub_nonneg.mpr hsc
  have hbase : sin φ ≤ A * (cos φ - sin φ) := by
    have hAB := mul_le_mul_of_nonneg_right hab hs
    unfold eq3 at h3
    nlinarith [cos_le_one φ]
  have hid := eliminate_B A B φ θ
  rw [h1, h3] at hid
  have hsmall : 2 * A * cos φ ≤ θ - φ + 3 * sin φ := by
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
  by_contra hlarge
  have hφlo : (1 / 2 : ℝ) ≤ φ := le_of_not_gt hlarge
  obtain ⟨hp, ho, ht, hA, hB, h1, h2, h3, h4⟩ := spec_iff.mp h
  obtain ⟨hs, hsc, hc, hcc, hts, htc, hsum⟩ := triangle_trig hp ho ht
  have hπ : π < (16 / 5 : ℝ) := by linarith [pi_lt_d2]
  have hδ : θ - φ ≤ 3 / 10 := by linarith
  have hsinHalf : (23 / 48 : ℝ) ≤ sin (1 / 2) := by
    have h := sin_ge_sub_cube (by norm_num : (0 : ℝ) ≤ 1 / 2)
    norm_num at h ⊢
    linarith
  have hsinOrder := sin_le_sin_of_le_of_le_pi_div_two
    (x := (1 / 2 : ℝ)) (y := φ) (by linarith [pi_pos])
    (by linarith [pi_pos]) hφlo
  have hslo : (23 / 48 : ℝ) ≤ sin φ := hsinHalf.trans hsinOrder
  have hprod : (θ - φ) * (cos φ - sin φ) ≤ (3 / 10) * (1 - sin φ) := by
    apply mul_le_mul hδ (sub_le_sub_right (cos_le_one φ) _)
    · exact sub_nonneg.mpr hsc
    · norm_num
  have hmul := mul_le_mul_of_nonneg_right (cos_le_one φ) hs
  have hin := h.angle_inequality
  nlinarith [sq_nonneg (sin φ - 23 / 48)]

/-!
## Derivatives of the reduced equation `reducedQ`

The partial derivatives of `reducedQ`. For `φ ≤ 1/2` its `φ`-derivative is negative
(`qPhi_neg`): it is bounded by an auxiliary function whose `θ`-derivative is a sum of nonpositive
terms and which is nonpositive on the diagonal.
-/

def gap (φ θ : ℝ) : ℝ := θ - φ

def frameDen (φ θ : ℝ) : ℝ := cos φ - slope φ θ * sin φ

def frameOffset (φ θ : ℝ) : ℝ :=
  sin φ * (1 + offset φ θ) + (1 - cos φ) / 2

def minOffset (φ θ : ℝ) : ℝ := gap φ θ / 2 + gap φ θ ^ 2 / 4

def qPhi (φ θ : ℝ) : ℝ :=
  -den φ θ * cos φ * offset φ θ -
    num φ θ * (sin φ / 2 + slope φ θ * cos φ) +
      3 * sin φ * frameOffset φ θ

def qTheta (φ θ : ℝ) : ℝ :=
  ((1 - gap φ θ) * frameDen φ θ - frameOffset φ θ) * sin θ +
    (3 * (1 - gap φ θ) * cos φ - 3 * sin φ + sin θ - 1) * sin φ / 2

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

theorem reducedQ_frame (φ θ : ℝ) :
    reducedQ φ θ = num φ θ * frameDen φ θ - den φ θ * frameOffset φ θ := by
  unfold reducedQ frameDen frameOffset
  ring

theorem num_phi_deriv (φ θ : ℝ) :
    HasDerivAt (fun p => num p θ) (den φ θ) φ := by
  have h := (((((hasDerivAt_id' φ).const_sub θ).mul_const (cos θ)).fun_add
    ((hasDerivAt_sin φ).const_mul 3)).sub_const (sin θ)).sub_const (cos θ) |>.add_const 1
  refine h.congr_deriv ?_
  unfold den
  ring

theorem num_theta_deriv (φ θ : ℝ) :
    HasDerivAt (fun t => num φ t) ((1 - gap φ θ) * sin θ) θ := by
  have h := (((((hasDerivAt_id' θ).sub_const φ).fun_mul (hasDerivAt_cos θ)).add_const
    (3 * sin φ)).fun_sub (hasDerivAt_sin θ)).fun_sub (hasDerivAt_cos θ) |>.add_const 1
  refine h.congr_deriv ?_
  unfold gap
  ring

theorem den_phi_deriv (φ θ : ℝ) :
    HasDerivAt (fun p => den p θ) (-3 * sin φ) φ := by
  have h := ((hasDerivAt_cos φ).const_mul 3).sub_const (cos θ)
  refine h.congr_deriv ?_
  ring

theorem den_theta_deriv (φ θ : ℝ) :
    HasDerivAt (fun t => den φ t) (sin θ) θ := by
  have h := (hasDerivAt_cos θ).const_sub (3 * cos φ)
  refine h.congr_deriv ?_
  ring

theorem slope_phi_deriv (φ θ : ℝ) :
    HasDerivAt (fun p => slope p θ) (-1 / 2) φ := by
  have h := (((hasDerivAt_id' φ).const_sub θ).div_const 2).const_add 1
  refine h.congr_deriv ?_
  ring

theorem slope_theta_deriv (φ θ : ℝ) :
    HasDerivAt (fun t => slope φ t) (1 / 2) θ := by
  have h := (((hasDerivAt_id' θ).sub_const φ).div_const 2).const_add 1
  refine h.congr_deriv ?_
  ring

theorem offset_phi_deriv (φ θ : ℝ) :
    HasDerivAt (fun p => offset p θ) (-slope φ θ - 1 / 2) φ := by
  have hg := (hasDerivAt_id' φ).const_sub θ
  have h := ((((hasDerivAt_id' φ).const_sub (π / 2)).sub_const θ).fun_add
    (hg.div_const 2)).fun_add ((hg.fun_pow 2).div_const 4)
  refine h.congr_deriv ?_
  unfold slope
  norm_num
  ring

theorem offset_theta_deriv (φ θ : ℝ) :
    HasDerivAt (fun t => offset φ t) ((gap φ θ - 1) / 2) θ := by
  have hg := (hasDerivAt_id' θ).sub_const φ
  have h := ((((hasDerivAt_id' θ).const_sub (π / 2 - φ))).fun_add
    (hg.div_const 2)).fun_add ((hg.fun_pow 2).div_const 4)
  refine h.congr_deriv ?_
  unfold gap
  norm_num
  ring

theorem frameDen_phi_deriv (φ θ : ℝ) :
    HasDerivAt (fun p => frameDen p θ) (-sin φ / 2 - slope φ θ * cos φ) φ := by
  have h := (hasDerivAt_cos φ).fun_sub ((slope_phi_deriv φ θ).fun_mul (hasDerivAt_sin φ))
  refine h.congr_deriv ?_
  ring

theorem frameDen_theta_deriv (φ θ : ℝ) :
    HasDerivAt (fun t => frameDen φ t) (-sin φ / 2) θ := by
  have h := ((slope_theta_deriv φ θ).mul_const (sin φ)).const_sub (cos φ)
  refine h.congr_deriv ?_
  ring

theorem frameOffset_phi_deriv (φ θ : ℝ) :
    HasDerivAt (fun p => frameOffset p θ)
      (cos φ * (1 + offset φ θ) - slope φ θ * sin φ) φ := by
  have h := ((hasDerivAt_sin φ).fun_mul ((offset_phi_deriv φ θ).const_add 1)).fun_add
    (((hasDerivAt_cos φ).const_sub 1).div_const 2)
  refine h.congr_deriv ?_
  ring

theorem frameOffset_theta_deriv (φ θ : ℝ) :
    HasDerivAt (fun t => frameOffset φ t) (sin φ * (gap φ θ - 1) / 2) θ := by
  have h := (((offset_theta_deriv φ θ).const_add 1).const_mul (sin φ)).add_const
    ((1 - cos φ) / 2)
  refine h.congr_deriv ?_
  ring

theorem reducedQ_phi_deriv (φ θ : ℝ) :
    HasDerivAt (fun p => reducedQ p θ) (qPhi φ θ) φ := by
  have hd := ((num_phi_deriv φ θ).mul (frameDen_phi_deriv φ θ)).sub
    ((den_phi_deriv φ θ).mul (frameOffset_phi_deriv φ θ))
  convert hd using 1
  · funext p
    exact reducedQ_frame p θ
  · unfold qPhi frameDen frameOffset
    ring

theorem reducedQ_theta_deriv (φ θ : ℝ) :
    HasDerivAt (fun t => reducedQ φ t) (qTheta φ θ) θ := by
  have hd := ((num_theta_deriv φ θ).mul (frameDen_theta_deriv φ θ)).sub
    ((den_theta_deriv φ θ).mul (frameOffset_theta_deriv φ θ))
  convert hd using 1
  · funext t
    exact reducedQ_frame φ t
  · unfold qTheta gap frameDen frameOffset num den slope
    ring

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

theorem qPhiMin_diagonal_nonpos {φ : ℝ} (hφ : 0 ≤ φ) (hφu : φ ≤ π / 4) :
    qPhiMin φ φ ≤ 0 := by
  obtain ⟨hs, hsc, hc, _, _, _, _⟩ := triangle_trig hφ le_rfl hφu
  have he : qPhiMin φ φ = (sin φ - cos φ) * (1 - cos φ + 2 * sin φ) := by
    unfold qPhiMin minOffset gap num den slope
    ring
  rw [he]
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hsc)
    (by linarith [cos_le_one φ])

/-- `qPhi` is bounded by the auxiliary `qPhiMin`. -/
theorem qPhi_le_min {φ θ : ℝ} (hφ : 0 ≤ φ) (hφh : φ ≤ 1 / 2)
    (horder : φ ≤ θ) (hθ : θ ≤ π / 4) : qPhi φ θ ≤ qPhiMin φ θ := by
  obtain ⟨hs, hsc, hc, hcc, hts, htc, hsum⟩ := triangle_trig hφ horder hθ
  have hsHalf : sin φ ≤ 1 / 2 := (sin_le hφ).trans hφh
  have hcLower : (7 / 8 : ℝ) ≤ cos φ := by
    have h := one_sub_sq_div_two_le_cos (x := φ)
    nlinarith
  have hden : 2 * cos φ ≤ den φ θ := by unfold den; linarith
  have hdenMul := mul_le_mul_of_nonneg_right hden hc.le
  have hcoeff : -den φ θ * cos φ + 3 * sin φ ^ 2 ≤ 0 := by nlinarith
  have hgap : 0 ≤ π / 2 - φ - θ := by linarith
  have hprod := mul_nonpos_of_nonpos_of_nonneg hcoeff hgap
  have he : qPhi φ θ - qPhiMin φ θ =
      (-den φ θ * cos φ + 3 * sin φ ^ 2) * (π / 2 - φ - θ) := by
    unfold qPhi qPhiMin frameOffset offset minOffset gap
    ring
  linarith

/-- The `φ`-derivative of `reducedQ` is negative for `φ ≤ 1/2`. -/
theorem qPhi_neg {φ θ : ℝ} (hφ : 0 ≤ φ) (hφh : φ ≤ 1 / 2)
    (horder : φ < θ) (hθ : θ ≤ π / 4) : qPhi φ θ < 0 := by
  have ha : StrictAntiOn (qPhiMin φ) (Icc φ θ) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc φ θ)
    · exact fun t _ => (qPhiMin_theta_deriv φ t).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(qPhiMin_theta_deriv φ t).deriv]
      exact qPhiMinTheta_neg hφ ht.1.le (ht.2.le.trans hθ)
  have hlt := ha ⟨le_rfl, horder.le⟩ ⟨horder.le, le_rfl⟩ horder
  exact (qPhi_le_min hφ hφh horder.le hθ).trans_lt
    (hlt.trans_le (qPhiMin_diagonal_nonpos hφ (horder.le.trans hθ)))

/-!
## Every solution has `φ < 1/20`

`reducedQ` decreases in `φ`, and at `φ = 1/20` it increases in `θ` up to a negative value at
`θ = π/4`; so it has no zero with `φ ≥ 1/20` (`Spec.phi_lt_twentieth`).
-/

theorem cut_trig :
    (499 / 10000 : ℝ) ≤ sin (1 / 20) ∧ sin (1 / 20) ≤ 1 / 20 ∧
      (499 / 500 : ℝ) ≤ cos (1 / 20) ∧ cos (1 / 20) ≤ 1 := by
  have hs := sin_ge_sub_cube (by norm_num : (0 : ℝ) ≤ 1 / 20)
  have hc := one_sub_sq_div_two_le_cos (x := (1 / 20 : ℝ))
  refine ⟨by linarith, sin_le (by norm_num), by linarith, cos_le_one _⟩

theorem cut_frame_bounds {θ : ℝ} (hl : (1 / 20 : ℝ) ≤ θ) (hu : θ ≤ π / 4) :
    (9 / 10 : ℝ) ≤ frameDen (1 / 20) θ ∧
      frameOffset (1 / 20) θ ≤ 151 / 1000 := by
  obtain ⟨hslo, hshi, hclo, hchi⟩ := cut_trig
  have hs0 : 0 ≤ sin (1 / 20 : ℝ) := by linarith
  have hd0 : 0 ≤ gap (1 / 20) θ := by unfold gap; linarith
  have hd1 : gap (1 / 20) θ ≤ 3 / 4 := by unfold gap; linarith [pi_lt_d2]
  have hk0 : 0 ≤ slope (1 / 20) θ := by unfold slope; linarith
  have hk1 : slope (1 / 20) θ ≤ 11 / 8 := by unfold slope gap at *; linarith
  have hoff : offset (1 / 20) θ ≤ 2 := by
    unfold offset
    have hsq : (θ - 1 / 20) ^ 2 ≤ 2 * (θ - 1 / 20) := by
      change 0 ≤ θ - 1 / 20 at hd0
      change θ - 1 / 20 ≤ 3 / 4 at hd1
      nlinarith
    linarith [pi_lt_four]
  have hp := mul_le_mul hk1 hshi hs0 (by norm_num : (0 : ℝ) ≤ 11 / 8)
  have hz : sin (1 / 20) * (1 + offset (1 / 20) θ) ≤ (1 / 20) * 3 := by
    apply mul_le_mul hshi (by linarith)
    · exact add_nonneg zero_le_one (offset_nonneg hl hu)
    · norm_num
  constructor
  · unfold frameDen
    linarith
  · unfold frameOffset
    linarith

theorem qTheta_cut_pos {θ : ℝ} (hl : (1 / 20 : ℝ) ≤ θ) (hu : θ ≤ π / 4) :
    0 < qTheta (1 / 20) θ := by
  obtain ⟨hslo, hshi, hclo, hchi⟩ := cut_trig
  obtain ⟨hJ, hZ⟩ := cut_frame_bounds hl hu
  have ht0 : 0 ≤ θ := by linarith
  have hsθ : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [pi_pos])
  have hd0 : 0 ≤ gap (1 / 20) θ := by unfold gap; linarith
  have hd1 : gap (1 / 20) θ ≤ 3 / 4 := by unfold gap; linarith [pi_lt_d2]
  have hUprod : (1 / 4 : ℝ) * (9 / 10) ≤
      (1 - gap (1 / 20) θ) * frameDen (1 / 20) θ := by
    apply mul_le_mul (by linarith) hJ (by norm_num)
    linarith
  have hU : 0 < (1 - gap (1 / 20) θ) * frameDen (1 / 20) θ -
      frameOffset (1 / 20) θ := by linarith
  have hC : 0 < 3 * (1 - gap (1 / 20) θ) * cos (1 / 20) -
      3 * sin (1 / 20) + sin θ - 1 := by
    by_cases ht : θ ≤ 1 / 2
    · have hd : gap (1 / 20) θ ≤ 9 / 20 := by unfold gap; linarith
      have hm : (11 / 20 : ℝ) * (499 / 500) ≤
          (1 - gap (1 / 20) θ) * cos (1 / 20) := by
        apply mul_le_mul (by linarith) hclo (by norm_num)
        linarith
      nlinarith
    · have htHalf : (1 / 2 : ℝ) ≤ θ := le_of_lt (lt_of_not_ge ht)
      have hsHalf : (23 / 48 : ℝ) ≤ sin (1 / 2) := by
        have h := sin_ge_sub_cube (by norm_num : (0 : ℝ) ≤ 1 / 2)
        linarith
      have hsOrder := sin_le_sin_of_le_of_le_pi_div_two
        (x := (1 / 2 : ℝ)) (y := θ) (by linarith [pi_pos])
        (by linarith [pi_pos]) htHalf
      have hm : (1 / 4 : ℝ) * (499 / 500) ≤
          (1 - gap (1 / 20) θ) * cos (1 / 20) := by
        apply mul_le_mul (by linarith) hclo (by norm_num)
        linarith
      nlinarith
  have hfirst := mul_nonneg hU.le hsθ
  have hsecond : 0 <
      (3 * (1 - gap (1 / 20) θ) * cos (1 / 20) - 3 * sin (1 / 20) + sin θ - 1) *
        sin (1 / 20) := mul_pos hC (by linarith)
  unfold qTheta
  linarith

/-- `reducedQ` is negative at `(1/20, π/4)`. -/
theorem reducedQ_cut_boundary_neg : reducedQ (1 / 20) (π / 4) < 0 := by
  obtain ⟨hslo, hshi, hclo, hchi⟩ := cut_trig
  have hπlo : (314 / 100 : ℝ) < π := by linarith [pi_gt_d20]
  have hπhi : π < (3144 / 1000 : ℝ) := by linarith [pi_lt_d20]
  have hdlo : (147 / 200 : ℝ) ≤ gap (1 / 20) (π / 4) := by unfold gap; linarith
  have hdhi : gap (1 / 20) (π / 4) ≤ 92 / 125 := by unfold gap; linarith
  have hu : (707 / 1000 : ℝ) ≤ cos (π / 4) ∧ cos (π / 4) ≤ 708 / 1000 := by
    rw [cos_pi_div_four]
    have hsqrt := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hsqrt0 := sqrt_nonneg (2 : ℝ)
    constructor <;> nlinarith
  have heq : sin (π / 4) = cos (π / 4) := by rw [sin_pi_div_four, cos_pi_div_four]
  have hN : num (1 / 20) (π / 4) ≤ 257 / 1000 := by
    have hm : (2 - (92 / 125 : ℝ)) * (707 / 1000) ≤
        (2 - gap (1 / 20) (π / 4)) * cos (π / 4) := by
      apply mul_le_mul (by linarith) hu.1 (by norm_num)
      linarith
    unfold num
    rw [heq]
    unfold gap at hm
    nlinarith
  have hD : (2286 / 1000 : ℝ) ≤ den (1 / 20) (π / 4) := by
    unfold den
    linarith [hu.2]
  have hJ0 := (cut_frame_bounds (θ := π / 4) (by linarith) le_rfl).1
  have hJ : frameDen (1 / 20) (π / 4) ≤ 932 / 1000 := by
    have hk : (1 + (147 / 200 : ℝ) / 2) ≤ slope (1 / 20) (π / 4) := by
      unfold slope gap at *
      linarith
    have hm := mul_le_mul hk hslo (by norm_num : (0 : ℝ) ≤ 499 / 10000)
      (by unfold slope; linarith : 0 ≤ slope (1 / 20) (π / 4))
    unfold frameDen
    nlinarith
  have hoff : (1237 / 1000 : ℝ) ≤ offset (1 / 20) (π / 4) := by
    have he : offset (1 / 20) (π / 4) =
        3 * gap (1 / 20) (π / 4) / 2 + gap (1 / 20) (π / 4) ^ 2 / 4 := by
      unfold offset gap
      ring
    rw [he]
    nlinarith
  have hZ : (111 / 1000 : ℝ) ≤ frameOffset (1 / 20) (π / 4) := by
    have hm : (499 / 10000 : ℝ) * (1 + 1237 / 1000) ≤
        sin (1 / 20) * (1 + offset (1 / 20) (π / 4)) := by
      apply mul_le_mul hslo (by linarith) (by norm_num)
      linarith
    unfold frameOffset
    linarith
  have hNJ : num (1 / 20) (π / 4) * frameDen (1 / 20) (π / 4) ≤
      (257 / 1000 : ℝ) * (932 / 1000) := by
    calc
      _ ≤ (257 / 1000) * frameDen (1 / 20) (π / 4) :=
        mul_le_mul_of_nonneg_right hN (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left hJ (by norm_num)
  have hDZ : (2286 / 1000 : ℝ) * (111 / 1000) ≤
      den (1 / 20) (π / 4) * frameOffset (1 / 20) (π / 4) := by
    apply mul_le_mul hD hZ (by norm_num)
    linarith
  rw [reducedQ_frame]
  linarith

/-- Every solution has `φ < 1/20`. -/
theorem Spec.phi_lt_twentieth {A B φ θ : ℝ} (h : Spec A B φ θ) : φ < 1 / 20 := by
  by_contra hlarge
  have hl : (1 / 20 : ℝ) ≤ φ := le_of_not_gt hlarge
  have hhalf := h.phi_lt_half
  have horder := h.phi_lt_theta
  have hθ := h.2.2.1
  have hanti : AntitoneOn (fun p => reducedQ p θ) (Icc (1 / 20) φ) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact fun p _ => (reducedQ_phi_deriv p θ).continuousAt.continuousWithinAt
    · exact fun p _ => (reducedQ_phi_deriv p θ).differentiableAt.differentiableWithinAt
    · intro p hp
      rw [interior_Icc] at hp
      rw [(reducedQ_phi_deriv p θ).deriv]
      exact (qPhi_neg (by linarith [hp.1]) (by linarith [hp.2])
        (hp.2.trans horder) hθ).le
  have hmono : MonotoneOn (reducedQ (1 / 20)) (Icc (1 / 20) (π / 4)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun t _ => (reducedQ_theta_deriv (1 / 20) t).continuousAt.continuousWithinAt
    · exact fun t _ => (reducedQ_theta_deriv (1 / 20) t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(reducedQ_theta_deriv (1 / 20) t).deriv]
      exact (qTheta_cut_pos ht.1.le ht.2.le).le
  have hfirst := hanti ⟨le_rfl, hl⟩ ⟨hl, le_rfl⟩ hl
  have hsecond := hmono ⟨hl.trans horder.le, hθ⟩
    ⟨hl.trans (horder.le.trans hθ), le_rfl⟩ hθ
  have hzero := h.reduced_zero.1
  linarith [reducedQ_cut_boundary_neg]

/-!
## The residuals `F` and `G`

`firstResidual` (`F`) and `secondResidual` (`G`) are the third and second equations with `A` and
`B` expressed through the angles, and `separatingResidual` is `H = G + (9/10) F`. Their partial
derivatives, with the common factor `C = 1 - A - (θ - φ)` of the `θ`-derivatives.
-/

def remainder (φ θ : ℝ) : ℝ := 1 - reconstructedA φ θ - gap φ θ

def firstResidual (φ θ : ℝ) : ℝ :=
  reconstructedA φ θ * cos φ - (reconstructedB φ θ + 1) * sin φ + (cos φ - 1) / 2

def secondResidual (φ θ : ℝ) : ℝ :=
  -3 * remainder φ θ * sin θ + (reconstructedA φ θ - 1) * sin φ +
    (1 - 2 * reconstructedB φ θ) * cos φ + 3 * cos θ

def separatingResidual (φ θ : ℝ) : ℝ := secondResidual φ θ + (9 / 10) * firstResidual φ θ

def armCoefficient (φ θ : ℝ) : ℝ := 3 * sin θ + sin φ - 2 * slope φ θ * cos φ

def firstPhi (φ θ : ℝ) : ℝ :=
  -reconstructedB φ θ * cos φ + reconstructedA φ θ * sin φ *
    (3 * cos φ + cos θ - 6 * slope φ θ * sin φ) / (2 * den φ θ)

def firstThetaFactor (φ θ : ℝ) : ℝ :=
  sin θ * frameDen φ θ / den φ θ + sin φ / 2

def secondPhi (φ θ : ℝ) : ℝ :=
  3 * reconstructedA φ θ * sin φ * armCoefficient φ θ / den φ θ +
    2 * reconstructedA φ θ * cos φ + 2 * reconstructedB φ θ * sin φ

def secondThetaFactor (φ θ : ℝ) : ℝ :=
  sin θ * armCoefficient φ θ / den φ θ + cos φ - 3 * cos θ

theorem firstResidual_eq (φ θ : ℝ) :
    firstResidual φ θ = eq3 (reconstructedA φ θ) (reconstructedB φ θ) φ θ := by
  unfold firstResidual eq3
  ring

theorem secondResidual_eq (φ θ : ℝ) :
    secondResidual φ θ = eq2 (reconstructedA φ θ) (reconstructedB φ θ) φ θ := by
  unfold secondResidual eq2 remainder gap
  ring

theorem Spec.residuals_zero {A B φ θ : ℝ} (h : Spec A B φ θ) :
    firstResidual φ θ = 0 ∧ separatingResidual φ θ = 0 := by
  have hA := h.coefficients.1
  have hB := h.coefficients.2
  have h2 := (spec_iff.mp h).2.2.2.2.2.2.1
  have h3 := (spec_iff.mp h).2.2.2.2.2.2.2.1
  have hF : firstResidual φ θ = 0 := by
    rw [firstResidual_eq, ← hA, ← hB]
    exact h3
  have hG : secondResidual φ θ = 0 := by
    rw [secondResidual_eq, ← hA, ← hB]
    exact h2
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
        (reconstructedA φ θ + 1) / 2) φ := by
  apply (((reconstructedA_phi_deriv φ θ hD).mul (slope_phi_deriv φ θ)).add
    (offset_phi_deriv φ θ)).congr_deriv
  ring

theorem reconstructedB_theta_deriv (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    HasDerivAt (fun t => reconstructedB φ t)
      (slope φ θ * (remainder φ θ * sin θ / den φ θ) - remainder φ θ / 2) θ := by
  apply (((reconstructedA_theta_deriv φ θ hD).mul (slope_theta_deriv φ θ)).add
    (offset_theta_deriv φ θ)).congr_deriv
  unfold remainder
  ring

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
      (remainder φ θ * firstThetaFactor φ θ) θ := by
  have hd := (((reconstructedA_theta_deriv φ θ hD).mul_const (cos φ)).sub
    (((reconstructedB_theta_deriv φ θ hD).add_const 1).mul_const (sin φ))).add_const
      ((cos φ - 1) / 2)
  apply hd.congr_deriv
  unfold firstThetaFactor frameDen
  ring

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
      (remainder φ θ * (secondThetaFactor φ θ + (9 / 10) * firstThetaFactor φ θ)) θ := by
  apply ((secondResidual_theta_deriv φ θ hD).add
    ((firstResidual_theta_deriv φ θ hD).const_mul (9 / 10))).congr_deriv
  ring

/-!
## Bounds on the triangle `0 ≤ φ ≤ 1/20`, `φ ≤ θ ≤ π/4`

Elementary bounds on the sines and cosines, on `A` and `B`, and on the other quantities of the
derivatives, on the whole triangle (`smallBounds`).
-/

def baseNumerator (t : ℝ) : ℝ := (t - 1) * cos t - sin t + 1

def numeratorMajorant (t : ℝ) : ℝ := t ^ 2 / 2 - t ^ 3 / 3

theorem baseNumerator_deriv (t : ℝ) :
    HasDerivAt baseNumerator ((1 - t) * sin t) t :=
  (((((hasDerivAt_id' t).sub_const 1).mul (hasDerivAt_cos t)).sub
    (hasDerivAt_sin t)).add_const 1).congr_deriv (by ring)

theorem numeratorMajorant_deriv (t : ℝ) :
    HasDerivAt numeratorMajorant (t * (1 - t)) t :=
  (((hasDerivAt_pow 2 t).div_const 2).sub
    ((hasDerivAt_pow 3 t).div_const 3)).congr_deriv (by norm_num; ring)

theorem baseNumerator_le_majorant {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 4 / 5) :
    baseNumerator t ≤ numeratorMajorant t := by
  have hd (u : ℝ) : HasDerivAt (fun u => numeratorMajorant u - baseNumerator u)
      ((1 - u) * (u - sin u)) u := by
    apply ((numeratorMajorant_deriv u).sub (baseNumerator_deriv u)).congr_deriv
    ring
  have hm : MonotoneOn (fun u => numeratorMajorant u - baseNumerator u) (Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun u _ => (hd u).continuousAt.continuousWithinAt
    · exact fun u _ => (hd u).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      rw [(hd u).deriv]
      exact mul_nonneg (by linarith [hu.2]) (sub_nonneg.mpr (sin_le hu.1.le))
  have h : numeratorMajorant 0 - baseNumerator 0 ≤ numeratorMajorant t - baseNumerator t :=
    hm ⟨le_rfl, ht0⟩ ⟨ht0, le_rfl⟩ ht0
  have h0 : numeratorMajorant 0 - baseNumerator 0 = 0 := by
    norm_num [numeratorMajorant, baseNumerator]
  linarith

theorem baseNumerator_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 4 / 5) :
    baseNumerator t ≤ 3 / 20 := by
  have hm : MonotoneOn numeratorMajorant (Icc 0 (4 / 5)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun u _ => (numeratorMajorant_deriv u).continuousAt.continuousWithinAt
    · exact fun u _ => (numeratorMajorant_deriv u).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      rw [(numeratorMajorant_deriv u).deriv]
      exact mul_nonneg hu.1.le (by linarith [hu.2])
  have h : numeratorMajorant t ≤ numeratorMajorant (4 / 5) :=
    hm ⟨ht0, ht1⟩ ⟨by norm_num, le_rfl⟩ ht1
  have h45 : numeratorMajorant (4 / 5) = 56 / 375 := by norm_num [numeratorMajorant]
  have hbase := baseNumerator_le_majorant ht0 ht1
  linarith

theorem num_nonneg {φ θ : ℝ} (hφ : 0 ≤ φ) (ho : φ ≤ θ) (ht : θ ≤ π / 4) :
    0 ≤ num φ θ := by
  have hm : MonotoneOn (num φ) (Icc φ θ) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun t _ => (num_theta_deriv φ t).continuousAt.continuousWithinAt
    · exact fun t _ => (num_theta_deriv φ t).differentiableAt.differentiableWithinAt
    · intro t ht'
      rw [interior_Icc] at ht'
      rw [(num_theta_deriv φ t).deriv]
      apply mul_nonneg
      · unfold gap
        linarith [pi_lt_four, ht'.2]
      · exact sin_nonneg_of_nonneg_of_le_pi (hφ.trans ht'.1.le)
          (by linarith [ht'.2, pi_pos])
  have hc := cos_le_one φ
  have hs := (triangle_trig hφ ho ht).1
  have hdiag : 0 ≤ num φ φ := by unfold num; nlinarith
  exact hdiag.trans (hm ⟨le_rfl, ho⟩ ⟨ho, le_rfl⟩ ho)

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

/-- The bounds of `SmallBounds` hold on the whole triangle. -/
theorem smallBounds {φ θ : ℝ} (hp0 : 0 ≤ φ) (hp1 : φ ≤ 1 / 20)
    (ho : φ ≤ θ) (ht : θ ≤ π / 4) : SmallBounds φ θ := by
  obtain ⟨hs0, hsc, hc0, hcc, hts0, htc0, hsum⟩ := triangle_trig hp0 ho ht
  have hs1 : sin φ ≤ 1 / 20 := (sin_le hp0).trans hp1
  have hc1 : (499 / 500 : ℝ) ≤ cos φ := by
    have h := one_sub_sq_div_two_le_cos (x := φ)
    nlinarith
  have hθ0 : 0 ≤ θ := hp0.trans ho
  have hθ1 : θ ≤ 4 / 5 := by linarith [pi_lt_d2]
  have hts1 : sin θ ≤ 4 / 5 := (sin_le hθ0).trans hθ1
  have htc1 : (7 / 10 : ℝ) ≤ cos θ := by
    have horder := cos_le_cos_of_nonneg_of_le_pi hθ0
      (show π / 4 ≤ π by linarith [pi_pos]) ht
    rw [cos_pi_div_four] at horder
    have hsqrt := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hsqrt0 := sqrt_nonneg (2 : ℝ)
    nlinarith
  have hd0 : 0 ≤ gap φ θ := sub_nonneg.mpr ho
  have hd1 : gap φ θ ≤ 4 / 5 := by unfold gap; linarith
  have hk0 : 1 ≤ slope φ θ := by unfold slope; linarith
  have hk1 : slope φ θ ≤ 7 / 5 := by unfold slope gap at *; linarith
  have hD0 : (199 / 100 : ℝ) ≤ den φ θ := by unfold den; linarith [cos_le_one θ]
  have hD1 : den φ θ ≤ 23 / 10 := by unfold den; linarith [cos_le_one φ]
  have hDpos : 0 < den φ θ := by linarith
  have hN0 := num_nonneg hp0 ho ht
  have hN1 : num φ θ ≤ 3 / 10 := by
    have hbase := baseNumerator_le hθ0 hθ1
    have hneg : 0 ≤ φ * cos θ := mul_nonneg hp0 htc0.le
    have he : num φ θ = baseNumerator θ - φ * cos θ + 3 * sin φ := by
      unfold num baseNumerator
      ring
    rw [he]
    linarith
  have hA0 : 0 ≤ reconstructedA φ θ := div_nonneg hN0 hDpos.le
  have hA1 : reconstructedA φ θ ≤ 4 / 25 := by
    apply (div_le_iff₀ hDpos).mpr
    linarith
  have hoff0 := offset_nonneg ho ht
  have hoffLow : (7 / 10 : ℝ) ≤ offset φ θ := by
    unfold offset
    have hδ := sub_nonneg.mpr ho
    nlinarith [sq_nonneg (θ - φ), pi_gt_three]
  have hoffHigh : offset φ θ ≤ 8 / 5 := by
    unfold offset
    change 0 ≤ θ - φ at hd0
    change θ - φ ≤ 4 / 5 at hd1
    have hsq : (θ - φ) ^ 2 ≤ 2 * (θ - φ) := by nlinarith
    linarith [pi_lt_d2]
  have hAB : reconstructedA φ θ * slope φ θ ≤ (4 / 25 : ℝ) * (7 / 5) :=
    mul_le_mul hA1 hk1 (by linarith) (by norm_num)
  have hB0 : (7 / 10 : ℝ) ≤ reconstructedB φ θ := by
    have hm := mul_nonneg hA0 (show 0 ≤ slope φ θ by linarith)
    unfold reconstructedB
    linarith
  have hB1 : reconstructedB φ θ ≤ 2 := by unfold reconstructedB; linarith
  have hJs : slope φ θ * sin φ ≤ (7 / 5 : ℝ) * (1 / 20) :=
    mul_le_mul hk1 hs1 hs0 (by norm_num)
  have hJ0 : (9 / 10 : ℝ) ≤ frameDen φ θ := by unfold frameDen; linarith
  have hJ1 : frameDen φ θ ≤ 1 := by
    have hm := mul_nonneg (show 0 ≤ slope φ θ by linarith) hs0
    unfold frameDen
    linarith [cos_le_one φ]
  refine ⟨⟨hs0, hs1⟩, ⟨hc1, cos_le_one _⟩, ⟨hts0, hts1⟩,
    ⟨htc1, cos_le_one _⟩, hsum, ⟨hk0, hk1⟩,
    ⟨hD0, hD1⟩, ⟨hA0, hA1⟩, ⟨hB0, hB1⟩, ⟨hJ0, hJ1⟩, ?_⟩
  unfold remainder
  linarith

/-!
## The signs of the partial derivatives

On the triangle, `∂F/∂φ ≤ -2/3`, `0 ≤ (∂F/∂θ)/C ≤ 1/2`, `∂G/∂φ ≤ 3/5` and `(∂G/∂θ)/C ≤ -2/3`, where
`C > 0`. So `H` decreases in `φ` and strictly in `θ` (`separating_signs`).
-/

namespace SmallBounds

variable {φ θ : ℝ} (b : SmallBounds φ θ)
include b

private theorem den_pos : 0 < den φ θ := by linarith [b.den_mem.1]

private theorem A_sin_bounds :
    0 ≤ reconstructedA φ θ * sin φ ∧
      reconstructedA φ θ * sin φ ≤ 1 / 125 := by
  refine ⟨mul_nonneg b.A_mem.1 b.sin_phi.1, ?_⟩
  have h := mul_le_mul b.A_mem.2 b.sin_phi.2 b.sin_phi.1
    (by norm_num : (0 : ℝ) ≤ 4 / 25)
  norm_num at h
  exact h

theorem firstPhi_le : firstPhi φ θ ≤ -2 / 3 := by
  obtain ⟨has0, has1⟩ := b.A_sin_bounds
  have hks : 0 ≤ slope φ θ * sin φ :=
    mul_nonneg (by linarith [b.slope_mem.1]) b.sin_phi.1
  have hT : 3 * cos φ + cos θ - 6 * slope φ θ * sin φ ≤ 4 := by
    linarith [b.cos_phi.2, b.cos_theta.2]
  have hnum : reconstructedA φ θ * sin φ *
      (3 * cos φ + cos θ - 6 * slope φ θ * sin φ) ≤ 4 / 125 := by
    have h := mul_le_mul_of_nonneg_left hT has0
    nlinarith
  have hcor : reconstructedA φ θ * sin φ *
      (3 * cos φ + cos θ - 6 * slope φ θ * sin φ) / (2 * den φ θ) ≤ 1 / 100 := by
    apply (div_le_iff₀ (show 0 < 2 * den φ θ by linarith [b.den_pos])).mpr
    linarith [b.den_mem.1]
  have hmain : (7 / 10 : ℝ) * (499 / 500) ≤ reconstructedB φ θ * cos φ := by
    apply mul_le_mul b.B_mem.1 b.cos_phi.1 (by norm_num)
    linarith [b.B_mem.1]
  unfold firstPhi
  linarith

theorem firstThetaFactor_bounds :
    0 ≤ firstThetaFactor φ θ ∧ firstThetaFactor φ θ ≤ 1 / 2 := by
  have hJ0 : 0 ≤ frameDen φ θ := by linarith [b.frame_mem.1]
  have hquot0 := div_nonneg (mul_nonneg b.sin_theta.1 hJ0) b.den_pos.le
  have hnum : sin θ * frameDen φ θ ≤ 4 / 5 := by
    have h := mul_le_mul_of_nonneg_left b.frame_mem.2 b.sin_theta.1
    nlinarith [b.sin_theta.2]
  have hquot : sin θ * frameDen φ θ / den φ θ ≤ 9 / 20 := by
    apply (div_le_iff₀ b.den_pos).mpr
    linarith [b.den_mem.1]
  unfold firstThetaFactor
  constructor <;> linarith [b.sin_phi.1, b.sin_phi.2]

theorem secondPhi_le : secondPhi φ θ ≤ 3 / 5 := by
  obtain ⟨has0, has1⟩ := b.A_sin_bounds
  have hkcos : 0 ≤ slope φ θ * cos φ :=
    mul_nonneg (by linarith [b.slope_mem.1]) (by linarith [b.cos_phi.1])
  have hH : armCoefficient φ θ ≤ 5 / 2 := by
    unfold armCoefficient
    linarith [b.sin_theta.2, b.sin_phi.2]
  have hnum : 3 * reconstructedA φ θ * sin φ * armCoefficient φ θ ≤ 3 / 50 := by
    have h := mul_le_mul_of_nonneg_left hH (show 0 ≤ 3 * reconstructedA φ θ * sin φ by nlinarith)
    nlinarith
  have hquot : 3 * reconstructedA φ θ * sin φ * armCoefficient φ θ / den φ θ ≤ 1 / 25 := by
    apply (div_le_iff₀ b.den_pos).mpr
    linarith [b.den_mem.1]
  have hac : reconstructedA φ θ * cos φ ≤ 4 / 25 := by
    have h := mul_le_mul_of_nonneg_left b.cos_phi.2 b.A_mem.1
    nlinarith [b.A_mem.2]
  have hbs : reconstructedB φ θ * sin φ ≤ 1 / 10 := by
    have h := mul_le_mul b.B_mem.2 b.sin_phi.2 b.sin_phi.1 (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at h
    exact h
  unfold secondPhi
  linarith

theorem secondThetaFactor_le : secondThetaFactor φ θ ≤ -2 / 3 := by
  have hD := b.den_pos
  have hid := secondThetaFactor_identity φ θ hD.ne'
  have hc0 : 0 ≤ cos φ := by linarith [b.cos_phi.1]
  have hcSq : cos φ ^ 2 ≤ 1 := by nlinarith [b.cos_phi.1, b.cos_phi.2]
  have hsmall : sin φ * sin θ ≤ sin θ / 20 := by
    have h := mul_le_mul_of_nonneg_right b.sin_phi.2 b.sin_theta.1
    nlinarith
  have hcos : (499 / 50 : ℝ) * cos θ ≤ 10 * cos φ * cos θ := by
    have h := mul_le_mul_of_nonneg_right b.cos_phi.1
      (show 0 ≤ cos θ by linarith [b.cos_theta.1])
    nlinarith
  have hkc : (499 / 500 : ℝ) ≤ slope φ θ * cos φ := by
    have h := mul_le_mul_of_nonneg_right b.slope_mem.1 hc0
    nlinarith [b.cos_phi.1]
  have hsin : (499 / 250 : ℝ) * sin θ ≤ 2 * slope φ θ * cos φ * sin θ := by
    have h := mul_le_mul_of_nonneg_right hkc b.sin_theta.1
    nlinarith
  have hsum : (37849 / 5000 : ℝ) ≤ (499 / 50) * cos θ + (973 / 500) * sin θ := by
    nlinarith [b.trig_sum, b.cos_theta.1]
  have hnum : den φ θ * secondThetaFactor φ θ ≤ -7849 / 5000 := by
    nlinarith
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
  refine ⟨by linarith, mul_neg_of_pos_of_neg b.remainder_pos (by linarith)⟩

end SmallBounds

/-!
## Uniqueness

If two solutions had `θ < θ'`, then `F(φ, θ') ≥ F(φ, θ) = 0` would force `φ ≤ φ'`, and then
`H(φ', θ') ≤ H(φ, θ') < H(φ, θ) = 0`, a contradiction (`angles_unique`, `spec_unique`).
-/

private theorem first_horizontal {b θ : ℝ}
    (hb1 : b ≤ 1 / 20) (hbθ : b ≤ θ) (hθ : θ ≤ π / 4) :
    StrictAntiOn (fun p => firstResidual p θ) (Icc 0 b) := by
  have hd : ∀ p ∈ Icc 0 b,
      HasDerivAt (fun p => firstResidual p θ) (firstPhi p θ) p := by
    intro p hp
    exact firstResidual_phi_deriv p θ (den_pos hp.1 (hp.2.trans hbθ) hθ).ne'
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact fun p hp => (hd p hp).continuousAt.continuousWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    rw [(hd p ⟨hp.1.le, hp.2.le⟩).deriv]
    have h := (smallBounds hp.1.le (hp.2.le.trans hb1) (hp.2.le.trans hbθ) hθ).firstPhi_le
    linarith

private theorem first_vertical {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1 / 20) :
    MonotoneOn (firstResidual φ) (Icc φ (π / 4)) := by
  have hd : ∀ t ∈ Icc φ (π / 4), HasDerivAt (firstResidual φ)
      (remainder φ t * firstThetaFactor φ t) t := by
    intro t ht
    exact firstResidual_theta_deriv φ t (den_pos hφ0 ht.1 ht.2).ne'
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hd t ⟨ht.1.le, ht.2.le⟩).deriv]
    have b := smallBounds hφ0 hφ1 ht.1.le ht.2.le
    exact mul_nonneg b.remainder_pos.le b.firstThetaFactor_bounds.1

private theorem separating_horizontal {b θ : ℝ}
    (hb1 : b ≤ 1 / 20) (hbθ : b ≤ θ) (hθ : θ ≤ π / 4) :
    AntitoneOn (fun p => separatingResidual p θ) (Icc 0 b) := by
  have hd : ∀ p ∈ Icc 0 b, HasDerivAt (fun p => separatingResidual p θ)
      (secondPhi p θ + (9 / 10) * firstPhi p θ) p := by
    intro p hp
    exact separatingResidual_phi_deriv p θ (den_pos hp.1 (hp.2.trans hbθ) hθ).ne'
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · exact fun p hp => (hd p hp).continuousAt.continuousWithinAt
  · intro p hp
    exact (hd p (interior_subset hp)).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    rw [(hd p ⟨hp.1.le, hp.2.le⟩).deriv]
    exact (smallBounds hp.1.le (hp.2.le.trans hb1) (hp.2.le.trans hbθ) hθ).separating_signs.1

private theorem separating_vertical {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1 / 20) :
    StrictAntiOn (separatingResidual φ) (Icc φ (π / 4)) := by
  have hd : ∀ t ∈ Icc φ (π / 4), HasDerivAt (separatingResidual φ)
      (remainder φ t * (secondThetaFactor φ t + (9 / 10) * firstThetaFactor φ t)) t := by
    intro t ht
    exact separatingResidual_theta_deriv φ t (den_pos hφ0 ht.1 ht.2).ne'
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hd t ⟨ht.1.le, ht.2.le⟩).deriv]
    exact (smallBounds hφ0 hφ1 ht.1.le ht.2.le).separating_signs.2

/-- Two roots cannot be strictly ordered in their second coordinate. -/
private theorem not_theta_lt {A B φ θ A' B' φ' θ' : ℝ}
    (h : Spec A B φ θ) (h' : Spec A' B' φ' θ') : ¬ θ < θ' := by
  intro htt
  have hp0 := h.phi_pos.le
  have hp1 := h.phi_lt_twentieth.le
  have hpθ := h.phi_lt_theta.le
  have ht1 := h.2.2.1
  have hp'0 := h'.phi_pos.le
  have hp'1 := h'.phi_lt_twentieth.le
  have hp'θ := h'.phi_lt_theta.le
  have ht'1 := h'.2.2.1
  obtain ⟨hF, hH⟩ := h.residuals_zero
  obtain ⟨hF', hH'⟩ := h'.residuals_zero
  have hFgrow : 0 ≤ firstResidual φ θ' := by
    have hh := first_vertical hp0 hp1
      ⟨hpθ, ht1⟩ ⟨hpθ.trans htt.le, ht'1⟩ htt.le
    rwa [hF] at hh
  have hpp : φ ≤ φ' := by
    by_contra hn
    have hlt : φ' < φ := lt_of_not_ge hn
    have hh : firstResidual φ θ' < firstResidual φ' θ' :=
      first_horizontal hp1 (hpθ.trans htt.le) ht'1 ⟨hp'0, hlt.le⟩ ⟨hp0, le_rfl⟩ hlt
    rw [hF'] at hh
    linarith
  have hHshrink : separatingResidual φ θ' < 0 := by
    have hh := separating_vertical hp0 hp1
      ⟨hpθ, ht1⟩ ⟨hpθ.trans htt.le, ht'1⟩ htt
    rwa [hH] at hh
  have hHphi : separatingResidual φ' θ' ≤ separatingResidual φ θ' :=
    separating_horizontal hp'1 hp'θ ht'1 ⟨hp0, hpp⟩ ⟨hp'0, le_rfl⟩ hpp
  rw [hH'] at hHphi
  linarith

/-- Two solutions have the same angles. -/
theorem angles_unique {A B φ θ A' B' φ' θ' : ℝ}
    (h : Spec A B φ θ) (h' : Spec A' B' φ' θ') : φ = φ' ∧ θ = θ' := by
  have ht : θ = θ' := le_antisymm (le_of_not_gt (not_theta_lt h' h))
    (le_of_not_gt (not_theta_lt h h'))
  subst θ'
  have hb1 : max φ φ' ≤ 1 / 20 := max_le h.phi_lt_twentieth.le h'.phi_lt_twentieth.le
  have hbθ : max φ φ' ≤ θ := max_le h.phi_lt_theta.le h'.phi_lt_theta.le
  have ha := first_horizontal hb1 hbθ h.2.2.1
  have heq : firstResidual φ θ = firstResidual φ' θ :=
    h.residuals_zero.1.trans h'.residuals_zero.1.symm
  exact ⟨ha.injOn ⟨h.phi_pos.le, le_max_left _ _⟩
    ⟨h'.phi_pos.le, le_max_right _ _⟩ heq, rfl⟩

/-- Gerver's system has at most one solution. -/
theorem spec_unique {A B φ θ A' B' φ' θ' : ℝ}
    (h : Spec A B φ θ) (h' : Spec A' B' φ' θ') :
    A = A' ∧ B = B' ∧ φ = φ' ∧ θ = θ' := by
  obtain ⟨hp, ht⟩ := angles_unique h h'
  subst φ' θ'
  obtain ⟨ha, hb⟩ := coefficients_unique h h'
  exact ⟨ha, hb, rfl, rfl⟩

end GerverConstants

end MovingSofaBridge
