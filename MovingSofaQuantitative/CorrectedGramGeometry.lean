module

public import MovingSofaQuantitative.AugmentedGram

/-!
# The positive corrected Gram form

Uncompiled proof source. These identities justify the interval checker's
centered-triangle fallback. A box meeting cos(t)=cos(u)=0 must not divide by
the quotient denominator. Positivity of the corrected form gives a valid
pair estimate from two diagonal bounds instead.
-/

@[expose] public section
noncomputable section

open Real
open scoped RealInnerProductSpace

namespace MovingSofaQuantitative

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The bilinear form after accounting for both auxiliary penalties. -/
def correctedInner (d₁ d₂ : ℝ) (v₁ v₂ k l : E) : ℝ :=
  ⟪k, l⟫_ℝ - inverseCoefficient1 d₁ d₂ v₁ v₂ k * ⟪l, v₁⟫_ℝ -
    inverseCoefficient2 d₁ d₂ v₁ v₂ k * ⟪l, v₂⟫_ℝ

def correctedSquare (d₁ d₂ : ℝ) (v₁ v₂ k : E) : ℝ :=
  correctedInner d₁ d₂ v₁ v₂ k k

theorem inverseCoefficient1_add (d₁ d₂ : ℝ) (v₁ v₂ k l : E) :
    inverseCoefficient1 d₁ d₂ v₁ v₂ (k + l) =
      inverseCoefficient1 d₁ d₂ v₁ v₂ k + inverseCoefficient1 d₁ d₂ v₁ v₂ l := by
  unfold inverseCoefficient1
  rw [inner_add_left, inner_add_left]
  ring

theorem inverseCoefficient2_add (d₁ d₂ : ℝ) (v₁ v₂ k l : E) :
    inverseCoefficient2 d₁ d₂ v₁ v₂ (k + l) =
      inverseCoefficient2 d₁ d₂ v₁ v₂ k + inverseCoefficient2 d₁ d₂ v₁ v₂ l := by
  unfold inverseCoefficient2
  rw [inner_add_left, inner_add_left]
  ring

theorem inverseCoefficient1_smul (d₁ d₂ a : ℝ) (v₁ v₂ k : E) :
    inverseCoefficient1 d₁ d₂ v₁ v₂ (a • k) =
      a * inverseCoefficient1 d₁ d₂ v₁ v₂ k := by
  simp only [inverseCoefficient1, real_inner_smul_left]
  ring

theorem inverseCoefficient2_smul (d₁ d₂ a : ℝ) (v₁ v₂ k : E) :
    inverseCoefficient2 d₁ d₂ v₁ v₂ (a • k) =
      a * inverseCoefficient2 d₁ d₂ v₁ v₂ k := by
  simp only [inverseCoefficient2, real_inner_smul_left]
  ring

theorem correctedInner_symm (d₁ d₂ : ℝ) (v₁ v₂ k l : E) :
    correctedInner d₁ d₂ v₁ v₂ k l = correctedInner d₁ d₂ v₁ v₂ l k := by
  unfold correctedInner inverseCoefficient1 inverseCoefficient2
  rw [real_inner_comm l k]
  ring

theorem correctedInner_add_left (d₁ d₂ : ℝ) (v₁ v₂ k l m : E) :
    correctedInner d₁ d₂ v₁ v₂ (k + l) m =
      correctedInner d₁ d₂ v₁ v₂ k m + correctedInner d₁ d₂ v₁ v₂ l m := by
  simp only [correctedInner, inner_add_left, inverseCoefficient1_add, inverseCoefficient2_add]
  ring

theorem correctedInner_smul_left (d₁ d₂ a : ℝ) (v₁ v₂ k l : E) :
    correctedInner d₁ d₂ v₁ v₂ (a • k) l = a * correctedInner d₁ d₂ v₁ v₂ k l := by
  simp only [correctedInner, real_inner_smul_left, inverseCoefficient1_smul, inverseCoefficient2_smul]
  ring

theorem correctedInner_add_right (d₁ d₂ : ℝ) (v₁ v₂ k l m : E) :
    correctedInner d₁ d₂ v₁ v₂ k (l + m) =
      correctedInner d₁ d₂ v₁ v₂ k l + correctedInner d₁ d₂ v₁ v₂ k m := by
  simp only [correctedInner, inner_add_right]
  ring

theorem correctedInner_smul_right (d₁ d₂ a : ℝ) (v₁ v₂ k l : E) :
    correctedInner d₁ d₂ v₁ v₂ k (a • l) = a * correctedInner d₁ d₂ v₁ v₂ k l := by
  simp only [correctedInner, real_inner_smul_right]
  ring

theorem correctedSquare_nonneg {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (v₁ v₂ k : E) : 0 ≤ correctedSquare d₁ d₂ v₁ v₂ k := by
  obtain ⟨h1, h2⟩ := inverseCoefficient_equations hd₁ hd₂ v₁ v₂ k
  have h := corrected_norm_identity v₁ v₂ k h1 h2
  unfold correctedSquare correctedInner
  rw [real_inner_self_eq_norm_sq, ← h]
  positivity

theorem correctedSquare_combo (d₁ d₂ a b : ℝ) (v₁ v₂ k l : E) :
    correctedSquare d₁ d₂ v₁ v₂ (a • k + b • l) =
      a ^ 2 * correctedSquare d₁ d₂ v₁ v₂ k +
      2 * a * b * correctedInner d₁ d₂ v₁ v₂ k l +
      b ^ 2 * correctedSquare d₁ d₂ v₁ v₂ l := by
  unfold correctedSquare
  simp only [correctedInner_add_left, correctedInner_add_right,
    correctedInner_smul_left, correctedInner_smul_right]
  rw [correctedInner_symm d₁ d₂ v₁ v₂ l k]
  ring

/-- Cauchy--Schwarz for the corrected continuum form. -/
theorem correctedInner_sq_le {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (v₁ v₂ k l : E) :
    correctedInner d₁ d₂ v₁ v₂ k l ^ 2 ≤
      correctedSquare d₁ d₂ v₁ v₂ k * correctedSquare d₁ d₂ v₁ v₂ l := by
  have h : ∀ a : ℝ, 0 ≤ correctedSquare d₁ d₂ v₁ v₂ l * (a * a) +
      (2 * correctedInner d₁ d₂ v₁ v₂ k l) * a + correctedSquare d₁ d₂ v₁ v₂ k := by
    intro a
    have hp := correctedSquare_nonneg hd₁ hd₂ v₁ v₂ (1 • k + a • l)
    rw [correctedSquare_combo] at hp
    nlinarith only [hp]
  have hdisc := discrim_le_zero h
  rw [discrim] at hdisc
  nlinarith only [hdisc]

/-- Two diagonal bounds control every weighted pair, without division by
|a|+|b| and hence also when both coefficients vanish. -/
theorem corrected_pair_of_diagonal {d₁ d₂ C : ℝ}
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (v₁ v₂ k l : E)
    (hk : 2 * correctedSquare d₁ d₂ v₁ v₂ k ≤ C ^ 2)
    (hl : 2 * correctedSquare d₁ d₂ v₁ v₂ l ≤ C ^ 2) (a b : ℝ) :
    2 * correctedSquare d₁ d₂ v₁ v₂ (a • k + b • l) ≤
      (C * (|a| + |b|)) ^ 2 := by
  let Nk := correctedSquare d₁ d₂ v₁ v₂ k
  let Nl := correctedSquare d₁ d₂ v₁ v₂ l
  let B := correctedInner d₁ d₂ v₁ v₂ k l
  have hNk : 0 ≤ Nk := correctedSquare_nonneg hd₁ hd₂ v₁ v₂ k
  have hNl : 0 ≤ Nl := correctedSquare_nonneg hd₁ hd₂ v₁ v₂ l
  have hcs : B ^ 2 ≤ Nk * Nl := correctedInner_sq_le hd₁ hd₂ v₁ v₂ k l
  have hprod : Nk * Nl ≤ (C ^ 2 / 2) ^ 2 := by
    have h1 : Nk ≤ C ^ 2 / 2 := by linarith only [hk]
    have h2 : Nl ≤ C ^ 2 / 2 := by linarith only [hl]
    exact (mul_le_mul h1 h2 hNl (by positivity)).trans_eq (by ring)
  have hB : 2 * |B| ≤ C ^ 2 := by
    nlinarith [abs_nonneg B, sq_abs B, sq_nonneg C]
  have hm := mul_le_mul_of_nonneg_left hB (mul_nonneg (abs_nonneg a) (abs_nonneg b))
  have hcross : a * b * B ≤ |a| * |b| * |B| := by
    simpa only [abs_mul] using le_abs_self (a * b * B)
  have hka := mul_le_mul_of_nonneg_left hk (sq_nonneg a)
  have hlb := mul_le_mul_of_nonneg_left hl (sq_nonneg b)
  rw [correctedSquare_combo]
  nlinarith only [hm, hcross, hka, hlb, sq_abs a, sq_abs b]

end MovingSofaQuantitative
