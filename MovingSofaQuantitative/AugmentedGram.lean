module

public import MovingSofaStability.CapEstimate
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Two auxiliary penalties strengthen an evaluation bound

Uncompiled proof source. This is a continuum Hilbert-space inequality, not a
Galerkin computation. The two-dimensional inverse only chooses the optimal
linear combination of two penalty representers. The residual vector remains
arbitrary in the entire real inner-product space.
-/

@[expose] public section
noncomputable section

open Real
open scoped RealInnerProductSpace
open MovingSofaStability

namespace MovingSofaQuantitative

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The original squared norm together with two endpoint penalties. -/
def augmentedEnergy (d₁ d₂ e₁ e₂ : ℝ) (v₁ v₂ r : E) : ℝ :=
  ‖r‖ ^ 2 + (⟪v₁, r⟫_ℝ - e₁) ^ 2 / d₁ + (⟪v₂, r⟫_ℝ - e₂) ^ 2 / d₂

def gram11 (d₁ : ℝ) (v₁ : E) : ℝ := d₁ + ‖v₁‖ ^ 2
def gram22 (d₂ : ℝ) (v₂ : E) : ℝ := d₂ + ‖v₂‖ ^ 2
def gram12 (v₁ v₂ : E) : ℝ := ⟪v₁, v₂⟫_ℝ

def gramDet (d₁ d₂ : ℝ) (v₁ v₂ : E) : ℝ :=
  gram11 d₁ v₁ * gram22 d₂ v₂ - gram12 v₁ v₂ ^ 2

def inverseCoefficient1 (d₁ d₂ : ℝ) (v₁ v₂ k : E) : ℝ :=
  (gram22 d₂ v₂ * ⟪k, v₁⟫_ℝ - gram12 v₁ v₂ * ⟪k, v₂⟫_ℝ) / gramDet d₁ d₂ v₁ v₂

def inverseCoefficient2 (d₁ d₂ : ℝ) (v₁ v₂ k : E) : ℝ :=
  (gram11 d₁ v₁ * ⟪k, v₂⟫_ℝ - gram12 v₁ v₂ * ⟪k, v₁⟫_ℝ) / gramDet d₁ d₂ v₁ v₂

private theorem inner_square_bound (x y : E) : ⟪x, y⟫_ℝ ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have h := abs_real_inner_le_norm x y
  have hn : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [sq_abs ⟪x, y⟫_ℝ, abs_nonneg ⟪x, y⟫_ℝ]

/-- Strict positivity comes from the two positive penalty weights, even if
the two representers are linearly dependent or zero. -/
theorem gramDet_pos {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (v₁ v₂ : E) :
    0 < gramDet d₁ d₂ v₁ v₂ := by
  have hcs := inner_square_bound v₁ v₂
  have h1 := mul_nonneg hd₁.le (sq_nonneg ‖v₂‖)
  have h2 := mul_nonneg hd₂.le (sq_nonneg ‖v₁‖)
  have h3 := mul_pos hd₁ hd₂
  unfold gramDet gram11 gram22 gram12
  nlinarith only [hcs, h1, h2, h3]

theorem inverseCoefficient_equations {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (v₁ v₂ k : E) :
    gram11 d₁ v₁ * inverseCoefficient1 d₁ d₂ v₁ v₂ k +
      gram12 v₁ v₂ * inverseCoefficient2 d₁ d₂ v₁ v₂ k = ⟪k, v₁⟫_ℝ ∧
    gram12 v₁ v₂ * inverseCoefficient1 d₁ d₂ v₁ v₂ k +
      gram22 d₂ v₂ * inverseCoefficient2 d₁ d₂ v₁ v₂ k = ⟪k, v₂⟫_ℝ := by
  have hd := (gramDet_pos hd₁ hd₂ v₁ v₂).ne'
  constructor <;> unfold inverseCoefficient1 inverseCoefficient2 <;>
    field_simp [hd] <;> unfold gramDet <;> ring

private theorem norm_sub_two_sq (k v₁ v₂ : E) (a₁ a₂ : ℝ) :
    ‖k - a₁ • v₁ - a₂ • v₂‖ ^ 2 = ‖k‖ ^ 2 - 2 * a₁ * ⟪k, v₁⟫_ℝ -
      2 * a₂ * ⟪k, v₂⟫_ℝ + a₁ ^ 2 * ‖v₁‖ ^ 2 +
      2 * a₁ * a₂ * ⟪v₁, v₂⟫_ℝ + a₂ ^ 2 * ‖v₂‖ ^ 2 := by
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_sub_left, real_inner_smul_left, real_inner_smul_right]
  ring

/-- Completing squares identifies the corrected norm without subtracting a
possibly negative numerical artifact. -/
theorem corrected_norm_identity {d₁ d₂ a₁ a₂ : ℝ} (v₁ v₂ k : E)
    (h1 : gram11 d₁ v₁ * a₁ + gram12 v₁ v₂ * a₂ = ⟪k, v₁⟫_ℝ)
    (h2 : gram12 v₁ v₂ * a₁ + gram22 d₂ v₂ * a₂ = ⟪k, v₂⟫_ℝ) :
    ‖k - a₁ • v₁ - a₂ • v₂‖ ^ 2 + d₁ * a₁ ^ 2 + d₂ * a₂ ^ 2 =
      ‖k‖ ^ 2 - a₁ * ⟪k, v₁⟫_ℝ - a₂ * ⟪k, v₂⟫_ℝ := by
  rw [norm_sub_two_sq]
  unfold gram11 gram22 gram12 at h1 h2
  linear_combination a₁ * h1 + a₂ * h2

/-- Weighted evaluation from the exact augmented energy. -/
theorem augmented_evaluation_sq {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (v₁ v₂ k r : E) (a₁ a₂ e₁ e₂ : ℝ) :
    (⟪k, r⟫_ℝ - a₁ * e₁ - a₂ * e₂) ^ 2 ≤
      (‖k - a₁ • v₁ - a₂ • v₂‖ ^ 2 + d₁ * a₁ ^ 2 + d₂ * a₂ ^ 2) *
        augmentedEnergy d₁ d₂ e₁ e₂ v₁ v₂ r := by
  let k' := k - a₁ • v₁ - a₂ • v₂
  let z₁ := ⟪v₁, r⟫_ℝ - e₁
  let z₂ := ⟪v₂, r⟫_ℝ - e₂
  have h0 : SquareControl ⟪k', r⟫_ℝ (‖k'‖ ^ 2) (‖r‖ ^ 2) :=
    ⟨sq_nonneg _, sq_nonneg _, inner_square_bound k' r⟩
  have h1 : SquareControl (a₁ * z₁) (d₁ * a₁ ^ 2) (z₁ ^ 2 / d₁) := by
    refine ⟨mul_nonneg hd₁.le (sq_nonneg _), div_nonneg (sq_nonneg _) hd₁.le, ?_⟩
    have he : (a₁ * z₁) ^ 2 = (d₁ * a₁ ^ 2) * (z₁ ^ 2 / d₁) := by
      field_simp [hd₁.ne']
      ring
    exact he.le
  have h2 : SquareControl (a₂ * z₂) (d₂ * a₂ ^ 2) (z₂ ^ 2 / d₂) := by
    refine ⟨mul_nonneg hd₂.le (sq_nonneg _), div_nonneg (sq_nonneg _) hd₂.le, ?_⟩
    have he : (a₂ * z₂) ^ 2 = (d₂ * a₂ ^ 2) * (z₂ ^ 2 / d₂) := by
      field_simp [hd₂.ne']
      ring
    exact he.le
  have h := ((h0.add h1).add h2).bound
  have he : ⟪k', r⟫_ℝ + a₁ * z₁ + a₂ * z₂ =
      ⟪k, r⟫_ℝ - a₁ * e₁ - a₂ * e₂ := by
    simp only [k', z₁, z₂, inner_sub_left, real_inner_smul_left]
    ring
  rw [he] at h
  exact h

/-- The two-dimensional inverse improves the full continuum evaluation norm.
The last term is the explicit sensitivity to the two nonzero endpoint slacks. -/
theorem rank_two_full_energy_bound {d₁ d₂ Δ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hΔ : 0 ≤ Δ) (v₁ v₂ k r : E) (e₁ e₂ : ℝ)
    (hbudget : augmentedEnergy d₁ d₂ e₁ e₂ v₁ v₂ r ≤ 2 * Δ) :
    |⟪k, r⟫_ℝ| ≤
      sqrt (2 * (‖k‖ ^ 2 - inverseCoefficient1 d₁ d₂ v₁ v₂ k * ⟪k, v₁⟫_ℝ -
        inverseCoefficient2 d₁ d₂ v₁ v₂ k * ⟪k, v₂⟫_ℝ)) * sqrt Δ +
      |inverseCoefficient1 d₁ d₂ v₁ v₂ k * e₁ + inverseCoefficient2 d₁ d₂ v₁ v₂ k * e₂| := by
  let a₁ := inverseCoefficient1 d₁ d₂ v₁ v₂ k
  let a₂ := inverseCoefficient2 d₁ d₂ v₁ v₂ k
  let N := ‖k‖ ^ 2 - a₁ * ⟪k, v₁⟫_ℝ - a₂ * ⟪k, v₂⟫_ℝ
  obtain ⟨he1, he2⟩ := inverseCoefficient_equations hd₁ hd₂ v₁ v₂ k
  have hNid := corrected_norm_identity v₁ v₂ k he1 he2
  have hN : 0 ≤ N := by
    rw [← hNid]
    positivity
  have hs := augmented_evaluation_sq hd₁ hd₂ v₁ v₂ k r a₁ a₂ e₁ e₂
  rw [hNid] at hs
  have hs' : (⟪k, r⟫_ℝ - (a₁ * e₁ + a₂ * e₂)) ^ 2 ≤ (2 * N) * Δ := by
    have hb := mul_le_mul_of_nonneg_left hbudget hN
    nlinarith only [hs, hb]
  have hroot := Real.abs_le_sqrt hs'
  rw [sqrt_mul (mul_nonneg (by norm_num) hN)] at hroot
  have htriangle := abs_sub_le ⟪k, r⟫_ℝ (a₁ * e₁ + a₂ * e₂) 0
  simpa only [sub_zero] using htriangle.trans (add_le_add_right hroot _)

end MovingSofaQuantitative
