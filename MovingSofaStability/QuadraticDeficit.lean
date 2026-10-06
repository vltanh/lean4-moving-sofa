module

public import MovingSofaOptimality.Convex.ConvexDomain

/-!
# Quantitative deficit of a quadratic functional

The midpoint concavity gap, multiplied by four, is the quadratic energy along
an entire segment. At a global maximizer that energy is bounded by the
objective deficit, with constant one. The proof uses an explicit small segment
parameter, not an unformalized passage to a limit.

There is no assumption of strict concavity or uniqueness of auxiliary variables.
-/

@[expose] public section
noncomputable section

open Set
open MovingSofaOptimality

namespace MovingSofaStability

/-- An elementary substitute for letting the segment parameter decrease to zero. -/
theorem energy_le_of_dilations {E δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ c ∈ Ioo (0 : ℝ) 1, (1 - c) * E ≤ δ) : E ≤ δ := by
  by_contra hnot
  have hδE : δ < E := not_le.mp hnot
  have hE : 0 < E := lt_of_le_of_lt hδ hδE
  have hden : 0 < 2 * E := by positivity
  let c : ℝ := (E - δ) / (2 * E)
  have hc0 : 0 < c := div_pos (sub_pos.mpr hδE) hden
  have hc1 : c < 1 := by
    dsimp [c]
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hcE : c * (2 * E) = E - δ := by
    dsimp [c]
    exact div_mul_cancel₀ _ (ne_of_gt hden)
  have hbound := h c ⟨hc0, hc1⟩
  nlinarith

/-- A segment identity with a quadratic energy yields a deficit bound at a
maximum. This statement does not presuppose the sign of the energy. -/
theorem energy_le_deficit_of_segment {V : Type*} (comb : ℝ → V → V → V)
    (Q : V → ℝ) (x₀ x₁ : V) (E : ℝ)
    (hmax : ∀ x, Q x ≤ Q x₀)
    (hsegment : ∀ c ∈ Icc (0 : ℝ) 1,
      Q (comb c x₀ x₁) = (1 - c) * Q x₀ + c * Q x₁ + c * (1 - c) * E) :
    E ≤ Q x₀ - Q x₁ := by
  apply energy_le_of_dilations (sub_nonneg.mpr (hmax x₁))
  intro c hc
  have he := hsegment c ⟨hc.1.le, hc.2.le⟩
  have hm := hmax (comb c x₀ x₁)
  have hp : c * ((1 - c) * E) ≤ c * (Q x₀ - Q x₁) := by
    nlinarith
  exact (mul_le_mul_iff_right₀ hc.1).mp hp

/-- Four times the midpoint concavity gap. For a quadratic functional this is
its negative quadratic part in the direction from `x` to `y`. -/
def segmentEnergy {V : Type} (D : ConvexDomain V) (Q : V → ℝ) (x y : V) : ℝ :=
  4 * (Q (D.comb (1 / 2) x y) - (Q x + Q y) / 2)

/-- The midpoint energy determines the exact value on every segment. -/
theorem quadratic_segment_identity {V : Type} (D : ConvexDomain V)
    {Q : V → ℝ} (hq : D.IsQuadratic Q) (x y : V) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) :
    Q (D.comb c x y) =
      (1 - c) * Q x + c * Q y + c * (1 - c) * segmentEnergy D Q x y := by
  obtain ⟨g, hg, hfg⟩ := hq
  have hf : Q = fun z => g z z := funext hfg
  subst Q
  have hh : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  unfold segmentEnergy
  beta_reduce
  rw [cvx_bilin_comb D hg x y hc, cvx_bilin_comb D hg x y hh]
  ring

/-- Concavity is needed for nonnegativity, but not for the exact identity. -/
theorem segmentEnergy_nonneg {V : Type} (D : ConvexDomain V) {Q : V → ℝ}
    (hc : D.IsConcave Q) (x y : V) : 0 ≤ segmentEnergy D Q x y := by
  have h := hc x y (1 / 2) ⟨by norm_num, by norm_num⟩
  unfold segmentEnergy
  nlinarith

/-- Quantitative strengthening of constancy on segments between maximizers. -/
theorem segmentEnergy_le_deficit {V : Type} (D : ConvexDomain V) {Q : V → ℝ}
    (hq : D.IsQuadratic Q) {x₀ : V} (hmax : ∀ x, Q x ≤ Q x₀) (x₁ : V) :
    segmentEnergy D Q x₀ x₁ ≤ Q x₀ - Q x₁ := by
  apply energy_le_deficit_of_segment D.comb Q x₀ x₁ _ hmax
  intro c hc
  exact quadratic_segment_identity D hq x₀ x₁ hc

/-- The exact deficit is the negative first variation plus the segment energy.
For an affine-minus-squares functional this is its dual-slack certificate. -/
theorem deficit_eq_neg_dirDeriv_add_energy {V : Type} (D : ConvexDomain V)
    {Q : V → ℝ} (hq : D.IsQuadratic Q) (x y : V) :
    Q x - Q y = -D.dirDeriv Q x y + segmentEnergy D Q x y := by
  obtain ⟨g, hg, hfg⟩ := hq
  have hf : Q = fun z => g z z := funext hfg
  subst Q
  have hh : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  rw [lemma7_1_4 D hg]
  unfold segmentEnergy
  beta_reduce
  rw [cvx_bilin_comb D hg x y hh]
  ring

/-- Equality of maximizing values makes the quadratic energy vanish. -/
theorem segmentEnergy_eq_zero_of_equal_values {V : Type} (D : ConvexDomain V)
    {Q : V → ℝ} (hq : D.IsQuadratic Q) (hc : D.IsConcave Q)
    {x₀ x₁ : V} (hmax : ∀ x, Q x ≤ Q x₀) (heq : Q x₁ = Q x₀) :
    segmentEnergy D Q x₀ x₁ = 0 := by
  have hlo := segmentEnergy_nonneg D hc x₀ x₁
  have hhi := segmentEnergy_le_deficit D hq hmax x₁
  rw [heq, sub_self] at hhi
  exact le_antisymm hhi hlo

end MovingSofaStability
