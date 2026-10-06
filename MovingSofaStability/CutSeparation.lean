module

public import MovingSofaStability.CoreIntegral

/-!
# Stable separation from the two niche cuts

Uncompiled proof source. Close to a cut, a uniform right-velocity margin is
used. Away from it, a strict compact reference margin is used. No derivative
control near the ends 0 and pi/2 is assumed for the competing cap.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- The two inequalities used in the three-region niche decomposition. -/
def CutSeparated (φ : ℝ) (K : Set Point) : Prop :=
  (∀ t ∈ Ioc φ (π / 2), dot (innerCorner K t) (uvec φ) < supp K φ - 1) ∧
  (∀ t ∈ Ico 0 (π / 2 - φ),
    dot (innerCorner K t) (vvec (π / 2 - φ)) < supp K (π / 2 - φ + π / 2) - 1)

theorem innerCorner_projection_error {K K₀ : Set Point} {δ t : ℝ}
    (h : UpperSupportClose δ K K₀) (ht : t ∈ Icc (0 : ℝ) (π / 2)) (a : ℝ) :
    |dot (innerCorner K t) (uvec a) - dot (innerCorner K₀ t) (uvec a)| ≤ 2 * δ := by
  have hp := abs_dot_le_norm2_mul (innerCorner K t - innerCorner K₀ t) (uvec a)
  rw [dot_sub_left, norm2_uvec, mul_one] at hp
  exact hp.trans (innerCorner_support_error h ht)

/-- Separation on the right includes times arbitrarily close to pi/2. -/
theorem nearby_right_cut_separation {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K₀ : Set Point} (hK₀ : IsKi K₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K K₀ →
        ∀ t ∈ Ioc φ (π / 2), dot (innerCorner K t) (uvec φ) < supp K φ - 1 := by
  sorry

/-- The left separation is obtained by the same local/compact split, without
assuming that all left arm lengths of the competing cap exceed one. -/
theorem nearby_left_cut_separation {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K₀ : Set Point} (hK₀ : IsKi K₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K K₀ →
        ∀ t ∈ Ico 0 (π / 2 - φ),
          dot (innerCorner K t) (vvec (π / 2 - φ)) < supp K (π / 2 - φ + π / 2) - 1 := by
  sorry

/-- Both cuts are simultaneously separated in one fixed neighborhood. -/
theorem nearby_cutSeparated {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K P.cap → CutSeparated P.φ K := by
  sorry

end MovingSofaStability
