module

public import MovingSofaStability.RoofMargins

/-!
# Uniform slack below an envelope roof

Uncompiled proof source. The inactive tail wall has a strictly negative slack
on its entire compact parameter interval, including its floor endpoint. The
active wall's vertical coefficient is uniformly positive. This is proved from
`EnvHyp`, rather than assumed as a local error bound.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

theorem innerSlackU_eq_dot (K : Set Point) (t : ℝ) (p : Point) :
    innerSlackU K t p = dot (p - innerCorner K t) (uvec t) := by
  rw [dot_sub_left, proposition2_2_2_innerCorner]
  simp only [dot_add_left, dot_smul_left, dot_uvec_self, dot_vvec_uvec, mul_one,
    mul_zero, add_zero, innerSlackU]
  ring

theorem innerSlackV_eq_dot (K : Set Point) (t : ℝ) (p : Point) :
    innerSlackV K t p = dot (p - innerCorner K t) (vvec t) := by
  rw [dot_sub_left, proposition2_2_2_innerCorner]
  simp only [dot_add_left, dot_smul_left, dot_uvec_vvec, dot_vvec_self, mul_one,
    mul_zero, zero_add, innerSlackV]
  ring

theorem innerSlackU_down (K : Set Point) (t d : ℝ) (q : Point) :
    innerSlackU K t (q.1, q.2 - d) = innerSlackU K t q - d * sin t := by
  simp only [innerSlackU, dot, uvec]
  ring

theorem innerSlackV_down (K : Set Point) (t d : ℝ) (q : Point) :
    innerSlackV K t (q.1, q.2 - d) = innerSlackV K t q - d * cos t := by
  simp only [innerSlackV, dot, vvec]
  ring

section Envelope

variable {t₁ t₂ t₃ t₄ sA sC : ℝ} {x : ℝ → Point} {α β ρA ρC : ℝ → ℝ}
variable (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC)

/-- The path's abscissa decreases even outside the middle exposed arc. -/
theorem envelope_path_fst_strictAnti : StrictAntiOn (fun t => (x t).1) (Icc 0 (π / 2)) := by
  sorry

/-- The inactive tail slacks stay strict at the two floor endpoints as well. -/
theorem envelope_endpoint_speeds : 0 < β 0 ∧ α (π / 2) < 0 := by
  sorry

/-- A common positive margin works for all three roof pieces. -/
theorem envelope_downward_slack {K : Set Point}
    (hpath : ∀ t ∈ Icc (0 : ℝ) (π / 2), innerCorner K t = x t) :
    ∃ c τ : ℝ, 0 < c ∧ 0 < τ ∧
      ∀ q ∈ envCurve t₁ t₂ t₃ t₄ x α β, ∀ d : ℝ, 0 < d → 0 ≤ q.2 - d →
        ∃ t ∈ Ioo (0 : ℝ) (π / 2),
          innerSlackU K t (q.1, q.2 - d) ≤ -min (c * d) τ ∧
          innerSlackV K t (q.1, q.2 - d) ≤ -min (c * d) τ := by
  sorry

end Envelope

end MovingSofaStability
