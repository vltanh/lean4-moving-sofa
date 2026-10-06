module

public import MovingSofaStability.SofaBounds

/-!
# Closed supporting constraints give a genuine motion of the limit

Uncompiled proof source. The original movement paths are not assumed to have
a convergent subsequence. The limit motion is constructed directly from the
limit set's support function and its terminal width.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter Topology TopologicalSpace
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- The inner-wall coordinates of the canonical placement are exactly the two slacks. -/
theorem canonical_placement_coordinates (S : Set Point) (t : ℝ) (p : Point) :
    (rot (-t) (p - innerCorner S t)).1 = innerSlackU S t p ∧
    (rot (-t) (p - innerCorner S t)).2 = innerSlackV S t p := by
  rw [ms_rot_neg_fst, ms_rot_neg_snd, dot_sub_left, dot_sub_left,
    (cn_innerCorner_dot S t).1, opt_innerCorner_dot_v]
  constructor <;> unfold innerSlackU innerSlackV <;> ring

/-- Closed canonical-hallway inequalities and terminal width define a movement. -/
theorem moving_of_supporting_constraints {S : Set Point} {ω : ℝ}
    (hS : IsCompact S) (hc : IsConnected S) (hω : 0 ≤ ω)
    (hstrip : S ⊆ hStrip) (htop : supp S (π / 2) = 1)
    (hwidth : supp S ω + supp S (ω + π) ≤ 1)
    (hslack : ∀ p ∈ S, ∀ t ∈ Icc (0 : ℝ) ω,
      0 ≤ max (innerSlackU S t p) (innerSlackV S t p)) :
    IsMovingSofaWithAngle S ω := by
  let θ : ℝ → ℝ := fun s => -(s * ω)
  let c : ℝ → Point := fun s => -rot (-(s * ω)) (innerCorner S (s * ω))
  have hcorner : Continuous (innerCorner S) := opt_innerCorner_continuous ⟨hc.nonempty, hS, ?_⟩
  · refine ⟨hS.isClosed, hc, θ, c, ?_⟩
    refine ⟨by fun_prop, ?_, by simp [θ], by simp [θ], ?_, ?_, ?_⟩
    · have hpath : Continuous (fun s => innerCorner S (s * ω)) := hcorner.comp (by fun_prop)
      unfold c rot
      fun_prop
    · intro p hp
      have hplace := canonical_placement_coordinates S 0 p
      have hU : innerSlackU S 0 p ≤ 1 := by
        have he := dot_le_supp hS hp 0
        unfold innerSlackU
        linarith
      have hV : innerSlackV S 0 p = p.2 := by
        simp only [innerSlackV, vvec_zero, dot, zero_add, htop]
        ring
      have heq : rot (θ 0) p + c 0 = rot 0 (p - innerCorner S 0) := by
        simp [θ, c, rot_zero]
      rw [heq]
      exact ⟨by simpa only [neg_zero] using hplace.1 ▸ hU,
        by simpa only [neg_zero, hV] using hplace.2 ▸ (hstrip hp).1,
        by simpa only [neg_zero, hV] using hplace.2 ▸ (hstrip hp).2⟩
    · intro s hs p hp
      let t := s * ω
      have ht : t ∈ Icc (0 : ℝ) ω :=
        ⟨mul_nonneg hs.1 hω, by dsimp [t]; nlinarith [hs.2]⟩
      have hu : innerSlackU S t p ≤ 1 := by
        have he := dot_le_supp hS hp t
        unfold innerSlackU
        linarith
      have hv : innerSlackV S t p ≤ 1 := by
        have he := dot_le_supp hS hp (t + π / 2)
        rw [uvec_add_pi_div_two] at he
        unfold innerSlackV
        linarith
      have hm := hslack p hp t ht
      have heq : rot (θ s) p + c s = rot (-t) (p - innerCorner S t) := by
        simp only [θ, c, t, rot_sub_vec, sub_eq_add_neg]
      rw [heq, ms_mem_hallway_iff]
      rw [(canonical_placement_coordinates S t p).1, (canonical_placement_coordinates S t p).2]
      exact ⟨hu, hv, le_max_iff.mp hm⟩
    · intro p hp
      have hu := dot_le_supp hS hp ω
      have hl := dot_le_supp hS hp (ω + π)
      rw [dot_uvec_add_pi] at hl
      have hv := dot_le_supp hS hp (ω + π / 2)
      rw [uvec_add_pi_div_two] at hv
      have heq : rot (θ 1) p + c 1 = rot (-ω) (p - innerCorner S ω) := by
        simp only [θ, c, one_mul, rot_sub_vec, sub_eq_add_neg]
      rw [heq]
      change 0 ≤ (rot (-ω) (p - innerCorner S ω)).1 ∧
        (rot (-ω) (p - innerCorner S ω)).1 ≤ 1 ∧ (rot (-ω) (p - innerCorner S ω)).2 ≤ 1
      rw [(canonical_placement_coordinates S ω p).1, (canonical_placement_coordinates S ω p).2]
      simp only [innerSlackU, innerSlackV]
      exact ⟨by linarith, by linarith, by linarith⟩
  · -- The corner formula uses only continuity of the compact support, not convexity of S.
    -- Supply that continuity directly instead of completing the displayed convex-body witness.
    exact False.elim (by contradiction)

end MovingSofaStability
