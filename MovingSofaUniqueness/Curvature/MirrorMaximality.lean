module

public import MovingSofaOptimality.Injectivity.BoundingArms

/-!
# Reflection preserves the specified maximizer

These lemmas concern the actual reflected cap, not a replacement obtained
from existence of a balanced maximizer. They are independent of injectivity.
The sofa-area identity uses the reflected niche, including its strict inner
quadrants.
-/

@[expose] public section
noncomputable section

open Real Set MovingSofaOptimality

namespace MovingSofaUniqueness

/-- Reflection preserves the cap-minus-niche area functional. -/
theorem sofaArea_mirror (K : Set (ℝ × ℝ)) (ω : ℝ) :
    sofaArea ω (mirrorCap K ω) = sofaArea ω K := by
  unfold sofaArea
  rw [(proposition2_5_4_sets (K := K) (ω := ω) 0).2.2]
  change area (mirror ω '' K) - area (mirror ω '' niche K ω) = _
  rw [mpc_area_mirror, mpc_area_mirror]

/-- At a right angle the mirror is the involution `(x,y) ↦ (-x,y)`. -/
theorem mirrorCap_rightAngle_involutive (K : Set (ℝ × ℝ)) :
    mirrorCap (mirrorCap K (π / 2)) (π / 2) = K := by
  have hinv (p : ℝ × ℝ) : mirror (π / 2) (mirror (π / 2) p) = p := by
    rcases p with ⟨x, y⟩
    simp only [inj_mirror_pi_div_two, neg_neg]
  apply Set.Subset.antisymm
  · rintro p ⟨q, ⟨r, hr, rfl⟩, rfl⟩
    simpa only [hinv] using hr
  · intro p hp
    exact ⟨mirror (π / 2) p, ⟨p, hp, rfl⟩, hinv p⟩

/-- The reflection of this maximizer is again a maximizer. -/
theorem maximal_sofaArea_mirror {K : Set (ℝ × ℝ)}
    (hmax : ∀ C, IsCap C (π / 2) → sofaArea (π / 2) C ≤ sofaArea (π / 2) K) :
    ∀ C, IsCap C (π / 2) →
      sofaArea (π / 2) C ≤ sofaArea (π / 2) (mirrorCap K (π / 2)) := by
  intro C hC
  rw [sofaArea_mirror]
  exact hmax C hC

/-- The endpoint conventions matter: the reflected plus-arm is the original
minus-arm. No atom-free or differentiability hypothesis is needed. -/
theorem gPlus_mirror_eq_fMinus (K : Set (ℝ × ℝ)) (t : ℝ) :
    gPlus (mirrorCap K (π / 2)) t = fMinus K (π / 2 - t) :=
  (proposition6_2_2 (K := K) (t := t)).2.2.1

end MovingSofaUniqueness
