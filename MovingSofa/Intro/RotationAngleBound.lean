module

public import MovingSofa.Monotone.SupportingHallway

/-!
# A first bound on the rotation angle (§1.5)

Theorem 1.5.1 (`thm:rotation-angle-simple-bound`, a modification of page 271 of Gerver's paper).
-/

@[expose] public section

open Real Set

namespace MovingSofa

/-- `sec⁻¹(2.2) = arccos(1/2.2)`. -/
noncomputable def arcsec22 : ℝ := arccos (1 / 2.2)

/-- **Theorem 1.5.1** (`thm:rotation-angle-simple-bound`). A moving sofa of area at least `2.2`
admits a movement in `L` with rotation angle `ω ∈ [sec⁻¹(2.2), π/2]`. -/
theorem theorem1_5_1 {S : Set (ℝ × ℝ)} (hS : IsMovingSofa S) (harea : 2.2 ≤ area S) :
    ∃ ω ∈ Icc arcsec22 (π / 2), IsMovingSofaWithAngle S ω := by
  sorry

end MovingSofa
