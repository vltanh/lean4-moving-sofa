module

public import MovingSofa.Monotone.CapDefs

/-!
# The supporting hallway (§2.2) and the common subset of a moving sofa (§1.2)

Propositions 2.2.1–2.2.3, Proposition 1.2.2 (`pro:moving-sofa-common-subset`), and the boundedness of
moving sofas.
-/

@[expose] public section

open Real Set

namespace MovingSofa

/-- **Proposition 2.2.1** (`pro:tangent-hallway`). Among the translations `p ↦ R_t p + c` of `R_t(L)`,
the supporting hallway `L_S(t)` is the unique one whose outer walls corresponding to `a_L` and `c_L`
are the supporting lines `l_S(t)` and `l_S(t + π/2)`. -/
theorem proposition2_2_1 (S : Set (ℝ × ℝ)) (t : ℝ) (c : ℝ × ℝ) :
    ((fun p => rot t p + c) '' aL = suppLine S t ∧
        (fun p => rot t p + c) '' cL = suppLine S (t + π / 2)) ↔
      (fun p => rot t p + c) = hallwayMap S t := by
  sorry

/-! **Proposition 2.2.2** (`pro:rotating-hallway-parts`). The parts of `L_S(t)` in terms of the support
function. The paper's last formula, for `Q_S⁻(t)`, misses a `- 1` in its second half-plane; the
statement below is the corrected one. -/

theorem proposition2_2_2_hallway (S : Set (ℝ × ℝ)) (t : ℝ) :
    suppHallway S t = qPlus S t \ qMinus S t := by
  sorry

theorem proposition2_2_2_innerCorner (S : Set (ℝ × ℝ)) (t : ℝ) :
    innerCorner S t = (supp S t - 1) • uvec t + (supp S (t + π / 2) - 1) • vvec t := by
  sorry

theorem proposition2_2_2_outerCorner (S : Set (ℝ × ℝ)) (t : ℝ) :
    outerCorner S t = supp S t • uvec t + supp S (t + π / 2) • vvec t := by
  sorry

theorem proposition2_2_2_wallA (S : Set (ℝ × ℝ)) (t : ℝ) : wallA S t = suppLine S t := by
  sorry

theorem proposition2_2_2_wallB (S : Set (ℝ × ℝ)) (t : ℝ) : wallB S t = line t (supp S t - 1) := by
  sorry

theorem proposition2_2_2_wallC (S : Set (ℝ × ℝ)) (t : ℝ) :
    wallC S t = suppLine S (t + π / 2) := by
  sorry

theorem proposition2_2_2_wallD (S : Set (ℝ × ℝ)) (t : ℝ) :
    wallD S t = line (t + π / 2) (supp S (t + π / 2) - 1) := by
  sorry

theorem proposition2_2_2_qPlus (S : Set (ℝ × ℝ)) (t : ℝ) :
    qPlus S t = suppHalf S t ∩ suppHalf S (t + π / 2) := by
  sorry

theorem proposition2_2_2_qMinus (S : Set (ℝ × ℝ)) (t : ℝ) :
    qMinus S t = halfMinusOpen t (supp S t - 1) ∩ halfMinusOpen (t + π / 2) (supp S (t + π / 2) - 1) := by
  sorry

/-- **Proposition 2.2.3** (`pro:tangent-hallway-contains`). A nonempty compact set contained in a
translation of `R_t(L)` is contained in its supporting hallway `L_S(t)`. -/
theorem proposition2_2_3 {S : Set (ℝ × ℝ)} (hS : IsCompact S) (hne : S.Nonempty) (t : ℝ)
    (c : ℝ × ℝ) (h : S ⊆ (fun p => rot t p + c) '' hallway) : S ⊆ suppHallway S t := by
  sorry

/-- Every moving sofa is bounded (implicit in the paper, which takes the area of moving sofas). -/
theorem isBounded_of_isMovingSofa {S : Set (ℝ × ℝ)} (hS : IsMovingSofa S) :
    Bornology.IsBounded S := by
  sorry

/-- A moving sofa is compact. -/
theorem isCompact_of_isMovingSofa {S : Set (ℝ × ℝ)} (hS : IsMovingSofa S) : IsCompact S := by
  sorry

/-- **Proposition 1.2.2** (`pro:moving-sofa-common-subset`). A moving sofa `S` with rotation angle
`ω ∈ (0, π/2]` in standard position lies in the strip `H`, in a translation of `R_t(L)` for every
`t ∈ [0, ω]`, and in the rotated strip `V_ω`. -/
theorem proposition1_2_2 {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) :
    S ⊆ hStrip ∧ (∀ t ∈ Icc 0 ω, ∃ c : ℝ × ℝ, S ⊆ (fun p => rot t p + c) '' hallway) ∧
      S ⊆ vStripRot ω := by
  sorry

end MovingSofa
