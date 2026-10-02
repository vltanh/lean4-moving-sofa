module

public import MovingSofa.Gerver.Properties

/-!
# Optimality of Gerver's sofa

Theorem 8.1.1 (`thm:cap-space-special`) parts (2)–(3), Theorem 8.5.7 (`thm:variation-a2-gerver`),
Corollary 8.5.8 (`cor:gerver-max-cap`), the existence and uniqueness of the parameters of Gerver's
sofa (implicit in Definition 8.1.2), and the main Theorem 1.1.1 (`thm:main`).
-/

@[expose] public section

open Real Set MeasureTheory

namespace MovingSofa

open GerverParams

/-- Romik's system has a solution in the box (implicit in Definition 8.1.2; Romik, Section 4 and
Table 1). -/
theorem definition8_1_2_exists : ∃ P : GerverParams, P.IsSolution ∧ P.InBox := by
  sorry

/-- The solution of Romik's system in the box is unique, so Gerver's sofa is well defined. -/
theorem definition8_1_2_unique {P Q : GerverParams} (hP : P.IsSolution) (hPb : P.InBox)
    (hQ : Q.IsSolution) (hQb : Q.InBox) : P = Q := by
  sorry

/-- **Theorem 8.1.1** (`thm:cap-space-special`) (2): every balanced maximum cap with rotation angle
`π/2` lies in `𝒦^i`. -/
theorem theorem8_1_1_balanced {K : Set (ℝ × ℝ)} (hK : IsBalancedMaxCap K (π / 2)) : IsKi K := by
  sorry

/-- **Theorem 8.1.1** (3): the cap of Gerver's sofa lies in `𝒦^i`. -/
theorem theorem8_1_1_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) : IsKi P.cap := by
  sorry

/-- The triple `(K, B_K, D_K)` of Gerver's sofa lies in `𝓛`. -/
theorem gerver_inL {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    InL P.φ P.cap (rightBody P.φ P.cap) (leftBody P.φ P.cap) := by
  sorry

/-- Gerver's triple as an element of `𝓛`. -/
noncomputable def gerverTriple {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) : LTriple P.φ :=
  ⟨(⟨P.cap, (gerver_inL hP hbox).1.1.2.1⟩, ⟨rightBody P.φ P.cap, (gerver_inL hP hbox).2.1⟩,
    ⟨leftBody P.φ P.cap, (gerver_inL hP hbox).2.2.1⟩), gerver_inL hP hbox⟩

/-- **Theorem 8.5.7** (`thm:variation-a2-gerver`). At Gerver's triple, the directional derivative of
`𝒬` towards any `(K*, B*, D*) ∈ 𝓛` is nonpositive. -/
theorem theorem8_5_7 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) (xs : LTriple P.φ) :
    (lDomain P.φ).dirDeriv (upperQL P.φ) (gerverTriple hP hbox) xs ≤ 0 := by
  sorry

/-- **Corollary 8.5.8** (`cor:gerver-max-cap`). Gerver's triple `(K, B_K, D_K)` maximizes `𝒬` on `𝓛`. -/
theorem corollary8_5_8 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) {K B D : Set (ℝ × ℝ)}
    (h : InL P.φ K B D) :
    upperQ P.φ K B D ≤ upperQ P.φ P.cap (rightBody P.φ P.cap) (leftBody P.φ P.cap) := by
  sorry

/-- **Theorem 1.1.1** (`thm:main`). Gerver's sofa attains the maximum area of a moving sofa: it is a
moving sofa, and every moving sofa has area at most that of Gerver's sofa. -/
theorem theorem1_1_1 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    IsMovingSofa (gerverSofa P) ∧ ∀ S, IsMovingSofa S → volume S ≤ volume (gerverSofa P) := by
  sorry

end MovingSofa
