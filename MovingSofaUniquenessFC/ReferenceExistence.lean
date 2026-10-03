module

public import MovingSofaUniquenessFC.ReferenceFromPaper
public import MovingSofaUniquenessFC.ReferenceUniqueness

/-!
# Existence and uniqueness for the exact upstream parameter specification

Existence comes from the already constructed paper solution via the explicit
inverse parameter map. Uniqueness is the global analytic residual argument,
not the paper's uniqueness-in-a-box assertion. These two logically separate
steps prove exactly the four-constant existence-and-uniqueness proposition
used to define the formal-conjectures reference.

No upstream placeholder is imported. No root certificate is evaluated.
-/

@[expose] public section
noncomputable section

open Set Real MovingSofaOptimality MovingSofaOptimality.GerverParams

namespace MovingSofaUniquenessFC.Reference

/-- A full-domain reference solution exists. -/
theorem spec_exists : ∃ A B φ θ : ℝ, Spec A B φ θ := by
  obtain ⟨P, hP, hbox⟩ := romik_exists
  exact ⟨(ofPaper P).A, (ofPaper P).B, P.φ, P.θ, ofPaper_valid hP hbox⟩

/-- The precise nested-product type used by formal-conjectures. -/
theorem spec_existsUnique : ∃! q : ℝ × ℝ × ℝ × ℝ,
    Spec q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  obtain ⟨A, B, φ, θ, h⟩ := spec_exists
  refine ⟨(A, B, φ, θ), h, ?_⟩
  rintro ⟨A', B', φ', θ'⟩ h'
  obtain ⟨ha, hb, hp, ht⟩ := spec_unique h' h
  simp only [Prod.mk.injEq]
  exact ⟨ha, hb, hp, ht⟩

/-- Every reference solution is the explicit inverse image of the same paper
witness. This supplies the small box as a CONSEQUENCE, never as a premise
silently replacing the upstream domain. -/
theorem Data.eq_ofPaper {D : Data} (hD : D.Valid) {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) : D = ofPaper P := by
  obtain ⟨ha, hb, hp, ht⟩ := spec_unique hD (ofPaper_valid hP hbox)
  cases D
  simp_all only [ofPaper]

/-- The reference equations imply the strict upper angle bound, which
`Data.toPaper_isSolution` takes as a hypothesis, by equality with the paper
witness. -/
theorem Data.theta_lt_pi_div_four {D : Data} (hD : D.Valid) : D.θ < π / 4 := by
  obtain ⟨P, hP, hbox⟩ := romik_exists
  rw [Data.eq_ofPaper hD hP hbox]
  exact hP.2.2.1

/-- The reconstructed paper parameters solve the paper equations and lie in
its established box, for EVERY solution of the exact upstream specification. -/
theorem Data.paper_solution {D : Data} (hD : D.Valid) :
    D.toPaper.IsSolution ∧ D.toPaper.InBox := by
  obtain ⟨P, hP, hbox⟩ := romik_exists
  rw [Data.eq_ofPaper hD hP hbox, ofPaper_toPaper hP]
  exact ⟨hP, hbox⟩

end MovingSofaUniquenessFC.Reference
