module

public import MovingSofa.Optimality.Equality

/-!
# Regression examples for the uniqueness equality conditions

These examples are included in the default library build. They cover a strictly concave
quadratic with zero first variation, a constant functional with distinct maximizers, and the
specialization of the cap equality conditions to Gerver's own cap.
-/

@[expose] public section

open Real Set

namespace MovingSofa.EqualityTests

open GerverParams

private theorem negMul_bilinear :
    realDomain.IsConvexBilinear realDomain realDomain (fun x y : ℝ => -(x * y)) := by
  constructor
  · intro x c _ y z
    change -(x * ((1 - c) * y + c * z)) = (1 - c) * -(x * y) + c * -(x * z)
    ring
  · intro y c _ x z
    change -(((1 - c) * x + c * z) * y) = (1 - c) * -(x * y) + c * -(z * y)
    ring

private theorem negSquare_quadratic : realDomain.IsQuadratic (fun x : ℝ => -(x * x)) :=
  ⟨fun x y => -(x * y), negMul_bilinear, fun _ => rfl⟩

private theorem negSquare_concave : realDomain.IsConcave (fun x : ℝ => -(x * x)) := by
  intro x y c hc
  change (1 - c) * -(x * x) + c * -(y * y) ≤
    -(((1 - c) * x + c * y) * ((1 - c) * x + c * y))
  nlinarith [mul_nonneg (mul_nonneg hc.1 (sub_nonneg.mpr hc.2)) (sq_nonneg (x - y))]

/-- At the maximum of `-x²`, first variation toward `1` vanishes although the values differ. -/
example : realDomain.dirDeriv (fun x : ℝ => -(x * x)) 0 1 = 0 ∧
    (-(1 * 1) : ℝ) ≠ -(0 * 0) := by
  constructor
  · rw [lemma7_1_4 realDomain negMul_bilinear]
    norm_num
  · norm_num

/-- The missing contribution is the strictly positive midpoint gap. -/
example : (-(realDomain.comb (1 / 2) 0 1 * realDomain.comb (1 / 2) 0 1) : ℝ) -
    (-(0 * 0) + -(1 * 1)) / 2 = 1 / 4 := by
  norm_num [realDomain]

/-- Exercise the deficit identity with a nonzero quadratic deficit. -/
example : (1 : ℝ) = -realDomain.dirDeriv (fun x : ℝ => -(x * x)) 0 1 + 4 * (1 / 4) := by
  have h := realDomain.quadratic_deficit_identity negSquare_quadratic 0 1
  norm_num [realDomain] at h ⊢
  exact h

/-- Exercise both directions of the equality characterization at a strict maximum. -/
example (y : ℝ) : -(y * y) = (0 : ℝ) ↔
    realDomain.dirDeriv (fun x : ℝ => -(x * x)) 0 y = 0 ∧
      -(realDomain.comb (1 / 2) 0 y * realDomain.comb (1 / 2) 0 y) = -(y * y) / 2 := by
  have hmax : ∀ z : ℝ, -(z * z) ≤ -(0 * 0) := fun z => by nlinarith [sq_nonneg z]
  simpa using realDomain.eq_iff_dirDeriv_eq_zero_and_midpoint_eq
    negSquare_quadratic negSquare_concave (y := y) hmax

private theorem const_quadratic : realDomain.IsQuadratic (fun _ : ℝ => (7 : ℝ)) := by
  refine ⟨fun _ _ => 7, ⟨?_, ?_⟩, fun _ => rfl⟩
  · intro x c _ y z
    change 7 = (1 - c) * 7 + c * 7
    ring
  · intro y c _ x z
    change 7 = (1 - c) * 7 + c * 7
    ring

private theorem const_concave : realDomain.IsConcave (fun _ : ℝ => (7 : ℝ)) := by
  intro x y c _
  change (1 - c) * 7 + c * 7 ≤ (7 : ℝ)
  nlinarith

/-- Distinct maximizers are permitted: these lemmas must not accidentally assume strictness. -/
example : realDomain.dirDeriv (fun _ : ℝ => (7 : ℝ)) 0 1 = 0 :=
  realDomain.dirDeriv_eq_zero_of_isMax const_quadratic const_concave (fun _ => le_rfl) rfl

/-- Gerver's own cap satisfies the newly exposed necessary conditions. -/
example {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    MamikonSegmentEquality P.φ (gerverTriple hP hbox)
      (kiExtensionTriple hbox.1 (theorem8_1_1_gerver hP hbox)) (1 / 2) := by
  have h := ki_maximizer_equality_conditions hP hbox (theorem8_1_1_gerver hP hbox)
    (gm_sofaArea_cap hP hbox)
  exact h.2 (1 / 2) (by constructor <;> norm_num)

/-- The converse characterization is usable without a geometric uniqueness assumption. -/
example {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) (x : LTriple P.φ)
    (hd : (lDomain P.φ).dirDeriv (upperQL P.φ) (gerverTriple hP hbox) x = 0)
    (hm : MamikonSegmentEquality P.φ (gerverTriple hP hbox) x (1 / 2)) :
    upperQL P.φ x = upperQL P.φ (gerverTriple hP hbox) :=
  (upperQL_eq_gerver_iff hP hbox x).2 ⟨hd, hm⟩

end MovingSofa.EqualityTests
