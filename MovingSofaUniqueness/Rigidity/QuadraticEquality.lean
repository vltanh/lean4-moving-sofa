module

public import MovingSofaOptimality.Convex.ConvexDomain

/-!
# Equality cases for concave quadratic functionals

Theorem 7.1.5 proves maximality from nonpositive first variations. Uniqueness also requires
control of the equality case. The exact deficit identity below separates the first variation
from the midpoint concavity gap; both terms are nonnegative at a maximum.
-/

@[expose] public section

open Set

namespace MovingSofaOptimality
namespace ConvexDomain

variable {V : Type} (D : ConvexDomain V) {f : V → ℝ}

/-- A concave functional is constant on a segment joining two global maximizers. -/
theorem eq_on_segment_of_isMax (hc : D.IsConcave f) {x y : V}
    (hmax : ∀ z, f z ≤ f x) (hxy : f y = f x) {c : ℝ} (hcm : c ∈ Icc (0 : ℝ) 1) :
    f (D.comb c x y) = f x := by
  apply le_antisymm (hmax _)
  have h := hc x y c hcm
  rw [hxy] at h
  nlinarith

/-- The deficit of a quadratic functional is minus its first variation plus four times its
midpoint concavity gap. No concavity or maximality assumption is needed for this identity. -/
theorem quadratic_deficit_identity (hq : D.IsQuadratic f) (x y : V) :
    f x - f y = -D.dirDeriv f x y +
      4 * (f (D.comb (1 / 2) x y) - (f x + f y) / 2) := by
  obtain ⟨g, hg, hfg⟩ := hq
  have hf : f = fun v => g v v := funext hfg
  have hhalf : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  rw [hf, lemma7_1_4 D hg]
  change g x x - g y y = -(g x y + g y x - 2 * g x x) +
    4 * (g (D.comb (1 / 2) x y) (D.comb (1 / 2) x y) - (g x x + g y y) / 2)
  rw [cvx_bilin_comb D hg x y hhalf]
  ring

/-- A concave quadratic functional lies below its first-order affine approximation. -/
theorem quadratic_tangent_bound (hq : D.IsQuadratic f) (hc : D.IsConcave f) (x y : V) :
    f y ≤ f x + D.dirDeriv f x y := by
  have h := hc x y (1 / 2) (by constructor <;> norm_num)
  have he := D.quadratic_deficit_identity hq x y
  nlinarith

/-- A direction from one maximizer to another has zero first variation, not merely a
nonpositive first variation. -/
theorem dirDeriv_eq_zero_of_isMax (hq : D.IsQuadratic f) (hc : D.IsConcave f) {x y : V}
    (hmax : ∀ z, f z ≤ f x) (hxy : f y = f x) : D.dirDeriv f x y = 0 := by
  have hle := (theorem7_1_5 D hq hc x).1 hmax y
  have hge := D.quadratic_tangent_bound hq hc x y
  rw [hxy] at hge
  linarith

/-- At a maximum, equality of values is equivalent to vanishing of both nonnegative
contributions to the deficit. A zero first variation alone does not suffice. -/
theorem eq_iff_dirDeriv_eq_zero_and_midpoint_eq (hq : D.IsQuadratic f)
    (hc : D.IsConcave f) {x y : V} (hmax : ∀ z, f z ≤ f x) :
    f y = f x ↔ D.dirDeriv f x y = 0 ∧
      f (D.comb (1 / 2) x y) = (f x + f y) / 2 := by
  constructor
  · intro hxy
    refine ⟨D.dirDeriv_eq_zero_of_isMax hq hc hmax hxy, ?_⟩
    rw [D.eq_on_segment_of_isMax hc hmax hxy (by constructor <;> norm_num), hxy]
    ring
  · rintro ⟨hderiv, hmid⟩
    have h := D.quadratic_deficit_identity hq x y
    rw [hderiv, hmid] at h
    linarith

end ConvexDomain
end MovingSofaOptimality
