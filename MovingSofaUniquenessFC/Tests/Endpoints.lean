module

public import MovingSofaUniquenessFC.Final
public import MovingSofaUniquenessFC.ReferenceBoundary

/-!
# Unexecuted endpoint and integration regressions

These are Lean examples, not external tests or numerical certificates. They
have not been elaborated or run. They check the intended source interfaces:
reflection includes normal pi, the pinned positivity premise is explicit at
its local interface, and neither smoothness nor injectivity is an input to
canonical shape uniqueness.

The exact upstream concrete-reference theorem is deliberately not asserted as
an example while its stricter source integration remains unfinished.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory MovingSofa MovingSofaOptimality
open scoped EuclideanGeometry

namespace MovingSofaUniquenessFC.Tests

open MovingSofaUniqueness

/-- Reflection starts from a general cap; no atom-free assumption is supplied. -/
example {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2))
    (hfirst : FirstCurvatureBound (mirrorCap K (π / 2))) :
    (sigma K).restrict (Ioc (π / 2) π) ≤
      (volume.restrict (Ioc (π / 2) π)).withDensity
        (fun t => ENNReal.ofReal (k0 (fMinus K (t - π / 2)))) := by
  exact secondCurvature_of_mirror_first hK hfirst

/-- The specified right-angle maximizer supplies its own positivity. -/
example {K : Set (ℝ × ℝ)} (hK : MovingSofaUniqueness.IsMaxCap (π / 2) K) :
    MovingSofaUniqueness.CurvatureBounds K := by
  exact MovingSofaUniqueness.curvatureBounds_of_isMaxCap hK

/-- The smaller-angle interface does not silently drop its positivity premise. -/
example {K : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioo 0 (π / 2))
    (hK : MovingSofaUniqueness.IsMaxCap ω K) (hpositive : 0 < sofaArea ω K) :
    MovingSofaUniqueness.PinnedBounds ω K := by
  exact MovingSofaUniqueness.pinnedBounds_of_isMaxCap hω hK hpositive

/-- Exact equality of sets modulo a Euclidean isometry, with no regularity
hypothesis added to either canonical competitor. -/
example (s t : Set ℝ²) (hs : ∃ m, MovingSofa.IsMovingSofa s m)
    (ht : ∃ m, MovingSofa.IsMovingSofa t m)
    (hsvol : volume s = MovingSofa.sofaConstant)
    (htvol : volume t = MovingSofa.sofaConstant) :
    ∃ g : E(2), s = g '' t := by
  exact MovingSofa.Canonical.maximizers_congruent s t hs ht hsvol htvol

/-- The reference used by the publication theorem is its actual concrete
Gerver set, not a newly defined choice of an abstract maximizing set. -/
example {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (s : Set ℝ²) (hs : ∃ m, MovingSofa.IsMovingSofa s m) :
    volume s = MovingSofa.sofaConstant ↔
      ∃ g : E(2), s = g '' (Bridge.point '' gerverSofa P) := by
  exact MovingSofa.Canonical.volume_eq_constant_iff_congruent_paper_gerver hP hbox s hs

/-- Nondegeneracy is derived from the original non-strict reference domain. -/
example {A B φ θ : ℝ} (h : Reference.Spec A B φ θ) :
    0 < φ ∧ φ < θ ∧ θ ≤ π / 4 := by
  exact h.strict_order

/-- Reconstructing the coefficients is separate from solving the two angle equations. -/
example {A B A' B' φ θ : ℝ} (h : Reference.Spec A B φ θ)
    (h' : Reference.Spec A' B' φ θ) : A = A' ∧ B = B' := by
  exact Reference.coefficients_unique h h'

end MovingSofaUniquenessFC.Tests
