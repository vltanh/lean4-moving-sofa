module

public import MovingSofaStability.PuncturedSofa

/-!
# A necessary lower bound on any unrestricted Hausdorff coefficient

Uncompiled proof source. This is a coefficient obstruction, complementing the
existing exponent-sharpness theorem. It quantifies over arbitrary rigid
alignments and any positive near-optimality threshold. It does not claim that
the puncture bound is the optimal coefficient.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- Every universal square-root Hausdorff coefficient is at least 1/sqrt(pi),
even when the alignment may depend on the sofa. -/
theorem universal_hausdorff_coefficient_lower_bound {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {C ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hbound : ∀ S : Set Point, IsMovingSofa S → sofaDeficit P S < ε₀ →
      ∃ g : Rigid, EuclideanClose (C * sqrt (sofaDeficit P S)) S (g '' gerverSofa P)) :
    1 / sqrt π ≤ C := by
  obtain ⟨p, r₀, hr₀, hfamily⟩ := punctured_gerver_family hP hbox
  let R := sqrt (ε₀ / π)
  have hR : 0 < R := sqrt_pos.mpr (div_pos hε₀ pi_pos)
  let r := min r₀ R / 2
  have hr : 0 < r := div_pos (lt_min hr₀ hR) (by norm_num)
  have hrmin : r < min r₀ R := by dsimp [r]; linarith [lt_min hr₀ hR]
  have hrr₀ : r < r₀ := hrmin.trans_le (min_le_left _ _)
  have hrR : r < R := hrmin.trans_le (min_le_right _ _)
  have hRsq : R ^ 2 = ε₀ / π := sq_sqrt (div_nonneg hε₀.le pi_pos.le)
  have hpiR : π * (ε₀ / π) = ε₀ := by field_simp
  have hr2 : r ^ 2 < ε₀ / π := by nlinarith
  have harea : π * r ^ 2 < ε₀ := by
    have hmul := mul_lt_mul_of_pos_left hr2 pi_pos
    linarith
  obtain ⟨hmove, hdef, _, hmin, _⟩ := hfamily r hr hrr₀
  obtain ⟨g, hg⟩ := hbound (puncture (gerverSofa P) p r) hmove (by rwa [hdef])
  have hrad := hmin g _ hg
  rw [hdef, sqrt_mul pi_pos.le, sqrt_sq_eq_abs, abs_of_pos hr] at hrad
  have hcoeff : 1 ≤ C * sqrt π := by
    apply (mul_le_mul_right hr).mp
    nlinarith only [hrad]
  apply (div_le_iff₀ (sqrt_pos.mpr pi_pos)).mpr
  nlinarith only [hcoeff]

end MovingSofaStability
