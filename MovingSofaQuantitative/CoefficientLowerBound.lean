module

public import MovingSofaQuantitative.Targets
public import MovingSofaQuantitative.CenteredKernel

/-!
# Two endpoint results with exact statement contracts

Proof source, not yet compiled in this session. The sofa lower bound uses the
integrated puncture family, including its lower distance bound for EVERY rigid
alignment. It is not a fixed-alignment argument. The rational cap coefficient
is only the scalar coefficient statement, not yet the centered cap estimate.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability

namespace MovingSofaQuantitative

/-- Any uniform square-root Hausdorff coefficient, even allowing arbitrary
rigid alignment, is at least 1/sqrt(pi). -/
theorem sofaCoefficientLower : Targets.SofaCoefficientLower := by
  intro P hP hbox C ε₀ hε₀ hbound
  obtain ⟨p, r₀, hr₀, hfamily⟩ := punctured_gerver_family hP hbox
  obtain ⟨r, hr, hrsmall, harea, _⟩ :=
    exists_puncture_scale (a := 1) (C := 0) (by norm_num) hε₀ hr₀
  obtain ⟨hmove, hdef, _, hminimal, _⟩ := hfamily r hr hrsmall
  have hpositive : 0 < sofaDeficit P (puncture (gerverSofa P) p r) := by
    rw [hdef]
    positivity
  have hsmall : sofaDeficit P (puncture (gerverSofa P) p r) < ε₀ := by
    rwa [hdef]
  obtain ⟨g, hg⟩ := hbound _ hmove hpositive hsmall
  have hmin := hminimal g _ hg
  rw [hdef, sqrt_mul pi_pos.le, sqrt_sq hr.le] at hmin
  have hscaled : 1 * r ≤ (C * sqrt π) * r := by nlinarith only [hmin]
  have hone : 1 ≤ C * sqrt π := (mul_le_mul_right hr).mp hscaled
  exact (div_le_iff₀ (sqrt_pos.2 pi_pos)).2 hone

/-- The source-box rational inequality appearing in the centered-cap statement. -/
theorem centeredNumeric : Targets.CenteredNumeric := by
  intro φ hφ
  exact sec_phi_rational_bound hφ

end MovingSofaQuantitative
