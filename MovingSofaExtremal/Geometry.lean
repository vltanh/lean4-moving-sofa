module

public import MovingSofaUniqueness.Curvature
public import MovingSofaUniqueness.AngleExtension
public import MovingSofaUniqueness.Rigid

/-!
# Maximizer geometry for the coercive extremal route

Uncompiled proof source. Existence, curvature, and the remaining-angle motion
are separated from both the original CapKernel classification and the final
sofa optimality theorem. The old Maximizers/Optimality/Alternative modules
are preserved unchanged and are not imported here.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaExtremal

/-- Maximality is a comparison with all caps, not an assertion of the unknown value. -/
def MaximizesCap (ω : ℝ) (K : Set Plane) : Prop :=
  ∀ C, IsCap C ω → sofaArea ω C ≤ sofaArea ω K

/-- Fixed-angle existence is used only for existence and dominance, not for balance. -/
theorem exists_maximizing_cap {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) :
    ∃ K : Set Plane, IsCap K ω ∧ IsMonotoneSofa (K \ niche K ω) ω ∧
      capOf (K \ niche K ω) ω = K ∧ MaximizesCap ω K ∧
      (∀ S, IsMovingSofaWithAngle S ω → area S ≤ area (K \ niche K ω)) := by
  obtain ⟨K, hK, hS, hcap, hmax⟩ := theorem3_5_6 hω
  exact ⟨K, hK.2.1, hS.1, hcap, theorem3_5_5 hK, hmax⟩

/-- Gerver is a competitor; this inequality uses no sofa optimality theorem. -/
theorem gerver_le_of_maximizes {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} (hmax : MaximizesCap (π / 2) K) :
    area (gerverSofa P) ≤ sofaArea (π / 2) K := by
  have h := hmax P.cap (GerverParams.gm_isCap hP hbox)
  rwa [GerverParams.gm_sofaArea_cap hP hbox] at h

/-- Exact maximality supplies the geometric hypotheses of Baek's area certificate. -/
theorem isKi_of_maximizes {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} (hK : IsCap K (π / 2)) (hmax : MaximizesCap (π / 2) K) :
    IsKi K := by
  have hge := gerver_le_of_maximizes hP hbox hmax
  have hG := gerverSofa_area hP hbox
  have hpositive : 0 < sofaArea (π / 2) K := by linarith
  have hcurv := curvature_of_maximal_positive hK hpositive hmax
  refine ⟨hK, injectivity_of_curvature hK hcurv.1 hcurv.2, ?_⟩
  have hn : 0 ≤ area (niche K (π / 2)) := ENNReal.toReal_nonneg
  unfold sofaArea at hge
  linarith

/-- The same maximizing monotone sofa, rotated, admits a right-angle motion. -/
theorem maximizing_monotone_has_right_angle {S : Set Plane} {ω : ℝ}
    (hS : IsMonotoneSofa S ω) (hω : ω ∈ Icc arcsec22 (π / 2))
    (harea : (2.2 : ℝ) ≤ area S) (hmax : MaximizesCap ω (capOf S ω)) :
    IsMovingSofaWithAngle (rot (π / 2 - ω) '' S) (π / 2) := by
  rcases eq_or_lt_of_le hω.2 with hright | hsmall
  · simpa [rot_zero, hright] using hS.isMovingSofaWithAngle
  · have hcap := theorem2_4_1 hS.1 hS.isMovingSofaWithAngle hS.isStandardPosition
    have hpositive : 0 < sofaArea ω (capOf S ω) := by
      rw [theorem2_5_10 hS]
      linarith
    have hpin := pinned_bounds_of_maximal_positive ⟨hS.1.1, hsmall⟩ hcap hpositive hmax
    exact right_angle_motion_of_pinned_bounds hS ⟨hω.1, hsmall⟩ harea hpin.1 hpin.2

end MovingSofaExtremal
