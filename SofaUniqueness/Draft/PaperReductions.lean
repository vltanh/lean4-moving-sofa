module

public import MovingSofa.Optimality.Equality
public import SofaUniqueness.Draft.CapKernel
public import SofaUniqueness.Draft.CapGeometry
public import SofaUniqueness.Draft.Selection
public import SofaUniqueness.Draft.AngleExtension
public import SofaUniqueness.InjectivityFromCurvature
public import SofaUniqueness.MamikonCapKernel
public import SofaUniqueness.GerverRegularClosed

/-!
# UNCOMPILED, INCOMPLETE DRAFT: the remaining variational reductions

Two admissions remain in this file: P2 and P4. The Mamikon kernel extraction
(P1), curvature-to-injectivity implication (P3), angular extension (P5), and
regular-closedness of Gerver's sofa (P6) now have explicit scripts in the
imported modules. No successful elaboration or completed uniqueness proof is
claimed while P2 and P4 remain admitted.

The old balanced-maximizer theorems are deliberately not applied to an
arbitrary specified maximizer. That invalid shortcut would lose the original
sofa and is precisely what the two remaining variational limits must avoid.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofa

namespace SofaUniqueness.Draft

/-- A specified cap, not a cap chosen from an existence theorem. -/
def IsMaxCap (ω : ℝ) (K : Set Plane) : Prop :=
  IsCap K ω ∧ ∀ C, IsCap C ω → sofaArea ω C ≤ sofaArea ω K

theorem moving_of_monotone {S : Set Plane} {ω : ℝ}
    (hS : IsMonotoneSofa S ω) : IsMovingSofaWithAngle S ω := by
  obtain ⟨hω, T, hT, hstd, rfl⟩ := hS
  exact (theorem2_3_2 hω hT hstd).1

theorem area_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofa.Paper.IsMovingSofa S) :
    area S ≤ area (gerverSofa P) := by
  exact ENNReal.toReal_mono (gerverSofa_volume_ne_top hP hbox)
    ((theorem1_1_1 hP hbox).2 S hS)

/-- Balanced cap existence is used here for a NUMBER bound only. -/
theorem cap_area_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} {ω : ℝ} (hK : IsCap K ω) :
    sofaArea ω K ≤ area (gerverSofa P) := by
  obtain ⟨B, hB, hS, hcap, _⟩ := theorem3_5_6 hK.1
  have hle := theorem3_5_5 hB K hK
  have hval := theorem2_5_10 hS.1
  rw [hcap] at hval
  have harea := area_le_gerver hP hbox ⟨ω, moving_of_monotone hS.1⟩
  linarith

theorem isMaxCap_of_area_eq {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} {ω : ℝ} (hK : IsCap K ω)
    (heq : sofaArea ω K = area (gerverSofa P)) : IsMaxCap ω K := by
  refine ⟨hK, fun C hC => ?_⟩
  rw [heq]
  exact cap_area_le_gerver hP hbox hC

/-- P1: all four zero Mamikon gaps yield the endpoint-safe support kernel. -/
theorem capKernel_of_mamikon_midpoint {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (x y : LTriple φ) (h : MamikonSegmentEquality φ x y (1 / 2)) :
    CapKernel φ (fun t => supp y.1.1.1 t - supp x.1.1.1 t) := by
  exact SofaUniqueness.capKernel_of_triple_midpoint hφ x y h

/-- Endpoint-safe curvature estimates. The possible top atom is excluded;
the atoms at 0 and pi are included. -/
def CurvatureBounds (K : Set Plane) : Prop :=
  (sigma K).restrict (Ico 0 (π / 2)) ≤
    (volume.restrict (Ico 0 (π / 2))).withDensity
      (fun t => ENNReal.ofReal (k0 (gPlus K t))) ∧
  (sigma K).restrict (Ioc (π / 2) π) ≤
    (volume.restrict (Ioc (π / 2) π)).withDensity
      (fun t => ENNReal.ofReal (k0 (fMinus K (t - π / 2))))

/-- DRAFT-P2: specified-cap selection, finite-angle variation and weak limits.

Use upper-support penalization, exact sine hats, and an eventually inactive
horizontal box. Each facet defect is O(lambda*delta), with total error
O(lambda+delta). The local ray estimate is
  tau(t) <= tan(delta)*(abs(gPlus(t)-1)+tan(delta/2))
             + max (2*tan(delta/2)-sigmaAt(t)) 0.
Tests crossing zero are required before concluding that it has no atom.
Sources: notes 10, 12 and 13. The abstract selection comparison alone does
not prove the missing geometric compactness, variations or limiting estimate.
-/
theorem curvatureBounds_of_isMaxCap {K : Set Plane}
    (hK : IsMaxCap (π / 2) K) : CurvatureBounds K := by
  sorry

/-- P3: both curvature bounds imply injectivity of this same cap. -/
theorem injectivity_of_curvatureBounds {K : Set Plane}
    (hK : IsCap K (π / 2)) (hbound : CurvatureBounds K) : SatisfiesInjectivity K := by
  exact SofaUniqueness.injectivity_of_curvature hK hbound.1 hbound.2

theorem isKi_of_maximal_area {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} (hK : IsCap K (π / 2))
    (heq : sofaArea (π / 2) K = area (gerverSofa P)) : IsKi K := by
  refine ⟨hK, injectivity_of_curvatureBounds hK
    (curvatureBounds_of_isMaxCap (isMaxCap_of_area_eq hP hbox hK heq)), ?_⟩
  have hG := gerverSofa_area hP hbox
  have hn : 0 ≤ area (niche K (π / 2)) := ENNReal.toReal_nonneg
  unfold sofaArea at heq
  linarith

/-- The two pinned inequalities for the specified smaller-angle cap. -/
def PinnedBounds (ω : ℝ) (K : Set Plane) : Prop :=
  wedgeGapWInf K ω ≤ sigmaAt K (π / 2) ∧ wedgeGapZInf K ω ≤ sigmaAt K ω

/-- DRAFT-P4: pinned-strip variation for a specified maximizer.

A common interior ball is needed. Actual and assigned supports must be
compared in the correct direction. Sum the positive weighted defects and
use sum d(t)*sin(t)=0 to control negative pinned defects. Upper semicontinuity
of the fixed atoms and continuity of the gap infima complete the limit.
Sources: notes 10, 12, 14 (sections 1-7) and 15.
-/
theorem pinnedBounds_of_isMaxCap {K : Set Plane} {ω : ℝ}
    (hω : ω ∈ Ioo 0 (π / 2)) (hK : IsMaxCap ω K) : PinnedBounds ω K := by
  sorry

/-- P5: the specified sofa admits the additional motion from its pinned bounds. -/
theorem right_angle_motion_of_pinned {S : Set Plane} {ω : ℝ}
    (hS : IsMonotoneSofa S ω) (hω : ω ∈ Ico arcsec22 (π / 2))
    (harea : (2.2 : ℝ) ≤ area S) (hpin : PinnedBounds ω (capOf S ω)) :
    ∃ a : ℝ, IsMovingSofaWithAngle (rot a '' S) (π / 2) := by
  exact right_angle_motion_of_pinned_bounds hS hω harea hpin.1 hpin.2

/-- P6: regular-closedness is proved for the actual library Gerver sofa. -/
theorem regularClosed_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    closure (interior (gerverSofa P)) = gerverSofa P := by
  exact SofaUniqueness.gerver_regularClosed hP hbox

/-- The four cap kernels identify the actual cap-minus-niche set. -/
theorem ki_sofa_eq_gerver_translate {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {K : Set Plane} (hK : IsKi K)
    (heq : sofaArea (π / 2) K = area (gerverSofa P)) :
    ∃ a : ℝ, K \ niche K (π / 2) = Rigid.translate (a, 0) '' gerverSofa P := by
  have hmid := (ki_maximizer_equality_conditions hP hbox hK heq).2
    (1 / 2) (by constructor <;> norm_num)
  have hker := capKernel_of_mamikon_midpoint (gm_φ_mem_Ioo hP hbox)
    (gerverTriple hP hbox) (kiExtensionTriple hbox.1 hK) hmid
  change CapKernel P.φ (fun t => supp K t - supp P.cap t) at hker
  let a := -(supp K π - supp P.cap π)
  have hsupp : ∀ t ∈ Icc (0 : ℝ) π, supp K t - supp P.cap t = a * cos t :=
    hker.eq_horizontal_translation (gm_φ_mem_Ioo hP hbox)
  refine ⟨a, ?_⟩
  have hGset : gerverSofa P = P.cap \ niche P.cap (π / 2) :=
    theorem2_4_3 (gm_isMonotone hP hbox)
  rw [hGset]
  exact sofa_eq_translate_of_upper_support hK.1 (gm_isCap hP hbox) a hsupp

end SofaUniqueness.Draft
