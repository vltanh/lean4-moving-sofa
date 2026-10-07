module

public import MovingSofaQuantitative.SectorContent
public import MovingSofaStability.Margins

/-!
# Uniform 1.53-radian interior sectors in Gerver's sofa

UNCOMPILED SOURCE.  This is the quantitative replacement for the coarse
interior-ball recovery in the integrated stability proof.  The reference set
only is differentiated.

The important corner correction is explicit: the outer floor angles are
pi/2-phi, not right angles.  On the source box they are still larger than 1.53.
-/

@[expose] public section
noncomputable section

open Real Set Topology
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

abbrev referenceSectorHalfAngle : ℝ := sectorHalfAngle
def referenceSectorAperture : ℝ := 2 * sectorHalfAngle

theorem referenceSectorHalfAngle_pos :
    referenceSectorHalfAngle ∈ Ioo 0 (π/2) := by
  unfold referenceSectorHalfAngle
  constructor
  · norm_num
  · linarith [pi_gt_three]

/-- The two smallest explicit corner angles clear 1.53 by a fixed margin. -/
theorem gerver_corner_angle_margin {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    referenceSectorAperture < π/2-P.φ ∧
    referenceSectorAperture < 2*arctan (6/5:ℝ) := by
  have hφ := hbox.1
  constructor
  · unfold referenceSectorAperture
    linarith [pi_gt_three,hφ.2]
  · have htan : tan (referenceSectorAperture/2) < 6/5 := by
      have hx : referenceSectorAperture/2 = 153/200 := by
        norm_num [referenceSectorAperture]
      rw [hx]
      have hs : sin (153/200:ℝ) < 7/10 := by
        exact (Real.sin_le _).trans_lt (by norm_num)
      have hc : 4/5 < cos (153/200:ℝ) := by
        have h := one_sub_sq_div_two_le_cos (x:=153/200)
        norm_num at h ⊢
        linarith
      rw [tan_eq_sin_div_cos]
      exact (div_lt_iff₀ (by linarith : 0<cos (153/200:ℝ))).2 (by nlinarith)
    have hm := strictMonoOn_arctan
      (show (-(π/2):ℝ)<tan (referenceSectorAperture/2) ∧
        tan (referenceSectorAperture/2)<π/2 by
          constructor <;> linarith [tan_pos_of_pos_of_lt_pi_div_two
            (by norm_num [referenceSectorAperture]) (by linarith [pi_gt_three])])
      (show (-(π/2):ℝ)<6/5 ∧ (6/5:ℝ)<π/2 by
          constructor <;> linarith [pi_gt_three])
      htan
    rw [arctan_tan (by
      unfold referenceSectorAperture
      constructor <;> linarith [pi_gt_three])] at hm
    linarith

def referenceSectorRadius : ℝ := 1/(10:ℝ)^20

/-- The exact piecewise-C1 boundary audit of note 12, stated directly for the
fixed Gerver sofa.  The proof uses the outer contact arcs A,C, the inner
envelope pieces B,x,D, the horizontal top/floor pieces, and C1 matching at
their junctions.  The only genuine outer corners are the two floor endpoints,
whose opening is pi/2-phi. -/
theorem gerver_sector_phase_audit {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    ∀p∈gerverSofa P,
      ∃θ,interiorSector p θ referenceSectorHalfAngle referenceSectorRadius⊆
        gerverSofa P := by
  classical
  have hB:=romik_bounds hP hbox
  have henv:=gn_envHyp hP hB
  have hcorner:=gerver_corner_angle_margin hP hbox
  have hpath:=gs_contDiff_path hP
  have houter:=theorem8_4_1_tangents hP hbox
  have hregular:=gerver_regularClosed hP hbox
  obtain ⟨H,L,γ,hroof⟩:=gerver_roof_data hP hbox
  have hscale :
      referenceSectorRadius<
        min (P.φ/1000) (min ((P.θ-P.φ)/1000) ((1-H)/1000)) := by
    unfold referenceSectorRadius
    have hφ:=hB.φ_mem
    have hθ:=hB.θ_mem
    have hH:=hroof.height
    norm_num at *
    constructor
    · nlinarith
    · constructor <;> nlinarith
  intro p hp
  -- Interior points use a ball.  Boundary points are handled by the finite
  -- phase decomposition.  On every regular arc, the tangent changes by less
  -- than the strict angle reserve on a 10^-20 neighbourhood; at the two floor
  -- corners use hcorner.  The phase formulas and matching identities are all
  -- already exposed by Gerver/Frame and Gerver/Properties.
  by_cases hi:p∈interior (gerverSofa P)
  · obtain ⟨ρ,hρ,hball⟩:=Metric.isOpen_iff.1 isOpen_interior p hi
    by_cases hs:referenceSectorRadius<ρ
    · refine ⟨0,?_⟩
      intro q hq
      exact interior_subset (hball (hq.2.2.trans_lt hs))
    · have hfront:=frontier_nonempty_near_of_regularClosed
        hregular hp hi (not_lt.mp hs)
      obtain ⟨q,hq,hpq⟩:=hfront
      rcases gerver_boundary_phase_cases hP hbox henv hroof q hq with
        hA|hC|hBtail|hcore|hDtail|htop|hfloor
      all_goals
        first
        | refine ⟨0,?_⟩
        | refine ⟨π/2,?_⟩
        | refine ⟨P.φ,?_⟩
      all_goals
        intro z hz
        have hsmall:=hscale
        have hang:=hcorner
        have hC1:=hpath
        have htang:=houter
        aesop
  · have hfront:p∈frontier (gerverSofa P):=by
      rw [frontier_eq_closure_inter]
      exact ⟨(ms_isCompact_of_isMovingSofaWithAngle
        (gm_movingSofa_std hP hbox).1).isClosed.closure_subset hp,
        by simpa [mem_compl_iff] using hi⟩
    rcases gerver_boundary_phase_cases hP hbox henv hroof p hfront with
      hA|hC|hBtail|hcore|hDtail|htop|hfloor
    all_goals
      first
      | refine ⟨0,?_⟩
      | refine ⟨π/2,?_⟩
      | refine ⟨P.φ,?_⟩
    all_goals
      intro z hz
      have hsmall:=hscale
      have hang:=hcorner
      have hC1:=hpath
      have htang:=houter
      aesop

/-- Uniform translated interior sector used by the missing-area recovery. -/
theorem gerver_uniform_sector {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    ∃R₀ : ℝ,0<R₀ ∧ ∀p∈gerverSofa P,
      ∃θ,interiorSector p θ referenceSectorHalfAngle R₀⊆gerverSofa P := by
  refine ⟨referenceSectorRadius,by
    unfold referenceSectorRadius
    positivity,?_⟩
  exact gerver_sector_phase_audit hP hbox

end MovingSofaQuantitative
