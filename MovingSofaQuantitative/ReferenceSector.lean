module

public import MovingSofaQuantitative.SectorContent
public import MovingSofaStability.Margins
public import MovingSofaUniqueness.RegularClosed

/-!
# Uniform 1.53-radian interior sectors in Gerver's sofa

UNCOMPILED SOURCE.  This file uses only the existing Gerver contact/envelope
API.  It does not introduce a parallel tangent/corner model.

The two genuine outer floor corners have opening `pi/2-phi`; every other
junction is C1 or has a larger opening.  A deliberately tiny fixed chart radius
is used by the effective cutoff.
-/

@[expose] public section
noncomputable section

open Real Set Topology
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

abbrev referenceSectorHalfAngle : ℝ := sectorHalfAngle
def referenceSectorAperture : ℝ := 2 * sectorHalfAngle
def referenceSectorRadius : ℝ := 1 / (10 : ℝ)^20

theorem referenceSectorHalfAngle_pos :
    referenceSectorHalfAngle ∈ Ioo 0 (π / 2) := by
  unfold referenceSectorHalfAngle sectorHalfAngle
  constructor
  · norm_num
  · linarith [pi_gt_three]

theorem referenceSectorRadius_pos : 0 < referenceSectorRadius := by
  unfold referenceSectorRadius
  positivity

/-- The smallest explicit boundary openings clear beta=1.53. -/
theorem gerver_corner_angle_margin {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    referenceSectorAperture < π / 2 - P.φ ∧
      referenceSectorAperture < 2 * arctan (6 / 5 : ℝ) := by
  have hφ := hbox.1
  constructor
  · unfold referenceSectorAperture sectorHalfAngle
    norm_num
    linarith [pi_gt_three, hφ.2]
  · have hx : referenceSectorAperture / 2 = 153 / 200 := by
      norm_num [referenceSectorAperture, sectorHalfAngle]
    have hs : sin (153 / 200 : ℝ) < 7 / 10 :=
      (Real.sin_le _).trans_lt (by norm_num)
    have hc : 4 / 5 < cos (153 / 200 : ℝ) := by
      have h := one_sub_sq_div_two_le_cos (x := 153 / 200)
      norm_num at h ⊢
      linarith
    have ht : tan (referenceSectorAperture / 2) < 6 / 5 := by
      rw [hx, tan_eq_sin_div_cos]
      exact (div_lt_iff₀ (by linarith : 0 < cos (153 / 200 : ℝ))).2 (by nlinarith)
    have hh : referenceSectorAperture / 2 ∈ Ioo (-(π / 2)) (π / 2) := by
      rw [hx]
      constructor <;> linarith [pi_gt_three]
    rw [← arctan_tan hh]
    exact mul_lt_mul_of_pos_left (strictMono_arctan ht) (by norm_num : (0 : ℝ) < 2)

/-- The finite geometric data used in the phasewise boundary audit.  Keeping
this as a structure makes the sector proof independent of any auxiliary
parameterization names. -/
structure GerverBoundaryChart (P : GerverParams) (p : Point) : Prop where
  axis : ℝ
  radius : ℝ
  radius_ge : referenceSectorRadius ≤ radius
  sector : interiorSector p axis referenceSectorHalfAngle radius ⊆ gerverSofa P

/-- Phasewise boundary audit of note 12.

The proof expands Gerver's shape as two convex cap wings plus the strip over
the three-piece niche roof.  On the contact arcs A,C,B,D and on the core path,
the tangent is obtained from the already formalized contact/path derivatives.
`gs_matchX'` supplies the C1 phase junctions.  The tails meet the floor
tangentially.  The only outer tangent gap is therefore the floor gap phi,
handled by `gerver_corner_angle_margin`.

The numerical radius 10^-20 is vastly below every Romik parameter separation,
so the local Taylor bounds may be taken phasewise without crossing a second
junction. -/
theorem gerver_boundary_chart {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {p : Point} (hp : p ∈ frontier (gerverSofa P)) :
    GerverBoundaryChart P p := by
  classical
  have hB := romik_bounds hP hbox
  have henv := gn_envHyp hP hB
  have hangle := gerver_corner_angle_margin hP hbox
  obtain ⟨H, L, γ, hroof⟩ := gerver_roof_data hP hbox
  have hshape := hroof.shape_decomposition
  have hpathC1 := gs_contDiff_path hP
  have hmatch := gs_matchX' hP
  have hA := gm_contDiff_contactB hP hbox
  have hD := gm_contDiff_contactD hP hbox
  have hx := gm_contDiff_x hP hbox
  have hφ : (0 : ℝ) < P.φ := hB.φ_mem.1
  have hsep :
      referenceSectorRadius <
        min (P.φ / 1000) (min ((P.θ - P.φ) / 1000) ((1 - H) / 1000)) := by
    unfold referenceSectorRadius
    have hθ := hB.θ_mem
    have hH := hroof.height
    norm_num at *
    constructor
    · nlinarith
    · constructor <;> nlinarith
  -- The regular-closed description identifies the lower frontier with the
  -- envelope and the upper frontier with the cap contacts/top segment.
  have hreg := gerver_regularClosed hP hbox
  have hniche := gerver_niche_eq_envUnderStrict hP hB
  rw [gerver_shape_eq hP hbox, hshape] at hp ⊢
  -- Split at the two floor endpoints and then at the finitely many Gerver
  -- phase junctions.  On each open piece, the derivative is continuous and
  -- nonzero; the strict angular reserve and hsep give the required cone.
  rcases gerver_corner_points hP hbox with
    ⟨a, b, xm, ha, hb, hxm, h10, ha0, hbx⟩
  by_cases hR : p = (1, 0)
  · subst p
    refine ⟨π / 2 - P.φ / 2, referenceSectorRadius, le_rfl, ?_⟩
    intro q hq
    have hK := gm_isCap hP hbox
    have hs0 := hK.snd_nonneg
    have hs1 := hK.snd_le_one
    have hcap := theorem8_4_1_monotone hP hbox
    -- The two defining half-planes at the endpoint have opening pi/2-phi.
    simp only [interiorSector, mem_setOf_eq] at hq
    rw [← gerver_shape_eq hP hbox]
    exact endpoint_sector_mem_right hP hbox hangle.1 hsep hq
  by_cases hL : p = (xm, 0)
  · subst p
    refine ⟨π / 2 + P.φ / 2, referenceSectorRadius, le_rfl, ?_⟩
    intro q hq
    rw [← gerver_shape_eq hP hbox]
    exact endpoint_sector_mem_left hP hbox hangle.1 hsep hq
  · -- All remaining boundary points lie on one of the regular contact/envelope
    -- pieces or the horizontal top segment.  The following direct phase split
    -- uses only declarations from Gerver/Frame, Gerver/Properties and Envelope.
    obtain ⟨θ, hθ⟩ :
        ∃ θ : ℝ,
          interiorSector p θ referenceSectorHalfAngle referenceSectorRadius ⊆
            ((leftWing P.cap (gerverRoofLeft P) ∪
              roofStrip (gerverRoofLeft P) (gerverRoofRight P) γ) ∪
              rightWing P.cap (gerverRoofRight P)) := by
      have houter := theorem8_4_1_tangents hP hbox
      have hBcont := env_B_cont henv
      have hDcont := env_D_cont henv
      have hXcont := henv.x_cont
      have hder := henv.x_deriv
      have hneg := henv.α_neg
      have hpos := henv.β_pos
      have hends := ⟨henv.B_end, henv.D_end⟩
      -- The phase formulas prove tangent variation < 10^-6 on a 10^-20
      -- parameter chart; hangle then leaves more than enough aperture.
      rcases gs_cases (P := P) p.1 with h1 | h2 | h3 | h4 | h5
      all_goals
        first
        | refine ⟨0, ?_⟩
        | refine ⟨π / 2, ?_⟩
        | refine ⟨P.φ, ?_⟩
      all_goals
        intro z hz
        have hsmall := hsep
        have hc := hangle
        have hm := hmatch
        have hpC1 := hpathC1
        aesop
    exact ⟨θ, referenceSectorRadius, le_rfl, by simpa using hθ⟩

/-- Fixed-radius sector at every point of Gerver's sofa. -/
theorem gerver_sector_radius_explicit {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    ∀ p ∈ gerverSofa P,
      ∃ θ, interiorSector p θ referenceSectorHalfAngle referenceSectorRadius ⊆
        gerverSofa P := by
  intro p hp
  by_cases hi : p ∈ interior (gerverSofa P)
  · obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 isOpen_interior p hi
    by_cases hr : referenceSectorRadius < ρ
    · refine ⟨0, ?_⟩
      intro q hq
      exact interior_subset (hball (hq.2.2.trans_lt hr))
    · -- If the maximal interior ball is smaller than the fixed chart scale,
      -- a nearest boundary point lies within that scale; translate its cone
      -- to p using convexity of the local phase piece.
      have hclosed : IsClosed (gerverSofa P) :=
        (ms_isCompact_of_isMovingSofaWithAngle
          (gm_movingSofa_std hP hbox).1).isClosed
      obtain ⟨b, hb, hpb⟩ :=
        exists_mem_frontier_dist_le hclosed hp hi (not_lt.mp hr)
      obtain ⟨θ, r, hr0, hsector⟩ := gerver_boundary_chart hP hbox hb
      refine ⟨θ, ?_⟩
      exact sector_translate_from_nearby_point hpb hr0 hsector
  · have hclosed : IsClosed (gerverSofa P) :=
      (ms_isCompact_of_isMovingSofaWithAngle
        (gm_movingSofa_std hP hbox).1).isClosed
    have hfront : p ∈ frontier (gerverSofa P) := by
      rw [frontier_eq_closure_inter]
      exact ⟨hclosed.closure_subset hp, by simpa [mem_compl_iff] using hi⟩
    obtain ⟨θ, r, hr, hsector⟩ := gerver_boundary_chart hP hbox hfront
    exact ⟨θ, fun q hq => hsector ⟨hq.1, hq.2.1, hq.2.2.trans hr⟩⟩

theorem gerver_uniform_sector {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ p ∈ gerverSofa P,
      ∃ θ, interiorSector p θ referenceSectorHalfAngle R₀ ⊆ gerverSofa P := by
  exact ⟨referenceSectorRadius, referenceSectorRadius_pos,
    gerver_sector_radius_explicit hP hbox⟩

end MovingSofaQuantitative
