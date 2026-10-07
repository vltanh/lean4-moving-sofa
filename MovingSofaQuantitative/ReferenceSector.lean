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

def referenceSectorAperture : ℝ := 153/100
def referenceSectorHalfAngle : ℝ := 153/200

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

/-- Local epigraph lemma in a rotated tangent chart.  If the tangent turns by
at most eta<pi/2-h, the epigraph contains a sector of half-angle h. -/
theorem rotated_epigraph_contains_sector
    {γ : ℝ→Point} {t₀ R h η : ℝ}
    (hh : h∈Ioo 0 (π/2)) (hη : 0≤η) (hreserve : h+η<π/2)
    (hγ : ContinuousOn γ (Icc (t₀-R) (t₀+R)))
    (htan : ∀s∈Icc (t₀-R) (t₀+R),
      angleBetween (tangentUnit γ s) (tangentUnit γ t₀)≤η)
    (hinside : ∀s∈Icc (t₀-R) (t₀+R),
      localInwardHalfplane γ s ⊆ localShape γ) :
    interiorSector (γ t₀) (inwardNormalAngle γ t₀) h
      (R/4) ⊆ localShape γ := by
  intro q hq
  have hproj₁ := hq.1
  have hproj₂ := hq.2.1
  have hdist := hq.2.2
  have hcone := cone_between_rotated_normals hh hη hreserve htan hproj₁ hproj₂
  exact local_epigraph_mem_of_cone hγ hinside hdist hcone

/-- Phasewise reference tangent variation.  The loose constants are chosen to
make the proof uniform through the C1 phase junctions. -/
theorem gerver_tangent_turning {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ r : ℝ, 0<r ∧
      ∀ t∈Icc (0:ℝ) (π/2), ∀s∈Icc (max 0 (t-r)) (min (π/2) (t+r)),
        angleBetween (referenceBoundaryTangent P s)
          (referenceBoundaryTangent P t) ≤ 1/100 := by
  let r : ℝ := 1/20000
  refine ⟨r,by norm_num,?_⟩
  intro t ht s hs
  have hB := romik_bounds hP hbox
  have hvel : ∀u∈Icc (0:ℝ) (π/2),
      1/2≤norm2 (referenceBoundaryVelocity P u) ∧
      norm2 (referenceBoundaryVelocity P u)≤10 := by
    intro u hu
    exact reference_velocity_bounds hP hbox hu
  have hLip : ∀u v, u∈Icc (0:ℝ) (π/2) → v∈Icc (0:ℝ) (π/2) →
      norm2 (referenceBoundaryVelocity P u-referenceBoundaryVelocity P v)≤100*|u-v| := by
    exact reference_velocity_lipschitz hP hbox
  have hst : |s-t|≤r := by
    dsimp [r] at *
    constructor <;> linarith [hs.1,hs.2]
  have hv := hLip s t
    ⟨(max_le_iff.mp hs.1).1,(min_le_iff.mp hs.2).1⟩ ht
  have hu := unit_direction_angle_le
    (hvel s ⟨(max_le_iff.mp hs.1).1,(min_le_iff.mp hs.2).1⟩).1
    (hvel t ht).1 (hv.trans (by dsimp [r]; nlinarith [hst]))
  exact hu.trans (by norm_num)

/-- The smooth reference boundary away from its finitely many junctions has
a uniform sector. -/
theorem gerver_smooth_sector {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ R : ℝ, 0<R ∧
      ∀p∈gerverSofa P, referenceSmoothPoint P p →
        ∃θ, interiorSector p θ referenceSectorHalfAngle R ⊆ gerverSofa P := by
  obtain ⟨r,hr,hturn⟩ := gerver_tangent_turning hP hbox
  let R := min (r/8) (1/100000)
  refine ⟨R,lt_min (by positivity) (by norm_num),?_⟩
  intro p hp hsmooth
  obtain ⟨t,ht,rfl⟩ := hsmooth.parameter
  refine ⟨inwardNormalAngle (referenceBoundaryCurve P) t,?_⟩
  apply rotated_epigraph_contains_sector referenceSectorHalfAngle_pos
    (show (0:ℝ)≤1/100 by norm_num)
    (by
      unfold referenceSectorHalfAngle
      linarith [pi_gt_three])
    (referenceBoundaryCurve_continuous hP hbox)
    (fun s hs => hturn t ht s (by
      constructor <;> dsimp [R] at * <;> linarith))
    (reference_boundary_inward_halfplanes hP hbox hp)

/-- The finite corner list has the same sector aperture. -/
theorem gerver_corner_sectors {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ R : ℝ, 0<R ∧
      ∀p∈gerverSofa P, referenceCornerPoint P p →
        ∃θ, interiorSector p θ referenceSectorHalfAngle R ⊆ gerverSofa P := by
  have hang := gerver_corner_angle_margin hP hbox
  let R : ℝ := 1/100000
  refine ⟨R,by norm_num,?_⟩
  intro p hp hcorner
  rcases hcorner.classification with hfloor | hroof | htangent
  · exact floor_corner_sector hP hbox hp hfloor hang.1 (by norm_num [R])
  · exact roof_corner_sector hP hbox hp hroof hang.2 (by norm_num [R])
  · exact tangent_junction_sector hP hbox hp htangent referenceSectorHalfAngle_pos
      (by norm_num [R])

/-- Uniform translated interior sector used by the missing-area recovery. -/
theorem gerver_uniform_sector {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ R₀ : ℝ, 0<R₀ ∧ ∀p∈gerverSofa P,
      ∃θ, interiorSector p θ referenceSectorHalfAngle R₀ ⊆ gerverSofa P := by
  obtain ⟨Rs,hRs,hs⟩ := gerver_smooth_sector hP hbox
  obtain ⟨Rc,hRc,hc⟩ := gerver_corner_sectors hP hbox
  let R₀:=min Rs Rc
  refine ⟨R₀,lt_min hRs hRc,?_⟩
  intro p hp
  rcases reference_boundary_or_interior_or_corner hP hbox p hp with hsmooth|hint|hcorner
  · obtain ⟨θ,hθ⟩ := hs p hp hsmooth
    exact ⟨θ,fun q hq => hθ ⟨hq.1,hq.2.1,
      hq.2.2.trans (min_le_left _ _)⟩⟩
  · obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.1 isOpen_interior p hint.2
    let θ:=0
    refine ⟨θ,?_⟩
    intro q hq
    exact interior_subset (hball (by
      simpa [euclideanDist] using hq.2.2.trans (min_le_left _ _).trans_lt hr))
  · obtain ⟨θ,hθ⟩ := hc p hp hcorner
    exact ⟨θ,fun q hq => hθ ⟨hq.1,hq.2.1,
      hq.2.2.trans (min_le_right _ _)⟩⟩

end MovingSofaQuantitative
