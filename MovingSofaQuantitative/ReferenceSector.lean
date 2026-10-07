module

public import MovingSofaQuantitative.Certificates.Trig
public import MovingSofaQuantitative.SectorContent
public import MovingSofaQuantitative.ScalarTaylor
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

/-- The concrete 1.53-radian sector is narrower than a right angle.
This is the only numerical fact required by the tangent-ball reduction. -/
theorem referenceSectorHalfAngle_sin_le_cos :
    0<sin referenceSectorHalfAngle ∧
      sin referenceSectorHalfAngle≤cos referenceSectorHalfAngle := by
  have hh : 0≤referenceSectorHalfAngle := by
    unfold referenceSectorHalfAngle sectorHalfAngle
    norm_num
  have hs:=MovingSofaQuantitative.sin_le_sinPoly5 hh
  have hc:=one_sub_sq_div_two_le_cos (x:=referenceSectorHalfAngle)
  have hpositive : 0<sin referenceSectorHalfAngle := by
    apply sin_pos_of_pos_of_lt_pi
    · exact referenceSectorHalfAngle_pos.1
    · linarith [referenceSectorHalfAngle_pos.2,pi_pos]
  constructor
  · exact hpositive
  · unfold referenceSectorHalfAngle sectorHalfAngle at *
    dsimp [MovingSofaQuantitative.sinPoly5] at hs
    norm_num at *
    linarith

/-- A narrow cone has axial projection at least half its Euclidean length.
It is enough that its sine is positive and does not exceed its cosine; no
trigonometric numerical approximation is used in the geometric argument. -/
theorem interiorSector_axis_half {p q : Point} {θ h R : ℝ}
    (hs : 0<sin h) (hsc : sin h≤cos h)
    (hq : q∈interiorSector p θ h R) :
    euclideanDist p q / 2 ≤ dot (q-p) (uvec θ) := by
  let w:=q-p
  let a:=dot w (uvec θ)
  let b:=dot w (vvec θ)
  have hplus : 0≤a*sin h+b*cos h := by
    have hh:=hq.1
    simpa [a,b,w,dot,uvec,vvec,cos_add,sin_add,
      cos_pi_div_two_sub,sin_pi_div_two_sub] using hh
  have hminus : 0≤a*sin h-b*cos h := by
    have hh:=hq.2.1
    simpa [a,b,w,dot,uvec,vvec,cos_sub,sin_sub,
      cos_pi_div_two_sub,sin_pi_div_two_sub] using hh
  have ha : 0≤a := by nlinarith [hs]
  have hb1 : b≤a := by
    have hh:=mul_le_mul_of_nonneg_left hsc ha
    have hc : 0<cos h := lt_of_lt_of_le hs hsc
    nlinarith
  have hb2 : -a≤b := by
    have hh:=mul_le_mul_of_nonneg_left hsc ha
    have hc : 0<cos h := lt_of_lt_of_le hs hsc
    nlinarith
  have hbSq : b^2≤a^2 := by
    nlinarith [mul_nonneg (by linarith : 0≤a-b) (by linarith : 0≤a+b)]
  have hframe : a^2+b^2=euclideanDist p q^2 := by
    dsimp [a,b,w,euclideanDist]
    rw [norm2_sq]
    simp [dot,uvec,vvec,cos_sq_add_sin_sq]
    ring
  have hd : 0≤euclideanDist p q := euclideanDist_nonneg _ _
  dsimp [a]
  nlinarith [hbSq,hframe,ha,hd]

/-- A cone whose half-angle is below pi/4 fits in the ball tangent at the
vertex in its axial direction.  The ball has radius R, and the cone is
truncated to a radius not exceeding R. -/
theorem sector_subset_tangent_ball {p : Point} {θ h r R : ℝ}
    (hR : 0≤R) (hr : r≤R)
    (hs : 0<sin h) (hsc : sin h≤cos h) :
    interiorSector p θ h r ⊆
      euclideanBall (p+R•uvec θ) R := by
  intro q hq
  have ha:=interiorSector_axis_half hs hsc hq
  have hd : euclideanDist p q≤R := hq.2.2.trans hr
  have hq0 : 0≤euclideanDist p q := euclideanDist_nonneg _ _
  have hsq :
      euclideanDist (p+R•uvec θ) q^2 =
      euclideanDist p q^2+R^2-
        2*R*dot (q-p) (uvec θ) := by
    rw [euclideanDist,euclideanDist,norm2_sq,norm2_sq]
    simp [dot,uvec,Prod.fst_add,Prod.snd_add,
      Prod.fst_smul,Prod.snd_smul,Prod.fst_sub,Prod.snd_sub]
    nlinarith [sin_sq_add_cos_sq θ]
  show euclideanDist (p+R•uvec θ) q≤R
  nlinarith [hsq,ha,hd,hq0,euclideanDist_nonneg (p+R•uvec θ) q]

/-- A tangent ball also contains a translated narrow cone at any point lying
a distance d along its inward normal. The condition r+d<=R is sufficient and
is stable under the tiny 10^-20 cutoff scale. -/
theorem translated_sector_subset_tangent_ball {b : Point} {θ h d r R : ℝ}
    (hd : 0≤d) (hR : 0≤R) (hr : 0≤r)
    (hfit : d+r≤R)
    (hs : 0<sin h) (hsc : sin h≤cos h) :
    interiorSector (b+d•uvec θ) θ h r ⊆
      euclideanBall (b+R•uvec θ) R := by
  let p:=b+d•uvec θ
  let c:=b+R•uvec θ
  intro q hq
  let ρ:=euclideanDist p q
  have hρ : 0≤ρ:=euclideanDist_nonneg _ _
  have hρr : ρ≤r:=hq.2.2
  have ha:=interiorSector_axis_half hs hsc hq
  have hRd : 0≤R-d:=by linarith
  have hρd : ρ≤R-d:=by linarith
  have hcenter :
      euclideanDist c q^2=
      ρ^2+(R-d)^2-
        2*(R-d)*dot (q-p) (uvec θ) := by
    dsimp [c,p,ρ]
    rw [euclideanDist,euclideanDist,norm2_sq,norm2_sq]
    simp [dot,uvec,Prod.fst_add,Prod.snd_add,
      Prod.fst_smul,Prod.snd_smul,Prod.fst_sub,Prod.snd_sub]
    nlinarith [sin_sq_add_cos_sq θ]
  have hdrop : ρ^2-(R-d)*ρ≤0 := by
    nlinarith [mul_nonneg hρ (sub_nonneg.mpr hρd)]
  have hball : euclideanDist c q^2≤R^2 := by
    nlinarith [hcenter,ha,hdrop,hd,hfit]
  have hdistNonneg:=euclideanDist_nonneg c q
  show euclideanDist c q≤R
  nlinarith

/-- The smallest explicit boundary openings clear beta=1.53. -/
theorem gerver_corner_angle_margin {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    referenceSectorAperture < π / 2 - P.φ ∧
      referenceSectorAperture < 2 * arctan (6 / 5 : ℝ) := by
  have hφ := hbox.1
  constructor
  · unfold referenceSectorAperture sectorHalfAngle
    have hπ : (314159265358979323846 / 100000000000000000000 : ℝ) ≤ π :=
      (Certificates.Interval.contains_pi).1
    norm_num at *
    linarith [hπ, hφ.2]
  · have hx : referenceSectorAperture / 2 = 153 / 200 := by
      norm_num [referenceSectorAperture, sectorHalfAngle]
    have hs : sin (153 / 200 : ℝ) < 7 / 10 :=
      (Real.sin_le _).trans_lt (by norm_num)
    have hc : 7 / 10 < cos (153 / 200 : ℝ) := by
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

/-- Right outer floor corner.  The adjacent outer contact arc starts at
normal phi, so the interior opening is exactly pi/2-phi. -/
theorem endpoint_sector_mem_right {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    (hopen : referenceSectorAperture < π/2-P.φ)
    (hscale : referenceSectorRadius < P.φ/1000)
    {q : Point}
    (hq : q∈interiorSector (1,0) (π/2-P.φ/2)
      referenceSectorHalfAngle referenceSectorRadius) :
    q∈gerverSofa P := by
  have hB:=romik_bounds hP hbox
  have hK:=gm_isCap hP hbox
  have hA0:=gs_A_zero hP
  have houter:=theorem8_4_1_tangents hP hbox
  rw [gerver_shape_eq hP hbox]
  refine ⟨?_,?_⟩
  · apply (cap_mem_iff_upper hK q).2
    refine ⟨?_,?_⟩
    · have h1:=hq.1
      have h2:=hq.2.1
      simp [interiorSector,dot,uvec] at h1 h2
      nlinarith
    · intro t ht
      have hs:=gs_supp_K hP hB ht.1 ht.2
      rw [gerver_cap_explicit hP hbox,hs]
      have hcorner:=gs_A_le_H hP hB ht.1 ht.2 le_rfl
        (by linarith [pi_pos])
      simp [hA0,dot,uvec] at hcorner ⊢
      have hd:=hq.2.2
      have hx:=abs_fst_le_norm2 (q-(1,0))
      have hy:=abs_snd_le_norm2 (q-(1,0))
      nlinarith [hx.trans hd,hy.trans hd,hopen,hscale]
  · intro hn
    rw [gerver_niche_eq_envUnderStrict hP hB] at hn
    have hx:=envUnderStrict_fst_mem_Ioo (gn_envHyp hP hB) hn
    have hright:=gerver_corner_points hP hbox
    rcases hright with ⟨a,b,xm,-,hb,-,-,-,-⟩
    have hd:=hq.2.2
    have hxq:=abs_fst_le_norm2 (q-(1,0))
    nlinarith [hxq.trans hd,hscale,hB.φ_mem.1]

def gerverFloorLeft (P : GerverParams) : ℝ := (P.path (π/2)).1-1

theorem gerverFloorLeft_mem {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    (gerverFloorLeft P,0)∈gerverSofa P := by
  have hB:=romik_bounds hP hbox
  have hC:=gs_C_mem_K hP hB (τ:=π/2) (by positivity) le_rfl
  rw [gs_C_pi_div_two hP] at hC
  rw [gerver_shape_eq hP hbox,gerver_niche_eq_envUnderStrict hP hB]
  refine ⟨?_,?_⟩
  · simpa [gerver_cap_explicit hP hbox,gerverFloorLeft] using hC
  · intro hn
    have hx:=envUnderStrict_fst_mem_Ioo (gn_envHyp hP hB) hn
    have hC0:=gs_C_mem_K hP hB (τ:=0) le_rfl (by positivity)
    rw [gerver_contactC_zero hP hB] at hC0
    have hxa : gerverFloorLeft P≤gerverRoofLeft P := by
      unfold gerverFloorLeft gerverRoofLeft
      exact (gs_K_bounds hP hC0).1
    exact (not_lt_of_ge hxa) hx.1

/-- Left outer floor corner, proved directly from the support half-planes. -/
theorem endpoint_sector_mem_left {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    (hopen : referenceSectorAperture < π/2-P.φ)
    (hscale : referenceSectorRadius < P.φ/1000)
    {q : Point}
    (hq : q∈interiorSector (gerverFloorLeft P,0) (π/2+P.φ/2)
      referenceSectorHalfAngle referenceSectorRadius) :
    q∈gerverSofa P := by
  have hB:=romik_bounds hP hbox
  have hK:=gm_isCap hP hbox
  rw [gerver_shape_eq hP hbox]
  refine ⟨?_,?_⟩
  · apply (cap_mem_iff_upper hK q).2
    refine ⟨?_,?_⟩
    · simp only [interiorSector,mem_setOf_eq] at hq
      have h1:=hq.1
      have h2:=hq.2.1
      simp [dot,uvec] at h1 h2
      nlinarith
    · intro t ht
      rw [gerver_cap_explicit hP hbox,gs_supp_K hP hB ht.1 ht.2]
      have hC:=gs_C_le_H hP hB ht.1 ht.2
        (show (0:ℝ)≤π/2 by positivity) le_rfl
      have hCend:=gs_C_pi_div_two hP
      have hd:=hq.2.2
      have hx:=abs_fst_le_norm2 (q-(gerverFloorLeft P,0))
      have hy:=abs_snd_le_norm2 (q-(gerverFloorLeft P,0))
      simp [gerverFloorLeft,hCend,dot,uvec] at hC ⊢
      nlinarith [hx.trans hd,hy.trans hd,hopen,hscale]
  · intro hn
    rw [gerver_niche_eq_envUnderStrict hP hB] at hn
    have hx:=envUnderStrict_fst_mem_Ioo (gn_envHyp hP hB) hn
    have hd:=hq.2.2
    have hxq:=abs_fst_le_norm2 (q-(gerverFloorLeft P,0))
    have hleft : gerverFloorLeft P≤gerverRoofLeft P := by
      have hC0:=gs_C_mem_K hP hB (τ:=0) le_rfl (by positivity)
      rw [gerver_contactC_zero hP hB] at hC0
      unfold gerverFloorLeft gerverRoofLeft
      exact (gs_K_bounds hP hC0).1
    nlinarith [hxq.trans hd,hscale,hB.φ_mem.1,hleft]

/-- Points of Gerver's sofa within one chart radius of its frontier inherit the
same sector from the local phase chart.  This is the translated-epigraph part
of note 12. -/
theorem gerver_near_boundary_sector {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {p : Point} (hp : p∈gerverSofa P)
    (hnear : ¬ euclideanBall p referenceSectorRadius⊆interior (gerverSofa P)) :
    ∃θ,interiorSector p θ referenceSectorHalfAngle referenceSectorRadius⊆
      gerverSofa P := by
  classical
  have hB:=romik_bounds hP hbox
  have henv:=gn_envHyp hP hB
  obtain ⟨H,L,γ,hroof⟩:=gerver_roof_data hP hbox
  have hshape:=hroof.shape_decomposition
  have hcorner:=gerver_corner_angle_margin hP hbox
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
  rw [gerver_shape_eq hP hbox,hshape] at hp ⊢
  rcases hp with ((hpL|hpR)|hpW)
  · refine ⟨π/2,?_⟩
    intro q hq
    left; left
    have hconv:Convex ℝ (leftWing P.cap (gerverRoofLeft P)):=hroof.wings.1.1.2.2
    have htop:=hroof.rectangle
    have hsmall:=hscale
    have hangle:=hcorner
    aesop
  · refine ⟨π/2,?_⟩
    intro q hq
    left; right
    have hsmall:=hscale
    have hangle:=hcorner
    have hLip:=hroof.roof_lipschitz
    aesop
  · refine ⟨π/2,?_⟩
    intro q hq
    right
    have hconv:Convex ℝ (rightWing P.cap (gerverRoofRight P)):=hroof.wings.2.1.2.2
    have hsmall:=hscale
    have hangle:=hcorner
    aesop

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
  by_cases hL : p = (gerverFloorLeft P, 0)
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
    · apply gerver_near_boundary_sector hP hbox hp
      intro hball
      have hself : p∈euclideanBall p referenceSectorRadius := by
        rw [euclideanBall,mem_setOf_eq,euclideanDist_self]
        exact le_of_not_gt hr
      have := hball hself
      exact hi (interior_mono (fun q hq=>hq) this)
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
