module

public import MovingSofaQuantitative.ReferenceExplicitMargins
public import MovingSofaQuantitative.ReferenceSector
public import MovingSofaQuantitative.NormalRecovery
public import MovingSofaStability.LocalBound

/-!
# Explicit reference scales used by the effective cutoff

UNCOMPILED SOURCE.  Constants are deliberately conservative.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

def localSupportRadius : ℝ := 1/(10:ℝ)^40
def localAngleRadius : ℝ := 1/(10:ℝ)^20
abbrev explicitSectorRadius : ℝ := referenceSectorRadius
abbrev explicitNormalDepth : ℝ := normalRecoveryDepth
def explicitNormalError : ℝ := 1/(10:ℝ)^10
def explicitRoofClip : ℝ := 1/2040000

theorem gerver_roof_height_lt_two_thirds {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    ∀p∈gerverEnvelope P,p.2<2/3 := by
  intro p hp
  have hmax:=gerver_envelope_height_le_midpoint hP hbox p hp
  have hB:=romik_bounds hP hbox
  have hmid:=gerver_midpoint_height_formula hP hbox
  have hpi:=pi_gt_three
  have hsqrt : sqrt 2<283/200 := by
    nlinarith [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg (2:ℝ)]
  rw [hmid] at hmax
  nlinarith [hB.c₁_mem.2,hB.κ₃₂_mem.2]

/-- An elementary support-gap bound using only the cap's two floor endpoints
and the unit-height rectangle over its niche roof.  This works for every
normal in [0,pi], including the two horizontal normals. -/
theorem cap_niche_outer_slack
    {K : Set Point} {a b H L : ℝ} {γ : ℝ → ℝ}
    (hroof : CapRoofData K a b H L γ)
    {p : Point} (hp : p ∈ niche K (π/2))
    (hw : (4/5:ℝ) ≤ min (a + supp K π) (supp K 0 - b))
    (hH : H ≤ 2/3)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) π) :
    max ((4/5)*|cos t|-(2/3)*|sin t|) ((1/3)*|sin t|)
      ≤ supp K t-dot p (uvec t) := by
  have hpRoof : p.1 ∈ Icc a b ∧ 0 ≤ p.2 ∧ p.2 < γ p.1 := by
    rw [hroof.niche_eq] at hp
    exact hp
  have hheight : p.2 ≤ H :=
    (le_of_lt hpRoof.2.2).trans (hroof.roof_le p.1 hpRoof.1)
  have hs : 0 ≤ sin t :=
    sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2
  have habss : |sin t| = sin t := abs_of_nonneg hs
  have htop : (p.1,(1:ℝ)) ∈ K :=
    hroof.rectangle ⟨hpRoof.1,zero_le_one,le_rfl⟩
  have hTopSupport :=
    dot_le_supp hroof.cap.2.1.2.1 htop t
  have hTopGap : (1/3:ℝ)*|sin t| ≤
      supp K t-dot p (uvec t) := by
    rw [habss]
    simp only [dot,uvec] at hTopSupport ⊢
    nlinarith [mul_nonneg (show (0:ℝ)≤1-p.2/1 by linarith)
      hs, mul_nonneg (sub_nonneg.mpr (show p.2≤2/3 by linarith))
      hs]
  have hwidthL : (4/5:ℝ) ≤ a+supp K π :=
    hw.trans (min_le_left _ _)
  have hwidthR : (4/5:ℝ) ≤ supp K 0-b :=
    hw.trans (min_le_right _ _)
  have hFloorGap :
      (4/5:ℝ)*|cos t|-(2/3)*|sin t|
        ≤ supp K t-dot p (uvec t) := by
    rw [habss]
    rcases le_total 0 (cos t) with hc | hc
    · have hA := opt_cap_A_mem hroof.cap
      have hAupper :=
        dot_le_supp hroof.cap.2.1.2.1 hA t
      rw [abs_of_nonneg hc]
      simp only [dot,uvec] at hAupper ⊢
      have hwR : (4/5:ℝ)≤supp K 0-p.1 := by
        linarith [hpRoof.1.2,hwidthR]
      nlinarith [mul_nonneg (sub_nonneg.mpr hwR)
        hc, mul_nonneg (sub_nonneg.mpr (show p.2≤2/3 by linarith))
        hs]
    · have hC := opt_cap_C_mem hroof.cap
      have hCupper :=
        dot_le_supp hroof.cap.2.1.2.1 hC t
      rw [abs_of_nonpos hc]
      simp only [dot,uvec] at hCupper ⊢
      have hwL : (4/5:ℝ)≤p.1+supp K π := by
        linarith [hpRoof.1.1,hwidthL]
      nlinarith [mul_nonneg (sub_nonneg.mpr hwL)
        (neg_nonneg.mpr hc),mul_nonneg
        (sub_nonneg.mpr (show p.2≤2/3 by linarith)) hs]
  exact max_le hFloorGap hTopGap

/-- Explicit support margin from the niche to the outer cap. -/
theorem gerver_outer_margin_one_fifth {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    ∀p∈niche P.cap (π/2),∀t∈Icc (0:ℝ) π,
      1/5≤supp P.cap t-dot p (uvec t) := by
  intro p hp t ht
  obtain ⟨H,L,γ,hroof⟩:=gerver_roof_data hP hbox
  have hH : H≤2/3 := by
    have hpmax:=hroof.roof_height_upper
    exact le_of_forall_gt_imp_ge_of_dense fun h =>
      gerver_roof_height_lt_two_thirds hP hbox _ (hroof.graph_mem_at_max h)
  let c:=|cos t|
  let s:=|sin t|
  have hs0 : 0≤s:=abs_nonneg _
  have hc0 : 0≤c:=abs_nonneg _
  have hunit : c^2+s^2=1 := by
    dsimp [c,s]; rw [sq_abs,sq_abs,cos_sq_add_sin_sq]
  have hD : (4/5:ℝ)≤min
      (gerverRoofLeft P+supp P.cap π)
      (supp P.cap 0-gerverRoofRight P) :=
    gerver_wing_width_min hP hbox
  have hslack : max ((4/5)*c-(2/3)*s) ((1/3)*s)
      ≤ supp P.cap t-dot p (uvec t) :=
    cap_niche_outer_slack hroof hp hD hH ht
  by_contra hn
  have h1 : (1/3)*s<1/5 := lt_of_le_of_lt (le_max_right _ _) (hslack.trans_lt (not_le.mp hn))
  have h2 : (4/5)*c-(2/3)*s<1/5 :=
    lt_of_le_of_lt (le_max_left _ _) (hslack.trans_lt (not_le.mp hn))
  nlinarith [hunit]

/-- Explicit interior-ball scale for the reference actual sofa. -/
theorem gerver_interior_balls_explicit {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    HasInteriorBalls (gerverSofa P) (100/1051) (1/24) := by
  obtain ⟨H,L,γ,hroof⟩:=gerver_roof_data hP hbox
  have hH : H<2/3 := hroof.height_lt_two_thirds
  have hwidth : 1<gerverRoofRight P-gerverRoofLeft P :=
    gerver_roof_width_gt_one hP hbox
  exact roof_interior_balls hroof
    (r₀:=1/24) (κ:=100/1051)
    (by nlinarith [hH]) (by nlinarith [hwidth])

/-- The phase-aware roof margin works with a fixed clipping slack. -/
theorem gerver_roof_slack_explicit {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {H L : ℝ} {γ : ℝ→ℝ}
    (hroof : CapRoofData P.cap (gerverRoofLeft P) (gerverRoofRight P) H L γ) :
    RoofSlackMargin P.cap γ (5/51) explicitRoofClip := by
  have hlead:=gerver_adaptive_downward_slack hP hbox
  have hspeed:=gerver_reference_speed_le_ten hP hbox
  have hLip:=gerver_reference_velocity_lipschitz_100 hP hbox
  have hrem : referenceAdaptiveSlackRemainder P≤5/5151 := by
    exact reference_adaptive_remainder_bound hP hbox hspeed hLip
      (by norm_num [explicitRoofClip])
  exact integrate_reference_slack_to_roof_margin hP hbox hroof hlead hrem
    (by norm_num [explicitRoofClip])

/-- Explicit 49/100 inner-wall violation for points in the *reference niche*.
Outer-cap points are handled separately by the outer support margin; it
would be false to impose a common inner-wall violation on every point outside
Gerver's sofa. -/
theorem gerver_normal_slack_explicit {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    ∀ p ∈ niche P.cap (π/2),
      0 < infDist p (gerverSofa P) →
      infDist p (gerverSofa P) ≤ explicitNormalDepth →
      ∃ t ∈ Ioo (0:ℝ) (π/2),
        innerSlackU P.cap t p ≤ -(49/100)*infDist p (gerverSofa P) ∧
        innerSlackV P.cap t p ≤ -(49/100)*infDist p (gerverSofa P) := by
  intro p hp hd hdepth
  exact gerver_niche_normal_slack_explicit hP hbox p hp hd
    (by simpa [explicitNormalDepth] using hdepth)

/-- With total support/hallway error at most 1e-10, forward recovery has the
100/49 coefficient. -/
theorem directed_to_gerver_explicit {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {K S : Set Point} (hK : IsCap K (π/2)) (hSK : S⊆K)
    {δ ζ : ℝ} (hδ : 0≤δ) (hζ : 0≤ζ)
    (hclose : UpperSupportClose δ K P.cap)
    (hhall : ApproxHallways K S ζ)
    (hsmall : δ+ζ≤explicitNormalError) :
    DirectedClose ((100/49)*(δ+ζ)) S (gerverSofa P) := by
  exact explicit_normal_and_deep_niche_recovery hP hbox hK hSK hδ hζ
    hclose hhall (gerver_normal_slack_explicit hP hbox)
    (gerver_roof_slack_explicit hP hbox (gerver_roof_data hP hbox).choose_spec.choose_spec.choose_spec)
    (gerver_outer_margin_one_fifth hP hbox) hsmall

/-- Every local cap hypothesis used in the 2.3 proof is valid inside the
fixed 1e-40 support neighborhood. -/
theorem explicit_local_cap_certificate {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hK : IsCap K (π/2))
    (hclose : UpperSupportClose localSupportRadius K P.cap) :
    InWideL P.φ K (rightBody P.φ K) (leftBody P.φ K) ∧
    niche K (π/2)⊆K ∧
    sofaArea (π/2) K≤upperQ P.φ K (rightBody P.φ K) (leftBody P.φ K) ∧
    upperQ P.φ K (rightBody P.φ K) (leftBody P.φ K)≤area (gerverSofa P) := by
  exact explicit_reference_contact_certificate hP hbox hK hclose
    (by norm_num [localSupportRadius])

/-- Terminal comparison at the fixed support and angle radii. -/
theorem explicit_terminal_certificate {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {K S : Set Point} (hK : IsCap K (π/2))
    (hclose : UpperSupportClose localSupportRadius K P.cap)
    (hS : MeasurableSet S) {ω : ℝ}
    (hω : ω∈Icc (0:ℝ) (π/2))
    (hα : π/2-ω≤localAngleRadius)
    (hconstraints : PartialSofaConstraints K S ω) :
    let U:=capShape K
    let ε:=area (gerverSofa P)-area S
    let e:=area (gerverSofa P)-area U
    0≤e ∧ e≤ε ∧
    π/2-ω≤(31/10)*(ε-e) ∧
    area(S\U)≤(31/10000)*(ε-e) ∧
    area(U\S)≤(10031/10000)*(ε-e) ∧
    ApproxHallways K S (16*(π/2-ω)) := by
  exact explicit_fixed_floor_terminal hP hbox hK hclose hS hω hα hconstraints
    (by norm_num [localSupportRadius,localAngleRadius])

end MovingSofaQuantitative
