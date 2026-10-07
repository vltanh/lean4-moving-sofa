module

public import MovingSofaQuantitative.ExplicitBudget
public import MovingSofaStability.Terminal

/-!
# Explicit terminal comparison with coefficient 31/10

UNCOMPILED SOURCE.  The older stability proof uses a small rectangular floor
witness and leaves its coefficient existential.  Here the witness is the
trapezoid from the quantitative analysis.  The omitted-wedge gain is forced
below alpha/1000 before the competitor is chosen.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

/-- Width of the left reference wing along the floor. -/
def gerverLeftWingWidth (P : GerverParams) : ℝ :=
  gerverRoofLeft P + supp P.cap π

/-- The parameter box gives more than 403/500 of left floor wing. -/
theorem gerver_left_wing_width_lower {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    403/500 < gerverLeftWingWidth P := by
  have hB := romik_bounds hP hbox
  have hC := gerver_contactC_zero hP hB
  have hleft := opt_cap_C_mem (gm_isCap hP hbox)
  unfold gerverLeftWingWidth gerverRoofLeft
  rw [henvD_zero_fst hP hB, gerver_cap_explicit hP hbox]
  norm_num [gs_K, gs_C, cK, hB.κ₅₁_mem, hB.κ₅₂_mem] at *
  linarith

/-- Fixed interior floor interval used by the terminal trapezoid. -/
def terminalEta (P : GerverParams) : ℝ := gerverLeftWingWidth P / 1000

def terminalFloorInterval (P : GerverParams) : Set ℝ :=
  Icc (-supp P.cap π + terminalEta P)
      (gerverRoofLeft P - terminalEta P)

/-- Area of the quantitative trapezoid before the omitted-wedge correction. -/
def terminalTrapezoid (P : GerverParams) (α : ℝ) : Set Point :=
  {p | p.1 ∈ terminalFloorInterval P ∧
    0 ≤ p.2 ∧ p.2 ≤ (999/1000)*α*(gerverRoofLeft P-p.1)}

theorem terminalTrapezoid_measurable (P : GerverParams) (α : ℝ) :
    MeasurableSet (terminalTrapezoid P α) := by
  apply (measurableSet_Icc.preimage measurable_fst).inter
  exact (measurableSet_Ici.preimage measurable_snd).inter
    (measurableSet_Iic.preimage (measurable_const.mul
      (measurable_const.sub measurable_fst)))

theorem terminalTrapezoid_area {P : GerverParams} {α : ℝ} (hα : 0≤α) :
    area (terminalTrapezoid P α) =
      (999/1000)*(499/1000)*(gerverLeftWingWidth P)^2*α := by
  unfold terminalTrapezoid terminalFloorInterval terminalEta gerverLeftWingWidth
  rw [area_under_affine_on_interval]
  ring

/-- The trapezoid lies in the full-angle shape for every sufficiently nearby
cap.  The neighborhood is fixed before alpha and the input sofa. -/
theorem nearby_terminal_trapezoid_inside {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ δ α₀ : ℝ, 0<δ ∧ δ≤1 ∧ 0<α₀ ∧
      ∀ K : Set Point, IsCap K (π/2) → UpperSupportClose δ K P.cap →
      ∀ α, 0≤α → α≤α₀ →
        terminalTrapezoid P α ⊆ capShape K := by
  have hD := gerver_left_wing_width_lower hP hbox
  have hη : 0<terminalEta P := by unfold terminalEta; linarith
  obtain ⟨H,L,γ,hroof⟩ := gerver_roof_data hP hbox
  let l := -supp P.cap π+terminalEta P
  let r := gerverRoofLeft P-terminalEta P
  have hlr : l<r := by
    unfold l r terminalEta gerverLeftWingWidth
    linarith
  obtain ⟨m,hm,hmargin⟩ := cap_rectangle_upper_margin hroof.cap hlr
    (by unfold l terminalEta; linarith)
    (by unfold r; linarith [hroof.order,hroof.right_wing])
    (show (1/10:ℝ)<1 by norm_num)
    (cap_horizontal_rectangle hroof.cap (by linarith)
      (opt_cap_down hroof.cap (opt_cap_C_mem hroof.cap) (by norm_num) (by norm_num))
      (hroof.rectangle ⟨⟨le_rfl,hroof.order.le⟩,by norm_num,le_rfl⟩)
      ⟨by simp [l]; linarith,by norm_num,by norm_num⟩)
    (hroof.rectangle ⟨⟨le_rfl,hroof.order.le⟩,by norm_num,le_rfl⟩)
  obtain ⟨δN,hδN,hδN1,hN⟩ :=
    nearby_niche_horizontal_localization hP hbox (η:=terminalEta P/2) (by positivity)
  let δ := min δN (m/4)
  let α₀ := min (1/10:ℝ) (1/(20*gerverLeftWingWidth P))
  refine ⟨δ,α₀,lt_min hδN (by positivity),(min_le_left _ _).trans hδN1,
    lt_min (by norm_num) (by positivity),?_⟩
  intro K hK hclose α hα hαsmall p hp
  have hy : p.2≤1/10 := by
    have hwidth : gerverRoofLeft P-p.1≤gerverLeftWingWidth P := by
      unfold terminalFloorInterval at hp
      linarith [hp.1.1]
    have hm := mul_le_mul_of_nonneg_left hαsmall (by positivity)
    dsimp [α₀] at hm
    nlinarith [hp.2.2]
  refine ⟨(cap_mem_iff_upper hK p).2 ⟨hp.2.1,?_⟩,?_⟩
  · intro t ht
    have hq := hmargin p
      ⟨⟨hp.1.1,hp.1.2⟩,hp.2.1,hy⟩ t ht
    have he := (abs_le.mp (hclose t ht)).1
    dsimp [δ] at *
    linarith
  · intro hn
    have hx := hN K hK (hclose.mono ((min_le_left _ _))) p hn
    unfold terminalFloorInterval terminalEta at hp
    linarith [hp.1.2,hx.1]

/-- The tilted terminal wall excludes the entire trapezoid. -/
theorem terminalTrapezoid_disjoint {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ δ α₀ : ℝ, 0<δ ∧ δ≤1 ∧ 0<α₀ ∧
      ∀ K : Set Point, IsCap K (π/2) → UpperSupportClose δ K P.cap →
      ∀ α, 0<α → α≤α₀ → ∀ S : Set Point,
        (∀ p∈S, supp K (π/2-α)-1≤dot p (uvec (π/2-α))) →
        Disjoint S (terminalTrapezoid P α) := by
  have hη : 0<terminalEta P := by
    unfold terminalEta
    linarith [gerver_left_wing_width_lower hP hbox]
  obtain ⟨δT,ρ,hδT,hρ,hδT1,htop⟩ :=
    gerver_near_top_contacts hP hbox (η:=terminalEta P/4000) (by positivity)
  let α₀ := min ρ (min (terminalEta P/4000)
    (terminalEta P/(4000*(gerverLeftWingWidth P+1))))
  refine ⟨δT,α₀,hδT,hδT1,lt_min hρ
    (lt_min (by positivity) (by positivity)),?_⟩
  intro K hK hclose α hα hαsmall S hterminal
  apply Set.disjoint_left.2
  intro p hpS hpF
  obtain ⟨q,hq,hqy,hqx⟩ :
      ∃q∈K,q.2=1 ∧ gerverRoofLeft P-terminalEta P/4000≤q.1 := by
    have he := vplus_mem_edge hK.2.1 (π/2)
    have hxy := htop K hK hclose (π/2)
      ⟨by positivity,by linarith [pi_pos]⟩
      (by simpa [α₀] using (show (0:ℝ)≤ρ from hρ.le)) _ he
    refine ⟨vplus K (π/2),he.1,?_,hxy.1.le⟩
    have := he.2
    simpa [dot_uvec_pi_div_two,hK.2.2.2.1] using this
  have hv : terminalEta P≤gerverRoofLeft P-p.1 := by
    unfold terminalTrapezoid terminalFloorInterval at hpF
    linarith [hpF.1.2]
  have hsin : α-α^3/6≤sin α := sin_bound_lower_cubic (by linarith [hα,hαsmall.1])
  have hcos : 1-α^2/2≤cos α := one_sub_sq_div_two_le_cos
  have hup := dot_le_supp hK.2.1.2.1 hq (π/2-α)
  simp only [dot,uvec,cos_pi_div_two_sub,sin_pi_div_two_sub,hqy,one_mul] at hup
  have hbad := hterminal p hpS
  simp only [dot,uvec,cos_pi_div_two_sub,sin_pi_div_two_sub] at hbad
  have hwidth : gerverRoofLeft P-p.1≤gerverLeftWingWidth P := by
    unfold terminalTrapezoid terminalFloorInterval terminalEta at hpF
    linarith [hpF.1.1]
  have hy := hpF.2.2
  have hsmall1 := hαsmall.trans (min_le_right _ _)
  have hsmall2 := hαsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  nlinarith

/-- Complete explicit terminal comparison. -/
theorem explicit_terminal_comparison {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ δ α₀ R : ℝ, 0<δ ∧ δ≤1 ∧ 0<α₀ ∧ 1≤R ∧
      ∀ K : Set Point, IsCap K (π/2) → UpperSupportClose δ K P.cap →
      ∀ S : Set Point, MeasurableSet S → ∀ ω∈Icc (0:ℝ) (π/2),
      π/2-ω≤α₀ → PartialSofaConstraints K S ω →
      let U:=capShape K
      let ε:=area (gerverSofa P)-area S
      let e:=area (gerverSofa P)-area U
      0≤e ∧ e≤ε ∧
      π/2-ω≤(31/10)*(ε-e) ∧
      area (S\U)≤(31/10000)*(ε-e) ∧
      area (U\S)≤(10031/10000)*(ε-e) ∧
      ApproxHallways K S (4*R*(π/2-ω)) := by
  obtain ⟨R,hR,hradius⟩ := exists_uniform_cap_radius (gm_isCap hP hbox)
  obtain ⟨δI,αI,hδI,hδI1,hαI,hinside⟩ :=
    nearby_terminal_trapezoid_inside hP hbox
  obtain ⟨δD,αD,hδD,hδD1,hαD,hdisj⟩ :=
    terminalTrapezoid_disjoint hP hbox
  let η := 1/(4000*(3*R+1))
  have hη : 0<η := by positivity
  obtain ⟨δO,αO,hδO,hδO1,hαO,homit⟩ :=
    nearby_omittedWedges_area hP hbox hη hR
  obtain ⟨δC,hδC,hδC1,hcert⟩ := nearby_cap_certificate hP hbox
  let δ:=min δC (min δI (min δD δO))
  let α₀:=min αI (min αD αO)
  refine ⟨δ,α₀,R,lt_min hδC (lt_min hδI (lt_min hδD hδO)),
    (min_le_left _ _).trans hδC1,
    lt_min hαI (lt_min hαD hαO),hR,?_⟩
  intro K hK hclose S hSm ω hω hα hconstraints
  dsimp
  have hNK := (hcert K hK (hclose.mono (min_le_left _ _))).2.1
  have hUarea := area_capShape_of_niche_subset hK hNK
  have hQM := (hcert K hK (hclose.mono (min_le_left _ _))).2.2
  have hmax : area (capShape K)≤area (gerverSofa P) := by
    rw [hUarea]
    exact hQM.1.trans hQM.2
  let α:=π/2-ω
  have hα0 : 0≤α := sub_nonneg.mpr hω.2
  have hSV : S⊆partialShape K ω := fun p hp =>
    ⟨hconstraints.1 hp,fun hn =>
      (hconstraints.2.1 p hp hn.choose ⟨hn.choose_spec.1.1.le,hn.choose_spec.1.2.le⟩).not_gt
        (max_lt hn.choose_spec.2.1 hn.choose_spec.2.2)⟩
  have hgain : area (S\capShape K)≤α/1000 := by
    have hs : S\capShape K⊆omittedWedges K ω := by
      intro p hp
      exact ⟨hSV hp.1,hp.2⟩
    have hm := homit K hK (hclose.mono
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
      (hradius K hK (hclose.mono (δ:=δ) (by exact (min_le_left _ _).trans hδC1)))
      ω hω (hα.trans ((min_le_right _ _).trans (min_le_right _ _)))
    have ha := ENNReal.toReal_mono
      (volume_ne_top_of_subset sdiff_subset hK.2.1.2.1.measure_lt_top.ne)
      (measure_mono hs)
    dsimp [η,α] at hm ⊢
    nlinarith
  have hloss : area S≤area (capShape K)-(10/31)*α := by
    rcases hα0.eq_or_lt with hz|hp
    · subst α
      have hsub : S⊆capShape K := by
        simpa [α] using hSV
      exact (ENNReal.toReal_mono hK.2.1.2.1.measure_lt_top.ne
        (measure_mono hsub)).trans_eq (by ring)
    · have hTin := hinside K hK
        (hclose.mono ((min_le_right _ _).trans (min_le_left _ _)))
        α hα0 (hα.trans (min_le_left _ _))
      have hTd := hdisj K hK
        (hclose.mono ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))))
        α hp (hα.trans ((min_le_right _ _).trans (min_le_left _ _)))
        S hconstraints.2.2
      have hareaT := terminalTrapezoid_area (P:=P) hα0
      have hcoef :
          (10/31:ℝ)<(999/1000)*(499/1000)*(gerverLeftWingWidth P)^2-1/1000 := by
        have hD := gerver_left_wing_width_lower hP hbox
        nlinarith [sq_lt_sq₀ (by norm_num : (0:ℝ)<403/500) hD]
      have hbalance := area_union_of_disjoint_subsets hSm
        (terminalTrapezoid_measurable P α) hSV hTin hTd
      rw [hareaT] at hbalance
      nlinarith [hbalance,hgain,hcoef]
  obtain ⟨he0,heε,hangle,hsurplus,hmissing⟩ :=
    precise_terminal_budget hSm
      (measurable_capShape hK) (ms_area_ne_top_of_measurable hSm)
      hK.2.1.2.1.measure_lt_top.ne hα0 hmax hloss hgain
  refine ⟨he0,heε,?_,hsurplus,hmissing,?_⟩
  · simpa [α] using hangle
  · have hR' := hradius K hK (hclose.mono (δ:=δ)
      (by exact (min_le_left _ _).trans hδC1))
    exact approximate_full_angle_slack hK hR hR' S hconstraints.1 ω hω hconstraints.2.1

end MovingSofaQuantitative
