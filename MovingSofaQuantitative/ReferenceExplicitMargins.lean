module

public import MovingSofaStability.Margins
public import MovingSofaQuantitative.ScalarTaylor

/-!
# Explicit phase-aware reference margins

UNCOMPILED SOURCE.  The integrated stability proof obtains positive margins by
compactness.  The quantitative appendix needs the fixed constants used in the
area and normal calculations.  All estimates concern Gerver's fixed reference
path.

The common roof-slack coefficient is 5/51.  It is smaller than the directly
proved transversality 10/101, leaving the rational reserve 5/5151.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

theorem phase_transversality_small {a b s c : ℝ}
    (ha : (59/625:ℝ)≤a) (hb0 : 0≤b) (hb : b≤7/5)
    (hs : (39/1000:ℝ)≤s) (hc : (127/128:ℝ)≤c) :
    (10/101:ℝ)*(a+b)≤a*c+b*s := by
  have ha0 : 0≤a := by linarith
  have h1 := mul_le_mul_of_nonneg_left
    (show (127/128:ℝ)-10/101≤c-10/101 by linarith) ha0
  have h2 := mul_le_mul_of_nonneg_left
    (show (39/1000:ℝ)-10/101≤s-10/101 by linarith) hb0
  have h3 := mul_le_mul_of_nonpos_right hb
    (show (39/1000:ℝ)-10/101≤0 by norm_num)
  nlinarith

theorem phase_velocity_large {a b s c : ℝ}
    (ha : 0≤a) (hb : 0≤b)
    (hs : s∈Icc (1/9:ℝ) 1) (hc : c∈Icc (1/9:ℝ) 1) :
    (10/101:ℝ)*(a+b)≤a*c+b*s := by
  have h1:=mul_le_mul_of_nonneg_left hc.1 ha
  have h2:=mul_le_mul_of_nonneg_left hs.1 hb
  nlinarith

theorem explicit_margin_reserve :
    (0:ℝ)<10/101-5/51 ∧ (10/101:ℝ)-5/51=5/5151 := by norm_num

/-- Gerver's actual reference velocity, using the integrated frame API. -/
def referenceBoundaryVelocity (P : GerverParams) (t : ℝ) : Point := P.gs_pathD t

theorem referenceBoundaryVelocity_eq {P : GerverParams}
    (hP : P.IsSolution) (t : ℝ) :
    referenceBoundaryVelocity P t =
      P.gs_α t • uvec t + P.gs_β t • vvec t := by
  unfold referenceBoundaryVelocity
  rw [←gs_deriv_path hP t]
  exact (gs_hasDerivAt_path' hP t).deriv

/-- On the left end of the core the negative u-coordinate of the velocity has
the explicit lower bound used in the phase-aware transversality estimate. -/
theorem gerver_left_core_a_lower {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t∈Icc P.φ (1/8:ℝ)) :
    (59/625:ℝ)≤-P.gs_α t := by
  have hB:=romik_bounds hP hbox
  have htθ : t≤P.θ := by nlinarith [ht.2,hB.θ_mem.1]
  rw [gs_α_eq hP (show gs_piece P 1 t from ⟨ht.1,htθ⟩),gs_α₂_eq]
  nlinarith [hB.b₁_mem.1]

theorem gerver_left_core_b_upper {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t∈Icc P.φ (1/8:ℝ)) :
    P.gs_β t≤7/5 := by
  have hB:=romik_bounds hP hbox
  have htθ : t≤P.θ := by nlinarith [ht.2,hB.θ_mem.1]
  rw [gs_β_eq hP (show gs_piece P 1 t from ⟨ht.1,htθ⟩),gs_β₂_eq]
  have hs:=sq_nonneg (t-1/8)
  nlinarith [hB.b₁_mem.1,hB.b₁_mem.2,hB.b₂_mem.2,ht.1,ht.2]

/-- The right end is the reflected phase-2 calculation. -/
theorem gerver_right_core_b_lower {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t∈Icc (π/2-1/8) (π/2-P.φ)) :
    (59/625:ℝ)≤P.gs_β t := by
  have hB:=romik_bounds hP hbox
  let s:=π/2-t
  have hs : s∈Icc P.φ (1/8:ℝ) := by
    dsimp [s]
    constructor <;> linarith [ht.1,ht.2]
  have hphase : gs_piece P 3 t := by
    constructor
    · have hθ:=hB.θ_mem.2
      nlinarith [ht.1]
    · exact ht.2
  rw [gs_β_eq hP hphase]
  have he:=gs_β₄_eq hP s
  have htEq : t=π/2-s := by dsimp [s]; ring
  rw [htEq,he]
  nlinarith [gerver_left_core_a_lower hP hbox hs]

theorem gerver_right_core_a_upper {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t∈Icc (π/2-1/8) (π/2-P.φ)) :
    -P.gs_α t≤7/5 := by
  have hB:=romik_bounds hP hbox
  let s:=π/2-t
  have hs : s∈Icc P.φ (1/8:ℝ) := by
    dsimp [s]
    constructor <;> linarith [ht.1,ht.2]
  have hphase : gs_piece P 3 t := by
    constructor
    · nlinarith [hB.θ_mem.2,ht.1]
    · exact ht.2
  rw [gs_α_eq hP hphase]
  have he:=gs_α₄_eq hP s
  have htEq : t=π/2-s := by dsimp [s]; ring
  rw [htEq,he]
  nlinarith [gerver_left_core_b_upper hP hbox hs]

/-- The reference core velocity is -a u_t + b v_t with a,b>0, and its
horizontal transversality is at least 10/101 of a+b. -/
theorem gerver_core_transversality {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t∈Icc P.φ (π/2-P.φ)) :
    ∃ a b : ℝ,0<a ∧ 0<b ∧
      referenceBoundaryVelocity P t=-a•uvec t+b•vvec t ∧
      (10/101:ℝ)*(a+b)≤a*cos t+b*sin t := by
  let a:=-P.gs_α t
  let b:=P.gs_β t
  have hB:=romik_bounds hP hbox
  have ht0 : 0<t := hB.φ_mem.1.trans_le ht.1
  have ht1 : t<π/2 := by linarith [ht.2,hB.φ_mem.1]
  have ha : 0<a := by
    dsimp [a]
    exact neg_pos.mpr (gs_α_neg hP hB ht0 ht1.le)
  have hb : 0<b := by
    dsimp [b]
    exact gs_β_pos hP hB ht0.le ht1
  have hvel : referenceBoundaryVelocity P t=-a•uvec t+b•vvec t := by
    rw [referenceBoundaryVelocity_eq hP]
    dsimp [a,b]
    module
    abel
  refine ⟨a,b,ha,hb,hvel,?_⟩
  by_cases hleft : t≤1/8
  · have htl : t∈Icc P.φ (1/8:ℝ):=⟨ht.1,hleft⟩
    have ha' := gerver_left_core_a_lower hP hbox htl
    have hb' := gerver_left_core_b_upper hP hbox htl
    have hs : (39/1000:ℝ)≤sin t := by
      have hlo:=sinPoly3_le_sin ht0.le
      simp [sinPoly3] at hlo
      nlinarith [ht.1,hB.φ_mem.1]
    have hc : (127/128:ℝ)≤cos t := by
      have hc0:=one_sub_sq_div_two_le_cos (x:=t)
      nlinarith [hleft,ht0]
    exact phase_transversality_small
      (by simpa [a] using ha') hb.le (by simpa [b] using hb') hs hc
  by_cases hright : π/2-1/8≤t
  · have htr : t∈Icc (π/2-1/8) (π/2-P.φ):=⟨hright,ht.2⟩
    have hb' := gerver_right_core_b_lower hP hbox htr
    have ha' := gerver_right_core_a_upper hP hbox htr
    have hc : (39/1000:ℝ)≤cos t := by
      rw [←sin_pi_div_two_sub]
      have hnon : 0≤π/2-t := by linarith [ht1]
      have hlo:=sinPoly3_le_sin hnon
      simp [sinPoly3] at hlo
      nlinarith [ht.2,hB.φ_mem.1]
    have hs : (127/128:ℝ)≤sin t := by
      rw [←cos_pi_div_two_sub]
      have hc0:=one_sub_sq_div_two_le_cos (x:=π/2-t)
      nlinarith [hright,ht1]
    have hswap:=phase_transversality_small
      (a:=b) (b:=a) (s:=cos t) (c:=sin t)
      (by simpa [b] using hb') ha.le (by simpa [a] using ha') hc hs
    nlinarith
  · have htL : 1/8<t:=lt_of_not_ge hleft
    have htR : t<π/2-1/8:=lt_of_not_ge hright
    have hs : (1/9:ℝ)≤sin t := by
      have hm:=sin_mono_quadrant (show (0:ℝ)≤1/8 by norm_num)
        htL.le (by linarith [htR,pi_pos])
      have h8:=sinPoly3_le_sin (show (0:ℝ)≤1/8 by norm_num)
      simp [sinPoly3] at h8
      nlinarith
    have hc : (1/9:ℝ)≤cos t := by
      rw [←sin_pi_div_two_sub]
      have hm:=sin_mono_quadrant (show (0:ℝ)≤1/8 by norm_num)
        (by linarith [htR]) (by linarith [htL,pi_pos])
      have h8:=sinPoly3_le_sin (show (0:ℝ)≤1/8 by norm_num)
      simp [sinPoly3] at h8
      nlinarith
    exact phase_velocity_large ha.le hb.le ⟨hs,sin_le_one t⟩ ⟨hc,cos_le_one t⟩

/-- Exact balancing identity for the adaptive witness angle. -/
theorem balanced_slack_rates {a b s c : ℝ} (hab : a+b≠0) :
    -s+a*((s-c)/(a+b))=-(a*c+b*s)/(a+b) ∧
    -c-b*((s-c)/(a+b))=-(a*c+b*s)/(a+b) := by
  constructor <;> field_simp [hab] <;> ring

/-- Along every smooth core point, downward motion admits a hallway with both
slacks decreasing at rate at least 5/51. -/
theorem gerver_adaptive_downward_slack {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t∈Icc P.φ (π/2-P.φ)) :
    ∃ λ : ℝ,
      wallVerticalRateU P t λ≤-(5/51:ℝ) ∧
      wallVerticalRateV P t λ≤-(5/51:ℝ) := by
  obtain ⟨a,b,ha,hb,hvel,htrans⟩ :=
    gerver_core_transversality hP hbox ht
  let λ := (sin t-cos t)/(a+b)
  have hid:=balanced_slack_rates (s:=sin t) (c:=cos t)
    (show a+b≠0 by positivity)
  refine ⟨λ,?_,?_⟩
  · rw [wallVerticalRateU_formula hP hbox ht hvel]
    dsimp [λ]
    rw [hid.1]
    have hres:=explicit_margin_reserve.1
    have hab : 0<a+b := add_pos ha hb
    apply neg_le_neg
    exact (le_div_iff₀ hab).2 (by
      nlinarith [mul_nonneg (show (0:ℝ)≤5/51 by norm_num) hab.le])
  · rw [wallVerticalRateV_formula hP hbox ht hvel]
    dsimp [λ]
    rw [hid.2]
    have hab : 0<a+b := add_pos ha hb
    apply neg_le_neg
    exact (le_div_iff₀ hab).2 (by
      nlinarith [mul_nonneg (show (0:ℝ)≤5/51 by norm_num) hab.le])

/-- Explicit roof margin.  Endpoint/tail phases use their active wall; the
inactive wall has a strict compact reserve. -/
theorem gerver_explicit_roof_slack {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {H L : ℝ} {γ : ℝ→ℝ}
    (hroof : CapRoofData P.cap (gerverRoofLeft P)
      (gerverRoofRight P) H L γ) :
    ∃ τ : ℝ,0<τ ∧ RoofSlackMargin P.cap γ (5/51) τ := by
  have henv:=gn_envHyp hP (romik_bounds hP hbox)
  have hcore:=gerver_adaptive_downward_slack hP hbox
  obtain ⟨τtail,hτtail,htail⟩ :=
    reference_tail_slack_compact hP hbox (5/51) (by norm_num)
  obtain ⟨τcore,hτcore,hcoreFinite⟩ :=
    integrate_adaptive_slack hP hbox hcore (5/5151)
      explicit_margin_reserve.1
  let τ:=min τtail τcore
  refine ⟨τ,lt_min hτtail hτcore,?_⟩
  intro p hp
  rw [hroof.niche_eq] at hp
  obtain ⟨t,ht,hslack⟩ :=
    reference_downward_slack_phase_split hP hbox htail hcoreFinite p hp
  exact ⟨t,ht,
    (hslack.1.trans (neg_le_neg (min_le_left _ _))),
    (hslack.2.trans (neg_le_neg (min_le_right _ _)))⟩

/-- Tighter reference width and niche-roof span. -/
theorem gerver_quantitative_widths {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    horizontalWidth P.cap<323/100 ∧
    gerverRoofRight P-gerverRoofLeft P<807/500 := by
  have h:=romik_bounds hP hbox
  have hk:=h.κ₃₁_mem
  have ha:=h.a₁_mem
  rw [gerver_horizontal_width_formula hP hbox,
    gerver_roof_span_formula hP hbox]
  constructor <;> linarith [hk.1,hk.2,ha.1,ha.2]

end MovingSofaQuantitative
