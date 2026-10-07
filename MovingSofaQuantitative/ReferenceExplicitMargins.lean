module

public import MovingSofaStability.Margins

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

/-- The reference core velocity decomposes as -a u + b v with positive
coefficients, and its horizontal projection has a fixed fraction of a+b. -/
theorem gerver_core_transversality {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t∈Icc P.φ (π/2-P.φ)) :
    ∃ a b : ℝ,0<a ∧ 0<b ∧
      referenceBoundaryVelocity P t=-a•uvec t+b•vvec t ∧
      (10/101:ℝ)*(a+b)≤a*cos t+b*sin t := by
  obtain ⟨a,b,ha,hb,hvel⟩ := gerver_velocity_frame hP hbox ht
  refine ⟨a,b,ha,hb,hvel,?_⟩
  by_cases hsmall : t≤1/8
  · have ha' : (59/625:ℝ)≤a :=
      gerver_second_phase_a_lower hP hbox ht hsmall
    have hb' : b≤7/5 := gerver_second_phase_b_upper hP hbox ht hsmall
    have hs : (39/1000:ℝ)≤sin t := by
      have hφ:=hbox.1
      have hlo:=sin_lower_cubic t
      nlinarith [hφ.1,ht.1]
    have hc : (127/128:ℝ)≤cos t := by
      have hc0:=one_sub_sq_div_two_le_cos (x:=t)
      nlinarith [hsmall,ht.1]
    exact phase_transversality_small ha' hb.le hb' hs hc
  · have hs : sin t∈Icc (1/9:ℝ) 1 := by
      constructor
      · have hm:=sin_mono_quadrant (show (0:ℝ)≤1/8 by norm_num)
          (by linarith [not_le.mp hsmall])
          (by linarith [ht.2,pi_pos])
        have hs8:=sin_lower_cubic (1/8:ℝ)
        nlinarith
      · exact sin_le_one t
    by_cases hright : π/2-1/8≤t
    · have hc : cos t∈Icc (1/9:ℝ) 1 := by
        rw [←sin_pi_div_two_sub]
        constructor
        · have hu : 1/8≤π/2-t := by linarith [ht.2,hbox.1.1]
          have hm:=sin_mono_quadrant (show (0:ℝ)≤1/8 by norm_num)
            hu (by linarith [ht.1,pi_pos])
          have hs8:=sin_lower_cubic (1/8:ℝ)
          nlinarith
        · exact sin_le_one _
      exact phase_velocity_large ha.le hb.le hs hc
    · have hc : cos t∈Icc (1/9:ℝ) 1 := by
        have hc0 : 1/9≤cos t :=
          cos_lower_on_middle hP hbox ht (not_le.mp hright)
        exact ⟨hc0,cos_le_one t⟩
      exact phase_velocity_large ha.le hb.le hs hc

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
