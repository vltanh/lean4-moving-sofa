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
      have hm:=strictMonoOn_sin.monotoneOn
        (show (1/8:ℝ)∈Icc (-(π/2)) (π/2) by
          constructor <;> linarith [pi_gt_three])
        (show t∈Icc (-(π/2)) (π/2) by
          constructor <;> linarith [htL,htR,pi_pos])
        htL.le
      have h8:=sinPoly3_le_sin (show (0:ℝ)≤1/8 by norm_num)
      simp [sinPoly3] at h8
      nlinarith
    have hc : (1/9:ℝ)≤cos t := by
      rw [←sin_pi_div_two_sub]
      have hm:=strictMonoOn_sin.monotoneOn
        (show (1/8:ℝ)∈Icc (-(π/2)) (π/2) by
          constructor <;> linarith [pi_gt_three])
        (show π/2-t∈Icc (-(π/2)) (π/2) by
          constructor <;> linarith [htL,htR,pi_pos])
        (by linarith [htR])
      have h8:=sinPoly3_le_sin (show (0:ℝ)≤1/8 by norm_num)
      simp [sinPoly3] at h8
      nlinarith
    exact phase_velocity_large ha.le hb.le ⟨hs,sin_le_one t⟩ ⟨hc,cos_le_one t⟩


/-- The inactive D-tail wall has a generous uniform reserve. This is a
direct two-phase consequence of the Romik parameter box. -/
theorem gerver_D_beta_ge_four_fifths {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) P.θ) :
    (4/5:ℝ) ≤ P.gs_β t := by
  have hB := romik_bounds hP hbox
  by_cases hfirst : t ≤ P.φ
  · rw [gs_β_eq hP (gs_piece₀ hfirst), gs_β₁_eq hP]
    have ht0 : 0 ≤ t := ht.1
    have ht04 : t ≤ (4/100:ℝ) :=
      hfirst.trans (hB.φ_mem.2.trans (by norm_num))
    have hcos := one_sub_sq_div_two_le_cos (x:=t)
    have hsin := Real.sin_le t
    have hcos0 : 0 ≤ cos t := by
      nlinarith [ht0,ht04,hcos]
    have hprod := mul_le_mul_of_nonneg_right hB.a₁_mem.1 hcos0
    nlinarith [hprod,ht0,ht04]
  · have hphase : gs_piece P 1 t := ⟨(not_le.mp hfirst).le,ht.2⟩
    rw [gs_β_eq hP hphase,gs_β₂_eq]
    have ht07 : t ≤ (7/10:ℝ) :=
      ht.2.trans (hB.θ_mem.2.trans (by norm_num))
    have hbs : (-53/100:ℝ) ≤ P.b₁ :=
      (by norm_num : (-53/100:ℝ) ≤ -0.527624699).trans hB.b₁_mem.1
    have hmul := mul_le_mul_of_nonneg_right hbs ht.1
    nlinarith [sq_nonneg (t-7/10),hB.b₂_mem.1,ht.1,ht07,hmul]

/-- Reflection of the Gerver frame exchanges the D and B inactive slacks. -/
theorem gerver_B_alpha_le_neg_four_fifths {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t ∈ Icc (π/2-P.θ) (π/2)) :
    P.gs_α t ≤ -(4/5:ℝ) := by
  let s := π/2-t
  have hs : s ∈ Icc (0:ℝ) P.θ := by
    dsimp [s]
    constructor <;> linarith [ht.1,ht.2]
  have hβ := gerver_D_beta_ge_four_fifths hP hbox hs
  by_cases hmiddle : t ≤ π/2-P.φ
  · have hphase : gs_piece P 3 t := ⟨ht.1,hmiddle⟩
    have hsφ : P.φ ≤ s := by dsimp [s]; linarith
    rw [gs_α_eq hP hphase]
    have htEq : t=π/2-s := by dsimp [s]; ring
    rw [htEq,gs_α₄_eq hP s]
    have hb : P.gs_β s =
        1/2-s^2/4+P.b₁*s+P.b₂ := by
      rw [gs_β_eq hP (gs_piece₁ hsφ hs.2),gs_β₂_eq]
    linarith
  · have hphase : gs_piece P 4 t := (not_le.mp hmiddle).le
    have hsφ : s ≤ P.φ := by dsimp [s]; linarith
    rw [gs_α_eq hP hphase]
    have htEq : t=π/2-s := by dsimp [s]; ring
    rw [htEq,gs_α₅_eq hP s]
    have hb : P.gs_β s =
        2*P.a₁*cos s-sin s/2-1 := by
      rw [gs_β_eq hP (gs_piece₀ hsφ),gs_β₁_eq hP]
    linarith

/-- Horizontal support width, shared by the area and effectivity modules. -/
def horizontalWidth (K : Set Point) : ℝ := supp K 0+supp K π

/-- First variations of the two inner-wall slacks under vertical lowering and
an angular correction \`lambda*d\`.  Gerver's frame coordinates are exactly
\`gs_alpha, gs_beta\`. -/
def wallVerticalRateU (P : GerverParams) (t λ : ℝ) : ℝ :=
  -sin t-P.gs_α t*λ

def wallVerticalRateV (P : GerverParams) (t λ : ℝ) : ℝ :=
  -cos t-P.gs_β t*λ

theorem wallVerticalRateU_formula {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {t a b λ : ℝ}
    (ht : t∈Icc P.φ (π/2-P.φ))
    (hvel : referenceBoundaryVelocity P t=-a•uvec t+b•vvec t) :
    wallVerticalRateU P t λ=-sin t+a*λ := by
  have hv:=referenceBoundaryVelocity_eq hP t
  rw [hv] at hvel
  have hu:=congrArg (fun z=>dot z (uvec t)) hvel
  simp [dot_add_left,dot_smul_left] at hu
  unfold wallVerticalRateU
  nlinarith

theorem wallVerticalRateV_formula {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {t a b λ : ℝ}
    (ht : t∈Icc P.φ (π/2-P.φ))
    (hvel : referenceBoundaryVelocity P t=-a•uvec t+b•vvec t) :
    wallVerticalRateV P t λ=-cos t-b*λ := by
  have hv:=referenceBoundaryVelocity_eq hP t
  rw [hv] at hvel
  have hu:=congrArg (fun z=>dot z (vvec t)) hvel
  simp [dot_add_left,dot_smul_left] at hu
  unfold wallVerticalRateV
  nlinarith

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

theorem sin_ge_half_of_mem {t : ℝ}
    (h0 : π/6≤t) (h1 : t≤π/2) : (1/2:ℝ)≤sin t := by
  have hm:=strictMonoOn_sin.monotoneOn
    (show t∈Icc (-(π/2)) (π/2) by constructor <;> linarith [h0,h1,pi_pos])
    (show π/6∈Icc (-(π/2)) (π/2) by constructor <;> linarith [pi_pos])
  have :=hm (by linarith)
  simpa using this

theorem cos_ge_half_of_mem {t : ℝ}
    (h0 : 0≤t) (h1 : t≤π/3) : (1/2:ℝ)≤cos t := by
  rw [←sin_pi_div_two_sub]
  apply sin_ge_half_of_mem
  · linarith
  · linarith [h0]

/-- The exact analytic integration principle for the core margin.

The derivative inequality is required at *every* point of the integration
interval, not just at its right endpoint. This is the mathematical
hypothesis missing from an earlier \`integral_mono_on\` invocation.

The statement uses no geometric premises, so it can be reused for both
perpendicular hallway walls. -/
private theorem core_slack_of_uniform_derivative_bound
    {F F' : ℝ → ℝ} {d c : ℝ}
    (hd : 0 ≤ d)
    (hder : ∀ x ∈ Icc (0 : ℝ) d, HasDerivAt F (F' x) x)
    (hcont : ContinuousOn F' (Icc (0 : ℝ) d))
    (hupper : ∀ x ∈ Icc (0 : ℝ) d, F' x ≤ -c)
    (hzero : F 0 = 0) :
    F d ≤ -c * d := by
  have hi : IntervalIntegrable F' volume 0 d :=
    hcont.intervalIntegrable_of_Icc hd
  have hFTC : (∫ x in (0 : ℝ)..d, F' x) = F d - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hder x (by rwa [uIcc_of_le hd] at hx)) hi
  have hconstant :
      IntervalIntegrable (fun _ : ℝ => -c) volume 0 d :=
    intervalIntegrable_const
  have hle : (∫ x in (0 : ℝ)..d, F' x) ≤
      ∫ _x in (0 : ℝ)..d, (-c) :=
    intervalIntegral.integral_mono_on hd hi hconstant
      (fun x hx => hupper x hx)
  rw [hFTC, intervalIntegral.integral_const, hzero] at hle
  nlinarith

/-!
### Exact C1 core residuals

For \`s=t+λ(t)d\` the support function at \`s\` is recovered from
\`innerCorner P.cap s=P.path s\` (for \`s∈[0,π/2]\`).
To differentiate in \`d\`, use the *explicit path expression* below, not an
unjustified derivative of the abstract support function.

The velocity \`gs_pathD\` is the already-formalized derivative of \`P.path\`.
-/

private def coreAdjustedAngle (λ : ℝ → ℝ) (t d : ℝ) : ℝ :=
  t + λ t * d

private def coreLoweredPoint (P : GerverParams) (t d : ℝ) : Point :=
  ((P.path t).1, (P.path t).2 - d)

private def corePathSlackU (P : GerverParams) (λ : ℝ → ℝ)
    (t d : ℝ) : ℝ :=
  dot (coreLoweredPoint P t d - P.path (coreAdjustedAngle λ t d))
    (uvec (coreAdjustedAngle λ t d))

private def corePathSlackV (P : GerverParams) (λ : ℝ → ℝ)
    (t d : ℝ) : ℝ :=
  dot (coreLoweredPoint P t d - P.path (coreAdjustedAngle λ t d))
    (vvec (coreAdjustedAngle λ t d))

private def corePathRateU (P : GerverParams) (λ : ℝ → ℝ)
    (t d : ℝ) : ℝ :=
  let s := coreAdjustedAngle λ t d
  dot ((0,-1) - λ t • P.gs_pathD s) (uvec s) +
    λ t * dot (coreLoweredPoint P t d - P.path s) (vvec s)

private def corePathRateV (P : GerverParams) (λ : ℝ → ℝ)
    (t d : ℝ) : ℝ :=
  let s := coreAdjustedAngle λ t d
  dot ((0,-1) - λ t • P.gs_pathD s) (vvec s) -
    λ t * dot (coreLoweredPoint P t d - P.path s) (uvec s)

/-- Exact derivative of the U residual for every depth, including zero. -/
private theorem corePathSlackU_hasDerivAt {P : GerverParams}
    (hP : P.IsSolution) (λ : ℝ → ℝ) (t d : ℝ) :
    HasDerivAt (fun x => corePathSlackU P λ t x)
      (corePathRateU P λ t d) d := by
  let s := coreAdjustedAngle λ t d
  have hs : HasDerivAt (fun x : ℝ => coreAdjustedAngle λ t x)
      (λ t) d := by
    dsimp [coreAdjustedAngle]
    convert ((hasDerivAt_id d).const_mul (λ t)).const_add t using 1 <;> ring
  have hp : HasDerivAt (fun x => P.path (coreAdjustedAngle λ t x))
      (λ t • P.gs_pathD s) d := by
    simpa [s] using (P.gs_hasDerivAt_path hP s).comp d hs
  have hq : HasDerivAt (fun x => coreLoweredPoint P t x)
      ((0,-1) : Point) d := by
    dsimp [coreLoweredPoint]
    convert (hasDerivAt_const d (P.path t).1).prodMk
      ((hasDerivAt_id d).const_sub (P.path t).2) using 1 <;> ext <;> simp
  have hu : HasDerivAt
      (fun x => uvec (coreAdjustedAngle λ t x))
      (λ t • vvec s) d := by
    simpa [s] using (hasDerivAt_uvec s).comp d hs
  have hdot := hasDerivAt_dot' (hq.sub hp) hu
  convert hdot using 1
  · ext x
    simp [corePathSlackU]
  · simp [corePathRateU,s,coreAdjustedAngle,dot_add_left,dot_smul_right]
    ring

/-- Exact derivative of the V residual for every depth, including zero. -/
private theorem corePathSlackV_hasDerivAt {P : GerverParams}
    (hP : P.IsSolution) (λ : ℝ → ℝ) (t d : ℝ) :
    HasDerivAt (fun x => corePathSlackV P λ t x)
      (corePathRateV P λ t d) d := by
  let s := coreAdjustedAngle λ t d
  have hs : HasDerivAt (fun x : ℝ => coreAdjustedAngle λ t x)
      (λ t) d := by
    dsimp [coreAdjustedAngle]
    convert ((hasDerivAt_id d).const_mul (λ t)).const_add t using 1 <;> ring
  have hp : HasDerivAt (fun x => P.path (coreAdjustedAngle λ t x))
      (λ t • P.gs_pathD s) d := by
    simpa [s] using (P.gs_hasDerivAt_path hP s).comp d hs
  have hq : HasDerivAt (fun x => coreLoweredPoint P t x)
      ((0,-1) : Point) d := by
    dsimp [coreLoweredPoint]
    convert (hasDerivAt_const d (P.path t).1).prodMk
      ((hasDerivAt_id d).const_sub (P.path t).2) using 1 <;> ext <;> simp
  have hv : HasDerivAt
      (fun x => vvec (coreAdjustedAngle λ t x))
      (-λ t • uvec s) d := by
    simpa [s, smul_neg, neg_smul] using (hasDerivAt_vvec s).comp d hs
  have hdot := hasDerivAt_dot' (hq.sub hp) hv
  convert hdot using 1
  · ext x
    simp [corePathSlackV]
  · simp [corePathRateV,s,coreAdjustedAngle,dot_add_left,dot_smul_right]
    ring

/-- On the reference turning interval, the explicit path residual is the
actual inner-wall slack of Gerver's cap. -/
private theorem corePathSlack_eq_innerSlack {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    (λ : ℝ → ℝ) (t d : ℝ)
    (hs : coreAdjustedAngle λ t d ∈ Icc (0 : ℝ) (π/2)) :
    corePathSlackU P λ t d =
        innerSlackU P.cap (coreAdjustedAngle λ t d)
          (coreLoweredPoint P t d) ∧
    corePathSlackV P λ t d =
        innerSlackV P.cap (coreAdjustedAngle λ t d)
          (coreLoweredPoint P t d) := by
  have hcorner := P.gm_innerCorner hP hbox hs
  have heq := cn_innerCorner_dot P.cap (coreAdjustedAngle λ t d)
  rw [hcorner] at heq
  constructor
  · simp only [corePathSlackU,innerSlackU,dot_sub_left]
    linarith [heq.1]
  · simp only [corePathSlackV,innerSlackV,dot_sub_left,
      ←uvec_add_pi_div_two]
    linarith [heq.2]

/-- Compact C1 persistence of the adaptive first-order inequality.  This is
the source-level compactness lemma behind the existential clipping depth.  Its
proof uses only continuity of Gerver's C1 path and the strict rational reserve;
no second derivative is assumed. -/
theorem uniform_core_slack_from_C1 {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {λ : ℝ→ℝ}
    (hλ : ContinuousOn λ (Icc P.φ (π/2-P.φ)))
    (hden : ∀t∈Icc P.φ (π/2-P.φ),0<-P.gs_α t+P.gs_β t)
    (hrate : ∀t∈Icc P.φ (π/2-P.φ),
      wallVerticalRateU P t (λ t)≤-(10/101:ℝ) ∧
      wallVerticalRateV P t (λ t)≤-(10/101:ℝ))
    (hC1 : ContDiff ℝ 1 P.path)
    (hreserve : 0<(10/101:ℝ)-5/51) :
    ∃d₀ : ℝ,0<d₀ ∧
      ∀t∈Icc P.φ (π/2-P.φ),∀d∈Icc (0:ℝ) d₀,
      let s:=t+λ t*d
      s∈Ioo (0:ℝ) (π/2) ∧
      innerSlackU P.cap s ((P.path t).1,(P.path t).2-d)≤-(5/51)*d ∧
      innerSlackV P.cap s ((P.path t).1,(P.path t).2-d)≤-(5/51)*d := by
  let I:=Icc P.φ (π/2-P.φ)
  -- Use the reference path rather than differentiating the abstract
  -- support function. The path is C1 on all of R, and the exact
  -- corePathSlack_eq_innerSlack lemma transfers back to the genuine wall
  -- support slacks once the adjusted angle lies in [0,pi/2].
  let FU : ℝ×ℝ→ℝ:=fun z=>corePathSlackU P λ z.1 z.2
  let FV : ℝ×ℝ→ℝ:=fun z=>corePathSlackV P λ z.1 z.2
  let RU : ℝ×ℝ→ℝ:=fun z=>corePathRateU P λ z.1 z.2
  let RV : ℝ×ℝ→ℝ:=fun z=>corePathRateV P λ z.1 z.2
  have hI : IsCompact I:=isCompact_Icc
  have hφ:=romik_bounds hP hbox |>.φ_mem
  have hinside : ∀t∈I,t∈Ioo (0:ℝ) (π/2) := by
    intro t ht
    exact ⟨by linarith [ht.1,hφ.1],
      by linarith [ht.2,hφ.1]⟩
  have hzeroU : ∀t∈I,FU (t,0)=0 := by
    intro t ht
    simp [FU,corePathSlackU,coreAdjustedAngle,coreLoweredPoint]
  have hzeroV : ∀t∈I,FV (t,0)=0 := by
    intro t ht
    simp [FV,corePathSlackV,coreAdjustedAngle,coreLoweredPoint]
  have hrateU_zero : ∀t∈I,RU (t,0)=wallVerticalRateU P t (λ t) := by
    intro t ht
    have hD := (P.gs_hasDerivAt_path hP t).deriv
    unfold RU corePathRateU coreAdjustedAngle coreLoweredPoint wallVerticalRateU
    simp only [mul_zero,add_zero,sub_zero,sub_self,dot_zero_left,mul_zero,
      add_zero,smul_eq_mul]
    rw [←hD]
    simp only [gs_α,dot_smul_left,dot_sub_left]
    ring
  have hrateV_zero : ∀t∈I,RV (t,0)=wallVerticalRateV P t (λ t) := by
    intro t ht
    have hD := (P.gs_hasDerivAt_path hP t).deriv
    unfold RV corePathRateV coreAdjustedAngle coreLoweredPoint wallVerticalRateV
    simp only [mul_zero,add_zero,sub_zero,sub_self,dot_zero_left,mul_zero,
      sub_zero,smul_eq_mul]
    rw [←hD]
    simp only [gs_β,dot_smul_left,dot_sub_left]
    ring
  have hpathD : Continuous P.gs_pathD := by
    have heq : P.gs_pathD=deriv P.path := by
      funext t
      exact (P.gs_hasDerivAt_path hP t).deriv.symm
    rw [heq]
    exact hC1.continuous_deriv
  have hpathC : Continuous P.path := hC1.continuous
  have hλJ : ContinuousOn (fun z : Point=>λ z.1)
      (I×ˢIcc (-1:ℝ) 1) :=
    hλ.comp continuous_fst.continuousOn (fun z hz=>hz.1)
  have hjointU : ContinuousOn RU (I×ˢIcc (-1:ℝ) 1) := by
    dsimp [RU,corePathRateU,coreAdjustedAngle,coreLoweredPoint]
    fun_prop
  have hjointV : ContinuousOn RV (I×ˢIcc (-1:ℝ) 1) := by
    dsimp [RV,corePathRateV,coreAdjustedAngle,coreLoweredPoint]
    fun_prop
  have h0U : ∀t∈I,RU (t,0)≤-(10/101:ℝ) := by
    intro t ht
    rw [hrateU_zero t ht]
    exact (hrate t ht).1
  have h0V : ∀t∈I,RV (t,0)≤-(10/101:ℝ) := by
    intro t ht
    rw [hrateV_zero t ht]
    exact (hrate t ht).2
  let εr:=((10/101:ℝ)-5/51)/2
  have hεr : 0<εr:=by dsimp [εr]; linarith
  have hJ : IsCompact (I×ˢIcc (-1:ℝ) 1):=hI.prod isCompact_Icc
  have hucU:=hJ.uniformContinuousOn_of_continuous hjointU
  have hucV:=hJ.uniformContinuousOn_of_continuous hjointV
  rw [Metric.uniformContinuousOn_iff] at hucU hucV
  obtain ⟨ηU,hηU,hcloseU⟩:=hucU εr hεr
  obtain ⟨ηV,hηV,hcloseV⟩:=hucV εr hεr
  obtain ⟨M,hM⟩:=hI.exists_bound_of_continuousOn hλ
  have hM0 : 0≤M:=by
    obtain ⟨t,ht⟩ : I.Nonempty:=⟨P.φ,by
      dsimp [I]
      constructor
      · exact le_rfl
      · have hφ:=romik_bounds hP hbox |>.φ_mem
        linarith [hφ.2,pi_gt_three]⟩
    exact (norm_nonneg (λ t)).trans (hM t ht)
  let η:=min ηU ηV
  let d₀:=min 1 (min (η/2) (P.φ/(2*(M+1))))
  have hφ0:=romik_bounds hP hbox |>.φ_mem.1
  have hη : 0<η:=lt_min hηU hηV
  have hd₀ : 0<d₀:=by
    dsimp [d₀]
    positivity
  have hd₀1 : d₀≤1:=min_le_left _ _
  have hDU : ∀t∈I,∀d∈Icc (0:ℝ) d₀,
      RU (t,d)≤-(5/51:ℝ) := by
    intro t ht d hd
    have hdη : d<η:=by
      have hhalf:=hd.2.trans (min_le_right (1:ℝ) _)
      have hη2:=hhalf.trans (min_le_left _ _)
      linarith
    have hpt0 : (t,0)∈I×ˢIcc (-1:ℝ) 1:=⟨ht,by norm_num⟩
    have hptd : (t,d)∈I×ˢIcc (-1:ℝ) 1:=⟨ht,by
      constructor
      · linarith [hd.1]
      · linarith [hd.2,hd₀1]⟩
    have hdist : dist (t,d) (t,0)<ηU:=by
      have : d<ηU:=hdη.trans_le (min_le_left _ _)
      simpa [Prod.dist_eq,Real.dist_eq,abs_of_nonneg hd.1] using this
    have hu:=hcloseU hptd hpt0 hdist
    rw [Real.dist_eq] at hu
    have h0:=h0U t ht
    have hres:=explicit_margin_reserve.2
    dsimp [εr] at hu
    nlinarith [abs_le.mp (le_of_lt hu) |>.2]
  have hDV : ∀t∈I,∀d∈Icc (0:ℝ) d₀,
      RV (t,d)≤-(5/51:ℝ) := by
    intro t ht d hd
    have hdη : d<η:=by
      have hhalf:=hd.2.trans (min_le_right (1:ℝ) _)
      have hη2:=hhalf.trans (min_le_left _ _)
      linarith
    have hpt0 : (t,0)∈I×ˢIcc (-1:ℝ) 1:=⟨ht,by norm_num⟩
    have hptd : (t,d)∈I×ˢIcc (-1:ℝ) 1:=⟨ht,by
      constructor
      · linarith [hd.1]
      · linarith [hd.2,hd₀1]⟩
    have hdist : dist (t,d) (t,0)<ηV:=by
      have : d<ηV:=hdη.trans_le (min_le_right _ _)
      simpa [Prod.dist_eq,Real.dist_eq,abs_of_nonneg hd.1] using this
    have hv:=hcloseV hptd hpt0 hdist
    rw [Real.dist_eq] at hv
    have h0:=h0V t ht
    dsimp [εr] at hv
    nlinarith [abs_le.mp (le_of_lt hv) |>.2]
  have hangle : ∀t∈I,∀d∈Icc (0:ℝ) d₀,
      t+λ t*d∈Ioo (0:ℝ) (π/2) := by
    intro t ht d hd
    have hλM : |λ t|≤M:=by
      simpa [Real.norm_eq_abs] using hM t ht
    have hdφ : d≤P.φ/(2*(M+1)) :=
      hd.2.trans ((min_le_right (1:ℝ) _).trans (min_le_right _ _))
    have hshift : |λ t*d|≤P.φ/2:=by
      rw [abs_mul]
      have hm:=mul_le_mul hλM hdφ (abs_nonneg _) hM0
      have hM1 : 0<M+1:=by linarith
      nlinarith
    constructor
    · nlinarith [ht.1,hφ0,neg_abs_le (λ t*d)]
    · nlinarith [ht.2,hφ0,le_abs_self (λ t*d)]
  refine ⟨d₀,hd₀,?_⟩
  intro t ht d hd
  have hs:=hangle t ht d hd
  have hUder : ∀x∈Icc (0:ℝ) d,
      HasDerivAt (fun y=>FU (t,y)) (RU (t,x)) x := by
    intro x hx
    exact corePathSlackU_hasDerivAt hP λ t x
  have hVder : ∀x∈Icc (0:ℝ) d,
      HasDerivAt (fun y=>FV (t,y)) (RV (t,x)) x := by
    intro x hx
    exact corePathSlackV_hasDerivAt hP λ t x
  have hUI : ContinuousOn (fun x=>RU (t,x)) (Icc (0:ℝ) d) := by
    apply hjointU.comp
      (continuous_const.prodMk continuous_id).continuousOn
    intro x hx
    exact ⟨ht,⟨by linarith [hx.1],by linarith [hx.2,hd.2,hd₀1]⟩⟩
  have hVI : ContinuousOn (fun x=>RV (t,x)) (Icc (0:ℝ) d) := by
    apply hjointV.comp
      (continuous_const.prodMk continuous_id).continuousOn
    intro x hx
    exact ⟨ht,⟨by linarith [hx.1],by linarith [hx.2,hd.2,hd₀1]⟩⟩
  have hUle : FU (t,d) ≤ -(5/51:ℝ)*d :=
    core_slack_of_uniform_derivative_bound hd.1 hUder hUI
      (fun x hx=>hDU t ht x ⟨hx.1,hx.2.trans hd.2⟩)
      (hzeroU t ht)
  have hVle : FV (t,d) ≤ -(5/51:ℝ)*d :=
    core_slack_of_uniform_derivative_bound hd.1 hVder hVI
      (fun x hx=>hDV t ht x ⟨hx.1,hx.2.trans hd.2⟩)
      (hzeroV t ht)
  obtain ⟨hmatchU,hmatchV⟩ :=
    corePathSlack_eq_innerSlack hP hbox λ t d hs.le
  dsimp [FU,FV] at hUle hVle
  dsimp
  exact ⟨hs,by simpa [coreLoweredPoint,coreAdjustedAngle] using
    hmatchU ▸ hUle,by simpa [coreLoweredPoint,coreAdjustedAngle] using
    hmatchV ▸ hVle⟩

/-- Lowering a point further at a fixed first-quadrant hallway angle cannot
increase either inner-wall slack.  This is the precise depth-extension
calculation used after the common core clipping threshold. -/
theorem innerSlack_down_more (K : Set Point) (s : ℝ) (q : Point)
    (d₀ d : ℝ) (hs : s∈Icc (0:ℝ) (π/2)) (hdd : d₀≤d) :
    innerSlackU K s (q.1,q.2-d)≤innerSlackU K s (q.1,q.2-d₀) ∧
    innerSlackV K s (q.1,q.2-d)≤innerSlackV K s (q.1,q.2-d₀) := by
  have hsin : 0≤sin s :=
    sin_nonneg_of_nonneg_of_le_pi hs.1 (hs.2.trans (by linarith [pi_pos]))
  have hcos : 0≤cos s := cos_nonneg_of_mem_Icc hs
  constructor
  · dsimp [innerSlackU,dot,uvec]
    nlinarith [mul_nonneg (sub_nonneg.mpr hdd) hsin]
  · dsimp [innerSlackV,dot,vvec]
    nlinarith [mul_nonneg (sub_nonneg.mpr hdd) hcos]

/-- Quantitative version of \`envelope_downward_slack\`.  The tails use
their active wall (whose vertical coefficient is at least 1/2) and a compact
inactive-wall margin.  On the core, the balancing angle from
\`gerver_adaptive_downward_slack\` gives derivative at most -10/101 at depth
zero.  C1 continuity of Gerver's path makes the two depth derivatives jointly
continuous on the compact core; the rational reserve 5/5151 therefore yields
one positive depth on which both are at most -5/51.  Below that depth the same
angle is frozen and further vertical lowering only decreases both slacks. -/
theorem gerver_envelope_downward_slack_explicit {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ τ : ℝ,0<τ ∧
      ∀ q∈gerverEnvelope P,∀d : ℝ,0<d → 0≤q.2-d →
      ∃t∈Ioo (0:ℝ) (π/2),
        innerSlackU P.cap t (q.1,q.2-d)≤-min ((5/51)*d) τ ∧
        innerSlackV P.cap t (q.1,q.2-d)≤-min ((5/51)*d) τ := by
  have hB:=romik_bounds hP hbox
  have henv:=gn_envHyp hP hB
  have hpath : ∀t∈Icc (0:ℝ) (π/2),innerCorner P.cap t=P.path t :=
    fun t ht=>gm_innerCorner hP hbox ht
  -- Inactive tail slacks have a positive compact minimum.
  obtain ⟨τD,hτD,hD⟩:=isCompact_Icc.exists_forall_le'
    (s:=Icc (0:ℝ) P.θ)
    ((gs_continuous_β hP).continuousOn.mono
      (Icc_subset_Icc le_rfl (by linarith [hB.θ_mem.2,pi_pos])))
    (fun t ht=>by
      rcases ht.1.eq_or_lt with rfl|hp
      · have h0:=gs_β_pos hP hB (show (0:ℝ)≤0 by norm_num)
          (by linarith [hB.θ_mem.2,pi_pos])
        exact h0
      · exact gs_β_pos hP hB hp.le
          (by linarith [ht.2,hB.θ_mem.2,pi_pos]))
  obtain ⟨τB,hτB,hBtail⟩:=isCompact_Icc.exists_forall_le'
    (s:=Icc (π/2-P.θ) (π/2))
    (f:=fun t=>-P.gs_α t)
    ((gs_continuous_α hP).continuousOn.neg.mono
      (Icc_subset_Icc (by linarith [hB.θ_mem.2,pi_pos]) le_rfl))
    (fun t ht=>by
      exact neg_pos.mpr (gs_α_neg hP hB
        (by linarith [ht.1,hB.θ_mem.2,pi_pos]) ht.2))
  -- Core angle adjustment.  We keep the compactness step explicit: the rate
  -- functions are continuous because gs_pathD, alpha, beta and the trig frame
  -- are continuous, and the denominator -alpha+beta is uniformly positive.
  let λ : ℝ→ℝ:=fun t=>(sin t-cos t)/(-P.gs_α t+P.gs_β t)
  have hden : ∀t∈Icc P.φ (π/2-P.φ),0<-P.gs_α t+P.gs_β t := by
    intro t ht
    have ht0 : 0<t:=lt_of_lt_of_le hB.φ_mem.1 ht.1
    have ht1 : t<π/2:=by linarith [ht.2,hB.φ_mem.1]
    nlinarith [gs_α_neg hP hB ht0 ht1.le,gs_β_pos hP hB ht0.le ht1]
  have hλc : ContinuousOn λ (Icc P.φ (π/2-P.φ)) := by
    unfold λ
    fun_prop
  have hrate0 : ∀t∈Icc P.φ (π/2-P.φ),
      wallVerticalRateU P t (λ t)≤-(10/101:ℝ) ∧
      wallVerticalRateV P t (λ t)≤-(10/101:ℝ) := by
    intro t ht
    obtain ⟨a,b,ha,hb,hvel,htr⟩:=gerver_core_transversality hP hbox ht
    have hu:=wallVerticalRateU_formula hP hbox ht hvel (λ:=λ t)
    have hv:=wallVerticalRateV_formula hP hbox ht hvel (λ:=λ t)
    have hid:=balanced_slack_rates (s:=sin t) (c:=cos t)
      (show a+b≠0 by positivity)
    unfold λ at hu hv
    have hα:=congrArg (fun z=>dot z (uvec t))
      ((referenceBoundaryVelocity_eq hP t).symm.trans hvel)
    have hβ:=congrArg (fun z=>dot z (vvec t))
      ((referenceBoundaryVelocity_eq hP t).symm.trans hvel)
    simp [dot_add_left,dot_smul_left] at hα hβ
    rw [show -P.gs_α t+P.gs_β t=a+b by linarith [hα,hβ]] at hu hv
    rw [hid.1] at hu
    rw [hid.2] at hv
    have hab : 0<a+b:=add_pos ha hb
    constructor <;> nlinarith [(le_div_iff₀ hab).2 htr]
  -- Uniform C1 persistence of the strict rate inequality.  This is the only
  -- compactness step in the quantitative roof lemma; it introduces the
  -- clipping threshold but not the coefficient.
  obtain ⟨d₀,hd₀,hcore⟩ :
      ∃d₀ : ℝ,0<d₀ ∧
        ∀t∈Icc P.φ (π/2-P.φ),∀d∈Icc (0:ℝ) d₀,
        let s:=t+λ t*d
        s∈Ioo (0:ℝ) (π/2) ∧
        innerSlackU P.cap s ((P.path t).1,(P.path t).2-d)≤-(5/51)*d ∧
        innerSlackV P.cap s ((P.path t).1,(P.path t).2-d)≤-(5/51)*d := by
    have hC1:=gs_contDiff_path hP
    have hreserve:=explicit_margin_reserve.1
    exact uniform_core_slack_from_C1 hP hbox hλc hden hrate0 hC1 hreserve
  let τ:=min (min τD τB) ((5/51)*d₀)
  refine ⟨τ,lt_min (lt_min hτD hτB) (mul_pos (by norm_num) hd₀),?_⟩
  intro q hq d hd hfloor
  rw [gerverEnvelope] at hq
  rcases hq with (⟨t,ht,rfl⟩|⟨t,ht,rfl⟩)|⟨t,ht,rfl⟩
  · -- right B-tail
    have hti : t∈Ioo (0:ℝ) (π/2):=⟨by linarith [ht.1,hB.θ_mem.2],
      ht.2.lt_of_ne (by
        rintro rfl
        rw [henv.B_end] at hfloor
        linarith)⟩
    obtain ⟨hU,hV⟩:=innerSlack_down (d:=d) (hpath t hti.le)
      (envB P.path P.gs_α t)
    refine ⟨t,hti,?_,?_⟩
    · rw [hU,env_dot_B_self]
      have hs : (1/2:ℝ)≤sin t:=by
        have ht0 : π/6≤t:=by
          have hθ:=hB.θ_mem.2
          linarith [ht.1,pi_gt_three]
        exact sin_ge_half_of_mem ht0 (by linarith [hti.2])
      have hmin:=min_le_left ((5/51)*d) τ
      nlinarith
    · rw [hV]
      have hdot : dot (envB P.path P.gs_α t-P.path t) (vvec t)=P.gs_α t := by
        simp [envB,dot_smul_left]
      rw [hdot]
      have hin : P.gs_α t≤-τB:=by
        nlinarith [hBtail t ⟨ht.1,ht.2.le⟩]
      have hc:=cos_nonneg_of_mem_Icc ⟨by linarith [hti.1,pi_pos],hti.2.le⟩
      have hmin:=min_le_left τB τ
      nlinarith [mul_nonneg hd.le hc]
  · -- core path
    by_cases hsmall : d≤d₀
    · obtain ⟨hs,hU,hV⟩:=hcore t ht d ⟨hd.le,hsmall⟩
      exact ⟨t+λ t*d,hs,
        hU.trans (neg_le_neg (min_le_left _ _)),
        hV.trans (neg_le_neg (min_le_left _ _))⟩
    · obtain ⟨hs,hU,hV⟩:=hcore t ht d₀ ⟨le_rfl,le_rfl⟩
      let s:=t+λ t*d₀
      have hsin : 0≤sin s :=
        sin_nonneg_of_nonneg_of_le_pi hs.1.le (by linarith [hs.2,pi_pos])
      have hcos : 0≤cos s :=
        cos_nonneg_of_mem_Icc ⟨by linarith [hs.1,pi_pos],hs.2.le⟩
      have hUmore :
          innerSlackU P.cap s ((P.path t).1,(P.path t).2-d)=
            innerSlackU P.cap s ((P.path t).1,(P.path t).2-d₀)
              -(d-d₀)*sin s := by
        unfold innerSlackU dot uvec
        ring
      have hVmore :
          innerSlackV P.cap s ((P.path t).1,(P.path t).2-d)=
            innerSlackV P.cap s ((P.path t).1,(P.path t).2-d₀)
              -(d-d₀)*cos s := by
        unfold innerSlackV dot uvec
        simp only [sin_add,cos_add,sin_pi_div_two,cos_pi_div_two]
        ring
      refine ⟨s,hs,?_,?_⟩
      · rw [hUmore]
        nlinarith [hU,min_le_right ((5/51)*d) τ,
          min_le_right (min τD τB) ((5/51)*d₀),
          mul_nonneg (sub_nonneg.mpr hsmall.le) hsin]
      · rw [hVmore]
        nlinarith [hV,min_le_right ((5/51)*d) τ,
          min_le_right (min τD τB) ((5/51)*d₀),
          mul_nonneg (sub_nonneg.mpr hsmall.le) hcos]
  · -- left D-tail
    have hti : t∈Ioo (0:ℝ) (π/2):=⟨ht.1.lt_of_ne (by
        rintro rfl
        rw [henv.D_end] at hfloor
        linarith),by linarith [ht.2,hB.θ_mem.2,pi_pos]⟩
    obtain ⟨hU,hV⟩:=innerSlack_down (d:=d) (hpath t hti.le)
      (envD P.path P.gs_β t)
    refine ⟨t,hti,?_,?_⟩
    · rw [hU]
      have hdot : dot (envD P.path P.gs_β t-P.path t) (uvec t)=-P.gs_β t := by
        simp [envD,dot_neg_left,dot_smul_left]
      rw [hdot]
      have hin : τD≤P.gs_β t:=hD t ht
      have hs:=sin_nonneg_of_nonneg_of_le_pi hti.1.le (by linarith [hti.2,pi_pos])
      nlinarith [min_le_left τD τ,mul_nonneg hd.le hs]
    · rw [hV,env_dot_D_self]
      have hc : (1/2:ℝ)≤cos t:=by
        have ht1 : t≤π/3:=by
          have hθ:=hB.θ_mem.2
          linarith [ht.2,pi_gt_three]
        exact cos_ge_half_of_mem hti.1.le ht1
      nlinarith [min_le_left ((5/51)*d) τ]


/-- The integrated regular-closed theorem identifies Gerver's niche with the
strict subgraph of its actual envelope (not an independent graph). -/
theorem gerver_niche_envelope {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    niche P.cap (π/2) = envUnderStrict (gerverEnvelope P) := by
  rw [gerver_cap_explicit hP hbox,
    gerver_niche_eq_envUnderStrict hP (romik_bounds hP hbox)]
  rfl

/-- Every point of Gerver's lower envelope belongs to the sofa.  The
envelope is in the closure of the niche, hence in the cap.  It is not in
the open niche: its strictly monotone horizontal graph has only one point
at any abscissa.  This is the missing boundary inclusion in the normal
and sector recovery chains. -/
theorem gerver_envelope_subset_shape {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    gerverEnvelope P ⊆ gerverSofa P := by
  have hB := romik_bounds hP hbox
  have henv := gn_envHyp hP hB
  obtain ⟨LΓ,hLΓ,hSlope⟩ := envelope_slope_bound henv
    (by linarith [henv.ht.2.2.1]) (by linarith [henv.ht.2.2.1])
  have hnc : envNiche P.path = niche P.cap (π/2) := by
    calc
      envNiche P.path =
          niche (capOf (gerverSofa P) (π/2)) (π/2) :=
        (gn_niche_eq hP hB).symm
      _ = niche P.cap (π/2) := by
        rw [(gs_monotone_K hP hB).2,gerver_cap_explicit hP hbox]
  intro q hq
  have hclos : q ∈ closure (envNiche P.path) := by
    have hmem := env_mem_closure henv
    rcases hq with (⟨t,ht,rfl⟩ | ⟨t,ht,rfl⟩) | ⟨t,ht,rfl⟩
    · exact hmem.2.1 t ht
    · exact hmem.1 t ht
    · exact hmem.2.2 t ht
  have hcap : q∈P.cap :=
    gm_closure_niche_subset_cap hP hbox (by rwa [←hnc])
  have hnot : q∉niche P.cap (π/2) := by
    rw [gerver_niche_envelope hP hbox]
    rintro ⟨_,z,hz,hzx,hlt⟩
    have heq : z=q := eq_of_same_abscissa hSlope hz hq hzx
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  rw [←gerver_shape_eq hP hbox]
  exact ⟨hcap,hnot⟩

/-- Two descriptions of the same strict subgraph force the graph height at
each point of the envelope. The vertical-slope condition supplies uniqueness
of the point of the envelope at the given horizontal coordinate. -/
theorem roof_value_of_envelope {P : GerverParams} {H L LΓ : ℝ}
    {γ : ℝ → ℝ}
    (hroof : CapRoofData P.cap (gerverRoofLeft P)
      (gerverRoofRight P) H L γ)
    (hΓ : niche P.cap (π/2) = envUnderStrict (gerverEnvelope P))
    (hSlope : VerticalSlopeBound (gerverEnvelope P) LΓ)
    (hbounds : ∀ z ∈ gerverEnvelope P,
      z.1 ∈ Icc (gerverRoofLeft P) (gerverRoofRight P) ∧ 0 ≤ z.2)
    {q : Point} (hq : q ∈ gerverEnvelope P) :
    γ q.1 = q.2 := by
  have hx := (hbounds q hq).1
  have hqy := (hbounds q hq).2
  have hγ0 := hroof.roof_nonneg q.1 hx
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · -- If the envelope is above the proposed roof, a midpoint belongs to
    -- the envelope subgraph but not to the roof subgraph.
    let p : Point := (q.1, (γ q.1 + q.2)/2)
    have hp : p ∈ envUnderStrict (gerverEnvelope P) := by
      refine ⟨by dsimp [p]; linarith, q, hq, by simp [p], by dsimp [p]; linarith⟩
    have hpN : p ∈ niche P.cap (π/2) := hΓ.symm ▸ hp
    rw [hroof.niche_eq] at hpN
    dsimp [p] at hpN
    linarith [hpN.2.2]
  · -- If the proposed roof is higher, its midpoint belongs to the roof
    -- subgraph and hence has an envelope witness higher than q. The
    -- vertical-slope bound forces that witness to be q itself.
    let p : Point := (q.1, (γ q.1 + q.2)/2)
    have hpN : p ∈ niche P.cap (π/2) := by
      rw [hroof.niche_eq]
      exact ⟨hx, by dsimp [p]; linarith, by dsimp [p]; linarith⟩
    rw [hΓ] at hpN
    obtain ⟨-, z, hz, hzx, hzy⟩ := hpN
    have hzx' : z.1 = q.1 := by simpa [p] using hzx
    have hzq : z = q := eq_of_same_abscissa hSlope hz hq hzx'
    subst z
    dsimp [p] at hzy
    linarith

/-- Explicit roof margin with coefficient 5/51. -/
theorem gerver_explicit_roof_slack {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {H L : ℝ} {γ : ℝ→ℝ}
    (hroof : CapRoofData P.cap (gerverRoofLeft P)
      (gerverRoofRight P) H L γ) :
    ∃τ : ℝ,0<τ ∧ RoofSlackMargin P.cap γ (5/51) τ := by
  obtain ⟨τ,hτ,hslack⟩:=gerver_envelope_downward_slack_explicit hP hbox
  have hB:=romik_bounds hP hbox
  have henv:=gn_envHyp hP hB
  have hΓ:=gerver_niche_envelope hP hbox
  obtain ⟨LΓ,hLΓ,hSlope⟩ := envelope_slope_bound henv
    (by linarith [henv.ht.2.2.1]) (by linarith [henv.ht.2.2.1])
  have hbounds : ∀ z ∈ gerverEnvelope P,
      z.1 ∈ Icc (gerverRoofLeft P) (gerverRoofRight P) ∧ 0 ≤ z.2 := by
    intro z hz
    have h := envelope_bounds_of_path_height henv
      (fun t ht => path_snd_lt_one hP hB ht.1 ht.2) z hz
    exact ⟨h.1,h.2.1⟩
  refine ⟨τ,hτ,?_⟩
  intro p hp
  rw [hroof.niche_eq] at hp
  have hpN : p∈niche P.cap (π/2):=by
    rw [hroof.niche_eq]
    exact hp
  rw [hΓ] at hpN
  obtain ⟨hpy,q,hq,hqx,hlt⟩:=hpN
  have hγq := roof_value_of_envelope hroof hΓ hSlope hbounds hq
  have hd : 0<q.2-p.2:=sub_pos.mpr hlt
  obtain ⟨t,ht,hU,hV⟩:=hslack q hq (q.2-p.2) hd (by linarith [hpy])
  rw [hγq,hqx] at hU hV
  simpa [sub_sub_cancel] using ⟨t,ht,hU,hV⟩

/-- Common endpoint formulas for Gerver's cap, used for both the total
cap width and the two floor-wing widths. -/
theorem gerver_endpoint_width_formulas {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    supp P.cap 0 = 1 ∧
    supp P.cap π = 1 - (P.path (π/2)).1 ∧
    gerverRoofLeft P = 1 - 2*P.a₁ ∧
    gerverRoofRight P = (P.path (π/2)).1 + 2*P.a₁ - 1 := by
  have hB := romik_bounds hP hbox
  have hzero : supp P.cap 0 = 1 := by
    rw [gerver_cap_explicit hP hbox,
      gs_supp_K hP hB le_rfl pi_pos.le,gs_H_zero hP]
  have hpi : supp P.cap π = 1 - (P.path (π/2)).1 := by
    rw [gerver_cap_explicit hP hbox,
      gs_supp_K hP hB pi_pos.le le_rfl,gs_H_pi]
  have hleft : gerverRoofLeft P = 1 - 2*P.a₁ := by
    unfold gerverRoofLeft envD
    rw [gs_path_zero hP]
    have hβ : P.gs_β 0 = 2*P.a₁ - 1 := by
      rw [gs_β_eq hP (show gs_piece P 0 0 by
        linarith [hB.φ_mem.1]),gs_β₁_eq hP]
      norm_num
    rw [hβ]
    simp [uvec]
    ring
  have hright : gerverRoofRight P =
      (P.path (π/2)).1 + 2*P.a₁ - 1 := by
    unfold gerverRoofRight envB
    rw [gs_α_pi_div_two hP]
    simp [vvec]
    ring
  exact ⟨hzero,hpi,hleft,hright⟩

/-- Each of the two floor wings is more than 4/5 wide.
No numerical geometry beyond the existing Romik box is used. -/
theorem gerver_wing_width_min {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    (4/5:ℝ) ≤ min
      (gerverRoofLeft P + supp P.cap π)
      (supp P.cap 0 - gerverRoofRight P) := by
  obtain ⟨h0,hpi,hl,hr⟩ :=
    gerver_endpoint_width_formulas hP hbox
  have hB := romik_bounds hP hbox
  have hX := gs_X₀_bounds hP hB
  have ha := hB.a₁_mem
  rw [hl,hpi,h0,hr,le_min_iff]
  constructor <;> nlinarith [hX.2,ha.2]

/-- Tighter reference cap width and niche-floor span. -/
theorem gerver_quantitative_widths {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    horizontalWidth P.cap<323/100 ∧
    gerverRoofRight P-gerverRoofLeft P<807/500 := by
  obtain ⟨h0,hpi,hl,hr⟩ :=
    gerver_endpoint_width_formulas hP hbox
  have hB := romik_bounds hP hbox
  have hX := gs_X₀_bounds hP hB
  have ha := hB.a₁_mem
  unfold horizontalWidth
  rw [h0,hpi,hl,hr]
  constructor
  · nlinarith [hX.1]
  · nlinarith [hX.2,ha.2]

end MovingSofaQuantitative
