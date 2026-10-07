module

public import MovingSofaOptimality.Gerver.Frame
public import MovingSofaOptimality.External.Romik.Fix
public import MovingSofaStability.Basic

/-!
# Coarse uniform speed and derivative bounds for Gerver's five phases

UNCOMPILED SOURCE. All numerical bounds here are deliberately loose. They
are intended for the explicit normal-recovery radius 10^-8 rather than for
optimizing a coefficient. Unlike pointwise compactness, the five-phase
bounds below have a common numerical constant.

The exact phase definition and parameter equalities are inherited from
Gerver/Frame. No extra reference-boundary parameterization is introduced.
-/

@[expose] public section
noncomputable section
open Real Set MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

def phaseAlpha (P : GerverParams) (i : Fin 5) (t : ℝ) : ℝ :=
  (P.gs_phase i.val).α t
def phaseBeta (P : GerverParams) (i : Fin 5) (t : ℝ) : ℝ :=
  (P.gs_phase i.val).β t
def phaseAlphaPrime (P : GerverParams) (i : Fin 5) (t : ℝ) : ℝ :=
  (P.gs_phase i.val).w₁'' t-(P.gs_phase i.val).w₂' t
def phaseBetaPrime (P : GerverParams) (i : Fin 5) (t : ℝ) : ℝ :=
  (P.gs_phase i.val).w₂'' t+(P.gs_phase i.val).w₁' t

theorem phase_alpha_hasDerivAt (P : GerverParams) (i : Fin 5) (t : ℝ) :
    HasDerivAt (phaseAlpha P i) (phaseAlphaPrime P i t) t := by
  have hV:=(P.gs_valid i.val)
  unfold phaseAlpha phaseAlphaPrime gs_Phase.α
  exact (hV.dd₁ t).sub (hV.d₂ t)

theorem phase_beta_hasDerivAt (P : GerverParams) (i : Fin 5) (t : ℝ) :
    HasDerivAt (phaseBeta P i) (phaseBetaPrime P i t) t := by
  have hV:=(P.gs_valid i.val)
  unfold phaseBeta phaseBetaPrime gs_Phase.β
  exact (hV.dd₂ t).add (hV.d₁ t)

/-- The absolute values of alpha, beta, and their derivatives are below 5
on each explicit phase on the full interval 0<=t<=pi/2.
This is an interval bound on fixed analytic functions, not an assumption
about arbitrary nearby caps. -/
theorem phase_coefficient_bounds {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    (i : Fin 5) {t : ℝ} (ht : t∈Icc (0:ℝ) (π/2)) :
    |phaseAlpha P i t|≤5 ∧ |phaseBeta P i t|≤5 ∧
    |phaseAlphaPrime P i t|≤5 ∧ |phaseBetaPrime P i t|≤5 := by
  have hB:=romik_bounds hP hbox
  have hsin : |sin t|≤1 := abs_sin_le_one t
  have hcos : |cos t|≤1 := abs_cos_le_one t
  have hsin' : |sin (π/2-t)|≤1 := abs_sin_le_one _
  have hcos' : |cos (π/2-t)|≤1 := abs_cos_le_one _
  have hπ : (0:ℝ)<π ∧ π<4 := ⟨pi_pos,pi_lt_four⟩
  have ha:=hB.a₁_mem
  have hb1:=hB.b₁_mem
  have hb2:=hB.b₂_mem
  have hc:=hB.c₁_mem
  have ht0:=ht.1
  have ht2:=ht.2
  have hP_a₂:=gs_a₂ hP
  have hP_c₂:=gs_c₂ hP
  have hP_d₁:=gs_d₁ hP
  have hP_d₂:=gs_d₂ hP
  have hP_e₁:=gs_e₁ hP
  have hP_e₂:=gs_e₂ hP
  -- Products of the parameter coefficients with sin/cos remain below 2.
  have htrig : ∀A : ℝ, |A|≤2 →
      |A*sin t|≤2 ∧ |A*cos t|≤2 ∧
      |A*sin (π/2-t)|≤2 ∧ |A*cos (π/2-t)|≤2 := by
    intro A hA
    constructor
    · rw [abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left hsin (abs_nonneg A)]
    constructor
    · rw [abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left hcos (abs_nonneg A)]
    constructor
    · rw [abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left hsin' (abs_nonneg A)]
    · rw [abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left hcos' (abs_nonneg A)]
  have haBound : |P.a₁|≤2 := by rw [abs_of_pos (by linarith [ha.1])]; linarith [ha.2]
  have heBound : |P.e₁|≤2 := by rw [hP_e₁]; exact haBound
  fin_cases i
  · -- Phase 1, two trigonometric coefficients.
    have htA:=htrig P.a₁ haBound
    simp only [phaseAlpha,phaseBeta,phaseAlphaPrime,phaseBetaPrime,
      gs_phase,gs_Phase.α,gs_Phase.β,gs_ph1,
      hP_a₂] at *
    rw [abs_le,abs_le,abs_le,abs_le]
    constructor
    · constructor <;> nlinarith [htA.1,htA.2.1,hsin,hcos]
    constructor
    · constructor <;> nlinarith [htA.1,htA.2.1,hsin,hcos]
    constructor
    · constructor <;> nlinarith [htA.1,htA.2.1,hsin,hcos]
    · constructor <;> nlinarith [htA.1,htA.2.1,hsin,hcos]
  · -- Phase 2, polynomial.
    simp only [phaseAlpha,phaseBeta,phaseAlphaPrime,phaseBetaPrime,
      gs_phase,gs_Phase.α,gs_Phase.β,gs_ph2] at *
    rw [abs_le,abs_le,abs_le,abs_le]
    constructor
    · constructor <;> nlinarith [hb1.1,hb1.2,ht0,ht2,hπ.1,hπ.2]
    constructor
    · constructor <;> nlinarith [hb1.1,hb1.2,hb2.1,hb2.2,ht0,ht2,hπ.2]
    constructor
    · constructor <;> nlinarith
    · constructor <;> nlinarith [hb1.1,hb1.2,ht0,ht2,hπ.2]
  · -- Phase 3, affine.
    simp only [phaseAlpha,phaseBeta,phaseAlphaPrime,phaseBetaPrime,
      gs_phase,gs_Phase.α,gs_Phase.β,gs_ph3,hP_c₂] at *
    rw [abs_le,abs_le,abs_le,abs_le]
    constructor
    · constructor <;> nlinarith [hc.1,hc.2,ht0,ht2,hπ.2]
    constructor
    · constructor <;> nlinarith [hc.1,hc.2,ht0,ht2,hπ.2]
    constructor
    · constructor <;> norm_num
    · constructor <;> norm_num
  · -- Phase 4, the reflected polynomial phase.
    simp only [phaseAlpha,phaseBeta,phaseAlphaPrime,phaseBetaPrime,
      gs_phase,gs_Phase.α,gs_Phase.β,gs_ph4,hP_d₁,hP_d₂] at *
    rw [abs_le,abs_le,abs_le,abs_le]
    constructor
    · constructor <;> nlinarith [hb1.1,hb1.2,hb2.1,hb2.2,ht0,ht2,hπ.2]
    constructor
    · constructor <;> nlinarith [hb1.1,hb1.2,ht0,ht2,hπ.2]
    constructor
    · constructor <;> nlinarith [hb1.1,hb1.2,ht0,ht2,hπ.2]
    · constructor <;> nlinarith [hb1.1,hb1.2,ht0,ht2,hπ.2]
  · -- Phase 5, reflected trigonometric phase.
    have htA:=htrig P.a₁ haBound
    simp only [phaseAlpha,phaseBeta,phaseAlphaPrime,phaseBetaPrime,
      gs_phase,gs_Phase.α,gs_Phase.β,gs_ph5,
      hP_e₁,hP_e₂,hP_a₂] at *
    rw [abs_le,abs_le,abs_le,abs_le]
    constructor
    · constructor <;> nlinarith [htA.1,htA.2.1,hsin,hcos]
    constructor
    · constructor <;> nlinarith [htA.1,htA.2.1,hsin,hcos]
    constructor
    · constructor <;> nlinarith [htA.1,htA.2.1,hsin,hcos]
    · constructor <;> nlinarith [htA.1,htA.2.1,hsin,hcos]

/-- The four scalar coefficient functions in every Gerver phase have a
common Lipschitz constant five on the full right-angle domain. -/
theorem phase_coefficients_lipschitz {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) (i : Fin 5)
    {s t : ℝ} (hs : s∈Icc (0:ℝ) (π/2)) (ht : t∈Icc (0:ℝ) (π/2)) :
    |phaseAlpha P i s-phaseAlpha P i t|≤5*|s-t| ∧
      |phaseBeta P i s-phaseBeta P i t|≤5*|s-t| := by
  have hda : ∀u∈Icc (0:ℝ) (π/2),
      HasDerivAt (phaseAlpha P i) (phaseAlphaPrime P i u) u :=
    fun u _=>phase_alpha_hasDerivAt P i u
  have hdb : ∀u∈Icc (0:ℝ) (π/2),
      HasDerivAt (phaseBeta P i) (phaseBetaPrime P i u) u :=
    fun u _=>phase_beta_hasDerivAt P i u
  have hba : ∀u∈Icc (0:ℝ) (π/2),
      |phaseAlphaPrime P i u|≤5 := fun u hu=>
    (phase_coefficient_bounds hP hbox i hu).2.2.1
  have hbb : ∀u∈Icc (0:ℝ) (π/2),
      |phaseBetaPrime P i u|≤5 := fun u hu=>
    (phase_coefficient_bounds hP hbox i hu).2.2.2
  exact ⟨rom_mvt hda hba hs ht,rom_mvt hdb hbb hs ht⟩

/-- The orthonormal angular frame is at most 2-Lipschitz in the elementary
sum-of-coordinate norm.  The second frame vector has the same bound. -/
theorem angular_frame_modulus (s t : ℝ) :
    norm2 (uvec s-uvec t)≤2*|s-t| ∧
    norm2 (vvec s-vvec t)≤2*|s-t| := by
  have hsin:=Real.lipschitzWith_sin.dist_le_mul s t
  have hcos:=Real.lipschitzWith_cos.dist_le_mul s t
  simp only [Real.dist_eq] at hsin hcos
  constructor
  · exact (norm2_le_abs_add _).trans (by
      simp only [uvec,Prod.fst_sub,Prod.snd_sub]
      linarith)
  · exact (norm2_le_abs_add _).trans (by
      simp only [vvec,Prod.fst_sub,Prod.snd_sub,abs_neg]
      linarith)

/-- A single phase's frame velocity is 40-Lipschitz (the direct elementary
estimate gives 30). The statement does not assert that the global glued
velocity has the same formula at every point. -/
theorem phase_velocity_lipschitz {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) (i : Fin 5)
    {s t : ℝ} (hs : s∈Icc (0:ℝ) (π/2)) (ht : t∈Icc (0:ℝ) (π/2)) :
    norm2 ((P.gs_phase i.val).X' s-(P.gs_phase i.val).X' t)
      ≤40*|s-t| := by
  let α:=phaseAlpha P i
  let β:=phaseBeta P i
  have hcoef:=phase_coefficients_lipschitz hP hbox i hs ht
  have hbound : |α t|≤5 ∧ |β t|≤5 := by
    have hh:=phase_coefficient_bounds hP hbox i ht
    exact ⟨hh.1,hh.2.1⟩
  have hframes:=angular_frame_modulus s t
  have hexp :
      (P.gs_phase i.val).X' s-(P.gs_phase i.val).X' t =
      (α s-α t)•uvec s+(β s-β t)•vvec s+
        α t•(uvec s-uvec t)+β t•(vvec s-vvec t) := by
    dsimp [α,β,phaseAlpha,phaseBeta,gs_Phase.X']
    abel
  rw [hexp]
  have hnorm:=norm2_add_le
    ((α s-α t)•uvec s+(β s-β t)•vvec s)
    (α t•(uvec s-uvec t)+β t•(vvec s-vvec t))
  have hnorm1:=norm2_add_le ((α s-α t)•uvec s) ((β s-β t)•vvec s)
  have hnorm2:=norm2_add_le (α t•(uvec s-uvec t)) (β t•(vvec s-vvec t))
  have hu : norm2 (uvec s)=1 := norm2_uvec s
  have hv : norm2 (vvec s)=1 := norm2_vvec s
  simp only [norm2_smul,hu,hv,mul_one] at hnorm1 hnorm2
  have hmulU : |α t|*norm2 (uvec s-uvec t)≤10*|s-t| := by
    nlinarith [mul_le_mul hbound.1 hframes.1 (abs_nonneg _) (by positivity)]
  have hmulV : |β t|*norm2 (vvec s-vvec t)≤10*|s-t| := by
    nlinarith [mul_le_mul hbound.2 hframes.2 (abs_nonneg _) (by positivity)]
  nlinarith [hnorm,hnorm1,hnorm2,hcoef.1,hcoef.2,hmulU,hmulV]

/-- A uniform phase speed estimate. -/
theorem phase_velocity_norm_le_ten {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) (i : Fin 5)
    {t : ℝ} (ht : t∈Icc (0:ℝ) (π/2)) :
    norm2 ((P.gs_phase i.val).X' t)≤10 := by
  have hb:=phase_coefficient_bounds hP hbox i ht
  simp only [gs_Phase.X']
  have hu:=norm2_uvec t
  have hv:=norm2_vvec t
  have hh:=norm2_add_le
    ((P.gs_phase i.val).α t•uvec t)
    ((P.gs_phase i.val).β t•vvec t)
  simpa [norm2_smul,hu,hv,phaseAlpha,phaseBeta] using
    hh.trans (by nlinarith [hb.1,hb.2.1])

/-- Gluing two Lipschitz bounds at a common endpoint.  The same constant
works on the union; no derivative at the joining point is needed. -/
theorem planar_lipschitz_glue {f : ℝ→Point} {a b c L : ℝ}
    (hab : a≤b) (hbc : b≤c) (hL : 0≤L)
    (hl : ∀s∈Icc a b,∀t∈Icc a b,
      norm2 (f s-f t)≤L*|s-t|)
    (hr : ∀s∈Icc b c,∀t∈Icc b c,
      norm2 (f s-f t)≤L*|s-t|) :
    ∀s∈Icc a c,∀t∈Icc a c,
      norm2 (f s-f t)≤L*|s-t| := by
  intro s hs t ht
  wlog hst : s≤t generalizing s t
  · have h:=this ht hs (le_of_not_ge hst)
    simpa only [←neg_sub, norm2_neg,abs_sub_comm] using h
  by_cases htLeft : t≤b
  · exact hl s ⟨hs.1,hst.trans htLeft⟩
      t ⟨hst.trans htLeft,htLeft⟩
  by_cases hsRight : b≤s
  · exact hr s ⟨hsRight,hs.2⟩ t ⟨hsRight.trans hst,ht.2⟩
  have hsL : s∈Icc a b := ⟨hs.1,le_of_not_ge hsRight⟩
  have htR : t∈Icc b c := ⟨le_of_not_ge htLeft,ht.2⟩
  have hbL : b∈Icc a b := ⟨hab,le_rfl⟩
  have hbR : b∈Icc b c := ⟨le_rfl,hbc⟩
  have hsum:=norm2_add_le (f s-f b) (f b-f t)
  have hsplit : f s-f t=(f s-f b)+(f b-f t) := by abel
  rw [hsplit]
  have h1:=hl s hsL b hbL
  have h2:=hr b hbR t htR
  rw [abs_of_nonpos (sub_nonpos.mpr hsL.2)] at h1
  rw [abs_of_nonpos (sub_nonpos.mpr htR.1)] at h2
  rw [abs_of_nonpos (sub_nonpos.mpr hst)]
  nlinarith [hsum,h1,h2]

/-- Uniform global speed bound from the true five-piece Gerver data. -/
theorem gerver_path_velocity_bound {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t∈Icc (0:ℝ) (π/2)) :
    norm2 (P.gs_pathD t)≤10 := by
  have hB:=romik_bounds hP hbox
  rcases gs_cases (P:=P) t with h0|h1|h2|h3|h4
  · rw [gs_pathD_eq_phase hP (gs_piece₀ h0)]
    exact phase_velocity_norm_le_ten hP hbox ⟨0,by decide⟩ ht
  · rw [gs_pathD_eq_phase hP (gs_piece₁ h1.1.le h1.2)]
    exact phase_velocity_norm_le_ten hP hbox ⟨1,by decide⟩ ht
  · rw [gs_pathD_eq_phase hP (gs_piece₂ h2.1.le h2.2)]
    exact phase_velocity_norm_le_ten hP hbox ⟨2,by decide⟩ ht
  · rw [gs_pathD_eq_phase hP (gs_piece₃ h3.1.le h3.2)]
    exact phase_velocity_norm_le_ten hP hbox ⟨3,by decide⟩ ht
  · rw [gs_pathD_eq_phase hP (gs_piece₄ h4.le)]
    exact phase_velocity_norm_le_ten hP hbox ⟨4,by decide⟩ ht

/-- Gerver's C1 path velocity is 40-Lipschitz throughout the right-angle
turn. On each of five explicit analytic pieces, the scalar frame estimates
give the bound; the four phase junctions are handled by the gluing lemma. -/
theorem gerver_path_velocity_lipschitz {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {s t : ℝ} (hs : s∈Icc (0:ℝ) (π/2))
    (ht : t∈Icc (0:ℝ) (π/2)) :
    norm2 (P.gs_pathD s-P.gs_pathD t)≤40*|s-t| := by
  have hB:=romik_bounds hP hbox
  have hφ:=hB.φ_mem
  have hθ:=hB.θ_mem
  have horder:=gs_ord hP
  have h0 : (0:ℝ)≤P.φ:=hφ.1.le
  have h1 : P.φ≤P.θ := by linarith [hφ.2,hθ.1]
  have h2 : P.θ≤π/2-P.θ := by
    have hp:=pi_gt_three
    linarith [hθ.2]
  have h3 : π/2-P.θ≤π/2-P.φ := by linarith [h1]
  have h4 : π/2-P.φ≤π/2 := by linarith [h0]
  have hlo : ∀i : Fin 5, ∀u v,
      u∈Icc (0:ℝ) (π/2)→v∈Icc (0:ℝ) (π/2) →
      norm2 ((P.gs_phase i.val).X' u-(P.gs_phase i.val).X' v)≤40*|u-v| :=
    fun i u v hu hv=>phase_velocity_lipschitz hP hbox i hu hv
  have hphase0 : ∀u∈Icc (0:ℝ) P.φ,∀v∈Icc (0:ℝ) P.φ,
      norm2 (P.gs_pathD u-P.gs_pathD v)≤40*|u-v| := by
    intro u hu v hv
    rw [gs_pathD_eq_phase hP (gs_piece₀ hu.2),
        gs_pathD_eq_phase hP (gs_piece₀ hv.2)]
    exact hlo ⟨0,by decide⟩ u v
      ⟨hu.1,by linarith [hu.2,hφ.2,pi_gt_three]⟩
      ⟨hv.1,by linarith [hv.2,h4]⟩
  have hphase1 : ∀u∈Icc P.φ P.θ,∀v∈Icc P.φ P.θ,
      norm2 (P.gs_pathD u-P.gs_pathD v)≤40*|u-v| := by
    intro u hu v hv
    rw [gs_pathD_eq_phase hP (gs_piece₁ hu.1 hu.2),
        gs_pathD_eq_phase hP (gs_piece₁ hv.1 hv.2)]
    exact hlo ⟨1,by decide⟩ u v
      ⟨h0.trans hu.1,by linarith [hu.2,hθ.2,pi_gt_three]⟩
      ⟨h0.trans hv.1,by linarith [hv.2,hθ.2,pi_gt_three]⟩
  have hphase2 : ∀u∈Icc P.θ (π/2-P.θ),∀v∈Icc P.θ (π/2-P.θ),
      norm2 (P.gs_pathD u-P.gs_pathD v)≤40*|u-v| := by
    intro u hu v hv
    rw [gs_pathD_eq_phase hP (gs_piece₂ hu.1 hu.2),
        gs_pathD_eq_phase hP (gs_piece₂ hv.1 hv.2)]
    exact hlo ⟨2,by decide⟩ u v
      ⟨h0.trans (h1.trans hu.1),by linarith [hu.2,hθ.1]⟩
      ⟨h0.trans (h1.trans hv.1),by linarith [hv.2,hθ.1]⟩
  have hphase3 : ∀u∈Icc (π/2-P.θ) (π/2-P.φ),
      ∀v∈Icc (π/2-P.θ) (π/2-P.φ),
      norm2 (P.gs_pathD u-P.gs_pathD v)≤40*|u-v| := by
    intro u hu v hv
    rw [gs_pathD_eq_phase hP (gs_piece₃ hu.1 hu.2),
        gs_pathD_eq_phase hP (gs_piece₃ hv.1 hv.2)]
    exact hlo ⟨3,by decide⟩ u v
      ⟨by linarith [hu.1,hθ.2,pi_gt_three],hu.2.trans h4⟩
      ⟨by linarith [hv.1,hθ.2,pi_gt_three],hv.2.trans h4⟩
  have hphase4 : ∀u∈Icc (π/2-P.φ) (π/2),
      ∀v∈Icc (π/2-P.φ) (π/2),
      norm2 (P.gs_pathD u-P.gs_pathD v)≤40*|u-v| := by
    intro u hu v hv
    rw [gs_pathD_eq_phase hP (gs_piece₄ hu.1),
        gs_pathD_eq_phase hP (gs_piece₄ hv.1)]
    exact hlo ⟨4,by decide⟩ u v
      ⟨by linarith [hu.1,hφ.2,pi_gt_three],hu.2⟩
      ⟨by linarith [hv.1,hφ.2,pi_gt_three],hv.2⟩
  have h01:=planar_lipschitz_glue h0 h1 (show (0:ℝ)≤40 by norm_num)
    hphase0 hphase1
  have h02:=planar_lipschitz_glue (h0.trans h1) h2
    (show (0:ℝ)≤40 by norm_num) h01 hphase2
  have h03:=planar_lipschitz_glue ((h0.trans h1).trans h2) h3
    (show (0:ℝ)≤40 by norm_num) h02 hphase3
  have h04:=planar_lipschitz_glue (((h0.trans h1).trans h2).trans h3) h4
    (show (0:ℝ)≤40 by norm_num) h03 hphase4
  exact h04 s hs t ht

end MovingSofaQuantitative
