module

public import MovingSofaQuantitative.TrialActiveArc
public import MovingSofaQuantitative.CriticalTrialData

/-!
# The genuine trial triple has the prescribed support profiles

Uncompiled proof source. The reference auxiliaries and the smaller active-arc
hulls need not agree away from their energy arcs. Their relevant supports do
agree exactly. This is sufficient for the Mamikon energy and dual-slack formula;
no equality of irrelevant outer boundaries is asserted.
-/

@[expose] public section
noncomputable section

open Real Set Filter Topology MeasureTheory
open MovingSofaOptimality MovingSofaStability MovingSofaOptimality.GerverParams

namespace MovingSofaQuantitative

private theorem mem_rightBody_iff (φ : ℝ) (K : Set Point) (p : Point) :
    p∈rightBody φ K ↔ p∈K ∧ ∀ t∈Icc φ (π/2),supp K t-1≤dot p (uvec t) := by
  simp only [rightBody,mem_inter_iff,mem_iInter,halfB,halfPlus,mem_setOf_eq]

private theorem mem_leftBody_iff (φ : ℝ) (K : Set Point) (p : Point) :
    p∈leftBody φ K ↔ p∈K ∧ ∀ s∈Icc (0 : ℝ) (π/2-φ),
      supp K (s+π/2)-1≤dot p (uvec (s+π/2)) := by
  simp only [leftBody,mem_inter_iff,mem_iInter,halfD,halfPlus,mem_setOf_eq]

/-- This symmetry is used only for the reference and chosen symmetric trials. -/
theorem leftBody_eq_reflected_right {K : Set Point} (hK : IsCap K (π/2))
    {φ m : ℝ} (hφ : φ∈Ioo (0 : ℝ) (π/2))
    (hsym : ∀ t∈Icc (0 : ℝ) π,supp K t=supp K (π-t)+2*m*cos t) :
    leftBody φ K=verticalReflection m '' rightBody φ K := by
  have hsymK := cap_verticalReflection_eq hK hsym
  have hKmem (p : Point) : p∈K ↔ verticalReflection m p∈K := by
    constructor
    · intro hp
      rw [←hsymK]
      exact mem_image_of_mem _ hp
    · intro hp
      have hh : verticalReflection m (verticalReflection m p)∈K := by
        rw [←hsymK]
        exact mem_image_of_mem _ hp
      simpa using hh
  ext p
  have himage : p∈verticalReflection m '' rightBody φ K ↔ verticalReflection m p∈rightBody φ K := by
    constructor
    · rintro ⟨q,hq,rfl⟩
      simpa using hq
    · intro hp
      exact ⟨verticalReflection m p,hp,verticalReflection_involutive m p⟩
  rw [himage,mem_rightBody_iff,mem_leftBody_iff]
  constructor
  · rintro ⟨hp,hw⟩
    refine ⟨(hKmem p).1 hp,?_⟩
    intro t ht
    have hs : π/2-t∈Icc (0 : ℝ) (π/2-φ) := ⟨by linarith [ht.2],by linarith [ht.1]⟩
    have hh := hw (π/2-t) hs
    rw [show π/2-t+π/2=π-t by ring] at hh
    rw [verticalReflection_dot,hsym t ⟨hφ.1.le.trans ht.1,by linarith [ht.2,pi_pos]⟩]
    linarith
  · rintro ⟨hp,hw⟩
    refine ⟨(hKmem p).2 hp,?_⟩
    intro s hs
    have ht : π/2-s∈Icc φ (π/2) := ⟨by linarith [hs.2],by linarith [hs.1]⟩
    have hh := hw (π/2-s) ht
    rw [verticalReflection_dot,show π-(π/2-s)=s+π/2 by ring] at hh
    have he := hsym (s+π/2) ⟨by linarith [hs.1,pi_pos],by linarith [hs.2,hφ.1]⟩
    rw [show π-(s+π/2)=π/2-s by ring] at he
    have hc : cos(s+π/2)= -cos(π/2-s) := by simp [cos_add,cos_sub]
    rw [hc] at he
    linarith

/-- Exact B support on its whole relevant lower-normal interval. -/
theorem reference_B_support {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {s : ℝ} (hs : s∈Icc P.φ (π/2)) :
    supp (rightBody P.φ P.cap) (π+s)=
      -dot (contactB P.path (max (π/2-P.θ) s)) (uvec s) := by
  have hO := gs_ord hP
  by_cases hsc : s≤π/2-P.θ
  · rw [max_eq_left hsc,gs_contactB_t₃ hP,
      ←dot_vplus_uvec (rightBody P.φ P.cap) (π+s),
      (gm_B_corner hP hbox ⟨hs.1,hsc⟩).2,
      gm_innerCorner hP hbox ⟨hO.1.le,by linarith [hO.2.1,hO.2.2,pi_pos]⟩]
    simp [dot,uvec,cos_pi_add,sin_pi_add]
  · rw [max_eq_right (not_le.mp hsc).le]
    have hp := (theorem8_4_3_three hP hbox).2 s ⟨(not_le.mp hsc).le,hs.2⟩
    have hpath := (gerver_support_path_pair hP hbox ⟨hO.1.le.trans hs.1,hs.2⟩).1
    have hdot : dot(contactB P.path s)(uvec s)=dot(P.path s)(uvec s) := by
      simp [contactB,dot_add_left,dot_smul_left]
    rw [hdot]
    linarith

/-- The actual auxiliary profile: a harmonic vertex before contact, the
negative cap perturbation on the active arc. -/
def trialAuxiliaryProfile {φ : ℝ} (F : HalfCapProfile φ) (c t : ℝ) : ℝ :=
  if t≤c then -harmonicBridge φ c (F.value φ) (F.value c) t else -F.value t

def trialAuxiliaryDerivative {φ : ℝ} (F : HalfCapProfile φ) (c t : ℝ) : ℝ :=
  if t<c then -harmonicBridgeFirst φ c (F.value φ) (F.value c) t else -F.first t

/-- The active-arc hull has exactly the prescribed support change. -/
theorem trial_B_support_difference {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (F : HalfCapProfile P.φ) {τ : ℝ} (hτ : 0≤τ) (hsmall : τ≤F.safeAmplitude)
    (hjet : F.first (π/2-P.θ)=harmonicBridgeFirst P.φ (π/2-P.θ)
      (F.value P.φ) (F.value (π/2-P.θ)) (π/2-P.θ))
    (D : ActiveArcData P.φ (π/2-P.θ) (perturbedCap hP hbox F τ hτ hsmall).1)
    (hcurve : D.curve=perturbedInnerCurve P F τ)
    {s : ℝ} (hs : s∈Icc P.φ (π/2)) :
    supp D.body (π+s)-supp (rightBody P.φ P.cap) (π+s)=
      τ*trialAuxiliaryProfile F (π/2-P.θ) s := by
  have hO := gs_ord hP
  have hsin : sin((π/2-P.θ)-P.φ)≠0 :=
    (sin_pos_of_pos_of_lt_pi (by linarith [hO.2.1,hO.2.2]) (by linarith [hO.1,pi_pos])).ne'
  rw [D.support hs,reference_B_support hP hbox hs,hcurve]
  simp only [perturbedInnerCurve,dot_add_left,dot_smul_left,trialAuxiliaryProfile]
  by_cases hsc : s≤π/2-P.θ
  · rw [if_pos hsc,max_eq_left hsc,F.bridge_projection hsin hjet]
    ring
  · rw [if_neg hsc,max_eq_right (not_le.mp hsc).le]
    simp [HalfCapProfile.rightOffset,dot_add_left,dot_smul_left]
    ring

/-- The reflected support difference has no residual translation term because
both the reference and trial use the same reflection axis. -/
theorem trial_D_support_difference {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (F : HalfCapProfile P.φ) {τ : ℝ} (hτ : 0≤τ) (hsmall : τ≤F.safeAmplitude)
    (hjet : F.first (π/2-P.θ)=harmonicBridgeFirst P.φ (π/2-P.θ)
      (F.value P.φ) (F.value (π/2-P.θ)) (π/2-P.θ))
    (D : ActiveArcData P.φ (π/2-P.θ) (perturbedCap hP hbox F τ hτ hsmall).1)
    (hcurve : D.curve=perturbedInnerCurve P F τ)
    {s : ℝ} (hs : s∈Icc (π/2) (π-P.φ)) :
    supp (verticalReflection P.κ₃.1 '' D.body) (π+s)-
      supp (leftBody P.φ P.cap) (π+s)=
      τ*trialAuxiliaryProfile F (π/2-P.θ) (π-s) := by
  have hO := gs_ord hP
  have hφv : P.φ∈Ioo (0 : ℝ) (π/2) := ⟨hO.1,by linarith [hO.2.1,hO.2.2,pi_pos]⟩
  rw [leftBody_eq_reflected_right (gm_isCap hP hbox) hφv
      (fun t ht => gerver_cap_reflection_support hP hbox ht),
    verticalReflection_support D.body_isConvexBody,
    verticalReflection_support (gm_isConvexBody_B hP hbox)]
  have period (B : Set Point) : supp B (π-(π+s))=supp B (π+(π-s)) := by
    unfold supp
    simp only [uvec,show π-(π+s)= -s by ring,show π+(π-s)= -s+2*π by ring,
      cos_add_two_pi,sin_add_two_pi]
  rw [period D.body,period (rightBody P.φ P.cap),add_sub_add_right_eq_sub]
  exact trial_B_support_difference hP hbox F hτ hsmall hjet D hcurve
    ⟨by linarith [hs.2],by linarith [hs.1]⟩

/-- The constructed continuously feasible triple belongs exactly to the
zero-first-variation face, not merely to its tangent approximation. -/
theorem activeArc_trial_zero_slack {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (F : HalfCapProfile P.φ) {τ : ℝ} (hτ : 0≤τ) (hsmall : τ≤F.safeAmplitude)
    (D : ActiveArcData P.φ (π/2-P.θ) (perturbedCap hP hbox F τ hτ hsmall).1) :
    wideDualSlack hP hbox
      (D.wideTriple (fun t ht => perturbedCap_reflection_support hP hbox F hτ hsmall ht))=0 := by
  let x := D.wideTriple (fun t ht => perturbedCap_reflection_support hP hbox F hτ hsmall ht)
  change wideDualSlack hP hbox x=0
  rw [wideDualSlack_eq_active_integrals hP hbox]
  have hB : (∫ t,rightWallSlack x t ∂activeMeasureB P)=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    have hh := D.active ⟨ht.1,ht.2.le⟩
    change 1-supp x.1.1.1 t-supp x.1.2.1.1 (π+t)=0
    change 1-supp (perturbedCap hP hbox F τ hτ hsmall).1 t-supp D.body (π+t)=0
    linarith
  have hD : (∫ t,leftWallSlack x t ∂activeMeasureD P)=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    have hh := D.wideTriple_left_active
      (fun t ht => perturbedCap_reflection_support hP hbox F hτ hsmall ht)
      (s := t-π/2) ⟨by linarith [ht.1],by linarith [ht.2]⟩
    rw [show π/2+(t-π/2)=t by ring,show 3*π/2+(t-π/2)=π+t by ring] at hh
    change 1-supp x.1.1.1 t-supp x.1.2.2.1 (π+t)=0
    linarith
  rw [hB,hD,add_zero]

end MovingSofaQuantitative
