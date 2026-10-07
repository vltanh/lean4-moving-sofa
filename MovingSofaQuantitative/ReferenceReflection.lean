module

public import MovingSofaQuantitative.ReflectedAuxiliary
public import MovingSofaQuantitative.PerturbationEnergy

/-!
# Exact reflection of Gerver and the deliberately symmetric trial cap

Uncompiled proof source. The symmetry is derived from the parameter equations
and phase matching. It is not inferred from a numerical drawing, nor assumed
of a general cap or competing sofa.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaStability MovingSofaOptimality.GerverParams

namespace MovingSofaQuantitative

private theorem reflection_add (m : ℝ) (p q : Point) :
    verticalReflection m (p+q) = verticalReflection m p + verticalReflection 0 q := by
  ext <;> simp [verticalReflection] <;> ring

private theorem reflection_phase3 {P : GerverParams} (hP : P.IsSolution) (t : ℝ) :
    P.x₃ (π/2-t)=verticalReflection P.κ₃.1 (P.x₃ t) := by
  ext <;> simp only [x₃, rot, verticalReflection, Prod.fst_add, Prod.snd_add,
    cos_pi_div_two_sub, sin_pi_div_two_sub, gs_c₂ hP] <;> ring

private theorem reflection_phase24_raw {P : GerverParams} (hP : P.IsSolution) (t : ℝ) :
    P.x₄ (π/2-t) = verticalReflection 0 (P.x₂ t) +
      (P.κ₄.1+P.κ₂.1,P.κ₄.2-P.κ₂.2) := by
  ext <;> simp only [x₂,x₄,rot,verticalReflection,Prod.fst_add,Prod.snd_add,
    cos_pi_div_two_sub,sin_pi_div_two_sub,gs_d₁ hP,gs_d₂ hP] <;> ring

private theorem reflection_phase15_raw {P : GerverParams} (hP : P.IsSolution) (t : ℝ) :
    P.x₅ (π/2-t) = verticalReflection 0 (P.x₁ t) +
      (P.κ₅.1+P.κ₁.1,P.κ₅.2-P.κ₁.2) := by
  ext <;> simp only [x₁,x₅,rot,verticalReflection,Prod.fst_add,Prod.snd_add,
    cos_pi_div_two_sub,sin_pi_div_two_sub,gs_e₁ hP,gs_e₂ hP] <;> ring

private theorem reflection_phase24 {P : GerverParams} (hP : P.IsSolution) (t : ℝ) :
    P.x₄ (π/2-t)=verticalReflection P.κ₃.1 (P.x₂ t) := by
  have hm := gs_matchX hP
  have h23 : P.x₂ P.θ=P.x₃ P.θ := hm.2.1
  have h34 : P.x₃ (π/2-P.θ)=P.x₄ (π/2-P.θ) := hm.2.2.1
  have hanchor : P.x₄ (π/2-P.θ)=verticalReflection P.κ₃.1 (P.x₂ P.θ) := by
    rw [←h34,reflection_phase3 hP,h23]
  have hraw := reflection_phase24_raw hP P.θ
  have hx := congrArg Prod.fst (hraw.symm.trans hanchor)
  have hy := congrArg Prod.snd (hraw.symm.trans hanchor)
  simp only [verticalReflection,Prod.fst_add,Prod.snd_add,zero_mul,zero_sub] at hx hy
  rw [reflection_phase24_raw hP]
  ext <;> simp only [verticalReflection,Prod.fst_add,Prod.snd_add,zero_mul,zero_sub] <;>
    linarith

private theorem reflection_phase15 {P : GerverParams} (hP : P.IsSolution) (t : ℝ) :
    P.x₅ (π/2-t)=verticalReflection P.κ₃.1 (P.x₁ t) := by
  have hm := gs_matchX hP
  have h12 : P.x₁ P.φ=P.x₂ P.φ := hm.1
  have h45 : P.x₄ (π/2-P.φ)=P.x₅ (π/2-P.φ) := hm.2.2.2
  have hanchor : P.x₅ (π/2-P.φ)=verticalReflection P.κ₃.1 (P.x₁ P.φ) := by
    rw [←h45,reflection_phase24 hP,←h12]
  have hraw := reflection_phase15_raw hP P.φ
  have hx := congrArg Prod.fst (hraw.symm.trans hanchor)
  have hy := congrArg Prod.snd (hraw.symm.trans hanchor)
  simp only [verticalReflection,Prod.fst_add,Prod.snd_add,zero_mul,zero_sub] at hx hy
  rw [reflection_phase15_raw hP]
  ext <;> simp only [verticalReflection,Prod.fst_add,Prod.snd_add,zero_mul,zero_sub] <;>
    linarith

/-- The path reflection holds for every parameter, including phase junctions. -/
theorem gerver_path_reflection {P : GerverParams} (hP : P.IsSolution) (t : ℝ) :
    P.path (π/2-t)=verticalReflection P.κ₃.1 (P.path t) := by
  have hO := gs_ord hP
  have phase1 {u : ℝ} (hu : u ≤ P.φ) : P.path u=P.x₁ u :=
    gs_path_eq_phase hP (gs_piece₀ hu)
  have phase2 {u : ℝ} (hu : u∈Icc P.φ P.θ) : P.path u=P.x₂ u :=
    gs_path_eq_phase hP (gs_piece₁ hu.1 hu.2)
  have phase3 {u : ℝ} (hu : u∈Icc P.θ (π/2-P.θ)) : P.path u=P.x₃ u :=
    gs_path_eq_phase hP (gs_piece₂ hu.1 hu.2)
  have phase4 {u : ℝ} (hu : u∈Icc (π/2-P.θ) (π/2-P.φ)) : P.path u=P.x₄ u :=
    gs_path_eq_phase hP (gs_piece₃ hu.1 hu.2)
  have phase5 {u : ℝ} (hu : π/2-P.φ ≤ u) : P.path u=P.x₅ u :=
    gs_path_eq_phase hP (gs_piece₄ hu)
  rcases gs_cases (P := P) t with h | ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩ | h
  · rw [phase1 h,phase5 (by linarith),reflection_phase15 hP]
  · rw [phase2 ⟨ha.le,hb⟩,phase4 ⟨by linarith,by linarith⟩,reflection_phase24 hP]
  · rw [phase3 ⟨ha.le,hb⟩,phase3 ⟨by linarith,by linarith⟩,reflection_phase3 hP]
  · rw [phase4 ⟨ha.le,hb⟩,phase2 ⟨by linarith,by linarith⟩]
    have he := congrArg (verticalReflection P.κ₃.1) (reflection_phase24 hP (π/2-t))
    simpa only [show π/2-(π/2-t)=t by ring,verticalReflection_involutive] using he.symm
  · rw [phase5 h.le,phase1 (by linarith)]
    have he := congrArg (verticalReflection P.κ₃.1) (reflection_phase15 hP (π/2-t))
    simpa only [show π/2-(π/2-t)=t by ring,verticalReflection_involutive] using he.symm

/-- The two support values are read directly from the verified reference
inner-corner identity, avoiding a separate convention for the constructed gs_K. -/
theorem gerver_support_path_pair {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t∈Icc (0 : ℝ) (π/2)) :
    supp P.cap t=dot(P.path t)(uvec t)+1 ∧
    supp P.cap (t+π/2)=dot(P.path t)(vvec t)+1 := by
  have h := gm_innerCorner hP hbox ht
  have hd := cn_innerCorner_dot P.cap t
  rw [h] at hd
  exact ⟨by linarith [hd.1],by linarith [hd.2]⟩

/-- Exact upper support reflection of the reference cap. -/
theorem gerver_cap_reflection_support {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t∈Icc (0 : ℝ) π) :
    supp P.cap t=supp P.cap (π-t)+2*P.κ₃.1*cos t := by
  have firsthalf {u : ℝ} (hu : u∈Icc (0 : ℝ) (π/2)) :
      supp P.cap u=supp P.cap (π-u)+2*P.κ₃.1*cos u := by
    have h1 := (gerver_support_path_pair hP hbox hu).1
    have h2 := (gerver_support_path_pair hP hbox
      (t := π/2-u) ⟨by linarith [hu.2],by linarith [hu.1]⟩).2
    rw [gerver_path_reflection hP] at h2
    rw [show π/2-u+π/2=π-u by ring] at h2
    simp only [dot,uvec,vvec,verticalReflection,cos_pi_div_two_sub,sin_pi_div_two_sub] at h1 h2 ⊢
    linarith
  by_cases hv : t ≤ π/2
  · exact firsthalf ⟨ht.1,hv⟩
  · have h := firsthalf (u := π-t) ⟨by linarith [ht.2],by linarith⟩
    rw [show π-(π-t)=t by ring,cos_pi_sub] at h
    linarith

theorem gerver_midpoint_eq {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    horizontalMidpoint P.cap=P.κ₃.1 := by
  have h := gerver_cap_reflection_support hP hbox (t := 0) ⟨le_rfl,pi_pos.le⟩
  simp only [sub_zero,cos_zero,mul_one] at h
  unfold horizontalMidpoint
  linarith

/-- Symmetrizing the chosen perturbation preserves the same reflection axis. -/
theorem perturbedCap_reflection_support {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (F : HalfCapProfile P.φ) {τ : ℝ} (hτ : 0 ≤ τ) (hsmall : τ ≤ F.safeAmplitude)
    {t : ℝ} (ht : t∈Icc (0 : ℝ) π) :
    supp (perturbedCap hP hbox F τ hτ hsmall).1 t =
      supp (perturbedCap hP hbox F τ hτ hsmall).1 (π-t)+2*P.κ₃.1*cos t := by
  rw [perturbedCap_support hP hbox F τ hτ hsmall ht,
    perturbedCap_support hP hbox F τ hτ hsmall ⟨by linarith [ht.2],by linarith [ht.1]⟩,
    gerver_cap_reflection_support hP hbox ht]
  have hs : F.symmetricValue t=F.symmetricValue (π-t) := by
    unfold HalfCapProfile.symmetricValue
    split_ifs <;> first | (congr 1; ring) | (have he : t=π/2 := by linarith; subst t; congr 1 <;> ring)
  rw [hs]
  ring

end MovingSofaQuantitative
