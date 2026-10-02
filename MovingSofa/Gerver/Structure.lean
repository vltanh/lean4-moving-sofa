module

public import MovingSofa.Gerver.Bounds
public import MovingSofa.Gerver.Frame
public import MovingSofa.Gerver.StructureCap
public import MovingSofa.Monotone.CapContainsNiche
public import MovingSofa.Injectivity.ArmLengths

/-!
# The structure of Gerver's sofa

The paper states the structure of Gerver's sofa (Theorem 8.4.1) without proof, and imports Romik's
balancing ODEs (Theorem 8.4.2). This file verifies, for every solution `P` of Romik's system satisfying
the enclosures `P.Bounds`, the parts of Theorem 8.4.1 that do not concern the niche, Theorem 8.4.2
and Theorem 6.1.2.

Method (see `notes/gerver_plan.md`): in the rotating frame of each phase the curves `𝐀, 𝐁, 𝐂, 𝐃` and
the derivatives of the rotation path are explicit; the cap of `G` is the explicit convex body
`{p_y ≥ 0} ∩ ⋂_{σ ∈ [0, π]} H₋(σ, H(σ))`, and Theorems 2.5.8–2.5.9 identify `G` with the monotone sofa
of that cap.
-/

@[expose] public section

open Real Set MeasureTheory

namespace MovingSofa

namespace GerverParams

variable {P : GerverParams}

/-- Theorem 8.4.1 (monotone, (1)) under the enclosures. -/
theorem gv_monotone (hP : P.IsSolution) (hB : P.Bounds) :
    IsMonotoneSofa (gerverSofa P) (π / 2) ∧
      ∀ t ∈ Icc 0 (π / 2), aMinus (capOf (gerverSofa P) (π / 2)) t = contactA P.path t ∧
        cPlus (capOf (gerverSofa P) (π / 2)) t = contactC P.path t ∧
        innerCorner (capOf (gerverSofa P) (π / 2)) t = P.path t := by
  obtain ⟨hmono, hcap⟩ := gs_monotone_K hP hB
  refine ⟨hmono, fun t ht => ?_⟩
  rw [hcap]
  exact ⟨gs_vminus_K hP hB ht.1 ht.2, gs_vplus_K' hP hB ht.1 ht.2,
    gs_innerCorner_K hP hB ht.1 ht.2⟩

/-- Theorem 8.4.1 (3) under the enclosures. -/
theorem gv_walls (hP : P.IsSolution) (hB : P.Bounds) :
    (∀ t ∈ Icc (π / 2 - P.θ) (π / 2), contactB P.path t ∈ wallBVec (capOf (gerverSofa P) (π / 2)) t) ∧
      ∀ t ∈ Icc 0 P.θ, contactD P.path t ∈ wallDVec (capOf (gerverSofa P) (π / 2)) t := by
  have hO := gs_ord hP
  rw [(gs_monotone_K hP hB).2]
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have h0 : 0 ≤ t := by linarith [ht.1, hO.2.2, pi_pos]
    rw [wallBVec, ms_mem_hallwayMap_image, (gs_supp_K_eq hP hB h0 ht.2).1,
      (gs_supp_K_eq hP hB h0 ht.2).2, gs_contactB_eq']
    simp only [bVecL, mem_ofPred_eq, dot_add_left, dot_smul_left, dot_vvec_uvec, dot_vvec_self]
    exact ⟨by ring, by linarith [gs_α_nonpos hP hB h0 ht.2]⟩
  · have h1 : t ≤ π / 2 := by linarith [ht.2, hO.2.2, pi_pos]
    rw [wallDVec, ms_mem_hallwayMap_image, (gs_supp_K_eq hP hB ht.1 h1).1,
      (gs_supp_K_eq hP hB ht.1 h1).2, gs_contactD_eq']
    simp only [dVecL, mem_ofPred_eq, dot_sub_left, dot_smul_left, dot_uvec_vvec, dot_uvec_self]
    exact ⟨by ring, by linarith [gs_β_nonneg hP hB ht.1 h1]⟩

/-- Theorem 8.4.1 (4) under the enclosures. -/
theorem gv_tangents (hP : P.IsSolution) (hB : P.Bounds) :
    (∀ t ∈ Ioo (π / 2 - P.θ) (π / 2), t ≠ π / 2 - P.φ →
        ∃ c < (0 : ℝ), HasDerivAt (contactB P.path) (c • vvec t) t) ∧
      ∀ t ∈ Ioo 0 P.θ, t ≠ P.φ → ∃ c > (0 : ℝ), HasDerivAt (contactD P.path) (c • uvec t) t := by
  have hO := gs_ord hP
  refine ⟨fun t ht hne => ?_, fun t ht hne => ?_⟩
  · rcases hne.lt_or_gt with h | h
    · have ho : gs_opiece P 3 t := ⟨ht.1, h⟩
      refine ⟨(P.gs_phase 3).ρA t - 1, ?_, gs_hasDerivAt_contactB hP ho⟩
      rw [show t = π / 2 - (π / 2 - t) by ring, gs_ρA₄_eq hP]
      have := (gs_ineq_ρC₂ hB (s := π / 2 - t) (by linarith [hO.1]) (by linarith [ht.1])).2
      linarith
    · have ho : gs_opiece P 4 t := h
      refine ⟨(P.gs_phase 4).ρA t - 1, ?_, gs_hasDerivAt_contactB hP ho⟩
      rw [gs_ρA₅_eq]; norm_num
  · rcases hne.lt_or_gt with h | h
    · have ho : gs_opiece P 0 t := h
      refine ⟨1 - (P.gs_phase 0).ρC t, ?_, gs_hasDerivAt_contactD hP ho⟩
      rw [gs_ρC₁_eq]; norm_num
    · have ho : gs_opiece P 1 t := ⟨h, ht.2⟩
      refine ⟨1 - (P.gs_phase 1).ρC t, ?_, gs_hasDerivAt_contactD hP ho⟩
      rw [gs_ρC₂_eq]
      have := (gs_ineq_ρC₂ hB (s := t) ht.1.le ht.2.le).2
      linarith

/-- Theorem 8.4.2 (Romik's ODEs) under the enclosures. -/
theorem gv_odes (hP : P.IsSolution) (hB : P.Bounds) :
    (∀ t ∈ Ioo 0 P.φ,
        dot (deriv (contactA P.path) t) (vvec t) = 0 ∧
        dot (-deriv (contactC P.path) t) (uvec t) = dot (deriv (contactD P.path) t) (uvec t)) ∧
      (∀ t ∈ Ioo P.φ P.θ,
        dot (deriv (contactA P.path) t) (vvec t) = dot (deriv P.path t) (vvec t) ∧
        dot (-deriv (contactC P.path) t) (uvec t) =
          dot (deriv (contactD P.path) t - deriv P.path t) (uvec t)) ∧
      (∀ t ∈ Ioo P.θ (π / 2 - P.θ),
        dot (deriv (contactA P.path) t) (vvec t) = dot (deriv P.path t) (vvec t) ∧
        dot (-deriv (contactC P.path) t) (uvec t) = dot (-deriv P.path t) (uvec t)) ∧
      (∀ t ∈ Ioo (π / 2 - P.θ) (π / 2 - P.φ),
        dot (deriv (contactA P.path) t) (vvec t) =
          dot (-deriv (contactB P.path) t + deriv P.path t) (vvec t) ∧
        dot (-deriv (contactC P.path) t) (uvec t) = dot (-deriv P.path t) (uvec t)) ∧
      (∀ t ∈ Ioo (π / 2 - P.φ) (π / 2),
        dot (deriv (contactA P.path) t) (vvec t) = dot (-deriv (contactB P.path) t) (vvec t) ∧
        dot (-deriv (contactC P.path) t) (uvec t) = 0) := by
  have _ := hB
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · have ho : gs_opiece P 0 t := ht.2
    rw [(gs_hasDerivAt_contactA hP ho).deriv, (gs_hasDerivAt_contactC hP ho).deriv,
      (gs_hasDerivAt_contactD hP ho).deriv]
    simp only [dot_neg_left, gs_dot_smul_vvec_vvec, gs_dot_smul_uvec_uvec, gs_ρA₁_eq, gs_ρC₁_eq]
    norm_num
  · have ho : gs_opiece P 1 t := ht
    rw [(gs_hasDerivAt_contactA hP ho).deriv, (gs_hasDerivAt_contactC hP ho).deriv,
      (gs_hasDerivAt_contactD hP ho).deriv, gs_deriv_path_eq hP (gs_piece_of_opiece ho)]
    simp only [dot_neg_left, dot_sub_left, dot_add_left, dot_smul_left, dot_uvec_self,
      dot_vvec_self, dot_uvec_vvec, dot_vvec_uvec, gs_ρA₂_eq, gs_ρC₂_eq, gs_α₂_eq, gs_β₂_eq]
    constructor <;> ring
  · have ho : gs_opiece P 2 t := ht
    rw [(gs_hasDerivAt_contactA hP ho).deriv, (gs_hasDerivAt_contactC hP ho).deriv,
      gs_deriv_path_eq hP (gs_piece_of_opiece ho)]
    simp only [dot_neg_left, dot_add_left, dot_smul_left, dot_uvec_self, dot_vvec_self,
      dot_uvec_vvec, dot_vvec_uvec, gs_ρA₃_eq, gs_ρC₃_eq hP, gs_α₃_eq hP, gs_β₃_eq]
    constructor <;> ring
  · have ho : gs_opiece P 3 t := ht
    rw [(gs_hasDerivAt_contactA hP ho).deriv, (gs_hasDerivAt_contactC hP ho).deriv,
      (gs_hasDerivAt_contactB hP ho).deriv, gs_deriv_path_eq hP (gs_piece_of_opiece ho)]
    simp only [dot_neg_left, dot_add_left, dot_smul_left, dot_uvec_self, dot_vvec_self,
      dot_uvec_vvec, dot_vvec_uvec]
    rw [show t = π / 2 - (π / 2 - t) by ring, gs_ρA₄_eq hP, gs_ρC₄_eq hP, gs_α₄_eq hP,
      gs_β₄_eq hP]
    constructor <;> ring
  · have ho : gs_opiece P 4 t := ht.1
    rw [(gs_hasDerivAt_contactA hP ho).deriv, (gs_hasDerivAt_contactC hP ho).deriv,
      (gs_hasDerivAt_contactB hP ho).deriv]
    simp only [dot_neg_left, gs_dot_smul_vvec_vvec, gs_dot_smul_uvec_uvec, gs_ρA₅_eq, gs_ρC₅_eq]
    norm_num

/-- Theorem 6.1.2 under the enclosures: the cap of Gerver's sofa satisfies the injectivity
condition. -/
theorem gv_injectivity (hP : P.IsSolution) (hB : P.Bounds) :
    SatisfiesInjectivity (capOf (gerverSofa P) (π / 2)) := by
  rw [(gs_monotone_K hP hB).2]
  exact ⟨gs_InjCond1 hP hB, gs_InjCond2 hP hB, gs_InjCond3 hP hB⟩

end GerverParams

end MovingSofa
