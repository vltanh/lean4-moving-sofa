module

public import MovingSofaQuantitative.Normalization
public import MovingSofaStability.Global

/-!
# Midpoint normalization and qualitative entry

UNCOMPILED SOURCE.  The integrated stability proof uses a left/top pin for its
compactness argument.  Quantitative stability uses horizontal midpoint/top
alignment.  This file transfers the already-proved qualitative entry theorem
between the two translations; no new compactness theorem is needed.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability

namespace MovingSofaQuantitative

theorem horizontalMidpoint_translate {S : Set Point} (hS : IsCompact S)
    (hne : S.Nonempty) (v : Point) :
    horizontalMidpoint (Rigid.translate v '' S)=horizontalMidpoint S+v.1 := by
  unfold horizontalMidpoint
  rw [Rigid.coe_translate,
    supp_translate S v 0 hS hne,
    supp_translate S v π hS hne]
  simp only [dot,uvec_zero,uvec_pi,Prod.fst_add,Prod.snd_add]
  ring

theorem midpointNormalizedSofa_top (P : GerverParams) {S : Set Point}
    (hS : IsCompact S) (hne : S.Nonempty) :
    supp (midpointNormalizedSofa P S) (π/2)=1 := by
  rw [midpointNormalizedSofa,Rigid.coe_translate,
    supp_translate S _ _ hS hne,dot_uvec_pi_div_two]
  simp

theorem midpointNormalizedSofa_midpoint (P : GerverParams) {S : Set Point}
    (hS : IsCompact S) (hne : S.Nonempty) :
    horizontalMidpoint (midpointNormalizedSofa P S)=
      horizontalMidpoint (gerverSofa P) := by
  rw [midpointNormalizedSofa,horizontalMidpoint_translate hS hne]
  simp
  ring

theorem midpointNormalizedSofa_movingWithAngle (P : GerverParams)
    {S : Set Point} {ω : ℝ} (hS : IsMovingSofaWithAngle S ω) :
    IsMovingSofaWithAngle (midpointNormalizedSofa P S) ω := by
  simpa only [midpointNormalizedSofa,Rigid.coe_translate] using
    mpc_isMovingSofaWithAngle_translate hS
      (horizontalMidpoint (gerverSofa P)-horizontalMidpoint S,
        1-supp S (π/2))

theorem midpointNormalizedSofa_moving (P : GerverParams)
    {S : Set Point} (hS : IsMovingSofa S) :
    IsMovingSofa (midpointNormalizedSofa P S) :=
  ⟨hS.choose,midpointNormalizedSofa_movingWithAngle P hS.choose_spec⟩

/-- Translation by a horizontal amount a moves every point exactly |a|. -/
theorem close_horizontal_translate (S : Set Point) (a : ℝ) :
    EuclideanClose |a| (Rigid.translate (a,0) '' S) S := by
  constructor
  · rintro p ⟨q,hq,rfl⟩
    refine ⟨q,hq,?_⟩
    simp [euclideanDist,Rigid.translate_apply,norm2,dot]
  · intro p hp
    refine ⟨p+(a,0),⟨p,hp,by simp [Rigid.translate_apply]⟩,?_⟩
    simp [euclideanDist,norm2,dot]

/-- Closeness controls the horizontal midpoint by the same radius. -/
theorem horizontalMidpoint_error {S T : Set Point} {r : ℝ}
    (hS : IsCompact S) (hT : IsCompact T)
    (hneS : S.Nonempty) (hneT : T.Nonempty)
    (h : EuclideanClose r S T) :
    |horizontalMidpoint S-horizontalMidpoint T|≤r := by
  have h0 := h.abs_supp_sub_le hS hT hneS hneT 0
  have hπ := h.abs_supp_sub_le hS hT hneS hneT π
  unfold horizontalMidpoint
  have hs := abs_sub_le (supp S 0-supp T 0) (supp S π-supp T π)
  nlinarith [h0,hπ]

/-- The two normalizations differ only by the horizontal midpoint error of the
left-pinned normalization. -/
theorem midpoint_eq_translate_normalized {P : GerverParams} {S : Set Point}
    (hS : IsCompact S) (hne : S.Nonempty) :
    midpointNormalizedSofa P S =
      Rigid.translate
        (horizontalMidpoint (gerverSofa P)-
          horizontalMidpoint (normalizedSofa P S),0) ''
        normalizedSofa P S := by
  ext p
  simp only [midpointNormalizedSofa,normalizedSofa,Rigid.mem_translate_image,
    Rigid.translate_apply,normalizingShift]
  constructor <;> rintro ⟨q,hq,rfl⟩
  · refine ⟨q+(normalizingShift P S),⟨q,hq,rfl⟩,?_⟩
    have hm := horizontalMidpoint_translate hS hne (normalizingShift P S)
    rw [hm]
    simp [normalizingShift,horizontalMidpoint]
    ext <;> ring
  · obtain ⟨q,hq,rfl⟩ := ‹_∈normalizedSofa P S›
    refine ⟨q,hq,?_⟩
    have hm := horizontalMidpoint_translate hS hne (normalizingShift P S)
    rw [hm]
    simp [normalizingShift,horizontalMidpoint]
    ext <;> ring

/-- Pinned qualitative entry implies midpoint qualitative entry. -/
theorem midpoint_entry_of_pinned {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {S : Set Point} (hS : IsMovingSofa S) {r : ℝ}
    (hr : 0≤r)
    (hclose : EuclideanClose r (normalizedSofa P S) (gerverSofa P)) :
    EuclideanClose (2*r) (midpointNormalizedSofa P S) (gerverSofa P) := by
  have hc := isCompact_of_isMovingSofa hS
  have hn := hS.choose_spec.2.1.nonempty
  have hNc := ms_isCompact_of_isMovingSofaWithAngle
    (normalizedSofa_movingWithAngle P hS.choose_spec)
  have hNn := (normalizedSofa_movingWithAngle P hS.choose_spec).2.1.nonempty
  have hGc := ms_isCompact_of_isMovingSofaWithAngle
    (GerverParams.gm_movingSofa_std hP hbox).1
  have hGn := (GerverParams.gm_movingSofa_std hP hbox).1.2.1.nonempty
  let a := horizontalMidpoint (gerverSofa P)-
    horizontalMidpoint (normalizedSofa P S)
  have ha : |a|≤r := by
    dsimp [a]
    simpa [abs_sub_comm] using
      horizontalMidpoint_error hNc hGc hNn hGn hclose
  rw [midpoint_eq_translate_normalized hc hn]
  exact (close_horizontal_translate (normalizedSofa P S) a).trans hclose |>.mono
    (by nlinarith [abs_nonneg a,ha])

/-- Qualitative entry in the normalization used by the quantitative theorem. -/
theorem near_maximizers_enter_midpoint_neighborhood {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {ρ α₀ : ℝ}
    (hρ : 0<ρ) (hα₀ : 0<α₀) :
    ∃ ε₀ : ℝ,0<ε₀ ∧ ∀S ω,
      IsMovingSofaWithAngle S ω →
      ω∈Icc (arccos (5/11)) (π/2) →
      sofaDeficit P S<ε₀ →
      EuclideanClose ρ (midpointNormalizedSofa P S) (gerverSofa P) ∧
      π/2-ω<α₀ := by
  obtain ⟨ε₀,hε₀,hentry⟩ :=
    near_maximizers_enter_neighborhood hP hbox (show 0<ρ/2 by positivity) hα₀
  refine ⟨ε₀,hε₀,?_⟩
  intro S ω hS hω hε
  obtain ⟨hc,ha⟩ := hentry S ω hS hω hε
  exact ⟨(midpoint_entry_of_pinned hP hbox ⟨ω,hS⟩ (by positivity) hc).mono
    (by ring_nf; exact le_rfl),ha⟩

end MovingSofaQuantitative
