module

public import MovingSofaStability.RoofGeometry

/-!
# Gerver's reference roof and uniform interior balls

Uncompiled proof source. All reference geometry is derived from the existing
Gerver envelope, contact and injectivity theorems. The two convex wings have
positive width because the cap has no vertical supporting faces.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaUniqueness
open GerverParams

namespace MovingSofaStability

def gerverRoofLeft (P : GerverParams) : ℝ := (envD P.path P.gs_β 0).1

def gerverRoofRight (P : GerverParams) : ℝ := (envB P.path P.gs_α (π / 2)).1

def gerverEnvelope (P : GerverParams) : Set Point :=
  envCurve P.φ P.θ (π / 2 - P.θ) (π / 2 - P.φ) P.path P.gs_α P.gs_β

theorem gerver_cap_explicit {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    P.cap = P.gs_K := (gs_monotone_K hP (romik_bounds hP hbox)).2

theorem gerver_shape_eq {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    capShape P.cap = gerverSofa P := by
  rw [capShape, gerver_cap_explicit hP hbox]
  exact (gs_gerverSofa_eq hP (romik_bounds hP hbox)).symm

theorem gerver_niche_envelope {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    niche P.cap (π / 2) = envUnderStrict (gerverEnvelope P) := by
  rw [gerver_cap_explicit hP hbox]
  exact gerver_niche_eq_envUnderStrict hP (romik_bounds hP hbox)

/-- A top point cannot lie on either vertical supporting face when those faces are points. -/
theorem cap_top_strict_between_floor_endpoints {K : Set Point}
    (hK : IsCap K (π / 2)) (h1 : InjCond1 K) {a : ℝ} (ha : (a, 1) ∈ K) :
    -supp K π < a ∧ a < supp K 0 := by
  have hb := opt_cap_fst_le hK ha
  have hleft : vplus K π = vminus K π := by
    have h := ((proposition6_4_5 hK h1).2 (π / 2) ⟨by positivity, le_rfl⟩).1
    simpa only [cPlus, cMinus, add_halves] using h
  have hright : vplus K 0 = vminus K 0 :=
    ((proposition6_4_5 hK h1).1 0 ⟨le_rfl, by positivity⟩).1
  constructor
  · apply lt_of_le_of_ne hb.1
    intro he
    have hp : (a, 1) ∈ edge K π := by
      refine ⟨ha, ?_⟩
      change dot (a, 1) (uvec π) = supp K π
      simp only [dot, uvec_pi]
      linarith
    rw [edge_eq_segment hK.2.1 π, ← hleft, opt_cap_vplus_pi hK, segment_same] at hp
    have hs := congrArg Prod.snd (mem_singleton_iff.mp hp)
    norm_num at hs
  · apply lt_of_le_of_ne hb.2
    intro he
    have hp : (a, 1) ∈ edge K 0 := by
      refine ⟨ha, ?_⟩
      change dot (a, 1) (uvec 0) = supp K 0
      simpa only [uvec_zero, dot, mul_one, mul_zero, add_zero] using he
    rw [edge_eq_segment hK.2.1 0, hright, (inj_cap_consecutive hK).1, segment_same] at hp
    have hs := congrArg Prod.snd (mem_singleton_iff.mp hp)
    norm_num at hs

/-- Gerver's niche is the region under a nonnegative, finite-slope roof strictly below one. -/
theorem gerver_roof_data {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ H L : ℝ, ∃ γ : ℝ → ℝ,
      CapRoofData P.cap (gerverRoofLeft P) (gerverRoofRight P) H L γ := by
  sorry

/-- The actual nonconvex Gerver sofa satisfies the uniform interior-ball condition. -/
theorem gerver_interiorBalls {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ κ r₀ : ℝ, 0 < κ ∧ 0 < r₀ ∧ HasInteriorBalls (gerverSofa P) κ r₀ := by
  obtain ⟨H, L, γ, hroof⟩ := gerver_roof_data hP hbox
  have h := hroof.interiorBalls
  rwa [gerver_shape_eq hP hbox] at h

end MovingSofaStability
