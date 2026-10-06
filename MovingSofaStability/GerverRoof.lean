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
  have hB := romik_bounds hP hbox
  have henv := gn_envHyp hP hB
  have hc : IsCap P.cap (π / 2) := gm_isCap hP hbox
  have hI : InjCond1 P.cap := (theorem6_1_2 hP hbox).1
  have hheight : ∀ t ∈ Icc (0 : ℝ) (π / 2), (P.path t).2 < 1 :=
    fun t ht => path_snd_lt_one hP hB ht.1 ht.2
  have hΓc : IsCompact (gerverEnvelope P) := envelope_isCompact henv
  have hΓbounds : ∀ p ∈ gerverEnvelope P,
      p.1 ∈ Icc (gerverRoofLeft P) (gerverRoofRight P) ∧ p.2 ∈ Ico (0 : ℝ) 1 :=
    envelope_bounds_of_path_height henv hheight
  have hcover : ∀ x ∈ Icc (gerverRoofLeft P) (gerverRoofRight P),
      ∃ p ∈ gerverEnvelope P, p.1 = x := fun x hx => env_exists_curve_fst henv hx
  have hθ : P.θ < π / 4 := by linarith [henv.ht.2.2.1]
  obtain ⟨L, hL, hSlope⟩ := envelope_slope_bound henv hθ (by linarith)
  obtain ⟨γ, hgraph, hLip⟩ := exists_roof_function
    (fun p hp => (hΓbounds p hp).1) hcover hSlope
  have hDmem : envD P.path P.gs_β 0 ∈ gerverEnvelope P :=
    Or.inr ⟨0, ⟨le_rfl, (henv.ht.1.trans henv.ht.2.1).le⟩, rfl⟩
  have hBmem : envB P.path P.gs_α (π / 2) ∈ gerverEnvelope P :=
    Or.inl (Or.inl ⟨π / 2, ⟨by linarith [henv.ht.2.2.2.1, henv.ht.2.2.2.2], le_rfl⟩, rfl⟩)
  obtain ⟨pmax, hpmax, hmax⟩ := hΓc.exists_isMaxOn ⟨_, hDmem⟩ continuous_snd.continuousOn
  let H := pmax.2
  have hH : H < 1 := (hΓbounds pmax hpmax).2.2
  have hγmem : ∀ x ∈ Icc (gerverRoofLeft P) (gerverRoofRight P), (x, γ x) ∈ gerverEnvelope P :=
    fun x hx => (hgraph (x, γ x)).2 ⟨hx, rfl⟩
  have hγnonneg : ∀ x ∈ Icc (gerverRoofLeft P) (gerverRoofRight P), 0 ≤ γ x :=
    fun x hx => (hΓbounds (x, γ x) (hγmem x hx)).2.1
  have hγheight : ∀ x ∈ Icc (gerverRoofLeft P) (gerverRoofRight P), γ x ≤ H :=
    fun x hx => hmax (hγmem x hx)
  have hγa : γ (gerverRoofLeft P) = 0 := by
    have h := ((hgraph _).1 hDmem).2
    rw [henv.D_end] at h
    exact h.symm
  have hγb : γ (gerverRoofRight P) = 0 := by
    have h := ((hgraph _).1 hBmem).2
    rw [henv.B_end] at h
    exact h.symm
  obtain ⟨ho1, ho2, ho3⟩ := envelope_endpoint_order henv
  have hab : gerverRoofLeft P < gerverRoofRight P := ho1.trans (ho2.trans ho3)
  have ha : (gerverRoofLeft P, 1) ∈ P.cap := by
    rw [gerver_cap_explicit hP hbox]
    have h := gs_C_mem_K hP hB (τ := 0) le_rfl (by positivity)
    rwa [gerver_contactC_zero hP hB] at h
  have hb : (gerverRoofRight P, 1) ∈ P.cap := by
    rw [gerver_cap_explicit hP hbox]
    have h := gs_A_mem_K hP hB (τ := π / 2) (by positivity) le_rfl
    rwa [gerver_contactA_pi_div_two hP hB] at h
  have hn : niche P.cap (π / 2) =
      {p : Point | p.1 ∈ Icc (gerverRoofLeft P) (gerverRoofRight P) ∧
        0 ≤ p.2 ∧ p.2 < γ p.1} := by
    rw [gerver_niche_envelope hP hbox]
    ext p
    constructor
    · rintro ⟨hpy, q, hq, hqx, hpq⟩
      obtain ⟨hx, hy⟩ := (hgraph q).1 hq
      rw [hqx] at hx
      rw [hy, hqx] at hpq
      exact ⟨hx, hpy, hpq⟩
    · rintro ⟨hx, hpy, hy⟩
      exact ⟨hpy, (p.1, γ p.1), hγmem p.1 hx, rfl, hy⟩
  exact ⟨H, L, γ, hc, hab, (cap_top_strict_between_floor_endpoints hc hI ha).1,
    (cap_top_strict_between_floor_endpoints hc hI hb).2, hH, hL,
    hγnonneg, hγheight, hLip, hγa, hγb, cap_horizontal_rectangle hc hab ha hb, hn⟩

/-- The actual nonconvex Gerver sofa satisfies the uniform interior-ball condition. -/
theorem gerver_interiorBalls {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ κ r₀ : ℝ, 0 < κ ∧ 0 < r₀ ∧ HasInteriorBalls (gerverSofa P) κ r₀ := by
  obtain ⟨H, L, γ, hroof⟩ := gerver_roof_data hP hbox
  have h := hroof.interiorBalls
  rwa [gerver_shape_eq hP hbox] at h

end MovingSofaStability
