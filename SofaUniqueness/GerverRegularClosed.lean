module

public import MovingSofa.Gerver.Properties
public import SofaUniqueness.GerverStrictHeight
public import SofaUniqueness.EnvelopeBounds
public import SofaUniqueness.RegularClosedEnvelope

/-!
# Gerver's sofa is the closure of its interior

This specializes the compact-envelope recovery lemma to the actual Gerver
sofa already defined in the paper library. Both top endpoints are contact
points of the cap, and convexity plus downward closure supplies the intervening
rectangle. The existing phase enclosures give strict height below one, so no
exceptional top contact or inverse graph parameterization is needed.

This discharges the draft's P6 obligation with an explicit script. It uses no
assumption about the boundary regularity of a competing sofa. It is uncompiled
and has no admitted statements.
-/

@[expose] public section
noncomputable section

open Real Set MovingSofa MovingSofa.GerverParams

namespace SofaUniqueness

/-- The concrete library Gerver sofa is regular closed. -/
theorem gerver_regularClosed {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    closure (interior (gerverSofa P)) = gerverSofa P := by
  have hB := GerverParams.romik_bounds hP hbox
  have henv := gn_envHyp hP hB
  let Γ := envCurve P.φ P.θ (π / 2 - P.θ) (π / 2 - P.φ)
    P.path P.gs_α P.gs_β
  let a := (envD P.path P.gs_β 0).1
  let b := (envB P.path P.gs_α (π / 2)).1
  have hheight : ∀ t ∈ Icc (0 : ℝ) (π / 2), (P.path t).2 < 1 :=
    fun t ht => path_snd_lt_one hP hB ht.1 ht.2
  have hΓc : IsCompact Γ := envelope_isCompact henv
  have hΓbounds : ∀ p ∈ Γ, p.1 ∈ Icc a b ∧ p.2 ∈ Ico (0 : ℝ) 1 :=
    envelope_bounds_of_path_height henv hheight
  obtain ⟨ho1, ho2, ho3⟩ := envelope_endpoint_order henv
  have hab : a < b := ho1.trans (ho2.trans ho3)
  have hcap : IsCap P.gs_K (π / 2) := gs_isCap_K hP hB
  have hconv : Convex ℝ P.gs_K := gs_convex_K
  have hleft : (a, 1) ∈ P.gs_K := by
    have hmem := gs_C_mem_K hP hB (τ := 0) le_rfl (by positivity)
    have he : contactC P.path 0 = (a, 1) := by
      change envD P.path P.gs_β 0 + vvec 0 = (a, 1)
      apply Prod.ext
      · simp [a, vvec]
      · simp [vvec, henv.D_end]
    rwa [he] at hmem
  have hright : (b, 1) ∈ P.gs_K := by
    have hmem := gs_A_mem_K hP hB (τ := π / 2) (by positivity) le_rfl
    have he : contactA P.path (π / 2) = (b, 1) := by
      change envB P.path P.gs_α (π / 2) + uvec (π / 2) = (b, 1)
      apply Prod.ext
      · simp [b, uvec]
      · simp [uvec, henv.B_end]
    rwa [he] at hmem
  have hrect : ∀ x ∈ Icc a b, ∀ y ∈ Icc (0 : ℝ) 1, (x, y) ∈ P.gs_K := by
    intro x hx y hy
    let c := (x - a) / (b - a)
    have hba : 0 < b - a := sub_pos.mpr hab
    have hc : c ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (sub_nonneg.mpr hx.1) hba.le,
        (div_le_one hba).mpr (by linarith [hx.2])⟩
    have htop := hconv.add_smul_sub_mem hleft hright hc
    have he : (a, (1 : ℝ)) + c • ((b, 1) - (a, 1)) = (x, 1) := by
      apply Prod.ext
      · dsimp [c]
        field_simp
        <;> ring
      · simp
    rw [he] at htop
    exact opt_cap_down hcap htop hy.1 hy.2
  have hKreg : closure (interior P.gs_K) = P.gs_K := by
    have hsub : Ioo a b ×ˢ Ioo (0 : ℝ) 1 ⊆ P.gs_K := by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      exact hrect x ⟨hx.1.le, hx.2.le⟩ y ⟨hy.1.le, hy.2.le⟩
    have hint := interior_maximal hsub (isOpen_Ioo.prod isOpen_Ioo)
    have hne : (interior P.gs_K).Nonempty := by
      refine ⟨((a + b) / 2, 1 / 2), hint ?_⟩
      constructor <;> constructor <;> dsimp <;> linarith
    calc
      closure (interior P.gs_K) = closure P.gs_K :=
        hconv.closure_interior_eq_closure_of_nonempty_interior hne
      _ = P.gs_K := gs_isClosed_K.closure_eq
  have hn : niche P.gs_K (π / 2) = envUnderStrict Γ := by
    calc
      niche P.gs_K (π / 2) = niche (capOf (gerverSofa P) (π / 2)) (π / 2) := by
        rw [(gs_monotone_K hP hB).2]
      _ = envNiche P.path := gn_niche_eq hP hB
      _ = envUnderStrict Γ := env_niche_eq henv
  have hG : gerverSofa P = P.gs_K \ envUnderStrict Γ := by
    rw [gs_gerverSofa_eq hP hB, hn]
  have hclosed : IsClosed (P.gs_K \ envUnderStrict Γ) := by
    rw [← hG]
    exact (gm_movingSofa_std hP hbox).1.1
  have hfinal := regularClosed_cap_sdiff_envelope hab hKreg
    (fun p hp => (gs_K_bounds hP hp).2.2) hrect hΓc
    (fun p hp => ⟨(hΓbounds p hp).1,
      (hΓbounds p hp).2.1, (hΓbounds p hp).2.2.le⟩)
    (fun p hp q hq hpone hqone => False.elim ((hΓbounds p hp).2.2.ne hpone))
    hclosed
  simpa only [← hG] using hfinal

end SofaUniqueness
