module

public import MovingSofaStability.UniformGeometryBounds

/-!
# Exposed faces with a varying normal

At a multiple-point reference face the conclusion is containment near the whole
face, not convergence to a selected endpoint. This is the form needed near the
top edge to control wedge feet uniformly.
-/

@[expose] public section
noncomputable section

open Real Set Metric
open scoped Pointwise
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- A strict property on one reference face persists as the body and normal vary. -/
theorem face_property_stable_in_angle {K₀ : Set Point} (h₀ : IsCap K₀ (π / 2))
    (t₀ : ℝ) (F : Point → ℝ) (hF : Continuous F)
    (hpositive : ∀ p ∈ edge K₀ t₀, 0 < F p) :
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧ δ ≤ 1 ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K K₀ →
        ∀ t ∈ Icc (0 : ℝ) π, |t - t₀| ≤ ρ → ∀ p ∈ edge K t, 0 < F p := by
  classical
  let B := K₀ + euclideanDisk 1
  have hB := convexBody_add h₀.2.1 (euclideanDisk_isConvexBody (by norm_num : (0 : ℝ) ≤ 1))
  have hK₀B : K₀ ⊆ B := by
    intro p hp
    exact ⟨p, hp, 0, by simp [euclideanDisk], by simp⟩
  obtain ⟨R', hR'⟩ := hB.2.1.exists_bound_of_continuousOn continuous_norm2.continuousOn
  let R := max 1 R'
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR0 : 0 ≤ R := by linarith
  have hR : ∀ p ∈ B, norm2 p ≤ R := by
    intro p hp
    have h := hR' p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (norm2_nonneg p)] at h
    exact h.trans (le_max_right _ _)
  let defect : Point → ℝ := fun p => Metric.infDist p K₀ + |dot p (uvec t₀) - supp K₀ t₀|
  have hdef : Continuous defect :=
    (Metric.continuous_infDist_pt K₀).add ((continuous_dot _).sub continuous_const).abs
  let bad : Set Point := B ∩ {p | F p ≤ 0}
  have hbad : IsCompact bad := hB.2.1.inter_right (isClosed_le hF continuous_const)
  have hdpos : ∀ p ∈ bad, 0 < defect p := by
    intro p hp
    by_contra hnot
    have hi0 : Metric.infDist p K₀ = 0 := by
      have hi := Metric.infDist_nonneg (x := p) (s := K₀)
      have ha := abs_nonneg (dot p (uvec t₀) - supp K₀ t₀)
      change ¬0 < Metric.infDist p K₀ + |dot p (uvec t₀) - supp K₀ t₀| at hnot
      linarith
    have hg0 : dot p (uvec t₀) = supp K₀ t₀ := by
      change ¬0 < Metric.infDist p K₀ + |dot p (uvec t₀) - supp K₀ t₀| at hnot
      rw [hi0, zero_add] at hnot
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (not_lt.mp hnot) (abs_nonneg _)))
    have hm : p ∈ K₀ := (h₀.2.1.2.1.isClosed.mem_iff_infDist_zero h₀.2.1.1).2 hi0
    exact (not_lt_of_ge hp.2) (hpositive p ⟨hm, hg0⟩)
  obtain ⟨m, hm, hmle⟩ := hbad.exists_forall_le' hdef.continuousOn hdpos
  let δ := min 1 (m / 8)
  let ρ := m / (16 * (R + 1))
  have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδm : δ ≤ m / 8 := min_le_right _ _
  have hρeq : 16 * (R + 1) * ρ = m := by
    dsimp [ρ]
    field_simp
  refine ⟨δ, ρ, hδ, hρ, hδ1, ?_⟩
  intro K hK hclose t ht htρ p hp
  have hpB := cap_subset_unit_parallel hK h₀ hδ1 hclose hp.1
  by_contra hnot
  have hbadp : p ∈ bad := ⟨hpB, not_lt.mp hnot⟩
  have hlower := hmle p hbadp
  obtain ⟨q, hq, hdq⟩ := (upperSupportClose_euclidean hδ.le hK h₀ hclose).1 p hp.1
  have hid : Metric.infDist p K₀ ≤ δ := by
    have hprod : dist p q ≤ euclideanDist p q := by
      rw [dist_eq_norm]
      exact product_norm_le_norm2 (p - q)
    exact (Metric.infDist_le_dist_of_mem hq).trans (hprod.trans hdq)
  have hsupport := hclose t ht
  have hangle := support_angle_bound h₀.2.1 hR0 (fun p hp => hR p (hK₀B hp)) t t₀
  have hdot : |dot p (uvec t₀) - dot p (uvec t)| ≤ 2 * R * |t - t₀| := by
    rw [← dot_sub_right]
    have h := (abs_dot_le_norm2_mul p (uvec t₀ - uvec t)).trans
      (mul_le_mul (hR p hpB) (norm2_uvec_sub_le t₀ t) (norm2_nonneg _) hR0)
    rw [abs_sub_comm t₀ t] at h
    nlinarith
  have hgap : |dot p (uvec t₀) - supp K₀ t₀| ≤ δ + 4 * R * |t - t₀| := by
    have he : dot p (uvec t₀) - supp K₀ t₀ =
        (dot p (uvec t₀) - dot p (uvec t)) + (supp K t - supp K₀ t) +
          (supp K₀ t - supp K₀ t₀) := by rw [hp.2]; ring
    rw [he]
    have h1 := abs_add_le (dot p (uvec t₀) - dot p (uvec t)) (supp K t - supp K₀ t)
    have h2 := abs_add_le ((dot p (uvec t₀) - dot p (uvec t)) + (supp K t - supp K₀ t))
      (supp K₀ t - supp K₀ t₀)
    linarith
  change m ≤ Metric.infDist p K₀ + |dot p (uvec t₀) - supp K₀ t₀| at hlower
  have hmul := mul_le_mul_of_nonneg_left htρ (show 0 ≤ 4 * R by positivity)
  nlinarith

/-- Gerver's full top face lies between its two contact endpoints. -/
theorem gerver_top_face_bounds {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {p : Point} (hp : p ∈ edge P.cap (π / 2)) :
    gerverRoofLeft P ≤ p.1 ∧ p.1 ≤ gerverRoofRight P := by
  have hcb := GerverParams.gm_isConvexBody_cap hP hbox
  have ha : vminus P.cap (π / 2) = (gerverRoofRight P, 1) := by
    have he := ((theorem8_4_1_monotone hP hbox).2 (π / 2) ⟨by positivity, le_rfl⟩).1
    exact he.trans (gerver_contactA_pi_div_two hP (GerverParams.romik_bounds hP hbox))
  have hc : vplus P.cap (π / 2) = (gerverRoofLeft P, 1) := by
    have he := ((theorem8_4_1_monotone hP hbox).2 0 ⟨le_rfl, by positivity⟩).2.1
    simpa only [cK, cPlus, zero_add, gerverRoofLeft] using
      he.trans (gerver_contactC_zero hP (GerverParams.romik_bounds hP hbox))
  have h1 := dot_vminus_le_dot hcb.2.1 hp
  have h2 := dot_le_dot_vplus hcb.2.1 hp
  rw [ha] at h1
  rw [hc] at h2
  simp only [dot, vvec_pi_div_two] at h1 h2
  constructor <;> linarith

/-- Uniformly control all nearby top contacts, including the ends of vertical or oblique faces. -/
theorem gerver_near_top_contacts {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧ δ ≤ 1 ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K P.cap →
        ∀ t ∈ Icc (0 : ℝ) π, |t - π / 2| ≤ ρ → ∀ p ∈ edge K t,
          gerverRoofLeft P - η < p.1 ∧ p.1 < gerverRoofRight P + η := by
  let F : Point → ℝ := fun p => min (p.1 - (gerverRoofLeft P - η))
    (gerverRoofRight P + η - p.1)
  have hF : Continuous F :=
    (continuous_fst.sub continuous_const).min (continuous_const.sub continuous_fst)
  obtain ⟨δ, ρ, hδ, hρ, hδ1, h⟩ := face_property_stable_in_angle (GerverParams.gm_isCap hP hbox)
    (π / 2) F hF (by
      intro p hp
      obtain ⟨hl, hr⟩ := gerver_top_face_bounds hP hbox hp
      exact lt_min (by linarith) (by linarith))
  refine ⟨δ, ρ, hδ, hρ, hδ1, ?_⟩
  intro K hK hclose t ht hnear p hp
  have hh := h K hK hclose t ht hnear p hp
  have hmin := lt_min_iff.mp hh
  constructor <;> linarith

end MovingSofaStability
