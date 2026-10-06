module

public import MovingSofaStability.AngularFaceStability

/-!
# Feet of forbidden wedges and horizontal niche localization

Uncompiled proof source. The potentially small sine/cosine denominators at
the endpoint angles are controlled by nearby top contacts, not by dividing a
uniform support error by a quantity tending to zero.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaUniqueness
open GerverParams

namespace MovingSofaStability

def wedgeRightFoot (K : Set Point) (t : ℝ) : ℝ := (supp K t - 1) / cos t

def wedgeLeftFoot (K : Set Point) (t : ℝ) : ℝ := (1 - supp K (t + π / 2)) / sin t

theorem wedge_floor_slacks (K : Set Point) {t x : ℝ}
    (hs : sin t ≠ 0) (hc : cos t ≠ 0) :
    innerSlackU K t (x, 0) = cos t * (x - wedgeRightFoot K t) ∧
      innerSlackV K t (x, 0) = -sin t * (x - wedgeLeftFoot K t) := by
  constructor <;> simp only [innerSlackU, innerSlackV, wedgeRightFoot, wedgeLeftFoot, dot, uvec, vvec] <;>
    field_simp [hs, hc] <;> ring

theorem wedge_feet_height (K : Set Point) {t : ℝ} (hs : sin t ≠ 0) (hc : cos t ≠ 0) :
    (innerCorner K t).2 = sin t * cos t * (wedgeRightFoot K t - wedgeLeftFoot K t) := by
  rw [proposition2_2_2_innerCorner]
  simp only [wedgeRightFoot, wedgeLeftFoot, Prod.snd_add, Prod.smul_snd,
    smul_eq_mul, uvec_snd, vvec_snd]
  field_simp [hs, hc]
  ring

/-- Every point in a positive-height wedge lies strictly between its floor feet. -/
theorem wedge_point_between_feet {K : Set Point} {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (π / 2)) {p : Point} (hpy : 0 ≤ p.2)
    (hu : innerSlackU K t p < 0) (hv : innerSlackV K t p < 0) :
    wedgeLeftFoot K t < p.1 ∧ p.1 < wedgeRightFoot K t := by
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
  have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩
  constructor
  · rw [wedgeLeftFoot, div_lt_iff₀ hs]
    have hterm := mul_nonneg hpy hc.le
    simp only [innerSlackV, dot, vvec] at hv
    nlinarith
  · rw [wedgeRightFoot, lt_div_iff₀ hc]
    have hterm := mul_nonneg hpy hs.le
    simp only [innerSlackU, dot, uvec] at hu
    nlinarith

/-- A floor point strictly between the feet belongs to the niche. -/
theorem floor_between_feet_mem_niche {K : Set Point} {t x : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (π / 2)) (hx : wedgeLeftFoot K t < x ∧ x < wedgeRightFoot K t) :
    (x, 0) ∈ niche K (π / 2) := by
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
  have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩
  obtain ⟨heU, heV⟩ := wedge_floor_slacks K (x := x) hs.ne' hc.ne'
  apply (mem_niche_iff_slacks K (x, 0)).2
  refine ⟨le_rfl, t, ht, ?_, ?_⟩
  · rw [heU]
    exact mul_neg_of_pos_of_neg hc (sub_neg.mpr hx.2)
  · rw [heV]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hs) (sub_pos.mpr hx.1)

/-- Gerver's entire open-angle corner path is above the floor, including the two unexposed phases. -/
theorem gerver_path_height_pos {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (π / 2)) : 0 < (P.path t).2 := by
  have henv := gn_envHyp hP (romik_bounds hP hbox)
  have hheight : ∀ u ∈ Icc (0 : ℝ) (π / 2), (P.path u).2 < 1 :=
    fun u hu => path_snd_lt_one hP (romik_bounds hP hbox) hu.1 hu.2
  have hbounds := envelope_bounds_of_path_height henv hheight
  by_cases hfirst : t < P.φ
  · have hD : envD P.path P.gs_β t ∈ gerverEnvelope P :=
      Or.inr ⟨t, ⟨ht.1.le, hfirst.le.trans henv.ht.2.1.le⟩, rfl⟩
    have hDy := (hbounds _ hD).2.1
    have hp := mul_pos (henv.β_pos t ht)
      (sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos]))
    simp only [envD, Prod.snd_sub, Prod.smul_snd, smul_eq_mul, uvec_snd] at hDy
    linarith
  by_cases hlast : π / 2 - P.φ < t
  · have hB : envB P.path P.gs_α t ∈ gerverEnvelope P :=
      Or.inl (Or.inl ⟨t, ⟨henv.ht.2.2.2.1.le.trans hlast.le, ht.2.le⟩, rfl⟩)
    have hBy := (hbounds _ hB).2.1
    have hp := mul_neg_of_neg_of_pos (henv.α_neg t ht)
      (cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩)
    simp only [envB, Prod.snd_add, Prod.smul_snd, smul_eq_mul, vvec_snd] at hBy
    linarith
  exact henv.x_pos t ⟨not_lt.mp hfirst, not_lt.mp hlast⟩

/-- Both Gerver wedge feet lie between the two roof endpoints at every open angle. -/
theorem gerver_wedge_feet_bounds {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (π / 2)) :
    gerverRoofLeft P ≤ wedgeLeftFoot P.cap t ∧
      wedgeRightFoot P.cap t ≤ gerverRoofRight P := by
  sorry

/-- Nearby niches stay in an arbitrarily small horizontal expansion of the reference roof interval. -/
theorem nearby_niche_horizontal_localization {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K P.cap →
      ∀ p ∈ niche K (π / 2), gerverRoofLeft P - η ≤ p.1 ∧ p.1 ≤ gerverRoofRight P + η := by
  sorry

end MovingSofaStability
