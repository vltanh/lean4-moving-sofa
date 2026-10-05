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
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
  have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩
  have hp := gerver_path_height_pos hP hbox ht
  have hpath := ((theorem8_4_1_monotone hP hbox).2 t ⟨ht.1.le, ht.2.le⟩).2.2
  rw [← hpath, wedge_feet_height P.cap hs.ne' hc.ne'] at hp
  have hZW : wedgeLeftFoot P.cap t < wedgeRightFoot P.cap t := by
    have hmul := mul_pos hs hc
    exact sub_pos.mp (pos_of_mul_pos_left hp hmul.le)
  obtain ⟨H, L, γ, hroof⟩ := gerver_roof_data hP hbox
  have hfloorbounds : ∀ x, wedgeLeftFoot P.cap t < x → x < wedgeRightFoot P.cap t →
      x ∈ Icc (gerverRoofLeft P) (gerverRoofRight P) := by
    intro x hx1 hx2
    have h := floor_between_feet_mem_niche ht ⟨hx1, hx2⟩
    rw [hroof.niche_eq] at h
    exact h.1
  constructor
  · by_contra hnot
    have hlt := not_le.mp hnot
    let y := min (gerverRoofLeft P) (wedgeRightFoot P.cap t)
    have hy : wedgeLeftFoot P.cap t < y := lt_min hlt hZW
    let x := (wedgeLeftFoot P.cap t + y) / 2
    have hx := hfloorbounds x (by dsimp [x]; linarith)
      (by have hh := min_le_right (gerverRoofLeft P) (wedgeRightFoot P.cap t); dsimp [x, y] at *; linarith)
    have hya : y ≤ gerverRoofLeft P := min_le_left _ _
    dsimp [x] at hx
    linarith [hx.1]
  · by_contra hnot
    have hlt := not_le.mp hnot
    let y := max (gerverRoofRight P) (wedgeLeftFoot P.cap t)
    have hy : y < wedgeRightFoot P.cap t := max_lt hlt hZW
    let x := (y + wedgeRightFoot P.cap t) / 2
    have hx := hfloorbounds x
      (by have hh := le_max_right (gerverRoofRight P) (wedgeLeftFoot P.cap t); dsimp [x, y] at *; linarith)
      (by dsimp [x]; linarith)
    have hyb : gerverRoofRight P ≤ y := le_max_left _ _
    dsimp [x] at hx
    linarith [hx.2]

/-- Nearby niches stay in an arbitrarily small horizontal expansion of the reference roof interval. -/
theorem nearby_niche_horizontal_localization {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K P.cap →
      ∀ p ∈ niche K (π / 2), gerverRoofLeft P - η ≤ p.1 ∧ p.1 ≤ gerverRoofRight P + η := by
  obtain ⟨δ₀, ρ₀, hδ₀, hρ₀, hδ₀1, htop⟩ := gerver_near_top_contacts hP hbox hη
  let ρ := min ρ₀ (π / 4)
  have hρ : 0 < ρ := lt_min hρ₀ (by positivity)
  have hρ₀' : ρ ≤ ρ₀ := min_le_left _ _
  have hρ4 : ρ ≤ π / 4 := min_le_right _ _
  have hsρ : 0 < sin ρ := sin_pos_of_pos_of_lt_pi hρ (by linarith [pi_pos])
  let δ := min δ₀ (η * sin ρ)
  have hδ : 0 < δ := lt_min hδ₀ (mul_pos hη hsρ)
  have hδ₀' : δ ≤ δ₀ := min_le_left _ _
  have hδρ : δ ≤ η * sin ρ := min_le_right _ _
  refine ⟨δ, hδ, hδ₀'.trans hδ₀1, ?_⟩
  intro K hK hclose p hp
  obtain ⟨hpy, t, ht, hu, hv⟩ := (mem_niche_iff_slacks K p).1 hp
  obtain ⟨hleft, hright⟩ := wedge_point_between_feet ht hpy hu hv
  obtain ⟨hrefL, hrefR⟩ := gerver_wedge_feet_bounds hP hbox ht
  have hsin : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
  have hcos : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩
  constructor
  · by_cases hnear : t ≤ ρ
    · let q := vplus K (t + π / 2)
      have hq := vplus_mem_edge hK.2.1 (t + π / 2)
      have hqx := (htop K hK (hclose.mono hδ₀') (t + π / 2)
        ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
        (by rw [add_sub_cancel_right, abs_of_pos ht.1]; exact hnear.trans hρ₀') q hq).1
      have hqy := hK.snd_le_one hq.1
      have hqy0 := hK.snd_nonneg hq.1
      have he : wedgeLeftFoot K t = q.1 + (1 - q.2 * cos t) / sin t := by
        unfold wedgeLeftFoot
        rw [← hq.2, uvec_add_pi_div_two]
        simp only [dot, vvec]
        field_simp [hsin.ne']
        ring
      have hnon : 0 ≤ (1 - q.2 * cos t) / sin t := by
        apply div_nonneg _ hsin.le
        nlinarith [cos_le_one t]
      rw [he] at hleft
      linarith
    · have hden : sin ρ ≤ sin t := by
        have hh := cos_le_cos_of_nonneg_of_le_pi
          (x := π / 2 - t) (y := π / 2 - ρ)
          (by linarith [ht.2]) (by linarith [hρ, pi_pos]) (by linarith [not_le.mp hnear])
        simpa only [cos_pi_div_two_sub] using hh
      have herr := (abs_le.mp (hclose (t + π / 2)
        ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩)).2
      have he : wedgeLeftFoot P.cap t - η ≤ wedgeLeftFoot K t := by
        unfold wedgeLeftFoot
        apply (div_le_div_iff₀ hsin hsin).2
        have hηden := mul_le_mul_of_nonneg_left hden hη.le
        nlinarith
      linarith
  · by_cases hnear : π / 2 - ρ ≤ t
    · let q := vplus K t
      have hq := vplus_mem_edge hK.2.1 t
      have hqx := (htop K hK (hclose.mono hδ₀') t
        ⟨ht.1.le, by linarith [ht.2, pi_pos]⟩
        (by rw [abs_of_nonpos (by linarith [ht.2] : t - π / 2 ≤ 0)]; linarith) q hq).2
      have hqy := hK.snd_le_one hq.1
      have hqy0 := hK.snd_nonneg hq.1
      have he : wedgeRightFoot K t = q.1 + (q.2 * sin t - 1) / cos t := by
        unfold wedgeRightFoot
        rw [← hq.2]
        simp only [dot, uvec]
        field_simp [hcos.ne']
        ring
      have hnon : (q.2 * sin t - 1) / cos t ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg _ hcos.le
        nlinarith [sin_le_one t]
      rw [he] at hright
      linarith
    · have hden : sin ρ ≤ cos t := by
        have hh := cos_le_cos_of_nonneg_of_le_pi
          (x := t) (y := π / 2 - ρ) ht.1.le
          (by linarith [hρ, pi_pos]) (not_le.mp hnear).le
        simpa only [cos_pi_div_two_sub] using hh
      have herr := (abs_le.mp (hclose t ⟨ht.1.le, by linarith [ht.2, pi_pos]⟩)).2
      have he : wedgeRightFoot K t ≤ wedgeRightFoot P.cap t + η := by
        unfold wedgeRightFoot
        apply (div_le_iff₀ hcos).2
        have hηden := mul_le_mul_of_nonneg_left hden hη.le
        have hcanc : ((supp P.cap t - 1) / cos t) * cos t = supp P.cap t - 1 :=
          div_mul_cancel₀ _ hcos.ne'
        nlinarith
      linarith

end MovingSofaStability
