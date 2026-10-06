module

public import MovingSofaStability.CapDistance

/-!
# The actual nonconvex cap shape and robust hallway inequalities

The erosion inclusion is proved for arbitrary pairs of normalized right-angle
caps, not just Gerver and not just injective caps. It keeps the actual set
difference K minus its niche throughout.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

def capShape (K : Set Point) : Set Point := K \ niche K (π / 2)

def UpperSupportClose (δ : ℝ) (K L : Set Point) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) π, |supp K t - supp L t| ≤ δ

def innerSlackU (K : Set Point) (t : ℝ) (p : Point) : ℝ := dot p (uvec t) - supp K t + 1

def innerSlackV (K : Set Point) (t : ℝ) (p : Point) : ℝ :=
  dot p (vvec t) - supp K (t + π / 2) + 1

/-- Closed Euclidean-ball erosion, convenient for point witnesses. -/
def euclideanErosion (r : ℝ) (S : Set Point) : Set Point :=
  {p | ∀ q, euclideanDist p q ≤ r → q ∈ S}

theorem UpperSupportClose.symm {δ : ℝ} {K L : Set Point}
    (h : UpperSupportClose δ K L) : UpperSupportClose δ L K := by
  intro t ht
  simpa only [abs_sub_comm] using h t ht

/-- A cap is determined by its upper half-planes and the floor. -/
theorem cap_mem_iff_upper {K : Set Point} (hK : IsCap K (π / 2)) (p : Point) :
    p ∈ K ↔ 0 ≤ p.2 ∧ ∀ t ∈ Icc (0 : ℝ) π, dot p (uvec t) ≤ supp K t := by
  constructor
  · intro hp
    exact ⟨hK.snd_nonneg hp, fun t _ => dot_le_supp hK.2.1.2.1 hp t⟩
  · rintro ⟨hpy, h⟩
    apply (mem_iff_forall_dot_le_supp hK.2.1 p).2
    intro t
    by_cases hs : 0 ≤ sin t
    · obtain ⟨s, hsI, hu, -⟩ := upper_normal_representative t hs
      have he : supp K s = supp K t := by simp only [supp, hu]
      have hh := h s hsI
      simpa only [hu, he] using hh
    have hs' := (not_le.mp hs).le
    have hys : p.2 * sin t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpy hs'
    by_cases hc : 0 ≤ cos t
    · rw [cap_lower_right_support hK hs' hc]
      have hx := h 0 ⟨le_rfl, pi_pos.le⟩
      simp only [uvec_zero, dot] at hx
      have hm := mul_le_mul_of_nonneg_right hx hc
      simp only [dot, uvec]
      linarith
    · rw [cap_lower_left_support hK hs' (not_le.mp hc).le]
      have hx := h π ⟨pi_pos.le, le_rfl⟩
      simp only [uvec_pi, dot] at hx
      have hm : p.1 * cos t ≤ -supp K π * cos t :=
        mul_le_mul_of_nonpos_right (by linarith) (not_le.mp hc).le
      simp only [dot, uvec]
      linarith

/-- The actual forbidden quadrant is described by two strict slack inequalities. -/
theorem mem_qMinus_iff_slacks (K : Set Point) (t : ℝ) (p : Point) :
    p ∈ qMinus K t ↔ innerSlackU K t p < 0 ∧ innerSlackV K t p < 0 := by
  rw [ms_mem_qMinus_iff]
  unfold innerSlackU innerSlackV
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem mem_niche_iff_slacks (K : Set Point) (p : Point) :
    p ∈ niche K (π / 2) ↔ 0 ≤ p.2 ∧
      ∃ t ∈ Ioo (0 : ℝ) (π / 2), innerSlackU K t p < 0 ∧ innerSlackV K t p < 0 := by
  simp only [niche, mem_inter_iff, mem_fan_iff, dot_uvec_pi_div_two, and_self,
    mem_iUnion, exists_prop, mem_qMinus_iff_slacks]

/-- Membership outside the niche is a closed, rather than strict, condition. -/
theorem mem_capShape_iff {K : Set Point} (hK : IsCap K (π / 2)) (p : Point) :
    p ∈ capShape K ↔ p ∈ K ∧ ∀ t ∈ Ioo (0 : ℝ) (π / 2),
      0 ≤ max (innerSlackU K t p) (innerSlackV K t p) := by
  constructor
  · rintro ⟨hp, hn⟩
    refine ⟨hp, fun t ht => ?_⟩
    by_contra hbad
    have hlt : max (innerSlackU K t p) (innerSlackV K t p) < 0 := not_le.mp hbad
    apply hn
    exact (mem_niche_iff_slacks K p).2 ⟨hK.snd_nonneg hp,
      t, ht, (le_max_left _ _).trans_lt hlt, (le_max_right _ _).trans_lt hlt⟩
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    intro hn
    obtain ⟨-, t, ht, hu, hv⟩ := (mem_niche_iff_slacks K p).1 hn
    have hm := h t ht
    exact (not_lt_of_ge hm) (max_lt hu hv)

theorem slackU_support_error {δ : ℝ} {K L : Set Point} (h : UpperSupportClose δ K L)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) π) (p : Point) :
    |innerSlackU K t p - innerSlackU L t p| ≤ δ := by
  have he : innerSlackU K t p - innerSlackU L t p = supp L t - supp K t := by
    unfold innerSlackU
    ring
  rw [he, abs_sub_comm]
  exact h t ht

theorem slackV_support_error {δ : ℝ} {K L : Set Point} (h : UpperSupportClose δ K L)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (π / 2)) (p : Point) :
    |innerSlackV K t p - innerSlackV L t p| ≤ δ := by
  have he : innerSlackV K t p - innerSlackV L t p =
      supp L (t + π / 2) - supp K (t + π / 2) := by
    unfold innerSlackV
    ring
  rw [he, abs_sub_comm]
  exact h _ ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩

/-- Strict reference violations larger than the support error remain violations. -/
theorem niche_of_reference_slack_margin {δ : ℝ} {K L : Set Point}
    (h : UpperSupportClose δ K L) {p : Point} (hpy : 0 ≤ p.2)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (π / 2))
    (hu : innerSlackU L t p < -δ) (hv : innerSlackV L t p < -δ) :
    p ∈ niche K (π / 2) := by
  have hU := (abs_le.mp (slackU_support_error h ⟨ht.1.le, by linarith [ht.2, pi_pos]⟩ p)).2
  have hV := (abs_le.mp (slackV_support_error h ⟨ht.1.le, ht.2.le⟩ p)).2
  exact (mem_niche_iff_slacks K p).2 ⟨hpy, t, ht, by linarith, by linarith⟩

/-- A reference erosion is contained in the perturbed nonconvex shape.
The coefficient two is convenient and non-sharp. -/
theorem reference_erosion_subset {δ : ℝ} (hδ : 0 ≤ δ) {K₀ K : Set Point}
    (h₀ : IsCap K₀ (π / 2)) (hK : IsCap K (π / 2))
    (hclose : UpperSupportClose δ K K₀) :
    euclideanErosion (2 * δ) (capShape K₀) ⊆ capShape K := by
  intro p hp
  have hp0 : p ∈ capShape K₀ := hp p (by simpa only [euclideanDist_self] using mul_nonneg (by norm_num) hδ)
  have hpK : p ∈ K := by
    apply (cap_mem_iff_upper hK p).2
    refine ⟨h₀.snd_nonneg hp0.1, ?_⟩
    intro t ht
    have hd : euclideanDist p (p + δ • uvec t) ≤ 2 * δ := by
      change norm2 (p - (p + δ • uvec t)) ≤ 2 * δ
      rw [show p - (p + δ • uvec t) = -(δ • uvec t) by abel,
        norm2_neg, norm2_smul, norm2_uvec, mul_one, abs_of_nonneg hδ]
      linarith
    have hq := (hp (p + δ • uvec t) hd).1
    have hs := dot_le_supp h₀.2.1.2.1 hq t
    rw [dot_add_left, dot_smul_left, dot_uvec_self, mul_one] at hs
    have herr := (abs_le.mp (hclose t ht)).1
    linarith
  refine ⟨hpK, ?_⟩
  intro hn
  obtain ⟨-, t, ht, hu, hv⟩ := (mem_niche_iff_slacks K p).1 hn
  let q := p - δ • uvec t - δ • vvec t
  have hd : euclideanDist p q ≤ 2 * δ := by
    change norm2 (p - (p - δ • uvec t - δ • vvec t)) ≤ 2 * δ
    rw [show p - (p - δ • uvec t - δ • vvec t) = δ • uvec t + δ • vvec t by abel]
    have hh := norm2_add_le (δ • uvec t) (δ • vvec t)
    have hnv : norm2 (vvec t) = 1 := by simp [norm2]
    rw [norm2_smul, norm2_smul, norm2_uvec, hnv, abs_of_nonneg hδ] at hh
    nlinarith
  have hq := hp q hd
  have herrU := (abs_le.mp (hclose t ⟨ht.1.le, by linarith [ht.2, pi_pos]⟩)).2
  have herrV := (abs_le.mp (hclose (t + π / 2)
    ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩)).2
  have eqU : innerSlackU K₀ t q = innerSlackU K t p + supp K t - supp K₀ t - δ := by
    simp only [innerSlackU, q, dot_sub_left, dot_smul_left, dot_uvec_self, dot_vvec_uvec]
    ring
  have eqV : innerSlackV K₀ t q = innerSlackV K t p +
      supp K (t + π / 2) - supp K₀ (t + π / 2) - δ := by
    simp only [innerSlackV, q, dot_sub_left, dot_smul_left, dot_uvec_vvec, dot_vvec_self]
    ring
  apply hq.2
  apply (mem_niche_iff_slacks K₀ q).2
  exact ⟨h₀.snd_nonneg hq.1, t, ht, by rw [eqU]; linarith, by rw [eqV]; linarith⟩

end MovingSofaStability
