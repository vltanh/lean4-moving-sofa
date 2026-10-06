module

public import MovingSofaStability.GerverRoof

/-!
# Quantitative roof margins and approximate hallway recovery

The smaller set may violate the omitted full-angle constraints by a controlled
slack. It is not assumed to lie in its full-angle cap shape. A positive
reference roof margin converts this slack into an actual point of the reference
sofa.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality

namespace MovingSofaStability

/-- Unpinned cap support control extends to the lower semicircle as well. -/
theorem upperSupportClose_all {δ : ℝ} {K L : Set Point}
    (hK : IsCap K (π / 2)) (hL : IsCap L (π / 2))
    (h : UpperSupportClose δ K L) : ∀ t, |supp K t - supp L t| ≤ δ := by
  intro t
  by_cases hs : 0 ≤ sin t
  · obtain ⟨s, hsi, hu, -⟩ := upper_normal_representative t hs
    have hK' : supp K s = supp K t := by simp only [supp, hu]
    have hL' : supp L s = supp L t := by simp only [supp, hu]
    simpa only [hK', hL'] using h s hsi
  have hs' := (not_le.mp hs).le
  by_cases hc : 0 ≤ cos t
  · rw [cap_lower_right_support hK hs' hc, cap_lower_right_support hL hs' hc,
      ← sub_mul, abs_mul]
    exact ((mul_le_mul_of_nonneg_left (abs_cos_le_one t) (abs_nonneg _)).trans_eq
      (mul_one _)).trans (h 0 ⟨le_rfl, pi_pos.le⟩)
  · rw [cap_lower_left_support hK hs' (not_le.mp hc).le,
      cap_lower_left_support hL hs' (not_le.mp hc).le]
    have he : -supp K π * cos t - -supp L π * cos t = -(supp K π - supp L π) * cos t := by ring
    rw [he, abs_mul, abs_neg]
    exact ((mul_le_mul_of_nonneg_left (abs_cos_le_one t) (abs_nonneg _)).trans_eq
      (mul_one _)).trans (h π ⟨pi_pos.le, le_rfl⟩)

theorem upperSupportClose_euclidean {δ : ℝ} (hδ : 0 ≤ δ) {K L : Set Point}
    (hK : IsCap K (π / 2)) (hL : IsCap L (π / 2)) (h : UpperSupportClose δ K L) :
    EuclideanClose δ K L :=
  euclideanClose_of_support_bound hK.2.1 hL.2.1 hδ (upperSupportClose_all hK hL h)

/-- Every roof point belongs to the actual nonconvex reference shape. -/
theorem CapRoofData.roof_mem {K : Set Point} {a b H L : ℝ} {γ : ℝ → ℝ}
    (h : CapRoofData K a b H L γ) {x : ℝ} (hx : x ∈ Icc a b) :
    (x, γ x) ∈ capShape K := by
  refine ⟨h.rectangle ⟨hx, h.roof_nonneg x hx, (h.roof_le x hx).trans h.height.le⟩, ?_⟩
  rw [h.niche_eq]
  rintro ⟨-, -, hh⟩
  exact (lt_irrefl (γ x)) hh

/-- The reference niche has a uniform positive margin from every upper supporting wall. -/
theorem CapRoofData.outer_margin {K : Set Point} {a b H L : ℝ} {γ : ℝ → ℝ}
    (h : CapRoofData K a b H L γ) :
    ∃ d : ℝ, 0 < d ∧ ∀ p ∈ niche K (π / 2), ∀ t ∈ Icc (0 : ℝ) π,
      d ≤ supp K t - dot p (uvec t) := by
  let R : Set Point := Icc a b ×ˢ Icc (0 : ℝ) H
  let F := fun z : Point × ℝ => supp K z.2 - dot z.1 (uvec z.2)
  have hc : Continuous F :=
    (h.cap.2.1.continuous_supp.comp continuous_snd).sub
      (continuous_dot_pair.comp (continuous_fst.prodMk (continuous_uvec.comp continuous_snd)))
  have hpos : ∀ z ∈ R ×ˢ Icc (0 : ℝ) π, 0 < F z := by
    rintro ⟨p, t⟩ ⟨hp, ht⟩
    change p ∈ R at hp
    change t ∈ Icc 0 π at ht
    rcases eq_or_lt_of_le ht.1 with he | ht0
    · subst t
      change 0 < supp K 0 - dot p (uvec 0)
      rw [dot_uvec_zero]
      linarith [hp.1.2, h.right_wing]
    rcases eq_or_lt_of_le ht.2 with he | htπ
    · subst t
      change 0 < supp K π - dot p (uvec π)
      simp only [dot, uvec_pi]
      linarith [hp.1.1, h.left_wing]
    have htop : (p.1, (1 : ℝ)) ∈ K := h.rectangle ⟨hp.1, by norm_num, le_rfl⟩
    have hs := dot_le_supp h.cap.2.1.2.1 htop t
    have hsin : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 htπ
    have hgap : 0 < (1 - p.2) * sin t :=
      mul_pos (by linarith [hp.2.2, h.height]) hsin
    change 0 < supp K t - dot p (uvec t)
    simp only [dot, uvec] at hs ⊢
    nlinarith
  obtain ⟨d, hd, hdle⟩ := ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).exists_forall_le'
    hc.continuousOn hpos
  refine ⟨d, hd, ?_⟩
  intro p hp t ht
  rw [h.niche_eq] at hp
  exact hdle (p, t) ⟨⟨hp.1, hp.2.1, hp.2.2.le.trans (h.roof_le p.1 hp.1)⟩, ht⟩

/-- Primitive wall-margin condition along a reference roof. -/
def RoofSlackMargin (K : Set Point) (γ : ℝ → ℝ) (c τ : ℝ) : Prop :=
  ∀ p ∈ niche K (π / 2), ∃ t ∈ Ioo (0 : ℝ) (π / 2),
    innerSlackU K t p ≤ -min (c * (γ p.1 - p.2)) τ ∧
      innerSlackV K t p ≤ -min (c * (γ p.1 - p.2)) τ

def ApproxHallways (K S : Set Point) (ζ : ℝ) : Prop :=
  ∀ p ∈ S, ∀ t ∈ Ioo (0 : ℝ) (π / 2),
    -ζ ≤ max (innerSlackU K t p) (innerSlackV K t p)

/-- A support perturbation and an approximate hallway bound control the
S-to-reference directed distance, including points outside the full-angle shape. -/
theorem directed_to_reference_of_margins {K₀ K S : Set Point}
    {a b H L c τ d₀ δ ζ : ℝ} {γ : ℝ → ℝ}
    (hroof : CapRoofData K₀ a b H L γ) (hK : IsCap K (π / 2))
    (hc : 0 < c) (hδ : 0 ≤ δ) (hζ : 0 ≤ ζ)
    (hclose : UpperSupportClose δ K K₀)
    (houter : ∀ q ∈ niche K₀ (π / 2), ∀ t ∈ Icc (0 : ℝ) π,
      d₀ ≤ supp K₀ t - dot q (uvec t))
    (hδsmall : δ < d₀) (hsmall : δ + ζ < τ)
    (hslack : RoofSlackMargin K₀ γ c τ)
    (hSK : S ⊆ K) (hhall : ApproxHallways K S ζ) :
    DirectedClose (max 1 (1 / c) * (δ + ζ)) S (capShape K₀) := by
  have hC : 0 ≤ max (1 : ℝ) (1 / c) := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hδC : δ ≤ max 1 (1 / c) * (δ + ζ) := by
    have hm := mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) (1 / c)) (add_nonneg hδ hζ)
    nlinarith
  have hcapclose := upperSupportClose_euclidean hδ hK hroof.cap hclose
  intro p hp
  have hpK := hSK hp
  by_cases hp₀ : p ∈ K₀
  · by_cases hpG : p ∈ capShape K₀
    · exact ⟨p, hpG, by simpa only [euclideanDist_self] using mul_nonneg hC (add_nonneg hδ hζ)⟩
    have hpN : p ∈ niche K₀ (π / 2) := by
      by_contra hn
      exact hpG ⟨hp₀, hn⟩
    have hn := hpN
    rw [hroof.niche_eq] at hn
    let depth := γ p.1 - p.2
    have hdpos : 0 < depth := sub_pos.mpr hn.2.2
    obtain ⟨t, ht, hu, hv⟩ := hslack p hpN
    have hU := (abs_le.mp (slackU_support_error hclose
      ⟨ht.1.le, by linarith [ht.2, pi_pos]⟩ p)).2
    have hV := (abs_le.mp (slackV_support_error hclose ⟨ht.1.le, ht.2.le⟩ p)).2
    have hdepth : c * depth ≤ δ + ζ := by
      by_contra he
      have hm : δ + ζ < min (c * depth) τ := lt_min (not_le.mp he) hsmall
      have hu' : innerSlackU K t p < -ζ := by linarith
      have hv' : innerSlackV K t p < -ζ := by linarith
      exact (not_lt_of_ge (hhall p hp t ht)) (max_lt hu' hv')
    let q : Point := (p.1, γ p.1)
    have hq : q ∈ capShape K₀ := hroof.roof_mem hn.1
    have hd : euclideanDist p q = depth := by
      change sqrt ((p.1 - p.1) * (p.1 - p.1) + (p.2 - γ p.1) * (p.2 - γ p.1)) = depth
      rw [sub_self, zero_mul, zero_add, ← pow_two, Real.sqrt_sq_eq_abs,
        abs_of_nonpos (by linarith : p.2 - γ p.1 ≤ 0)]
      dsimp [depth]
      ring
    refine ⟨q, hq, ?_⟩
    rw [hd]
    have hdiv : depth ≤ (δ + ζ) / c := (le_div_iff₀ hc).2 (by nlinarith)
    have hmul := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) (1 / c)) (add_nonneg hδ hζ)
    have he : (1 / c) * (δ + ζ) = (δ + ζ) / c := by ring
    exact hdiv.trans (by simpa only [he] using hmul)
  · obtain ⟨q, hq, hpq⟩ := hcapclose.1 p hpK
    by_cases hqG : q ∈ capShape K₀
    · exact ⟨q, hqG, hpq.trans hδC⟩
    have hqN : q ∈ niche K₀ (π / 2) := by
      by_contra hn
      exact hqG ⟨hq, hn⟩
    have hpinside : p ∈ K₀ := by
      apply (cap_mem_iff_upper hroof.cap p).2
      refine ⟨hK.snd_nonneg hpK, ?_⟩
      intro t ht
      have hproj := dot_uvec_le_norm2 (p - q) t
      rw [dot_sub_left] at hproj
      have hmargin := houter q hqN t ht
      change norm2 (p - q) ≤ δ at hpq
      linarith
    exact (hp₀ hpinside).elim

end MovingSofaStability
