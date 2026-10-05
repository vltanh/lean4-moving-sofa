module

public import MovingSofaStability.EnvelopeSlope

/-!
# Geometric consequences of a cap with a Lipschitz niche roof

Uncompiled proof source. `CapRoofData` records concrete boundary geometry; it
does not assume a stability estimate. The nonconvex set is decomposed into
two convex wings and a positive-height epigraph strip, and its uniform
interior-ball property is proved from that decomposition.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality

namespace MovingSofaStability

structure CapRoofData (K : Set Point) (a b H L : ℝ) (γ : ℝ → ℝ) : Prop where
  cap : IsCap K (π / 2)
  order : a < b
  left_wing : -supp K π < a
  right_wing : b < supp K 0
  height : H < 1
  slope_nonneg : 0 ≤ L
  roof_nonneg : ∀ x ∈ Icc a b, 0 ≤ γ x
  roof_le : ∀ x ∈ Icc a b, γ x ≤ H
  roof_lipschitz : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |γ x - γ y| ≤ L * |x - y|
  left_zero : γ a = 0
  right_zero : γ b = 0
  rectangle : Icc a b ×ˢ Icc (0 : ℝ) 1 ⊆ K
  niche_eq : niche K (π / 2) = {p | p.1 ∈ Icc a b ∧ 0 ≤ p.2 ∧ p.2 < γ p.1}

/-- Fill downward below a horizontal chord of a cap. -/
theorem cap_horizontal_rectangle {K : Set Point} (hK : IsCap K (π / 2))
    {a b h : ℝ} (hab : a < b) (ha : (a, h) ∈ K) (hb : (b, h) ∈ K) :
    Icc a b ×ˢ Icc (0 : ℝ) h ⊆ K := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  let c := (x - a) / (b - a)
  have hba : 0 < b - a := sub_pos.mpr hab
  have hc : c ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hx.1) hba.le,
      (div_le_one hba).2 (by linarith [hx.2])⟩
  have htop := hK.2.1.2.2.add_smul_sub_mem ha hb hc
  have he : (a, h) + c • ((b, h) - (a, h)) = (x, h) := by
    apply Prod.ext
    · dsimp [c]
      field_simp [hba.ne']
      ring
    · simp
  rw [he] at htop
  exact opt_cap_down hK htop hy.1 hy.2

/-- A nondegenerate box inside a set witnesses nonempty interior. -/
theorem interior_nonempty_of_box {C : Set Point} {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hbox : Icc a b ×ˢ Icc c d ⊆ C) :
    (interior C).Nonempty := by
  have hi : Ioo a b ×ˢ Ioo c d ⊆ C := fun p hp =>
    hbox ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  have hint := interior_maximal hi (isOpen_Ioo.prod isOpen_Ioo)
  refine ⟨((a + b) / 2, (c + d) / 2), hint ?_⟩
  constructor <;> constructor <;> dsimp <;> linarith

def leftWing (K : Set Point) (a : ℝ) : Set Point := K ∩ {p | p.1 ≤ a}
def rightWing (K : Set Point) (b : ℝ) : Set Point := K ∩ {p | b ≤ p.1}

/-- The two wings are genuinely two-dimensional convex bodies. -/
theorem CapRoofData.wings {K : Set Point} {a b H L : ℝ} {γ : ℝ → ℝ}
    (h : CapRoofData K a b H L γ) :
    (IsConvexBody (leftWing K a) ∧ (interior (leftWing K a)).Nonempty) ∧
      (IsConvexBody (rightWing K b) ∧ (interior (rightWing K b)).Nonempty) := by
  have hleft : (a, 1) ∈ K := h.rectangle ⟨⟨le_rfl, h.order.le⟩, ⟨by norm_num, le_rfl⟩⟩
  have hright : (b, 1) ∈ K := h.rectangle ⟨⟨h.order.le, le_rfl⟩, ⟨by norm_num, le_rfl⟩⟩
  let l := -supp K π
  let r := supp K 0
  have hll : l < a := h.left_wing
  have hrr : b < r := h.right_wing
  have hmidL : ((l + a) / 2, (1 / 2 : ℝ)) ∈ K := by
    have hh := h.cap.2.1.2.2 (opt_cap_C_mem h.cap) hleft
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    convert hh using 1 <;> ext <;> simp only [l, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
  have hmidR : ((b + r) / 2, (1 / 2 : ℝ)) ∈ K := by
    have hh := h.cap.2.1.2.2 hright (opt_cap_A_mem h.cap)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    convert hh using 1 <;> ext <;> simp only [r, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
  have hboxL : Icc ((l + a) / 2) a ×ˢ Icc (0 : ℝ) (1 / 2) ⊆ leftWing K a := by
    have hh := cap_horizontal_rectangle h.cap (by linarith : (l + a) / 2 < a)
      hmidL (opt_cap_down h.cap hleft (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    exact fun p hp => ⟨hh hp, hp.1.2⟩
  have hboxR : Icc b ((b + r) / 2) ×ˢ Icc (0 : ℝ) (1 / 2) ⊆ rightWing K b := by
    have hh := cap_horizontal_rectangle h.cap (by linarith : b < (b + r) / 2)
      (opt_cap_down h.cap hright (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)) hmidR
    exact fun p hp => ⟨hh hp, hp.1.1⟩
  have hLi := interior_nonempty_of_box (by linarith : (l + a) / 2 < a)
    (by norm_num : (0 : ℝ) < 1 / 2) hboxL
  have hRi := interior_nonempty_of_box (by linarith : b < (b + r) / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) hboxR
  have hLc : IsCompact (leftWing K a) :=
    h.cap.2.1.2.1.of_isClosed_subset
      (h.cap.2.1.2.1.isClosed.inter (isClosed_le continuous_fst continuous_const)) inter_subset_left
  have hRc : IsCompact (rightWing K b) :=
    h.cap.2.1.2.1.of_isClosed_subset
      (h.cap.2.1.2.1.isClosed.inter (isClosed_le continuous_const continuous_fst)) inter_subset_left
  have hLv : Convex ℝ (leftWing K a) := by
    have hh := h.cap.2.1.2.2.inter (convex_halfMinus 0 a)
    simpa only [leftWing, halfMinus, dot_uvec_zero] using hh
  have hRv : Convex ℝ (rightWing K b) := by
    have hh := h.cap.2.1.2.2.inter (convex_halfPlus 0 b)
    simpa only [rightWing, halfPlus, dot_uvec_zero] using hh
  exact ⟨⟨⟨hLi.mono interior_subset, hLc, hLv⟩, hLi⟩,
    ⟨⟨hRi.mono interior_subset, hRc, hRv⟩, hRi⟩⟩

/-- The nonconvex shape is exactly its two wings and its roof strip. -/
theorem CapRoofData.shape_decomposition {K : Set Point} {a b H L : ℝ} {γ : ℝ → ℝ}
    (h : CapRoofData K a b H L γ) :
    capShape K = (leftWing K a ∪ roofStrip a b γ) ∪ rightWing K b := by
  ext p
  constructor
  · rintro ⟨hp, hn⟩
    by_cases ha : p.1 ≤ a
    · exact Or.inl (Or.inl ⟨hp, ha⟩)
    by_cases hb : b ≤ p.1
    · exact Or.inr ⟨hp, hb⟩
    have hx : p.1 ∈ Icc a b := ⟨(not_le.mp ha).le, (not_le.mp hb).le⟩
    have hy : γ p.1 ≤ p.2 := by
      by_contra hbad
      apply hn
      rw [h.niche_eq]
      exact ⟨hx, h.cap.snd_nonneg hp, not_le.mp hbad⟩
    exact Or.inl (Or.inr ⟨hx, hy, h.cap.snd_le_one hp⟩)
  · rintro ((hp | hp) | hp)
    · refine ⟨hp.1, ?_⟩
      rw [h.niche_eq]
      rintro ⟨hx, hy, hγ⟩
      have he : p.1 = a := le_antisymm hp.2 hx.1
      rw [he, h.left_zero] at hγ
      linarith
    · have hpK := h.rectangle ⟨hp.1, (h.roof_nonneg p.1 hp.1).trans hp.2.1, hp.2.2⟩
      refine ⟨hpK, ?_⟩
      rw [h.niche_eq]
      rintro ⟨-, -, hy⟩
      exact (not_lt_of_ge hp.2.1) hy
    · refine ⟨hp.1, ?_⟩
      rw [h.niche_eq]
      rintro ⟨hx, hy, hγ⟩
      have he : p.1 = b := le_antisymm hx.2 hp.2
      rw [he, h.right_zero] at hγ
      linarith

/-- The uniform interior-ball property follows from concrete cap/roof data. -/
theorem CapRoofData.interiorBalls {K : Set Point} {a b H L : ℝ} {γ : ℝ → ℝ}
    (h : CapRoofData K a b H L γ) :
    ∃ κ r₀ : ℝ, 0 < κ ∧ 0 < r₀ ∧ HasInteriorBalls (capShape K) κ r₀ := by
  obtain ⟨hL, hR⟩ := h.wings
  have left := convexBody_hasInteriorBalls hL.1 hL.2
  have middle := roofStrip_hasInteriorBalls h.order h.height h.slope_nonneg h.roof_lipschitz h.roof_le
  have right := convexBody_hasInteriorBalls hR.1 hR.2
  rw [h.shape_decomposition]
  exact exists_interiorBalls_union (exists_interiorBalls_union left middle) right

end MovingSofaStability
