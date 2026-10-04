module

public import MovingSofaOptimality.Gerver.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# The domain of `𝒬` (§8.1)

Definitions 8.1.1 (`def:cap-space-special`), 8.1.3–8.1.6, Theorem 8.1.1 (`thm:cap-space-special`)
part (1), Proposition 8.1.2, Lemmas 8.1.3–8.1.7 and Theorem 8.1.8 (`thm:cap-tail-extension`).

The paper fixes `φ^R = φ` and `φ^L = π/2 - φ` with `φ` Gerver's angle (Definition 8.1.2).
Everything here is stated for a parameter `φ`; where the paper uses numerical properties of
Gerver's `φ` (`2 sec φ + 2 tan φ < 2.2`, `sec φ < 1.1`) we assume `φ ∈ [0.039, 0.04]`, the range
the paper quotes.

**A gap in the proofs.** The paper proves Lemma 8.1.7 (2), (4) with `𝒩(K) ⊆ K` (through
Theorem 2.5.8 (2)), and splits `𝒩(K)` in Theorem 8.2.4 using the disjointness of `K ∩ H̆_K^R` and
`K ∩ H̆_K^L` (Lemma 8.1.4). But `K ∈ 𝒦^i` does not give `𝒩(K) ⊆ K`: the cap with two unit
quarter-discs joined by a flat top of length 3 satisfies the injectivity condition and has area
`3 + π/2`, but its niche is not inside it. The statements hold on all of `𝒦^i` nevertheless, and we
prove them so:
* Lemma 8.1.7 (2): let `p` be the topmost point of `K` on `b_K^R`, and `θ ∈ [φ^R, φ^R + π]` a
  normal angle of `K` at `p` (`opt_exists_normal_of_isMax`). If `θ > φ^R + π/2`, then `p` lies
  beyond `C_K(φ^R)` and `g_K(φ^R) ≤ 1`, against the injectivity condition (`opt_arm_gt_one`).
  Otherwise the sublinearity of the support function (`opt_supp_interp`) between `φ^R` and `θ`, and
  between `θ` and `π/2`, gives `p ∈ H_K^b(t)` for every `t ∈ [φ^R, π/2]`. (4) is the mirror image,
  with `f_K(φ^L)`.
* Theorem 8.2.4: `𝒩(K) ∩ H̆_K^R ∩ H̆_K^L = ∅` (`opt_niche_hRight_hLeft`), since the niche lies
  below height `W₀/2` while `H̆_K^R ∩ H̆_K^L` lies above `(W₀ cos φ^R - 2) / (2 sin φ^R)`, where
  `W₀ = h_K(0) + h_K(π) ≥ |K| ≥ 2.2`.
-/

@[expose] public section

open Real Set
open scoped Pointwise

namespace MovingSofaOptimality

/-! ### Caps with rotation angle `π/2` -/

-- A simp lemma for the files of this chapter only (not exported to importers).
attribute [local simp] dot_mk

section CapFacts
variable {K : Set (ℝ × ℝ)}

/-- A cap with rotation angle `π/2` is closed under moving a point straight down to any height
`y ≥ 0`: it is cut out by half-planes with normal angles in `[0, π]` (whose constraints only
weaken when `y` decreases) and by `y ≥ 0`. -/
lemma opt_cap_down (hK : IsCap K (π / 2)) {p : ℝ × ℝ} (hp : p ∈ K) {y : ℝ} (hy0 : 0 ≤ y)
    (hy : y ≤ p.2) : (p.1, y) ∈ K := by
  obtain ⟨-, hcb, -, -, -, h3, ι, t, c, ht, hKeq⟩ := hK
  -- the half-plane of normal angle `3π/2` is `y ≥ 0`, as `h_K(3π/2) = 0` is attained
  obtain ⟨z, hz, hz3⟩ := exists_dot_eq_supp hcb.2.1 hcb.1 (3 * π / 2)
  rw [h3, dot_uvec_three_pi_div_two] at hz3
  rw [hKeq] at hp hz ⊢
  simp only [mem_iInter, halfMinus, mem_ofPred_eq] at hp hz ⊢
  intro i
  have hpi := hp i
  have hzi := hz i
  have hti := ht i
  simp only [jSet, mem_union, mem_Icc, mem_insert_iff, mem_singleton_iff] at hti
  rcases hti with (h | h) | h | h
  · have hs : 0 ≤ sin (t i) := sin_nonneg_of_nonneg_of_le_pi h.1 (by linarith [pi_pos, h.2])
    simp only [dot, uvec] at hpi ⊢
    nlinarith
  · have hs : 0 ≤ sin (t i) := sin_nonneg_of_nonneg_of_le_pi (by linarith [pi_pos, h.1])
      (by linarith [h.2])
    simp only [dot, uvec] at hpi ⊢
    nlinarith
  · rw [h, show π / 2 + π = 3 * π / 2 by ring, dot_uvec_three_pi_div_two] at hzi ⊢
    linarith
  · rw [h, dot_uvec_three_pi_div_two] at hzi ⊢
    linarith

/-- The bottom-right corner `A = (h_K(0), 0) = v_K⁻(0)` lies in `K`. -/
lemma opt_cap_A_mem (hK : IsCap K (π / 2)) : (supp K 0, (0 : ℝ)) ∈ K := by
  rw [← (inj_cap_consecutive hK).1]
  exact (vminus_mem_edge hK.2.1 0).1

/-- The bottom-left corner `C = (-h_K(π), 0)` lies in `K`. -/
lemma opt_cap_C_mem (hK : IsCap K (π / 2)) : (-supp K π, (0 : ℝ)) ∈ K := by
  obtain ⟨p, hp, hp0⟩ := exists_dot_eq_supp hK.2.1.2.1 hK.2.1.1 π
  rw [uvec_pi] at hp0
  simp at hp0
  have := opt_cap_down hK hp le_rfl (inj_cap_strip hK hp).1
  rwa [show p.1 = -supp K π by linarith] at this

/-- A cap lies between the vertical lines `x = -h_K(π)` and `x = h_K(0)`. -/
lemma opt_cap_fst_le (hK : IsCap K (π / 2)) {p : ℝ × ℝ} (hp : p ∈ K) :
    -supp K π ≤ p.1 ∧ p.1 ≤ supp K 0 := by
  have a := dot_le_supp hK.2.1.2.1 hp 0
  have b := dot_le_supp hK.2.1.2.1 hp π
  rw [dot_uvec_zero] at a
  rw [uvec_pi] at b
  simp at b
  constructor <;> linarith

/-- The vertex `v_K⁺(π)` of a cap is its bottom-left corner `(-h_K(π), 0)`. -/
lemma opt_cap_vplus_pi (hK : IsCap K (π / 2)) : vplus K π = (-supp K π, 0) := by
  have hC := opt_cap_C_mem hK
  have hS : sSup ((fun p => dot p (vvec π)) '' edge K π) = 0 := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨(-supp K π, 0), ⟨hC, ?_⟩, ?_⟩, ?_⟩
    · simp [suppLine, line, uvec_pi]
    · simp [vvec]
    · rintro _ ⟨q, ⟨hq, -⟩, rfl⟩
      simp [vvec]
      exact (inj_cap_strip hK hq).1
  simp [vplus, hS, uvec_pi]

/-- The corner `A = (h_K(0), 0)` lies above the inner wall `b_K(t)` for `t ∈ [0, π/2]`. -/
lemma opt_cap_A_mem_halfB (hK : IsCap K (π / 2)) {t : ℝ} (ht : t ∈ Icc 0 (π / 2)) :
    (supp K 0, (0 : ℝ)) ∈ halfB K t := by
  simp only [halfB, halfPlus, mem_ofPred_eq]
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0; simp [uvec_zero]
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · rw [h1, hK.2.2.2.1, uvec_pi_div_two]; simp
  · have := (theorem2_5_5_supp hK ⟨h0, h1⟩).1
    simp only [dot, uvec]; linarith

/-- The corner `C = (-h_K(π), 0)` lies above the inner wall `d_K(t)` for `t ∈ [0, π/2]`. -/
lemma opt_cap_C_mem_halfD (hK : IsCap K (π / 2)) {t : ℝ} (ht : t ∈ Icc 0 (π / 2)) :
    (-supp K π, (0 : ℝ)) ∈ halfD K t := by
  simp only [halfD, halfPlus, mem_ofPred_eq, uvec_add_pi_div_two]
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0; simp [hK.2.2.2.1, vvec_zero]
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · subst h1; rw [add_halves]; simp [vvec_pi_div_two]
  · have := (theorem2_5_5_supp hK ⟨h0, h1⟩).2
    rw [add_halves, cos_pi_div_two_sub] at this
    simp only [dot, vvec]; linarith

/-- A cap with rotation angle `π/2` whose points have `x`-coordinates in `[a, b]` has area at most
`b - a` (it lies in the box `[a, b] × [0, 1]`). -/
lemma opt_area_le_of_fst_bounds (hK : IsCap K (π / 2)) {a b : ℝ}
    (h : ∀ q ∈ K, a ≤ q.1 ∧ q.1 ≤ b) : area K ≤ b - a := by
  have hsub : K ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 := fun q hq =>
    ⟨⟨(h q hq).1, (h q hq).2⟩, ⟨(inj_cap_strip hK hq).1, (inj_cap_strip hK hq).2⟩⟩
  obtain ⟨q, hq⟩ := hK.2.1.1
  have hab : a ≤ b := le_trans (h q hq).1 (h q hq).2
  have hvol : MeasureTheory.volume (Icc a b ×ˢ Icc (0 : ℝ) 1) = ENNReal.ofReal (b - a) := by
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, Real.volume_Icc,
      Real.volume_Icc]
    simp
  calc area K ≤ (MeasureTheory.volume (Icc a b ×ˢ Icc (0 : ℝ) 1)).toReal :=
        ENNReal.toReal_mono (by rw [hvol]; exact ENNReal.ofReal_ne_top)
          (MeasureTheory.measure_mono hsub)
    _ = b - a := by rw [hvol, ENNReal.toReal_ofReal (by linarith)]

/-- Bounds on `x`-coordinates from the supporting half-planes `H_K(φ)` and `H_K(π - φ)`. -/
lemma opt_cap_fst_le_phi (hK : IsCap K (π / 2)) {φ : ℝ} (hc : 0 < cos φ) (hs : 0 ≤ sin φ)
    {q : ℝ × ℝ} (hq : q ∈ K) : -supp K (π - φ) / cos φ ≤ q.1 ∧ q.1 ≤ supp K φ / cos φ := by
  have a := dot_le_supp hK.2.1.2.1 hq φ
  have b := dot_le_supp hK.2.1.2.1 hq (π - φ)
  simp only [dot, uvec, cos_pi_sub, sin_pi_sub] at a b
  have hq2 := (inj_cap_strip hK hq).1
  constructor
  · rw [div_le_iff₀ hc]; nlinarith
  · rw [le_div_iff₀ hc]; nlinarith

/-- `|K| cos φ ≤ h_K(φ) + h_K(π - φ)`: the cap lies in a box of height `1` between the lines
`x = -h_K(π - φ) / cos φ` and `x = h_K(φ) / cos φ`. -/
lemma opt_area_mul_cos_le (hK : IsCap K (π / 2)) {φ : ℝ} (hc : 0 < cos φ) (hs : 0 ≤ sin φ) :
    area K * cos φ ≤ supp K φ + supp K (π - φ) := by
  have h := opt_area_le_of_fst_bounds hK (fun q hq => opt_cap_fst_le_phi hK hc hs hq)
  rw [show supp K φ / cos φ - -supp K (π - φ) / cos φ = (supp K φ + supp K (π - φ)) / cos φ by
    ring, le_div_iff₀ hc] at h
  exact h

end CapFacts

/-- The numerical facts on `φ ∈ [0.039, 0.04]` used in this chapter. -/
lemma opt_phi_bounds {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) :
    0 < φ ∧ φ < π / 4 ∧ sin φ ≤ 0.04 ∧ 0.9992 ≤ cos φ ∧ 0 < sin φ := by
  obtain ⟨h1, h2⟩ := hφ
  have hpi := two_le_pi
  refine ⟨by linarith, by linarith, (sin_le (by linarith)).trans h2, ?_,
    sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)⟩
  have := one_sub_sq_div_two_le_cos (x := φ)
  nlinarith

/-- The frame identity `w · v_a = -sin (a - s) (w · u_s) + cos (a - s) (w · v_s)`. -/
lemma opt_dot_frame_v (w : ℝ × ℝ) (a s : ℝ) :
    dot w (vvec a) = -sin (a - s) * dot w (uvec s) + cos (a - s) * dot w (vvec s) := by
  rw [vvec_eq_frame s a, dot_add_right, dot_smul_right, dot_smul_right]

/-- `𝐱_K(t) · v_t = h_K(t + π/2) - 1`: the inner corner lies on the inner wall `d_K(t)`. -/
lemma opt_innerCorner_dot_v (K : Set (ℝ × ℝ)) (t : ℝ) :
    dot (innerCorner K t) (vvec t) = supp K (t + π / 2) - 1 := by
  rw [← uvec_add_pi_div_two]; exact (cn_innerCorner_dot K t).2

/-- Under the injectivity condition (2), `𝐱_K` is differentiable on `(0, π/2)`. -/
lemma opt_inj_hasDerivAt {K : Set (ℝ × ℝ)} (h2 : InjCond2 K) {t : ℝ} (ht : t ∈ Ioo 0 (π / 2)) :
    HasDerivAt (innerCorner K) (deriv (innerCorner K) t) t :=
  ((h2.differentiableOn one_ne_zero).differentiableAt (Icc_mem_nhds ht.1 ht.2)).hasDerivAt

/-- The space `𝒦^i` of caps with rotation angle `π/2` satisfying the injectivity condition and with
area at least `2.2` (Definition 8.1.1, `def:cap-space-special`). -/
def IsKi (K : Set (ℝ × ℝ)) : Prop := IsCap K (π / 2) ∧ SatisfiesInjectivity K ∧ 2.2 ≤ area K

/-! ### Minkowski combinations of caps -/

section Comb
open MeasureTheory
variable {K₁ K₂ : Set (ℝ × ℝ)} {c : ℝ}

/-- The combination of points of `K₁` and `K₂` lies in the combination of the sets. -/
lemma opt_comb_mem {a b : ℝ × ℝ} (ha : a ∈ K₁) (hb : b ∈ K₂) :
    (1 - c) • a + c • b ∈ (1 - c) • K₁ + c • K₂ :=
  Set.add_mem_add (Set.smul_mem_smul_set ha) (Set.smul_mem_smul_set hb)

/-- Every point of `(1 - c) K₁ + c K₂` is a combination of points of `K₁` and `K₂`. -/
lemma opt_mem_comb {p : ℝ × ℝ} (hp : p ∈ (1 - c) • K₁ + c • K₂) :
    ∃ a ∈ K₁, ∃ b ∈ K₂, p = (1 - c) • a + c • b := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.mp hp
  obtain ⟨a, ha, rfl⟩ := Set.mem_smul_set.mp hx
  obtain ⟨b, hb, rfl⟩ := Set.mem_smul_set.mp hy
  exact ⟨a, ha, b, hb, rfl⟩

/-- A convex combination of negative numbers is negative. -/
lemma opt_comb_neg {a b : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (ha : a < 0) (hb : b < 0) :
    (1 - c) * a + c * b < 0 :=
  convex_Iio (0 : ℝ) ha hb (sub_nonneg.mpr hc.2) hc.1 (sub_add_cancel 1 c)

/-- The Minkowski combination of two caps with rotation angle `π/2` is such a cap. -/
lemma opt_comb_isCap (h₁ : IsCap K₁ (π / 2)) (h₂ : IsCap K₂ (π / 2)) (hc : c ∈ Icc (0 : ℝ) 1) :
    IsCap ((1 - c) • K₁ + c • K₂) (π / 2) := by
  set M := (1 - c) • K₁ + c • K₂ with hM
  have hMcb : IsConvexBody M := isConvexBody_comb h₁.2.1 h₂.2.1
  have sM : ∀ t, supp M t = (1 - c) * supp K₁ t + c * supp K₂ t := supp_comb h₁.2.1 h₂.2.1 hc
  have e2 : supp M (π / 2) = 1 := by rw [sM, h₁.2.2.2.1, h₂.2.2.2.1]; ring
  have e3 : supp M (3 * π / 2) = 0 := by rw [sM, h₁.2.2.2.2.2.1, h₂.2.2.2.2.2.1]; ring
  -- `M`, like `K₁` and `K₂`, is closed under projection to the `x`-axis
  have hproj : ∀ q ∈ M, ((q.1, 0) : ℝ × ℝ) ∈ M := by
    intro q hq
    obtain ⟨a, ha, b, hb, rfl⟩ := opt_mem_comb hq
    have := opt_comb_mem (c := c) (opt_cap_down h₁ ha le_rfl (inj_cap_strip h₁ ha).1)
      (opt_cap_down h₂ hb le_rfl (inj_cap_strip h₂ hb).1)
    convert this using 1
    ext <;> simp
  refine ⟨h₁.1, hMcb, e2, e2, by rw [show π / 2 + π = 3 * π / 2 by ring]; exact e3, e3, ?_⟩
  -- `M` is cut out by its supporting half-planes with normal angles in `[0, π] ∪ {3π/2}`
  refine ⟨{t : ℝ // t ∈ Icc 0 π ∨ t = 3 * π / 2}, fun i => i.1, fun i => supp M i.1, ?_, ?_⟩
  · rintro ⟨t, ht | ht⟩
    · simp only [jSet, mem_union, mem_Icc, mem_insert_iff, mem_singleton_iff]
      rcases le_total t (π / 2) with h | h
      · exact Or.inl (Or.inl ⟨ht.1, h⟩)
      · exact Or.inl (Or.inr ⟨h, by linarith [ht.2]⟩)
    · simp only [mem_union, mem_insert_iff, mem_singleton_iff]
      exact Or.inr (Or.inr ht)
  ext p
  simp only [mem_iInter, halfMinus, mem_ofPred_eq]
  refine ⟨fun hp i => dot_le_supp hMcb.2.1 hp i.1, fun hp => ?_⟩
  rw [mem_iff_forall_dot_le_supp hMcb]
  have h0 := hp ⟨0, Or.inl ⟨le_rfl, pi_pos.le⟩⟩
  have hpi := hp ⟨π, Or.inl ⟨pi_pos.le, le_rfl⟩⟩
  have h3 := hp ⟨3 * π / 2, Or.inr rfl⟩
  simp only [uvec_zero, uvec_pi, uvec_three_pi_div_two, dot_mk, e3] at h0 hpi h3
  intro t
  rcases le_or_gt 0 (sin t) with hs | hs
  · -- `sin t ≥ 0`: the direction `t` is the direction `arccos (cos t) ∈ [0, π]`
    have hu : uvec (arccos (cos t)) = uvec t := by
      ext
      · simp [uvec, cos_arccos (neg_one_le_cos t) (cos_le_one t)]
      · simp only [uvec, sin_arccos]
        rw [← sin_sq, Real.sqrt_sq hs]
    have := hp ⟨arccos (cos t), Or.inl ⟨arccos_nonneg _, arccos_le_pi _⟩⟩
    simp only at this
    rwa [hu, show supp M (arccos (cos t)) = supp M t by simp only [supp, hu]] at this
  · -- `sin t < 0`: compare with the projection of a point of `M` extreme in the direction `0`
    -- or `π` (according to the sign of `cos t`) to the `x`-axis
    obtain ⟨q₀, hq₀, hq₀e⟩ := exists_dot_eq_supp hMcb.2.1 hMcb.1 0
    obtain ⟨q₁, hq₁, hq₁e⟩ := exists_dot_eq_supp hMcb.2.1 hMcb.1 π
    rw [dot_uvec_zero] at hq₀e
    rw [uvec_pi] at hq₁e
    simp only [dot_mk, mul_zero, add_zero, mul_neg, mul_one] at hq₁e
    have hp2 : 0 ≤ p.2 := by linarith
    rcases le_or_gt 0 (cos t) with hcs | hcs
    · have := dot_le_supp hMcb.2.1 (hproj q₀ hq₀) t
      simp only [dot, uvec, zero_mul, add_zero] at this ⊢
      rw [hq₀e] at this
      nlinarith [mul_nonneg (sub_nonneg.mpr h0) hcs, mul_nonneg hp2 (neg_nonneg.mpr hs.le)]
    · have := dot_le_supp hMcb.2.1 (hproj q₁ hq₁) t
      simp only [dot, uvec, zero_mul, add_zero] at this ⊢
      rw [show q₁.1 = -supp M π by linarith] at this
      nlinarith [mul_nonneg (by linarith : 0 ≤ p.1 + supp M π) (neg_nonneg.mpr hcs.le),
        mul_nonneg hp2 (neg_nonneg.mpr hs.le)]

/-- The inner corner is linear under Minkowski combinations. -/
lemma opt_innerCorner_comb (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂)
    (hc : c ∈ Icc (0 : ℝ) 1) :
    innerCorner ((1 - c) • K₁ + c • K₂) = (1 - c) • innerCorner K₁ + c • innerCorner K₂ := by
  funext t
  simp only [Pi.add_apply, Pi.smul_apply, proposition2_2_2_innerCorner, supp_comb h₁ h₂ hc]
  ext <;> simp <;> ring

/-- The outer corner is linear under Minkowski combinations. -/
lemma opt_outerCorner_comb (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂)
    (hc : c ∈ Icc (0 : ℝ) 1) :
    outerCorner ((1 - c) • K₁ + c • K₂) = (1 - c) • outerCorner K₁ + c • outerCorner K₂ := by
  funext t
  simp only [Pi.add_apply, Pi.smul_apply, proposition2_2_2_outerCorner, supp_comb h₁ h₂ hc]
  ext <;> simp <;> ring

/-- The surface area measure is linear under Minkowski combinations (Theorem 7.1.2). -/
lemma opt_sigma_comb (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂) (hc : c ∈ Icc (0 : ℝ) 1) :
    sigma ((1 - c) • K₁ + c • K₂) =
      ENNReal.ofReal (1 - c) • sigma K₁ + ENNReal.ofReal c • sigma K₂ := by
  simpa [convexBodyComb, hc] using theorem7_1_2_sigma ⟨K₁, h₁⟩ ⟨K₂, h₂⟩ hc

/-- If `σ_{K₁}` and `σ_{K₂}` have densities `f₁` and `f₂` on `S`, then `σ` of their combination has
density `(1 - c) f₁ + c f₂` there. -/
lemma opt_sigma_comb_restrict (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂)
    (hc : c ∈ Icc (0 : ℝ) 1) {S : Set ℝ} {f₁ f₂ : ℝ → ℝ} (hf₁ : Measurable f₁)
    (hf₂ : Measurable f₂) (hf₁0 : ∀ t, 0 ≤ f₁ t) (hf₂0 : ∀ t, 0 ≤ f₂ t)
    (e₁ : (sigma K₁).restrict S = (volume.restrict S).withDensity fun t => ENNReal.ofReal (f₁ t))
    (e₂ : (sigma K₂).restrict S = (volume.restrict S).withDensity fun t => ENNReal.ofReal (f₂ t)) :
    (sigma ((1 - c) • K₁ + c • K₂)).restrict S = (volume.restrict S).withDensity
      fun t => ENNReal.ofReal ((1 - c) * f₁ t + c * f₂ t) := by
  rw [opt_sigma_comb h₁ h₂ hc, Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
    e₁, e₂, ← withDensity_smul _ (by fun_prop), ← withDensity_smul _ (by fun_prop),
    ← withDensity_add_left (by fun_prop)]
  congr 1
  funext t
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.ofReal_add (mul_nonneg (sub_nonneg.mpr hc.2) (hf₁0 t)) (mul_nonneg hc.1 (hf₂0 t)),
    ENNReal.ofReal_mul (sub_nonneg.mpr hc.2), ENNReal.ofReal_mul hc.1]

/-- The injectivity condition is preserved by Minkowski combinations (it is made of conditions
linear in `K`). -/
lemma opt_comb_injectivity (h₁ : IsKi K₁) (h₂ : IsKi K₂) (hc : c ∈ Icc (0 : ℝ) 1) :
    SatisfiesInjectivity ((1 - c) • K₁ + c • K₂) := by
  obtain ⟨hcap₁, ⟨⟨r₁, s₁, hr₁, hs₁, hr₁0, hs₁0, hσr₁, hσs₁⟩, i2₁, i3₁⟩, -⟩ := h₁
  obtain ⟨hcap₂, ⟨⟨r₂, s₂, hr₂, hs₂, hr₂0, hs₂0, hσr₂, hσs₂⟩, i2₂, i3₂⟩, -⟩ := h₂
  have hx := opt_innerCorner_comb hcap₁.2.1 hcap₂.2.1 hc
  -- (1) the densities of `σ` combine linearly
  refine ⟨⟨fun t => (1 - c) * r₁ t + c * r₂ t, fun t => (1 - c) * s₁ t + c * s₂ t,
    by fun_prop, by fun_prop,
    fun t => add_nonneg (mul_nonneg (sub_nonneg.mpr hc.2) (hr₁0 t)) (mul_nonneg hc.1 (hr₂0 t)),
    fun t => add_nonneg (mul_nonneg (sub_nonneg.mpr hc.2) (hs₁0 t)) (mul_nonneg hc.1 (hs₂0 t)),
    opt_sigma_comb_restrict hcap₁.2.1 hcap₂.2.1 hc hr₁ hr₂ hr₁0 hr₂0 hσr₁ hσr₂,
    opt_sigma_comb_restrict (f₁ := fun t => s₁ (t - π / 2)) (f₂ := fun t => s₂ (t - π / 2))
      hcap₁.2.1 hcap₂.2.1 hc (hs₁.comp (measurable_id.sub_const _))
      (hs₂.comp (measurable_id.sub_const _)) (fun t => hs₁0 _) (fun t => hs₂0 _) hσs₁ hσs₂⟩,
    ?_, ?_⟩
  -- (2) `𝐱_K` stays `C¹`
  · unfold InjCond2
    rw [hx]
    exact (i2₁.const_smul (1 - c)).add (i2₂.const_smul c)
  -- (3) the signs of `𝐱_K' · u_t` and `𝐱_K' · v_t` are kept
  · intro t ht
    have hd : HasDerivAt (innerCorner ((1 - c) • K₁ + c • K₂))
        ((1 - c) • deriv (innerCorner K₁) t + c • deriv (innerCorner K₂) t) t := by
      rw [hx]
      exact ((opt_inj_hasDerivAt i2₁ ht).const_smul _).add
        ((opt_inj_hasDerivAt i2₂ ht).const_smul _)
    rw [hd.deriv, dot_add_left, dot_add_left, dot_smul_left, dot_smul_left, dot_smul_left,
      dot_smul_left]
    obtain ⟨a1, b1⟩ := i3₁ t ht
    obtain ⟨a2, b2⟩ := i3₂ t ht
    refine ⟨opt_comb_neg hc a1 a2, ?_⟩
    have := opt_comb_neg hc (neg_lt_zero.mpr b1) (neg_lt_zero.mpr b2)
    linarith

/-- For `y ∈ [0, 1]`, the slice of a cap at height `y` is a nonempty compact interval
`[m, M]`. -/
private lemma opt_cap_slice (hK : IsCap K₁ (π / 2)) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    ∃ m M : ℝ, (m, y) ∈ K₁ ∧ (M, y) ∈ K₁ ∧ (fun x : ℝ => (x, y)) ⁻¹' K₁ ⊆ Icc m M := by
  have hcb := hK.2.1
  set S := (fun x : ℝ => (x, y)) ⁻¹' K₁
  have hSc : IsCompact S := isCompact_Icc.of_isClosed_subset
    (hcb.isClosed.preimage (by fun_prop)) fun x hx => opt_cap_fst_le hK hx
  -- a point of `K` at height `y`, on the segment from `A = (h_K(0), 0)` to a point at height `1`
  obtain ⟨T, hT, hTe⟩ := exists_dot_eq_supp hcb.2.1 hcb.1 (π / 2)
  rw [hK.2.2.2.1, dot_uvec_pi_div_two] at hTe
  have hP := hcb.2.2 (opt_cap_A_mem hK) hT (by linarith [hy.2] : (0 : ℝ) ≤ 1 - y) hy.1 (by ring)
  have hSne : S.Nonempty := ⟨((1 - y) • (supp K₁ 0, (0 : ℝ)) + y • T).1, by
    show (_, y) ∈ K₁
    convert hP using 1
    ext
    · rfl
    · simp [hTe]⟩
  obtain ⟨m, hm, hmmin⟩ := hSc.exists_isMinOn hSne continuous_id.continuousOn
  obtain ⟨M, hM, hMmax⟩ := hSc.exists_isMaxOn hSne continuous_id.continuousOn
  exact ⟨m, M, hm, hM, fun x hx => ⟨hmmin hx, hMmax hx⟩⟩

/-- The area of a Minkowski combination of caps is at least the combination of the areas (the
horizontal slices of the combination contain the combinations of the slices). This replaces the
paper's appeal to the Brunn–Minkowski inequality. -/
lemma opt_comb_area (h₁ : IsCap K₁ (π / 2)) (h₂ : IsCap K₂ (π / 2)) (hc : c ∈ Icc (0 : ℝ) 1) :
    (1 - c) * area K₁ + c * area K₂ ≤ area ((1 - c) • K₁ + c • K₂) := by
  set M := (1 - c) • K₁ + c • K₂ with hM
  have hcb₁ := h₁.2.1
  have hcb₂ := h₂.2.1
  have hMcb : IsConvexBody M := isConvexBody_comb hcb₁ hcb₂
  have hc0 := hc.1
  have hc1 : 0 ≤ 1 - c := sub_nonneg.mpr hc.2
  -- Step 1: slice by slice, `(1 - c) |K₁ ∩ {y}| + c |K₂ ∩ {y}| ≤ |M ∩ {y}|`.
  have hslice : ∀ y : ℝ, ENNReal.ofReal (1 - c) * volume ((fun x : ℝ => (x, y)) ⁻¹' K₁) +
      ENNReal.ofReal c * volume ((fun x : ℝ => (x, y)) ⁻¹' K₂) ≤
      volume ((fun x : ℝ => (x, y)) ⁻¹' M) := by
    intro y
    by_cases hy : y ∈ Icc (0 : ℝ) 1
    · -- the slices are intervals `[m₁, M₁]`, `[m₂, M₂]`; the slice of `M` is convex and contains
      -- the combinations of their endpoints
      obtain ⟨m₁, M₁, hm₁, hM₁, hS₁⟩ := opt_cap_slice h₁ hy
      obtain ⟨m₂, M₂, hm₂, hM₂, hS₂⟩ := opt_cap_slice h₂ hy
      have hmM : ∀ {a b : ℝ}, (a, y) ∈ K₁ → (b, y) ∈ K₂ → ((1 - c) * a + c * b, y) ∈ M := by
        intro a b ha hb
        convert opt_comb_mem (c := c) ha hb using 1
        ext
        · simp
        · simp; ring
      have hSconv : Convex ℝ ((fun x : ℝ => (x, y)) ⁻¹' M) := by
        intro x hx x' hx' a b ha hb hab
        have := hMcb.2.2 hx hx' ha hb hab
        show (a • x + b • x', y) ∈ M
        convert this using 1
        ext
        · simp
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          rw [← add_mul, hab, one_mul]
      calc ENNReal.ofReal (1 - c) * volume ((fun x : ℝ => (x, y)) ⁻¹' K₁) +
            ENNReal.ofReal c * volume ((fun x : ℝ => (x, y)) ⁻¹' K₂)
          ≤ ENNReal.ofReal (1 - c) * volume (Icc m₁ M₁) +
              ENNReal.ofReal c * volume (Icc m₂ M₂) := by
            gcongr
        _ = volume (Icc ((1 - c) * m₁ + c * m₂) ((1 - c) * M₁ + c * M₂)) := by
            have hle₁ : m₁ ≤ M₁ := (hS₁ hm₁).2
            have hle₂ : m₂ ≤ M₂ := (hS₂ hm₂).2
            rw [Real.volume_Icc, Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_mul hc1,
              ← ENNReal.ofReal_mul hc0,
              ← ENNReal.ofReal_add (mul_nonneg hc1 (by linarith)) (mul_nonneg hc0 (by linarith))]
            congr 1; ring
        _ ≤ volume ((fun x : ℝ => (x, y)) ⁻¹' M) :=
            measure_mono (hSconv.ordConnected.out (hmM hm₁ hm₂) (hmM hM₁ hM₂))
    · -- outside the strip `0 ≤ y ≤ 1` the slices of the caps are empty
      have hempty : ∀ {L : Set (ℝ × ℝ)}, IsCap L (π / 2) → (fun x : ℝ => (x, y)) ⁻¹' L = ∅ :=
        fun hL => eq_empty_of_forall_notMem fun x hx =>
          hy ⟨(inj_cap_strip hL hx).1, (inj_cap_strip hL hx).2⟩
      simp [hempty h₁, hempty h₂]
  -- Step 2: integrate over `y` (Fubini).
  have hmeas₁ : MeasurableSet K₁ := hcb₁.isClosed.measurableSet
  have hmeas₂ : MeasurableSet K₂ := hcb₂.isClosed.measurableSet
  have hvol : ENNReal.ofReal (1 - c) * volume K₁ + ENNReal.ofReal c * volume K₂ ≤ volume M := by
    rw [Measure.volume_eq_prod, Measure.prod_apply_symm hmeas₁, Measure.prod_apply_symm hmeas₂,
      Measure.prod_apply_symm hMcb.isClosed.measurableSet,
      ← lintegral_const_mul _ (measurable_measure_prodMk_right hmeas₁),
      ← lintegral_const_mul _ (measurable_measure_prodMk_right hmeas₂),
      ← lintegral_add_left ((measurable_measure_prodMk_right hmeas₁).const_mul _)]
    exact lintegral_mono hslice
  -- Step 3: pass to real numbers.
  unfold area
  have hfin₁ : volume K₁ ≠ ⊤ := hcb₁.2.1.measure_lt_top.ne
  have hfin₂ : volume K₂ ≠ ⊤ := hcb₂.2.1.measure_lt_top.ne
  have := ENNReal.toReal_mono hMcb.2.1.measure_lt_top.ne hvol
  rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin₁)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin₂), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc1, ENNReal.toReal_ofReal hc0] at this

end Comb

/-- **Theorem 8.1.1** (`thm:cap-space-special`) (1): `𝒦^i` is closed under Minkowski combinations.

Departure from the paper: the paper gets `|(1 - c) K₁ + c K₂| ≥ 2.2` from the Brunn–Minkowski
inequality; this proof uses that the horizontal slices of `(1 - c) K₁ + c K₂` contain the
combinations of the slices of `K₁` and `K₂`, which with Fubini gives
`|(1 - c) K₁ + c K₂| ≥ (1 - c) |K₁| + c |K₂|` (`opt_comb_area`), because Mathlib has no
Brunn–Minkowski inequality. -/
theorem theorem8_1_1_convex {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsKi K₁) (h₂ : IsKi K₂) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) : IsKi ((1 - c) • K₁ + c • K₂) := by
  refine ⟨opt_comb_isCap h₁.1 h₂.1 hc, opt_comb_injectivity h₁ h₂ hc,
    le_trans ?_ (opt_comb_area h₁.1 h₂.1 hc)⟩
  nlinarith [mul_le_mul_of_nonneg_left h₁.2.2 (sub_nonneg.mpr hc.2),
    mul_le_mul_of_nonneg_left h₂.2.2 hc.1]

/-- The space `𝓛` of triples `(K, B, D)` of convex bodies (Definition 8.1.3, `def:cap-tail-space`),
for the core angle `φ` (so `φ^R = φ`, `φ^L = π/2 - φ`). -/
def InL (φ : ℝ) (K B D : Set (ℝ × ℝ)) : Prop :=
  IsKi K ∧ IsConvexBody B ∧ IsConvexBody D ∧ B ⊆ K ∧ D ⊆ K ∧
    (∀ t ∈ Icc φ (π / 2), supp K t + supp B (π + t) ≤ 1) ∧
    supp K φ + supp B (π + φ) = 1 ∧ supp K (π / 2) + supp B (π + π / 2) = 1 ∧
    (∀ t ∈ Icc 0 (π / 2 - φ), supp K (π / 2 + t) + supp D (3 * π / 2 + t) ≤ 1) ∧
    supp K (π / 2 + 0) + supp D (3 * π / 2 + 0) = 1 ∧
    supp K (π / 2 + (π / 2 - φ)) + supp D (3 * π / 2 + (π / 2 - φ)) = 1

/-- The tails of a triple of `𝓛` touch the lines `l(π/2, 0)`, `b_K^R` and `d_K^L`:
`h_B(3π/2) = h_D(3π/2) = 0`, `h_B(π + φ) = 1 - h_K(φ)` and `h_D(3π/2 + φ^L) = 1 - h_K(π - φ)`. -/
lemma opt_inL_supp {φ : ℝ} {K B D : Set (ℝ × ℝ)} (h : InL φ K B D) :
    supp B (3 * π / 2) = 0 ∧ supp D (3 * π / 2) = 0 ∧ supp B (π + φ) = 1 - supp K φ ∧
      supp D (3 * π / 2 + (π / 2 - φ)) = 1 - supp K (π - φ) := by
  obtain ⟨hK, -, -, -, -, -, e1, e1', -, e2, e2'⟩ := h
  have hK2 : supp K (π / 2) = 1 := hK.1.2.2.2.1
  rw [add_zero, add_zero, hK2] at e2
  rw [hK2, show π + π / 2 = 3 * π / 2 by ring] at e1'
  rw [show π / 2 + (π / 2 - φ) = π - φ by ring] at e2'
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **Proposition 8.1.2** (`pro:cap-tail-space`). `𝓛` is closed under the componentwise Minkowski
combinations, so it is a convex domain. -/
theorem proposition8_1_2 {φ : ℝ} {K₁ B₁ D₁ K₂ B₂ D₂ : Set (ℝ × ℝ)} (h₁ : InL φ K₁ B₁ D₁)
    (h₂ : InL φ K₂ B₂ D₂) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    InL φ ((1 - c) • K₁ + c • K₂) ((1 - c) • B₁ + c • B₂) ((1 - c) • D₁ + c • D₂) := by
  obtain ⟨hK₁, hB₁, hD₁, hBK₁, hDK₁, i1, e1, e1', i2, e2, e2'⟩ := h₁
  obtain ⟨hK₂, hB₂, hD₂, hBK₂, hDK₂, j1, f1, f1', j2, f2, f2'⟩ := h₂
  have sK := supp_comb hK₁.1.2.1 hK₂.1.2.1 hc
  have sB := supp_comb hB₁ hB₂ hc
  have sD := supp_comb hD₁ hD₂ hc
  have hc0 := hc.1
  have hc1 : 0 ≤ 1 - c := sub_nonneg.mpr hc.2
  refine ⟨theorem8_1_1_convex hK₁ hK₂ hc, isConvexBody_comb hB₁ hB₂,
    isConvexBody_comb hD₁ hD₂, Set.add_subset_add (Set.smul_set_mono hBK₁) (Set.smul_set_mono hBK₂),
    Set.add_subset_add (Set.smul_set_mono hDK₁) (Set.smul_set_mono hDK₂), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [sK, sB]
    nlinarith [mul_le_mul_of_nonneg_left (i1 t ht) hc1, mul_le_mul_of_nonneg_left (j1 t ht) hc0]
  · rw [sK, sB]; linear_combination (1 - c) * e1 + c * f1
  · rw [sK, sB]; linear_combination (1 - c) * e1' + c * f1'
  · intro t ht
    rw [sK, sD]
    nlinarith [mul_le_mul_of_nonneg_left (i2 t ht) hc1, mul_le_mul_of_nonneg_left (j2 t ht) hc0]
  · rw [sK, sD]; linear_combination (1 - c) * e2 + c * f2
  · rw [sK, sD]; linear_combination (1 - c) * e2' + c * f2'

/-- The elements of `𝓛`. -/
def LTriple (φ : ℝ) : Type :=
  {x : ConvexBodySet × ConvexBodySet × ConvexBodySet // InL φ x.1.1 x.2.1.1 x.2.2.1}

open Classical in
/-- The componentwise barycentric operation on `𝓛`. -/
noncomputable def LTriple.comb {φ : ℝ} (c : ℝ) (x y : LTriple φ) : LTriple φ :=
  if hc : c ∈ Icc (0 : ℝ) 1 then
    ⟨(convexBodyComb c x.1.1 y.1.1, convexBodyComb c x.1.2.1 y.1.2.1,
        convexBodyComb c x.1.2.2 y.1.2.2), by
      simpa [convexBodyComb, hc] using proposition8_1_2 x.2 y.2 hc⟩
  else x

/-- `𝓛` as a convex domain (Proposition 8.1.2). -/
theorem lTriple_embeds (φ : ℝ) :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℝ E) (e : LTriple φ → E), Function.Injective e ∧
      ∀ c ∈ Icc (0 : ℝ) 1, ∀ v w, e (LTriple.comb c v w) = (1 - c) • e v + c • e w := by
  obtain ⟨E, i1, i2, e, he, hlin⟩ := theorem7_1_1
  refine ⟨E × E × E, inferInstance, inferInstance,
    fun x => (e x.1.1, e x.1.2.1, e x.1.2.2), ?_, ?_⟩
  · intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2, h3⟩ := hxy
    apply Subtype.ext
    exact Prod.ext (he h1) (Prod.ext (he h2) (he h3))
  · intro c hc v w
    simp only [LTriple.comb, hc, ↓reduceDIte]
    rw [hlin c hc, hlin c hc, hlin c hc]
    simp only [Prod.smul_mk, Prod.mk_add_mk]

/-- The convex domain `𝓛` (Proposition 8.1.2). -/
noncomputable def lDomain (φ : ℝ) : ConvexDomain (LTriple φ) where
  comb := LTriple.comb
  embeds := lTriple_embeds φ

/-- `B_K = K ∩ ⋂_{t ∈ [φ^R, π/2]} H_K^b(t)` (Definition 8.1.4, `def:right-left-body`). -/
def rightBody (φ : ℝ) (K : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := K ∩ ⋂ t ∈ Icc φ (π / 2), halfB K t

/-- `D_K = K ∩ ⋂_{t ∈ [0, φ^L]} H_K^d(t)` (Definition 8.1.4). -/
def leftBody (φ : ℝ) (K : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := K ∩ ⋂ t ∈ Icc 0 (π / 2 - φ), halfD K t

/-- The half-plane `H̆_K^R = H_K^b(φ^R)` bounded from below by `b_K^R = b_K(φ^R)`
(Definition 8.1.5, `def:cap-left-right`). -/
def hRight (φ : ℝ) (K : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := halfB K φ
/-- The half-plane `H̆_K^L = H_K^d(φ^L)` bounded from below by `d_K^L = d_K(φ^L)`
(Definition 8.1.5). -/
def hLeft (φ : ℝ) (K : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := halfD K (π / 2 - φ)
/-- `W_K^R = W_K(φ^R)` (Definition 8.1.5). -/
noncomputable def wRight (φ : ℝ) (K : Set (ℝ × ℝ)) : ℝ × ℝ := wedgeW K φ
/-- `𝐱_K^R = 𝐱_K(φ^R)` (Definition 8.1.5). -/
noncomputable def xRight (φ : ℝ) (K : Set (ℝ × ℝ)) : ℝ × ℝ := innerCorner K φ
/-- `Z_K^L = Z_K(φ^L)` (Definition 8.1.5). -/
noncomputable def zLeft (φ : ℝ) (K : Set (ℝ × ℝ)) : ℝ × ℝ := wedgeZ K (π / 2) (π / 2 - φ)
/-- `𝐱_K^L = 𝐱_K(φ^L)` (Definition 8.1.5). -/
noncomputable def xLeft (φ : ℝ) (K : Set (ℝ × ℝ)) : ℝ × ℝ := innerCorner K (π / 2 - φ)

/-- The parallelogram `P_K^R = H ∩ H_K(φ^R) ∩ H̆_K^R` (Definition 8.1.6). -/
def paraR (φ : ℝ) (K : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := hStrip ∩ suppHalf K φ ∩ hRight φ K
/-- The parallelogram `P_K^L = H ∩ H_K(π/2 + φ^L) ∩ H̆_K^L` (Definition 8.1.6). -/
def paraL (φ : ℝ) (K : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  hStrip ∩ suppHalf K (π / 2 + (π / 2 - φ)) ∩ hLeft φ K

/-! ### Auxiliary facts on `B_K`, `D_K`, `W_K^R`, `Z_K^L` -/

/-- `W_K^R = ((h_K(φ) - 1) / cos φ, 0)`. -/
lemma opt_wRight_eq (φ : ℝ) (K : Set (ℝ × ℝ)) : wRight φ K = ((supp K φ - 1) / cos φ, 0) := rfl

/-- `Z_K^L = ((1 - h_K(π - φ)) / cos φ, 0)`. -/
lemma opt_zLeft_eq (φ : ℝ) (K : Set (ℝ × ℝ)) :
    zLeft φ K = ((1 - supp K (π - φ)) / cos φ, 0) := by
  simp only [zLeft, wedgeZ, vvec_pi_div_two, show π / 2 - (π / 2 - φ) = φ by ring,
    show π / 2 - φ + π / 2 = π - φ by ring]
  ext
  · simp only [Prod.smul_mk, smul_eq_mul]; ring
  · simp

/-- The corner `A = (h_K(0), 0)` lies in `B_K`. -/
lemma opt_rightBody_A_mem {φ : ℝ} (hφ : 0 ≤ φ) {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) :
    (supp K 0, (0 : ℝ)) ∈ rightBody φ K := by
  refine ⟨opt_cap_A_mem hK, ?_⟩
  simp only [mem_iInter₂]
  intro t ht
  exact opt_cap_A_mem_halfB hK ⟨le_trans hφ ht.1, ht.2⟩

/-- The corner `C = (-h_K(π), 0)` lies in `D_K`. -/
lemma opt_leftBody_C_mem {φ : ℝ} (hφ : 0 ≤ φ) {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) :
    (-supp K π, (0 : ℝ)) ∈ leftBody φ K := by
  refine ⟨opt_cap_C_mem hK, ?_⟩
  simp only [mem_iInter₂]
  intro t ht
  exact opt_cap_C_mem_halfD hK ⟨ht.1, by linarith [ht.2]⟩

/-- `B_K` is a convex body. -/
lemma opt_rightBody_isConvexBody {φ : ℝ} (hφ : 0 ≤ φ) {K : Set (ℝ × ℝ)}
    (hK : IsCap K (π / 2)) : IsConvexBody (rightBody φ K) := by
  refine ⟨⟨_, opt_rightBody_A_mem hφ hK⟩, ?_, ?_⟩
  · exact hK.2.1.2.1.inter_right
      (isClosed_biInter fun t _ => isClosed_halfPlus t (supp K t - 1))
  · exact hK.2.1.2.2.inter (convex_iInter₂ fun t _ => convex_halfPlus t (supp K t - 1))

/-- `D_K` is a convex body. -/
lemma opt_leftBody_isConvexBody {φ : ℝ} (hφ : 0 ≤ φ) {K : Set (ℝ × ℝ)}
    (hK : IsCap K (π / 2)) : IsConvexBody (leftBody φ K) := by
  refine ⟨⟨_, opt_leftBody_C_mem hφ hK⟩, ?_, ?_⟩
  · exact hK.2.1.2.1.inter_right
      (isClosed_biInter fun t _ => isClosed_halfPlus (t + π / 2) (supp K (t + π / 2) - 1))
  · exact hK.2.1.2.2.inter
      (convex_iInter₂ fun t _ => convex_halfPlus (t + π / 2) (supp K (t + π / 2) - 1))

/-- **Lemma 8.1.3** (`lem:cap-right-left-parallelogram`). `P_K^R` is the parallelogram bounded by
`l(π/2, 0)`, `l(π/2, 1)`, `a_K(φ^R)` and `b_K(φ^R)`, with base `sec φ` on `l(π/2, 0)` starting at
its lower-left corner `W_K^R`. -/
theorem lemma8_1_3 {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) (K : Set (ℝ × ℝ)) :
    paraR φ K =
        {p | 0 ≤ p.2 ∧ p.2 ≤ 1 ∧ supp K φ - 1 ≤ dot p (uvec φ) ∧ dot p (uvec φ) ≤ supp K φ} ∧
      paraR φ K ∩ line (π / 2) 0 = segment ℝ (wRight φ K) (wRight φ K + (1 / cos φ, 0)) := by
  have hc : 0 < cos φ :=
    cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, pi_pos], by linarith [hφ.2, pi_pos]⟩
  have h1 : paraR φ K = {p | 0 ≤ p.2 ∧ p.2 ≤ 1 ∧ supp K φ - 1 ≤ dot p (uvec φ) ∧
      dot p (uvec φ) ≤ supp K φ} := by
    ext p
    simp only [paraR, hStrip, suppHalf, hRight, halfB, halfMinus, halfPlus, mem_inter_iff,
      mem_ofPred_eq]
    tauto
  refine ⟨h1, ?_⟩
  rw [h1, segment_eq_image', opt_wRight_eq]
  ext p
  simp only [mem_inter_iff, mem_ofPred_eq, line, uvec_pi_div_two, dot_mk, mem_image,
    mem_Icc, add_sub_cancel_left, mul_zero, mul_one, zero_add]
  constructor
  · rintro ⟨⟨-, -, h3, h4⟩, hp2⟩
    simp only [dot, uvec, hp2, zero_mul, add_zero] at h3 h4
    refine ⟨p.1 * cos φ - (supp K φ - 1), ⟨by linarith, by linarith⟩, ?_⟩
    ext
    · simp only [Prod.fst_add, Prod.smul_mk, smul_eq_mul]; field_simp; ring
    · simp [hp2]
  · rintro ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
    simp only [dot, uvec, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul, mul_zero,
      add_zero, zero_mul]
    have e : ((supp K φ - 1) / cos φ + θ * (1 / cos φ)) * cos φ = supp K φ - 1 + θ := by
      field_simp
    rw [e]
    exact ⟨⟨le_refl _, zero_le_one, by linarith, by linarith⟩, trivial⟩

/-- **Lemma 8.1.4** (`lem:cap-left-right-disjoint`). For `K ∈ 𝒦^i`, `K ∩ H̆_K^R` and `K ∩ H̆_K^L`
are disjoint. -/
theorem lemma8_1_4 {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)} (hK : IsKi K) :
    Disjoint (K ∩ hRight φ K) (K ∩ hLeft φ K) := by
  obtain ⟨hφ0, hφ4, hs4, hc9, hs0⟩ := opt_phi_bounds hφ
  have hc : 0 < cos φ := by linarith
  have hcap := hK.1
  rw [Set.disjoint_left]
  rintro p ⟨hpK, hpR⟩ ⟨-, hpL⟩
  simp only [hRight, hLeft, halfB, halfD, halfPlus, mem_ofPred_eq,
    show π / 2 - φ + π / 2 = π - φ by ring] at hpR hpL
  simp only [dot, uvec, cos_pi_sub, sin_pi_sub] at hpR hpL
  -- adding the two constraints at a point of height `≤ 1` gives
  -- `h_K(φ) + h_K(π - φ) ≤ 2 + 2 sin φ`, while `h_K(φ) + h_K(π - φ) ≥ |K| cos φ ≥ 2.2 cos φ`
  have hp2 := inj_cap_strip hcap hpK
  have hsum : supp K φ + supp K (π - φ) ≤ 2 + 2 * sin φ := by nlinarith
  have h3 := opt_area_mul_cos_le hcap hc hs0.le
  nlinarith [mul_le_mul_of_nonneg_right hK.2.2 hc.le]

/-- `1 ≤ sin t + cos t` and `2 sin t cos t ≤ 1` when `sin t, cos t ≥ 0`. -/
lemma opt_sin_cos_bounds {t : ℝ} (hs : 0 ≤ sin t) (hc : 0 ≤ cos t) :
    1 ≤ sin t + cos t ∧ 2 * (sin t * cos t) ≤ 1 := by
  have e := sin_sq_add_cos_sq t
  constructor
  · nlinarith [mul_nonneg hs (sub_nonneg.mpr (sin_le_one t)),
      mul_nonneg hc (sub_nonneg.mpr (cos_le_one t))]
  · nlinarith [sq_nonneg (sin t - cos t)]

/-- `𝒩(K) ∩ H̆_K^R` and `H̆_K^L` are disjoint. Adding the inequalities of `H̆_K^R` and `H̆_K^L`
gives height at least `(h_K(φ) + h_K(π - φ) - 2) / (2 sin φ) ≥ (W₀ cos φ - 2) / (2 sin φ)`, where
`W₀ = h_K(0) + h_K(π) ≥ |K| ≥ 2.2` is the bottom width; a point of `𝒩(K)` lies in some `Q_K⁻(t)`,
below the inner corner `𝐱_K(t)`, whose height is at most `W₀ sin t cos t ≤ W₀ / 2`. -/
lemma opt_niche_hRight_hLeft {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)}
    (hK : IsKi K) : Disjoint (niche K (π / 2) ∩ hRight φ K) (hLeft φ K) := by
  obtain ⟨hφ0, hφ4, hs4, hc9, hs0⟩ := opt_phi_bounds hφ
  have hpi := two_le_pi
  have hcap := hK.1
  have hcb := hcap.2.1
  -- the bottom width `W₀ = h_K(0) + h_K(π)` is at least `|K| ≥ 2.2`
  have hW : 2.2 ≤ supp K 0 + supp K π := by
    have := opt_area_le_of_fst_bounds hcap (a := -supp K π) (b := supp K 0)
      (fun q hq => opt_cap_fst_le hcap hq)
    linarith [hK.2.2]
  -- `h_K(φ) + h_K(π - φ) ≥ W₀ cos φ`, from the bottom corners `A` and `C`
  have hA := dot_le_supp hcb.2.1 (opt_cap_A_mem hcap) φ
  have hC := dot_le_supp hcb.2.1 (opt_cap_C_mem hcap) (π - φ)
  simp only [dot, uvec, cos_pi_sub, sin_pi_sub, zero_mul, add_zero] at hA hC
  rw [Set.disjoint_left]
  rintro q ⟨⟨-, hU⟩, hqR⟩ hqL
  simp only [hRight, hLeft, halfB, halfD, halfPlus, mem_ofPred_eq,
    show π / 2 - φ + π / 2 = π - φ by ring] at hqR hqL
  simp only [dot, uvec, cos_pi_sub, sin_pi_sub] at hqR hqL
  -- the point lies in some `Q_K⁻(t)`
  simp only [mem_iUnion] at hU
  obtain ⟨t, ht, hqt⟩ := hU
  rw [proposition2_2_2_qMinus] at hqt
  simp only [mem_inter_iff, halfMinusOpen, mem_ofPred_eq, uvec_add_pi_div_two] at hqt
  obtain ⟨hq1, hq2⟩ := hqt
  have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1], ht.2⟩
  have hst : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2])
  obtain ⟨hsc1, hsc2⟩ := opt_sin_cos_bounds hst.le hct.le
  -- `h_K(t) ≤ h_K(0) cos t + sin t` and `h_K(t + π/2) ≤ h_K(π) sin t + cos t`
  obtain ⟨r, hr, hrt⟩ := exists_dot_eq_supp hcb.2.1 hcb.1 t
  obtain ⟨r', hr', hrt'⟩ := exists_dot_eq_supp hcb.2.1 hcb.1 (t + π / 2)
  have hr1 := opt_cap_fst_le hcap hr
  have hr2 := inj_cap_strip hcap hr
  have hr1' := opt_cap_fst_le hcap hr'
  have hr2' := inj_cap_strip hcap hr'
  rw [uvec_add_pi_div_two] at hrt'
  simp only [dot, uvec, vvec] at hrt hrt'
  have ha : supp K t ≤ supp K 0 * cos t + sin t := by
    linarith [mul_le_mul_of_nonneg_right hr1.2 hct.le, mul_le_mul_of_nonneg_right hr2.2 hst.le]
  have hb : supp K (t + π / 2) ≤ supp K π * sin t + cos t := by
    linarith [mul_le_mul_of_nonneg_right hr1'.1 hst.le, mul_le_mul_of_nonneg_right hr2'.2 hct.le]
  -- the height of the point is below that of `𝐱_K(t)`, at most `W₀ / 2`
  have hyq : q.2 = dot q (uvec t) * sin t + dot q (vvec t) * cos t := by
    simp only [dot, uvec, vvec]
    linear_combination q.2 * (sin_sq_add_cos_sq t).symm
  have hy : q.2 < (supp K t - 1) * sin t + (supp K (t + π / 2) - 1) * cos t := by
    rw [hyq]
    linarith [mul_lt_mul_of_pos_right hq1 hst, mul_lt_mul_of_pos_right hq2 hct]
  have hyW : q.2 < (supp K 0 + supp K π) / 2 := by
    have e := sin_sq_add_cos_sq t
    have h1 := mul_le_mul_of_nonneg_right (sub_le_sub_right ha 1) hst.le
    have h2 := mul_le_mul_of_nonneg_right (sub_le_sub_right hb 1) hct.le
    have h3 := mul_nonneg (by linarith : (0 : ℝ) ≤ supp K 0 + supp K π)
      (by linarith : (0 : ℝ) ≤ 1 - 2 * (sin t * cos t))
    linarith
  -- but on `H̆_K^R ∩ H̆_K^L` the height is at least `(W₀ cos φ - 2) / (2 sin φ) > W₀ / 2`
  have hcs : (0.9592 : ℝ) ≤ cos φ - sin φ := by linarith
  have h4 := mul_lt_mul_of_pos_right hyW hs0
  have h5 := mul_le_mul hW hcs (by norm_num) (by linarith : (0 : ℝ) ≤ supp K 0 + supp K π)
  linarith

/-- A point strictly inside the bottom edge of a cap lies on `e_K(3π/2)` and is not an endpoint. -/
lemma opt_mem_bottom_edge {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) {x : ℝ}
    (h1 : -supp K π < x) (h2 : x < supp K 0) :
    ((x, 0) : ℝ × ℝ) ∈ edge K (3 * π / 2) \ {aK K 0, cK K (π / 2)} := by
  have hA : aK K 0 = (supp K 0, 0) := (inj_cap_consecutive hK).1
  have hC : cK K (π / 2) = (-supp K π, 0) := by
    rw [cK, cPlus, add_halves]; exact opt_cap_vplus_pi hK
  rw [hA, hC]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- `(x, 0)` lies on the segment from `C` to `A`
    have hA := opt_cap_A_mem hK
    have hC := opt_cap_C_mem hK
    have hden : 0 < supp K 0 + supp K π := by linarith
    set θ := (x + supp K π) / (supp K 0 + supp K π) with hθ
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hden.le
    have hθ1 : θ ≤ 1 := (div_le_one hden).mpr (by linarith)
    have := hK.2.1.2.2 hC hA (by linarith : (0 : ℝ) ≤ 1 - θ) hθ0 (by ring)
    convert this using 1
    ext
    · simp only [Prod.fst_add, Prod.smul_mk, smul_eq_mul]
      rw [hθ]; field_simp; ring
    · simp
  · simp [suppLine, line, hK.2.2.2.2.2.1, uvec_three_pi_div_two]
  · simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq, not_or]
    exact ⟨fun h => by linarith [h.1], fun h => by linarith [h.1]⟩

/-- **Lemma 8.1.5** (`lem:cap-wz-in-edge`). For `K ∈ 𝒦^i`, `W_K^R` and `Z_K^L` lie on the edge
`e_K(3π/2)` but are not its endpoints `A_K(0)` and `C_K(π/2)`. -/
theorem lemma8_1_5 {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)} (hK : IsKi K) :
    wRight φ K ∈ edge K (3 * π / 2) \ {aK K 0, cK K (π / 2)} ∧
      zLeft φ K ∈ edge K (3 * π / 2) \ {aK K 0, cK K (π / 2)} := by
  obtain ⟨hφ0, hφ4, hs4, hc9, hs0⟩ := opt_phi_bounds hφ
  have hc : 0 < cos φ := by linarith
  have hcap := hK.1
  have hKa := hK.2.2
  have hpi := two_le_pi
  have hφ' : φ ∈ Ioo 0 (π / 2) := ⟨hφ0, by linarith⟩
  have hψ' : π / 2 - φ ∈ Ioo 0 (π / 2) := ⟨by linarith, by linarith⟩
  have hinv : 1 / cos φ < 2.2 := by rw [div_lt_iff₀ hc]; linarith
  constructor
  · rw [opt_wRight_eq]
    apply opt_mem_bottom_edge hcap
    · by_contra hle
      push Not at hle
      have := opt_area_le_of_fst_bounds hcap (a := -supp K π) (b := supp K φ / cos φ)
        (fun q hq => ⟨(opt_cap_fst_le hcap hq).1, (opt_cap_fst_le_phi hcap hc hs0.le hq).2⟩)
      have e : supp K φ / cos φ = (supp K φ - 1) / cos φ + 1 / cos φ := by ring
      linarith
    · have := (theorem2_5_5_supp hcap hφ').1
      rw [div_lt_iff₀ hc]; linarith
  · rw [opt_zLeft_eq]
    apply opt_mem_bottom_edge hcap
    · have := (theorem2_5_5_supp hcap hψ').2
      rw [show π / 2 - φ + π / 2 = π - φ by ring, add_halves, sub_sub_cancel] at this
      rw [lt_div_iff₀ hc]; linarith
    · by_contra hle
      push Not at hle
      have := opt_area_le_of_fst_bounds hcap (a := -supp K (π - φ) / cos φ) (b := supp K 0)
        (fun q hq => ⟨(opt_cap_fst_le_phi hcap hc hs0.le hq).1, (opt_cap_fst_le hcap hq).2⟩)
      have e : -supp K (π - φ) / cos φ = (1 - supp K (π - φ)) / cos φ - 1 / cos φ := by ring
      linarith

/-- `t ↦ 𝐱_K(t) · u_φ` decreases strictly on `[φ, π/2]`, so `𝐱_K(t) · u_φ < h_K(φ) - 1` for
`t ∈ (φ, π/2]`. -/
lemma opt_innerCorner_lt_right {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) {K : Set (ℝ × ℝ)} (hK : IsKi K)
    {t : ℝ} (ht : t ∈ Ioc φ (π / 2)) : dot (innerCorner K t) (uvec φ) < supp K φ - 1 := by
  obtain ⟨-, ⟨-, h2, h3⟩, -⟩ := hK
  have hpi := pi_pos
  have hmono : StrictAntiOn (fun s => dot (innerCorner K s) (uvec φ)) (Icc φ (π / 2)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · exact continuousOn_dot (h2.continuousOn.mono (Icc_subset_Icc_left hφ.1.le)) _
    · intro s hs
      rw [interior_Icc] at hs
      have hs' : s ∈ Ioo 0 (π / 2) := ⟨lt_trans hφ.1 hs.1, hs.2⟩
      rw [(hasDerivAt_dot (opt_inj_hasDerivAt h2 hs') (uvec φ)).deriv,
        dot_uvec_eq_cos_add_sin _ φ s]
      obtain ⟨hu, hv⟩ := h3 s hs'
      have hc : 0 < cos (φ - s) :=
        cos_pos_of_mem_Ioo ⟨by linarith [hs.1, hs.2, hφ.1], by linarith [hs.1]⟩
      have hsn : sin (φ - s) < 0 :=
        sin_neg_of_neg_of_neg_pi_lt (by linarith [hs.1]) (by linarith [hs.2, hφ.1])
      nlinarith [mul_pos hc (neg_pos.mpr hu), mul_pos (neg_pos.mpr hsn) hv]
  have := hmono ⟨le_rfl, by linarith [hφ.2]⟩ ⟨ht.1.le, ht.2⟩ ht.1
  simpa [(cn_innerCorner_dot K φ).1] using this

/-- `t ↦ 𝐱_K(t) · v_{φ^L}` increases strictly on `[0, φ^L]`. -/
lemma opt_innerCorner_lt_left {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) {K : Set (ℝ × ℝ)} (hK : IsKi K)
    {t : ℝ} (ht : t ∈ Ico 0 (π / 2 - φ)) :
    dot (innerCorner K t) (vvec (π / 2 - φ)) < supp K (π / 2 - φ + π / 2) - 1 := by
  obtain ⟨-, ⟨-, h2, h3⟩, -⟩ := hK
  have hpi := pi_pos
  have hmono : StrictMonoOn (fun s => dot (innerCorner K s) (vvec (π / 2 - φ)))
      (Icc 0 (π / 2 - φ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact continuousOn_dot
        (h2.continuousOn.mono (Icc_subset_Icc_right (by linarith [hφ.1]))) _
    · intro s hs
      rw [interior_Icc] at hs
      have hs' : s ∈ Ioo 0 (π / 2) := ⟨hs.1, by linarith [hs.2, hφ.1]⟩
      rw [(hasDerivAt_dot (opt_inj_hasDerivAt h2 hs') _).deriv, opt_dot_frame_v _ _ s]
      obtain ⟨hu, hv⟩ := h3 s hs'
      have hc : 0 < cos (π / 2 - φ - s) :=
        cos_pos_of_mem_Ioo ⟨by linarith [hs.2], by linarith [hs.1, hφ.1]⟩
      have hsn : 0 < sin (π / 2 - φ - s) :=
        sin_pos_of_pos_of_lt_pi (by linarith [hs.2]) (by linarith [hs.1, hφ.1])
      nlinarith [mul_pos hsn (neg_pos.mpr hu), mul_pos hc hv]
  have := hmono ⟨ht.1, ht.2.le⟩ ⟨by linarith [ht.1, ht.2], le_rfl⟩ ht.2
  simpa [opt_innerCorner_dot_v] using this

/-- **Lemma 8.1.6** (`lem:monotonicity-intervals`) (1). For `K ∈ 𝒦^i` and `t ∈ (φ^R, π/2]`, the
inner corner `𝐱_K(t)` is outside `H̆_K^R`, `H̆_K^R ∩ Q_K⁻(t) = H̆_K^R \ H_K^b(t)`, and
`H̆_K^R ∩ T_K(t) = H̆_K^R ∩ H₊(π/2, 0) \ H_K^b(t)`. -/
theorem lemma8_1_6_right {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) {K : Set (ℝ × ℝ)} (hK : IsKi K) {t : ℝ}
    (ht : t ∈ Ioc φ (π / 2)) :
    innerCorner K t ∉ hRight φ K ∧ hRight φ K ∩ qMinus K t = hRight φ K \ halfB K t ∧
      hRight φ K ∩ wedge K (π / 2) t = (hRight φ K ∩ halfPlus (π / 2) 0) \ halfB K t := by
  have hlt := opt_innerCorner_lt_right hφ hK ht
  have hpi := pi_pos
  have h2 : hRight φ K ∩ qMinus K t = hRight φ K \ halfB K t := by
    ext p
    simp only [hRight, halfB, halfPlus, mem_inter_iff, mem_sdiff, mem_ofPred_eq,
      proposition2_2_2_qMinus, halfMinusOpen, not_le, uvec_add_pi_div_two]
    constructor
    · rintro ⟨hp, h1, -⟩; exact ⟨hp, h1⟩
    · rintro ⟨hp, h1⟩
      refine ⟨hp, h1, ?_⟩
      by_contra hcon
      push Not at hcon
      have e1 := dot_uvec_eq_cos_add_sin p φ t
      have e2 := dot_uvec_eq_cos_add_sin (innerCorner K t) φ t
      rw [(cn_innerCorner_dot K t).1, opt_innerCorner_dot_v] at e2
      have hc : 0 ≤ cos (φ - t) :=
        (cos_pos_of_mem_Ioo ⟨by linarith [ht.2, hφ.1], by linarith [ht.1]⟩).le
      have hsn : sin (φ - t) ≤ 0 :=
        (sin_neg_of_neg_of_neg_pi_lt (by linarith [ht.1]) (by linarith [ht.2, hφ.1])).le
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hc
          (by linarith : dot p (uvec t) - (supp K t - 1) ≤ 0),
        mul_nonpos_of_nonpos_of_nonneg hsn
          (by linarith : 0 ≤ dot p (vvec t) - (supp K (t + π / 2) - 1))]
  refine ⟨?_, h2, ?_⟩
  · simp only [hRight, halfB, halfPlus, mem_ofPred_eq, not_le]; exact hlt
  · ext p
    have h2' := Set.ext_iff.mp h2 p
    simp only [wedge, fan, mem_inter_iff, mem_sdiff] at h2' ⊢
    tauto

/-- **Lemma 8.1.6** (`lem:monotonicity-intervals`) (2), the mirror statement for `t ∈ [0, φ^L)`. -/
theorem lemma8_1_6_left {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) {K : Set (ℝ × ℝ)} (hK : IsKi K) {t : ℝ}
    (ht : t ∈ Ico 0 (π / 2 - φ)) :
    innerCorner K t ∉ hLeft φ K ∧ hLeft φ K ∩ qMinus K t = hLeft φ K \ halfD K t ∧
      hLeft φ K ∩ wedge K (π / 2) t = (hLeft φ K ∩ halfPlus (π / 2) 0) \ halfD K t := by
  have hlt := opt_innerCorner_lt_left hφ hK ht
  have hpi := pi_pos
  have h2 : hLeft φ K ∩ qMinus K t = hLeft φ K \ halfD K t := by
    ext p
    simp only [hLeft, halfD, halfPlus, mem_inter_iff, mem_sdiff, mem_ofPred_eq,
      proposition2_2_2_qMinus, halfMinusOpen, not_le, uvec_add_pi_div_two]
    constructor
    · rintro ⟨hp, -, h1⟩; exact ⟨hp, h1⟩
    · rintro ⟨hp, h1⟩
      refine ⟨hp, ?_, h1⟩
      by_contra hcon
      push Not at hcon
      have e1 := opt_dot_frame_v p (π / 2 - φ) t
      have e2 := opt_dot_frame_v (innerCorner K t) (π / 2 - φ) t
      rw [(cn_innerCorner_dot K t).1, opt_innerCorner_dot_v] at e2
      have hc : 0 < cos (π / 2 - φ - t) :=
        cos_pos_of_mem_Ioo ⟨by linarith [ht.2], by linarith [ht.1, hφ.1]⟩
      have hsn : 0 ≤ sin (π / 2 - φ - t) :=
        (sin_pos_of_pos_of_lt_pi (by linarith [ht.2]) (by linarith [ht.1, hφ.1])).le
      nlinarith [mul_nonneg hsn (by linarith : 0 ≤ dot p (uvec t) - (supp K t - 1)),
        mul_neg_of_pos_of_neg hc
          (by linarith : dot p (vvec t) - (supp K (t + π / 2) - 1) < 0)]
  refine ⟨?_, h2, ?_⟩
  · simp only [hLeft, halfD, halfPlus, mem_ofPred_eq, not_le, uvec_add_pi_div_two]; exact hlt
  · ext p
    have h2' := Set.ext_iff.mp h2 p
    simp only [wedge, fan, mem_inter_iff, mem_sdiff] at h2' ⊢
    tauto

/-- **Lemma 8.1.7** (`lem:right-left-body`) (1): `h_K(t) + h_B(π + t) ≤ 1` on `[φ^R, π/2]`.

**Added hypothesis `φ ∈ [0.039, 0.04]`** (as in the sibling lemmas; `0 ≤ φ` would suffice). Without
it the statement fails: for `φ = -π` the half-planes
`H_K^b(-π)` and `H_K^b(0)` are the strips `x ≤ 1 - h_K(π)` and `x ≥ h_K(0) - 1`, disjoint since
`h_K(0) + h_K(π) ≥ |K| ≥ 2.2 > 2`; so `B_K = ∅`, `h_B = 0`, and the inequality at `t = 0` would say
`h_K(0) ≤ 1`, false for a horizontal translate of a cap of `𝒦^i` with `h_K(0) > 1`. -/
theorem lemma8_1_7_one {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)} (hK : IsKi K)
    {t : ℝ} (ht : t ∈ Icc φ (π / 2)) : supp K t + supp (rightBody φ K) (π + t) ≤ 1 := by
  -- every point of `B_K` lies in `H_K^b(t)`, i.e. `p · u_{π + t} ≤ 1 - h_K(t)`
  have : supp (rightBody φ K) (π + t) ≤ 1 - supp K t := by
    refine supp_le_of_forall ⟨_, opt_rightBody_A_mem (by linarith [hφ.1] : 0 ≤ φ) hK.1⟩
      fun p hp => ?_
    have hpt : p ∈ halfB K t := (mem_iInter₂.mp hp.2) t ht
    simp only [halfB, halfPlus, mem_ofPred_eq] at hpt
    rw [add_comm, dot_uvec_add_pi]
    linarith
  linarith

/-- If `p ∈ K` maximizes `q · v_α` over the points `q ∈ K` with `q · u_α = c` (the end point of the
chord of `K` on the line `l(α, c)`), then `K` has a supporting line at `p` with normal angle in
`[α, α + π]`. -/
lemma opt_exists_normal_of_isMax {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {α c : ℝ}
    {p : ℝ × ℝ} (hp : p ∈ K) (hpl : dot p (uvec α) = c)
    (hmax : ∀ q ∈ K, dot q (uvec α) = c → dot q (vvec α) ≤ dot p (vvec α)) :
    ∃ θ ∈ Icc α (α + π), dot p (uvec θ) = supp K θ := by
  -- Otherwise `h_K(θ) - p · u_θ` has a positive minimum `δ` on `[α, α + π]`; then `p + δ v_α`
  -- lies in `K` and on the chord, beyond `p`.
  by_contra hcon
  push Not at hcon
  have hpi := pi_pos
  have hcont : Continuous fun θ => supp K θ - dot p (uvec θ) :=
    (continuous_supp hK.2.1).sub (by unfold dot uvec; fun_prop)
  obtain ⟨θ₀, hθ₀, hmin⟩ := (isCompact_Icc (a := α) (b := α + π)).exists_isMinOn
    (nonempty_Icc.mpr (by linarith))
    hcont.continuousOn
  have hpos : ∀ θ ∈ Icc α (α + π), 0 < supp K θ - dot p (uvec θ) := fun θ hθ =>
    sub_pos.mpr (lt_of_le_of_ne (dot_le_supp hK.2.1 hp θ) (hcon θ hθ))
  set δ := supp K θ₀ - dot p (uvec θ₀) with hδ
  have hδpos : 0 < δ := hpos θ₀ hθ₀
  have hmem : p + δ • vvec α ∈ K := by
    rw [mem_iff_forall_dot_le_supp hK]
    intro θ
    -- reduce `θ` to `θ' ∈ [α, α + 2π)`
    set θ' := α + toIcoMod two_pi_pos 0 (θ - α) with hθ'
    have hrange := toIcoMod_mem_Ico two_pi_pos 0 (θ - α)
    rw [zero_add] at hrange
    have hu : uvec θ' = uvec θ := by
      obtain ⟨k, hk⟩ : ∃ k : ℤ, toIcoMod two_pi_pos 0 (θ - α) = θ - α - k * (2 * π) :=
        ⟨toIcoDiv two_pi_pos 0 (θ - α), by rw [toIcoMod, zsmul_eq_mul]⟩
      rw [hθ', hk, show α + (θ - α - k * (2 * π)) = θ - k * (2 * π) by ring]
      simp [uvec, cos_sub_int_mul_two_pi, sin_sub_int_mul_two_pi]
    have hs : supp K θ' = supp K θ := by simp only [supp, hu]
    rw [← hu, ← hs, dot_add_left, dot_smul_left, dot_vvec_uvec']
    have hθ'α : θ' - α = toIcoMod two_pi_pos 0 (θ - α) := by rw [hθ']; ring
    by_cases hle : θ' - α ≤ π
    · have hin : θ' ∈ Icc α (α + π) := ⟨by linarith [hrange.1], by linarith⟩
      have h1 : δ ≤ supp K θ' - dot p (uvec θ') := hmin hin
      have h2 : sin (θ' - α) ≤ 1 := sin_le_one _
      nlinarith
    · push Not at hle
      have h1 : sin (θ' - α) ≤ 0 := by
        have : 0 ≤ sin (θ' - α - π) :=
          sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hrange.2])
        rw [sin_sub_pi] at this
        linarith
      have h2 := dot_le_supp hK.2.1 hp θ'
      nlinarith
  have hline : dot (p + δ • vvec α) (uvec α) = c := by
    rw [dot_add_left, dot_smul_left, dot_vvec_uvec, mul_zero, add_zero, hpl]
  have := hmax _ hmem hline
  rw [dot_add_left, dot_smul_left, dot_vvec_self, mul_one] at this
  linarith

/-- A convex body inside a cap that meets the `x`-axis has `h(3π/2) = 0`. -/
lemma opt_supp_three_pi_div_two_eq_zero {K C : Set (ℝ × ℝ)} (hK : IsCap K (π / 2))
    (hC : IsConvexBody C) (hCK : C ⊆ K) {x : ℝ} (hx : (x, (0 : ℝ)) ∈ C) :
    supp C (3 * π / 2) = 0 := by
  apply le_antisymm
  · have := supp_mono hCK ⟨_, hx⟩ hK.2.1.2.1 (3 * π / 2)
    rwa [hK.2.2.2.2.2.1] at this
  · simpa [dot_uvec_three_pi_div_two] using dot_le_supp hC.2.1 hx (3 * π / 2)

/-- Sublinearity of the support function:
`sin(β - α) h_K(t) ≤ sin(β - t) h_K(α) + sin(t - α) h_K(β)` for `α ≤ t ≤ β ≤ α + π`. -/
lemma opt_supp_interp {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {α β t : ℝ} (hαt : α ≤ t)
    (htβ : t ≤ β) (hβα : β ≤ α + π) :
    sin (β - α) * supp K t ≤ sin (β - t) * supp K α + sin (t - α) * supp K β := by
  obtain ⟨q, hq, hqt⟩ := exists_dot_eq_supp hK.2.1 hK.1 t
  have h1 := dot_le_supp hK.2.1 hq α
  have h2 := dot_le_supp hK.2.1 hq β
  have hs1 : 0 ≤ sin (β - t) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs2 : 0 ≤ sin (t - α) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rw [← hqt, dot_uvec_comb]
  nlinarith [mul_le_mul_of_nonneg_left h1 hs1, mul_le_mul_of_nonneg_left h2 hs2]

/-- The injectivity condition gives `g_K⁺(t) > 1` and `f_K⁻(t) > 1` on `(0, π/2)`. -/
lemma opt_arm_gt_one {K : Set (ℝ × ℝ)} (hK : IsKi K) {t : ℝ} (ht : t ∈ Ioo 0 (π / 2)) :
    1 < gPlus K t ∧ 1 < fMinus K t := by
  obtain ⟨hcap, ⟨-, h2, h3⟩, -⟩ := hK
  have hd := opt_inj_hasDerivAt h2 ht
  obtain ⟨hu, hv⟩ := h3 t ht
  have eR := (uniqueDiffWithinAt_Ici t).eq_deriv _ hd.hasDerivWithinAt
    (theorem6_2_3_right hcap (t := t)).2
  have eL := (uniqueDiffWithinAt_Iic t).eq_deriv _ hd.hasDerivWithinAt
    (theorem6_2_3_left hcap (t := t)).2
  rw [eR] at hv
  rw [eL] at hu
  simp only [dot_add_left, dot_smul_left, dot_neg_left, dot_uvec_self, dot_vvec_self,
    dot_uvec_vvec, dot_vvec_uvec, neg_smul] at hu hv
  constructor <;> linarith

/-- The topmost point of `K` on `b_K^R` lies in `B_K` (the core of the proof of Lemma 8.1.7 (2);
see the module docstring). -/
lemma opt_exists_rightBody_on_line {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)}
    (hK : IsKi K) :
    ∃ p ∈ rightBody φ K, dot p (uvec φ) = supp K φ - 1 := by
  obtain ⟨hφ0, hφ4, -, hc9, hs0⟩ := opt_phi_bounds hφ
  have hpi := two_le_pi
  have hc : 0 < cos φ := by linarith
  have hcap := hK.1
  have hcb := hcap.2.1
  -- Step 1: the topmost point `p` of `K` on `b_K^R` (which meets `K` at `W_K^R`)
  set L := K ∩ line φ (supp K φ - 1) with hL
  have hWL : wRight φ K ∈ L := by
    refine ⟨(lemma8_1_5 hφ hK).1.1.1, ?_⟩
    simp only [line, mem_ofPred_eq, opt_wRight_eq, dot, uvec, zero_mul, add_zero]
    field_simp
  obtain ⟨p, ⟨hpK, hpl⟩, hpmax⟩ := (hcb.2.1.inter_right (isClosed_line _ _)).exists_isMaxOn
    ⟨_, hWL⟩ (continuous_dot (vvec φ)).continuousOn
  have hpl' : dot p (uvec φ) = supp K φ - 1 := hpl
  -- Step 2: a supporting line of `K` at `p`, with normal angle `θ ∈ [φ, φ + π]`
  obtain ⟨θ, hθ, hpθ⟩ := opt_exists_normal_of_isMax hcb hpK hpl'
    (fun q hq hql => hpmax ⟨hq, hql⟩)
  have hp2 := inj_cap_strip hcap hpK
  -- Step 3: `θ > φ + π/2` would put `p` beyond `C_K(φ)`, contradicting `g_K(φ) > 1`
  have hθ2 : θ ≤ φ + π / 2 := by
    by_contra hθ2
    push Not at hθ2
    have hg := (opt_arm_gt_one hK ⟨hφ0, by linarith⟩).1
    set c := vplus K (φ + π / 2) with hcdef
    have hcK : c ∈ K := (vplus_mem_edge hcb _).1
    have h1 : dot p (uvec (φ + π / 2)) ≤ dot c (uvec (φ + π / 2)) := by
      rw [hcdef, dot_vplus_uvec]; exact dot_le_supp hcb.2.1 hpK _
    have h2 : dot c (uvec θ) ≤ dot p (uvec θ) := by rw [hpθ]; exact dot_le_supp hcb.2.1 hcK θ
    have e1 : ∀ q : ℝ × ℝ, dot q (uvec θ) =
        cos (θ - φ) * dot q (uvec φ) + sin (θ - φ) * dot q (uvec (φ + π / 2)) := fun q => by
      rw [uvec_add_pi_div_two]; exact dot_uvec_eq_cos_add_sin q θ φ
    have hcos : cos (θ - φ) < 0 := cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [hθ.2])
    have hsin : 0 ≤ sin (θ - φ) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθ.2])
    have key : dot p (uvec φ) ≤ dot c (uvec φ) := by
      have ep := e1 p
      have ec := e1 c
      nlinarith [mul_le_mul_of_nonneg_left h1 hsin]
    rw [inj_gPlus_eq, vvec_add_pi_div_two, dot_neg_right, ← hcdef] at hg
    linarith
  -- Step 4: `p ∈ H_K^b(s)` for `s ∈ [φ, π/2]`, by the sublinearity of `h_K` on `[φ, θ]`, `[θ, π/2]`
  refine ⟨p, ⟨hpK, ?_⟩, hpl'⟩
  simp only [mem_iInter₂]
  intro s hs
  simp only [halfB, halfPlus, mem_ofPred_eq]
  rcases le_or_gt s θ with hsθ | hsθ
  · -- between `φ` and `θ`: `d` is bounded by `d(φ) = 1`
    rcases eq_or_lt_of_le hθ.1 with hθφ | hθφ
    · have : s = φ := le_antisymm (hθφ ▸ hsθ) hs.1
      subst this; linarith
    · have hI := opt_supp_interp hcb hs.1 hsθ (by linarith)
      have hE := dot_uvec_comb p φ θ s
      have hsinpos : 0 < sin (θ - φ) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have hmono : sin (θ - s) ≤ sin (θ - φ) :=
        sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith [hs.1])
      have hs1 : 0 ≤ sin (s - φ) := sin_nonneg_of_nonneg_of_le_pi (by linarith [hs.1]) (by linarith)
      rw [hpθ, hpl'] at hE
      nlinarith
  · -- between `θ` and `π/2`: `p` lies in the strip `0 ≤ y ≤ 1`
    have hθπ : θ < π / 2 := lt_of_lt_of_le hsθ hs.2
    have hI := opt_supp_interp hcb hsθ.le hs.2 (by linarith [hθ.1])
    have hE := dot_uvec_comb p θ (π / 2) s
    rw [hcap.2.2.2.1] at hI
    rw [hpθ, dot_uvec_pi_div_two] at hE
    have hcpos : 0 < sin (π / 2 - θ) := by
      rw [sin_pi_div_two_sub]; exact cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθπ⟩
    have hmono : sin (s - θ) ≤ sin (π / 2 - θ) :=
      sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith [hθ.1]) (by linarith [hs.2])
    have hs1 : 0 ≤ sin (s - θ) :=
      sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθ.1, hs.2])
    have hp2' : 0 ≤ p.2 := hp2.1
    nlinarith [mul_le_mul_of_nonneg_left hp2.2 hs1, mul_nonneg hs1 hp2']

/-- **Lemma 8.1.7** (`lem:right-left-body`) (2): equality at `t = φ^R, π/2`, so
`l_B(3π/2) = l(π/2, 0)` and `l_B(π + φ^R) = b_K^R`.

Departure from the paper: the paper puts the point `p` where `δK` meets `b_K^R` in `B_K` by placing
it outside the niche (Theorem 2.5.8 (2)) and applying Lemma 8.1.6 (1); this proof takes the topmost
point `p` of `K` on `b_K^R` and a normal angle `θ` of `K` at `p`, excludes `θ > φ^R + π/2` by the
injectivity condition (`g_K(φ^R) > 1`, through Theorem 6.2.3), and otherwise bounds
`h_K(t) - ⟨p, u_t⟩` on `[φ^R, π/2]` by the sublinearity of `h_K`, because Theorem 2.5.8 (2) needs
`𝒩(K) ⊆ K`, which fails on `𝒦^i` (see the module docstring). -/
theorem lemma8_1_7_two {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)} (hK : IsKi K) :
    supp K φ + supp (rightBody φ K) (π + φ) = 1 ∧
      supp K (π / 2) + supp (rightBody φ K) (π + π / 2) = 1 ∧
      suppLine (rightBody φ K) (3 * π / 2) = line (π / 2) 0 ∧
      suppLine (rightBody φ K) (π + φ) = wallB K φ := by
  obtain ⟨hφ0, hφ4, -, hc9, hs0⟩ := opt_phi_bounds hφ
  have hpi := two_le_pi
  have hcap := hK.1
  have hBcb := opt_rightBody_isConvexBody hφ0.le hcap
  have hA := opt_rightBody_A_mem hφ0.le hcap
  obtain ⟨p, hpB, hpl⟩ := opt_exists_rightBody_on_line hφ hK
  have h1 : supp K φ + supp (rightBody φ K) (π + φ) = 1 := by
    have le1 := lemma8_1_7_one hφ hK ⟨le_rfl, by linarith⟩
    have ge1 := dot_le_supp hBcb.2.1 hpB (π + φ)
    rw [show π + φ = φ + π by ring, uvec_add_pi, dot_neg_right, hpl] at ge1
    rw [show π + φ = φ + π by ring] at le1 ⊢
    linarith
  have hB3 := opt_supp_three_pi_div_two_eq_zero hcap hBcb inter_subset_left hA
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [show π + π / 2 = 3 * π / 2 by ring, hB3, hcap.2.2.2.1]; norm_num
  · ext q
    simp only [suppLine, line, mem_ofPred_eq, hB3, uvec_three_pi_div_two, uvec_pi_div_two,
      dot_mk]
    constructor <;> intro h <;> linarith
  · rw [proposition2_2_2_wallB]
    ext q
    simp only [suppLine, line, mem_ofPred_eq]
    rw [show π + φ = φ + π by ring, uvec_add_pi, dot_neg_right]
    have e : supp (rightBody φ K) (φ + π) = 1 - supp K φ := by
      rw [show φ + π = π + φ by ring]; linarith
    rw [e]
    constructor <;> intro h <;> linarith

/-- **Lemma 8.1.7** (`lem:right-left-body`) (3): `h_K(π/2 + t) + h_D(3π/2 + t) ≤ 1` on `[0, φ^L]`.

**Added hypothesis `φ ∈ [0.039, 0.04]`**, for the same reason as in Lemma 8.1.7 (1): for `φ = -π`
the set `D_K` is empty. -/
theorem lemma8_1_7_three {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)} (hK : IsKi K)
    {t : ℝ} (ht : t ∈ Icc 0 (π / 2 - φ)) :
    supp K (π / 2 + t) + supp (leftBody φ K) (3 * π / 2 + t) ≤ 1 := by
  -- every point of `D_K` lies in `H_K^d(t)`, i.e. `p · u_{3π/2 + t} ≤ 1 - h_K(π/2 + t)`
  have : supp (leftBody φ K) (3 * π / 2 + t) ≤ 1 - supp K (π / 2 + t) := by
    refine supp_le_of_forall ⟨_, opt_leftBody_C_mem (by linarith [hφ.1] : 0 ≤ φ) hK.1⟩
      fun p hp => ?_
    have hpt : p ∈ halfD K t := (mem_iInter₂.mp hp.2) t ht
    simp only [halfD, halfPlus, mem_ofPred_eq] at hpt
    rw [show 3 * π / 2 + t = t + π / 2 + π by ring, dot_uvec_add_pi,
      show π / 2 + t = t + π / 2 by ring]
    linarith
  linarith

/-- The topmost point of `K` on `d_K^L` lies in `D_K` (the core of the proof of Lemma 8.1.7 (4), the
mirror image of `opt_exists_rightBody_on_line`). -/
lemma opt_exists_leftBody_on_line {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)}
    (hK : IsKi K) :
    ∃ p ∈ leftBody φ K, dot p (vvec (π / 2 - φ)) = supp K (π / 2 - φ + π / 2) - 1 := by
  obtain ⟨hφ0, hφ4, -, hc9, hs0⟩ := opt_phi_bounds hφ
  have hpi := two_le_pi
  have hc : 0 < cos φ := by linarith
  have hcap := hK.1
  have hcb := hcap.2.1
  -- Step 1: the topmost point `p` of `K` on `d_K^L` (which meets `K` at `Z_K^L`)
  set L := K ∩ {q | dot q (vvec (π / 2 - φ)) = supp K (π / 2 - φ + π / 2) - 1} with hL
  have hLc : IsCompact L :=
    hcb.2.1.inter_right (isClosed_eq (continuous_dot _) continuous_const)
  have hZL : zLeft φ K ∈ L := by
    refine ⟨(lemma8_1_5 hφ hK).2.1.1, ?_⟩
    simp only [mem_ofPred_eq, opt_zLeft_eq, dot, vvec, sin_pi_div_two_sub, zero_mul, add_zero,
      show π / 2 - φ + π / 2 = π - φ by ring]
    field_simp
    ring
  obtain ⟨p, ⟨hpK, hpl⟩, hpmax⟩ :=
    hLc.exists_isMaxOn ⟨_, hZL⟩ (continuous_dot (uvec (π / 2 - φ))).continuousOn
  have hpl' : dot p (vvec (π / 2 - φ)) = supp K (π / 2 - φ + π / 2) - 1 := hpl
  -- Step 2: a supporting line of `K` at `p`, with normal angle `θ ∈ [-φ, π - φ]`; the line is
  -- `l(-φ, 1 - h_K(φ^L + π/2))`, traversed in the direction `v_{-φ} = u_{φ^L}`
  have hu : ∀ q : ℝ × ℝ, dot q (uvec (-φ)) = -dot q (vvec (π / 2 - φ)) := by
    intro q
    simp only [dot, uvec, vvec, cos_neg, sin_neg, sin_pi_div_two_sub, cos_pi_div_two_sub]
    ring
  have hv : ∀ q : ℝ × ℝ, dot q (vvec (-φ)) = dot q (uvec (π / 2 - φ)) := by
    intro q
    simp only [dot, uvec, vvec, cos_neg, sin_neg, sin_pi_div_two_sub, cos_pi_div_two_sub]
    ring
  obtain ⟨θ, hθ, hpθ⟩ := opt_exists_normal_of_isMax hcb hpK (α := -φ)
    (c := -(supp K (π / 2 - φ + π / 2) - 1)) (by rw [hu, hpl'])
    (fun q hq hql => by
      rw [hv, hv]
      refine hpmax ⟨hq, ?_⟩
      show dot q (vvec (π / 2 - φ)) = _
      rw [hu] at hql
      linarith)
  have hp2 := inj_cap_strip hcap hpK
  -- Step 3: `θ < φ^L` would put `p` before `A_K(φ^L)`, contradicting `f_K(φ^L) > 1`
  have hθ2 : π / 2 - φ ≤ θ := by
    by_contra hθ2
    push Not at hθ2
    have hf := (opt_arm_gt_one hK (t := π / 2 - φ) ⟨by linarith, by linarith⟩).2
    set a := vminus K (π / 2 - φ) with hadef
    have haK : a ∈ K := (vminus_mem_edge hcb _).1
    have h1 : dot p (uvec (π / 2 - φ)) ≤ dot a (uvec (π / 2 - φ)) := by
      rw [hadef, dot_vminus_uvec]; exact dot_le_supp hcb.2.1 hpK _
    have h2 : dot a (uvec θ) ≤ dot p (uvec θ) := by rw [hpθ]; exact dot_le_supp hcb.2.1 haK θ
    have e1 : ∀ q : ℝ × ℝ, dot q (uvec θ) = cos (θ - (π / 2 - φ)) * dot q (uvec (π / 2 - φ)) +
        sin (θ - (π / 2 - φ)) * dot q (vvec (π / 2 - φ)) := fun q => dot_uvec_eq_cos_add_sin q θ _
    have hcos : 0 ≤ cos (θ - (π / 2 - φ)) :=
      cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith⟩
    have hsin : sin (θ - (π / 2 - φ)) < 0 :=
      sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith [hθ.1])
    have key : dot p (vvec (π / 2 - φ)) ≤ dot a (vvec (π / 2 - φ)) := by
      have ep := e1 p
      have ea := e1 a
      nlinarith [mul_le_mul_of_nonneg_left h1 hcos]
    rw [inj_fMinus_eq, ← hadef] at hf
    linarith
  have hp1 : dot p (uvec (π - φ)) = supp K (π - φ) - 1 := by
    rw [show π - φ = π / 2 - φ + π / 2 by ring, uvec_add_pi_div_two]; exact hpl'
  -- Step 4: `p ∈ H_K^d(s)` for `s ∈ [0, φ^L]`, by the sublinearity of `h_K` on `[π/2, θ]` and
  -- `[θ, π - φ]`
  have key : ∀ t ∈ Icc (π / 2) (π - φ), supp K t - 1 ≤ dot p (uvec t) := by
    intro t ht
    rcases le_or_gt θ t with hθt | hθt
    · -- between `θ` and `π - φ`: `d` is bounded by `d(π - φ) = 1`
      rcases eq_or_lt_of_le hθ.2 with hθe | hθe
      · have : t = π - φ := le_antisymm ht.2 (by linarith)
        rw [this]; linarith
      · have hI := opt_supp_interp hcb hθt ht.2 (by linarith)
        have hE := dot_uvec_comb p θ (π - φ) t
        have hsinpos : 0 < sin (π - φ - θ) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
        have hmono : sin (t - θ) ≤ sin (π - φ - θ) :=
          sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith [ht.2])
        have hs1 : 0 ≤ sin (π - φ - t) :=
          sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.2]) (by linarith [ht.1])
        rw [hpθ, hp1] at hE
        nlinarith
    · -- between `π/2` and `θ`: `p` lies in the strip `0 ≤ y ≤ 1`
      have hθπ : π / 2 < θ := lt_of_le_of_lt ht.1 hθt
      have hI := opt_supp_interp hcb ht.1 hθt.le (by linarith [hθ.2])
      have hE := dot_uvec_comb p (π / 2) θ t
      rw [hcap.2.2.2.1] at hI
      rw [hpθ, dot_uvec_pi_div_two] at hE
      have hsinpos : 0 < sin (θ - π / 2) :=
        sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ.2])
      have hmono : sin (θ - t) ≤ sin (θ - π / 2) :=
        sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith [hθ.2]) (by linarith [ht.1])
      have hs1 : 0 ≤ sin (θ - t) :=
        sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθ.2, ht.1])
      have hs2 : 0 ≤ sin (t - π / 2) :=
        sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht.2])
      nlinarith [mul_le_mul_of_nonneg_left hp2.2 hs1, mul_nonneg hs1 hp2.1]
  refine ⟨p, ⟨hpK, ?_⟩, hpl'⟩
  simp only [mem_iInter₂]
  intro s hs
  simp only [halfD, halfPlus, mem_ofPred_eq]
  exact key (s + π / 2) ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- **Lemma 8.1.7** (`lem:right-left-body`) (4): equality at `t = 0, φ^L` (the paper writes `φ^R`),
so `l_D(3π/2) = l(π/2, 0)` and `l_D(3π/2 + φ^L) = d_K^L`.

Departure from the paper: the paper argues as for (2), through Theorem 2.5.8 (2) and Lemma 8.1.6
(2); this proof is the mirror image of the proof of (2), with `f_K(φ^L) > 1` (through
Theorem 6.2.3), because Theorem 2.5.8 (2) needs `𝒩(K) ⊆ K`, which fails on `𝒦^i` (see the module
docstring). -/
theorem lemma8_1_7_four {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)} (hK : IsKi K) :
    supp K (π / 2 + 0) + supp (leftBody φ K) (3 * π / 2 + 0) = 1 ∧
      supp K (π / 2 + (π / 2 - φ)) + supp (leftBody φ K) (3 * π / 2 + (π / 2 - φ)) = 1 ∧
      suppLine (leftBody φ K) (3 * π / 2) = line (π / 2) 0 ∧
      suppLine (leftBody φ K) (3 * π / 2 + (π / 2 - φ)) = wallD K (π / 2 - φ) := by
  obtain ⟨hφ0, hφ4, -, hc9, hs0⟩ := opt_phi_bounds hφ
  have hpi := two_le_pi
  have hcap := hK.1
  have hDcb := opt_leftBody_isConvexBody hφ0.le hcap
  have hC := opt_leftBody_C_mem hφ0.le hcap
  obtain ⟨p, hpD, hpl⟩ := opt_exists_leftBody_on_line hφ hK
  have hD3 := opt_supp_three_pi_div_two_eq_zero hcap hDcb inter_subset_left hC
  have h2 : supp K (π / 2 + (π / 2 - φ)) + supp (leftBody φ K) (3 * π / 2 + (π / 2 - φ)) = 1 := by
    have le1 := lemma8_1_7_three hφ hK (t := π / 2 - φ) ⟨by linarith, le_rfl⟩
    have ge1 := dot_le_supp hDcb.2.1 hpD (3 * π / 2 + (π / 2 - φ))
    rw [show 3 * π / 2 + (π / 2 - φ) = π / 2 - φ + π / 2 + π by ring, uvec_add_pi,
      dot_neg_right, uvec_add_pi_div_two, hpl] at ge1
    rw [show 3 * π / 2 + (π / 2 - φ) = π / 2 - φ + π / 2 + π by ring,
      show π / 2 + (π / 2 - φ) = π / 2 - φ + π / 2 by ring] at le1 ⊢
    linarith
  refine ⟨?_, h2, ?_, ?_⟩
  · rw [add_zero, add_zero, hD3, hcap.2.2.2.1]; norm_num
  · ext q
    simp only [suppLine, line, mem_ofPred_eq, hD3, uvec_three_pi_div_two, uvec_pi_div_two,
      dot_mk]
    constructor <;> intro h <;> linarith
  · rw [proposition2_2_2_wallD]
    ext q
    simp only [suppLine, line, mem_ofPred_eq]
    rw [show 3 * π / 2 + (π / 2 - φ) = π / 2 - φ + π / 2 + π by ring, uvec_add_pi,
      dot_neg_right]
    have e : supp (leftBody φ K) (π / 2 - φ + π / 2 + π) = 1 - supp K (π / 2 - φ + π / 2) := by
      rw [show π / 2 - φ + π / 2 + π = 3 * π / 2 + (π / 2 - φ) by ring,
        show π / 2 - φ + π / 2 = π / 2 + (π / 2 - φ) by ring]
      linarith
    rw [e]
    constructor <;> intro h <;> linarith

/-- **Theorem 8.1.8** (`thm:cap-tail-extension`). For `K ∈ 𝒦^i`, `(K, B_K, D_K) ∈ 𝓛`. -/
theorem theorem8_1_8 {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)} (hK : IsKi K) :
    InL φ K (rightBody φ K) (leftBody φ K) := by
  have hφ0 : 0 ≤ φ := by linarith [hφ.1]
  have h2 := lemma8_1_7_two hφ hK
  have h4 := lemma8_1_7_four hφ hK
  exact ⟨hK, opt_rightBody_isConvexBody hφ0 hK.1, opt_leftBody_isConvexBody hφ0 hK.1,
    inter_subset_left, inter_subset_left, fun t ht => lemma8_1_7_one hφ hK ht, h2.1, h2.2.1,
    fun t ht => lemma8_1_7_three hφ hK ht, h4.1, h4.2.1⟩

end MovingSofaOptimality
