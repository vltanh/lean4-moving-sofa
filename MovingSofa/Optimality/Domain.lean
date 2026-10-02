module

public import MovingSofa.Gerver.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# The domain of `𝒬` (§8.1)

Definitions 8.1.1 (`def:cap-space-special`), 8.1.3–8.1.6, Theorem 8.1.1 (`thm:cap-space-special`)
part (1), Proposition 8.1.2, Lemmas 8.1.3–8.1.7 and Theorem 8.1.8 (`thm:cap-tail-extension`).

The paper fixes `φ^R = φ` and `φ^L = π/2 - φ` with `φ` Gerver's angle (Definition 8.1.2). Everything
here is stated for a parameter `φ`; where the paper uses numerical properties of Gerver's `φ`
(`2 sec φ + 2 tan φ < 2.2`, `sec φ < 1.1`) we assume `φ ∈ [0.039, 0.04]`, the range the paper quotes.

**A gap in the proofs.** The paper proves Lemma 8.1.7 (2), (4) with `𝒩(K) ⊆ K` (through Theorem 2.5.8
(2)), and splits `𝒩(K)` in Theorem 8.2.4 using the disjointness of `K ∩ H̆_K^R` and `K ∩ H̆_K^L`
(Lemma 8.1.4). But `K ∈ 𝒦^i` does not give `𝒩(K) ⊆ K`: the cap with two unit quarter-discs joined by a
flat top of length 3 satisfies the injectivity condition and has area `3 + π/2`, but its niche is not
inside it. The statements hold on all of `𝒦^i` nevertheless, and we prove them so:
* Lemma 8.1.7 (2): let `p` be the topmost point of `K` on `b_K^R`, and `θ ∈ [φ^R, φ^R + π]` a normal
  angle of `K` at `p` (`opt_exists_normal_of_isMax`). If `θ > φ^R + π/2`, then `p` lies beyond `C_K(φ^R)`
  and `g_K(φ^R) ≤ 1`, against the injectivity condition (`opt_arm_gt_one`). Otherwise the sublinearity
  of the support function (`opt_supp_interp`) between `φ^R` and `θ`, and between `θ` and `π/2`, gives
  `p ∈ H_K^b(t)` for every `t ∈ [φ^R, π/2]`. (4) is the mirror image, with `f_K(φ^L)`.
* Theorem 8.2.4: `𝒩(K) ∩ H̆_K^R ∩ H̆_K^L = ∅` (`opt_niche_hRight_hLeft`), since the niche lies below
  height `W₀/2` while `H̆_K^R ∩ H̆_K^L` lies above `(W₀ cos φ^R - 2) / (2 sin φ^R)`, where
  `W₀ = h_K(0) + h_K(π) ≥ |K| ≥ 2.2`.
-/

@[expose] public section

open Real Set
open scoped Pointwise

namespace MovingSofa

/-! ### Auxiliary facts on caps with rotation angle `π/2` (package I) -/

lemma opt_uvec_zero : uvec 0 = (1, 0) := by simp [uvec]
lemma opt_vvec_zero : vvec 0 = (0, 1) := by simp [vvec]
lemma opt_uvec_pi_div_two : uvec (π / 2) = (0, 1) := by simp [uvec]
lemma opt_vvec_pi_div_two : vvec (π / 2) = (-1, 0) := by simp [vvec]
lemma opt_uvec_pi : uvec π = (-1, 0) := by simp [uvec]
lemma opt_vvec_pi : vvec π = (0, -1) := by simp [vvec]
lemma opt_uvec_three_pi_div_two : uvec (3 * π / 2) = (0, -1) := by
  rw [show 3 * π / 2 = π / 2 + π by ring, uvec_add_pi, opt_uvec_pi_div_two]; simp
lemma opt_vvec_three_pi_div_two : vvec (3 * π / 2) = (1, 0) := by
  rw [show 3 * π / 2 = π / 2 + π by ring, vvec_add_pi, opt_vvec_pi_div_two]; simp

lemma opt_dot_mk (p : ℝ × ℝ) (a b : ℝ) : dot p (a, b) = p.1 * a + p.2 * b := rfl

-- A simp lemma for the files of package I only (not exported to importers).
attribute [local simp] opt_dot_mk

section CapFacts
variable {K : Set (ℝ × ℝ)}

lemma opt_cap_mem_strip (hK : IsCap K (π / 2)) {p : ℝ × ℝ} (hp : p ∈ K) :
    0 ≤ p.2 ∧ p.2 ≤ 1 := by
  obtain ⟨-, hcb, -, h2, -, h3, -⟩ := hK
  have a := dot_le_supp hcb.2.1 hp (π / 2)
  have b := dot_le_supp hcb.2.1 hp (3 * π / 2)
  rw [h2, opt_uvec_pi_div_two] at a
  rw [h3, opt_uvec_three_pi_div_two] at b
  simp at a b
  exact ⟨b, a⟩

lemma opt_cap_down (hK : IsCap K (π / 2)) {p : ℝ × ℝ} (hp : p ∈ K) {y : ℝ} (hy0 : 0 ≤ y)
    (hy : y ≤ p.2) : (p.1, y) ∈ K := by
  obtain ⟨-, hcb, -, -, -, h3, ι, t, c, ht, hKeq⟩ := hK
  obtain ⟨z, hz, hz3⟩ := exists_dot_eq_supp hcb.2.1 hcb.1 (3 * π / 2)
  rw [h3, opt_uvec_three_pi_div_two] at hz3
  simp at hz3
  rw [hKeq] at hp hz ⊢
  simp only [mem_iInter] at hp hz ⊢
  intro i
  have hpi := hp i
  have hzi := hz i
  simp only [halfMinus, mem_ofPred_eq] at hpi hzi ⊢
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
  · rw [h, show π / 2 + π = 3 * π / 2 by ring, opt_uvec_three_pi_div_two] at hzi ⊢
    simp at hzi ⊢
    linarith
  · rw [h, opt_uvec_three_pi_div_two] at hzi ⊢
    simp at hzi ⊢
    linarith

/-- The bottom-right corner `A = (h_K(0), 0)` lies in `K`. -/
lemma opt_cap_A_mem (hK : IsCap K (π / 2)) : (supp K 0, (0 : ℝ)) ∈ K := by
  have hcb := hK.2.1
  obtain ⟨p, hp, hp0⟩ := exists_dot_eq_supp hcb.2.1 hcb.1 0
  rw [opt_uvec_zero] at hp0
  simp at hp0
  have := opt_cap_down hK hp le_rfl (opt_cap_mem_strip hK hp).1
  rwa [hp0] at this

/-- The bottom-left corner `C = (-h_K(π), 0)` lies in `K`. -/
lemma opt_cap_C_mem (hK : IsCap K (π / 2)) : (-supp K π, (0 : ℝ)) ∈ K := by
  have hcb := hK.2.1
  obtain ⟨p, hp, hp0⟩ := exists_dot_eq_supp hcb.2.1 hcb.1 π
  rw [opt_uvec_pi] at hp0
  simp at hp0
  have := opt_cap_down hK hp le_rfl (opt_cap_mem_strip hK hp).1
  rwa [show p.1 = -supp K π by linarith] at this

lemma opt_cap_fst_le (hK : IsCap K (π / 2)) {p : ℝ × ℝ} (hp : p ∈ K) :
    -supp K π ≤ p.1 ∧ p.1 ≤ supp K 0 := by
  have hcb := hK.2.1
  have a := dot_le_supp hcb.2.1 hp 0
  have b := dot_le_supp hcb.2.1 hp π
  rw [opt_uvec_zero] at a
  rw [opt_uvec_pi] at b
  simp at a b
  constructor <;> linarith

lemma opt_cap_vminus_zero (hK : IsCap K (π / 2)) : vminus K 0 = (supp K 0, 0) := by
  have hA := opt_cap_A_mem hK
  have hS : sInf ((fun p => dot p (vvec 0)) '' edge K 0) = 0 := by
    apply IsLeast.csInf_eq
    refine ⟨⟨(supp K 0, 0), ⟨hA, ?_⟩, ?_⟩, ?_⟩
    · simp [suppLine, line, opt_uvec_zero]
    · simp [opt_vvec_zero]
    · rintro _ ⟨q, ⟨hq, -⟩, rfl⟩
      simp [opt_vvec_zero]
      exact (opt_cap_mem_strip hK hq).1
  simp [vminus, hS, opt_uvec_zero]

lemma opt_cap_vplus_pi (hK : IsCap K (π / 2)) : vplus K π = (-supp K π, 0) := by
  have hC := opt_cap_C_mem hK
  have hS : sSup ((fun p => dot p (vvec π)) '' edge K π) = 0 := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨(-supp K π, 0), ⟨hC, ?_⟩, ?_⟩, ?_⟩
    · simp [suppLine, line, opt_uvec_pi]
    · simp [opt_vvec_pi]
    · rintro _ ⟨q, ⟨hq, -⟩, rfl⟩
      simp [opt_vvec_pi]
      exact (opt_cap_mem_strip hK hq).1
  simp [vplus, hS, opt_uvec_pi]

lemma opt_cap_aK_zero (hK : IsCap K (π / 2)) : aK K 0 = (supp K 0, 0) := opt_cap_vminus_zero hK

lemma opt_cap_cK_pi_div_two (hK : IsCap K (π / 2)) : cK K (π / 2) = (-supp K π, 0) := by
  simp only [cK, cPlus, show π / 2 + π / 2 = π by ring]
  exact opt_cap_vplus_pi hK

lemma opt_cap_gapW (hK : IsCap K (π / 2)) {t : ℝ} (ht : t ∈ Ioo 0 (π / 2)) :
    supp K t - 1 < supp K 0 * cos t := by
  have h := (theorem2_5_5 hK ht).1
  have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩
  simp only [wedgeGapW, aMinus] at h
  rw [opt_cap_vminus_zero hK, opt_uvec_zero] at h
  simp only [wedgeW, opt_dot_mk, Prod.fst_sub, Prod.snd_sub, mul_one, mul_zero, add_zero,
    sub_pos] at h
  rwa [div_lt_iff₀ hc] at h

lemma opt_cap_gapZ (hK : IsCap K (π / 2)) {t : ℝ} (ht : t ∈ Ioo 0 (π / 2)) :
    supp K (t + π / 2) - 1 < supp K π * sin t := by
  have h := (theorem2_5_5 hK ht).2
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
  simp only [wedgeGapZ, cPlus, show π / 2 + π / 2 = π by ring] at h
  rw [opt_cap_vplus_pi hK, opt_vvec_pi_div_two] at h
  simp only [wedgeZ, opt_vvec_pi_div_two, cos_pi_div_two_sub, opt_dot_mk, Prod.fst_sub,
    Prod.snd_sub, Prod.smul_mk, smul_eq_mul] at h
  have h' : (supp K (t + π / 2) - 1) / sin t < supp K π := by linarith
  rwa [div_lt_iff₀ hs] at h'

lemma opt_cap_A_mem_halfB (hK : IsCap K (π / 2)) {t : ℝ} (ht : t ∈ Icc 0 (π / 2)) :
    (supp K 0, (0 : ℝ)) ∈ halfB K t := by
  simp only [halfB, halfPlus, mem_ofPred_eq]
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0; simp [opt_uvec_zero]
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · rw [h1, hK.2.2.2.1, opt_uvec_pi_div_two]; simp
  · have := opt_cap_gapW hK ⟨h0, h1⟩
    simp only [dot, uvec]; linarith

lemma opt_cap_C_mem_halfD (hK : IsCap K (π / 2)) {t : ℝ} (ht : t ∈ Icc 0 (π / 2)) :
    (-supp K π, (0 : ℝ)) ∈ halfD K t := by
  simp only [halfD, halfPlus, mem_ofPred_eq, uvec_add_pi_div_two]
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0; simp [hK.2.2.2.1, opt_vvec_zero]
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · subst h1; rw [show π / 2 + π / 2 = π by ring]; simp [opt_vvec_pi_div_two]
  · have := opt_cap_gapZ hK ⟨h0, h1⟩
    simp only [dot, vvec]; linarith

/-- A cap with rotation angle `π/2` whose points have `x`-coordinates in `[a, b]` has area at most
`b - a`. -/
lemma opt_area_le_of_fst_bounds (hK : IsCap K (π / 2)) {a b : ℝ}
    (h : ∀ q ∈ K, a ≤ q.1 ∧ q.1 ≤ b) : area K ≤ b - a := by
  have hsub : K ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 := fun q hq =>
    ⟨⟨(h q hq).1, (h q hq).2⟩, ⟨(opt_cap_mem_strip hK hq).1, (opt_cap_mem_strip hK hq).2⟩⟩
  obtain ⟨q, hq⟩ := hK.2.1.1
  have hab : a ≤ b := le_trans (h q hq).1 (h q hq).2
  have hvol : MeasureTheory.volume (Icc a b ×ˢ Icc (0 : ℝ) 1) = ENNReal.ofReal (b - a) := by
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, Real.volume_Icc,
      Real.volume_Icc]
    simp
  unfold area
  calc (MeasureTheory.volume K).toReal
      ≤ (MeasureTheory.volume (Icc a b ×ˢ Icc (0 : ℝ) 1)).toReal :=
        ENNReal.toReal_mono (by rw [hvol]; exact ENNReal.ofReal_ne_top)
          (MeasureTheory.measure_mono hsub)
    _ = b - a := by rw [hvol, ENNReal.toReal_ofReal (by linarith)]

/-- Bounds on `x`-coordinates from the supporting half-planes `H_K(φ)` and `H_K(π - φ)`. -/
lemma opt_cap_fst_le_phi (hK : IsCap K (π / 2)) {φ : ℝ} (hc : 0 < cos φ) (hs : 0 ≤ sin φ)
    {q : ℝ × ℝ} (hq : q ∈ K) : -supp K (π - φ) / cos φ ≤ q.1 ∧ q.1 ≤ supp K φ / cos φ := by
  have a := dot_le_supp hK.2.1.2.1 hq φ
  have b := dot_le_supp hK.2.1.2.1 hq (π - φ)
  simp only [dot, uvec, cos_pi_sub, sin_pi_sub] at a b
  have hq2 := (opt_cap_mem_strip hK hq).1
  constructor
  · rw [div_le_iff₀ hc]; nlinarith
  · rw [le_div_iff₀ hc]; nlinarith

end CapFacts

lemma opt_phi_bounds {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) :
    0 < φ ∧ φ < π / 4 ∧ sin φ ≤ 0.04 ∧ 0.9992 ≤ cos φ ∧ 0 < sin φ := by
  obtain ⟨h1, h2⟩ := hφ
  have hpi := two_le_pi
  refine ⟨by linarith, by linarith, (sin_le (by linarith)).trans h2, ?_,
    sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)⟩
  have := one_sub_sq_div_two_le_cos (x := φ)
  nlinarith

lemma opt_dot_frame_u (w : ℝ × ℝ) (a s : ℝ) :
    dot w (uvec a) = cos (a - s) * dot w (uvec s) + sin (a - s) * dot w (vvec s) := by
  simp only [dot, uvec, vvec, cos_sub, sin_sub]
  linear_combination (-(w.1 * cos a + w.2 * sin a)) * sin_sq_add_cos_sq s

lemma opt_dot_frame_v (w : ℝ × ℝ) (a s : ℝ) :
    dot w (vvec a) = -sin (a - s) * dot w (uvec s) + cos (a - s) * dot w (vvec s) := by
  simp only [dot, uvec, vvec, cos_sub, sin_sub]
  linear_combination (-(-w.1 * sin a + w.2 * cos a)) * sin_sq_add_cos_sq s

lemma opt_innerCorner_dot_u (K : Set (ℝ × ℝ)) (t : ℝ) :
    dot (innerCorner K t) (uvec t) = supp K t - 1 := by
  rw [proposition2_2_2_innerCorner]; simp [dot_add_left, dot_smul_left]

lemma opt_innerCorner_dot_v (K : Set (ℝ × ℝ)) (t : ℝ) :
    dot (innerCorner K t) (vvec t) = supp K (t + π / 2) - 1 := by
  rw [proposition2_2_2_innerCorner]; simp [dot_add_left, dot_smul_left]

lemma opt_inj_hasDerivAt {K : Set (ℝ × ℝ)} (h2 : InjCond2 K) {t : ℝ} (ht : t ∈ Ioo 0 (π / 2)) :
    HasDerivAt (innerCorner K) (deriv (innerCorner K) t) t :=
  ((h2.differentiableOn one_ne_zero).differentiableAt (Icc_mem_nhds ht.1 ht.2)).hasDerivAt

lemma opt_hasDerivAt_dot {f : ℝ → ℝ × ℝ} {f' : ℝ × ℝ} {s : ℝ} (hf : HasDerivAt f f' s)
    (w : ℝ × ℝ) : HasDerivAt (fun r => dot (f r) w) (dot f' w) s := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ :=
    w.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + w.2 • ContinuousLinearMap.snd ℝ ℝ ℝ
  have h := L.hasFDerivAt.comp_hasDerivAt s hf
  convert h using 1
  · funext r; simp [L, dot]; ring
  · simp [L, dot]; ring

lemma opt_continuousOn_dot {f : ℝ → ℝ × ℝ} {S : Set ℝ} (hf : ContinuousOn f S) (w : ℝ × ℝ) :
    ContinuousOn (fun r => dot (f r) w) S := by
  unfold dot
  exact ((continuous_fst.comp_continuousOn hf).mul continuousOn_const).add
    ((continuous_snd.comp_continuousOn hf).mul continuousOn_const)



/-- The space `𝒦^i` of caps with rotation angle `π/2` satisfying the injectivity condition and with
area at least `2.2` (Definition 8.1.1, `def:cap-space-special`). -/
def IsKi (K : Set (ℝ × ℝ)) : Prop := IsCap K (π / 2) ∧ SatisfiesInjectivity K ∧ 2.2 ≤ area K

/-! ### Minkowski combinations of caps (package I) -/

section Comb
open MeasureTheory
variable {K₁ K₂ : Set (ℝ × ℝ)} {c : ℝ}

lemma opt_comb_mem {a b : ℝ × ℝ} (ha : a ∈ K₁) (hb : b ∈ K₂) :
    (1 - c) • a + c • b ∈ (1 - c) • K₁ + c • K₂ :=
  Set.add_mem_add (Set.smul_mem_smul_set ha) (Set.smul_mem_smul_set hb)

lemma opt_mem_comb {p : ℝ × ℝ} (hp : p ∈ (1 - c) • K₁ + c • K₂) :
    ∃ a ∈ K₁, ∃ b ∈ K₂, p = (1 - c) • a + c • b := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.mp hp
  obtain ⟨a, ha, rfl⟩ := Set.mem_smul_set.mp hx
  obtain ⟨b, hb, rfl⟩ := Set.mem_smul_set.mp hy
  exact ⟨a, ha, b, hb, rfl⟩

lemma opt_comb_neg {a b : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (ha : a < 0) (hb : b < 0) :
    (1 - c) * a + c * b < 0 := by
  rcases eq_or_lt_of_le hc.1 with h | h
  · subst h; simpa using ha
  · nlinarith [mul_neg_of_pos_of_neg h hb,
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hc.2) ha.le]

/-- The Minkowski combination of two caps with rotation angle `π/2` is such a cap. -/
lemma opt_comb_isCap (h₁ : IsCap K₁ (π / 2)) (h₂ : IsCap K₂ (π / 2)) (hc : c ∈ Icc (0 : ℝ) 1) :
    IsCap ((1 - c) • K₁ + c • K₂) (π / 2) := by
  set M := (1 - c) • K₁ + c • K₂ with hM
  have hcb₁ := h₁.2.1
  have hcb₂ := h₂.2.1
  have hMcb : IsConvexBody M := isConvexBody_comb hcb₁ hcb₂
  have sM : ∀ t, supp M t = (1 - c) * supp K₁ t + c * supp K₂ t := supp_comb hcb₁ hcb₂ hc
  have e2 : supp M (π / 2) = 1 := by rw [sM, h₁.2.2.2.1, h₂.2.2.2.1]; ring
  have e3 : supp M (3 * π / 2) = 0 := by rw [sM, h₁.2.2.2.2.2.1, h₂.2.2.2.2.2.1]; ring
  have hproj : ∀ q ∈ M, ((q.1, 0) : ℝ × ℝ) ∈ M := by
    intro q hq
    obtain ⟨a, ha, b, hb, rfl⟩ := opt_mem_comb hq
    have := opt_comb_mem (c := c) (opt_cap_down h₁ ha le_rfl (opt_cap_mem_strip h₁ ha).1)
      (opt_cap_down h₂ hb le_rfl (opt_cap_mem_strip h₂ hb).1)
    convert this using 1
    ext <;> simp
  refine ⟨h₁.1, hMcb, e2, e2, by rw [show π / 2 + π = 3 * π / 2 by ring]; exact e3, e3, ?_⟩
  refine ⟨{t : ℝ // t ∈ Icc 0 π ∨ t = 3 * π / 2}, fun i => i.1, fun i => supp M i.1, ?_, ?_⟩
  · rintro ⟨t, ht | ht⟩
    · simp only [jSet, mem_union, mem_Icc, mem_insert_iff, mem_singleton_iff]
      rcases le_total t (π / 2) with h | h
      · left; left; exact ⟨ht.1, h⟩
      · left; right; exact ⟨h, by linarith [ht.2]⟩
    · simp only [mem_union, mem_insert_iff, mem_singleton_iff]
      right; right; exact ht
  · ext p
    simp only [mem_iInter, halfMinus, mem_ofPred_eq]
    constructor
    · intro hp i; exact dot_le_supp hMcb.2.1 hp i.1
    · intro hp
      rw [mem_iff_forall_dot_le_supp hMcb]
      have h0 := hp ⟨0, Or.inl ⟨le_rfl, pi_pos.le⟩⟩
      have hpi := hp ⟨π, Or.inl ⟨pi_pos.le, le_rfl⟩⟩
      have h3 := hp ⟨3 * π / 2, Or.inr rfl⟩
      simp only [opt_uvec_zero, opt_uvec_pi, opt_uvec_three_pi_div_two, opt_dot_mk, e3] at h0 hpi h3
      intro t
      rcases le_or_gt 0 (sin t) with hs | hs
      · have hu : uvec (arccos (cos t)) = uvec t := by
          ext
          · simp [uvec, cos_arccos (neg_one_le_cos t) (cos_le_one t)]
          · simp only [uvec, sin_arccos]
            rw [← sin_sq, Real.sqrt_sq hs]
        have := hp ⟨arccos (cos t), Or.inl ⟨arccos_nonneg _, arccos_le_pi _⟩⟩
        simp only at this
        rw [hu] at this
        rwa [show supp M (arccos (cos t)) = supp M t by simp only [supp, hu]] at this
      · obtain ⟨q₀, hq₀, hq₀e⟩ := exists_dot_eq_supp hMcb.2.1 hMcb.1 0
        obtain ⟨q₁, hq₁, hq₁e⟩ := exists_dot_eq_supp hMcb.2.1 hMcb.1 π
        rw [opt_uvec_zero] at hq₀e
        rw [opt_uvec_pi] at hq₁e
        simp only [opt_dot_mk, mul_one, mul_zero, add_zero, mul_neg] at hq₀e hq₁e
        have hp2 : 0 ≤ p.2 := by linarith
        rcases le_or_gt 0 (cos t) with hcs | hcs
        · have := dot_le_supp hMcb.2.1 (hproj q₀ hq₀) t
          simp only [dot, uvec, zero_mul, add_zero] at this ⊢
          rw [hq₀e] at this
          nlinarith [mul_nonneg (sub_nonneg.mpr h0) hcs, mul_nonneg hp2 (neg_nonneg.mpr hs.le)]
        · have := dot_le_supp hMcb.2.1 (hproj q₁ hq₁) t
          simp only [dot, uvec, zero_mul, add_zero] at this ⊢
          have hq1 : q₁.1 = -supp M π := by linarith
          rw [hq1] at this
          nlinarith [mul_nonneg (by linarith : 0 ≤ p.1 + supp M π) (neg_nonneg.mpr hcs.le),
            mul_nonneg hp2 (neg_nonneg.mpr hs.le)]

lemma opt_innerCorner_comb (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂)
    (hc : c ∈ Icc (0 : ℝ) 1) :
    innerCorner ((1 - c) • K₁ + c • K₂) = (1 - c) • innerCorner K₁ + c • innerCorner K₂ := by
  funext t
  simp only [Pi.add_apply, Pi.smul_apply, proposition2_2_2_innerCorner, supp_comb h₁ h₂ hc]
  ext <;> simp <;> ring

lemma opt_outerCorner_comb (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂)
    (hc : c ∈ Icc (0 : ℝ) 1) :
    outerCorner ((1 - c) • K₁ + c • K₂) = (1 - c) • outerCorner K₁ + c • outerCorner K₂ := by
  funext t
  simp only [Pi.add_apply, Pi.smul_apply, proposition2_2_2_outerCorner, supp_comb h₁ h₂ hc]
  ext <;> simp <;> ring

lemma opt_sigma_comb (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂) (hc : c ∈ Icc (0 : ℝ) 1) :
    sigma ((1 - c) • K₁ + c • K₂) =
      ENNReal.ofReal (1 - c) • sigma K₁ + ENNReal.ofReal c • sigma K₂ := by
  have := theorem7_1_2_sigma ⟨K₁, h₁⟩ ⟨K₂, h₂⟩ hc
  simpa [convexBodyComb, hc] using this

/-- The injectivity condition is preserved by Minkowski combinations (it is made of conditions
linear in `K`). -/
lemma opt_comb_injectivity (h₁ : IsKi K₁) (h₂ : IsKi K₂) (hc : c ∈ Icc (0 : ℝ) 1) :
    SatisfiesInjectivity ((1 - c) • K₁ + c • K₂) := by
  obtain ⟨hcap₁, ⟨⟨r₁, s₁, hr₁, hs₁, hr₁0, hs₁0, hσr₁, hσs₁⟩, i2₁, i3₁⟩, -⟩ := h₁
  obtain ⟨hcap₂, ⟨⟨r₂, s₂, hr₂, hs₂, hr₂0, hs₂0, hσr₂, hσs₂⟩, i2₂, i3₂⟩, -⟩ := h₂
  have hcb₁ := hcap₁.2.1
  have hcb₂ := hcap₂.2.1
  have hc0 := hc.1
  have hc1 : 0 ≤ 1 - c := sub_nonneg.mpr hc.2
  have hσ := opt_sigma_comb hcb₁ hcb₂ hc
  have hx := opt_innerCorner_comb hcb₁ hcb₂ hc
  refine ⟨⟨fun t => (1 - c) * r₁ t + c * r₂ t, fun t => (1 - c) * s₁ t + c * s₂ t,
    by fun_prop, by fun_prop, fun t => by nlinarith [hr₁0 t, hr₂0 t],
    fun t => by nlinarith [hs₁0 t, hs₂0 t], ?_, ?_⟩, ?_, ?_⟩
  · rw [hσ, MeasureTheory.Measure.restrict_add, MeasureTheory.Measure.restrict_smul,
      MeasureTheory.Measure.restrict_smul, hσr₁, hσr₂,
      ← MeasureTheory.withDensity_smul _ (by fun_prop),
      ← MeasureTheory.withDensity_smul _ (by fun_prop),
      ← MeasureTheory.withDensity_add_left (by fun_prop)]
    congr 1
    funext t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [ENNReal.ofReal_add (mul_nonneg hc1 (hr₁0 t)) (mul_nonneg hc0 (hr₂0 t)),
      ENNReal.ofReal_mul hc1, ENNReal.ofReal_mul hc0]
  · rw [hσ, MeasureTheory.Measure.restrict_add, MeasureTheory.Measure.restrict_smul,
      MeasureTheory.Measure.restrict_smul, hσs₁, hσs₂,
      ← MeasureTheory.withDensity_smul _ (by fun_prop),
      ← MeasureTheory.withDensity_smul _ (by fun_prop),
      ← MeasureTheory.withDensity_add_left (by fun_prop)]
    congr 1
    funext t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [ENNReal.ofReal_add (mul_nonneg hc1 (hs₁0 _)) (mul_nonneg hc0 (hs₂0 _)),
      ENNReal.ofReal_mul hc1, ENNReal.ofReal_mul hc0]
  · unfold InjCond2
    rw [hx]
    exact (i2₁.const_smul (1 - c)).add (i2₂.const_smul c)
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

/-- The horizontal slice `{x | (x, y) ∈ K}` of a set. -/
private lemma opt_slice_closed {K : Set (ℝ × ℝ)} (hK : IsClosed K) (y : ℝ) :
    IsClosed ((fun x : ℝ => (x, y)) ⁻¹' K) :=
  hK.preimage (by fun_prop)

/-- For `y ∈ [0, 1]`, the slice of a cap at height `y` is a nonempty compact interval
`[m, M]`. -/
private lemma opt_cap_slice (hK : IsCap K₁ (π / 2)) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    ∃ m M : ℝ, (m, y) ∈ K₁ ∧ (M, y) ∈ K₁ ∧ (fun x : ℝ => (x, y)) ⁻¹' K₁ ⊆ Icc m M := by
  have hcb := hK.2.1
  set S := (fun x : ℝ => (x, y)) ⁻¹' K₁
  have hSb : S ⊆ Icc (-supp K₁ π) (supp K₁ 0) := fun x hx => opt_cap_fst_le hK hx
  have hSc : IsCompact S := (isCompact_Icc).of_isClosed_subset (opt_slice_closed hcb.isClosed y) hSb
  -- a point of `K` at height `y`
  obtain ⟨T, hT, hTe⟩ := exists_dot_eq_supp hcb.2.1 hcb.1 (π / 2)
  rw [hK.2.2.2.1, opt_uvec_pi_div_two] at hTe
  simp only [opt_dot_mk, mul_zero, mul_one, zero_add] at hTe
  have hA := opt_cap_A_mem hK
  have hP := hcb.2.2 hA hT (by linarith [hy.2] : (0 : ℝ) ≤ 1 - y) hy.1 (by ring)
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
  have hslice : ∀ y : ℝ, ENNReal.ofReal (1 - c) * volume ((fun x : ℝ => (x, y)) ⁻¹' K₁) +
      ENNReal.ofReal c * volume ((fun x : ℝ => (x, y)) ⁻¹' K₂) ≤
      volume ((fun x : ℝ => (x, y)) ⁻¹' M) := by
    intro y
    by_cases hy : y ∈ Icc (0 : ℝ) 1
    · obtain ⟨m₁, M₁, hm₁, hM₁, hS₁⟩ := opt_cap_slice h₁ hy
      obtain ⟨m₂, M₂, hm₂, hM₂, hS₂⟩ := opt_cap_slice h₂ hy
      have hmM : ∀ {a b : ℝ}, (a, y) ∈ K₁ → (b, y) ∈ K₂ → ((1 - c) * a + c * b, y) ∈ M := by
        intro a b ha hb
        convert opt_comb_mem (c := c) ha hb using 1
        ext
        · simp
        · simp; ring
      have hconv : Icc ((1 - c) * m₁ + c * m₂) ((1 - c) * M₁ + c * M₂) ⊆
          (fun x : ℝ => (x, y)) ⁻¹' M := by
        have hSconv : Convex ℝ ((fun x : ℝ => (x, y)) ⁻¹' M) := by
          intro x hx x' hx' a b ha hb hab
          have := hMcb.2.2 hx hx' ha hb hab
          show (a • x + b • x', y) ∈ M
          convert this using 1
          ext
          · simp
          · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
            rw [← add_mul, hab, one_mul]
        exact hSconv.ordConnected.out (hmM hm₁ hm₂) (hmM hM₁ hM₂)
      have hle₁ : m₁ ≤ M₁ := (hS₁ hm₁).2
      have hle₂ : m₂ ≤ M₂ := (hS₂ hm₂).2
      calc ENNReal.ofReal (1 - c) * volume ((fun x : ℝ => (x, y)) ⁻¹' K₁) +
            ENNReal.ofReal c * volume ((fun x : ℝ => (x, y)) ⁻¹' K₂)
          ≤ ENNReal.ofReal (1 - c) * volume (Icc m₁ M₁) + ENNReal.ofReal c * volume (Icc m₂ M₂) := by
            gcongr
        _ = volume (Icc ((1 - c) * m₁ + c * m₂) ((1 - c) * M₁ + c * M₂)) := by
            rw [Real.volume_Icc, Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_mul hc1,
              ← ENNReal.ofReal_mul hc0,
              ← ENNReal.ofReal_add (mul_nonneg hc1 (by linarith)) (mul_nonneg hc0 (by linarith))]
            congr 1; ring
        _ ≤ volume ((fun x : ℝ => (x, y)) ⁻¹' M) := measure_mono hconv
    · have e₁ : (fun x : ℝ => (x, y)) ⁻¹' K₁ = ∅ := by
        ext x
        simp only [mem_preimage, mem_empty_iff_false, iff_false]
        intro hx
        exact hy ⟨(opt_cap_mem_strip h₁ hx).1, (opt_cap_mem_strip h₁ hx).2⟩
      have e₂ : (fun x : ℝ => (x, y)) ⁻¹' K₂ = ∅ := by
        ext x
        simp only [mem_preimage, mem_empty_iff_false, iff_false]
        intro hx
        exact hy ⟨(opt_cap_mem_strip h₂ hx).1, (opt_cap_mem_strip h₂ hx).2⟩
      simp [e₁, e₂]
  have hmeas₁ : MeasurableSet K₁ := hcb₁.isClosed.measurableSet
  have hmeas₂ : MeasurableSet K₂ := hcb₂.isClosed.measurableSet
  have hmeasM : MeasurableSet M := hMcb.isClosed.measurableSet
  have hvol : ENNReal.ofReal (1 - c) * volume K₁ + ENNReal.ofReal c * volume K₂ ≤ volume M := by
    rw [Measure.volume_eq_prod, Measure.prod_apply_symm hmeas₁, Measure.prod_apply_symm hmeas₂,
      Measure.prod_apply_symm hmeasM, ← lintegral_const_mul _ (measurable_measure_prodMk_right hmeas₁),
      ← lintegral_const_mul _ (measurable_measure_prodMk_right hmeas₂),
      ← lintegral_add_left ((measurable_measure_prodMk_right hmeas₁).const_mul _)]
    exact lintegral_mono hslice
  have hfin₁ : volume K₁ ≠ ⊤ := hcb₁.2.1.measure_lt_top.ne
  have hfin₂ : volume K₂ ≠ ⊤ := hcb₂.2.1.measure_lt_top.ne
  have hfinM : volume M ≠ ⊤ := hMcb.2.1.measure_lt_top.ne
  unfold area
  have := ENNReal.toReal_mono hfinM hvol
  rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin₁)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin₂), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc1, ENNReal.toReal_ofReal hc0] at this

end Comb

/-- **Theorem 8.1.1** (`thm:cap-space-special`) (1): `𝒦^i` is closed under Minkowski combinations.
(The paper's proof uses the Brunn–Minkowski inequality for the area condition. We use instead that the
horizontal slices of `(1 - c) K₁ + c K₂` contain the combinations of the slices of `K₁` and `K₂`,
which with Fubini gives `|(1 - c) K₁ + c K₂| ≥ (1 - c) |K₁| + c |K₂|`; see `opt_comb_area`.) -/
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
/-- The half-plane `H̆_K^L = H_K^d(φ^L)` bounded from below by `d_K^L = d_K(φ^L)` (Definition 8.1.5). -/
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

/-! ### Auxiliary facts on `B_K`, `D_K`, `W_K^R`, `Z_K^L` (package I) -/

lemma opt_wRight_eq (φ : ℝ) (K : Set (ℝ × ℝ)) : wRight φ K = ((supp K φ - 1) / cos φ, 0) := rfl

lemma opt_zLeft_eq (φ : ℝ) (K : Set (ℝ × ℝ)) :
    zLeft φ K = ((1 - supp K (π - φ)) / cos φ, 0) := by
  simp only [zLeft, wedgeZ, opt_vvec_pi_div_two, show π / 2 - (π / 2 - φ) = φ by ring,
    show π / 2 - φ + π / 2 = π - φ by ring]
  ext
  · simp only [Prod.smul_mk, smul_eq_mul]; ring
  · simp

lemma opt_halfPlus_isClosed (t c : ℝ) : IsClosed (halfPlus t c) :=
  isClosed_le continuous_const (by unfold dot; fun_prop)

lemma opt_halfPlus_convex (t c : ℝ) : Convex ℝ (halfPlus t c) := by
  intro x hx y hy a b ha hb hab
  simp only [halfPlus, mem_ofPred_eq] at *
  rw [dot_add_left, dot_smul_left, dot_smul_left]
  have e : c = a * c + b * c := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

lemma opt_rightBody_A_mem {φ : ℝ} (hφ : 0 ≤ φ) {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) :
    (supp K 0, (0 : ℝ)) ∈ rightBody φ K := by
  refine ⟨opt_cap_A_mem hK, ?_⟩
  simp only [mem_iInter₂]
  intro t ht
  exact opt_cap_A_mem_halfB hK ⟨le_trans hφ ht.1, ht.2⟩

lemma opt_leftBody_C_mem {φ : ℝ} (hφ : 0 ≤ φ) {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) :
    (-supp K π, (0 : ℝ)) ∈ leftBody φ K := by
  refine ⟨opt_cap_C_mem hK, ?_⟩
  simp only [mem_iInter₂]
  intro t ht
  exact opt_cap_C_mem_halfD hK ⟨ht.1, by linarith [ht.2]⟩

lemma opt_rightBody_isConvexBody {φ : ℝ} (hφ : 0 ≤ φ) {K : Set (ℝ × ℝ)}
    (hK : IsCap K (π / 2)) : IsConvexBody (rightBody φ K) := by
  refine ⟨⟨_, opt_rightBody_A_mem hφ hK⟩, ?_, ?_⟩
  · exact hK.2.1.2.1.inter_right
      (isClosed_biInter fun t _ => opt_halfPlus_isClosed t (supp K t - 1))
  · exact hK.2.1.2.2.inter (convex_iInter₂ fun t _ => opt_halfPlus_convex t (supp K t - 1))

lemma opt_leftBody_isConvexBody {φ : ℝ} (hφ : 0 ≤ φ) {K : Set (ℝ × ℝ)}
    (hK : IsCap K (π / 2)) : IsConvexBody (leftBody φ K) := by
  refine ⟨⟨_, opt_leftBody_C_mem hφ hK⟩, ?_, ?_⟩
  · exact hK.2.1.2.1.inter_right
      (isClosed_biInter fun t _ => opt_halfPlus_isClosed (t + π / 2) (supp K (t + π / 2) - 1))
  · exact hK.2.1.2.2.inter
      (convex_iInter₂ fun t _ => opt_halfPlus_convex (t + π / 2) (supp K (t + π / 2) - 1))

/-- **Lemma 8.1.3** (`lem:cap-right-left-parallelogram`). `P_K^R` is the parallelogram bounded by
`l(π/2, 0)`, `l(π/2, 1)`, `a_K(φ^R)` and `b_K(φ^R)`, with base `sec φ` on `l(π/2, 0)` starting at its
lower-left corner `W_K^R`. -/
theorem lemma8_1_3 {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) (K : Set (ℝ × ℝ)) :
    paraR φ K = {p | 0 ≤ p.2 ∧ p.2 ≤ 1 ∧ supp K φ - 1 ≤ dot p (uvec φ) ∧ dot p (uvec φ) ≤ supp K φ} ∧
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
  simp only [mem_inter_iff, mem_ofPred_eq, line, opt_uvec_pi_div_two, opt_dot_mk, mem_image,
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

/-- **Lemma 8.1.4** (`lem:cap-left-right-disjoint`). For `K ∈ 𝒦^i`, `K ∩ H̆_K^R` and `K ∩ H̆_K^L` are
disjoint. -/
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
  have hp2 := opt_cap_mem_strip hcap hpK
  have harea := opt_area_le_of_fst_bounds hcap
    (fun q hq => opt_cap_fst_le_phi hcap hc hs0.le hq)
  have hKa := hK.2.2
  have hsum : supp K φ + supp K (π - φ) ≤ 2 + 2 * sin φ := by nlinarith
  have h3 : area K * cos φ ≤ supp K φ + supp K (π - φ) := by
    have e : supp K φ / cos φ - -supp K (π - φ) / cos φ =
        (supp K φ + supp K (π - φ)) / cos φ := by ring
    rw [e, le_div_iff₀ hc] at harea
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hKa hc.le]

/-- `1 ≤ sin t + cos t` and `2 sin t cos t ≤ 1` when `sin t, cos t ≥ 0`. -/
lemma opt_sin_cos_bounds {t : ℝ} (hs : 0 ≤ sin t) (hc : 0 ≤ cos t) :
    1 ≤ sin t + cos t ∧ 2 * (sin t * cos t) ≤ 1 := by
  have e := sin_sq_add_cos_sq t
  constructor
  · nlinarith [mul_nonneg hs (sub_nonneg.mpr (sin_le_one t)),
      mul_nonneg hc (sub_nonneg.mpr (cos_le_one t))]
  · nlinarith [sq_nonneg (sin t - cos t)]

/-- `𝒩(K) ∩ H̆_K^R` and `H̆_K^L` are disjoint. Adding the inequalities of `H̆_K^R` and `H̆_K^L` gives
height at least `(h_K(φ) + h_K(π - φ) - 2) / (2 sin φ) ≥ (W₀ cos φ - 2) / (2 sin φ)`, where
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
  have hr2 := opt_cap_mem_strip hcap hr
  have hr1' := opt_cap_fst_le hcap hr'
  have hr2' := opt_cap_mem_strip hcap hr'
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
  rw [opt_cap_aK_zero hK, opt_cap_cK_pi_div_two hK]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hA := opt_cap_A_mem hK
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
  · simp [suppLine, line, hK.2.2.2.2.2.1, opt_uvec_three_pi_div_two]
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
    · have := opt_cap_gapW hcap hφ'
      rw [div_lt_iff₀ hc]; linarith
  · rw [opt_zLeft_eq]
    apply opt_mem_bottom_edge hcap
    · have := opt_cap_gapZ hcap hψ'
      rw [show π / 2 - φ + π / 2 = π - φ by ring, sin_pi_div_two_sub] at this
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
    · exact opt_continuousOn_dot (h2.continuousOn.mono (Icc_subset_Icc_left hφ.1.le)) _
    · intro s hs
      rw [interior_Icc] at hs
      have hs' : s ∈ Ioo 0 (π / 2) := ⟨lt_trans hφ.1 hs.1, hs.2⟩
      rw [(opt_hasDerivAt_dot (opt_inj_hasDerivAt h2 hs') (uvec φ)).deriv,
        opt_dot_frame_u _ φ s]
      obtain ⟨hu, hv⟩ := h3 s hs'
      have hc : 0 < cos (φ - s) :=
        cos_pos_of_mem_Ioo ⟨by linarith [hs.1, hs.2, hφ.1], by linarith [hs.1]⟩
      have hsn : sin (φ - s) < 0 :=
        sin_neg_of_neg_of_neg_pi_lt (by linarith [hs.1]) (by linarith [hs.2, hφ.1])
      nlinarith [mul_pos hc (neg_pos.mpr hu), mul_pos (neg_pos.mpr hsn) hv]
  have := hmono ⟨le_rfl, by linarith [hφ.2]⟩ ⟨ht.1.le, ht.2⟩ ht.1
  simpa [opt_innerCorner_dot_u] using this

/-- `t ↦ 𝐱_K(t) · v_{φ^L}` increases strictly on `[0, φ^L]`. -/
lemma opt_innerCorner_lt_left {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) {K : Set (ℝ × ℝ)} (hK : IsKi K)
    {t : ℝ} (ht : t ∈ Ico 0 (π / 2 - φ)) :
    dot (innerCorner K t) (vvec (π / 2 - φ)) < supp K (π / 2 - φ + π / 2) - 1 := by
  obtain ⟨-, ⟨-, h2, h3⟩, -⟩ := hK
  have hpi := pi_pos
  have hmono : StrictMonoOn (fun s => dot (innerCorner K s) (vvec (π / 2 - φ)))
      (Icc 0 (π / 2 - φ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact opt_continuousOn_dot
        (h2.continuousOn.mono (Icc_subset_Icc_right (by linarith [hφ.1]))) _
    · intro s hs
      rw [interior_Icc] at hs
      have hs' : s ∈ Ioo 0 (π / 2) := ⟨hs.1, by linarith [hs.2, hφ.1]⟩
      rw [(opt_hasDerivAt_dot (opt_inj_hasDerivAt h2 hs') _).deriv, opt_dot_frame_v _ _ s]
      obtain ⟨hu, hv⟩ := h3 s hs'
      have hc : 0 < cos (π / 2 - φ - s) :=
        cos_pos_of_mem_Ioo ⟨by linarith [hs.2], by linarith [hs.1, hφ.1]⟩
      have hsn : 0 < sin (π / 2 - φ - s) :=
        sin_pos_of_pos_of_lt_pi (by linarith [hs.2]) (by linarith [hs.1, hφ.1])
      nlinarith [mul_pos hsn (neg_pos.mpr hu), mul_pos hc hv]
  have := hmono ⟨ht.1, ht.2.le⟩ ⟨by linarith [ht.1, ht.2], le_rfl⟩ ht.2
  simpa [opt_innerCorner_dot_v] using this

/-- **Lemma 8.1.6** (`lem:monotonicity-intervals`) (1). For `K ∈ 𝒦^i` and `t ∈ (φ^R, π/2]`, the inner
corner `𝐱_K(t)` is outside `H̆_K^R`, `H̆_K^R ∩ Q_K⁻(t) = H̆_K^R \ H_K^b(t)`, and
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
      have e1 := opt_dot_frame_u p φ t
      have e2 := opt_dot_frame_u (innerCorner K t) φ t
      rw [opt_innerCorner_dot_u, opt_innerCorner_dot_v] at e2
      have hc : 0 ≤ cos (φ - t) :=
        (cos_pos_of_mem_Ioo ⟨by linarith [ht.2, hφ.1], by linarith [ht.1]⟩).le
      have hsn : sin (φ - t) ≤ 0 :=
        (sin_neg_of_neg_of_neg_pi_lt (by linarith [ht.1]) (by linarith [ht.2, hφ.1])).le
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hc (by linarith : dot p (uvec t) - (supp K t - 1) ≤ 0),
        mul_nonpos_of_nonpos_of_nonneg hsn
          (by linarith : 0 ≤ dot p (vvec t) - (supp K (t + π / 2) - 1))]
  refine ⟨?_, h2, ?_⟩
  · simp only [hRight, halfB, halfPlus, mem_ofPred_eq, not_le]; exact hlt
  · ext p
    have h2' := Set.ext_iff.mp h2 p
    simp only [wedge, fan, mem_inter_iff, mem_sdiff] at h2' ⊢
    tauto

/-- **Lemma 8.1.6** (2), the mirror statement for `t ∈ [0, φ^L)`. -/
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
      rw [opt_innerCorner_dot_u, opt_innerCorner_dot_v] at e2
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
  have hA := opt_rightBody_A_mem (by linarith [hφ.1] : 0 ≤ φ) hK.1
  have : supp (rightBody φ K) (π + t) ≤ 1 - supp K t := by
    show sSup _ ≤ _
    refine csSup_le ((Set.Nonempty.image _ ⟨_, hA⟩)) ?_
    rintro _ ⟨p, hp, rfl⟩
    have hpt : p ∈ halfB K t := (mem_iInter₂.mp hp.2) t ht
    simp only [halfB, halfPlus, mem_ofPred_eq] at hpt
    simp only [show π + t = t + π by ring, uvec_add_pi, dot_neg_right]
    linarith
  linarith

/-- If `p ∈ K` maximizes `q · v_α` over the points `q ∈ K` with `q · u_α = c` (the end point of the
chord of `K` on the line `l(α, c)`), then `K` has a supporting line at `p` with normal angle in
`[α, α + π]`. -/
lemma opt_exists_normal_of_isMax {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {α c : ℝ}
    {p : ℝ × ℝ} (hp : p ∈ K) (hpl : dot p (uvec α) = c)
    (hmax : ∀ q ∈ K, dot q (uvec α) = c → dot q (vvec α) ≤ dot p (vvec α)) :
    ∃ θ ∈ Icc α (α + π), dot p (uvec θ) = supp K θ := by
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

/-- `sin(β - α) (p · u_t) = sin(β - t) (p · u_α) + sin(t - α) (p · u_β)`. -/
lemma opt_dot_interp (p : ℝ × ℝ) (α β t : ℝ) :
    sin (β - α) * dot p (uvec t) = sin (β - t) * dot p (uvec α) + sin (t - α) * dot p (uvec β) := by
  simp only [dot, uvec, sin_sub]
  ring

/-- Sublinearity of the support function: `sin(β - α) h_K(t) ≤ sin(β - t) h_K(α) + sin(t - α) h_K(β)`
for `α ≤ t ≤ β ≤ α + π`. -/
lemma opt_supp_interp {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {α β t : ℝ} (hαt : α ≤ t)
    (htβ : t ≤ β) (hβα : β ≤ α + π) :
    sin (β - α) * supp K t ≤ sin (β - t) * supp K α + sin (t - α) * supp K β := by
  obtain ⟨q, hq, hqt⟩ := exists_dot_eq_supp hK.2.1 hK.1 t
  have h1 := dot_le_supp hK.2.1 hq α
  have h2 := dot_le_supp hK.2.1 hq β
  have hs1 : 0 ≤ sin (β - t) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs2 : 0 ≤ sin (t - α) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rw [← hqt, opt_dot_interp]
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

/-- The topmost point of `K` on `b_K^R` lies in `B_K` (the core of the proof of Lemma 8.1.7 (2); see the
module docstring). -/
lemma opt_exists_rightBody_on_line {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)}
    (hK : IsKi K) :
    ∃ p ∈ rightBody φ K, dot p (uvec φ) = supp K φ - 1 := by
  obtain ⟨hφ0, hφ4, -, hc9, hs0⟩ := opt_phi_bounds hφ
  have hpi := two_le_pi
  have hc : 0 < cos φ := by linarith
  have hcap := hK.1
  have hcb := hcap.2.1
  set L := K ∩ {q | dot q (uvec φ) = supp K φ - 1} with hL
  have hLc : IsCompact L :=
    hcap.2.1.2.1.inter_right (isClosed_eq (by unfold dot; fun_prop) continuous_const)
  have hWL : wRight φ K ∈ L := by
    refine ⟨(lemma8_1_5 hφ hK).1.1.1, ?_⟩
    simp only [mem_ofPred_eq, opt_wRight_eq, dot, uvec, zero_mul, add_zero]
    field_simp
  obtain ⟨p, hpL, hpmax⟩ := hLc.exists_isMaxOn ⟨_, hWL⟩
    (by unfold dot; fun_prop : Continuous fun q : ℝ × ℝ => dot q (vvec φ)).continuousOn
  obtain ⟨hpK, hpl⟩ := hpL
  have hpl' : dot p (uvec φ) = supp K φ - 1 := hpl
  -- a supporting line of `K` at `p`, with normal angle `θ ∈ [φ, φ + π]`
  obtain ⟨θ, hθ, hpθ⟩ := opt_exists_normal_of_isMax hcb hpK hpl'
    (fun q hq hql => hpmax ⟨hq, hql⟩)
  have hp2 := opt_cap_mem_strip hcap hpK
  -- `θ > φ + π/2` would put `p` beyond `C_K(φ)`, contradicting `g_K(φ) > 1`
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
      rw [uvec_add_pi_div_two]; exact opt_dot_frame_u q θ φ
    have hcos : cos (θ - φ) < 0 := cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [hθ.2])
    have hsin : 0 ≤ sin (θ - φ) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθ.2])
    have key : dot p (uvec φ) ≤ dot c (uvec φ) := by
      have ep := e1 p
      have ec := e1 c
      nlinarith [mul_le_mul_of_nonneg_left h1 hsin]
    rw [inj_gPlus_eq, vvec_add_pi_div_two, dot_neg_right, ← hcdef] at hg
    linarith
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
      have hE := opt_dot_interp p φ θ s
      have hsinpos : 0 < sin (θ - φ) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have hmono : sin (θ - s) ≤ sin (θ - φ) :=
        sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith [hs.1])
      have hs1 : 0 ≤ sin (s - φ) := sin_nonneg_of_nonneg_of_le_pi (by linarith [hs.1]) (by linarith)
      rw [hpθ, hpl'] at hE
      nlinarith
  · -- between `θ` and `π/2`: `p` lies in the strip `0 ≤ y ≤ 1`
    have hθπ : θ < π / 2 := lt_of_lt_of_le hsθ hs.2
    have hI := opt_supp_interp hcb hsθ.le hs.2 (by linarith [hθ.1])
    have hE := opt_dot_interp p θ (π / 2) s
    rw [hcap.2.2.2.1] at hI
    have hpy : dot p (uvec (π / 2)) = p.2 := by rw [opt_uvec_pi_div_two]; simp [dot]
    rw [hpθ, hpy] at hE
    have hcpos : 0 < sin (π / 2 - θ) := by rw [sin_pi_div_two_sub]; exact cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθπ⟩
    have hmono : sin (s - θ) ≤ sin (π / 2 - θ) :=
      sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith [hθ.1]) (by linarith [hs.2])
    have hs1 : 0 ≤ sin (s - θ) :=
      sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθ.1, hs.2])
    have hp2' : 0 ≤ p.2 := hp2.1
    nlinarith [mul_le_mul_of_nonneg_left hp2.2 hs1, mul_nonneg hs1 hp2']

/-- **Lemma 8.1.7** (2): equality at `t = φ^R, π/2`, so `l_B(3π/2) = l(π/2, 0)` and
`l_B(π + φ^R) = b_K^R` (see the module docstring for the proof). -/
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
  have hB3 : supp (rightBody φ K) (3 * π / 2) = 0 := by
    apply le_antisymm
    · have := supp_mono inter_subset_left ⟨_, hA⟩ hcap.2.1.2.1 (3 * π / 2)
      rwa [hcap.2.2.2.2.2.1] at this
    · have := dot_le_supp hBcb.2.1 hA (3 * π / 2)
      rw [opt_uvec_three_pi_div_two] at this
      simpa using this
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [show π + π / 2 = 3 * π / 2 by ring, hB3, hcap.2.2.2.1]; norm_num
  · ext q
    simp only [suppLine, line, mem_ofPred_eq, hB3, opt_uvec_three_pi_div_two, opt_uvec_pi_div_two,
      opt_dot_mk]
    constructor <;> intro h <;> linarith
  · rw [proposition2_2_2_wallB]
    ext q
    simp only [suppLine, line, mem_ofPred_eq]
    rw [show π + φ = φ + π by ring, uvec_add_pi, dot_neg_right]
    have e : supp (rightBody φ K) (φ + π) = 1 - supp K φ := by
      rw [show φ + π = π + φ by ring]; linarith
    rw [e]
    constructor <;> intro h <;> linarith

/-- **Lemma 8.1.7** (3): `h_K(π/2 + t) + h_D(3π/2 + t) ≤ 1` on `[0, φ^L]`.

**Added hypothesis `φ ∈ [0.039, 0.04]`**, for the same reason as in Lemma 8.1.7 (1): for `φ = -π` the
set `D_K` is empty. -/
theorem lemma8_1_7_three {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)} (hK : IsKi K)
    {t : ℝ} (ht : t ∈ Icc 0 (π / 2 - φ)) :
    supp K (π / 2 + t) + supp (leftBody φ K) (3 * π / 2 + t) ≤ 1 := by
  have hC := opt_leftBody_C_mem (by linarith [hφ.1] : 0 ≤ φ) hK.1
  have : supp (leftBody φ K) (3 * π / 2 + t) ≤ 1 - supp K (π / 2 + t) := by
    show sSup _ ≤ _
    refine csSup_le ((Set.Nonempty.image _ ⟨_, hC⟩)) ?_
    rintro _ ⟨p, hp, rfl⟩
    have hpt : p ∈ halfD K t := (mem_iInter₂.mp hp.2) t ht
    simp only [halfD, halfPlus, mem_ofPred_eq] at hpt
    simp only [show 3 * π / 2 + t = t + π / 2 + π by ring, uvec_add_pi, dot_neg_right,
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
  set L := K ∩ {q | dot q (vvec (π / 2 - φ)) = supp K (π / 2 - φ + π / 2) - 1} with hL
  have hLc : IsCompact L :=
    hcap.2.1.2.1.inter_right (isClosed_eq (by unfold dot; fun_prop) continuous_const)
  have hZL : zLeft φ K ∈ L := by
    refine ⟨(lemma8_1_5 hφ hK).2.1.1, ?_⟩
    simp only [mem_ofPred_eq, opt_zLeft_eq, dot, vvec, sin_pi_div_two_sub, zero_mul, add_zero,
      show π / 2 - φ + π / 2 = π - φ by ring]
    field_simp
    ring
  obtain ⟨p, hpL, hpmax⟩ := hLc.exists_isMaxOn ⟨_, hZL⟩
    (by unfold dot; fun_prop : Continuous fun q : ℝ × ℝ => dot q (uvec (π / 2 - φ))).continuousOn
  obtain ⟨hpK, hpl⟩ := hpL
  have hpl' : dot p (vvec (π / 2 - φ)) = supp K (π / 2 - φ + π / 2) - 1 := hpl
  -- the line is `l(-φ, 1 - h_K(φ^L + π/2))`, traversed in the direction `v_{-φ} = u_{φ^L}`
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
  have hp2 := opt_cap_mem_strip hcap hpK
  -- `θ < φ^L` would put `p` before `A_K(φ^L)`, contradicting `f_K(φ^L) > 1`
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
        sin (θ - (π / 2 - φ)) * dot q (vvec (π / 2 - φ)) := fun q => opt_dot_frame_u q θ _
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
  have hpy : dot p (uvec (π / 2)) = p.2 := by rw [opt_uvec_pi_div_two]; simp [dot]
  have key : ∀ t ∈ Icc (π / 2) (π - φ), supp K t - 1 ≤ dot p (uvec t) := by
    intro t ht
    rcases le_or_gt θ t with hθt | hθt
    · -- between `θ` and `π - φ`: `d` is bounded by `d(π - φ) = 1`
      rcases eq_or_lt_of_le hθ.2 with hθe | hθe
      · have : t = π - φ := le_antisymm ht.2 (by linarith)
        rw [this]; linarith
      · have hI := opt_supp_interp hcb hθt ht.2 (by linarith)
        have hE := opt_dot_interp p θ (π - φ) t
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
      have hE := opt_dot_interp p (π / 2) θ t
      rw [hcap.2.2.2.1] at hI
      rw [hpθ, hpy] at hE
      have hsinpos : 0 < sin (θ - π / 2) :=
        sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ.2])
      have hmono : sin (θ - t) ≤ sin (θ - π / 2) :=
        sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith [hθ.2]) (by linarith [ht.1])
      have hs1 : 0 ≤ sin (θ - t) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθ.2, ht.1])
      have hs2 : 0 ≤ sin (t - π / 2) := sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht.2])
      nlinarith [mul_le_mul_of_nonneg_left hp2.2 hs1, mul_nonneg hs1 hp2.1]
  refine ⟨p, ⟨hpK, ?_⟩, hpl'⟩
  simp only [mem_iInter₂]
  intro s hs
  simp only [halfD, halfPlus, mem_ofPred_eq]
  exact key (s + π / 2) ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- **Lemma 8.1.7** (4): equality at `t = 0, φ^L` (the paper writes `φ^R`), so `l_D(3π/2) = l(π/2, 0)`
and `l_D(3π/2 + φ^L) = d_K^L`. -/
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
  have hD3 : supp (leftBody φ K) (3 * π / 2) = 0 := by
    apply le_antisymm
    · have := supp_mono inter_subset_left ⟨_, hC⟩ hcap.2.1.2.1 (3 * π / 2)
      rwa [hcap.2.2.2.2.2.1] at this
    · have := dot_le_supp hDcb.2.1 hC (3 * π / 2)
      rw [opt_uvec_three_pi_div_two] at this
      simpa using this
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
    simp only [suppLine, line, mem_ofPred_eq, hD3, opt_uvec_three_pi_div_two, opt_uvec_pi_div_two,
      opt_dot_mk]
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

end MovingSofa
