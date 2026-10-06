module

public import MovingSofaStability.BaekDeficit

/-!
# The enlarged nonsmooth triple domain

This is the domain of stability note 05: normalized right-angle caps, arbitrary
convex tail bodies, and the original linear wall constraints. No
curvature-density, injectivity, or area threshold is assumed.

The convex-domain construction and `wide_upperQ_decomposition` are proved here.
The further identity `upperP + mamikonS = affineCore` for all nonsmooth caps,
and the enlarged-domain first variation at Gerver, are separate obligations.
-/

@[expose] public section
noncomputable section

open Real Set
open scoped Pointwise
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- The original wall constraints, with `IsCap` instead of `IsKi`. -/
def InWideL (φ : ℝ) (K B D : Set (ℝ × ℝ)) : Prop :=
  IsCap K (π / 2) ∧ IsConvexBody B ∧ IsConvexBody D ∧ B ⊆ K ∧ D ⊆ K ∧
    (∀ t ∈ Icc φ (π / 2), supp K t + supp B (π + t) ≤ 1) ∧
    supp K φ + supp B (π + φ) = 1 ∧ supp K (π / 2) + supp B (π + π / 2) = 1 ∧
    (∀ t ∈ Icc 0 (π / 2 - φ), supp K (π / 2 + t) + supp D (3 * π / 2 + t) ≤ 1) ∧
    supp K (π / 2 + 0) + supp D (3 * π / 2 + 0) = 1 ∧
    supp K (π / 2 + (π / 2 - φ)) + supp D (3 * π / 2 + (π / 2 - φ)) = 1

theorem inWideL_of_inL {φ : ℝ} {K B D : Set (ℝ × ℝ)} (h : InL φ K B D) :
    InWideL φ K B D := ⟨h.1.1, h.2⟩

theorem inL_of_inWideL {φ : ℝ} {K B D : Set (ℝ × ℝ)}
    (h : InWideL φ K B D) (hK : IsKi K) : InL φ K B D := ⟨hK, h.2⟩

/-- Endpoint support identities require only the cap normalization and contacts. -/
theorem inWideL_supp {φ : ℝ} {K B D : Set (ℝ × ℝ)} (h : InWideL φ K B D) :
    supp B (3 * π / 2) = 0 ∧ supp D (3 * π / 2) = 0 ∧
      supp B (π + φ) = 1 - supp K φ ∧
      supp D (3 * π / 2 + (π / 2 - φ)) = 1 - supp K (π - φ) := by
  obtain ⟨hK, -, -, -, -, -, e1, e1', -, e2, e2'⟩ := h
  have hK2 : supp K (π / 2) = 1 := hK.2.2.2.1
  rw [add_zero, add_zero, hK2] at e2
  rw [hK2, show π + π / 2 = 3 * π / 2 by ring] at e1'
  rw [show π / 2 + (π / 2 - φ) = π - φ by ring] at e2'
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Nonsmooth feasible triples are closed under componentwise Minkowski combinations. -/
theorem inWideL_comb {φ : ℝ} {K₁ B₁ D₁ K₂ B₂ D₂ : Set (ℝ × ℝ)}
    (h₁ : InWideL φ K₁ B₁ D₁) (h₂ : InWideL φ K₂ B₂ D₂)
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    InWideL φ ((1 - c) • K₁ + c • K₂) ((1 - c) • B₁ + c • B₂)
      ((1 - c) • D₁ + c • D₂) := by
  obtain ⟨hK₁, hB₁, hD₁, hBK₁, hDK₁, i1, e1, e1', i2, e2, e2'⟩ := h₁
  obtain ⟨hK₂, hB₂, hD₂, hBK₂, hDK₂, j1, f1, f1', j2, f2, f2'⟩ := h₂
  have sK := supp_comb hK₁.2.1 hK₂.2.1 hc
  have sB := supp_comb hB₁ hB₂ hc
  have sD := supp_comb hD₁ hD₂ hc
  have hc0 := hc.1
  have hc1 : 0 ≤ 1 - c := sub_nonneg.mpr hc.2
  refine ⟨opt_comb_isCap hK₁ hK₂ hc, isConvexBody_comb hB₁ hB₂,
    isConvexBody_comb hD₁ hD₂,
    Set.add_subset_add (Set.smul_set_mono hBK₁) (Set.smul_set_mono hBK₂),
    Set.add_subset_add (Set.smul_set_mono hDK₁) (Set.smul_set_mono hDK₂),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [sK, sB]
    nlinarith [mul_le_mul_of_nonneg_left (i1 t ht) hc1,
      mul_le_mul_of_nonneg_left (j1 t ht) hc0]
  · rw [sK, sB]; linear_combination (1 - c) * e1 + c * f1
  · rw [sK, sB]; linear_combination (1 - c) * e1' + c * f1'
  · intro t ht
    rw [sK, sD]
    nlinarith [mul_le_mul_of_nonneg_left (i2 t ht) hc1,
      mul_le_mul_of_nonneg_left (j2 t ht) hc0]
  · rw [sK, sD]; linear_combination (1 - c) * e2 + c * f2
  · rw [sK, sD]; linear_combination (1 - c) * e2' + c * f2'

def WideTriple (φ : ℝ) : Type :=
  {x : ConvexBodySet × ConvexBodySet × ConvexBodySet //
    InWideL φ x.1.1 x.2.1.1 x.2.2.1}

open Classical in
noncomputable def WideTriple.comb {φ : ℝ} (c : ℝ) (x y : WideTriple φ) : WideTriple φ :=
  if hc : c ∈ Icc (0 : ℝ) 1 then
    ⟨(convexBodyComb c x.1.1 y.1.1, convexBodyComb c x.1.2.1 y.1.2.1,
      convexBodyComb c x.1.2.2 y.1.2.2), by
        simpa [convexBodyComb, hc] using inWideL_comb x.2 y.2 hc⟩
  else x

theorem wideTriple_embeds (φ : ℝ) :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℝ E) (e : WideTriple φ → E),
      Function.Injective e ∧ ∀ c ∈ Icc (0 : ℝ) 1, ∀ x y,
        e (WideTriple.comb c x y) = (1 - c) • e x + c • e y := by
  obtain ⟨E, i1, i2, e, he, hlin⟩ := theorem7_1_1
  refine ⟨E × E × E, inferInstance, inferInstance,
    fun x => (e x.1.1, e x.1.2.1, e x.1.2.2), ?_, ?_⟩
  · intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2, h3⟩ := hxy
    apply Subtype.ext
    exact Prod.ext (he h1) (Prod.ext (he h2) (he h3))
  · intro c hc x y
    simp only [WideTriple.comb, hc, ↓reduceDIte]
    rw [hlin c hc, hlin c hc, hlin c hc]
    simp only [Prod.smul_mk, Prod.mk_add_mk]

noncomputable def wideDomain (φ : ℝ) : ConvexDomain (WideTriple φ) where
  comb := WideTriple.comb
  embeds := wideTriple_embeds φ

/-- The enlarged functional retains the original curve-area definition. -/
def wideUpperQ (φ : ℝ) (x : WideTriple φ) : ℝ :=
  upperQ φ x.1.1.1 x.1.2.1.1 x.1.2.2.1

def toWideTriple {φ : ℝ} (x : LTriple φ) : WideTriple φ :=
  ⟨x.1, inWideL_of_inL x.2⟩

@[simp] theorem wideUpperQ_toWide {φ : ℝ} (x : LTriple φ) :
    wideUpperQ φ (toWideTriple x) = upperQL φ x := rfl

/-- The tail decomposition extends to the enlarged domain. This proof is the
source's segment/arc argument with the weaker, sufficient endpoint hypotheses. -/
theorem wide_upperQ_decomposition {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K B D : Set (ℝ × ℝ)} (h : InWideL φ K B D) :
    upperQ φ K B D = upperP φ K - mamikonR φ B - mamikonL φ D := by
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  obtain ⟨hB3, hD3, hBa, hDb⟩ := inWideL_supp h
  obtain ⟨-, hBcb, hDcb, -⟩ := h
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have tR1 : tangentParam B (3 * π / 2) (π + φ) = wRight φ K := by
    simp only [tangentParam, show π + φ < 3 * π / 2 by linarith, ↓reduceIte]
    exact opt_vint_right_eq ⟨hφ0, by linarith⟩ hBa hB3
  have tR2 : tangentParam B (3 * π / 2) (3 * π / 2) = vminus B (3 * π / 2) := by
    simp only [tangentParam, lt_irrefl, ↓reduceIte]
  have tL1 : tangentParam D (3 * π / 2 + (π / 2 - φ)) (3 * π / 2) = zLeft φ K := by
    simp only [tangentParam, show 3 * π / 2 < 3 * π / 2 + (π / 2 - φ) by linarith,
      ↓reduceIte]
    exact opt_vint_left_eq hD3 hDb
  have tL2 : tangentParam D (3 * π / 2 + (π / 2 - φ)) (3 * π / 2 + (π / 2 - φ)) =
      vminus D (3 * π / 2 + (π / 2 - φ)) := by
    simp only [tangentParam, lt_irrefl, ↓reduceIte]
  have hlR := (theorem8_3_1 hBcb (t := 3 * π / 2) (a := π + φ) (b := 3 * π / 2)
    (by linarith) (by linarith) le_rfl).2.2
  have hlL := (theorem8_3_1 hDcb (t := 3 * π / 2 + (π / 2 - φ)) (a := 3 * π / 2)
    (b := 3 * π / 2 + (π / 2 - φ)) (by linarith) (by linarith) le_rfl).2.2
  rw [tR1, tR2] at hlR
  rw [tL1, tL2] at hlL
  have z1 := segArea_of_snd_eq_zero (p := wRight φ K) rfl
    (opt_snd_vminus_three_pi_div_two hB3)
  have z2 := segArea_of_snd_eq_zero (opt_snd_vplus_three_pi_div_two hD3)
    (q := zLeft φ K) (by rw [opt_zLeft_eq])
  have z3 := segArea_self (vminus B (3 * π / 2))
  have z4 := segArea_self (vminus D (3 * π / 2 + (π / 2 - φ)))
  obtain ⟨hXB, hWl, hxR⟩ := opt_right_mem_line hc.ne' hBa
  obtain ⟨hYD, hZl, hxL⟩ := opt_left_mem_line hc.ne' hDb
  have c1 := segArea_add_of_mem_line hxR hXB hWl
  have c2 := segArea_add_of_mem_line hZl hYD hxL
  simp only [upperQ, upperP, mamikonR, mamikonL, mamikon, hlR, hlL,
    tR1, tR2, tL1, tL2]
  simp only [xB, yD] at c1 c2 ⊢
  linarith

end MovingSofaStability
