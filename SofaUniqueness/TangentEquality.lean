module

public import SofaUniqueness.SupportKernelEquations

/-!
# From Mamikon equality to the support equations

Each convex-body family uses the continuous supporting curves already proved
in Theorem 8.3.1 and the outer-corner lemmas. Square-integrability and pointwise
interior equality come from `MamikonDisplacement`; support derivatives and
endpoint-safe integration come from `SupportKernelEquations`.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory MovingSofa SofaUniqueness.Draft

namespace SofaUniqueness

/-- Equality in a tangent Mamikon term forces the complete support kernel. -/
theorem tangentKernel_of_mamikon_eq {a b T : ℝ}
    (hab : a < b) (hTa : T - π < a) (hbT : b ≤ T) (hArc : UpperArc a b)
    (K₀ K₁ : ConvexBodySet) (hcap₀ : IsCap K₀.1 (π / 2)) (hcap₁ : IsCap K₁.1 (π / 2))
    (h1₀ : InjCond1 K₀.1) (h1₁ : InjCond1 K₁.1) {c : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (heq : mamikon (convexBodyComb c K₀ K₁).1 a b
        (tangentParam (convexBodyComb c K₀ K₁).1 T) =
      (1 - c) * mamikon K₀.1 a b (tangentParam K₀.1 T) +
        c * mamikon K₁.1 a b (tangentParam K₁.1 T)) :
    TangentKernel (fun t => supp K₁.1 t - supp K₀.1 t) a b T := by
  have hbπ : b < a + π := by linarith
  let z : ConvexBodySet → ℝ → ℝ × ℝ := fun K => tangentParam K.1 T
  have hz : ∀ K, IsCBV (z K) a b :=
    fun K => (theorem8_3_1 K.2 hTa hab.le hbT).1
  have hzl : ∀ K, ∀ t ∈ Icc a b, z K t ∈ suppLine K.1 t := by
    intro K t ht
    by_cases hlt : t < T
    · simp only [z, tangentParam, hlt, ite_true]
      exact vint_mem_line_left K.1 t T
    · have he : t = T := le_antisymm (ht.2.trans hbT) (not_lt.mp hlt)
      subst t
      simp only [z, tangentParam, lt_irrefl, ite_false]
      exact dot_vminus_uvec K.1 T
  have hlin : ∀ K L, ∀ d ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b,
      z (convexBodyComb d K L) t = (1 - d) • z K t + d • z L t :=
    fun K L d hd t ht => theorem8_3_2 hab.le hbT K L hd t ht
  have hdEq := displacement_eqOn_of_mamikon_eq hab hbπ z hz hzl hlin K₀ K₁ hc heq
    (displacement_continuousOn_arc hcap₀ h1₀ hArc (hz K₀).1)
    (displacement_continuousOn_arc hcap₁ h1₁ hArc (hz K₁).1)
  let f : ℝ → ℝ := fun t => supp K₁.1 t - supp K₀.1 t
  let f' : ℝ → ℝ := fun t => dot (vplus K₁.1 t) (vvec t) -
    dot (vplus K₀.1 t) (vvec t)
  have hf : Continuous f := (inj_continuous_supp K₁.2).sub (inj_continuous_supp K₀.2)
  have hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t := by
    intro t ht
    exact (support_hasDerivAt_of_injCond1 K₁.2 h1₁ (arc_mem_regular hArc ht)).sub
      (support_hasDerivAt_of_injCond1 K₀.2 h1₀ (arc_mem_regular hArc ht))
  apply tangentKernel_of_equation hab hTa hbT hf hd
  intro t ht
  have hlt : t < T := ht.2.trans_le hbT
  have hs : sin (T - t) ≠ 0 :=
    (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [ht.1])).ne'
  have he := hdEq ht
  change displacement K₀.1 (tangentParam K₀.1 T) t =
    displacement K₁.1 (tangentParam K₁.1 T) t at he
  rw [tangent_displacement_formula K₀.1 hlt, tangent_displacement_formula K₁.1 hlt] at he
  field_simp [hs] at he
  dsimp [f, f']
  nlinarith [he]

/-- Equality in the outer-corner term integrates to the middle support equation. -/
theorem middleKernel_of_mamikon_eq {a b : ℝ}
    (hab : a < b) (hbπ : b < a + π) (hArc : UpperArc a b)
    (K₀ K₁ : ConvexBodySet) (hcap₀ : IsCap K₀.1 (π / 2)) (hcap₁ : IsCap K₁.1 (π / 2))
    (h1₀ : InjCond1 K₀.1) (h1₁ : InjCond1 K₁.1) {c : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (heq : mamikon (convexBodyComb c K₀ K₁).1 a b
        (outerCorner (convexBodyComb c K₀ K₁).1) =
      (1 - c) * mamikon K₀.1 a b (outerCorner K₀.1) +
        c * mamikon K₁.1 a b (outerCorner K₁.1)) :
    ∀ t ∈ Icc a b, supp K₁.1 t - supp K₀.1 t =
      (supp K₁.1 b - supp K₀.1 b) -
        ∫ u in t..b, supp K₁.1 (u + π / 2) - supp K₀.1 (u + π / 2) := by
  let z : ConvexBodySet → ℝ → ℝ × ℝ := fun K => outerCorner K.1
  have hz : ∀ K, IsCBV (z K) a b := fun K => opt_outerCorner_cbv K.2 a b
  have hzl : ∀ K, ∀ t ∈ Icc a b, z K t ∈ suppLine K.1 t := by
    intro K t ht
    exact inj_dot_outerCorner_uvec K.1 t
  have hlin : ∀ K L, ∀ d ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b,
      z (convexBodyComb d K L) t = (1 - d) • z K t + d • z L t := by
    intro K L d hd t ht
    change outerCorner (convexBodyComb d K L).1 t = _
    rw [opt_convexBodyComb_val hd, opt_outerCorner_comb K.2 L.2 hd]
    rfl
  have hdEq := displacement_eqOn_of_mamikon_eq hab hbπ z hz hzl hlin K₀ K₁ hc heq
    (displacement_continuousOn_arc hcap₀ h1₀ hArc (hz K₀).1)
    (displacement_continuousOn_arc hcap₁ h1₁ hArc (hz K₁).1)
  let f : ℝ → ℝ := fun t => supp K₁.1 t - supp K₀.1 t
  have hf : Continuous f := (inj_continuous_supp K₁.2).sub (inj_continuous_supp K₀.2)
  apply integrated_middle_equation hf
  intro t ht
  have hd := (support_hasDerivAt_of_injCond1 K₁.2 h1₁ (arc_mem_regular hArc ht)).sub
    (support_hasDerivAt_of_injCond1 K₀.2 h1₀ (arc_mem_regular hArc ht))
  have he := hdEq ht
  change displacement K₀.1 (outerCorner K₀.1) t =
    displacement K₁.1 (outerCorner K₁.1) t at he
  rw [outer_displacement_formula, outer_displacement_formula] at he
  convert hd using 1
  dsimp [f]
  linarith

end SofaUniqueness
