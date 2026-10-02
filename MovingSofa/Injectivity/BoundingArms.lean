module

public import MovingSofa.Injectivity.LimitIneq

/-!
# Bounding the arm lengths (§6.5); Theorem 6.1.1 and Theorem 1.7.1

Theorem 6.5.1 (`thm:leg-length-bounds`), Definitions 6.5.1–6.5.3, Lemmas 6.5.2–6.5.5, Theorem 6.5.6
(`thm:lower-bound-one`), Theorem 6.1.1 (`thm:injectivity`) and Theorem 1.7.1
(`thm:injectivity-abridged`).

**Reading of Lemma 6.5.5.** The paper states `f_11 > 1` on `(0, 1]`; its proof shows it on
`(0, π/2]`, which Theorem 6.5.6 needs. We state it on `(0, π/2]`. Lemma 6.5.4 is stated for continuous
functions, the domain of the operator `𝓕` (Definition 6.5.1).
-/

@[expose] public section

open Real Set MeasureTheory

namespace MovingSofa

/-- **Theorem 6.5.1** (`thm:leg-length-bounds`). For a balanced maximum cap, `f_K` is absolutely
continuous on `[0, π/2]` and `f_K'(t) ≥ m₀(g_K(t))` for almost every `t`. -/
theorem theorem6_5_1 {K : Set (ℝ × ℝ)} (hK : IsBalancedMaxCap K (π / 2)) :
    AbsolutelyContinuousOnInterval (fK K) 0 (π / 2) ∧
      ∀ᵐ t ∂(volume.restrict (Icc 0 (π / 2))), m0 (gK K t) ≤ deriv (fK K) t := by
  sorry

/-- The operator `𝓕 f(x) = 1 + ∫_0^x m₀(f(π/2 - u)) du` (Definition 6.5.1, `def:integral-operator`). -/
noncomputable def lowerOp (f : ℝ → ℝ) (x : ℝ) : ℝ := 1 + ∫ u in (0 : ℝ)..x, m0 (f (π / 2 - u))

/-- The lower bounds `f_0 = 0`, `f_{n+1} = max(f_n, 𝓕 f_n)` (Definition 6.5.2, `def:lower-bound-sequence`). -/
noncomputable def lowerSeq : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => max (lowerSeq n x) (lowerOp (lowerSeq n) x)

/-- **Lemma 6.5.2** (`lem:lower-bound-sequence`). Every balanced maximum cap satisfies
`f_K(t) ≥ f_n(t)` on `[0, π/2)` and `g_K(t) ≥ f_n(π/2 - t)` on `(0, π/2]`. -/
theorem lemma6_5_2 (n : ℕ) {K : Set (ℝ × ℝ)} (hK : IsBalancedMaxCap K (π / 2)) :
    (∀ t ∈ Ico 0 (π / 2), lowerSeq n t ≤ fK K t) ∧
      ∀ t ∈ Ioc 0 (π / 2), lowerSeq n (π / 2 - t) ≤ gK K t := by
  sorry

/-- `j_c(x) = max(1 - x, c)` (Definition 6.5.3, `def:lower-bound-j`). -/
noncomputable def jFun (c x : ℝ) : ℝ := max (1 - x) c

/-- **Lemma 6.5.3** (`lem:lower-bound-j-iter`). With `d₀ = 1/12`, for `c ∈ [0, 2/3]`,
`𝓕 j_c(x) ≥ j_{c + d₀}(x)` on `[0, π/2]`. -/
theorem lemma6_5_3 {c : ℝ} (hc : c ∈ Icc 0 (2 / 3)) {x : ℝ} (hx : x ∈ Icc 0 (π / 2)) :
    jFun (c + 1 / 12) x ≤ lowerOp (jFun c) x := by
  sorry

/-- **Lemma 6.5.4** (`lem:operator-monotonicity`). `𝓕` is monotone on nonnegative continuous
functions on `[0, π/2]`. -/
theorem lemma6_5_4 {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 (π / 2)))
    (hg : ContinuousOn g (Icc 0 (π / 2))) (hf0 : ∀ x ∈ Icc 0 (π / 2), 0 ≤ f x)
    (hfg : ∀ x ∈ Icc 0 (π / 2), f x ≤ g x) : ∀ x ∈ Icc 0 (π / 2), lowerOp f x ≤ lowerOp g x := by
  sorry

/-- **Lemma 6.5.5** (`lem:lower-bound-threshold`), on `(0, π/2]` (see the module docstring). -/
theorem lemma6_5_5 {x : ℝ} (hx : x ∈ Ioc 0 (π / 2)) : 1 < lowerSeq 11 x := by
  sorry

/-- **Theorem 6.5.6** (`thm:lower-bound-one`). For a balanced maximum cap, `f_K > 1` on `(0, π/2]`
and `g_K > 1` on `[0, π/2)`. -/
theorem theorem6_5_6 {K : Set (ℝ × ℝ)} (hK : IsBalancedMaxCap K (π / 2)) :
    (∀ t ∈ Ioc 0 (π / 2), 1 < fK K t) ∧ ∀ t ∈ Ico 0 (π / 2), 1 < gK K t := by
  sorry

/-- **Theorem 6.1.1** (`thm:injectivity`). Every balanced maximum cap satisfies the injectivity
condition. -/
theorem theorem6_1_1 {K : Set (ℝ × ℝ)} (hK : IsBalancedMaxCap K (π / 2)) : SatisfiesInjectivity K := by
  sorry

/-- **Theorem 1.7.1** (`thm:injectivity-abridged`). The rotation path `x_K` of a balanced maximum sofa
is continuously differentiable on `[0, π/2]`, with `x_K'(t) · u_t < 0` and `x_K'(t) · v_t > 0` for
`t ∈ (0, π/2)`. -/
theorem theorem1_7_1 {S : Set (ℝ × ℝ)} (hS : IsBalancedMaxSofa S (π / 2)) :
    ContDiffOn ℝ 1 (innerCorner (capOf S (π / 2))) (Icc 0 (π / 2)) ∧
      ∀ t ∈ Ioo 0 (π / 2), dot (deriv (innerCorner (capOf S (π / 2))) t) (uvec t) < 0 ∧
        0 < dot (deriv (innerCorner (capOf S (π / 2))) t) (vvec t) := by
  sorry

end MovingSofa
