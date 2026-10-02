module

public import MovingSofa.Injectivity.DiscreteIneq

/-!
# The inequality on balanced maximum caps (§6.4)

Lemmas 6.4.1 (`lem:arm-length-discrete-bound`), 6.4.2 (`lem:leg-convergence`), Theorem 6.4.3
(`thm:balanced-ineq-limit`), Corollary 6.4.4 (`cor:cap-nondegenerate`), Propositions 6.4.5–6.4.6 and
Definition 6.4.1 (`def:cap-nondegenerate`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace MovingSofa

/-- **Lemma 6.4.1** (`lem:arm-length-discrete-bound`). For a maximum polygon cap with step size `δ`,
`t ∈ {0} ∪ Θ_n` and `t' ∈ (t, t + δ)`: (1) `g_K⁺(t) ≥ g_K⁺(t') = g_K⁻(t') ≥ g_K⁻(t + δ)`;
(2) `g_K⁺(t) - g_K⁻(t + δ) ≤ 5δ`. -/
theorem lemma6_4_1 {k : ℕ} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap (rightAngleSet k) K) {t : ℝ}
    (ht : t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ)) :
    (∀ t' ∈ Ioo t (t + stepSize k), gPlus K t' ≤ gPlus K t ∧ gPlus K t' = gMinus K t' ∧
        gMinus K (t + stepSize k) ≤ gMinus K t') ∧
      gPlus K t - gMinus K (t + stepSize k) ≤ 5 * stepSize k := by
  sorry

/-- **Lemma 6.4.2** (`lem:leg-convergence`). If polygon caps `K_n` (rotation angle `π/2`) converge to a
cap `K` in the Hausdorff distance, then `∫_0^{π/2} |g_{K_n}⁺ - g_K⁺| → 0`. -/
theorem lemma6_4_2 {Θs : ℕ → AngleSet} {Ks : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)}
    (hΘ : ∀ n, (Θs n).ω = π / 2) (hKs : ∀ n, IsPolygonCap (Θs n) (Ks n)) (hK : IsCap K (π / 2))
    (hlim : HausdorffTendsto Ks K) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..(π / 2), |gPlus (Ks n) t - gPlus K t|) atTop (𝓝 0) := by
  sorry

/-- **Theorem 6.4.3** (`thm:balanced-ineq-limit`). A balanced maximum cap satisfies
`σ_K ≤ k₀(g_K⁺(t)) dt` on `[0, π/2)`. -/
theorem theorem6_4_3 {K : Set (ℝ × ℝ)} (hK : IsBalancedMaxCap K (π / 2)) :
    (sigma K).restrict (Ico 0 (π / 2)) ≤
      (volume.restrict (Ico 0 (π / 2))).withDensity (fun t => ENNReal.ofReal (k0 (gPlus K t))) := by
  sorry

/-- **Corollary 6.4.4** (`cor:cap-nondegenerate`). A balanced maximum cap satisfies condition (1) of
the injectivity condition. -/
theorem corollary6_4_4 {K : Set (ℝ × ℝ)} (hK : IsBalancedMaxCap K (π / 2)) : InjCond1 K := by
  sorry

/-- **Proposition 6.4.5** (`pro:cap-nondegenerate`). Under condition (1), `A_K⁺ = A_K⁻`,
`f_K⁺ = f_K⁻` on `[0, π/2)` and `C_K⁺ = C_K⁻`, `g_K⁺ = g_K⁻` on `(0, π/2]`. -/
theorem proposition6_4_5 {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) (h1 : InjCond1 K) :
    (∀ t ∈ Ico 0 (π / 2), aPlus K t = aMinus K t ∧ fPlus K t = fMinus K t) ∧
      ∀ t ∈ Ioc 0 (π / 2), cPlus K t = cMinus K t ∧ gPlus K t = gMinus K t := by
  sorry

/-- `A_K(t)` (Definition 6.4.1): the common value `A_K^±(t)` for `t < π/2`, and `A_K⁻(π/2)` at `π/2`;
that is, `A_K⁻` on `[0, π/2]` (Proposition 6.4.5). -/
noncomputable def aK (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ × ℝ := aMinus K t
/-- `f_K(t)` (Definition 6.4.1): `f_K⁻` on `[0, π/2]`. -/
noncomputable def fK (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ := fMinus K t
/-- `C_K(t)` (Definition 6.4.1): the common value `C_K^±(t)` for `t > 0`, and `C_K⁺(0)` at `0`; that
is, `C_K⁺` on `[0, π/2]`. -/
noncomputable def cK (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ × ℝ := cPlus K t
/-- `g_K(t)` (Definition 6.4.1): `g_K⁺` on `[0, π/2]`. -/
noncomputable def gK (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ := gPlus K t

/-- **Proposition 6.4.6** (`pro:cap-nondegenerate-continuity`) (1): under condition (1), `A_K`, `C_K`,
`f_K` and `g_K` are continuous on `[0, π/2]`. -/
theorem proposition6_4_6_continuous {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) (h1 : InjCond1 K) :
    ContinuousOn (aK K) (Icc 0 (π / 2)) ∧ ContinuousOn (cK K) (Icc 0 (π / 2)) ∧
      ContinuousOn (fK K) (Icc 0 (π / 2)) ∧ ContinuousOn (gK K) (Icc 0 (π / 2)) := by
  sorry

/-- **Proposition 6.4.6** (2): under condition (1), `x_K` and `y_K` are continuously differentiable on
`[0, π/2]` with `x_K' = -(f_K - 1) u_t + (g_K - 1) v_t` and `y_K' = -f_K u_t + g_K v_t`. -/
theorem proposition6_4_6_deriv {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) (h1 : InjCond1 K) :
    ContDiffOn ℝ 1 (innerCorner K) (Icc 0 (π / 2)) ∧ ContDiffOn ℝ 1 (outerCorner K) (Icc 0 (π / 2)) ∧
      ∀ t ∈ Icc 0 (π / 2),
        HasDerivWithinAt (innerCorner K) (-(fK K t - 1) • uvec t + (gK K t - 1) • vvec t)
            (Icc 0 (π / 2)) t ∧
          HasDerivWithinAt (outerCorner K) (-fK K t • uvec t + gK K t • vvec t) (Icc 0 (π / 2)) t := by
  sorry

end MovingSofa
