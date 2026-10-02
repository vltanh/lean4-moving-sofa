module

public import MovingSofa.Optimality.Concavity

/-!
# Directional derivatives of `𝒬` (§8.5, general part)

Theorems 8.5.1–8.5.6, together with the general Definitions 8.4.5 (`def:opposite-surface-area`) and
8.4.6 (`def:i-cap`) that they use.
-/

@[expose] public section

open Real Set MeasureTheory

namespace MovingSofa

/-- `σ̆_C(X) = σ_C(X + π)` (Definition 8.4.5, `def:opposite-surface-area`). -/
noncomputable def sigmaBreve (C : Set (ℝ × ℝ)) : Measure ℝ := (sigma C).map (fun t => t - π)

/-- `h̆_C(t) = h_C(t + π)` (Definition 8.4.5). -/
noncomputable def suppBreve (C : Set (ℝ × ℝ)) (t : ℝ) : ℝ := supp C (t + π)

/-- The density `i_K` on `(0, π]`: `i_K(t) = ⟨𝐱_K'(t), v_t⟩` and `i_K(t + π/2) = ⟨-𝐱_K'(t), u_t⟩` for
`t ∈ (0, π/2]` (Definition 8.4.6, `def:i-cap`). -/
noncomputable def iFun (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ :=
  if t ≤ π / 2 then dot (deriv (innerCorner K) t) (vvec t)
  else -dot (deriv (innerCorner K) (t - π / 2)) (uvec (t - π / 2))

/-- The measure `ι_K = i_K dt` on `[0, π]` (Definition 8.4.6). For `K ∈ 𝒦^i` the density is positive
on `(0, π) \ {π/2}`, so `ι_K` is a positive measure. -/
noncomputable def iota (K : Set (ℝ × ℝ)) : Measure ℝ :=
  (volume.restrict (Icc 0 π)).withDensity (fun t => ENNReal.ofReal (iFun K t))

/-- **Theorem 8.5.1** (`thm:variation-convex-body`). The area is quadratic on `𝒦^i`, with
`D|·|(K; K*) = ∫_{[0, π]} (h_{K*} - h_K) dσ_K`. -/
theorem theorem8_5_1 : kiDomain.IsQuadratic (fun K => area K.1.1) ∧
    ∀ K Ks : KiSet, kiDomain.dirDeriv (fun K => area K.1.1) K Ks =
      ∫ t in Icc 0 π, (supp Ks.1.1 t - supp K.1.1 t) ∂(sigma K.1.1) := by
  sorry

/-- **Theorem 8.5.2** (`thm:convex-curve-area-variation`). For `a < b < a + π`, `𝒥(𝐮_K^{a,b})` is
quadratic on `𝒦` with directional derivative
`∫_{(a,b)} (h_{K*} - h_K) dσ_K + [𝒥(v_K⁻(b), v_{K*}⁻(b)) - 𝒥(v_K⁺(a), v_{K*}⁺(a))]`. -/
theorem theorem8_5_2 {a b : ℝ} (hab : a < b) (hb : b < a + π) :
    convexBodyDomain.IsQuadratic (fun K => convexCurveArea K.1 a b) ∧
      ∀ K Ks : ConvexBodySet, convexBodyDomain.dirDeriv (fun K => convexCurveArea K.1 a b) K Ks =
        (∫ t in Ioo a b, (supp Ks.1 t - supp K.1 t) ∂(sigma K.1)) +
          (segArea (vminus K.1 b) (vminus Ks.1 b) - segArea (vplus K.1 a) (vplus Ks.1 a)) := by
  sorry

/-- **Theorem 8.5.3** (`thm:variation-segment`). `𝒥(p, q)` is quadratic on `ℝ² × ℝ²` with directional
derivative `½((p* + q*) × (q - p) - 2(p × q)) + [𝒥(q, q*) - 𝒥(p, p*)]`. -/
theorem theorem8_5_3 :
    (vectorDomain ((ℝ × ℝ) × (ℝ × ℝ))).IsQuadratic (fun x => segArea x.1 x.2) ∧
      ∀ x xs : (ℝ × ℝ) × (ℝ × ℝ),
        (vectorDomain ((ℝ × ℝ) × (ℝ × ℝ))).dirDeriv (fun x => segArea x.1 x.2) x xs =
          (1 / 2) * (cross (xs.1 + xs.2) (x.2 - x.1) - 2 * cross x.1 x.2) +
            (segArea x.2 xs.2 - segArea x.1 xs.1) := by
  sorry

/-- **Theorem 8.5.4** (`thm:variation-curve`). The curve area functional is quadratic on `C^BV[a, b]`
with directional derivative `∫_a^b (𝐱* - 𝐱) × d𝐱 + [𝒥(𝐱(b), 𝐱*(b)) - 𝒥(𝐱(a), 𝐱*(a))]`. -/
theorem theorem8_5_4 {a b : ℝ} (hab : a ≤ b) :
    (cbvDomain a b).IsQuadratic (fun x => curveArea x.1 a b) ∧
      ∀ x xs : CBV a b, (cbvDomain a b).dirDeriv (fun x => curveArea x.1 a b) x xs =
        (∫ᵛ t in Icc a b, (xs.1 t - x.1 t) ∂[crossCLM; lsMeasure x.1 a b]) +
          (segArea (x.1 b) (xs.1 b) - segArea (x.1 a) (xs.1 a)) := by
  sorry

/-- **Theorem 8.5.5** (`thm:variation-inner-corner`). With `I = [φ^R, φ^L]`, `𝒥(𝐱_K|_I)` is quadratic on
`𝒦^i` with directional derivative
`⟨h_{K*} - h_K, ι_K⟩_{I ∪ (I + π/2)} + [𝒥(𝐱_K^L, 𝐱_{K*}^L) - 𝒥(𝐱_K^R, 𝐱_{K*}^R)]`. -/
theorem theorem8_5_5 {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    kiDomain.IsQuadratic (fun K => curveArea (innerCorner K.1.1) φ (π / 2 - φ)) ∧
      ∀ K Ks : KiSet,
        kiDomain.dirDeriv (fun K => curveArea (innerCorner K.1.1) φ (π / 2 - φ)) K Ks =
          (∫ t in Icc φ (π / 2 - φ) ∪ Icc (φ + π / 2) (π - φ),
              (supp Ks.1.1 t - supp K.1.1 t) * iFun K.1.1 t) +
            (segArea (xLeft φ K.1.1) (xLeft φ Ks.1.1) - segArea (xRight φ K.1.1) (xRight φ Ks.1.1)) := by
  sorry

/-- **Theorem 8.5.6** (`thm:variation-a2`). If `(K, B, D) ∈ 𝓛` has `X_B = 𝐱_K^R` and `Y_D = 𝐱_K^L`, the
directional derivative of `𝒬` towards `(K*, B*, D*) ∈ 𝓛` is
`⟨h_{K*} - h_K, σ_K⟩_{[0,π]} - ⟨h_{K*} - h_K, ι_K⟩_{I ∪ (I + π/2)} + ⟨h̆_{B*} - h̆_B, σ̆_B⟩_{(φ^R, π/2)}
+ ⟨h̆_{D*} - h̆_D, σ̆_D⟩_{(π/2, π/2 + φ^L)}`. -/
theorem theorem8_5_6 {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) (x xs : LTriple φ)
    (hX : xB φ x.1.2.1.1 = xRight φ x.1.1.1) (hY : yD φ x.1.2.2.1 = xLeft φ x.1.1.1) :
    (lDomain φ).dirDeriv (upperQL φ) x xs =
      (∫ t in Icc 0 π, (supp xs.1.1.1 t - supp x.1.1.1 t) ∂(sigma x.1.1.1)) -
        (∫ t in Icc φ (π / 2 - φ) ∪ Icc (φ + π / 2) (π - φ),
          (supp xs.1.1.1 t - supp x.1.1.1 t) * iFun x.1.1.1 t) +
        (∫ t in Ioo φ (π / 2),
          (suppBreve xs.1.2.1.1 t - suppBreve x.1.2.1.1 t) ∂(sigmaBreve x.1.2.1.1)) +
        (∫ t in Ioo (π / 2) (π / 2 + (π / 2 - φ)),
          (suppBreve xs.1.2.2.1 t - suppBreve x.1.2.2.1 t) ∂(sigmaBreve x.1.2.2.1)) := by
  sorry

end MovingSofa
