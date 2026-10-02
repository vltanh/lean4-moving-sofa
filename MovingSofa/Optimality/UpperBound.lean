module

public import MovingSofa.Optimality.Domain

/-!
# Definition of `𝒬` (§8.2)

Definitions 8.2.1 (`def:right-left-tails`), 8.2.2 (`def:upper-bound-q`), Proposition 8.2.1, Lemmas
8.2.2 (`lem:cap-left-right-tail`), 8.2.3 (`lem:cap-middle-lower-estimate`) and Theorem 8.2.4
(`thm:upper-bound-q`). The curve area functionals of the tails are the values of Theorem 7.3.2, and
that of the core is the curve area functional of the rotation path on `[φ^R, φ^L]`.
-/

@[expose] public section

open Real Set

namespace MovingSofa

/-- The right tail `𝐛_B = 𝐮_B^{π + φ^R, 3π/2}` (Definition 8.2.1). -/
def tailB (φ : ℝ) (B : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := convexCurve B (π + φ) (3 * π / 2)
/-- Its starting point `X_B = v_B⁺(π + φ^R)`. -/
noncomputable def xB (φ : ℝ) (B : Set (ℝ × ℝ)) : ℝ × ℝ := vplus B (π + φ)
/-- Its ending point `W_B = v_B⁻(3π/2)`. -/
noncomputable def wB (B : Set (ℝ × ℝ)) : ℝ × ℝ := vminus B (3 * π / 2)
/-- The left tail `𝐝_D = 𝐮_D^{3π/2, 3π/2 + φ^L}` (Definition 8.2.1). -/
def tailD (φ : ℝ) (D : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := convexCurve D (3 * π / 2) (3 * π / 2 + (π / 2 - φ))
/-- Its starting point `Z_D = v_D⁺(3π/2)`. -/
noncomputable def zD (D : Set (ℝ × ℝ)) : ℝ × ℝ := vplus D (3 * π / 2)
/-- Its ending point `Y_D = v_D⁻(3π/2 + φ^L)`. -/
noncomputable def yD (φ : ℝ) (D : Set (ℝ × ℝ)) : ℝ × ℝ := vminus D (3 * π / 2 + (π / 2 - φ))

/-- The upper bound `𝒬(K, B, D) = |K| + 𝒥(𝐝_D) + 𝒥(Y_D, 𝐱_K^L) - 𝒥(𝐱_K|_{[φ^R, φ^L]}) + 𝒥(𝐱_K^R, X_B)
+ 𝒥(𝐛_B)` (Definition 8.2.2, `def:upper-bound-q`). -/
noncomputable def upperQ (φ : ℝ) (K B D : Set (ℝ × ℝ)) : ℝ :=
  area K + convexCurveArea D (3 * π / 2) (3 * π / 2 + (π / 2 - φ)) + segArea (yD φ D) (xLeft φ K) -
    curveArea (innerCorner K) φ (π / 2 - φ) + segArea (xRight φ K) (xB φ B) +
    convexCurveArea B (π + φ) (3 * π / 2)

/-- `𝒬` as a function on the convex domain `𝓛`. -/
noncomputable def upperQL (φ : ℝ) (x : LTriple φ) : ℝ := upperQ φ x.1.1.1 x.1.2.1.1 x.1.2.2.1

/-- **Proposition 8.2.1** (`pro:upper-bound-q-quadratic`). `𝒬` is a quadratic functional on `𝓛`. -/
theorem proposition8_2_1 {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) : (lDomain φ).IsQuadratic (upperQL φ) := by
  sorry

/-- **Lemma 8.2.2** (`lem:cap-left-right-tail`). For `K ∈ 𝒦^i` with `𝒩(K) ⊆ K`, `B = B_K`, `D = D_K`:
`|𝒩(K) ∩ H̆_K^R| ≥ 𝒥(X_B, W_K^R) - 𝒥(𝐛_B)` and `|𝒩(K) ∩ H̆_K^L| ≥ 𝒥(Z_K^L, Y_D) - 𝒥(𝐝_D)`. -/
theorem lemma8_2_2 {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)} (hK : IsKi K)
    (hN : niche K (π / 2) ⊆ K) :
    segArea (xB φ (rightBody φ K)) (wRight φ K) - convexCurveArea (rightBody φ K) (π + φ) (3 * π / 2) ≤
        area (niche K (π / 2) ∩ hRight φ K) ∧
      segArea (zLeft φ K) (yD φ (leftBody φ K)) -
          convexCurveArea (leftBody φ K) (3 * π / 2) (3 * π / 2 + (π / 2 - φ)) ≤
        area (niche K (π / 2) ∩ hLeft φ K) := by
  sorry

/-- **Lemma 8.2.3** (`lem:cap-middle-lower-estimate`). For `K ∈ 𝒦^i`,
`|𝒩(K) \ H̆_K^R \ H̆_K^L| ≥ 𝒥(W_K^R, 𝐱_K^R) + 𝒥(𝐱_K|_{[φ^R, φ^L]}) + 𝒥(𝐱_K^L, Z_K^L)`. -/
theorem lemma8_2_3 {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)} (hK : IsKi K) :
    segArea (wRight φ K) (xRight φ K) + curveArea (innerCorner K) φ (π / 2 - φ) +
        segArea (xLeft φ K) (zLeft φ K) ≤
      area ((niche K (π / 2) \ hRight φ K) \ hLeft φ K) := by
  sorry

/-- **Theorem 8.2.4** (`thm:upper-bound-q`). For `K ∈ 𝒦^i` with `𝒩(K) ⊆ K`,
`𝒜(K) ≤ 𝒬(K, B_K, D_K)`. -/
theorem theorem8_2_4 {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)} (hK : IsKi K)
    (hN : niche K (π / 2) ⊆ K) :
    sofaArea (π / 2) K ≤ upperQ φ K (rightBody φ K) (leftBody φ K) := by
  sorry

end MovingSofa
