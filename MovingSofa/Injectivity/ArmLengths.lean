module

public import MovingSofa.Angle.RightAngle
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# The injectivity condition (§6.1) and arm lengths (§6.2)

Definitions 6.1.1–6.1.2 (`def:injectivity-condition`), 6.2.1 (`def:cap-tangent-arm-length`),
6.2.2 (one-sided derivatives, taken from Mathlib), Propositions 6.2.1–6.2.2, Theorem 6.2.3
(`thm:inner-corner-deriv`), Lemma 6.2.4 (`lem:arm-length-convolution`) and Theorem 6.2.5
(`thm:arm-length-differentiation`).

From this chapter on the rotation angle is `ω = π/2` (Definition 6.1.1, `def:cap-space-right-angle`):
the cap space `𝒦^c` is `capSpace (π/2)` and `𝒜` is `sofaArea (π/2)`.

**Reading of Proposition 6.2.2.** The paper writes `f^±_{K^m}(t) = g^∓_K(t)`; the reflection also
replaces `t` by `π/2 - t` (as Lemma 6.5.2 uses), and we state that.
-/

@[expose] public section

open Real Set MeasureTheory

namespace MovingSofa

/-- Condition (1) of the injectivity condition: `σ_K = r_K(t) dt` on `[0, π/2)` and
`σ_K = s_K(t - π/2) dt` on `(π/2, π]` for measurable `r_K, s_K ≥ 0`. -/
def InjCond1 (K : Set (ℝ × ℝ)) : Prop :=
  ∃ r s : ℝ → ℝ, Measurable r ∧ Measurable s ∧ (∀ t, 0 ≤ r t) ∧ (∀ t, 0 ≤ s t) ∧
    (sigma K).restrict (Ico 0 (π / 2)) =
      (volume.restrict (Ico 0 (π / 2))).withDensity (fun t => ENNReal.ofReal (r t)) ∧
    (sigma K).restrict (Ioc (π / 2) π) =
      (volume.restrict (Ioc (π / 2) π)).withDensity (fun t => ENNReal.ofReal (s (t - π / 2)))

/-- Condition (2): the inner corner `x_K : [0, π/2] → ℝ²` is continuously differentiable. -/
def InjCond2 (K : Set (ℝ × ℝ)) : Prop := ContDiffOn ℝ 1 (innerCorner K) (Icc 0 (π / 2))

/-- Condition (3): `x_K'(t) · u_t < 0` and `x_K'(t) · v_t > 0` for `t ∈ (0, π/2)`. -/
def InjCond3 (K : Set (ℝ × ℝ)) : Prop :=
  ∀ t ∈ Ioo 0 (π / 2), dot (deriv (innerCorner K) t) (uvec t) < 0 ∧
    0 < dot (deriv (innerCorner K) t) (vvec t)

/-- A cap `K ∈ 𝒦^c` satisfies the injectivity condition (Definition 6.1.2, `def:injectivity-condition`). -/
def SatisfiesInjectivity (K : Set (ℝ × ℝ)) : Prop := InjCond1 K ∧ InjCond2 K ∧ InjCond3 K

/-- The arm length `f_K⁺(t) = (y_K(t) - A_K⁺(t)) · v_t` (Definition 6.2.1). -/
noncomputable def fPlus (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ := dot (outerCorner K t - aPlus K t) (vvec t)
/-- The arm length `f_K⁻(t) = (y_K(t) - A_K⁻(t)) · v_t`. -/
noncomputable def fMinus (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ := dot (outerCorner K t - aMinus K t) (vvec t)
/-- The arm length `g_K⁺(t) = (y_K(t) - C_K⁺(t)) · u_t`. -/
noncomputable def gPlus (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ := dot (outerCorner K t - cPlus K t) (uvec t)
/-- The arm length `g_K⁻(t) = (y_K(t) - C_K⁻(t)) · u_t`. -/
noncomputable def gMinus (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ := dot (outerCorner K t - cMinus K t) (uvec t)

/-- **Proposition 6.2.1** (`pro:cap-tangent-arm-length`). `y_K(t) = A_K^±(t) + f_K^±(t) v_t` and
`y_K(t) = C_K^±(t) + g_K^±(t) u_t`. -/
theorem proposition6_2_1 {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) {t : ℝ} (ht : t ∈ Icc 0 (π / 2)) :
    outerCorner K t = aPlus K t + fPlus K t • vvec t ∧
      outerCorner K t = aMinus K t + fMinus K t • vvec t ∧
      outerCorner K t = cPlus K t + gPlus K t • uvec t ∧
      outerCorner K t = cMinus K t + gMinus K t • uvec t := by
  sorry

/-- **Proposition 6.2.2** (`pro:cap-tangent-arm-mirror`), with `t` replaced by `π/2 - t` on the right
(see the module docstring). -/
theorem proposition6_2_2 {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) {t : ℝ} (ht : t ∈ Icc 0 (π / 2)) :
    fPlus (mirrorCap K (π / 2)) t = gMinus K (π / 2 - t) ∧
      fMinus (mirrorCap K (π / 2)) t = gPlus K (π / 2 - t) ∧
      gPlus (mirrorCap K (π / 2)) t = fMinus K (π / 2 - t) ∧
      gMinus (mirrorCap K (π / 2)) t = fPlus K (π / 2 - t) := by
  sorry

/-- **Theorem 6.2.3** (`thm:inner-corner-deriv`), right derivatives at `t ∈ [0, π/2)`:
`∂⁺y_K(t) = -f_K⁺(t) u_t + g_K⁺(t) v_t` and `∂⁺x_K(t) = -(f_K⁺(t) - 1) u_t + (g_K⁺(t) - 1) v_t`. -/
theorem theorem6_2_3_right {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) {t : ℝ} (ht : t ∈ Ico 0 (π / 2)) :
    HasDerivWithinAt (outerCorner K) (-fPlus K t • uvec t + gPlus K t • vvec t) (Ici t) t ∧
      HasDerivWithinAt (innerCorner K) (-(fPlus K t - 1) • uvec t + (gPlus K t - 1) • vvec t)
        (Ici t) t := by
  sorry

/-- **Theorem 6.2.3**, left derivatives at `t ∈ (0, π/2]`, with `f_K⁻` and `g_K⁻`. -/
theorem theorem6_2_3_left {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) {t : ℝ} (ht : t ∈ Ioc 0 (π / 2)) :
    HasDerivWithinAt (outerCorner K) (-fMinus K t • uvec t + gMinus K t • vvec t) (Iic t) t ∧
      HasDerivWithinAt (innerCorner K) (-(fMinus K t - 1) • uvec t + (gMinus K t - 1) • vvec t)
        (Iic t) t := by
  sorry

/-- **Lemma 6.2.4** (`lem:arm-length-convolution`). `g_K⁺(t) = ∫_{(t, t+π/2]} sin(u - t) σ_K(du)`. -/
theorem lemma6_2_4 {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) {t : ℝ} (ht : t ∈ Icc 0 (π / 2)) :
    gPlus K t = ∫ u in Ioc t (t + π / 2), sin (u - t) ∂(sigma K) := by
  sorry

/-- **Theorem 6.2.5** (`thm:arm-length-differentiation`), regularity: for a convex body `K`, `f_K⁺` is
right-continuous and of bounded variation on `[0, π/2]`. -/
theorem theorem6_2_5_regular {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    BoundedVariationOn (fPlus K) (Icc 0 (π / 2)) ∧
      ∀ t ∈ Ico 0 (π / 2), ContinuousWithinAt (fPlus K) (Ici t) t := by
  sorry

/-- **Theorem 6.2.5** (`thm:arm-length-differentiation`). On `(0, π/2]`,
`d f_K⁺(t) = g_K⁺(t) dt - σ_K` as signed measures. -/
theorem theorem6_2_5 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    (lsMeasure (fPlus K) 0 (π / 2)).restrict (Ioc 0 (π / 2)) =
      (volume.restrict (Ioc 0 (π / 2))).withDensityᵥ (gPlus K) -
        ((sigma K).restrict (Ioc 0 (π / 2))).withDensityᵥ (fun _ => (1 : ℝ)) := by
  sorry

/-- The integrated form of Theorem 6.2.5:
`f_K⁺(b) - f_K⁺(a) = ∫_a^b g_K⁺ - σ_K((a, b])` for `0 ≤ a ≤ b ≤ π/2`. -/
theorem fPlus_sub_fPlus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ π / 2) :
    fPlus K b - fPlus K a = (∫ t in a..b, gPlus K t) - (sigma K (Ioc a b)).toReal := by
  sorry

end MovingSofa
