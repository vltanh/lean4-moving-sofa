module

public import MovingSofa.Injectivity.ArmLengths

/-!
# The inequality on maximum polygon caps (§6.3)

Definitions 6.3.1–6.3.4, Lemmas 6.3.1 (`lem:leg-bounded`), 6.3.2 (`lem:leg-computation`) and
Theorem 6.3.3 (`thm:balanced-discrete-ineq`).

The uniform angle sets `Θ_n` of Definition 6.3.1 with `n = 2^(k+1)` are `dyadicAngleSet (π/2) _ k`,
and a "maximum polygon cap with `n` steps of step size `δ = (π/2)/n`" (Definition 6.3.2) is a maximum
polygon cap with that angle set.
-/

@[expose] public section

open Real Set

namespace MovingSofa

lemma pi_div_two_mem_Ioc : π / 2 ∈ Ioc 0 (π / 2) := ⟨by positivity, le_rfl⟩

/-- The uniform angle set `Θ_n` of rotation angle `π/2` with `n = 2^(k+1)` steps
(Definition 6.3.1, `def:right-angle-set`). -/
noncomputable def rightAngleSet (k : ℕ) : AngleSet := dyadicAngleSet (π / 2) pi_div_two_mem_Ioc k

/-- The step size `δ = (π/2)/n` with `n = 2^(k+1)` (Definition 6.3.2). -/
noncomputable def stepSize (k : ℕ) : ℝ := (π / 2) / 2 ^ (k + 1)

/-- The half-plane `H_K^b(t) = H₊(t, h_K(t) - 1)` above the inner wall `b_K(t)`
(Definition 6.3.3, `def:upper-half-planes`). -/
def halfB (K : Set (ℝ × ℝ)) (t : ℝ) : Set (ℝ × ℝ) := halfPlus t (supp K t - 1)

/-- The half-plane `H_K^d(t) = H₊(t + π/2, h_K(t + π/2) - 1)` above the inner wall `d_K(t)`
(Definition 6.3.3). -/
def halfD (K : Set (ℝ × ℝ)) (t : ℝ) : Set (ℝ × ℝ) := halfPlus (t + π / 2) (supp K (t + π / 2) - 1)

/-- **Lemma 6.3.1** (`lem:leg-bounded`). A maximum polygon cap with `n` steps has diameter at most
`5`; consequently its arm lengths are at most `5`. -/
theorem lemma6_3_1 {k : ℕ} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap (rightAngleSet k) K) :
    (∀ p ∈ K, ∀ q ∈ K, norm2 (p - q) ≤ 5) ∧
      ∀ t ∈ Icc 0 (π / 2), fPlus K t ≤ 5 ∧ fMinus K t ≤ 5 ∧ gPlus K t ≤ 5 ∧ gMinus K t ≤ 5 := by
  sorry

/-- **Lemma 6.3.2** (`lem:leg-computation`). For a maximum polygon cap with step size `δ` and
`t ∈ Θ`: (1) `𝓗¹(b⃗_K(t) ∩ H_K^d(t - δ)) = tan δ · max(0, g_K⁻(t) - 1 + tan(δ/2))` and
(2) `𝓗¹(b⃗_K(t) ∩ H_K^d(t + δ)) = tan δ · max(0, 1 - g_K⁺(t) + tan(δ/2))`. -/
theorem lemma6_3_2 {k : ℕ} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap (rightAngleSet k) K) {t : ℝ}
    (ht : t ∈ (rightAngleSet k).angles) :
    lineLength t (supp K t - 1) (wallBVec K t ∩ halfD K (t - stepSize k)) =
        tan (stepSize k) * max 0 (gMinus K t - 1 + tan (stepSize k / 2)) ∧
      lineLength t (supp K t - 1) (wallBVec K t ∩ halfD K (t + stepSize k)) =
        tan (stepSize k) * max 0 (1 - gPlus K t + tan (stepSize k / 2)) := by
  sorry

/-- `k₀(x) = max(|x - 1|, (|x - 1| + 1)/2)` (Definition 6.3.4, `def:magic-function`). -/
noncomputable def k0 (x : ℝ) : ℝ := max |x - 1| ((|x - 1| + 1) / 2)

/-- `m₀(x) = x - k₀(x)` (Definition 6.3.4). -/
noncomputable def m0 (x : ℝ) : ℝ := x - k0 x

/-- **Theorem 6.3.3** (`thm:balanced-discrete-ineq`). There is an absolute constant `C` such that every
maximum polygon cap `K` with `n` steps of step size `δ` satisfies
`σ_K(t) ≤ k₀(g_K⁺(t)) δ + C δ²` for every `t ∈ {0} ∪ Θ_n`. -/
theorem theorem6_3_3 : ∃ C : ℝ, ∀ k : ℕ, ∀ K, IsMaxPolygonCap (rightAngleSet k) K →
    ∀ t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ),
      sigmaAt K t ≤ k0 (gPlus K t) * stepSize k + C * stepSize k ^ 2 := by
  sorry

end MovingSofa
