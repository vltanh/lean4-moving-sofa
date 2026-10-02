module

public import MovingSofa.Gerver.Defs

/-!
# The domain of `𝒬` (§8.1)

Definitions 8.1.1 (`def:cap-space-special`), 8.1.3–8.1.6, Theorem 8.1.1 (`thm:cap-space-special`)
part (1), Proposition 8.1.2, Lemmas 8.1.3–8.1.7 and Theorem 8.1.8 (`thm:cap-tail-extension`).

The paper fixes `φ^R = φ` and `φ^L = π/2 - φ` with `φ` Gerver's angle (Definition 8.1.2). Everything
here is stated for a parameter `φ`; where the paper uses numerical properties of Gerver's `φ`
(`2 sec φ + 2 tan φ < 2.2`, `sec φ < 1.1`) we assume `φ ∈ [0.039, 0.04]`, the range the paper quotes.

**Missing hypothesis.** The proof of Lemma 8.1.7 (2), (4) uses `𝒩(K) ⊆ K` (through Theorem 2.5.8 (2)),
which `K ∈ 𝒦^i` does not provide; the cap with two unit quarter-discs joined by a flat top of
length 3 satisfies the injectivity condition and has area `3 + π/2`, but its niche is not inside it.
Lemma 8.1.7 (2), (4), Theorem 8.1.8 and the results of §8.2 that depend on them assume `𝒩(K) ⊆ K`,
which holds for every cap of a monotone sofa (Theorem 2.5.9), in particular wherever the paper applies
them.
-/

@[expose] public section

open Real Set
open scoped Pointwise

namespace MovingSofa

/-- The space `𝒦^i` of caps with rotation angle `π/2` satisfying the injectivity condition and with
area at least `2.2` (Definition 8.1.1, `def:cap-space-special`). -/
def IsKi (K : Set (ℝ × ℝ)) : Prop := IsCap K (π / 2) ∧ SatisfiesInjectivity K ∧ 2.2 ≤ area K

/-- **Theorem 8.1.1** (`thm:cap-space-special`) (1): `𝒦^i` is closed under Minkowski combinations.
(The paper's proof uses the Brunn–Minkowski inequality for the area condition.) -/
theorem theorem8_1_1_convex {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsKi K₁) (h₂ : IsKi K₂) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) : IsKi ((1 - c) • K₁ + c • K₂) := by
  sorry

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
  sorry

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
  sorry

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

/-- **Lemma 8.1.3** (`lem:cap-right-left-parallelogram`). `P_K^R` is the parallelogram bounded by
`l(π/2, 0)`, `l(π/2, 1)`, `a_K(φ^R)` and `b_K(φ^R)`, with base `sec φ` on `l(π/2, 0)` starting at its
lower-left corner `W_K^R`. -/
theorem lemma8_1_3 {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) (K : Set (ℝ × ℝ)) :
    paraR φ K = {p | 0 ≤ p.2 ∧ p.2 ≤ 1 ∧ supp K φ - 1 ≤ dot p (uvec φ) ∧ dot p (uvec φ) ≤ supp K φ} ∧
      paraR φ K ∩ line (π / 2) 0 = segment ℝ (wRight φ K) (wRight φ K + (1 / cos φ, 0)) := by
  sorry

/-- **Lemma 8.1.4** (`lem:cap-left-right-disjoint`). For `K ∈ 𝒦^i`, `K ∩ H̆_K^R` and `K ∩ H̆_K^L` are
disjoint. -/
theorem lemma8_1_4 {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)} (hK : IsKi K) :
    Disjoint (K ∩ hRight φ K) (K ∩ hLeft φ K) := by
  sorry

/-- **Lemma 8.1.5** (`lem:cap-wz-in-edge`). For `K ∈ 𝒦^i`, `W_K^R` and `Z_K^L` lie on the edge
`e_K(3π/2)` but are not its endpoints `A_K(0)` and `C_K(π/2)`. -/
theorem lemma8_1_5 {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)} (hK : IsKi K) :
    wRight φ K ∈ edge K (3 * π / 2) \ {aK K 0, cK K (π / 2)} ∧
      zLeft φ K ∈ edge K (3 * π / 2) \ {aK K 0, cK K (π / 2)} := by
  sorry

/-- **Lemma 8.1.6** (`lem:monotonicity-intervals`) (1). For `K ∈ 𝒦^i` and `t ∈ (φ^R, π/2]`, the inner
corner `𝐱_K(t)` is outside `H̆_K^R`, `H̆_K^R ∩ Q_K⁻(t) = H̆_K^R \ H_K^b(t)`, and
`H̆_K^R ∩ T_K(t) = H̆_K^R ∩ H₊(π/2, 0) \ H_K^b(t)`. -/
theorem lemma8_1_6_right {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) {K : Set (ℝ × ℝ)} (hK : IsKi K) {t : ℝ}
    (ht : t ∈ Ioc φ (π / 2)) :
    innerCorner K t ∉ hRight φ K ∧ hRight φ K ∩ qMinus K t = hRight φ K \ halfB K t ∧
      hRight φ K ∩ wedge K (π / 2) t = (hRight φ K ∩ halfPlus (π / 2) 0) \ halfB K t := by
  sorry

/-- **Lemma 8.1.6** (2), the mirror statement for `t ∈ [0, φ^L)`. -/
theorem lemma8_1_6_left {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) {K : Set (ℝ × ℝ)} (hK : IsKi K) {t : ℝ}
    (ht : t ∈ Ico 0 (π / 2 - φ)) :
    innerCorner K t ∉ hLeft φ K ∧ hLeft φ K ∩ qMinus K t = hLeft φ K \ halfD K t ∧
      hLeft φ K ∩ wedge K (π / 2) t = (hLeft φ K ∩ halfPlus (π / 2) 0) \ halfD K t := by
  sorry

/-- **Lemma 8.1.7** (`lem:right-left-body`) (1): `h_K(t) + h_B(π + t) ≤ 1` on `[φ^R, π/2]`. -/
theorem lemma8_1_7_one {φ : ℝ} {K : Set (ℝ × ℝ)} (hK : IsKi K) {t : ℝ} (ht : t ∈ Icc φ (π / 2)) :
    supp K t + supp (rightBody φ K) (π + t) ≤ 1 := by
  sorry

/-- **Lemma 8.1.7** (2): equality at `t = φ^R, π/2`, so `l_B(3π/2) = l(π/2, 0)` and
`l_B(π + φ^R) = b_K^R`; under `𝒩(K) ⊆ K` (see the module docstring). -/
theorem lemma8_1_7_two {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)} (hK : IsKi K)
    (hN : niche K (π / 2) ⊆ K) :
    supp K φ + supp (rightBody φ K) (π + φ) = 1 ∧
      supp K (π / 2) + supp (rightBody φ K) (π + π / 2) = 1 ∧
      suppLine (rightBody φ K) (3 * π / 2) = line (π / 2) 0 ∧
      suppLine (rightBody φ K) (π + φ) = wallB K φ := by
  sorry

/-- **Lemma 8.1.7** (3): `h_K(π/2 + t) + h_D(3π/2 + t) ≤ 1` on `[0, φ^L]`. -/
theorem lemma8_1_7_three {φ : ℝ} {K : Set (ℝ × ℝ)} (hK : IsKi K) {t : ℝ}
    (ht : t ∈ Icc 0 (π / 2 - φ)) : supp K (π / 2 + t) + supp (leftBody φ K) (3 * π / 2 + t) ≤ 1 := by
  sorry

/-- **Lemma 8.1.7** (4): equality at `t = 0, φ^L` (the paper writes `φ^R`), so `l_D(3π/2) = l(π/2, 0)`
and `l_D(3π/2 + φ^L) = d_K^L`; under `𝒩(K) ⊆ K`. -/
theorem lemma8_1_7_four {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)} (hK : IsKi K)
    (hN : niche K (π / 2) ⊆ K) :
    supp K (π / 2 + 0) + supp (leftBody φ K) (3 * π / 2 + 0) = 1 ∧
      supp K (π / 2 + (π / 2 - φ)) + supp (leftBody φ K) (3 * π / 2 + (π / 2 - φ)) = 1 ∧
      suppLine (leftBody φ K) (3 * π / 2) = line (π / 2) 0 ∧
      suppLine (leftBody φ K) (3 * π / 2 + (π / 2 - φ)) = wallD K (π / 2 - φ) := by
  sorry

/-- **Theorem 8.1.8** (`thm:cap-tail-extension`). For `K ∈ 𝒦^i` with `𝒩(K) ⊆ K`,
`(K, B_K, D_K) ∈ 𝓛`. -/
theorem theorem8_1_8 {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)} (hK : IsKi K)
    (hN : niche K (π / 2) ⊆ K) : InL φ K (rightBody φ K) (leftBody φ K) := by
  sorry

end MovingSofa
