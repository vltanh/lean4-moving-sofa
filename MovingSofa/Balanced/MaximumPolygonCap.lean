module

public import MovingSofa.Balanced.PolygonCap

/-!
# Maximum polygon caps (§3.4)

Definitions 3.4.1–3.4.5, Lemmas 3.4.1–3.4.2, Theorem 3.4.3 (`thm:maximum-polygon-cap`), Theorem 3.4.4
(`thm:polyline`), Lemmas 3.4.5–3.4.8, Theorems 3.4.9 (`thm:balanced-polygon-sofa`) and 3.4.10
(`thm:balanced-polygon-sofa-connected`).
-/

@[expose] public section

open Real Set

namespace MovingSofa

/-- A maximum polygon cap with angle set `Θ` (Definition 3.4.1, `def:maximum-polygon-cap`): a polygon
cap containing `o_ω` that maximizes `𝒜_Θ` over the polygon caps with angle set `Θ`. -/
def IsMaxPolygonCap (Θ : AngleSet) (K : Set (ℝ × ℝ)) : Prop :=
  IsPolygonCap Θ K ∧ oPt Θ.ω ∈ K ∧ ∀ K', IsPolygonCap Θ K' → polyArea Θ K' ≤ polyArea Θ K

/-- The mirror angle set `ω - Θ`. -/
noncomputable def AngleSet.mirror (Θ : AngleSet) : AngleSet where
  ω := Θ.ω
  angles := Θ.angles.image (fun t => Θ.ω - t)
  hω := Θ.hω
  nonempty := Θ.nonempty.image _
  subset := by
    intro t ht
    simp only [Finset.mem_image] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    have := Θ.subset s hs
    constructor <;> linarith [this.1, this.2]

/-- **Lemma 3.4.1** (`lem:maximum-polygon-cap-mirror`). The mirror reflection of a maximum polygon cap
is a maximum polygon cap with the angle set `ω - Θ`. -/
theorem lemma3_4_1 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap Θ K) :
    IsMaxPolygonCap Θ.mirror (mirrorCap K Θ.ω) := by
  sorry

/-- **Lemma 3.4.2** (`lem:polygon-cap-bounded`). For `t ∈ (0, ω)` there is `c_{ω,t} > 0` such that
every polygon cap `K` with an angle set containing `t` and with `𝒜_Θ(K) > 0` has width at most
`c_{ω,t}` along `u_0`. -/
theorem lemma3_4_2 {ω t : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) (ht : t ∈ Ioo 0 ω) :
    ∃ c > 0, ∀ Θ : AngleSet, Θ.ω = ω → t ∈ Θ.angles → ∀ K, IsPolygonCap Θ K →
      0 < polyArea Θ K → width K 0 ≤ c := by
  sorry

/-- **Theorem 3.4.3** (`thm:maximum-polygon-cap`). A maximum polygon cap exists for every angle set. -/
theorem theorem3_4_3 (Θ : AngleSet) : ∃ K, IsMaxPolygonCap Θ K := by
  sorry

/-- An `x`-monotone polyline through `p_1, …, p_n` (Definition 3.4.2, `def:polyline`). -/
def IsXMonotonePolyline (P : Set (ℝ × ℝ)) : Prop :=
  ∃ (n : ℕ) (p : Fin (n + 1) → ℝ × ℝ), StrictMono (fun i => (p i).1) ∧
    P = ⋃ i : Fin n, segment ℝ (p i.castSucc) (p i.succ)

/-- The open half-line `l⃗_K` from `C_K⁺(ω)` in the direction `v_ω`, without its endpoint. -/
def rayLeft (K : Set (ℝ × ℝ)) (ω : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ s : ℝ, 0 < s ∧ p = cPlus K ω + s • vvec ω}

/-- The open half-line `r⃗_K` from `A_K⁻(0)` in the direction `u_0`, without its endpoint. -/
def rayRight (K : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := {p | ∃ s : ℝ, 0 < s ∧ p = aMinus K 0 + s • uvec 0}

/-- The polyline `𝐩_K` of a polygon cap (Definition 3.4.3, `def:polyline-of-cap`): the boundary of
`F_ω \ 𝒩_Θ(K)` without the two open half-lines. -/
def polyline (Θ : AngleSet) (K : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  frontier (fan Θ.ω \ polyNiche Θ K) \ (rayLeft K Θ.ω ∪ rayRight K)

/-- **Theorem 3.4.4** (`thm:polyline`). For a polygon cap `K`, the boundary of `F_ω \ 𝒩_Θ(K)` is the
disjoint union, from left to right, of `l⃗_K`, an `x`-monotone polyline `𝐩_K` from `C_K⁺(ω)` to
`A_K⁻(0)` whose segments have normal angles in `Θ^◇`, and `r⃗_K`. -/
theorem theorem3_4_4 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) :
    frontier (fan Θ.ω \ polyNiche Θ K) = rayLeft K Θ.ω ∪ polyline Θ K ∪ rayRight K ∧
      Disjoint (rayLeft K Θ.ω) (polyline Θ K ∪ rayRight K) ∧ Disjoint (polyline Θ K) (rayRight K) ∧
      ∃ (n : ℕ) (p : Fin (n + 1) → ℝ × ℝ), p 0 = cPlus K Θ.ω ∧ p (Fin.last n) = aMinus K 0 ∧
        StrictMono (fun i => (p i).1) ∧ polyline Θ K = ⋃ i : Fin n, segment ℝ (p i.castSucc) (p i.succ) ∧
        ∀ i : Fin n, ∃ s ∈ Θ.diamond, ∃ ℓ > 0, p i.castSucc - p i.succ = ℓ • vvec s := by
  sorry

/-- `τ_K(t)`, the total length of the edges of the polyline `𝐩_K` with normal angle `t`
(Definition 3.4.4, `def:polyline-length`): the sum over the parallel lines `l(t, c)` of the length of
the part of `𝐩_K` on them. Only finitely many terms are nonzero. -/
noncomputable def tau (Θ : AngleSet) (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ :=
  ∑' c : ℝ, lineLength t c (polyline Θ K)

/-- **Lemma 3.4.5** (`lem:polyline-length`) (1). For `t ∈ Θ`, the sides of `𝒩_Θ(K)` on `b_K(t)`
(all on the half-line `b⃗_K(t)`) have total length `τ_K(t)`, and those on `d_K(t)` (all on `d⃗_K(t)`)
have total length `τ_K(t + π/2)`. -/
theorem lemma3_4_5_one {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) {t : ℝ}
    (ht : t ∈ Θ.angles) :
    lineLength t (supp K t - 1) (frontier (polyNiche Θ K)) = tau Θ K t ∧
      lineLength t (supp K t - 1) (frontier (polyNiche Θ K) ∩ wallBVec K t) = tau Θ K t ∧
      lineLength (t + π / 2) (supp K (t + π / 2) - 1) (frontier (polyNiche Θ K)) =
        tau Θ K (t + π / 2) ∧
      lineLength (t + π / 2) (supp K (t + π / 2) - 1) (frontier (polyNiche Θ K) ∩ wallDVec K t) =
        tau Θ K (t + π / 2) := by
  sorry

/-- **Lemma 3.4.5** (2). For `t ∈ {ω, π/2}`, the sides of `𝒩_Θ(K)` on `l(t, 0)` have total length
`σ_K(t + π) - τ_K(t)`. -/
theorem lemma3_4_5_two {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) {t : ℝ}
    (ht : t ∈ ({Θ.ω, π / 2} : Set ℝ)) :
    lineLength t 0 (frontier (polyNiche Θ K)) = sigmaAt K (t + π) - tau Θ K t ∧
      lineLength t 0 (polyNiche Θ K) = sigmaAt K (t + π) - tau Θ K t := by
  sorry

/-- A polygon cap is balanced if `σ_K(t) = τ_K(t)` for every `t ∈ Θ^◇` (Definition 3.4.5,
`def:polygon-cap-balanced`). -/
def IsBalanced (Θ : AngleSet) (K : Set (ℝ × ℝ)) : Prop := ∀ t ∈ Θ.diamond, sigmaAt K t = tau Θ K t

/-- **Lemma 3.4.6** (`lem:not-balanced-positive`). An unbalanced polygon cap has an angle
`t ∈ Θ^◇` with `σ_K(t) > τ_K(t)`. -/
theorem lemma3_4_6 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K)
    (hnb : ¬ IsBalanced Θ K) : ∃ t ∈ Θ.diamond, tau Θ K t < sigmaAt K t := by
  sorry

/-- **Lemma 3.4.7** (`lem:balancing`). Raising `h_K(t)` by a small `ε > 0` changes `𝒜_Θ` by
`(σ_K(t) - τ_K(t)) ε + O(ε²)`, with the constant depending on `K` and `t`. -/
theorem lemma3_4_7 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) {t : ℝ}
    (ht : t ∈ Θ.diamond) :
    ∃ ε₀ > 0, ∃ C : ℝ, ∀ ε ∈ Ioc 0 ε₀,
      |areaH Θ (Function.update (supp K) t (supp K t + ε)) - areaH Θ (supp K) -
          (sigmaAt K t - tau Θ K t) * ε| ≤ C * ε ^ 2 := by
  sorry

/-- **Lemma 3.4.8** (`lem:height-positive-increment`). If `σ_K(t) > 0`, raising `h_K(t)` by a small
`ε > 0` gives a polygon cap translate `𝓒_Θ(h⁺)`. -/
theorem lemma3_4_8 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) {t : ℝ}
    (ht : t ∈ Θ.diamond) (hσ : 0 < sigmaAt K t) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀,
      IsPolygonCapTranslate Θ (capH Θ (Function.update (supp K) t (supp K t + ε))) := by
  sorry

/-- **Theorem 3.4.9** (`thm:balanced-polygon-sofa`). Every maximum polygon cap is balanced. -/
theorem theorem3_4_9 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap Θ K) :
    IsBalanced Θ K := by
  sorry

/-- **Theorem 3.4.10** (`thm:balanced-polygon-sofa-connected`). Every maximum polygon cap contains its
polygon niche. -/
theorem theorem3_4_10 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap Θ K) :
    polyNiche Θ K ⊆ K := by
  sorry

end MovingSofa
