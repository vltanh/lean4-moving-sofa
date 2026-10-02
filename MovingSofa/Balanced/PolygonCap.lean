module

public import MovingSofa.Balanced.NefPolygon

/-!
# Polygon caps and niches (§3.2) and the extensions of the space of polygon caps (§3.3)

Definitions 3.2.1–3.2.6 and 3.3.1–3.3.4; Propositions 3.2.1–3.2.2, Theorem 3.2.3
(`thm:polygon-upper-bound`), Propositions 3.3.1–3.3.5, Theorem 3.3.6 (`thm:height-extensions`) and
Proposition 3.3.7 (`pro:cap-translate-reduction`).

**Reading of Definition 3.2.5.** The paper defines the polygon niche as
`𝒩_Θ(K) = P_ω ∩ ⋃_{t ∈ Θ} Q_K⁻(t)`, but its definition of the niche (Definition 2.4.5), of the
extended niche (Definition 3.3.3), the proofs of Theorem 3.4.4 and Lemma 3.4.5, and the overview all
use the fan `F_ω` in place of `P_ω`. With `P_ω`, Proposition 3.3.5 fails. We use `F_ω`.
-/

@[expose] public section

open Real Set

namespace MovingSofa

/-- An angle set `Θ` with rotation angle `ω ∈ (0, π/2]`: a nonempty finite subset of `(0, ω)`
(Definition 3.2.1, `def:angle-set`). -/
structure AngleSet where
  ω : ℝ
  angles : Finset ℝ
  hω : ω ∈ Ioc 0 (π / 2)
  nonempty : angles.Nonempty
  subset : ∀ t ∈ angles, t ∈ Ioo 0 ω

/-- `Θ^◇ = Θ ∪ (Θ + π/2) ∪ {ω, π/2}` (Definition 3.2.2, `def:angle-domain`). -/
def AngleSet.diamond (Θ : AngleSet) : Set ℝ :=
  (Θ.angles : Set ℝ) ∪ (fun t => t + π / 2) '' (Θ.angles : Set ℝ) ∪ {Θ.ω, π / 2}

/-- The normal angles of a polygon cap: `Θ^◇ ∪ {ω + π, 3π/2}`. -/
def AngleSet.capAngles (Θ : AngleSet) : Set ℝ := Θ.diamond ∪ {Θ.ω + π, 3 * π / 2}

/-- A polygon cap with angle set `Θ` (Definition 3.2.3, `def:angled-cap-space`): a cap with rotation
angle `ω` which is an intersection of closed half-planes with normal angles in
`Θ^◇ ∪ {ω + π, 3π/2}`. -/
def IsPolygonCap (Θ : AngleSet) (K : Set (ℝ × ℝ)) : Prop :=
  IsCap K Θ.ω ∧ IsHalfPlaneInter K Θ.capAngles

/-- The polygon cap `𝓒_Θ(K) = P_ω ∩ ⋂_{t ∈ Θ} Q_K⁺(t)` approximating a cap `K`
(Definition 3.2.4, `def:angled-cap`). -/
def polyCap (Θ : AngleSet) (K : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  para Θ.ω ∩ ⋂ t ∈ Θ.angles, qPlus K t

/-- The polygon niche `𝒩_Θ(K) = F_ω ∩ ⋃_{t ∈ Θ} Q_K⁻(t)` (Definition 3.2.5, `def:angled-niche`,
with the fan `F_ω`; see the module docstring). -/
def polyNiche (Θ : AngleSet) (K : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  fan Θ.ω ∩ ⋃ t ∈ Θ.angles, qMinus K t

/-- The polygon sofa area functional `𝒜_Θ(K) = |𝓒_Θ(K)| - |𝒩_Θ(K)|` (Definition 3.2.6,
`def:polygon-upper-bound`). -/
noncomputable def polyArea (Θ : AngleSet) (K : Set (ℝ × ℝ)) : ℝ :=
  area (polyCap Θ K) - area (polyNiche Θ K)

/-- **Proposition 3.2.1** (`pro:angled-cap`). For a cap `K`, `𝓒_Θ(K)` is a polygon cap containing
`K`; and `𝓒_Θ` fixes polygon caps (so `𝓒_Θ : 𝒦_ω^c → 𝒦_Θ^c` is surjective). -/
theorem proposition3_2_1 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsCap K Θ.ω) :
    K ⊆ polyCap Θ K ∧ IsPolygonCap Θ (polyCap Θ K) := by
  sorry

theorem proposition3_2_1_fix {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) :
    polyCap Θ K = K := by
  sorry

/-- **Proposition 3.2.2** (`pro:angled-niche-polygon-cap`). `𝒩_Θ(K) = 𝒩_Θ(𝓒_Θ(K)) ⊆ 𝒩(K)`. -/
theorem proposition3_2_2 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsCap K Θ.ω) :
    polyNiche Θ K = polyNiche Θ (polyCap Θ K) ∧ polyNiche Θ K ⊆ niche K Θ.ω := by
  sorry

/-- **Theorem 3.2.3** (`thm:polygon-upper-bound`). For a polygon cap, `𝒜_Θ(K) = |K| - |𝒩_Θ(K)|`; for
every cap, `𝒜_ω(K) ≤ 𝒜_Θ(K)`. -/
theorem theorem3_2_3 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) :
    polyArea Θ K = area K - area (polyNiche Θ K) := by
  sorry

theorem theorem3_2_3_le {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsCap K Θ.ω) :
    sofaArea Θ.ω K ≤ polyArea Θ K := by
  sorry

/-! ### Extensions of the space of polygon caps (§3.3) -/

/-- A polygon cap translate (Definition 3.3.1, `def:cap-trans`). -/
def IsPolygonCapTranslate (Θ : AngleSet) (K' : Set (ℝ × ℝ)) : Prop :=
  ∃ K : Set (ℝ × ℝ), ∃ v : ℝ × ℝ, IsPolygonCap Θ K ∧ K' = (fun p => p + v) '' K

/-- **Proposition 3.3.1** (`pro:cap-trans-space`). A convex polygon `K'` is a polygon cap translate if
and only if its widths along the angles `ω` and `π/2` are one, and it is a convex polygon with normal
angles in `Θ^◇ ∪ {ω + π, 3π/2}`. (The paper writes `Θ^◇`; the bottom sides of a cap have the normal
angles `ω + π` and `3π/2`, which its proof uses.) -/
theorem proposition3_3_1 {Θ : AngleSet} {K' : Set (ℝ × ℝ)} :
    IsPolygonCapTranslate Θ K' ↔
      IsConvexBody K' ∧ width K' Θ.ω = 1 ∧ width K' (π / 2) = 1 ∧
        IsHalfPlaneInter K' Θ.capAngles := by
  sorry

/-- **Proposition 3.3.2** (`pro:height-space-embedding`). A polygon cap translate is determined by
its support function on `Θ^◇`. Definition 3.3.2 (`def:height-space`): the space `ℋ_Θ` of functions
`Θ^◇ → ℝ` is represented by functions `ℝ → ℝ`, of which only the values on `Θ^◇` are used. -/
theorem proposition3_3_2 {Θ : AngleSet} {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsPolygonCapTranslate Θ K₁)
    (h₂ : IsPolygonCapTranslate Θ K₂) (h : ∀ t ∈ Θ.diamond, supp K₁ t = supp K₂ t) : K₁ = K₂ := by
  sorry

/-- The parallelogram `P_h` of `h ∈ ℋ_Θ` (Definition 3.3.3, `def:height-extensions`). -/
def paraH (Θ : AngleSet) (h : ℝ → ℝ) : Set (ℝ × ℝ) :=
  ⋂ t ∈ ({Θ.ω, π / 2} : Set ℝ), halfMinus t (h t) ∩ halfPlus t (h t - 1)

/-- The cap `𝓒_Θ(h)` (Definition 3.3.3). -/
def capH (Θ : AngleSet) (h : ℝ → ℝ) : Set (ℝ × ℝ) :=
  paraH Θ h ∩ ⋂ t ∈ (Θ.angles : Set ℝ) ∪ (fun s => s + π / 2) '' (Θ.angles : Set ℝ),
    halfMinus t (h t)

/-- The fan `F_h` (Definition 3.3.3). -/
def fanH (Θ : AngleSet) (h : ℝ → ℝ) : Set (ℝ × ℝ) :=
  ⋂ t ∈ ({Θ.ω, π / 2} : Set ℝ), halfPlus t (h t - 1)

/-- The niche `𝒩_Θ(h)` (Definition 3.3.3). -/
def nicheH (Θ : AngleSet) (h : ℝ → ℝ) : Set (ℝ × ℝ) :=
  fanH Θ h ∩ ⋃ t ∈ Θ.angles,
    (halfMinusOpen t (h t - 1) ∩ halfMinusOpen (t + π / 2) (h (t + π / 2) - 1))

/-- The polygon sofa area functional `𝒜_Θ(h) = |𝓒_Θ(h)| - |𝒩_Θ(h)|` (Definition 3.3.3). -/
noncomputable def areaH (Θ : AngleSet) (h : ℝ → ℝ) : ℝ := area (capH Θ h) - area (nicheH Θ h)

/-- The defining half-planes of `𝓒_Θ(h)` listed in Proposition 3.3.3 (1): `H₋(t, h(t))` for
`t ∈ Θ^◇` and `H₊(t, h(t) - 1) = H₋(t + π, 1 - h(t))` for `t ∈ {ω, π/2}`. -/
def capHalfPlanes (Θ : AngleSet) (h : ℝ → ℝ) : Set HalfPlaneData :=
  {d | (d.t ∈ Θ.diamond ∧ d.h = h d.t ∧ d.isOpen = false) ∨
    (∃ t ∈ ({Θ.ω, π / 2} : Set ℝ), d.t = t + π ∧ d.h = 1 - h t ∧ d.isOpen = false)}

/-- The defining half-planes of `𝒩_Θ(h)` listed in Proposition 3.3.3 (2): `H₋°(t, h(t) - 1)` for
`t ∈ Θ ∪ (Θ + π/2)` and `H₊(t, h(t) - 1)` for `t ∈ {ω, π/2}`. -/
def nicheHalfPlanes (Θ : AngleSet) (h : ℝ → ℝ) : Set HalfPlaneData :=
  {d | (d.t ∈ (Θ.angles : Set ℝ) ∪ (fun s => s + π / 2) '' (Θ.angles : Set ℝ) ∧ d.h = h d.t - 1 ∧
      d.isOpen = true) ∨
    (∃ t ∈ ({Θ.ω, π / 2} : Set ℝ), d.t = t + π ∧ d.h = 1 - h t ∧ d.isOpen = false)}

/-- **Proposition 3.3.3** (`pro:cap-niche-nef-polygons`). `𝓒_Θ(h)` and `𝒩_Θ(h)` are simple Nef
polygons with the listed defining half-planes. -/
theorem proposition3_3_3 (Θ : AngleSet) (h : ℝ → ℝ) :
    (∃ (n : ℕ) (E : BoolFun n) (H : Fin n → HalfPlaneData), IsSimpleNefPolygon (capH Θ h) E H ∧
        Set.range H = capHalfPlanes Θ h) ∧
      (∃ (n : ℕ) (E : BoolFun n) (H : Fin n → HalfPlaneData), IsSimpleNefPolygon (nicheH Θ h) E H ∧
        Set.range H = nicheHalfPlanes Θ h) := by
  sorry

/-- **Proposition 3.3.4** (`pro:cap-extension-compatible`). `𝓒_Θ(h_{K'}) = K'` for a polygon cap
translate `K'`. -/
theorem proposition3_3_4 {Θ : AngleSet} {K' : Set (ℝ × ℝ)} (hK' : IsPolygonCapTranslate Θ K') :
    capH Θ (supp K') = K' := by
  sorry

/-- **Proposition 3.3.5** (`pro:niche-extension-compatible`). For a polygon cap `K`,
`𝒩_Θ(h_K) = 𝒩_Θ(K)` and `𝒜_Θ(h_K) = 𝒜_Θ(K)`. -/
theorem proposition3_3_5 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) :
    nicheH Θ (supp K) = polyNiche Θ K ∧ areaH Θ (supp K) = polyArea Θ K := by
  sorry

/-- The niche and the polygon sofa area functional of a polygon cap translate
(Definition 3.3.4, `def:cap-translate-extensions`). -/
def nicheT (Θ : AngleSet) (K' : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := nicheH Θ (supp K')

/-- `𝒜_Θ(K') := 𝒜_Θ(h_{K'})` (Definition 3.3.4). -/
noncomputable def areaT (Θ : AngleSet) (K' : Set (ℝ × ℝ)) : ℝ := areaH Θ (supp K')

/-- **Theorem 3.3.6** (`thm:height-extensions`). For a translate `K' = K + v` of a polygon cap,
`𝒩_Θ(K') = 𝒩_Θ(K) + v` and `𝒜_Θ(K') = 𝒜_Θ(K)`. -/
theorem theorem3_3_6 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) (v : ℝ × ℝ) :
    nicheT Θ ((fun p => p + v) '' K) = (fun p => p + v) '' polyNiche Θ K ∧
      areaT Θ ((fun p => p + v) '' K) = polyArea Θ K := by
  sorry

/-- **Proposition 3.3.7** (`pro:cap-translate-reduction`). If `K⁺ = 𝓒_Θ(h⁺)` is a polygon cap
translate, then `𝒜_Θ(h⁺) ≤ 𝒜_Θ(K⁺)`. -/
theorem proposition3_3_7 {Θ : AngleSet} {h : ℝ → ℝ}
    (hK : IsPolygonCapTranslate Θ (capH Θ h)) : areaH Θ h ≤ areaT Θ (capH Θ h) := by
  sorry

end MovingSofa
