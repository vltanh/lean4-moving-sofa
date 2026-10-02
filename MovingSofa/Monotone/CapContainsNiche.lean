module

public import MovingSofa.Monotone.CapNiche

/-!
# The cap contains the niche (§2.5)

Propositions 2.5.1–2.5.4, Theorem 2.5.5 (`thm:wedge-ends-in-cap`), Lemmas 2.5.6–2.5.7, Theorems
2.5.8 (`thm:monotonization-connected-iff`), 2.5.9 (`thm:niche-in-cap`), 2.5.10
(`thm:sofa-area-functional`) and Remark 2.5.2 (`rem:niche-not-in-cap`).
-/

@[expose] public section

open Real Set

namespace MovingSofa

/-- **Proposition 2.5.1** (`pro:upper-boundary-interior`). The upper boundary `δK` is the boundary of
`K` in the subspace topology of the fan `F_ω`, that is `K ∩ closure (F_ω \ K)`. -/
theorem proposition2_5_1 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    upperBoundary K ω = K ∩ closure (fan ω \ K) := by
  sorry

/-- **Proposition 2.5.2** (`pro:upper-boundary-connected`). The upper boundary of a cap is
connected. -/
theorem proposition2_5_2 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    IsConnected (upperBoundary K ω) := by
  sorry

/-- **Proposition 2.5.3** (`pro:wedge`). The niche is the union of the wedges. -/
theorem proposition2_5_3 (K : Set (ℝ × ℝ)) (ω : ℝ) :
    niche K ω = ⋃ t ∈ Ioo 0 ω, wedge K ω t := by
  sorry

/-! **Proposition 2.5.4** (`pro:mirror-reflection`). The parts of the supporting hallway, the cap
and the niche are equivariant under `M_ω`. The paper writes `?_{K^m}(t) = M_ω(?_K(ω - t))` also for
`? = a, b, c, d, W, Z`; since the reflection exchanges the two arms of the hallway, the correct
statement exchanges `a ↔ c`, `b ↔ d` and `W ↔ Z`, as the paper's own next items (`A ↔ C` and
`w ↔ z`) do. The statements below are the corrected ones. -/

theorem proposition2_5_4_isCap {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    IsCap (mirrorCap K ω) ω := by
  sorry

theorem proposition2_5_4_supp {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (t : ℝ) :
    supp (mirrorCap K ω) t = supp K (ω + π / 2 - t) := by
  sorry

theorem proposition2_5_4_hallway {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (t : ℝ) :
    suppHallway (mirrorCap K ω) t = mirror ω '' suppHallway K (ω - t) ∧
      innerCorner (mirrorCap K ω) t = mirror ω (innerCorner K (ω - t)) ∧
      outerCorner (mirrorCap K ω) t = mirror ω (outerCorner K (ω - t)) ∧
      wallA (mirrorCap K ω) t = mirror ω '' wallC K (ω - t) ∧
      wallB (mirrorCap K ω) t = mirror ω '' wallD K (ω - t) ∧
      wallC (mirrorCap K ω) t = mirror ω '' wallA K (ω - t) ∧
      wallD (mirrorCap K ω) t = mirror ω '' wallB K (ω - t) ∧
      wedgeW (mirrorCap K ω) t = mirror ω (wedgeZ K ω (ω - t)) ∧
      wedgeZ (mirrorCap K ω) ω t = mirror ω (wedgeW K (ω - t)) := by
  sorry

theorem proposition2_5_4_vertices {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (t : ℝ) :
    aPlus (mirrorCap K ω) t = mirror ω (cMinus K (ω - t)) ∧
      aMinus (mirrorCap K ω) t = mirror ω (cPlus K (ω - t)) ∧
      cPlus (mirrorCap K ω) t = mirror ω (aMinus K (ω - t)) ∧
      cMinus (mirrorCap K ω) t = mirror ω (aPlus K (ω - t)) := by
  sorry

theorem proposition2_5_4_gaps {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (t : ℝ) :
    wedgeGapW (mirrorCap K ω) t = wedgeGapZ K ω (ω - t) ∧
      wedgeGapZ (mirrorCap K ω) ω t = wedgeGapW K (ω - t) := by
  sorry

theorem proposition2_5_4_sets {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (t : ℝ) :
    upperBoundary (mirrorCap K ω) ω = mirror ω '' upperBoundary K ω ∧
      wedge (mirrorCap K ω) ω t = mirror ω '' wedge K ω (ω - t) ∧
      niche (mirrorCap K ω) ω = mirror ω '' niche K ω := by
  sorry

theorem proposition2_5_4_sigma {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    sigma (mirrorCap K ω) = (sigma K).map (fun s => ω + π / 2 - s) := by
  sorry

/-- **Theorem 2.5.5** (`thm:wedge-ends-in-cap`). The wedge gaps are positive. -/
theorem theorem2_5_5 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) {t : ℝ} (ht : t ∈ Ioo 0 ω) :
    0 < wedgeGapW K t ∧ 0 < wedgeGapZ K ω t := by
  sorry

/-- **Lemma 2.5.6** (`lem:niche-in-cap`). If the inner corner `x_K(t)` lies in `K`, then so does the
wedge `T_K(t)`. -/
theorem lemma2_5_6 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) {t : ℝ} (ht : t ∈ Ioo 0 ω)
    (hx : innerCorner K t ∈ K) : wedge K ω t ⊆ K := by
  sorry

/-- **Lemma 2.5.7** (`lem:cap-ends-not-in-niche`). The endpoints `A_K⁻(0)` and `C_K⁺(ω)` lie in
`K \ 𝒩(K)`. -/
theorem lemma2_5_7 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    aMinus K 0 ∈ K \ niche K ω ∧ cPlus K ω ∈ K \ niche K ω := by
  sorry

/-- **Theorem 2.5.8** (`thm:monotonization-connected-iff`). For a cap `K`, the following are
equivalent: (1) `𝒩(K) ⊆ K`; (2) `𝒩(K) ⊆ K \ δK`; (3) for every `t ∈ (0, ω)`, either
`x_K(t) ∉ F_ω°` or `x_K(t) ∈ K`; (4) `K \ 𝒩(K)` is connected. -/
theorem theorem2_5_8 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    List.TFAE [niche K ω ⊆ K, niche K ω ⊆ K \ upperBoundary K ω,
      ∀ t ∈ Ioo 0 ω, innerCorner K t ∉ interior (fan ω) ∨ innerCorner K t ∈ K,
      IsConnected (K \ niche K ω)] := by
  sorry

/-- **Theorem 2.5.9** (`thm:niche-in-cap`). A cap `K` is the cap of a monotone sofa if and only if it
contains its niche. -/
theorem theorem2_5_9 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    (∃ S, IsMonotoneSofa S ω ∧ capOf S ω = K) ↔ niche K ω ⊆ K := by
  sorry

/-- **Remark 2.5.2** (`rem:niche-not-in-cap`). The cap `[0, 100] × [0, 1]` with rotation angle `π/2`
does not contain its niche. -/
theorem remark2_5_2 : IsCap (Icc (0 : ℝ) 100 ×ˢ Icc 0 1) (π / 2) ∧
    ¬ niche (Icc (0 : ℝ) 100 ×ˢ Icc 0 1) (π / 2) ⊆ Icc (0 : ℝ) 100 ×ˢ Icc 0 1 := by
  sorry

/-- **Theorem 2.5.10** (`thm:sofa-area-functional`). For the cap `K = 𝓒(S)` of a monotone sofa,
`𝒜_ω(K) = |S|`. -/
theorem theorem2_5_10 {S : Set (ℝ × ℝ)} {ω : ℝ} (hS : IsMonotoneSofa S ω) :
    sofaArea ω (capOf S ω) = area S := by
  sorry

end MovingSofa
