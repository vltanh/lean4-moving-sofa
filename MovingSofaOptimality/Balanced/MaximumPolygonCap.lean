module

public import MovingSofaOptimality.Balanced.Polyline

/-!
# Maximum polygon caps (§3.4)

Definition 3.4.5, Lemmas 3.4.6–3.4.8 and Theorems 3.4.9, 3.4.10: maximum polygon caps are balanced
(Theorem 3.4.9, `thm:balanced-polygon-sofa`) and contain their niches (Theorem 3.4.10,
`thm:balanced-polygon-sofa-connected`).

This is the last of the four modules of §3.4, which form a chain of imports; it re-exports the
earlier ones:
* `MovingSofaOptimality.Balanced.CapGeometry`: preliminaries on convex bodies, the angles `Θ^◇`,
  the corners and the walk along the upper boundary of polygon caps (`mpc_walk`), the caps
  `𝓒_Θ(h)`, and the niche as the region between two graphs.
* `MovingSofaOptimality.Balanced.MaxPolygonCapExists`: Definition 3.4.1, Lemmas 3.4.1–3.4.2 and
  Theorem 3.4.3 (`thm:maximum-polygon-cap`): maximum polygon caps exist.
* `MovingSofaOptimality.Balanced.Polyline`: Definitions 3.4.2–3.4.4, Theorem 3.4.4
  (`thm:polyline`) and Lemma 3.4.5 (`lem:polyline-length`).

**Organization.**
* Definition 3.4.5 (`IsBalanced`) and Lemma 3.4.6 (`lem:not-balanced-positive`).
* Lemma 3.4.7 (`lem:balancing`): Theorem 3.1.2 applied to the simple Nef polygons `𝓒_Θ(h)` and
  `𝒩_Θ(h)` of Proposition 3.3.3, written with the defining half-planes and Boolean functions of
  Definition 3.3.3 (`mpcCapData`, `mpcNicheData`), the same for every `h`, so that pushing one
  half-plane of `𝓒_Θ(h)` gives `𝓒_Θ(h⁺)`; moving `l(t, h(t))` and `l(t, h(t) - 1)` together is
  reduced to two separate moves (`mpc_capH2_two_shift`).
* Lemma 3.4.8 (`lem:height-positive-increment`), Theorem 3.4.9, and Theorem 3.4.10: the walk
  along the polyline (`mpc_walk_vertex_dot_le`) puts the vertices of `𝐩_K` that Theorem 3.4.4
  gives in `H_K(s)`, `s ∈ Θ ∪ {ω}`, with `τ_K` computed from these vertices (`mpc_tau_eq_edges`);
  the other angles of `Θ^◇` come from the mirror image (Lemma 3.4.1), whose polyline is `M_ω(𝐩_K)`
  (`mpc_polyline_mirror`).
* Remark: the original statement of Theorem 3.4.4, whose edge lengths `∃ ℓ > 0` Lean elaborated
  with `ℓ : ℕ`, is false (`mpc_theorem3_4_4_nat_false`; see the statement fix in `Polyline`).
-/

@[expose] public section

open Real Set

namespace MovingSofaOptimality

/-! ## Balanced polygon caps (Definition 3.4.5, Lemma 3.4.6) -/

/-- A polygon cap is balanced if `σ_K(t) = τ_K(t)` for every `t ∈ Θ^◇` (Definition 3.4.5,
`def:polygon-cap-balanced`). -/
def IsBalanced (Θ : AngleSet) (K : Set (ℝ × ℝ)) : Prop := ∀ t ∈ Θ.diamond, sigmaAt K t = tau Θ K t

/-- **Lemma 3.4.6** (`lem:not-balanced-positive`). An unbalanced polygon cap has an angle
`t ∈ Θ^◇` with `σ_K(t) > τ_K(t)`. -/
theorem lemma3_4_6 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K)
    (hnb : ¬ IsBalanced Θ K) : ∃ t ∈ Θ.diamond, tau Θ K t < sigmaAt K t := by
  by_contra hcon
  push Not at hcon
  apply hnb
  have hsum : ∑ t ∈ mpcDiamond Θ, (tau Θ K t - sigmaAt K t) * sin t = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, mpc_sum_tau_sin hK, mpc_sum_sigma_sin hK,
      sub_self]
  have hnn : ∀ t ∈ mpcDiamond Θ, 0 ≤ (tau Θ K t - sigmaAt K t) * sin t := by
    intro t ht
    have ht' := mpc_mem_mpcDiamond.1 ht
    exact mul_nonneg (by linarith [hcon t ht']) (mpc_sin_pos_of_diamond ht').le
  intro t ht
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum t (mpc_mem_mpcDiamond.2 ht)
  rcases mul_eq_zero.1 h1 with h | h
  · linarith
  · exact absurd h (mpc_sin_pos_of_diamond ht).ne'

/-! ## The first variation of `𝒜_Θ` (Lemma 3.4.7)

`𝓒_Θ(h)` and `𝒩_Θ(h)` are simple Nef polygons with explicit defining half-planes (`mpcCapData`,
`mpcNicheData`), so Theorem 3.1.2 gives the first-order change of their areas when one defining
half-plane is pushed. For `t ∈ {ω, π/2}`, raising `h(t)` moves two sides of `𝓒_Θ(h)`, the upper
side `l(t, h(t))` and the bottom side `l(t, h(t) - 1)`; the two moves add up
(`mpc_capH2_two_shift`).
The first-order terms are the edge length `σ_K(t)` (`mpc_lineLength_edge`) and the lengths of the
sides of the niche (Lemma 3.4.5). -/

section Balancing

open Filter Topology MeasureTheory

open Classical in
/-- **Theorem 3.1.2** for simple Nef polygons indexed by a finite type. -/
lemma mpc_nef_transfer {ι : Type*} [Fintype ι] [DecidableEq ι] (Φ : (ι → Bool) → Bool)
    (hΦ : ∀ P Q : ι → Bool, (∀ i, P i = true → Q i = true) → Φ P = true → Φ Q = true)
    (d : ι → HalfPlaneData) (hd : Pairwise fun i j => (d i).boundary ≠ (d j).boundary)
    {X : Set (ℝ × ℝ)} (hX : X = {p | Φ (fun i => decide (p ∈ (d i).toSet)) = true})
    (hb : Bornology.IsBounded X) (i₀ : ι) :
    ∃ ε > 0, ∃ C : ℝ, ∀ δ : ℝ, |δ| ≤ ε →
      |area {p | Φ (fun i => decide (p ∈ (Function.update d i₀ ((d i₀).shift δ) i).toSet)) = true} -
        area X - lineLength (d i₀).t (d i₀).h (frontier X) * δ| ≤ C * δ ^ 2 := by
  classical
  set e := Fintype.equivFin ι
  set E : BoolFun (Fintype.card ι) := fun P => Φ (fun i => P (e i))
  set H : Fin (Fintype.card ι) → HalfPlaneData := fun k => d (e.symm k)
  have hsimple : IsSimpleNefPolygon X E H := by
    refine ⟨fun P Q hPQ hP => hΦ _ _ (fun i => hPQ (e i)) hP, ?_, ?_⟩
    · intro k l hkl
      exact hd (fun h => hkl (e.symm.injective h))
    · rw [hX]
      ext p
      simp only [nefPolygon, mem_ofPred_eq, E, H, Equiv.symm_apply_apply]
  obtain ⟨ε, hε, C, hC⟩ := theorem3_1_2 hsimple hb (e i₀)
  refine ⟨ε, hε, C, fun δ hδ => ?_⟩
  have h := hC δ hδ
  have hset :
      nefPolygon E (Function.update (fun j => (H j).toSet) (e i₀) ((H (e i₀)).shift δ).toSet) =
      {p | Φ (fun i => decide (p ∈ (Function.update d i₀ ((d i₀).shift δ) i).toSet)) = true} := by
    ext p
    simp only [nefPolygon, mem_ofPred_eq, E, H]
    congr! 3 with i
    by_cases hi : i = i₀
    · subst hi
      simp [Function.update_self]
    · rw [Function.update_of_ne (e.injective.ne hi), Function.update_of_ne hi,
        Equiv.symm_apply_apply]
  rw [hset] at h
  simpa [H] using h

/-- The length of the part of the frontier of a convex body on a supporting line is the length of
the edge. -/
lemma mpc_lineLength_edge {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (s : ℝ) :
    lineLength s (supp K s) (frontier K) = sigmaAt K s := by
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ × ℝ, g = fun σ => supp K s • uvec s + σ • vvec s := ⟨_, rfl⟩
  have hgu : ∀ σ, dot (g σ) (uvec s) = supp K s := fun σ => by
    simp [hg, dot_add_left, dot_smul_left]
  -- a point of the supporting line `l_K(s)` lies on the frontier of `K` iff it lies in `K`
  have hfr : ∀ σ, g σ ∈ frontier K ↔ g σ ∈ K := fun σ => by
    refine ⟨fun h => hK.isClosed.frontier_subset h, fun h => ⟨subset_closure h, fun hint => ?_⟩⟩
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
    have hq : g σ + (ε / 2) • uvec s ∈ Metric.ball (g σ) ε := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (half_pos hε)]
      nlinarith [norm_uvec_le s]
    have := dot_le_supp hK.2.1 (hball hq) s
    rw [dot_add_left, dot_smul_left, dot_uvec_self, hgu] at this
    linarith
  -- the edge `e_K(s)` is the image of `[v_K⁻(s) · v_s, v_K⁺(s) · v_s]` under the affine map `g`
  have hle := dot_vminus_le_dot_vplus hK s
  have hseg : edge K s = g '' Icc (dot (vminus K s) (vvec s)) (dot (vplus K s) (vvec s)) := by
    have hg' : ∀ p ∈ edge K s, g (dot p (vvec s)) = p := fun p hp => by
      rw [hg]; dsimp only; rw [← hp.2]; exact (eq_dot_uvec_smul_add p s).symm
    have hf : ⇑(AffineMap.lineMap (supp K s • uvec s) (supp K s • uvec s + vvec s) :
        ℝ →ᵃ[ℝ] ℝ × ℝ) = g := by
      funext τ; simp [AffineMap.lineMap_apply_module', hg, add_comm]
    rw [← segment_eq_Icc hle, ← hf, image_segment, hf, hg' _ (vminus_mem_edge hK s),
      hg' _ (vplus_mem_edge hK s), edge_eq_segment hK]
  have hinj : Function.Injective g := fun σ τ h => by
    simpa [hg, dot_add_left, dot_smul_left] using congrArg (fun p => dot p (vvec s)) h
  have hset : {σ : ℝ | supp K s • uvec s + σ • vvec s ∈ frontier K} =
      Icc (dot (vminus K s) (vvec s)) (dot (vplus K s) (vvec s)) := by
    ext σ
    rw [mem_ofPred_eq, show supp K s • uvec s + σ • vvec s = g σ by rw [hg], hfr,
      show g σ ∈ K ↔ g σ ∈ edge K s from ⟨fun h => ⟨h, hgu σ⟩, fun h => h.1⟩, hseg,
      hinj.mem_set_image]
  rw [lineLength, hset, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.2 hle),
    sigmaAt_eq_dot_sub hK]

/-- Reversing the normal of a line. -/
lemma mpc_lineLength_add_pi (t c : ℝ) (X : Set (ℝ × ℝ)) :
    lineLength (t + π) c X = lineLength t (-c) X := by
  have : {σ : ℝ | c • uvec (t + π) + σ • vvec (t + π) ∈ X} =
      (fun σ => -1 * σ) ⁻¹' {σ : ℝ | (-c) • uvec t + σ • vvec t ∈ X} := by
    ext σ
    simp only [mem_ofPred_eq, mem_preimage, uvec_add_pi, vvec_add_pi]
    rw [show c • -uvec t + σ • -vvec t = (-c) • uvec t + (-1 * σ) • vvec t by
      simp [smul_neg, neg_smul]]
  rw [lineLength, lineLength, this, Real.volume_preimage_mul_left (by norm_num)]
  simp

/-! ### Simple Nef representations of `𝓒_Θ(h)` and `𝒩_Θ(h)` -/

/-- The finset `{ω, π/2}` of the bottom normal angles (up to `π`). -/
noncomputable def mpcBot (Θ : AngleSet) : Finset ℝ := {Θ.ω, π / 2}

/-- The finset `Θ ∪ (Θ + π/2)` of the inner normal angles. -/
noncomputable def mpcInner (Θ : AngleSet) : Finset ℝ :=
  Θ.angles ∪ Θ.angles.image (fun t => t + π / 2)

lemma mpc_mem_mpcBot {Θ : AngleSet} {b : ℝ} : b ∈ mpcBot Θ ↔ b = Θ.ω ∨ b = π / 2 := by
  simp [mpcBot]

lemma mpc_mem_mpcInner {Θ : AngleSet} {s : ℝ} :
    s ∈ mpcInner Θ ↔ s ∈ Θ.angles ∨ ∃ t ∈ Θ.angles, s = t + π / 2 := by
  simp only [mpcInner, Finset.mem_union, Finset.mem_image, eq_comm (a := s)]

lemma mpc_bot_diamond {Θ : AngleSet} {b : ℝ} (hb : b ∈ mpcBot Θ) : b ∈ Θ.diamond := by
  rcases mpc_mem_mpcBot.1 hb with rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

lemma mpc_inner_diamond {Θ : AngleSet} {s : ℝ} (hs : s ∈ mpcInner Θ) : s ∈ Θ.diamond :=
  (mpc_inner_ne (mpc_mem_mpcInner.1 hs)).1

lemma mpc_inner_not_bot {Θ : AngleSet} {s : ℝ} (hs : s ∈ mpcInner Θ) : s ∉ mpcBot Θ := by
  obtain ⟨-, h1, h2⟩ := mpc_inner_ne (mpc_mem_mpcInner.1 hs)
  rw [mpc_mem_mpcBot]
  push Not
  exact ⟨h1, h2⟩

/-- The defining half-planes of `𝓒_Θ`. -/
noncomputable def mpcCapData (Θ : AngleSet) (hT hB : ℝ → ℝ) :
    {s // s ∈ mpcDiamond Θ} ⊕ {b // b ∈ mpcBot Θ} → HalfPlaneData
  | Sum.inl s => ⟨s.1, hT s.1, false⟩
  | Sum.inr b => ⟨b.1 + π, 1 - hB b.1, false⟩

/-- The defining half-planes of `𝒩_Θ`. -/
noncomputable def mpcNicheData (Θ : AngleSet) (h : ℝ → ℝ) :
    {s // s ∈ mpcInner Θ} ⊕ {b // b ∈ mpcBot Θ} → HalfPlaneData
  | Sum.inl s => ⟨s.1, h s.1 - 1, true⟩
  | Sum.inr b => ⟨b.1 + π, 1 - h b.1, false⟩

/-- A bottom half-plane `H₋(b + π, c)` is `{p : -c ≤ p · u_b}`. -/
lemma mpc_toSet_bot (b c : ℝ) (p : ℝ × ℝ) :
    p ∈ (⟨b + π, c, false⟩ : HalfPlaneData).toSet ↔ -c ≤ dot p (uvec b) := by
  simp only [HalfPlaneData.toSet, Bool.false_eq_true, ↓reduceIte, halfMinus, mem_ofPred_eq,
    dot_uvec_add_pi]
  constructor <;> intro h <;> linarith

/-- `mpcCapH2 Θ hT hB` is the intersection of the half-planes of `mpcCapData`. -/
lemma mpc_mem_capH2_iff (Θ : AngleSet) (hT hB : ℝ → ℝ) (p : ℝ × ℝ) :
    p ∈ mpcCapH2 Θ hT hB ↔ ∀ i, p ∈ (mpcCapData Θ hT hB i).toSet := by
  constructor
  · rintro ⟨h1, h2, h3⟩ (⟨s, hs⟩ | ⟨b, hb⟩)
    · exact h1 s (mpc_mem_mpcDiamond.1 hs)
    · rw [mpcCapData, mpc_toSet_bot]
      rcases mpc_mem_mpcBot.1 hb with rfl | rfl <;> linarith
  · intro h
    refine ⟨fun s hs => h (Sum.inl ⟨s, mpc_mem_mpcDiamond.2 hs⟩), ?_, ?_⟩
    · have := h (Sum.inr ⟨Θ.ω, mpc_mem_mpcBot.2 (Or.inl rfl)⟩)
      rw [mpcCapData, mpc_toSet_bot] at this
      linarith
    · have := h (Sum.inr ⟨π / 2, mpc_mem_mpcBot.2 (Or.inr rfl)⟩)
      rw [mpcCapData, mpc_toSet_bot] at this
      linarith

/-- `𝒩_Θ(h)` in terms of the half-planes of `mpcNicheData`. -/
lemma mpc_mem_nicheH_iff (Θ : AngleSet) (h : ℝ → ℝ) (p : ℝ × ℝ) :
    p ∈ nicheH Θ h ↔ (∀ b : {b // b ∈ mpcBot Θ}, p ∈ (mpcNicheData Θ h (Sum.inr b)).toSet) ∧
      ∃ t, ∃ ht : t ∈ Θ.angles,
        p ∈ (mpcNicheData Θ h (Sum.inl ⟨t, Finset.mem_union_left _ ht⟩)).toSet ∧
        p ∈ (mpcNicheData Θ h (Sum.inl ⟨t + π / 2,
          Finset.mem_union_right _ (Finset.mem_image_of_mem _ ht)⟩)).toSet := by
  simp only [nicheH, fanH, mem_inter_iff, mem_iInter, mem_iUnion, mem_insert_iff,
    mem_singleton_iff, halfPlus, mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨h1, t, ht, h2, h3⟩
    refine ⟨fun ⟨b, hb⟩ => ?_, t, ht, ?_, ?_⟩
    · rw [mpcNicheData, mpc_toSet_bot]
      have := h1 b (mpc_mem_mpcBot.1 hb)
      linarith
    · simp only [mpcNicheData, HalfPlaneData.toSet, ↓reduceIte]; exact h2
    · simp only [mpcNicheData, HalfPlaneData.toSet, ↓reduceIte]; exact h3
  · rintro ⟨h1, t, ht, h2, h3⟩
    refine ⟨fun b hb => ?_, t, ht, ?_, ?_⟩
    · have := h1 ⟨b, mpc_mem_mpcBot.2 hb⟩
      rw [mpcNicheData, mpc_toSet_bot] at this
      linarith
    · simp only [mpcNicheData, HalfPlaneData.toSet, ↓reduceIte] at h2; exact h2
    · simp only [mpcNicheData, HalfPlaneData.toSet, ↓reduceIte] at h3; exact h3

open Classical in
/-- The boolean function of `𝒩_Θ`. -/
noncomputable def mpcNicheBool (Θ : AngleSet)
    (P : {s // s ∈ mpcInner Θ} ⊕ {b // b ∈ mpcBot Θ} → Bool) : Bool :=
  decide ((∀ b, P (Sum.inr b) = true) ∧ ∃ t, ∃ ht : t ∈ Θ.angles,
    P (Sum.inl ⟨t, Finset.mem_union_left _ ht⟩) = true ∧
    P (Sum.inl ⟨t + π / 2, Finset.mem_union_right _ (Finset.mem_image_of_mem _ ht)⟩) = true)

section NefData

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

/-- The defining half-planes of `𝓒_Θ(h)` have distinct boundary lines: they are the defining
half-planes of the simple Nef polygon `𝓒_Θ(h)` of Proposition 3.3.3 (1). -/
lemma mpc_capData_pairwise (Θ : AngleSet) (h : ℝ → ℝ) :
    Pairwise fun i j => (mpcCapData Θ h h i).boundary ≠ (mpcCapData Θ h h j).boundary := by
  obtain ⟨_, _, H, ⟨-, hH, -⟩, hrange⟩ := (proposition3_3_3 Θ h).1
  have hmem : ∀ i, mpcCapData Θ h h i ∈ Set.range H := by
    rw [hrange]
    rintro (⟨s, hs⟩ | ⟨b, hb⟩)
    · exact Or.inl ⟨mpc_mem_mpcDiamond.1 hs, rfl, rfl⟩
    · exact Or.inr ⟨b, mpc_mem_mpcBot.1 hb, rfl, rfl, rfl⟩
  -- `mpcCapData` is injective: the normal angles `s ∈ Θ^◇` lie in `(0, π)`, the normal angles
  -- `b + π` of the bottom half-planes in `(π, 2π)`
  have hD : ∀ s ∈ mpcDiamond Θ, s ∈ Ioo 0 π := fun s hs =>
    nef_mem_diamond_Ioo (mpc_mem_mpcDiamond.1 hs)
  have hB : ∀ b ∈ mpcBot Θ, b ∈ Ioo 0 π := fun b hb => nef_mem_diamond_Ioo (mpc_bot_diamond hb)
  have hinj : Function.Injective (mpcCapData Θ h h) := by
    intro i j he
    have ht := congrArg HalfPlaneData.t he
    rcases i with ⟨s, hs⟩ | ⟨b, hb⟩ <;> rcases j with ⟨s', hs'⟩ | ⟨b', hb'⟩ <;>
      simp only [mpcCapData] at ht
    · exact congrArg Sum.inl (Subtype.ext ht)
    · linarith [(hD s hs).2, (hB b' hb').1]
    · linarith [(hB b hb).1, (hD s' hs').2]
    · exact congrArg Sum.inr (Subtype.ext (by linarith))
  intro i j hij heq
  obtain ⟨k, hk⟩ := hmem i
  obtain ⟨l, hl⟩ := hmem j
  have hkl : k ≠ l := by
    rintro rfl
    exact hij (hinj (hk.symm.trans hl))
  exact hH hkl (by rw [hk, hl]; exact heq)

/-- The defining half-planes of `𝒩_Θ(h)` have distinct boundary lines: they are the defining
half-planes of the simple Nef polygon `𝒩_Θ(h)` of Proposition 3.3.3 (2). -/
lemma mpc_nicheData_pairwise (Θ : AngleSet) (h : ℝ → ℝ) :
    Pairwise fun i j => (mpcNicheData Θ h i).boundary ≠ (mpcNicheData Θ h j).boundary := by
  obtain ⟨_, _, H, ⟨-, hH, -⟩, hrange⟩ := (proposition3_3_3 Θ h).2
  have hmem : ∀ i, mpcNicheData Θ h i ∈ Set.range H := by
    rw [hrange]
    rintro (⟨s, hs⟩ | ⟨b, hb⟩)
    · refine Or.inl ⟨?_, rfl, rfl⟩
      rcases mpc_mem_mpcInner.1 hs with hs' | ⟨t, ht, rfl⟩
      · exact Or.inl hs'
      · exact Or.inr ⟨t, ht, rfl⟩
    · exact Or.inr ⟨b, mpc_mem_mpcBot.1 hb, rfl, rfl, rfl⟩
  -- `mpcNicheData` is injective: the inner normal angles lie in `(0, π)`, the normal angles
  -- `b + π` of the bottom half-planes in `(π, 2π)`
  have hI : ∀ s ∈ mpcInner Θ, s ∈ Ioo 0 π := fun s hs =>
    nef_mem_diamond_Ioo (mpc_inner_diamond hs)
  have hB : ∀ b ∈ mpcBot Θ, b ∈ Ioo 0 π := fun b hb => nef_mem_diamond_Ioo (mpc_bot_diamond hb)
  have hinj : Function.Injective (mpcNicheData Θ h) := by
    intro i j he
    have ht := congrArg HalfPlaneData.t he
    rcases i with ⟨s, hs⟩ | ⟨b, hb⟩ <;> rcases j with ⟨s', hs'⟩ | ⟨b', hb'⟩ <;>
      simp only [mpcNicheData] at ht
    · exact congrArg Sum.inl (Subtype.ext ht)
    · linarith [(hI s hs).2, (hB b' hb').1]
    · linarith [(hB b hb).1, (hI s' hs').2]
    · exact congrArg Sum.inr (Subtype.ext (by linarith))
  intro i j hij heq
  obtain ⟨k, hk⟩ := hmem i
  obtain ⟨l, hl⟩ := hmem j
  have hkl : k ≠ l := by
    rintro rfl
    exact hij (hinj (hk.symm.trans hl))
  exact hH hkl (by rw [hk, hl]; exact heq)

/-- Pushing the upper side `l(t, h_T(t))` of `mpcCapH2` raises `h_T(t)`. -/
lemma mpc_capData_update_inl (hT hB : ℝ → ℝ) {t : ℝ} (ht : t ∈ mpcDiamond Θ) (δ : ℝ) :
    Function.update (mpcCapData Θ hT hB) (Sum.inl ⟨t, ht⟩)
        ((mpcCapData Θ hT hB (Sum.inl ⟨t, ht⟩)).shift δ) =
      mpcCapData Θ (Function.update hT t (hT t + δ)) hB := by
  funext i
  rcases i with ⟨s, hs⟩ | ⟨b, hb⟩
  · by_cases hst : s = t
    · subst hst
      rw [Function.update_self]
      simp [mpcCapData, HalfPlaneData.shift, Function.update_self]
    · rw [Function.update_of_ne (fun h => hst (by injection h with h; injection h))]
      simp [mpcCapData, Function.update_of_ne hst]
  · rw [Function.update_of_ne (by simp)]
    simp [mpcCapData]

/-- Pushing the bottom side `l(b + π, 1 - h_B(b))` of `mpcCapH2` lowers `h_B(b)`. -/
lemma mpc_capData_update_inr (hT hB : ℝ → ℝ) {b : ℝ} (hb : b ∈ mpcBot Θ) (δ : ℝ) :
    Function.update (mpcCapData Θ hT hB) (Sum.inr ⟨b, hb⟩)
        ((mpcCapData Θ hT hB (Sum.inr ⟨b, hb⟩)).shift δ) =
      mpcCapData Θ hT (Function.update hB b (hB b - δ)) := by
  funext i
  rcases i with ⟨s, hs⟩ | ⟨b', hb'⟩
  · rw [Function.update_of_ne (by simp)]
    simp [mpcCapData]
  · by_cases hbb : b' = b
    · subst hbb
      rw [Function.update_self]
      simp only [mpcCapData, HalfPlaneData.shift, Function.update_self]
      congr 1
      ring
    · rw [Function.update_of_ne (fun h => hbb (by injection h with h; injection h))]
      simp [mpcCapData, Function.update_of_ne hbb]

/-- Pushing the wall `l(t, h(t) - 1)` of `𝒩_Θ(h)` raises `h(t)`. -/
lemma mpc_nicheData_update_inl (h : ℝ → ℝ) {t : ℝ} (ht : t ∈ mpcInner Θ) (δ : ℝ) :
    Function.update (mpcNicheData Θ h) (Sum.inl ⟨t, ht⟩)
        ((mpcNicheData Θ h (Sum.inl ⟨t, ht⟩)).shift δ) =
      mpcNicheData Θ (Function.update h t (h t + δ)) := by
  funext i
  rcases i with ⟨s, hs⟩ | ⟨b, hb⟩
  · by_cases hst : s = t
    · subst hst
      rw [Function.update_self]
      simp only [mpcNicheData, HalfPlaneData.shift, Function.update_self]
      congr 1
      ring
    · rw [Function.update_of_ne (fun h => hst (by injection h with h; injection h))]
      simp [mpcNicheData, Function.update_of_ne hst]
  · rw [Function.update_of_ne (by simp)]
    have hbt : b ≠ t := fun h => mpc_inner_not_bot ht (h ▸ hb)
    simp [mpcNicheData, Function.update_of_ne hbt]

/-- Pushing the bottom side `l(b + π, 1 - h(b))` of `𝒩_Θ(h)` lowers `h(b)`. -/
lemma mpc_nicheData_update_inr (h : ℝ → ℝ) {b : ℝ} (hb : b ∈ mpcBot Θ) (δ : ℝ) :
    Function.update (mpcNicheData Θ h) (Sum.inr ⟨b, hb⟩)
        ((mpcNicheData Θ h (Sum.inr ⟨b, hb⟩)).shift δ) =
      mpcNicheData Θ (Function.update h b (h b - δ)) := by
  funext i
  rcases i with ⟨s, hs⟩ | ⟨b', hb'⟩
  · rw [Function.update_of_ne (by simp)]
    have hsb : s ≠ b := fun h => mpc_inner_not_bot hs (h ▸ hb)
    simp [mpcNicheData, Function.update_of_ne hsb]
  · by_cases hbb : b' = b
    · subst hbb
      rw [Function.update_self]
      simp only [mpcNicheData, HalfPlaneData.shift, Function.update_self]
      congr 1
      ring
    · rw [Function.update_of_ne (fun h => hbb (by injection h with h; injection h))]
      simp [mpcNicheData, Function.update_of_ne hbb]

end NefData

section Derivatives

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

/-- `mpcCapH2 Θ hT hB` is closed. -/
lemma mpc_isClosed_capH2 (Θ : AngleSet) (hT hB : ℝ → ℝ) : IsClosed (mpcCapH2 Θ hT hB) := by
  have : mpcCapH2 Θ hT hB = (⋂ s ∈ Θ.diamond, {p : ℝ × ℝ | dot p (uvec s) ≤ hT s}) ∩
      ({p | hB Θ.ω - 1 ≤ dot p (uvec Θ.ω)} ∩ {p | hB (π / 2) - 1 ≤ dot p (uvec (π / 2))}) := by
    ext p; simp [mpcCapH2]
  rw [this]
  have hc : ∀ v : ℝ × ℝ, Continuous fun p : ℝ × ℝ => dot p v := fun v => by
    simp only [dot]; fun_prop
  exact (isClosed_biInter fun s _ => isClosed_le (hc _) continuous_const).inter
    ((isClosed_le continuous_const (hc _)).inter (isClosed_le continuous_const (hc _)))

/-- Pushing the top side `l(t, h(t))` and the bottom side `l(t, h(t) - 1)` of `𝓒_Θ` by `ε ≤ 1` in
the same direction adds up the two separate area changes. -/
lemma mpc_capH2_two_shift (hh : ℝ → ℝ) {t ε : ℝ} (ht : t ∈ mpcBot Θ) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) :
    area (mpcCapH2 Θ (Function.update hh t (hh t + ε)) (Function.update hh t (hh t + ε))) +
        area (mpcCapH2 Θ hh hh) =
      area (mpcCapH2 Θ (Function.update hh t (hh t + ε)) hh) +
        area (mpcCapH2 Θ hh (Function.update hh t (hh t + ε))) := by
  set hp := Function.update hh t (hh t + ε) with hhp
  have hle : ∀ r, hh r ≤ hp r := by
    intro r; rw [hhp, Function.update_apply]; split_ifs with h
    · rw [h]; linarith
    · exact le_rfl
  have htd := mpc_bot_diamond ht
  set V := mpcCapH2 Θ hp hp
  set X := mpcCapH2 Θ hh hh
  set U := mpcCapH2 Θ hp hh
  set W := mpcCapH2 Θ hh hp
  have hVU : V ⊆ U := by
    rintro p ⟨h1, h2, h3⟩
    exact ⟨h1, by linarith [hle Θ.ω], by linarith [hle (π / 2)]⟩
  have hWX : W ⊆ X := by
    rintro p ⟨h1, h2, h3⟩
    exact ⟨h1, by linarith [hle Θ.ω], by linarith [hle (π / 2)]⟩
  -- raising the bottom side at `t` removes the same strip, whether or not the top side at `t` is
  -- raised (as `ε ≤ 1`)
  have hdiff : U \ V = X \ W := by
    ext p
    simp only [Set.mem_sdiff, U, V, X, W, mpcCapH2, mem_ofPred_eq, not_and, not_le]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      -- the failing constraint is the raised bottom side at `t`
      have hfail : dot p (uvec t) < hh t + ε - 1 := by
        by_contra hc
        push Not at hc
        have hω' : hp Θ.ω - 1 ≤ dot p (uvec Θ.ω) := by
          rw [hhp, Function.update_apply]; split_ifs with h
          · rw [h]; linarith
          · exact h2
        have hπ' : hp (π / 2) - 1 ≤ dot p (uvec (π / 2)) := by
          rw [hhp, Function.update_apply]; split_ifs with h
          · rw [h]; linarith
          · exact h3
        exact absurd (h4 h1 hω') (not_lt.2 hπ')
      have htop : ∀ s ∈ Θ.diamond, dot p (uvec s) ≤ hh s := by
        intro s hs
        by_cases hst : s = t
        · subst hst; linarith
        · have := h1 s hs
          rwa [hhp, Function.update_of_ne hst] at this
      refine ⟨⟨htop, h2, h3⟩, fun _ hω => ?_⟩
      by_cases htπ : t = π / 2
      · rw [hhp, ← htπ, Function.update_self]; exact hfail
      · have htω : t = Θ.ω := by
          rcases mpc_mem_mpcBot.1 ht with h | h
          · exact h
          · exact absurd h htπ
        rw [hhp, ← htω, Function.update_self] at hω
        linarith
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨⟨fun s hs => (h1 s hs).trans (hle s), h2, h3⟩, fun _ hω => h4 h1 hω⟩
  have hVm := (mpc_isClosed_capH2 Θ hp hp).measurableSet
  have hWm := (mpc_isClosed_capH2 Θ hh hp).measurableSet
  -- the areas add up: `|V| + |U \ V| = |U|` and `|W| + |X \ W| = |X|`
  have hfin : ∀ hT hB, volume (mpcCapH2 Θ hT hB) ≠ ⊤ := fun hT hB =>
    (mpc_isBounded_capH2 Θ hT hB).measure_lt_top.ne
  have e1 : volume V + volume (U \ V) = volume U := by
    rw [measure_add_sdiff hVm.nullMeasurableSet, union_eq_right.2 hVU]
  have e2 : volume W + volume (X \ W) = volume X := by
    rw [measure_add_sdiff hWm.nullMeasurableSet, union_eq_right.2 hWX]
  have hd1 : volume (U \ V) ≠ ⊤ := ne_top_of_le_ne_top (hfin _ _) (measure_mono sdiff_subset)
  have r1 := congrArg ENNReal.toReal e1
  have r2 := congrArg ENNReal.toReal e2
  rw [ENNReal.toReal_add (hfin _ _) hd1] at r1
  rw [hdiff] at hd1 r1
  rw [ENNReal.toReal_add (hfin _ _) hd1] at r2
  simp only [area]
  linarith

open Classical in
/-- First-order area change of a polygon cap when one defining half-plane is pushed. -/
lemma mpc_cap_deriv (hK : IsPolygonCap Θ K)
    (i₀ : {s // s ∈ mpcDiamond Θ} ⊕ {b // b ∈ mpcBot Θ}) :
    ∃ ε > 0, ∃ C : ℝ, ∀ δ : ℝ, |δ| ≤ ε →
      |area {p | ∀ i, p ∈ (Function.update (mpcCapData Θ (supp K) (supp K)) i₀
          ((mpcCapData Θ (supp K) (supp K) i₀).shift δ) i).toSet} - area K -
        lineLength (mpcCapData Θ (supp K) (supp K) i₀).t (mpcCapData Θ (supp K) (supp K) i₀).h
          (frontier K) * δ| ≤ C * δ ^ 2 := by
  have hKeq : K = mpcCapH2 Θ (supp K) (supp K) := by
    rw [← mpc_capH_eq_capH2, proposition3_3_4 ⟨K, 0, hK, by simp⟩]
  obtain ⟨ε, hε, C, hC⟩ := mpc_nef_transfer (fun P => decide (∀ i, P i = true))
    (fun P Q hPQ hP => by simp only [decide_eq_true_eq] at hP ⊢; exact fun i => hPQ i (hP i))
    (mpcCapData Θ (supp K) (supp K)) (mpc_capData_pairwise Θ (supp K)) (X := K)
    (by ext p; rw [Set.ext_iff.1 hKeq p, mpc_mem_capH2_iff]; simp) hK.1.2.1.isBounded i₀
  refine ⟨ε, hε, C, fun δ hδ => ?_⟩
  simpa using hC δ hδ

open Classical in
/-- First-order area change of the polygon niche when one defining half-plane is pushed. -/
lemma mpc_niche_deriv (hK : IsPolygonCap Θ K)
    (i₀ : {s // s ∈ mpcInner Θ} ⊕ {b // b ∈ mpcBot Θ}) :
    ∃ ε > 0, ∃ C : ℝ, ∀ δ : ℝ, |δ| ≤ ε →
      |area {p | mpcNicheBool Θ (fun i => decide (p ∈ (Function.update (mpcNicheData Θ (supp K))
          i₀ ((mpcNicheData Θ (supp K) i₀).shift δ) i).toSet)) = true} - area (polyNiche Θ K) -
        lineLength (mpcNicheData Θ (supp K) i₀).t (mpcNicheData Θ (supp K) i₀).h
          (frontier (polyNiche Θ K)) * δ| ≤ C * δ ^ 2 := by
  have hNeq : polyNiche Θ K = nicheH Θ (supp K) := (proposition3_3_5 hK).1.symm
  apply mpc_nef_transfer (mpcNicheBool Θ) _ (mpcNicheData Θ (supp K))
    (mpc_nicheData_pairwise Θ (supp K)) _ (mpc_isBounded_polyNiche hK) i₀
  · intro P Q hPQ hP
    simp only [mpcNicheBool, decide_eq_true_eq] at hP ⊢
    obtain ⟨h1, t, ht, h2, h3⟩ := hP
    exact ⟨fun b => hPQ _ (h1 b), t, ht, hPQ _ h2, hPQ _ h3⟩
  · ext p
    rw [hNeq, mpc_mem_nicheH_iff]
    simp [mpcNicheBool]

end Derivatives

/-- `mpcCapH2` depends on `hB` only through `hB(ω)` and `hB(π/2)`. -/
lemma mpc_capH2_eq_bot {Θ : AngleSet} (hT hB hB' : ℝ → ℝ) (h1 : hB Θ.ω = hB' Θ.ω)
    (h2 : hB (π / 2) = hB' (π / 2)) : mpcCapH2 Θ hT hB = mpcCapH2 Θ hT hB' := by
  ext p; simp only [mpcCapH2, mem_ofPred_eq, h1, h2]

lemma mpc_capH2_set (Θ : AngleSet) (hT hB : ℝ → ℝ) :
    {p | ∀ i, p ∈ (mpcCapData Θ hT hB i).toSet} = mpcCapH2 Θ hT hB := by
  ext p; rw [mem_ofPred_eq, mpc_mem_capH2_iff]

open Classical in
lemma mpc_nicheH_set (Θ : AngleSet) (h : ℝ → ℝ) :
    {p | mpcNicheBool Θ (fun i => decide (p ∈ (mpcNicheData Θ h i).toSet)) = true} =
      nicheH Θ h := by
  ext p; rw [mpc_mem_nicheH_iff]; simp [mpcNicheBool]

end Balancing

/-- **Lemma 3.4.7** (`lem:balancing`). Raising `h_K(t)` by a small `ε > 0` changes `𝒜_Θ` by
`(σ_K(t) - τ_K(t)) ε + O(ε²)`, with the constant depending on `K` and `t`. -/
theorem lemma3_4_7 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) {t : ℝ}
    (ht : t ∈ Θ.diamond) :
    ∃ ε₀ > 0, ∃ C : ℝ, ∀ ε ∈ Ioc 0 ε₀,
      |areaH Θ (Function.update (supp K) t (supp K t + ε)) - areaH Θ (supp K) -
          (sigmaAt K t - tau Θ K t) * ε| ≤ C * ε ^ 2 := by
  classical
  have hcap := hK.1
  have hKcap : capH Θ (supp K) = K := proposition3_3_4 ⟨K, 0, hK, by simp⟩
  have hNiche : nicheH Θ (supp K) = polyNiche Θ K := (proposition3_3_5 hK).1
  have hareaH : areaH Θ (supp K) = area K - area (polyNiche Θ K) := by
    rw [areaH, hKcap, hNiche]
  have htD : t ∈ mpcDiamond Θ := mpc_mem_mpcDiamond.2 ht
  have hareaH' : ∀ ε, areaH Θ (Function.update (supp K) t (supp K t + ε)) =
      area (mpcCapH2 Θ (Function.update (supp K) t (supp K t + ε))
        (Function.update (supp K) t (supp K t + ε))) -
      area (nicheH Θ (Function.update (supp K) t (supp K t + ε))) := by
    intro ε; rw [areaH, mpc_capH_eq_capH2]
  by_cases hb : t ∈ mpcBot Θ
  · -- `t ∈ {ω, π/2}`: both the upper and the bottom side of `𝓒_Θ` move
    obtain ⟨ht1, htπ⟩ := mpc_supp_bot hcap (mpc_mem_mpcBot.1 hb)
    obtain ⟨ε1, hε1, C1, hC1⟩ := mpc_cap_deriv hK (Sum.inl ⟨t, htD⟩)
    obtain ⟨ε2, hε2, C2, hC2⟩ := mpc_cap_deriv hK (Sum.inr ⟨t, hb⟩)
    obtain ⟨ε3, hε3, C3, hC3⟩ := mpc_niche_deriv hK (Sum.inr ⟨t, hb⟩)
    refine ⟨min (min ε1 ε2) (min ε3 1), by positivity, C1 + C2 + C3, fun ε hε => ?_⟩
    obtain ⟨hε0, hεle⟩ := hε
    have hε1' : ε ≤ ε1 := hεle.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hε2' : ε ≤ ε2 := hεle.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hε3' : ε ≤ ε3 := hεle.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hε4' : ε ≤ 1 := hεle.trans ((min_le_right _ _).trans (min_le_right _ _))
    have e1 := hC1 ε (by rw [abs_of_pos hε0]; exact hε1')
    have e2 := hC2 (-ε) (by rw [abs_neg, abs_of_pos hε0]; exact hε2')
    have e3 := hC3 (-ε) (by rw [abs_neg, abs_of_pos hε0]; exact hε3')
    rw [mpc_capData_update_inl, mpc_capH2_set] at e1
    rw [mpc_capData_update_inr, mpc_capH2_set, sub_neg_eq_add] at e2
    rw [mpc_nicheData_update_inr, mpc_nicheH_set, sub_neg_eq_add] at e3
    simp only [mpcCapData, mpcNicheData] at e1 e2 e3
    rw [mpc_lineLength_edge hcap.2.1] at e1
    rw [show 1 - supp K t = supp K (t + π) by rw [ht1, htπ]; ring,
      mpc_lineLength_edge hcap.2.1] at e2
    rw [mpc_lineLength_add_pi, show -(1 - supp K t) = 0 by rw [ht1]; ring,
      (lemma3_4_5_two hK (mpc_mem_mpcBot.1 hb)).1, hNiche.symm] at e3
    rw [hNiche] at e3
    have hshift := mpc_capH2_two_shift (Θ := Θ) (supp K) hb hε0.le hε4'
    rw [← mpc_capH_eq_capH2 Θ (supp K), hKcap] at hshift
    rw [hareaH' ε, hareaH]
    have a1 := abs_le.1 e1
    have a2 := abs_le.1 e2
    have a3 := abs_le.1 e3
    rw [neg_sq] at a2 a3
    rw [abs_le]
    constructor <;> nlinarith
  · -- `t ∈ Θ ∪ (Θ + π/2)`: one side moves in `𝓒_Θ` and one in `𝒩_Θ`
    have htI : t ∈ mpcInner Θ := by
      rw [mpc_mem_mpcInner]
      rcases mpc_diamond_cases ht with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (mpc_mem_mpcBot.2 (Or.inl h)) hb
      · exact absurd (mpc_mem_mpcBot.2 (Or.inr h)) hb
    obtain ⟨-, htω, htπ2⟩ := mpc_inner_ne (mpc_mem_mpcInner.1 htI)
    obtain ⟨ε1, hε1, C1, hC1⟩ := mpc_cap_deriv hK (Sum.inl ⟨t, htD⟩)
    obtain ⟨ε3, hε3, C3, hC3⟩ := mpc_niche_deriv hK (Sum.inl ⟨t, htI⟩)
    refine ⟨min ε1 ε3, by positivity, C1 + C3, fun ε hε => ?_⟩
    obtain ⟨hε0, hεle⟩ := hε
    have e1 := hC1 ε (by rw [abs_of_pos hε0]; exact hεle.trans (min_le_left _ _))
    have e3 := hC3 ε (by rw [abs_of_pos hε0]; exact hεle.trans (min_le_right _ _))
    rw [mpc_capData_update_inl, mpc_capH2_set] at e1
    rw [mpc_nicheData_update_inl, mpc_nicheH_set] at e3
    simp only [mpcCapData, mpcNicheData] at e1 e3
    rw [mpc_lineLength_edge hcap.2.1] at e1
    have hτ : lineLength t (supp K t - 1) (frontier (polyNiche Θ K)) = tau Θ K t := by
      rcases mpc_mem_mpcInner.1 htI with h | ⟨r, hr, rfl⟩
      · exact (lemma3_4_5_one hK h).1
      · exact (lemma3_4_5_one hK hr).2.2.1
    rw [hτ] at e3
    rw [mpc_capH2_eq_bot _ _ (Function.update (supp K) t (supp K t + ε))
      (by rw [Function.update_of_ne htω.symm]) (by rw [Function.update_of_ne htπ2.symm])] at e1
    rw [hareaH' ε, hareaH]
    have a1 := abs_le.1 e1
    have a3 := abs_le.1 e3
    rw [abs_le]
    constructor <;> nlinarith

/-! ## Raising one side of a polygon cap (Lemma 3.4.8)

Raising an upper side `l(t, h_K(t))` with `t ∈ Θ ∪ (Θ + π/2)` gives a polygon cap. For
`t ∈ {ω, π/2}`, `𝓒_Θ(h⁺)` also raises the bottom side `l(t, h_K(t) - 1)`; it is a polygon cap
translate as long as it keeps the width `1` along `u_ω` and `u_{π/2}` (Proposition 3.3.1), which the
midpoints of the edges `e_K(t)` and `e_K(t + π)` guarantee for small `ε`. -/

section HeightIncrement

open Filter Topology

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

/-- The midpoint of an edge of positive length lies strictly inside every other supporting
half-plane that is not parallel to the edge. -/
lemma mpc_midpoint_strict {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {s : ℝ}
    (hσ : 0 < sigmaAt K s) {r : ℝ} (hr : sin (r - s) ≠ 0) :
    (1 / 2 : ℝ) • (vplus K s + vminus K s) ∈ K ∧
      dot ((1 / 2 : ℝ) • (vplus K s + vminus K s)) (uvec s) = supp K s ∧
      dot ((1 / 2 : ℝ) • (vplus K s + vminus K s)) (uvec r) < supp K r := by
  have hp := vplus_mem_edge hK s
  have hm := vminus_mem_edge hK s
  have hmem : (1 / 2 : ℝ) • (vplus K s + vminus K s) ∈ K := by
    rw [smul_add]
    exact hK.2.2 hp.1 hm.1 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨hmem, ?_, (dot_le_supp hK.2.1 hmem r).lt_of_ne fun h => ?_⟩
  · rw [dot_smul_left, dot_add_left, dot_vplus_uvec, dot_vminus_uvec]; ring
  · -- otherwise both ends of the edge lie on `l_K(r)`, and the edge is parallel to it
    have h1 := dot_le_supp hK.2.1 hp.1 r
    have h2 := dot_le_supp hK.2.1 hm.1 r
    rw [dot_smul_left, dot_add_left] at h
    have h3 : dot (vplus K s - vminus K s) (uvec r) = 0 := by
      rw [dot_sub_left]; linarith
    rw [(proposition2_1_2 hK s).2, add_sub_cancel_left, dot_smul_left, dot_vvec_uvec'] at h3
    exact (mul_ne_zero hσ.ne' hr) h3

/-- A compact set squeezed between `l(s, c - 1)` and `l(s, c)` and touching both has width one. -/
lemma mpc_width_eq_one {S : Set (ℝ × ℝ)} (hS : IsCompact S) {s c : ℝ}
    (hsub : ∀ p ∈ S, c - 1 ≤ dot p (uvec s) ∧ dot p (uvec s) ≤ c) {P Q : ℝ × ℝ}
    (hP : P ∈ S) (hPs : dot P (uvec s) = c) (hQ : Q ∈ S) (hQs : dot Q (uvec s) = c - 1) :
    width S s = 1 := by
  have h1 : supp S s = c := supp_eq_of_mem hS (fun p hp => (hsub p hp).2) hP hPs
  have h2 : supp S (s + π) = 1 - c := supp_eq_of_mem hS
    (fun p hp => by rw [dot_uvec_add_pi]; linarith [(hsub p hp).1]) hQ
    (by rw [dot_uvec_add_pi, hQs]; ring)
  rw [width, h1, h2]; ring

/-- **Lemma 3.4.8**, case `t ∈ Θ ∪ (Θ + π/2)`: raising `h_K(t)` gives a polygon cap, which
contains `K` and has the same bottom sides. -/
lemma mpc_capH_update_inner (hK : IsPolygonCap Θ K) {t : ℝ}
    (htω : t ≠ Θ.ω) (htπ : t ≠ π / 2) {ε : ℝ} (hε : 0 ≤ ε) :
    IsPolygonCap Θ (capH Θ (Function.update (supp K) t (supp K t + ε))) := by
  set h' := Function.update (supp K) t (supp K t + ε) with hh'
  have hcap := hK.1
  have hω1 : h' Θ.ω = 1 := by rw [hh', Function.update_of_ne htω.symm]; exact hcap.2.2.1
  have hπ1 : h' (π / 2) = 1 := by rw [hh', Function.update_of_ne htπ.symm]; exact hcap.2.2.2.1
  have hle : ∀ r, supp K r ≤ h' r := by
    intro r
    rw [hh', Function.update_apply]
    split_ifs with h
    · rw [h]; linarith
    · exact le_rfl
  have hKsub : K ⊆ capH Θ h' := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := (mpc_polycap_mem_iff hK p).1 hp
    rw [nef_mem_capH_iff, hω1, hπ1, sub_self]
    exact ⟨fun s hs => (h1 s hs).trans (hle s), h2, h3⟩
  have hc := mpc_isCompact_capH Θ h'
  have hne : K.Nonempty := hcap.2.1.1
  have hmem := fun p => (nef_mem_capH_iff Θ h' p).1
  -- the support values of a cap are those of `K`, by squeezing between `K` and `𝓒_Θ(h⁺)`
  refine mpc_capH_isPolygonCap (hne.mono hKsub) ?_ ?_ ?_ ?_
  · refine supp_eq_of_squeeze hKsub hne hc hcap.2.2.1 fun p hp => ?_
    have := (hmem p hp).1 Θ.ω (Or.inr (Or.inl rfl))
    rwa [hω1] at this
  · refine supp_eq_of_squeeze hKsub hne hc hcap.2.2.2.1 fun p hp => ?_
    have := (hmem p hp).1 (π / 2) (Or.inr (Or.inr rfl))
    rwa [hπ1] at this
  · refine supp_eq_of_squeeze hKsub hne hc hcap.2.2.2.2.1 fun p hp => ?_
    have := (hmem p hp).2.1
    rw [hω1] at this
    rw [dot_uvec_add_pi]
    linarith
  · refine supp_eq_of_squeeze hKsub hne hc hcap.2.2.2.2.2.1 fun p hp => ?_
    have := (hmem p hp).2.2
    rw [hπ1, dot_uvec_pi_div_two] at this
    rw [dot_uvec_three_pi_div_two]
    linarith

/-- Membership in `𝓒_Θ(h⁺)` for `h⁺ = h` raised by `ε` at `t ∈ {ω, π/2}`. -/
lemma mpc_mem_capH_update {h : ℝ → ℝ} {t ε : ℝ} {P : ℝ × ℝ}
    (ha : ∀ s ∈ Θ.diamond, s ≠ t → dot P (uvec s) ≤ h s)
    (hb : dot P (uvec t) ≤ h t + ε) (hc : h t + ε - 1 ≤ dot P (uvec t))
    (hd : ∀ s ∈ ({Θ.ω, π / 2} : Set ℝ), s ≠ t → h s - 1 ≤ dot P (uvec s)) :
    P ∈ capH Θ (Function.update h t (h t + ε)) := by
  rw [nef_mem_capH_iff]
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · by_cases hst : s = t
    · subst hst; rw [Function.update_self]; exact hb
    · rw [Function.update_of_ne hst]; exact ha s hs hst
  · by_cases hst : Θ.ω = t
    · rw [hst, Function.update_self]; exact hc
    · rw [Function.update_of_ne hst]; exact hd _ (Or.inl rfl) hst
  · by_cases hst : π / 2 = t
    · rw [hst, Function.update_self]; exact hc
    · rw [Function.update_of_ne hst]; exact hd _ (Or.inr rfl) hst

/-- `𝓒_Θ(h⁺)` lies between its bottom side and the opposite upper side, along `u_ω` and
`u_{π/2}`. -/
lemma mpc_capH_update_bounds {h : ℝ → ℝ} {t ε : ℝ} {s : ℝ}
    (hs : s ∈ ({Θ.ω, π / 2} : Set ℝ)) {p : ℝ × ℝ}
    (hp : p ∈ capH Θ (Function.update h t (h t + ε))) :
    Function.update h t (h t + ε) s - 1 ≤ dot p (uvec s) ∧
      dot p (uvec s) ≤ Function.update h t (h t + ε) s := by
  rw [nef_mem_capH_iff] at hp
  rcases hs with rfl | rfl
  · exact ⟨hp.2.1, hp.1 _ (Or.inr (Or.inl rfl))⟩
  · exact ⟨hp.2.2, hp.1 _ (Or.inr (Or.inr rfl))⟩

/-- `cos (t - s) ≥ 0` for `s, t ∈ {ω, π/2}`. -/
lemma mpc_cos_nonneg_of_bottom {s t : ℝ} (hs : s ∈ ({Θ.ω, π / 2} : Set ℝ))
    (ht : t ∈ ({Θ.ω, π / 2} : Set ℝ)) : 0 ≤ cos (t - s) := by
  have hω0 := mpc_omega_pos Θ
  have hω2 := mpc_omega_le Θ
  apply cos_nonneg_of_neg_pi_div_two_le_of_le <;>
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> linarith [pi_pos]

/-- For `t ∈ {ω, π/2}`, the bottom side `e_K(t + π)` opposite to the side `e_K(t)` has positive
length. -/
lemma mpc_sigma_opposite_pos (hK : IsPolygonCap Θ K) {t : ℝ}
    (ht : t ∈ ({Θ.ω, π / 2} : Set ℝ)) : 0 < sigmaAt K (t + π) := by
  rcases (mpc_omega_le Θ).lt_or_eq with hlt | heq
  · obtain ⟨h1, h2, h3, h4⟩ := mpc_sigma_bottom_lt hK hlt
    rcases ht with rfl | rfl
    · rw [h3]; exact h4
    · rw [show π / 2 + π = 3 * π / 2 by ring, h1]; exact h2
  · have ht' : t = π / 2 := by rcases ht with rfl | rfl; exacts [heq, rfl]
    subst ht'
    -- `σ_K(3π/2)` is the width along `u_0`, positive as `C_K⁺(ω)` lies left of `A_K⁻(0)`
    rw [show π / 2 + π = 3 * π / 2 by ring, mpc_sigma_bottom_eq hK heq,
      (mpc_cPlus_eq hK).2.2.2.2, ← (mpc_aMinus_coords hK).1]
    linarith [mpc_C_lt_A hK]

/-- For `ω < π/2` and `t ∈ {ω, π/2}`, a point of `K` on the other bottom side `l(s, 0)`, `s ≠ t`,
strictly above the side `l(t, 0)`: the vertex `A_K⁻(0)` for `t = ω`, `C_K⁺(ω)` for `t = π/2`. -/
lemma mpc_bottom_point (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) {t : ℝ}
    (ht : t ∈ ({Θ.ω, π / 2} : Set ℝ)) :
    ∃ Q ∈ K, (∀ s ∈ ({Θ.ω, π / 2} : Set ℝ), s ≠ t → dot Q (uvec s) = 0) ∧
      0 < dot Q (uvec t) := by
  obtain ⟨-, h2, -, h4⟩ := mpc_sigma_bottom_lt hK hω
  have hcos : 0 < cos Θ.ω := cos_pos_of_mem_Ioo ⟨by linarith [mpc_omega_pos Θ], hω⟩
  rcases ht with rfl | rfl
  · refine ⟨_, (mpc_aMinus_eq hK).2.1, ?_, ?_⟩
    · rintro s (rfl | rfl) hst
      · exact absurd rfl hst
      · rw [dot_uvec_pi_div_two]
    · simp only [dot, uvec, zero_mul, add_zero]
      positivity
  · obtain ⟨hC1, hC2, -⟩ := mpc_cPlus_eq hK
    refine ⟨_, hC2, ?_, ?_⟩
    · rintro s (rfl | rfl) hst
      · rw [hC1, dot_smul_left, dot_vvec_uvec', sub_self, sin_zero, mul_zero]
      · exact absurd rfl hst
    · rw [hC1, dot_smul_left, dot_vvec_uvec', sin_pi_div_two_sub]
      positivity

/-- **Lemma 3.4.8**, case `t ∈ {ω, π/2}`: raising `h_K(t)` by a small `ε > 0` gives a polygon cap
translate. -/
lemma mpc_capH_update_bottom (hK : IsPolygonCap Θ K) {t : ℝ}
    (ht : t ∈ ({Θ.ω, π / 2} : Set ℝ)) (hσ : 0 < sigmaAt K t) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀,
      IsPolygonCapTranslate Θ (capH Θ (Function.update (supp K) t (supp K t + ε))) := by
  have hcap := hK.1
  have hKb := hcap.2.1
  have hω2 := mpc_omega_le Θ
  obtain ⟨ht1, htπ⟩ := mpc_supp_bot hcap ht
  have hs1 : ∀ s ∈ ({Θ.ω, π / 2} : Set ℝ), supp K s = 1 := fun s hs => (mpc_supp_bot hcap hs).1
  have hfan : ∀ P ∈ K, ∀ s ∈ ({Θ.ω, π / 2} : Set ℝ), 0 ≤ dot P (uvec s) := by
    rintro P hP s (rfl | rfl)
    exacts [(hcap.subset_fan hP).1, (hcap.subset_fan hP).2]
  have htb := mpc_diamond_bounds (nef_pair_mem_diamond ht)
  have htπ' := mpc_diamond_lt_pi (nef_pair_mem_diamond ht)
  -- Step 1: the midpoints `m`, `m'` of the edges `e_K(t)` and `e_K(t + π)` lie strictly inside
  -- the supporting half-planes with the other normal angles of `Θ^◇`.
  set m := (1 / 2 : ℝ) • (vplus K t + vminus K t) with hm_def
  set m' := (1 / 2 : ℝ) • (vplus K (t + π) + vminus K (t + π)) with hm'_def
  have hsin1 : sin (t + π / 2 - t) ≠ 0 := by
    rw [show t + π / 2 - t = π / 2 by ring, sin_pi_div_two]; norm_num
  have hsin2 : sin (t + π / 2 - (t + π)) ≠ 0 := by
    rw [show t + π / 2 - (t + π) = -(π / 2) by ring, sin_neg, sin_pi_div_two]; norm_num
  have hσπ := mpc_sigma_opposite_pos hK ht
  obtain ⟨hmK, hmt, -⟩ := mpc_midpoint_strict hKb hσ hsin1
  obtain ⟨hm'K, hm't, -⟩ := mpc_midpoint_strict hKb hσπ hsin2
  rw [← hm_def] at hmK hmt
  rw [← hm'_def] at hm'K hm't
  rw [ht1] at hmt
  rw [htπ, dot_uvec_add_pi] at hm't
  have hm't' : dot m' (uvec t) = 0 := by linarith
  have hslack : ∀ s ∈ Θ.diamond, s ≠ t →
      dot m (uvec s) < supp K s ∧ dot m' (uvec s) < supp K s := by
    intro s hs hst
    have hsin : sin (s - t) ≠ 0 := mpc_diamond_sin_sub_ne (nef_pair_mem_diamond ht) hs (Ne.symm hst)
    refine ⟨(mpc_midpoint_strict hKb hσ hsin).2.2, (mpc_midpoint_strict hKb hσπ ?_).2.2⟩
    rw [show s - (t + π) = (s - t) - π by ring, sin_sub_pi]
    exact neg_ne_zero.2 hsin
  -- Step 2: for `ω < π/2`, a point `Q` of `K` on the other bottom side, at height `≥ c₀` above
  -- `l(t, 0)`.
  obtain ⟨c₀, hc₀, hQ⟩ : ∃ c₀ > 0, Θ.ω < π / 2 → ∃ Q ∈ K,
      (∀ s ∈ ({Θ.ω, π / 2} : Set ℝ), s ≠ t → dot Q (uvec s) = 0) ∧ c₀ ≤ dot Q (uvec t) := by
    rcases hω2.lt_or_eq with hlt | heq
    · obtain ⟨Q, hQK, hQ1, hQ2⟩ := mpc_bottom_point hK hlt ht
      exact ⟨_, hQ2, fun _ => ⟨Q, hQK, hQ1, le_rfl⟩⟩
    · exact ⟨1, one_pos, fun h => absurd heq h.ne⟩
  -- Step 3: choose `ε < c₀` so small that the slack of Step 1 survives the shift by `ε u_t`.
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), (∀ s ∈ mpcDiamond Θ, s ≠ t →
      dot m (uvec s) + ε * cos (t - s) ≤ supp K s ∧
        dot m' (uvec s) + ε * cos (t - s) ≤ supp K s) ∧ ε < 1 ∧ ε < c₀ := by
    refine Filter.Eventually.and ?_ (Filter.Eventually.and (gt_mem_nhds one_pos)
      (gt_mem_nhds hc₀))
    rw [Filter.eventually_all_finset]
    intro s hs
    by_cases hst : s = t
    · exact Filter.Eventually.of_forall fun _ h => absurd hst h
    · obtain ⟨h1, h2⟩ := hslack s (mpc_mem_mpcDiamond.1 hs) hst
      have hc : ∀ P : ℝ × ℝ, Tendsto (fun ε : ℝ => dot P (uvec s) + ε * cos (t - s)) (𝓝 0)
          (𝓝 (dot P (uvec s))) := fun P => by
        have hcont : Continuous fun ε : ℝ => dot P (uvec s) + ε * cos (t - s) := by fun_prop
        simpa using hcont.tendsto 0
      filter_upwards [(hc m).eventually (gt_mem_nhds h1), (hc m').eventually (gt_mem_nhds h2)]
        with ε e1 e2 _
      exact ⟨e1.le, e2.le⟩
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ / 2, by positivity, fun ε hε => ?_⟩
  have hεδ : dist ε 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε.1]; linarith [hε.2]
  obtain ⟨hεs, hε1, hεc⟩ := hδP hεδ
  have hε0 := hε.1
  set h' := Function.update (supp K) t (supp K t + ε) with hh'
  have hc := mpc_isCompact_capH Θ h'
  -- Step 4: `m + ε u_t` and `m' + ε u_t` lie in `𝓒_Θ(h⁺)`, on its sides with normals `±u_t`.
  have hshift : ∀ P ∈ K, (∀ s ∈ mpcDiamond Θ, s ≠ t →
      dot P (uvec s) + ε * cos (t - s) ≤ supp K s) → P + ε • uvec t ∈ capH Θ h' := by
    intro P hP hslackP
    have hPt := dot_le_supp hKb.2.1 hP t
    have hPt0 := hfan P hP t ht
    apply mpc_mem_capH_update
    · intro s hs hst
      rw [dot_add_left, dot_smul_left, dot_uvec_uvec]
      exact hslackP s (mpc_mem_mpcDiamond.2 hs) hst
    · rw [dot_add_left, dot_smul_left, dot_uvec_self]; linarith
    · rw [dot_add_left, dot_smul_left, dot_uvec_self, ht1]; linarith
    · intro s hs hst
      rw [dot_add_left, dot_smul_left, dot_uvec_uvec, hs1 s hs]
      nlinarith [hfan P hP s hs, mpc_cos_nonneg_of_bottom hs ht]
  have hT := hshift m hmK fun s hs hst => (hεs s hs hst).1
  have hB := hshift m' hm'K fun s hs hst => (hεs s hs hst).2
  have hTt : dot (m + ε • uvec t) (uvec t) = h' t := by
    rw [hh', Function.update_self, dot_add_left, dot_smul_left ε, dot_uvec_self, hmt, ht1]; ring
  have hBt : dot (m' + ε • uvec t) (uvec t) = h' t - 1 := by
    rw [hh', Function.update_self, dot_add_left, dot_smul_left ε, dot_uvec_self, hm't', ht1]
    ring
  -- Step 5: the widths of `𝓒_Θ(h⁺)` along `u_ω` and `u_{π/2}` are one: along `u_t` by Step 4,
  -- and along the other direction `u_s` by the points `o_ω` and `Q`, which stay in `𝓒_Θ(h⁺)`.
  have hw : ∀ s ∈ ({Θ.ω, π / 2} : Set ℝ), width (capH Θ h') s = 1 := by
    intro s hs
    by_cases hst : s = t
    · subst hst
      exact mpc_width_eq_one hc (fun p hp => mpc_capH_update_bounds hs hp) hT hTt hB hBt
    have hlt : Θ.ω < π / 2 := by
      refine hω2.lt_of_ne fun h => hst ?_
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp_all
    obtain ⟨Q, hQK, hQ1, hQ2⟩ := hQ hlt
    have ho := hK.1.oPt_mem hlt
    have hos : ∀ r ∈ ({Θ.ω, π / 2} : Set ℝ), dot (oPt Θ.ω) (uvec r) = 1 := by
      rintro r (rfl | rfl)
      · exact oPt_dot_uvec (Ioc_subset_Icc_self Θ.hω)
      · rw [dot_uvec_pi_div_two]; rfl
    have hOin : oPt Θ.ω ∈ capH Θ h' := by
      apply mpc_mem_capH_update
      · intro r _ _; exact dot_le_supp hKb.2.1 ho r
      · linarith [dot_le_supp hKb.2.1 ho t]
      · rw [hos t ht, ht1]; linarith
      · intro r hr _; rw [hos r hr, hs1 r hr]; norm_num
    have hQin : Q ∈ capH Θ h' := by
      apply mpc_mem_capH_update
      · intro r _ _; exact dot_le_supp hKb.2.1 hQK r
      · linarith [dot_le_supp hKb.2.1 hQK t]
      · rw [ht1]; linarith
      · intro r hr hrt; rw [hQ1 r hr hrt, hs1 r hr]; norm_num
    refine mpc_width_eq_one hc (c := h' s) (fun p hp => mpc_capH_update_bounds hs hp) hOin ?_
      hQin ?_
    · rw [hh', Function.update_of_ne hst, hs1 s hs, hos s hs]
    · rw [hh', Function.update_of_ne hst, hs1 s hs, hQ1 s hs hst]; ring
  -- Step 6: Proposition 3.3.1.
  exact proposition3_3_1.2
    ⟨⟨⟨_, hT⟩, hc, nef_isHalfPlaneInter_convex (mpc_capH_halfPlaneInter Θ h')⟩,
      hw _ (Or.inl rfl), hw _ (Or.inr rfl), mpc_capH_halfPlaneInter Θ h'⟩

end HeightIncrement

/-- **Lemma 3.4.8** (`lem:height-positive-increment`). If `σ_K(t) > 0`, raising `h_K(t)` by a small
`ε > 0` gives a polygon cap translate `𝓒_Θ(h⁺)`. -/
theorem lemma3_4_8 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) {t : ℝ}
    (ht : t ∈ Θ.diamond) (hσ : 0 < sigmaAt K t) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀,
      IsPolygonCapTranslate Θ (capH Θ (Function.update (supp K) t (supp K t + ε))) := by
  -- the hypothesis `t ∈ Θ^◇` of the paper is not needed
  have _ := ht
  by_cases hb : t ∈ ({Θ.ω, π / 2} : Set ℝ)
  · exact mpc_capH_update_bottom hK hb hσ
  · have htω : t ≠ Θ.ω := fun h => hb (Or.inl h)
    have htπ : t ≠ π / 2 := fun h => hb (Or.inr h)
    exact ⟨1, one_pos, fun ε hε => ⟨_, 0, mpc_capH_update_inner hK htω htπ hε.1.le, by simp⟩⟩

/-! ## Maximum polygon caps are balanced and contain their niches (Theorems 3.4.9, 3.4.10) -/

/-- **Theorem 3.4.9** (`thm:balanced-polygon-sofa`). Every maximum polygon cap is balanced. -/
theorem theorem3_4_9 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap Θ K) :
    IsBalanced Θ K := by
  by_contra hnb
  obtain ⟨t, ht, hlt⟩ := lemma3_4_6 hK.1 hnb
  have hτ : 0 ≤ tau Θ K t := tsum_nonneg (fun c => ENNReal.toReal_nonneg)
  have hσ : 0 < sigmaAt K t := lt_of_le_of_lt hτ hlt
  obtain ⟨ε₀, hε₀, hcap⟩ := lemma3_4_8 hK.1 ht hσ
  obtain ⟨ε₁, hε₁, C, hC⟩ := lemma3_4_7 hK.1 ht
  set d := sigmaAt K t - tau Θ K t with hd_def
  have hd : 0 < d := sub_pos.2 hlt
  set ε := min (min ε₀ ε₁) (d / (2 * (|C| + 1))) with hε_def
  have hC1 : 0 < |C| + 1 := by positivity
  have hε : 0 < ε := lt_min (lt_min hε₀ hε₁) (by positivity)
  have hεle0 : ε ≤ ε₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hεle1 : ε ≤ ε₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hεd : ε ≤ d / (2 * (|C| + 1)) := min_le_right _ _
  have hCε : C * ε ^ 2 < d * ε := by
    have h1 : ε * (2 * (|C| + 1)) ≤ d := by rwa [le_div_iff₀ (by positivity)] at hεd
    have h2 : C ≤ |C| := le_abs_self C
    nlinarith [mul_pos hε hε]
  have h1 := abs_le.1 (hC ε ⟨hε, hεle1⟩)
  have h2 : areaH Θ (supp K) < areaH Θ (Function.update (supp K) t (supp K t + ε)) := by
    nlinarith [h1.1]
  have htr := hcap ε ⟨hε, hεle0⟩
  have h3 := proposition3_3_7 htr
  obtain ⟨K₀, v, hK₀, hK₀eq⟩ := htr
  have h4 : areaT Θ (capH Θ (Function.update (supp K) t (supp K t + ε))) = polyArea Θ K₀ := by
    rw [hK₀eq]; exact (theorem3_3_6 hK₀ v).2
  have h5 : areaH Θ (supp K) = polyArea Θ K := (proposition3_3_5 hK.1).2
  have h6 := hK.2.2 K₀ hK₀
  linarith

/-! ### The proof of Theorem 3.4.10 -/

/-- `τ_K(t)` from the vertices `p_0, …, p_n` of `𝐩_K` that Theorem 3.4.4 gives, with
`p_i - p_{i+1} = ℓ_i v_{s_i}`: the total length `∑_{s_i = t} ℓ_i` of the edges with normal angle
`t` (Definition 3.4.4), as the walk in the proof of Theorem 3.4.10 uses it. The edge
`[p_i, p_{i+1}]` lies on the line `l(s_i, c_i)`, `c_i = p_{i+1} · u_{s_i}`, and meets every other
line `l(t, c)` in at most one point. -/
private lemma mpc_tau_eq_edges {Θ : AngleSet} {K : Set (ℝ × ℝ)} {n : ℕ}
    {p : Fin (n + 1) → ℝ × ℝ} {sp ℓ : Fin n → ℝ} (hmono : StrictMono fun i => (p i).1)
    (hunion : polyline Θ K = ⋃ i : Fin n, segment ℝ (p i.castSucc) (p i.succ))
    (hsp : ∀ i, sp i ∈ Θ.diamond) (hedge : ∀ i, p i.castSucc - p i.succ = ℓ i • vvec (sp i))
    {t : ℝ} (ht : t ∈ Θ.diamond) :
    tau Θ K t = ∑ i ∈ Finset.univ.filter (fun i => sp i = t), ℓ i := by
  classical
  have hst := mpc_sin_pos_of_diamond ht
  obtain ⟨c, hc⟩ : ∃ c : Fin n → ℝ, ∀ i, c i = dot (p i.succ) (uvec (sp i)) := ⟨_, fun _ => rfl⟩
  -- the edge `[p_i, p_{i+1}]` is the graph of the line `l(s_i, c_i)` over `[x_i, x_{i+1}]`, and
  -- `x_{i+1} - x_i = ℓ_i sin s_i`
  have hon : ∀ (i : Fin n) (q : ℝ × ℝ), dot q (uvec (sp i)) = c i →
      q = (q.1, mpcLineY (sp i) (c i) q.1) := by
    intro i q hq
    refine Prod.ext rfl ?_
    simp only [dot, uvec, mpcLineY] at hq ⊢
    rw [eq_div_iff (mpc_sin_pos_of_diamond (hsp i)).ne']
    linarith
  have hseg : ∀ i, segment ℝ (p i.castSucc) (p i.succ) =
      {q | (p i.castSucc).1 ≤ q.1 ∧ q.1 ≤ (p i.succ).1 ∧ q.2 = mpcLineY (sp i) (c i) q.1} := by
    intro i
    have h1 : dot (p i.castSucc) (uvec (sp i)) = c i := by
      rw [hc, ← sub_add_cancel (p i.castSucc) (p i.succ), hedge, dot_add_left, dot_smul_left,
        dot_vvec_uvec, mul_zero, zero_add]
    rw [hon i (p i.castSucc) h1, hon i (p i.succ) (hc i).symm]
    exact mpc_segment_graph _ _ _ _ (hmono (Fin.castSucc_lt_succ (i := i))).le
  have hlen : ∀ i, (p i.succ).1 - (p i.castSucc).1 = ℓ i * sin (sp i) := fun i => by
    have := congrArg Prod.fst (hedge i)
    simp only [Prod.fst_sub, Prod.smul_fst, vvec_fst, smul_eq_mul] at this
    linarith
  -- the length of `𝐩_K` on the line `l(t, c₀)`: the edges on it, up to finitely many crossings
  have hline : ∀ c₀ : ℝ, lineLength t c₀ (polyline Θ K) =
      ∑ i ∈ (Finset.univ.filter (fun i => sp i = t)).filter (fun i => c i = c₀), ℓ i := by
    intro c₀
    set A := (Finset.univ.filter (fun i => sp i = t)).filter (fun i => c i = c₀)
    set U := ⋃ i ∈ A, Icc (p i.castSucc).1 (p i.succ).1
    set F : Finset ℝ := Finset.univ.image (fun i => mpcCrossX t c₀ (sp i) (c i))
    have hA : ∀ i, i ∈ A ↔ sp i = t ∧ c i = c₀ := fun i => by
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    have hsub : {x : ℝ | (x, mpcLineY t c₀ x) ∈ polyline Θ K} ⊆ U ∪ (F : Set ℝ) := by
      intro x hx
      rw [mem_ofPred_eq, hunion, mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      rw [hseg] at hi
      obtain ⟨h1, h2, h3⟩ := hi
      dsimp only at h1 h2 h3
      by_cases hit : sp i = t
      · rw [hit] at h3
        exact Or.inl (mem_iUnion₂.2 ⟨i, (hA i).2 ⟨hit, (mpc_lineY_inj hst.ne' h3).symm⟩, h1, h2⟩)
      · right
        have := mpc_lineY_eq_imp hst.ne' (mpc_sin_pos_of_diamond (hsp i)).ne'
          (mpc_diamond_sin_sub_ne ht (hsp i) (Ne.symm hit)) h3
        exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_univ _, this.symm⟩)
    have hUS : U ⊆ {x : ℝ | (x, mpcLineY t c₀ x) ∈ polyline Θ K} := by
      intro x hx
      obtain ⟨i, hi, hx'⟩ := mem_iUnion₂.1 hx
      obtain ⟨hi1, hi2⟩ := (hA i).1 hi
      rw [mem_ofPred_eq, hunion, mem_iUnion]
      refine ⟨i, ?_⟩
      rw [hseg]
      exact ⟨hx'.1, hx'.2, by rw [hi1, hi2]⟩
    rw [mpc_lineLength_eq hst, mpc_volume_eq_of_finite_diff F.finite_toSet finite_empty hsub
      (fun x hx => Or.inl (hUS hx)), mpc_measure_union_Icc hmono,
      ENNReal.toReal_sum (fun i _ => ENNReal.ofReal_ne_top), Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ENNReal.toReal_ofReal (by linarith [hmono (Fin.castSucc_lt_succ (i := i))]), hlen,
      ((hA i).1 hi).1, mul_div_cancel_right₀ _ hst.ne']
  -- summing over the parallel lines `l(t, c₀)`
  rw [tau, tsum_congr hline, tsum_eq_sum (s := (Finset.univ.filter (fun i => sp i = t)).image c)]
  · exact Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem c hi) ℓ
  · intro c₀ hc₀
    refine Finset.sum_eq_zero fun i hi => absurd ?_ hc₀
    obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
    exact hi2 ▸ Finset.mem_image_of_mem c hi1

/-- **The walk along `𝐩_K`** in the proof of Theorem 3.4.10. Let `K` be a balanced polygon cap,
`p_0, …, p_n` the vertices of `𝐩_K` as Theorem 3.4.4 gives them (`p_n = A_K⁻(0)`,
`p_i - p_{i+1} = ℓ_i v_{s_i}`), and `s ∈ Θ ∪ {ω}`. Then `p_k ∈ H_K(s)`. Following `𝐩_K` from
`A_K⁻(0)` back to `p_k` gives `p_k - A_K⁻(0) = ∑_t c_t v_t` with `c_t ∈ [0, τ_K(t)]` (the paper
writes `A_K⁻(0) - p_k`, a typo); `∑_t c_t (v_t · u_s)` is largest for `c_t = τ_K(t)`, `t < s`, and
`c_t = 0` otherwise, and then, as `τ_K = σ_K`, the sum is the walk from `A_K⁻(0)` to `v_K⁺(s)` along
the upper boundary of `K` (`mpc_walk`). -/
private lemma mpc_walk_vertex_dot_le {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K)
    (hbal : IsBalanced Θ K) {n : ℕ} {p : Fin (n + 1) → ℝ × ℝ} {sp ℓ : Fin n → ℝ}
    (hlast : p (Fin.last n) = aMinus K 0) (hsp : ∀ i, sp i ∈ Θ.diamond) (hℓpos : ∀ i, 0 < ℓ i)
    (hedge : ∀ i, p i.castSucc - p i.succ = ℓ i • vvec (sp i))
    (hτ : ∀ t ∈ Θ.diamond, tau Θ K t = ∑ i ∈ Finset.univ.filter (fun i => sp i = t), ℓ i)
    (k : Fin (n + 1)) {s : ℝ} (hs : s ∈ (Θ.angles : Set ℝ) ∪ {Θ.ω}) :
    dot (p k) (uvec s) ≤ supp K s := by
  have hs' : s ∈ Θ.diamond := by
    rcases hs with h | h
    exacts [Or.inl (Or.inl h), Or.inr (Or.inl h)]
  have hsd := mpc_mem_mpcDiamond.2 hs'
  have hsb := mpc_diamond_bounds hs'
  have hsπ := mpc_diamond_lt_pi hs'
  set F := Finset.univ.filter (fun i : Fin n => k ≤ i.castSucc)
  set f : Fin n → ℝ := fun i => ℓ i * sin (s - sp i) with hf
  -- Step 1: `p_k · u_s = A_K⁻(0) · u_s + ∑_{i ≥ k} ℓ_i sin (s - s_i)`.
  have hdot : dot (p k) (uvec s) = dot (aMinus K 0) (uvec s) + ∑ i ∈ F, f i := by
    have hPk : p k = aMinus K 0 + ∑ i ∈ F, ℓ i • vvec (sp i) := by
      have := mpc_sum_telescope_from p k
      rw [Finset.sum_congr rfl (fun i _ => hedge i), hlast] at this
      rw [this]; abel
    rw [hPk, dot_add_left, mpc_dot_sum]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by rw [dot_smul_left, dot_vvec_uvec'])
  -- Step 2: dropping the terms with `s_i ≥ s` (which are `≤ 0`) and adding the missing terms with
  -- `s_i < s` (which are `≥ 0`) can only increase the sum.
  have hbound : ∑ i ∈ F, f i ≤ ∑ i ∈ Finset.univ.filter (fun i => sp i < s), f i := by
    rw [← Finset.sum_filter_add_sum_filter_not F (fun i => sp i < s)]
    have h1 : ∑ i ∈ F.filter (fun i => ¬ sp i < s), f i ≤ 0 := by
      refine Finset.sum_nonpos fun i hi => mul_nonpos_of_nonneg_of_nonpos (hℓpos i).le ?_
      have hi' := not_lt.1 (Finset.mem_filter.1 hi).2
      exact sin_nonpos_of_nonpos_of_neg_pi_le (by linarith)
        (by linarith [mpc_diamond_bounds (hsp i), mpc_diamond_lt_pi (hsp i)])
    have h2 : ∑ i ∈ F.filter (fun i => sp i < s), f i ≤
        ∑ i ∈ Finset.univ.filter (fun i => sp i < s), f i := by
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hi).2⟩)
        fun i hi _ => mul_nonneg (hℓpos i).le ?_
      have hi' := (Finset.mem_filter.1 hi).2
      exact sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by linarith [(mpc_diamond_bounds (hsp i)).1])
    linarith
  -- Step 3: grouped by normal angle, with `τ_K(t) = ∑_{s_i = t} ℓ_i = σ_K(t)`, the bound is the
  -- walk `(v_K⁺(s) - A_K⁻(0)) · u_s` along the upper boundary.
  have hgroup : ∑ i ∈ Finset.univ.filter (fun i => sp i < s), f i =
      ∑ t ∈ (mpcDiamond Θ).filter (· < s), sigmaAt K t * sin (s - t) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := sp) (t := (mpcDiamond Θ).filter (· < s))
      (fun i hi => Finset.mem_filter.2 ⟨mpc_mem_mpcDiamond.2 (hsp i),
        (Finset.mem_filter.1 hi).2⟩)]
    refine Finset.sum_congr rfl fun t ht => ?_
    obtain ⟨htD, hts⟩ := Finset.mem_filter.1 ht
    have htd := mpc_mem_mpcDiamond.1 htD
    rw [hbal t htd, hτ t htd, Finset.sum_mul, Finset.filter_filter]
    refine Finset.sum_congr ?_ fun i hi => by simp only [hf, (Finset.mem_filter.1 hi).2]
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hts, h⟩⟩
  have hwalk : dot (vplus K s - aMinus K 0) (uvec s) =
      ∑ t ∈ (mpcDiamond Θ).filter (· < s), sigmaAt K t * sin (s - t) := by
    have hsplit : (mpcDiamond Θ).filter (· ≤ s) = insert s ((mpcDiamond Θ).filter (· < s)) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨ht, hts⟩
        exact hts.eq_or_lt.imp id fun h => ⟨ht, h⟩
      · rintro (rfl | ⟨ht, hts⟩)
        · exact ⟨hsd, le_rfl⟩
        · exact ⟨ht, hts.le⟩
    rw [mpc_walk hK hsd, mpc_dot_sum, hsplit, Finset.sum_insert (by simp)]
    simp only [dot_smul_left, dot_vvec_uvec', sub_self, sin_zero, mul_zero, zero_add]
  rw [hdot, ← dot_vplus_uvec K s,
    show dot (vplus K s) (uvec s) = dot (aMinus K 0) (uvec s) +
      dot (vplus K s - aMinus K 0) (uvec s) by rw [dot_sub_left]; ring, hwalk, ← hgroup]
  linarith

/-- The claim in the proof of Theorem 3.4.10: for a maximum polygon cap `K` and `s ∈ Θ ∪ {ω}`, the
polyline `𝐩_K` lies in `H_K(s)`. By Theorem 3.4.4, `𝐩_K` is the union of the segments between its
vertices, which lie in `H_K(s)` by the walk (`mpc_walk_vertex_dot_le`; `K` is balanced by
Theorem 3.4.9). -/
private lemma mpc_polyline_dot_le {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap Θ K)
    {q : ℝ × ℝ} (hq : q ∈ polyline Θ K) {s : ℝ} (hs : s ∈ (Θ.angles : Set ℝ) ∪ {Θ.ω}) :
    dot q (uvec s) ≤ supp K s := by
  obtain ⟨-, -, -, n, p, -, hlast, hmono, hunion, hedge⟩ := theorem3_4_4 hK.1
  choose sp hsp ℓ hℓ hedge using hedge
  have hv := fun k => mpc_walk_vertex_dot_le hK.1 (theorem3_4_9 hK) hlast hsp hℓ hedge
    (fun t ht => mpc_tau_eq_edges hmono hunion hsp hedge ht) k hs
  rw [hunion] at hq
  obtain ⟨i, hi⟩ := mem_iUnion.1 hq
  exact (convex_halfMinus s (supp K s)).segment_subset (hv _) (hv _) hi

/-- The polyline of the mirror image `K^m = M_ω(K)`, with angle set `ω - Θ` (Lemma 3.4.1), is
`𝐩_{K^m} = M_ω(𝐩_K)`: by Proposition 2.5.4, `M_ω` maps `F_ω` to itself and `𝒩_Θ(K)` to
`𝒩_{ω - Θ}(K^m)`, and exchanges the half-lines `l⃗` and `r⃗`
(`C_{K^m}⁺(ω) = M_ω(A_K⁻(0))`, `A_{K^m}⁻(0) = M_ω(C_K⁺(ω))`). -/
private lemma mpc_polyline_mirror (Θ : AngleSet) (K : Set (ℝ × ℝ)) :
    polyline Θ.mirror (mirrorCap K Θ.ω) = mirror Θ.ω '' polyline Θ K := by
  let e : ℝ × ℝ ≃ₜ ℝ × ℝ :=
    { toFun := mirror Θ.ω, invFun := mirror Θ.ω, left_inv := cn_mirror_mirror Θ.ω,
      right_inv := cn_mirror_mirror Θ.ω, continuous_toFun := by unfold mirror; fun_prop,
      continuous_invFun := by unfold mirror; fun_prop }
  have hfr : ∀ X, mirror Θ.ω '' frontier X = frontier (mirror Θ.ω '' X) :=
    fun X => e.image_frontier X
  have hfan : mirror Θ.ω '' fan Θ.ω = fan Θ.ω := by
    ext q
    rw [cn_mem_mirror_image]
    simp only [fan, halfPlus, mem_inter_iff, mem_ofPred_eq, cn_dot_mirror_uvec,
      show Θ.ω + π / 2 - Θ.ω = π / 2 by ring, show Θ.ω + π / 2 - π / 2 = Θ.ω by ring]
    exact and_comm
  have hniche : polyNiche Θ.mirror (mirrorCap K Θ.ω) = mirror Θ.ω '' polyNiche Θ K := by
    have e : ∀ (Θ' : AngleSet) L, polyNiche Θ' L = ⋃ t ∈ Θ'.angles, wedge L Θ'.ω t :=
      fun Θ' L => by simp only [polyNiche, wedge, inter_iUnion₂]
    have hw : ∀ t, wedge (mirrorCap K Θ.ω) Θ.ω t = mirror Θ.ω '' wedge K Θ.ω (Θ.ω - t) :=
      fun t => (proposition2_5_4_sets t).2.1
    rw [e, e, image_iUnion₂]
    simp only [AngleSet.mirror, Finset.set_biUnion_finset_image, hw, sub_sub_cancel]
  have hray : ∀ c v : ℝ × ℝ, mirror Θ.ω '' {q | ∃ a : ℝ, 0 < a ∧ q = c + a • v} =
      {q | ∃ a : ℝ, 0 < a ∧ q = mirror Θ.ω c + a • mirror Θ.ω v} := by
    intro c v
    have hlin : ∀ a : ℝ, mirror Θ.ω (c + a • v) = mirror Θ.ω c + a • mirror Θ.ω v := fun a => by
      ext <;> simp only [mirror, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul] <;> ring
    ext q
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, hlin a⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨_, ⟨a, ha, rfl⟩, hlin a⟩
  have hvu : mirror Θ.ω (vvec Θ.ω) = uvec 0 := by
    rw [mirror, add_comm (π / 2), cos_add_pi_div_two, sin_add_pi_div_two]
    ext
    · simp only [vvec_fst, vvec_snd, uvec_fst, cos_zero]
      linear_combination sin_sq_add_cos_sq Θ.ω
    · simp only [vvec_fst, vvec_snd, uvec_snd, sin_zero]
      ring
  have huv : mirror Θ.ω (uvec 0) = vvec Θ.ω := by rw [← hvu, cn_mirror_mirror]
  have hA : mirror Θ.ω (cPlus K Θ.ω) = aMinus (mirrorCap K Θ.ω) 0 := by
    rw [(proposition2_5_4_vertices 0).2.1, sub_zero]
  have hC : mirror Θ.ω (aMinus K 0) = cPlus (mirrorCap K Θ.ω) Θ.ω := by
    rw [(proposition2_5_4_vertices Θ.ω).2.2.1, sub_self]
  have hl : mirror Θ.ω '' rayLeft K Θ.ω = rayRight (mirrorCap K Θ.ω) := by
    rw [rayLeft, hray, hA, hvu]; rfl
  have hr : mirror Θ.ω '' rayRight K = rayLeft (mirrorCap K Θ.ω) Θ.ω := by
    rw [rayRight, hray, hC, huv]; rfl
  have hinj : Function.Injective (mirror Θ.ω) := e.injective
  rw [polyline, polyline, image_sdiff hinj, image_union, hl, hr, hfr, image_sdiff hinj, hfan,
    ← hniche, union_comm]
  rfl

/-- **Theorem 3.4.10** (`thm:balanced-polygon-sofa-connected`). Every maximum polygon cap contains
its polygon niche. -/
theorem theorem3_4_10 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap Θ K) :
    polyNiche Θ K ⊆ K := by
  have hK' := hK.1
  -- Step 1: the polyline lies in `H_K(s)` for every `s ∈ Θ^◇`. For `s ∈ Θ ∪ {ω}` this is the walk
  -- along `𝐩_K`; for `s = ω + π/2 - t`, `t ∈ (ω - Θ) ∪ {ω}`, it is the walk along the polyline
  -- `𝐩_{K^m} = M_ω(𝐩_K)` of the mirror image, a maximum polygon cap with angle set `ω - Θ`
  -- (Lemma 3.4.1), reflected back with `h_{K^m}(t) = h_K(ω + π/2 - t)` (Proposition 2.5.4).
  have hline : ∀ q ∈ polyline Θ K, ∀ s ∈ Θ.diamond, dot q (uvec s) ≤ supp K s := by
    intro q hq s hs
    have hqm : mirror Θ.ω q ∈ polyline Θ.mirror (mirrorCap K Θ.ω) := by
      rw [mpc_polyline_mirror]; exact mem_image_of_mem _ hq
    have hm := fun t ht => mpc_polyline_dot_le (lemma3_4_1 hK) hqm (s := t) ht
    rcases mpc_diamond_cases hs with h | ⟨t, ht, rfl⟩ | rfl | rfl
    · exact mpc_polyline_dot_le hK hq (Or.inl h)
    · have := hm (Θ.ω - t) (Or.inl (mpc_mem_mirror_angles.2 (by rwa [sub_sub_cancel])))
      rwa [cn_dot_mirror_uvec, proposition2_5_4_supp,
        show Θ.ω + π / 2 - (Θ.ω - t) = t + π / 2 by ring] at this
    · exact mpc_polyline_dot_le hK hq (Or.inr rfl)
    · have := hm Θ.ω (Or.inr rfl)
      rwa [cn_dot_mirror_uvec, proposition2_5_4_supp,
        show Θ.ω + π / 2 - Θ.ω = π / 2 by ring] at this
  -- Step 2: the polygon niche lies in the fan, below the polyline.
  intro p hp
  rw [mpc_polyNiche_eq hK'] at hp
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hx1, hx2⟩ := mpc_between hK' (hp1.trans hp2.le)
  rw [mpc_polycap_mem_iff hK', mpc_fan_eq hK']
  refine ⟨fun s hs => ?_, hp1⟩
  have e := hline (p.1, mpcG Θ K p.1) (by rw [mpc_polyline_eq hK']; exact ⟨hx1, hx2, rfl⟩) s hs
  have hs' := mpc_sin_pos_of_diamond hs
  have hG : p.2 ≤ mpcG Θ K p.1 := hp2.le.trans (le_max_right _ _)
  simp only [dot, uvec] at e ⊢
  nlinarith

/-! ## Remark: the original statement of Theorem 3.4.4

The statement of Theorem 3.4.4 originally read `∃ ℓ > 0, p i.castSucc - p i.succ = ℓ • vvec s`,
which Lean elaborated with `ℓ : ℕ`. That version is false; we record the counterexample. -/

/-- The angle set `{π/4}` with rotation angle `π/2`. -/
noncomputable def mpcΘ₀ : AngleSet where
  ω := π / 2
  angles := {π / 4}
  hω := ⟨by positivity, le_rfl⟩
  nonempty := ⟨π / 4, Finset.mem_singleton_self _⟩
  subset := by
    intro t ht
    rw [Finset.mem_singleton.1 ht]
    constructor <;> linarith [pi_pos]

/-- **The original statement of Theorem 3.4.4 is false**: Lean elaborated `∃ ℓ > 0` with `ℓ : ℕ`.
For the polygon cap `𝓒_Θ(1)` with `Θ = {π/4}` and `ω = π/2`, the polyline is the horizontal segment
from `(-√2, 0)` to `(√2, 0)`, of irrational length `2√2`, so it is not a union of segments of
natural lengths. -/
theorem mpc_theorem3_4_4_nat_false : ¬ ∀ (Θ : AngleSet) (K : Set (ℝ × ℝ)), IsPolygonCap Θ K →
    frontier (fan Θ.ω \ polyNiche Θ K) = rayLeft K Θ.ω ∪ polyline Θ K ∪ rayRight K ∧
      Disjoint (rayLeft K Θ.ω) (polyline Θ K ∪ rayRight K) ∧ Disjoint (polyline Θ K) (rayRight K) ∧
      ∃ (n : ℕ) (p : Fin (n + 1) → ℝ × ℝ), p 0 = cPlus K Θ.ω ∧ p (Fin.last n) = aMinus K 0 ∧
        StrictMono (fun i => (p i).1) ∧
        polyline Θ K = ⋃ i : Fin n, segment ℝ (p i.castSucc) (p i.succ) ∧
        ∀ i : Fin n, ∃ s ∈ Θ.diamond, ∃ ℓ > 0, p i.castSucc - p i.succ = ℓ • vvec s := by
  intro H
  obtain ⟨hK, -, hN, -⟩ := mpc_K1 mpcΘ₀
  set K := capH mpcΘ₀ (fun _ => 1) with hKdef
  have hω : mpcΘ₀.ω = π / 2 := rfl
  obtain ⟨-, -, -, n, p, hp0, hpl, -, hpoly, hedge⟩ := H mpcΘ₀ K hK
  -- Step 1: the polyline lies on the line `y = 0`, since the niche is empty.
  have hy : ∀ q ∈ polyline mpcΘ₀ K, q.2 = 0 := by
    intro q hq
    rw [mpc_polyline_eq hK] at hq
    have hlow : mpcLow mpcΘ₀ K q.1 = 0 := by
      rw [mpcLow, hω, mpc_mpcL_pi_div_two hK, max_self]
    have htop : mpcTop mpcΘ₀ K q.1 ≤ 0 := by
      by_contra h
      have : (q.1, (0 : ℝ)) ∈ polyNiche mpcΘ₀ K := by
        rw [mpc_polyNiche_eq hK]
        exact ⟨hlow.le, not_le.1 h⟩
      simp [hN] at this
    rw [hq.2.2, mpcG, hlow, max_eq_left htop]
  -- Step 2: every edge is horizontal, of natural length.
  have hstep : ∀ j : Fin n, ∃ ℓ : ℕ, (p j.succ).1 - (p j.castSucc).1 = ℓ := by
    intro j
    obtain ⟨s, hs, ℓ, hℓ, he⟩ := hedge j
    have h1 := hy (p j.castSucc) (by rw [hpoly]; exact mem_iUnion.2 ⟨j, left_mem_segment ℝ _ _⟩)
    have h2 := hy (p j.succ) (by rw [hpoly]; exact mem_iUnion.2 ⟨j, right_mem_segment ℝ _ _⟩)
    have e1 := congrArg Prod.fst he
    have e2 := congrArg Prod.snd he
    simp only [Prod.snd_sub, Prod.fst_sub, h1, h2, sub_zero, Prod.smul_snd, Prod.smul_fst,
      vvec_snd, vvec_fst] at e1 e2
    rw [nsmul_eq_mul] at e1 e2
    have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    -- `ℓ cos s = 0` forces `s = π/2`
    have hcos : cos s = 0 := (mul_eq_zero.1 e2.symm).resolve_left hℓ'.ne'
    have hsin : sin s = 1 := by
      have := sin_sq_add_cos_sq s
      rw [hcos] at this
      nlinarith [mpc_sin_pos_of_diamond hs]
    exact ⟨ℓ, by rw [hsin] at e1; linarith⟩
  choose ℓ hℓ using hstep
  -- Step 3: the polyline runs from `C_K⁺(ω) = (-√2, 0)` to `A_K⁻(0) = (√2, 0)`.
  have hmemK : ∀ q : ℝ × ℝ, q ∈ K ↔ (∀ s ∈ mpcΘ₀.diamond, dot q (uvec s) ≤ 1) ∧
      0 ≤ dot q (uvec mpcΘ₀.ω) ∧ 0 ≤ dot q (uvec (π / 2)) := by
    intro q; rw [hKdef, nef_mem_capH_iff]; simp
  have hdiam : ∀ s ∈ mpcΘ₀.diamond, s = π / 4 ∨ s = π / 4 + π / 2 ∨ s = π / 2 := by
    rintro s ((h | ⟨u, hu, rfl⟩) | (h | h))
    · exact Or.inl (Finset.mem_singleton.1 h)
    · exact Or.inr (Or.inl (by rw [Finset.mem_singleton.1 hu]))
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inr h)
  have hsq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2 : 0 < √2 := by positivity
  have hpt : ∀ x : ℝ, x * x = 2 → (x, (0 : ℝ)) ∈ K := by
    intro x hx
    rw [hmemK]
    refine ⟨fun s hs => ?_, by rw [hω]; simp [dot, uvec], by simp [dot, uvec]⟩
    rcases hdiam s hs with rfl | rfl | rfl
    · simp only [dot, uvec, cos_pi_div_four, sin_pi_div_four]
      nlinarith [sq_nonneg (x - √2), sq_nonneg (x + √2)]
    · simp only [dot, uvec, cos_add_pi_div_two, sin_add_pi_div_two, sin_pi_div_four,
        cos_pi_div_four]
      nlinarith [sq_nonneg (x - √2), sq_nonneg (x + √2)]
    · simp [dot, uvec]
  -- on `K`, `|x| ≤ √2`, from the sides with normal angles `π/4`, `3π/4` and `y ≥ 0`
  have hx : ∀ q ∈ K, q.1 ≤ √2 ∧ -q.1 ≤ √2 := by
    intro q hq
    rw [hmemK] at hq
    have h1 := hq.1 (π / 4) (Or.inl (Or.inl (Finset.mem_singleton_self _)))
    have h2 := hq.1 (π / 4 + π / 2) (Or.inl (Or.inr ⟨π / 4, Finset.mem_singleton_self _, rfl⟩))
    have h3 := hq.2.2
    simp only [dot, uvec, cos_pi_div_four, sin_pi_div_four, cos_add_pi_div_two,
      sin_add_pi_div_two, cos_pi_div_two, sin_pi_div_two] at h1 h2 h3
    constructor <;> nlinarith
  have hKc := hK.1.2.1.2.1
  have hA : supp K 0 = √2 := supp_eq_of_mem hKc
    (fun q hq => by rw [dot_uvec_zero]; exact (hx q hq).1) (hpt √2 hsq) (by simp [dot, uvec])
  have hC : supp K π = √2 := supp_eq_of_mem hKc
    (fun q hq => by rw [dot_uvec_pi]; exact (hx q hq).2) (hpt (-√2) (by nlinarith))
    (by simp [dot, uvec])
  -- Step 4: `2√2` would be a natural number.
  have hsum : (p (Fin.last n)).1 - (p 0).1 = ∑ j, (ℓ j : ℝ) := by
    rw [← mpc_sum_telescope (fun i => (p i).1)]
    exact Finset.sum_congr rfl fun j _ => hℓ j
  rw [hpl, hp0, (mpc_aMinus_coords hK).1, hA, ← neg_neg (cPlus K mpcΘ₀.ω).1,
    ← (mpc_cPlus_eq hK).2.2.2.2, hC] at hsum
  set N := ∑ j, ℓ j
  have h8 : (N : ℝ) ^ 2 = 8 := by
    rw [show (N : ℝ) = 2 * √2 by simp only [N]; push_cast; linarith, mul_pow,
      Real.sq_sqrt (by norm_num)]
    norm_num
  have h8' : N ^ 2 = 8 := by exact_mod_cast h8
  rcases (show N ≤ 2 ∨ 3 ≤ N by omega) with h | h
  · have := Nat.pow_le_pow_left h 2; omega
  · have := Nat.pow_le_pow_left h 2; omega

end MovingSofaOptimality
