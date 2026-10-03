module

public import MovingSofaOptimality.Balanced.NefPolygon

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

namespace MovingSofaOptimality

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

/-! ### Auxiliary lemmas for §3.2 -/

lemma nef_isHalfPlaneInter_halfMinus {A : Set ℝ} {t : ℝ} (ht : t ∈ A) (c : ℝ) :
    IsHalfPlaneInter (halfMinus t c) A :=
  ⟨Unit, fun _ => t, fun _ => c, fun _ => ht, (iInter_const _).symm⟩

lemma nef_isHalfPlaneInter_inter {A : Set ℝ} {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsHalfPlaneInter K₁ A)
    (h₂ : IsHalfPlaneInter K₂ A) : IsHalfPlaneInter (K₁ ∩ K₂) A := by
  obtain ⟨ι₁, t₁, c₁, ht₁, rfl⟩ := h₁
  obtain ⟨ι₂, t₂, c₂, ht₂, rfl⟩ := h₂
  refine ⟨ι₁ ⊕ ι₂, Sum.elim t₁ t₂, Sum.elim c₁ c₂, ?_, ?_⟩
  · rintro (i | i)
    · exact ht₁ i
    · exact ht₂ i
  · rw [Set.iInter_sum]; rfl

lemma nef_isHalfPlaneInter_iInter {A : Set ℝ} {κ : Type} (K : κ → Set (ℝ × ℝ))
    (h : ∀ k, IsHalfPlaneInter (K k) A) : IsHalfPlaneInter (⋂ k, K k) A := by
  choose ι t c ht hK using h
  refine ⟨Σ k, ι k, fun x => t x.1 x.2, fun x => c x.1 x.2, fun x => ht x.1 x.2, ?_⟩
  rw [Set.iInter_sigma]
  exact Set.iInter_congr hK

lemma nef_isHalfPlaneInter_mono {A B : Set ℝ} (hAB : A ⊆ B) {K : Set (ℝ × ℝ)}
    (h : IsHalfPlaneInter K A) : IsHalfPlaneInter K B := by
  obtain ⟨ι, t, c, ht, rfl⟩ := h
  exact ⟨ι, t, c, fun i => hAB (ht i), rfl⟩

lemma nef_dot_uvec_pi_div_two (p : ℝ × ℝ) : dot p (uvec (π / 2)) = p.2 := by
  simp [dot, uvec]

lemma nef_dot_uvec_add_pi (p : ℝ × ℝ) (t : ℝ) : dot p (uvec (t + π)) = -dot p (uvec t) := by
  rw [uvec_add_pi, dot_neg_right]

lemma nef_three_pi_div_two : 3 * π / 2 = π / 2 + π := by ring

lemma nef_dot_uvec_three_pi_div_two (p : ℝ × ℝ) : dot p (uvec (3 * π / 2)) = -p.2 := by
  rw [nef_three_pi_div_two, nef_dot_uvec_add_pi, nef_dot_uvec_pi_div_two]

lemma nef_mem_para (ω : ℝ) (p : ℝ × ℝ) :
    p ∈ para ω ↔ (0 ≤ p.2 ∧ p.2 ≤ 1) ∧ (0 ≤ dot p (uvec ω) ∧ dot p (uvec ω) ≤ 1) := by
  constructor
  · rintro ⟨h1, q, hq, rfl⟩
    refine ⟨h1, ?_⟩
    have : dot (rot ω q) (uvec ω) = q.1 := by
      have := dot_rot_uvec ω 0 q
      simp only [zero_add] at this
      rw [this]; simp [dot, uvec]
    rw [this]; exact hq
  · rintro ⟨h1, h2⟩
    refine ⟨h1, rot (-ω) p, ?_, rot_rot_neg ω p⟩
    have : (rot (-ω) p).1 = dot p (uvec ω) := by
      simp [rot, dot, uvec, cos_neg, sin_neg]; ring
    show 0 ≤ (rot (-ω) p).1 ∧ (rot (-ω) p).1 ≤ 1
    rw [this]; exact h2

/-- `P_ω = H₋(π/2, 1) ∩ H₋(3π/2, 0) ∩ H₋(ω, 1) ∩ H₋(ω + π, 0)`. -/
lemma nef_para_eq (ω : ℝ) : para ω =
    halfMinus (π / 2) 1 ∩ halfMinus (3 * π / 2) 0 ∩ halfMinus ω 1 ∩ halfMinus (ω + π) 0 := by
  ext p
  simp only [nef_mem_para, mem_inter_iff, halfMinus, mem_ofPred_eq, nef_dot_uvec_pi_div_two,
    nef_dot_uvec_three_pi_div_two, nef_dot_uvec_add_pi]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨⟨h2, by linarith⟩, h4⟩, by linarith⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨⟨by linarith, h1⟩, by linarith, h3⟩

lemma nef_supp_le {S : Set (ℝ × ℝ)} (hS : S.Nonempty) {t c : ℝ}
    (h : ∀ p ∈ S, dot p (uvec t) ≤ c) : supp S t ≤ c :=
  csSup_le (hS.image _) (by rintro _ ⟨p, hp, rfl⟩; exact h p hp)

lemma nef_continuous_dot (u : ℝ × ℝ) : Continuous fun p : ℝ × ℝ => dot p u := by
  unfold dot; fun_prop

lemma nef_isClosed_halfMinus (t c : ℝ) : IsClosed (halfMinus t c) :=
  isClosed_le (nef_continuous_dot _) continuous_const

lemma nef_convex_halfMinus (t c : ℝ) : Convex ℝ (halfMinus t c) := by
  intro p hp q hq a b ha hb hab
  simp only [halfMinus, mem_ofPred_eq] at *
  rw [dot_add_left, dot_smul_left, dot_smul_left]
  calc a * dot p (uvec t) + b * dot q (uvec t) ≤ a * c + b * c := by gcongr
    _ = c := by rw [← add_mul, hab, one_mul]

lemma nef_isHalfPlaneInter_isClosed {K : Set (ℝ × ℝ)} {A : Set ℝ} (h : IsHalfPlaneInter K A) :
    IsClosed K := by
  obtain ⟨ι, t, c, -, rfl⟩ := h
  exact isClosed_iInter fun i => nef_isClosed_halfMinus _ _

lemma nef_isHalfPlaneInter_convex {K : Set (ℝ × ℝ)} {A : Set ℝ} (h : IsHalfPlaneInter K A) :
    Convex ℝ K := by
  obtain ⟨ι, t, c, -, rfl⟩ := h
  exact convex_iInter fun i => nef_convex_halfMinus _ _

/-- A convex body which is an intersection of closed half-planes with normal angles in `A` is the
intersection of its supporting half-planes with normal angles in `A`. -/
lemma nef_eq_setOf_supp {K : Set (ℝ × ℝ)} {A : Set ℝ} (hK : IsConvexBody K)
    (hA : IsHalfPlaneInter K A) : K = {p | ∀ s ∈ A, dot p (uvec s) ≤ supp K s} := by
  apply Subset.antisymm
  · intro p hp s _
    exact dot_le_supp hK.2.1 hp s
  · intro p hp
    obtain ⟨ι, t, c, ht, hKeq⟩ := hA
    have hle : ∀ i, supp K (t i) ≤ c i := fun i =>
      nef_supp_le hK.1 (fun q hq => by rw [hKeq] at hq; exact mem_iInter.1 hq i)
    rw [hKeq]
    exact mem_iInter.2 fun i => (hp (t i) (ht i)).trans (hle i)

lemma nef_mem_capAngles {Θ : AngleSet} {s : ℝ} :
    s ∈ Θ.capAngles ↔ s ∈ Θ.angles ∨ (∃ t ∈ Θ.angles, s = t + π / 2) ∨ s = Θ.ω ∨ s = π / 2 ∨
      s = Θ.ω + π ∨ s = 3 * π / 2 := by
  simp only [AngleSet.capAngles, AngleSet.diamond, mem_union, mem_insert_iff,
    mem_singleton_iff, Finset.mem_coe, mem_image]
  constructor
  · rintro (((h | ⟨t, ht, rfl⟩) | h | h) | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨t, ht, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rintro (h | ⟨t, ht, rfl⟩ | h | h | h | h)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr ⟨t, ht, rfl⟩))
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

lemma nef_angle_mem {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.angles) :
    0 < t ∧ t < Θ.ω ∧ Θ.ω ≤ π / 2 := ⟨(Θ.subset t ht).1, (Θ.subset t ht).2, Θ.hω.2⟩

lemma nef_mem_polyCap_iff {Θ : AngleSet} {K : Set (ℝ × ℝ)} (p : ℝ × ℝ) :
    p ∈ polyCap Θ K ↔ p ∈ para Θ.ω ∧ ∀ t ∈ Θ.angles,
      dot p (uvec t) ≤ supp K t ∧ dot p (uvec (t + π / 2)) ≤ supp K (t + π / 2) := by
  simp only [polyCap, mem_inter_iff, mem_iInter, proposition2_2_2_qPlus, suppHalf, halfMinus,
    mem_ofPred_eq]

lemma nef_mem_polyCap_dot_le {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsCap K Θ.ω) {p : ℝ × ℝ}
    (hp : p ∈ polyCap Θ K) {s : ℝ} (hs : s ∈ Θ.capAngles) : dot p (uvec s) ≤ supp K s := by
  obtain ⟨hω, hKcb, h1, h2, h3, h4, -⟩ := hK
  rw [nef_mem_polyCap_iff, nef_mem_para] at hp
  obtain ⟨⟨⟨hy0, hy1⟩, hu0, hu1⟩, hΘ⟩ := hp
  rcases nef_mem_capAngles.1 hs with h | ⟨t, ht, rfl⟩ | rfl | rfl | rfl | rfl
  · exact (hΘ s h).1
  · exact (hΘ t ht).2
  · rw [h1]; exact hu1
  · rw [h2, nef_dot_uvec_pi_div_two]; exact hy1
  · rw [h3, nef_dot_uvec_add_pi]; linarith
  · rw [h4, nef_dot_uvec_three_pi_div_two]; linarith

lemma nef_subset_polyCap {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsCap K Θ.ω) :
    K ⊆ polyCap Θ K := by
  obtain ⟨hω, hKcb, h1, h2, h3, h4, -⟩ := hK
  intro p hp
  have hd := fun s => dot_le_supp hKcb.2.1 hp s
  rw [nef_mem_polyCap_iff, nef_mem_para]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, fun t _ => ⟨hd t, hd _⟩⟩
  · have := hd (3 * π / 2); rw [h4, nef_dot_uvec_three_pi_div_two] at this; linarith
  · have := hd (π / 2); rwa [h2, nef_dot_uvec_pi_div_two] at this
  · have := hd (Θ.ω + π); rw [h3, nef_dot_uvec_add_pi] at this; linarith
  · have := hd Θ.ω; rwa [h1] at this

lemma nef_polyCap_isHalfPlaneInter (Θ : AngleSet) (K : Set (ℝ × ℝ)) :
    IsHalfPlaneInter (polyCap Θ K) Θ.capAngles := by
  have hmem : ∀ s, (s ∈ Θ.angles ∨ (∃ t ∈ Θ.angles, s = t + π / 2) ∨ s = Θ.ω ∨ s = π / 2 ∨
      s = Θ.ω + π ∨ s = 3 * π / 2) → s ∈ Θ.capAngles := fun s h => nef_mem_capAngles.2 h
  unfold polyCap
  rw [nef_para_eq]
  refine nef_isHalfPlaneInter_inter (nef_isHalfPlaneInter_inter (nef_isHalfPlaneInter_inter
    (nef_isHalfPlaneInter_inter ?_ ?_) ?_) ?_) ?_
  · exact nef_isHalfPlaneInter_halfMinus (hmem _ (by simp)) _
  · exact nef_isHalfPlaneInter_halfMinus (hmem _ (by simp)) _
  · exact nef_isHalfPlaneInter_halfMinus (hmem _ (by simp)) _
  · exact nef_isHalfPlaneInter_halfMinus (hmem _ (by simp)) _
  · rw [← Finset.set_biInter_coe, Set.biInter_eq_iInter]
    refine nef_isHalfPlaneInter_iInter _ fun t => ?_
    rw [proposition2_2_2_qPlus]
    exact nef_isHalfPlaneInter_inter (nef_isHalfPlaneInter_halfMinus (hmem _ (Or.inl t.2)) _)
      (nef_isHalfPlaneInter_halfMinus (hmem _ (Or.inr (Or.inl ⟨t, t.2, rfl⟩))) _)

lemma nef_polyCap_isBounded (Θ : AngleSet) (K : Set (ℝ × ℝ)) :
    Bornology.IsBounded (polyCap Θ K) := by
  obtain ⟨t, ht⟩ := Θ.nonempty
  obtain ⟨ht0, htω, hω⟩ := nef_angle_mem ht
  have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 (by linarith)
  refine (Metric.isBounded_Icc ((-supp K (t + π / 2) / sin t, (0 : ℝ)))
    (supp K t / cos t, (1 : ℝ))).subset ?_
  intro p hp
  rw [nef_mem_polyCap_iff, nef_mem_para] at hp
  obtain ⟨⟨⟨hy0, hy1⟩, -, -⟩, hΘ⟩ := hp
  obtain ⟨hA, hB⟩ := hΘ t ht
  rw [uvec_add_pi_div_two] at hB
  simp only [dot, uvec, vvec] at hA hB
  refine ⟨⟨?_, hy0⟩, ⟨?_, hy1⟩⟩
  · show -supp K (t + π / 2) / sin t ≤ p.1
    rw [div_le_iff₀ hs]
    nlinarith
  · show p.1 ≤ supp K t / cos t
    rw [le_div_iff₀ hc]
    nlinarith

lemma nef_polyCap_isConvexBody {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsCap K Θ.ω) :
    IsConvexBody (polyCap Θ K) := by
  have hint := nef_polyCap_isHalfPlaneInter Θ K
  exact ⟨hK.2.1.1.mono (nef_subset_polyCap hK),
    Metric.isCompact_of_isClosed_isBounded (nef_isHalfPlaneInter_isClosed hint)
      (nef_polyCap_isBounded Θ K), nef_isHalfPlaneInter_convex hint⟩

/-- `𝓒_Θ(K)` and `K` have the same support function on `Θ^◇ ∪ {ω + π, 3π/2}`. -/
lemma nef_supp_polyCap {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsCap K Θ.ω) {s : ℝ}
    (hs : s ∈ Θ.capAngles) : supp (polyCap Θ K) s = supp K s := by
  have hcb := nef_polyCap_isConvexBody hK
  exact le_antisymm (nef_supp_le hcb.1 fun p hp => nef_mem_polyCap_dot_le hK hp hs)
    (supp_mono (nef_subset_polyCap hK) hK.2.1.1 hcb.2.1 s)

lemma nef_capAngles_subset (Θ : AngleSet) : Θ.capAngles ⊆ jSet Θ.ω ∪ {Θ.ω + π, 3 * π / 2} := by
  intro s hs
  obtain ⟨hω0, hω1⟩ := Θ.hω
  rcases nef_mem_capAngles.1 hs with h | ⟨t, ht, rfl⟩ | rfl | rfl | rfl | rfl
  · have := Θ.subset s h; left; left; exact ⟨this.1.le, this.2.le⟩
  · have := Θ.subset t ht; left; right; constructor <;> linarith [this.1, this.2]
  · left; left; exact ⟨hω0.le, le_rfl⟩
  · left; right; constructor <;> linarith
  · right; simp
  · right; simp

/-- The niche of a cap is bounded. -/
lemma nef_niche_isBounded {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    Bornology.IsBounded (niche K ω) := by
  obtain ⟨⟨hω0, hω1⟩, hKcb, h1, h2, h3, h4, -⟩ := hK
  obtain ⟨R, hR⟩ := hKcb.2.1.isBounded.subset_closedBall 0
  have hRK : ∀ q ∈ K, |q.1| ≤ R ∧ |q.2| ≤ R := by
    intro q hq
    have := hR hq
    rw [mem_closedBall_zero_iff] at this
    exact ⟨(Real.norm_eq_abs q.1 ▸ norm_fst_le q).trans this,
      (Real.norm_eq_abs q.2 ▸ norm_snd_le q).trans this⟩
  obtain ⟨q0, hq0⟩ := hKcb.1
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hRK q0 hq0).1
  have hq2 : ∀ q ∈ K, q.2 ≤ 1 := fun q hq => by
    have := dot_le_supp hKcb.2.1 hq (π / 2)
    rwa [h2, nef_dot_uvec_pi_div_two] at this
  refine (Metric.isBounded_Icc ((-R, (0 : ℝ))) (R, 2 * R)).subset ?_
  rintro p ⟨⟨hf1, hf2⟩, hu⟩
  simp only [halfPlus, mem_ofPred_eq, nef_dot_uvec_pi_div_two] at hf1 hf2
  simp only [mem_iUnion] at hu
  obtain ⟨t, ⟨ht0, htω⟩, hp⟩ := hu
  rw [proposition2_2_2_qMinus] at hp
  obtain ⟨hpa, hpb⟩ := hp
  simp only [halfMinusOpen, mem_ofPred_eq, uvec_add_pi_div_two] at hpa hpb
  have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 (by linarith)
  have hc1 : cos t ≤ 1 := cos_le_one t
  have hs1 : sin t ≤ 1 := sin_le_one t
  have hsuppa : supp K t ≤ R * cos t + 1 := by
    refine nef_supp_le ⟨q0, hq0⟩ fun q hq => ?_
    obtain ⟨hq1, -⟩ := hRK q hq
    have := hq2 q hq
    simp only [dot, uvec]
    have := (abs_le.1 hq1).2
    nlinarith
  have hsuppb : supp K (t + π / 2) ≤ R * sin t + 1 := by
    refine nef_supp_le ⟨q0, hq0⟩ fun q hq => ?_
    obtain ⟨hq1, -⟩ := hRK q hq
    have := hq2 q hq
    rw [uvec_add_pi_div_two]
    simp only [dot, vvec]
    have := (abs_le.1 hq1).1
    nlinarith
  simp only [dot, uvec, vvec] at hpa hpb
  have hx1 : p.1 < R := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hx2 : -R < p.1 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hsc := sin_sq_add_cos_sq t
  have hy : p.2 ≤ 2 * R := by
    have e : p.2 = sin t * (p.1 * cos t + p.2 * sin t) + cos t * (p.1 * -sin t + p.2 * cos t) := by
      linear_combination (-p.2) * hsc
    rw [e]
    nlinarith
  exact ⟨⟨hx2.le, hf2⟩, ⟨hx1.le, hy⟩⟩

/-- **Proposition 3.2.1** (`pro:angled-cap`). For a cap `K`, `𝓒_Θ(K)` is a polygon cap containing
`K`; and `𝓒_Θ` fixes polygon caps (so `𝓒_Θ : 𝒦_ω^c → 𝒦_Θ^c` is surjective). -/
theorem proposition3_2_1 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsCap K Θ.ω) :
    K ⊆ polyCap Θ K ∧ IsPolygonCap Θ (polyCap Θ K) := by
  have hsub := nef_subset_polyCap hK
  have hint := nef_polyCap_isHalfPlaneInter Θ K
  have hcb : IsConvexBody (polyCap Θ K) := nef_polyCap_isConvexBody hK
  have hs := fun s hs => nef_supp_polyCap (Θ := Θ) hK (s := s) hs
  obtain ⟨hω, hKcb, h1, h2, h3, h4, -⟩ := hK
  refine ⟨hsub, ⟨hω, hcb, ?_, ?_, ?_, ?_, nef_isHalfPlaneInter_mono (nef_capAngles_subset Θ) hint⟩,
    hint⟩
  · rw [hs _ (nef_mem_capAngles.2 (by simp)), h1]
  · rw [hs _ (nef_mem_capAngles.2 (by simp)), h2]
  · rw [hs _ (nef_mem_capAngles.2 (by simp)), h3]
  · rw [hs _ (nef_mem_capAngles.2 (by simp)), h4]

theorem proposition3_2_1_fix {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) :
    polyCap Θ K = K := by
  refine Subset.antisymm ?_ (nef_subset_polyCap hK.1)
  intro p hp
  have hKeq := nef_eq_setOf_supp hK.1.2.1 hK.2
  rw [Set.ext_iff] at hKeq
  exact (hKeq p).2 fun s hs => nef_mem_polyCap_dot_le hK.1 hp hs

/-- **Proposition 3.2.2** (`pro:angled-niche-polygon-cap`). `𝒩_Θ(K) = 𝒩_Θ(𝓒_Θ(K)) ⊆ 𝒩(K)`. -/
theorem proposition3_2_2 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsCap K Θ.ω) :
    polyNiche Θ K = polyNiche Θ (polyCap Θ K) ∧ polyNiche Θ K ⊆ niche K Θ.ω := by
  constructor
  · have hq : ∀ t ∈ Θ.angles, qMinus K t = qMinus (polyCap Θ K) t := by
      intro t ht
      have e1 := nef_supp_polyCap hK (nef_mem_capAngles.2 (Or.inl ht))
      have e2 := nef_supp_polyCap hK (s := t + π / 2) (nef_mem_capAngles.2 (Or.inr (Or.inl
        ⟨t, ht, rfl⟩)))
      have : hallwayMap K t = hallwayMap (polyCap Θ K) t := by
        funext p; simp only [hallwayMap, e1, e2]
      simp only [qMinus, this]
    unfold polyNiche
    congr 1
    exact iUnion₂_congr hq
  · rintro p ⟨hf, hu⟩
    refine ⟨hf, ?_⟩
    simp only [mem_iUnion] at hu ⊢
    obtain ⟨t, ht, hp⟩ := hu
    exact ⟨t, Θ.subset t ht, hp⟩

/-- **Theorem 3.2.3** (`thm:polygon-upper-bound`). For a polygon cap, `𝒜_Θ(K) = |K| - |𝒩_Θ(K)|`; for
every cap, `𝒜_ω(K) ≤ 𝒜_Θ(K)`. -/
theorem theorem3_2_3 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) :
    polyArea Θ K = area K - area (polyNiche Θ K) := by
  rw [polyArea, proposition3_2_1_fix hK]

theorem theorem3_2_3_le {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsCap K Θ.ω) :
    sofaArea Θ.ω K ≤ polyArea Θ K := by
  have h1 : area K ≤ area (polyCap Θ K) :=
    ENNReal.toReal_mono (nef_polyCap_isBounded Θ K).measure_lt_top.ne
      (MeasureTheory.measure_mono (nef_subset_polyCap hK))
  have h2 : area (polyNiche Θ K) ≤ area (niche K Θ.ω) :=
    ENNReal.toReal_mono (nef_niche_isBounded hK).measure_lt_top.ne
      (MeasureTheory.measure_mono (proposition3_2_2 hK).2)
  unfold sofaArea polyArea; linarith

/-! ### Extensions of the space of polygon caps (§3.3) -/

/-- A polygon cap translate (Definition 3.3.1, `def:cap-trans`). -/
def IsPolygonCapTranslate (Θ : AngleSet) (K' : Set (ℝ × ℝ)) : Prop :=
  ∃ K : Set (ℝ × ℝ), ∃ v : ℝ × ℝ, IsPolygonCap Θ K ∧ K' = (fun p => p + v) '' K

/-! ### Auxiliary lemmas for §3.3 -/

lemma nef_mem_translate {K : Set (ℝ × ℝ)} {v p : ℝ × ℝ} :
    p ∈ (fun q => q + v) '' K ↔ p - v ∈ K := by
  constructor
  · rintro ⟨q, hq, rfl⟩; simpa using hq
  · intro h; exact ⟨p - v, h, by simp⟩

lemma nef_isHalfPlaneInter_translate {K : Set (ℝ × ℝ)} {A : Set ℝ} (h : IsHalfPlaneInter K A)
    (v : ℝ × ℝ) : IsHalfPlaneInter ((fun p => p + v) '' K) A := by
  obtain ⟨ι, t, c, ht, rfl⟩ := h
  refine ⟨ι, t, fun i => c i + dot v (uvec (t i)), ht, ?_⟩
  ext p
  simp only [nef_mem_translate, mem_iInter, halfMinus, mem_ofPred_eq, dot_sub_left]
  exact forall_congr' fun i => by constructor <;> intro h <;> linarith

lemma nef_isConvexBody_translate {K : Set (ℝ × ℝ)} (h : IsConvexBody K) (v : ℝ × ℝ) :
    IsConvexBody ((fun p => p + v) '' K) := by
  refine ⟨h.1.image _, h.2.1.image (continuous_id.add continuous_const), ?_⟩
  have : (fun p => p + v) '' K = (fun p => v + p) '' K := by simp_rw [add_comm]
  rw [this]; exact h.2.2.translate v

lemma nef_area_translate (S : Set (ℝ × ℝ)) (v : ℝ × ℝ) :
    area ((fun p => p + v) '' S) = area S := by
  have : MeasureTheory.Measure.IsAddHaarMeasure (MeasureTheory.volume : MeasureTheory.Measure
      (ℝ × ℝ)) := MeasureTheory.Measure.prod.instIsAddHaarMeasure _ _
  rw [area, area, Set.image_add_right, MeasureTheory.measure_preimage_add_right]

lemma nef_mem_diamond_of_mem_capAngles {Θ : AngleSet} {s : ℝ} (hs : s ∈ Θ.capAngles)
    (h1 : s ≠ Θ.ω + π) (h2 : s ≠ 3 * π / 2) : s ∈ Θ.diamond := by
  rcases hs with hs | hs
  · exact hs
  · rcases hs with rfl | hs
    · exact absurd rfl h1
    · exact absurd hs h2

lemma nef_diamond_subset_capAngles (Θ : AngleSet) : Θ.diamond ⊆ Θ.capAngles :=
  subset_union_left

/-- **Proposition 3.3.1** (`pro:cap-trans-space`). A convex polygon `K'` is a polygon cap translate if
and only if its widths along the angles `ω` and `π/2` are one, and it is a convex polygon with normal
angles in `Θ^◇ ∪ {ω + π, 3π/2}`. (The paper writes `Θ^◇`; the bottom sides of a cap have the normal
angles `ω + π` and `3π/2`, which its proof uses.) -/
theorem proposition3_3_1 {Θ : AngleSet} {K' : Set (ℝ × ℝ)} :
    IsPolygonCapTranslate Θ K' ↔
      IsConvexBody K' ∧ width K' Θ.ω = 1 ∧ width K' (π / 2) = 1 ∧
        IsHalfPlaneInter K' Θ.capAngles := by
  constructor
  · rintro ⟨K, v, ⟨⟨hω, hKcb, h1, h2, h3, h4, -⟩, hint⟩, rfl⟩
    have hs := fun t => supp_translate K v t hKcb.2.1 hKcb.1
    refine ⟨nef_isConvexBody_translate hKcb v, ?_, ?_, nef_isHalfPlaneInter_translate hint v⟩
    · rw [width, hs, hs, h1, h3, nef_dot_uvec_add_pi]; ring
    · rw [width, hs, hs, ← nef_three_pi_div_two, h2, h4, nef_three_pi_div_two,
        nef_dot_uvec_add_pi]; ring
  · rintro ⟨hcb, hw1, hw2, hint⟩
    obtain ⟨hω0, hω1⟩ := Θ.hω
    set A := supp K' Θ.ω - 1 with hA
    set B := supp K' (π / 2) - 1 with hB
    set v : ℝ × ℝ := ((A - B * sin Θ.ω) / cos Θ.ω, B) with hv
    have hvω : dot v (uvec Θ.ω) = A := by
      rcases eq_or_ne (cos Θ.ω) 0 with hc | hc
      · have hωe : Θ.ω = π / 2 := by
          by_contra hne
          have : 0 < cos Θ.ω := cos_pos_of_mem_Ioo ⟨by linarith, lt_of_le_of_ne hω1 hne⟩
          linarith
        simp only [dot, uvec, hv, hc, mul_zero, zero_add]
        rw [hωe, sin_pi_div_two, mul_one, hA, hB, hωe]
      · simp only [dot, uvec, hv]; field_simp; ring
    have hv2 : dot v (uvec (π / 2)) = B := by rw [nef_dot_uvec_pi_div_two]
    refine ⟨(fun p => p + -v) '' K', v, ?_, ?_⟩
    · have hcb' := nef_isConvexBody_translate hcb (-v)
      have hs := fun t => supp_translate K' (-v) t hcb.2.1 hcb.1
      have hint' := nef_isHalfPlaneInter_translate hint (-v)
      unfold width at hw1 hw2
      refine ⟨⟨⟨hω0, hω1⟩, hcb', ?_, ?_, ?_, ?_,
        nef_isHalfPlaneInter_mono (nef_capAngles_subset Θ) hint'⟩, hint'⟩
      · rw [hs, dot_neg_left, hvω, hA]; ring
      · rw [hs, dot_neg_left, hv2, hB]; ring
      · rw [hs, dot_neg_left, nef_dot_uvec_add_pi, hvω, hA]; linarith
      · rw [hs, dot_neg_left, nef_three_pi_div_two, nef_dot_uvec_add_pi, hv2, hB]; linarith
    · rw [Set.image_image]; simp

/-- **Proposition 3.3.2** (`pro:height-space-embedding`). A polygon cap translate is determined by
its support function on `Θ^◇`. Definition 3.3.2 (`def:height-space`): the space `ℋ_Θ` of functions
`Θ^◇ → ℝ` is represented by functions `ℝ → ℝ`, of which only the values on `Θ^◇` are used. -/
theorem proposition3_3_2 {Θ : AngleSet} {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsPolygonCapTranslate Θ K₁)
    (h₂ : IsPolygonCapTranslate Θ K₂) (h : ∀ t ∈ Θ.diamond, supp K₁ t = supp K₂ t) : K₁ = K₂ := by
  obtain ⟨hcb₁, hw₁, hw₁', hint₁⟩ := proposition3_3_1.1 h₁
  obtain ⟨hcb₂, hw₂, hw₂', hint₂⟩ := proposition3_3_1.1 h₂
  unfold width at hw₁ hw₁' hw₂ hw₂'
  have hωd : Θ.ω ∈ Θ.diamond := by simp [AngleSet.diamond]
  have hπd : π / 2 ∈ Θ.diamond := by simp [AngleSet.diamond]
  have hs : ∀ s ∈ Θ.capAngles, supp K₁ s = supp K₂ s := by
    intro s hs
    by_cases e1 : s = Θ.ω + π
    · subst e1; linarith [h _ hωd]
    by_cases e2 : s = 3 * π / 2
    · subst e2; rw [nef_three_pi_div_two]; linarith [h _ hπd]
    exact h s (nef_mem_diamond_of_mem_capAngles hs e1 e2)
  rw [nef_eq_setOf_supp hcb₁ hint₁, nef_eq_setOf_supp hcb₂ hint₂]
  ext p
  simp only [mem_ofPred_eq]
  exact forall₂_congr fun s hs' => by rw [hs s hs']

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

/-! ### Auxiliary lemmas for Proposition 3.3.3 -/

lemma nef_mem_capH_iff (Θ : AngleSet) (h : ℝ → ℝ) (p : ℝ × ℝ) :
    p ∈ capH Θ h ↔ (∀ s ∈ Θ.diamond, dot p (uvec s) ≤ h s) ∧
      h Θ.ω - 1 ≤ dot p (uvec Θ.ω) ∧ h (π / 2) - 1 ≤ dot p (uvec (π / 2)) := by
  simp only [capH, paraH, mem_inter_iff, mem_iInter, halfMinus, halfPlus, mem_ofPred_eq,
    mem_insert_iff, mem_singleton_iff, AngleSet.diamond, mem_union]
  constructor
  · rintro ⟨hpara, hΘ⟩
    refine ⟨?_, (hpara _ (Or.inl rfl)).2, (hpara _ (Or.inr rfl)).2⟩
    rintro s ((hs | hs) | hs | hs)
    · exact hΘ s (Or.inl hs)
    · exact hΘ s (Or.inr hs)
    · exact (hpara s (Or.inl hs)).1
    · exact (hpara s (Or.inr hs)).1
  · rintro ⟨hd, hω, hπ⟩
    refine ⟨?_, fun s hs => hd s (Or.inl hs)⟩
    rintro s (rfl | rfl)
    · exact ⟨hd _ (Or.inr (Or.inl rfl)), hω⟩
    · exact ⟨hd _ (Or.inr (Or.inr rfl)), hπ⟩

lemma nef_line_eq_imp {t₁ t₂ c₁ c₂ : ℝ} (h : line t₁ c₁ = line t₂ c₂) :
    sin (t₁ - t₂) = 0 ∧ c₁ * cos (t₁ - t₂) = c₂ := by
  have h0 : c₁ • uvec t₁ ∈ line t₂ c₂ := h ▸ (by simp [line, dot_smul_left])
  have h1 : c₁ • uvec t₁ + vvec t₁ ∈ line t₂ c₂ :=
    h ▸ (by simp [line, dot_add_left, dot_smul_left])
  simp only [line, mem_ofPred_eq, dot_add_left, dot_smul_left, dot_uvec_uvec,
    dot_vvec_uvec'] at h0 h1
  refine ⟨?_, h0⟩
  have : sin (t₂ - t₁) = 0 := by linarith
  rw [← neg_sub, sin_neg, this, neg_zero]

lemma nef_line_inj {t₁ t₂ c₁ c₂ : ℝ} (h1 : t₁ ∈ Ioo 0 π) (h2 : t₂ ∈ Ioo 0 π)
    (h : line t₁ c₁ = line t₂ c₂) : t₁ = t₂ ∧ c₁ = c₂ := by
  obtain ⟨hs, hc⟩ := nef_line_eq_imp h
  have h0 : t₁ - t₂ = 0 :=
    (sin_eq_zero_iff_of_lt_of_lt (by linarith [h1.1, h2.2]) (by linarith [h1.2, h2.1])).1 hs
  refine ⟨by linarith, ?_⟩
  rw [h0, cos_zero, mul_one] at hc; exact hc

lemma nef_line_add_pi (s c : ℝ) : line (s + π) c = line s (-c) := by
  ext p; simp only [line, mem_ofPred_eq, nef_dot_uvec_add_pi]
  constructor <;> intro h <;> linarith

lemma nef_mem_diamond_Ioo {Θ : AngleSet} {s : ℝ} (hs : s ∈ Θ.diamond) : s ∈ Ioo 0 π := by
  obtain ⟨hω0, hω1⟩ := Θ.hω
  have hπ := pi_pos
  simp only [AngleSet.diamond, mem_union, Finset.mem_coe, mem_image, mem_insert_iff,
    mem_singleton_iff] at hs
  rcases hs with (h | ⟨t, ht, rfl⟩) | rfl | rfl
  · have := Θ.subset s h; exact ⟨this.1, by linarith [this.2]⟩
  · have := Θ.subset t ht; exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · exact ⟨hω0, by linarith⟩
  · exact ⟨by linarith, by linarith⟩

lemma nef_pair_mem_diamond {Θ : AngleSet} {s : ℝ} (hs : s ∈ ({Θ.ω, π / 2} : Set ℝ)) :
    s ∈ Θ.diamond := by
  rcases hs with rfl | rfl <;> simp [AngleSet.diamond]

lemma nef_ne_of_mem_angles {Θ : AngleSet} {t s : ℝ}
    (ht : t ∈ (Θ.angles : Set ℝ) ∪ (fun s => s + π / 2) '' (Θ.angles : Set ℝ))
    (hs : s ∈ ({Θ.ω, π / 2} : Set ℝ)) : t ≠ s := by
  obtain ⟨hω0, hω1⟩ := Θ.hω
  rcases ht with ht | ⟨t', ht', rfl⟩
  · have := Θ.subset t ht
    rcases hs with rfl | rfl <;> intro h <;> linarith [this.1, this.2]
  · have := Θ.subset t' ht'
    rcases hs with rfl | rfl <;> intro h <;> linarith [this.1, this.2]

lemma nef_angles_subset_diamond (Θ : AngleSet) :
    (Θ.angles : Set ℝ) ∪ (fun s => s + π / 2) '' (Θ.angles : Set ℝ) ⊆ Θ.diamond :=
  subset_union_left

lemma nef_diamond_finite (Θ : AngleSet) : Θ.diamond.Finite :=
  ((Θ.angles.finite_toSet).union (Θ.angles.finite_toSet.image _)).union (Set.toFinite _)

lemma nef_toSet_closed (t c : ℝ) : (⟨t, c, false⟩ : HalfPlaneData).toSet = halfMinus t c := rfl

lemma nef_toSet_open (t c : ℝ) : (⟨t, c, true⟩ : HalfPlaneData).toSet = halfMinusOpen t c := rfl

lemma nef_boundary_eq (t c : ℝ) (o : Bool) :
    (⟨t, c, o⟩ : HalfPlaneData).boundary = line t c := rfl

lemma nef_capHalfPlanes_boundary_ne {Θ : AngleSet} {h : ℝ → ℝ} {d₁ d₂ : HalfPlaneData}
    (h₁ : d₁ ∈ capHalfPlanes Θ h) (h₂ : d₂ ∈ capHalfPlanes Θ h) (hne : d₁ ≠ d₂) :
    d₁.boundary ≠ d₂.boundary := by
  obtain ⟨t₁, c₁, o₁⟩ := d₁
  obtain ⟨t₂, c₂, o₂⟩ := d₂
  simp only [capHalfPlanes, mem_ofPred_eq] at h₁ h₂
  simp only [nef_boundary_eq, ne_eq, HalfPlaneData.mk.injEq] at hne ⊢
  intro hl
  rcases h₁ with ⟨ht₁, rfl, rfl⟩ | ⟨s₁, hs₁, rfl, rfl, rfl⟩ <;>
    rcases h₂ with ⟨ht₂, rfl, rfl⟩ | ⟨s₂, hs₂, rfl, rfl, rfl⟩
  · obtain ⟨rfl, -⟩ := nef_line_inj (nef_mem_diamond_Ioo ht₁) (nef_mem_diamond_Ioo ht₂) hl
    exact hne ⟨rfl, rfl, rfl⟩
  · rw [nef_line_add_pi] at hl
    obtain ⟨rfl, h'⟩ := nef_line_inj (nef_mem_diamond_Ioo ht₁)
      (nef_mem_diamond_Ioo (nef_pair_mem_diamond hs₂)) hl
    linarith
  · rw [nef_line_add_pi] at hl
    obtain ⟨rfl, h'⟩ := nef_line_inj (nef_mem_diamond_Ioo (nef_pair_mem_diamond hs₁))
      (nef_mem_diamond_Ioo ht₂) hl
    linarith
  · rw [nef_line_add_pi, nef_line_add_pi] at hl
    obtain ⟨rfl, -⟩ := nef_line_inj (nef_mem_diamond_Ioo (nef_pair_mem_diamond hs₁))
      (nef_mem_diamond_Ioo (nef_pair_mem_diamond hs₂)) hl
    exact hne ⟨rfl, rfl, rfl⟩

lemma nef_nicheHalfPlanes_boundary_ne {Θ : AngleSet} {h : ℝ → ℝ} {d₁ d₂ : HalfPlaneData}
    (h₁ : d₁ ∈ nicheHalfPlanes Θ h) (h₂ : d₂ ∈ nicheHalfPlanes Θ h) (hne : d₁ ≠ d₂) :
    d₁.boundary ≠ d₂.boundary := by
  obtain ⟨t₁, c₁, o₁⟩ := d₁
  obtain ⟨t₂, c₂, o₂⟩ := d₂
  simp only [nicheHalfPlanes, mem_ofPred_eq] at h₁ h₂
  simp only [nef_boundary_eq, ne_eq, HalfPlaneData.mk.injEq] at hne ⊢
  intro hl
  rcases h₁ with ⟨ht₁, rfl, rfl⟩ | ⟨s₁, hs₁, rfl, rfl, rfl⟩ <;>
    rcases h₂ with ⟨ht₂, rfl, rfl⟩ | ⟨s₂, hs₂, rfl, rfl, rfl⟩
  · obtain ⟨rfl, -⟩ := nef_line_inj (nef_mem_diamond_Ioo (nef_angles_subset_diamond Θ ht₁))
      (nef_mem_diamond_Ioo (nef_angles_subset_diamond Θ ht₂)) hl
    exact hne ⟨rfl, rfl, rfl⟩
  · rw [nef_line_add_pi] at hl
    obtain ⟨rfl, -⟩ := nef_line_inj (nef_mem_diamond_Ioo (nef_angles_subset_diamond Θ ht₁))
      (nef_mem_diamond_Ioo (nef_pair_mem_diamond hs₂)) hl
    exact nef_ne_of_mem_angles ht₁ hs₂ rfl
  · rw [nef_line_add_pi] at hl
    obtain ⟨rfl, -⟩ := nef_line_inj (nef_mem_diamond_Ioo (nef_pair_mem_diamond hs₁))
      (nef_mem_diamond_Ioo (nef_angles_subset_diamond Θ ht₂)) hl
    exact nef_ne_of_mem_angles ht₂ hs₁ rfl
  · rw [nef_line_add_pi, nef_line_add_pi] at hl
    obtain ⟨rfl, -⟩ := nef_line_inj (nef_mem_diamond_Ioo (nef_pair_mem_diamond hs₁))
      (nef_mem_diamond_Ioo (nef_pair_mem_diamond hs₂)) hl
    exact hne ⟨rfl, rfl, rfl⟩

lemma nef_capHalfPlanes_finite (Θ : AngleSet) (h : ℝ → ℝ) : (capHalfPlanes Θ h).Finite := by
  refine (((nef_diamond_finite Θ).image (fun t => (⟨t, h t, false⟩ : HalfPlaneData))).union
    ((Set.toFinite ({Θ.ω, π / 2} : Set ℝ)).image
      (fun s => (⟨s + π, 1 - h s, false⟩ : HalfPlaneData)))).subset ?_
  rintro ⟨t, c, o⟩ (⟨ht, hc, ho⟩ | ⟨s, hs, ht, hc, ho⟩)
  · simp only at ht hc ho; subst hc ho
    exact Or.inl ⟨t, ht, rfl⟩
  · simp only at ht hc ho; subst ht hc ho
    exact Or.inr ⟨s, hs, rfl⟩

lemma nef_nicheHalfPlanes_finite (Θ : AngleSet) (h : ℝ → ℝ) :
    (nicheHalfPlanes Θ h).Finite := by
  refine (((((Θ.angles.finite_toSet).union
    (Θ.angles.finite_toSet.image (fun s => s + π / 2)))).image
    (fun t => (⟨t, h t - 1, true⟩ : HalfPlaneData))).union
    ((Set.toFinite ({Θ.ω, π / 2} : Set ℝ)).image
      (fun s => (⟨s + π, 1 - h s, false⟩ : HalfPlaneData)))).subset ?_
  rintro ⟨t, c, o⟩ (⟨ht, hc, ho⟩ | ⟨s, hs, ht, hc, ho⟩)
  · simp only at ht hc ho; subst hc ho
    exact Or.inl ⟨t, ht, rfl⟩
  · simp only at ht hc ho; subst ht hc ho
    exact Or.inr ⟨s, hs, rfl⟩

lemma nef_mem_capH_iff_halfPlanes (Θ : AngleSet) (h : ℝ → ℝ) (p : ℝ × ℝ) :
    p ∈ capH Θ h ↔ ∀ d ∈ capHalfPlanes Θ h, p ∈ d.toSet := by
  rw [nef_mem_capH_iff]
  constructor
  · rintro ⟨hd, hω, hπ⟩ ⟨t, c, o⟩ (⟨ht, hc, ho⟩ | ⟨s, hs, ht, hc, ho⟩)
    · simp only at ht hc ho; subst hc ho
      exact hd t ht
    · simp only at ht hc ho; subst ht hc ho
      show dot p (uvec (s + π)) ≤ 1 - h s
      rw [nef_dot_uvec_add_pi]
      rcases hs with rfl | rfl
      · linarith
      · linarith
  · intro H
    refine ⟨fun s hs => H ⟨s, h s, false⟩ (Or.inl ⟨hs, rfl, rfl⟩), ?_, ?_⟩
    · have : dot p (uvec (Θ.ω + π)) ≤ 1 - h Θ.ω :=
        H ⟨Θ.ω + π, 1 - h Θ.ω, false⟩ (Or.inr ⟨Θ.ω, by simp, rfl, rfl, rfl⟩)
      rw [nef_dot_uvec_add_pi] at this; linarith
    · have : dot p (uvec (π / 2 + π)) ≤ 1 - h (π / 2) :=
        H ⟨π / 2 + π, 1 - h (π / 2), false⟩ (Or.inr ⟨π / 2, by simp, rfl, rfl, rfl⟩)
      rw [nef_dot_uvec_add_pi] at this; linarith

lemma nef_mem_nicheH_iff (Θ : AngleSet) (h : ℝ → ℝ) (p : ℝ × ℝ) :
    p ∈ nicheH Θ h ↔ (∀ s ∈ ({Θ.ω, π / 2} : Set ℝ),
        p ∈ (⟨s + π, 1 - h s, false⟩ : HalfPlaneData).toSet) ∧
      ∃ t ∈ Θ.angles, p ∈ (⟨t, h t - 1, true⟩ : HalfPlaneData).toSet ∧
        p ∈ (⟨t + π / 2, h (t + π / 2) - 1, true⟩ : HalfPlaneData).toSet := by
  simp only [nicheH, fanH, mem_inter_iff, mem_iInter, mem_iUnion, nef_toSet_closed,
    nef_toSet_open, halfPlus, halfMinus, mem_ofPred_eq, nef_dot_uvec_add_pi, exists_prop]
  constructor
  · rintro ⟨hf, ht⟩
    exact ⟨fun s hs => by linarith [hf s hs], ht⟩
  · rintro ⟨hf, ht⟩
    exact ⟨fun s hs => by linarith [hf s hs], ht⟩

/-- **Proposition 3.3.3** (`pro:cap-niche-nef-polygons`). `𝓒_Θ(h)` and `𝒩_Θ(h)` are simple Nef
polygons with the listed defining half-planes. -/
theorem proposition3_3_3 (Θ : AngleSet) (h : ℝ → ℝ) :
    (∃ (n : ℕ) (E : BoolFun n) (H : Fin n → HalfPlaneData), IsSimpleNefPolygon (capH Θ h) E H ∧
        Set.range H = capHalfPlanes Θ h) ∧
      (∃ (n : ℕ) (E : BoolFun n) (H : Fin n → HalfPlaneData), IsSimpleNefPolygon (nicheH Θ h) E H ∧
        Set.range H = nicheHalfPlanes Θ h) := by
  classical
  constructor
  · obtain ⟨n, H, hinj, hrange⟩ := (nef_capHalfPlanes_finite Θ h).fin_param
    refine ⟨n, fun P => decide (∀ j, P j = true), H, ⟨?_, ?_, ?_⟩, hrange⟩
    · intro P Q hPQ hP
      simp only [decide_eq_true_eq] at hP ⊢
      exact fun j => hPQ j (hP j)
    · intro i j hij
      exact nef_capHalfPlanes_boundary_ne (hrange ▸ mem_range_self i)
        (hrange ▸ mem_range_self j) (hinj.ne hij)
    · ext p
      simp only [nefPolygon, mem_ofPred_eq, decide_eq_true_eq]
      rw [nef_mem_capH_iff_halfPlanes, ← hrange]
      simp only [mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  · obtain ⟨n, H, hinj, hrange⟩ := (nef_nicheHalfPlanes_finite Θ h).fin_param
    have hmemF : ∀ s ∈ ({Θ.ω, π / 2} : Set ℝ),
        (⟨s + π, 1 - h s, false⟩ : HalfPlaneData) ∈ Set.range H := fun s hs =>
      hrange ▸ Or.inr ⟨s, hs, rfl, rfl, rfl⟩
    have hmemA : ∀ t ∈ Θ.angles, (⟨t, h t - 1, true⟩ : HalfPlaneData) ∈ Set.range H :=
      fun t ht => hrange ▸ Or.inl ⟨Or.inl ht, rfl, rfl⟩
    have hmemB : ∀ t ∈ Θ.angles,
        (⟨t + π / 2, h (t + π / 2) - 1, true⟩ : HalfPlaneData) ∈ Set.range H :=
      fun t ht => hrange ▸ Or.inl ⟨Or.inr ⟨t, ht, rfl⟩, rfl, rfl⟩
    refine ⟨n, fun P => decide ((∀ j, (∃ s ∈ ({Θ.ω, π / 2} : Set ℝ),
        H j = ⟨s + π, 1 - h s, false⟩) → P j = true) ∧
      ∃ t ∈ Θ.angles, ∀ j, (H j = ⟨t, h t - 1, true⟩ ∨
        H j = ⟨t + π / 2, h (t + π / 2) - 1, true⟩) → P j = true), H, ⟨?_, ?_, ?_⟩, hrange⟩
    · intro P Q hPQ hP
      simp only [decide_eq_true_eq] at hP ⊢
      obtain ⟨h1, t, ht, h2⟩ := hP
      exact ⟨fun j hj => hPQ j (h1 j hj), t, ht, fun j hj => hPQ j (h2 j hj)⟩
    · intro i j hij
      exact nef_nicheHalfPlanes_boundary_ne (hrange ▸ mem_range_self i)
        (hrange ▸ mem_range_self j) (hinj.ne hij)
    · ext p
      simp only [nefPolygon, mem_ofPred_eq, decide_eq_true_eq]
      rw [nef_mem_nicheH_iff]
      constructor
      · rintro ⟨hf, t, ht, hA, hB⟩
        refine ⟨?_, t, ht, ?_⟩
        · rintro j ⟨s, hs, hj⟩
          rw [hj]; exact hf s hs
        · rintro j (hj | hj)
          · rw [hj]; exact hA
          · rw [hj]; exact hB
      · rintro ⟨hf, t, ht, hAB⟩
        refine ⟨fun s hs => ?_, t, ht, ?_, ?_⟩
        · obtain ⟨j, hj⟩ := hmemF s hs
          have := hf j ⟨s, hs, hj⟩
          rwa [hj] at this
        · obtain ⟨j, hj⟩ := hmemA t ht
          have := hAB j (Or.inl hj)
          rwa [hj] at this
        · obtain ⟨j, hj⟩ := hmemB t ht
          have := hAB j (Or.inr hj)
          rwa [hj] at this

/-- **Proposition 3.3.4** (`pro:cap-extension-compatible`). `𝓒_Θ(h_{K'}) = K'` for a polygon cap
translate `K'`. -/
theorem proposition3_3_4 {Θ : AngleSet} {K' : Set (ℝ × ℝ)} (hK' : IsPolygonCapTranslate Θ K') :
    capH Θ (supp K') = K' := by
  obtain ⟨hcb, hw1, hw2, hint⟩ := proposition3_3_1.1 hK'
  have hKeq := nef_eq_setOf_supp hcb hint
  unfold width at hw1 hw2
  ext p
  rw [nef_mem_capH_iff]
  conv_rhs => rw [hKeq]
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨hd, hω, hπ⟩ s hs
    by_cases h1 : s = Θ.ω + π
    · subst h1; rw [nef_dot_uvec_add_pi]; linarith
    by_cases h2 : s = 3 * π / 2
    · subst h2; rw [nef_three_pi_div_two, nef_dot_uvec_add_pi]; linarith
    exact hd s (nef_mem_diamond_of_mem_capAngles hs h1 h2)
  · intro H
    refine ⟨fun s hs => H s (nef_diamond_subset_capAngles Θ hs), ?_, ?_⟩
    · have := H (Θ.ω + π) (by simp [AngleSet.capAngles])
      rw [nef_dot_uvec_add_pi] at this; linarith
    · have := H (3 * π / 2) (by simp [AngleSet.capAngles])
      rw [nef_three_pi_div_two, nef_dot_uvec_add_pi] at this; linarith

/-- **Proposition 3.3.5** (`pro:niche-extension-compatible`). For a polygon cap `K`,
`𝒩_Θ(h_K) = 𝒩_Θ(K)` and `𝒜_Θ(h_K) = 𝒜_Θ(K)`. -/
theorem proposition3_3_5 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) :
    nicheH Θ (supp K) = polyNiche Θ K ∧ areaH Θ (supp K) = polyArea Θ K := by
  have hn : nicheH Θ (supp K) = polyNiche Θ K := by
    obtain ⟨⟨hω, hKcb, h1, h2, h3, h4, -⟩, -⟩ := hK
    unfold nicheH polyNiche fanH fan
    congr 1
    · ext p
      simp only [mem_iInter, mem_inter_iff, halfPlus, mem_ofPred_eq, mem_insert_iff,
        mem_singleton_iff, forall_eq_or_imp, forall_eq, h1, h2, sub_self]
    · refine iUnion₂_congr fun t _ => ?_
      rw [proposition2_2_2_qMinus]
  refine ⟨hn, ?_⟩
  have htr : IsPolygonCapTranslate Θ K := ⟨K, 0, hK, by simp⟩
  rw [areaH, proposition3_3_4 htr, hn, theorem3_2_3 hK]

/-- The niche and the polygon sofa area functional of a polygon cap translate
(Definition 3.3.4, `def:cap-translate-extensions`). -/
def nicheT (Θ : AngleSet) (K' : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := nicheH Θ (supp K')

/-- `𝒜_Θ(K') := 𝒜_Θ(h_{K'})` (Definition 3.3.4). -/
noncomputable def areaT (Θ : AngleSet) (K' : Set (ℝ × ℝ)) : ℝ := areaH Θ (supp K')

lemma nef_nicheH_translate (Θ : AngleSet) (h : ℝ → ℝ) (v : ℝ × ℝ) :
    nicheH Θ (fun t => h t + dot v (uvec t)) = (fun p => p + v) '' nicheH Θ h := by
  ext p
  rw [nef_mem_translate]
  simp only [nicheH, fanH, mem_inter_iff, mem_iInter, mem_iUnion, halfPlus, halfMinusOpen,
    mem_ofPred_eq, dot_sub_left, exists_prop]
  constructor
  · rintro ⟨hf, t, ht, h1, h2⟩
    exact ⟨fun s hs => by have := hf s hs; linarith, t, ht, by linarith, by linarith⟩
  · rintro ⟨hf, t, ht, h1, h2⟩
    exact ⟨fun s hs => by have := hf s hs; linarith, t, ht, by linarith, by linarith⟩

/-- **Theorem 3.3.6** (`thm:height-extensions`). For a translate `K' = K + v` of a polygon cap,
`𝒩_Θ(K') = 𝒩_Θ(K) + v` and `𝒜_Θ(K') = 𝒜_Θ(K)`. -/
theorem theorem3_3_6 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) (v : ℝ × ℝ) :
    nicheT Θ ((fun p => p + v) '' K) = (fun p => p + v) '' polyNiche Θ K ∧
      areaT Θ ((fun p => p + v) '' K) = polyArea Θ K := by
  have hKcb := hK.1.2.1
  have hs : supp ((fun p => p + v) '' K) = fun t => supp K t + dot v (uvec t) :=
    funext fun t => supp_translate K v t hKcb.2.1 hKcb.1
  have hn : nicheH Θ (supp ((fun p => p + v) '' K)) = (fun p => p + v) '' polyNiche Θ K := by
    rw [hs, nef_nicheH_translate, (proposition3_3_5 hK).1]
  refine ⟨hn, ?_⟩
  have htr : IsPolygonCapTranslate Θ ((fun p => p + v) '' K) := ⟨K, v, hK, rfl⟩
  rw [areaT, areaH, proposition3_3_4 htr, hn, theorem3_2_3 hK, nef_area_translate,
    nef_area_translate]

/-- Each wedge `F_h ∩ H₋°(t, ·) ∩ H₋°(t + π/2, ·)`, `t ∈ (0, ω)`, is bounded. -/
lemma nef_wedge_isBounded {ω t a b c d : ℝ} (ht0 : 0 < t) (htω : t < ω) (hω : ω ≤ π / 2) :
    Bornology.IsBounded {p : ℝ × ℝ | a ≤ dot p (uvec ω) ∧ b ≤ dot p (uvec (π / 2)) ∧
      dot p (uvec t) < c ∧ dot p (vvec t) < d} := by
  have hc1 : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs1 : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 (by linarith)
  have hc2 : 0 < cos (ω - t) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs2 : 0 < sin (ω - t) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hf : Continuous fun q : ℝ × ℝ => q.1 • uvec t + q.2 • vvec t := by fun_prop
  have hbox : Bornology.IsBounded ((fun q : ℝ × ℝ => q.1 • uvec t + q.2 • vvec t) ''
      (Icc ((a - d * sin (ω - t)) / cos (ω - t)) c ×ˢ Icc ((b - c * sin t) / cos t) d)) :=
    ((isCompact_Icc.prod isCompact_Icc).image hf).isBounded
  refine hbox.subset ?_
  rintro p ⟨h1, h2, h3, h4⟩
  refine ⟨(dot p (uvec t), dot p (vvec t)), ⟨⟨?_, h3.le⟩, ⟨?_, h4.le⟩⟩,
    (eq_dot_uvec_smul_add p t).symm⟩
  · have e : dot p (uvec ω) = cos (ω - t) * dot p (uvec t) + sin (ω - t) * dot p (vvec t) := by
      simp only [dot, uvec, vvec, cos_sub, sin_sub]
      linear_combination (-(p.1 * cos ω + p.2 * sin ω)) * sin_sq_add_cos_sq t
    show (a - d * sin (ω - t)) / cos (ω - t) ≤ dot p (uvec t)
    rw [div_le_iff₀ hc2]
    nlinarith
  · have e : dot p (uvec (π / 2)) = sin t * dot p (uvec t) + cos t * dot p (vvec t) := by
      simp only [dot, uvec, vvec, cos_pi_div_two, sin_pi_div_two]
      linear_combination (-p.2) * sin_sq_add_cos_sq t
    show (b - c * sin t) / cos t ≤ dot p (vvec t)
    rw [div_le_iff₀ hc1]
    nlinarith

/-- The niche `𝒩_Θ(h)` is bounded for every `h ∈ ℋ_Θ`. -/
lemma nef_nicheH_isBounded (Θ : AngleSet) (h : ℝ → ℝ) : Bornology.IsBounded (nicheH Θ h) := by
  have hsub : nicheH Θ h ⊆ ⋃ t ∈ Θ.angles, {p : ℝ × ℝ | h Θ.ω - 1 ≤ dot p (uvec Θ.ω) ∧
      h (π / 2) - 1 ≤ dot p (uvec (π / 2)) ∧ dot p (uvec t) < h t - 1 ∧
        dot p (vvec t) < h (t + π / 2) - 1} := by
    rintro p ⟨hf, hu⟩
    simp only [fanH, mem_iInter, halfPlus, mem_ofPred_eq, mem_insert_iff,
      mem_singleton_iff] at hf
    simp only [mem_iUnion, mem_inter_iff, halfMinusOpen, mem_ofPred_eq,
      uvec_add_pi_div_two] at hu ⊢
    obtain ⟨t, ht, h1, h2⟩ := hu
    exact ⟨t, ht, hf _ (Or.inl rfl), hf _ (Or.inr rfl), h1, h2⟩
  refine Bornology.IsBounded.subset ?_ hsub
  refine (Bornology.isBounded_biUnion_finset _).2 fun t ht => ?_
  obtain ⟨ht0, htω, hω⟩ := nef_angle_mem ht
  exact nef_wedge_isBounded ht0 htω hω

/-- **Proposition 3.3.7** (`pro:cap-translate-reduction`). If `K⁺ = 𝓒_Θ(h⁺)` is a polygon cap
translate, then `𝒜_Θ(h⁺) ≤ 𝒜_Θ(K⁺)`. -/
theorem proposition3_3_7 {Θ : AngleSet} {h : ℝ → ℝ}
    (hK : IsPolygonCapTranslate Θ (capH Θ h)) : areaH Θ h ≤ areaT Θ (capH Θ h) := by
  obtain ⟨hcb, hw1, hw2, -⟩ := proposition3_3_1.1 hK
  set K := capH Θ h with hKdef
  have hmem : ∀ p ∈ K, (∀ s ∈ Θ.diamond, dot p (uvec s) ≤ h s) ∧
      h Θ.ω - 1 ≤ dot p (uvec Θ.ω) ∧ h (π / 2) - 1 ≤ dot p (uvec (π / 2)) :=
    fun p hp => (nef_mem_capH_iff Θ h p).1 hp
  have hle : ∀ s ∈ Θ.diamond, supp K s ≤ h s := fun s hs =>
    nef_supp_le hcb.1 fun p hp => (hmem p hp).1 s hs
  have hge : ∀ s ∈ ({Θ.ω, π / 2} : Set ℝ), h s ≤ supp K s := by
    intro s hs
    have hw : supp K s + supp K (s + π) = 1 := by
      rcases hs with rfl | rfl
      · exact hw1
      · exact hw2
    have hpi : supp K (s + π) ≤ 1 - h s := by
      refine nef_supp_le hcb.1 fun p hp => ?_
      rw [nef_dot_uvec_add_pi]
      rcases hs with rfl | rfl
      · linarith [(hmem p hp).2.1]
      · linarith [(hmem p hp).2.2]
    linarith
  have hsub : nicheH Θ (supp K) ⊆ nicheH Θ h := by
    rintro p ⟨hf, hu⟩
    simp only [fanH, mem_iInter, halfPlus, mem_ofPred_eq, mem_insert_iff,
      mem_singleton_iff] at hf
    simp only [mem_iUnion, mem_inter_iff, halfMinusOpen, mem_ofPred_eq] at hu
    refine ⟨?_, ?_⟩
    · simp only [fanH, mem_iInter, halfPlus, mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
      intro s hs
      have h1 := hf s hs
      have h2 := hge s hs
      linarith
    · simp only [mem_iUnion, mem_inter_iff, halfMinusOpen, mem_ofPred_eq]
      obtain ⟨t, ht, h1, h2⟩ := hu
      have htd : t ∈ Θ.diamond := by simp [AngleSet.diamond, ht]
      have htd' : t + π / 2 ∈ Θ.diamond := by
        simp only [AngleSet.diamond, mem_union, Finset.mem_coe, mem_image]
        exact Or.inl (Or.inr ⟨t, ht, rfl⟩)
      exact ⟨t, ht, by linarith [hle t htd], by linarith [hle _ htd']⟩
  unfold areaT areaH
  rw [proposition3_3_4 hK]
  have := ENNReal.toReal_mono ((nef_nicheH_isBounded Θ h).measure_lt_top
    (μ := MeasureTheory.volume)).ne (MeasureTheory.measure_mono hsub)
  unfold area at *
  linarith

end MovingSofaOptimality
