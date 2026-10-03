module

public import MovingSofaOptimality.Monotone.MonotoneSofa

/-!
# Cap and niche (§2.4)

Theorems 2.4.1 (`thm:cap-hallway-intersection`), 2.4.2 (`thm:monotonization-structure`), 2.4.3
(`thm:monotone-sofa-structure`) and 2.4.4 (`thm:monotonization-idempotent`).

In Theorem 2.4.2 the niche is a union over `t ∈ (0, ω)` while `𝓘(S)` removes `Q_S⁻(t)` for
`t ∈ [0, ω]` (inventory item 3): the two endpoints contribute nothing, as `Q_S⁻(0)` lies below the
strip `H` and `Q_S⁻(ω)` lies outside the strip `V_ω` (by `h_S(π/2) = h_S(ω) = 1`).
-/

@[expose] public section

open Real Set

namespace MovingSofaOptimality

lemma ms_dot_uvec_three_pi_div_two (p : ℝ × ℝ) : dot p (uvec (3 * π / 2)) = -p.2 := by
  rw [show 3 * π / 2 = π / 2 + π by ring, uvec_add_pi, dot_neg_right, ms_dot_uvec_pi_div_two]

lemma ms_dot_uvec_add_pi (p : ℝ × ℝ) (t : ℝ) : dot p (uvec (t + π)) = -dot p (uvec t) := by
  rw [uvec_add_pi, dot_neg_right]

/-- The upper right vertex `o_ω` of `P_ω` (any point of the upper side if `ω = π/2`) lies in
`𝓒(S)`. -/
lemma ms_exists_corner {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) :
    ∃ o ∈ capOf S ω, o.2 = 1 ∧ dot o (uvec ω) = 1 := by
  have hcpt := ms_isCompact_of_isMovingSofaWithAngle hS
  have hne := hS.2.1.nonempty
  obtain ⟨h1, h2⟩ := proposition2_3_4 hω hS hstd
  have hP := proposition2_3_1_subset hω hS hstd
  obtain ⟨q₂, hq₂, hq₂1⟩ := exists_dot_eq_supp hcpt hne (π / 2)
  rw [hstd.2, ms_dot_uvec_pi_div_two] at hq₂1
  rcases hω.2.lt_or_eq with hlt | heq
  · obtain ⟨qω, hqω, hqω1⟩ := exists_dot_eq_supp hcpt hne ω
    rw [hstd.1] at hqω1
    have hcos : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [hω.1, pi_pos], hlt⟩
    have hoω : dot ((1 - sin ω) / cos ω, (1 : ℝ)) (uvec ω) = 1 := by
      simp only [dot, uvec]; field_simp; ring
    refine ⟨((1 - sin ω) / cos ω, 1), ⟨⟨⟨zero_le_one, le_rfl⟩, ?_⟩, ?_⟩, rfl, hoω⟩
    · rw [ms_mem_vStripRot_iff, hoω]; exact ⟨zero_le_one, le_rfl⟩
    rw [mem_iInter₂]
    intro t ht
    have ht2 : t ≤ π / 2 := ht.2.trans hω.2
    rw [ms_mem_qPlus_iff]
    constructor
    · -- `o_ω` is below `q_ω` in the direction `u_t`
      refine le_trans ?_ (dot_le_supp hcpt hqω t)
      have hqω2 : qω.2 ≤ 1 := (hP hqω).1.2
      have hsin : sin (t - ω) ≤ 0 :=
        sin_nonpos_of_nonpos_of_neg_pi_le (by linarith [ht.2]) (by linarith [ht.1, hω.2, pi_pos])
      have key : cos ω * (dot ((1 - sin ω) / cos ω, (1 : ℝ)) (uvec t) - dot qω (uvec t)) =
          (1 - qω.2) * sin (t - ω) := by
        simp only [dot, uvec] at hqω1 ⊢
        rw [sin_sub]
        field_simp
        linear_combination (-cos t) * hqω1
      have : (1 - qω.2) * sin (t - ω) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) hsin
      nlinarith
    · -- `o_ω` is below `q_{π/2}` in the direction `v_t`
      have := dot_le_supp hcpt hq₂ (t + π / 2)
      rw [uvec_add_pi_div_two] at this
      refine le_trans ?_ this
      have hV := (ms_mem_vStripRot_iff ω q₂).1 (hP hq₂).2
      have hsin : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [pi_pos])
      have hx : q₂.1 ≤ (1 - sin ω) / cos ω := by
        rw [le_div_iff₀ hcos]
        simp only [dot, uvec] at hV
        rw [hq₂1] at hV
        linarith [hV.2]
      simp only [dot, vvec, hq₂1]
      nlinarith
  · refine ⟨q₂, h2 (h1 hq₂), hq₂1, ?_⟩
    rw [heq, ms_dot_uvec_pi_div_two, hq₂1]

/-- **Theorem 2.4.1** (`thm:cap-hallway-intersection`). For a moving sofa `S` with rotation angle
`ω ∈ (0, π/2]` in standard position, `𝓒(S)` is a cap with rotation angle `ω`. -/
theorem theorem2_4_1 {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) : IsCap (capOf S ω) ω := by
  have hne := hS.2.1.nonempty
  obtain ⟨h1, h2⟩ := proposition2_3_4 hω hS hstd
  have hCne : (capOf S ω).Nonempty := (hne.mono h1).mono h2
  have hCc : IsCompact (capOf S ω) := ms_isCompact_capOf hω
  have hJ : ∀ s ∈ jSet ω, supp (capOf S ω) s = supp S s :=
    fun s hs => (lemma2_3_5_supp hω hS hstd hs).2
  have hωJ : ω ∈ jSet ω := Or.inl ⟨hω.1.le, le_rfl⟩
  have hπJ : π / 2 ∈ jSet ω := Or.inr ⟨le_rfl, by linarith [hω.1]⟩
  have hsin0 : 0 ≤ sin ω := sin_nonneg_of_nonneg_of_le_pi hω.1.le (by linarith [hω.2, pi_pos])
  have hsin1 : sin ω ≤ 1 := sin_le_one ω
  -- the corner `o` and the points `o - u_{π/2}`, `o - u_ω` of `𝓒(S)` on the lower sides of `P_ω`
  obtain ⟨o, ho, ho2, hoω⟩ := ms_exists_corner hω hS hstd
  have hz1 : o - uvec (π / 2) ∈ capOf S ω := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [ms_mem_hStrip_iff]; simp [ho2]
    · rw [ms_mem_vStripRot_iff, dot_sub_left, hoω, dot_uvec_uvec, cos_pi_div_two_sub]
      constructor <;> linarith
    · rw [mem_iInter₂]
      intro t ht
      have := ms_qPlus_sub (θ := π / 2) (l := 1) ⟨by linarith [ht.2, hω.2], by linarith [ht.1]⟩
        zero_le_one (mem_iInter₂.1 ho.2 t ht)
      rwa [one_smul] at this
  have hz2 : o - uvec ω ∈ capOf S ω := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [ms_mem_hStrip_iff]; simp only [Prod.snd_sub, uvec_snd, ho2]
      constructor <;> linarith
    · rw [ms_mem_vStripRot_iff, dot_sub_left, hoω, dot_uvec_self]; norm_num
    · rw [mem_iInter₂]
      intro t ht
      have := ms_qPlus_sub (θ := ω) (l := 1) ⟨by linarith [ht.2], by linarith [ht.1, hω.2]⟩
        zero_le_one (mem_iInter₂.1 ho.2 t ht)
      rwa [one_smul] at this
  have hsupp3 : supp (capOf S ω) (ω + π) = 0 := by
    refine le_antisymm (ms_supp_le_of_forall hCne fun p hp => ?_) ?_
    · rw [ms_dot_uvec_add_pi]
      linarith [((ms_mem_vStripRot_iff ω p).1 hp.1.2).1]
    · have := dot_le_supp hCc hz2 (ω + π)
      rwa [ms_dot_uvec_add_pi, dot_sub_left, hoω, dot_uvec_self, sub_self, neg_zero] at this
  have hsupp4 : supp (capOf S ω) (3 * π / 2) = 0 := by
    refine le_antisymm (ms_supp_le_of_forall hCne fun p hp => ?_) ?_
    · rw [ms_dot_uvec_three_pi_div_two]
      linarith [hp.1.1.1]
    · have := dot_le_supp hCc hz1 (3 * π / 2)
      rw [ms_dot_uvec_three_pi_div_two] at this
      simpa [ho2] using this
  refine ⟨hω, ⟨hCne, hCc, ms_convex_capOf S ω⟩, (hJ ω hωJ).trans hstd.1,
    (hJ (π / 2) hπJ).trans hstd.2, hsupp3, hsupp4, ?_⟩
  -- `𝓒(S)` is the intersection of its supporting half-planes with normal angles in
  -- `J_ω ∪ {ω + π, 3π/2}`
  refine ⟨↥(jSet ω ∪ {ω + π, 3 * π / 2}), fun i => i.1, fun i => supp (capOf S ω) i.1,
    fun i => i.2, ?_⟩
  ext p
  simp only [mem_iInter, Subtype.forall]
  constructor
  · intro hp s _
    exact dot_le_supp hCc hp s
  · intro h
    have hJ' : ∀ s ∈ jSet ω, dot p (uvec s) ≤ supp S s := fun s hs => by
      have := h s (Or.inl hs); rwa [halfMinus, mem_ofPred_eq, hJ s hs] at this
    have hA : dot p (uvec (ω + π)) ≤ 0 := by
      have := h (ω + π) (Or.inr (mem_insert _ _)); rwa [halfMinus, mem_ofPred_eq, hsupp3] at this
    have hB : dot p (uvec (3 * π / 2)) ≤ 0 := by
      have := h (3 * π / 2) (Or.inr (mem_insert_of_mem _ (mem_singleton _)))
      rwa [halfMinus, mem_ofPred_eq, hsupp4] at this
    rw [ms_dot_uvec_add_pi] at hA
    rw [ms_dot_uvec_three_pi_div_two] at hB
    have hp2 := hJ' (π / 2) hπJ
    rw [ms_dot_uvec_pi_div_two, hstd.2] at hp2
    have hpω := hJ' ω hωJ
    rw [hstd.1] at hpω
    refine ⟨⟨⟨by linarith, hp2⟩, (ms_mem_vStripRot_iff ω p).2 ⟨by linarith, hpω⟩⟩,
      mem_iInter₂.2 fun t ht => (ms_mem_qPlus_iff S t p).2 ⟨hJ' t (ms_mem_jSet_left ht), ?_⟩⟩
    have := hJ' (t + π / 2) (ms_mem_jSet_right ht)
    rwa [uvec_add_pi_div_two] at this

lemma ms_capOf_congr {X Y : Set (ℝ × ℝ)} {ω : ℝ} (h : ∀ s ∈ jSet ω, supp X s = supp Y s) :
    capOf X ω = capOf Y ω := by
  unfold capOf
  congr 1
  refine iInter₂_congr fun t ht => ?_
  rw [qPlus, qPlus, ms_hallwayMap_congr_jSet h ht]

lemma ms_monotonization_congr {X Y : Set (ℝ × ℝ)} {ω : ℝ}
    (h : ∀ s ∈ jSet ω, supp X s = supp Y s) : monotonization X ω = monotonization Y ω := by
  unfold monotonization
  congr 1
  refine iInter₂_congr fun t ht => ?_
  rw [suppHallway, suppHallway, ms_hallwayMap_congr_jSet h ht]

/-- **Theorem 2.4.2** (`thm:monotonization-structure`). `𝓘(S) = K \ 𝒩(K)` for the cap
`K = 𝓒(S)`. -/
theorem theorem2_4_2 {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) :
    monotonization S ω = capOf S ω \ niche (capOf S ω) ω := by
  have hJ : ∀ s ∈ jSet ω, supp (capOf S ω) s = supp S s :=
    fun s hs => (lemma2_3_5_supp hω hS hstd hs).2
  ext p
  constructor
  · intro hp
    refine ⟨ms_monotonization_subset_capOf S ω hp, ?_⟩
    rintro ⟨-, hU⟩
    obtain ⟨t, ht, hpt⟩ := mem_iUnion₂.1 hU
    have ht' : t ∈ Icc 0 ω := Ioo_subset_Icc_self ht
    rw [qMinus, ms_hallwayMap_congr_jSet hJ ht'] at hpt
    have := mem_iInter₂.1 hp.2 t ht'
    rw [proposition2_2_2_hallway] at this
    exact this.2 hpt
  · rintro ⟨hpC, hpN⟩
    have hH := hpC.1.1
    have hV := (ms_mem_vStripRot_iff ω p).1 hpC.1.2
    refine ⟨hpC.1, mem_iInter₂.2 fun t ht => ?_⟩
    rw [proposition2_2_2_hallway]
    refine ⟨mem_iInter₂.1 hpC.2 t ht, fun hpt => ?_⟩
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · -- `t = 0`: `Q_S⁻(0)` lies below the strip `H`
      rw [← h0, ms_mem_qMinus_iff, zero_add, hstd.2] at hpt
      have : dot p (vvec 0) = p.2 := by simp [dot, vvec]
      linarith [hpt.2, hH.1]
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · -- `t = ω`: `Q_S⁻(ω)` lies outside the strip `V_ω`
      rw [h1, ms_mem_qMinus_iff, hstd.1] at hpt
      linarith [hpt.1, hV.1]
    · apply hpN
      refine ⟨⟨?_, ?_⟩, mem_iUnion₂.2 ⟨t, ⟨h0, h1⟩, ?_⟩⟩
      · exact hV.1
      · show 0 ≤ dot p (uvec (π / 2)); rw [ms_dot_uvec_pi_div_two]; exact hH.1
      · rw [qMinus, ms_hallwayMap_congr_jSet hJ ht]; exact hpt

/-- **Theorem 2.4.3** (`thm:monotone-sofa-structure`). A monotone sofa `S` with cap `K = 𝓒(S)` is
`K \ 𝒩(K)`. -/
theorem theorem2_4_3 {S : Set (ℝ × ℝ)} {ω : ℝ} (hS : IsMonotoneSofa S ω) :
    S = capOf S ω \ niche (capOf S ω) ω := by
  obtain ⟨hω, S', hS', hstd', rfl⟩ := hS
  rw [ms_capOf_congr fun _ hs => (lemma2_3_5_supp hω hS' hstd' hs).1]
  exact theorem2_4_2 hω hS' hstd'

/-- **Theorem 2.4.4** (`thm:monotonization-idempotent`), first claim: `𝓘(𝓘(S')) = 𝓘(S')`. -/
theorem theorem2_4_4 {S' : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S' ω) (hstd : IsStandardPosition S' ω) :
    monotonization (monotonization S' ω) ω = monotonization S' ω :=
  ms_monotonization_congr fun _ hs => (lemma2_3_5_supp hω hS hstd hs).1

/-- **Theorem 2.4.4**, second claim: a moving sofa `S` in standard position satisfies `S = 𝓘(S)` if
and only if it is a monotone sofa. -/
theorem theorem2_4_4_iff {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) :
    S = monotonization S ω ↔ IsMonotoneSofa S ω := by
  constructor
  · intro h
    exact ⟨hω, S, hS, hstd, h⟩
  · rintro ⟨-, S', hS', hstd', rfl⟩
    exact (theorem2_4_4 hω hS' hstd').symm

end MovingSofaOptimality
