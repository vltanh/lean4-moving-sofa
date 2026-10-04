module

public import MovingSofaOptimality.Monotone.SupportingHallway

/-!
# Monotone sofas (§2.3)

Proposition 2.3.1 (`pro:standard-position-shape`, also Proposition 1.2.1), Theorem 2.3.2
(`thm:monotonization`), Propositions 2.3.3–2.3.4, Lemma 2.3.5 (`lem:cap-same-support-function`)
and Theorem 2.3.6 (`thm:monotonization-is-connected`).

**Proof of Theorem 2.3.6.** As in the paper, every `p ∈ 𝓘(S)` is joined to the connected set
`S ⊆ 𝓘(S)` by a segment `[p, q] ⊆ 𝓘(S)`, `q ∈ S`, in a direction `u_θ`, `θ ∈ [ω, π/2]`. Such a `q`
exists: otherwise `S` lies in the complement `Y` of the lines `l_θ` through `p`, whose points lie on
the left of every `l_θ` or on the right of every `l_θ`; these two disjoint open sets cover `S` and
meet it in `e_S(ω + π/2)` and `e_S(0)` respectively, which contradicts the connectedness of `S`.
-/

@[expose] public section

open Real Set

namespace MovingSofaOptimality

/-! ### Convexity, closedness and compactness of `𝓒(S)` and `𝓘(S)` -/

/-- The strip `V_ω` is `H₊(ω, 0) ∩ H₋(ω, 1)`. -/
private lemma ms_vStripRot_eq (ω : ℝ) : vStripRot ω = halfPlus ω 0 ∩ halfMinus ω 1 := by
  ext p; rw [ms_mem_vStripRot_iff]; rfl

lemma ms_convex_hStrip : Convex ℝ hStrip := by
  intro x hx y hy a b ha hb hab
  simp only [hStrip, mem_ofPred_eq, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at *
  constructor <;> nlinarith

lemma ms_convex_vStripRot (ω : ℝ) : Convex ℝ (vStripRot ω) := by
  rw [ms_vStripRot_eq]; exact (convex_halfPlus ω 0).inter (convex_halfMinus ω 1)

lemma ms_convex_para (ω : ℝ) : Convex ℝ (para ω) := ms_convex_hStrip.inter (ms_convex_vStripRot ω)

lemma ms_convex_qPlus (S : Set (ℝ × ℝ)) (t : ℝ) : Convex ℝ (qPlus S t) := by
  rw [proposition2_2_2_qPlus]; exact (convex_halfMinus _ _).inter (convex_halfMinus _ _)

lemma ms_isClosed_para (ω : ℝ) : IsClosed (para ω) := by
  have h1 : hStrip = {p : ℝ × ℝ | 0 ≤ p.2} ∩ {p | p.2 ≤ 1} := rfl
  rw [para, h1, ms_vStripRot_eq]
  exact ((isClosed_le continuous_const continuous_snd).inter
    (isClosed_le continuous_snd continuous_const)).inter
    ((isClosed_halfPlus ω 0).inter (isClosed_halfMinus ω 1))

lemma ms_isClosed_qPlus (S : Set (ℝ × ℝ)) (t : ℝ) : IsClosed (qPlus S t) := by
  rw [proposition2_2_2_qPlus]; exact (isClosed_halfMinus _ _).inter (isClosed_halfMinus _ _)

lemma ms_isOpen_qMinus (S : Set (ℝ × ℝ)) (t : ℝ) : IsOpen (qMinus S t) := by
  rw [proposition2_2_2_qMinus]
  exact (isOpen_halfMinusOpen _ _).inter (isOpen_halfMinusOpen _ _)

lemma ms_isClosed_suppHallway (S : Set (ℝ × ℝ)) (t : ℝ) : IsClosed (suppHallway S t) := by
  rw [proposition2_2_2_hallway]; exact (ms_isClosed_qPlus S t).sdiff (ms_isOpen_qMinus S t)

lemma ms_isClosed_capOf (S : Set (ℝ × ℝ)) (ω : ℝ) : IsClosed (capOf S ω) :=
  (ms_isClosed_para ω).inter (isClosed_biInter fun t _ => ms_isClosed_qPlus S t)

lemma ms_isClosed_monotonization (S : Set (ℝ × ℝ)) (ω : ℝ) : IsClosed (monotonization S ω) :=
  (ms_isClosed_para ω).inter (isClosed_biInter fun t _ => ms_isClosed_suppHallway S t)

lemma ms_convex_capOf (S : Set (ℝ × ℝ)) (ω : ℝ) : Convex ℝ (capOf S ω) :=
  (ms_convex_para ω).inter (convex_iInter₂ fun t _ => ms_convex_qPlus S t)

lemma ms_mem_qPlus_iff (S : Set (ℝ × ℝ)) (t : ℝ) (p : ℝ × ℝ) :
    p ∈ qPlus S t ↔ dot p (uvec t) ≤ supp S t ∧ dot p (vvec t) ≤ supp S (t + π / 2) := by
  rw [proposition2_2_2_qPlus]
  simp only [suppHalf, halfMinus, mem_inter_iff, mem_ofPred_eq, uvec_add_pi_div_two]

lemma ms_mem_qMinus_iff (S : Set (ℝ × ℝ)) (t : ℝ) (p : ℝ × ℝ) :
    p ∈ qMinus S t ↔
      dot p (uvec t) < supp S t - 1 ∧ dot p (vvec t) < supp S (t + π / 2) - 1 := by
  rw [proposition2_2_2_qMinus]
  simp only [halfMinusOpen, mem_inter_iff, mem_ofPred_eq, uvec_add_pi_div_two]

/-- A point `(x, y)` of the cap `𝓒(S)` satisfies explicit bounds: `0 ≤ y ≤ 1` (it lies in `H`),
`x ≤ h_S(0)` (it lies in `Q_S⁺(0)`), and `x ≥ -h_S(ω + π/2) / sin ω` (it lies in `Q_S⁺(ω)`, and
`y ≥ 0`). -/
lemma ms_capOf_bounds {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) {p : ℝ × ℝ}
    (hp : p ∈ capOf S ω) :
    -supp S (ω + π / 2) / sin ω ≤ p.1 ∧ p.1 ≤ supp S 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := by
  obtain ⟨⟨⟨h1, h2⟩, -⟩, hq⟩ := hp
  rw [mem_iInter₂] at hq
  have h0 := (ms_mem_qPlus_iff S 0 p).1 (hq 0 ⟨le_rfl, hω.1.le⟩)
  have hω' := (ms_mem_qPlus_iff S ω p).1 (hq ω ⟨hω.1.le, le_rfl⟩)
  rw [dot_uvec_zero] at h0
  have hsin : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω.1 (by linarith [hω.2, pi_pos])
  have hcos : 0 ≤ cos ω := cos_nonneg_of_mem_Icc ⟨by linarith [hω.1, pi_pos], hω.2⟩
  refine ⟨?_, h0.1, h1, h2⟩
  have := hω'.2
  simp only [dot, vvec] at this
  rw [div_le_iff₀ hsin]
  nlinarith

lemma ms_isBounded_capOf {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) :
    Bornology.IsBounded (capOf S ω) :=
  ms_isBounded_of_bounds _ _ _ _ fun _ hp => ms_capOf_bounds hω hp

lemma ms_isCompact_capOf {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) :
    IsCompact (capOf S ω) :=
  Metric.isCompact_of_isClosed_isBounded (ms_isClosed_capOf S ω) (ms_isBounded_capOf hω)

/-- `𝓘(S) ⊆ 𝓒(S)`, as `L_S(t) = Q_S⁺(t) \ Q_S⁻(t)`. -/
lemma ms_monotonization_subset_capOf (S : Set (ℝ × ℝ)) (ω : ℝ) :
    monotonization S ω ⊆ capOf S ω :=
  inter_subset_inter_right _ <| iInter₂_mono fun t _ =>
    (proposition2_2_2_hallway S t).subset.trans sdiff_subset

lemma ms_isCompact_monotonization {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) :
    IsCompact (monotonization S ω) :=
  (ms_isCompact_capOf hω).of_isClosed_subset (ms_isClosed_monotonization S ω)
    (ms_monotonization_subset_capOf S ω)

/-- **Proposition 2.3.1** (`pro:standard-position-shape`), existence: a moving sofa with rotation
angle `ω ∈ (0, π/2]` has a translation in standard position. -/
theorem proposition2_3_1_exists {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) :
    ∃ v : ℝ × ℝ, IsStandardPosition ((fun p => p + v) '' S) ω := by
  have hcpt := ms_isCompact_of_isMovingSofaWithAngle hS
  have hne := hS.2.1.nonempty
  set a := 1 - supp S ω
  set b := 1 - supp S (π / 2)
  -- it suffices to find `v` with `v · u_ω = a` and `v · u_{π/2} = b`
  suffices h : ∃ v : ℝ × ℝ, dot v (uvec ω) = a ∧ v.2 = b by
    obtain ⟨v, h1, h2⟩ := h
    refine ⟨v, ?_, ?_⟩
    · rw [supp_translate S v ω hcpt hne, h1]; ring
    · rw [supp_translate S v (π / 2) hcpt hne, dot_uvec_pi_div_two, h2]; ring
  rcases hω.2.lt_or_eq with hlt | heq
  · have hcos : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [hω.1, pi_pos], hlt⟩
    refine ⟨((a - sin ω * b) / cos ω, b), ?_, rfl⟩
    simp only [dot, uvec]
    field_simp
    ring
  · refine ⟨(0, b), ?_, rfl⟩
    simp [dot, uvec, heq, b, a]

/-- **Proposition 2.3.1** (`pro:standard-position-shape`) (i): for `ω < π/2` the translation in
standard position is unique. -/
theorem proposition2_3_1_unique {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioo 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) {v v' : ℝ × ℝ}
    (hv : IsStandardPosition ((fun p => p + v) '' S) ω)
    (hv' : IsStandardPosition ((fun p => p + v') '' S) ω) : v = v' := by
  have hcpt := ms_isCompact_of_isMovingSofaWithAngle hS
  have hne := hS.2.1.nonempty
  obtain ⟨h1, h2⟩ := hv
  obtain ⟨h1', h2'⟩ := hv'
  rw [supp_translate S _ _ hcpt hne] at h1 h2 h1' h2'
  -- `v` and `v'` have the same coordinates in the directions `u_ω` and `u_{π/2}`
  refine eq_of_dot_uvec_eq (a := ω) (b := π / 2) ?_ (by linarith) (by linarith)
  rw [sin_pi_div_two_sub]
  exact (cos_pos_of_mem_Ioo ⟨by linarith [hω.1, pi_pos], hω.2⟩).ne'

/-- **Proposition 2.3.1** (`pro:standard-position-shape`) (ii): for `ω = π/2` it is unique up to
horizontal translations. -/
theorem proposition2_3_1_unique_horizontal {S : Set (ℝ × ℝ)}
    (hS : IsMovingSofaWithAngle S (π / 2)) {v v' : ℝ × ℝ}
    (hv : IsStandardPosition ((fun p => p + v) '' S) (π / 2))
    (hv' : IsStandardPosition ((fun p => p + v') '' S) (π / 2)) : v.2 = v'.2 := by
  have hcpt := ms_isCompact_of_isMovingSofaWithAngle hS
  have hne := hS.2.1.nonempty
  have h2 := hv.2
  have h2' := hv'.2
  rw [supp_translate S _ _ hcpt hne, dot_uvec_pi_div_two] at h2 h2'
  linarith

/-- **Proposition 2.3.1** (`pro:standard-position-shape`), last claim: a moving sofa in standard
position lies in `P_ω`. -/
theorem proposition2_3_1_subset {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) : S ⊆ para ω := by
  obtain ⟨h1, -, h3⟩ := proposition1_2_2 hω hS hstd
  exact subset_inter h1 h3

/-- **Proposition 2.3.3** (`pro:monotonization-contains-sofa`). `S ⊆ 𝓘(S)`. -/
theorem proposition2_3_3 {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) :
    S ⊆ monotonization S ω := by
  have hcpt := ms_isCompact_of_isMovingSofaWithAngle hS
  have hne := hS.2.1.nonempty
  refine subset_inter (proposition2_3_1_subset hω hS hstd) ?_
  refine subset_iInter₂ fun t ht => ?_
  obtain ⟨c, hc⟩ := (proposition1_2_2 hω hS hstd).2.1 t ht
  exact proposition2_2_3 hcpt hne t c hc

/-- **Proposition 2.3.4** (`pro:cap-contains-sofa`). `S ⊆ 𝓘(S) ⊆ 𝓒(S)`. -/
theorem proposition2_3_4 {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) :
    S ⊆ monotonization S ω ∧ monotonization S ω ⊆ capOf S ω :=
  ⟨proposition2_3_3 hω hS hstd, ms_monotonization_subset_capOf S ω⟩

/-- The cap `𝓒(S)` lies in the supporting half-planes of `S` with normal angles in `J_ω`. -/
lemma ms_capOf_subset_suppHalf {S : Set (ℝ × ℝ)} {ω t : ℝ} (ht : t ∈ jSet ω) {p : ℝ × ℝ}
    (hp : p ∈ capOf S ω) : dot p (uvec t) ≤ supp S t := by
  have hq := hp.2
  rw [mem_iInter₂] at hq
  rcases ht with ht | ht
  · exact ((ms_mem_qPlus_iff S t p).1 (hq t ht)).1
  · have ht' : t - π / 2 ∈ Icc 0 ω := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have := ((ms_mem_qPlus_iff S _ p).1 (hq _ ht')).2
    rwa [sub_add_cancel, ← uvec_add_pi_div_two, sub_add_cancel] at this

/-- **Lemma 2.3.5** (`lem:cap-same-support-function`). The support functions of `S`, `𝓘(S)` and
`𝓒(S)` agree on `J_ω`. -/
theorem lemma2_3_5_supp {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) {t : ℝ} (ht : t ∈ jSet ω) :
    supp (monotonization S ω) t = supp S t ∧ supp (capOf S ω) t = supp S t := by
  have hne := hS.2.1.nonempty
  obtain ⟨h1, h2⟩ := proposition2_3_4 hω hS hstd
  have hC : supp (capOf S ω) t ≤ supp S t :=
    supp_le_of_forall ((hne.mono h1).mono h2) fun p hp => ms_capOf_subset_suppHalf ht hp
  have hSI : supp S t ≤ supp (monotonization S ω) t :=
    supp_mono h1 hne (ms_isCompact_monotonization hω) t
  have hIC : supp (monotonization S ω) t ≤ supp (capOf S ω) t :=
    supp_mono h2 (hne.mono h1) (ms_isCompact_capOf hω) t
  exact ⟨le_antisymm (hIC.trans hC) hSI, le_antisymm hC (hSI.trans hIC)⟩

/-- `f_{X,t}` depends only on `h_X(t)` and `h_X(t + π/2)`. -/
lemma ms_hallwayMap_congr {X Y : Set (ℝ × ℝ)} {t : ℝ} (h1 : supp X t = supp Y t)
    (h2 : supp X (t + π / 2) = supp Y (t + π / 2)) : hallwayMap X t = hallwayMap Y t := by
  funext p; simp only [hallwayMap, h1, h2]

lemma ms_mem_jSet_left {ω t : ℝ} (ht : t ∈ Icc 0 ω) : t ∈ jSet ω := Or.inl ht

lemma ms_mem_jSet_right {ω t : ℝ} (ht : t ∈ Icc 0 ω) : t + π / 2 ∈ jSet ω :=
  Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- Two sets whose support functions agree on `J_ω` have the same supporting hallways
`L(t)`, `t ∈ [0, ω]`. -/
lemma ms_hallwayMap_congr_jSet {X Y : Set (ℝ × ℝ)} {ω t : ℝ}
    (h : ∀ s ∈ jSet ω, supp X s = supp Y s) (ht : t ∈ Icc 0 ω) :
    hallwayMap X t = hallwayMap Y t :=
  ms_hallwayMap_congr (h t (ms_mem_jSet_left ht)) (h _ (ms_mem_jSet_right ht))

/-- **Lemma 2.3.5** (`lem:cap-same-support-function`), consequence: the supporting hallways of `S`,
`𝓘(S)` and `𝓒(S)` agree for `t ∈ [0, ω]`. -/
theorem lemma2_3_5_hallway {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) {t : ℝ} (ht : t ∈ Icc 0 ω) :
    suppHallway (monotonization S ω) t = suppHallway S t ∧
      suppHallway (capOf S ω) t = suppHallway S t := by
  refine ⟨?_, ?_⟩
  · rw [suppHallway, suppHallway,
      ms_hallwayMap_congr_jSet (fun s hs => (lemma2_3_5_supp hω hS hstd hs).1) ht]
  · rw [suppHallway, suppHallway,
      ms_hallwayMap_congr_jSet (fun s hs => (lemma2_3_5_supp hω hS hstd hs).2) ht]

/-- Moving a point by `-l u_θ`, `l ≥ 0`, with `θ - t ∈ [0, π/2]`, decreases both of its
coordinates in the frame `(u_t, v_t)`. -/
private lemma ms_dot_sub_smul_uvec_le {t θ l : ℝ} (hθt : θ - t ∈ Icc 0 (π / 2)) (hl : 0 ≤ l)
    (z : ℝ × ℝ) : dot (z - l • uvec θ) (uvec t) ≤ dot z (uvec t) ∧
      dot (z - l • uvec θ) (vvec t) ≤ dot z (vvec t) := by
  have hc : 0 ≤ cos (θ - t) := cos_nonneg_of_mem_Icc ⟨by linarith [hθt.1, pi_pos], hθt.2⟩
  have hs : 0 ≤ sin (θ - t) := sin_nonneg_of_nonneg_of_le_pi hθt.1 (by linarith [hθt.2, pi_pos])
  rw [dot_sub_left, dot_sub_left, dot_smul_left, dot_smul_left, dot_uvec_uvec, dot_uvec_vvec']
  exact ⟨sub_le_self _ (mul_nonneg hl hc), sub_le_self _ (mul_nonneg hl hs)⟩

/-- Each `Q_S⁻(t)` is closed in the direction `-u_θ` when `θ - t ∈ [0, π/2]`. -/
lemma ms_qMinus_sub {S : Set (ℝ × ℝ)} {t θ l : ℝ} {z : ℝ × ℝ} (hθt : θ - t ∈ Icc 0 (π / 2))
    (hl : 0 ≤ l) (hz : z ∈ qMinus S t) : z - l • uvec θ ∈ qMinus S t := by
  rw [ms_mem_qMinus_iff] at hz ⊢
  have h := ms_dot_sub_smul_uvec_le hθt hl z
  exact ⟨h.1.trans_lt hz.1, h.2.trans_lt hz.2⟩

/-- Each `Q_S⁺(t)` is closed in the direction `-u_θ` when `θ - t ∈ [0, π/2]`. -/
lemma ms_qPlus_sub {S : Set (ℝ × ℝ)} {t θ l : ℝ} {z : ℝ × ℝ} (hθt : θ - t ∈ Icc 0 (π / 2))
    (hl : 0 ≤ l) (hz : z ∈ qPlus S t) : z - l • uvec θ ∈ qPlus S t := by
  rw [ms_mem_qPlus_iff] at hz ⊢
  have h := ms_dot_sub_smul_uvec_le hθt hl z
  exact ⟨h.1.trans hz.1, h.2.trans hz.2⟩

/-- The key step of Theorem 2.3.6: if two points `p, q` of `𝓘(S)` lie on a line with direction
`u_θ`, `θ ∈ [ω, π/2]`, then the segment `[p, q]` lies in `𝓘(S)`. Indeed `𝓘(S) = 𝓒(S) \ X` with
`𝓒(S)` convex and `X = ⋃_{t ∈ [0, ω]} Q_S⁻(t)` closed in the direction `-u_θ`. -/
lemma ms_segment_subset_monotonization {S : Set (ℝ × ℝ)} {ω θ : ℝ} (hθ : θ ∈ Icc ω (π / 2))
    {p q : ℝ × ℝ} (hp : p ∈ monotonization S ω) (hq : q ∈ monotonization S ω)
    (hpq : dot (q - p) (vvec θ) = 0) : segment ℝ p q ⊆ monotonization S ω := by
  set μ := dot (q - p) (uvec θ) with hμ
  have hqp : q = p + μ • uvec θ := by
    have := eq_dot_uvec_smul_add (q - p) θ
    rw [hpq, zero_smul, add_zero, ← hμ] at this
    rw [← this]; abel
  intro z hz
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  refine ⟨(ms_convex_para ω).segment_subset hp.1 hq.1 ⟨a, b, ha, hb, hab, rfl⟩, ?_⟩
  rw [mem_iInter₂]
  intro t ht
  have hpt := mem_iInter₂.1 hp.2 t ht
  have hqt := mem_iInter₂.1 hq.2 t ht
  rw [proposition2_2_2_hallway] at hpt hqt ⊢
  refine ⟨(ms_convex_qPlus S t).segment_subset hpt.1 hqt.1 ⟨a, b, ha, hb, hab, rfl⟩, fun hz => ?_⟩
  have hθt : θ - t ∈ Icc 0 (π / 2) := ⟨by linarith [hθ.1, ht.2], by linarith [hθ.2, ht.1]⟩
  obtain rfl : b = 1 - a := by linarith
  rcases le_total 0 μ with hμ0 | hμ0
  · -- `p` lies below `z` in the direction `u_θ`
    apply hpt.2
    have := ms_qMinus_sub hθt (mul_nonneg hb hμ0) hz
    convert this using 1
    rw [hqp]; ext <;> simp <;> ring
  · -- `q` lies below `z` in the direction `u_θ`
    apply hqt.2
    have := ms_qMinus_sub hθt (mul_nonneg ha (neg_nonneg.2 hμ0)) hz
    convert this using 1
    rw [hqp]; ext <;> simp <;> ring

/-- **Theorem 2.3.6** (`thm:monotonization-is-connected`). `𝓘(S)` is connected. -/
theorem theorem2_3_6 {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) :
    IsConnected (monotonization S ω) := by
  have hcpt := ms_isCompact_of_isMovingSofaWithAngle hS
  have hconn := hS.2.1
  have hsub := proposition2_3_3 hω hS hstd
  obtain ⟨x₀, hx₀⟩ := hconn.nonempty
  refine ⟨⟨x₀, hsub hx₀⟩, isPreconnected_of_forall x₀ fun p hp => ?_⟩
  -- `h_{𝓘(S)} = h_S` on `J_ω` (Lemma 2.3.5), so `p ∈ 𝓘(S)` lies on the left of `l_S(0)` and on
  -- the right of `l_S(ω + π/2)`
  have hI := ms_isCompact_monotonization (S := S) hω
  have hp0 : dot p (uvec 0) ≤ supp S 0 := by
    rw [← (lemma2_3_5_supp hω hS hstd (ms_mem_jSet_left ⟨le_rfl, hω.1.le⟩)).1]
    exact dot_le_supp hI hp 0
  have hpω : dot p (uvec (ω + π / 2)) ≤ supp S (ω + π / 2) := by
    rw [← (lemma2_3_5_supp hω hS hstd (ms_mem_jSet_right ⟨hω.1.le, le_rfl⟩)).1]
    exact dot_le_supp hI hp _
  -- some line `l_θ` through `p` in the direction `u_θ`, `θ ∈ [ω, π/2]`, meets `S`
  obtain ⟨q, hq, θ, hθ, hz⟩ : ∃ q ∈ S, ∃ θ ∈ Icc ω (π / 2), dot (q - p) (vvec θ) = 0 := by
    by_contra hne
    push Not at hne
    -- then `S` lies in `Y = ℝ² \ ⋃_θ l_θ`; by the intermediate value theorem in `θ`, every point
    -- of `Y` lies on the left of both `l_ω` and `l_{π/2}` (in `Y_L`) or on the right of both (in
    -- `Y_R`)
    have hY : ∀ z ∈ S, (0 < dot (z - p) (vvec ω) ∧ 0 < dot (z - p) (vvec (π / 2))) ∨
        (dot (z - p) (vvec ω) < 0 ∧ dot (z - p) (vvec (π / 2)) < 0) := by
      intro z hz
      have hcθ : ContinuousOn (fun θ => dot (z - p) (vvec θ)) (uIcc ω (π / 2)) := by
        simp only [dot, vvec]; fun_prop
      have h0 : (0 : ℝ) ∉ uIcc (dot (z - p) (vvec ω)) (dot (z - p) (vvec (π / 2))) := fun h => by
        obtain ⟨θ, hθ, hθ0⟩ := intermediate_value_uIcc hcθ h
        rw [uIcc_of_le hω.2] at hθ
        exact hne z hz θ hθ hθ0
      rw [mem_uIcc] at h0
      rcases (hne z hz ω ⟨le_rfl, hω.2⟩).lt_or_gt with ha | ha <;>
        rcases (hne z hz (π / 2) ⟨hω.2, le_rfl⟩).lt_or_gt with hb | hb
      · exact Or.inr ⟨ha, hb⟩
      · exact absurd (Or.inl ⟨ha.le, hb.le⟩) h0
      · exact absurd (Or.inr ⟨hb.le, ha.le⟩) h0
      · exact Or.inl ⟨ha, hb⟩
    have hcont : ∀ θ, Continuous fun z : ℝ × ℝ => dot (z - p) (vvec θ) := fun θ =>
      (continuous_dot _).comp (continuous_sub_right p)
    -- a point `b ∈ e_S(ω + π/2)` lies on the left of `l_ω`, so in `Y_L`; a point `a ∈ e_S(0)` lies
    -- on the right of `l_{π/2}`, so in `Y_R`
    obtain ⟨b, hb, hb1⟩ := exists_dot_eq_supp hcpt ⟨x₀, hx₀⟩ (ω + π / 2)
    obtain ⟨a, ha, ha1⟩ := exists_dot_eq_supp hcpt ⟨x₀, hx₀⟩ 0
    have hbL : b ∈ S ∩ {z | 0 < dot (z - p) (vvec ω) ∧ 0 < dot (z - p) (vvec (π / 2))} := by
      refine ⟨hb, (hY b hb).resolve_right fun h => ?_⟩
      rw [dot_sub_left, ← uvec_add_pi_div_two] at h
      linarith [h.1]
    have haR : a ∈ S ∩ {z | dot (z - p) (vvec ω) < 0 ∧ dot (z - p) (vvec (π / 2)) < 0} := by
      refine ⟨ha, (hY a ha).resolve_left fun h => ?_⟩
      rw [dot_uvec_zero] at ha1 hp0
      have h2 := h.2
      simp only [dot, vvec, sin_pi_div_two, cos_pi_div_two, Prod.fst_sub, Prod.snd_sub] at h2
      linarith
    -- `S` is connected, but meets the disjoint open sets `Y_L` and `Y_R`, which cover it
    obtain ⟨z, -, hzL, hzR⟩ := hconn.isPreconnected _ _
      ((isOpen_lt continuous_const (hcont ω)).inter (isOpen_lt continuous_const (hcont _)))
      ((isOpen_lt (hcont ω) continuous_const).inter (isOpen_lt (hcont _) continuous_const))
      hY ⟨b, hbL⟩ ⟨a, haR⟩
    exact absurd hzL.1 (not_lt.2 hzR.1.le)
  -- the segment `s_θ` from `p` to `q ∈ S ∩ l_θ` lies in `𝓘(S)`, which is therefore connected
  refine ⟨S ∪ segment ℝ p q,
    union_subset hsub (ms_segment_subset_monotonization hθ hp (hsub hq) hz), Or.inl hx₀,
    Or.inr (left_mem_segment ℝ p q), ?_⟩
  exact IsPreconnected.union q hq (right_mem_segment ℝ p q) hconn.isPreconnected
    (convex_segment p q).isPreconnected

/-- The movement of `ms_isMovement_monotonization` at angle `t`, applied to `p`: its coordinates
are those of `p` relative to the supporting hallway `L_S(t)`. -/
lemma ms_movement_eq (S : Set (ℝ × ℝ)) (t : ℝ) (p : ℝ × ℝ) :
    rot (-t) p + -rot (-t) ((supp S t - 1) • uvec t + (supp S (t + π / 2) - 1) • vvec t) =
      (dot p (uvec t) - (supp S t - 1), dot p (vvec t) - (supp S (t + π / 2) - 1)) := by
  ext
  · simp only [Prod.fst_add, Prod.fst_neg, ms_rot_neg_fst, dot_add_left, dot_smul_left,
      dot_uvec_self, dot_vvec_uvec]; ring
  · simp only [Prod.snd_add, Prod.snd_neg, ms_rot_neg_snd, dot_add_left, dot_smul_left,
      dot_vvec_self, dot_uvec_vvec]; ring

/-- The movement of `𝓘(S)` given by the supporting hallways `L_S(sω)`, `s ∈ [0, 1]`, seen from
the hallway. -/
lemma ms_isMovement_monotonization {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) :
    IsMovement (monotonization S ω) ω (fun s => -(s * ω))
      (fun s => -rot (-(s * ω)) ((supp S (s * ω) - 1) • uvec (s * ω) +
        (supp S (s * ω + π / 2) - 1) • vvec (s * ω))) := by
  have hcpt := ms_isCompact_of_isMovingSofaWithAngle hS
  have hsupp := continuous_supp hcpt
  refine ⟨by fun_prop, ?_, by simp, by simp, ?_, ?_, ?_⟩
  · have : Continuous fun s : ℝ => -rot (-(s * ω)) ((supp S (s * ω) - 1) • uvec (s * ω) +
        (supp S (s * ω + π / 2) - 1) • vvec (s * ω)) := by
      simp only [rot, uvec, vvec]; fun_prop
    exact this.continuousOn
  · intro p hp
    have hq := (ms_mem_qPlus_iff S 0 p).1
      (mem_iInter₂.1 (ms_monotonization_subset_capOf S ω hp).2 0 ⟨le_rfl, hω.1.le⟩)
    have hH := hp.1.1
    rw [ms_movement_eq]
    simp only [zero_mul, zero_add, hstd.2, dot_uvec_zero] at hq ⊢
    rw [ms_mem_hStrip_iff] at hH
    have h1 : dot p (vvec 0) = p.2 := by simp [dot, vvec]
    refine ⟨by linarith [hq.1], ?_, ?_⟩ <;> simp only [h1] <;> linarith [hH.1, hH.2]
  · intro s hs p hp
    have hst : s * ω ∈ Icc 0 ω :=
      ⟨mul_nonneg hs.1 hω.1.le, by nlinarith [hs.2, hω.1]⟩
    have := mem_iInter₂.1 hp.2 (s * ω) hst
    rw [suppHallway, ms_mem_hallwayMap_image] at this
    rwa [ms_movement_eq]
  · intro p hp
    have hq := (ms_mem_qPlus_iff S ω p).1
      (mem_iInter₂.1 (ms_monotonization_subset_capOf S ω hp).2 ω ⟨hω.1.le, le_rfl⟩)
    have hV := (ms_mem_vStripRot_iff ω p).1 hp.1.2
    rw [ms_movement_eq]
    simp only [one_mul, hstd.1]
    refine ⟨by linarith [hV.1], by linarith [hV.2], by linarith [hq.2]⟩

/-- **Theorem 2.3.2** (`thm:monotonization`). For a moving sofa `S` with rotation angle
`ω ∈ (0, π/2]` in standard position, `𝓘(S)` is a moving sofa with the same rotation angle, in
standard position, containing `S`. -/
theorem theorem2_3_2 {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) :
    IsMovingSofaWithAngle (monotonization S ω) ω ∧ IsStandardPosition (monotonization S ω) ω ∧
      S ⊆ monotonization S ω := by
  refine ⟨⟨ms_isClosed_monotonization S ω, theorem2_3_6 hω hS hstd, _, _,
    ms_isMovement_monotonization hω hS hstd⟩, ⟨?_, ?_⟩, proposition2_3_3 hω hS hstd⟩
  · rw [(lemma2_3_5_supp hω hS hstd (Or.inl ⟨hω.1.le, le_rfl⟩)).1, hstd.1]
  · rw [(lemma2_3_5_supp hω hS hstd (Or.inr ⟨le_rfl, by linarith [hω.1]⟩)).1, hstd.2]

/-- A monotone sofa with rotation angle `ω` is a moving sofa with rotation angle `ω`. -/
theorem IsMonotoneSofa.isMovingSofaWithAngle {S : Set (ℝ × ℝ)} {ω : ℝ}
    (hS : IsMonotoneSofa S ω) : IsMovingSofaWithAngle S ω := by
  obtain ⟨hω, T, hT, hstd, rfl⟩ := hS
  exact (theorem2_3_2 hω hT hstd).1

/-- A monotone sofa with rotation angle `ω` is in standard position. -/
theorem IsMonotoneSofa.isStandardPosition {S : Set (ℝ × ℝ)} {ω : ℝ}
    (hS : IsMonotoneSofa S ω) : IsStandardPosition S ω := by
  obtain ⟨hω, T, hT, hstd, rfl⟩ := hS
  exact (theorem2_3_2 hω hT hstd).2.1

end MovingSofaOptimality
