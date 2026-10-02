module

public import MovingSofa.Monotone.SupportingHallway

/-!
# Monotone sofas (§2.3)

Proposition 2.3.1 (`pro:standard-position-shape`, also Proposition 1.2.1), Theorem 2.3.2
(`thm:monotonization`), Propositions 2.3.3–2.3.4, Lemma 2.3.5 (`lem:cap-same-support-function`) and
Theorem 2.3.6 (`thm:monotonization-is-connected`).

**Proof of Theorem 2.3.6.** As in the paper, every `p ∈ 𝓘(S)` is joined to the connected set
`S ⊆ 𝓘(S)` by a segment `[p, q] ⊆ 𝓘(S)`, `q ∈ S`, in a direction `u_θ`, `θ ∈ [ω, π/2]`. The paper's
contradiction argument (the lines `l_θ` through `p` separating `S`) is replaced by the intermediate
value theorem for the continuous function `(q, θ) ↦ (q - p) · v_θ` on the connected set
`S × [ω, π/2]`: it is `≤ 0` at `(a, π/2)` for `a ∈ e_S(0)` and `≥ 0` at `(b, ω)` for
`b ∈ e_S(ω + π/2)`, so it vanishes somewhere.
-/

@[expose] public section

open Real Set

namespace MovingSofa

/-! ### Convexity, closedness and compactness of `𝓒(S)` and `𝓘(S)` -/

lemma ms_convex_halfMinus (t h : ℝ) : Convex ℝ (halfMinus t h) := by
  intro x hx y hy a b ha hb hab
  simp only [halfMinus, mem_ofPred_eq, dot_add_left, dot_smul_left] at *
  have : a * h + b * h = h := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

lemma ms_convex_hStrip : Convex ℝ hStrip := by
  intro x hx y hy a b ha hb hab
  simp only [hStrip, mem_ofPred_eq, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at *
  constructor <;> nlinarith

lemma ms_convex_vStripRot (ω : ℝ) : Convex ℝ (vStripRot ω) := by
  intro x hx y hy a b ha hb hab
  rw [ms_mem_vStripRot_iff] at *
  simp only [dot_add_left, dot_smul_left]
  constructor <;> nlinarith

lemma ms_convex_para (ω : ℝ) : Convex ℝ (para ω) := ms_convex_hStrip.inter (ms_convex_vStripRot ω)

lemma ms_convex_qPlus (S : Set (ℝ × ℝ)) (t : ℝ) : Convex ℝ (qPlus S t) := by
  rw [proposition2_2_2_qPlus]; exact (ms_convex_halfMinus _ _).inter (ms_convex_halfMinus _ _)

lemma ms_continuous_dot (v : ℝ × ℝ) : Continuous fun p : ℝ × ℝ => dot p v := by
  unfold dot; fun_prop

lemma ms_isClosed_halfMinus (t h : ℝ) : IsClosed (halfMinus t h) :=
  isClosed_le (ms_continuous_dot _) continuous_const

lemma ms_isOpen_halfMinusOpen (t h : ℝ) : IsOpen (halfMinusOpen t h) :=
  isOpen_lt (ms_continuous_dot _) continuous_const

lemma ms_isClosed_para (ω : ℝ) : IsClosed (para ω) := by
  have h1 : hStrip = {p : ℝ × ℝ | 0 ≤ p.2} ∩ {p | p.2 ≤ 1} := rfl
  have h2 : vStripRot ω = {p : ℝ × ℝ | 0 ≤ dot p (uvec ω)} ∩ {p | dot p (uvec ω) ≤ 1} := by
    ext p; rw [ms_mem_vStripRot_iff]; rfl
  rw [para, h1, h2]
  exact ((isClosed_le continuous_const continuous_snd).inter
    (isClosed_le continuous_snd continuous_const)).inter
    ((isClosed_le continuous_const (ms_continuous_dot _)).inter
    (isClosed_le (ms_continuous_dot _) continuous_const))

lemma ms_isClosed_qPlus (S : Set (ℝ × ℝ)) (t : ℝ) : IsClosed (qPlus S t) := by
  rw [proposition2_2_2_qPlus]; exact (ms_isClosed_halfMinus _ _).inter (ms_isClosed_halfMinus _ _)

lemma ms_isOpen_qMinus (S : Set (ℝ × ℝ)) (t : ℝ) : IsOpen (qMinus S t) := by
  rw [proposition2_2_2_qMinus]
  exact (ms_isOpen_halfMinusOpen _ _).inter (ms_isOpen_halfMinusOpen _ _)

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
    p ∈ qMinus S t ↔ dot p (uvec t) < supp S t - 1 ∧ dot p (vvec t) < supp S (t + π / 2) - 1 := by
  rw [proposition2_2_2_qMinus]
  simp only [halfMinusOpen, mem_inter_iff, mem_ofPred_eq, uvec_add_pi_div_two]

/-- A point of the cap `𝓒(S)` satisfies explicit bounds. -/
lemma ms_capOf_bounds {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) {p : ℝ × ℝ}
    (hp : p ∈ capOf S ω) :
    -supp S (ω + π / 2) / sin ω ≤ p.1 ∧ p.1 ≤ supp S 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := by
  obtain ⟨⟨⟨h1, h2⟩, -⟩, hq⟩ := hp
  rw [mem_iInter₂] at hq
  have h0 := (ms_mem_qPlus_iff S 0 p).1 (hq 0 ⟨le_rfl, hω.1.le⟩)
  have hω' := (ms_mem_qPlus_iff S ω p).1 (hq ω ⟨hω.1.le, le_rfl⟩)
  rw [ms_dot_uvec_zero] at h0
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

lemma ms_monotonization_subset_capOf (S : Set (ℝ × ℝ)) (ω : ℝ) :
    monotonization S ω ⊆ capOf S ω := by
  rintro p ⟨hp, hq⟩
  refine ⟨hp, ?_⟩
  rw [mem_iInter₂] at hq ⊢
  intro t ht
  have := hq t ht
  rw [proposition2_2_2_hallway] at this
  exact this.1

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
    · rw [supp_translate S v (π / 2) hcpt hne, ms_dot_uvec_pi_div_two, h2]; ring
  rcases hω.2.lt_or_eq with hlt | heq
  · have hcos : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [hω.1, pi_pos], hlt⟩
    refine ⟨((a - sin ω * b) / cos ω, b), ?_, rfl⟩
    simp only [dot, uvec]
    field_simp
    ring
  · refine ⟨(0, b), ?_, rfl⟩
    simp [dot, uvec, heq, b, a]

/-- **Proposition 2.3.1** (i): for `ω < π/2` the translation in standard position is unique. -/
theorem proposition2_3_1_unique {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioo 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) {v v' : ℝ × ℝ}
    (hv : IsStandardPosition ((fun p => p + v) '' S) ω)
    (hv' : IsStandardPosition ((fun p => p + v') '' S) ω) : v = v' := by
  have hcpt := ms_isCompact_of_isMovingSofaWithAngle hS
  have hne := hS.2.1.nonempty
  obtain ⟨h1, h2⟩ := hv
  obtain ⟨h1', h2'⟩ := hv'
  rw [supp_translate S _ _ hcpt hne] at h1 h2 h1' h2'
  rw [ms_dot_uvec_pi_div_two] at h2 h2'
  have hcos : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [hω.1, pi_pos], hω.2⟩
  have hy : v.2 = v'.2 := by linarith
  simp only [dot, uvec] at h1 h1'
  have hx : v.1 = v'.1 := by
    have : cos ω * (v.1 - v'.1) = 0 := by rw [hy] at h1; linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hcos.ne'
    · linarith
  exact Prod.ext hx hy

/-- **Proposition 2.3.1** (ii): for `ω = π/2` it is unique up to horizontal translations. -/
theorem proposition2_3_1_unique_horizontal {S : Set (ℝ × ℝ)}
    (hS : IsMovingSofaWithAngle S (π / 2)) {v v' : ℝ × ℝ}
    (hv : IsStandardPosition ((fun p => p + v) '' S) (π / 2))
    (hv' : IsStandardPosition ((fun p => p + v') '' S) (π / 2)) : v.2 = v'.2 := by
  have hcpt := ms_isCompact_of_isMovingSofaWithAngle hS
  have hne := hS.2.1.nonempty
  have h2 := hv.2
  have h2' := hv'.2
  rw [supp_translate S _ _ hcpt hne, ms_dot_uvec_pi_div_two] at h2 h2'
  linarith

/-- **Proposition 2.3.1**, last claim: a moving sofa in standard position lies in `P_ω`. -/
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
    ms_supp_le_of_forall ((hne.mono h1).mono h2) fun p hp => ms_capOf_subset_suppHalf ht hp
  have hSI : supp S t ≤ supp (monotonization S ω) t :=
    supp_mono h1 hne (ms_isCompact_monotonization hω) t
  have hIC : supp (monotonization S ω) t ≤ supp (capOf S ω) t :=
    supp_mono h2 (hne.mono h1) (ms_isCompact_capOf hω) t
  exact ⟨le_antisymm (hIC.trans hC) hSI, le_antisymm hC (hSI.trans hIC)⟩

lemma ms_hallwayMap_congr {X Y : Set (ℝ × ℝ)} {t : ℝ} (h1 : supp X t = supp Y t)
    (h2 : supp X (t + π / 2) = supp Y (t + π / 2)) : hallwayMap X t = hallwayMap Y t := by
  funext p; simp only [hallwayMap, h1, h2]

lemma ms_mem_jSet_left {ω t : ℝ} (ht : t ∈ Icc 0 ω) : t ∈ jSet ω := Or.inl ht

lemma ms_mem_jSet_right {ω t : ℝ} (ht : t ∈ Icc 0 ω) : t + π / 2 ∈ jSet ω :=
  Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩

lemma ms_hallwayMap_congr_jSet {X Y : Set (ℝ × ℝ)} {ω t : ℝ}
    (h : ∀ s ∈ jSet ω, supp X s = supp Y s) (ht : t ∈ Icc 0 ω) :
    hallwayMap X t = hallwayMap Y t :=
  ms_hallwayMap_congr (h t (ms_mem_jSet_left ht)) (h _ (ms_mem_jSet_right ht))

/-- **Lemma 2.3.5**, consequence: the supporting hallways of `S`, `𝓘(S)` and `𝓒(S)` agree for
`t ∈ [0, ω]`. -/
theorem lemma2_3_5_hallway {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) {t : ℝ} (ht : t ∈ Icc 0 ω) :
    suppHallway (monotonization S ω) t = suppHallway S t ∧
      suppHallway (capOf S ω) t = suppHallway S t := by
  refine ⟨?_, ?_⟩
  · rw [suppHallway, suppHallway,
      ms_hallwayMap_congr_jSet (fun s hs => (lemma2_3_5_supp hω hS hstd hs).1) ht]
  · rw [suppHallway, suppHallway,
      ms_hallwayMap_congr_jSet (fun s hs => (lemma2_3_5_supp hω hS hstd hs).2) ht]

/-- Each `Q_S⁻(t)` is closed in the direction `-u_θ` when `θ - t ∈ [0, π/2]`. -/
lemma ms_qMinus_sub {S : Set (ℝ × ℝ)} {t θ l : ℝ} {z : ℝ × ℝ} (hθt : θ - t ∈ Icc 0 (π / 2))
    (hl : 0 ≤ l) (hz : z ∈ qMinus S t) : z - l • uvec θ ∈ qMinus S t := by
  rw [ms_mem_qMinus_iff] at hz ⊢
  have hc : 0 ≤ cos (θ - t) := cos_nonneg_of_mem_Icc ⟨by linarith [hθt.1, pi_pos], hθt.2⟩
  have hs : 0 ≤ sin (θ - t) := sin_nonneg_of_nonneg_of_le_pi hθt.1 (by linarith [hθt.2, pi_pos])
  rw [dot_sub_left, dot_sub_left, dot_smul_left, dot_smul_left, dot_uvec_uvec, dot_uvec_vvec']
  constructor <;> nlinarith [hz.1, hz.2, mul_nonneg hl hc, mul_nonneg hl hs]

/-- Each `Q_S⁺(t)` is closed in the direction `-u_θ` when `θ - t ∈ [0, π/2]`. -/
lemma ms_qPlus_sub {S : Set (ℝ × ℝ)} {t θ l : ℝ} {z : ℝ × ℝ} (hθt : θ - t ∈ Icc 0 (π / 2))
    (hl : 0 ≤ l) (hz : z ∈ qPlus S t) : z - l • uvec θ ∈ qPlus S t := by
  rw [ms_mem_qPlus_iff] at hz ⊢
  have hc : 0 ≤ cos (θ - t) := cos_nonneg_of_mem_Icc ⟨by linarith [hθt.1, pi_pos], hθt.2⟩
  have hs : 0 ≤ sin (θ - t) := sin_nonneg_of_nonneg_of_le_pi hθt.1 (by linarith [hθt.2, pi_pos])
  rw [dot_sub_left, dot_sub_left, dot_smul_left, dot_smul_left, dot_uvec_uvec, dot_uvec_vvec']
  constructor <;> nlinarith [hz.1, hz.2, mul_nonneg hl hc, mul_nonneg hl hs]

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
  -- points `a ∈ e_S(0)` and `b ∈ e_S(ω + π/2)`
  obtain ⟨a, ha, ha1⟩ := exists_dot_eq_supp hcpt ⟨x₀, hx₀⟩ 0
  obtain ⟨b, hb, hb1⟩ := exists_dot_eq_supp hcpt ⟨x₀, hx₀⟩ (ω + π / 2)
  have hpq := mem_iInter₂.1 (ms_monotonization_subset_capOf S ω hp).2
  have hp0 := (ms_mem_qPlus_iff S 0 p).1 (hpq 0 ⟨le_rfl, hω.1.le⟩)
  have hpω := (ms_mem_qPlus_iff S ω p).1 (hpq ω ⟨hω.1.le, le_rfl⟩)
  -- the signed distance of `q ∈ S` to the line through `p` with direction `u_θ`
  set F : (ℝ × ℝ) × ℝ → ℝ := fun z => dot (z.1 - p) (vvec z.2) with hF
  have hFc : Continuous F := by simp only [hF, dot, vvec]; fun_prop
  have hpre : IsPreconnected (S ×ˢ Icc ω (π / 2)) := hconn.isPreconnected.prod isPreconnected_Icc
  -- `a` is on the right of the vertical line through `p`
  have hFa : F (a, π / 2) ≤ 0 := by
    rw [ms_dot_uvec_zero] at ha1 hp0
    simp only [hF, dot, vvec, sin_pi_div_two, cos_pi_div_two, Prod.fst_sub, Prod.snd_sub]
    linarith [hp0.1]
  -- `b` is on the left of the line through `p` with direction `u_ω`
  have hFb : 0 ≤ F (b, ω) := by
    rw [uvec_add_pi_div_two] at hb1
    simp only [hF, dot_sub_left]
    linarith [hpω.2]
  obtain ⟨⟨q, θ⟩, ⟨hq, hθ⟩, hz⟩ := hpre.intermediate_value (a := (a, π / 2)) (b := (b, ω))
    ⟨ha, hω.2, le_rfl⟩ ⟨hb, le_rfl, hω.2⟩ hFc.continuousOn ⟨hFa, hFb⟩
  refine ⟨S ∪ segment ℝ p q,
    union_subset hsub (ms_segment_subset_monotonization hθ hp (hsub hq) hz), Or.inl hx₀,
    Or.inr (left_mem_segment ℝ p q), ?_⟩
  exact IsPreconnected.union q hq (right_mem_segment ℝ p q) hconn.isPreconnected
    (convex_segment p q).isPreconnected

lemma ms_movement_eq (S : Set (ℝ × ℝ)) (t : ℝ) (p : ℝ × ℝ) :
    rot (-t) p + -rot (-t) ((supp S t - 1) • uvec t + (supp S (t + π / 2) - 1) • vvec t) =
      (dot p (uvec t) - (supp S t - 1), dot p (vvec t) - (supp S (t + π / 2) - 1)) := by
  ext
  · simp only [Prod.fst_add, Prod.fst_neg, ms_rot_neg_fst, dot_add_left, dot_smul_left,
      dot_uvec_self, dot_vvec_uvec]; ring
  · simp only [Prod.snd_add, Prod.snd_neg, ms_rot_neg_snd, dot_add_left, dot_smul_left,
      dot_vvec_self, dot_uvec_vvec]; ring

/-- The movement of `𝓘(S)` given by the supporting hallways `L_S(sω)`, `s ∈ [0, 1]`, seen from the
hallway. -/
lemma ms_isMovement_monotonization {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) :
    IsMovement (monotonization S ω) ω (fun s => -(s * ω))
      (fun s => -rot (-(s * ω)) ((supp S (s * ω) - 1) • uvec (s * ω) +
        (supp S (s * ω + π / 2) - 1) • vvec (s * ω))) := by
  have hcpt := ms_isCompact_of_isMovingSofaWithAngle hS
  have hsupp := continuous_supp hcpt hS.2.1.nonempty
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
    simp only [zero_mul, zero_add, hstd.2, ms_dot_uvec_zero] at hq ⊢
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

end MovingSofa
