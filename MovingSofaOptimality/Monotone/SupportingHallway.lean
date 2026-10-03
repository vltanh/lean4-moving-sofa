module

public import MovingSofaOptimality.Monotone.CapDefs

/-!
# The supporting hallway (§2.2) and the common subset of a moving sofa (§1.2)

Propositions 2.2.1–2.2.3, Proposition 1.2.2 (`pro:moving-sofa-common-subset`), and the
boundedness of moving sofas.

**Boundedness of moving sofas** (not in the paper, which takes areas of moving sofas). At time `0`
the sofa lies in a translate of `H_L`, so it is bounded above in `x` and bounded in `y`; it remains
to bound `x` from below. If the final angle `θ(1)` is `0`, the final position in `V_L` does it.
Otherwise, by the intermediate value theorem, the motion passes through an angle `φ` with either
`sin φ < 0` (if `θ(1) < 0`), when the wall `y ≤ 1` of `L` bounds `x` from below, or `φ ∈ (0, π/2)`
(if `θ(1) > 0`), when the open quarter-plane `Q_L⁻` (avoided by `L`) does.
-/

@[expose] public section

open Real Set

namespace MovingSofaOptimality

/-! ### Elementary lemmas on rigid motions and the hallway -/

/-- Membership in the image of a set under the rigid motion `p ↦ R_t p + c`. -/
lemma ms_mem_image_iff (t : ℝ) (c q : ℝ × ℝ) (A : Set (ℝ × ℝ)) :
    q ∈ (fun p => rot t p + c) '' A ↔ (dot (q - c) (uvec t), dot (q - c) (vvec t)) ∈ A := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    simpa [dot_rot_uvec_eq_fst, dot_rot_vvec_eq_snd] using hp
  · intro h
    refine ⟨_, h, ?_⟩
    simp only [rot_pair]
    rw [← eq_dot_uvec_smul_add]; abel

/-- Membership in the image of a set under the rotation `R_t`. -/
lemma ms_mem_rot_image_iff (t : ℝ) (q : ℝ × ℝ) (A : Set (ℝ × ℝ)) :
    q ∈ rot t '' A ↔ (dot q (uvec t), dot q (vvec t)) ∈ A := by
  simpa using ms_mem_image_iff t 0 q A

lemma ms_hallwayMap_eq (S : Set (ℝ × ℝ)) (t : ℝ) : hallwayMap S t = fun p => rot t p +
    ((supp S t - 1) • uvec t + (supp S (t + π / 2) - 1) • vvec t) := by
  funext p; simp [hallwayMap, add_assoc]

/-- Membership in the image of a set under `f_{S,t}`. -/
lemma ms_mem_hallwayMap_image (S : Set (ℝ × ℝ)) (t : ℝ) (q : ℝ × ℝ) (A : Set (ℝ × ℝ)) :
    q ∈ hallwayMap S t '' A ↔
      (dot q (uvec t) - (supp S t - 1), dot q (vvec t) - (supp S (t + π / 2) - 1)) ∈ A := by
  rw [ms_hallwayMap_eq, ms_mem_image_iff]
  simp [dot_sub_left, dot_add_left, dot_smul_left]

/-- `L = Q_L⁺ \ Q_L⁻`: a point is in the hallway iff both its coordinates are at most `1` and
one of them is nonnegative. -/
lemma ms_mem_hallway_iff (q : ℝ × ℝ) :
    q ∈ hallway ↔ q.1 ≤ 1 ∧ q.2 ≤ 1 ∧ (0 ≤ q.1 ∨ 0 ≤ q.2) := by
  simp only [hallway, horizSide, vertSide, mem_union, mem_ofPred_eq]
  tauto

/-- Two lines with the same normal angle are equal iff their offsets are. -/
lemma ms_line_eq_iff (t a b : ℝ) : line t a = line t b ↔ a = b := by
  constructor
  · intro h
    have : a • uvec t ∈ line t a := by simp [line, dot_smul_left]
    rw [h] at this
    simpa [line, dot_smul_left] using this
  · rintro rfl; rfl

lemma ms_image_aL (t : ℝ) (c : ℝ × ℝ) :
    (fun p => rot t p + c) '' aL = line t (1 + dot c (uvec t)) := by
  ext q
  rw [ms_mem_image_iff]
  simp only [aL, line, mem_ofPred_eq, dot_sub_left]
  constructor <;> intro h <;> linarith

lemma ms_image_cL (t : ℝ) (c : ℝ × ℝ) :
    (fun p => rot t p + c) '' cL = line (t + π / 2) (1 + dot c (vvec t)) := by
  ext q
  rw [ms_mem_image_iff]
  simp only [cL, line, mem_ofPred_eq, dot_sub_left, uvec_add_pi_div_two]
  constructor <;> intro h <;> linarith

/-- **Proposition 2.2.1** (`pro:tangent-hallway`). Among the translations `p ↦ R_t p + c` of
`R_t(L)`, the supporting hallway `L_S(t)` is the unique one whose outer walls corresponding to
`a_L` and `c_L` are the supporting lines `l_S(t)` and `l_S(t + π/2)`. -/
theorem proposition2_2_1 (S : Set (ℝ × ℝ)) (t : ℝ) (c : ℝ × ℝ) :
    ((fun p => rot t p + c) '' aL = suppLine S t ∧
        (fun p => rot t p + c) '' cL = suppLine S (t + π / 2)) ↔
      (fun p => rot t p + c) = hallwayMap S t := by
  rw [ms_image_aL, ms_image_cL, suppLine, suppLine, ms_line_eq_iff, ms_line_eq_iff,
    ms_hallwayMap_eq]
  constructor
  · rintro ⟨h1, h2⟩
    funext p
    congr 1
    rw [eq_dot_uvec_smul_add c t, ← h1, ← h2]
    congr 2 <;> ring
  · intro h
    have hc := congrFun h 0
    simp only [add_right_inj] at hc
    rw [hc]
    simp [dot_add_left, dot_smul_left]

/-! **Proposition 2.2.2** (`pro:rotating-hallway-parts`). The parts of `L_S(t)` in terms of the
support function. The paper's last formula, for `Q_S⁻(t)`, misses a `- 1` in its second
half-plane; the statement below is the corrected one. -/

theorem proposition2_2_2_hallway (S : Set (ℝ × ℝ)) (t : ℝ) :
    suppHallway S t = qPlus S t \ qMinus S t := by
  ext q
  simp only [suppHallway, qPlus, qMinus, mem_sdiff, ms_mem_hallwayMap_image, ms_mem_hallway_iff,
    qPlusL, qMinusL, mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    rintro ⟨h4, h5⟩
    rcases h3 with h3 | h3 <;> linarith
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, ?_⟩
    by_contra hc
    push Not at hc
    exact h3 ⟨hc.1, hc.2⟩

theorem proposition2_2_2_innerCorner (S : Set (ℝ × ℝ)) (t : ℝ) :
    innerCorner S t = (supp S t - 1) • uvec t + (supp S (t + π / 2) - 1) • vvec t := by
  simp [innerCorner, hallwayMap, xL, rot]

theorem proposition2_2_2_outerCorner (S : Set (ℝ × ℝ)) (t : ℝ) :
    outerCorner S t = supp S t • uvec t + supp S (t + π / 2) • vvec t := by
  ext <;> simp [outerCorner, hallwayMap, yL, rot, uvec, vvec] <;> ring

theorem proposition2_2_2_wallA (S : Set (ℝ × ℝ)) (t : ℝ) : wallA S t = suppLine S t := by
  ext q
  simp only [wallA, ms_mem_hallwayMap_image, aL, suppLine, line, mem_ofPred_eq]
  constructor <;> intro h <;> linarith

theorem proposition2_2_2_wallB (S : Set (ℝ × ℝ)) (t : ℝ) : wallB S t = line t (supp S t - 1) := by
  ext q
  simp only [wallB, ms_mem_hallwayMap_image, bL, line, mem_ofPred_eq]
  constructor <;> intro h <;> linarith

theorem proposition2_2_2_wallC (S : Set (ℝ × ℝ)) (t : ℝ) :
    wallC S t = suppLine S (t + π / 2) := by
  ext q
  simp only [wallC, ms_mem_hallwayMap_image, cL, suppLine, line, mem_ofPred_eq,
    uvec_add_pi_div_two]
  constructor <;> intro h <;> linarith

theorem proposition2_2_2_wallD (S : Set (ℝ × ℝ)) (t : ℝ) :
    wallD S t = line (t + π / 2) (supp S (t + π / 2) - 1) := by
  ext q
  simp only [wallD, ms_mem_hallwayMap_image, dL, line, mem_ofPred_eq, uvec_add_pi_div_two]
  constructor <;> intro h <;> linarith

theorem proposition2_2_2_qPlus (S : Set (ℝ × ℝ)) (t : ℝ) :
    qPlus S t = suppHalf S t ∩ suppHalf S (t + π / 2) := by
  ext q
  simp only [qPlus, ms_mem_hallwayMap_image, qPlusL, suppHalf, halfMinus, mem_inter_iff,
    mem_ofPred_eq, uvec_add_pi_div_two]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem proposition2_2_2_qMinus (S : Set (ℝ × ℝ)) (t : ℝ) :
    qMinus S t =
      halfMinusOpen t (supp S t - 1) ∩ halfMinusOpen (t + π / 2) (supp S (t + π / 2) - 1) := by
  ext q
  simp only [qMinus, ms_mem_hallwayMap_image, qMinusL, halfMinusOpen, mem_inter_iff,
    mem_ofPred_eq, uvec_add_pi_div_two]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Proposition 2.2.3** (`pro:tangent-hallway-contains`). A nonempty compact set contained in a
translation of `R_t(L)` is contained in its supporting hallway `L_S(t)`. -/
theorem proposition2_2_3 {S : Set (ℝ × ℝ)} (hS : IsCompact S) (hne : S.Nonempty) (t : ℝ)
    (c : ℝ × ℝ) (h : S ⊆ (fun p => rot t p + c) '' hallway) : S ⊆ suppHallway S t := by
  have hmem : ∀ p ∈ S, dot p (uvec t) - dot c (uvec t) ≤ 1 ∧ dot p (vvec t) - dot c (vvec t) ≤ 1 ∧
      (0 ≤ dot p (uvec t) - dot c (uvec t) ∨ 0 ≤ dot p (vvec t) - dot c (vvec t)) := by
    intro p hp
    have := h hp
    rw [ms_mem_image_iff, ms_mem_hallway_iff] at this
    simpa only [dot_sub_left] using this
  -- the outer walls of the given hallway lie beyond the supporting lines
  have h1 : supp S t ≤ dot c (uvec t) + 1 :=
    supp_le_of_forall hne fun p hp => by linarith [(hmem p hp).1]
  have h2 : supp S (t + π / 2) ≤ dot c (vvec t) + 1 :=
    supp_le_of_forall hne fun p hp => by rw [uvec_add_pi_div_two]; linarith [(hmem p hp).2.1]
  intro q hq
  have hq1 := dot_le_supp hS hq t
  have hq2 := dot_le_supp hS hq (t + π / 2)
  rw [uvec_add_pi_div_two] at hq2
  rw [suppHallway, ms_mem_hallwayMap_image, ms_mem_hallway_iff]
  refine ⟨by simp only; linarith, by simp only; linarith, ?_⟩
  rcases (hmem q hq).2.2 with h3 | h3
  · left; simp only; linarith
  · right; simp only; linarith

/-! ### Boundedness and compactness of moving sofas -/

/-- A set whose points satisfy `a ≤ x ≤ b` and `c ≤ y ≤ d` is bounded. -/
lemma ms_isBounded_of_bounds {S : Set (ℝ × ℝ)} (a b c d : ℝ)
    (h : ∀ p ∈ S, a ≤ p.1 ∧ p.1 ≤ b ∧ c ≤ p.2 ∧ p.2 ≤ d) : Bornology.IsBounded S :=
  ((Metric.isBounded_Icc a b).prod (Metric.isBounded_Icc c d)).subset
    fun p hp => ⟨⟨(h p hp).1, (h p hp).2.1⟩, ⟨(h p hp).2.2.1, (h p hp).2.2.2⟩⟩

private lemma ms_abs_mul_le {a b Y : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ Y) :
    -Y ≤ a * b ∧ a * b ≤ Y :=
  abs_le.1 <| (abs_mul a b).trans_le <| (mul_le_of_le_one_left (abs_nonneg b) ha).trans hb

/-- At an angle `φ` with `sin φ < 0`, a point of a horizontal strip `|p.2| ≤ Y` that lies in a
translate of `R_{-φ}(L)` is bounded below in `x` (by the wall `y ≤ 1` of `L`). -/
private lemma ms_lower_of_hallway_sin_neg {φ Y : ℝ} {c p : ℝ × ℝ} (hY : |p.2| ≤ Y)
    (h : rot φ p + c ∈ hallway) (hφ : sin φ < 0) : (1 + |c.2| + Y) / sin φ ≤ p.1 := by
  rw [ms_mem_hallway_iff] at h
  obtain ⟨-, h2, -⟩ := h
  simp only [rot, Prod.snd_add] at h2
  have := ms_abs_mul_le (abs_cos_le_one φ) hY
  have hc := neg_abs_le c.2
  rw [div_le_iff_of_neg hφ]
  nlinarith

/-- At an angle `φ ∈ (0, π/2)`, a point of a horizontal strip `|p.2| ≤ Y` that lies in a
translate of `R_{-φ}(L)` is bounded below in `x`, as it avoids the open quarter-plane `Q_L⁻`. -/
private lemma ms_lower_of_hallway_pos {φ Y : ℝ} {c p : ℝ × ℝ} (hY : |p.2| ≤ Y)
    (h : rot φ p + c ∈ hallway) (hc : 0 < cos φ) (hs : 0 < sin φ) :
    min ((-Y - |c.1|) / cos φ) ((-Y - |c.2|) / sin φ) ≤ p.1 := by
  rw [ms_mem_hallway_iff] at h
  obtain ⟨-, -, h3 | h3⟩ := h
  · refine (min_le_left _ _).trans ?_
    simp only [rot, Prod.fst_add] at h3
    have := ms_abs_mul_le (abs_sin_le_one φ) hY
    have hc1 := le_abs_self c.1
    rw [div_le_iff₀ hc]
    nlinarith
  · refine (min_le_right _ _).trans ?_
    simp only [rot, Prod.snd_add] at h3
    have := ms_abs_mul_le (abs_cos_le_one φ) hY
    have hc2 := le_abs_self c.2
    rw [div_le_iff₀ hs]
    nlinarith

/-- Every moving sofa is bounded (implicit in the paper, which takes the area of moving sofas). -/
theorem isBounded_of_isMovingSofa {S : Set (ℝ × ℝ)} (hS : IsMovingSofa S) :
    Bornology.IsBounded S := by
  obtain ⟨ω, -, -, θ, c, hm⟩ := hS
  -- the initial position: `S` lies in a translate of `H_L`
  have hstart : ∀ p ∈ S, p.1 ≤ 1 - (c 0).1 ∧ -(c 0).2 ≤ p.2 ∧ p.2 ≤ 1 - (c 0).2 := by
    intro p hp
    have := hm.start p hp
    rw [hm.angle_zero, rot_zero] at this
    obtain ⟨h1, h2, h3⟩ := this
    simp only [Prod.fst_add, Prod.snd_add] at h1 h2 h3
    exact ⟨by linarith, by linarith, by linarith⟩
  set Y := |(c 0).2| + 1
  have hY : ∀ p ∈ S, |p.2| ≤ Y := by
    intro p hp
    obtain ⟨-, h2, h3⟩ := hstart p hp
    rw [abs_le]; constructor <;> linarith [neg_abs_le (c 0).2, le_abs_self (c 0).2]
  -- it remains to bound `x` from below
  suffices hlow : ∃ M, ∀ p ∈ S, M ≤ p.1 by
    obtain ⟨M, hM⟩ := hlow
    refine ms_isBounded_of_bounds M (1 - (c 0).1) (-(c 0).2) (1 - (c 0).2) fun p hp => ?_
    obtain ⟨h1, h2, h3⟩ := hstart p hp
    exact ⟨hM p hp, h1, h2, h3⟩
  rcases lt_trichotomy (θ 1) 0 with hneg | hzero | hpos
  · -- the motion passes through a clockwise angle `φ ∈ [-1/2, 0)`
    set φ := max (θ 1) (-1) / 2 with hφ
    have hφ1 : φ ∈ Icc (θ 1) (θ 0) := by
      rw [hm.angle_zero]
      constructor
      · have := le_max_left (θ 1) (-1); linarith
      · have : max (θ 1) (-1) < 0 := max_lt hneg (by norm_num); linarith
    obtain ⟨s, hs, hθs⟩ := intermediate_value_Icc' zero_le_one hm.continuousOn_angle hφ1
    have hsin : sin φ < 0 := by
      apply sin_neg_of_neg_of_neg_pi_lt
      · have : max (θ 1) (-1) < 0 := max_lt hneg (by norm_num); linarith
      · have := le_max_right (θ 1) (-1); linarith [two_le_pi]
    refine ⟨(1 + |(c s).2| + Y) / sin φ, fun p hp => ?_⟩
    have := hm.inside s hs p hp
    rw [hθs] at this
    exact ms_lower_of_hallway_sin_neg (hY p hp) this hsin
  · -- no rotation: the final position bounds `x`
    refine ⟨-(c 1).1, fun p hp => ?_⟩
    have := hm.finish p hp
    rw [hzero, rot_zero] at this
    obtain ⟨h1, -, -⟩ := this
    simp only [Prod.fst_add] at h1
    linarith
  · -- the motion passes through a counterclockwise angle `φ ∈ (0, 1/2]`
    set φ := min (θ 1) 1 / 2 with hφ
    have hφpos : 0 < φ := by
      have : 0 < min (θ 1) 1 := lt_min hpos one_pos; linarith
    have hφle : φ ≤ 1 / 2 := by have := min_le_right (θ 1) 1; linarith
    have hφ1 : φ ∈ Icc (θ 0) (θ 1) := by
      rw [hm.angle_zero]
      exact ⟨hφpos.le, by have := min_le_left (θ 1) 1; linarith⟩
    obtain ⟨s, hs, hθs⟩ := intermediate_value_Icc zero_le_one hm.continuousOn_angle hφ1
    have hcos : 0 < cos φ :=
      cos_pos_of_mem_Ioo ⟨by linarith [two_le_pi], by linarith [two_le_pi]⟩
    have hsin : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφpos (by linarith [two_le_pi])
    refine ⟨min ((-Y - |(c s).1|) / cos φ) ((-Y - |(c s).2|) / sin φ), fun p hp => ?_⟩
    have := hm.inside s hs p hp
    rw [hθs] at this
    exact ms_lower_of_hallway_pos (hY p hp) this hcos hsin

/-- A moving sofa is compact. -/
theorem isCompact_of_isMovingSofa {S : Set (ℝ × ℝ)} (hS : IsMovingSofa S) : IsCompact S :=
  Metric.isCompact_of_isClosed_isBounded hS.choose_spec.1 (isBounded_of_isMovingSofa hS)

/-- A moving sofa with rotation angle `ω` is compact. -/
lemma ms_isCompact_of_isMovingSofaWithAngle {S : Set (ℝ × ℝ)} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) : IsCompact S :=
  isCompact_of_isMovingSofa ⟨ω, hS⟩

/-! ### The common subset of a moving sofa (Proposition 1.2.2) -/

/-- `V_ω = {p : 0 ≤ p · u_ω ≤ 1}`. -/
lemma ms_mem_vStripRot_iff (ω : ℝ) (p : ℝ × ℝ) :
    p ∈ vStripRot ω ↔ 0 ≤ dot p (uvec ω) ∧ dot p (uvec ω) ≤ 1 := by
  rw [vStripRot, ms_mem_rot_image_iff]; rfl

/-- Membership in the parallelogram `P_ω = H ∩ V_ω`. -/
lemma mem_para_iff {ω : ℝ} {p : ℝ × ℝ} :
    p ∈ para ω ↔ (0 ≤ p.2 ∧ p.2 ≤ 1) ∧ (0 ≤ dot p (uvec ω) ∧ dot p (uvec ω) ≤ 1) := by
  rw [para, Set.mem_inter_iff, ms_mem_vStripRot_iff]; rfl

/-- A cap with rotation angle `ω` lies in the parallelogram `P_ω`. -/
lemma IsCap.subset_para {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) : K ⊆ para ω :=
  fun _ hp => mem_para_iff.2 ⟨⟨hK.snd_nonneg hp, hK.snd_le_one hp⟩,
    ⟨hK.dot_omega_nonneg hp, hK.dot_omega_le_one hp⟩⟩

lemma ms_mem_hStrip_iff (p : ℝ × ℝ) : p ∈ hStrip ↔ 0 ≤ p.2 ∧ p.2 ≤ 1 := Iff.rfl

/-- The coordinates of `R_{-ω} p` are those of `p` in the frame `(u_ω, v_ω)`. -/
lemma ms_rot_neg_fst (ω : ℝ) (p : ℝ × ℝ) : (rot (-ω) p).1 = dot p (uvec ω) := by
  simp [rot, dot, uvec]; ring

lemma ms_rot_neg_snd (ω : ℝ) (p : ℝ × ℝ) : (rot (-ω) p).2 = dot p (vvec ω) := by
  simp [rot, dot, vvec]; ring

/-- **Proposition 1.2.2** (`pro:moving-sofa-common-subset`). A moving sofa `S` with rotation
angle `ω ∈ (0, π/2]` in standard position lies in the strip `H`, in a translation of `R_t(L)` for
every `t ∈ [0, ω]`, and in the rotated strip `V_ω`. -/
theorem proposition1_2_2 {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) :
    S ⊆ hStrip ∧ (∀ t ∈ Icc 0 ω, ∃ c : ℝ × ℝ, S ⊆ (fun p => rot t p + c) '' hallway) ∧
      S ⊆ vStripRot ω := by
  have _ := hω  -- the angle range is not needed for these inclusions
  have hcpt := ms_isCompact_of_isMovingSofaWithAngle hS
  obtain ⟨-, hconn, θ, c, hm⟩ := hS
  have hne := hconn.nonempty
  refine ⟨?_, ?_, ?_⟩
  · -- (1): the initial position lies in `H_L`, and `h_S(π/2) = 1`
    obtain ⟨q, hq, hq1⟩ := exists_dot_eq_supp hcpt hne (π / 2)
    rw [hstd.2, dot_uvec_pi_div_two] at hq1
    have hq' := hm.start q hq
    rw [hm.angle_zero, rot_zero] at hq'
    intro p hp
    have hp' := hm.start p hp
    rw [hm.angle_zero, rot_zero] at hp'
    have hp1 := dot_le_supp hcpt hp (π / 2)
    rw [hstd.2, dot_uvec_pi_div_two] at hp1
    obtain ⟨-, h2, -⟩ := hp'
    obtain ⟨-, -, h3⟩ := hq'
    simp only [Prod.snd_add] at h2 h3
    exact ⟨by linarith, hp1⟩
  · -- (2): by the intermediate value theorem the motion passes through the angle `-t`
    intro t ht
    have ht' : -t ∈ Icc (θ 1) (θ 0) := by
      rw [hm.angle_zero, hm.angle_one]; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    obtain ⟨s, hs, hθs⟩ := intermediate_value_Icc' zero_le_one hm.continuousOn_angle ht'
    refine ⟨-rot t (c s), fun p hp => ⟨rot (-t) p + c s, ?_, ?_⟩⟩
    · have := hm.inside s hs p hp
      rwa [hθs] at this
    · simp only [rot_add_vec, rot_rot_neg]; abel
  · -- (3): the final position lies in `V_L`, and `h_S(ω) = 1`
    obtain ⟨q, hq, hq1⟩ := exists_dot_eq_supp hcpt hne ω
    rw [hstd.1] at hq1
    have hq' := hm.finish q hq
    rw [hm.angle_one] at hq'
    intro p hp
    have hp' := hm.finish p hp
    rw [hm.angle_one] at hp'
    have hp1 := dot_le_supp hcpt hp ω
    rw [hstd.1] at hp1
    obtain ⟨h1, -, -⟩ := hp'
    obtain ⟨-, h2, -⟩ := hq'
    simp only [Prod.fst_add, ms_rot_neg_fst] at h1 h2
    rw [ms_mem_vStripRot_iff]
    exact ⟨by linarith, hp1⟩

end MovingSofaOptimality
