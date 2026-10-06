module

public import MovingSofaStability.TerminalComparison

/-!
# Coordinates inherited from a genuine moving sofa

Uncompiled proof source. Supporting hallways and the terminal lower wall are
derived from the given movement. The initial normalization is a translation,
not a rotation of a set that might no longer satisfy the original convention.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness
open GerverParams

namespace MovingSofaStability

/-- Standard-position assumptions are unnecessary for the supporting-hallway containment. -/
theorem moving_supporting_hallways {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) ω) :
    S ⊆ suppHallway S t := by
  have hcompact := ms_isCompact_of_isMovingSofaWithAngle hS
  have hne := hS.2.1.nonempty
  obtain ⟨-, -, θ, c, hm⟩ := hS
  have ht' : -t ∈ Icc (θ 1) (θ 0) := by
    rw [hm.angle_zero, hm.angle_one]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc' zero_le_one hm.continuousOn_angle ht'
  apply proposition2_2_3 hcompact hne t (-rot t (c s))
  intro p hp
  refine ⟨rot (-t) p + c s, ?_, ?_⟩
  · simpa only [he] using hm.inside s hs p hp
  · simp only [rot_add_vec, rot_rot_neg]
    abel

/-- The closed maximum of the two inner slacks is the condition that passes to limits. -/
theorem moving_hallway_slacks {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) {p : Point} (hp : p ∈ S)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) ω) :
    0 ≤ max (innerSlackU S t p) (innerSlackV S t p) := by
  have he := moving_supporting_hallways hS ht hp
  rw [proposition2_2_2_hallway] at he
  by_contra hn
  have hl := not_le.mp hn
  apply he.2
  exact (mem_qMinus_iff_slacks S t p).2
    ⟨(le_max_left _ _).trans_lt hl, (le_max_right _ _).trans_lt hl⟩

/-- The terminal unit strip bounds the difference of any two projections. -/
theorem moving_terminal_projection {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) {p q : Point} (hp : p ∈ S) (hq : q ∈ S) :
    dot (q - p) (uvec ω) ≤ 1 := by
  obtain ⟨-, -, θ, c, hm⟩ := hS
  have hp' := hm.finish p hp
  have hq' := hm.finish q hq
  rw [hm.angle_one] at hp' hq'
  simp only [vertSide, mem_ofPred_eq, Prod.fst_add, ms_rot_neg_fst] at hp' hq'
  rw [dot_sub_left]
  linarith [hp'.1, hq'.2.1]

/-- The lower wall is expressed relative to the actual supporting upper wall. -/
theorem moving_terminal_lower {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) {p : Point} (hp : p ∈ S) :
    supp S ω - 1 ≤ dot p (uvec ω) := by
  obtain ⟨q, hq, he⟩ := exists_dot_eq_supp (ms_isCompact_of_isMovingSofaWithAngle hS)
    hS.2.1.nonempty ω
  have h := moving_terminal_projection hS hp hq
  rw [dot_sub_left, he] at h
  linarith

theorem moving_terminal_width {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) : supp S ω + supp S (ω + π) ≤ 1 := by
  obtain ⟨p, hp, he⟩ := exists_dot_eq_supp (ms_isCompact_of_isMovingSofaWithAngle hS)
    hS.2.1.nonempty (ω + π)
  have hl := moving_terminal_lower hS hp
  rw [dot_uvec_add_pi] at he
  linarith

/-- Initial unit width and top support one fix a containing horizontal strip. -/
theorem moving_strip_of_top {S : Set Point} (hS : IsMovingSofa S)
    (htop : supp S (π / 2) = 1) : S ⊆ hStrip := by
  have hc := isCompact_of_isMovingSofa hS
  have hne := hS.choose_spec.2.1.nonempty
  obtain ⟨q, hq, hqy⟩ := exists_dot_eq_supp hc hne (π / 2)
  rw [dot_uvec_pi_div_two, htop] at hqy
  intro p hp
  have hw := snd_sub_le_one_of_isMovingSofa hS hq hp
  have hu := dot_le_supp hc hp (π / 2)
  rw [dot_uvec_pi_div_two, htop] at hu
  exact ⟨by linarith, hu⟩

theorem normalizedSofa_movingWithAngle (P : GerverParams) {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) : IsMovingSofaWithAngle (normalizedSofa P S) ω := by
  simpa only [normalizedSofa, Rigid.coe_translate] using
    mpc_isMovingSofaWithAngle_translate hS (normalizingShift P S)

theorem normalizedSofa_moving (P : GerverParams) {S : Set Point} (hS : IsMovingSofa S) :
    IsMovingSofa (normalizedSofa P S) :=
  ⟨hS.choose, normalizedSofa_movingWithAngle P hS.choose_spec⟩

theorem normalizedSofa_strip (P : GerverParams) {S : Set Point} (hS : IsMovingSofa S) :
    normalizedSofa P S ⊆ hStrip :=
  moving_strip_of_top (normalizedSofa_moving P hS)
    (normalizedSofa_top P (isCompact_of_isMovingSofa hS) hS.choose_spec.2.1.nonempty)

/-- Gerver's cap and sofa have identical upper-semicircle supports. -/
theorem gerver_upper_support {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) π) : supp P.cap t = supp (gerverSofa P) t := by
  have hJ : t ∈ jSet (π / 2) := by
    by_cases hv : t ≤ π / 2
    · exact Or.inl ⟨ht.1, hv⟩
    · exact Or.inr ⟨(not_le.mp hv).le, by linarith [ht.2]⟩
  exact (lemma2_3_5_supp ⟨by positivity, le_rfl⟩ (gm_movingSofa_std hP hbox).1
    (gm_movingSofa_std hP hbox).2 hJ).2

/-- Equality of finite real areas also gives equality of the underlying measures. -/
theorem volume_eq_of_area_eq {S T : Set Point}
    (hS : volume S ≠ ⊤) (hT : volume T ≠ ⊤) (he : area S = area T) : volume S = volume T := by
  have h := congrArg ENNReal.ofReal he
  simpa only [area, ENNReal.ofReal_toReal hS, ENNReal.ofReal_toReal hT] using h

/-- In the pinned frame, the existing uniqueness theorem identifies an exact maximizer. -/
theorem pinned_maximizer_eq_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Point} (hS : IsMovingSofa S) (htop : supp S (π / 2) = 1)
    (hleft : supp S π = supp (gerverSofa P) π) (harea : area S = area (gerverSofa P)) :
    S = gerverSofa P := by
  have hcompact := isCompact_of_isMovingSofa hS
  have hne := hS.choose_spec.2.1.nonempty
  obtain ⟨w, hw⟩ := translate_eq_gerver_of_volume_eq hP hbox hS
    (volume_eq_of_area_eq hcompact.measure_lt_top.ne (gerverSofa_volume_ne_top hP hbox) harea)
  have hv := congrArg (fun T => supp T (π / 2)) hw
  have hl := congrArg (fun T => supp T π) hw
  rw [Rigid.coe_translate, supp_translate S _ _ hcompact hne, htop,
    ← gerver_upper_support hP hbox (t := π / 2) ⟨by positivity, by linarith [pi_pos]⟩,
    gm_supp_cap_pi_div_two hP hbox, dot_uvec_pi_div_two] at hv
  rw [Rigid.coe_translate, supp_translate S _ _ hcompact hne, hleft] at hl
  simp only [dot, uvec_pi] at hl
  have hw0 : w = 0 := by ext <;> simp only [Prod.fst_zero, Prod.snd_zero] <;> linarith
  rw [hw0, Rigid.coe_translate] at hw
  simpa only [add_zero, image_id'] using hw

end MovingSofaStability
