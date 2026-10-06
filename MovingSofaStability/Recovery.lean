module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import MovingSofaExtremal.Main
public import MovingSofaStability.Terminal

/-!
# From the cap back to the sofa

The cap of a moving sofa has the sofa's upper support function; with the margins of Gerver's sofa, the
distance between the caps and the missing area bound the Euclidean distance between the sofa and Gerver's,
and a parallel-body estimate bounds their symmetric difference (`local_positive_sofa_hausdorff`).

The sections below follow the steps of the proof.
-/

@[expose] public section
noncomputable section

/-!
## Coordinates inherited from a genuine moving sofa

Supporting hallways and the terminal lower wall are derived from the given
movement. The initial normalization is a translation, not a rotation of a set
that might no longer satisfy the original convention.
-/

section SofaCoordinates

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

/-- In the pinned frame, a moving sofa of area `|G|` is Gerver's sofa: it is a translate of `G`
(`MovingSofaExtremal.translate_eq_gerver_of_volume_eq`), and the two supports fix the translation. -/
theorem pinned_maximizer_eq_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Point} (hS : IsMovingSofa S) (htop : supp S (π / 2) = 1)
    (hleft : supp S π = supp (gerverSofa P) π) (harea : area S = area (gerverSofa P)) :
    S = gerverSofa P := by
  have hcompact := isCompact_of_isMovingSofa hS
  have hne := hS.choose_spec.2.1.nonempty
  obtain ⟨w, hw⟩ := MovingSofaExtremal.translate_eq_gerver_of_volume_eq hP hbox hS
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

end SofaCoordinates

/-!
## A full-angle cap without extending the sofa's motion

The downward completion contains the normalized original set and preserves all
upper supports. The actual set need not be convex and need not admit a
full-angle movement.
-/

section SofaCap

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness
open GerverParams

namespace MovingSofaStability

def sofaCap (S : Set Point) : Set Point :=
  {p | 0 ≤ p.2 ∧ ∀ t ∈ Icc (0 : ℝ) π, dot p (uvec t) ≤ supp S t}

theorem subset_sofaCap {S : Set Point} (hS : IsCompact S) (hstrip : S ⊆ hStrip) : S ⊆ sofaCap S :=
  fun _ hp => ⟨(hstrip hp).1, fun t _ => dot_le_supp hS hp t⟩

theorem sofaCap_down {S : Set Point} {p : Point} (hp : p ∈ sofaCap S)
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ p.2) : (p.1, y) ∈ sofaCap S := by
  refine ⟨hy0, ?_⟩
  intro t ht
  have he := hp.2 t ht
  have hs := sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2
  simp only [dot, uvec] at he ⊢
  nlinarith

theorem sofaCap_closed (S : Set Point) : IsClosed (sofaCap S) := by
  have he : sofaCap S = halfPlus (π / 2) 0 ∩ ⋂ t ∈ Icc (0 : ℝ) π, halfMinus t (supp S t) := by
    ext p
    simp only [sofaCap, halfPlus, halfMinus, mem_inter_iff, mem_iInter,
      mem_ofPred_eq, dot_uvec_pi_div_two]
  rw [he]
  exact (isClosed_halfPlus _ _).inter (isClosed_biInter fun t ht => isClosed_halfMinus _ _)

theorem sofaCap_convex (S : Set Point) : Convex ℝ (sofaCap S) := by
  intro p hp q hq a b ha hb hab
  refine ⟨by simpa only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] using
    add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1), ?_⟩
  intro t ht
  have h1 := mul_le_mul_of_nonneg_left (hp.2 t ht) ha
  have h2 := mul_le_mul_of_nonneg_left (hq.2 t ht) hb
  have h3 : a * supp S t + b * supp S t = supp S t := by rw [← add_mul, hab, one_mul]
  rw [dot_add_left, dot_smul_left, dot_smul_left]
  linarith

theorem sofaCap_compact {S : Set Point} (htop : supp S (π / 2) = 1) : IsCompact (sofaCap S) := by
  have hb : IsCompact (Icc (-supp S π) (supp S 0) ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  apply hb.of_isClosed_subset (sofaCap_closed S)
  intro p hp
  have h0 := hp.2 0 ⟨le_rfl, pi_pos.le⟩
  have hπ := hp.2 π ⟨pi_pos.le, le_rfl⟩
  have hv := hp.2 (π / 2) ⟨by positivity, by linarith [pi_pos]⟩
  rw [dot_uvec_zero] at h0
  simp only [dot, uvec_pi] at hπ
  rw [dot_uvec_pi_div_two, htop] at hv
  exact ⟨⟨by linarith, h0⟩, hp.1, hv⟩

theorem sofaCap_upper_support {S : Set Point} (hS : IsCompact S) (hne : S.Nonempty)
    (hstrip : S ⊆ hStrip) (htop : supp S (π / 2) = 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) π) : supp (sofaCap S) t = supp S t := by
  have hsub := subset_sofaCap hS hstrip
  exact le_antisymm (supp_le_of_forall (hne.mono hsub) (fun p hp => hp.2 t ht))
    (supp_mono hsub hne (sofaCap_compact htop) t)

theorem sofaCap_isCap {S : Set Point} (hS : IsCompact S) (hne : S.Nonempty)
    (hstrip : S ⊆ hStrip) (htop : supp S (π / 2) = 1) : IsCap (sofaCap S) (π / 2) := by
  have hsub := subset_sofaCap hS hstrip
  have hcpt := sofaCap_compact htop
  have hneC := hne.mono hsub
  have htopC : supp (sofaCap S) (π / 2) = 1 :=
    (sofaCap_upper_support hS hne hstrip htop ⟨by positivity, by linarith [pi_pos]⟩).trans htop
  obtain ⟨p, hp⟩ := id hneC
  have hfloor : (p.1, 0) ∈ sofaCap S := sofaCap_down hp le_rfl hp.1
  have hbottom : supp (sofaCap S) (3 * π / 2) = 0 := by
    apply le_antisymm
    · apply supp_le_of_forall hneC
      intro q hq
      rw [dot_uvec_three_pi_div_two]
      linarith [hq.1]
    · have he := dot_le_supp hcpt hfloor (3 * π / 2)
      simpa only [dot_uvec_three_pi_div_two, neg_zero] using he
  refine ⟨⟨by positivity, le_rfl⟩, ⟨hneC, hcpt, sofaCap_convex S⟩,
    htopC, htopC, ?_, hbottom, ?_⟩
  · simpa only [show π / 2 + π = 3 * π / 2 by ring] using hbottom
  · let I := ↥(Icc (0 : ℝ) π)
    refine ⟨Option I, (fun i => i.elim (3 * π / 2) Subtype.val),
      (fun i => i.elim 0 (fun t => supp S t.1)), ?_, ?_⟩
    · intro i
      cases i with
      | none => exact Or.inr (by simp)
      | some t =>
        apply Or.inl
        by_cases ht : t.1 ≤ π / 2
        · exact Or.inl ⟨t.2.1, ht⟩
        · exact Or.inr ⟨(not_le.mp ht).le, show t.1 ≤ π / 2 + π / 2 by linarith [t.2.2]⟩
    · ext q
      simp only [mem_iInter]
      constructor
      · intro h i
        cases i with
        | none => simpa only [Option.elim_none, halfMinus, mem_ofPred_eq,
            dot_uvec_three_pi_div_two, neg_nonpos] using h.1
        | some t => exact h.2 t.1 t.2
      · intro h
        have hf := h none
        have hf' : 0 ≤ q.2 := by
          simpa only [Option.elim_none, halfMinus, mem_ofPred_eq,
            dot_uvec_three_pi_div_two, neg_nonpos] using hf
        exact ⟨hf', fun t ht => h (some ⟨t, ht⟩)⟩

theorem sofaCap_close_to_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Point} (hS : IsCompact S) (hne : S.Nonempty) (hstrip : S ⊆ hStrip)
    (htop : supp S (π / 2) = 1) {δ : ℝ} (hclose : EuclideanClose δ S (gerverSofa P)) :
    UpperSupportClose δ (sofaCap S) P.cap := by
  intro t ht
  rw [sofaCap_upper_support hS hne hstrip htop ht, gerver_upper_support hP hbox ht]
  have hG := (gm_movingSofa_std hP hbox).1
  exact hclose.abs_supp_sub_le hS (ms_isCompact_of_isMovingSofaWithAngle hG) hne hG.2.1.nonempty t

theorem sofaCap_partial_constraints {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) (hω : ω ∈ Icc (0 : ℝ) (π / 2))
    (htop : supp S (π / 2) = 1) : PartialSofaConstraints (sofaCap S) S ω := by
  have hcpt := ms_isCompact_of_isMovingSofaWithAngle hS
  have hne := hS.2.1.nonempty
  have hstrip := moving_strip_of_top ⟨ω, hS⟩ htop
  have hs : ∀ {t : ℝ}, t ∈ Icc (0 : ℝ) π → supp (sofaCap S) t = supp S t :=
    sofaCap_upper_support hcpt hne hstrip htop
  refine ⟨subset_sofaCap hcpt hstrip, ?_, ?_⟩
  · intro p hp t ht
    have h0 := moving_hallway_slacks hS hp ht
    have h1 := hs ⟨ht.1, ht.2.trans (hω.2.trans (by linarith [pi_pos]))⟩
    have h2 := hs (t := t + π / 2) ⟨by linarith [ht.1, pi_pos], by linarith [ht.2, hω.2]⟩
    simpa only [innerSlackU, innerSlackV, h1, h2] using h0
  · intro p hp
    rw [hs ⟨hω.1, by linarith [hω.2, pi_pos]⟩]
    exact moving_terminal_lower hS hp

end MovingSofaStability

end SofaCap

/-!
## Local quantitative recovery of the actual sofa

All cap, terminal, erosion and reference-roof hypotheses are assembled here.
Only entry into a fixed neighborhood remains for the global step. The smaller
sofa need not be contained in its full-angle shape, and the conclusion concerns
its actual nonconvex points.
-/

section LocalSofaRecovery

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- A single explicit threshold controls a fixed coefficient times sqrt epsilon. -/
theorem exists_sqrt_threshold {A r : ℝ} (hA : 0 ≤ A) (hr : 0 < r) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ → A * sqrt ε < r := by
  let q := r / (A + 1)
  have hq : 0 < q := div_pos hr (by linarith)
  let ε₀ := min 1 (q ^ 2)
  have he : 0 < ε₀ := lt_min (by norm_num) (sq_pos_of_pos hq)
  refine ⟨ε₀, he, min_le_left _ _, ?_⟩
  intro ε hε hsmall
  have hsq := sq_sqrt hε
  have hs := sqrt_nonneg ε
  have hεq : ε < q ^ 2 := hsmall.trans_le (min_le_right _ _)
  have hslt : sqrt ε < q := by nlinarith
  have hqr : (A + 1) * q = r := by dsimp [q]; field_simp
  have hm := mul_le_mul_of_nonneg_left hslt.le hA
  nlinarith

theorem self_le_sqrt_of_unit {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) 1) : ε ≤ sqrt ε := by
  have hs := sqrt_nonneg ε
  have hsq := sq_sqrt hε.1
  have hs1 : sqrt ε ≤ 1 := by nlinarith [hε.2]
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hs1)]

/-- The local unrestricted rate, with the cap and terminal constraints explicitly
constructed elsewhere. No smoothness or injectivity of K is assumed. -/
theorem local_positive_sofa_hausdorff {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ C c δ α₀ ε₀ : ℝ,
      0 < C ∧ 0 < c ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < α₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ∀ K : Set Point, IsCap K (π / 2) → supp K π = supp P.cap π →
      UpperSupportClose δ K P.cap → ∀ S : Set Point, MeasurableSet S →
      ∀ ω ∈ Icc (0 : ℝ) (π / 2), π / 2 - ω ≤ α₀ → PartialSofaConstraints K S ω →
      ∀ ε : ℝ, ε = area (gerverSofa P) - area S → 0 < ε → ε < ε₀ →
        EuclideanClose (C * sqrt ε) S (gerverSofa P) ∧ π / 2 - ω ≤ ε / c := by
  obtain ⟨c, δT, α₀, R, hc, hδT, hδT1, hα₀, hR, hterminal⟩ := nearby_terminal_comparison hP hbox
  obtain ⟨δK, hδK, hδK1, hcapestimate⟩ := nearby_cap_distance hP hbox
  obtain ⟨H, L, γ, cr, τ, d₀, κ, r₀, hroof, hcr, hτ, hd₀, hκ, hr₀,
    hslack, houter, hballs⟩ := gerver_recovery_constants hP hbox
  -- `a` is the coefficient of the cap estimate.
  let a := 2 / cos P.φ
  have ha : 0 < a :=
    div_pos (by norm_num) (cap_angle_parameters (GerverParams.gm_φ_mem_Ioo hP hbox)).1
  let B := 4 * R / c
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let Cf := max 1 (1 / cr) * (a + B)
  let Cb := 4 * (2 * a + 1) / κ
  let C := max 1 (max Cf Cb)
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hCb : 0 ≤ Cb := div_nonneg (by linarith) hκ.le
  obtain ⟨εd, hεd, hεd1, hsmallD⟩ := exists_sqrt_threshold (A := a) ha.le hd₀
  obtain ⟨εt, hεt, hεt1, hsmallT⟩ := exists_sqrt_threshold (A := a + B) (by linarith) hτ
  obtain ⟨εr, hεr, hεr1, hsmallR⟩ := exists_sqrt_threshold hCb hr₀
  let ε₀ := min εd (min εt εr)
  let δ := min δT δK
  have hε₀ : 0 < ε₀ := lt_min hεd (lt_min hεt hεr)
  have hδ : 0 < δ := lt_min hδT hδK
  have dT : δ ≤ δT := min_le_left _ _
  have dK : δ ≤ δK := min_le_right _ _
  have ed : ε₀ ≤ εd := min_le_left _ _
  have et : ε₀ ≤ εt := (min_le_right _ _).trans (min_le_left _ _)
  have er : ε₀ ≤ εr := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨C, c, δ, α₀, ε₀, hC, hc, hδ, dT.trans hδT1, hα₀, hε₀, ed.trans hεd1, ?_⟩
  intro K hK hleft hclose S hS ω hω hα hconstraints ε hεeq hε hεsmall
  obtain ⟨hloss, hangle, hdeficit, hSU, hUS, hhall⟩ :=
    hterminal K hK (hclose.mono dT) S hS ω hω hα hconstraints
  rw [← hεeq] at hangle hdeficit hSU hUS
  obtain ⟨hNK, hAM, hdist⟩ := hcapestimate K hK (hclose.mono dK)
  rw [shiftedReferenceCap_eq_of_left_support hleft] at hdist
  have hdist' : EuclideanClose (a * sqrt ε) K P.cap := hdist.mono
    (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hdeficit) ha.le)
  have hsupport : UpperSupportClose (a * sqrt ε) K P.cap :=
    fun t ht => hdist'.abs_supp_sub_le hK.2.1.2.1 hroof.cap.2.1.2.1 hK.2.1.1 hroof.cap.2.1.1 t
  have hε1 : ε ≤ 1 := hεsmall.le.trans (ed.trans hεd1)
  have hεsqrt := self_le_sqrt_of_unit ⟨hε.le, hε1⟩
  have hζ : 4 * R * (π / 2 - ω) ≤ B * sqrt ε := by
    have he := mul_le_mul_of_nonneg_left hangle (show 0 ≤ 4 * R by linarith)
    have he' := mul_le_mul_of_nonneg_left hεsqrt hB
    dsimp [B] at *
    nlinarith [show 4 * R * (ε / c) = (4 * R / c) * ε by ring]
  have hhall' : ApproxHallways K S (B * sqrt ε) := by
    intro p hp t ht
    exact (neg_le_neg hζ).trans (hhall p hp t ht)
  have hsmall1 := hsmallD ε hε.le (hεsmall.trans_le ed)
  have hsmall2 : a * sqrt ε + B * sqrt ε < τ := by
    have he := hsmallT ε hε.le (hεsmall.trans_le et)
    linarith [show (a + B) * sqrt ε = a * sqrt ε + B * sqrt ε by ring]
  have hfront := directed_to_reference_of_margins hroof hK hcr
    (mul_nonneg ha.le (sqrt_nonneg ε)) (mul_nonneg hB (sqrt_nonneg ε))
    hsupport houter hsmall1 hsmall2 hslack hconstraints.1 hhall'
  rw [gerver_shape_eq hP hbox] at hfront
  have hback := reference_to_sofa_recovery hroof.cap hK
    (mul_nonneg ha.le (sqrt_nonneg ε)) hsupport hκ (A := 2 * a) (by linarith) hε
    (by simpa only [gerver_shape_eq hP hbox] using hballs)
    (le_of_eq (by ring))
    (hsmallR ε hε.le (hεsmall.trans_le er)).le
    (volume_ne_top_of_subset sdiff_subset hK.2.1.2.1.measure_lt_top.ne) hUS
  rw [gerver_shape_eq hP hbox] at hback
  refine ⟨⟨hfront.mono ?_, hback.mono ?_⟩, hangle⟩
  · have hle : Cf ≤ C := (le_max_left _ _).trans (le_max_right _ _)
    have he := mul_le_mul_of_nonneg_right hle (sqrt_nonneg ε)
    dsimp [Cf] at he
    nlinarith
  · exact mul_le_mul_of_nonneg_right
      ((le_max_right Cf Cb).trans (le_max_right 1 (max Cf Cb))) (sqrt_nonneg ε)

end MovingSofaStability

end LocalSofaRecovery

/-!
## A linear area bound for an outer parallel layer

One fixed interior disk bounds the Euclidean parallel body by a homothetic copy.
The area calculation uses two-dimensional Haar scaling and requires no
smoothness or perimeter formula.
-/

section ConvexParallelArea

open Real Set MeasureTheory
open scoped Pointwise
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

def homotheticBody (K : Set Point) (z : Point) (lam : ℝ) : Set Point :=
  (fun p => lam • (p - z) + z) '' K

theorem homotheticBody_convexBody {K : Set Point} (hK : IsConvexBody K) (z : Point) (lam : ℝ) :
    IsConvexBody (homotheticBody K z lam) := by
  refine ⟨hK.1.image _, hK.2.1.image (by fun_prop), ?_⟩
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ a b ha hb hab
  refine ⟨a • p + b • q, hK.2.2 hp hq ha hb hab, ?_⟩
  obtain rfl : b = 1 - a := by linarith
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem homotheticBody_support {K : Set Point} (hK : IsConvexBody K) (z : Point)
    {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) :
    supp (homotheticBody K z lam) t = lam * supp K t + (1 - lam) * dot z (uvec t) := by
  have hC := homotheticBody_convexBody hK z lam
  obtain ⟨p, hp, he⟩ := exists_dot_eq_supp hK.2.1 hK.1 t
  apply supp_eq_of_mem hC.2.1
  · rintro _ ⟨q, hq, rfl⟩
    have h := mul_le_mul_of_nonneg_left (dot_le_supp hK.2.1 hq t) hlam
    rw [dot_add_left, dot_smul_left, dot_sub_left]
    linarith
  · exact mem_image_of_mem _ hp
  · rw [dot_add_left, dot_smul_left, dot_sub_left, he]
    ring

theorem area_homotheticBody (K : Set Point) (z : Point) (lam : ℝ) :
    area (homotheticBody K z lam) = lam ^ 2 * area K := by
  have hdim : Module.finrank ℝ Point = 2 := by
    simp [Point, Module.finrank_prod]
  have he := Measure.addHaar_image_homothety (volume : Measure Point) z lam K
  change volume (homotheticBody K z lam) = _ at he
  unfold area
  rw [he, hdim, abs_of_nonneg (sq_nonneg lam), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg lam)]

/-- A fixed inscribed ball provides a support margin in every direction. -/
theorem support_margin_of_ball {K : Set Point} (hK : IsConvexBody K) {z : Point} {r : ℝ}
    (hr : 0 ≤ r) (hball : euclideanBall z r ⊆ K) (t : ℝ) :
    dot z (uvec t) + r ≤ supp K t := by
  have hp : z + r • uvec t ∈ euclideanBall z r := by
    change norm2 (z - (z + r • uvec t)) ≤ r
    rw [show z - (z + r • uvec t) = -(r • uvec t) by abel,
      norm2_neg, norm2_smul, norm2_uvec, abs_of_nonneg hr, mul_one]
  have he := dot_le_supp hK.2.1 (hball hp) t
  simpa only [dot_add_left, dot_smul_left, dot_uvec_self, mul_one] using he

/-- The parallel body fits inside a dilation by factor 1+d/r about the ball center. -/
theorem parallel_subset_homothetic {K : Set Point} (hK : IsConvexBody K) {z : Point}
    {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) (hball : euclideanBall z r ⊆ K) :
    K + euclideanDisk d ⊆ homotheticBody K z (1 + d / r) := by
  intro p hp
  apply (mem_iff_forall_dot_le_supp (homotheticBody_convexBody hK z (1 + d / r)) p).2
  intro t
  have hsum := convexBody_add hK (euclideanDisk_isConvexBody hd)
  have h1 := dot_le_supp hsum.2.1 hp t
  rw [supp_add_euclideanDisk hK hd] at h1
  have h2 := support_margin_of_ball hK hr.le hball t
  have hratio : 0 ≤ d / r := div_nonneg hd hr.le
  have hm := mul_le_mul_of_nonneg_left h2 hratio
  rw [homotheticBody_support hK z (by positivity)]
  have hc : d / r * r = d := div_mul_cancel₀ _ hr.ne'
  nlinarith

/-- The excess area of an arbitrary subset of a thin parallel layer is linear in thickness. -/
theorem area_parallel_layer_le {K : Set Point} (hK : IsConvexBody K) {z : Point} {r d : ℝ}
    (hr : 0 < r) (hd : d ∈ Icc (0 : ℝ) 1) (hball : euclideanBall z r ⊆ K)
    {E : Set Point} (hE : E ⊆ (K + euclideanDisk d) \ K) :
    area E ≤ area K * (2 / r + 1 / r ^ 2) * d := by
  let lam := 1 + d / r
  let C := homotheticBody K z lam
  have hCK := homotheticBody_convexBody hK z lam
  have hsub := parallel_subset_homothetic hK hr hd.1 hball
  have hKsum : K ⊆ K + euclideanDisk d := by
    intro p hp
    exact ⟨p, hp, 0, by simpa only [euclideanDisk, mem_ofPred_eq, norm2_zero] using hd.1,
      add_zero p⟩
  have hKC : K ⊆ C := hKsum.trans hsub
  have hEC : E ⊆ C \ K := fun p hp => ⟨hsub (hE hp).1, (hE hp).2⟩
  have he := area_mono_of_finite hEC
    (volume_ne_top_of_subset sdiff_subset hCK.2.1.measure_lt_top.ne)
  have harea := area_inter_add_sdiff (S := C) hK.2.1.measurableSet hCK.2.1.measure_lt_top.ne
  rw [inter_eq_right.mpr hKC] at harea
  have hscale : area C = lam ^ 2 * area K := area_homotheticBody K z lam
  have hK0 : 0 ≤ area K := ENNReal.toReal_nonneg
  have hd2 : d ^ 2 ≤ d := by nlinarith [hd.1, hd.2]
  have hpoly : lam ^ 2 - 1 ≤ (2 / r + 1 / r ^ 2) * d := by
    dsimp [lam]
    field_simp [hr.ne']
    nlinarith [mul_nonneg hd.1 hr.le]
  have hm := mul_le_mul_of_nonneg_left hpoly hK0
  nlinarith

/-- Every fixed convex body with interior has a uniform linear outer-layer bound. -/
theorem exists_parallel_layer_constant {K : Set Point} (hK : IsConvexBody K)
    (hint : (interior K).Nonempty) :
    ∃ A : ℝ, 0 < A ∧ ∀ d ∈ Icc (0 : ℝ) 1, ∀ E : Set Point,
      E ⊆ (K + euclideanDisk d) \ K → area E ≤ A * d := by
  obtain ⟨z, r, hr, hb⟩ := exists_euclideanBall_subset_of_interior hint
  let A := 1 + area K * (2 / r + 1 / r ^ 2)
  have ha : 0 ≤ area K * (2 / r + 1 / r ^ 2) := by
    have hk : 0 ≤ area K := ENNReal.toReal_nonneg
    positivity
  refine ⟨A, by dsimp [A]; linarith, ?_⟩
  intro d hd E hE
  have he := area_parallel_layer_le hK hr hd hb hE
  have hm : area K * (2 / r + 1 / r ^ 2) * d ≤ A * d := by dsimp [A]; nlinarith [hd.1]
  exact he.trans hm

end MovingSofaStability

end ConvexParallelArea

/-!
## Area distance from actual-set closeness

A convex parallel layer and a thin vertical niche band control S minus G. The
area deficit then controls the opposite difference.
-/

section SymmetricDifference

open Real Set MeasureTheory
open scoped Pointwise
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

theorem roof_gap_of_close_point {K : Set Point} {a b H L : ℝ} {γ : ℝ → ℝ}
    (h : CapRoofData K a b H L γ) {p q : Point} {d : ℝ}
    (hp : p ∈ niche K (π / 2)) (hq : q ∈ capShape K)
    (hd : euclideanDist p q ≤ d) : γ p.1 - p.2 ≤ (L + 1) * d := by
  rw [h.niche_eq] at hp
  have hx : |p.1 - q.1| ≤ d := (abs_fst_le_norm2 (p - q)).trans hd
  have hy : |p.2 - q.2| ≤ d := (abs_snd_le_norm2 (p - q)).trans hd
  have hy0 := h.cap.snd_nonneg hq.1
  have hroof : γ p.1 - q.2 ≤ L * d := by
    by_cases hqa : a ≤ q.1
    · by_cases hqb : q.1 ≤ b
      · have hqy : γ q.1 ≤ q.2 := by
          by_contra hn
          exact hq.2 (by rw [h.niche_eq]; exact ⟨⟨hqa, hqb⟩, hy0, not_le.mp hn⟩)
        have he := (abs_le.mp (h.roof_lipschitz p.1 hp.1 q.1 ⟨hqa, hqb⟩)).2
        have hm := mul_le_mul_of_nonneg_left hx h.slope_nonneg
        linarith
      · have hqb' : b < q.1 := not_le.mp hqb
        have he := (abs_le.mp (h.roof_lipschitz p.1 hp.1 b ⟨h.order.le, le_rfl⟩)).2
        rw [h.right_zero, sub_zero, abs_of_nonpos (sub_nonpos.mpr hp.1.2)] at he
        have hbd : b - p.1 ≤ d := by
          have he := (abs_le.mp hx).1
          linarith
        have hm := mul_le_mul_of_nonneg_left hbd h.slope_nonneg
        linarith
    · have hqa' : q.1 < a := not_le.mp hqa
      have he := (abs_le.mp (h.roof_lipschitz p.1 hp.1 a ⟨le_rfl, h.order.le⟩)).2
      rw [h.left_zero, sub_zero, abs_of_nonneg (sub_nonneg.mpr hp.1.1)] at he
      have had : p.1 - a ≤ d := by
        have he := (abs_le.mp hx).2
        linarith
      have hm := mul_le_mul_of_nonneg_left had h.slope_nonneg
      linarith
  have hdy := (abs_le.mp hy).1
  nlinarith

/-- The band between `F - 2e` and `F + e` over `[a, b]` has measure `3e(b - a)`: its vertical
sections have the constant length `3e`. -/
private theorem volume_continuous_band {F : ℝ → ℝ} (hF : Continuous F) {a b e : ℝ}
    (he : 0 ≤ e) :
    volume (regionBetween (fun x => F x - 2 * e) (fun x => F x + e) (Icc a b)) =
      ENNReal.ofReal (3 * e * (b - a)) := by
  have h1 : Measurable fun x => F x - 2 * e := (hF.sub continuous_const).measurable
  have h2 : Measurable fun x => F x + e := (hF.add continuous_const).measurable
  rw [Measure.volume_eq_prod, volume_regionBetween_eq_lintegral' h1 h2 measurableSet_Icc]
  have heq : ∀ x, ((fun x => F x + e) - (fun x => F x - 2 * e)) x = 3 * e := fun x => by
    simp only [Pi.sub_apply]
    ring
  simp only [heq, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Icc]
  rw [← ENNReal.ofReal_mul (by positivity), mul_assoc]

theorem area_continuous_band {F : ℝ → ℝ} (hF : Continuous F) {a b e : ℝ}
    (hab : a ≤ b) (he : 0 ≤ e) :
    area (regionBetween (fun x => F x - 2 * e) (fun x => F x + e) (Icc a b)) =
      3 * e * (b - a) := by
  unfold area
  rw [volume_continuous_band hF he, ENNReal.toReal_ofReal]
  have := sub_nonneg.mpr hab
  positivity

theorem CapRoofData.outer_area_bound {K : Set Point} {a b H L : ℝ} {γ : ℝ → ℝ}
    (h : CapRoofData K a b H L γ) :
    ∃ A : ℝ, 0 < A ∧ ∀ S : Set Point, IsCompact S → ∀ d ∈ Ioc (0 : ℝ) 1,
      DirectedClose d S (capShape K) → area (S \ capShape K) ≤ A * d := by
  obtain ⟨A0, hA0, hparallel⟩ := exists_parallel_layer_constant h.cap.2.1
    (interior_nonempty_of_box h.order (by norm_num) h.rectangle)
  let A := A0 + 3 * (L + 1) * (b - a)
  have hL := h.slope_nonneg
  have hab := sub_pos.mpr h.order
  have hA : 0 < A := by
    have : 0 ≤ 3 * (L + 1) * (b - a) := by positivity
    dsimp [A]
    linarith
  let F : ℝ → ℝ := fun x => γ (max a (min x b))
  have hF : Continuous F := continuous_clamped_roof h.order.le h.slope_nonneg h.roof_lipschitz
  have hFeq : ∀ x ∈ Icc a b, F x = γ x := by
    intro x hx
    simp only [F, min_eq_left hx.2, max_eq_right hx.1]
  refine ⟨A, hA, ?_⟩
  intro S hS d hd hclose
  let E := S \ capShape K
  let Eout := E \ K
  let Ein := E ∩ K
  have hEf : volume E ≠ ⊤ := volume_ne_top_of_subset sdiff_subset hS.measure_lt_top.ne
  have hout : Eout ⊆ (K + euclideanDisk d) \ K := by
    rintro p ⟨⟨hpS, -⟩, hpK⟩
    obtain ⟨q, hq, hpq⟩ := hclose p hpS
    exact ⟨⟨q, hq.1, p - q, hpq, add_sub_cancel q p⟩, hpK⟩
  have hareaOut := hparallel d ⟨hd.1.le, hd.2⟩ Eout hout
  let e := (L + 1) * d
  have he : 0 < e := mul_pos (by linarith) hd.1
  let Band := regionBetween (fun x => F x - 2 * e) (fun x => F x + e) (Icc a b)
  have hin : Ein ⊆ Band := by
    rintro p ⟨⟨hpS, hpG⟩, hpK⟩
    have hpN : p ∈ niche K (π / 2) := by
      by_contra hn
      exact hpG ⟨hpK, hn⟩
    obtain ⟨q, hq, hpq⟩ := hclose p hpS
    have hgap := roof_gap_of_close_point h hpN hq hpq
    rw [h.niche_eq] at hpN
    refine ⟨hpN.1, ?_, ?_⟩
    · change F p.1 - 2 * e < p.2
      rw [hFeq p.1 hpN.1]
      change γ p.1 - p.2 ≤ e at hgap
      linarith
    · change p.2 < F p.1 + e
      rw [hFeq p.1 hpN.1]
      linarith [hpN.2.2]
  have hBandf : volume Band ≠ ⊤ := by
    rw [volume_continuous_band hF he.le]
    exact ENNReal.ofReal_ne_top
  have hareaIn := area_mono_of_finite hin hBandf
  rw [area_continuous_band hF h.order.le he.le] at hareaIn
  have hsplit := area_inter_add_sdiff (S := E) h.cap.2.1.2.1.measurableSet hEf
  change area Ein + area Eout = area E at hsplit
  dsimp [A, e] at *
  linarith

theorem symmetricDifferenceArea_eq {S G : Set Point} (hS : MeasurableSet S)
    (hG : MeasurableSet G) (hSf : volume S ≠ ⊤) (hGf : volume G ≠ ⊤) :
    symmetricDifferenceArea S G = area G - area S + 2 * area (S \ G) := by
  have hd : Disjoint (S \ G) (G \ S) := by
    rw [Set.disjoint_left]
    intro p hp hq
    exact hp.2 hq.1
  rw [symmetricDifferenceArea, area_union_of_disjoint hd (hG.diff hS)
    (volume_ne_top_of_subset sdiff_subset hSf) (volume_ne_top_of_subset sdiff_subset hGf),
    area_sdiff_balance hS hG hSf hGf]
  ring

theorem gerver_symmetricDifference_from_distance {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {C : ℝ} (hC : 0 < C) :
    ∃ Carea ε₀ : ℝ, 0 < Carea ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ∀ S : Set Point, IsCompact S → ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      ε = area (gerverSofa P) - area S →
      EuclideanClose (C * sqrt ε) S (gerverSofa P) →
        symmetricDifferenceArea S (gerverSofa P) ≤ Carea * sqrt ε := by
  obtain ⟨H, L, γ, hroof⟩ := gerver_roof_data hP hbox
  obtain ⟨A, hA, hbound⟩ := hroof.outer_area_bound
  obtain ⟨ε₀, hε₀, hε₀1, hsmall⟩ := exists_sqrt_threshold hC.le (show (0 : ℝ) < 1 by norm_num)
  let Carea := 1 + 2 * A * C
  refine ⟨Carea, ε₀ / 2, by dsimp [Carea]; positivity, by positivity, by linarith, ?_⟩
  intro S hS ε hε hεeq hclose
  have hεsmall : ε < ε₀ := by linarith [hε.2]
  have hdpos : 0 < C * sqrt ε := mul_pos hC (sqrt_pos.mpr hε.1)
  have hd1 := hsmall ε hε.1.le hεsmall
  have he := hbound S hS (C * sqrt ε) ⟨hdpos, hd1.le⟩
    (by simpa only [gerver_shape_eq hP hbox] using hclose.1)
  rw [gerver_shape_eq hP hbox] at he
  have hG := ms_isCompact_of_isMovingSofaWithAngle (GerverParams.gm_movingSofa_std hP hbox).1
  rw [symmetricDifferenceArea_eq hS.measurableSet hG.measurableSet hS.measure_lt_top.ne
    hG.measure_lt_top.ne, ← hεeq]
  have hs := self_le_sqrt_of_unit ⟨hε.1.le, hεsmall.le.trans hε₀1⟩
  dsimp [Carea]
  nlinarith

end MovingSofaStability

end SymmetricDifference
