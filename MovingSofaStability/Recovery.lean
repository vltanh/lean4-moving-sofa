module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import MovingSofaExtremal.Main
public import MovingSofaStability.Terminal

/-!
# From the cap back to the sofa

A moving sofa lies in its supporting hallways and in its terminal strip, and its cap `sofaCap S`
has the sofa's upper supports. With the margins of Gerver's sofa, the distance between the caps and
the missing area bound the Euclidean distance between the sofa and Gerver's
(`local_positive_sofa_hausdorff`), and a parallel-layer estimate bounds their symmetric difference
(`gerver_symmetricDifference_from_distance`).
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open scoped Pointwise
open MovingSofaOptimality MovingSofaUniqueness GerverParams

namespace MovingSofaStability

/-! ## Hallways and the terminal strip of a moving sofa -/

/-- A moving sofa lies in each of its supporting hallways, without standard-position assumptions. -/
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

/-- Each point of a moving sofa has a nonnegative inner slack in each supporting hallway; this
closed condition passes to limits. -/
theorem moving_hallway_slacks {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) {p : Point} (hp : p ∈ S)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) ω) :
    0 ≤ max (innerSlackU S t p) (innerSlackV S t p) := by
  have he := moving_supporting_hallways hS ht hp
  rw [proposition2_2_2_hallway] at he
  exact not_lt.mp fun hn => he.2 ((mem_qMinus_iff_slacks S t p).2 (max_lt_iff.mp hn))

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

/-- Each point of a moving sofa lies within distance one of its terminal supporting line. -/
theorem moving_terminal_lower {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) {p : Point} (hp : p ∈ S) :
    supp S ω - 1 ≤ dot p (uvec ω) := by
  obtain ⟨q, hq, he⟩ := exists_dot_eq_supp (ms_isCompact_of_isMovingSofaWithAngle hS)
    hS.2.1.nonempty ω
  have h := moving_terminal_projection hS hp hq
  rw [dot_sub_left, he] at h
  linarith

/-- A moving sofa has width at most one in its terminal direction. -/
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
  obtain ⟨q, hq, hqy⟩ := exists_dot_eq_supp hc hS.choose_spec.2.1.nonempty (π / 2)
  rw [dot_uvec_pi_div_two, htop] at hqy
  intro p hp
  have hu := dot_le_supp hc hp (π / 2)
  rw [dot_uvec_pi_div_two, htop] at hu
  exact ⟨by linarith [snd_sub_le_one_of_isMovingSofa hS hq hp], hu⟩

/-- The normalized sofa moves with the same rotation angle. -/
theorem normalizedSofa_movingWithAngle (P : GerverParams) {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) : IsMovingSofaWithAngle (normalizedSofa P S) ω := by
  simpa only [normalizedSofa, Rigid.coe_translate] using
    mpc_isMovingSofaWithAngle_translate hS (normalizingShift P S)

/-- The normalized sofa is a moving sofa. -/
theorem normalizedSofa_moving (P : GerverParams) {S : Set Point} (hS : IsMovingSofa S) :
    IsMovingSofa (normalizedSofa P S) :=
  ⟨hS.choose, normalizedSofa_movingWithAngle P hS.choose_spec⟩

/-- The normalized sofa lies in the horizontal unit strip. -/
theorem normalizedSofa_strip (P : GerverParams) {S : Set Point} (hS : IsMovingSofa S) :
    normalizedSofa P S ⊆ hStrip :=
  moving_strip_of_top (normalizedSofa_moving P hS)
    (normalizedSofa_top P (isCompact_of_isMovingSofa hS) hS.choose_spec.2.1.nonempty)

/-- Gerver's cap and sofa have identical upper-semicircle supports. -/
theorem gerver_upper_support {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) π) : supp P.cap t = supp (gerverSofa P) t := by
  have hJ : t ∈ jSet (π / 2) := by
    rcases le_total t (π / 2) with hv | hv
    · exact Or.inl ⟨ht.1, hv⟩
    · exact Or.inr ⟨hv, by linarith [ht.2]⟩
  exact (lemma2_3_5_supp ⟨by positivity, le_rfl⟩ (gm_movingSofa_std hP hbox).1
    (gm_movingSofa_std hP hbox).2 hJ).2

/-- In the pinned frame, a moving sofa of area `|G|` is Gerver's sofa: it is a translate of `G`
(`MovingSofaExtremal.translate_eq_gerver_of_volume_eq`), and the two supports fix the
translation. -/
theorem pinned_maximizer_eq_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Point} (hS : IsMovingSofa S) (htop : supp S (π / 2) = 1)
    (hleft : supp S π = supp (gerverSofa P) π) (harea : area S = area (gerverSofa P)) :
    S = gerverSofa P := by
  have hcompact := isCompact_of_isMovingSofa hS
  have hne := hS.choose_spec.2.1.nonempty
  obtain ⟨w, hw⟩ := MovingSofaExtremal.translate_eq_gerver_of_volume_eq hP hbox hS
    ((ENNReal.toReal_eq_toReal_iff' hcompact.measure_lt_top.ne
      (gerverSofa_volume_ne_top hP hbox)).1 harea)
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

/-! ## The cap of a sofa

The cap is the set of points above the floor and below the sofa's upper supporting lines. It
contains a sofa in the horizontal strip and has the same upper supports; the sofa itself need not
be convex or admit a full-angle movement. -/

/-- The cap of a sofa: the points above the floor below all its upper supporting lines. -/
def sofaCap (S : Set Point) : Set Point :=
  {p | 0 ≤ p.2 ∧ ∀ t ∈ Icc (0 : ℝ) π, dot p (uvec t) ≤ supp S t}

theorem subset_sofaCap {S : Set Point} (hS : IsCompact S) (hstrip : S ⊆ hStrip) : S ⊆ sofaCap S :=
  fun _ hp => ⟨(hstrip hp).1, fun t _ => dot_le_supp hS hp t⟩

theorem sofaCap_convex (S : Set Point) : Convex ℝ (sofaCap S) := by
  intro p hp q hq a b ha hb hab
  refine ⟨by simpa only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] using
    add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1), fun t ht => ?_⟩
  have h1 := mul_le_mul_of_nonneg_left (hp.2 t ht) ha
  have h2 := mul_le_mul_of_nonneg_left (hq.2 t ht) hb
  rw [dot_add_left, dot_smul_left, dot_smul_left]
  linarith [show a * supp S t + b * supp S t = supp S t by rw [← add_mul, hab, one_mul]]

theorem sofaCap_compact {S : Set Point} (htop : supp S (π / 2) = 1) : IsCompact (sofaCap S) := by
  have hclosed : IsClosed (sofaCap S) := by
    simp only [sofaCap, ofPred_and, ofPred_forall]
    exact (isClosed_le continuous_const continuous_snd).inter (isClosed_iInter fun t =>
      isClosed_iInter fun _ => isClosed_le (continuous_dot _) continuous_const)
  refine IsCompact.of_isClosed_subset (s := Icc (-supp S π) (supp S 0) ×ˢ Icc (0 : ℝ) 1)
    (isCompact_Icc.prod isCompact_Icc) hclosed fun p hp => ?_
  have h0 := hp.2 0 ⟨le_rfl, pi_pos.le⟩
  have hπ := hp.2 π ⟨pi_pos.le, le_rfl⟩
  have hv := hp.2 (π / 2) ⟨by positivity, by linarith [pi_pos]⟩
  rw [dot_uvec_zero] at h0
  simp only [dot, uvec_pi] at hπ
  rw [dot_uvec_pi_div_two, htop] at hv
  exact ⟨⟨by linarith, h0⟩, hp.1, hv⟩

/-- The cap of a compact set in the strip has the set's upper supports. -/
theorem sofaCap_upper_support {S : Set Point} (hS : IsCompact S) (hne : S.Nonempty)
    (hstrip : S ⊆ hStrip) (htop : supp S (π / 2) = 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) π) : supp (sofaCap S) t = supp S t := by
  have hsub := subset_sofaCap hS hstrip
  exact le_antisymm (supp_le_of_forall (hne.mono hsub) (fun p hp => hp.2 t ht))
    (supp_mono hsub hne (sofaCap_compact htop) t)

/-- The cap of a compact set in the strip with top support one is a right-angle cap. -/
theorem sofaCap_isCap {S : Set Point} (hS : IsCompact S) (hne : S.Nonempty)
    (hstrip : S ⊆ hStrip) (htop : supp S (π / 2) = 1) : IsCap (sofaCap S) (π / 2) := by
  have hcpt := sofaCap_compact htop
  have hneC := hne.mono (subset_sofaCap hS hstrip)
  have htopC : supp (sofaCap S) (π / 2) = 1 :=
    (sofaCap_upper_support hS hne hstrip htop ⟨by positivity, by linarith [pi_pos]⟩).trans htop
  obtain ⟨p, hp⟩ := id hneC
  -- the foot of `p` on the floor is in the cap
  have hfloor : (p.1, 0) ∈ sofaCap S := ⟨le_rfl, fun t ht => by
    have he := hp.2 t ht
    simp only [dot, uvec] at he ⊢
    nlinarith [mul_nonneg hp.1 (sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2)]⟩
  have hbottom : supp (sofaCap S) (3 * π / 2) = 0 := by
    refine le_antisymm (supp_le_of_forall hneC fun q hq => ?_) ?_
    · rw [dot_uvec_three_pi_div_two]
      linarith [hq.1]
    · simpa only [dot_uvec_three_pi_div_two, neg_zero] using dot_le_supp hcpt hfloor (3 * π / 2)
  refine ⟨⟨by positivity, le_rfl⟩, ⟨hneC, hcpt, sofaCap_convex S⟩, htopC, htopC,
    by rwa [show π / 2 + π = 3 * π / 2 by ring], hbottom,
    Option (Icc (0 : ℝ) π), fun i => i.elim (3 * π / 2) Subtype.val,
    fun i => i.elim 0 fun t => supp S t, ?_, ?_⟩
  · rintro (_ | ⟨t, ht⟩)
    · exact Or.inr (by simp)
    · rcases le_total t (π / 2) with h | h
      · exact Or.inl (Or.inl ⟨ht.1, h⟩)
      · exact Or.inl (Or.inr ⟨h, show t ≤ π / 2 + π / 2 by linarith [ht.2]⟩)
  · ext q
    simp only [sofaCap, mem_iInter, Option.forall, Option.elim, halfMinus, mem_ofPred_eq,
      dot_uvec_three_pi_div_two, neg_nonpos, Subtype.forall]

/-- If a sofa is within Euclidean distance `δ` of Gerver's, the upper supports of its cap are within
`δ` of those of Gerver's cap. -/
theorem sofaCap_close_to_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Point} (hS : IsCompact S) (hne : S.Nonempty) (hstrip : S ⊆ hStrip)
    (htop : supp S (π / 2) = 1) {δ : ℝ} (hclose : EuclideanClose δ S (gerverSofa P)) :
    UpperSupportClose δ (sofaCap S) P.cap := by
  intro t ht
  rw [sofaCap_upper_support hS hne hstrip htop ht, gerver_upper_support hP hbox ht]
  have hG := (gm_movingSofa_std hP hbox).1
  exact hclose.abs_supp_sub_le hS (ms_isCompact_of_isMovingSofaWithAngle hG) hne hG.2.1.nonempty t

/-- A moving sofa with rotation angle `ω ≤ π/2` and top support one satisfies the hallway and
terminal constraints relative to its cap. -/
theorem sofaCap_partial_constraints {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) (hω : ω ∈ Icc (0 : ℝ) (π / 2))
    (htop : supp S (π / 2) = 1) : PartialSofaConstraints (sofaCap S) S ω := by
  have hcpt := ms_isCompact_of_isMovingSofaWithAngle hS
  have hstrip := moving_strip_of_top ⟨ω, hS⟩ htop
  have hs : ∀ {t : ℝ}, t ∈ Icc (0 : ℝ) π → supp (sofaCap S) t = supp S t :=
    sofaCap_upper_support hcpt hS.2.1.nonempty hstrip htop
  refine ⟨subset_sofaCap hcpt hstrip, fun p hp t ht => ?_, fun p hp => ?_⟩
  · have h1 := hs ⟨ht.1, ht.2.trans (hω.2.trans (by linarith [pi_pos]))⟩
    have h2 := hs (t := t + π / 2) ⟨by linarith [ht.1, pi_pos], by linarith [ht.2, hω.2]⟩
    simpa only [innerSlackU, innerSlackV, h1, h2] using moving_hallway_slacks hS hp ht
  · rw [hs ⟨hω.1, by linarith [hω.2, pi_pos]⟩]
    exact moving_terminal_lower hS hp

/-! ## The local recovery of the sofa

The cap, terminal, erosion and roof estimates are assembled on one neighborhood of Gerver's cap; the
global step only has to enter it. The sofa need not lie in its full-angle shape, and the conclusion
concerns its own, possibly nonconvex, points. -/

/-- A threshold below which a fixed multiple of `√ε` stays below a given bound. -/
theorem exists_sqrt_threshold {A r : ℝ} (hA : 0 ≤ A) (hr : 0 < r) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, ε < ε₀ → A * sqrt ε < r := by
  have hq : 0 < r / (A + 1) := div_pos hr (by linarith)
  refine ⟨min 1 ((r / (A + 1)) ^ 2), lt_min one_pos (by positivity), min_le_left _ _,
    fun ε hε => ?_⟩
  have hs := (sqrt_lt' hq).2 (hε.trans_le (min_le_right _ _))
  calc A * sqrt ε ≤ A * (r / (A + 1)) := mul_le_mul_of_nonneg_left hs.le hA
    _ < (A + 1) * (r / (A + 1)) := by linarith
    _ = r := by field_simp

theorem self_le_sqrt_of_unit {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) 1) : ε ≤ sqrt ε :=
  (le_sqrt hε.1 hε.1).2 (_root_.sq_le hε.1 hε.2)

/-- Near Gerver's cap, a set satisfying the hallway and terminal constraints of a cap with Gerver's
left support, with small area deficit `ε`, lies within `C √ε` of Gerver's sofa, and its rotation
angle is within `ε / c` of `π/2`. Neither smoothness nor injectivity is assumed. -/
theorem local_positive_sofa_hausdorff {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ C c δ α₀ ε₀ : ℝ,
      0 < C ∧ 0 < c ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < α₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ∀ K : Set Point, IsCap K (π / 2) → supp K π = supp P.cap π →
      UpperSupportClose δ K P.cap → ∀ S : Set Point, MeasurableSet S →
      ∀ ω ∈ Icc (0 : ℝ) (π / 2), π / 2 - ω ≤ α₀ → PartialSofaConstraints K S ω →
      ∀ ε : ℝ, ε = area (gerverSofa P) - area S → 0 < ε → ε < ε₀ →
        EuclideanClose (C * sqrt ε) S (gerverSofa P) ∧ π / 2 - ω ≤ ε / c := by
  obtain ⟨c, δT, α₀, R, hc, hδT, hδT1, hα₀, hR, hterminal⟩ := nearby_terminal_comparison hP hbox
  obtain ⟨δK, hδK, -, hcapestimate⟩ := nearby_cap_distance hP hbox
  obtain ⟨H, L, γ, cr, τ, d₀, κ, r₀, hroof, hcr, hτ, hd₀, hκ, hr₀,
    hslack, houter, hballs⟩ := gerver_recovery_constants hP hbox
  -- `a √ε` bounds the cap distance and `B √ε` the hallway defect
  set a := 2 / cos P.φ
  have ha : 0 < a :=
    div_pos two_pos (cap_angle_parameters (gm_φ_mem_Ioo hP hbox)).1
  set B := 4 * R / c with hB_def
  have hB : 0 ≤ B := div_nonneg (by linarith) hc.le
  set Cf := max 1 (1 / cr) * (a + B)
  set Cb := 4 * (2 * a + 1) / κ
  obtain ⟨εd, hεd, hεd1, hsmallD⟩ := exists_sqrt_threshold ha.le hd₀
  obtain ⟨εt, hεt, -, hsmallT⟩ := exists_sqrt_threshold (A := a + B) (by linarith) hτ
  obtain ⟨εr, hεr, -, hsmallR⟩ := exists_sqrt_threshold (A := Cb)
    (div_nonneg (by linarith) hκ.le) hr₀
  refine ⟨max 1 (max Cf Cb), c, min δT δK, α₀, min εd (min εt εr),
    lt_max_of_lt_left one_pos, hc, lt_min hδT hδK, (min_le_left _ _).trans hδT1, hα₀,
    lt_min hεd (lt_min hεt hεr), (min_le_left _ _).trans hεd1, ?_⟩
  intro K hK hleft hclose S hS ω hω hα hconstraints ε hεeq hε hεsmall
  have hεd' : ε < εd := hεsmall.trans_le (min_le_left _ _)
  have hεt' : ε < εt := hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεr' : ε < εr := hεsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨-, hangle, hdeficit, -, hUS, hhall⟩ :=
    hterminal K hK (hclose.mono (min_le_left _ _)) S hS ω hω hα hconstraints
  rw [← hεeq] at hangle hdeficit hUS
  obtain ⟨-, -, hdist⟩ := hcapestimate K hK (hclose.mono (min_le_right _ _))
  rw [shiftedReferenceCap_eq_of_left_support hleft] at hdist
  have hsupport : UpperSupportClose (a * sqrt ε) K P.cap := fun t _ =>
    (hdist.mono (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hdeficit) ha.le)).abs_supp_sub_le
      hK.2.1.2.1 hroof.cap.2.1.2.1 hK.2.1.1 hroof.cap.2.1.1 t
  have hζ : 4 * R * (π / 2 - ω) ≤ B * sqrt ε :=
    calc 4 * R * (π / 2 - ω) ≤ 4 * R * (ε / c) :=
          mul_le_mul_of_nonneg_left hangle (by linarith)
      _ = B * ε := by rw [hB_def]; ring
      _ ≤ B * sqrt ε := mul_le_mul_of_nonneg_left
          (self_le_sqrt_of_unit ⟨hε.le, (hεd'.trans_le hεd1).le⟩) hB
  have hfront := directed_to_reference_of_margins hroof hK hcr
    (mul_nonneg ha.le (sqrt_nonneg ε)) (mul_nonneg hB (sqrt_nonneg ε)) hsupport houter
    (hsmallD ε hεd') (by linarith [hsmallT ε hεt']) hslack hconstraints.1
    (fun p hp t ht => (neg_le_neg hζ).trans (hhall p hp t ht))
  have hback := reference_to_sofa_recovery hroof.cap hK (mul_nonneg ha.le (sqrt_nonneg ε))
    hsupport hκ (A := 2 * a) (by linarith) hε
    (by simpa only [gerver_shape_eq hP hbox] using hballs) (le_of_eq (by ring))
    (hsmallR ε hεr').le (volume_ne_top_of_subset sdiff_subset hK.2.1.2.1.measure_lt_top.ne) hUS
  rw [gerver_shape_eq hP hbox] at hfront hback
  refine ⟨⟨hfront.mono ?_, hback.mono ?_⟩, hangle⟩
  · calc max 1 (1 / cr) * (a * sqrt ε + B * sqrt ε) = Cf * sqrt ε := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _))
          (sqrt_nonneg ε)
  · exact mul_le_mul_of_nonneg_right ((le_max_right Cf Cb).trans (le_max_right _ _))
      (sqrt_nonneg ε)

/-! ## Outer parallel layers

A fixed interior disk puts the Euclidean parallel body inside a homothetic copy, whose area is given
by Haar scaling; no smoothness or perimeter formula is needed. -/

/-- The image of `K` under the homothety with center `z` and ratio `lam`. -/
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
  obtain ⟨p, hp, he⟩ := exists_dot_eq_supp hK.2.1 hK.1 t
  apply supp_eq_of_mem (homotheticBody_convexBody hK z lam).2.1
  · rintro _ ⟨q, hq, rfl⟩
    have h := mul_le_mul_of_nonneg_left (dot_le_supp hK.2.1 hq t) hlam
    rw [dot_add_left, dot_smul_left, dot_sub_left]
    linarith
  · exact mem_image_of_mem _ hp
  · rw [dot_add_left, dot_smul_left, dot_sub_left, he]
    ring

theorem area_homotheticBody (K : Set Point) (z : Point) (lam : ℝ) :
    area (homotheticBody K z lam) = lam ^ 2 * area K := by
  have he := Measure.addHaar_image_homothety (volume : Measure Point) z lam K
  change volume (homotheticBody K z lam) = _ at he
  have hdim : Module.finrank ℝ Point = 2 := by simp [Point, Module.finrank_prod]
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
  simpa only [dot_add_left, dot_smul_left, dot_uvec_self, mul_one] using
    dot_le_supp hK.2.1 (hball hp) t

/-- The parallel body fits inside the dilation by `1 + d / r` about the center of an inscribed
ball of radius `r`. -/
theorem parallel_subset_homothetic {K : Set Point} (hK : IsConvexBody K) {z : Point}
    {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) (hball : euclideanBall z r ⊆ K) :
    K + euclideanDisk d ⊆ homotheticBody K z (1 + d / r) := by
  intro p hp
  refine (mem_iff_forall_dot_le_supp (homotheticBody_convexBody hK z _) p).2 fun t => ?_
  have h1 := dot_le_supp (convexBody_add hK (euclideanDisk_isConvexBody hd)).2.1 hp t
  rw [supp_add_euclideanDisk hK hd] at h1
  have hm := mul_le_mul_of_nonneg_left (support_margin_of_ball hK hr.le hball t)
    (div_nonneg hd hr.le)
  rw [homotheticBody_support hK z (by positivity)]
  have hc : d / r * r = d := div_mul_cancel₀ _ hr.ne'
  nlinarith

/-- Every convex body with interior has a uniform linear bound for the area of any subset of a thin
outer parallel layer. -/
theorem exists_parallel_layer_constant {K : Set Point} (hK : IsConvexBody K)
    (hint : (interior K).Nonempty) :
    ∃ A : ℝ, 0 < A ∧ ∀ d ∈ Icc (0 : ℝ) 1, ∀ E : Set Point,
      E ⊆ (K + euclideanDisk d) \ K → area E ≤ A * d := by
  obtain ⟨z, r, hr, hball⟩ := exists_euclideanBall_subset_of_interior hint
  have hK0 : 0 ≤ area K := ENNReal.toReal_nonneg
  refine ⟨1 + area K * (2 / r + 1 / r ^ 2), by positivity, fun d hd E hE => ?_⟩
  -- `E` lies in `C \ K` for the dilation `C` by `1 + d / r`, of area `(1 + d / r) ^ 2 |K|`
  have hC := homotheticBody_convexBody hK z (1 + d / r)
  have hsub := parallel_subset_homothetic hK hr hd.1 hball
  have hKC : K ⊆ homotheticBody K z (1 + d / r) := fun p hp =>
    hsub ⟨p, hp, 0, by simpa only [euclideanDisk, mem_ofPred_eq, norm2_zero] using hd.1,
      add_zero p⟩
  have he := area_mono_of_finite
    (show E ⊆ homotheticBody K z (1 + d / r) \ K from fun p hp => ⟨hsub (hE hp).1, (hE hp).2⟩)
    (volume_ne_top_of_subset sdiff_subset hC.2.1.measure_lt_top.ne)
  have harea := area_inter_add_sdiff hK.2.1.measurableSet hC.2.1.measure_lt_top.ne
  rw [inter_eq_right.mpr hKC, area_homotheticBody] at harea
  have hpoly : (1 + d / r) ^ 2 - 1 ≤ (2 / r + 1 / r ^ 2) * d := by
    field_simp
    nlinarith [mul_nonneg hd.1 hr.le, hd.2]
  linarith [mul_le_mul_of_nonneg_left hpoly hK0, hd.1]

/-! ## The symmetric difference

A convex parallel layer and a thin band under the roof of the niche bound the part of the sofa
outside Gerver's; the area deficit then bounds the other part. -/

/-- A niche point close to a point of the cap shape lies at most `(L + 1) d` below the roof. -/
theorem roof_gap_of_close_point {K : Set Point} {a b H L : ℝ} {γ : ℝ → ℝ}
    (h : CapRoofData K a b H L γ) {p q : Point} {d : ℝ}
    (hp : p ∈ niche K (π / 2)) (hq : q ∈ capShape K)
    (hd : euclideanDist p q ≤ d) : γ p.1 - p.2 ≤ (L + 1) * d := by
  rw [h.niche_eq] at hp
  have hx : |p.1 - q.1| ≤ d := (abs_fst_le_norm2 (p - q)).trans hd
  have hy : |p.2 - q.2| ≤ d := (abs_snd_le_norm2 (p - q)).trans hd
  have hy0 := h.cap.snd_nonneg hq.1
  -- a point `x` of `[a, b]` at most `d` from `p.1` where the roof is below `q`
  obtain ⟨x, hx, hγx, hxd⟩ : ∃ x ∈ Icc a b, γ x ≤ q.2 ∧ |p.1 - x| ≤ d := by
    rcases lt_or_ge q.1 a with hqa | hqa
    · refine ⟨a, ⟨le_rfl, h.order.le⟩, h.left_zero ▸ hy0, ?_⟩
      rw [abs_of_nonneg (sub_nonneg.mpr hp.1.1)]
      linarith [(abs_le.mp hx).2]
    rcases le_or_gt q.1 b with hqb | hqb
    · refine ⟨q.1, ⟨hqa, hqb⟩, not_lt.mp fun hn => hq.2 ?_, hx⟩
      rw [h.niche_eq]
      exact ⟨⟨hqa, hqb⟩, hy0, hn⟩
    · refine ⟨b, ⟨h.order.le, le_rfl⟩, h.right_zero ▸ hy0, ?_⟩
      rw [abs_of_nonpos (sub_nonpos.mpr hp.1.2)]
      linarith [(abs_le.mp hx).1]
  have he := (abs_le.mp (h.roof_lipschitz p.1 hp.1 x hx)).2
  linarith [mul_le_mul_of_nonneg_left hxd h.slope_nonneg, (abs_le.mp hy).1]

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

/-- The part of a compact set `S` outside the cap shape has area linear in the directed distance
from `S` to the cap shape. -/
theorem CapRoofData.outer_area_bound {K : Set Point} {a b H L : ℝ} {γ : ℝ → ℝ}
    (h : CapRoofData K a b H L γ) :
    ∃ A : ℝ, 0 < A ∧ ∀ S : Set Point, IsCompact S → ∀ d ∈ Ioc (0 : ℝ) 1,
      DirectedClose d S (capShape K) → area (S \ capShape K) ≤ A * d := by
  obtain ⟨A0, hA0, hparallel⟩ := exists_parallel_layer_constant h.cap.2.1
    (interior_nonempty_of_box h.order (by norm_num) h.rectangle)
  have hL := h.slope_nonneg
  have hab := sub_pos.mpr h.order
  obtain ⟨F, hF, hFeq⟩ : ∃ F : ℝ → ℝ, Continuous F ∧ ∀ x ∈ Icc a b, F x = γ x :=
    ⟨_, continuous_clamped_roof h.order.le hL h.roof_lipschitz,
      fun x hx => by simp only [min_eq_left hx.2, max_eq_right hx.1]⟩
  refine ⟨A0 + 3 * (L + 1) * (b - a), by positivity, fun S hS d hd hclose => ?_⟩
  -- outside `K`, the points of `S` lie in the outer parallel layer
  have hout := hparallel d ⟨hd.1.le, hd.2⟩ ((S \ capShape K) \ K) (by
    rintro p ⟨⟨hpS, -⟩, hpK⟩
    obtain ⟨q, hq, hpq⟩ := hclose p hpS
    exact ⟨⟨q, hq.1, p - q, hpq, add_sub_cancel q p⟩, hpK⟩)
  -- inside `K`, they lie in the niche, at most `(L + 1) d` below the roof
  have he : 0 < (L + 1) * d := mul_pos (by linarith) hd.1
  have hin : (S \ capShape K) ∩ K ⊆ regionBetween (fun x => F x - 2 * ((L + 1) * d))
      (fun x => F x + (L + 1) * d) (Icc a b) := by
    rintro p ⟨⟨hpS, hpG⟩, hpK⟩
    have hpN : p ∈ niche K (π / 2) := by_contra fun hn => hpG ⟨hpK, hn⟩
    obtain ⟨q, hq, hpq⟩ := hclose p hpS
    have hgap := roof_gap_of_close_point h hpN hq hpq
    rw [h.niche_eq] at hpN
    refine ⟨hpN.1, ?_, ?_⟩ <;> simp only [hFeq p.1 hpN.1]
    · linarith
    · linarith [hpN.2.2]
  have hvol := volume_continuous_band hF he.le (a := a) (b := b)
  have hareaIn : area ((S \ capShape K) ∩ K) ≤ 3 * ((L + 1) * d) * (b - a) :=
    (area_mono_of_finite hin (hvol ▸ ENNReal.ofReal_ne_top)).trans_eq
      (by rw [area, hvol, ENNReal.toReal_ofReal (by positivity)])
  have hsplit := area_inter_add_sdiff (S := S \ capShape K) h.cap.2.1.2.1.measurableSet
    (volume_ne_top_of_subset sdiff_subset hS.measure_lt_top.ne)
  linarith

theorem symmetricDifferenceArea_eq {S G : Set Point} (hS : MeasurableSet S)
    (hG : MeasurableSet G) (hSf : volume S ≠ ⊤) (hGf : volume G ≠ ⊤) :
    symmetricDifferenceArea S G = area G - area S + 2 * area (S \ G) := by
  rw [symmetricDifferenceArea, area_union_of_disjoint disjoint_sdiff_sdiff (hG.diff hS)
    (volume_ne_top_of_subset sdiff_subset hSf) (volume_ne_top_of_subset sdiff_subset hGf),
    area_sdiff_balance hS hG hSf hGf]
  ring

/-- A compact set within `C √ε` of Gerver's sofa, where `ε ≤ ε₀` is its area deficit, has symmetric
difference with Gerver's sofa of area at most a constant times `√ε`. -/
theorem gerver_symmetricDifference_from_distance {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {C : ℝ} (hC : 0 < C) :
    ∃ Carea ε₀ : ℝ, 0 < Carea ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ∀ S : Set Point, IsCompact S → ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      ε = area (gerverSofa P) - area S →
      EuclideanClose (C * sqrt ε) S (gerverSofa P) →
        symmetricDifferenceArea S (gerverSofa P) ≤ Carea * sqrt ε := by
  obtain ⟨H, L, γ, hroof⟩ := gerver_roof_data hP hbox
  obtain ⟨A, hA, hbound⟩ := hroof.outer_area_bound
  obtain ⟨ε₀, hε₀, hε₀1, hsmall⟩ := exists_sqrt_threshold hC.le one_pos
  refine ⟨1 + 2 * A * C, ε₀ / 2, by positivity, by positivity, by linarith,
    fun S hS ε hε hεeq hclose => ?_⟩
  have hεsmall : ε < ε₀ := by linarith [hε.2]
  have he := hbound S hS (C * sqrt ε) ⟨mul_pos hC (sqrt_pos.mpr hε.1), (hsmall ε hεsmall).le⟩
    (by simpa only [gerver_shape_eq hP hbox] using hclose.1)
  rw [gerver_shape_eq hP hbox] at he
  have hG := ms_isCompact_of_isMovingSofaWithAngle (gm_movingSofa_std hP hbox).1
  rw [symmetricDifferenceArea_eq hS.measurableSet hG.measurableSet hS.measure_lt_top.ne
    hG.measure_lt_top.ne, ← hεeq]
  linarith [self_le_sqrt_of_unit ⟨hε.1.le, hεsmall.le.trans hε₀1⟩]

end MovingSofaStability
