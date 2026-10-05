module

public import MovingSofaStability.ExposedFaceStability

/-!
# Uniform arm margins near an injective reference

Uncompiled proof source. The reference cap is injective; a competitor need
only be a normalized cap. Both endpoints of every competing exposed face
satisfy the margin, so polygonal and other nonsmooth competitors are included.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality

namespace MovingSofaStability

theorem UpperSupportClose.mono {δ R : ℝ} {K L : Set Point}
    (h : UpperSupportClose δ K L) (hδ : δ ≤ R) : UpperSupportClose R K L :=
  fun t ht => (h t ht).trans hδ

theorem injective_face_eq_aK {K : Set Point} (hK : IsCap K (π / 2)) (hI : InjCond1 K)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) (π / 2)) {p : Point} (hp : p ∈ edge K t) : p = aK K t := by
  have he := inj_vplus_eq_vminus_of_injCond1 hK.2.1 hI (Or.inl ht)
  rw [edge_eq_segment hK.2.1 t, he, segment_same] at hp
  exact mem_singleton_iff.mp hp

theorem injective_face_eq_cK {K : Set Point} (hK : IsCap K (π / 2)) (hI : InjCond1 K)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) (π / 2)) {p : Point} (hp : p ∈ edge K (t + π / 2)) :
    p = cK K t := by
  have he := inj_vplus_eq_vminus_of_injCond1 hK.2.1 hI
    (Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  rw [edge_eq_segment hK.2.1 (t + π / 2), ← he, segment_same] at hp
  exact mem_singleton_iff.mp hp

/-- A margin for all contacts at all normals of a compact interior angular interval. -/
def CoreArmMargin (K : Set Point) (a b c : ℝ) : Prop :=
  (∀ t ∈ Icc a b, ∀ p ∈ edge K t,
      1 + c ≤ supp K (t + π / 2) - dot p (vvec t)) ∧
  (∀ t ∈ Icc a b, ∀ p ∈ edge K (t + π / 2),
      1 + c ≤ supp K t - dot p (uvec t))

/-- The needed regularity is on the reference, not on every cap in its neighborhood. -/
theorem core_arm_margin_near_reference {K₀ : Set Point} (h₀ : IsKi K₀)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < π / 2) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K K₀ →
        CoreArmMargin K a b c := by
  have hcap := h₀.1
  have hI := h₀.2.1.1
  have hsub : Icc a b ⊆ Icc (0 : ℝ) (π / 2) := Icc_subset_Icc ha.le hb.le
  obtain ⟨-, -, hfc, hgc⟩ := proposition6_4_6_continuous hcap hI
  have hpositive : ∀ t ∈ Icc a b, 0 < min (fK K₀ t - 1) (gK K₀ t - 1) := by
    intro t ht
    have hti : t ∈ Ioo (0 : ℝ) (π / 2) := ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
    obtain ⟨hf, hg⟩ := opt_arm_gt_one h₀ hti
    exact lt_min (sub_pos.mpr hf) (sub_pos.mpr hg)
  obtain ⟨m, hm, hmle⟩ := isCompact_Icc.exists_forall_le'
    (((hfc.mono hsub).sub continuousOn_const).min ((hgc.mono hsub).sub continuousOn_const))
    hpositive
  let FA := fun p : Point => fun t : ℝ => supp K₀ (t + π / 2) - dot p (vvec t) - 1 - m / 2
  let FC := fun p : Point => fun t : ℝ => supp K₀ (t - π / 2) - dot p (uvec (t - π / 2)) - 1 - m / 2
  have hFA : Continuous (fun z : Point × ℝ => FA z.1 z.2) := by
    apply Continuous.sub
    apply Continuous.sub
    apply Continuous.sub
    · exact hcap.2.1.continuous_supp.comp (continuous_snd.add continuous_const)
    · exact continuous_dot_pair.comp (continuous_fst.prodMk (continuous_vvec.comp continuous_snd))
    · exact continuous_const
    · exact continuous_const
  have hFC : Continuous (fun z : Point × ℝ => FC z.1 z.2) := by
    apply Continuous.sub
    apply Continuous.sub
    apply Continuous.sub
    · exact hcap.2.1.continuous_supp.comp (continuous_snd.sub continuous_const)
    · exact continuous_dot_pair.comp
        (continuous_fst.prodMk (continuous_uvec.comp (continuous_snd.sub continuous_const)))
    · exact continuous_const
    · exact continuous_const
  obtain ⟨δA, hδA, -, hA⟩ := exposed_face_property_stable hcap isCompact_Icc
    (I := Icc a b) (fun t ht => ⟨ha.le.trans ht.1, ht.2.trans hb.le |>.trans (by linarith [pi_pos])⟩)
    FA hFA.continuousOn (by
      intro t ht p hp
      have he := injective_face_eq_aK hcap hI
        ⟨ha.le.trans ht.1, ht.2.trans_lt hb⟩ hp
      rw [he]
      have hf := (hmle t ht).trans (min_le_left _ _)
      have hform : supp K₀ (t + π / 2) - dot (aK K₀ t) (vvec t) = fK K₀ t := by
        exact (inj_fMinus_eq K₀ t).symm
      change 0 < supp K₀ (t + π / 2) - dot (aK K₀ t) (vvec t) - 1 - m / 2
      rw [hform]
      linarith)
  obtain ⟨δC, hδC, -, hC⟩ := exposed_face_property_stable hcap isCompact_Icc
    (I := Icc (a + π / 2) (b + π / 2))
    (fun t ht => ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩)
    FC hFC.continuousOn (by
      intro t ht p hp
      have hti : t - π / 2 ∈ Icc a b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hp' : p ∈ edge K₀ ((t - π / 2) + π / 2) := by simpa only [sub_add_cancel] using hp
      have he := injective_face_eq_cK hcap hI
        ⟨by linarith [hti.1], by linarith [hti.2]⟩ hp'
      rw [he]
      have hg := (hmle (t - π / 2) hti).trans (min_le_right _ _)
      have hform : supp K₀ (t - π / 2) - dot (cK K₀ (t - π / 2)) (uvec (t - π / 2)) =
          gK K₀ (t - π / 2) := by
        simp only [gK, gPlus, dot_sub_left, inj_dot_outerCorner_uvec, cK]
      change 0 < supp K₀ (t - π / 2) - dot (cK K₀ (t - π / 2)) (uvec (t - π / 2)) - 1 - m / 2
      rw [hform]
      linarith)
  let δ := min 1 (min (m / 4) (min δA δC))
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min (by linarith) (lt_min hδA hδC))
  have hδm : δ ≤ m / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδA' : δ ≤ δA := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδC' : δ ≤ δC := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨m / 4, δ, by linarith, hδ, min_le_left _ _, ?_⟩
  intro K hK hclose
  constructor
  · intro t ht p hp
    have hh := hA K hK (hclose.mono hδA') t ht p hp
    have he := (abs_le.mp (hclose (t + π / 2)
      ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩)).1
    change 0 < supp K₀ (t + π / 2) - dot p (vvec t) - 1 - m / 2 at hh
    linarith
  · intro t ht p hp
    have hh := hC K hK (hclose.mono hδC') (t + π / 2)
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ p hp
    have he := (abs_le.mp (hclose t ⟨by linarith [ht.1], by linarith [ht.2, pi_pos]⟩)).1
    change 0 < supp K₀ (t + π / 2 - π / 2) - dot p (uvec (t + π / 2 - π / 2)) - 1 - m / 2 at hh
    rw [add_sub_cancel_right] at hh
    linarith

/-- One-sided arm values inherit the all-face margin. -/
theorem CoreArmMargin.oneSided {K : Set Point} (hK : IsCap K (π / 2))
    {a b c : ℝ} (h : CoreArmMargin K a b c) {t : ℝ} (ht : t ∈ Icc a b) :
    1 + c ≤ fPlus K t ∧ 1 + c ≤ fMinus K t ∧
      1 + c ≤ gPlus K t ∧ 1 + c ≤ gMinus K t := by
  have h1 := h.1 t ht (vplus K t) (vplus_mem_edge hK.2.1 t)
  have h2 := h.1 t ht (vminus K t) (vminus_mem_edge hK.2.1 t)
  have h3 := h.2 t ht (vplus K (t + π / 2)) (vplus_mem_edge hK.2.1 _)
  have h4 := h.2 t ht (vminus K (t + π / 2)) (vminus_mem_edge hK.2.1 _)
  rw [← inj_fPlus_eq] at h1
  rw [← inj_fMinus_eq] at h2
  simp only [gPlus, gMinus, cPlus, cMinus, dot_sub_left, inj_dot_outerCorner_uvec]
  exact ⟨h1, h2, h3, h4⟩

end MovingSofaStability
