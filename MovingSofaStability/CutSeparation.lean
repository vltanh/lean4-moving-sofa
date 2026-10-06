module

public import MovingSofaStability.CoreIntegral

/-!
# Stable separation from the two niche cuts

Close to a cut, a uniform right-velocity margin is used. Away from it, a strict
compact reference margin is used. No derivative control near the ends 0 and pi/2
is assumed for the competing cap.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- The two inequalities used in the three-region niche decomposition. -/
def CutSeparated (φ : ℝ) (K : Set Point) : Prop :=
  (∀ t ∈ Ioc φ (π / 2), dot (innerCorner K t) (uvec φ) < supp K φ - 1) ∧
  (∀ t ∈ Ico 0 (π / 2 - φ),
    dot (innerCorner K t) (vvec (π / 2 - φ)) < supp K (π / 2 - φ + π / 2) - 1)

theorem innerCorner_projection_error {K K₀ : Set Point} {δ t : ℝ}
    (h : UpperSupportClose δ K K₀) (ht : t ∈ Icc (0 : ℝ) (π / 2)) (a : ℝ) :
    |dot (innerCorner K t) (uvec a) - dot (innerCorner K₀ t) (uvec a)| ≤ 2 * δ := by
  have hp := abs_dot_le_norm2_mul (innerCorner K t - innerCorner K₀ t) (uvec a)
  rw [dot_sub_left, norm2_uvec, mul_one] at hp
  exact hp.trans (innerCorner_support_error h ht)

/-- Separation on the right includes times arbitrarily close to pi/2. -/
theorem nearby_right_cut_separation {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K₀ : Set Point} (hK₀ : IsKi K₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K K₀ →
        ∀ t ∈ Ioc φ (π / 2), dot (innerCorner K t) (uvec φ) < supp K φ - 1 := by
  have hpi := pi_pos
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (φ + π / 2) / 2 := ⟨_, rfl⟩
  have hφm : φ < m := by rw [hm]; linarith [hφ.2]
  have hmv : m < π / 2 := by rw [hm]; linarith [hφ.2]
  obtain ⟨c, δA, hc, hδA, hδA1, hA⟩ :=
    core_arm_margin_near_reference hK₀ hφ.1 hφm.le hmv
  have hgapcont : Continuous (fun t => supp K₀ φ - 1 - dot (innerCorner K₀ t) (uvec φ)) :=
    continuous_const.sub ((continuous_dot (uvec φ)).comp (opt_innerCorner_continuous hK₀.1.2.1))
  obtain ⟨g, hg, hgap⟩ := isCompact_Icc.exists_forall_le' hgapcont.continuousOn
    (s := Icc m (π / 2)) (fun t ht => sub_pos.mpr
      (opt_innerCorner_lt_right hφ hK₀ ⟨hφm.trans_le ht.1, ht.2⟩))
  refine ⟨min δA (g / 4), lt_min hδA (by linarith), (min_le_left _ _).trans hδA1, ?_⟩
  intro K hK hclose t ht
  have hδA' : min δA (g / 4) ≤ δA := min_le_left _ _
  have hδg : min δA (g / 4) ≤ g / 4 := min_le_right _ _
  by_cases htm : t ≤ m
  · have hcore := hA K hK (hclose.mono hδA')
    have hinc := right_derivative_increment_le (f := fun s => dot (innerCorner K s) (uvec φ))
      ht.1.le (continuousOn_dot (opt_innerCorner_continuous hK.2.1).continuousOn (uvec φ))
      (fun s _ => hasRightDeriv_dot_uvec (d := φ) (corner_hasRightDeriv hK s))
      (B := -c) (fun s hs => hcore.right_cut_velocity hK hc.le
        ⟨hs.1.le, hs.2.le.trans htm⟩
        ⟨by linarith [hs.1], by linarith [hs.2, ht.2, hφ.1]⟩)
    rw [(cn_innerCorner_dot K φ).1] at hinc
    have hneg : -c * (t - φ) < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos hc) (sub_pos.mpr ht.1)
    linarith
  · have hr := hgap t ⟨(not_le.mp htm).le, ht.2⟩
    have he := innerCorner_projection_error hclose ⟨(hφ.1.trans ht.1).le, ht.2⟩ φ
    have hs := hclose φ ⟨hφ.1.le, by linarith [hφ.2]⟩
    have hu := (abs_le.mp he).2
    have hl := (abs_le.mp hs).1
    linarith

/-- The left separation is obtained by the same local/compact split, without
assuming that all left arm lengths of the competing cap exceed one. -/
theorem nearby_left_cut_separation {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K₀ : Set Point} (hK₀ : IsKi K₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K K₀ →
        ∀ t ∈ Ico 0 (π / 2 - φ),
          dot (innerCorner K t) (vvec (π / 2 - φ)) < supp K (π / 2 - φ + π / 2) - 1 := by
  have hpi := pi_pos
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = π / 2 - φ := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = b / 2 := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hb]; linarith [hφ.2]
  have hmv : 0 < m := by rw [hm]; linarith
  have hmb : m < b := by rw [hm]; linarith
  have hbv : b < π / 2 := by rw [hb]; linarith [hφ.1]
  rw [← hb]
  obtain ⟨c, δA, hc, hδA, hδA1, hA⟩ :=
    core_arm_margin_near_reference hK₀ hmv hmb.le hbv
  have hgapcont :
      Continuous (fun t => supp K₀ (b + π / 2) - 1 - dot (innerCorner K₀ t) (vvec b)) :=
    continuous_const.sub ((continuous_dot (vvec b)).comp (opt_innerCorner_continuous hK₀.1.2.1))
  obtain ⟨g, hg, hgap⟩ := isCompact_Icc.exists_forall_le' hgapcont.continuousOn
    (s := Icc (0 : ℝ) m) (fun t ht => sub_pos.mpr (by
      have h := opt_innerCorner_lt_left hφ hK₀ (t := t) ⟨ht.1, hb ▸ ht.2.trans_lt hmb⟩
      rwa [← hb] at h))
  refine ⟨min δA (g / 4), lt_min hδA (by linarith), (min_le_left _ _).trans hδA1, ?_⟩
  intro K hK hclose t ht
  have hδA' : min δA (g / 4) ≤ δA := min_le_left _ _
  have hδg : min δA (g / 4) ≤ g / 4 := min_le_right _ _
  by_cases hmt : m ≤ t
  · have hcore := hA K hK (hclose.mono hδA')
    have hinc := right_derivative_increment_ge (f := fun s => dot (innerCorner K s) (vvec b))
      ht.2.le (continuousOn_dot (opt_innerCorner_continuous hK.2.1).continuousOn (vvec b))
      (fun s _ => by
        simpa only [uvec_add_pi_div_two] using
          hasRightDeriv_dot_uvec (d := b + π / 2) (corner_hasRightDeriv hK s))
      (B := c) (fun s hs => by
        simpa only [uvec_add_pi_div_two] using hcore.left_cut_velocity hK hc.le
          ⟨hmt.trans hs.1.le, hs.2.le⟩
          ⟨by linarith [hs.2], by linarith [hs.1, ht.1]⟩)
    rw [opt_innerCorner_dot_v] at hinc
    have hpos : 0 < c * (b - t) := mul_pos hc (sub_pos.mpr ht.2)
    linarith
  · have hr := hgap t ⟨ht.1, (not_le.mp hmt).le⟩
    have he := innerCorner_projection_error hclose ⟨ht.1, ht.2.le.trans hbv.le⟩ (b + π / 2)
    rw [uvec_add_pi_div_two] at he
    have hs := hclose (b + π / 2) ⟨by linarith, by linarith [hφ.1]⟩
    have hu := (abs_le.mp he).2
    have hl := (abs_le.mp hs).1
    linarith

/-- Both cuts are simultaneously separated in one fixed neighborhood. -/
theorem nearby_cutSeparated {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K P.cap → CutSeparated P.φ K := by
  have hφ := GerverParams.gm_φ_mem_Ioo hP hbox
  have hK₀ := theorem8_1_1_gerver hP hbox
  obtain ⟨δR, hR, hR1, hright⟩ := nearby_right_cut_separation hφ hK₀
  obtain ⟨δL, hL, hL1, hleft⟩ := nearby_left_cut_separation hφ hK₀
  exact ⟨min δR δL, lt_min hR hL, (min_le_left _ _).trans hR1,
    fun K hK hclose => ⟨hright K hK (hclose.mono (min_le_left _ _)),
      hleft K hK (hclose.mono (min_le_right _ _))⟩⟩

end MovingSofaStability
