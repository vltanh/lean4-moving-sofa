module

public import MovingSofaQuantitative.Normalization

/-!
# The geometric translation quotient and its asymptotic coefficient

Proof source, not yet compiled in this session.

The geometric distance is defined by Euclidean point-witness bounds and then
identified with the support quotient for caps. The nonempty/finite sides of the
infimum and supremum constructions are proved, rather than relying on Lean's
totalized real infimum on an empty set. The final lemma records the uniform
margin needed for a STRICT asymptotic lower bound.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability

namespace MovingSofaQuantitative

abbrev UpperNormal := Icc (0 : ℝ) π

def upperSupportDifference (K₀ K₁ : Set Point) (t : UpperNormal) : ℝ :=
  supp K₁ t - supp K₀ t

def horizontalMode (t : UpperNormal) : ℝ := cos t

/-- Euclidean Hausdorff distance of convex caps minimized over horizontal
translations. Its finiteness and attainment are established below. -/
def capTranslationDistance (K₀ K₁ : Set Point) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ ∃ a : ℝ, EuclideanClose r K₁ (horizontalReference K₀ a)}

theorem horizontalMode_nonzero : ∃ t : UpperNormal, horizontalMode t ≠ 0 := by
  refine ⟨⟨0, le_rfl, pi_pos.le⟩, ?_⟩
  simp [horizontalMode]

/-- The uniform upper-semicircle support bound and actual Euclidean cap bound
are equivalent at each radius and for the same translation parameter. -/
theorem fitsTranslation_iff_capClose {K₀ K₁ : Set Point}
    (h₀ : IsCap K₀ (π / 2)) (h₁ : IsCap K₁ (π / 2)) (r : ℝ) :
    FitsTranslation (upperSupportDifference K₀ K₁) horizontalMode r ↔
      ∃ a : ℝ, EuclideanClose r K₁ (horizontalReference K₀ a) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, cap_close_of_horizontalError h₀ h₁ ?_⟩
    intro t ht
    exact ha ⟨t, ht⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    intro t
    have hT := nef_isConvexBody_translate h₀.2.1 (a, 0)
    have hs := ha.abs_supp_sub_le h₁.2.1.2.1 hT.2.1 h₁.2.1.1 hT.1 t
    rw [← horizontalError_eq_support h₀.2.1] at hs
    exact hs

theorem capTranslationDistance_eq_quotientRadius {K₀ K₁ : Set Point}
    (h₀ : IsCap K₀ (π / 2)) (h₁ : IsCap K₁ (π / 2)) :
    capTranslationDistance K₀ K₁ =
      quotientRadius (upperSupportDifference K₀ K₁) horizontalMode := by
  unfold capTranslationDistance quotientRadius
  congr 1
  ext r
  exact and_congr_right fun _ => (fitsTranslation_iff_capClose h₀ h₁ r).symm

private theorem upperSupportDifference_bounded {K₀ K₁ : Set Point}
    (h₀ : IsCap K₀ (π / 2)) (h₁ : IsCap K₁ (π / 2)) :
    ∃ B : ℝ, ∀ t : UpperNormal, |upperSupportDifference K₀ K₁ t| ≤ B := by
  have hc : Continuous (fun t : ℝ => |supp K₁ t - supp K₀ t|) :=
    (h₁.2.1.continuous_supp.sub h₀.2.1.continuous_supp).abs
  obtain ⟨B, hB⟩ := (isCompact_Icc.image hc).bddAbove
  exact ⟨B, fun t => hB (mem_image_of_mem _ t.property)⟩

/-- Exact two-point formula, nonnegativity, and an attained best alignment for caps. -/
theorem capTranslationDistance_formula {K₀ K₁ : Set Point}
    (h₀ : IsCap K₀ (π / 2)) (h₁ : IsCap K₁ (π / 2)) :
    capTranslationDistance K₀ K₁ =
        quotientScore (upperSupportDifference K₀ K₁) horizontalMode ∧
      0 ≤ capTranslationDistance K₀ K₁ ∧
      ∃ a : ℝ, EuclideanClose (capTranslationDistance K₀ K₁) K₁ (horizontalReference K₀ a) := by
  obtain ⟨B, hB⟩ := upperSupportDifference_bounded h₀ h₁
  obtain ⟨he, hn, ha⟩ := quotientRadius_eq_score_and_attained horizontalMode_nonzero hB
  rw [capTranslationDistance_eq_quotientRadius h₀ h₁, he]
  exact ⟨rfl, hn, (fitsTranslation_iff_capClose h₀ h₁ _).1 ha⟩

/-- Any actual alignment gives an upper bound for the geometric infimum. -/
theorem capTranslationDistance_le_of_close {K₀ K₁ : Set Point} {r : ℝ}
    (hr : 0 ≤ r) (h : ∃ a : ℝ, EuclideanClose r K₁ (horizontalReference K₀ a)) :
    capTranslationDistance K₀ K₁ ≤ r :=
  csInf_le ⟨0, fun _ hd => hd.1⟩ ⟨hr, h⟩

/-- Since the best alignment is attained, a bound on the infimum is an actual
point-witness bound, not just a sequence of slightly larger radii. -/
theorem capTranslationDistance_le_iff {K₀ K₁ : Set Point}
    (h₀ : IsCap K₀ (π / 2)) (h₁ : IsCap K₁ (π / 2)) {r : ℝ} (hr : 0 ≤ r) :
    capTranslationDistance K₀ K₁ ≤ r ↔
      ∃ a : ℝ, EuclideanClose r K₁ (horizontalReference K₀ a) := by
  constructor
  · intro h
    obtain ⟨_, _, a, ha⟩ := capTranslationDistance_formula h₀ h₁
    exact ⟨a, ha.mono h⟩
  · exact capTranslationDistance_le_of_close hr

/-- The full Q deficit; distinct from the original sofa-area deficit. -/
def qDeficit (P : GerverParams) (x : WideTriple P.φ) : ℝ :=
  area (gerverSofa P) - wideUpperQ P.φ x

/-- Eventual, uniform, nonnegative coefficients. This operational definition
avoids an unbounded/empty real limsup and fixes all quantifiers explicitly. -/
def localQCoefficients (P : GerverParams) : Set ℝ :=
  {c | 0 ≤ c ∧ ∃ η : ℝ, 0 < η ∧ ∀ x : WideTriple P.φ,
    0 < qDeficit P x → qDeficit P x < η →
      capTranslationDistance P.cap x.1.1.1 ≤ c * sqrt (qDeficit P x)}

def intrinsicQCoefficient (P : GerverParams) : ℝ := sInf (localQCoefficients P)

/-- The integrated pinned certificate already makes the coefficient set nonempty.
No new critical-cone or 0.93 result is assumed here. -/
theorem localQCoefficients_nonempty {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (localQCoefficients P).Nonempty := by
  have hφ := GerverParams.gm_φ_mem_Ioo hP hbox
  have hc : 0 ≤ 2 / cos P.φ := div_nonneg (by norm_num) (cap_angle_parameters hφ).1.le
  refine ⟨2 / cos P.φ, hc, 1, by norm_num, ?_⟩
  intro x _ _
  apply capTranslationDistance_le_of_close (mul_nonneg hc (sqrt_nonneg _))
  refine ⟨-(supp x.1.1.1 π - supp P.cap π), ?_⟩
  exact sharp_wide_cap_distance_bound hP hbox x

theorem intrinsicQCoefficient_nonneg {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    0 ≤ intrinsicQCoefficient P :=
  le_csInf (localQCoefficients_nonempty hP hbox) (fun _ hc => hc.1)

/-- A UNIFORM lower ratio at arbitrarily small positive deficits bounds the
asymptotic coefficient. Strictness is obtained only by a separate strict margin
below L, not from examples whose ratios may converge to L from above. -/
theorem uniform_trial_lower_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {L : ℝ}
    (htrial : ∀ η : ℝ, 0 < η → ∃ x : WideTriple P.φ,
      0 < qDeficit P x ∧ qDeficit P x < η ∧
      L * sqrt (qDeficit P x) ≤ capTranslationDistance P.cap x.1.1.1) :
    L ≤ intrinsicQCoefficient P := by
  apply le_csInf (localQCoefficients_nonempty hP hbox)
  rintro c ⟨_, η, hη, hc⟩
  obtain ⟨x, hΔ, hsmall, hlower⟩ := htrial η hη
  have hupper := hc x hΔ hsmall
  exact (mul_le_mul_right (sqrt_pos.2 hΔ)).mp (hlower.trans hupper)

/-- A fixed positive margin upgrades the operational lower theorem to strictness. -/
theorem strict_intrinsic_lower_of_uniform_trial {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {l L : ℝ} (hl : l < L)
    (htrial : ∀ η : ℝ, 0 < η → ∃ x : WideTriple P.φ,
      0 < qDeficit P x ∧ qDeficit P x < η ∧
      L * sqrt (qDeficit P x) ≤ capTranslationDistance P.cap x.1.1.1) :
    l < intrinsicQCoefficient P :=
  hl.trans_le (uniform_trial_lower_bound hP hbox htrial)

end MovingSofaQuantitative
