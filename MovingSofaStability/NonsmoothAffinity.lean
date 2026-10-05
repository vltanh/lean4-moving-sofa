module

public import MovingSofaStability.NonsmoothBookkeeping

/-!
# The affine cap remainder on all normalized caps

Uncompiled proof source. The atom-aware decomposition and the bounded-variation
curve argument remove all Ki assumptions from the affine part of Q.
-/

@[expose] public section
noncomputable section

open Real Set
open scoped Pointwise
open MovingSofaOptimality

namespace MovingSofaStability

/-- The joined boundary expression is affine even when supporting faces have length. -/
theorem capAffineBoundary_comb (φ : ℝ) {K₁ K₂ : Set (ℝ × ℝ)}
    (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) :
    capAffineBoundary φ ((1 - c) • K₁ + c • K₂) =
      (1 - c) * capAffineBoundary φ K₁ + c * capAffineBoundary φ K₂ := by
  simp only [capAffineBoundary, supp_comb h₁ h₂ hc]
  ring

/-- Source Lemma 8.3.6(2) uses the top support, but not cap injectivity. -/
theorem rightSegmentRemainder_comb {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 2))
    {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsCap K₁ (π / 2)) (h₂ : IsCap K₂ (π / 2))
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    rightSegmentRemainder φ ((1 - c) • K₁ + c • K₂) =
      (1 - c) * rightSegmentRemainder φ K₁ + c * rightSegmentRemainder φ K₂ := by
  have hm := opt_comb_isCap h₁ h₂ hc
  have hcb₁ := h₁.2.1
  have hcb₂ := h₂.2.1
  simp only [rightSegmentRemainder]
  rw [opt_tangent_right_eq hφ hm.2.2.2.1,
    opt_tangent_right_eq hφ h₁.2.2.2.1, opt_tangent_right_eq hφ h₂.2.2.2.1,
    opt_outer_eq_inner_add, opt_outer_eq_inner_add, opt_outer_eq_inner_add,
    opt_wRight_comb hcb₁ hcb₂ hc, xRight, xRight, xRight,
    opt_innerCorner_comb hcb₁ hcb₂ hc]
  simp only [segArea, cross, Pi.add_apply, Pi.smul_apply, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The left segment term is likewise affine for all normalized caps. -/
theorem leftSegmentRemainder_comb {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 2))
    {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsCap K₁ (π / 2)) (h₂ : IsCap K₂ (π / 2))
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    leftSegmentRemainder φ ((1 - c) • K₁ + c • K₂) =
      (1 - c) * leftSegmentRemainder φ K₁ + c * leftSegmentRemainder φ K₂ := by
  have hm := opt_comb_isCap h₁ h₂ hc
  have hcb₁ := h₁.2.1
  have hcb₂ := h₂.2.1
  simp only [leftSegmentRemainder]
  rw [opt_tangent_left_eq hφ hm.2.2.2.1,
    opt_tangent_left_eq hφ h₁.2.2.2.1, opt_tangent_left_eq hφ h₂.2.2.2.1,
    opt_outer_eq_inner_add, opt_outer_eq_inner_add, opt_outer_eq_inner_add,
    opt_zLeft_comb hcb₁ hcb₂ hc, xLeft, xLeft, xLeft,
    opt_innerCorner_comb hcb₁ hcb₂ hc]
  simp only [segArea, cross, Pi.add_apply, Pi.smul_apply, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The nonsmooth extension of source Lemma 8.3.7. No density or arm condition appears. -/
theorem cap_mamikon_upperP_affine {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsCap K₁ (π / 2)) (h₂ : IsCap K₂ (π / 2))
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    mamikonS φ ((1 - c) • K₁ + c • K₂) + upperP φ ((1 - c) • K₁ + c • K₂) =
      (1 - c) * (mamikonS φ K₁ + upperP φ K₁) +
      c * (mamikonS φ K₂ + upperP φ K₂) := by
  have hpi := pi_pos
  have hφ2 : φ ∈ Ioo 0 (π / 2) := ⟨hφ.1, by linarith [hφ.2]⟩
  have hM := opt_comb_isCap h₁ h₂ hc
  have hboundary := capAffineBoundary_comb φ h₁.2.1 h₂.2.1 hc
  have hright := rightSegmentRemainder_comb hφ2 h₁ h₂ hc
  have hleft := leftSegmentRemainder_comb hφ2 h₁ h₂ hc
  have hcurve := outer_inner_area_affine
    (a := φ) (b := π / 2 - φ) (by linarith [hφ.2]) h₁.2.1 h₂.2.1 hc
  rw [mamikonS_add_upperP_nonsmooth hφ hM,
    mamikonS_add_upperP_nonsmooth hφ h₁, mamikonS_add_upperP_nonsmooth hφ h₂]
  linarith

/-- The cap Mamikon sum was convex on all convex bodies even before restricting to Ki. -/
theorem mamikonS_convex_all {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    convexBodyDomain.IsConvexFun (fun K => mamikonS φ K.1) := by
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  have c1 := (opt_mamikon_tangent (t := π / 2) (a := 0) (b := φ)
    hφ0 (by linarith) (by linarith) (by linarith)).2
  have c2 := (opt_mamikon_outer (a := φ) (b := π / 2 - φ)
    (by linarith) (by linarith)).2
  have c3 := (opt_mamikon_tangent (t := π / 2 + (π / 2 - φ))
    (a := π / 2 - φ) (b := π / 2)
    (by linarith) (by linarith) (by linarith) (by linarith)).2
  have c4 := (opt_mamikon_tangent (t := π) (a := π / 2) (b := π)
    (by linarith) (by linarith) (by linarith) le_rfl).2
  exact opt_isConvexFun_add (opt_isConvexFun_add (opt_isConvexFun_add c1 c2) c3) c4

end MovingSofaStability
