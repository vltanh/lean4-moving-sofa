module

public import MovingSofaStability.CoreAreaBound
public import MovingSofaStability.CapDistance

/-!
# The local upper bound without Ki

Uncompiled proof source. Canonical-tail feasibility, cut separation, positive
core height, and niche containment are proved on a common neighborhood of
Gerver. The original three-region argument then gives A <= Q there.

The cap-distance coefficient used in the present Lean source is 80. It is
not the sharp 2 sec(phi) coefficient of the analytic notes; no sharp constant
is needed for the unrestricted existence theorem.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- The geometric certificate on a cap with separated, positive, monotone core. -/
theorem separated_upperQ_bound {φ c : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04)
    {K : Set Point} (hK : IsCap K (π / 2))
    (hwidth : (21 / 10 : ℝ) ≤ bottomWidth K)
    (htriple : InWideL φ K (rightBody φ K) (leftBody φ K))
    (hcore : CoreArmMargin K φ (π / 2 - φ) c) (hc : 0 < c)
    (hsep : CutSeparated φ K)
    (hheight : ∀ t ∈ Icc φ (π / 2 - φ), 0 < (innerCorner K t).2)
    (hNK : niche K (π / 2) ⊆ K) :
    sofaArea (π / 2) K ≤ upperQ φ K (rightBody φ K) (leftBody φ K) := by
  obtain ⟨hφ0, hφ4, -, hc9, -⟩ := opt_phi_bounds hφ
  have hcos : 0 < cos φ := by linarith
  have hRm : MeasurableSet (hRight φ K) := (isClosed_halfPlus _ _).measurableSet
  have hLm : MeasurableSet (hLeft φ K) := (isClosed_halfPlus _ _).measurableSet
  have hfin : volume (niche K (π / 2)) ≠ ⊤ := (nef_niche_isBounded hK).measure_lt_top.ne
  have hdisj := cut_regions_disjoint_of_width hφ hK hwidth
  have he3 : (niche K (π / 2) \ hRight φ K) ∩ hLeft φ K =
      niche K (π / 2) ∩ hLeft φ K := by
    ext p
    constructor
    · rintro ⟨⟨hp, -⟩, hL⟩; exact ⟨hp, hL⟩
    · rintro ⟨hp, hL⟩
      refine ⟨⟨hp, ?_⟩, hL⟩
      intro hR
      exact Set.disjoint_left.mp hdisj ⟨hNK hp, hR⟩ ⟨hNK hp, hL⟩
  have e1 := area_inter_add_sdiff (S := niche K (π / 2)) hRm hfin
  have e2 := area_inter_add_sdiff (S := niche K (π / 2) \ hRight φ K) hLm
    (volume_ne_top_of_subset sdiff_subset hfin)
  rw [he3] at e2
  have hdecomp : area (niche K (π / 2)) =
      area (niche K (π / 2) ∩ hRight φ K) + area (niche K (π / 2) ∩ hLeft φ K) +
      area ((niche K (π / 2) \ hRight φ K) \ hLeft φ K) := by linarith
  obtain ⟨htR, htL⟩ := separated_tail_areas hφ hK hwidth htriple hsep
  have hco := positive_core_area_le ⟨hφ0, hφ4⟩ hK hcore hc hsep hheight
  obtain ⟨-, -, hBa, hDb⟩ := inWideL_supp htriple
  obtain ⟨hXB, hW, hxR⟩ := opt_right_mem_line hcos.ne' hBa
  obtain ⟨hYD, hZ, hxL⟩ := opt_left_mem_line hcos.ne' hDb
  have c1 := segArea_add_of_mem_line hXB hW hxR
  have c2 := segArea_add_of_mem_line hxL hZ hYD
  have s1 := segArea_swap (xRight φ K) (xB φ (rightBody φ K))
  have s2 := segArea_swap (yD φ (leftBody φ K)) (xLeft φ K)
  unfold sofaArea upperQ
  linarith

/-- All local geometric hypotheses hold together, not as assumptions on an
arbitrary near-maximizer. The certificate's radius is independent of K. -/
theorem nearby_cap_certificate {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K P.cap →
        InWideL P.φ K (rightBody P.φ K) (leftBody P.φ K) ∧
        niche K (π / 2) ⊆ K ∧
        sofaArea (π / 2) K ≤ upperQ P.φ K (rightBody P.φ K) (leftBody P.φ K) ∧
        upperQ P.φ K (rightBody P.φ K) (leftBody P.φ K) ≤ area (gerverSofa P) := by
  sorry

/-- Local cap stability in the original area functional, now without Ki. -/
theorem nearby_cap_distance {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K P.cap →
        niche K (π / 2) ⊆ K ∧ sofaArea (π / 2) K ≤ area (gerverSofa P) ∧
        EuclideanClose (80 * sqrt (area (gerverSofa P) - sofaArea (π / 2) K))
          K (shiftedReferenceCap P.cap K) := by
  obtain ⟨δ, hδ, hδ1, hcert⟩ := nearby_cap_certificate hP hbox
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro K hK hclose
  obtain ⟨ht, hn, ha, hq⟩ := hcert K hK hclose
  have hd := wide_cap_distance_bound hP hbox (canonicalWideTriple ht)
  have hrad : 80 * sqrt (area (gerverSofa P) - upperQ P.φ K (rightBody P.φ K) (leftBody P.φ K)) ≤
      80 * sqrt (area (gerverSofa P) - sofaArea (π / 2) K) := by
    apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (sub_le_sub_left ha _))
    norm_num
  exact ⟨hn, ha.trans hq, hd.mono hrad⟩

end MovingSofaStability
