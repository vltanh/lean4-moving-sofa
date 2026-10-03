module

public import SofaUniqueness.PinnedVariation
public import SofaUniqueness.SelectedCaps

/-!
# Pinned bounds for the specified continuum maximizer

The polygon inequalities here are w<=tau and z<=tau. They are valid before
balancedness and are not the balanced-polygon Theorem 4.1.2. The selected
polygons have vanishing signed pinned defects; upper semicontinuity of a fixed
edge length then gives the desired inequalities for their specified limit.

Positive sofa-area is stated because it supplies the compact selector. In the
shape-uniqueness application it follows from the already proved lower bound
on Gerver's area, not from any additional assumption on the starting sofa.

Uncompiled source. No admissions or decision tactics.
-/

@[expose] public section
noncomputable section

open Set Real Filter Topology MeasureTheory MovingSofa

namespace SofaUniqueness

/-- The completed inner boundary, not the outer top edge, is bounded below
by the right gap before any maximality or stationarity argument is used. -/
theorem polygon_wedgeGapW_le_tau {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) :
    wedgeGapWInf K Θ.ω ≤ tau Θ K (π / 2) := by
  obtain ⟨t₀, ht₀, hmax⟩ :=
    Θ.angles.exists_max_image (fun t => (supp K t - 1) / cos t) Θ.nonempty
  have hℓ := ang_lineLength_polyNiche_le (K := K) hω hmax
  have h352 := (lemma3_4_5_two hK (t := π / 2) (Or.inr rfl)).2
  rw [show π / 2 + π = 3 * π / 2 by ring] at h352
  have hσ := ang_supp_zero_le_sigmaAt hK.1 hω
  have h1 := ang_wedgeGapWInf_le_supp_zero hK.1 hω
  have h2 := ang_wedgeGapWInf_le hK.1.2.1 hω (Θ.subset t₀ ht₀)
  rw [ang_wedgeGapW_eq] at h2
  rcases le_total ((supp K t₀ - 1) / cos t₀) 0 with hW | hW
  · rw [max_eq_right hW] at hℓ
    linarith
  · rw [max_eq_left hW] at hℓ
    linarith

theorem polygon_wedgeGapZ_le_tau {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) :
    wedgeGapZInf K Θ.ω ≤ tau Θ K Θ.ω := by
  obtain ⟨t₀, ht₀, hmax⟩ :=
    Θ.angles.exists_max_image (fun t => (supp K (t + π / 2) - 1) / cos (Θ.ω - t)) Θ.nonempty
  have hℓ := ang_lineLength_polyNiche_le_z (K := K) hω hmax
  have h352 := (lemma3_4_5_two hK (t := Θ.ω) (Or.inl rfl)).2
  have hσ := ang_supp_le_sigmaAt_add_pi hK.1 hω
  have h1 := ang_wedgeGapZInf_le_supp hK.1 hω
  have h2 := ang_wedgeGapZInf_le hK.1.2.1 hω (Θ.subset t₀ ht₀)
  rw [ang_wedgeGapZ_eq] at h2
  rcases le_total ((supp K (t₀ + π / 2) - 1) / cos (Θ.ω - t₀)) 0 with hW | hW
  · rw [max_eq_right hW] at hℓ
    linarith
  · rw [max_eq_left hW] at hℓ
    linarith

/-- A common coordinate box bounds the supports in every direction. -/
theorem abs_supp_le_box {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {R : ℝ}
    (hR : 0 ≤ R) (hbox : K ⊆ Icc (-R) R ×ˢ Icc 0 1) (t : ℝ) :
    |supp K t| ≤ R + 1 := by
  obtain ⟨p, hp, hpt⟩ := exists_dot_eq_supp hK.2.1 hK.1 t
  rw [← hpt]
  have h := mpc_abs_dot_uvec_le p t
  obtain ⟨hx, hy⟩ := hbox hp
  have hx' : |p.1| ≤ R := abs_le.mpr hx
  have hy' : |p.2| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
  linarith

/-- Pinned inequalities for every specified cap maximizing a positive value.
The sequence in this proof converges to K itself. -/
theorem pinned_bounds_of_maximal_positive {ω : ℝ} (hω : ω ∈ Ioo 0 (π / 2))
    {K : Set (ℝ × ℝ)} (hK : IsCap K ω) (hpositive : 0 < sofaArea ω K)
    (hmax : ∀ C, IsCap C ω → sofaArea ω C ≤ sofaArea ω K) :
    wedgeGapWInf K ω ≤ sigmaAt K (π / 2) ∧ wedgeGapZInf K ω ≤ sigmaAt K ω := by
  sorry

end SofaUniqueness
