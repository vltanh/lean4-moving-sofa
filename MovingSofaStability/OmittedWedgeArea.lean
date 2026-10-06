module

public import MovingSofaStability.PartialHallways

/-!
# A small linear cost for omitted terminal wedges

Uncompiled proof source. The radius is fixed before the endpoint-window
width. Only afterwards are the support neighborhood and angle threshold
chosen. Thus the gain coefficient can be made smaller than a fixed terminal
floor loss, without any quantitative compactness assumption.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- Late wedges add area only in two arbitrarily short endpoint windows. -/
theorem nearby_omittedWedges_area {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {η R : ℝ} (hη : 0 < η) (hR : 1 ≤ R) :
    ∃ δ α₀ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < α₀ ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K P.cap →
      (∀ p ∈ K, norm2 p ≤ R) → ∀ ω ∈ Icc (0 : ℝ) (π / 2), π / 2 - ω ≤ α₀ →
        area (omittedWedges K ω) ≤ 4 * η * (3 * R + 1) * (π / 2 - ω) := by
  obtain ⟨δN, hδN, hδN1, hlocal⟩ := nearby_niche_horizontal_localization hP hbox hη
  obtain ⟨e, δF, he, hδF, hδF1, hcover⟩ := gerver_floor_slab_covered hP hbox
    (l := gerverRoofLeft P + η) (r := gerverRoofRight P - η) (by linarith) (by linarith)
  let Cw := 3 * R + 1
  have hCw : 0 < Cw := by dsimp [Cw]; linarith
  let δ := min δN δF
  let α₀ := min (e / 2) (δF / Cw)
  have hδ : 0 < δ := lt_min hδN hδF
  have hα₀ : 0 < α₀ := lt_min (by linarith) (div_pos hδF hCw)
  have hδN' : δ ≤ δN := min_le_left _ _
  have hδF' : δ ≤ δF := min_le_right _ _
  have hαe : α₀ ≤ e / 2 := min_le_left _ _
  have hαh : α₀ ≤ δF / Cw := min_le_right _ _
  refine ⟨δ, α₀, hδ, hδN'.trans hδN1, hα₀, ?_⟩
  intro K hK hclose hradius ω hω hα
  have hα0 : 0 ≤ π / 2 - ω := sub_nonneg.mpr hω.2
  have hheight : Cw * (π / 2 - ω) ≤ δF := by
    have hh := (le_div_iff₀ hCw).1 (hα.trans hαh)
    nlinarith
  have homega : π / 2 - e < ω := by linarith
  have hsub : omittedWedges K ω ⊆
      (Icc (gerverRoofLeft P - η) (gerverRoofLeft P + η) ×ˢ Icc (0 : ℝ) (Cw * (π / 2 - ω))) ∪
      (Icc (gerverRoofRight P - η) (gerverRoofRight P + η) ×ˢ Icc (0 : ℝ) (Cw * (π / 2 - ω))) := by
    intro p hp
    obtain ⟨hpK, hy0, t, ht, -, hu, hv⟩ := omittedWedges_witness hp
    have hpN := (mem_niche_iff_slacks K p).2 ⟨hy0, t, ht, hu, hv⟩
    have hx := hlocal K hK (hclose.mono hδN') p hpN
    have hy := omittedWedges_height hK hR hradius p hp
    by_cases hleft : p.1 ≤ gerverRoofLeft P + η
    · exact Or.inl ⟨⟨hx.1, hleft⟩, hy⟩
    by_cases hright : gerverRoofRight P - η ≤ p.1
    · exact Or.inr ⟨⟨hright, hx.2⟩, hy⟩
    have hpbox : p ∈ Icc (gerverRoofLeft P + η) (gerverRoofRight P - η) ×ˢ Icc (0 : ℝ) δF :=
      ⟨⟨(not_le.mp hleft).le, (not_le.mp hright).le⟩, hy0, hy.2.trans hheight⟩
    obtain ⟨s, hs, hsU, hsV⟩ := hcover K (hclose.mono hδF') p hpbox
    exact (hp.1.2 ⟨hy0, s, ⟨hs.1, hs.2.trans homega⟩, hsU, hsV⟩).elim
  have ha := area_two_windows_le hη.le (mul_nonneg hCw.le hα0) hsub
  dsimp [Cw] at ha
  nlinarith

end MovingSofaStability
