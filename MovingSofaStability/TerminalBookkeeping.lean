module

public import MovingSofaStability.Statement

/-!
# Terminal-angle loss: finite-measure bookkeeping

Uncompiled proof source. These lemmas implement the set/area comparison in
stability note 07. In particular they do not assume `S ⊆ U`: `S` can contain
points in the wedges omitted by stopping before a right-angle turn.

The geometric construction of the excluded floor rectangle and the upper
bound for the omitted wedges are NOT proved by this file. Those are explicit
hypotheses of `terminal_region_comparison`, rather than hidden axioms.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality

namespace MovingSofaStability

/-- Finiteness of the containing set is essential when using `area = toReal volume`. -/
theorem area_mono_of_finite {S T : Set Point} (hST : S ⊆ T) (hT : volume T ≠ ⊤) :
    area S ≤ area T :=
  ENNReal.toReal_mono hT (measure_mono hST)

theorem volume_ne_top_of_subset {S T : Set Point} (hST : S ⊆ T)
    (hT : volume T ≠ ⊤) : volume S ≠ ⊤ :=
  ne_top_of_le_ne_top hT (measure_mono hST)

theorem area_union_of_disjoint {S T : Set Point} (hd : Disjoint S T)
    (hT : MeasurableSet T) (hSf : volume S ≠ ⊤) (hTf : volume T ≠ ⊤) :
    area (S ∪ T) = area S + area T := by
  unfold area
  rw [measure_union hd hT, ENNReal.toReal_add hSf hTf]

/-- Partition a finite set by a measurable set, without assuming containment. -/
theorem area_inter_add_sdiff {S T : Set Point} (hT : MeasurableSet T)
    (hSf : volume S ≠ ⊤) : area (S ∩ T) + area (S \ T) = area S := by
  have hi : volume (S ∩ T) ≠ ⊤ := volume_ne_top_of_subset inter_subset_left hSf
  have hd : volume (S \ T) ≠ ⊤ := volume_ne_top_of_subset sdiff_subset hSf
  have h := congrArg ENNReal.toReal (measure_inter_add_sdiff (μ := volume) S hT)
  simpa only [ENNReal.toReal_add hi hd, area] using h

/-- The two directed missing areas differ by the area deficit. -/
theorem area_sdiff_balance {S U : Set Point} (hS : MeasurableSet S)
    (hU : MeasurableSet U) (hSf : volume S ≠ ⊤) (hUf : volume U ≠ ⊤) :
    area (U \ S) = area U - area S + area (S \ U) := by
  have h₁ := area_inter_add_sdiff hS hUf
  have h₂ := area_inter_add_sdiff hU hSf
  rw [inter_comm U S] at h₁
  linarith

/-- If a finite containing region is `U` plus a remainder, its area splits that way. -/
theorem area_eq_add_remainder {U V : Set Point} (hUV : U ⊆ V)
    (hU : MeasurableSet U) (hVf : volume V ≠ ⊤) :
    area V = area U + area (V \ U) := by
  have h := area_inter_add_sdiff hU hVf
  rw [inter_eq_right.mpr hUV] at h
  exact h.symm

/-- Excluding a disjoint measurable region loses its full area. -/
theorem area_add_excluded_le {S F V : Set Point}
    (hSV : S ⊆ V) (hFV : F ⊆ V) (hSF : Disjoint S F)
    (hF : MeasurableSet F) (hVf : volume V ≠ ⊤) :
    area S + area F ≤ area V := by
  have hSf := volume_ne_top_of_subset hSV hVf
  have hFf := volume_ne_top_of_subset hFV hVf
  rw [← area_union_of_disjoint hSF hF hSf hFf]
  exact area_mono_of_finite (union_subset hSV hFV) hVf

/-- The terminal strip wins when its excluded floor region costs at least
`2 c α` and the omitted wedges gain at most `c α`.

`U` is the full-angle set, `V` the partial-angle set, and `F` the excluded
floor region. The conclusion includes BOTH missing-set bounds. -/
theorem terminal_region_comparison {S U V F : Set Point} {M c α : ℝ}
    (hc : 0 < c) (hα : 0 ≤ α)
    (hSV : S ⊆ V) (hUV : U ⊆ V) (hFU : F ⊆ U) (hSF : Disjoint S F)
    (hS : MeasurableSet S) (hU : MeasurableSet U) (hF : MeasurableSet F)
    (hVf : volume V ≠ ⊤)
    (hfloor : 2 * c * α ≤ area F) (homitted : area (V \ U) ≤ c * α)
    (hmax : area U ≤ M) :
    area S ≤ area U - c * α ∧
      α ≤ (M - area S) / c ∧
      M - area U ≤ M - area S ∧
      area (S \ U) ≤ M - area S ∧
      area (U \ S) ≤ 2 * (M - area S) := by
  have hUf := volume_ne_top_of_subset hUV hVf
  have hSf := volume_ne_top_of_subset hSV hVf
  have hsum := area_add_excluded_le hSV (hFU.trans hUV) hSF hF hVf
  rw [area_eq_add_remainder hUV hU hVf] at hsum
  have hloss : area S ≤ area U - c * α := by linarith
  have hca : 0 ≤ c * α := mul_nonneg hc.le hα
  have hpay : c * α ≤ M - area S := by linarith
  have hangle : α ≤ (M - area S) / c := by
    apply (le_div_iff₀ hc).2
    nlinarith
  have hsub : S \ U ⊆ V \ U := fun p hp => ⟨hSV hp.1, hp.2⟩
  have hleft : area (S \ U) ≤ M - area S :=
    ((area_mono_of_finite hsub (volume_ne_top_of_subset sdiff_subset hVf)).trans
      homitted).trans hpay
  have hbalance := area_sdiff_balance hS hU hSf hUf
  refine ⟨hloss, hangle, ?_, hleft, ?_⟩
  · linarith
  · linarith

/-- Scalar form useful when the geometric estimates are already expressed as areas. -/
theorem terminal_scalar_comparison {M s u omitted lost c α : ℝ}
    (hc : 0 < c) (hα : 0 ≤ α) (hmax : u ≤ M)
    (hcompare : s ≤ u + omitted - lost)
    (hgain : omitted ≤ c * α) (hloss : 2 * c * α ≤ lost) :
    s ≤ u - c * α ∧ α ≤ (M - s) / c ∧ M - u ≤ M - s := by
  have h : s ≤ u - c * α := by linarith
  have hca : 0 ≤ c * α := mul_nonneg hc.le hα
  refine ⟨h, ?_, ?_⟩
  · apply (le_div_iff₀ hc).2
    nlinarith
  · linarith

end MovingSofaStability
