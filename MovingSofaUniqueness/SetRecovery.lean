module

public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Basic

/-!
# Recover a closed set from containment and equal volume

These lemmas are independent of both moving-sofa definitions. They isolate the
last step of the paper argument: a closed full-measure subset of a regular-closed
set is the entire set, for a measure positive on nonempty open sets.

Regular closedness of Gerver's sofa is not proved or assumed globally here. It is
an explicit hypothesis of the applicable lemmas. Finite measure is needed only
when replacing a null set difference by equality of measures.
-/

@[expose] public section

open Set MeasureTheory

namespace MovingSofaUniqueness

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
variable {μ : Measure X} [Measure.IsOpenPosMeasure μ]
variable {s t : Set X}

/-- A closed set whose complement in `t` is null contains the interior of `t`. -/
theorem interior_subset_of_null_sdiff (hs : IsClosed s) (hnull : μ (t \ s) = 0) :
    interior t ⊆ s := by
  intro x hx
  by_contra hxs
  have hopen : IsOpen (interior t \ s) := isOpen_interior.inter hs.isOpen_compl
  have hne : μ (interior t \ s) ≠ 0 := hopen.measure_ne_zero μ ⟨x, hx, hxs⟩
  have hsub : interior t \ s ⊆ t \ s := Set.sdiff_subset_sdiff_left interior_subset
  exact hne (measure_mono_null hsub hnull)

/-- Closedness upgrades containment of the interior to containment of its closure. -/
theorem closure_interior_subset_of_null_sdiff (hs : IsClosed s)
    (hnull : μ (t \ s) = 0) : closure (interior t) ⊆ s :=
  closure_minimal (interior_subset_of_null_sdiff hs hnull) hs

/-- A closed full-measure subset of a regular-closed set is that set.

The hypothesis is nullity of the difference, so this version does not need finite
measure or measurability of either set. -/
theorem eq_of_subset_of_null_sdiff (hs : IsClosed s) (hst : s ⊆ t)
    (ht : closure (interior t) = t) (hnull : μ (t \ s) = 0) : s = t := by
  apply Set.Subset.antisymm hst
  rw [← ht]
  exact closure_interior_subset_of_null_sdiff hs hnull

/-- In the finite-measure case, equal measure supplies the null difference.

The finite-measure hypothesis must not be dropped: equality `∞ = ∞` gives no
information about the measure of the difference. -/
theorem eq_of_subset_of_measure_eq [OpensMeasurableSpace X]
    (hs : IsClosed s) (hst : s ⊆ t) (ht : closure (interior t) = t)
    (htfin : μ t ≠ ⊤) (hvol : μ s = μ t) : s = t := by
  have hsfin : μ s ≠ ⊤ := by
    rw [hvol]
    exact htfin
  have hnull : μ (t \ s) = 0 := by
    rw [measure_sdiff hst hs.measurableSet.nullMeasurableSet hsfin, hvol, tsub_self]
  exact eq_of_subset_of_null_sdiff hs hst ht hnull

/-- Under the set-recovery hypotheses, equality of measures is exactly equality
of the sets. -/
theorem measure_eq_iff_eq_of_subset [OpensMeasurableSpace X]
    (hs : IsClosed s) (hst : s ⊆ t) (ht : closure (interior t) = t)
    (htfin : μ t ≠ ⊤) : μ s = μ t ↔ s = t := by
  constructor
  · exact eq_of_subset_of_measure_eq hs hst ht htfin
  · intro h
    rw [h]

end MovingSofaUniqueness
