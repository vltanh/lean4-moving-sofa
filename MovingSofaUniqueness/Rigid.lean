module

public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Basic
public import MovingSofaOptimality.Main

/-!
# Rigid maps, and the recovery of a set from its area

A `Rigid` map of `ℝ × ℝ` is a rotation about the origin followed by a translation; it preserves
volume. A closed set contained in a regular closed set `G` of finite measure, with the same measure,
is `G` itself (`Rigid.recover`): this is the last step of the uniqueness theorem.
-/

@[expose] public section
noncomputable section

/-!
## Recover a closed set from containment and equal volume

These lemmas are independent of both moving-sofa definitions. They isolate the
last step of the paper argument: a closed full-measure subset of a regular-closed
set is the entire set, for a measure positive on nonempty open sets.

Regular closedness of Gerver's sofa is not proved or assumed globally here. It is
an explicit hypothesis of the applicable lemmas. Finite measure is needed only
when replacing a null set difference by equality of measures.
-/

section

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

end MovingSofaUniqueness

end

/-!
## Rigid maps in the library's coordinate plane

The product norm on `ℝ × ℝ` is not the Euclidean norm. We therefore represent
rotations and translations explicitly, rather than asserting that an arbitrary
plane rotation is an isometry for that norm. A `Rigid` map is a rotation by `angle`
about the origin followed by the translation by `shift`.
-/

section

open Set Real MeasureTheory

namespace MovingSofaUniqueness

abbrev Plane := ℝ × ℝ

/-- An orientation-preserving Euclidean rigid map, in product coordinates. -/
structure Rigid where
  angle : ℝ
  shift : Plane

def Rigid.apply (g : Rigid) (p : Plane) : Plane :=
  MovingSofaOptimality.rot g.angle p + g.shift

instance : CoeFun Rigid (fun _ => Plane → Plane) := ⟨Rigid.apply⟩

def Rigid.translate (v : Plane) : Rigid := ⟨0, v⟩
def Rigid.rotate (a : ℝ) : Rigid := ⟨a, 0⟩

/-- Apply `g`, then `h`. This is the order of `Equiv.trans`. -/
def Rigid.trans (g h : Rigid) : Rigid :=
  ⟨h.angle + g.angle, MovingSofaOptimality.rot h.angle g.shift + h.shift⟩

def Rigid.symm (g : Rigid) : Rigid :=
  ⟨-g.angle, -MovingSofaOptimality.rot (-g.angle) g.shift⟩

@[simp] theorem Rigid.translate_apply (v p : Plane) : Rigid.translate v p = p + v := by
  simp [Rigid.translate, Rigid.apply, MovingSofaOptimality.rot_zero]

@[simp] theorem Rigid.rotate_apply (a : ℝ) (p : Plane) :
    Rigid.rotate a p = MovingSofaOptimality.rot a p := by
  simp [Rigid.rotate, Rigid.apply]

@[simp] theorem Rigid.trans_apply (g h : Rigid) (p : Plane) :
    (g.trans h) p = h (g p) := by
  simp only [Rigid.trans, Rigid.apply, MovingSofaOptimality.rot_add, MovingSofaOptimality.rot_add_vec]
  abel

@[simp] theorem Rigid.symm_apply_apply (g : Rigid) (p : Plane) : g.symm (g p) = p := by
  simp [Rigid.symm, Rigid.apply, MovingSofaOptimality.rot_add_vec, MovingSofaOptimality.rot_neg_rot]

@[simp] theorem Rigid.apply_symm_apply (g : Rigid) (p : Plane) : g (g.symm p) = p := by
  -- Rewrite the negative rotated translation using linearity, not a norm claim.
  have hneg : MovingSofaOptimality.rot g.angle (-MovingSofaOptimality.rot (-g.angle) g.shift) = -g.shift := by
    have h := (MovingSofaOptimality.gm_rotLM g.angle).map_neg (MovingSofaOptimality.rot (-g.angle) g.shift)
    simpa [MovingSofaOptimality.gm_rotLM, MovingSofaOptimality.rot_rot_neg] using h
  simp only [Rigid.symm, Rigid.apply, MovingSofaOptimality.rot_add_vec,
    MovingSofaOptimality.rot_rot_neg, hneg]
  abel

theorem Rigid.continuous (g : Rigid) : Continuous g := by
  change Continuous (fun p : Plane => MovingSofaOptimality.rot g.angle p + g.shift)
  exact (MovingSofaOptimality.ang_continuous_rot g.angle).add continuous_const

@[simp] theorem Rigid.trans_image (g h : Rigid) (s : Set Plane) :
    (g.trans h) '' s = h '' (g '' s) := by
  ext p
  simp only [Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨g x, ⟨x, hx, rfl⟩, (g.trans_apply h x).symm⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, g.trans_apply h x⟩

theorem Rigid.isClosed_image (g : Rigid) {s : Set Plane} (hs : IsClosed s) :
    IsClosed (g '' s) := by
  have he : g '' s = g.symm ⁻¹' s := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hp
      exact ⟨g.symm p, hp, g.apply_symm_apply p⟩
  rw [he]
  exact hs.preimage g.symm.continuous

/-- Exact ENNReal volume, not just its `toReal`, is invariant. -/
theorem volume_rot (a : ℝ) (s : Set Plane) :
    volume (MovingSofaOptimality.rot a '' s) = volume s := by
  have h := Measure.addHaar_image_linearMap volume (MovingSofaOptimality.gm_rotLM a) s
  have he : (⇑(MovingSofaOptimality.gm_rotLM a) : Plane → Plane) = MovingSofaOptimality.rot a := rfl
  rw [he, MovingSofaOptimality.gm_det_rotLM] at h
  simpa using h

theorem volume_translate (v : Plane) (s : Set Plane) :
    volume ((fun p => p + v) '' s) = volume s := by
  rw [image_add_right]
  exact MovingSofaOptimality.mpc_volume_preimage_add s (-v)

@[simp] theorem Rigid.volume_image (g : Rigid) (s : Set Plane) :
    volume (g '' s) = volume s := by
  have he : g '' s = (fun p => p + g.shift) '' (MovingSofaOptimality.rot g.angle '' s) := by
    rw [Set.image_image]
    rfl
  rw [he, volume_translate, volume_rot]

@[simp] theorem Rigid.area_image (g : Rigid) (s : Set Plane) :
    MovingSofaOptimality.area (g '' s) = MovingSofaOptimality.area s := by
  unfold MovingSofaOptimality.area
  rw [g.volume_image]

/-- Recover the original closed set from the actual inclusion constructed on paper. -/
theorem Rigid.recover (g : Rigid) {s G : Set Plane} (hs : IsClosed s)
    (hsub : g '' s ⊆ G) (hreg : closure (interior G) = G)
    (hfin : volume G ≠ ⊤) (hvol : volume s = volume G) : g '' s = G := by
  apply MovingSofaUniqueness.eq_of_subset_of_measure_eq (μ := volume)
    (g.isClosed_image hs) hsub hreg hfin
  simpa using hvol

end MovingSofaUniqueness

end
