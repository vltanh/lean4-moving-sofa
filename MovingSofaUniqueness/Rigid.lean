module

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
## A closed subset of full measure

Let `μ` be a measure that is positive on nonempty open sets. A closed set `s` with
`μ (t \ s) = 0` contains the interior of `t`, hence its closure; so if `s ⊆ t` and `t` is regular
closed, then `s = t` (`eq_of_subset_of_null_sdiff`). When `μ t` is finite, equal measures give
`μ (t \ s) = 0` (`eq_of_subset_of_measure_eq`). This is the last step of the proof of the theorem
in note 20.
-/

section

open Set MeasureTheory

namespace MovingSofaUniqueness

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
variable {μ : Measure X} [Measure.IsOpenPosMeasure μ]
variable {s t : Set X}

/-- A closed set `s` with `μ (t \ s) = 0` contains the interior of `t`. -/
theorem interior_subset_of_null_sdiff (hs : IsClosed s) (hnull : μ (t \ s) = 0) :
    interior t ⊆ s := by
  intro x hx
  by_contra hxs
  have hopen : IsOpen (interior t \ s) := isOpen_interior.inter hs.isOpen_compl
  have hne : μ (interior t \ s) ≠ 0 := hopen.measure_ne_zero μ ⟨x, hx, hxs⟩
  have hsub : interior t \ s ⊆ t \ s := Set.sdiff_subset_sdiff_left interior_subset
  exact hne (measure_mono_null hsub hnull)

/-- A closed set `s` with `μ (t \ s) = 0` contains the closure of the interior of `t`. -/
theorem closure_interior_subset_of_null_sdiff (hs : IsClosed s)
    (hnull : μ (t \ s) = 0) : closure (interior t) ⊆ s :=
  closure_minimal (interior_subset_of_null_sdiff hs hnull) hs

/-- A closed subset `s` of a regular closed set `t` with `μ (t \ s) = 0` is `t`. -/
theorem eq_of_subset_of_null_sdiff (hs : IsClosed s) (hst : s ⊆ t)
    (ht : closure (interior t) = t) (hnull : μ (t \ s) = 0) : s = t := by
  apply Set.Subset.antisymm hst
  rw [← ht]
  exact closure_interior_subset_of_null_sdiff hs hnull

/-- A closed subset `s` of a regular closed set `t` with `μ s = μ t < ∞` is `t`. -/
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
## Rigid maps of the plane

The norm of `ℝ × ℝ` is the sup norm, so a rigid map is represented by its angle and its shift: a
`Rigid` map is the rotation `rot angle` about the origin followed by the translation by `shift`.
Rigid maps compose (`Rigid.trans`), have inverses (`Rigid.symm`) and preserve Lebesgue measure
(`Rigid.volume_image`). `Rigid.recover` concludes `g '' s = G` from `g '' s ⊆ G` and
`volume s = volume G`, for a closed set `s` and a regular closed set `G` of finite measure.
-/

section

open Set Real MeasureTheory

namespace MovingSofaUniqueness

abbrev Plane := ℝ × ℝ

/-- An orientation-preserving rigid map of the plane: the rotation by `angle` about the origin,
followed by the translation by `shift`. -/
structure Rigid where
  angle : ℝ
  shift : Plane

def Rigid.apply (g : Rigid) (p : Plane) : Plane :=
  MovingSofaOptimality.rot g.angle p + g.shift

instance : CoeFun Rigid (fun _ => Plane → Plane) := ⟨Rigid.apply⟩

def Rigid.translate (v : Plane) : Rigid := ⟨0, v⟩
def Rigid.rotate (a : ℝ) : Rigid := ⟨a, 0⟩

/-- The rigid map that applies `g`, then `h`, in the order of `Equiv.trans`. -/
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
  -- Rewrite the negative rotated translation by linearity of the rotation.
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

/-- A rotation about the origin preserves volume. -/
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

/-- If `g '' s ⊆ G` for a closed set `s` and a regular closed set `G` of finite volume, and
`volume s = volume G`, then `g '' s = G`. -/
theorem Rigid.recover (g : Rigid) {s G : Set Plane} (hs : IsClosed s)
    (hsub : g '' s ⊆ G) (hreg : closure (interior G) = G)
    (hfin : volume G ≠ ⊤) (hvol : volume s = volume G) : g '' s = G := by
  apply MovingSofaUniqueness.eq_of_subset_of_measure_eq (μ := volume)
    (g.isClosed_image hs) hsub hreg hfin
  simpa using hvol

end MovingSofaUniqueness

end
