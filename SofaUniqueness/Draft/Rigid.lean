module

public import MovingSofa.Main
public import SofaUniqueness.SetRecovery

/-!
# UNCOMPILED DRAFT: rigid maps in the library's coordinate plane

The product norm on `ℝ × ℝ` is not the Euclidean norm. We therefore represent
rotations and translations explicitly, rather than asserting that an arbitrary
plane rotation is an isometry for that norm. The upstream adapter separately
realizes these formulas as affine isometries of EuclideanSpace.

No Lean elaboration or execution has been performed for this draft.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory

namespace SofaUniqueness.Draft

abbrev Plane := ℝ × ℝ

/-- An orientation-preserving Euclidean rigid map, in product coordinates. -/
structure Rigid where
  angle : ℝ
  shift : Plane

def Rigid.apply (g : Rigid) (p : Plane) : Plane :=
  MovingSofa.rot g.angle p + g.shift

instance : CoeFun Rigid (fun _ => Plane → Plane) := ⟨Rigid.apply⟩

def Rigid.refl : Rigid := ⟨0, 0⟩
def Rigid.translate (v : Plane) : Rigid := ⟨0, v⟩
def Rigid.rotate (a : ℝ) : Rigid := ⟨a, 0⟩

/-- Apply `g`, then `h`. This is the order of `Equiv.trans`. -/
def Rigid.trans (g h : Rigid) : Rigid :=
  ⟨h.angle + g.angle, MovingSofa.rot h.angle g.shift + h.shift⟩

def Rigid.symm (g : Rigid) : Rigid :=
  ⟨-g.angle, -MovingSofa.rot (-g.angle) g.shift⟩

@[simp] theorem Rigid.refl_apply (p : Plane) : Rigid.refl p = p := by
  simp [Rigid.refl, Rigid.apply, MovingSofa.rot_zero]

@[simp] theorem Rigid.translate_apply (v p : Plane) : Rigid.translate v p = p + v := by
  simp [Rigid.translate, Rigid.apply, MovingSofa.rot_zero]

@[simp] theorem Rigid.rotate_apply (a : ℝ) (p : Plane) :
    Rigid.rotate a p = MovingSofa.rot a p := by
  simp [Rigid.rotate, Rigid.apply]

@[simp] theorem Rigid.trans_apply (g h : Rigid) (p : Plane) :
    (g.trans h) p = h (g p) := by
  simp only [Rigid.trans, Rigid.apply, MovingSofa.rot_add, MovingSofa.rot_add_vec]
  abel

@[simp] theorem Rigid.symm_apply_apply (g : Rigid) (p : Plane) : g.symm (g p) = p := by
  simp [Rigid.symm, Rigid.apply, MovingSofa.rot_add_vec, MovingSofa.rot_neg_rot]

@[simp] theorem Rigid.apply_symm_apply (g : Rigid) (p : Plane) : g (g.symm p) = p := by
  -- Rewrite the negative rotated translation using linearity, not a norm claim.
  have hneg : MovingSofa.rot g.angle (-MovingSofa.rot (-g.angle) g.shift) = -g.shift := by
    have h := (MovingSofa.gm_rotLM g.angle).map_neg (MovingSofa.rot (-g.angle) g.shift)
    simpa [MovingSofa.gm_rotLM, MovingSofa.rot_rot_neg] using h
  simp only [Rigid.symm, Rigid.apply, MovingSofa.rot_add_vec,
    MovingSofa.rot_rot_neg, hneg]
  abel

def Rigid.toEquiv (g : Rigid) : Plane ≃ Plane where
  toFun := g
  invFun := g.symm
  left_inv := g.symm_apply_apply
  right_inv := g.apply_symm_apply

theorem Rigid.injective (g : Rigid) : Function.Injective g := g.toEquiv.injective

theorem Rigid.continuous (g : Rigid) : Continuous g := by
  change Continuous (fun p : Plane => MovingSofa.rot g.angle p + g.shift)
  exact (MovingSofa.ang_continuous_rot g.angle).add continuous_const

def Rigid.toHomeomorph (g : Rigid) : Plane ≃ₜ Plane where
  toEquiv := g.toEquiv
  continuous_toFun := g.continuous
  continuous_invFun := g.symm.continuous

@[simp] theorem Rigid.trans_image (g h : Rigid) (s : Set Plane) :
    (g.trans h) '' s = h '' (g '' s) := by
  ext p
  simp only [Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨g x, ⟨x, hx, rfl⟩, (g.trans_apply h x).symm⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, g.trans_apply h x⟩

@[simp] theorem Rigid.symm_image_image (g : Rigid) (s : Set Plane) :
    g.symm '' (g '' s) = s := by
  ext p
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    simpa using hx
  · intro hp
    exact ⟨g p, ⟨p, hp, rfl⟩, g.symm_apply_apply p⟩

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
    volume (MovingSofa.rot a '' s) = volume s := by
  have h := Measure.addHaar_image_linearMap volume (MovingSofa.gm_rotLM a) s
  have he : (⇑(MovingSofa.gm_rotLM a) : Plane → Plane) = MovingSofa.rot a := rfl
  rw [he, MovingSofa.gm_det_rotLM] at h
  simpa using h

theorem volume_translate (v : Plane) (s : Set Plane) :
    volume ((fun p => p + v) '' s) = volume s := by
  rw [image_add_right]
  exact MovingSofa.mpc_volume_preimage_add s (-v)

@[simp] theorem Rigid.volume_image (g : Rigid) (s : Set Plane) :
    volume (g '' s) = volume s := by
  have he : g '' s = (fun p => p + g.shift) '' (MovingSofa.rot g.angle '' s) := by
    rw [Set.image_image]
    rfl
  rw [he, volume_translate, volume_rot]

@[simp] theorem Rigid.area_image (g : Rigid) (s : Set Plane) :
    MovingSofa.area (g '' s) = MovingSofa.area s := by
  unfold MovingSofa.area
  rw [g.volume_image]

/-- Keep the direction of the final set equality explicit. -/
theorem Rigid.eq_image_symm (g : Rigid) {s t : Set Plane} (h : g '' s = t) :
    s = g.symm '' t := by
  rw [← h, g.symm_image_image]

/-- Recover the original closed set from the actual inclusion constructed on paper. -/
theorem Rigid.recover (g : Rigid) {s G : Set Plane} (hs : IsClosed s)
    (hsub : g '' s ⊆ G) (hreg : closure (interior G) = G)
    (hfin : volume G ≠ ⊤) (hvol : volume s = volume G) : g '' s = G := by
  apply SofaUniqueness.eq_of_subset_of_measure_eq (μ := volume)
    (g.isClosed_image hs) hsub hreg hfin
  simpa using hvol

end SofaUniqueness.Draft
