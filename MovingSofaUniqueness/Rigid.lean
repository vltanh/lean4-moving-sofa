module

public import MovingSofaOptimality.Main
public import MovingSofaUniqueness.SetRecovery

/-!
# Rigid maps in the library's coordinate plane

The product norm on `ℝ × ℝ` is not the Euclidean norm. We therefore represent
rotations and translations explicitly, rather than asserting that an arbitrary
plane rotation is an isometry for that norm. A `Rigid` map is a rotation by `angle`
about the origin followed by the translation by `shift`.
-/

@[expose] public section
noncomputable section

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

def Rigid.refl : Rigid := ⟨0, 0⟩
def Rigid.translate (v : Plane) : Rigid := ⟨0, v⟩
def Rigid.rotate (a : ℝ) : Rigid := ⟨a, 0⟩

/-- Apply `g`, then `h`. This is the order of `Equiv.trans`. -/
def Rigid.trans (g h : Rigid) : Rigid :=
  ⟨h.angle + g.angle, MovingSofaOptimality.rot h.angle g.shift + h.shift⟩

def Rigid.symm (g : Rigid) : Rigid :=
  ⟨-g.angle, -MovingSofaOptimality.rot (-g.angle) g.shift⟩

@[simp] theorem Rigid.refl_apply (p : Plane) : Rigid.refl p = p := by
  simp [Rigid.refl, Rigid.apply, MovingSofaOptimality.rot_zero]

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

/-- A rigid map preserves the Euclidean inner product of differences. -/
theorem Rigid.dot_sub (g : Rigid) (p q : Plane) :
    MovingSofaOptimality.dot (g p - g q) (g p - g q) = MovingSofaOptimality.dot (p - q) (p - q) := by
  simp only [Rigid.apply, MovingSofaOptimality.rot, MovingSofaOptimality.dot, Prod.fst_sub, Prod.snd_sub,
    Prod.fst_add, Prod.snd_add]
  nlinarith [sin_sq_add_cos_sq g.angle]

/-- A rigid map is a Euclidean isometry. -/
theorem Rigid.norm2_sub (g : Rigid) (p q : Plane) :
    MovingSofaOptimality.norm2 (g p - g q) = MovingSofaOptimality.norm2 (p - q) := by
  unfold MovingSofaOptimality.norm2
  rw [g.dot_sub]

def Rigid.toEquiv (g : Rigid) : Plane ≃ Plane where
  toFun := g
  invFun := g.symm
  left_inv := g.symm_apply_apply
  right_inv := g.apply_symm_apply

theorem Rigid.injective (g : Rigid) : Function.Injective g := g.toEquiv.injective

theorem Rigid.continuous (g : Rigid) : Continuous g := by
  change Continuous (fun p : Plane => MovingSofaOptimality.rot g.angle p + g.shift)
  exact (MovingSofaOptimality.ang_continuous_rot g.angle).add continuous_const

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

/-- Keep the direction of the final set equality explicit. -/
theorem Rigid.eq_image_symm (g : Rigid) {s t : Set Plane} (h : g '' s = t) :
    s = g.symm '' t := by
  rw [← h, g.symm_image_image]

/-- Recover the original closed set from the actual inclusion constructed on paper. -/
theorem Rigid.recover (g : Rigid) {s G : Set Plane} (hs : IsClosed s)
    (hsub : g '' s ⊆ G) (hreg : closure (interior G) = G)
    (hfin : volume G ≠ ⊤) (hvol : volume s = volume G) : g '' s = G := by
  apply MovingSofaUniqueness.eq_of_subset_of_measure_eq (μ := volume)
    (g.isClosed_image hs) hsub hreg hfin
  simpa using hvol

end MovingSofaUniqueness
