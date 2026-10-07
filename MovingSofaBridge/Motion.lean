module

public import MovingSofaBridge.Defs
public import MovingSofaOptimality.Main

/-!
# The two notions of moving sofa agree

Formal-conjectures works in `ℝ² = EuclideanSpace ℝ (Fin 2)`: a moving sofa lies in the horizontal
side of the hallway and is moved by a continuous path in the affine isometries `E(2)` that starts
at the identity. Baek's paper works in `ℝ × ℝ`: a moving sofa is moved by a continuous rotation
angle and translation, starting from a translation. Read in coordinates, the two notions agree:
a set is a moving sofa of formal-conjectures if and only if it lies in the horizontal side and its
coordinates form a moving sofa of the paper (`isMovingSofa_iff`). So the two optimal areas are
equal (`sofaConstant_eq`).

The coordinate map preserves volume (`volume_coordinates_image`). Conversely, a rotation followed
by a translation is an element of `E(2)` (`realization`), continuous in the parameters. A path in
`E(2)` from the identity consists of rotations, whose angle lifts to a continuous real function
(`exists_angle_lift`).
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory
open scoped ENNReal unitInterval EuclideanGeometry

namespace MovingSofaBridge

open FormalConjectures

/-! ## Coordinates -/

/-- The plane `ℝ²` of formal-conjectures. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)
/-- The plane `ℝ × ℝ` of Baek's paper. -/
abbrev CoordinatePlane := ℝ × ℝ
/-- The group `E(2)` of affine isometries of `ℝ²`. -/
abbrev Motion := Point ≃ᵃⁱ[ℝ] Point

/-- The coordinates `(p 0, p 1)` of a point of `ℝ²`. -/
def coordinates (p : Point) : CoordinatePlane := (p 0, p 1)

/-- The point of `ℝ²` with given coordinates. -/
def point (p : CoordinatePlane) : Point := !₂[p.1, p.2]

@[simp] theorem coordinates_point (p : CoordinatePlane) : coordinates (point p) = p := rfl

@[simp] theorem point_coordinates (p : Point) : point (coordinates p) = p := by
  ext i
  fin_cases i <;> rfl

theorem coordinates_injective : Function.Injective coordinates :=
  Function.LeftInverse.injective point_coordinates

theorem coordinates_continuous : Continuous coordinates := by
  unfold coordinates
  fun_prop

theorem point_continuous : Continuous point := by
  unfold point
  fun_prop

@[simp] theorem coordinates_add (p q : Point) :
    coordinates (p + q) = coordinates p + coordinates q := rfl

@[simp] theorem coordinates_smul (a : ℝ) (p : Point) :
    coordinates (a • p) = a • coordinates p := rfl

/-- The coordinate map as a measurable equivalence. -/
def coordinatesMeasurableEquiv : Point ≃ᵐ CoordinatePlane :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

theorem coordinates_measurePreserving :
    MeasurePreserving coordinates (volume : Measure Point) volume :=
  (volume_preserving_finTwoArrow ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

@[simp] theorem point_coordinates_image (s : Set Point) :
    point '' (coordinates '' s) = s := by
  rw [Set.image_image]
  simp only [point_coordinates, Set.image_id']

@[simp] theorem coordinates_point_image (s : Set CoordinatePlane) :
    coordinates '' (point '' s) = s := by
  rw [Set.image_image]
  simp only [coordinates_point, Set.image_id']

/-- The coordinate map preserves volume. -/
theorem volume_coordinates_image (s : Set Point) :
    volume (coordinates '' s) = volume s := by
  have h := coordinates_measurePreserving.measure_preimage_emb
    coordinatesMeasurableEquiv.measurableEmbedding (coordinates '' s)
  rw [Set.preimage_image_eq s coordinates_injective] at h
  exact h.symm

theorem volume_point_image (s : Set CoordinatePlane) :
    volume (point '' s) = volume s := by
  rw [← volume_coordinates_image, coordinates_point_image]

theorem coordinates_image_closed {s : Set Point} (hs : IsClosed s) :
    IsClosed (coordinates '' s) := by
  rw [image_eq_preimage_of_inverse point_coordinates coordinates_point]
  exact hs.preimage point_continuous

theorem mem_horizontalHallway_iff (p : Point) :
    p ∈ MovingSofa.horizontalHallway ↔ p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 := by
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    exact hxy
  · intro hp
    exact ⟨p 0, p 1, hp, by ext i; fin_cases i <;> rfl⟩

theorem mem_verticalHallway_iff (p : Point) :
    p ∈ MovingSofa.verticalHallway ↔ 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ p 1 ≤ 1 := by
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    exact hxy
  · intro hp
    exact ⟨p 0, p 1, hp, by ext i; fin_cases i <;> rfl⟩

/-- The two horizontal sides of the hallway agree in coordinates. -/
theorem coordinates_mem_horizontal (p : Point) :
    coordinates p ∈ MovingSofaOptimality.horizSide ↔ p ∈ MovingSofa.horizontalHallway := by
  rw [mem_horizontalHallway_iff]
  rfl

/-- The two vertical sides of the hallway agree in coordinates. -/
theorem coordinates_mem_vertical (p : Point) :
    coordinates p ∈ MovingSofaOptimality.vertSide ↔ p ∈ MovingSofa.verticalHallway := by
  rw [mem_verticalHallway_iff]
  rfl

/-- The two hallways agree in coordinates. -/
theorem coordinates_mem_hallway (p : Point) :
    coordinates p ∈ MovingSofaOptimality.hallway ↔ p ∈ MovingSofa.hallway := by
  simp only [MovingSofaOptimality.hallway, MovingSofa.hallway, Set.mem_union,
    coordinates_mem_horizontal, coordinates_mem_vertical]

/-! ## Affine isometries preserve volume -/

section AffineIsometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An affine isometry is its linear part followed by a translation. -/
theorem affineIsometry_apply_eq (e : E ≃ᵃⁱ[ℝ] E) (x : E) :
    e x = e.linearIsometryEquiv x + e 0 := by
  simpa only [vadd_eq_add, add_zero] using e.map_vadd (0 : E) x

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- An affine isometry preserves volume. -/
theorem affineIsometry_measurePreserving (e : E ≃ᵃⁱ[ℝ] E) :
    MeasurePreserving e (volume : Measure E) volume := by
  have hp : MeasurePreserving (fun x : E => e.linearIsometryEquiv x + e 0)
      (volume : Measure E) volume :=
    (measurePreserving_add_right (volume : Measure E) (e 0)).comp
      e.linearIsometryEquiv.measurePreserving
  have he : (fun x : E => e.linearIsometryEquiv x + e 0) = e := by
    funext x
    exact (affineIsometry_apply_eq e x).symm
  rwa [he] at hp

/-- An affine isometry preserves the volume of every set, measurable or not. -/
theorem volume_image_affineIsometry (e : E ≃ᵃⁱ[ℝ] E) (s : Set E) :
    volume (e '' s) = volume s := by
  have h := (affineIsometry_measurePreserving e).measure_preimage_emb
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding (e '' s)
  rw [Set.preimage_image_eq s e.injective] at h
  exact h.symm

end AffineIsometry

/-! ## Rotations and translations as elements of `E(2)` -/

/-- The squared Euclidean norm in coordinates. -/
theorem norm_sq_coordinates (p : Point) : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

/-- The counterclockwise rotation of `ℝ²` by the angle `t`. -/
def euclideanRotate (t : ℝ) (p : Point) : Point :=
  !₂[cos t * p 0 - sin t * p 1, sin t * p 0 + cos t * p 1]

@[simp] theorem euclideanRotate_coordinates (t : ℝ) (p : Point) :
    coordinates (euclideanRotate t p) = MovingSofaOptimality.rot t (coordinates p) := rfl

theorem euclideanRotate_norm (t : ℝ) (p : Point) :
    ‖euclideanRotate t p‖ = ‖p‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_coordinates, norm_sq_coordinates]
  change (cos t * p 0 - sin t * p 1) ^ 2 +
      (sin t * p 0 + cos t * p 1) ^ 2 = (p 0) ^ 2 + (p 1) ^ 2
  linear_combination ((p 0) ^ 2 + (p 1) ^ 2) * sin_sq_add_cos_sq t

/-- The rotation by `t`, as a linear equivalence of `ℝ²`. -/
def rotationLinearEquiv (t : ℝ) : Point ≃ₗ[ℝ] Point where
  toFun := euclideanRotate t
  invFun := euclideanRotate (-t)
  left_inv p := by
    apply coordinates_injective
    simp only [euclideanRotate_coordinates, MovingSofaOptimality.rot_neg_rot]
  right_inv p := by
    apply coordinates_injective
    simp only [euclideanRotate_coordinates, MovingSofaOptimality.rot_rot_neg]
  map_add' p q := by
    apply coordinates_injective
    simp only [euclideanRotate_coordinates, coordinates_add, MovingSofaOptimality.rot_add_vec]
  map_smul' a p := by
    apply coordinates_injective
    simp only [euclideanRotate_coordinates, coordinates_smul, MovingSofaOptimality.rot_smul,
      RingHom.id_apply]

/-- The rotation by `t`, as a linear isometry of `ℝ²`. -/
def rotation (t : ℝ) : Point ≃ₗᵢ[ℝ] Point :=
  { rotationLinearEquiv t with norm_map' := euclideanRotate_norm t }

/-- The rotation by `ac.1` followed by the translation by `ac.2`, as an element of `E(2)`. -/
def realization (ac : ℝ × CoordinatePlane) : Motion :=
  (rotation ac.1).toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.vaddConst ℝ (point ac.2))

theorem realization_coordinates (ac : ℝ × CoordinatePlane) (p : Point) :
    coordinates (realization ac p) = MovingSofaOptimality.rot ac.1 (coordinates p) + ac.2 := by
  change coordinates (euclideanRotate ac.1 p + point ac.2) = _
  rw [coordinates_add, euclideanRotate_coordinates, coordinates_point]

/-- The quarter turn, as a continuous linear map. -/
def quarterTurn : Point →L[ℝ] Point where
  toFun p := !₂[-p 1, p 0]
  map_add' p q := by
    ext i
    fin_cases i <;> simp
    ring
  map_smul' a p := by
    ext i
    fin_cases i <;> simp
  cont := by fun_prop

/-- `realization (a, c)` as a continuous affine map: the linear part `cos a • id + sin a • J`,
with `J` the quarter turn, and the translation by `c`. -/
theorem realization_toContinuousAffineMap (ac : ℝ × CoordinatePlane) :
    (realization ac).toAffineIsometry.toContinuousAffineMap =
      (ContinuousAffineMap.decompHomeomorph ℝ Point Point).symm
        (point ac.2, cos ac.1 • (ContinuousLinearMap.id ℝ Point) +
          sin ac.1 • quarterTurn) := by
  ext p : 1
  apply coordinates_injective
  change coordinates (realization ac p) = _
  rw [realization_coordinates,
    ContinuousAffineMap.decompHomeomorph_symm_apply]
  change MovingSofaOptimality.rot ac.1 (coordinates p) + ac.2 =
    coordinates ((cos ac.1 • p + sin ac.1 • quarterTurn p) + point ac.2)
  ext <;> simp [MovingSofaOptimality.rot, coordinates, quarterTurn, point] <;> ring

/-- `realization` is continuous for the topology of `E(2)` of formal-conjectures. -/
theorem realization_continuous : Continuous realization := by
  apply continuous_induced_rng.mpr
  change Continuous (fun ac : ℝ × CoordinatePlane =>
    (realization ac).toAffineIsometry.toContinuousAffineMap)
  simp_rw [realization_toContinuousAffineMap]
  apply (ContinuousAffineMap.decompHomeomorph ℝ Point Point).symm.continuous.comp
  exact (point_continuous.comp continuous_snd).prodMk
    (((Real.continuous_cos.comp continuous_fst).smul continuous_const).add
      ((Real.continuous_sin.comp continuous_fst).smul continuous_const))

/-- If the rotation by `a` followed by the translation by `c` maps the coordinates of `s` onto
those of `t`, then `realization (a, c)` maps `s` onto `t`. -/
theorem realization_image_eq {s t : Set Point} (a : ℝ) (c : CoordinatePlane)
    (h : (fun p => MovingSofaOptimality.rot a p + c) '' (coordinates '' s) = coordinates '' t) :
    realization (a, c) '' s = t := by
  apply Set.image_injective.mpr coordinates_injective
  rw [← h, Set.image_image, Set.image_image]
  congr 1

/-! ## The rotation angle of a path from the identity -/

/-- The first vector of the standard basis of `ℝ²`. -/
def basisX : Point := !₂[1, 0]
/-- The second vector of the standard basis of `ℝ²`. -/
def basisY : Point := !₂[0, 1]
/-- The first column of the linear part of an element of `E(2)`. -/
def leftColumn (e : Motion) : Point := e.linearIsometryEquiv basisX
/-- The second column of the linear part of an element of `E(2)`. -/
def rightColumn (e : Motion) : Point := e.linearIsometryEquiv basisY

/-- The determinant of the linear part of an element of `E(2)`. -/
def determinant (e : Motion) : ℝ :=
  leftColumn e 0 * rightColumn e 1 - leftColumn e 1 * rightColumn e 0

/-- Evaluation is continuous for the topology of `E(2)`. -/
theorem continuous_motion_eval (p : Point) : Continuous (fun e : Motion => e p) :=
  (continuous_eval_const (F := Point →ᴬ[ℝ] Point) p).comp
    (continuous_induced_dom : Continuous fun e : Motion => e.toAffineIsometry.toContinuousAffineMap)

theorem linear_apply_eq_sub (e : Motion) (p : Point) :
    e.linearIsometryEquiv p = e p - e 0 :=
  eq_sub_of_add_eq (affineIsometry_apply_eq e p).symm

/-- The linear part of the identity is the identity. -/
theorem refl_linearIsometryEquiv_apply (p : Point) :
    (AffineIsometryEquiv.refl ℝ Point).linearIsometryEquiv p = p := rfl

theorem continuous_linear_eval (p : Point) :
    Continuous (fun e : Motion => e.linearIsometryEquiv p) := by
  simp_rw [linear_apply_eq_sub]
  exact (continuous_motion_eval p).sub (continuous_motion_eval 0)

/-- The two columns are orthonormal. -/
theorem column_laws (e : Motion) :
    (leftColumn e 0) ^ 2 + (leftColumn e 1) ^ 2 = 1 ∧
    (rightColumn e 0) ^ 2 + (rightColumn e 1) ^ 2 = 1 ∧
    leftColumn e 0 * rightColumn e 0 + leftColumn e 1 * rightColumn e 1 = 0 := by
  have hx : (leftColumn e 0) ^ 2 + (leftColumn e 1) ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => r ^ 2) (e.linearIsometryEquiv.norm_map basisX)
    rw [norm_sq_coordinates, norm_sq_coordinates] at h
    simpa [leftColumn, basisX] using h
  have hy : (rightColumn e 0) ^ 2 + (rightColumn e 1) ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => r ^ 2) (e.linearIsometryEquiv.norm_map basisY)
    rw [norm_sq_coordinates, norm_sq_coordinates] at h
    simpa [rightColumn, basisY] using h
  have hsum : (leftColumn e 0 + rightColumn e 0) ^ 2 +
      (leftColumn e 1 + rightColumn e 1) ^ 2 = 2 := by
    have h := congrArg (fun r : ℝ => r ^ 2)
      (e.linearIsometryEquiv.norm_map (basisX + basisY))
    rw [e.linearIsometryEquiv.map_add, norm_sq_coordinates, norm_sq_coordinates] at h
    simpa [leftColumn, rightColumn, basisX, basisY, one_add_one_eq_two] using h
  exact ⟨hx, hy, by nlinarith⟩

/-- The determinant of an element of `E(2)` is `±1`. -/
theorem determinant_sq (e : Motion) : determinant e ^ 2 = 1 := by
  obtain ⟨hx, hy, hxy⟩ := column_laws e
  calc
    _ = ((leftColumn e 0) ^ 2 + (leftColumn e 1) ^ 2) *
        ((rightColumn e 0) ^ 2 + (rightColumn e 1) ^ 2) -
        (leftColumn e 0 * rightColumn e 0 +
          leftColumn e 1 * rightColumn e 1) ^ 2 := by
      unfold determinant
      ring
    _ = 1 := by rw [hx, hy, hxy]; norm_num

theorem determinant_continuous : Continuous determinant := by
  have hx := continuous_linear_eval basisX
  have hy := continuous_linear_eval basisY
  unfold determinant leftColumn rightColumn
  fun_prop

/-- Along a continuous path from the identity, the determinant stays `1`. -/
theorem determinant_eq_one_on_path (m : I → Motion) (hm : Continuous m)
    (hzero : m 0 = AffineIsometryEquiv.refl ℝ Point) (t : I) :
    determinant (m t) = 1 := by
  have hd0 : determinant (m 0) = 1 := by
    rw [hzero]
    norm_num [determinant, leftColumn, rightColumn, refl_linearIsometryEquiv_apply, basisX,
      basisY]
  have hc := determinant_continuous.comp hm
  have hpos : 0 < determinant (m t) := by
    by_contra h
    have hle : determinant (m t) ≤ 0 := le_of_not_gt h
    obtain ⟨u, hu⟩ := intermediate_value_univ t 0 hc
      (show (0 : ℝ) ∈ Icc (determinant (m t)) (determinant (m 0)) from
        ⟨hle, by rw [hd0]; norm_num⟩)
    have hs := determinant_sq (m u)
    rw [show determinant (m u) = 0 from hu] at hs
    norm_num at hs
  have hs := determinant_sq (m t)
  nlinarith

/-- For determinant `1`, the second column is the first rotated by a right angle. -/
theorem rightColumn_of_determinant_one {e : Motion} (he : determinant e = 1) :
    rightColumn e 0 = -leftColumn e 1 ∧ rightColumn e 1 = leftColumn e 0 := by
  obtain ⟨hx, hy, _⟩ := column_laws e
  unfold determinant at he
  -- The two columns are unit vectors with determinant `1`, so the second is the first turned.
  have hsum : (rightColumn e 0 + leftColumn e 1) ^ 2 +
      (rightColumn e 1 - leftColumn e 0) ^ 2 = 0 := by nlinarith
  obtain ⟨h0, h1⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp hsum
  have h0' := pow_eq_zero_iff two_ne_zero |>.mp h0
  have h1' := pow_eq_zero_iff two_ne_zero |>.mp h1
  constructor <;> linarith

/-- With determinant `1`, the first column determines the linear part. -/
theorem linear_eq_euclideanRotate {e : Motion} {t : ℝ}
    (he : determinant e = 1) (hc : leftColumn e 0 = cos t)
    (hs : leftColumn e 1 = sin t) (p : Point) :
    e.linearIsometryEquiv p = euclideanRotate t p := by
  obtain ⟨h0, h1⟩ := rightColumn_of_determinant_one he
  have hp : p = (p 0) • basisX + (p 1) • basisY := by
    ext i
    fin_cases i <;> simp [basisX, basisY]
  have hl : e.linearIsometryEquiv p =
      (p 0) • leftColumn e + (p 1) • rightColumn e := by
    calc
      _ = e.linearIsometryEquiv ((p 0) • basisX + (p 1) • basisY) :=
        congrArg e.linearIsometryEquiv hp
      _ = _ := by simp only [map_add, map_smul, leftColumn, rightColumn]
  rw [hl]
  ext i
  fin_cases i <;> simp [euclideanRotate, h0, h1, hc, hs] <;> ring

/-- The first column of an element of `E(2)`, as a unit complex number. -/
def firstDirection (e : Motion) : Circle :=
  ⟨⟨leftColumn e 0, leftColumn e 1⟩, by
    apply mem_sphere_zero_iff_norm.mpr
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
    rw [Complex.sq_norm]
    simpa [Complex.normSq_apply, pow_two] using (column_laws e).1⟩

theorem firstDirection_continuous : Continuous firstDirection := by
  have hx := continuous_linear_eval basisX
  have h0 : Continuous (fun e : Motion => leftColumn e 0) := by
    unfold leftColumn
    fun_prop
  have h1 : Continuous (fun e : Motion => leftColumn e 1) := by
    unfold leftColumn
    fun_prop
  apply Continuous.subtype_mk
  exact Complex.equivRealProdCLM.symm.continuous.comp (h0.prodMk h1)

/-- A continuous path in `E(2)` from the identity is a rotation by a continuous angle, starting at
`0`, followed by a continuous translation, starting at `0`. The angle lifts the path of first
columns through the covering `ℝ → S¹`. -/
theorem exists_angle_lift (m : I → Motion) (hm : Continuous m)
    (hzero : m 0 = AffineIsometryEquiv.refl ℝ Point) :
    ∃ (θ : I → ℝ) (c : I → CoordinatePlane), Continuous θ ∧ Continuous c ∧
      θ 0 = 0 ∧ c 0 = 0 ∧ ∀ t p,
        coordinates (m t p) = MovingSofaOptimality.rot (θ t) (coordinates p) + c t := by
  let γ : C(I, Circle) :=
    ⟨fun t => firstDirection (m t), firstDirection_continuous.comp hm⟩
  have hγ0 : γ 0 = Circle.exp 0 := by
    change firstDirection (m 0) = Circle.exp 0
    rw [hzero, Circle.exp_zero]
    apply Circle.ext
    simp [firstDirection, leftColumn, basisX, refl_linearIsometryEquiv_apply, Complex.ext_iff]
  obtain ⟨θ, hθ, hθ0⟩ := Circle.isCoveringMap_exp.exists_path_lifts γ 0 hγ0
  refine ⟨θ, fun t => coordinates (m t 0), θ.continuous,
    coordinates_continuous.comp ((continuous_motion_eval 0).comp hm),
    hθ0, ?_, ?_⟩
  · change coordinates (m 0 0) = 0
    rw [hzero]
    rfl
  · intro t p
    have hexp : Circle.exp (θ t) = firstDirection (m t) := congrFun hθ t
    have hc : leftColumn (m t) 0 = cos (θ t) := by
      have h := congrArg (fun z : Circle => Complex.re (z : ℂ)) hexp
      simp only [Circle.coe_exp, Complex.exp_ofReal_mul_I_re] at h
      exact h.symm
    have hs : leftColumn (m t) 1 = sin (θ t) := by
      have h := congrArg (fun z : Circle => Complex.im (z : ℂ)) hexp
      simp only [Circle.coe_exp, Complex.exp_ofReal_mul_I_im] at h
      exact h.symm
    rw [affineIsometry_apply_eq,
      linear_eq_euclideanRotate (determinant_eq_one_on_path m hm hzero t) hc hs p,
      coordinates_add, euclideanRotate_coordinates]

/-! ## Moving sofas -/

/-- The coordinates of a moving sofa of formal-conjectures form a moving sofa of the paper. -/
theorem isMovingSofa_coordinates {s : Set Point}
    (hs : ∃ m, MovingSofa.IsMovingSofa s m) :
    MovingSofaOptimality.IsMovingSofa (coordinates '' s) := by
  obtain ⟨m, hm⟩ := hs
  obtain ⟨θ, c, hθ, hc, hθ0, hc0, hformula⟩ :=
    exists_angle_lift m hm.continuous hm.zero
  let τ : ℝ → I := fun t =>
    ⟨max 0 (min 1 t), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hτ : Continuous τ := by unfold τ; fun_prop
  have hτ0 : τ 0 = (0 : I) := by apply Subtype.ext; norm_num [τ]
  have hτ1 : τ 1 = (1 : I) := by apply Subtype.ext; norm_num [τ]
  refine ⟨-(θ 1), coordinates_image_closed hm.isClosed,
    hm.isConnected.image _ coordinates_continuous.continuousOn,
    (fun t => θ (τ t)), (fun t => c (τ t)), ?_⟩
  refine ⟨(hθ.comp hτ).continuousOn, (hc.comp hτ).continuousOn,
    by simpa [hτ0] using hθ0, by simp [hτ1], ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    simpa [hτ0, hθ0, hc0, MovingSofaOptimality.rot_zero] using
      (coordinates_mem_horizontal p).mpr (hm.initial hp)
  · rintro t ht _ ⟨p, hp, rfl⟩
    rw [← hformula (τ t) p]
    exact (coordinates_mem_hallway _).mpr
      (hm.subset_hallway (τ t) ⟨p, hp, rfl⟩)
  · rintro _ ⟨p, hp, rfl⟩
    rw [hτ1, ← hformula 1 p]
    exact (coordinates_mem_vertical _).mpr (hm.final ⟨p, hp, rfl⟩)

/-- A set in the horizontal side whose coordinates form a moving sofa of the paper is a moving
sofa of formal-conjectures: translate it to the start of the paper's motion, then follow that
motion. -/
theorem isMovingSofa_of_coordinates {s : Set Point}
    (hS : MovingSofaOptimality.IsMovingSofa (coordinates '' s))
    (hinitial : s ⊆ MovingSofa.horizontalHallway) :
    ∃ m, MovingSofa.IsMovingSofa s m := by
  obtain ⟨ω, hclosed, hconnected, θ, c, hm⟩ := hS
  have hsclosed : IsClosed s := by
    simpa only [preimage_image_eq _ coordinates_injective] using
      hclosed.preimage coordinates_continuous
  have hsconnected : IsConnected s := by
    simpa only [point_coordinates_image] using
      hconnected.image _ point_continuous.continuousOn
  have hθ : Continuous (fun t : I => θ t) :=
    hm.continuousOn_angle.comp_continuous continuous_subtype_val (fun t => t.property)
  have hc : Continuous (fun t : I => c t) :=
    hm.continuousOn_shift.comp_continuous continuous_subtype_val (fun t => t.property)
  -- The motion `m`: on `[0, 1/2]` it slides `s` by `lam t • c 0`, from `0` to `c 0` (the angle
  -- is `θ 0 = 0`); on `[1/2, 1]` it follows the paper's motion, reparametrized by `τ`.
  let τ : I → I := fun t =>
    ⟨max 0 (2 * (t : ℝ) - 1), le_max_left _ _,
      max_le zero_le_one (by linarith [t.property.2])⟩
  let lam : I → ℝ := fun t => min (2 * (t : ℝ)) 1
  have hτ : Continuous τ := by unfold τ; fun_prop
  have hlam : Continuous lam := by unfold lam; fun_prop
  have hlambounds (t : I) : 0 ≤ lam t ∧ lam t ≤ 1 :=
    ⟨le_min (by linarith [t.property.1]) zero_le_one, min_le_right _ _⟩
  have hτ0 : τ 0 = (0 : I) := by apply Subtype.ext; norm_num [τ]
  have hτ1 : τ 1 = (1 : I) := by apply Subtype.ext; norm_num [τ]
  have hlam0 : lam 0 = 0 := by norm_num [lam]
  have hlam1 : lam 1 = 1 := by norm_num [lam]
  let m : I → Motion := fun t => realization (θ (τ t), lam t • c (τ t))
  have hmcont : Continuous m :=
    realization_continuous.comp ((hθ.comp hτ).prodMk (hlam.smul (hc.comp hτ)))
  have hformula (t : I) (p : Point) :
      coordinates (m t p) = MovingSofaOptimality.rot (θ (τ t)) (coordinates p) +
        lam t • c (τ t) := realization_coordinates _ _
  have hmzero : m 0 = AffineIsometryEquiv.refl ℝ Point := by
    apply AffineIsometryEquiv.ext
    intro p
    apply coordinates_injective
    rw [hformula]
    simp [hτ0, hlam0, hm.angle_zero, MovingSofaOptimality.rot_zero]
  refine ⟨m, hsconnected, hsclosed, hmcont, hmzero, hinitial, ?_, ?_⟩
  · -- The sofa stays in the hallway: during the slide it stays in the horizontal side, between
    -- `s` and its translate by `c 0`; afterwards it is moved by the paper's motion.
    rintro t _ ⟨p, hp, rfl⟩
    apply (coordinates_mem_hallway _).mp
    rw [hformula]
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · have hτt : τ t = (0 : I) := by
        apply Subtype.ext
        simp only [τ]
        exact max_eq_left (by linarith)
      rw [hτt, Set.Icc.coe_zero, hm.angle_zero, MovingSofaOptimality.rot_zero]
      left
      have hstart := hm.start (coordinates p) ⟨p, hp, rfl⟩
      rw [hm.angle_zero, MovingSofaOptimality.rot_zero] at hstart
      have hfirst : coordinates p ∈ MovingSofaOptimality.horizSide :=
        (coordinates_mem_horizontal p).mpr (hinitial hp)
      have h := MovingSofaOptimality.ang_horizSide_combo
        (p := coordinates p) (a := (0 : CoordinatePlane)) (b := c 0)
        (by simpa using hfirst) hstart (hlambounds t).1 (hlambounds t).2
      simpa only [smul_zero, zero_add] using h
    · have hlamt : lam t = 1 := min_eq_right (by linarith [not_le.mp ht])
      rw [hlamt, one_smul]
      exact hm.inside (τ t) (τ t).property (coordinates p) ⟨p, hp, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    apply (coordinates_mem_vertical _).mp
    rw [hformula, hτ1, hlam1, one_smul]
    exact hm.finish (coordinates p) ⟨p, hp, rfl⟩

/-- **The two notions of moving sofa agree.** A set is a moving sofa of formal-conjectures if and
only if it lies in the horizontal side and its coordinates form a moving sofa of the paper. -/
theorem isMovingSofa_iff (s : Set Point) :
    (∃ m, MovingSofa.IsMovingSofa s m) ↔
      s ⊆ MovingSofa.horizontalHallway ∧
        MovingSofaOptimality.IsMovingSofa (coordinates '' s) := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨hm.initial, isMovingSofa_coordinates ⟨m, hm⟩⟩
  · rintro ⟨hinit, hpaper⟩
    exact isMovingSofa_of_coordinates hpaper hinit

/-- A translate of every moving sofa of the paper is a moving sofa of formal-conjectures, of the
same area. -/
theorem exists_isMovingSofa_volume_eq {S : Set CoordinatePlane}
    (hS : MovingSofaOptimality.IsMovingSofa S) :
    ∃ s : Set Point, (∃ m, MovingSofa.IsMovingSofa s m) ∧ volume s = volume S := by
  obtain ⟨ω, hclosed, hconnected, θ, c, hm⟩ := hS
  have hmove : MovingSofaOptimality.IsMovingSofaWithAngle S ω :=
    ⟨hclosed, hconnected, θ, c, hm⟩
  have hplaced := MovingSofaOptimality.mpc_isMovingSofaWithAngle_translate hmove (c 0)
  refine ⟨point '' ((fun p => p + c 0) '' S), ?_, ?_⟩
  · apply isMovingSofa_of_coordinates
    · rw [coordinates_point_image]
      exact ⟨ω, hplaced⟩
    · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      apply (coordinates_mem_horizontal _).mp
      simpa only [coordinates_point, hm.angle_zero, MovingSofaOptimality.rot_zero] using
        hm.start p hp
  · rw [volume_point_image, image_add_right]
    exact MovingSofaOptimality.volume_preimage_add S (-(c 0))

/-- The area of a moving sofa of formal-conjectures is at most the sofa constant. -/
theorem volume_le_sofaConstant {s : Set Point} (hs : ∃ m, MovingSofa.IsMovingSofa s m) :
    volume s ≤ MovingSofa.sofaConstant := by
  unfold MovingSofa.sofaConstant
  exact le_iSup₂ (f := fun (s : Set Point) (_ : ∃ m, MovingSofa.IsMovingSofa s m) => volume s) s hs

/-- **The two optimal areas agree.** The sofa constant of formal-conjectures is the supremum of the
areas of the moving sofas of the paper. -/
theorem sofaConstant_eq : MovingSofa.sofaConstant =
    ⨆ (S : Set CoordinatePlane) (_ : MovingSofaOptimality.IsMovingSofa S), volume S := by
  apply le_antisymm
  · unfold MovingSofa.sofaConstant
    refine iSup₂_le fun s hs => ?_
    rw [← volume_coordinates_image s]
    exact le_iSup₂ (f := fun (S : Set CoordinatePlane)
      (_ : MovingSofaOptimality.IsMovingSofa S) => volume S)
      (coordinates '' s) (isMovingSofa_coordinates hs)
  · refine iSup₂_le fun S hS => ?_
    obtain ⟨s, hs, hvol⟩ := exists_isMovingSofa_volume_eq hS
    rw [← hvol]
    exact volume_le_sofaConstant hs

end MovingSofaBridge
