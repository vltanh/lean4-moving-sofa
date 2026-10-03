module

public import MovingSofaBridge.Motion
public import MovingSofaBridge.RomikParams

/-!
# The two Gerver's sofas agree

Formal-conjectures defines Gerver's sofa from Gerver's four constants: the rotation path `p` is
given by integrals of a piecewise radius `r`, and each hallway is translated by `p α` and then
rotated by `α`. Baek's paper defines it from Romik's parameters: the rotation path `𝐱` is glued
from five explicit phases, and each hallway is rotated by `t` and then translated by `𝐱 t`. In
coordinates the two sets are equal (`gerversSofa_eq`).

The radius `r` is the speed of the contact point `𝐂` of Romik's path, so the integrals are the
coordinates of `𝐂` and of its reflection `𝐀` (`contactC_integral_coordinates`,
`contactA_integral_coordinates`). They are the coordinates of Romik's path in the rotating frame,
so rotating formal-conjectures' path by `t` gives Romik's path (`rotated_prePath`). Finally
formal-conjectures' rotation of `ℝ²` is the rotation of coordinates (`rotation_coordinates`).
-/

@[expose] public section
noncomputable section

open Set Real Filter Topology MeasureTheory MovingSofaOptimality MovingSofaOptimality.GerverParams
open scoped EuclideanGeometry

namespace MovingSofaBridge.GerverConstants

/-! ## The rotation path of Gerver's four constants -/

section

variable (D : GerverConstants)

/-- Formal-conjectures' radius `GerversSofa.r`, for the constants `D`. -/
def radius (t : ℝ) : ℝ :=
  if t ≤ D.φ then 1 / 2
  else if t ≤ D.θ then (1 + D.A + t - D.φ) / 2
  else if t ≤ π / 2 - D.θ then D.A + t - D.φ
  else if t ≤ π / 2 - D.φ then
    D.B - (π / 2 - t - D.φ) * (1 + D.A) / 2 - (π / 2 - t - D.φ) ^ 2 / 4
  else 0

/-- Formal-conjectures' `GerversSofa.y`, for the constants `D`. -/
def boundaryY (t : ℝ) : ℝ :=
  ∫ s in t..π / 2 - D.φ, D.radius s * sin s

/-- Formal-conjectures' `GerversSofa.x`, for the constants `D`. -/
def boundaryX (t : ℝ) : ℝ :=
  1 - ∫ s in t..π / 2 - D.φ, D.radius s * cos s

/-- Formal-conjectures' rotation path `GerversSofa.p`, for the constants `D`, in coordinates. -/
def prePath (t : ℝ) : ℝ × ℝ :=
  (if t ≤ D.φ then cos t - 1
   else D.boundaryX (π / 2 - t) * cos t +
     D.boundaryY (π / 2 - t) * sin t - 1,
   if t ≤ π / 2 - D.φ then
     D.boundaryY t * cos t - (4 * D.boundaryX 0 - 2 - D.boundaryX t) * sin t - 1
   else -(4 * D.boundaryX 0 - 3) * sin t - 1)

end

/-- Formal-conjectures' `rotateTranslate` in coordinates: translate by `p`, then rotate by `t`. -/
def rotateTranslatePair (t : ℝ) (p q : ℝ × ℝ) : ℝ × ℝ := rot t (q + p)

/-- The sofa of a rotation path `p` in the convention of formal-conjectures
(`sofaOfRotateTranslatePath`), in coordinates. -/
def shapeFromPrePath (p : ℝ → ℝ × ℝ) : Set (ℝ × ℝ) :=
  rotateTranslatePair 0 (p 0) '' horizSide ∩
  rotateTranslatePair (π / 2) (p (π / 2)) '' vertSide ∩
  ⋂ t ∈ Icc 0 (π / 2), rotateTranslatePair t (p t) '' MovingSofaOptimality.hallway

/-- The sofa of Gerver's four constants, in coordinates. -/
def shape (D : GerverConstants) : Set (ℝ × ℝ) := shapeFromPrePath D.prePath

/-- If `p 0 = 0` and rotating `p t` by `t` gives `x t`, the two conventions give the same sofa. -/
theorem shape_eq_of_rotated_path {p x : ℝ → ℝ × ℝ}
    (hzero : p 0 = 0)
    (hpath : ∀ t ∈ Icc 0 (π / 2), rot t (p t) = x t) :
    shapeFromPrePath p = shapeOfPath x := by
  have hL : (0 : ℝ) ≤ π / 2 := by positivity
  have hmap : ∀ t ∈ Icc 0 (π / 2),
      rotateTranslatePair t (p t) = fun q => x t + rot t q := by
    intro t ht
    funext q
    rw [rotateTranslatePair, rot_add_vec, hpath t ht, add_comm]
  have hstart : rotateTranslatePair 0 (p 0) '' horizSide = horizSide := by
    have hid : rotateTranslatePair 0 (p 0) = id := by
      funext q
      simp [rotateTranslatePair, hzero]
    rw [hid, Set.image_id]
  have hfinish := hmap (π / 2) ⟨hL, le_rfl⟩
  have hall : (⋂ t ∈ Icc 0 (π / 2),
      rotateTranslatePair t (p t) '' MovingSofaOptimality.hallway) =
      ⋂ t ∈ Icc 0 (π / 2), (fun q => x t + rot t q) '' MovingSofaOptimality.hallway :=
    iInter₂_congr fun t ht => by rw [hmap t ht]
  unfold shapeFromPrePath shapeOfPath
  rw [hstart, hfinish, hall, Set.inter_right_comm]

/-! ## The radius is the speed of Romik's contact point `𝐂` -/

private theorem intervalIntegrable_ite {p : ℝ → Prop} [DecidablePred p]
    (hp : MeasurableSet {t | p t}) {f g : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun t => if p t then f t else g t) volume a b := by
  have he : (fun t => if p t then f t else g t) =
      fun t => ({t | p t} : Set ℝ).indicator f t + ({t | p t} : Set ℝ)ᶜ.indicator g t := by
    funext t
    by_cases ht : p t <;> simp [ht]
  rw [he]
  exact ⟨(hf.1.indicator hp).add (hg.1.indicator hp.compl),
    (hf.2.indicator hp).add (hg.2.indicator hp.compl)⟩

/-- The same piecewise radius, with right values at the four breakpoints. -/
def rightRadius (D : GerverConstants) (t : ℝ) : ℝ :=
  if t < D.φ then 1 / 2
  else if t < D.θ then (1 + D.A + t - D.φ) / 2
  else if t < π / 2 - D.θ then D.A + t - D.φ
  else if t < π / 2 - D.φ then
    D.B - (π / 2 - t - D.φ) * (1 + D.A) / 2 - (π / 2 - t - D.φ) ^ 2 / 4
  else 0

/-- `rightRadius` is, phase by phase, the speed of the contact point `𝐂` of Romik's path. -/
theorem rightRadius_eq_phase (D : GerverConstants) (t : ℝ) :
    D.rightRadius t = (D.toRomik.gs_phase (D.toRomik.gs_ridx t)).ρC t := by
  have hφ : D.toRomik.φ = D.φ := rfl
  have hθ : D.toRomik.θ = D.θ := rfl
  unfold rightRadius GerverParams.gs_ridx
  rw [hφ, hθ]
  split_ifs <;>
    simp only [gs_phase, gs_ph1, gs_ph2, gs_ph3, gs_ph4, gs_ph5, gs_Phase.ρC, toRomik, b1, b2] <;>
    ring

/-- `radius` and `rightRadius` differ only at the four breakpoints. -/
theorem radius_ae_rightRadius (D : GerverConstants) : D.radius =ᵐ[volume] D.rightRadius := by
  have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ D.φ := by rw [ae_iff]; simp
  have h2 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ D.θ := by rw [ae_iff]; simp
  have h3 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ π / 2 - D.θ := by rw [ae_iff]; simp
  have h4 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ π / 2 - D.φ := by rw [ae_iff]; simp
  filter_upwards [h1, h2, h3, h4] with t ht1 ht2 ht3 ht4
  simp only [radius, rightRadius, le_iff_lt_or_eq, ht1, ht2, ht3, ht4, or_false]

/-- `rightRadius` times a continuous function is integrable. -/
theorem rightRadius_mul_integrable (D : GerverConstants) {w : ℝ → ℝ} (hw : Continuous w)
    (a b : ℝ) : IntervalIntegrable (fun t => D.rightRadius t * w t) volume a b := by
  simp only [rightRadius, ite_mul]
  apply intervalIntegrable_ite measurableSet_Iio
  · exact ((continuous_const.mul hw)).intervalIntegrable a b
  · apply intervalIntegrable_ite measurableSet_Iio
    · exact ((by fun_prop : Continuous fun t : ℝ => (1 + D.A + t - D.φ) / 2).mul
        hw).intervalIntegrable a b
    · apply intervalIntegrable_ite measurableSet_Iio
      · exact ((by fun_prop : Continuous fun t : ℝ => D.A + t - D.φ).mul
          hw).intervalIntegrable a b
      · apply intervalIntegrable_ite measurableSet_Iio
        · exact ((by fun_prop : Continuous fun t : ℝ =>
            D.B - (π / 2 - t - D.φ) * (1 + D.A) / 2 - (π / 2 - t - D.φ) ^ 2 / 4).mul
              hw).intervalIntegrable a b
        · simp

/-- The integrals against `radius` and `rightRadius` agree. -/
theorem integral_radius_eq_rightRadius (D : GerverConstants) (w : ℝ → ℝ) (a b : ℝ) :
    (∫ t in a..b, D.radius t * w t) = ∫ t in a..b, D.rightRadius t * w t :=
  intervalIntegral.integral_congr_ae (D.radius_ae_rightRadius.mono fun t ht _ => by rw [ht])

/-- The right derivative of Romik's contact point `𝐂`. -/
theorem contactC_right_deriv {D : GerverConstants} (hD : D.Valid) (t : ℝ) :
    HasDerivWithinAt (contactC D.toRomik.path)
      (-D.rightRadius t • uvec t) (Ioi t) t := by
  rw [rightRadius_eq_phase]
  exact (gs_hasDerivWithinAt_contactC (romik_solution hD).1
    (gs_rpiece_ridx t)).mono Ioi_subset_Ici_self

/-- The integrals of `radius` against `cos` and `sin` are the increments of the coordinates of
`𝐂`. -/
theorem contactC_integrals {D : GerverConstants} (hD : D.Valid) (a b : ℝ) :
    (∫ t in a..b, D.radius t * cos t) =
        (contactC D.toRomik.path a).1 - (contactC D.toRomik.path b).1 ∧
    (∫ t in a..b, D.radius t * sin t) =
        (contactC D.toRomik.path a).2 - (contactC D.toRomik.path b).2 := by
  have hcont := gs_continuous_contactC (romik_solution hD).1
  have hdx : ∀ t, HasDerivWithinAt (fun t => (contactC D.toRomik.path t).1)
      (-(D.rightRadius t * cos t)) (Ioi t) t := by
    intro t
    have hd := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt t
      (contactC_right_deriv hD t)
    refine hd.congr_deriv ?_
    simp only [ContinuousLinearMap.coe_fst', Prod.smul_fst, uvec, smul_eq_mul]
    ring
  have hdy : ∀ t, HasDerivWithinAt (fun t => (contactC D.toRomik.path t).2)
      (-(D.rightRadius t * sin t)) (Ioi t) t := by
    intro t
    have hd := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt t
      (contactC_right_deriv hD t)
    refine hd.congr_deriv ?_
    simp only [ContinuousLinearMap.coe_snd', Prod.smul_snd, uvec, smul_eq_mul]
    ring
  have hx := intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont.fst.continuousOn
    (fun t _ => hdx t) (D.rightRadius_mul_integrable continuous_cos a b).neg
  have hy := intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont.snd.continuousOn
    (fun t _ => hdy t) (D.rightRadius_mul_integrable continuous_sin a b).neg
  rw [intervalIntegral.integral_neg] at hx hy
  rw [D.integral_radius_eq_rightRadius cos a b, D.integral_radius_eq_rightRadius sin a b]
  constructor <;> linarith

/-! ## The integrals are the coordinates of Romik's contact points -/

/-- `𝐂` is constant on the last phase. -/
theorem contactC_last {D : GerverConstants} (hD : D.Valid) {t : ℝ}
    (ht : π / 2 - D.φ ≤ t) :
    contactC D.toRomik.path t = (2 * D.k3.1 - 1, 0) := by
  rw [gs_contactC_eq (romik_solution hD).1 (show gs_piece D.toRomik 4 t from ht)]
  ext <;> simp only [gs_phase, gs_ph5, gs_Phase.C, toRomik, rot, Prod.fst_add, Prod.snd_add]
  · linear_combination (-D.a1) * sin_sq_add_cos_sq t
  · linear_combination (-1 / 4 : ℝ) * sin_sq_add_cos_sq t

/-- `𝐀` is constant on the first phase. -/
theorem contactA_first {D : GerverConstants} (hD : D.Valid) {t : ℝ} (ht : t ≤ D.φ) :
    contactA D.toRomik.path t = (1, 0) := by
  rw [gs_contactA_eq (romik_solution hD).1 (show gs_piece D.toRomik 0 t from ht)]
  change rot t (D.a1 * cos t + (-1 / 4) * sin t - 1 + 1,
      -D.a1 * sin t + (-1 / 4) * cos t) + D.k1 = _
  rw [sub_add_cancel, show (D.a1 * cos t + (-1 / 4) * sin t, -D.a1 * sin t + (-1 / 4) * cos t) =
    (dot (D.a1, -1 / 4) (uvec t), dot (D.a1, -1 / 4) (vvec t)) by ext <;> simp [dot],
    rot_frame_coords]
  ext <;> simp only [k1, Prod.fst_add, Prod.snd_add] <;> ring

/-- The value of `𝐂` at `0`. -/
theorem contactC_zero {D : GerverConstants} (hD : D.Valid) :
    contactC D.toRomik.path 0 = (1 - 2 * D.a1, 1) := by
  rw [gs_contactC_eq (romik_solution hD).1
    (show gs_piece D.toRomik 0 0 from hD.phi_pos.le)]
  simp only [gs_phase, gs_ph1, gs_Phase.C, toRomik, k1, rot, sin_zero, cos_zero]
  ext <;> simp <;> ring

/-- Every parameter belongs to one of the five closed phase intervals. -/
private theorem exists_piece (P : GerverParams) (t : ℝ) :
    ∃ i : Fin 5, gs_piece P i t := by
  by_cases h1 : t ≤ P.φ
  · exact ⟨0, h1⟩
  by_cases h2 : t ≤ P.θ
  · exact ⟨1, ⟨(lt_of_not_ge h1).le, h2⟩⟩
  by_cases h3 : t ≤ π / 2 - P.θ
  · exact ⟨2, ⟨(lt_of_not_ge h2).le, h3⟩⟩
  by_cases h4 : t ≤ π / 2 - P.φ
  · exact ⟨3, ⟨(lt_of_not_ge h3).le, h4⟩⟩
  exact ⟨4, (lt_of_not_ge h4).le⟩

private theorem reflected_piece (D : GerverConstants) (i : Fin 5) {t : ℝ}
    (ht : gs_piece D.toRomik i t) :
    gs_piece D.toRomik (4 - (i : ℕ)) (π / 2 - t) := by
  obtain ⟨k, hk⟩ := i
  interval_cases k <;> simp only [Nat.sub_zero, gs_piece, toRomik] at ht ⊢
  · linarith
  · constructor <;> linarith [ht.1, ht.2]
  · constructor <;> linarith [ht.1, ht.2]
  · constructor <;> linarith [ht.1, ht.2]
  · linarith

/-- On each phase, `𝐀` is the reflection of `𝐂` at the reflected angle. -/
private theorem phase_contact_reflection (D : GerverConstants) (i : Fin 5) (t : ℝ) :
    (D.toRomik.gs_phase i).A t =
      D.reflect ((D.toRomik.gs_phase (4 - (i : ℕ))).C (π / 2 - t)) := by
  obtain ⟨k, hk⟩ := i
  interval_cases k <;> ext <;>
    simp only [Nat.sub_zero, gs_phase, gs_ph1, gs_ph2, gs_ph3, gs_ph4, gs_ph5,
      gs_Phase.A, gs_Phase.C, toRomik, reflect, k1, rot,
      cos_pi_div_two_sub, sin_pi_div_two_sub, Prod.fst_add, Prod.snd_add] <;> ring

/-- `𝐀 t` is the reflection of `𝐂 (π/2 - t)`. -/
theorem contactA_reflection {D : GerverConstants} (hD : D.Valid) (t : ℝ) :
    contactA D.toRomik.path t = D.reflect (contactC D.toRomik.path (π / 2 - t)) := by
  obtain ⟨i, hi⟩ := exists_piece D.toRomik t
  rw [gs_contactA_eq (romik_solution hD).1 hi,
    gs_contactC_eq (romik_solution hD).1 (reflected_piece D i hi)]
  exact phase_contact_reflection D i t

/-- The integrals `boundaryX` and `boundaryY` give the coordinates of `𝐂`. -/
theorem contactC_integral_coordinates {D : GerverConstants} (hD : D.Valid) (t : ℝ) :
    contactC D.toRomik.path t = (2 * D.k3.1 - D.boundaryX t, D.boundaryY t) := by
  obtain ⟨hx, hy⟩ := contactC_integrals hD t (π / 2 - D.φ)
  rw [contactC_last hD le_rfl] at hx hy
  ext <;> simp only [boundaryX, boundaryY] at hx hy ⊢ <;> linarith

/-- `boundaryX` and `boundaryY` at `π/2 - t` are the coordinates of `𝐀 t`. -/
theorem contactA_integral_coordinates {D : GerverConstants} (hD : D.Valid) (t : ℝ) :
    contactA D.toRomik.path t = (D.boundaryX (π / 2 - t), D.boundaryY (π / 2 - t)) := by
  rw [contactA_reflection hD, contactC_integral_coordinates hD]
  ext <;> simp only [reflect]
  ring

/-- The value of `boundaryX` at `0`, from `𝐂 0`. -/
theorem boundaryX_zero {D : GerverConstants} (hD : D.Valid) :
    D.boundaryX 0 = 2 * D.k3.1 - 1 + 2 * D.a1 := by
  have h := congrArg Prod.fst (contactC_integral_coordinates hD 0)
  rw [contactC_zero hD] at h
  linarith

/-- The horizontal normalization `4 x(0) - 2` of formal-conjectures' path. -/
theorem horizontal_normalization {D : GerverConstants} (hD : D.Valid) :
    2 * D.k3.1 = 4 * D.boundaryX 0 - 2 := by
  rw [boundaryX_zero hD]
  have h := k3_fst hD
  linarith

/-! ## The two rotation paths agree -/

private theorem contactA_projection (D : GerverConstants) (t : ℝ) :
    dot (contactA D.toRomik.path t) (uvec t) = dot (D.toRomik.path t) (uvec t) + 1 := by
  rw [contactA, dot_add_left, dot_add_left, dot_smul_left,
    dot_vvec_uvec, dot_uvec_self]
  ring

private theorem contactC_projection (D : GerverConstants) (t : ℝ) :
    dot (contactC D.toRomik.path t) (vvec t) = dot (D.toRomik.path t) (vvec t) + 1 := by
  rw [contactC, dot_add_left, dot_sub_left, dot_smul_left,
    dot_uvec_vvec, dot_vvec_self]
  ring

/-- Formal-conjectures' path gives the coordinates of Romik's path in the rotating frame. -/
theorem prePath_eq_projections {D : GerverConstants} (hD : D.Valid) (t : ℝ) :
    D.prePath t = (dot (D.toRomik.path t) (uvec t), dot (D.toRomik.path t) (vvec t)) := by
  have hA := contactA_projection D t
  have hC := contactC_projection D t
  unfold prePath
  congr 1
  · -- The first coordinate, from `𝐀 t`: constant `(1, 0)` up to `φ`, then given by the integrals.
    split_ifs with ht
    · rw [contactA_first hD ht] at hA
      simp only [dot, uvec] at hA ⊢
      linarith
    · rw [contactA_integral_coordinates hD] at hA
      simp only [dot, uvec] at hA ⊢
      linarith
  · -- The second coordinate, from `𝐂 t`: given by the integrals up to `π/2 - φ`, then constant.
    split_ifs with ht
    · rw [contactC_integral_coordinates hD, horizontal_normalization hD] at hC
      simp only [dot, vvec] at hC ⊢
      linarith
    · rw [contactC_last hD (not_le.mp ht).le, horizontal_normalization hD] at hC
      simp only [dot, vvec] at hC ⊢
      linarith

/-- Rotating formal-conjectures' path by `t` gives Romik's path. -/
theorem rotated_prePath {D : GerverConstants} (hD : D.Valid) (t : ℝ) :
    rot t (D.prePath t) = D.toRomik.path t := by
  rw [prePath_eq_projections hD, rot_frame_coords]

/-- Formal-conjectures' path starts at `0`. -/
theorem prePath_zero_of_valid {D : GerverConstants} (hD : D.Valid) : D.prePath 0 = 0 := by
  have h := rotated_prePath hD 0
  rwa [rot_zero, gs_path_zero (romik_solution hD).1] at h

/-- The sofa of Gerver's constants is the sofa of the corresponding Romik parameters. -/
theorem shape_eq_gerverSofa {D : GerverConstants} (hD : D.Valid) :
    D.shape = gerverSofa D.toRomik :=
  shape_eq_of_rotated_path (prePath_zero_of_valid hD) fun t _ => rotated_prePath hD t

/-- The sofa of a solution of Gerver's system is the sofa of every solution of Romik's system in
the box. -/
theorem shape_eq_gerverSofa_of_isSolution {D : GerverConstants} (hD : D.Valid) {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) : D.shape = gerverSofa P := by
  rw [shape_eq_gerverSofa hD, eq_ofRomik hD hP hbox, ofRomik_toRomik hP]

end MovingSofaBridge.GerverConstants

namespace MovingSofaBridge

open FormalConjectures

/-! ## Formal-conjectures' rotation in coordinates -/

/-- Formal-conjectures' `rotateTranslate α p` translates by `p`, then rotates by `α`. -/
theorem rotateTranslate_apply (α : Real.Angle) (p q : Point) :
    MovingSofa.rotateTranslate α p q = EuclideanGeometry.o.rotation α (q + p) := rfl

private def stdBasis : OrthonormalBasis (Fin 2) ℝ Point :=
  EuclideanSpace.basisFun (Fin 2) ℝ

private theorem stdBasis_orientation :
    stdBasis.toBasis.orientation = EuclideanGeometry.o := by
  rfl

private theorem stdBasis_areaForm :
    EuclideanGeometry.o.areaForm (stdBasis 0) (stdBasis 1) = 1 := by
  rw [Orientation.areaForm_to_volumeForm,
    Orientation.volumeForm_robust _ stdBasis stdBasis_orientation]
  have he : ![stdBasis 0, stdBasis 1] = (stdBasis : Fin 2 → Point) := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact stdBasis.toBasis.det_self

private theorem rightAngleRotation_stdBasis_zero :
    EuclideanGeometry.o.rightAngleRotation (stdBasis 0) = stdBasis 1 := by
  apply PiLp.ext
  intro i
  fin_cases i
  · have h := EuclideanGeometry.o.inner_rightAngleRotation_self (stdBasis 0)
    change inner ℝ (EuclideanGeometry.o.rightAngleRotation (stdBasis 0))
      (EuclideanSpace.basisFun (Fin 2) ℝ 0) = 0 at h
    rw [EuclideanSpace.inner_basisFun_real] at h
    simpa [stdBasis, EuclideanSpace.basisFun_apply] using h
  · have h := EuclideanGeometry.o.inner_rightAngleRotation_left
      (stdBasis 0) (stdBasis 1)
    rw [stdBasis_areaForm] at h
    change inner ℝ (EuclideanGeometry.o.rightAngleRotation (stdBasis 0))
      (EuclideanSpace.basisFun (Fin 2) ℝ 1) = 1 at h
    rw [EuclideanSpace.inner_basisFun_real] at h
    simpa [stdBasis, EuclideanSpace.basisFun_apply] using h

private theorem rightAngleRotation_stdBasis_one :
    EuclideanGeometry.o.rightAngleRotation (stdBasis 1) = -stdBasis 0 := by
  have h := EuclideanGeometry.o.rightAngleRotation_rightAngleRotation (stdBasis 0)
  rwa [rightAngleRotation_stdBasis_zero] at h

private theorem stdBasis_expansion (q : Point) :
    q = q 0 • stdBasis 0 + q 1 • stdBasis 1 := by
  ext i
  fin_cases i <;> simp [stdBasis, EuclideanSpace.basisFun_apply]

/-- The right-angle rotation of the standard orientation of `ℝ²`, in coordinates. -/
theorem rightAngleRotation_coordinates (q : Point) :
    coordinates (EuclideanGeometry.o.rightAngleRotation q) = (-(q 1), q 0) := by
  conv_lhs => rw [stdBasis_expansion q]
  rw [map_add, map_smul, map_smul, rightAngleRotation_stdBasis_zero,
    rightAngleRotation_stdBasis_one]
  ext <;> simp [coordinates, stdBasis, EuclideanSpace.basisFun_apply]

/-- The rotations of the standard orientation of `ℝ²` are the rotations of coordinates. -/
theorem rotation_coordinates (t : ℝ) (q : Point) :
    coordinates (EuclideanGeometry.o.rotation (t : Real.Angle) q) =
      MovingSofaOptimality.rot t (coordinates q) := by
  rw [Orientation.rotation_apply, coordinates_add, coordinates_smul, coordinates_smul,
    rightAngleRotation_coordinates]
  ext <;> simp [MovingSofaOptimality.rot, coordinates] <;> ring

/-- Formal-conjectures' `rotateTranslate`, in coordinates. -/
theorem rotateTranslate_coordinates (t : ℝ) (p q : Point) :
    coordinates (MovingSofa.rotateTranslate (t : Real.Angle) p q) =
      MovingSofaOptimality.rot t (coordinates q + coordinates p) := by
  rw [rotateTranslate_apply, rotation_coordinates, coordinates_add]

/-! ## The two Gerver's sofas agree -/

/-- The constants chosen by formal-conjectures. -/
def gerverConstants : GerverConstants :=
  ⟨MovingSofa.GerversSofa.A, MovingSofa.GerversSofa.B, MovingSofa.GerversSofa.φ,
    MovingSofa.GerversSofa.θ⟩

/-- The constants chosen by formal-conjectures solve Gerver's system. -/
theorem gerverConstants_valid : gerverConstants.Valid :=
  MovingSofa.GerversSofa.ABφθSpec.existsUnique.choose_spec.1

/-- Formal-conjectures' path `p`, in coordinates. -/
theorem coordinates_p (t : ℝ) :
    coordinates (MovingSofa.GerversSofa.p t) = gerverConstants.prePath t := rfl

/-- Membership in a hallway moved by `rotateTranslate`, in coordinates. -/
private theorem mem_rotateTranslate_image_iff (t : ℝ) (q : Point)
    (A : Set Point) (B : Set CoordinatePlane)
    (hAB : ∀ p, coordinates p ∈ B ↔ p ∈ A) :
    q ∈ MovingSofa.rotateTranslate (t : Real.Angle) (MovingSofa.GerversSofa.p t) '' A ↔
      coordinates q ∈ GerverConstants.rotateTranslatePair t
        (gerverConstants.prePath t) '' B := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨coordinates p, (hAB p).mpr hp, ?_⟩
    rw [rotateTranslate_coordinates, coordinates_p]
    rfl
  · rintro ⟨p, hp, heq⟩
    refine ⟨point p, (hAB (point p)).mp (by simpa using hp), ?_⟩
    apply coordinates_injective
    rw [rotateTranslate_coordinates, coordinates_p, coordinates_point]
    exact heq

/-- Membership in formal-conjectures' Gerver's sofa, in coordinates. -/
theorem mem_gerversSofa_iff (q : Point) :
    q ∈ MovingSofa.gerversSofa ↔ coordinates q ∈ gerverConstants.shape := by
  have hH := mem_rotateTranslate_image_iff 0 q MovingSofa.horizontalHallway
    MovingSofaOptimality.horizSide coordinates_mem_horizontal
  have hV := mem_rotateTranslate_image_iff (π / 2) q MovingSofa.verticalHallway
    MovingSofaOptimality.vertSide coordinates_mem_vertical
  have hL := fun t => mem_rotateTranslate_image_iff t q MovingSofa.hallway
    MovingSofaOptimality.hallway coordinates_mem_hallway
  simp only [MovingSofa.gerversSofa, MovingSofa.sofaOfRotateTranslatePath,
    GerverConstants.shape, GerverConstants.shapeFromPrePath, mem_inter_iff, mem_iInter]
  constructor
  · rintro ⟨⟨hh, hv⟩, hall⟩
    exact ⟨⟨hH.mp hh, hV.mp hv⟩, fun t ht => (hL t).mp (hall t ht)⟩
  · rintro ⟨⟨hh, hv⟩, hall⟩
    exact ⟨⟨hH.mpr hh, hV.mpr hv⟩, fun t ht => (hL t).mpr (hall t ht)⟩

/-- In coordinates, formal-conjectures' Gerver's sofa is the sofa of Gerver's constants. -/
theorem coordinates_gerversSofa :
    coordinates '' MovingSofa.gerversSofa = gerverConstants.shape := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (mem_gerversSofa_iff p).mp hp
  · intro hq
    exact ⟨point q, (mem_gerversSofa_iff (point q)).mpr (by simpa using hq), coordinates_point q⟩

/-- **The two Gerver's sofas agree.** In coordinates, formal-conjectures' Gerver's sofa is the
Gerver's sofa of every solution of Romik's system in the box. -/
theorem gerversSofa_eq {P : MovingSofaOptimality.GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    coordinates '' MovingSofa.gerversSofa = MovingSofaOptimality.gerverSofa P := by
  rw [coordinates_gerversSofa]
  exact GerverConstants.shape_eq_gerverSofa_of_isSolution gerverConstants_valid hP hbox

end MovingSofaBridge
