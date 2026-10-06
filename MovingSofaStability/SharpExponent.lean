module

public import MovingSofaStability.PuncturedSofa
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Sharpness of the unrestricted Hausdorff exponent

Uncompiled proof source. For every exponent greater than one half, every
constant, and every positive entry threshold, a punctured Gerver sofa violates
the proposed estimate for EVERY orientation-preserving rigid alignment.
This is not a sharpness claim for the cap constant or symmetric-difference area.
-/

@[expose] public section
noncomputable section

open Real Set Metric Filter Topology MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- The power-law identity used to compare r with C*(pi*r^2)^a. -/
theorem puncture_power_identity {r : ℝ} (hr : 0 < r) (a C : ℝ) :
    C * (π * r ^ 2) ^ a = (C * π ^ a * r ^ (2 * a - 1)) * r := by
  have hsquare : (r ^ 2) ^ a = r ^ (2 * a) := by
    rw [← rpow_natCast r 2]
    exact (rpow_mul hr.le (2 : ℝ) a).symm
  have hjoin : r ^ (2 * a - 1) * r = r ^ (2 * a) := by
    calc
      _ = r ^ (2 * a - 1) * r ^ (1 : ℝ) := by rw [rpow_one]
      _ = r ^ ((2 * a - 1) + 1) := (rpow_add hr _ _).symm
      _ = _ := by congr 1; ring
  calc
    C * (π * r ^ 2) ^ a = C * π ^ a * r ^ (2 * a) := by
      rw [mul_rpow pi_pos.le (sq_nonneg r), hsquare]
      ring
    _ = (C * π ^ a * r ^ (2 * a - 1)) * r := by
      rw [← hjoin]
      ring

/-- Arbitrarily small positive radii violate every exponent above one half. -/
theorem exists_puncture_scale {a C ε₀ r₀ : ℝ} (ha : 1 / 2 < a)
    (hε₀ : 0 < ε₀) (hr₀ : 0 < r₀) :
    ∃ r : ℝ, 0 < r ∧ r < r₀ ∧ π * r ^ 2 < ε₀ ∧ C * (π * r ^ 2) ^ a < r := by
  have hq : 0 < 2 * a - 1 := by linarith
  have harea : {r : ℝ | π * r ^ 2 < ε₀} ∈ 𝓝 (0 : ℝ) := by
    apply (isOpen_lt (by fun_prop) continuous_const).mem_nhds
    simpa using hε₀
  have hpow : {r : ℝ | C * π ^ a * r ^ (2 * a - 1) < 1} ∈ 𝓝 (0 : ℝ) := by
    have hc : Continuous (fun r : ℝ => C * π ^ a * r ^ (2 * a - 1)) :=
      continuous_const.mul (continuous_rpow_const hq.le)
    apply (isOpen_lt hc continuous_const).mem_nhds
    simp [zero_rpow hq.ne']
  obtain ⟨η, hη, hηset⟩ := Metric.mem_nhds_iff.1 (inter_mem harea hpow)
  let r := min r₀ η / 2
  have hr : 0 < r := div_pos (lt_min hr₀ hη) (by norm_num)
  have hrsmall : r < min r₀ η := by dsimp [r]; linarith [lt_min hr₀ hη]
  have hrη := hrsmall.trans_le (min_le_right r₀ η)
  have hmem : r ∈ ball (0 : ℝ) η := by
    simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hr] using hrη
  obtain ⟨hA, hP⟩ := hηset hmem
  refine ⟨r, hr, hrsmall.trans_le (min_le_left _ _), hA, ?_⟩
  rw [puncture_power_identity hr]
  simpa only [one_mul] using mul_lt_mul_of_pos_right hP hr

/-- No exponent greater than one half can control all near-optimal moving sofas.
The quantifiers include every proposed C, every threshold, and every alignment. -/
theorem no_hausdorff_exponent_gt_half {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {a : ℝ} (ha : 1 / 2 < a)
    (C : ℝ) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ S : Set Point, IsMovingSofa S ∧ 0 < sofaDeficit P S ∧ sofaDeficit P S < ε₀ ∧
      ∀ g : Rigid, ¬EuclideanClose (C * (sofaDeficit P S) ^ a) S (g '' gerverSofa P) := by
  obtain ⟨p, r₀, hr₀, hfamily⟩ := punctured_gerver_family hP hbox
  obtain ⟨r, hr, hrsmall, harea, hpower⟩ := exists_puncture_scale (C := C) ha hε₀ hr₀
  obtain ⟨hmove, hdef, _, hminimal, _⟩ := hfamily r hr hrsmall
  refine ⟨puncture (gerverSofa P) p r, hmove, ?_, ?_, ?_⟩
  · rw [hdef]
    positivity
  · rwa [hdef]
  · intro g hclose
    rw [hdef] at hclose
    exact (not_lt_of_ge (hminimal g _ hclose)) hpower

/-- The same obstruction using the actual infimum over rigid alignments. -/
theorem rigid_distance_not_higher_order {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {a : ℝ} (ha : 1 / 2 < a)
    (C : ℝ) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ S : Set Point, IsMovingSofa S ∧ 0 < sofaDeficit P S ∧ sofaDeficit P S < ε₀ ∧
      C * (sofaDeficit P S) ^ a < rigidHausdorffDistance S (gerverSofa P) := by
  obtain ⟨p, r₀, hr₀, hfamily⟩ := punctured_gerver_family hP hbox
  obtain ⟨r, hr, hrsmall, harea, hpower⟩ := exists_puncture_scale (C := C) ha hε₀ hr₀
  obtain ⟨hmove, hdef, _, _, hdist⟩ := hfamily r hr hrsmall
  refine ⟨puncture (gerverSofa P) p r, hmove, ?_, ?_, ?_⟩
  · rw [hdef]
    positivity
  · rwa [hdef]
  · rwa [hdef, hdist]

end MovingSofaStability
