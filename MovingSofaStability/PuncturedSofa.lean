module

public import MovingSofaStability.RigidInterior
public import MovingSofaStability.Statement

/-!
# A punctured Gerver family, including optimization over rigid alignment

Uncompiled proof source. The family has area loss pi*r^2 and distance exactly r
from the entire orientation-preserving rigid orbit of Gerver. The conclusion
concerns the actual closed sets, not the Hausdorff distance of their boundaries.
-/

@[expose] public section
noncomputable section

open Real Set Metric MeasureTheory Topology
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- For a sufficiently small interior puncture, no rigid alignment improves r. -/
theorem small_puncture_rigid_minimum {X : Set Point} (hX : IsCompact X)
    {p : Point} (hp : p ∈ interior X) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      euclideanBall p r ⊆ X ∧ EuclideanClose r (puncture X p r) X ∧
      (∀ g : Rigid, ∀ d : ℝ, EuclideanClose d (puncture X p r) (g '' X) → r ≤ d) ∧
      rigidHausdorffDistance (puncture X p r) X = r := by
  obtain ⟨R, hR, hRball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hp)
  obtain ⟨η, hη, hret⟩ := rigid_copies_retain_interior hX hp
  let r₀ := min (R / 2) (η / 3)
  have hr₀ : 0 < r₀ := lt_min (by positivity) (by positivity)
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr hrsmall
  have hrR : r < R / 2 := hrsmall.trans_le (min_le_left _ _)
  have hrη : r < η / 3 := hrsmall.trans_le (min_le_right _ _)
  have hball : euclideanBall p r ⊆ X := by
    intro q hq
    apply hRball
    change dist q p < R
    have hprod : dist q p ≤ euclideanDist p q := by
      rw [dist_comm, dist_eq_norm]
      exact product_norm_le_norm2 _
    exact (hprod.trans hq).trans_lt (by linarith)
  have hatt := puncture_euclideanClose hr hball
  have hmin : ∀ g : Rigid, ∀ d : ℝ,
      EuclideanClose d (puncture X p r) (g '' X) → r ≤ d := by
    intro g d hd
    by_contra hnot
    have hdr : d < r := not_le.mp hnot
    have hjoined : EuclideanClose (r + d) X (g '' X) := hatt.symm.trans hd
    have hp' := hret g (r + d) (by linarith) hjoined
    exact (not_lt_of_ge (puncture_radius_le_of_center_mem hp' hd)) hdr
  refine ⟨hball, hatt, hmin, ?_⟩
  apply rigidHausdorffDistance_eq_of_attained hr.le _ hmin
  refine ⟨Rigid.translate 0, ?_⟩
  simpa only [Rigid.coe_translate, add_zero, image_id'] using hatt

/-- The explicit family witnesses the scale sqrt(area deficit), without any
regularity assumption on the new sofas and without fixing the alignment. -/
theorem punctured_gerver_family {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ p : Point, ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      IsMovingSofa (puncture (gerverSofa P) p r) ∧
      sofaDeficit P (puncture (gerverSofa P) p r) = π * r ^ 2 ∧
      EuclideanClose r (puncture (gerverSofa P) p r) (gerverSofa P) ∧
      (∀ g : Rigid, ∀ d : ℝ,
        EuclideanClose d (puncture (gerverSofa P) p r) (g '' gerverSofa P) → r ≤ d) ∧
      rigidHausdorffDistance (puncture (gerverSofa P) p r) (gerverSofa P) = r := by
  have hGangle := (GerverParams.gm_movingSofa_std hP hbox).1
  have hG : IsMovingSofa (gerverSofa P) := ⟨π / 2, hGangle⟩
  have hGc := isCompact_of_isMovingSofa hG
  have hInt : (interior (gerverSofa P)).Nonempty := by
    apply closure_nonempty_iff.mp
    rw [gerver_regularClosed hP hbox]
    exact hGangle.2.1.nonempty
  obtain ⟨p, hp⟩ := hInt
  obtain ⟨r₀, hr₀, hmin⟩ := small_puncture_rigid_minimum hGc hp
  refine ⟨p, r₀, hr₀, ?_⟩
  intro r hr hrsmall
  obtain ⟨hball, hclose, hlower, heq⟩ := hmin r hr hrsmall
  exact ⟨puncture_moving hG hr hball, puncture_area_loss hGc hr.le hball,
    hclose, hlower, heq⟩

end MovingSofaStability
