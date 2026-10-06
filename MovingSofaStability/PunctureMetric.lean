module

public import MovingSofaStability.EuclideanDisks

/-!
# Puncture distance and inherited motion

Uncompiled proof source. The identity alignment attains distance r. The lower
bound applies against any comparison set containing the removed center; the
rigid-orbit lemma supplies that hypothesis for close rigid copies later.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- A point in a closed disk is within r of its retained boundary circle. -/
theorem exists_sphere_point_near (p : Point) {r : ℝ} (hr : 0 < r)
    {x : Point} (hx : euclideanDist p x ≤ r) :
    ∃ q ∈ euclideanSphere p r, euclideanDist x q ≤ r := by
  sorry

/-- The original set and its puncture have Euclidean Hausdorff distance at most r. -/
theorem puncture_euclideanClose {S : Set Point} {p : Point} {r : ℝ}
    (hr : 0 < r) (hball : euclideanBall p r ⊆ S) :
    EuclideanClose r (puncture S p r) S := by
  constructor
  · intro x hx
    exact ⟨x, hx.1, by simpa using hr.le⟩
  · intro x hx
    by_cases hin : x ∈ openEuclideanBall p r
    · obtain ⟨q, hq, hd⟩ := exists_sphere_point_near p hr hin.le
      refine ⟨q, ⟨hball hq.le, ?_⟩, hd⟩
      intro hlt
      exact (show euclideanDist p q < r from hlt).ne hq
    · exact ⟨x, ⟨hx, hin⟩, by simpa using hr.le⟩

/-- A comparison set that contains the removed center is at distance at least r. -/
theorem puncture_radius_le_of_center_mem {S T : Set Point} {p : Point} {r d : ℝ}
    (hp : p ∈ T) (hclose : EuclideanClose d (puncture S p r) T) : r ≤ d := by
  obtain ⟨q, hq, hd⟩ := hclose.2 p hp
  have hlower : r ≤ euclideanDist p q := not_lt.mp hq.2
  exact hlower.trans hd

/-- Equality of the identity-aligned Hausdorff radius, in the actual-set API. -/
theorem puncture_exact_radius {S : Set Point} {p : Point} {r : ℝ}
    (hr : 0 < r) (hball : euclideanBall p r ⊆ S) :
    EuclideanClose r (puncture S p r) S ∧
      ∀ d, EuclideanClose d (puncture S p r) S → r ≤ d := by
  have hp : p ∈ S := hball (by simpa only [euclideanBall, mem_setOf_eq, euclideanDist_self] using hr.le)
  exact ⟨puncture_euclideanClose hr hball, fun _ h => puncture_radius_le_of_center_mem hp h⟩

/-- A closed connected subset inherits precisely the same movement. -/
theorem moving_subset_of_closed_connected {S T : Set Point} {ω : ℝ}
    (hT : IsMovingSofaWithAngle T ω) (hST : S ⊆ T)
    (hSclosed : IsClosed S) (hSconnected : IsConnected S) :
    IsMovingSofaWithAngle S ω := by
  obtain ⟨_, _, θ, c, hm⟩ := hT
  refine ⟨hSclosed, hSconnected, θ, c,
    hm.continuousOn_angle, hm.continuousOn_shift, hm.angle_zero, hm.angle_one,
    ?_, ?_, ?_⟩
  · intro p hp
    exact hm.start p (hST hp)
  · intro t ht p hp
    exact hm.inside t ht p (hST hp)
  · intro p hp
    exact hm.finish p (hST hp)

/-- The puncture is an original moving sofa, not merely an area perturbation. -/
theorem puncture_movingWithAngle {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) {p : Point} {r : ℝ} (hr : 0 < r)
    (hball : euclideanBall p r ⊆ S) : IsMovingSofaWithAngle (puncture S p r) ω := by
  sorry

theorem puncture_moving {S : Set Point} (hS : IsMovingSofa S)
    {p : Point} {r : ℝ} (hr : 0 < r) (hball : euclideanBall p r ⊆ S) :
    IsMovingSofa (puncture S p r) := by
  obtain ⟨ω, hω⟩ := hS
  exact ⟨ω, puncture_movingWithAngle hω hr hball⟩

/-- Infimum of Euclidean Hausdorff radii over orientation-preserving rigid maps.
For nonempty compact sets this is the usual distance modulo rigid alignment. -/
def rigidHausdorffDistance (S T : Set Point) : ℝ :=
  sInf {d : ℝ | 0 ≤ d ∧ ∃ g : Rigid, EuclideanClose d S (g '' T)}

/-- A radius that is attained and bounds every rigid alignment is the infimum. -/
theorem rigidHausdorffDistance_eq_of_attained {S T : Set Point} {r : ℝ} (hr : 0 ≤ r)
    (hatt : ∃ g : Rigid, EuclideanClose r S (g '' T))
    (hmin : ∀ g : Rigid, ∀ d : ℝ, EuclideanClose d S (g '' T) → r ≤ d) :
    rigidHausdorffDistance S T = r := by
  have hne : {d : ℝ | 0 ≤ d ∧ ∃ g : Rigid, EuclideanClose d S (g '' T)}.Nonempty :=
    ⟨r, hr, hatt⟩
  apply le_antisymm
  · exact csInf_le ⟨0, fun d hd => hd.1⟩ ⟨hr, hatt⟩
  · apply le_csInf hne
    rintro d ⟨_, g, hg⟩
    exact hmin g d hg

end MovingSofaStability
