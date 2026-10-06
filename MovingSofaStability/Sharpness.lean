module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Connected.Clopen
public import MovingSofaBridge.Motion
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import MovingSofaStability.Basic
public import MovingSofaStability.Margins

/-!
# Punctured sofas: the exponent one half is optimal

Removing a small open disk of radius `r` from the interior of Gerver's sofa leaves a moving sofa that has
lost area `π r²` and lies at distance at least `r` from every rigid copy of Gerver's sofa
(`punctured_gerver_family`), so no rate `C εᵃ` with `a > 1/2` holds (`no_hausdorff_exponent_gt_half`).

The sections below follow the steps of the proof.
-/

@[expose] public section
noncomputable section

/-!
## Removing an interior disk from a connected set

No path connectedness of the original set is assumed. The boundary of the
removed open set connects every possible separation of the remainder. In
dimension two this applies to an interior disk because its circle is connected.
This avoids assuming that a general closed moving sofa has paths between all of
its points.
-/

section PunctureTopology

open Set Metric

namespace MovingSofaStability

/-- An open region with connected boundary can be removed from a closed
connected set containing its closure without disconnecting the remainder. -/
theorem preconnected_sdiff_of_connected_frontier {X : Type*} [TopologicalSpace X]
    {S U : Set X} (hS : IsClosed S) (hconn : IsPreconnected S)
    (hU : IsOpen U) (hcl : closure U ⊆ S) (hF : IsPreconnected (frontier U)) :
    IsPreconnected (S \ U) := by
  let Y := S \ U
  have hY : IsClosed Y := hS.sdiff hU
  have hFY : frontier U ⊆ Y := by
    intro x hx
    refine ⟨hcl (frontier_subset_closure hx), ?_⟩
    have hx' : x ∉ interior U := hx.2
    simpa only [hU.interior_eq] using hx'
  apply isPreconnected_iff_subset_of_disjoint_closed.mpr
  intro A B hA hB hcover hdisj
  have hFC : frontier U ⊆ A ∪ B := hFY.trans hcover
  have hFD : frontier U ∩ (A ∩ B) = ∅ := by
    apply subset_empty_iff.mp
    intro x hx
    have hy : x ∈ Y ∩ (A ∩ B) := ⟨hFY hx.1, hx.2⟩
    exact hdisj.subset hy
  have step (A B : Set X) (hA : IsClosed A) (hB : IsClosed B)
      (hcover : Y ⊆ A ∪ B) (hdisj : Y ∩ (A ∩ B) = ∅)
      (hFA : frontier U ⊆ A) : Y ⊆ A ∨ Y ⊆ B := by
    let A' := (Y ∩ A) ∪ closure U
    let B' := Y ∩ B
    have hA' : IsClosed A' := (hY.inter hA).union isClosed_closure
    have hB' : IsClosed B' := hY.inter hB
    have hcov' : S ⊆ A' ∪ B' := by
      intro x hx
      by_cases hxU : x ∈ U
      · exact Or.inl (Or.inr (subset_closure hxU))
      · rcases hcover ⟨hx, hxU⟩ with ha | hb
        · exact Or.inl (Or.inl ⟨⟨hx, hxU⟩, ha⟩)
        · exact Or.inr ⟨⟨hx, hxU⟩, hb⟩
    have hdisj' : S ∩ (A' ∩ B') = ∅ := by
      apply subset_empty_iff.mp
      rintro x ⟨hxS, hxA | hxcl, hxY, hxB⟩
      · have hx : x ∈ Y ∩ (A ∩ B) := ⟨hxA.1, hxA.2, hxB⟩
        exact hdisj.subset hx
      · have hxf : x ∈ frontier U := by
          refine ⟨hxcl, ?_⟩
          simpa only [hU.interior_eq] using hxY.2
        have hx : x ∈ Y ∩ (A ∩ B) := ⟨hxY, hFA hxf, hxB⟩
        exact hdisj.subset hx
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn A' B' hA' hB' hcov' hdisj' with
      h | h
    · left
      intro x hx
      rcases h hx.1 with ha | hclx
      · exact ha.2
      · apply hFA
        refine ⟨hclx, ?_⟩
        simpa only [hU.interior_eq] using hx.2
    · exact Or.inr (fun x hx => (h hx.1).2)
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hF A B hA hB hFC hFD with hFA | hFB
  · exact step A B hA hB hcover hdisj hFA
  · have hcover' : Y ⊆ B ∪ A := by simpa only [union_comm] using hcover
    have hdisj' : Y ∩ (B ∩ A) = ∅ := by simpa only [inter_comm A B] using hdisj
    exact (step B A hB hA hcover' hdisj' hFB).symm

/-- Removing a disk contained in a closed connected set preserves connectedness
in any nontrivial real normed space of dimension at least two. -/
theorem connected_sdiff_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] (hdim : 1 < Module.rank ℝ E) {S : Set E} (hS : IsClosed S)
    (hconn : IsConnected S) {p : E} {r : ℝ} (hr : 0 < r)
    (hball : closedBall p r ⊆ S) : IsConnected (S \ ball p r) := by
  have hcircle := isConnected_sphere hdim p hr.le
  have hcircleSub : sphere p r ⊆ S \ ball p r := by
    intro q hq
    have he := mem_sphere.mp hq
    exact ⟨hball (mem_closedBall.mpr he.le), fun h => (mem_ball.mp h).ne he⟩
  refine ⟨hcircle.nonempty.mono hcircleSub, ?_⟩
  apply preconnected_sdiff_of_connected_frontier hS hconn.isPreconnected isOpen_ball
  · simpa only [closure_ball p hr.ne'] using hball
  · simpa only [frontier_ball p hr.ne'] using hcircle.isPreconnected

end MovingSofaStability

end PunctureTopology

/-!
## Euclidean disks in the repository's product coordinates

The product metric is not used for disk radii or areas. The existing
measure-preserving coordinate bridge supplies the exact Euclidean disk area,
while a homeomorphism transports connectedness.
-/

section EuclideanDisks

open Real Set MeasureTheory Metric
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

abbrev EuclideanPoint := EuclideanSpace ℝ (Fin 2)

/-- The existing coordinate equivalence, equipped with its proved topology. -/
def diskCoordinates : EuclideanPoint ≃ₜ Point where
  toFun := MovingSofaBridge.coordinates
  invFun := MovingSofaBridge.point
  left_inv := MovingSofaBridge.point_coordinates
  right_inv := MovingSofaBridge.coordinates_point
  continuous_toFun := MovingSofaBridge.coordinates_continuous
  continuous_invFun := MovingSofaBridge.point_continuous

@[simp] theorem euclideanDist_coordinates (p q : EuclideanPoint) :
    euclideanDist (diskCoordinates p) (diskCoordinates q) = dist p q := by
  rw [euclideanDist, dist_eq_norm]
  apply (sq_eq_sq₀ (norm2_nonneg _) (norm_nonneg _)).mp
  rw [norm2_sq, MovingSofaBridge.norm_sq_coordinates]
  change dot (MovingSofaBridge.coordinates p - MovingSofaBridge.coordinates q)
    (MovingSofaBridge.coordinates p - MovingSofaBridge.coordinates q) = _
  simp only [MovingSofaBridge.coordinates, dot, Prod.fst_sub, Prod.snd_sub, PiLp.sub_apply]
  ring

@[simp] theorem dist_inverse_coordinates (p q : Point) :
    dist (diskCoordinates.symm p) (diskCoordinates.symm q) = euclideanDist p q := by
  rw [← euclideanDist_coordinates]
  simp

/-- An open Euclidean disk; `euclideanBall` in the recovery files is closed. -/
def openEuclideanBall (p : Point) (r : ℝ) : Set Point :=
  {q | euclideanDist p q < r}

def euclideanSphere (p : Point) (r : ℝ) : Set Point :=
  {q | euclideanDist p q = r}

/-- The punctured set retains the circle. -/
def puncture (S : Set Point) (p : Point) (r : ℝ) : Set Point :=
  S \ openEuclideanBall p r

@[simp] theorem coordinates_image_ball (p : Point) (r : ℝ) :
    diskCoordinates '' ball (diskCoordinates.symm p) r = openEuclideanBall p r := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    change euclideanDist p (diskCoordinates x) < r
    rw [← diskCoordinates.apply_symm_apply p, euclideanDist_coordinates, dist_comm]
    exact hx
  · intro hq
    refine ⟨diskCoordinates.symm q, ?_, by simp⟩
    change dist (diskCoordinates.symm q) (diskCoordinates.symm p) < r
    rw [dist_inverse_coordinates, euclideanDist_comm]
    exact hq

@[simp] theorem coordinates_image_closedBall (p : Point) (r : ℝ) :
    diskCoordinates '' closedBall (diskCoordinates.symm p) r = euclideanBall p r := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    change euclideanDist p (diskCoordinates x) ≤ r
    rw [← diskCoordinates.apply_symm_apply p, euclideanDist_coordinates, dist_comm]
    exact hx
  · intro hq
    refine ⟨diskCoordinates.symm q, ?_, by simp⟩
    change dist (diskCoordinates.symm q) (diskCoordinates.symm p) ≤ r
    rw [dist_inverse_coordinates, euclideanDist_comm]
    exact hq

@[simp] theorem coordinates_image_sphere (p : Point) (r : ℝ) :
    diskCoordinates '' sphere (diskCoordinates.symm p) r = euclideanSphere p r := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    change euclideanDist p (diskCoordinates x) = r
    rw [← diskCoordinates.apply_symm_apply p, euclideanDist_coordinates, dist_comm]
    exact hx
  · intro hq
    refine ⟨diskCoordinates.symm q, ?_, by simp⟩
    change dist (diskCoordinates.symm q) (diskCoordinates.symm p) = r
    rw [dist_inverse_coordinates, euclideanDist_comm]
    exact hq

theorem openEuclideanBall_isOpen (p : Point) (r : ℝ) : IsOpen (openEuclideanBall p r) := by
  rw [← coordinates_image_ball]
  exact diskCoordinates.isOpenMap _ isOpen_ball

/-- Exact area, with no sup-norm disk substitution. -/
theorem area_openEuclideanBall (p : Point) {r : ℝ} (hr : 0 ≤ r) :
    area (openEuclideanBall p r) = π * r ^ 2 := by
  rw [← coordinates_image_ball]
  change (volume (MovingSofaBridge.coordinates '' ball (diskCoordinates.symm p) r)).toReal = _
  rw [MovingSofaBridge.volume_coordinates_image, EuclideanSpace.volume_ball_fin_two,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal pi_pos.le]
  ring

theorem euclideanSphere_connected (p : Point) {r : ℝ} (hr : 0 ≤ r) :
    IsConnected (euclideanSphere p r) := by
  rw [← coordinates_image_sphere]
  exact (isConnected_sphere
    (Module.one_lt_rank_of_one_lt_finrank (by simp) : 1 < Module.rank ℝ EuclideanPoint)
    (diskCoordinates.symm p) hr).image _ diskCoordinates.continuous.continuousOn

/-- This uses connectedness, not a stronger unproved path-connectedness hypothesis. -/
theorem puncture_connected {S : Set Point} (hS : IsClosed S) (hconn : IsConnected S)
    {p : Point} {r : ℝ} (hr : 0 < r) (hball : euclideanBall p r ⊆ S) :
    IsConnected (puncture S p r) := by
  let T := diskCoordinates.symm '' S
  have hTclosed : IsClosed T := diskCoordinates.symm.isClosedMap _ hS
  have hTconn : IsConnected T := hconn.image _ diskCoordinates.symm.continuous.continuousOn
  have hTball : closedBall (diskCoordinates.symm p) r ⊆ T := by
    intro q hq
    have hq' : diskCoordinates q ∈ euclideanBall p r := by
      rw [← coordinates_image_closedBall]
      exact mem_image_of_mem _ hq
    exact ⟨diskCoordinates q, hball hq', by simp⟩
  have h := connected_sdiff_ball
    (Module.one_lt_rank_of_one_lt_finrank (by simp) : 1 < Module.rank ℝ EuclideanPoint)
    hTclosed hTconn hr hTball
  have he : diskCoordinates '' (T \ ball (diskCoordinates.symm p) r) = puncture S p r := by
    rw [image_sdiff diskCoordinates.injective, coordinates_image_ball]
    simp only [T, image_image, Homeomorph.apply_symm_apply, image_id', puncture]
  rw [← he]
  exact h.image _ diskCoordinates.continuous.continuousOn

/-- The missing area is exactly the disk area. All measures involved are finite. -/
theorem puncture_area_loss {S : Set Point} (hS : IsCompact S)
    {p : Point} {r : ℝ} (hr : 0 ≤ r) (hball : euclideanBall p r ⊆ S) :
    area S - area (puncture S p r) = π * r ^ 2 := by
  have hsub : openEuclideanBall p r ⊆ S := fun q hq =>
    hball (show euclideanDist p q ≤ r from (show euclideanDist p q < r from hq).le)
  have hi : S ∩ openEuclideanBall p r = openEuclideanBall p r := inter_eq_right.mpr hsub
  have hpart := area_inter_add_sdiff (openEuclideanBall_isOpen p r).measurableSet
    hS.isBounded.measure_lt_top.ne
  rw [hi, area_openEuclideanBall p hr] at hpart
  change area S - area (S \ openEuclideanBall p r) = _
  linarith

end MovingSofaStability

end EuclideanDisks

/-!
## Puncture distance and inherited motion

The identity alignment attains distance r. The lower bound applies against any
comparison set containing the removed center; the rigid-orbit lemma supplies
that hypothesis for close rigid copies later.
-/

section PunctureMetric

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- A point in a closed disk is within r of its retained boundary circle. -/
theorem exists_sphere_point_near (p : Point) {r : ℝ} (hr : 0 < r)
    {x : Point} (hx : euclideanDist p x ≤ r) :
    ∃ q ∈ euclideanSphere p r, euclideanDist x q ≤ r := by
  by_cases hxp : x = p
  · obtain ⟨q, hq⟩ := (euclideanSphere_connected p hr.le).nonempty
    exact ⟨q, hq, by simpa only [hxp] using hq.le⟩
  let u := x - p
  let n := norm2 u
  have hn : 0 < n := by
    have hne : euclideanDist x p ≠ 0 := by
      simpa only [ne_eq, euclideanDist_eq_zero_iff] using hxp
    exact lt_of_le_of_ne (norm2_nonneg u) (Ne.symm hne)
  have hnr : n ≤ r := by
    simpa only [n, u, euclideanDist, show x - p = -(p - x) by abel, norm2_neg] using hx
  let a := r / n
  let q := p + a • u
  have ha : 0 < a := div_pos hr hn
  have han : a * n = r := div_mul_cancel₀ _ hn.ne'
  have ha1 : 1 ≤ a := (le_div_iff₀ hn).2 (by simpa using hnr)
  have hpq : euclideanDist p q = r := by
    change norm2 (p - (p + a • u)) = r
    rw [show p - (p + a • u) = -(a • u) by abel, norm2_neg, norm2_smul, abs_of_pos ha]
    exact han
  have hxu : x - q = (1 - a) • u := by
    dsimp [q, u]
    simp only [sub_smul, one_smul, smul_sub]
    abel
  refine ⟨q, hpq, ?_⟩
  change norm2 (x - q) ≤ r
  rw [hxu, norm2_smul, abs_of_nonpos (sub_nonpos.mpr ha1)]
  change -(1 - a) * n ≤ r
  nlinarith

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
  exact moving_subset_of_closed_connected hS sdiff_subset
    (hS.1.sdiff (openEuclideanBall_isOpen p r)) (puncture_connected hS.1 hS.2.1 hr hball)

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

end PunctureMetric

/-!
## Interior retention on a compact rigid orbit

The conclusion is special to rigid copies of one fixed compact set. It is false
for arbitrary Hausdorff-close compact sets.

The proof takes subsequences of the cosine/sine coefficients and translations,
not of unrestricted real angles. No trivial-stabilizer assumption is needed.
-/

section RigidInterior

open Real Set Filter Topology Metric
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

abbrev RotationShift := Point × Point

def rotationShift (g : Rigid) : RotationShift := ((cos g.angle, sin g.angle), g.shift)

def coefficientApply (z : RotationShift) (p : Point) : Point :=
  (z.1.1 * p.1 - z.1.2 * p.2 + z.2.1, z.1.2 * p.1 + z.1.1 * p.2 + z.2.2)

def coefficientInverse (z : RotationShift) (p : Point) : Point :=
  (z.1.1 * (p.1 - z.2.1) + z.1.2 * (p.2 - z.2.2),
    -z.1.2 * (p.1 - z.2.1) + z.1.1 * (p.2 - z.2.2))

@[simp] theorem coefficientInverse_rotationShift (g : Rigid) (p : Point) :
    coefficientInverse (rotationShift g) p = g.symm p := by
  ext <;> simp only [coefficientInverse, rotationShift, Rigid.symm, Rigid.apply,
    rot, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, cos_neg, sin_neg] <;> ring

/-- The limit of the matrix coefficients still defines a homeomorphism. -/
def coefficientHomeomorph (z : RotationShift) (h : z.1.1 ^ 2 + z.1.2 ^ 2 = 1) : Point ≃ₜ Point where
  toFun := coefficientApply z
  invFun := coefficientInverse z
  left_inv p := by
    ext <;> dsimp only [coefficientApply, coefficientInverse]
    · linear_combination p.1 * h
    · linear_combination p.2 * h
  right_inv p := by
    ext <;> dsimp only [coefficientApply, coefficientInverse]
    · linear_combination (p.1 - z.2.1) * h
    · linear_combination (p.2 - z.2.2) * h
  continuous_toFun := by unfold coefficientApply; fun_prop
  continuous_invFun := by unfold coefficientInverse; fun_prop

/-- A closed set contains a limiting point approximated by points of that set. -/
theorem closed_mem_of_euclidean_near {X : Set Point} (hX : IsClosed X) (hne : X.Nonempty)
    {x : ℕ → Point} {p : Point} {δ : ℕ → ℝ}
    (hx : Tendsto x atTop (𝓝 p)) (hδ : Tendsto δ atTop (𝓝 0))
    (hnear : ∀ n, ∃ q ∈ X, euclideanDist (x n) q ≤ δ n) : p ∈ X := by
  have hupper : ∀ n, infDist (x n) X ≤ δ n := by
    intro n
    obtain ⟨q, hq, hd⟩ := hnear n
    have hm : dist (x n) q ≤ euclideanDist (x n) q := by
      rw [dist_eq_norm]
      exact product_norm_le_norm2 _
    exact (infDist_le_dist_of_mem hq).trans (hm.trans hd)
  have hzero : Tendsto (fun n => infDist (x n) X) atTop (𝓝 0) :=
    squeeze_zero (fun _ => infDist_nonneg) hupper hδ
  have hlim := ((lipschitz_infDist_pt X).continuous.tendsto p).comp hx
  have he : infDist p X = 0 := tendsto_nhds_unique hlim hzero
  rw [← hX.closure_eq]
  exact (mem_closure_iff_infDist_zero hne).mpr he

/-- Closeness of a rigid image bounds its translation uniformly. -/
theorem rigid_shift_bound {X : Set Point} {R δ : ℝ} (hne : X.Nonempty)
    (hR : ∀ x ∈ X, ‖x‖ ≤ R) (hδ : δ ≤ 1) {g : Rigid}
    (hclose : EuclideanClose δ X (g '' X)) : ‖g.shift‖ ≤ 4 * R + 1 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨q, hq, hd⟩ := hclose.2 (g x) (mem_image_of_mem _ hx)
  have hnq : norm2 q ≤ 2 * R := (norm2_le_two_product_norm q).trans (by linarith [hR q hq])
  have hnx : norm2 (rot g.angle x) ≤ 2 * R := by
    rw [norm2_rot]
    exact (norm2_le_two_product_norm x).trans (by linarith [hR x hx])
  have he : g.shift = (g x - q) + q + -(rot g.angle x) := by
    simp only [Rigid.apply]
    abel
  calc
    ‖g.shift‖ ≤ norm2 g.shift := product_norm_le_norm2 _
    _ ≤ norm2 (g x - q) + norm2 q + norm2 (rot g.angle x) := by
      rw [he]
      exact (norm2_add_le _ _).trans (by
        rw [norm2_neg]
        exact add_le_add (norm2_add_le _ _) le_rfl)
    _ ≤ 4 * R + 1 := by
      change norm2 (g x - q) ≤ δ at hd
      linarith

/-- Every fixed interior point is retained by sufficiently close rigid copies.
No restriction on rotation angle, translation, or symmetries of X is imposed. -/
theorem rigid_copies_retain_interior {X : Set Point} (hX : IsCompact X)
    {p : Point} (hp : p ∈ interior X) :
    ∃ η : ℝ, 0 < η ∧ ∀ g : Rigid, ∀ δ : ℝ,
      δ < η → EuclideanClose δ X (g '' X) → p ∈ g '' X := by
  classical
  have hne : X.Nonempty := ⟨p, interior_subset hp⟩
  by_contra hnot
  have counter (η : ℝ) (hη : 0 < η) :
      ∃ g : Rigid, ∃ δ : ℝ, δ < η ∧ EuclideanClose δ X (g '' X) ∧ p ∉ g '' X := by
    by_contra hnone
    apply hnot
    refine ⟨η, hη, ?_⟩
    intro g δ hδη hclose
    by_contra hout
    exact hnone ⟨g, δ, hδη, hclose, hout⟩
  choose g δ hsmall hclose hout using
    fun n : ℕ => counter (1 / ((n : ℝ) + 1)) (by positivity)
  have hδnonneg : ∀ n, 0 ≤ δ n := by
    intro n
    obtain ⟨q, _, hd⟩ := (hclose n).1 p (interior_subset hp)
    exact (euclideanDist_nonneg _ _).trans hd
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hδlim : Tendsto δ atTop (𝓝 0) := squeeze_zero hδnonneg (fun n => (hsmall n).le) hinv
  obtain ⟨R, hR⟩ := hX.isBounded.exists_norm_le
  let B : Set RotationShift :=
    (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ×ˢ closedBall (0 : Point) (4 * R + 1)
  have hB : IsCompact B := (isCompact_Icc.prod isCompact_Icc).prod (isCompact_closedBall _ _)
  have hgB : ∀ n, rotationShift (g n) ∈ B := by
    intro n
    refine ⟨⟨⟨neg_one_le_cos _, cos_le_one _⟩, neg_one_le_sin _, sin_le_one _⟩, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    apply rigid_shift_bound hne hR _ (hclose n)
    have he : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      linarith [Nat.cast_nonneg (α := ℝ) n]
    exact (hsmall n).le.trans he
  obtain ⟨z, hzB, σ, hσ, hz⟩ := hB.tendsto_subseq hgB
  have hunit : z.1.1 ^ 2 + z.1.2 ^ 2 = 1 := by
    have hclosed : IsClosed {z : RotationShift | z.1.1 ^ 2 + z.1.2 ^ 2 = 1} :=
      isClosed_eq (by fun_prop) continuous_const
    apply hclosed.mem_of_tendsto hz
    exact Eventually.of_forall fun n => cos_sq_add_sin_sq (g (σ n)).angle
  let F := coefficientHomeomorph z hunit
  have invmaps : ∀ x ∈ X, F.symm x ∈ X := by
    intro x hx
    have hcont : Continuous (fun z : RotationShift => coefficientInverse z x) := by
      unfold coefficientInverse
      fun_prop
    have hlim := (hcont.tendsto z).comp hz
    apply closed_mem_of_euclidean_near hX.isClosed hne hlim (hδlim.comp hσ.tendsto_atTop)
    intro n
    obtain ⟨_, ⟨q, hq, rfl⟩, hd⟩ := (hclose (σ n)).1 x hx
    refine ⟨q, hq, ?_⟩
    change euclideanDist (coefficientInverse (rotationShift (g (σ n))) x) q ≤ δ (σ n)
    rw [coefficientInverse_rotationShift]
    have he := euclideanDist_rigid (g (σ n)) ((g (σ n)).symm x) q
    rw [Rigid.apply_symm_apply] at he
    exact he.symm.le.trans hd
  have hU : IsOpen (F.symm '' interior X) := F.symm.isOpenMap _ isOpen_interior
  have hUX : F.symm '' interior X ⊆ X := by
    rintro _ ⟨x, hx, rfl⟩
    exact invmaps x (interior_subset hx)
  have hnhds : X ∈ 𝓝 (F.symm p) :=
    mem_of_superset (hU.mem_nhds (mem_image_of_mem _ hp)) hUX
  have hcont : Continuous (fun z : RotationShift => coefficientInverse z p) := by
    unfold coefficientInverse
    fun_prop
  have hev := ((hcont.tendsto z).comp hz).eventually hnhds
  obtain ⟨n, hn⟩ := hev.exists
  replace hn : coefficientInverse (rotationShift (g (σ n))) p ∈ X := hn
  rw [coefficientInverse_rotationShift] at hn
  exact hout (σ n) ⟨(g (σ n)).symm p, hn, (g (σ n)).apply_symm_apply p⟩

end MovingSofaStability

end RigidInterior

/-!
## A punctured Gerver family, including optimization over rigid alignment

The family has area loss pi*r^2 and distance exactly r from the entire
orientation-preserving rigid orbit of Gerver. The conclusion concerns the actual
closed sets, not the Hausdorff distance of their boundaries.
-/

section PuncturedSofa

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

end PuncturedSofa

/-!
## Sharpness of the unrestricted Hausdorff exponent

For every exponent greater than one half, every constant, and every positive
entry threshold, a punctured Gerver sofa violates the proposed estimate for
EVERY orientation-preserving rigid alignment. This is not a sharpness claim for
the cap constant or symmetric-difference area.
-/

section SharpExponent

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

end SharpExponent
