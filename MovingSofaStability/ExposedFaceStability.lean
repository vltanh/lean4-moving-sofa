module

public import MovingSofaStability.GerverMargins
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Uniform stability of exposed-face properties

Uncompiled proof source. A positive continuous property on the reference
exposed faces persists for every point of every nearby exposed face. This
covers atoms in the competitor and does not presume derivative convergence
at a multiple-point face of the reference.

The proof takes a minimum of a membership/face defect on a fixed compact set.
It does not require a metric or a differentiable structure on the space of caps.
-/

@[expose] public section
noncomputable section

open Real Set Metric
open scoped Pointwise
open MovingSofaOptimality

namespace MovingSofaStability

/-- Caps in a unit support neighborhood share a fixed compact containing body. -/
theorem cap_subset_unit_parallel {K K₀ : Set Point} (hK : IsCap K (π / 2))
    (h₀ : IsCap K₀ (π / 2)) {δ : ℝ} (hδ : δ ≤ 1)
    (hclose : UpperSupportClose δ K K₀) : K ⊆ K₀ + euclideanDisk 1 := by
  intro p hp
  have hsum := convexBody_add h₀.2.1 (euclideanDisk_isConvexBody (by norm_num : (0 : ℝ) ≤ 1))
  apply (mem_iff_forall_dot_le_supp hsum p).2
  intro t
  rw [supp_add_euclideanDisk h₀.2.1 (by norm_num)]
  have he := (abs_le.mp (upperSupportClose_all hK h₀ hclose t)).2
  have hpoint := dot_le_supp hK.2.1.2.1 hp t
  linarith

/-- Strict continuous inequalities on exposed faces are uniform under cap perturbation. -/
theorem exposed_face_property_stable {K₀ : Set Point} (h₀ : IsCap K₀ (π / 2))
    {I : Set ℝ} (hI : IsCompact I) (hIupper : I ⊆ Icc (0 : ℝ) π)
    (F : Point → ℝ → ℝ)
    (hF : ContinuousOn (fun z : Point × ℝ => F z.1 z.2)
      ((K₀ + euclideanDisk 1) ×ˢ I))
    (hpositive : ∀ t ∈ I, ∀ p ∈ edge K₀ t, 0 < F p t) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K K₀ →
        ∀ t ∈ I, ∀ p ∈ edge K t, 0 < F p t := by
  sorry

/-- On a compact interval of unique reference faces, all competing contact
points are uniformly close to the reference contact curve. -/
theorem exposed_points_uniformly_close {K₀ : Set Point} (h₀ : IsCap K₀ (π / 2))
    {I : Set ℝ} (hI : IsCompact I) (hIupper : I ⊆ Icc (0 : ℝ) π)
    (v : ℝ → Point) (hv : ContinuousOn v I)
    (hface : ∀ t ∈ I, ∀ p ∈ edge K₀ t, p = v t)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K K₀ →
        ∀ t ∈ I, ∀ p ∈ edge K t, euclideanDist p (v t) < η := by
  have hFc : ContinuousOn (fun z : Point × ℝ => η - euclideanDist z.1 (v z.2))
      ((K₀ + euclideanDisk 1) ×ˢ I) := by
    apply continuousOn_const.sub
    apply continuous_norm2.comp_continuousOn
    exact continuous_fst.continuousOn.sub
      (hv.comp continuous_snd.continuousOn (fun z hz => hz.2))
  obtain ⟨δ, hδ, hδ1, htransfer⟩ := exposed_face_property_stable h₀ hI hIupper
    (fun p t => η - euclideanDist p (v t)) hFc (by
      intro t ht p hp
      rw [hface t ht p hp, euclideanDist_self, sub_zero]
      exact hη)
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro K hK hclose t ht p hp
  have h := htransfer K hK hclose t ht p hp
  linarith

end MovingSofaStability
