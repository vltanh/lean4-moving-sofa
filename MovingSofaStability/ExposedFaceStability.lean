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
  classical
  let B := K₀ + euclideanDisk 1
  have hB : IsCompact B :=
    (convexBody_add h₀.2.1 (euclideanDisk_isConvexBody (by norm_num : (0 : ℝ) ≤ 1))).2.1
  have : CompactSpace ↥B := isCompact_iff_compactSpace.mp hB
  have : CompactSpace ↥I := isCompact_iff_compactSpace.mp hI
  let defect : ↥B × ↥I → ℝ := fun z => Metric.infDist z.1.1 K₀ +
    |dot z.1.1 (uvec z.2.1) - supp K₀ z.2.1|
  let property : ↥B × ↥I → ℝ := fun z => F z.1.1 z.2.1
  have hmap : Continuous (fun z : ↥B × ↥I => (z.1.1, z.2.1)) := by fun_prop
  have hprop : Continuous property := by
    exact hF.comp_continuous hmap (fun z => ⟨z.1.2, z.2.2⟩)
  have hdef : Continuous defect := by
    apply Continuous.add
    · exact (Metric.continuous_infDist_pt K₀).comp (continuous_subtype_val.comp continuous_fst)
    · apply Continuous.abs
      apply Continuous.sub
      · exact continuous_dot_pair.comp
          ((continuous_subtype_val.comp continuous_fst).prodMk
            (continuous_uvec.comp (continuous_subtype_val.comp continuous_snd)))
      · exact h₀.2.1.continuous_supp.comp (continuous_subtype_val.comp continuous_snd)
  let bad : Set (↥B × ↥I) := {z | property z ≤ 0}
  have hbad : IsCompact bad := (isClosed_le hprop continuous_const).isCompact
  have hpos : ∀ z ∈ bad, 0 < defect z := by
    intro z hz
    by_contra hnot
    have hdist0 : Metric.infDist z.1.1 K₀ = 0 := by
      have hn := Metric.infDist_nonneg (x := z.1.1) (s := K₀)
      have ha := abs_nonneg (dot z.1.1 (uvec z.2.1) - supp K₀ z.2.1)
      change ¬0 < Metric.infDist z.1.1 K₀ +
        |dot z.1.1 (uvec z.2.1) - supp K₀ z.2.1| at hnot
      linarith
    have hgap0 : dot z.1.1 (uvec z.2.1) = supp K₀ z.2.1 := by
      change ¬0 < Metric.infDist z.1.1 K₀ +
        |dot z.1.1 (uvec z.2.1) - supp K₀ z.2.1| at hnot
      rw [hdist0, zero_add] at hnot
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (not_lt.mp hnot) (abs_nonneg _)))
    have hp : z.1.1 ∈ K₀ := (h₀.2.1.2.1.isClosed.mem_iff_infDist_zero h₀.2.1.1).2 hdist0
    have hh := hpositive z.2.1 z.2.2 z.1.1 ⟨hp, hgap0⟩
    exact (not_lt_of_ge hz) hh
  obtain ⟨m, hm, hmin⟩ := hbad.exists_forall_le' hdef.continuousOn hpos
  let δ := min 1 (m / 4)
  have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδm : 2 * δ < m := by
    have h := min_le_right (1 : ℝ) (m / 4)
    change δ ≤ m / 4 at h
    linarith
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro K hK hclose t ht p hp
  have hpB := cap_subset_unit_parallel hK h₀ hδ1 hclose hp.1
  let z : ↥B × ↥I := (⟨p, hpB⟩, ⟨t, ht⟩)
  by_contra hnot
  have hzbad : z ∈ bad := not_lt.mp hnot
  have hd : m ≤ defect z := hmin z hzbad
  have hcapclose := upperSupportClose_euclidean hδ.le hK h₀ hclose
  obtain ⟨q, hq, hpq⟩ := hcapclose.1 p hp.1
  have hdist : Metric.infDist p K₀ ≤ δ := by
    have hprod : dist p q ≤ euclideanDist p q := by
      rw [dist_eq_norm]
      exact product_norm_le_norm2 (p - q)
    exact (Metric.infDist_le_dist_of_mem hq).trans (hprod.trans hpq)
  have hsupport : |dot p (uvec t) - supp K₀ t| ≤ δ := by
    rw [hp.2]
    exact hclose t (hIupper ht)
  change m ≤ Metric.infDist p K₀ + |dot p (uvec t) - supp K₀ t| at hd
  linarith

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
