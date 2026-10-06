module

public import MovingSofaStability.MissingAreaRecovery

/-!
# Uniform interior balls from convex pieces

Uncompiled proof source. The construction shrinks one fixed interior ball
about each point of a convex piece. The union lemmas permit a nonconvex
reference to be assembled from finitely many such pieces.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality

namespace MovingSofaStability

/-- Shrinking a ball inside a convex set gives a ball at every boundary point. -/
theorem convex_interiorBalls_of_ball {C : Set Point} (hC : Convex ℝ C)
    {c : Point} {s D : ℝ} (hs : 0 < s) (hD : 0 ≤ D)
    (hball : euclideanBall c s ⊆ C)
    (hbound : ∀ p ∈ C, euclideanDist p c ≤ D) :
    HasInteriorBalls C (s / (D + s)) (D + s) := by
  sorry

/-- A nonempty interior supplies a closed Euclidean ball even though the ambient
product-space topology is originally presented with the sup norm. -/
theorem exists_euclideanBall_subset_of_interior {C : Set Point}
    (hne : (interior C).Nonempty) :
    ∃ c s, 0 < s ∧ euclideanBall c s ⊆ C := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hc)
  refine ⟨c, r / 2, by linarith, ?_⟩
  intro q hq
  apply hball
  change dist q c < r
  have hd : dist q c ≤ euclideanDist c q := by
    rw [dist_comm, dist_eq_norm]
    exact product_norm_le_norm2 (c - q)
  exact (hd.trans hq).trans_lt (by linarith)

/-- Compact convex bodies with interior have uniform interior balls at all small scales. -/
theorem convexBody_hasInteriorBalls {C : Set Point} (hC : IsConvexBody C)
    (hne : (interior C).Nonempty) :
    ∃ κ r₀ : ℝ, 0 < κ ∧ 0 < r₀ ∧ HasInteriorBalls C κ r₀ := by
  obtain ⟨c, s, hs, hball⟩ := exists_euclideanBall_subset_of_interior hne
  have hc : c ∈ C := hball (by simpa only [euclideanBall, mem_setOf_eq, euclideanDist_self] using hs.le)
  have hcont : Continuous (fun p : Point => euclideanDist p c) := by
    exact continuous_norm2.comp (continuous_id.sub continuous_const)
  obtain ⟨D, hD⟩ := hC.2.1.exists_bound_of_continuousOn hcont.continuousOn
  have hD0 : 0 ≤ D := by simpa only [euclideanDist_self, norm_zero] using hD c hc
  have hbound : ∀ p ∈ C, euclideanDist p c ≤ D := by
    intro p hp
    have h := hD p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg (euclideanDist_nonneg p c)] using h
  refine ⟨s / (D + s), D + s, by positivity, by positivity, ?_⟩
  exact convex_interiorBalls_of_ball hC.2.2 hs hD0 hball hbound

/-- An interior-ball statement persists when its constants are decreased. -/
theorem HasInteriorBalls.mono_constants {G : Set Point} {κ r₀ κ' r₀' : ℝ}
    (h : HasInteriorBalls G κ r₀) (hκ : κ' ≤ κ) (hr : r₀' ≤ r₀) :
    HasInteriorBalls G κ' r₀' := by
  intro p hp ρ hρ hρmax
  obtain ⟨z, hz⟩ := h p hp ρ hρ (hρmax.trans hr)
  refine ⟨z, ?_⟩
  intro q hq
  exact hz (hq.trans (mul_le_mul_of_nonneg_right hκ hρ.le))

/-- A finite union need not be convex; a containing piece provides the local ball. -/
theorem interiorBalls_union {G H : Set Point} {κ r₀ : ℝ}
    (hG : HasInteriorBalls G κ r₀) (hH : HasInteriorBalls H κ r₀) :
    HasInteriorBalls (G ∪ H) κ r₀ := by
  intro p hp ρ hρ hρmax
  rcases hp with hp | hp
  · obtain ⟨z, hz⟩ := hG p hp ρ hρ hρmax
    exact ⟨z, fun q hq => ⟨Or.inl (hz hq).1, (hz hq).2⟩⟩
  · obtain ⟨z, hz⟩ := hH p hp ρ hρ hρmax
    exact ⟨z, fun q hq => ⟨Or.inr (hz hq).1, (hz hq).2⟩⟩

/-- Existential interior-ball constants combine without a shared initial scale. -/
theorem exists_interiorBalls_union {G H : Set Point}
    (hG : ∃ κ r₀ : ℝ, 0 < κ ∧ 0 < r₀ ∧ HasInteriorBalls G κ r₀)
    (hH : ∃ κ r₀ : ℝ, 0 < κ ∧ 0 < r₀ ∧ HasInteriorBalls H κ r₀) :
    ∃ κ r₀ : ℝ, 0 < κ ∧ 0 < r₀ ∧ HasInteriorBalls (G ∪ H) κ r₀ := by
  obtain ⟨κG, rG, hκG, hrG, hG⟩ := hG
  obtain ⟨κH, rH, hκH, hrH, hH⟩ := hH
  refine ⟨min κG κH, min rG rH, lt_min hκG hκH, lt_min hrG hrH, ?_⟩
  exact interiorBalls_union
    (hG.mono_constants (min_le_left _ _) (min_le_left _ _))
    (hH.mono_constants (min_le_right _ _) (min_le_right _ _))

end MovingSofaStability
