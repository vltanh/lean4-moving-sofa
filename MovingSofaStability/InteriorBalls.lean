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
  intro p hp ρ hρ hρmax
  have hden : 0 < D + s := by linarith
  let μ := ρ / (D + s)
  let z := (1 - μ) • p + μ • c
  have hμ : 0 < μ := div_pos hρ hden
  have hμ1 : μ ≤ 1 := (div_le_one hden).2 hρmax
  have hμden : μ * (D + s) = ρ := div_mul_cancel₀ _ hden.ne'
  have hrad : s / (D + s) * ρ = μ * s := by dsimp [μ]; ring
  refine ⟨z, ?_⟩
  intro q hq
  rw [hrad] at hq
  let w := c + μ⁻¹ • (q - z)
  have hwball : w ∈ euclideanBall c s := by
    change norm2 (c - (c + μ⁻¹ • (q - z))) ≤ s
    rw [show c - (c + μ⁻¹ • (q - z)) = -(μ⁻¹ • (q - z)) by abel,
      norm2_neg, norm2_smul, abs_of_pos (inv_pos.mpr hμ)]
    have hq' : norm2 (q - z) ≤ μ * s := by
      rw [← norm2_neg, neg_sub]
      exact hq
    have hmul := mul_le_mul_of_nonneg_left hq' (inv_nonneg.mpr hμ.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hμ.ne', one_mul] using hmul
  have hqC : q ∈ C := by
    have h := hC hp (hball hwball) (sub_nonneg.mpr hμ1) hμ.le (by ring : 1 - μ + μ = 1)
    have he : (1 - μ) • p + μ • w = q := by
      have hw : μ • w = μ • c + (q - z) := by
        simp only [w, smul_add, smul_inv_smul₀ hμ.ne']
      rw [hw]
      simp only [z]
      abel
    rwa [he] at h
  have hzp : euclideanDist p z ≤ μ * D := by
    change norm2 (p - ((1 - μ) • p + μ • c)) ≤ μ * D
    rw [show p - ((1 - μ) • p + μ • c) = μ • (p - c) by
      ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring,
      norm2_smul, abs_of_pos hμ]
    exact mul_le_mul_of_nonneg_left (hbound p hp) hμ.le
  refine ⟨hqC, ?_⟩
  change euclideanDist p q ≤ ρ
  have hh := euclideanDist_triangle p z q
  have he : μ * D + μ * s = ρ := by rw [← mul_add, hμden]
  exact hh.trans ((add_le_add hzp hq).trans_eq he)

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
  have hc : c ∈ C := hball (by simpa only [euclideanBall, mem_ofPred_eq, euclideanDist_self] using hs.le)
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
