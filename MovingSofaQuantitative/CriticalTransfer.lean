module

public import MovingSofaQuantitative.DualSlack
public import MovingSofaQuantitative.FullQConsequences

/-!
# From the actual operator and endpoint bounds to the paper's Q statements

Uncompiled proof source. The hypotheses here name the two independent inputs
that still need to be instantiated: the concrete continuum operator inequality
and the actual endpoint wall-slack estimate. No target is registered as proved
merely by this transfer. In particular the existing zero-slack theorem is used
on the actual input triple, not assumed as a property of an arbitrary function.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability

namespace MovingSofaQuantitative

/-- Pairwise bounds on the pinned profile give an attained horizontal alignment
of the actual convex caps. Pinning cancels from the two-point determinant. -/
theorem capTranslationDistance_le_of_pinned_pairs {K₀ K₁ : Set Point}
    (h₀ : IsCap K₀ (π / 2)) (h₁ : IsCap K₁ (π / 2)) {R : ℝ} (hR : 0 ≤ R)
    (hp : ∀ t u : UpperAngle,
      |capDifference K₀ K₁ t * cos u - capDifference K₀ K₁ u * cos t| ≤
        R * (|cos t| + |cos u|)) :
    capTranslationDistance K₀ K₁ ≤ R := by
  apply capTranslationDistance_le_of_close hR
  apply (fitsTranslation_iff_capClose h₀ h₁ R).mp
  apply (fitsTranslation_iff_pairwise horizontalMode_nonzero R).mpr
  intro t u
  have he : capDifference K₀ K₁ t * cos u - capDifference K₀ K₁ u * cos t =
      upperSupportDifference K₀ K₁ t * horizontalMode u -
        upperSupportDifference K₀ K₁ u * horizontalMode t := by
    unfold capDifference pinnedDifference upperSupportDifference horizontalMode
    ring
  rw [← he]
  exact hp t u

/-- Both actual wall gaps vanish at the critical endpoints on the exposed face. -/
theorem critical_endpoint_slacks_zero {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) (x : WideTriple P.φ) (hz : wideDualSlack hP hbox x = 0) :
    rightWallSlack x (criticalLeft P) = 0 ∧ leftWallSlack x (criticalRight P) = 0 := by
  have h := zero_dual_slack_profiles hP hbox x hz
  obtain ⟨hp, hpc, hcb, hb, hvd, hdT, hTp⟩ := critical_arc_order hP
  exact ⟨h.1 _ ⟨le_rfl, hcb.le.trans hb.le⟩, h.2 _ ⟨hvd.le, le_rfl⟩⟩

/-- Instantiating the concrete operator theorem closes the exact critical-face
upper theorem, including triples whose Q deficit is zero. -/
theorem criticalFaceUpper_of_operator
    (hop : ∀ (P : GerverParams) (hP : P.IsSolution) (hbox : P.InBox),
      CriticalOperatorBound hP hbox) : Targets.CriticalFaceUpper := by
  intro P hP hbox x hz
  obtain ⟨hB, hD⟩ := critical_endpoint_slacks_zero hP hbox x hz
  apply capTranslationDistance_le_of_pinned_pairs (wideGerverTriple hP hbox).2.1 x.2.1
    (by positivity)
  intro t u
  have he := actual_pair_bound hP hbox (hop P hP hbox) x (σ := 0) le_rfl
    (by rw [hB, abs_zero]) (by rw [hD, abs_zero]) t u
  simpa only [zero_div, add_zero] using he

/-- An operational endpoint assertion. It mentions the actual nonnegative
wall gaps, not a fictitious derivative bound on an unspecified function. -/
def EndpointSlackBound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) : Prop :=
  ∀ x : WideTriple P.φ, 0 < qDeficit P x → qDeficit P x ≤ 1 / 512 →
    |rightWallSlack x (criticalLeft P)| ≤ 16 * (qDeficit P x) ^ (2 / 3 : ℝ) ∧
    |leftWallSlack x (criticalRight P)| ≤ 16 * (qDeficit P x) ^ (2 / 3 : ℝ)

/-- The all-pairs operator theorem and the endpoint-slack theorem give the
finite-deficit estimate with its exact higher-order term. -/
theorem fullQFinite_of_operator_endpoints
    (hop : ∀ (P : GerverParams) (hP : P.IsSolution) (hbox : P.InBox),
      CriticalOperatorBound hP hbox)
    (hend : ∀ (P : GerverParams) (hP : P.IsSolution) (hbox : P.InBox),
      EndpointSlackBound hP hbox) : Targets.FullQFinite := by
  intro P hP hbox x hΔ hsmall
  obtain ⟨hB, hD⟩ := hend P hP hbox x hΔ hsmall
  apply capTranslationDistance_le_of_pinned_pairs (wideGerverTriple hP hbox).2.1 x.2.1
    (by positivity)
  intro t u
  have he := actual_pair_bound hP hbox (hop P hP hbox) x
    (σ := 16 * (qDeficit P x) ^ (2 / 3 : ℝ)) (by positivity) hB hD t u
  convert he using 1 <;> ring

/-- All upper conclusions use the same operator/endpoint hypotheses, so an
uninstantiated numerical premise cannot be hidden by calling a corollary. -/
theorem fullQ_upper_package_of_inputs
    (hop : ∀ (P : GerverParams) (hP : P.IsSolution) (hbox : P.InBox),
      CriticalOperatorBound hP hbox)
    (hend : ∀ (P : GerverParams) (hP : P.IsSolution) (hbox : P.InBox),
      EndpointSlackBound hP hbox) :
    Targets.CriticalFaceUpper ∧ Targets.FullQFinite ∧ Targets.FullQ094 := by
  have hf := fullQFinite_of_operator_endpoints hop hend
  exact ⟨criticalFaceUpper_of_operator hop, hf, fullQ094_of_finite hf⟩

end MovingSofaQuantitative
