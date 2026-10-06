module

public import MovingSofaStability.CBVAlgebra

/-!
# Cap area split at the four Mamikon arcs, retaining all atoms

In a nonsmooth cap, atoms at 0, phi, pi/2-phi and pi cannot be discarded. The
five edge segments below account for those atoms and the top edge. This is the
missing bookkeeping in a naive reuse of the Ki-only source Lemma 8.3.5.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality

namespace MovingSofaStability

/-- Signed area of the supporting face traversed counterclockwise. -/
def edgeArea (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ :=
  segArea (vminus K t) (vplus K t)

/-- A curvature atom contributes exactly its supporting-face area. -/
theorem edgeArea_eq_atom {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    edgeArea K t = (1 / 2) * (sigma K).real {t} * supp K t := by
  have hv := (proposition2_1_2 hK t).2
  have hcross : cross (vminus K t) (vvec t) = supp K t := by
    simpa [cross, vvec, dot, uvec] using dot_vminus_uvec K t
  unfold edgeArea segArea
  rw [hv, cross_add_right, cross_self, cross_smul_right, hcross]
  simp only [zero_add, sigmaAt, measureReal_def]
  ring

/-- Right-endpoint atoms in a support integral. -/
theorem support_integral_Ioc {K : Set (ℝ × ℝ)} (hK : IsConvexBody K)
    {a b : ℝ} (hab : a < b) :
    (∫ t in Ioc a b, supp K t ∂(sigma K)) =
      (∫ t in Ioo a b, supp K t ∂(sigma K)) + (sigma K).real {b} * supp K b := by
  have hf := hK.continuous_supp
  have hint : IntegrableOn (supp K) (Icc a b) (sigma K) :=
    hf.continuousOn.integrableOn_compact isCompact_Icc
  have hpoint : IntegrableOn (supp K) ({b} : Set ℝ) (sigma K) :=
    hint.mono_set (by intro t ht; rw [mem_singleton_iff.mp ht]; exact ⟨hab.le, le_rfl⟩)
  rw [← Ioo_union_right hab,
    setIntegral_union (by simp) (measurableSet_singleton _)
      (hint.mono_set Ioo_subset_Icc_self) hpoint,
    integral_singleton, smul_eq_mul]

/-- Left-endpoint atoms in a support integral. -/
theorem support_integral_Icc {K : Set (ℝ × ℝ)} (hK : IsConvexBody K)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Icc a b, supp K t ∂(sigma K)) =
      (∫ t in Ioc a b, supp K t ∂(sigma K)) + (sigma K).real {a} * supp K a := by
  have hf := hK.continuous_supp
  have hint : IntegrableOn (supp K) (Icc a b) (sigma K) :=
    hf.continuousOn.integrableOn_compact isCompact_Icc
  have hpoint : IntegrableOn (supp K) ({a} : Set ℝ) (sigma K) :=
    hint.mono_set (by intro t ht; rw [mem_singleton_iff.mp ht]; exact ⟨le_rfl, hab⟩)
  rw [← Ioc_union_left hab,
    setIntegral_union (by simp) (measurableSet_singleton _)
      (hint.mono_set Ioc_subset_Icc_self) hpoint,
    integral_singleton, smul_eq_mul]

/-- The two half-arcs plus their three endpoint faces give the cap's area. -/
theorem cap_area_two_arcs {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) :
    area K = convexCurveArea K 0 (π / 2) + convexCurveArea K (π / 2) π +
      edgeArea K 0 + edgeArea K (π / 2) + edgeArea K π := by
  have hcb := hK.2.1
  have hf := hcb.continuous_supp
  have hv : (0 : ℝ) < π / 2 := by linarith [pi_pos]
  have hvπ : π / 2 < π := by linarith [pi_pos]
  have hup : (∫ t in Icc 0 π, supp K t ∂(sigma K)) =
      (∫ t in Ioo 0 (π / 2), supp K t ∂(sigma K)) +
      (∫ t in Ioo (π / 2) π, supp K t ∂(sigma K)) +
      (sigma K).real {0} * supp K 0 +
      (sigma K).real {π / 2} * supp K (π / 2) +
      (sigma K).real {π} * supp K π := by
    rw [support_integral_Icc hcb pi_pos.le,
      ← intervalIntegral.integral_of_le pi_pos.le,
      ← intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable 0 (π / 2)) (hf.intervalIntegrable (π / 2) π),
      intervalIntegral.integral_of_le hv.le,
      intervalIntegral.integral_of_le hvπ.le,
      support_integral_Ioc hcb hv, support_integral_Ioc hcb hvπ]
    ring
  rw [theorem7_1_3 hcb, opt_Ico_eq_Icc hK hf hK.2.2.2.2.2.1, hup]
  rw [edgeArea_eq_atom hcb, edgeArea_eq_atom hcb, edgeArea_eq_atom hcb]
  unfold convexCurveArea
  ring

/-- Four cap Mamikon arcs plus all five supporting faces. No atom is omitted. -/
theorem cap_area_four_arcs {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) :
    area K = convexCurveArea K 0 φ + convexCurveArea K φ (π / 2 - φ) +
      convexCurveArea K (π / 2 - φ) (π / 2) + convexCurveArea K (π / 2) π +
      edgeArea K 0 + edgeArea K φ + edgeArea K (π / 2 - φ) +
      edgeArea K (π / 2) + edgeArea K π := by
  have hcb := hK.2.1
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  have c1 := (lemma7_3_4 hcb hφ0 (by linarith : φ < π / 2)
    (by linarith)).2.2.2
  have c2 := (lemma7_3_4 hcb (by linarith : φ < π / 2 - φ)
    (by linarith : π / 2 - φ < π / 2) (by linarith)).2.2.2
  have ha := cap_area_two_arcs hK
  unfold edgeArea at *
  linarith

/-- A useful three-point collinearity identity, with a face inserted between
its two endpoints rather than identified with a point. -/
theorem segArea_join_face {t h : ℝ} {z₁ pl pr z₂ : ℝ × ℝ}
    (hz₁ : z₁ ∈ line t h) (hpl : pl ∈ line t h)
    (hpr : pr ∈ line t h) (hz₂ : z₂ ∈ line t h) :
    segArea z₁ pl + segArea pr z₂ + segArea pl pr = segArea z₁ z₂ := by
  have h1 := segArea_add_of_mem_line hz₁ hpl hpr
  have h2 := segArea_add_of_mem_line hz₁ hpr hz₂
  linarith

end MovingSofaStability
