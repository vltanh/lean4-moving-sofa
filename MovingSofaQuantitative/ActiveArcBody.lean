module

public import MovingSofaQuantitative.TurningCap

/-!
# A minimal auxiliary body from its active inner arc

Uncompiled proof source. Only the lower support arc of an auxiliary body enters
its Mamikon energy. Taking the closed convex hull of that arc constructs a real
body without also perturbing the irrelevant outer boundary. Containment and
all wall constraints are proved for the constructed set, not assumed of a
hypothetical support function.
-/

@[expose] public section
noncomputable section

open Real Set Filter Topology MeasureTheory
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

/-- The curve turns clockwise as its *opposite* supporting normal increases.
The gap inequality is on the inactive interval before its first contact. -/
structure ActiveArcData (φ c : ℝ) (K : Set Point) where
  cap : IsCap K (π / 2)
  order : 0 < φ ∧ φ < c ∧ c < π / 2
  curve : ℝ → Point
  density : ℝ → ℝ
  continuous : ContinuousOn curve (Icc c (π / 2))
  derivative : ∀ t ∈ Ico c (π / 2),
    HasDerivWithinAt curve (-(density t) • vvec t) (Ici t) t
  density_nonneg : ∀ t ∈ Ico c (π / 2), 0 ≤ density t
  contained : ∀ t ∈ Icc c (π / 2), curve t ∈ K
  contact : ∀ t ∈ Icc c (π / 2), dot (curve t) (uvec t) = supp K t - 1
  gap : ∀ t ∈ Icc φ c, supp K t - 1 ≤ dot (curve c) (uvec t)
  cut_contact : dot (curve c) (uvec φ) = supp K φ - 1

namespace ActiveArcData

variable {φ c : ℝ} {K : Set Point} (D : ActiveArcData φ c K)

def body : Set Point := closure (convexHull ℝ (D.curve '' Icc c (π / 2)))

theorem curve_mem {t : ℝ} (ht : t ∈ Icc c (π / 2)) : D.curve t ∈ D.body :=
  subset_closure (subset_convexHull ℝ _ (mem_image_of_mem _ ht))

theorem body_subset : D.body ⊆ K :=
  closure_minimal (convexHull_min (image_subset_iff.mpr D.contained) D.cap.2.1.2.2)
    D.cap.2.1.2.1.isClosed

theorem body_isConvexBody : IsConvexBody D.body := by
  refine ⟨⟨D.curve c, D.curve_mem ⟨le_rfl, D.order.2.2.le⟩⟩, ?_, ?_⟩
  · exact D.cap.2.1.2.1.of_isClosed_subset isClosed_closure D.body_subset
  · exact (convex_convexHull ℝ _).closure

/-- Projection decreases until its active angle is reached. -/
theorem projection_decreases {s a b : ℝ} (ha : c ≤ a) (hab : a ≤ b)
    (hb : b ≤ π / 2) (hs : b ≤ s) (hsπ : s ≤ π / 2) :
    dot (D.curve b) (uvec s) ≤ dot (D.curve a) (uvec s) := by
  apply le_of_right_deriv_nonpos hab
    (((continuous_dot (uvec s)).comp_continuousOn D.continuous).mono (Icc_subset_Icc ha hb))
  · intro t ht
    have hd := hasDerivWithinAt_dot (D.derivative t ⟨ha.trans ht.1, ht.2.trans_le hb⟩) (uvec s)
    simpa only [dot_smul_left, dot_vvec_uvec'] using hd
  · intro t ht
    have hρ := D.density_nonneg t ⟨ha.trans ht.1, ht.2.trans_le hb⟩
    have hsin : 0 ≤ sin (s - t) := sin_nonneg_of_nonneg_of_le_pi
      (by linarith [ht.2]) (by linarith [ht.1, ha, D.order.1, D.order.2.1, pi_pos])
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ) hsin

/-- Projection increases after its active angle, including all inactive angles
before c. Both statements concern entire arcs, not sampled points. -/
theorem projection_increases {s a b : ℝ} (ha : c ≤ a) (hab : a ≤ b)
    (hb : b ≤ π / 2) (hs : s ≤ a) (hs0 : 0 ≤ s) :
    dot (D.curve a) (uvec s) ≤ dot (D.curve b) (uvec s) := by
  apply le_of_right_deriv_nonneg hab
    (((continuous_dot (uvec s)).comp_continuousOn D.continuous).mono (Icc_subset_Icc ha hb))
  · intro t ht
    have hd := hasDerivWithinAt_dot (D.derivative t ⟨ha.trans ht.1, ht.2.trans_le hb⟩) (uvec s)
    simpa only [dot_smul_left, dot_vvec_uvec'] using hd
  · intro t ht
    have hρ := D.density_nonneg t ⟨ha.trans ht.1, ht.2.trans_le hb⟩
    have hsin : sin (s - t) ≤ 0 := sin_nonpos_of_nonpos_of_neg_pi_le
      (by linarith [ht.1]) (by linarith [ht.2, hs0, pi_pos])
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hρ) hsin

/-- The closest point to an inner supporting line occurs at max(c,s). -/
theorem projection_minimum {s t : ℝ} (hs : s ∈ Icc φ (π / 2))
    (ht : t ∈ Icc c (π / 2)) :
    dot (D.curve (max c s)) (uvec s) ≤ dot (D.curve t) (uvec s) := by
  by_cases hsc : s ≤ c
  · rw [max_eq_left hsc]
    exact D.projection_increases le_rfl ht.1 ht.2 hsc (D.order.1.le.trans hs.1)
  · rw [max_eq_right (not_le.mp hsc).le]
    rcases le_total t s with hts | hst
    · exact D.projection_decreases ht.1 hts hs.2 le_rfl hs.2
    · exact D.projection_increases (not_le.mp hsc).le hst ht.2 le_rfl
        (D.order.1.le.trans hs.1)

private theorem dot_opposite (p : Point) (s : ℝ) : dot p (uvec (π + s)) = -dot p (uvec s) := by
  simp only [uvec, dot, cos_add, sin_add, cos_pi, sin_pi]
  ring

/-- The half-plane inequality passes through closed convex hulls. -/
theorem body_projection {s : ℝ} (hs : s ∈ Icc φ (π / 2)) {p : Point} (hp : p ∈ D.body) :
    dot (D.curve (max c s)) (uvec s) ≤ dot p (uvec s) := by
  have hsub : D.body ⊆ halfMinus (π + s) (-dot (D.curve (max c s)) (uvec s)) := by
    apply closure_minimal _ (isClosed_halfMinus _ _)
    apply convexHull_min _ (convex_halfMinus _ _)
    rintro p ⟨t, ht, rfl⟩
    change dot (D.curve t) (uvec (π + s)) ≤ _
    rw [dot_opposite]
    linarith [D.projection_minimum hs ht]
  have hh := hsub hp
  change dot p (uvec (π + s)) ≤ _ at hh
  rw [dot_opposite] at hh
  linarith

/-- Exact support on the energy-relevant arc. The inactive part is a single
vertex; the active part is the actual negatively turning curve. -/
theorem support {s : ℝ} (hs : s ∈ Icc φ (π / 2)) :
    supp D.body (π + s) = -dot (D.curve (max c s)) (uvec s) := by
  have hpoint : max c s ∈ Icc c (π / 2) :=
    ⟨le_max_left _ _, max_le D.order.2.2.le hs.2⟩
  calc
    supp D.body (π + s) = dot (D.curve (max c s)) (uvec (π + s)) :=
      cvx_supp_eq_of_isGreatest (D.curve_mem hpoint) (fun p hp => by
        rw [dot_opposite, dot_opposite]
        linarith [D.body_projection hs hp])
    _ = _ := dot_opposite _ _

/-- Every paired wall inequality holds on the full continuous angular interval. -/
theorem walls {s : ℝ} (hs : s ∈ Icc φ (π / 2)) :
    supp K s + supp D.body (π + s) ≤ 1 := by
  rw [D.support hs]
  by_cases hsc : s ≤ c
  · rw [max_eq_left hsc]
    linarith [D.gap s ⟨hs.1, hsc⟩]
  · rw [max_eq_right (not_le.mp hsc).le, D.contact s ⟨(not_le.mp hsc).le, hs.2⟩]
    ring_nf

/-- The entire active paired support is exactly one. -/
theorem active {s : ℝ} (hs : s ∈ Icc c (π / 2)) :
    supp K s + supp D.body (π + s) = 1 := by
  rw [D.support ⟨D.order.2.1.le.trans hs.1, hs.2⟩,
    max_eq_right hs.1, D.contact s hs]
  ring

theorem cut : supp K φ + supp D.body (π + φ) = 1 := by
  rw [D.support ⟨le_rfl, (D.order.2.1.trans D.order.2.2).le⟩,
    max_eq_left D.order.2.1.le, D.cut_contact]
  ring

theorem bottom : supp K (π / 2) + supp D.body (3 * π / 2) = 1 := by
  simpa only [show π + π / 2 = 3 * π / 2 by ring] using
    D.active ⟨D.order.2.2.le, le_rfl⟩

end ActiveArcData
end MovingSofaQuantitative
