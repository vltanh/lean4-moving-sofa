module

public import SofaUniqueness.DyadicSelector
public import MovingSofa.Injectivity.LimitIneq

/-!
# The approximation facts needed by the sampled selector

Only upper semicontinuity of the varying polygon objective is needed. The
niches of caps in a common horizontal box have a common bounded rectangle;
this does NOT use niche containment in the cap or balancedness. Eventual
membership in the open inner quadrants then gives the required lower bound
for the niche areas.

Agreement on all persistent dyadic supports identifies a cap. There is no
uniform convergence theorem for the area functionals hidden in that step.
Uncompiled source, with no admissions or decision tactics.
-/

@[expose] public section
noncomputable section

open Set Real Filter Topology MeasureTheory MovingSofa

namespace SofaUniqueness

/-- A uniform bound for niches, without assuming that a niche is in its cap. -/
theorem niche_subset_box {K : Set (ℝ × ℝ)} {ω R : ℝ}
    (hK : IsCap K ω) (hR : 0 ≤ R)
    (hbox : K ⊆ Icc (-R) R ×ˢ Icc 0 1) :
    niche K ω ⊆ Icc (-R) R ×ˢ Icc 0 (2 * R) := by
  sorry

/-- The same rectangle bounds every sampled niche of a cap in the box. -/
theorem polyNiche_subset_box {Θ : AngleSet} {K : Set (ℝ × ℝ)} {R : ℝ}
    (hK : IsCap K Θ.ω) (hR : 0 ≤ R)
    (hbox : K ⊆ Icc (-R) R ×ˢ Icc 0 1) :
    polyNiche Θ K ⊆ Icc (-R) R ×ˢ Icc 0 (2 * R) :=
  (proposition3_2_2 hK).2.trans (niche_subset_box hK hR hbox)

/-- Upper semicontinuity of the varying dyadic polygon objective along a
Hausdorff-convergent sequence. No maximizer hypothesis is used. -/
theorem dyadic_objective_limsup {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    {k : ℕ → ℕ} (hk : StrictMono k) {Ks : ℕ → Set (ℝ × ℝ)}
    (hKs : ∀ n, IsPolygonCap (dyadicAngleSet ω hω (k n)) (Ks n))
    {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (hlim : HausdorffTendsto Ks K)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ n, Ks n ⊆ Icc (-R) R ×ˢ Icc 0 1) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      polyArea (dyadicAngleSet ω hω (k n)) (Ks n) ≤ sofaArea ω K + ε := by
  intro ε hε
  have hKsc : ∀ n, IsConvexBody (Ks n) := fun n => (hKs n).1.2.1
  have hA := mpc_area_usc hK hKsc hlim (half_pos hε)
  have hN := mpc_area_lsc (N := niche K ω)
    (fun p hp => mpc_niche_eventually hω hK hk hKsc hlim hp)
    ((isCompact_Icc.prod isCompact_Icc).isBounded :
      Bornology.IsBounded (Icc (-R) R ×ˢ Icc (0 : ℝ) (2 * R)))
    (Eventually.of_forall fun n => polyNiche_subset_box (hKs n).1 hR (hbox n))
    (half_pos hε)
  filter_upwards [hA, hN] with n hnA hnN
  rw [theorem3_2_3 (hKs n)]
  unfold sofaArea
  linarith

/-- Exact recovery comparison plus a one-sided objective limit forces the
possibly varying nonnegative penalties to converge to zero. -/
theorem penalty_tendsto_zero_of_objective
    (F P : ℕ → ℝ) (M A : ℝ) (hP : ∀ n, 0 ≤ P n)
    (hselect : ∀ n, M ≤ F n - P n) (hA : A ≤ M)
    (hupper : ∀ ε > 0, ∀ᶠ n in atTop, F n ≤ A + ε) :
    Tendsto P atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (hP n)
  · intro b hb
    filter_upwards [hupper (b / 2) (by linarith)] with n hn
    have h := hselect n
    linarith

/-- Continuous functions agreeing on every dyadic angle agree on the whole
closed rotation interval, including its two endpoints. -/
theorem eqOn_of_dyadic_eq {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (heq : ∀ m, ∀ t ∈ (dyadicAngleSet ω hω m).angles, f t = g t) :
    EqOn f g (Icc 0 ω) := by
  sorry

/-- Upper supports and the standard lower strips determine the entire cap. -/
theorem caps_eq_of_upper_supports {ω : ℝ} {K L : Set (ℝ × ℝ)}
    (hK : IsCap K ω) (hL : IsCap L ω)
    (heq : ∀ t ∈ jSet ω, supp K t = supp L t) : K = L := by
  have hA : ∀ t ∈ jSet ω ∪ {ω + π, 3 * π / 2}, supp K t = supp L t := by
    intro t ht
    simp only [mem_union, mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with ht | rfl | rfl
    · exact heq t ht
    · rw [hK.2.2.2.2.1, hL.2.2.2.2.1]
    · rw [hK.2.2.2.2.2.1, hL.2.2.2.2.2.1]
  rw [nef_eq_setOf_supp hK.2.1 hK.2.2.2.2.2.2,
    nef_eq_setOf_supp hL.2.1 hL.2.2.2.2.2.2]
  ext p
  constructor
  · intro hp t ht
    rw [← hA t ht]
    exact hp t ht
  · intro hp t ht
    rw [hA t ht]
    exact hp t ht

/-- Persistent first and shifted dyadic supports identify a standard cap. -/
theorem caps_eq_of_dyadic_supports {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    {K L : Set (ℝ × ℝ)} (hK : IsCap K ω) (hL : IsCap L ω)
    (heq : ∀ m, ∀ t ∈ (dyadicAngleSet ω hω m).angles,
      supp K t = supp L t ∧ supp K (t + π / 2) = supp L (t + π / 2)) : K = L := by
  sorry

end SofaUniqueness
