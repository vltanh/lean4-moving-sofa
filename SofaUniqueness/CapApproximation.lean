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
  have hcb := hK.2.1
  rintro p ⟨⟨_, hfy⟩, hquad⟩
  have hy₀ : 0 ≤ p.2 := by
    simpa only [halfPlus, mem_ofPred_eq, nef_dot_uvec_pi_div_two] using hfy
  obtain ⟨t, ht, hp⟩ := mem_iUnion₂.mp hquad
  have hcos : 0 < cos t :=
    cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2.trans_le hK.1.2⟩
  have hsin : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [ht.2, hK.1.2, pi_pos])
  have hsupA : supp K t ≤ R * cos t + 1 := by
    apply nef_supp_le hcb.1
    intro q hq
    obtain ⟨hx, hy⟩ := hbox hq
    simp only [dot, uvec]
    nlinarith [sin_le_one t]
  have hsupC : supp K (t + π / 2) ≤ R * sin t + 1 := by
    apply nef_supp_le hcb.1
    intro q hq
    obtain ⟨hx, hy⟩ := hbox hq
    rw [uvec_add_pi_div_two]
    simp only [dot, vvec]
    nlinarith [cos_le_one t]
  rw [proposition2_2_2_qMinus] at hp
  have hpa : dot p (uvec t) < R * cos t := by
    have h : dot p (uvec t) < supp K t - 1 := hp.1
    linarith
  have hpc : dot p (vvec t) < R * sin t := by
    have h : dot p (uvec (t + π / 2)) < supp K (t + π / 2) - 1 := hp.2
    rw [uvec_add_pi_div_two] at h
    linarith
  have hx₁ : p.1 < R := by
    simp only [dot, uvec] at hpa
    nlinarith
  have hx₀ : -R < p.1 := by
    simp only [dot, vvec] at hpc
    nlinarith
  have hyid : p.2 = sin t * dot p (uvec t) + cos t * dot p (vvec t) := by
    simp only [dot, uvec, vvec]
    linear_combination (-p.2) * sin_sq_add_cos_sq t
  have hylt : p.2 < 2 * R * (sin t * cos t) := by
    rw [hyid]
    have h₁ := mul_lt_mul_of_pos_left hpa hsin
    have h₂ := mul_lt_mul_of_pos_left hpc hcos
    nlinarith
  have hprod : sin t * cos t ≤ 1 := by
    have h := mul_le_mul (sin_le_one t) (cos_le_one t) hcos.le zero_le_one
    simpa only [one_mul] using h
  have hy₁ : p.2 ≤ 2 * R := by
    have h := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2 * R by positivity)
    linarith
  exact ⟨⟨hx₀.le, hx₁.le⟩, hy₀, hy₁⟩

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
  let E : Set ℝ := {t | f t = g t}
  have hE : IsClosed E := isClosed_eq hf hg
  have hI : Ioo 0 ω ⊆ E := by
    intro t ht
    have htE : t ∈ closure E := by
      apply Metric.mem_closure_iff.mpr
      intro ε hε
      obtain ⟨m, s, hs, hst⟩ := mpc_dyadic_dense hω ht hε
      refine ⟨s, heq m s hs, ?_⟩
      rw [Real.dist_eq, abs_sub_comm]
      exact hst
    rwa [hE.closure_eq] at htE
  have hclosure := closure_minimal hI hE
  rw [closure_Ioo hω.1.ne'] at hclosure
  exact hclosure

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
  have hfirst := eqOn_of_dyadic_eq hω (continuous_supp hK.2.1.2.1)
    (continuous_supp hL.2.1.2.1) (fun m t ht => (heq m t ht).1)
  have hsecond := eqOn_of_dyadic_eq hω
    ((continuous_supp hK.2.1.2.1).comp (continuous_id.add continuous_const))
    ((continuous_supp hL.2.1.2.1).comp (continuous_id.add continuous_const))
    (fun m t ht => (heq m t ht).2)
  apply caps_eq_of_upper_supports hK hL
  intro t ht
  rcases ht with ht | ht
  · exact hfirst ht
  · have h := hsecond (show t - π / 2 ∈ Icc (0 : ℝ) ω by
      constructor <;> linarith [ht.1, ht.2])
    simpa only [sub_add_cancel] using h

end SofaUniqueness
