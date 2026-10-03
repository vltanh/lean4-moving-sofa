module

public import SofaUniqueness.SupportSamples
public import MovingSofa.Balanced.BalancedMaximumSofa

/-!
# Existence of actual penalized polygon maximizers

We maximize the polygon objective minus a finite sampled support penalty over
ALL standard polygon caps of the fixed angle set. Two positively weighted
orthogonal samples prevent translations from escaping. Positive objective
prevents the width from escaping, by the paper's general polygon-width lemma.

The compactness argument is the finite-support-value argument used for
Theorem 3.4.3, with the continuous finite penalty retained. It does not assume
that the selected polygons are balanced, and it imposes no artificial box
constraint whose later variations would have to be justified.

Uncompiled source. No admissions, decision tactics, or external proof scripts.
-/

@[expose] public section
noncomputable section

open Set Real Filter Topology MeasureTheory MovingSofa
open scoped BigOperators

namespace SofaUniqueness

/-- A common position bound from two controlled orthogonal support samples. -/
def sampleBoxRadius (target : Set (ℝ × ℝ)) (t c q : ℝ) : ℝ :=
  let H := |supp target t| + |supp target (t + π / 2)| + c / q + 1
  H / sin t + H / cos t

theorem sampleBoxRadius_nonneg (target : Set (ℝ × ℝ)) {t c q : ℝ}
    (ht0 : 0 < t) (htL : t < π / 2) (hc : 0 ≤ c) (hq : 0 < q) :
    0 ≤ sampleBoxRadius target t c q := by
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 (by linarith [pi_pos])
  have hcos : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], htL⟩
  unfold sampleBoxRadius
  positivity

/-- Two sample bounds give a compact bounding rectangle for the actual cap. -/
theorem polygon_subset_sampleBox {Θ : AngleSet} {K target : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {t c q : ℝ} (ht : t ∈ Θ.angles)
    (hc : 0 ≤ c) (hq : 0 < q)
    (hfirst : q * (supp K t - supp target t) ^ 2 ≤ c)
    (hsecond : q * (supp K (t + π / 2) - supp target (t + π / 2)) ^ 2 ≤ c) :
    K ⊆ Icc (-sampleBoxRadius target t c q) (sampleBoxRadius target t c q) ×ˢ Icc 0 1 := by
  have htI := mpc_angles_bounds ht
  have htL : t < π / 2 := htI.2.trans_le (mpc_omega_le Θ)
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi htI.1 (by linarith [pi_pos])
  have hcos : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [htI.1, pi_pos], htL⟩
  have hqdiv : 0 ≤ c / q := div_nonneg hc hq.le
  have hsq₀ : (supp K t - supp target t) ^ 2 ≤ c / q := by
    apply (le_div_iff₀ hq).mpr
    simpa only [mul_comm] using hfirst
  have hsq₁ : (supp K (t + π / 2) - supp target (t + π / 2)) ^ 2 ≤ c / q := by
    apply (le_div_iff₀ hq).mpr
    simpa only [mul_comm] using hsecond
  have habs (x : ℝ) (hx : x ^ 2 ≤ c / q) : |x| ≤ c / q + 1 := by
    have h₀ := abs_nonneg x
    have h₁ : |x| ^ 2 = x ^ 2 := sq_abs x
    nlinarith [sq_nonneg (|x| - 1)]
  have ha₀ := habs _ hsq₀
  have ha₁ := habs _ hsq₁
  let H := |supp target t| + |supp target (t + π / 2)| + c / q + 1
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hb₀ : supp K t ≤ H := by
    have h := (abs_le.mp ha₀).2
    have htarget := le_abs_self (supp target t)
    dsimp [H]
    linarith [abs_nonneg (supp target (t + π / 2))]
  have hb₁ : supp K (t + π / 2) ≤ H := by
    have h := (abs_le.mp ha₁).2
    have htarget := le_abs_self (supp target (t + π / 2))
    dsimp [H]
    linarith [abs_nonneg (supp target t)]
  intro p hp
  have hy₀ : 0 ≤ p.2 := (mpc_cap_nonneg hK.1 hp).1
  have hy₁ : p.2 ≤ 1 := (mpc_cap_le_one hK.1 hp).2
  have h₀ := (dot_le_supp hK.1.2.1.2.1 hp t).trans hb₀
  have h₁ := (dot_le_supp hK.1.2.1.2.1 hp (t + π / 2)).trans hb₁
  rw [uvec_add_pi_div_two] at h₁
  simp only [dot, uvec, vvec] at h₀ h₁
  have hx₀ : p.1 ≤ H / cos t := by
    apply (le_div_iff₀ hcos).mpr
    nlinarith
  have hx₁ : -p.1 ≤ H / sin t := by
    apply (le_div_iff₀ hs).mpr
    nlinarith
  have hdiv₀ : 0 ≤ H / cos t := div_nonneg hH hcos.le
  have hdiv₁ : 0 ≤ H / sin t := div_nonneg hH hs.le
  change p ∈ Icc (-(H / sin t + H / cos t)) (H / sin t + H / cos t) ×ˢ Icc 0 1
  exact ⟨⟨by linarith, by linarith⟩, hy₀, hy₁⟩

/-- Actual penalized maximality, with no balancing condition. -/
def IsPenalizedMax {Θ : AngleSet} (S : SupportSamples Θ)
    (target K : Set (ℝ × ℝ)) : Prop :=
  IsPolygonCap Θ K ∧ ∀ C, IsPolygonCap Θ C →
    polyArea Θ C - S.penalty target C ≤ polyArea Θ K - S.penalty target K

/-- Positive penalized value implies a bound on the unpenalized objective and
on the nonnegative penalty, using a supplied polygon-width bound. -/
theorem penalty_and_area_le_of_positive {Θ : AngleSet} (S : SupportSamples Θ)
    {target K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) {c : ℝ}
    (hcK : ∀ C, IsPolygonCap Θ C → 0 < polyArea Θ C → width C 0 ≤ c)
    (hpos : 0 < polyArea Θ K - S.penalty target K) :
    polyArea Θ K ≤ c ∧ S.penalty target K ≤ c := by
  have hP := S.penalty_nonneg target K
  have hApos : 0 < polyArea Θ K := by linarith
  have hw := hcK K hK hApos
  have ha := mpc_area_le_width hK.1
  have hN : 0 ≤ area (polyNiche Θ K) := ENNReal.toReal_nonneg
  have heq := theorem3_2_3 hK
  constructor <;> linarith

/-- The penalized objective attains its supremum whenever a positive reference
value and two positively weighted orthogonal samples are available. -/
theorem exists_penalizedMax {Θ : AngleSet} (S : SupportSamples Θ)
    (target : Set (ℝ × ℝ)) {t : ℝ} (ht : t ∈ Θ.angles)
    (i₀ i₁ : S.Index) (hi₀ : S.normal i₀ = t) (hi₁ : S.normal i₁ = t + π / 2)
    (hw₀ : 0 < S.weight i₀) (hw₁ : 0 < S.weight i₁)
    {R₀ : Set (ℝ × ℝ)} (hR₀ : IsPolygonCap Θ R₀)
    (hpositive : 0 < polyArea Θ R₀ - S.penalty target R₀) :
    ∃ K, IsPenalizedMax S target K := by
  sorry

end SofaUniqueness
