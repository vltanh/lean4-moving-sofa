module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Tactic

/-!
# UNCOMPILED DRAFT: the algebra and limit step of specified-maximizer selection

The cap-space compactness, finite-angle approximation, and local variation
arguments are NOT asserted by this abstract lemma. They must supply its explicit
hypotheses. The penalty uses upper supports only; a full-circle penalty does
not have the extreme-cell error estimate required by the paper.
-/

@[expose] public section

open Filter Topology

namespace SofaUniqueness.Draft

variable {X : Type*}

/-- Comparison with a recovery point gives the exact penalty bound.
Only positivity of lambda permits division; it must not be dropped. -/
theorem selection_penalty_bound
    (A An P : X → ℝ) (target chosen recovery : X) {e λ : ℝ}
    (hλ : 0 < λ)
    (hmax : A chosen ≤ A target)
    (hupper : An chosen ≤ A chosen + e)
    (hrecovery : A target ≤ An recovery)
    (hselect : An recovery - λ * P recovery ≤ An chosen - λ * P chosen) :
    P chosen ≤ P recovery + e / λ := by
  have hmul : λ * P chosen ≤ λ * P recovery + e := by linarith
  have hdiv : P chosen - P recovery ≤ e / λ := by
    apply (le_div_iff₀ hλ).mpr
    nlinarith [hmul]
  linarith

/-- Vanishing approximation error relative to lambda forces vanishing penalty.
No unpenalized argmax-selection assertion is used. -/
theorem selection_penalty_tendsto
    (A : X → ℝ) (An : ℕ → X → ℝ) (P : X → ℝ)
    (target : X) (chosen recovery : ℕ → X) (err weight : ℕ → ℝ)
    (hweight : ∀ n, 0 < weight n)
    (hnonneg : ∀ x, 0 ≤ P x)
    (hmax : ∀ n, A (chosen n) ≤ A target)
    (hupper : ∀ n, An n (chosen n) ≤ A (chosen n) + err n)
    (hrecovery : ∀ n, A target ≤ An n (recovery n))
    (hselect : ∀ n, An n (recovery n) - weight n * P (recovery n) ≤
      An n (chosen n) - weight n * P (chosen n))
    (hrec : Tendsto (fun n => P (recovery n)) atTop (𝓝 0))
    (herr : Tendsto (fun n => err n / weight n) atTop (𝓝 0)) :
    Tendsto (fun n => P (chosen n)) atTop (𝓝 0) := by
  have hb : ∀ n, P (chosen n) ≤ P (recovery n) + err n / weight n := by
    intro n
    exact selection_penalty_bound A (An n) P target (chosen n) (recovery n)
      (hweight n) (hmax n) (hupper n) (hrecovery n) (hselect n)
  have hlim : Tendsto (fun n => P (recovery n) + err n / weight n) atTop (𝓝 0) := by
    simpa using hrec.add herr
  exact squeeze_zero (fun n => hnonneg (chosen n)) hb hlim

/-- An isolated-zero penalty identifies every convergent subsequence once its
penalties tend to zero. Compactness is responsible for supplying subsequences. -/
theorem limit_eq_target_of_penalty
    [TopologicalSpace X] (P : X → ℝ) (target limit : X) (x : ℕ → X)
    (hcontinuous : Continuous P) (hzero : ∀ y, P y = 0 → y = target)
    (hx : Tendsto x atTop (𝓝 limit))
    (hpenalty : Tendsto (fun n => P (x n)) atTop (𝓝 0)) : limit = target := by
  apply hzero limit
  exact tendsto_nhds_unique ((hcontinuous.tendsto limit).comp hx) hpenalty

/-- Negative regression: each strictly positive linear approximation on [0,1]
has only the right endpoint as a maximizer. The zero limit has every point as a
maximizer, so exact approximating maximizers cannot select an arbitrary one. -/
theorem linear_approximation_unique_max {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hmax : ∀ y ∈ Set.Icc (0 : ℝ) 1, ε * y ≤ ε * x) : x = 1 := by
  have h := hmax 1 ⟨zero_le_one, le_rfl⟩
  nlinarith [hx.2]

/-- Per-facet errors proportional to the mesh give a bounded total coefficient.
The bound is deliberately not the false O(lambda/delta) accumulation. -/
theorem total_mesh_error (n : ℕ) (λ δ C L : ℝ)
    (hmesh : (n : ℝ) * δ = L) :
    (n : ℝ) * (C * λ * δ) = C * λ * L := by
  rw [← hmesh]
  ring

end SofaUniqueness.Draft
