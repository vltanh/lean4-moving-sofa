module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith

/-!
# Select a specified maximizer with a fixed centered penalty

A fixed penalty is enough. Let A_n be the finite objectives, M the value of the
specified continuum maximizer, and P a nonnegative continuous penalty vanishing
only at that maximizer. For penalized maximizers x_n and recovery points r_n,

  M - P(r_n) <= A_n(x_n) - P(x_n).

If x_n tends to x, P(r_n) tends to zero, and limsup A_n(x_n) <= A(x) <= M,
then P(x)=0. No uniform convergence of A_n is needed, and no sequence of
weights or error/weight division is needed. Geometric compactness and the
limsup estimate remain explicit inputs: they are not supplied by this lemma.

For a squared support penalty its first variation also tends to zero as the
selected support functions approach the target. See `QuadraticPenalty`.

Uncompiled, admission-free source proofs.
-/

@[expose] public section

open Filter Topology Set

namespace SofaUniqueness

/-- The scalar limiting comparison, formulated without an unnecessary limit
of the finite objective itself. Only its one-sided upper bound is used. -/
theorem penalty_limit_le_deficit
    (finiteValue selectedPenalty recoveryPenalty : ℕ → ℝ)
    (M limitValue limitPenalty : ℝ)
    (hselect : ∀ n, M - recoveryPenalty n ≤ finiteValue n - selectedPenalty n)
    (hrecovery : Tendsto recoveryPenalty atTop (𝓝 0))
    (hpenalty : Tendsto selectedPenalty atTop (𝓝 limitPenalty))
    (hupper : ∀ ε > 0, ∀ᶠ n in atTop, finiteValue n ≤ limitValue + ε) :
    limitPenalty ≤ limitValue - M := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hthird : (0 : ℝ) < ε / 3 := by linarith
  have hrec : ∀ᶠ n in atTop, recoveryPenalty n < ε / 3 :=
    hrecovery.eventually (Iio_mem_nhds hthird)
  have hpen : ∀ᶠ n in atTop, limitPenalty - ε / 3 < selectedPenalty n :=
    hpenalty.eventually (Ioi_mem_nhds (by linarith))
  obtain ⟨n, hn⟩ := ((hupper (ε / 3) hthird).and (hrec.and hpen)).exists
  have hs := hselect n
  rcases hn with ⟨hu, hr, hp⟩
  linarith

/-- A globally maximal limit value forces the centered penalty to be zero. -/
theorem penalty_limit_eq_zero
    (finiteValue selectedPenalty recoveryPenalty : ℕ → ℝ)
    (M limitValue limitPenalty : ℝ)
    (hnonneg : 0 ≤ limitPenalty) (hmax : limitValue ≤ M)
    (hselect : ∀ n, M - recoveryPenalty n ≤ finiteValue n - selectedPenalty n)
    (hrecovery : Tendsto recoveryPenalty atTop (𝓝 0))
    (hpenalty : Tendsto selectedPenalty atTop (𝓝 limitPenalty))
    (hupper : ∀ ε > 0, ∀ᶠ n in atTop, finiteValue n ≤ limitValue + ε) :
    limitPenalty = 0 := by
  have h := penalty_limit_le_deficit finiteValue selectedPenalty recoveryPenalty
    M limitValue limitPenalty hselect hrecovery hpenalty hupper
  linarith

/-- Apply the limiting comparison to a specified convergent subsequence of
penalized maximizers. The sequence index may already encode a subsequence. -/
theorem fixedPenalty_limit_eq_target {X : Type*} [TopologicalSpace X]
    (A P : X → ℝ) (An : ℕ → X → ℝ)
    (target limit : X) (chosen recovery : ℕ → X)
    (hP : Continuous P) (hPnonneg : ∀ x, 0 ≤ P x)
    (hPzero : ∀ x, P x = 0 → x = target)
    (hmax : A limit ≤ A target)
    (hrecoveryValue : ∀ n, A target ≤ An n (recovery n))
    (hselect : ∀ n, An n (recovery n) - P (recovery n) ≤
      An n (chosen n) - P (chosen n))
    (hrecovery : Tendsto (fun n => P (recovery n)) atTop (𝓝 0))
    (hchosen : Tendsto chosen atTop (𝓝 limit))
    (hupper : ∀ ε > 0, ∀ᶠ n in atTop, An n (chosen n) ≤ A limit + ε) :
    limit = target := by
  apply hPzero limit
  apply penalty_limit_eq_zero (fun n => An n (chosen n))
    (fun n => P (chosen n)) (fun n => P (recovery n))
    (A target) (A limit) (P limit) (hPnonneg limit) hmax
  · intro n
    have h₁ := hrecoveryValue n
    have h₂ := hselect n
    linarith
  · exact hrecovery
  · exact (hP.tendsto limit).comp hchosen
  · exact hupper

/-- No uniform approximation estimate is hidden in the elementary selection
comparison. The finite objective at the recovery point need only be a lower
bound for the desired value. -/
theorem fixedPenalty_comparison {M ar ax pr px : ℝ}
    (hrecovery : M ≤ ar) (hmax : ar - pr ≤ ax - px) : M - pr ≤ ax - px := by
  linarith

end SofaUniqueness
