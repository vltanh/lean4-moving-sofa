module

public import MovingSofaUniqueness.Curvature.CurvatureRegularity

/-!
# Injectivity from curvature bounds for the specified cap

The operator comparison below is simultaneous in the two arm functions. It
never assumes that the cap is balanced or replaces it by its mirror's chosen
maximizer. Only the two integrated inequalities and nonnegativity are used.

For the final strict threshold we reuse the existing analytic Lemma 6.5.5.
Its finite induction consists of real integral inequalities and rational
algebraic proofs, not a Boolean evaluation or a decision procedure. The
alternative maximum-deficit argument of the notes is not needed here.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

/-- The lower sequence bounds both arms without any cap-specific hypothesis.
The opposite endpoint conventions are kept throughout the induction. -/
theorem lowerSeq_le_of_integral_bounds {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 (π / 2))) (hg : ContinuousOn g (Icc 0 (π / 2)))
    (hf0 : ∀ t ∈ Icc (0 : ℝ) (π / 2), 0 ≤ f t)
    (hg0 : ∀ t ∈ Icc (0 : ℝ) (π / 2), 0 ≤ g t)
    (hfi : ∀ t ∈ Ico (0 : ℝ) (π / 2),
      (∫ u in (0 : ℝ)..t, m0 (g u)) ≤ f t - 1)
    (hgi : ∀ t ∈ Ioc (0 : ℝ) (π / 2),
      (∫ u in t..(π / 2), m0 (f u)) ≤ g t - 1) :
    ∀ n : ℕ,
      (∀ t ∈ Ico (0 : ℝ) (π / 2), lowerSeq n t ≤ f t) ∧
      (∀ t ∈ Ioc (0 : ℝ) (π / 2), lowerSeq n (π / 2 - t) ≤ g t) := by
  intro n
  induction n with
  | zero =>
    exact ⟨fun t ht => hf0 t ⟨ht.1, ht.2.le⟩,
      fun t ht => hg0 t ⟨ht.1.le, ht.2⟩⟩
  | succ n ih =>
    constructor
    · intro t ht
      change max (lowerSeq n t) (lowerOp (lowerSeq n) t) ≤ f t
      apply max_le (ih.1 t ht)
      have hseq : IntervalIntegrable
          (fun u => m0 (lowerSeq n (π / 2 - u))) volume 0 t :=
        (inj_continuous_m0.comp ((inj_continuous_lowerSeq n).comp
          (continuous_const.sub continuous_id))).intervalIntegrable _ _
      have hgint : IntervalIntegrable (fun u => m0 (g u)) volume 0 t := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le ht.1]
        exact inj_continuous_m0.comp_continuousOn
          (hg.mono (Icc_subset_Icc le_rfl ht.2.le))
      have hi := intervalIntegral.integral_mono_on_of_le_Ioo ht.1 hseq hgint
        (fun u hu => inj_m0_mono (ih.2 u ⟨hu.1, hu.2.le.trans ht.2.le⟩))
      have hb := hfi t ht
      unfold lowerOp
      linarith
    · intro t ht
      change max (lowerSeq n (π / 2 - t))
        (lowerOp (lowerSeq n) (π / 2 - t)) ≤ g t
      apply max_le (ih.2 t ht)
      have hseq : IntervalIntegrable (fun u => m0 (lowerSeq n u))
          volume t (π / 2) :=
        (inj_continuous_m0.comp (inj_continuous_lowerSeq n)).intervalIntegrable _ _
      have hfint : IntervalIntegrable (fun u => m0 (f u)) volume t (π / 2) := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le ht.2]
        exact inj_continuous_m0.comp_continuousOn
          (hf.mono (Icc_subset_Icc ht.1.le le_rfl))
      have hi := intervalIntegral.integral_mono_on_of_le_Ioo ht.2 hseq hfint
        (fun u hu => inj_m0_mono (ih.1 u ⟨ht.1.le.trans hu.1.le, hu.2⟩))
      have hb := hgi t ht
      rw [lowerOp, intervalIntegral.integral_comp_sub_left (fun u => m0 (lowerSeq n u)),
        sub_sub_cancel, sub_zero]
      linarith

/-- Strict interior arm inequalities follow from the given curvature bounds. -/
theorem arms_strict_of_curvature {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2))
    (hfirst : FirstCurvatureBound K) (hsecond : SecondCurvatureBound K) :
    ∀ t ∈ Ioo (0 : ℝ) (π / 2), 1 < fK K t ∧ 1 < gK K t := by
  have h1 := injCond1_of_curvature hfirst hsecond
  obtain ⟨_, _, hfc, hgc⟩ := proposition6_4_6_continuous hK h1
  have hseq := lowerSeq_le_of_integral_bounds hfc hgc
    (fun t _ => (inj_arm_nonneg hK.2.1 t).2.1)
    (fun t _ => (inj_arm_nonneg hK.2.1 t).2.2.1)
    (fun t ht => first_arm_integral_lower hK h1 hfirst ht)
    (fun t ht => second_arm_integral_lower hK h1 hsecond ht) 11
  intro t ht
  refine ⟨(lemma6_5_5 ⟨ht.1, ht.2.le⟩).trans_le (hseq.1 t ⟨ht.1.le, ht.2⟩), ?_⟩
  exact (lemma6_5_5 ⟨by linarith [ht.2], by linarith [ht.1]⟩).trans_le
    (hseq.2 t ⟨ht.1, ht.2.le⟩)

/-- Proposition 3: the specified cap satisfies all three injectivity conditions.
No global maximality or balancedness hypothesis is present. -/
theorem injectivity_of_curvature {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2))
    (hfirst : FirstCurvatureBound K) (hsecond : SecondCurvatureBound K) :
    SatisfiesInjectivity K := by
  have h1 := injCond1_of_curvature hfirst hsecond
  obtain ⟨hx, _, hder⟩ := proposition6_4_6_deriv hK h1
  have harms := arms_strict_of_curvature hK hfirst hsecond
  refine ⟨h1, hx, fun t ht => ?_⟩
  have hd := (hder t ⟨ht.1.le, ht.2.le⟩).1.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  rw [hd.deriv]
  simp only [dot_add_left, dot_smul_left, dot_uvec_self, dot_vvec_uvec,
    dot_uvec_vvec, dot_vvec_self]
  obtain ⟨hf, hg⟩ := harms t ht
  constructor <;> linarith

end MovingSofaUniqueness
