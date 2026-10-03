module

public import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Lebesgue–Stieltjes measures (§5.1)

The paper's Lebesgue–Stieltjes measure `df` of a right-continuous function `f : [a, b] → E` of
bounded variation (Definition 5.1.3, `def:lebesgue-stieltjes`) is the unique finite signed measure
on `[a, b]` with `df({a}) = 0` and `df((a, t]) = f(t) - f(a)`.

We realise it with Mathlib's vector measure `BoundedVariationOn.vectorMeasure` of the function
`t ↦ f (max a (min b t))`, which agrees with `f` on `[a, b]` and is constant outside; that
function has bounded variation on `ℝ` exactly when `f` has bounded variation on `[a, b]`, and its
vector measure gives no mass to `{a}` and the mass `f t - f a` to `(a, t]`. Integrals against `df`
are Mathlib's vector-measure integrals `∫ᵛ`, with an explicit pairing (scalar multiplication, the
dot product, or the cross product).

## Corrections to the statements

* `lsMeasure_singleton_left` assumes, like the paper's Definition 5.1.3, that `f` is
  right-continuous on `[a, b)`: without it the statement is false (for `f = 1_{(0, ∞)}` on
  `[0, 1]` the clamped function jumps at `0`, so `df({0}) = 1`).
* `proposition5_1_4`: an absolutely continuous `f` has `df = r dt` with `r = f'` *integrable*, not
  necessarily bounded (`f = √·` on `[0, 1]` is absolutely continuous, but `df = (2√t)⁻¹ dt` has no
  bounded density). The density is therefore asked to be integrable on `[a, b]`; a bounded
  measurable density is in particular integrable there, which is how the paper uses the direction
  (2 ⇒ 1) (`absolutelyContinuousOnInterval_of_lsMeasure_eq`).
-/

@[expose] public section

open Set Filter MeasureTheory Topology

namespace MovingSofaOptimality

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

/-- The function `f` restricted to `[a, b]` and extended by constants outside. -/
def clampFun {α : Type*} (f : ℝ → α) (a b : ℝ) (t : ℝ) : α := f (max a (min b t))

open Classical in
/-- The Lebesgue–Stieltjes measure `df` of `f` on `[a, b]` (Definition 5.1.3,
`def:lebesgue-stieltjes`). It is meaningful when `f` has bounded variation on `[a, b]`; otherwise
it is defined as `0`. -/
noncomputable def lsMeasure (f : ℝ → E) (a b : ℝ) : VectorMeasure ℝ E :=
  if h : BoundedVariationOn (clampFun f a b) univ then h.vectorMeasure else 0

/-! ### The clamped function -/

lemma clampFun_of_mem {α : Type*} {f : ℝ → α} {a b t : ℝ} (ht : t ∈ Icc a b) :
    clampFun f a b t = f t := by
  simp [clampFun, ht.1, ht.2]

lemma clampFun_of_le {α : Type*} {f : ℝ → α} {a b t : ℝ} (ht : t ≤ a) :
    clampFun f a b t = f a := by
  simp [clampFun, min_le_of_right_le ht]

lemma clamp_mem {a b : ℝ} (hab : a ≤ b) (t : ℝ) : max a (min b t) ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

/-- `clampFun f a b` only depends on the values of `f` on `[a, b]`. -/
lemma clampFun_congr {α : Type*} {f g : ℝ → α} {a b : ℝ} (hab : a ≤ b) (h : EqOn f g (Icc a b)) :
    clampFun f a b = clampFun g a b :=
  funext fun t => h (clamp_mem hab t)

private lemma monotone_clamp (a b : ℝ) : Monotone (fun t : ℝ => max a (min b t)) :=
  fun _ _ h => max_le_max le_rfl (min_le_min le_rfl h)

private lemma continuous_clamp (a b : ℝ) : Continuous (fun t : ℝ => max a (min b t)) := by
  fun_prop

/-- The clamped function has bounded variation on `ℝ` when `f` has bounded variation on
`[a, b]`. -/
lemma boundedVariationOn_clampFun {F : Type*} [NormedAddCommGroup F] {f : ℝ → F} {a b : ℝ}
    (hab : a ≤ b) (hf : BoundedVariationOn f (Icc a b)) :
    BoundedVariationOn (clampFun f a b) univ := by
  have := eVariationOn.comp_le_of_monotoneOn f (fun t : ℝ => max a (min b t))
    ((monotone_clamp a b).monotoneOn univ) (fun t _ => clamp_mem hab t)
  exact ne_top_of_le_ne_top hf this

/-- The clamped function is right-continuous everywhere when `f` is right-continuous on `[a, b)`. -/
lemma continuousWithinAt_clampFun_Ici {α : Type*} [TopologicalSpace α] {f : ℝ → α} {a b : ℝ}
    (hab : a ≤ b) (hrc : ∀ x ∈ Ico a b, ContinuousWithinAt f (Ici x) x) (t : ℝ) :
    ContinuousWithinAt (clampFun f a b) (Ici t) t := by
  have hfφ : ContinuousWithinAt f (Icc a b ∩ Ici (max a (min b t))) (max a (min b t)) := by
    rcases (clamp_mem hab t).2.lt_or_eq with h | h
    · exact (hrc _ ⟨(clamp_mem hab t).1, h⟩).mono inter_subset_right
    · -- at `b` the set `[a, b] ∩ [b, ∞)` is `{b}`
      rw [h]
      exact continuousWithinAt_singleton.mono fun x hx => le_antisymm hx.1.2 hx.2
  exact ContinuousWithinAt.comp (f := fun t => max a (min b t)) hfφ
    (continuous_clamp a b).continuousWithinAt
    (fun x hx => ⟨clamp_mem hab x, monotone_clamp a b hx⟩)

/-- The clamped function is continuous when `f` is continuous on `[a, b]`. -/
lemma continuous_clampFun {α : Type*} [TopologicalSpace α] {f : ℝ → α} {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn f (Icc a b)) : Continuous (clampFun f a b) :=
  hc.comp_continuous (continuous_clamp a b) (clamp_mem hab)

lemma rightLim_clampFun {α : Type*} [TopologicalSpace α] [T2Space α] {f : ℝ → α} {a b : ℝ}
    (hab : a ≤ b) (hrc : ∀ x ∈ Ico a b, ContinuousWithinAt f (Ici x) x) (t : ℝ) :
    Function.rightLim (clampFun f a b) t = clampFun f a b t :=
  (continuousWithinAt_clampFun_Ici hab hrc t).rightLim_eq

lemma leftLim_clampFun {α : Type*} [TopologicalSpace α] [T2Space α] {f : ℝ → α} {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn f (Icc a b)) (t : ℝ) :
    Function.leftLim (clampFun f a b) t = clampFun f a b t :=
  (continuous_clampFun hab hc).continuousWithinAt.leftLim_eq

/-! ### Bounded variation and vector measures -/

/-- The variation is subadditive: `Var(f + g) ≤ Var(f) + Var(g)`. -/
lemma eVariationOn_add_le {α F : Type*} [LinearOrder α] [SeminormedAddCommGroup F]
    (f g : α → F) (s : Set α) :
    eVariationOn (fun x => f x + g x) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, ⟨u, u_mono, u_mem⟩⟩
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1)) + g (u (i + 1))) (f (u i) + g (u i))
    _ ≤ ∑ i ∈ Finset.range n,
        (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) :=
      Finset.sum_le_sum (fun i _ => edist_add_add_le _ _ _ _)
    _ = ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) +
        ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
      add_le_add (eVariationOn.sum_le u_mono u_mem) (eVariationOn.sum_le u_mono u_mem)

/-- A sum of functions of bounded variation has bounded variation. -/
lemma boundedVariationOn_add {α F : Type*} [LinearOrder α] [SeminormedAddCommGroup F]
    {f g : α → F} {s : Set α} (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (fun x => f x + g x) s :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hf, hg⟩) (eVariationOn_add_le f g s)

/-- A constant multiple of a function of bounded variation has bounded variation. -/
lemma boundedVariationOn_const_mul {α : Type*} [LinearOrder α] {f : α → ℝ} {s : Set α}
    (r : ℝ) (hf : BoundedVariationOn f s) : BoundedVariationOn (fun x => r * f x) s := by
  have hc : BoundedVariationOn (fun _ : α => r) s := by
    simp [BoundedVariationOn, eVariationOn.constant_on (f := fun _ : α => r)
      (s := s) (by simp [Set.Subsingleton])]
  exact hc.mul hf

/-- A Lipschitz function has bounded variation on every interval. -/
lemma boundedVariationOn_of_lipschitz {F : Type*} [PseudoEMetricSpace F] {f : ℝ → F} {L : NNReal}
    (hf : LipschitzWith L f) (a b : ℝ) : BoundedVariationOn f (Icc a b) := by
  have := hf.locallyBoundedVariationOn univ a b (mem_univ a) (mem_univ b)
  rwa [univ_inter] at this

/-- When the clamped function has bounded variation, `df` is its vector measure. -/
lemma lsMeasure_eq_vectorMeasure {f : ℝ → E} {a b : ℝ}
    (h : BoundedVariationOn (clampFun f a b) univ) : lsMeasure f a b = h.vectorMeasure := by
  simp [lsMeasure, h]

/-- The vector measure of a function of bounded variation depends only on the function. -/
lemma vectorMeasure_congr {f g : ℝ → E} (hfg : f = g) (hf : BoundedVariationOn f univ)
    (hg : BoundedVariationOn g univ) : hf.vectorMeasure = hg.vectorMeasure := by
  subst hfg; rfl

private lemma Icc_eq_iInter_Ioc (c d : ℝ) :
    Icc c d = ⋂ n : ℕ, Ioc (c - 1 / ((n : ℝ) + 1)) d := by
  ext x
  simp only [mem_Icc, mem_iInter, mem_Ioc]
  refine ⟨fun h n => ⟨by linarith [h.1, Nat.one_div_pos_of_nat (α := ℝ) (n := n)], h.2⟩,
    fun h => ⟨le_of_not_gt fun hx => ?_, (h 0).2⟩⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
  linarith [(h n).1]

private lemma antitone_Ioc (c d : ℝ) :
    Antitone (fun n : ℕ => Ioc (c - 1 / ((n : ℝ) + 1)) d) :=
  fun _ _ hmn => Ioc_subset_Ioc_left (by gcongr)

/-- Two vector measures on `ℝ` which agree on all intervals `(c, d]` are equal. -/
lemma vectorMeasure_ext_Ioc {F : Type*} [NormedAddCommGroup F] (μ ν : VectorMeasure ℝ F)
    (h : ∀ c d : ℝ, c < d → μ (Ioc c d) = ν (Ioc c d)) : μ = ν := by
  apply VectorMeasure.ext_of_Icc
  intro c d _
  rw [Icc_eq_iInter_Ioc]
  have hm : ∀ n : ℕ, MeasurableSet (Ioc (c - 1 / ((n : ℝ) + 1)) d) := fun _ => measurableSet_Ioc
  refine tendsto_nhds_unique
    (VectorMeasure.tendsto_vectorMeasure_iInter_atTop_nat (v := μ) (antitone_Ioc c d) hm) ?_
  have e : ∀ n : ℕ, μ (Ioc (c - 1 / ((n : ℝ) + 1)) d) = ν (Ioc (c - 1 / ((n : ℝ) + 1)) d) :=
    fun n => h _ _ (by linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := n)])
  simp_rw [e]
  exact VectorMeasure.tendsto_vectorMeasure_iInter_atTop_nat (v := ν) (antitone_Ioc c d) hm

/-! ### Definition 5.1.3 -/

/-- `df` gives no mass to the left endpoint (Definition 5.1.3). The paper's standing hypothesis
that `f` is right-continuous is needed: see the module docstring. -/
theorem lsMeasure_singleton_left {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hrc : ∀ x ∈ Ico a b, ContinuousWithinAt f (Ici x) x) :
    lsMeasure f a b {a} = 0 := by
  by_cases h : BoundedVariationOn (clampFun f a b) univ
  · have hl : ContinuousWithinAt (clampFun f a b) (Iic a) a := by
      have h1 : ContinuousWithinAt (fun _ : ℝ => f a) (Iic a) a := continuousWithinAt_const
      exact h1.congr (fun x hx => clampFun_of_le hx) (clampFun_of_le le_rfl)
    rw [lsMeasure_eq_vectorMeasure h, h.vectorMeasure_singleton, rightLim_clampFun hab hrc,
      hl.leftLim_eq, sub_self]
  · simp [lsMeasure, h]

/-- `df((a, t]) = f(t) - f(a)` for right-continuous `f` of bounded variation (Definition 5.1.3). -/
theorem lsMeasure_Ioc {f : ℝ → E} {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Icc a b)
    (hf : BoundedVariationOn f (Icc a b)) (hrc : ∀ x ∈ Ico a b, ContinuousWithinAt f (Ici x) x) :
    lsMeasure f a b (Ioc a t) = f t - f a := by
  have h := boundedVariationOn_clampFun hab hf
  rw [lsMeasure_eq_vectorMeasure h, h.vectorMeasure_Ioc ht.1, rightLim_clampFun hab hrc,
    rightLim_clampFun hab hrc, clampFun_of_mem ht, clampFun_of_mem ⟨le_rfl, hab⟩]

/-- `df((c, d]) = f(d) - f(c)` for `a ≤ c ≤ d ≤ b`. -/
lemma lsMeasure_Ioc_of_le {f : ℝ → E} {a b c d : ℝ} (hab : a ≤ b) (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b) (hf : BoundedVariationOn f (Icc a b))
    (hrc : ∀ x ∈ Ico a b, ContinuousWithinAt f (Ici x) x) :
    lsMeasure f a b (Ioc c d) = f d - f c := by
  have e : Ioc c d = Ioc a d \ Ioc a c := by
    ext x; simp only [mem_Ioc, Set.mem_sdiff, not_and, not_le]
    exact ⟨fun h => ⟨⟨hac.trans_lt h.1, h.2⟩, fun _ => h.1⟩, fun h => ⟨h.2 h.1.1, h.1.2⟩⟩
  rw [e, VectorMeasure.of_sdiff measurableSet_Ioc measurableSet_Ioc (Ioc_subset_Ioc_right hcd),
    lsMeasure_Ioc hab ⟨hac.trans hcd, hdb⟩ hf hrc, lsMeasure_Ioc hab ⟨hac, hcd.trans hdb⟩ hf hrc]
  abel

/-! ### Linearity -/

private lemma rightLim_lin {F G : ℝ → ℝ} (hF : BoundedVariationOn F univ)
    (hG : BoundedVariationOn G univ) (r s x : ℝ) :
    Function.rightLim (fun t => r * F t + s * G t) x =
      r * Function.rightLim F x + s * Function.rightLim G x :=
  rightLim_eq_of_tendsto (((hF.tendsto_rightLim x).const_mul r).add
    ((hG.tendsto_rightLim x).const_mul s))

private lemma leftLim_lin {F G : ℝ → ℝ} (hF : BoundedVariationOn F univ)
    (hG : BoundedVariationOn G univ) (r s x : ℝ) :
    Function.leftLim (fun t => r * F t + s * G t) x =
      r * Function.leftLim F x + s * Function.leftLim G x :=
  leftLim_eq_of_tendsto (((hF.tendsto_leftLim x).const_mul r).add
    ((hG.tendsto_leftLim x).const_mul s))

/-- **Proposition 5.1.1** (`pro:lebesgue-stieltjes-sum`). `d(rf + sg) = r df + s dg`. -/
theorem proposition5_1_1 {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hg : BoundedVariationOn g (Icc a b)) (r s : ℝ) :
    lsMeasure (fun t => r * f t + s * g t) a b = r • lsMeasure f a b + s • lsMeasure g a b := by
  have hF := boundedVariationOn_clampFun hab hf
  have hG := boundedVariationOn_clampFun hab hg
  have hH : BoundedVariationOn (clampFun (fun t => r * f t + s * g t) a b) univ :=
    boundedVariationOn_add (boundedVariationOn_const_mul r hF)
      (boundedVariationOn_const_mul s hG)
  rw [lsMeasure_eq_vectorMeasure hH, lsMeasure_eq_vectorMeasure hF, lsMeasure_eq_vectorMeasure hG]
  apply VectorMeasure.ext_of_Icc
  intro c d hcd
  rw [add_apply, smul_apply, smul_apply,
    hH.vectorMeasure_Icc hcd, hF.vectorMeasure_Icc hcd, hG.vectorMeasure_Icc hcd]
  have e : clampFun (fun t => r * f t + s * g t) a b =
      fun t => r * clampFun f a b t + s * clampFun g a b t := rfl
  rw [e, rightLim_lin hF hG, leftLim_lin hF hG, smul_eq_mul, smul_eq_mul]
  ring

/-! ### Integration by parts -/

private lemma lsmul_flip : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip =
    ContinuousLinearMap.lsmul ℝ ℝ := by
  ext
  simp

/-- **Lemma 5.1.2** (`lem:integration-by-parts`, Revuz–Yor Proposition 4.5). For right-continuous
`f, g` of bounded variation on `[a, b]`,
`∫_{(a,b]} g df + ∫_{(a,b]} f(t-) dg = f(b) g(b) - f(a) g(a)`. -/
theorem lemma5_1_2 {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hg : BoundedVariationOn g (Icc a b))
    (hfr : ∀ x ∈ Ico a b, ContinuousWithinAt f (Ici x) x)
    (hgr : ∀ x ∈ Ico a b, ContinuousWithinAt g (Ici x) x) :
    (∫ᵛ t in Ioc a b, g t ∂• lsMeasure f a b) +
      (∫ᵛ t in Ioc a b, Function.leftLim (clampFun f a b) t ∂• lsMeasure g a b) =
      f b * g b - f a * g a := by
  have hF := boundedVariationOn_clampFun hab hf
  have hG := boundedVariationOn_clampFun hab hg
  rw [lsMeasure_eq_vectorMeasure hF, lsMeasure_eq_vectorMeasure hG,
    BoundedVariationOn.setIntegral_Ioc_leftLim_smul_vectorMeasure_eq_sub hF hG hab,
    rightLim_clampFun hab hfr, rightLim_clampFun hab hfr, rightLim_clampFun hab hgr,
    rightLim_clampFun hab hgr, clampFun_of_mem ⟨hab, le_rfl⟩,
    clampFun_of_mem ⟨le_rfl, hab⟩, clampFun_of_mem ⟨hab, le_rfl⟩,
    clampFun_of_mem ⟨le_rfl, hab⟩, lsmul_flip]
  have : ∫ᵛ t in Ioc a b, g t ∂• hF.vectorMeasure =
      ∫ᵛ t in Ioc a b, Function.rightLim (clampFun g a b) t ∂• hF.vectorMeasure :=
    VectorMeasure.setIntegral_congr_fun fun x hx => by
      rw [rightLim_clampFun hab hgr, clampFun_of_mem ⟨hx.1.le, hx.2⟩]
  rw [this, smul_eq_mul, smul_eq_mul]
  abel

/-- **Lemma 5.1.3** (`lem:lebesgue-stieltjes-product`). If one of `f, g` is continuous, then
`d(fg) = g df + f dg` on `[a, b]`; stated on every Borel subset of `[a, b]`. -/
theorem lemma5_1_3 {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hg : BoundedVariationOn g (Icc a b))
    (hfr : ∀ x ∈ Ico a b, ContinuousWithinAt f (Ici x) x)
    (hgr : ∀ x ∈ Ico a b, ContinuousWithinAt g (Ici x) x)
    (hcont : ContinuousOn f (Icc a b) ∨ ContinuousOn g (Icc a b))
    {X : Set ℝ} (hXab : X ⊆ Icc a b) :
    lsMeasure (fun t => f t * g t) a b X =
      (∫ᵛ t in X, g t ∂• lsMeasure f a b) + (∫ᵛ t in X, f t ∂• lsMeasure g a b) := by
  have hF := boundedVariationOn_clampFun hab hf
  have hG := boundedVariationOn_clampFun hab hg
  have hFG := hF.bilinear_comp hG (ContinuousLinearMap.lsmul ℝ ℝ)
  have e : clampFun (fun t => f t * g t) a b =
      fun x => ContinuousLinearMap.lsmul ℝ ℝ (clampFun f a b x) (clampFun g a b x) := by
    ext x; simp [clampFun]
  have hH : BoundedVariationOn (clampFun (fun t => f t * g t) a b) univ := e ▸ hFG
  rw [lsMeasure_eq_vectorMeasure hH, vectorMeasure_congr e hH hFG, lsMeasure_eq_vectorMeasure hF,
    lsMeasure_eq_vectorMeasure hG]
  -- Mathlib's product rule, with the one-sided limits of the continuous factor equal to itself
  rcases hcont with hfc | hgc
  · rw [hF.vectorMeasure_bilinear_comp_eq hG, add_apply,
      VectorMeasure.withDensity_apply hG.rightLim.integrable,
      VectorMeasure.withDensity_apply hF.leftLim.integrable, lsmul_flip]
    congr 1 <;> refine VectorMeasure.setIntegral_congr_fun fun x hx => ?_
    · rw [rightLim_clampFun hab hgr, clampFun_of_mem (hXab hx)]
    · rw [leftLim_clampFun hab hfc, clampFun_of_mem (hXab hx)]
  · rw [hF.vectorMeasure_bilinear_comp_eq' hG, add_apply,
      VectorMeasure.withDensity_apply hG.leftLim.integrable,
      VectorMeasure.withDensity_apply hF.rightLim.integrable, lsmul_flip]
    congr 1 <;> refine VectorMeasure.setIntegral_congr_fun fun x hx => ?_
    · rw [leftLim_clampFun hab hgc, clampFun_of_mem (hXab hx)]
    · rw [rightLim_clampFun hab hfr, clampFun_of_mem (hXab hx)]

/-! ### Integration by parts against a Stieltjes function -/

/-- Integration by parts against the measure `dF` of a Stieltjes function `F`, for a `C¹`
function `g`: `∫_{(a, b]} g dF = F(b) g(b) - F(a) g(a) - ∫_a^b F g'`. -/
theorem integral_Ioc_stieltjes {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [CompleteSpace F'] (F : StieltjesFunction ℝ) {g g' : ℝ → F'} {a b : ℝ} (hab : a ≤ b)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g') :
    ∫ x in Ioc a b, g x ∂F.measure = F b • g b - F a • g a - ∫ x in a..b, F x • g' x := by
  -- write `g(x) = g(b) - ∫_x^b g'` and swap the two integrals (Fubini on `(a, b]²`, with the
  -- kernel `k(x, y) = 1_{x ≤ y} g'(y)`)
  set μ := F.measure.restrict (Ioc a b) with hμ
  set ν := (volume : Measure ℝ).restrict (Ioc a b) with hν
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hF : ∀ x, a ≤ x → F.measure.real (Ioc a x) = F x - F a := fun x hx => by
    rw [measureReal_def, F.measure_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 (F.mono hx))]
  have hftc : ∀ x y, ∫ z in x..y, g' z = g y - g x := fun x y =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hg z) (hg'.intervalIntegrable x y)
  set k : ℝ → ℝ → F' := fun x y => if x ≤ y then g' y else 0 with hk
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg'.continuousOn (s := Icc a b))
  have hkm : StronglyMeasurable (Function.uncurry k) :=
    StronglyMeasurable.ite (measurableSet_le measurable_fst measurable_snd)
      (hg'.comp continuous_snd).stronglyMeasurable stronglyMeasurable_const
  have hkint : Integrable (Function.uncurry k) (μ.prod ν) := by
    refine Integrable.of_bound hkm.aestronglyMeasurable C ?_
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)]
      with p hp
    simp only [Function.uncurry, hk]
    split_ifs
    · exact hC p.2 (Ioc_subset_Icc_self hp)
    · simpa using (norm_nonneg _).trans (hC p.2 (Ioc_subset_Icc_self hp))
  have h1 : ∀ x ∈ Ioc a b, g x = g b - ∫ y, k x y ∂ν := by
    intro x hx
    have e1 : (fun y => k x y) = (Ici x).indicator g' := by
      ext1 y; simp [hk, Set.indicator_apply]
    have e2 : Ioc a b ∩ Ici x = Icc x b := by
      ext y; simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hx.1.trans_le h.1, h.2⟩, h.1⟩⟩
    rw [hν, e1, setIntegral_indicator measurableSet_Ici, e2, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hx.2, hftc]
    abel
  have h2 : ∀ y ∈ Ioc a b, ∫ x, k x y ∂μ = (F y - F a) • g' y := by
    intro y hy
    have e1 : (fun x => k x y) = (Iic y).indicator (fun _ => g' y) := by
      ext1 x; simp [hk, Set.indicator_apply]
    rw [hμ, e1, setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, inf_eq_right.2 hy.2,
      setIntegral_const, hF y hy.1.le]
  have hi : IntervalIntegrable (fun x => F x • g' x) volume a b :=
    F.mono.intervalIntegrable.smul_continuousOn hg'.continuousOn
  calc ∫ x in Ioc a b, g x ∂F.measure
      = ∫ x, (g b - ∫ y, k x y ∂ν) ∂μ := setIntegral_congr_fun measurableSet_Ioc h1
    _ = ∫ x, g b ∂μ - ∫ x, ∫ y, k x y ∂ν ∂μ :=
        integral_sub (integrable_const _) hkint.integral_prod_left
    _ = (F b - F a) • g b - ∫ y, ∫ x, k x y ∂μ ∂ν := by
        rw [integral_const, integral_integral_swap hkint, hμ, measureReal_restrict_apply_univ,
          hF b hab]
    _ = (F b - F a) • g b - ∫ y in a..b, (F y • g' y - F a • g' y) := by
        rw [hν, setIntegral_congr_fun measurableSet_Ioc h2, intervalIntegral.integral_of_le hab]
        simp only [sub_smul]
    _ = _ := by
        rw [intervalIntegral.integral_sub (g := fun y => F a • g' y) hi
            ((hg'.const_smul (F a)).intervalIntegrable a b),
          intervalIntegral.integral_smul, hftc, sub_smul, smul_sub]
        abel

/-! ### Absolutely continuous functions -/

private lemma Iic_sdiff_Iic {c d : ℝ} : Iic d \ Iic c = Ioc c d := by
  ext x; simp only [Set.mem_sdiff, mem_Iic, not_le, mem_Ioc]; tauto

/-- A right-continuous `f` of bounded variation with `f t - f a = ∫_a^t r` on `[a, b]` has
`df = r dt`. -/
private lemma lsMeasure_eq_withDensityᵥ {f r : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hfr : ∀ x ∈ Ico a b, ContinuousWithinAt f (Ici x) x)
    (hr : IntegrableOn r (Icc a b))
    (hint : ∀ t ∈ Icc a b, f t - f a = ∫ x in a..t, r x) :
    lsMeasure f a b = (volume.restrict (Icc a b)).withDensityᵥ r := by
  have hF := boundedVariationOn_clampFun hab hf
  rw [lsMeasure_eq_vectorMeasure hF]
  have hν : ∀ x, (volume.restrict (Icc a b)).withDensityᵥ r (Iic x) = clampFun f a b x - f a := by
    intro x
    rw [withDensityᵥ_apply hr measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
    rcases lt_or_ge x a with hxa | hxa
    · have : Iic x ∩ Icc a b = ∅ := by
        ext y; simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2, -⟩; linarith
      rw [this, Measure.restrict_empty, integral_zero_measure, clampFun_of_le hxa.le, sub_self]
    · have hm : min x b ∈ Icc a b := ⟨le_min hxa hab, min_le_right _ _⟩
      have : Iic x ∩ Icc a b = Icc a (min x b) := by
        ext y; simp only [mem_inter_iff, mem_Iic, mem_Icc, le_min_iff]; tauto
      rw [this, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hm.1, ← hint _ hm]
      congr 1
      simp only [clampFun]
      rw [max_eq_right (le_min hab hxa), min_comm]
  apply vectorMeasure_ext_Ioc
  intro c d hcd
  rw [hF.vectorMeasure_Ioc hcd.le, rightLim_clampFun hab hfr, rightLim_clampFun hab hfr,
    ← Iic_sdiff_Iic, VectorMeasure.of_sdiff measurableSet_Iic measurableSet_Iic
      (Iic_subset_Iic.2 hcd.le), hν, hν]
  ring

/-- If `df = r dt`, then `f t - f a = ∫_a^t r` on `[a, b]`. -/
private lemma sub_eq_integral_of_lsMeasure_eq {f r : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hfr : ∀ x ∈ Ico a b, ContinuousWithinAt f (Ici x) x)
    (hr : IntegrableOn r (Icc a b))
    (h : lsMeasure f a b = (volume.restrict (Icc a b)).withDensityᵥ r) {t : ℝ}
    (ht : t ∈ Icc a b) :
    f t - f a = ∫ x in a..t, r x := by
  rw [← lsMeasure_Ioc hab ht hf hfr, h, withDensityᵥ_apply hr measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, intervalIntegral.integral_of_le ht.1,
    inter_eq_left.2 (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2))]

/-- A measurable function with `|r| ≤ C` is integrable on `[a, b]`. -/
private lemma integrableOn_Icc_of_abs_le {r : ℝ → ℝ} {a b C : ℝ} (hr : Measurable r)
    (hC : ∀ t, |r t| ≤ C) : IntegrableOn r (Icc a b) :=
  Measure.integrableOn_of_bounded (by simp) hr.aestronglyMeasurable (M := C)
    (Eventually.of_forall fun t => by simpa using hC t)

/-- **Proposition 5.1.4** (`pro:lebesgue-stieltjes-abs-cont`). A right-continuous `f` of bounded
variation on `[a, b]` is absolutely continuous iff `df = r dt` for a measurable `r` which is
integrable on `[a, b]`; then `f' = r` almost everywhere (see `proposition5_1_4_deriv`).
The paper asks `r` to be bounded, which is false in the direction (1 ⇒ 2): see the module
docstring. -/
theorem proposition5_1_4 {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hfr : ∀ x ∈ Ico a b, ContinuousWithinAt f (Ici x) x) :
    AbsolutelyContinuousOnInterval f a b ↔
      ∃ r : ℝ → ℝ, Measurable r ∧ IntegrableOn r (Icc a b) ∧
        lsMeasure f a b = (volume.restrict (Icc a b)).withDensityᵥ r := by
  constructor
  · intro hac
    have hi : IntegrableOn (deriv f) (Icc a b) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hac.intervalIntegrable_deriv
    refine ⟨deriv f, measurable_deriv f, hi, ?_⟩
    apply lsMeasure_eq_withDensityᵥ hab hf hfr hi
    intro t ht
    have hsub : uIcc a t ⊆ uIcc a b :=
      uIcc_subset_uIcc left_mem_uIcc (by rw [uIcc_of_le hab]; exact ht)
    rw [(hac.mono hsub).integral_deriv_eq_sub]
  · rintro ⟨r, -, hri, h⟩
    have hii : IntervalIntegrable r volume a b :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hri
    have hac : AbsolutelyContinuousOnInterval (fun x => f a + ∫ v in a..x, r v) a b :=
      ((LipschitzWith.const (f a)).lipschitzOnWith.absolutelyContinuousOnInterval).fun_add
        (hii.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
    refine hac.congr fun t ht => ?_
    rw [uIcc_of_le hab] at ht
    have := sub_eq_integral_of_lsMeasure_eq hab hf hfr hri h ht
    simp only
    linarith

/-- The direction (2 ⇒ 1) of Proposition 5.1.4 for a bounded measurable density, as used in the
paper. -/
theorem absolutelyContinuousOnInterval_of_lsMeasure_eq {f r : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hfr : ∀ x ∈ Ico a b, ContinuousWithinAt f (Ici x) x)
    (hr : Measurable r) (hrb : ∃ C, ∀ t, |r t| ≤ C)
    (h : lsMeasure f a b = (volume.restrict (Icc a b)).withDensityᵥ r) :
    AbsolutelyContinuousOnInterval f a b := by
  obtain ⟨C, hC⟩ := hrb
  exact (proposition5_1_4 hab hf hfr).2 ⟨r, hr, integrableOn_Icc_of_abs_le hr hC, h⟩

/-- **Proposition 5.1.4**, last claim: if `df = r dt` for a bounded measurable `r`, then `f' = r`
almost everywhere on `[a, b]`. -/
theorem proposition5_1_4_deriv {f r : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hfr : ∀ x ∈ Ico a b, ContinuousWithinAt f (Ici x) x)
    (hr : Measurable r) (hrb : ∃ C, ∀ t, |r t| ≤ C)
    (h : lsMeasure f a b = (volume.restrict (Icc a b)).withDensityᵥ r) :
    ∀ᵐ t ∂(volume.restrict (Icc a b)), HasDerivAt f (r t) t := by
  obtain ⟨C, hC⟩ := hrb
  have hri : IntegrableOn r (Icc a b) := integrableOn_Icc_of_abs_le hr hC
  have hii : IntervalIntegrable r volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hri
  -- at almost every `x ∈ (a, b)`, `f = f(a) + ∫_a^· r` near `x`, and this primitive has
  -- derivative `r x` (Lebesgue's differentiation theorem)
  have h₁ : ∀ᵐ x ∂volume, x ≠ a := by simp [ae_iff, measure_singleton]
  have h₂ : ∀ᵐ x ∂volume, x ≠ b := by simp [ae_iff, measure_singleton]
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hii.ae_hasDerivAt_integral, h₁, h₂] with x hx hxa hxb hxI
  have hxI' : x ∈ Ioo a b := ⟨lt_of_le_of_ne hxI.1 (Ne.symm hxa), lt_of_le_of_ne hxI.2 hxb⟩
  have hd := hx (by rwa [uIcc_of_le hab]) a left_mem_uIcc
  have heq : f =ᶠ[𝓝 x] (fun y => f a + ∫ t in a..y, r t) := by
    filter_upwards [Ioo_mem_nhds hxI'.1 hxI'.2] with y hy
    have := sub_eq_integral_of_lsMeasure_eq hab hf hfr hri h ⟨hy.1.le, hy.2.le⟩
    linarith
  exact (hd.const_add (f a)).congr_of_eventuallyEq heq

/-- **Proposition 5.1.4 as the paper states it is false.** With a *bounded* density, the
direction (1) ⇒ (2) fails: `f(t) = ∫₀ᵗ x^(-1/2) dx = 2√t` on `[0, 1]` is absolutely continuous,
right-continuous and of bounded variation, but `df` has no bounded density. `proposition5_1_4` is
the corrected statement, with an integrable density. -/
theorem proposition5_1_4_as_stated_false :
    ¬ (∀ (f : ℝ → ℝ) (a b : ℝ), a ≤ b → BoundedVariationOn f (Icc a b) →
      (∀ x ∈ Ico a b, ContinuousWithinAt f (Ici x) x) →
      (AbsolutelyContinuousOnInterval f a b ↔
        ∃ r : ℝ → ℝ, Measurable r ∧ (∃ C, ∀ t, |r t| ≤ C) ∧
          lsMeasure f a b = (volume.restrict (Icc a b)).withDensityᵥ r)) := by
  intro H
  -- the counterexample `f(t) = ∫₀ᵗ x^(-1/2) dx`, which is `2√t` for `t ≥ 0`
  let f : ℝ → ℝ := fun t => ∫ x in (0 : ℝ)..t, x ^ (-(1 / 2) : ℝ)
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) volume a b :=
    fun a b => intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hac : AbsolutelyContinuousOnInterval f 0 1 :=
    (hint 0 1).absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hbv : BoundedVariationOn f (Icc 0 1) := by
    simpa [uIcc_of_le zero_le_one] using hac.boundedVariationOn
  have hrc : ∀ x ∈ Ico (0 : ℝ) 1, ContinuousWithinAt f (Ici x) x :=
    fun x _ => (intervalIntegral.continuous_primitive hint 0).continuousWithinAt
  have hval : ∀ t, 0 ≤ t → f t = 2 * Real.sqrt t := by
    intro t ht
    simp only [f]
    rw [integral_rpow (Or.inl (by norm_num)), Real.zero_rpow (by norm_num), Real.sqrt_eq_rpow]
    norm_num
    ring
  -- by hypothesis `df = r dt` with `|r| ≤ C`, so `2√t = f(t) - f(0) = ∫₀ᵗ r ≤ C t` on `[0, 1]`
  obtain ⟨r, hrm, ⟨C, hC⟩, h⟩ := (H f 0 1 zero_le_one hbv hrc).1 hac
  have hri : IntegrableOn r (Icc 0 1) := integrableOn_Icc_of_abs_le hrm hC
  have hle : ∀ t ∈ Icc (0 : ℝ) 1, 2 * Real.sqrt t ≤ C * t := by
    intro t ht
    have hii : IntervalIntegrable r volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).2
        (hri.mono_set (Icc_subset_Icc_right ht.2))
    have := intervalIntegral.integral_mono_on ht.1 hii
      ((continuous_const : Continuous (fun _ : ℝ => C)).intervalIntegrable (μ := volume) 0 t)
      (fun x _ => (le_abs_self _).trans (hC x))
    rw [← sub_eq_integral_of_lsMeasure_eq zero_le_one hbv hrc hri h ht, hval t ht.1,
      hval 0 le_rfl, Real.sqrt_zero, mul_zero, sub_zero] at this
    simpa [mul_comm] using this
  -- this fails at `t = u²`, `u = 1 / (|C| + 1)`: `2 u ≤ C u² ≤ (|C| + 1) u² = u`
  set u := (|C| + 1)⁻¹
  have hu0 : 0 < u := by positivity
  have hu : (|C| + 1) * u = 1 := mul_inv_cancel₀ (by positivity)
  have hu1 : u ≤ 1 := inv_le_one_of_one_le₀ (by linarith [abs_nonneg C])
  have h1 := hle (u ^ 2) ⟨by positivity, by nlinarith⟩
  rw [Real.sqrt_sq hu0.le] at h1
  nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self C)) (sq_nonneg u)]

end MovingSofaOptimality
