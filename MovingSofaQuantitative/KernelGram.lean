module

public import MovingSofaQuantitative.EvaluationKernel
public import MovingSofaQuantitative.AugmentedGram

/-!
# Exact Gram algebra for the four residual arcs

Uncompiled proof source. These identities connect the finite kernel-piece
calculation to the continuum L2 vectors. In particular, an interval computation
of a Gram entry is not substituted for the integral without this bridge.
Closed endpoints have zero Lebesgue measure; an empty intersection contributes
zero and is never interpreted as a negatively oriented integral.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter
open scoped RealInnerProductSpace
open MovingSofaStability

namespace MovingSofaQuantitative

namespace FourKernel

variable {φ : ℝ}

theorem gram_symm (k l : FourKernel φ) : k.gram l = l.gram k := by
  rw [← inner_vectors, real_inner_comm, inner_vectors]

theorem gram_add_left (k l m : FourKernel φ) :
    (k.add l).gram m = k.gram m + l.gram m := by
  rw [← inner_vectors, vector_add, inner_add_left, inner_vectors, inner_vectors]

theorem gram_add_right (k l m : FourKernel φ) :
    k.gram (l.add m) = k.gram l + k.gram m := by
  rw [gram_symm, gram_add_left, gram_symm l k, gram_symm m k]

theorem gram_scale_left (a : ℝ) (k l : FourKernel φ) :
    (k.scale a).gram l = a * k.gram l := by
  rw [← inner_vectors, vector_scale, real_inner_smul_left, inner_vectors]

theorem gram_scale_right (a : ℝ) (k l : FourKernel φ) :
    k.gram (l.scale a) = a * k.gram l := by
  rw [gram_symm, gram_scale_left, gram_symm l k]

@[simp] theorem gram_zero_left (k : FourKernel φ) : zero.gram k = 0 := by
  rw [← inner_vectors, vector_zero, inner_zero_left]

@[simp] theorem gram_zero_right (k : FourKernel φ) : k.gram zero = 0 := by
  rw [gram_symm, gram_zero_left]

/-- A finite piece expansion is evaluated by the actual Hilbert inner product. -/
def sum : List (FourKernel φ) → FourKernel φ
  | [] => zero
  | k :: ks => k.add (sum ks)

theorem gram_sum_left (ks : List (FourKernel φ)) (l : FourKernel φ) :
    (sum ks).gram l = (ks.map fun k => k.gram l).sum := by
  induction ks with
  | nil => simp [sum]
  | cons k ks ih => simp [sum, gram_add_left, ih]

theorem gram_sum_right (k : FourKernel φ) (ls : List (FourKernel φ)) :
    k.gram (sum ls) = (ls.map fun l => k.gram l).sum := by
  induction ls with
  | nil => simp [sum]
  | cons l ls ih => simp [sum, gram_add_right, ih]

end FourKernel

/-- Different residual components are orthogonal, regardless of arc overlap. -/
theorem kernelAtom_gram_ne {φ : ℝ} {i j : Fin 4} (hij : i ≠ j)
    (a b c d : ℝ) (k l : ℝ → ℝ)
    (hk : ContinuousOn k (Icc a b)) (hl : ContinuousOn l (Icc c d)) :
    (kernelAtom φ i a b k hk).gram (kernelAtom φ j c d l hl) = 0 := by
  unfold FourKernel.gram kernelAtom
  apply Finset.sum_eq_zero
  intro m _
  by_cases hmi : m = i
  · subst m
    simp [hij]
  · simp [hmi]

/-- A product of two indicator pieces is the product restricted to their
intersection. This elementary identity does not require integrability. -/
theorem indicator_product_inter {a b c d : ℝ} (k l : ℝ → ℝ) :
    (fun u => (Icc a b).indicator k u * (Icc c d).indicator l u) =
      (Icc a b ∩ Icc c d).indicator (fun u => k u * l u) := by
  funext u
  by_cases h1 : u ∈ Icc a b <;> by_cases h2 : u ∈ Icc c d <;> simp [h1, h2]

/-- Exact same-component Gram entry as a set integral. The pieces are required
to lie in the actual residual arc, not merely in a numerical bounding box. -/
theorem kernelAtom_gram_same {φ : ℝ} (j : Fin 4) (a b c d : ℝ)
    (ha : residualStart φ j ≤ a) (hb : b ≤ residualEnd φ j)
    (hc : residualStart φ j ≤ c) (hd : d ≤ residualEnd φ j)
    (k l : ℝ → ℝ) (hk : ContinuousOn k (Icc a b)) (hl : ContinuousOn l (Icc c d)) :
    (kernelAtom φ j a b k hk).gram (kernelAtom φ j c d l hl) =
      ∫ u in Icc (max a c) (min b d), k u * l u := by
  unfold FourKernel.gram kernelAtom
  rw [Finset.sum_eq_single j]
  · simp only [if_true]
    rw [indicator_product_inter, integral_indicator (measurableSet_Icc.inter measurableSet_Icc),
      residualMeasure, Measure.restrict_restrict (measurableSet_Icc.inter measurableSet_Icc)]
    apply setIntegral_congr_set
    filter_upwards [ae_neq (residualStart φ j), ae_neq (residualEnd φ j)] with u hs he
    change ((u ∈ Icc a b ∧ u ∈ Icc c d) ∧
      u ∈ Ioo (residualStart φ j) (residualEnd φ j)) ↔ u ∈ Icc (max a c) (min b d)
    constructor
    · rintro ⟨⟨hu1, hu2⟩, _⟩
      exact ⟨max_le hu1.1 hu2.1, le_min hu1.2 hu2.2⟩
    · rintro ⟨hu1, hu2⟩
      have hua := (le_max_left a c).trans hu1
      have hub := hu2.trans (min_le_left b d)
      have huc := (le_max_right a c).trans hu1
      have hud := hu2.trans (min_le_right b d)
      exact ⟨⟨⟨hua, hub⟩, ⟨huc, hud⟩⟩,
        ⟨lt_of_le_of_ne (ha.trans hua) (Ne.symm hs),
          lt_of_le_of_ne (hub.trans hb) he⟩⟩
  · intro i _ hij
    simp [hij]
  · simp

/-- Empty overlap contributes zero; otherwise the familiar oriented integral
has increasing endpoints. This is the case distinction used by the checker. -/
theorem kernelAtom_gram_interval {φ : ℝ} (j : Fin 4) (a b c d : ℝ)
    (ha : residualStart φ j ≤ a) (hb : b ≤ residualEnd φ j)
    (hc : residualStart φ j ≤ c) (hd : d ≤ residualEnd φ j)
    (k l : ℝ → ℝ) (hk : ContinuousOn k (Icc a b)) (hl : ContinuousOn l (Icc c d)) :
    (kernelAtom φ j a b k hk).gram (kernelAtom φ j c d l hl) =
      if h : max a c ≤ min b d then ∫ u in (max a c)..(min b d), k u * l u else 0 := by
  rw [kernelAtom_gram_same j a b c d ha hb hc hd k l hk hl]
  split_ifs with h
  · rw [intervalIntegral.integral_of_le h, integral_Icc_eq_integral_Ioc]
  · rw [Icc_eq_empty (not_le.mp h)]
    simp

end MovingSofaQuantitative
