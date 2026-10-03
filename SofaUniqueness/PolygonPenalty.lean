module

public import MovingSofa.Balanced.MaximumPolygonCap
public import SofaUniqueness.VariationDefect

/-!
# Penalized stationarity for actual polygon caps

The area expansion is the existing Lemma 3.4.7, applied to arbitrary polygon
caps, not to maximizers. The comparison between assigned and actual supports
uses Proposition 3.3.7 in its proved direction. Therefore an unpenalized
balancedness theorem is never used for a penalized maximizer.

This module discharges the algebraic variational step. It does not manufacture
the feasible candidates or the mesh-uniform penalty-growth bounds; those
geometric inputs are explicit in the statements.
-/

@[expose] public section
noncomputable section

open Set Real MovingSofa

namespace SofaUniqueness

/-- The assigned-height objective after one outward height increment. -/
def assignedAreaIncrement (Θ : AngleSet) (K : Set (ℝ × ℝ)) (t ε : ℝ) : ℝ :=
  areaH Θ (Function.update (supp K) t (supp K t + ε))

@[simp] theorem assignedAreaIncrement_zero (Θ : AngleSet)
    (K : Set (ℝ × ℝ)) (t : ℝ) :
    assignedAreaIncrement Θ K t 0 = areaH Θ (supp K) := by
  classical
  have heq : Function.update (supp K) t (supp K t + 0) = supp K := by
    funext s
    by_cases hs : s = t
    · subst s
      simp
    · simp [hs]
  unfold assignedAreaIncrement
  rw [heq]

/-- Assigned supports can overestimate the niche. Thus the assigned objective
is bounded ABOVE by the actual normalized polygon objective. This is the
correct direction for obtaining a maximality contradiction. -/
theorem assigned_comparison_of_actual {Θ : AngleSet}
    {K C : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) (hC : IsPolygonCap Θ C)
    (height : ℝ → ℝ) (v : ℝ × ℝ)
    (hset : capH Θ height = (fun p => p + v) '' C)
    (P₀ Pε : ℝ)
    (hselect : polyArea Θ C - Pε ≤ polyArea Θ K - P₀) :
    areaH Θ height - Pε ≤ areaH Θ (supp K) - P₀ := by
  have htr : IsPolygonCapTranslate Θ (capH Θ height) := ⟨C, v, hC, hset⟩
  have hbound := proposition3_3_7 htr
  have hactual : areaT Θ (capH Θ height) = polyArea Θ C := by
    rw [hset]
    exact (theorem3_3_6 hC v).2
  have hbase : areaH Θ (supp K) = polyArea Θ K := (proposition3_3_5 hK).2
  rw [hactual] at hbound
  rw [hbase]
  linarith

/-- Outward polygon defect bounded by a one-sided penalty-growth coefficient.
No derivative of the normalization map is assumed: a quadratic upper bound on
the actual penalty change is sufficient, including for pinned-strip moves. -/
theorem polygon_defect_le_penalty_growth {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {t : ℝ} (ht : t ∈ Θ.diamond)
    (P : ℝ → ℝ) {ε₀ b D : ℝ} (hε₀ : 0 < ε₀)
    (hP : ∀ ε ∈ Ioc (0 : ℝ) ε₀, P ε - P 0 ≤ b * ε + D * ε ^ 2)
    (hcompare : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      assignedAreaIncrement Θ K t ε - P ε ≤ areaH Θ (supp K) - P 0) :
    sigmaAt K t - tau Θ K t ≤ b := by
  obtain ⟨r, hr, C, hC⟩ := lemma3_4_7 hK ht
  have hsmall : 0 < min r ε₀ := lt_min hr hε₀
  have hd : sigmaAt K t - tau Θ K t - b ≤ 0 :=
    le_zero_of_mul_le_sq (C := C + D) hsmall (by
      intro ε hε
      have he₁ : ε ∈ Ioc (0 : ℝ) r :=
        ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
      have he₂ : ε ∈ Ioc (0 : ℝ) ε₀ :=
        ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
      have ha := (abs_le.mp (hC ε he₁)).1
      have hp := hP ε he₂
      have hm := hcompare ε he₂
      unfold assignedAreaIncrement at hm
      nlinarith)
  linarith

/-- A zero-length outer facet needs no feasible outward perturbation:
nonnegativity of the completed inner-boundary length already controls it. -/
theorem polygon_defect_le_of_zero_facet {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    {t b : ℝ} (hσ : sigmaAt K t = 0) (hb : 0 ≤ b) :
    sigmaAt K t - tau Θ K t ≤ b := by
  have hτ : 0 ≤ tau Θ K t := tsum_nonneg (fun c => ENNReal.toReal_nonneg)
  rw [hσ]
  linarith

/-- Separate the degenerate facet from the actual variation argument.
The nondegenerate branch must provide its own feasible-candidate comparison. -/
theorem polygon_defect_le {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {t b : ℝ} (ht : t ∈ Θ.diamond) (hb : 0 ≤ b)
    (hpositive : 0 < sigmaAt K t →
      ∃ (P : ℝ → ℝ) (ε₀ D : ℝ), 0 < ε₀ ∧
        (∀ ε ∈ Ioc (0 : ℝ) ε₀, P ε - P 0 ≤ b * ε + D * ε ^ 2) ∧
        ∀ ε ∈ Ioc (0 : ℝ) ε₀,
          assignedAreaIncrement Θ K t ε - P ε ≤ areaH Θ (supp K) - P 0) :
    sigmaAt K t - tau Θ K t ≤ b := by
  by_cases hpos : 0 < sigmaAt K t
  · obtain ⟨P, ε₀, D, hε₀, hP, hc⟩ := hpositive hpos
    exact polygon_defect_le_penalty_growth hK ht P hε₀ hP hc
  · have hσ : sigmaAt K t = 0 :=
      le_antisymm (le_of_not_gt hpos) ENNReal.toReal_nonneg
    exact polygon_defect_le_of_zero_facet hσ hb

end SofaUniqueness
