module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import MovingSofaOptimality.Balanced.MaximumPolygonCap
public import MovingSofaUniqueness.Selection
public import MovingSofaOptimality.Angle.HorizontalSide
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Proposition 2: variations of the selected polygons

Raising one defining height of a penalized maximizer, or moving one of its two pinned strips,
bounds the defect between the edge length `σ` and the polygon quantity `τ` by the change of the
penalty (`floating_defect_le`, `pinned_defect_le`, inequalities (11) and (12) of note 20). Along the
selected sequence these defects vanish, which gives the pinned bounds (19) for the limit cap
(`pinned_bounds_of_maximal_positive`).
-/

@[expose] public section
noncomputable section

/-!
## Quantitative stationarity without assuming balancedness

A one-sided quadratic expansion and penalized maximality bound the outward
first variation. A finite weighted endpoint identity then controls both signs
of a pinned defect. These are the algebraic steps needed for a specified
maximizer, whose approximating polygons are not unpenalized maxima.

All feasibility, area-expansion and penalty-expansion hypotheses are visible.
No existence or geometric regularity claim is hidden in these lemmas.
-/

section

open Set
open scoped BigOperators

namespace MovingSofaUniqueness

/-- A strictly positive first-order term cannot be bounded by a quadratic
remainder at every sufficiently small positive increment. -/
theorem le_zero_of_mul_le_sq {d C ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (h : ∀ ε ∈ Ioc (0 : ℝ) ε₀, d * ε ≤ C * ε ^ 2) : d ≤ 0 := by
  by_contra hnot
  have hd : 0 < d := lt_of_not_ge hnot
  let ε := min ε₀ (d / (2 * (|C| + 1)))
  have hC : 0 < |C| + 1 := by positivity
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hεle : ε ≤ ε₀ := min_le_left _ _
  have hεd : ε ≤ d / (2 * (|C| + 1)) := min_le_right _ _
  have hm : ε * (2 * (|C| + 1)) ≤ d :=
    (le_div_iff₀ (by positivity)).mp hεd
  have hbound := h ε ⟨hε, hεle⟩
  have habs : C ≤ |C| := le_abs_self C
  have hsmall : C * ε ^ 2 < d * ε := by
    nlinarith [mul_pos hε hε]
  exact (not_lt_of_ge hbound) hsmall

/-- If signed defects sum to zero with nonnegative weights, their one-sided
upper bounds also control their negative parts. Crucially the denominator
below is the pinned weight, never a small extreme-cell sine. -/
theorem abs_weighted_defect_le {ι : Type*} (s : Finset ι)
    (w d e : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (he : ∀ i ∈ s, 0 ≤ e i) (hd : ∀ i ∈ s, d i ≤ e i)
    (hsum : (∑ i ∈ s, w i * d i) = 0) {k : ι} (hk : k ∈ s) :
    |w k * d k| ≤ ∑ i ∈ s, w i * e i := by
  classical
  have heach := Finset.single_le_sum (s := s) (f := fun i => w i * e i)
    (fun i hi => mul_nonneg (hw i hi) (he i hi)) hk
  have hgap := Finset.single_le_sum (s := s)
    (f := fun i => w i * (e i - d i))
    (fun i hi => mul_nonneg (hw i hi) (sub_nonneg.mpr (hd i hi))) hk
  simp_rw [mul_sub] at hgap
  rw [Finset.sum_sub_distrib, hsum, sub_zero] at hgap
  have hnonneg : 0 ≤ w k * e k := mul_nonneg (hw k hk) (he k hk)
  have hupper : w k * d k ≤ w k * e k :=
    mul_le_mul_of_nonneg_left (hd k hk) (hw k hk)
  rw [abs_le]
  constructor <;> linarith

/-- Quantitative pinned-facet estimate obtained from the endpoint identity. -/
theorem abs_defect_le_div {ι : Type*} (s : Finset ι)
    (w d e : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (he : ∀ i ∈ s, 0 ≤ e i) (hd : ∀ i ∈ s, d i ≤ e i)
    (hsum : (∑ i ∈ s, w i * d i) = 0) {k : ι} (hk : k ∈ s)
    (hwk : 0 < w k) : |d k| ≤ (∑ i ∈ s, w i * e i) / w k := by
  have h := abs_weighted_defect_le s w d e hw he hd hsum hk
  rw [abs_mul, abs_of_pos hwk] at h
  apply (le_div_iff₀ hwk).mpr
  simpa only [mul_comm] using h

end MovingSofaUniqueness

end

/-!
## Penalized stationarity for actual polygon caps

The area expansion is the existing Lemma 3.4.7, applied to arbitrary polygon
caps, not to maximizers. The comparison between assigned and actual supports
uses Proposition 3.3.7 in its proved direction. Therefore an unpenalized
balancedness theorem is never used for a penalized maximizer.

This module discharges the algebraic variational step. It does not manufacture
the feasible candidates or the mesh-uniform penalty-growth bounds; those
geometric inputs are explicit in the statements.
-/

section

open Set Real MovingSofaOptimality

namespace MovingSofaUniqueness

/-- The assigned-height objective after one outward height increment. -/
def assignedAreaIncrement (Θ : AngleSet) (K : Set (ℝ × ℝ)) (t ε : ℝ) : ℝ :=
  areaH Θ (Function.update (supp K) t (supp K t + ε))

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

end MovingSofaUniqueness

end

/-!
## Floating-facet variations of the actual selected polygons

Raising a non-pinned defining height preserves every other sampled actual
support. The changed actual support lies between its old height and the new
assigned height. These two elementary facts, not an unproved support-hat
formula, give the penalty bound needed for stationarity.

The conclusion holds even for a zero-length floating facet. No unpenalized
maximality, balancedness, or geometric regularity is assumed.
-/

section

open Set Real MovingSofaOptimality

namespace MovingSofaUniqueness

/-- The actual outward-perturbed cap. -/
def floatingCap (Θ : AngleSet) (K : Set (ℝ × ℝ)) (t ε : ℝ) : Set (ℝ × ℝ) :=
  capH Θ (Function.update (supp K) t (supp K t + ε))

theorem floatingCap_polygon {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {t ε : ℝ} (htω : t ≠ Θ.ω) (htL : t ≠ π / 2)
    (hε : 0 ≤ ε) : IsPolygonCap Θ (floatingCap Θ K t ε) :=
  mpc_capH_update_inner hK htω htL hε

@[simp] theorem floatingCap_zero {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (t : ℝ) : floatingCap Θ K t 0 = K := by
  classical
  have heq : Function.update (supp K) t (supp K t + 0) = supp K := by
    funext s
    by_cases hs : s = t
    · subst s
      simp
    · simp [hs]
  unfold floatingCap
  rw [heq]
  exact proposition3_3_4 ⟨K, 0, hK, by simp⟩

/-- Every old point satisfies the relaxed upper constraint; the two lower
strip constraints are unchanged. -/
theorem subset_floatingCap {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {t ε : ℝ} (htω : t ≠ Θ.ω) (htL : t ≠ π / 2)
    (hε : 0 ≤ ε) : K ⊆ floatingCap Θ K t ε := by
  classical
  intro p hp
  change p ∈ capH Θ (Function.update (supp K) t (supp K t + ε))
  rw [mpc_mem_capH]
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have h := dot_le_supp hK.1.2.1.2.1 hp s
    by_cases hst : s = t
    · subst s
      rw [Function.update_self]
      linarith
    · rw [Function.update_of_ne hst]
      exact h
  · rw [Function.update_of_ne htω.symm, hK.1.2.2.1]
    simpa only [sub_self] using (mpc_cap_nonneg hK.1 hp).2
  · rw [Function.update_of_ne htL.symm, hK.1.2.2.2.1]
    simpa only [sub_self, mpc_dot_uvec_pi_div_two] using (mpc_cap_nonneg hK.1 hp).1

/-- At every defining normal, the old actual support is a lower bound and the
new assigned height is an upper bound for the perturbed actual support. -/
theorem floatingCap_support_bounds {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {t ε s : ℝ}
    (htω : t ≠ Θ.ω) (htL : t ≠ π / 2) (hε : 0 ≤ ε) (hs : s ∈ Θ.diamond) :
    supp K s ≤ supp (floatingCap Θ K t ε) s ∧
      supp (floatingCap Θ K t ε) s ≤ Function.update (supp K) t (supp K t + ε) s := by
  have hC := floatingCap_polygon hK htω htL hε
  constructor
  · exact supp_mono (subset_floatingCap hK htω htL hε) hK.1.2.1.1 hC.1.2.1.2.1 s
  · apply nef_supp_le hC.1.2.1.1
    intro p hp
    change p ∈ capH Θ (Function.update (supp K) t (supp K t + ε)) at hp
    rw [mpc_mem_capH] at hp
    exact hp.1 s hs

/-- No unsampled-direction estimate is necessary for this selector. -/
theorem floatingCap_support_other {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {t ε s : ℝ}
    (htω : t ≠ Θ.ω) (htL : t ≠ π / 2) (hε : 0 ≤ ε)
    (hs : s ∈ Θ.diamond) (hst : s ≠ t) :
    supp (floatingCap Θ K t ε) s = supp K s := by
  have h := floatingCap_support_bounds hK htω htL hε hs
  rw [Function.update_of_ne hst] at h
  exact le_antisymm h.2 h.1

theorem floatingCap_support_self {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {t ε : ℝ}
    (ht : t ∈ Θ.diamond) (htω : t ≠ Θ.ω) (htL : t ≠ π / 2) (hε : 0 ≤ ε) :
    |supp (floatingCap Θ K t ε) t - supp K t| ≤ ε := by
  have h := floatingCap_support_bounds hK htω htL hε ht
  rw [Function.update_self] at h
  rw [abs_of_nonneg (sub_nonneg.mpr h.1)]
  linarith

/-- Exact one-sided penalty growth for an outward floating move. -/
theorem floating_penalty_growth {Θ : AngleSet} (S : SupportSamples Θ)
    {target K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) {t η ε : ℝ}
    (ht : t ∈ Θ.diamond) (htω : t ≠ Θ.ω) (htL : t ≠ π / 2)
    (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hclose : ∀ i, |supp K (S.normal i) - supp target (S.normal i)| ≤ η) :
    S.penalty target (floatingCap Θ K t ε) - S.penalty target K ≤
      (2 * η * S.atNormal t) * ε + S.atNormal t * ε ^ 2 := by
  have h := S.penalty_change_one (ε := ε) hη hclose
    (fun i hi => floatingCap_support_other hK htω htL hε (S.normal_mem i) hi)
    (fun i hi => by rw [hi]; exact floatingCap_support_self hK ht htω htL hε)
  have hu := (abs_le.mp h).2
  nlinarith

/-- The actual stationarity estimate for selected polygons. Total sample mass,
not the number of finest-mesh normals, controls the sum of these errors. -/
theorem floating_defect_le {Θ : AngleSet} (S : SupportSamples Θ)
    {target K : Set (ℝ × ℝ)} (hK : IsPenalizedMax S target K) {t η : ℝ}
    (ht : t ∈ Θ.diamond) (htω : t ≠ Θ.ω) (htL : t ≠ π / 2)
    (hη : 0 ≤ η)
    (hclose : ∀ i, |supp K (S.normal i) - supp target (S.normal i)| ≤ η) :
    sigmaAt K t - tau Θ K t ≤ 2 * η * S.atNormal t := by
  let P : ℝ → ℝ := fun ε => S.penalty target (floatingCap Θ K t ε)
  apply polygon_defect_le_penalty_growth hK.1 ht P (ε₀ := 1)
    (D := S.atNormal t) (by norm_num)
  · intro ε hε
    dsimp only [P]
    rw [floatingCap_zero hK.1]
    exact floating_penalty_growth S hK.1 ht htω htL hη hε.1.le hclose
  · intro ε hε
    have hC := floatingCap_polygon hK.1 htω htL hε.1.le
    have hcomp := hK.2 (floatingCap Θ K t ε) hC
    have h := assigned_comparison_of_actual hK.1 hC
      (Function.update (supp K) t (supp K t + ε)) (0 : ℝ × ℝ)
      (by simp [floatingCap]) (S.penalty target K)
      (S.penalty target (floatingCap Θ K t ε)) hcomp
    simpa only [assignedAreaIncrement, P, floatingCap_zero hK.1] using h

end MovingSofaUniqueness

end

/-!
## Uniform control of the structured pinned-strip move

For omega<pi/2 a standard cap contains O and its top corner o. Raising either
pinned height by epsilon simultaneously moves the corresponding lower strip.
For 0<=epsilon<=1 the resulting assigned cap K' satisfies

  (1-epsilon) K + epsilon o subset K' subset (1+epsilon) K.

This specific sandwich, rather than a false general diameter-to-height
perturbation estimate, gives a mesh-independent support bound. Feasibility as
a translated polygon cap is supplied by the existing Lemma 3.4.8. Width one
then determines the normalization translation directly.
-/

section

open Set Real MovingSofaOptimality

namespace MovingSofaUniqueness

/-- The assigned height at a pinned normal before subtracting the unit width. -/
theorem pinned_support_value {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {s : ℝ} (hs : s = Θ.ω ∨ s = π / 2) : supp K s = 1 := by
  rcases hs with rfl | rfl
  · exact hK.1.2.2.1
  · exact hK.1.2.2.2.1

/-- Both scalar products of the common top corner with the pinned normals
are exactly one. -/
theorem pinned_corner_dot {Θ : AngleSet} {s : ℝ}
    (hs : s = Θ.ω ∨ s = π / 2) : dot (oPt Θ.ω) (uvec s) = 1 := by
  rcases hs with rfl | rfl
  · exact mpc_oPt_dot_uvec Θ.hω
  · rw [mpc_dot_uvec_pi_div_two, mpc_oPt_snd]

/-- The common origin makes every upper support nonnegative. -/
theorem pinned_support_nonneg {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) (s : ℝ) : 0 ≤ supp K s := by
  have h := dot_le_supp hK.1.2.1.2.1 (ang_cap_origin_mem hK.1 hω) s
  simpa [dot] using h

/-- Contracting toward the common top corner produces points of the moved
assigned cap. The statement covers both distinct pinned normals. -/
theorem pinned_contract_mem {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) {t ε : ℝ}
    (ht : t = Θ.ω ∨ t = π / 2) (hε : ε ∈ Icc (0 : ℝ) 1)
    {p : ℝ × ℝ} (hp : p ∈ K) :
    (1 - ε) • p + ε • oPt Θ.ω ∈ floatingCap Θ K t ε := by
  classical
  have ho := mpc_oPt_mem hK hω
  have hcombo : (1 - ε) • p + ε • oPt Θ.ω ∈ K :=
    hK.1.2.1.2.2 hp ho (by linarith [hε.2]) hε.1 (by ring)
  change _ ∈ capH Θ (Function.update (supp K) t (supp K t + ε))
  rw [mpc_mem_capH]
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have h := dot_le_supp hK.1.2.1.2.1 hcombo s
    by_cases hst : s = t
    · subst s
      rw [Function.update_self]
      linarith [hε.1]
    · rw [Function.update_of_ne hst]
      exact h
  · by_cases hst : Θ.ω = t
    · subst hst
      rw [Function.update_self, pinned_support_value hK ht]
      have hp0 : 0 ≤ dot p (uvec Θ.ω) := (mpc_cap_nonneg hK.1 hp).2
      rw [dot_add_left, dot_smul_left, dot_smul_left, pinned_corner_dot ht]
      nlinarith [hε.2]
    · rw [Function.update_of_ne hst, hK.1.2.2.1]
      have h := (mpc_cap_nonneg hK.1 hcombo).2
      simpa only [sub_self] using h
  · by_cases hst : π / 2 = t
    · subst hst
      rw [Function.update_self, pinned_support_value hK ht]
      have hp0 : 0 ≤ dot p (uvec (π / 2)) := by
        rw [mpc_dot_uvec_pi_div_two]
        exact (mpc_cap_nonneg hK.1 hp).1
      rw [dot_add_left, dot_smul_left, dot_smul_left, pinned_corner_dot ht]
      nlinarith [hε.2]
    · rw [Function.update_of_ne hst, hK.1.2.2.2.1]
      have h := (mpc_cap_nonneg hK.1 hcombo).1
      simpa only [sub_self, mpc_dot_uvec_pi_div_two] using h

/-- Contracting the moved assigned cap toward the common origin by
1/(1+epsilon) puts it back in the original cap. -/
theorem pinned_div_mem {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) {t ε : ℝ}
    (ht : t = Θ.ω ∨ t = π / 2) (hε : 0 ≤ ε)
    {p : ℝ × ℝ} (hp : p ∈ floatingCap Θ K t ε) :
    (1 / (1 + ε)) • p ∈ K := by
  classical
  have hden : 0 < 1 + ε := by linarith
  change p ∈ capH Θ (Function.update (supp K) t (supp K t + ε)) at hp
  rw [mpc_mem_capH] at hp
  rw [mpc_polycap_mem_iff hK]
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have hu := hp.1 s hs
    rw [dot_smul_left, one_div, inv_mul_eq_div, div_le_iff₀ hden]
    by_cases hst : s = t
    · subst s
      rw [Function.update_self, pinned_support_value hK ht] at hu
      rw [pinned_support_value hK ht]
      nlinarith
    · rw [Function.update_of_ne hst] at hu
      have hnonneg := pinned_support_nonneg hK hω s
      nlinarith
  · have hlo : 0 ≤ dot p (uvec Θ.ω) := by
      have h := hp.2.1
      by_cases hst : Θ.ω = t
      · subst hst
        rw [Function.update_self, pinned_support_value hK ht] at h
        linarith
      · rw [Function.update_of_ne hst, hK.1.2.2.1] at h
        linarith
    show 0 ≤ dot ((1 / (1 + ε)) • p) (uvec Θ.ω)
    rw [dot_smul_left]
    exact mul_nonneg (by positivity) hlo
  · have hlo : 0 ≤ dot p (uvec (π / 2)) := by
      have h := hp.2.2
      by_cases hst : π / 2 = t
      · subst hst
        rw [Function.update_self, pinned_support_value hK ht] at h
        linarith
      · rw [Function.update_of_ne hst, hK.1.2.2.2.1] at h
        linarith
    show 0 ≤ dot ((1 / (1 + ε)) • p) (uvec (π / 2))
    rw [dot_smul_left]
    exact mul_nonneg (by positivity) hlo

/-- A bounded-support consequence of the structured contraction sandwich.
It is independent of the number or spacing of polygon normals. -/
theorem pinned_raw_support_bound {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) {t ε R : ℝ}
    (ht : t = Θ.ω ∨ t = π / 2) (hε : ε ∈ Icc (0 : ℝ) 1)
    (hR : 0 ≤ R) (hsupp : ∀ s, |supp K s| ≤ R) (s : ℝ) :
    |supp (floatingCap Θ K t ε) s - supp K s| ≤ 2 * R * ε := by
  have hcpt : IsCompact (floatingCap Θ K t ε) := mpc_isCompact_capH Θ _
  obtain ⟨q, hq, hqs⟩ := exists_dot_eq_supp hK.1.2.1.2.1 hK.1.2.1.1 s
  have hmem := pinned_contract_mem hK hω ht hε hq
  have hne : (floatingCap Θ K t ε).Nonempty := ⟨_, hmem⟩
  have hupper : supp (floatingCap Θ K t ε) s ≤ (1 + ε) * supp K s := by
    apply nef_supp_le hne
    intro p hp
    have h := dot_le_supp hK.1.2.1.2.1 (pinned_div_mem hK hω ht hε.1 hp) s
    rw [dot_smul_left, one_div, inv_mul_eq_div, div_le_iff₀ (by linarith [hε.1] : 0 < 1 + ε)] at h
    nlinarith
  have hlower := dot_le_supp hcpt hmem s
  rw [dot_add_left, dot_smul_left, dot_smul_left, hqs] at hlower
  have ho := mpc_oPt_mem hK hω
  have hodot : -R ≤ dot (oPt Θ.ω) (uvec s) := by
    have h := dot_le_supp hK.1.2.1.2.1 ho (s + π)
    rw [mpc_dot_uvec_add_pi] at h
    have hb := (abs_le.mp (hsupp (s + π))).2
    linarith
  have hKs := abs_le.mp (hsupp s)
  rw [abs_le]
  constructor <;> nlinarith [hε.1]

/-- An actual width-one translated cap fitting between the assigned two strip
bounds has exactly those two supports: there is no hidden strip slack. -/
theorem translated_strip_support {Θ : AngleSet} {C : Set (ℝ × ℝ)}
    (hC : IsPolygonCap Θ C) (v : ℝ × ℝ) {s a : ℝ}
    (hs : s = Θ.ω ∨ s = π / 2)
    (hlo : ∀ p ∈ (fun q => q + v) '' C, a ≤ dot p (uvec s))
    (hhi : ∀ p ∈ (fun q => q + v) '' C, dot p (uvec s) ≤ a + 1) :
    dot v (uvec s) = a := by
  have hc := hC.1.2.1
  have htop : supp C s = 1 := pinned_support_value hC hs
  have hbot : supp C (s + π) = 0 := by
    rcases hs with rfl | rfl
    · exact hC.1.2.2.2.2.1
    · rw [show π / 2 + π = 3 * π / 2 by ring]
      exact hC.1.2.2.2.2.2.1
  obtain ⟨p, hp, hps⟩ := exists_dot_eq_supp hc.2.1 hc.1 s
  obtain ⟨q, hq, hqs⟩ := exists_dot_eq_supp hc.2.1 hc.1 (s + π)
  rw [htop] at hps
  rw [hbot, mpc_dot_uvec_add_pi] at hqs
  have hu := hhi (p + v) ⟨p, hp, rfl⟩
  have hl := hlo (q + v) ⟨q, hq, rfl⟩
  rw [dot_add_left, hps] at hu
  rw [dot_add_left] at hl
  linarith

/-- The normalization displacement of a pinned move has uniformly controlled
scalar products. The denominator cos(omega) is fixed, not a mesh sine. -/
theorem pinned_translation_bound {Θ : AngleSet} {K C : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hC : IsPolygonCap Θ C) (hω : Θ.ω < π / 2)
    {t ε : ℝ} (ht : t = Θ.ω ∨ t = π / 2) (hε : 0 ≤ ε)
    (v : ℝ × ℝ) (hset : floatingCap Θ K t ε = (fun p => p + v) '' C) (s : ℝ) :
    |dot v (uvec s)| ≤ (2 / cos Θ.ω + 1) * ε := by
  classical
  have hcos : 0 < cos Θ.ω :=
    cos_pos_of_mem_Ioo ⟨by linarith [Θ.hω.1, pi_pos], hω⟩
  have hsin : 0 ≤ sin Θ.ω := sin_nonneg_of_nonneg_of_le_pi Θ.hω.1.le
    (by linarith [hω, pi_pos])
  let a : ℝ → ℝ := fun r => Function.update (supp K) t (supp K t + ε) r - 1
  have ha : ∀ r, (r = Θ.ω ∨ r = π / 2) → a r ∈ Icc (0 : ℝ) ε := by
    intro r hr
    dsimp [a]
    by_cases hrt : r = t
    · subst r
      rw [Function.update_self, pinned_support_value hK ht]
      constructor <;> linarith
    · rw [Function.update_of_ne hrt, pinned_support_value hK hr]
      constructor <;> linarith
  have hv : ∀ r, (r = Θ.ω ∨ r = π / 2) → dot v (uvec r) = a r := by
    intro r hr
    apply translated_strip_support hC v hr
    · intro p hp
      rw [← hset] at hp
      change p ∈ capH Θ (Function.update (supp K) t (supp K t + ε)) at hp
      rw [mpc_mem_capH] at hp
      rcases hr with rfl | rfl
      · exact hp.2.1
      · exact hp.2.2
    · intro p hp
      rw [← hset] at hp
      change p ∈ capH Θ (Function.update (supp K) t (supp K t + ε)) at hp
      rw [mpc_mem_capH] at hp
      have hrd : r ∈ Θ.diamond := by
        rcases hr with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      have h := hp.1 r hrd
      dsimp [a]
      linarith
  have hy := ha (π / 2) (Or.inr rfl)
  have hx := ha Θ.ω (Or.inl rfl)
  rw [← hv (π / 2) (Or.inr rfl), mpc_dot_uvec_pi_div_two] at hy
  rw [← hv Θ.ω (Or.inl rfl)] at hx
  have hyabs : |v.2| ≤ ε := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
  have hxy : |v.1| ≤ 2 * ε / cos Θ.ω := by
    rw [le_div_iff₀ hcos]
    simp only [dot, uvec] at hx
    have hs := sin_le_one Θ.ω
    have hprod : v.2 * sin Θ.ω ≤ ε := by nlinarith [hy.1, hy.2]
    rw [← abs_of_pos hcos, ← abs_mul, abs_le]
    constructor <;> nlinarith [hx.1, hx.2, hy.1]
  have hdot := mpc_abs_dot_uvec_le v s
  have hbound : |v.1| + |v.2| ≤ (2 / cos Θ.ω + 1) * ε := by
    have heq : 2 * ε / cos Θ.ω + ε = (2 / cos Θ.ω + 1) * ε := by ring
    rw [← heq]
    exact add_le_add hxy hyabs
  exact hdot.trans hbound

/-- Uniform support error AFTER normalization to the original two strips. -/
theorem pinned_normalized_support_bound {Θ : AngleSet} {K C : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hC : IsPolygonCap Θ C) (hω : Θ.ω < π / 2)
    {t ε R : ℝ} (ht : t = Θ.ω ∨ t = π / 2) (hε : ε ∈ Icc (0 : ℝ) 1)
    (hR : 0 ≤ R) (hsupp : ∀ s, |supp K s| ≤ R)
    (v : ℝ × ℝ) (hset : floatingCap Θ K t ε = (fun p => p + v) '' C) (s : ℝ) :
    |supp C s - supp K s| ≤ (2 * R + 2 / cos Θ.ω + 1) * ε := by
  have hraw := pinned_raw_support_bound hK hω ht hε hR hsupp s
  have hv := pinned_translation_bound hK hC hω ht hε.1 v hset s
  have heq : supp (floatingCap Θ K t ε) s = supp C s + dot v (uvec s) := by
    rw [hset]
    exact supp_translate C v s hC.1.2.1.2.1 hC.1.2.1.1
  rw [heq] at hraw
  have htri := abs_sub (supp C s + dot v (uvec s) - supp K s) (dot v (uvec s))
  have halg : supp C s + dot v (uvec s) - supp K s - dot v (uvec s) =
      supp C s - supp K s := by ring
  rw [halg] at htri
  nlinarith

end MovingSofaUniqueness

end

/-!
## Pinned stationarity and the endpoint balance identity

The structured strip sandwich controls the selected penalty after the actual
normalization supplied by Lemma 3.4.8. The positive pinned defect is therefore
O(eta), where eta is the uniform support distance to the target. The outer and
completed inner boundary walks have the same horizontal displacement. Their
weighted defect sum is zero, so the negative pinned defect is controlled too.
-/

section

open Set Real MovingSofaOptimality
open scoped BigOperators

namespace MovingSofaUniqueness

/-- The outward pinned defect for an actual selected polygon. -/
theorem pinned_defect_le {Θ : AngleSet} (S : SupportSamples Θ)
    {target K : Set (ℝ × ℝ)} (hK : IsPenalizedMax S target K)
    (hω : Θ.ω < π / 2) {t η R : ℝ} (ht : t = Θ.ω ∨ t = π / 2)
    (hη : 0 ≤ η) (hR : 0 ≤ R) (hsupp : ∀ s, |supp K s| ≤ R)
    (hclose : ∀ i, |supp K (S.normal i) - supp target (S.normal i)| ≤ η) :
    sigmaAt K t - tau Θ K t ≤
      2 * S.totalWeight * η * (2 * R + 2 / cos Θ.ω + 1) := by
  classical
  let G := 2 * R + 2 / cos Θ.ω + 1
  have hcos : 0 < cos Θ.ω :=
    cos_pos_of_mem_Ioo ⟨by linarith [Θ.hω.1, pi_pos], hω⟩
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have htd : t ∈ Θ.diamond := by
    rcases ht with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  by_cases hσ : 0 < sigmaAt K t
  · obtain ⟨r, hr, hfeasible⟩ := lemma3_4_8 hK.1 htd hσ
    let r' := min r 1
    have hr' : 0 < r' := lt_min hr zero_lt_one
    have hC : ∀ e : Ioc (0 : ℝ) r', ∃ C v, IsPolygonCap Θ C ∧
        floatingCap Θ K t e.1 = (fun p => p + v) '' C := by
      intro e
      exact hfeasible e.1 ⟨e.2.1, e.2.2.trans (min_le_left _ _)⟩
    choose C v hCp hset using hC
    let chosen : ℝ → Set (ℝ × ℝ) := fun ε =>
      if he : ε ∈ Ioc (0 : ℝ) r' then C ⟨ε, he⟩ else K
    let P : ℝ → ℝ := fun ε => S.penalty target (chosen ε)
    have hchosen0 : chosen 0 = K := by simp [chosen]
    apply polygon_defect_le_penalty_growth hK.1 htd P hr'
      (D := S.totalWeight * G ^ 2)
    · intro ε he
      have hε : ε ∈ Icc (0 : ℝ) 1 :=
        ⟨he.1.le, he.2.trans (min_le_right _ _)⟩
      have hgrowth := S.penalty_change_uniform hη hclose
        (fun i => pinned_normalized_support_bound hK.1 (hCp ⟨ε, he⟩)
          hω ht hε hR hsupp (v ⟨ε, he⟩) (hset ⟨ε, he⟩) (S.normal i))
      dsimp only [P]
      rw [hchosen0, show chosen ε = C ⟨ε, he⟩ from dite_eq_left he]
      have h := (abs_le.mp hgrowth).2
      dsimp [G] at h ⊢
      nlinarith
    · intro ε he
      have hcompare := hK.2 (C ⟨ε, he⟩) (hCp ⟨ε, he⟩)
      have h := assigned_comparison_of_actual hK.1 (hCp ⟨ε, he⟩)
        (Function.update (supp K) t (supp K t + ε)) (v ⟨ε, he⟩)
        (hset ⟨ε, he⟩) (S.penalty target K) (S.penalty target (C ⟨ε, he⟩)) hcompare
      dsimp only [P]
      rw [hchosen0, show chosen ε = C ⟨ε, he⟩ from dite_eq_left he]
      exact h
  · have hz : sigmaAt K t = 0 := le_antisymm (le_of_not_gt hσ) ENNReal.toReal_nonneg
    apply polygon_defect_le_of_zero_facet hz
    change 0 ≤ 2 * S.totalWeight * η * G
    have hw := S.totalWeight_nonneg
    positivity

/-- The weighted signed defect identity holds for every polygon cap. -/
theorem polygon_weighted_defect_zero {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) :
    (∑ t ∈ mpcDiamond Θ, sin t * (sigmaAt K t - tau Θ K t)) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  simp_rw [mul_comm (sin _)]
  rw [mpc_sum_sigma_sin hK, mpc_sum_tau_sin hK, sub_self]

/-- Total error controlling every defect of the actual sampled selector. -/
def selectorDefectBound {Θ : AngleSet} (S : SupportSamples Θ) (G η t : ℝ) : ℝ := by
  classical
  exact 2 * η * S.atNormal t +
    if t = Θ.ω ∨ t = π / 2 then 2 * S.totalWeight * η * G else 0

theorem selectorDefectBound_nonneg {Θ : AngleSet} (S : SupportSamples Θ)
    {G η : ℝ} (hG : 0 ≤ G) (hη : 0 ≤ η) (t : ℝ) :
    0 ≤ selectorDefectBound S G η t := by
  classical
  have hw := S.atNormal_nonneg t
  have hW := S.totalWeight_nonneg
  unfold selectorDefectBound
  split_ifs <;> positivity

/-- At most two pinned normals contribute a normalization error. -/
theorem selectorDefectBound_sum_le {Θ : AngleSet} (S : SupportSamples Θ)
    {G η : ℝ} (hG : 0 ≤ G) (hη : 0 ≤ η) :
    (∑ t ∈ mpcDiamond Θ, selectorDefectBound S G η t) ≤
      2 * η * S.totalWeight + 4 * S.totalWeight * η * G := by
  classical
  let b := 2 * S.totalWeight * η * G
  have hb : 0 ≤ b := by
    have hW := S.totalWeight_nonneg
    dsimp [b]
    positivity
  have hpin : (∑ t ∈ mpcDiamond Θ, if t = Θ.ω ∨ t = π / 2 then b else 0) ≤ 2 * b := by
    calc
      (∑ t ∈ mpcDiamond Θ, if t = Θ.ω ∨ t = π / 2 then b else 0)
          ≤ ∑ t ∈ mpcDiamond Θ, ((if t = Θ.ω then b else 0) + (if t = π / 2 then b else 0)) := by
        apply Finset.sum_le_sum
        intro t ht
        split_ifs <;> simp_all
      _ ≤ 2 * b := by
        rw [Finset.sum_add_distrib]
        have h₀ : (∑ t ∈ mpcDiamond Θ, if t = Θ.ω then b else 0) ≤ b := by
          by_cases h : Θ.ω ∈ mpcDiamond Θ <;> simp [h, hb]
        have h₁ : (∑ t ∈ mpcDiamond Θ, if t = π / 2 then b else 0) ≤ b := by
          by_cases h : π / 2 ∈ mpcDiamond Θ <;> simp [h, hb]
        linarith
  unfold selectorDefectBound
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, S.sum_atNormal]
  dsimp [b] at hpin
  linarith

/-- Two-sided control of any specified upper-normal defect. Only its own
positive sine appears in the denominator, so this is uniform at fixed pins. -/
theorem abs_selected_defect_le {Θ : AngleSet} (S : SupportSamples Θ)
    {target K : Set (ℝ × ℝ)} (hK : IsPenalizedMax S target K)
    (hω : Θ.ω < π / 2) {η R : ℝ} (hη : 0 ≤ η) (hR : 0 ≤ R)
    (hsupp : ∀ s, |supp K s| ≤ R)
    (hclose : ∀ i, |supp K (S.normal i) - supp target (S.normal i)| ≤ η)
    {t : ℝ} (ht : t ∈ Θ.diamond) :
    |sigmaAt K t - tau Θ K t| ≤
      (2 * η * S.totalWeight +
        4 * S.totalWeight * η * (2 * R + 2 / cos Θ.ω + 1)) / sin t := by
  classical
  let G := 2 * R + 2 / cos Θ.ω + 1
  have hcos : 0 < cos Θ.ω :=
    cos_pos_of_mem_Ioo ⟨by linarith [Θ.hω.1, pi_pos], hω⟩
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have herror : ∀ s ∈ mpcDiamond Θ,
      sigmaAt K s - tau Θ K s ≤ selectorDefectBound S G η s := by
    intro s hs
    have hsd := mpc_mem_mpcDiamond.mp hs
    by_cases hpin : s = Θ.ω ∨ s = π / 2
    · have h := pinned_defect_le S hK hω hpin hη hR hsupp hclose
      have hnonneg : 0 ≤ 2 * η * S.atNormal s := by
        have hw := S.atNormal_nonneg s
        positivity
      simp only [selectorDefectBound, ite_eq_left hpin]
      exact h.trans (le_add_of_nonneg_left hnonneg)
    · have hnot := not_or.mp hpin
      simpa only [selectorDefectBound, ite_eq_right hpin, add_zero] using
        floating_defect_le S hK hsd hnot.1 hnot.2 hη hclose
  have h := abs_defect_le_div (mpcDiamond Θ) sin
    (fun s => sigmaAt K s - tau Θ K s) (selectorDefectBound S G η)
    (fun s hs => (mpc_sin_pos_of_diamond (mpc_mem_mpcDiamond.mp hs)).le)
    (fun s _ => selectorDefectBound_nonneg S hG hη s) herror
    (polygon_weighted_defect_zero hK.1) (mpc_mem_mpcDiamond.mpr ht)
    (mpc_sin_pos_of_diamond ht)
  have hsum : (∑ s ∈ mpcDiamond Θ, sin s * selectorDefectBound S G η s) ≤
      2 * η * S.totalWeight + 4 * S.totalWeight * η * G := by
    calc
      _ ≤ ∑ s ∈ mpcDiamond Θ, selectorDefectBound S G η s := by
        apply Finset.sum_le_sum
        intro s hs
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (sin_le_one s)
          (selectorDefectBound_nonneg S hG hη s)
      _ ≤ _ := selectorDefectBound_sum_le S hG hη
  exact h.trans (div_le_div_of_nonneg_right hsum (mpc_sin_pos_of_diamond ht).le)

end MovingSofaUniqueness

end

/-!
## Pinned bounds for the specified continuum maximizer

The polygon inequalities here are w<=tau and z<=tau. They are valid before
balancedness and are not the balanced-polygon Theorem 4.1.2. The selected
polygons have vanishing signed pinned defects; upper semicontinuity of a fixed
edge length then gives the desired inequalities for their specified limit.

Positive sofa-area is stated because it supplies the compact selector. In the
shape-uniqueness application it follows from the already proved lower bound
on Gerver's area, not from any additional assumption on the starting sofa.
-/

section

open Set Real Filter Topology MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

/-- The completed inner boundary, not the outer top edge, is bounded below
by the right gap before any maximality or stationarity argument is used. -/
theorem polygon_wedgeGapW_le_tau {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) :
    wedgeGapWInf K Θ.ω ≤ tau Θ K (π / 2) := by
  obtain ⟨t₀, ht₀, hmax⟩ :=
    Θ.angles.exists_max_image (fun t => (supp K t - 1) / cos t) Θ.nonempty
  have hℓ := ang_lineLength_polyNiche_le (K := K) hω hmax
  have h352 := (lemma3_4_5_two hK (t := π / 2) (Or.inr rfl)).2
  rw [show π / 2 + π = 3 * π / 2 by ring] at h352
  have hσ := ang_supp_zero_le_sigmaAt hK.1 hω
  have h1 := ang_wedgeGapWInf_le_supp_zero hK.1 hω
  have h2 := ang_wedgeGapWInf_le hK.1.2.1 hω (Θ.subset t₀ ht₀)
  rw [ang_wedgeGapW_eq] at h2
  rcases le_total ((supp K t₀ - 1) / cos t₀) 0 with hW | hW
  · rw [max_eq_right hW] at hℓ
    linarith
  · rw [max_eq_left hW] at hℓ
    linarith

theorem polygon_wedgeGapZ_le_tau {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) :
    wedgeGapZInf K Θ.ω ≤ tau Θ K Θ.ω := by
  obtain ⟨t₀, ht₀, hmax⟩ :=
    Θ.angles.exists_max_image (fun t => (supp K (t + π / 2) - 1) / cos (Θ.ω - t)) Θ.nonempty
  have hℓ := ang_lineLength_polyNiche_le_z (K := K) hω hmax
  have h352 := (lemma3_4_5_two hK (t := Θ.ω) (Or.inl rfl)).2
  have hσ := ang_supp_le_sigmaAt_add_pi hK.1 hω
  have h1 := ang_wedgeGapZInf_le_supp hK.1 hω
  have h2 := ang_wedgeGapZInf_le hK.1.2.1 hω (Θ.subset t₀ ht₀)
  rw [ang_wedgeGapZ_eq] at h2
  rcases le_total ((supp K (t₀ + π / 2) - 1) / cos (Θ.ω - t₀)) 0 with hW | hW
  · rw [max_eq_right hW] at hℓ
    linarith
  · rw [max_eq_left hW] at hℓ
    linarith

/-- A common coordinate box bounds the supports in every direction. -/
theorem abs_supp_le_box {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {R : ℝ}
    (hbox : K ⊆ Icc (-R) R ×ˢ Icc 0 1) (t : ℝ) :
    |supp K t| ≤ R + 1 := by
  obtain ⟨p, hp, hpt⟩ := exists_dot_eq_supp hK.2.1 hK.1 t
  rw [← hpt]
  have h := mpc_abs_dot_uvec_le p t
  obtain ⟨hx, hy⟩ := hbox hp
  have hx' : |p.1| ≤ R := abs_le.mpr hx
  have hy' : |p.2| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
  linarith

/-- Pinned inequalities for every specified cap maximizing a positive value.
The sequence in this proof converges to K itself. -/
theorem pinned_bounds_of_maximal_positive {ω : ℝ} (hω : ω ∈ Ioo 0 (π / 2))
    {K : Set (ℝ × ℝ)} (hK : IsCap K ω) (hpositive : 0 < sofaArea ω K)
    (hmax : ∀ C, IsCap C ω → sofaArea ω C ≤ sofaArea ω K) :
    wedgeGapWInf K ω ≤ sigmaAt K (π / 2) ∧ wedgeGapZInf K ω ≤ sigmaAt K ω := by
  classical
  have hω' : ω ∈ Ioc 0 (π / 2) := ⟨hω.1, hω.2.le⟩
  obtain ⟨seq⟩ := exists_selectedCapSequence hω' hK hpositive hmax
  let Ks := seq.cap
  have hcap : ∀ n, IsCap (Ks n) ω := fun n => (seq.selected n).1.1
  have hcb : ∀ n, IsConvexBody (Ks n) := fun n => (hcap n).2.1
  let η : ℕ → ℝ := fun n => hausdorffDist (Ks n) K
  have hη : ∀ n, 0 ≤ η n := fun n => ang_hausdorffDist_nonneg (hcb n) hK.2.1
  have hηlim : Tendsto η atTop (𝓝 0) := seq.tends
  let R := seq.radius + 1
  have hR : 0 ≤ R := by dsimp [R]; linarith [seq.radius_nonneg]
  have hsupp : ∀ n s, |supp (Ks n) s| ≤ R :=
    fun n s => abs_supp_le_box (hcb n) (seq.boxed n) s
  have hclose : ∀ n s, |supp (Ks n) s - supp K s| ≤ η n :=
    fun n s => ang_abs_supp_sub_le_hausdorffDist (hcb n) hK.2.1 s
  let G := 2 * R + 2 / cos ω + 1
  have hcos : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [hω.1, pi_pos], hω.2⟩
  have hG : 0 ≤ G := by dsimp [G]; positivity
  let err (t : ℝ) (n : ℕ) := (2 + 4 * G) * η n / sin t
  have herrlim : ∀ t, Tendsto (err t) atTop (𝓝 0) := by
    intro t
    simpa [err] using (hηlim.const_mul (2 + 4 * G)).div_const (sin t)
  have hdefect : ∀ n t, (t = ω ∨ t = π / 2) →
      |sigmaAt (Ks n) t - tau (dyadicAngleSet ω hω' (seq.index n)) (Ks n) t| ≤ err t n := by
    intro n t ht
    let S := dyadicSamples ω hω' (seq.index n)
    have htd : t ∈ (dyadicAngleSet ω hω' (seq.index n)).diamond := by
      rcases ht with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    have h := abs_selected_defect_le S (seq.selected n) hω.2 (hη n) hR
      (hsupp n) (fun i => hclose n (S.normal i)) htd
    have hmass : S.totalWeight ≤ 1 := dyadic_totalWeight_le_one ω hω' (seq.index n)
    have hnumer : 2 * η n * S.totalWeight + 4 * S.totalWeight * η n * G ≤
        (2 + 4 * G) * η n := by
      have h₀ := mul_le_mul_of_nonneg_left hmass
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hη n))
      have h₁ := mul_le_mul_of_nonneg_left hmass
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (hη n)) hG)
      nlinarith
    have hsint : 0 ≤ sin t := (mpc_sin_pos_of_diamond htd).le
    exact h.trans (div_le_div_of_nonneg_right hnumer hsint)
  have hgapErr : Tendsto (fun n => (1 + 1 / cos ω) * η n) atTop (𝓝 0) := by
    simpa using hηlim.const_mul (1 + 1 / cos ω)
  constructor
  · have hw : Tendsto (fun n => wedgeGapWInf (Ks n) ω) atTop (𝓝 (wedgeGapWInf K ω)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun _ => norm_nonneg _)
        (fun n => lemma4_1_1 hω.2 (hcap n) hK) hgapErr
    have hlim : Tendsto (fun n => wedgeGapWInf (Ks n) ω - err (π / 2) n)
        atTop (𝓝 (wedgeGapWInf K ω)) := by
      simpa using hw.sub (herrlim (π / 2))
    apply ang_le_sigmaAt_of_tendsto hcb hK.2.1 seq.tends hlim
    intro n
    have hτ : wedgeGapWInf (Ks n) ω ≤
        tau (dyadicAngleSet ω hω' (seq.index n)) (Ks n) (π / 2) :=
      polygon_wedgeGapW_le_tau (seq.selected n).1 hω.2
    have hd := (abs_le.mp (hdefect n (π / 2) (Or.inr rfl))).1
    linarith
  · have hz : Tendsto (fun n => wedgeGapZInf (Ks n) ω) atTop (𝓝 (wedgeGapZInf K ω)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun _ => norm_nonneg _)
        (fun n => ang_abs_wedgeGapZInf_sub_le hω.2 (hcap n) hK) hgapErr
    have hlim : Tendsto (fun n => wedgeGapZInf (Ks n) ω - err ω n)
        atTop (𝓝 (wedgeGapZInf K ω)) := by
      simpa using hz.sub (herrlim ω)
    apply ang_le_sigmaAt_of_tendsto hcb hK.2.1 seq.tends hlim
    intro n
    have hτ : wedgeGapZInf (Ks n) ω ≤
        tau (dyadicAngleSet ω hω' (seq.index n)) (Ks n) ω :=
      polygon_wedgeGapZ_le_tau (seq.selected n).1 hω.2
    have hd := (abs_le.mp (hdefect n ω (Or.inl rfl))).1
    linarith

end MovingSofaUniqueness

end
