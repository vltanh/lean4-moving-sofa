module

public import MovingSofaUniqueness.Selection.PolygonSelection
public import MovingSofaUniqueness.Selection.CapApproximation

/-!
# Polygon selection which retains the specified maximizer

The finite objective is A_n-P_n. The recovery polygon has P_n=0 exactly.
Persistent dyadic sample weights identify every Hausdorff subsequential limit
with the specified cap. Two coarsest samples give a common bounding box before
compactness is used. Neither a vanishing penalty weight nor uniform convergence
of the objectives is assumed.

Only a convergent subsequence is selected, which is all the subsequent
variational arguments require. Its finite polygons remain exact maximizers of
A_n-P_n, never reclassified as unpenalized or balanced maxima.
-/

@[expose] public section
noncomputable section

open Set Real Filter Topology MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

/-- Every stage has an actual penalized maximizer. -/
theorem exists_dyadic_penalizedMax {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    {target : Set (ℝ × ℝ)} (hK : IsCap target ω)
    (hpositive : 0 < sofaArea ω target) (n : ℕ) :
    ∃ K, IsPenalizedMax (dyadicSamples ω hω n) target K := by
  obtain ⟨t₀, ht₀⟩ := (dyadicAngleSet ω hω 0).nonempty
  have ht₀n : t₀ ∈ (dyadicAngleSet ω hω n).angles :=
    mpc_dyadic_mono hω (Nat.zero_le n) ht₀
  let i₀ : DyadicSampleIndex ω hω n := ⟨⟨0, by omega⟩, ⟨⟨t₀, ht₀⟩, 0⟩⟩
  let i₁ : DyadicSampleIndex ω hω n := ⟨⟨0, by omega⟩, ⟨⟨t₀, ht₀⟩, 1⟩⟩
  have hR := (proposition3_2_1 (Θ := dyadicAngleSet ω hω n) hK).2
  apply exists_penalizedMax (dyadicSamples ω hω n) target ht₀n i₀ i₁
  · simp [dyadicSamples, i₀]
  · simp [dyadicSamples, i₁]
  · exact dyadicLevelWeight_pos ω hω 0
  · exact dyadicLevelWeight_pos ω hω 0
  · exact hR
  · exact hpositive.trans_le (dyadic_recovery_ge ω hω hK n)

/-- The recovery comparison gives the continuum value as a lower bound for
the selected finite penalized objective at every stage. -/
theorem selected_objective_ge {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    {target K : Set (ℝ × ℝ)} (hK : IsCap target ω) {n : ℕ}
    (hselected : IsPenalizedMax (dyadicSamples ω hω n) target K) :
    sofaArea ω target ≤ polyArea (dyadicAngleSet ω hω n) K -
      dyadicPenalty ω hω n target K := by
  have hrec := dyadic_recovery_ge ω hω hK n
  have hmax := hselected.2 (polyCap (dyadicAngleSet ω hω n) target)
    (proposition3_2_1 (Θ := dyadicAngleSet ω hω n) hK).2
  exact hrec.trans hmax

/-- A common box for a full sequence of selected finite maximizers. Its bound
uses the persistent coarsest samples, not any fine-grid angle denominator. -/
theorem selected_sequence_bounded {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    {target : Set (ℝ × ℝ)} (hK : IsCap target ω)
    (hpositive : 0 < sofaArea ω target)
    (Ks : ℕ → Set (ℝ × ℝ))
    (hKs : ∀ n, IsPenalizedMax (dyadicSamples ω hω n) target (Ks n)) :
    ∃ R ≥ 0, ∀ n, Ks n ⊆ Icc (-R) R ×ˢ Icc 0 1 := by
  obtain ⟨t₀, ht₀⟩ := (dyadicAngleSet ω hω 0).nonempty
  have htI : t₀ ∈ Ioo 0 ω := (dyadicAngleSet ω hω 0).subset t₀ ht₀
  obtain ⟨c, hc, hcAll⟩ := lemma3_4_2 hω htI
  let q := dyadicLevelWeight ω hω 0
  have hq : 0 < q := dyadicLevelWeight_pos ω hω 0
  let R := sampleBoxRadius target t₀ c q
  refine ⟨R, sampleBoxRadius_nonneg target htI.1 (htI.2.trans_le hω.2) hc.le hq, ?_⟩
  intro n
  have ht₀n := mpc_dyadic_mono hω (Nat.zero_le n) ht₀
  have hFn : 0 < polyArea (dyadicAngleSet ω hω n) (Ks n) -
      dyadicPenalty ω hω n target (Ks n) :=
    hpositive.trans_le (selected_objective_ge hω hK (hKs n))
  have hwidth : ∀ C, IsPolygonCap (dyadicAngleSet ω hω n) C →
      0 < polyArea (dyadicAngleSet ω hω n) C → width C 0 ≤ c :=
    fun C hC hpos => hcAll (dyadicAngleSet ω hω n) rfl ht₀n C hC hpos
  have hP := (penalty_and_area_le_of_positive (dyadicSamples ω hω n)
    (hKs n).1 hwidth hFn).2
  have h₀ := (persistent_sample_first ω hω (Nat.zero_le n) ht₀ target (Ks n)).trans hP
  have h₁ := (persistent_sample_second ω hω (Nat.zero_le n) ht₀ target (Ks n)).trans hP
  exact polygon_subset_sampleBox (hKs n).1 ht₀n hc.le hq h₀ h₁

/-- The exact data passed to the variational and limiting arguments. -/
structure SelectedCapSequence (ω : ℝ) (hω : ω ∈ Ioc 0 (π / 2))
    (target : Set (ℝ × ℝ)) where
  index : ℕ → ℕ
  index_strict : StrictMono index
  cap : ℕ → Set (ℝ × ℝ)
  selected : ∀ n, IsPenalizedMax (dyadicSamples ω hω (index n)) target (cap n)
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  boxed : ∀ n, cap n ⊆ Icc (-radius) radius ×ˢ Icc 0 1
  tends : HausdorffTendsto cap target

/-- Selection of the specified cap, rather than an arbitrary limit maximizer. -/
theorem exists_selectedCapSequence {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    {target : Set (ℝ × ℝ)} (hK : IsCap target ω)
    (hpositive : 0 < sofaArea ω target)
    (hmax : ∀ C, IsCap C ω → sofaArea ω C ≤ sofaArea ω target) :
    Nonempty (SelectedCapSequence ω hω target) := by
  classical
  choose Ks hKs using fun n => exists_dyadic_penalizedMax hω hK hpositive n
  obtain ⟨R, hR, hbox⟩ := selected_sequence_bounded hω hK hpositive Ks hKs
  have hKsc : ∀ n, IsConvexBody (Ks n) := fun n => (hKs n).1.1.2.1
  obtain ⟨L, hL, _, φ, hφ, hlim⟩ := mpc_blaschke hKsc
    (isCompact_Icc.prod isCompact_Icc) hbox
  have hpoly : ∀ n, IsPolygonCap (dyadicAngleSet ω hω (φ n)) (Ks (φ n)) :=
    fun n => (hKs (φ n)).1
  have hLcap : IsCap L ω := mpc_limit_isCap hω (fun _ => rfl) hpoly hL hlim
  have hupper := dyadic_objective_limsup hω hφ hpoly hL hlim hR (fun n => hbox (φ n))
  have hPzero : Tendsto (fun n => dyadicPenalty ω hω (φ n) target (Ks (φ n)))
      atTop (𝓝 0) := by
    apply penalty_tendsto_zero_of_objective
      (fun n => polyArea (dyadicAngleSet ω hω (φ n)) (Ks (φ n)))
      (fun n => dyadicPenalty ω hω (φ n) target (Ks (φ n)))
      (sofaArea ω target) (sofaArea ω L)
    · exact fun n => dyadicPenalty_nonneg ω hω (φ n) target (Ks (φ n))
    · exact fun n => selected_objective_ge hω hK (hKs (φ n))
    · exact hmax L hLcap
    · exact hupper
  have hsame : L = target := by
    apply caps_eq_of_dyadic_supports hω hLcap hK
    intro m t ht
    have hcoef : 0 < dyadicLevelWeight ω hω m := dyadicLevelWeight_pos ω hω m
    have hlarge : ∀ᶠ n in atTop, m ≤ φ n := hφ.tendsto_atTop.eventually_ge_atTop m
    have hsupport := mpc_supp_tendsto hL (fun n => hKsc (φ n)) hlim
    have hfirstLim : Tendsto (fun n => dyadicLevelWeight ω hω m *
        (supp (Ks (φ n)) t - supp target t) ^ 2) atTop
        (𝓝 (dyadicLevelWeight ω hω m * (supp L t - supp target t) ^ 2)) :=
      ((hsupport t).sub_const (supp target t)).pow 2 |>.const_mul (dyadicLevelWeight ω hω m)
    have hsecondLim : Tendsto (fun n => dyadicLevelWeight ω hω m *
        (supp (Ks (φ n)) (t + π / 2) - supp target (t + π / 2)) ^ 2) atTop
        (𝓝 (dyadicLevelWeight ω hω m * (supp L (t + π / 2) - supp target (t + π / 2)) ^ 2)) :=
      ((hsupport (t + π / 2)).sub_const (supp target (t + π / 2))).pow 2
        |>.const_mul (dyadicLevelWeight ω hω m)
    have hfirst : dyadicLevelWeight ω hω m * (supp L t - supp target t) ^ 2 ≤ 0 := by
      apply le_of_tendsto_of_tendsto hfirstLim hPzero
      filter_upwards [hlarge] with n hn
      exact persistent_sample_first ω hω hn ht target (Ks (φ n))
    have hsecond : dyadicLevelWeight ω hω m *
        (supp L (t + π / 2) - supp target (t + π / 2)) ^ 2 ≤ 0 := by
      apply le_of_tendsto_of_tendsto hsecondLim hPzero
      filter_upwards [hlarge] with n hn
      exact persistent_sample_second ω hω hn ht target (Ks (φ n))
    constructor
    · have hsq : (supp L t - supp target t) ^ 2 = 0 := by
        nlinarith [sq_nonneg (supp L t - supp target t)]
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
    · have hsq : (supp L (t + π / 2) - supp target (t + π / 2)) ^ 2 = 0 := by
        nlinarith [sq_nonneg (supp L (t + π / 2) - supp target (t + π / 2))]
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  refine ⟨⟨φ, hφ, fun n => Ks (φ n), fun n => hKs (φ n), R, hR,
    fun n => hbox (φ n), ?_⟩⟩
  rw [← hsame]
  exact hlim

end MovingSofaUniqueness
