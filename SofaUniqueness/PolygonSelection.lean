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
  classical
  obtain ⟨c, hc, hcAll⟩ := lemma3_4_2 Θ.hω (mpc_angles_bounds ht)
  have hcK : ∀ C, IsPolygonCap Θ C → 0 < polyArea Θ C → width C 0 ≤ c :=
    fun C hC hpos => hcAll Θ rfl ht C hC hpos
  let F : Set (ℝ × ℝ) → ℝ := fun K => polyArea Θ K - S.penalty target K
  have hFbound : ∀ K, IsPolygonCap Θ K → F K ≤ c := by
    intro K hK
    by_cases hp : 0 < F K
    · have hA := (penalty_and_area_le_of_positive S hK hcK hp).1
      have hP := S.penalty_nonneg target K
      dsimp [F]
      linarith
    · exact (le_of_not_gt hp).trans hc.le
  let values : Set ℝ := {x | ∃ K, IsPolygonCap Θ K ∧ F K = x}
  have hbdd : BddAbove values := ⟨c, by rintro _ ⟨K, hK, rfl⟩; exact hFbound K hK⟩
  have hmem : F R₀ ∈ values := ⟨R₀, hR₀, rfl⟩
  let M := sSup values
  have hMref : F R₀ ≤ M := le_csSup hbdd hmem
  have hMpos : 0 < M := hpositive.trans_le hMref
  have hseq : ∀ n : ℕ, ∃ K, IsPolygonCap Θ K ∧
      M - 1 / (n + 1) < F K ∧ 0 < F K := by
    intro n
    have hlt : max (M - 1 / (n + 1)) (M / 2) < M := by
      apply max_lt
      · have h : (0 : ℝ) < 1 / (n + 1) := by positivity
        linarith
      · linarith
    obtain ⟨_, ⟨K, hK, rfl⟩, hval⟩ := exists_lt_of_lt_csSup ⟨_, hmem⟩ hlt
    exact ⟨K, hK, (le_max_left _ _).trans_lt hval,
      by linarith [le_max_right (M - 1 / (n + 1)) (M / 2)]⟩
  choose Ks hKs hnear hpos using hseq
  let q := min (S.weight i₀) (S.weight i₁)
  have hq : 0 < q := lt_min hw₀ hw₁
  have hq₀ : q ≤ S.weight i₀ := min_le_left _ _
  have hq₁ : q ≤ S.weight i₁ := min_le_right _ _
  let R := sampleBoxRadius target t c q
  have hbox : ∀ n, Ks n ⊆ Icc (-R) R ×ˢ Icc 0 1 := by
    intro n
    have hP := (penalty_and_area_le_of_positive S (hKs n) hcK (hpos n)).2
    have h₀ := (S.sample_bound target (Ks n) i₀).trans hP
    have h₁ := (S.sample_bound target (Ks n) i₁).trans hP
    rw [hi₀] at h₀
    rw [hi₁] at h₁
    apply polygon_subset_sampleBox (hKs n) ht hc.le hq
    · exact (mul_le_mul_of_nonneg_right hq₀ (sq_nonneg _)).trans h₀
    · exact (mul_le_mul_of_nonneg_right hq₁ (sq_nonneg _)).trans h₁
  have hR : 0 ≤ R := sampleBoxRadius_nonneg target (mpc_angles_bounds ht).1
    ((mpc_angles_bounds ht).2.trans_le (mpc_omega_le Θ)) hc.le hq
  let v : ℕ → ({s // s ∈ mpcDiamond Θ} → ℝ) := fun n s => supp (Ks n) s.1
  have hvb : ∀ n, v n ∈ Metric.closedBall (0 : {s // s ∈ mpcDiamond Θ} → ℝ) (R + 1) := by
    intro n
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by linarith)]
    intro s
    obtain ⟨p, hp, hpe⟩ := exists_dot_eq_supp (hKs n).1.2.1.2.1 (hKs n).1.2.1.1 s.1
    rw [Real.norm_eq_abs]
    change |supp (Ks n) s.1| ≤ R + 1
    rw [← hpe]
    have hdot := mpc_abs_dot_uvec_le p s.1
    obtain ⟨hx, hy⟩ := hbox n hp
    have hx' : |p.1| ≤ R := abs_le.mpr hx
    have hy' : |p.2| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
    linarith
  obtain ⟨a, _, φ, hφ, hvlim⟩ := (isCompact_closedBall _ _).tendsto_subseq hvb
  let hinf : ℝ → ℝ := fun s => if hs : s ∈ mpcDiamond Θ then a ⟨s, hs⟩ else 0
  have hlim : ∀ s ∈ Θ.diamond,
      Tendsto (fun n => supp (Ks (φ n)) s) atTop (𝓝 (hinf s)) := by
    intro s hs
    have hs' := mpc_mem_mpcDiamond.mpr hs
    have h := tendsto_pi_nhds.mp hvlim ⟨s, hs'⟩
    have he : hinf s = a ⟨s, hs'⟩ := by simp only [hinf, hs', dite_true]
    rw [he]
    exact h
  obtain ⟨hLcap, hsupp, _, husc, hlsc⟩ := mpc_limit_polycap (fun n => hKs (φ n))
    (isCompact_Icc.prod isCompact_Icc) (fun n => hbox (φ n)) hlim
  have hPlim : Tendsto (fun n => S.penalty target (Ks (φ n))) atTop
      (𝓝 (S.penalty target (capH Θ hinf))) := by
    apply S.penalty_tendsto
    intro i
    rw [hsupp _ (S.normal_mem i)]
    exact hlim _ (S.normal_mem i)
  have hML : M ≤ F (capH Θ hinf) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hε4 : 0 < ε / 4 := by positivity
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε4
    have hnear' : ∀ᶠ n in atTop, M - ε / 4 < F (Ks (φ n)) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have h₁ := hnear (φ n)
      have h₂ : (1 : ℝ) / (φ n + 1) ≤ 1 / (N + 1) := by
        apply div_le_div_of_nonneg_left zero_le_one (by positivity)
        have hNφ : (N : ℝ) ≤ φ n := by exact_mod_cast hn.trans (hφ.id_le n)
        linarith
      linarith
    have hP' : ∀ᶠ n in atTop,
        S.penalty target (capH Θ hinf) - ε / 4 < S.penalty target (Ks (φ n)) :=
      hPlim.eventually (Ioi_mem_nhds (by linarith))
    obtain ⟨n, hn⟩ := (hnear'.and ((husc (ε / 4) hε4).and
      ((hlsc (ε / 4) hε4).and hP'))).exists
    rcases hn with ⟨hn, hA, hN, hP⟩
    dsimp [F] at hn ⊢
    rw [theorem3_2_3 hLcap]
    rw [theorem3_2_3 (hKs (φ n))] at hn
    linarith
  refine ⟨capH Θ hinf, hLcap, ?_⟩
  intro K hK
  exact (le_csSup hbdd ⟨K, hK, rfl⟩).trans hML

end SofaUniqueness
