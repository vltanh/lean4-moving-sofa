module

public import MovingSofaUniqueness.Curvature.PolygonArms
public import MovingSofaUniqueness.Curvature.PolygonCurvature

/-!
# Integrated polygon curvature bounds with summable defects

The error need not be uniformly O(delta) at each facet. A nonnegative error
function on the grid is sufficient provided that its TOTAL tends to zero.
This is important for persistent sampled penalties: their coarse-angle and
endpoint weights need not shrink proportionally to the finest mesh.

The estimate includes normal zero and extends to open intervals starting below
zero. Thus passage to the limit can exclude an atom at zero rather than assume
that it is absent. No balancedness or polygon maximality occurs in the hypotheses.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofaOptimality
open scoped BigOperators

namespace MovingSofaUniqueness

/-- One cell with an arbitrary additive local error. -/
theorem polygon_step_with_error {k : ℕ} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap (rightAngleSet k) K) {D C e : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ p ∈ K, ∀ q ∈ K, norm2 (p - q) ≤ D) {t : ℝ}
    (ht : t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ))
    (hlocal : sigmaAt K t ≤ k0 (gPlus K t) * stepSize k + C * stepSize k ^ 2 + e) :
    sigmaAt K t ≤ (∫ u in t..(t + stepSize k), k0 (gPlus K u)) +
      (C + D) * stepSize k ^ 2 + e := by
  have hδ : stepSize k ≠ 0 := (inj_stepSize_pos k).ne'
  have h := polygon_step_integral_bound hK hD hdiam ht
    (η := e / stepSize k) (by simpa only [div_mul_cancel₀ _ hδ] using hlocal)
  simpa only [div_mul_cancel₀ _ hδ] using h

/-- Sum of the nonnegative grid errors, including the zero normal. -/
def polygonGridError (k : ℕ) (e : ℝ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (2 ^ (k + 1)), e ((j : ℝ) * stepSize k)

/-- Integrated estimate on an arbitrary half-open interval in the first
quadrant. The entire error sum appears once, not once for each cell. -/
theorem polygon_Ico_with_errors {k : ℕ} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap (rightAngleSet k) K) {D C B : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hdiam : ∀ p ∈ K, ∀ q ∈ K, norm2 (p - q) ≤ D)
    (hbound : ∀ u ∈ Icc (0 : ℝ) (π / 2), k0 (gPlus K u) ≤ B)
    (e : ℝ → ℝ)
    (he : ∀ t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ), 0 ≤ e t)
    (hlocal : ∀ t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ),
      sigmaAt K t ≤ k0 (gPlus K t) * stepSize k + C * stepSize k ^ 2 + e t)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π / 2) :
    (sigma K (Ico a b)).toReal ≤ (∫ u in a..b, k0 (gPlus K u)) +
      (2 * B + π / 2 * (C + D)) * stepSize k + polygonGridError k e := by
  have hKc : IsConvexBody K := hK.1.2.1
  have hδ := inj_stepSize_pos k
  have hn : ((2 ^ (k + 1) : ℕ) : ℝ) * stepSize k = π / 2 := by
    push_cast
    exact inj_two_pow_mul_stepSize k
  set δ := stepSize k with hδdef
  set n := 2 ^ (k + 1) with hndef
  let E : ℕ → ℝ := fun m => ∑ j ∈ Finset.range m, e ((j : ℝ) * δ)
  have hint := inj_intervalIntegrable_k0_gPlus hKc
  have hgrid : ∀ j : ℕ, j < n →
      (j : ℝ) * δ ∈ insert 0 ((rightAngleSet k).angles : Set ℝ) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · left
      simp
    · right
      exact inj_mem_angles.2 ⟨j, hj0, hj, rfl⟩
  have hEnonneg : ∀ m ≤ n, 0 ≤ E m := by
    intro m hm
    apply Finset.sum_nonneg
    intro j hj
    exact he _ (hgrid j ((Finset.mem_range.mp hj).trans_le hm))
  have hEmono : ∀ m ≤ n, E m ≤ E n := by
    intro m hm
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
    intro j hj _
    exact he _ (hgrid j (Finset.mem_range.mp hj))
  have hsum : ∀ p m : ℕ, p ≤ m → m ≤ n →
      (sigma K (Ico (p * δ) (m * δ))).toReal ≤
        (∫ u in (p * δ)..(m * δ), k0 (gPlus K u)) +
          ((m : ℝ) - p) * ((C + D) * δ ^ 2) + (E m - E p) := by
    intro p m hpm
    induction m, hpm using Nat.le_induction with
    | base =>
      intro _
      simp
    | succ m hpm ih =>
      intro hmn
      have ih := ih (by omega)
      have hmδ : (m : ℝ) * δ ≤ ((m + 1 : ℕ) : ℝ) * δ :=
        mul_le_mul_of_nonneg_right (by push_cast; linarith) hδ.le
      have hpδ : (p : ℝ) * δ ≤ m * δ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hpm) hδ.le
      have e1 : Ico ((p : ℝ) * δ) (((m + 1 : ℕ) : ℝ) * δ) =
          Ico ((p : ℝ) * δ) (m * δ) ∪ Ico ((m : ℝ) * δ) (((m + 1 : ℕ) : ℝ) * δ) :=
        (Ico_union_Ico_eq_Ico hpδ hmδ).symm
      have hm1 : (((m + 1 : ℕ) : ℝ) * δ) = m * δ + δ := by push_cast; ring
      have hmΘ := hgrid m (by omega)
      obtain ⟨_, hA1, _, hA3⟩ := inj_polygon_consecutive hK (m := m) (by omega) rfl
      have hIoo : sigma K (Ioo ((m : ℝ) * δ) (m * δ + δ)) = 0 := by
        apply inj_sigma_Ioo_eq_zero hKc (by linarith)
          (q := vint K (m * δ) (m * δ + δ))
        intro s hs
        rcases eq_or_lt_of_le hs.1 with rfl | h1
        · exact hA1
        · exact (hA3 s ⟨h1, hs.2⟩).2.1
      have hstep : (sigma K (Ico ((m : ℝ) * δ) (((m + 1 : ℕ) : ℝ) * δ))).toReal =
          sigmaAt K (m * δ) := by
        rw [hm1, ← Ioo_insert_left (by linarith), insert_eq,
          measure_union (disjoint_singleton_left.2 (fun h => lt_irrefl _ h.1)) measurableSet_Ioo,
          hIoo, add_zero, sigmaAt]
      have hs := polygon_step_with_error hK hD hdiam hmΘ (hlocal _ hmΘ)
      rw [← hδdef] at hs
      have hEs : E (m + 1) = E m + e ((m : ℝ) * δ) := by
        exact Finset.sum_range_succ _ m
      rw [e1, measure_union Ico_disjoint_Ico_same measurableSet_Ico,
        ENNReal.toReal_add measure_Ico_lt_top.ne measure_Ico_lt_top.ne, hstep,
        ← intervalIntegral.integral_add_adjacent_intervals (b := (m : ℝ) * δ)
          (hint _ _) (hint _ _), hm1, hEs]
      push_cast
      nlinarith
  set p := ⌊a / δ⌋₊ with hp
  set q := ⌈b / δ⌉₊ with hq
  have hpa : (p : ℝ) * δ ≤ a := by
    have h := Nat.floor_le (div_nonneg ha hδ.le)
    rw [← hp] at h
    calc
      (p : ℝ) * δ ≤ a / δ * δ := by gcongr
      _ = a := div_mul_cancel₀ a hδ.ne'
  have hpa' : a < (p : ℝ) * δ + δ := by
    have h := Nat.lt_floor_add_one (a / δ)
    rw [← hp] at h
    calc
      a = a / δ * δ := (div_mul_cancel₀ a hδ.ne').symm
      _ < ((p : ℝ) + 1) * δ := by gcongr
      _ = p * δ + δ := by ring
  have hqb : b ≤ (q : ℝ) * δ := by
    have h := Nat.le_ceil (b / δ)
    rw [← hq] at h
    calc
      b = b / δ * δ := (div_mul_cancel₀ b hδ.ne').symm
      _ ≤ q * δ := by gcongr
  have hqb' : (q : ℝ) * δ < b + δ := by
    have h := Nat.ceil_lt_add_one (div_nonneg (ha.trans hab) hδ.le)
    rw [← hq] at h
    calc
      (q : ℝ) * δ < (b / δ + 1) * δ := by gcongr
      _ = b + δ := by rw [add_mul, div_mul_cancel₀ b hδ.ne', one_mul]
  have hqn : q ≤ n := by
    rw [hq]
    apply Nat.ceil_le.2
    rw [div_le_iff₀ hδ, hn]
    exact hb
  have hpq : p ≤ q := by
    have h : (p : ℝ) * δ ≤ q * δ := hpa.trans (hab.trans hqb)
    exact_mod_cast le_of_mul_le_mul_right h hδ
  have hqπ : (q : ℝ) * δ ≤ π / 2 := by
    rw [← hn]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hqn) hδ.le
  have hp0 : (0 : ℝ) ≤ p * δ := by positivity
  have hsumPQ := hsum p q hpq hqn
  have hleft : ∫ u in (p * δ)..a, k0 (gPlus K u) ≤ B * δ := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hpa (hint _ _)
      (intervalIntegrable_const (c := B))
      (fun u hu => hbound u ⟨hp0.trans hu.1, by linarith [hu.2]⟩)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    nlinarith
  have hright : ∫ u in b..(q * δ), k0 (gPlus K u) ≤ B * δ := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hqb (hint _ _)
      (intervalIntegrable_const (c := B))
      (fun u hu => hbound u ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    nlinarith
  have hsplit : ∫ u in (p * δ)..(q * δ), k0 (gPlus K u) =
      (∫ u in (p * δ)..a, k0 (gPlus K u)) + (∫ u in a..b, k0 (gPlus K u)) +
        ∫ u in b..(q * δ), k0 (gPlus K u) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  have hmono : (sigma K (Ico a b)).toReal ≤
      (sigma K (Ico ((p : ℝ) * δ) (q * δ))).toReal :=
    ENNReal.toReal_mono measure_Ico_lt_top.ne (measure_mono (Ico_subset_Ico hpa hqb))
  have hqp : ((q : ℝ) - p) * ((C + D) * δ ^ 2) ≤ π / 2 * (C + D) * δ := by
    have hqp' : ((q : ℝ) - p) ≤ n := by
      have hqn' : (q : ℝ) ≤ n := by exact_mod_cast hqn
      linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
    calc
      ((q : ℝ) - p) * ((C + D) * δ ^ 2) ≤ n * ((C + D) * δ ^ 2) :=
        mul_le_mul_of_nonneg_right hqp' (by positivity)
      _ = ((n : ℝ) * δ) * (C + D) * δ := by ring
      _ = π / 2 * (C + D) * δ := by rw [hn]
  have hE : E q - E p ≤ polygonGridError k e := by
    have h₁ := hEmono q hqn
    have h₂ := hEnonneg p (hpq.trans hqn)
    change E q - E p ≤ E n
    linarith
  linarith

/-- The same estimate on intervals beginning below zero. This deliberately
keeps zero INSIDE an open interval before taking the limiting measure. -/
theorem polygon_Ioo_with_errors {k : ℕ} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap (rightAngleSet k) K) {D C B : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hdiam : ∀ p ∈ K, ∀ q ∈ K, norm2 (p - q) ≤ D)
    (hbound : ∀ u ∈ Icc (0 : ℝ) (π / 2), k0 (gPlus K u) ≤ B)
    (e : ℝ → ℝ)
    (he : ∀ t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ), 0 ≤ e t)
    (hlocal : ∀ t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ),
      sigmaAt K t ≤ k0 (gPlus K t) * stepSize k + C * stepSize k ^ 2 + e t)
    {a b : ℝ} (ha : -(π / 2) ≤ a) (hab : max a 0 ≤ b) (hb : b ≤ π / 2) :
    (sigma K (Ioo a b)).toReal ≤ (∫ u in (max a 0)..b, k0 (gPlus K u)) +
      (2 * B + π / 2 * (C + D)) * stepSize k + polygonGridError k e := by
  have hcap : IsCap K (π / 2) := hK.1
  have hKc : IsConvexBody K := hcap.2.1
  obtain ⟨_, hc2, hc3⟩ := inj_cap_consecutive hcap
  have h0 : sigma K (Ioo (-(π / 2)) 0) = 0 := by
    apply inj_sigma_Ioo_eq_zero hKc (by linarith [pi_pos]) (q := (supp K 0, 0))
    intro s hs
    rcases eq_or_lt_of_le hs.1 with rfl | h1
    · exact hc2
    · exact hc3 s ⟨h1, hs.2⟩
  have hsub : Ioo a b ⊆ Ioo (-(π / 2)) 0 ∪ Ico (max a 0) b := by
    intro x hx
    by_cases hx0 : x < 0
    · left
      exact ⟨by linarith [hx.1], hx0⟩
    · right
      exact ⟨max_le hx.1.le (not_lt.mp hx0), hx.2⟩
  have hle : sigma K (Ioo a b) ≤ sigma K (Ico (max a 0) b) := by
    calc
      sigma K (Ioo a b) ≤ sigma K (Ioo (-(π / 2)) 0 ∪ Ico (max a 0) b) := measure_mono hsub
      _ ≤ sigma K (Ioo (-(π / 2)) 0) + sigma K (Ico (max a 0) b) := measure_union_le _ _
      _ = sigma K (Ico (max a 0) b) := by rw [h0, zero_add]
  calc
    (sigma K (Ioo a b)).toReal ≤ (sigma K (Ico (max a 0) b)).toReal :=
      ENNReal.toReal_mono measure_Ico_lt_top.ne hle
    _ ≤ _ := polygon_Ico_with_errors hK hD hC hB hdiam hbound e he hlocal
      (le_max_right _ _) hab hb

end MovingSofaUniqueness
