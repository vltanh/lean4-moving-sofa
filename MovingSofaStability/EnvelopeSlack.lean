module

public import MovingSofaStability.RoofMargins

/-!
# Uniform slack below an envelope roof

Uncompiled proof source. The inactive tail wall has a strictly negative slack
on its entire compact parameter interval, including its floor endpoint. The
active wall's vertical coefficient is uniformly positive. This is proved from
`EnvHyp`, rather than assumed as a local error bound.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

theorem innerSlackU_eq_dot (K : Set Point) (t : ℝ) (p : Point) :
    innerSlackU K t p = dot (p - innerCorner K t) (uvec t) := by
  rw [dot_sub_left, proposition2_2_2_innerCorner]
  simp only [dot_add_left, dot_smul_left, dot_uvec_self, dot_vvec_uvec, mul_one,
    mul_zero, add_zero, innerSlackU]
  ring

theorem innerSlackV_eq_dot (K : Set Point) (t : ℝ) (p : Point) :
    innerSlackV K t p = dot (p - innerCorner K t) (vvec t) := by
  rw [dot_sub_left, proposition2_2_2_innerCorner]
  simp only [dot_add_left, dot_smul_left, dot_uvec_vvec, dot_vvec_self, mul_one,
    mul_zero, zero_add, innerSlackV]
  ring

theorem innerSlackU_down (K : Set Point) (t d : ℝ) (q : Point) :
    innerSlackU K t (q.1, q.2 - d) = innerSlackU K t q - d * sin t := by
  simp only [innerSlackU, dot, uvec]
  ring

theorem innerSlackV_down (K : Set Point) (t d : ℝ) (q : Point) :
    innerSlackV K t (q.1, q.2 - d) = innerSlackV K t q - d * cos t := by
  simp only [innerSlackV, dot, vvec]
  ring

section Envelope

variable {t₁ t₂ t₃ t₄ sA sC : ℝ} {x : ℝ → Point} {α β ρA ρC : ℝ → ℝ}
variable (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC)
-- The statements below do not mention `h`, so it is included explicitly.
include h

/-- The path's abscissa decreases even outside the middle exposed arc. -/
theorem envelope_path_fst_strictAnti : StrictAntiOn (fun t => (x t).1) (Icc 0 (π / 2)) := by
  apply env_strictAntiOn (Set.finite_empty : (∅ : Set ℝ).Finite) h.x_cont.fst
    (f' := fun t => α t * cos t - β t * sin t)
  · intro t ht _
    convert hasDerivAt_fst (h.x_deriv t ht) using 1
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, uvec_fst, vvec_fst]
    ring
  · intro t ht _
    have hcos : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩
    have hsin : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
    have h1 := mul_neg_of_neg_of_pos (h.α_neg t ht) hcos
    have h2 := mul_pos (h.β_pos t ht) hsin
    linarith

/-- The inactive tail slacks stay strict at the two floor endpoints as well. -/
theorem envelope_endpoint_speeds : 0 < β 0 ∧ α (π / 2) < 0 := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  obtain ⟨ho1, ho2, ho3⟩ := envelope_endpoint_order h
  have hx1 : (x t₁).1 < (x 0).1 := envelope_path_fst_strictAnti h
    ⟨le_rfl, by positivity⟩ ⟨h1.le, by linarith⟩ h1
  have hx4 : (x (π / 2)).1 < (x t₄).1 := envelope_path_fst_strictAnti h
    ⟨by linarith, h4.le⟩ ⟨by positivity, le_rfl⟩ h4
  have hD : (envD x β 0).1 = (x 0).1 - β 0 := by
    simp [envD, uvec]
  have hB : (envB x α (π / 2)).1 = (x (π / 2)).1 - α (π / 2) := by
    simp [envB, vvec, sub_eq_add_neg]
  rw [hD] at ho1
  rw [hB] at ho3
  constructor <;> linarith

/-- A common positive margin works for all three roof pieces. -/
theorem envelope_downward_slack {K : Set Point}
    (hpath : ∀ t ∈ Icc (0 : ℝ) (π / 2), innerCorner K t = x t) :
    ∃ c τ : ℝ, 0 < c ∧ 0 < τ ∧
      ∀ q ∈ envCurve t₁ t₂ t₃ t₄ x α β, ∀ d : ℝ, 0 < d → 0 ≤ q.2 - d →
        ∃ t ∈ Ioo (0 : ℝ) (π / 2),
          innerSlackU K t (q.1, q.2 - d) ≤ -min (c * d) τ ∧
          innerSlackV K t (q.1, q.2 - d) ≤ -min (c * d) τ := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  obtain ⟨hβ0, hαv⟩ := envelope_endpoint_speeds h
  have hβpos : ∀ t ∈ Icc (0 : ℝ) t₂, 0 < β t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with he | hp
    · simpa only [← he] using hβ0
    · exact h.β_pos t ⟨hp, by linarith [ht.2]⟩
  have hαpos : ∀ t ∈ Icc t₃ (π / 2), 0 < -α t := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with he | hp
    · simpa only [he] using neg_pos.mpr hαv
    · exact neg_pos.mpr (h.α_neg t ⟨by linarith [ht.1], hp⟩)
  obtain ⟨τD, hτD, hD⟩ := isCompact_Icc.exists_forall_le'
    (h.β_cont.mono (Icc_subset_Icc le_rfl (by linarith))) hβpos
  obtain ⟨τB, hτB, hB⟩ := isCompact_Icc.exists_forall_le'
    ((h.α_cont.mono (Icc_subset_Icc (by linarith) le_rfl)).neg) hαpos
  have corepos : ∀ t ∈ Icc t₁ t₄, 0 < min (sin t) (cos t) := by
    intro t ht
    exact lt_min
      (sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, pi_pos]))
      (cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩)
  obtain ⟨cC, hcC, hC⟩ := isCompact_Icc.exists_forall_le'
    (continuous_sin.min continuous_cos).continuousOn corepos
  obtain ⟨cD, hcD, hcos⟩ := isCompact_Icc.exists_forall_le'
    continuous_cos.continuousOn (s := Icc (0 : ℝ) t₂)
    (fun t ht => cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩)
  obtain ⟨cB, hcB, hsin⟩ := isCompact_Icc.exists_forall_le'
    continuous_sin.continuousOn (s := Icc t₃ (π / 2))
    (fun t ht => sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, pi_pos]))
  let c := min cC (min cD cB)
  let τ := min τD τB
  have hc : 0 < c := lt_min hcC (lt_min hcD hcB)
  have hτ : 0 < τ := lt_min hτD hτB
  have hcC' : c ≤ cC := min_le_left _ _
  have hcD' : c ≤ cD := (min_le_right _ _).trans (min_le_left _ _)
  have hcB' : c ≤ cB := (min_le_right _ _).trans (min_le_right _ _)
  have hτD' : τ ≤ τD := min_le_left _ _
  have hτB' : τ ≤ τB := min_le_right _ _
  refine ⟨c, τ, hc, hτ, ?_⟩
  intro q hq d hd hfloor
  rcases hq with (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩
  · have htv : t < π / 2 := lt_of_le_of_ne ht.2 (by
      intro he
      rw [he, h.B_end] at hfloor
      linarith)
    have hti : t ∈ Ioo (0 : ℝ) (π / 2) := ⟨by linarith [ht.1], htv⟩
    have heU : innerSlackU K t (envB x α t) = 0 := by
      rw [innerSlackU_eq_dot, hpath t ⟨hti.1.le, hti.2.le⟩]
      exact env_dot_B_self x α t
    have heV : innerSlackV K t (envB x α t) = α t := by
      rw [innerSlackV_eq_dot, hpath t ⟨hti.1.le, hti.2.le⟩]
      simp [envB, dot_smul_left]
    have hcoef : c ≤ sin t := hcB'.trans (hsin t ht)
    have hinactive : τ ≤ -α t := hτB'.trans (hB t ht)
    have hcos0 : 0 ≤ cos t := cos_nonneg_of_mem_Icc ⟨by linarith [hti.1, pi_pos], ht.2⟩
    refine ⟨t, hti, ?_, ?_⟩
    · rw [innerSlackU_down, heU, zero_sub]
      have hm := mul_le_mul_of_nonneg_left hcoef hd.le
      have hmin := min_le_left (c * d) τ
      nlinarith
    · rw [innerSlackV_down, heV]
      have hp := mul_nonneg hd.le hcos0
      have hmin := min_le_right (c * d) τ
      linarith
  · have hti : t ∈ Ioo (0 : ℝ) (π / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have heU : innerSlackU K t (x t) = 0 := by
      rw [innerSlackU_eq_dot, hpath t ⟨hti.1.le, hti.2.le⟩]
      simp [dot]
    have heV : innerSlackV K t (x t) = 0 := by
      rw [innerSlackV_eq_dot, hpath t ⟨hti.1.le, hti.2.le⟩]
      simp [dot]
    have hcu : c ≤ sin t := (hcC'.trans (hC t ht)).trans (min_le_left _ _)
    have hcv : c ≤ cos t := (hcC'.trans (hC t ht)).trans (min_le_right _ _)
    refine ⟨t, hti, ?_, ?_⟩
    · rw [innerSlackU_down, heU, zero_sub]
      have hm := mul_le_mul_of_nonneg_left hcu hd.le
      have hmin := min_le_left (c * d) τ
      nlinarith
    · rw [innerSlackV_down, heV, zero_sub]
      have hm := mul_le_mul_of_nonneg_left hcv hd.le
      have hmin := min_le_left (c * d) τ
      nlinarith
  · have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by
      intro he
      rw [← he, h.D_end] at hfloor
      linarith)
    have hti : t ∈ Ioo (0 : ℝ) (π / 2) := ⟨ht0, by linarith [ht.2]⟩
    have heU : innerSlackU K t (envD x β t) = -β t := by
      rw [innerSlackU_eq_dot, hpath t ⟨hti.1.le, hti.2.le⟩]
      simp [envD, dot_neg_left, dot_smul_left]
    have heV : innerSlackV K t (envD x β t) = 0 := by
      rw [innerSlackV_eq_dot, hpath t ⟨hti.1.le, hti.2.le⟩]
      exact env_dot_D_self x β t
    have hcoef : c ≤ cos t := hcD'.trans (hcos t ht)
    have hinactive : τ ≤ β t := hτD'.trans (hD t ht)
    have hsin0 : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht0.le (by linarith [hti.2, pi_pos])
    refine ⟨t, hti, ?_, ?_⟩
    · rw [innerSlackU_down, heU]
      have hp := mul_nonneg hd.le hsin0
      have hmin := min_le_right (c * d) τ
      linarith
    · rw [innerSlackV_down, heV, zero_sub]
      have hm := mul_le_mul_of_nonneg_left hcoef hd.le
      have hmin := min_le_left (c * d) τ
      nlinarith

end Envelope

end MovingSofaStability
