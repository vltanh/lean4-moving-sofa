module

public import MovingSofaStability.CurveRoof

/-!
# The niche envelope has a finite vertical slope bound

Uncompiled proof source. The two tails have slope at most two when their
angles stay within a quarter turn of the floor. On the compact middle arc,
the negative horizontal speed has a positive minimum. The three bounds are
joined at the actual matching endpoints.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

section Envelope

variable {t₁ t₂ t₃ t₄ sA sC : ℝ} {x : ℝ → Point} {α β ρA ρC : ℝ → ℝ}
variable (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC)
-- The statements below do not mention `h`, so it is included explicitly.
include h

theorem envelope_left_slope (ht₂ : t₂ < π / 4) :
    VerticalSlopeBound (envD x β '' Icc 0 t₂) 2 := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  have hθ : t₂ ∈ Ioo 0 (π / 4) := ⟨h1.trans h12, ht₂⟩
  have hc : ContinuousOn (envD x β) (Icc 0 t₂) :=
    (env_D_cont h).mono (Icc_subset_Icc le_rfl (by linarith))
  have hs := scalar_graph_slope (L := 2) (env_bp_finite t₁ t₂ t₃ t₄) hc.fst hc.snd
    (dX := fun t => (1 - ρC t) * cos t) (dY := fun t => (1 - ρC t) * sin t)
    (fun t ht he => by
      simpa only [Prod.smul_fst, smul_eq_mul, uvec_fst] using
        hasDerivAt_fst (h.D_deriv t ⟨ht.1, by linarith [ht.2]⟩ he))
    (fun t ht he => by
      simpa only [Prod.smul_snd, smul_eq_mul, uvec_snd] using
        hasDerivAt_snd (h.D_deriv t ⟨ht.1, by linarith [ht.2]⟩ he))
    (fun t ht _ => by
      have hp : 0 ≤ 1 - ρC t := by linarith [h.ρC_lt t ⟨ht.1.le, ht.2.le⟩]
      have hcos := cos_ge_half_of_small hθ ⟨ht.1.le, ht.2.le⟩
      exact mul_nonneg hp (by linarith))
    (fun t ht _ => by
      have hp : 0 ≤ 1 - ρC t := by linarith [h.ρC_lt t ⟨ht.1.le, ht.2.le⟩]
      have hsin : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith [ht.2, pi_pos])
      have hcos := cos_ge_half_of_small hθ ⟨ht.1.le, ht.2.le⟩
      rw [abs_of_nonneg (mul_nonneg hp hsin)]
      have hm := mul_le_mul_of_nonneg_left (show sin t ≤ 2 * cos t by linarith [sin_le_one t]) hp
      nlinarith)
  rintro p ⟨u, hu, rfl⟩ q ⟨v, hv, rfl⟩
  exact hs u hu v hv

theorem envelope_right_slope (ht₃ : π / 4 < t₃) :
    VerticalSlopeBound (envB x α '' Icc t₃ (π / 2)) 2 := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  have hsφ : π / 2 - t₃ ∈ Ioo 0 (π / 4) := ⟨by linarith, by linarith⟩
  have hc : ContinuousOn (envB x α) (Icc t₃ (π / 2)) :=
    (env_B_cont h).mono (Icc_subset_Icc (by linarith) le_rfl)
  have hs := scalar_graph_slope (L := 2) (env_bp_finite t₁ t₂ t₃ t₄) hc.fst hc.snd
    (dX := fun t => (1 - ρA t) * sin t) (dY := fun t => -(1 - ρA t) * cos t)
    (fun t ht he => by
      convert hasDerivAt_fst (h.B_deriv t ⟨by linarith [ht.1], ht.2⟩ he) using 1
      simp only [Prod.smul_fst, smul_eq_mul, vvec_fst]
      ring)
    (fun t ht he => by
      convert hasDerivAt_snd (h.B_deriv t ⟨by linarith [ht.1], ht.2⟩ he) using 1
      simp only [Prod.smul_snd, smul_eq_mul, vvec_snd]
      ring)
    (fun t ht _ => by
      have hp : 0 ≤ 1 - ρA t := by linarith [h.ρA_lt t ⟨ht.1.le, ht.2.le⟩]
      exact mul_nonneg hp
        (sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht.2, pi_pos])))
    (fun t ht _ => by
      have hp : 0 ≤ 1 - ρA t := by linarith [h.ρA_lt t ⟨ht.1.le, ht.2.le⟩]
      have hcos : 0 ≤ cos t := cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, pi_pos], ht.2.le⟩
      have hsin := cos_ge_half_of_small hsφ
        (t := π / 2 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
      rw [cos_pi_div_two_sub] at hsin
      rw [neg_mul, abs_neg, abs_of_nonneg (mul_nonneg hp hcos)]
      have hm := mul_le_mul_of_nonneg_left (show cos t ≤ 2 * sin t by linarith [cos_le_one t]) hp
      nlinarith)
  rintro p ⟨u, hu, rfl⟩ q ⟨v, hv, rfl⟩
  exact hs u hu v hv

/-- The middle arc is a Lipschitz graph because its horizontal speed is uniformly nonzero. -/
theorem envelope_core_slope :
    ∃ L : ℝ, 0 ≤ L ∧ VerticalSlopeBound (x '' Icc t₁ t₄) L := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  have hsub : Icc t₁ t₄ ⊆ Icc 0 (π / 2) := Icc_subset_Icc h1.le h4.le
  let dX : ℝ → ℝ := fun t => -α t * cos t + β t * sin t
  let dY : ℝ → ℝ := fun t => α t * sin t + β t * cos t
  have hdx : ContinuousOn dX (Icc t₁ t₄) :=
    ((h.α_cont.mono hsub).neg.mul continuous_cos.continuousOn).add
      ((h.β_cont.mono hsub).mul continuous_sin.continuousOn)
  have hdy : ContinuousOn dY (Icc t₁ t₄) :=
    ((h.α_cont.mono hsub).mul continuous_sin.continuousOn).add
      ((h.β_cont.mono hsub).mul continuous_cos.continuousOn)
  have hpositive : ∀ t ∈ Icc t₁ t₄, 0 < dX t := by
    intro t ht
    have hti : t ∈ Ioo 0 (π / 2) := ⟨h1.trans_le ht.1, ht.2.trans_lt h4⟩
    have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [hti.1, pi_pos], hti.2⟩
    have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi hti.1 (by linarith [hti.2, pi_pos])
    exact add_pos (mul_pos (neg_pos.mpr (h.α_neg t hti)) hc) (mul_pos (h.β_pos t hti) hs)
  obtain ⟨m, hm, hmle⟩ := isCompact_Icc.exists_forall_le' hdx hpositive
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hdy
  let L := (|B| + 1) / m
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hLm : L * m = |B| + 1 := by dsimp [L]; exact div_mul_cancel₀ _ hm.ne'
  have hc := h.x_cont.mono hsub
  have hs := scalar_graph_slope (L := L) (Set.finite_empty : (∅ : Set ℝ).Finite)
    hc.fst.neg hc.snd
    (dX := dX) (dY := dY)
    (fun t ht _ => by
      convert (hasDerivAt_fst (h.x_deriv t ⟨by linarith [ht.1], by linarith [ht.2]⟩)).neg
        using 1
      simp only [dX, Prod.fst_add, Prod.smul_fst, smul_eq_mul, uvec_fst, vvec_fst]
      ring)
    (fun t ht _ => by
      simpa only [dY, Prod.snd_add, Prod.smul_snd, smul_eq_mul, uvec_snd, vvec_snd] using
        hasDerivAt_snd (h.x_deriv t ⟨by linarith [ht.1], by linarith [ht.2]⟩))
    (fun t ht _ => (hpositive t ⟨ht.1.le, ht.2.le⟩).le)
    (fun t ht _ => by
      have hbnd : |dY t| ≤ B := by simpa only [Real.norm_eq_abs] using hB t ⟨ht.1.le, ht.2.le⟩
      have hbnd' : |dY t| ≤ |B| + 1 := by linarith [le_abs_self B]
      have hprod := mul_le_mul_of_nonneg_left (hmle t ⟨ht.1.le, ht.2.le⟩) hL
      rw [hLm] at hprod
      exact hbnd'.trans hprod)
  refine ⟨L, hL, ?_⟩
  rintro p ⟨u, hu, rfl⟩ q ⟨v, hv, rfl⟩
  simpa only [Pi.neg_apply, neg_sub_neg, abs_sub_comm] using hs u hu v hv

/-- The whole three-piece envelope inherits a single finite slope bound. -/
theorem envelope_slope_bound (ht₂ : t₂ < π / 4) (ht₃ : π / 4 < t₃) :
    ∃ L : ℝ, 0 ≤ L ∧ VerticalSlopeBound (envCurve t₁ t₂ t₃ t₄ x α β) L := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  obtain ⟨L₀, hL₀, hcore⟩ := envelope_core_slope h
  let L := max 2 L₀
  let D := envD x β '' Icc 0 t₂
  let C := x '' Icc t₁ t₄
  let B := envB x α '' Icc t₃ (π / 2)
  have hD : VerticalSlopeBound D L :=
    (envelope_left_slope h ht₂).mono_constant (le_max_left _ _)
  have hC : VerticalSlopeBound C L := hcore.mono_constant (le_max_right _ _)
  have hB : VerticalSlopeBound B L :=
    (envelope_right_slope h ht₃).mono_constant (le_max_left _ _)
  have hzD : x t₄ ∈ D := ⟨t₂, ⟨by linarith, le_rfl⟩, h.D_t₂⟩
  have hzC : x t₄ ∈ C := ⟨t₄, ⟨by linarith, le_rfl⟩, rfl⟩
  have hdmax : ∀ p ∈ D, p.1 ≤ (x t₄).1 := by
    rintro p ⟨t, ht, rfl⟩
    have he := (env_D₁_strictMono h).monotoneOn ht ⟨by linarith, le_rfl⟩ ht.2
    simpa only [h.D_t₂] using he
  have hcmin : ∀ p ∈ C, (x t₄).1 ≤ p.1 := by
    rintro p ⟨t, ht, rfl⟩
    exact (env_x₁_strictAnti h).antitoneOn ht ⟨by linarith, le_rfl⟩ ht.2
  have hDC := verticalSlopeBound_join hD hC hzD hzC hdmax hcmin
  have hzDC : x t₁ ∈ D ∪ C := Or.inr ⟨t₁, ⟨le_rfl, by linarith⟩, rfl⟩
  have hzB : x t₁ ∈ B := ⟨t₃, ⟨le_rfl, by linarith⟩, h.B_t₃⟩
  have hdcmax : ∀ p ∈ D ∪ C, p.1 ≤ (x t₁).1 := by
    intro p hp
    rcases hp with hp | ⟨t, ht, rfl⟩
    · exact (hdmax p hp).trans (envelope_endpoint_order h).2.1.le
    · exact (env_x₁_strictAnti h).antitoneOn ⟨le_rfl, by linarith⟩ ht ht.1
  have hbmin : ∀ p ∈ B, (x t₁).1 ≤ p.1 := by
    rintro p ⟨t, ht, rfl⟩
    have he := (env_B₁_strictMono h).monotoneOn ⟨le_rfl, by linarith⟩ ht ht.1
    simpa only [h.B_t₃] using he
  have hj := verticalSlopeBound_join hDC hB hzDC hzB hdcmax hbmin
  have he : (D ∪ C) ∪ B = envCurve t₁ t₂ t₃ t₄ x α β := by
    ext p
    simp only [D, C, B, envCurve, mem_union]
    tauto
  refine ⟨L, (show (0 : ℝ) ≤ 2 by norm_num).trans (le_max_left _ _), ?_⟩
  rwa [he] at hj

end Envelope

end MovingSofaStability
