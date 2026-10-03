module

public import MovingSofa.Gerver.Envelope

/-!
# Compactness and coordinate bounds of the three-piece niche envelope

These lemmas use only the existing `EnvHyp` geometry and a strict height bound
for the rotation path. The endpoint matching and monotonicity prove the
horizontal range and nonnegative height of the whole envelope, including both
ends. No inverse graph parameterization is chosen.
-/

@[expose] public section
noncomputable section

open Real Set MovingSofa

namespace SofaUniqueness

variable {t₁ t₂ t₃ t₄ sA sC : ℝ}
variable {x : ℝ → ℝ × ℝ} {α β ρA ρC : ℝ → ℝ}

/-- The endpoints and junctions are strictly ordered in the horizontal direction. -/
theorem envelope_endpoint_order (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) :
    (envD x β 0).1 < (x t₄).1 ∧ (x t₄).1 < (x t₁).1 ∧
      (x t₁).1 < (envB x α (π / 2)).1 := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  have hd := env_D₁_strictMono h
    ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : (0 : ℝ) < t₂)
  simp only at hd
  rw [h.D_t₂] at hd
  have hx := env_x₁_strictAnti h
    ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : t₁ < t₄)
  simp only at hx
  have hb := env_B₁_strictMono h
    ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : t₃ < π / 2)
  simp only at hb
  rw [h.B_t₃] at hb
  exact ⟨hd, hx, hb⟩

theorem envelope_isCompact (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) :
    IsCompact (envCurve t₁ t₂ t₃ t₄ x α β) := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  unfold envCurve
  apply IsCompact.union
  · apply IsCompact.union
    · exact isCompact_Icc.image_of_continuousOn
        ((env_B_cont h).mono (Icc_subset_Icc (by linarith) le_rfl))
    · exact isCompact_Icc.image_of_continuousOn
        (h.x_cont.mono (Icc_subset_Icc h1.le h4.le))
  · exact isCompact_Icc.image_of_continuousOn
      ((env_D_cont h).mono (Icc_subset_Icc le_rfl (by linarith)))

/-- A strict path-height bound propagates to the entire closed envelope. -/
theorem envelope_bounds_of_path_height
    (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC)
    (hheight : ∀ t ∈ Icc (0 : ℝ) (π / 2), (x t).2 < 1) :
    ∀ p ∈ envCurve t₁ t₂ t₃ t₄ x α β,
      p.1 ∈ Icc (envD x β 0).1 (envB x α (π / 2)).1 ∧
        p.2 ∈ Ico (0 : ℝ) 1 := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  obtain ⟨ha, hm, hb⟩ := envelope_endpoint_order h
  have hBstart : t₃ ∈ Icc t₃ (π / 2) := ⟨le_rfl, by linarith⟩
  have hBend : π / 2 ∈ Icc t₃ (π / 2) := ⟨by linarith, le_rfl⟩
  have hxstart : t₁ ∈ Icc t₁ t₄ := ⟨le_rfl, by linarith⟩
  have hxend : t₄ ∈ Icc t₁ t₄ := ⟨by linarith, le_rfl⟩
  have hDstart : (0 : ℝ) ∈ Icc 0 t₂ := ⟨le_rfl, by linarith⟩
  have hDend : t₂ ∈ Icc 0 t₂ := ⟨by linarith, le_rfl⟩
  intro p hp
  rcases hp with (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩
  · have hxlo := (env_B₁_strictMono h).monotoneOn hBstart ht ht.1
    have hxhi := (env_B₁_strictMono h).monotoneOn ht hBend ht.2
    have hylo := (env_B₂_strictAnti h).antitoneOn ht hBend ht.2
    have hyhi := (env_B₂_strictAnti h).antitoneOn hBstart ht ht.1
    rw [h.B_t₃] at hxlo hyhi
    rw [h.B_end] at hylo
    have htopy := hheight t₁ ⟨h1.le, by linarith⟩
    exact ⟨⟨(ha.trans hm).le.trans hxlo, hxhi⟩, hylo, hyhi.trans_lt htopy⟩
  · have hxlo := (env_x₁_strictAnti h).antitoneOn ht hxend ht.2
    have hxhi := (env_x₁_strictAnti h).antitoneOn hxstart ht ht.1
    have hyhi := hheight t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ⟨⟨ha.le.trans hxlo, hxhi.trans hb.le⟩, (h.x_pos t ht).le, hyhi⟩
  · have hxlo := (env_D₁_strictMono h).monotoneOn hDstart ht ht.1
    have hxhi := (env_D₁_strictMono h).monotoneOn ht hDend ht.2
    have hylo := (env_D₂_strictMono h).monotoneOn hDstart ht ht.1
    have hyhi := (env_D₂_strictMono h).monotoneOn ht hDend ht.2
    rw [h.D_t₂] at hxhi hyhi
    rw [h.D_end] at hylo
    have htopy := hheight t₄ ⟨by linarith, h4.le⟩
    exact ⟨⟨hxlo, hxhi.trans (hm.trans hb).le⟩, hylo, hyhi.trans_lt htopy⟩

end SofaUniqueness
