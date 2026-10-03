module

public import MovingSofaOptimality.Gerver.StructureCap

/-!
# Gerver's rotation path stays strictly below the cap's top

The existing phase estimates already have strict slack after adding the
translation bounds: at most 0.95, 0.99240672, 0.88962658, 0.99240672 and
0.9500001 respectively. This proof reuses those established inequalities and
performs only rational linear/nonlinear arithmetic on them. No new numerical
enclosure, evaluator or decision certificate is introduced.

The strict bound removes the exceptional top-contact case from regular-closed
recovery.
-/

@[expose] public section
noncomputable section

open Real Set

namespace MovingSofaOptimality.GerverParams

variable {P : GerverParams}

/-- A strict version of `gs_path_snd_le_one`, using its existing phase estimates. -/
theorem path_snd_lt_one (hP : P.IsSolution) (hB : P.Bounds) {t : ℝ}
    (h0 : 0 ≤ t) (h1 : t ≤ π / 2) : (P.path t).2 < 1 := by
  have hO := gs_ord hP
  rcases gs_cases (P := P) t with h | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | h
  · rw [gs_path_eq_phase hP (gs_piece₀ h)]
    have := gs_ineq_y₁ hB h0 h
    simp only [gs_phase, gs_Phase.X, gs_ph1, rot, Prod.snd_add, gs_a₂ hP, gs_κ₁₂ hP]
    linarith
  · rw [gs_path_eq_phase hP (gs_piece₁ ha.le hb)]
    have := gs_ineq_y₂ hB hP h0 hb
    have := hB.κ₂₂_mem.2
    simp only [gs_phase, gs_Phase.X, gs_ph2, rot, Prod.snd_add]
    linarith
  · rw [gs_path_eq_phase hP (gs_piece₂ ha.le hb)]
    have := gs_ineq_y₃ hB hP ha.le hb
    have := hB.κ₃₂_mem.2
    simp only [gs_phase, gs_Phase.X, gs_ph3, rot, Prod.snd_add]
    linarith
  · rw [gs_path_eq_phase hP (gs_piece₃ ha.le hb)]
    obtain ⟨s, rfl⟩ : ∃ s, t = π / 2 - s := ⟨π / 2 - t, by ring⟩
    have := gs_ineq_y₂ hB hP (s := s) (by linarith [hO.1]) (by linarith)
    have := hB.κ₄₂_mem.2
    simp only [gs_phase, gs_Phase.X, gs_ph4, rot, Prod.snd_add, sin_pi_div_two_sub,
      cos_pi_div_two_sub, gs_d₁ hP, gs_d₂ hP]
    nlinarith
  · rw [gs_path_eq_phase hP (gs_piece₄ h.le)]
    obtain ⟨s, rfl⟩ : ∃ s, t = π / 2 - s := ⟨π / 2 - t, by ring⟩
    have := gs_ineq_y₁ hB (s := s) (by linarith) (by linarith)
    have := hB.κ₅₂_mem.2
    simp only [gs_phase, gs_Phase.X, gs_ph5, rot, Prod.snd_add, sin_pi_div_two_sub,
      cos_pi_div_two_sub, gs_e₁ hP, gs_e₂ hP, gs_a₂ hP]
    nlinarith

end MovingSofaOptimality.GerverParams
