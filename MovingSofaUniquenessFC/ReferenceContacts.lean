module

public import MovingSofaUniquenessFC.ReferenceRadius

/-!
# Exact boundary coordinates and normalization of the integral reference

Integrating the paper contact derivative recovers the reference's X and Y.
Reflection recovers the opposite outer contact. The equality
`2*k3.x = 4*X(0)-2`, which is needed in the reference path, follows from
its second equation; it is not inferred from an illustration or a numerical
approximation.
-/

@[expose] public section
noncomputable section

open Set Real MovingSofaOptimality MovingSofaOptimality.GerverParams

namespace MovingSofaUniquenessFC.Reference.Data

private theorem rot_frame_constant (t a b : ℝ) :
    rot t (a * cos t + b * sin t, -a * sin t + b * cos t) = (a, b) := by
  have hframe : (a * cos t + b * sin t, -a * sin t + b * cos t) = rot (-t) (a, b) := by
    ext <;> simp only [rot, cos_neg, sin_neg] <;> ring
  rw [hframe, rot_rot_neg]

/-- The final outer contact is constant over the entire last phase. -/
theorem contactC_last {D : Data} (hD : D.Valid) {t : ℝ}
    (ht : π / 2 - D.φ ≤ t) :
    contactC D.toPaper.path t = (2 * D.k3.1 - 1, 0) := by
  rw [gs_contactC_eq (paper_solution hD).1 (show gs_piece D.toPaper 4 t from ht)]
  ext <;> simp only [gs_phase, gs_ph5, gs_Phase.C, toPaper, rot, Prod.fst_add, Prod.snd_add]
  · linear_combination (-D.a1) * sin_sq_add_cos_sq t
  · linear_combination (-1 / 4 : ℝ) * sin_sq_add_cos_sq t

/-- The first outer contact is fixed, including the first junction. -/
theorem contactA_first {D : Data} (hD : D.Valid) {t : ℝ} (ht : t ≤ D.φ) :
    contactA D.toPaper.path t = (1, 0) := by
  rw [gs_contactA_eq (paper_solution hD).1 (show gs_piece D.toPaper 0 t from ht)]
  change rot t (D.a1 * cos t + (-1 / 4) * sin t - 1 + 1,
      -D.a1 * sin t + (-1 / 4) * cos t) + D.k1 = _
  rw [sub_add_cancel, rot_frame_constant]
  ext <;> simp only [k1, Prod.fst_add, Prod.snd_add] <;> ring

/-- The initial outer contact fixes the integral's height normalization. -/
theorem contactC_zero {D : Data} (hD : D.Valid) :
    contactC D.toPaper.path 0 = (1 - 2 * D.a1, 1) := by
  rw [gs_contactC_eq (paper_solution hD).1
    (show gs_piece D.toPaper 0 0 from hD.phi_pos.le)]
  simp only [gs_phase, gs_ph1, gs_Phase.C, toPaper, k1, rot, sin_zero, cos_zero]
  ext <;> simp <;> ring

/-- Every parameter belongs to one of the five closed phase intervals. -/
private theorem exists_piece (P : GerverParams) (t : ℝ) :
    ∃ i : Fin 5, gs_piece P i t := by
  by_cases h1 : t ≤ P.φ
  · exact ⟨0, h1⟩
  by_cases h2 : t ≤ P.θ
  · exact ⟨1, ⟨(lt_of_not_ge h1).le, h2⟩⟩
  by_cases h3 : t ≤ π / 2 - P.θ
  · exact ⟨2, ⟨(lt_of_not_ge h2).le, h3⟩⟩
  by_cases h4 : t ≤ π / 2 - P.φ
  · exact ⟨3, ⟨(lt_of_not_ge h3).le, h4⟩⟩
  exact ⟨4, (lt_of_not_ge h4).le⟩

private theorem reflected_piece (D : Data) (i : Fin 5) {t : ℝ}
    (ht : gs_piece D.toPaper i t) :
    gs_piece D.toPaper (4 - (i : ℕ)) (π / 2 - t) := by
  obtain ⟨k, hk⟩ := i
  interval_cases k <;> simp only [Nat.sub_zero, gs_piece, toPaper] at ht ⊢
  · linarith
  · constructor <;> linarith [ht.1, ht.2]
  · constructor <;> linarith [ht.1, ht.2]
  · constructor <;> linarith [ht.1, ht.2]
  · linarith

/-- The reflection identity is algebraic at the level of each phase. -/
private theorem phase_contact_reflection (D : Data) (i : Fin 5) (t : ℝ) :
    (D.toPaper.gs_phase i).A t =
      D.reflect ((D.toPaper.gs_phase (4 - (i : ℕ))).C (π / 2 - t)) := by
  obtain ⟨k, hk⟩ := i
  interval_cases k <;> ext <;>
    simp only [Nat.sub_zero, gs_phase, gs_ph1, gs_ph2, gs_ph3, gs_ph4, gs_ph5,
      gs_Phase.A, gs_Phase.C, toPaper, reflect, k1, rot,
      cos_pi_div_two_sub, sin_pi_div_two_sub, Prod.fst_add, Prod.snd_add] <;> ring

/-- Reflection relates the actual glued contacts, also at their junctions. -/
theorem contactA_reflection {D : Data} (hD : D.Valid) (t : ℝ) :
    contactA D.toPaper.path t = D.reflect (contactC D.toPaper.path (π / 2 - t)) := by
  obtain ⟨i, hi⟩ := exists_piece D.toPaper t
  rw [gs_contactA_eq (paper_solution hD).1 hi,
    gs_contactC_eq (paper_solution hD).1 (reflected_piece D i hi)]
  exact phase_contact_reflection D i t

/-- The reference integrals are the two coordinates of the paper contact C. -/
theorem contactC_integral_coordinates {D : Data} (hD : D.Valid) (t : ℝ) :
    contactC D.toPaper.path t = (2 * D.k3.1 - D.boundaryX t, D.boundaryY t) := by
  obtain ⟨hx, hy⟩ := contactC_integrals hD t (π / 2 - D.φ)
  rw [contactC_last hD le_rfl] at hx hy
  ext <;> simp only [boundaryX, boundaryY] at hx hy ⊢ <;> linarith

/-- The opposite contact gives the reference boundary evaluated at L-t. -/
theorem contactA_integral_coordinates {D : Data} (hD : D.Valid) (t : ℝ) :
    contactA D.toPaper.path t = (D.boundaryX (π / 2 - t), D.boundaryY (π / 2 - t)) := by
  rw [contactA_reflection hD, contactC_integral_coordinates hD]
  ext <;> simp only [reflect]
  ring

theorem boundaryY_zero {D : Data} (hD : D.Valid) : D.boundaryY 0 = 1 := by
  have h := congrArg Prod.snd (contactC_integral_coordinates hD 0)
  rw [contactC_zero hD] at h
  exact h.symm

theorem boundaryX_zero {D : Data} (hD : D.Valid) :
    D.boundaryX 0 = 2 * D.k3.1 - 1 + 2 * D.a1 := by
  have h := congrArg Prod.fst (contactC_integral_coordinates hD 0)
  rw [contactC_zero hD] at h
  linarith

/-- The scalar normalization occurring in the exact upstream path formula. -/
theorem horizontal_normalization {D : Data} (hD : D.Valid) :
    2 * D.k3.1 = 4 * D.boundaryX 0 - 2 := by
  rw [boundaryX_zero hD]
  have h := k3_fst hD
  linarith

end MovingSofaUniquenessFC.Reference.Data
