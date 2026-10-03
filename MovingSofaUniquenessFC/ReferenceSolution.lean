module

public import MovingSofaUniquenessFC.ReferenceParameters

/-!
# The reference equations imply all of Romik's matching conditions

The first contact error is exactly `(-eq2/2, -eq1/2)`. The second contact and
the two remaining phase junctions follow from an explicit reflection. Thus
this conversion does not call the global shape-uniqueness theorem, a numerical
root finder, or an assertion that the two Gerver constructions are the same.

The strict upper angle bound is stated explicitly. `Valid` alone currently
supplies only `theta <= pi/4`; no global localization is hidden here.
Uncompiled Lean source.
-/

@[expose] public section
noncomputable section

open Real Set MovingSofaOptimality MovingSofaOptimality.GerverParams

namespace MovingSofaUniquenessFC.Reference.Data

/-- Reflection about the center line of the constructed five-phase path. -/
def reflect (D : Data) (q : ℝ × ℝ) : ℝ × ℝ := (2 * D.k3.1 - q.1, q.2)

/-- Reversal of parameter direction changes the reflected tangent's sign. -/
def reverseTangent (q : ℝ × ℝ) : ℝ × ℝ := (q.1, -q.2)

theorem x5_reflection (D : Data) (t : ℝ) :
    D.toPaper.x₅ (π / 2 - t) = D.reflect (D.toPaper.x₁ t) := by
  ext <;> simp only [toPaper, GerverParams.x₅, GerverParams.x₁, reflect, k1,
    rot, sin_pi_div_two_sub, cos_pi_div_two_sub, Prod.fst_add, Prod.snd_add] <;> ring

theorem x4_reflection (D : Data) (t : ℝ) :
    D.toPaper.x₄ (π / 2 - t) = D.reflect (D.toPaper.x₂ t) := by
  ext <;> simp only [toPaper, GerverParams.x₄, GerverParams.x₂, reflect,
    rot, sin_pi_div_two_sub, cos_pi_div_two_sub, Prod.fst_add, Prod.snd_add] <;> ring

theorem x3_reflection (D : Data) (t : ℝ) :
    D.toPaper.x₃ (π / 2 - t) = D.reflect (D.toPaper.x₃ t) := by
  ext <;> simp only [toPaper, GerverParams.x₃, reflect,
    rot, sin_pi_div_two_sub, cos_pi_div_two_sub, Prod.fst_add, Prod.snd_add] <;> ring

theorem dx5_reflection (D : Data) (t : ℝ) :
    deriv D.toPaper.x₅ (π / 2 - t) = reverseTangent (deriv D.toPaper.x₁ t) := by
  rw [(rom_hasDerivAt_x₅ _ _).deriv, (rom_hasDerivAt_x₁ _ _).deriv]
  ext <;> simp only [toPaper, reverseTangent, rot,
    sin_pi_div_two_sub, cos_pi_div_two_sub] <;> ring

theorem dx4_reflection (D : Data) (t : ℝ) :
    deriv D.toPaper.x₄ (π / 2 - t) = reverseTangent (deriv D.toPaper.x₂ t) := by
  rw [(rom_hasDerivAt_x₄ _ _).deriv, (rom_hasDerivAt_x₂ _ _).deriv]
  ext <;> simp only [toPaper, reverseTangent, rot,
    sin_pi_div_two_sub, cos_pi_div_two_sub] <;> ring

theorem dx3_reflection (D : Data) (t : ℝ) :
    deriv D.toPaper.x₃ (π / 2 - t) = reverseTangent (deriv D.toPaper.x₃ t) := by
  rw [(rom_hasDerivAt_x₃ _ _).deriv, (rom_hasDerivAt_x₃ _ _).deriv]
  ext <;> simp only [toPaper, reverseTangent, rot,
    sin_pi_div_two_sub, cos_pi_div_two_sub] <;> ring

/-- Evaluate the fourth-phase inner contact in its own rotating frame. -/
theorem contactB_four (D : Data) (t : ℝ) :
    contactB D.toPaper.x₄ (π / 2 - t) =
      rot (π / 2 - t) ((D.A + t - D.φ - 1) / 2, -1 / 2) +
        (2 * D.k3.1 - D.k2.1, D.k2.2) := by
  rw [contactB, (rom_hasDerivAt_x₄ _ _).deriv, rom_dot_rot_uvec]
  ext <;> simp only [toPaper, GerverParams.x₄, b1, rot, vvec,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem contactD_two (D : Data) (t : ℝ) :
    contactD D.toPaper.x₂ t =
      rot t (-1 / 2, (D.A + t - D.φ - 1) / 2) + D.k2 := by
  rw [contactD, (rom_hasDerivAt_x₂ _ _).deriv, rom_dot_rot_vvec]
  ext <;> simp only [toPaper, GerverParams.x₂, b1, rot, uvec,
    Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem contact_reflection (D : Data) (t : ℝ) :
    contactD D.toPaper.x₂ t = D.reflect (contactB D.toPaper.x₄ (π / 2 - t)) := by
  rw [contactD_two, contactB_four]
  ext <;> simp only [reflect, rot, sin_pi_div_two_sub, cos_pi_div_two_sub,
    Prod.fst_add, Prod.snd_add] <;> ring

/-- Both contact residuals, before assuming any of the four equations. -/
theorem contact_error (D : Data) :
    D.toPaper.x₂ D.φ - contactB D.toPaper.x₄ (π / 2 - D.θ) =
      (-eq2 D.A D.B D.φ D.θ / 2, -eq1 D.A D.B D.φ D.θ / 2) := by
  rw [x2_phi, contactB_four]
  ext <;> simp only [k3, rot, sin_pi_div_two_sub, cos_pi_div_two_sub,
    Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, eq1, eq2] <;> ring

theorem contact_first {D : Data} (h : D.Valid) :
    D.toPaper.x₁ D.φ = contactB D.toPaper.x₄ (π / 2 - D.θ) := by
  have h1 := (spec_iff.mp h).2.2.2.2.2.1
  have h2 := (spec_iff.mp h).2.2.2.2.2.2.1
  have he := contact_error D
  rw [h1, h2] at he
  have hz : D.toPaper.x₂ D.φ - contactB D.toPaper.x₄ (π / 2 - D.θ) = 0 := by
    rw [he]
    ext <;> simp
  exact (continuity_phi h).trans (sub_eq_zero.mp hz)

theorem contact_second {D : Data} (h : D.Valid) :
    D.toPaper.x₅ (π / 2 - D.φ) = contactD D.toPaper.x₂ D.θ := by
  rw [x5_reflection, contact_reflection]
  exact congrArg D.reflect (contact_first h)

/-- Explicit construction of a solution of the paper's 22-parameter system.
The strict upper angle premise is supplied by any reference solution in the
paper's box, but is not silently inferred on the whole upstream triangle. -/
theorem toPaper_isSolution {D : Data} (h : D.Valid) (hθ : D.θ < π / 4) :
    D.toPaper.IsSolution := by
  have h34 : D.toPaper.x₃ (π / 2 - D.θ) = D.toPaper.x₄ (π / 2 - D.θ) := by
    rw [x3_reflection, x4_reflection]
    exact congrArg D.reflect (continuity_theta h).symm
  have hd34 : deriv D.toPaper.x₃ (π / 2 - D.θ) =
      deriv D.toPaper.x₄ (π / 2 - D.θ) := by
    rw [dx3_reflection, dx4_reflection]
    exact congrArg reverseTangent (derivative_theta h).symm
  have h45 : D.toPaper.x₄ (π / 2 - D.φ) = D.toPaper.x₅ (π / 2 - D.φ) := by
    rw [x4_reflection, x5_reflection]
    exact congrArg D.reflect (continuity_phi h).symm
  have hd45 : deriv D.toPaper.x₄ (π / 2 - D.φ) =
      deriv D.toPaper.x₅ (π / 2 - D.φ) := by
    rw [dx4_reflection, dx5_reflection]
    exact congrArg reverseTangent (derivative_phi h).symm
  refine ⟨h.phi_pos, h.phi_lt_theta, hθ, rfl, ?_, rfl, rfl, ?_,
    rfl, rfl, rfl, continuity_phi h, derivative_phi h,
    continuity_theta h, derivative_theta h, h34, hd34, h45, hd45,
    contact_first h, contact_second h⟩
  · norm_num [toPaper]
  · simp only [toPaper]
    ring

/-- Local parameter uniqueness may now be used with its actual hypotheses. -/
theorem toPaper_eq_of_same_box {D E : Data} (hD : D.Valid) (hE : E.Valid)
    (hDb : D.toPaper.InBox) (hEb : E.toPaper.InBox) : D = E := by
  have hDθ : D.θ < π / 4 := by
    have h69 : D.θ ≤ 0.69 := hDb.2.2
    linarith [pi_gt_three]
  have hEθ : E.θ < π / 4 := by
    have h69 : E.θ ≤ 0.69 := hEb.2.2
    linarith [pi_gt_three]
  have hp := romik_unique (toPaper_isSolution hD hDθ) hDb
    (toPaper_isSolution hE hEθ) hEb
  have hφ : D.φ = E.φ := congrArg GerverParams.φ hp
  have hθ : D.θ = E.θ := congrArg GerverParams.θ hp
  have hA : D.A = E.A := by
    rw [← D.coefficients_roundtrip.1, hp, E.coefficients_roundtrip.1]
  have hB : D.B = E.B := by
    rw [← D.coefficients_roundtrip.2, hp, E.coefficients_roundtrip.2]
  cases D
  cases E
  simp_all

end MovingSofaUniquenessFC.Reference.Data
