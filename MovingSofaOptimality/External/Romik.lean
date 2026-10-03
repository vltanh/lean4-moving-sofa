module

public import MovingSofaOptimality.Gerver.Defs
public import MovingSofaOptimality.Gerver.Bounds
public import MovingSofaOptimality.External.Romik.Fix

/-!
# Existence and uniqueness of the parameters of Gerver's sofa

Romik (Section 4) computes the parameters of Gerver's sofa numerically and states that the solution
of his system with `0 < φ < θ < π/4` is unique. This file proves that the system
`GerverParams.IsSolution` has exactly one solution with `φ ∈ [0.039, 0.04]` and `θ ∈ [0.68, 0.69]`,
and gives tight enclosures of its parameters for the numerical verifications of
`MovingSofaOptimality.Gerver.*`.

**Reduction.** Write `𝐱_i(t) = R_t w_i(t) + κ_i`. Then `𝐱_i'(t) = R_t (w_i' + J w_i)(t)` with
`J (a, b) = (-b, a)` (`rom_hasDerivAt_x₁` … `rom_hasDerivAt_x₅`), so the derivative conditions are
linear equations in the parameters. Together with the symmetry and initial conditions they determine
all the parameters from the two angles: `a₁ = N/D`, `b₁ = β₀ - a₁ sin φ`, `b₂ = K - (2 + θ) b₁`,
`c₁ = π/2 - 2 - 2 b₁`, and the continuity conditions give `κ₂, κ₃` and `κ₄ = (2 κ₃₁ - κ₂₁, κ₂₂)`,
`κ₅ = (2 κ₃₁ - 1 + a₁, 1/4)` (`rom_eq_mk`: a solution in the box equals `rom_mk φ θ`). The first
contact condition then reads `U + b₁ V = 0` (`rom_mk_contact1_iff`), i.e.
`H(φ, θ) = D (U + b₁ V) = 0` for the explicit system `H` of `MovingSofaOptimality.External.Romik.Num`.
Conversely, for every zero of `H` in the box, `rom_mk φ θ` satisfies all of Romik's equations
(`rom_mk_isSolution`): the remaining derivative conditions and the second contact condition follow
from the left-right symmetry, as Romik says (they are polynomial identities in the explicit
parameters).

**Numerics.** `H` has a unique zero in the box, which lies within `10⁻¹⁰` of
`(0.0391773648, 0.6813015094)` (`MovingSofaOptimality.External.Romik.Fix`: a Newton-type map is a contraction on
the box, by interval arithmetic). This gives `romik_exists` and `romik_unique`, and the enclosures
`rom_phi_mem`, `rom_theta_mem`, `rom_a1_mem`, … and `romik_bounds` of the parameters.
-/

@[expose] public section

open Real Set

namespace MovingSofaOptimality

namespace GerverParams

/-! ### Derivatives of the five pieces of the rotation path -/

/-- The derivative of `t ↦ R_t (f t, g t) + κ` is `R_t (f' - g, g' + f)`. -/
theorem rom_hasDerivAt_rot {f g : ℝ → ℝ} {f' g' t : ℝ} (κ : ℝ × ℝ) (hf : HasDerivAt f f' t)
    (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => rot s (f s, g s) + κ) (rot t (f' - g t, g' + f t)) t := by
  have h1 : HasDerivAt (fun s => cos s * f s - sin s * g s + κ.1)
      (-sin t * f t + cos t * f' - (cos t * g t + sin t * g')) t :=
    (((hasDerivAt_cos t).fun_mul hf).fun_sub ((hasDerivAt_sin t).fun_mul hg)).add_const κ.1
  have h2 : HasDerivAt (fun s => sin s * f s + cos s * g s + κ.2)
      (cos t * f t + sin t * f' + (-sin t * g t + cos t * g')) t :=
    (((hasDerivAt_sin t).fun_mul hf).fun_add ((hasDerivAt_cos t).fun_mul hg)).add_const κ.2
  have e1 : (fun s => rot s (f s, g s) + κ) =
      fun s => (cos s * f s - sin s * g s + κ.1, sin s * f s + cos s * g s + κ.2) := by
    funext s
    ext <;> simp [rot]
  have e2 : rot t (f' - g t, g' + f t) = (-sin t * f t + cos t * f' - (cos t * g t + sin t * g'),
      cos t * f t + sin t * f' + (-sin t * g t + cos t * g')) := by
    ext <;> simp only [rot] <;> ring
  rw [e1, e2]
  exact h1.prodMk h2

/-- The derivative of `t ↦ t² / 4`. -/
theorem rom_hasDerivAt_sq_div (t : ℝ) : HasDerivAt (fun s : ℝ => s ^ 2 / 4) (t / 2) t := by
  convert (hasDerivAt_pow 2 t).div_const 4 using 1
  norm_num; ring

/-- The derivative of the first piece (SOL1) of the rotation path. -/
theorem rom_hasDerivAt_x₁ (P : GerverParams) (t : ℝ) :
    HasDerivAt P.x₁ (rot t (2 * P.a₂ * cos t - 2 * P.a₁ * sin t + 1 / 2,
      2 * P.a₁ * cos t + 2 * P.a₂ * sin t - 1)) t := by
  have hf : HasDerivAt (fun s => P.a₁ * cos s + P.a₂ * sin s - 1)
      (P.a₁ * -sin t + P.a₂ * cos t) t :=
    (((hasDerivAt_cos t).const_mul P.a₁).fun_add ((hasDerivAt_sin t).const_mul P.a₂)).sub_const 1
  have hg : HasDerivAt (fun s => -P.a₂ * cos s + P.a₁ * sin s - 1 / 2)
      (-P.a₂ * -sin t + P.a₁ * cos t) t :=
    (((hasDerivAt_cos t).const_mul (-P.a₂)).fun_add ((hasDerivAt_sin t).const_mul P.a₁)).sub_const
      (1 / 2)
  refine (rom_hasDerivAt_rot P.κ₁ hf hg).congr_deriv ?_
  congr 1
  ext <;> ring

/-- The derivative of the second piece (SOL2) of the rotation path. -/
theorem rom_hasDerivAt_x₂ (P : GerverParams) (t : ℝ) :
    HasDerivAt P.x₂ (rot t (2 * P.b₁ + 1 - t, 1 / 2 - t ^ 2 / 4 + P.b₁ * t + P.b₂)) t := by
  have hf : HasDerivAt (fun s => -s ^ 2 / 4 + P.b₁ * s + P.b₂) (-(t / 2) + P.b₁ * 1) t := by
    have := (((rom_hasDerivAt_sq_div t).fun_neg).fun_add
      ((hasDerivAt_id' t).const_mul P.b₁)).add_const P.b₂
    convert this using 1
    funext s; ring
  have hg : HasDerivAt (fun s => s / 2 - P.b₁ - 1) (1 / 2) t :=
    (((hasDerivAt_id' t).div_const 2).sub_const P.b₁).sub_const 1
  refine (rom_hasDerivAt_rot P.κ₂ hf hg).congr_deriv ?_
  congr 1
  ext <;> ring

/-- The derivative of the third piece (SOL3) of the rotation path. -/
theorem rom_hasDerivAt_x₃ (P : GerverParams) (t : ℝ) :
    HasDerivAt P.x₃ (rot t (-1 - P.c₂ - t, 1 + P.c₁ - t)) t := by
  have hf : HasDerivAt (fun s => P.c₁ - s) (-1) t := (hasDerivAt_id' t).const_sub P.c₁
  have hg : HasDerivAt (fun s => P.c₂ + s) 1 t := (hasDerivAt_id' t).const_add P.c₂
  refine (rom_hasDerivAt_rot P.κ₃ hf hg).congr_deriv ?_
  congr 1
  ext <;> ring

/-- The derivative of the fourth piece (SOL4) of the rotation path. -/
theorem rom_hasDerivAt_x₄ (P : GerverParams) (t : ℝ) :
    HasDerivAt P.x₄ (rot t (t ^ 2 / 4 - P.d₁ * t - P.d₂ - 1 / 2, 2 * P.d₁ - 1 - t)) t := by
  have hf : HasDerivAt (fun s => -s / 2 + P.d₁ - 1) (-1 / 2) t := by
    have := (((hasDerivAt_id' t).fun_neg.div_const 2).add_const P.d₁).sub_const 1
    convert this using 1
  have hg : HasDerivAt (fun s => -s ^ 2 / 4 + P.d₁ * s + P.d₂) (-(t / 2) + P.d₁ * 1) t := by
    have := (((rom_hasDerivAt_sq_div t).fun_neg).fun_add
      ((hasDerivAt_id' t).const_mul P.d₁)).add_const P.d₂
    convert this using 1
    funext s; ring
  refine (rom_hasDerivAt_rot P.κ₄ hf hg).congr_deriv ?_
  congr 1
  ext <;> ring

/-- The derivative of the fifth piece (SOL5) of the rotation path. -/
theorem rom_hasDerivAt_x₅ (P : GerverParams) (t : ℝ) :
    HasDerivAt P.x₅ (rot t (2 * P.e₂ * cos t - 2 * P.e₁ * sin t + 1,
      2 * P.e₁ * cos t + 2 * P.e₂ * sin t - 1 / 2)) t := by
  have hf : HasDerivAt (fun s => P.e₁ * cos s + P.e₂ * sin s - 1 / 2)
      (P.e₁ * -sin t + P.e₂ * cos t) t :=
    (((hasDerivAt_cos t).const_mul P.e₁).fun_add ((hasDerivAt_sin t).const_mul P.e₂)).sub_const
      (1 / 2)
  have hg : HasDerivAt (fun s => -P.e₂ * cos s + P.e₁ * sin s - 1)
      (-P.e₂ * -sin t + P.e₁ * cos t) t :=
    (((hasDerivAt_cos t).const_mul (-P.e₂)).fun_add ((hasDerivAt_sin t).const_mul P.e₁)).sub_const 1
  refine (rom_hasDerivAt_rot P.κ₅ hf hg).congr_deriv ?_
  congr 1
  ext <;> ring

/-- The rotation `R_t` is injective. -/
theorem rom_rot_inj {t : ℝ} {u v : ℝ × ℝ} (h : rot t u = rot t v) : u = v := by
  rw [← rot_neg_rot t u, h, rot_neg_rot]

/-- `⟨R_t v, u_t⟩ = v₁`. -/
theorem rom_dot_rot_uvec (t : ℝ) (v : ℝ × ℝ) : dot (rot t v) (uvec t) = v.1 := by
  simp only [dot, rot, uvec]
  linear_combination v.1 * cos_sq_add_sin_sq t

/-- `⟨R_t v, v_t⟩ = v₂`. -/
theorem rom_dot_rot_vvec (t : ℝ) (v : ℝ × ℝ) : dot (rot t v) (vvec t) = v.2 := by
  simp only [dot, rot, vvec]
  linear_combination v.2 * sin_sq_add_cos_sq t

/-! ### Reduction to the angles -/

/-- The parameters determined by the angles `(φ, θ)`: the unique solution of all of Romik's
equations except the contact conditions (given `D(φ, θ) ≠ 0`). -/
noncomputable def rom_mk (φ θ : ℝ) : GerverParams where
  φ := φ
  θ := θ
  a₁ := rom_a₁ φ θ (cos φ) (sin φ) π
  a₂ := -1 / 4
  b₁ := rom_b₁ φ θ (cos φ) (sin φ) π
  b₂ := rom_b₂ φ θ (cos φ) (sin φ) π
  c₁ := rom_c₁ φ θ (cos φ) (sin φ) π
  c₂ := rom_c₁ φ θ (cos φ) (sin φ) π - π / 2
  d₁ := π / 4 - rom_b₁ φ θ (cos φ) (sin φ) π
  d₂ := rom_b₂ φ θ (cos φ) (sin φ) π + π / 4 * (2 * rom_b₁ φ θ (cos φ) (sin φ) π - π / 4)
  e₁ := rom_a₁ φ θ (cos φ) (sin φ) π
  e₂ := 1 / 4
  κ₁ := (1 - rom_a₁ φ θ (cos φ) (sin φ) π, 1 / 4)
  κ₂ := (rom_κ₂₁ φ θ (cos φ) (sin φ) π, rom_κ₂₂ φ θ (cos φ) (sin φ) π)
  κ₃ := (rom_κ₃₁ φ θ (cos φ) (sin φ) (cos θ) (sin θ) π,
    rom_κ₃₂ φ θ (cos φ) (sin φ) (cos θ) (sin θ) π)
  κ₄ := (rom_κ₄₁ φ θ (cos φ) (sin φ) (cos θ) (sin θ) π, rom_κ₂₂ φ θ (cos φ) (sin φ) π)
  κ₅ := (rom_κ₅₁ φ θ (cos φ) (sin φ) (cos θ) (sin θ) π, 1 / 4)

/-- `D(φ, θ) > 0` on the box. -/
theorem rom_D_pos {φ θ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) (hθ : θ ∈ Icc (0.68 : ℝ) 0.69) :
    0 < rom_D φ θ (cos φ) (sin φ) := by
  have h := rom_D_box hφ hθ (rom_cos_box hφ) (rom_sin_box hφ)
  linarith [h.1]

/-- A solution in the box is determined by its angles. -/
theorem rom_eq_mk {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) :
    P = rom_mk P.φ P.θ := by
  obtain ⟨φ, θ, A1, A2, B1, B2, C1, C2, D1, D2, E1, E2, ⟨k11, k12⟩, ⟨k21, k22⟩, ⟨k31, k32⟩,
    ⟨k41, k42⟩, ⟨k51, k52⟩⟩ := P
  obtain ⟨-, -, -, he1, he2, hd1, hd2, hc2, hk11, hk12, ha2, c12, d12, c23, d23, c34, -, c45, -, -,
    -⟩ := hP
  obtain ⟨hφ, hθ⟩ := hb
  dsimp only at he1 he2 hd1 hd2 hc2 hk11 hk12 ha2 hφ hθ
  subst E1 E2 D1 D2 C2 k11 k12 A2
  have hD := rom_D_pos hφ hθ
  rw [(rom_hasDerivAt_x₁ _ φ).deriv, (rom_hasDerivAt_x₂ _ φ).deriv] at d12
  rw [(rom_hasDerivAt_x₂ _ θ).deriv, (rom_hasDerivAt_x₃ _ θ).deriv] at d23
  have E12 := rom_rot_inj d12
  have E23 := rom_rot_inj d23
  simp only [Prod.mk.injEq] at E12 E23
  obtain ⟨eq1, eq2⟩ := E12
  obtain ⟨eq3, eq4⟩ := E23
  have hb1 : B1 = (φ - 1 / 2 - cos φ / 2) / 2 - sin φ * A1 := by
    linear_combination (-1 / 2 : ℝ) * eq1
  subst hb1
  have hc1 : C1 = π / 2 - 2 - 2 * ((φ - 1 / 2 - cos φ / 2) / 2 - sin φ * A1) := by
    linear_combination eq3
  subst hc1
  have hb2 : B2 = rom_K θ π - (2 + θ) * ((φ - 1 / 2 - cos φ / 2) / 2 - sin φ * A1) := by
    simp only [rom_K]
    linear_combination eq4
  subst hb2
  have hmul : A1 * rom_D φ θ (cos φ) (sin φ) = rom_N φ θ (cos φ) (sin φ) π := by
    simp only [rom_D, rom_N, rom_β₀]
    linear_combination eq2
  have ha1 : A1 = rom_a₁ φ θ (cos φ) (sin φ) π := by
    rw [rom_a₁, eq_div_iff hD.ne']; exact hmul
  subst ha1
  clear d12 d23 eq1 eq2 eq3 eq4
  simp only [GerverParams.x₁, GerverParams.x₂, GerverParams.x₃, GerverParams.x₄, GerverParams.x₅,
    rot, cos_pi_div_two_sub, sin_pi_div_two_sub, Prod.mk_add_mk, Prod.mk.injEq, rom_K]
    at c12 c23 c34 c45
  obtain ⟨c12a, c12b⟩ := c12
  obtain ⟨c23a, c23b⟩ := c23
  obtain ⟨c34a, c34b⟩ := c34
  obtain ⟨c45a, c45b⟩ := c45
  simp only [rom_mk]
  congr 1
  · norm_num
  · simp only [rom_κ₂₁, rom_κ₂₂, rom_Δ₁, rom_Δ₂, rom_b₁, rom_b₂, rom_β₀, rom_K, Prod.mk.injEq]
    constructor
    · linear_combination (-1 : ℝ) * c12a
    · linear_combination (-1 : ℝ) * c12b
  · simp only [rom_κ₃₁, rom_κ₃₂, rom_κ₂₁, rom_κ₂₂, rom_Δ₁, rom_Δ₂, rom_b₁, rom_b₂, rom_β₀, rom_K,
      Prod.mk.injEq]
    constructor
    · linear_combination (-1 : ℝ) * c23a + (-1 : ℝ) * c12a
    · linear_combination (-1 : ℝ) * c23b + (-1 : ℝ) * c12b
  · simp only [rom_κ₄₁, rom_κ₃₁, rom_κ₂₁, rom_κ₂₂, rom_Δ₁, rom_Δ₂, rom_b₁, rom_b₂, rom_β₀, rom_K,
      Prod.mk.injEq]
    constructor
    · linear_combination (-1 : ℝ) * c34a + (-1 : ℝ) * c23a + (-1 : ℝ) * c12a
    · linear_combination (-1 : ℝ) * c34b + (-1 : ℝ) * c23b + (-1 : ℝ) * c12b
  · simp only [rom_κ₅₁, rom_κ₃₁, rom_κ₂₁, rom_Δ₁, rom_Δ₂, rom_b₁, rom_b₂, rom_β₀, rom_K,
      Prod.mk.injEq]
    constructor
    · linear_combination (-1 : ℝ) * c45a + (-1 : ℝ) * c34a + (-1 : ℝ) * c23a + (-1 : ℝ) * c12a
    · linear_combination (-1 : ℝ) * c45b + (-1 : ℝ) * c34b + (-1 : ℝ) * c23b + (-1 : ℝ) * c12b

/-- `a₁ D = N`. -/
theorem rom_a₁_mul {φ θ : ℝ} (hD : 0 < rom_D φ θ (cos φ) (sin φ)) :
    rom_a₁ φ θ (cos φ) (sin φ) π * rom_D φ θ (cos φ) (sin φ) = rom_N φ θ (cos φ) (sin φ) π := by
  rw [rom_a₁, div_mul_cancel₀ _ hD.ne']

/-- `H = D (U + b₁ V)`. -/
theorem rom_H_eq {φ θ : ℝ} (hD : 0 < rom_D φ θ (cos φ) (sin φ)) :
    rom_H1 φ θ (cos φ) (sin φ) (cos θ) (sin θ) π = rom_D φ θ (cos φ) (sin φ) *
      (rom_U1 φ θ (cos φ) (sin φ) (cos θ) (sin θ) π +
        rom_b₁ φ θ (cos φ) (sin φ) π * rom_V1 φ θ (cos φ) (sin φ) (sin θ)) ∧
    rom_H2 φ θ (cos φ) (sin φ) (cos θ) (sin θ) π = rom_D φ θ (cos φ) (sin φ) *
      (rom_U2 φ θ (cos φ) (sin φ) (cos θ) (sin θ) π +
        rom_b₁ φ θ (cos φ) (sin φ) π * rom_V2 φ θ (cos φ) (sin φ) (cos θ)) := by
  have h := rom_a₁_mul hD
  simp only [rom_H1, rom_H2, rom_Nb, rom_b₁, rom_D, rom_N, rom_β₀] at h ⊢
  constructor
  · linear_combination (sin φ * rom_V1 φ θ (cos φ) (sin φ) (sin θ)) * h
  · linear_combination (sin φ * rom_V2 φ θ (cos φ) (sin φ) (cos θ)) * h

/-- The first contact condition for `rom_mk φ θ` is `U + b₁ V = 0`. -/
theorem rom_mk_contact1_iff (φ θ : ℝ) :
    (rom_mk φ θ).x₁ φ = contactB (rom_mk φ θ).x₄ (π / 2 - θ) ↔
      rom_U1 φ θ (cos φ) (sin φ) (cos θ) (sin θ) π +
          rom_b₁ φ θ (cos φ) (sin φ) π * rom_V1 φ θ (cos φ) (sin φ) (sin θ) = 0 ∧
        rom_U2 φ θ (cos φ) (sin φ) (cos θ) (sin θ) π +
          rom_b₁ φ θ (cos φ) (sin φ) π * rom_V2 φ θ (cos φ) (sin φ) (cos θ) = 0 := by
  rw [contactB, (rom_hasDerivAt_x₄ _ _).deriv, rom_dot_rot_uvec]
  simp only [GerverParams.x₁, GerverParams.x₄, rom_mk, rot, vvec, cos_pi_div_two_sub,
    sin_pi_div_two_sub, Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
  simp only [rom_U1, rom_U2, rom_V1, rom_V2, rom_κ₄₁, rom_κ₃₁, rom_κ₂₁, rom_κ₂₂, rom_Δ₁, rom_Δ₂,
    rom_b₂, rom_b₁, rom_β₀, rom_K]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linear_combination (-1 : ℝ) * h1, by linear_combination (-1 : ℝ) * h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linear_combination (-1 : ℝ) * h1, by linear_combination (-1 : ℝ) * h2⟩

/-- The second contact condition for `rom_mk φ θ` follows from `U + b₁ V = 0` (left-right
symmetry). -/
theorem rom_mk_contact2 {φ θ : ℝ}
    (h1 : rom_U1 φ θ (cos φ) (sin φ) (cos θ) (sin θ) π +
      rom_b₁ φ θ (cos φ) (sin φ) π * rom_V1 φ θ (cos φ) (sin φ) (sin θ) = 0)
    (h2 : rom_U2 φ θ (cos φ) (sin φ) (cos θ) (sin θ) π +
      rom_b₁ φ θ (cos φ) (sin φ) π * rom_V2 φ θ (cos φ) (sin φ) (cos θ) = 0) :
    (rom_mk φ θ).x₅ (π / 2 - φ) = contactD (rom_mk φ θ).x₂ θ := by
  rw [contactD, (rom_hasDerivAt_x₂ _ _).deriv, rom_dot_rot_vvec]
  simp only [GerverParams.x₅, GerverParams.x₂, rom_mk, rot, uvec, cos_pi_div_two_sub,
    sin_pi_div_two_sub, Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, Prod.mk_sub_mk, Prod.mk.injEq]
  simp only [rom_U1, rom_U2, rom_V1, rom_V2, rom_κ₅₁, rom_κ₃₁, rom_κ₂₁, rom_κ₂₂, rom_Δ₁, rom_Δ₂,
    rom_b₂, rom_b₁, rom_β₀, rom_K] at h1 h2 ⊢
  exact ⟨by linear_combination h1, by linear_combination (-1 : ℝ) * h2⟩

/-- For a zero `(φ, θ)` of `H` in the box, `rom_mk φ θ` solves Romik's system. -/
theorem rom_mk_isSolution {z : ℝ × ℝ} (hz : z ∈ rom_box) (hH : rom_Hz z = 0) :
    (rom_mk z.1 z.2).IsSolution := by
  obtain ⟨φ, θ⟩ := z
  obtain ⟨hφ, hθ⟩ := hz
  dsimp only at hφ hθ ⊢
  have hD := rom_D_pos hφ hθ
  have hmul := rom_a₁_mul hD
  obtain ⟨hH1, hH2⟩ := rom_H_eq (θ := θ) hD
  simp only [rom_Hz, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at hH
  have hF1 := (mul_eq_zero.1 (hH1 ▸ hH.1)).resolve_left hD.ne'
  have hF2 := (mul_eq_zero.1 (hH2 ▸ hH.2)).resolve_left hD.ne'
  have hpi := pi_gt_d2
  refine ⟨?_, ?_, ?_, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (rom_mk_contact1_iff φ θ).2 ⟨hF1, hF2⟩, rom_mk_contact2 hF1 hF2⟩
  · show 0 < φ; linarith [hφ.1]
  · show φ < θ; linarith [hφ.2, hθ.1]
  · show θ < π / 4; linarith [hθ.2]
  · show (1 / 4 : ℝ) = -(-1 / 4); norm_num
  · -- cont12
    simp only [GerverParams.x₁, GerverParams.x₂, rom_mk, rot, Prod.mk_add_mk, Prod.mk.injEq]
    simp only [rom_κ₂₁, rom_κ₂₂, rom_Δ₁, rom_Δ₂]
    constructor <;> ring
  · -- diff12
    rw [(rom_hasDerivAt_x₁ _ _).deriv, (rom_hasDerivAt_x₂ _ _).deriv]
    simp only [rom_mk]
    congr 1
    simp only [rom_b₂, rom_b₁, rom_β₀, Prod.mk.injEq]
    simp only [rom_D, rom_N, rom_β₀] at hmul
    constructor
    · ring
    · linear_combination hmul
  · -- cont23
    simp only [GerverParams.x₂, GerverParams.x₃, rom_mk, rot, Prod.mk_add_mk, Prod.mk.injEq]
    simp only [rom_κ₃₁, rom_κ₃₂, rom_c₁, rom_b₂, rom_b₁, rom_β₀, rom_K]
    constructor <;> ring
  · -- diff23
    rw [(rom_hasDerivAt_x₂ _ _).deriv, (rom_hasDerivAt_x₃ _ _).deriv]
    simp only [rom_mk]
    congr 1
    simp only [rom_c₁, rom_b₂, rom_b₁, rom_β₀, rom_K, Prod.mk.injEq]
    constructor <;> ring
  · -- cont34
    simp only [GerverParams.x₃, GerverParams.x₄, rom_mk, rot, cos_pi_div_two_sub,
      sin_pi_div_two_sub, Prod.mk_add_mk, Prod.mk.injEq]
    simp only [rom_κ₄₁, rom_κ₃₁, rom_κ₃₂, rom_c₁, rom_b₂, rom_b₁, rom_β₀, rom_K]
    constructor <;> ring
  · -- diff34
    rw [(rom_hasDerivAt_x₃ _ _).deriv, (rom_hasDerivAt_x₄ _ _).deriv]
    simp only [rom_mk]
    congr 1
    simp only [rom_c₁, rom_b₂, rom_b₁, rom_β₀, rom_K, Prod.mk.injEq]
    constructor <;> ring
  · -- cont45
    simp only [GerverParams.x₄, GerverParams.x₅, rom_mk, rot, cos_pi_div_two_sub,
      sin_pi_div_two_sub, Prod.mk_add_mk, Prod.mk.injEq]
    simp only [rom_κ₅₁, rom_κ₄₁, rom_κ₃₁, rom_κ₂₁, rom_κ₂₂, rom_Δ₁, rom_Δ₂, rom_b₂, rom_b₁, rom_β₀,
      rom_K]
    constructor <;> ring
  · -- diff45
    rw [(rom_hasDerivAt_x₄ _ _).deriv, (rom_hasDerivAt_x₅ _ _).deriv]
    simp only [rom_mk, cos_pi_div_two_sub, sin_pi_div_two_sub]
    congr 1
    simp only [rom_b₂, rom_b₁, rom_β₀, Prod.mk.injEq]
    simp only [rom_D, rom_N, rom_β₀] at hmul
    constructor
    · linear_combination hmul
    · ring


/-! ### The angles of a solution and the main theorems -/

/-- A solution in the box gives a zero of the reduced system `H`. -/
theorem rom_Hz_of_solution {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) :
    rom_Hz (P.φ, P.θ) = 0 := by
  have hD := rom_D_pos hb.1 hb.2
  have hc : (rom_mk P.φ P.θ).x₁ P.φ = contactB (rom_mk P.φ P.θ).x₄ (π / 2 - P.θ) := by
    have e := rom_eq_mk hP hb
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hP
    rw [← e]
    exact h
  obtain ⟨hF1, hF2⟩ := (rom_mk_contact1_iff P.φ P.θ).1 hc
  obtain ⟨hH1, hH2⟩ := rom_H_eq (θ := P.θ) hD
  simp only [rom_Hz, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
  rw [hH1, hH2, hF1, hF2, mul_zero]
  exact ⟨rfl, rfl⟩

/-- Romik's system has a solution in the box. -/
theorem romik_exists : ∃ P : GerverParams, P.IsSolution ∧ P.InBox := by
  obtain ⟨z, hz, hH⟩ := rom_exists_zero
  have hzb := rom_tiny_subset hz
  exact ⟨rom_mk z.1 z.2, rom_mk_isSolution hzb hH, hzb.1, hzb.2⟩

/-- Romik's system has at most one solution in the box. -/
theorem romik_unique {P Q : GerverParams} (hP : P.IsSolution) (hPb : P.InBox) (hQ : Q.IsSolution)
    (hQb : Q.InBox) : P = Q := by
  have h := rom_zero_unique (z := (P.φ, P.θ)) (z' := (Q.φ, Q.θ)) ⟨hPb.1, hPb.2⟩ ⟨hQb.1, hQb.2⟩
    (rom_Hz_of_solution hP hPb) (rom_Hz_of_solution hQ hQb)
  simp only [Prod.mk.injEq] at h
  calc P = rom_mk P.φ P.θ := rom_eq_mk hP hPb
    _ = rom_mk Q.φ Q.θ := by rw [h.1, h.2]
    _ = Q := (rom_eq_mk hQ hQb).symm

/-! ### Enclosures of the parameters -/

/-- The angles of a solution in the box lie within `10⁻¹⁰` of `(0.0391773648, 0.6813015094)`. -/
theorem rom_angles_mem {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) :
    P.φ ∈ Icc (0.0391773647 : ℝ) 0.0391773649 ∧ P.θ ∈ Icc (0.6813015093 : ℝ) 0.6813015095 := by
  obtain ⟨z, hz, hH⟩ := rom_exists_zero
  have h := rom_zero_unique (z := (P.φ, P.θ)) ⟨hb.1, hb.2⟩ (rom_tiny_subset hz)
    (rom_Hz_of_solution hP hb) hH
  rw [← h] at hz
  exact hz

/-- Enclosure of `φ` for a solution in the box. -/
theorem rom_phi_mem {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) :
    P.φ ∈ Icc (0.0391773647 : ℝ) 0.0391773649 :=
  (rom_angles_mem hP hb).1

/-- Enclosure of `θ` for a solution in the box. -/
theorem rom_theta_mem {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) :
    P.θ ∈ Icc (0.6813015093 : ℝ) 0.6813015095 :=
  (rom_angles_mem hP hb).2

/-- Enclosure of `a₁` (and `e₁ = a₁`) for a solution in the box. -/
theorem rom_a1_mem {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) :
    P.a₁ ∈ Icc (1.2103224215 : ℝ) 1.2103224227 := by
  obtain ⟨h1, h2⟩ := rom_angles_mem hP hb
  have e : P.a₁ = rom_a₁ P.φ P.θ (cos P.φ) (sin P.φ) π :=
    congrArg GerverParams.a₁ (rom_eq_mk hP hb)
  rw [e]
  exact rom_iv_mono (rom_a₁_tiny h1 h2 (rom_cos_tiny h1) (rom_sin_tiny h1) rom_pi_mem20)
    (by norm_num)

/-- Enclosure of `b₁` for a solution in the box. -/
theorem rom_b1_mem {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) :
    P.b₁ ∈ Icc (-0.5276245983 : ℝ) (-0.5276245978) := by
  obtain ⟨h1, h2⟩ := rom_angles_mem hP hb
  have e : P.b₁ = rom_b₁ P.φ P.θ (cos P.φ) (sin P.φ) π :=
    congrArg GerverParams.b₁ (rom_eq_mk hP hb)
  rw [e]
  exact rom_iv_mono (rom_b₁_tiny h1 h2 (rom_cos_tiny h1) (rom_sin_tiny h1) rom_pi_mem20)
    (by norm_num)

/-- Enclosure of `b₂` for a solution in the box. -/
theorem rom_b2_mem {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) :
    P.b₂ ∈ Icc (0.9202583844 : ℝ) 0.920258386 := by
  obtain ⟨h1, h2⟩ := rom_angles_mem hP hb
  have e : P.b₂ = rom_b₂ P.φ P.θ (cos P.φ) (sin P.φ) π :=
    congrArg GerverParams.b₂ (rom_eq_mk hP hb)
  rw [e]
  exact rom_iv_mono (rom_b₂_tiny h1 h2 (rom_cos_tiny h1) (rom_sin_tiny h1) rom_pi_mem20)
    (by norm_num)

/-- Enclosure of `c₁` for a solution in the box. -/
theorem rom_c1_mem {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) :
    P.c₁ ∈ Icc (0.6260455224 : ℝ) 0.6260455233 := by
  obtain ⟨h1, h2⟩ := rom_angles_mem hP hb
  have e : P.c₁ = rom_c₁ P.φ P.θ (cos P.φ) (sin P.φ) π :=
    congrArg GerverParams.c₁ (rom_eq_mk hP hb)
  rw [e]
  exact rom_iv_mono (rom_c₁_tiny h1 h2 (rom_cos_tiny h1) (rom_sin_tiny h1) rom_pi_mem20)
    (by norm_num)

/-- Enclosure of `c₂ = c₁ - π/2` for a solution in the box. -/
theorem rom_c2_mem {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) :
    P.c₂ ∈ Icc (-0.9447508045 : ℝ) (-0.9447508034) := by
  have h := rom_c1_mem hP hb
  have e : P.c₂ = P.c₁ - π / 2 := hP.2.2.2.2.2.2.2.1
  have hp := rom_pi_mem20
  rw [e]
  exact ⟨by linarith [h.1, hp.2], by linarith [h.2, hp.1]⟩

/-- Enclosure of `d₁ = π/4 - b₁` for a solution in the box. -/
theorem rom_d1_mem {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) :
    P.d₁ ∈ Icc (1.3130227611 : ℝ) 1.3130227617 := by
  have h := rom_b1_mem hP hb
  have e : P.d₁ = π / 4 - P.b₁ := hP.2.2.2.2.2.1
  have hp := rom_pi_mem20
  rw [e]
  exact ⟨by linarith [h.2, hp.1], by linarith [h.1, hp.2]⟩

/-- Enclosure of `d₂ = b₂ + π/4 (2 b₁ - π/4)` for a solution in the box. -/
theorem rom_d2_mem {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) :
    P.d₂ ∈ Icc (-0.5253826717 : ℝ) (-0.5253826691) := by
  have h1 := rom_b1_mem hP hb
  have h2 := rom_b2_mem hP hb
  have e : P.d₂ = P.b₂ + π / 4 * (2 * P.b₁ - π / 4) := hP.2.2.2.2.2.2.1
  have k1 := rom_iv_div (L := 0.785398163397) (U := 0.785398163398) (k := 4) rom_pi_mem20
    (by norm_num)
  have k2 := rom_iv_mul (L := -1.0552491966) (U := -1.0552491956) (rom_iv_self 2) h1 (by norm_num)
  have k3 := rom_iv_sub (L := -1.84064736) (U := -1.8406473589) k2 k1 (by norm_num)
  have k4 := rom_iv_mul (L := -1.4456410561) (U := -1.4456410551) k1 k3 (by norm_num)
  have k5 := rom_iv_add (L := -0.5253826717) (U := -0.5253826691) h2 k4 (by norm_num)
  rw [e]
  exact k5

/-- Enclosure of `κ₂.1` for a solution in the box. -/
theorem rom_kappa21_mem {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) :
    P.κ₂.1 ∈ Icc (-0.919179295 : ℝ) (-0.9191792905) := by
  obtain ⟨h1, h2⟩ := rom_angles_mem hP hb
  have e : P.κ₂.1 = rom_κ₂₁ P.φ P.θ (cos P.φ) (sin P.φ) π :=
    congrArg (fun Q : GerverParams => Q.κ₂.1) (rom_eq_mk hP hb)
  rw [e]
  exact rom_iv_mono (rom_κ₂₁_tiny h1 h2 (rom_cos_tiny h1) (rom_sin_tiny h1) rom_pi_mem20)
    (by norm_num)

/-- Enclosure of `κ₂.2` for a solution in the box. -/
theorem rom_kappa22_mem {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) :
    P.κ₂.2 ∈ Icc (0.4724066191 : ℝ) 0.4724066204 := by
  obtain ⟨h1, h2⟩ := rom_angles_mem hP hb
  have e : P.κ₂.2 = rom_κ₂₂ P.φ P.θ (cos P.φ) (sin P.φ) π :=
    congrArg (fun Q : GerverParams => Q.κ₂.2) (rom_eq_mk hP hb)
  rw [e]
  exact rom_iv_mono (rom_κ₂₂_tiny h1 h2 (rom_cos_tiny h1) (rom_sin_tiny h1) rom_pi_mem20)
    (by norm_num)

/-- Enclosure of `κ₃.1` for a solution in the box. -/
theorem rom_kappa31_mem {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) :
    P.κ₃.1 ∈ Icc (-0.6137632319 : ℝ) (-0.613763227) := by
  obtain ⟨h1, h2⟩ := rom_angles_mem hP hb
  have e : P.κ₃.1 = rom_κ₃₁ P.φ P.θ (cos P.φ) (sin P.φ) (cos P.θ) (sin P.θ) π :=
    congrArg (fun Q : GerverParams => Q.κ₃.1) (rom_eq_mk hP hb)
  rw [e]
  exact rom_iv_mono (rom_κ₃₁_tiny h1 h2 (rom_cos_tiny h1) (rom_sin_tiny h1) (rom_cos_tiny' h2)
    (rom_sin_tiny' h2) rom_pi_mem20) (by norm_num)

/-- Enclosure of `κ₃.2` for a solution in the box. -/
theorem rom_kappa32_mem {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) :
    P.κ₃.2 ∈ Icc (0.8896264781 : ℝ) 0.8896264799 := by
  obtain ⟨h1, h2⟩ := rom_angles_mem hP hb
  have e : P.κ₃.2 = rom_κ₃₂ P.φ P.θ (cos P.φ) (sin P.φ) (cos P.θ) (sin P.θ) π :=
    congrArg (fun Q : GerverParams => Q.κ₃.2) (rom_eq_mk hP hb)
  rw [e]
  exact rom_iv_mono (rom_κ₃₂_tiny h1 h2 (rom_cos_tiny h1) (rom_sin_tiny h1) (rom_cos_tiny' h2)
    (rom_sin_tiny' h2) rom_pi_mem20) (by norm_num)

/-- Enclosure of `κ₄.1` for a solution in the box. -/
theorem rom_kappa41_mem {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) :
    P.κ₄.1 ∈ Icc (-0.3083471732 : ℝ) (-0.308347159) := by
  obtain ⟨h1, h2⟩ := rom_angles_mem hP hb
  have e : P.κ₄.1 = rom_κ₄₁ P.φ P.θ (cos P.φ) (sin P.φ) (cos P.θ) (sin P.θ) π :=
    congrArg (fun Q : GerverParams => Q.κ₄.1) (rom_eq_mk hP hb)
  rw [e]
  exact rom_iv_mono (rom_κ₄₁_tiny h1 h2 (rom_cos_tiny h1) (rom_sin_tiny h1) (rom_cos_tiny' h2)
    (rom_sin_tiny' h2) rom_pi_mem20) (by norm_num)

/-- `κ₄.2 = κ₂.2` (left-right symmetry). -/
theorem rom_kappa42_eq {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) :
    P.κ₄.2 = P.κ₂.2 := by
  have e := rom_eq_mk hP hb
  have e1 : P.κ₄.2 = (rom_mk P.φ P.θ).κ₄.2 := congrArg (fun Q : GerverParams => Q.κ₄.2) e
  have e2 : P.κ₂.2 = (rom_mk P.φ P.θ).κ₂.2 := congrArg (fun Q : GerverParams => Q.κ₂.2) e
  rw [e1, e2]
  rfl

/-- Enclosure of `κ₄.2` for a solution in the box. -/
theorem rom_kappa42_mem {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) :
    P.κ₄.2 ∈ Icc (0.4724066191 : ℝ) 0.4724066204 := by
  rw [rom_kappa42_eq hP hb]
  exact rom_kappa22_mem hP hb

/-- Enclosure of `κ₅.1` for a solution in the box. -/
theorem rom_kappa51_mem {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) :
    P.κ₅.1 ∈ Icc (-1.0172040423 : ℝ) (-1.0172040313) := by
  obtain ⟨h1, h2⟩ := rom_angles_mem hP hb
  have e : P.κ₅.1 = rom_κ₅₁ P.φ P.θ (cos P.φ) (sin P.φ) (cos P.θ) (sin P.θ) π :=
    congrArg (fun Q : GerverParams => Q.κ₅.1) (rom_eq_mk hP hb)
  rw [e]
  exact rom_iv_mono (rom_κ₅₁_tiny h1 h2 (rom_cos_tiny h1) (rom_sin_tiny h1) (rom_cos_tiny' h2)
    (rom_sin_tiny' h2) rom_pi_mem20) (by norm_num)

/-- `κ₅.2 = 1/4` (left-right symmetry). -/
theorem rom_kappa52_eq {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) :
    P.κ₅.2 = 1 / 4 :=
  congrArg (fun Q : GerverParams => Q.κ₅.2) (rom_eq_mk hP hb)

/-- Every solution in the box satisfies the enclosures `GerverParams.Bounds`. -/
theorem romik_bounds {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) : P.Bounds where
  φ_mem := rom_iv_mono (rom_phi_mem hP hb) (by norm_num)
  θ_mem := rom_iv_mono (rom_theta_mem hP hb) (by norm_num)
  a₁_mem := rom_iv_mono (rom_a1_mem hP hb) (by norm_num)
  b₁_mem := rom_iv_mono (rom_b1_mem hP hb) (by norm_num)
  b₂_mem := rom_iv_mono (rom_b2_mem hP hb) (by norm_num)
  c₁_mem := rom_iv_mono (rom_c1_mem hP hb) (by norm_num)
  κ₂₁_mem := rom_iv_mono (rom_kappa21_mem hP hb) (by norm_num)
  κ₂₂_mem := rom_iv_mono (rom_kappa22_mem hP hb) (by norm_num)
  κ₃₁_mem := rom_iv_mono (rom_kappa31_mem hP hb) (by norm_num)
  κ₃₂_mem := rom_iv_mono (rom_kappa32_mem hP hb) (by norm_num)
  κ₄₁_mem := rom_iv_mono (rom_kappa41_mem hP hb) (by norm_num)
  κ₄₂_mem := rom_iv_mono (rom_kappa42_mem hP hb) (by norm_num)
  κ₅₁_mem := rom_iv_mono (rom_kappa51_mem hP hb) (by norm_num)
  κ₅₂_mem := by rw [rom_kappa52_eq hP hb]; norm_num


end GerverParams

end MovingSofaOptimality
