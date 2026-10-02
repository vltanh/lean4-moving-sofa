module

public import MovingSofa.Gerver.Frame
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Order.Monotone.Union

/-!
# Numerical facts about Gerver's rotation path for the niche

Package GB. For a solution `hP : P.IsSolution` with the enclosures `hB : P.Bounds`, this file
proves the one-dimensional facts about Gerver's rotation path `𝐱 = P.path` that the abstract
envelope argument for the niche of Gerver's sofa uses (`notes/gerver_plan.md`, section "Niche
structure"), with the breakpoints `t₁ = φ`, `t₂ = θ`, `t₃ = π/2 - θ`, `t₄ = π/2 - φ` and the
auxiliary angles `s_A = 0.62`, `s_C = 0.95`:

* the functions `gb_rhoA P`, `gb_rhoC P` (glued along the phases like `P.path`), with
  `𝐁' = (ρ_A - 1) v_t` for `𝐁 = 𝐱 + α v_t` and `𝐃' = (1 - ρ_C) u_t` for `𝐃 = 𝐱 - β u_t` away from
  the breakpoints;
* `gb_order`, `gb_sA_mem`, `gb_sC_mem`: the order of the angles;
* `gb_x_cont`, `gb_x_deriv`, `gb_α_cont`, `gb_β_cont`, `gb_B_deriv`, `gb_D_deriv`: regularity;
* `gb_α_neg`, `gb_β_pos`, `gb_ratio_mono` (`|α|/β` is nondecreasing, as `α` and `β` are antitone,
  `gb_α_antitoneOn`, `gb_β_antitoneOn`);
* `gb_rhoA_le`, `gb_rhoA_lt`, `gb_rhoC_le`, `gb_rhoC_lt`: `ρ_A ≤ 1` on `[s_A, π/2]`, `ρ_C ≤ 1` on
  `[0, s_C]`;
* `gb_I_nonneg`, `gb_I'_nonneg`: `(𝐱(t₁) - 𝐱(s)) · u_s ≥ 0` on `[t₁, s_A]` and its mirror image;
* `gb_corner_B`, `gb_corner_D`: `(𝐱(t₁) - 𝐱(s)) · u_{t₃} ≥ 0` on `[0, t₁]` and its mirror image;
* `gb_x_pos`: `𝐱(t)_y > 0` on `[t₁, t₄]`;
* `gb_rhoA_measurable`, `gb_rhoA_bdd`, `gb_rhoC_measurable`, `gb_rhoC_bdd`;
* `gb_B_t₃`, `gb_D_t₂`, `gb_B_end`, `gb_D_end`: the identities `𝐁(t₃) = 𝐱(t₁)`, `𝐃(t₂) = 𝐱(t₄)`,
  `𝐁(π/2)_y = 0`, `𝐃(0)_y = 0`.

Method: interval arithmetic with the enclosures and `π ∈ (3.141592, 3.141593)`, the Taylor bounds
`gb_cos_le`, `gb_sin_le`, `gb_cos_ge` for `sin` and `cos`, and monotonicity from derivative signs.
The inequality `gb_I_nonneg` reduces, with `σ = s - φ`, to
`σ + σ²/4 - W₁ (1 - cos σ) + W₂ (σ + sin σ) ≥ 0` on `[0, 0.582]` (`gb_core`), where
`W₁ = -φ²/4 + b₁ φ + b₂ ≈ 0.8992` and `W₂ = φ/2 - b₁ - 1 ≈ -0.4528`; `gb_I'_nonneg` reduces to the
same inequality in the variable `π/2 - φ - s`.
-/

@[expose] public section

open Real Set

namespace MovingSofa

namespace GerverParams

/-- The function `ρ_A` of Gerver's rotation path (`𝐀' = ρ_A v_t`, `𝐁' = (ρ_A - 1) v_t`), glued
along the phases like `P.path`. -/
noncomputable def gb_rhoA (P : GerverParams) (t : ℝ) : ℝ :=
  if t < P.φ then (P.gs_phase 0).ρA t else if t < P.θ then (P.gs_phase 1).ρA t
  else if t ≤ π / 2 - P.θ then (P.gs_phase 2).ρA t else if t ≤ π / 2 - P.φ then (P.gs_phase 3).ρA t
  else (P.gs_phase 4).ρA t

/-- The function `ρ_C` of Gerver's rotation path (`𝐂' = -ρ_C u_t`, `𝐃' = (1 - ρ_C) u_t`), glued
along the phases like `P.path`. -/
noncomputable def gb_rhoC (P : GerverParams) (t : ℝ) : ℝ :=
  if t < P.φ then (P.gs_phase 0).ρC t else if t < P.θ then (P.gs_phase 1).ρC t
  else if t ≤ π / 2 - P.θ then (P.gs_phase 2).ρC t else if t ≤ π / 2 - P.φ then (P.gs_phase 3).ρC t
  else (P.gs_phase 4).ρC t

/-! ### Calculus helpers and Taylor bounds -/

private lemma gb_nonneg_of_deriv {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (h0 : f 0 = 0)
    (hf' : ∀ x, 0 < x → 0 ≤ f' x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hmono : MonotoneOn f (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun y _ => (hf y).continuousAt.continuousWithinAt)
      (fun y _ => (hf y).hasDerivWithinAt)
      (fun y hy => hf' y (by rwa [interior_Ici] at hy))
  have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hx) hx
  linarith

private lemma gb_monotoneOn_Icc {f f' : ℝ → ℝ} {a b : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ioo a b, 0 ≤ f' x) : MonotoneOn f (Icc a b) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (fun x _ => (hf x).continuousAt.continuousWithinAt)
    (fun x _ => (hf x).hasDerivWithinAt)
    (fun x hx => hf' x (by rwa [interior_Icc] at hx))

private lemma gb_antitoneOn_Icc {f f' : ℝ → ℝ} {a b : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ioo a b, f' x ≤ 0) : AntitoneOn f (Icc a b) :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    (fun x _ => (hf x).continuousAt.continuousWithinAt)
    (fun x _ => (hf x).hasDerivWithinAt)
    (fun x hx => hf' x (by rwa [interior_Icc] at hx))

private lemma gb_antitoneOn_union {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h₁ : AntitoneOn f (Icc a b)) (h₂ : AntitoneOn f (Icc b c)) : AntitoneOn f (Icc a c) := by
  rw [← Icc_union_Icc_eq_Icc hab hbc]
  exact AntitoneOn.union_right h₁ h₂ (isGreatest_Icc hab) (isLeast_Icc hbc)

private lemma gb_hasDerivAt_dot {f : ℝ → ℝ × ℝ} {f' : ℝ × ℝ} {s : ℝ} (hf : HasDerivAt f f' s)
    (w : ℝ × ℝ) : HasDerivAt (fun r => dot (f r) w) (dot f' w) s := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ :=
    w.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + w.2 • ContinuousLinearMap.snd ℝ ℝ ℝ
  have h := L.hasFDerivAt.comp_hasDerivAt s hf
  convert h using 1
  · funext r; simp [L, dot]; ring
  · simp [L, dot]; ring

private lemma gb_hasDerivAt_snd {f : ℝ → ℝ × ℝ} {f' : ℝ × ℝ} {s : ℝ} (hf : HasDerivAt f f' s) :
    HasDerivAt (fun r => (f r).2) f'.2 s := by
  have h := gb_hasDerivAt_dot hf (0, 1)
  simp only [dot, mul_zero, mul_one, zero_add] at h
  exact h

/-- `cos x ≤ 1 - x²/2 + x⁴/24` for `x ≥ 0`. -/
lemma gb_cos_le {x : ℝ} (hx : 0 ≤ x) : cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have := gb_nonneg_of_deriv (f := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - cos t)
    (f' := fun t => -t + t ^ 3 / 6 + sin t) (fun t => by
      have := ((((hasDerivAt_pow 2 t).div_const 2).const_sub 1).add
        ((hasDerivAt_pow 4 t).div_const 24)).sub (hasDerivAt_cos t)
      convert this using 1; push_cast; ring) (by simp)
    (fun t ht => by linarith [sin_ge_sub_cube ht.le]) hx
  linarith

/-- `sin x ≤ x - x³/6 + x⁵/120` for `x ≥ 0`. -/
lemma gb_sin_le {x : ℝ} (hx : 0 ≤ x) : sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have := gb_nonneg_of_deriv (f := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - sin t)
    (f' := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - cos t) (fun t => by
      have := (((hasDerivAt_id' t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
        ((hasDerivAt_pow 5 t).div_const 120)).sub (hasDerivAt_sin t)
      convert this using 1; push_cast; ring) (by simp)
    (fun t ht => by linarith [gb_cos_le ht.le]) hx
  linarith

/-- `1 - x²/2 + x⁴/24 - x⁶/720 ≤ cos x` for `x ≥ 0`. -/
lemma gb_cos_ge {x : ℝ} (hx : 0 ≤ x) : 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ cos x := by
  have := gb_nonneg_of_deriv (f := fun t => cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720))
    (f' := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - sin t) (fun t => by
      have := (hasDerivAt_cos t).sub (((((hasDerivAt_pow 2 t).div_const 2).const_sub 1).add
        ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720))
      convert this using 1; push_cast; ring) (by simp)
    (fun t ht => by linarith [gb_sin_le ht.le]) hx
  linarith

/-- The one-variable inequality behind `gb_I_nonneg` and `gb_I'_nonneg`: with
`W₁ ∈ [0, 0.8992039]`, `W₂ ∈ [-0.4527869, 0]`, the function
`σ + σ²/4 - W₁ (1 - cos σ) + W₂ (σ + sin σ)` is nonnegative on `[0, 0.582]` (numerically, its
quotient by `σ` stays above `0.0106`). Proof: `1 - cos σ ≤ σ²/2 - σ⁴/24 + σ⁶/720` and
`sin σ ≤ σ - σ³/6 + σ⁵/120` reduce it to a polynomial inequality. -/
lemma gb_core {W₁ W₂ σ : ℝ} (hW₁ : 0 ≤ W₁) (hW₁' : W₁ ≤ 0.8992039) (hW₂ : -0.4527869 ≤ W₂)
    (hW₂' : W₂ ≤ 0) (hσ : 0 ≤ σ) (hσ' : σ ≤ 0.582) :
    0 ≤ σ + σ ^ 2 / 4 - W₁ * (1 - cos σ) + W₂ * (σ + sin σ) := by
  have hc := gb_cos_ge hσ
  have hs := gb_sin_le hσ
  have hσ2 : σ ^ 2 ≤ 1 := by nlinarith
  have hb₁ : 0 ≤ σ ^ 2 / 2 - σ ^ 4 / 24 + σ ^ 6 / 720 := by
    nlinarith [mul_nonneg (sq_nonneg σ) (sub_nonneg.2 hσ2), pow_nonneg hσ 6]
  have hb₂ : 0 ≤ 2 * σ - σ ^ 3 / 6 + σ ^ 5 / 120 := by
    nlinarith [mul_nonneg hσ (sub_nonneg.2 hσ2), pow_nonneg hσ 5]
  have h1 : W₁ * (1 - cos σ) ≤ W₁ * (σ ^ 2 / 2 - σ ^ 4 / 24 + σ ^ 6 / 720) :=
    mul_le_mul_of_nonneg_left (by linarith) hW₁
  have h2 : W₂ * (2 * σ - σ ^ 3 / 6 + σ ^ 5 / 120) ≤ W₂ * (σ + sin σ) :=
    mul_le_mul_of_nonpos_left (by linarith) hW₂'
  have h3 : W₁ * (σ ^ 2 / 2 - σ ^ 4 / 24 + σ ^ 6 / 720) ≤
      0.8992039 * (σ ^ 2 / 2 - σ ^ 4 / 24 + σ ^ 6 / 720) := mul_le_mul_of_nonneg_right hW₁' hb₁
  have h4 : -0.4527869 * (2 * σ - σ ^ 3 / 6 + σ ^ 5 / 120) ≤
      W₂ * (2 * σ - σ ^ 3 / 6 + σ ^ 5 / 120) := mul_le_mul_of_nonneg_right hW₂ hb₂
  have hQ : 0 ≤ 1 + σ / 4 - 0.8992039 * (σ / 2 - σ ^ 3 / 24 + σ ^ 5 / 720) +
      -0.4527869 * (2 - σ ^ 2 / 6 + σ ^ 4 / 120) := by
    nlinarith [mul_nonneg hσ (sub_nonneg.2 hσ'), pow_nonneg hσ 3, pow_nonneg hσ 4, pow_nonneg hσ 5,
      mul_nonneg (pow_nonneg hσ 2) (sub_nonneg.2 hσ')]
  have hP : 0 ≤ σ * (1 + σ / 4 - 0.8992039 * (σ / 2 - σ ^ 3 / 24 + σ ^ 5 / 720) +
      -0.4527869 * (2 - σ ^ 2 / 6 + σ ^ 4 / 120)) := mul_nonneg hσ hQ
  linarith

variable {P : GerverParams}

/-! ### Order of the angles -/

/-- The breakpoints `0 < t₁ < t₂ < t₃ < t₄ < π/2`. -/
lemma gb_order (hP : P.IsSolution) :
    0 < P.φ ∧ P.φ < P.θ ∧ P.θ < π / 2 - P.θ ∧ π / 2 - P.θ < π / 2 - P.φ ∧ π / 2 - P.φ < π / 2 := by
  obtain ⟨h1, h2, h3⟩ := gs_ord hP
  exact ⟨h1, h2, by linarith, by linarith, by linarith⟩

/-- `t₁ ≤ s_A ≤ t₃` for `s_A = 0.62`. -/
lemma gb_sA_mem (hB : P.Bounds) : P.φ ≤ 0.62 ∧ 0.62 ≤ π / 2 - P.θ := by
  have := gs_φ_hi hB
  have := gs_θ_hi hB
  have := pi_gt_d6
  constructor <;> linarith

/-- `t₂ ≤ s_C ≤ t₄` for `s_C = 0.95`. -/
lemma gb_sC_mem (hB : P.Bounds) : P.θ ≤ 0.95 ∧ 0.95 ≤ π / 2 - P.φ := by
  have := gs_φ_hi hB
  have := gs_θ_hi hB
  have := pi_gt_d6
  constructor <;> linarith

/-! ### Regularity -/

lemma gb_x_cont (hP : P.IsSolution) : ContinuousOn P.path (Icc 0 (π / 2)) :=
  (gs_continuous_path hP).continuousOn

private lemma gb_pathD_eq (hP : P.IsSolution) (t : ℝ) :
    P.gs_pathD t = P.gs_α t • uvec t + P.gs_β t • vvec t := by
  rw [gs_α, gs_β, ← gs_deriv_path hP]
  exact eq_dot_uvec_smul_add _ t

/-- `𝐱' = α u_t + β v_t`. -/
lemma gb_x_deriv (hP : P.IsSolution) :
    ∀ t ∈ Ioo 0 (π / 2), HasDerivAt P.path (P.gs_α t • uvec t + P.gs_β t • vvec t) t := by
  intro t _
  rw [← gb_pathD_eq hP]
  exact gs_hasDerivAt_path hP t

lemma gb_α_cont (hP : P.IsSolution) : ContinuousOn P.gs_α (Icc 0 (π / 2)) :=
  (gs_continuous_α hP).continuousOn

lemma gb_β_cont (hP : P.IsSolution) : ContinuousOn P.gs_β (Icc 0 (π / 2)) :=
  (gs_continuous_β hP).continuousOn

/-- Away from the breakpoints, `t` lies in an open phase interval on which `gb_rhoA`, `gb_rhoC` are
the phase formulas. -/
private lemma gb_opiece_of_ne {t : ℝ}
    (ht : t ∉ ({P.φ, P.θ, π / 2 - P.θ, π / 2 - P.φ} : Set ℝ)) :
    ∃ i, gs_opiece P i t ∧ gb_rhoA P t = (P.gs_phase i).ρA t ∧
      gb_rhoC P t = (P.gs_phase i).ρC t := by
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at ht
  obtain ⟨h1, h2, h3, h4⟩ := ht
  unfold gb_rhoA gb_rhoC
  by_cases c1 : t < P.φ
  · simp only [c1, ↓reduceIte]
    exact ⟨0, (show t < P.φ from c1), rfl, rfl⟩
  by_cases c2 : t < P.θ
  · simp only [c1, c2, ↓reduceIte]
    exact ⟨1, (show P.φ < t ∧ t < P.θ from ⟨lt_of_le_of_ne (not_lt.1 c1) (Ne.symm h1), c2⟩),
      rfl, rfl⟩
  by_cases c3 : t ≤ π / 2 - P.θ
  · simp only [c1, c2, c3, ↓reduceIte]
    exact ⟨2, (show P.θ < t ∧ t < π / 2 - P.θ from
      ⟨lt_of_le_of_ne (not_lt.1 c2) (Ne.symm h2), lt_of_le_of_ne c3 h3⟩), rfl, rfl⟩
  by_cases c4 : t ≤ π / 2 - P.φ
  · simp only [c1, c2, c3, c4, ↓reduceIte]
    exact ⟨3, (show π / 2 - P.θ < t ∧ t < π / 2 - P.φ from ⟨not_le.1 c3, lt_of_le_of_ne c4 h4⟩),
      rfl, rfl⟩
  · simp only [c1, c2, c3, c4, ↓reduceIte]
    exact ⟨4, (show π / 2 - P.φ < t from not_le.1 c4), rfl, rfl⟩

/-- `𝐁' = (ρ_A - 1) v_t` off the breakpoints, for `𝐁 = 𝐱 + α v_t`. -/
lemma gb_B_deriv (hP : P.IsSolution) :
    ∀ t ∈ Ioo 0 (π / 2), t ∉ ({P.φ, P.θ, π / 2 - P.θ, π / 2 - P.φ} : Set ℝ) →
      HasDerivAt (fun r => P.path r + P.gs_α r • vvec r) ((gb_rhoA P t - 1) • vvec t) t := by
  intro t _ ht
  obtain ⟨i, hi, hA, -⟩ := gb_opiece_of_ne ht
  rw [hA]
  exact gs_hasDerivAt_contactB hP hi

/-- `𝐃' = (1 - ρ_C) u_t` off the breakpoints, for `𝐃 = 𝐱 - β u_t`. -/
lemma gb_D_deriv (hP : P.IsSolution) :
    ∀ t ∈ Ioo 0 (π / 2), t ∉ ({P.φ, P.θ, π / 2 - P.θ, π / 2 - P.φ} : Set ℝ) →
      HasDerivAt (fun r => P.path r - P.gs_β r • uvec r) ((1 - gb_rhoC P t) • uvec t) t := by
  intro t _ ht
  obtain ⟨i, hi, -, hC⟩ := gb_opiece_of_ne ht
  rw [hC]
  exact gs_hasDerivAt_contactD hP hi

/-! ### Signs and monotonicity of `α` and `β` -/

lemma gb_α_neg (hP : P.IsSolution) (hB : P.Bounds) : ∀ t ∈ Ioo 0 (π / 2), P.gs_α t < 0 :=
  fun _ ht => gs_α_neg hP hB ht.1 ht.2.le

lemma gb_β_pos (hP : P.IsSolution) (hB : P.Bounds) : ∀ t ∈ Ioo 0 (π / 2), 0 < P.gs_β t :=
  fun _ ht => gs_β_pos hP hB ht.1.le ht.2

/-! Phase formulas in the variable `t` (Frame states phases 4–5 in the variable `π/2 - t`). -/

private lemma gb_α₄ (hP : P.IsSolution) (t : ℝ) :
    (P.gs_phase 3).α t = -(1 / 2 - (π / 2 - t) ^ 2 / 4 + P.b₁ * (π / 2 - t) + P.b₂) := by
  have := gs_α₄_eq hP (π / 2 - t); rwa [sub_sub_cancel] at this

private lemma gb_β₄ (hP : P.IsSolution) (t : ℝ) :
    (P.gs_phase 3).β t = -(2 * P.b₁ + 1 - (π / 2 - t)) := by
  have := gs_β₄_eq hP (π / 2 - t); rwa [sub_sub_cancel] at this

private lemma gb_α₅ (hP : P.IsSolution) (t : ℝ) :
    (P.gs_phase 4).α t = -(2 * P.a₁ * cos (π / 2 - t) - sin (π / 2 - t) / 2 - 1) := by
  have := gs_α₅_eq hP (π / 2 - t); rwa [sub_sub_cancel] at this

private lemma gb_β₅ (hP : P.IsSolution) (t : ℝ) :
    (P.gs_phase 4).β t = -((1 - cos (π / 2 - t)) / 2 - 2 * P.a₁ * sin (π / 2 - t)) := by
  have := gs_β₅_eq hP (π / 2 - t); rwa [sub_sub_cancel] at this

private lemma gb_ρA₄ (hP : P.IsSolution) (t : ℝ) :
    (P.gs_phase 3).ρA t = (π / 2 - t) / 2 - P.b₁ := by
  have := gs_ρA₄_eq hP (π / 2 - t); rwa [sub_sub_cancel] at this

private lemma gb_ρC₄ (hP : P.IsSolution) (t : ℝ) :
    (P.gs_phase 3).ρC t = 1 / 2 - (π / 2 - t) ^ 2 / 4 + P.b₁ * (π / 2 - t) + P.b₂ := by
  have := gs_ρC₄_eq hP (π / 2 - t); rwa [sub_sub_cancel] at this

/-- `α₁` is antitone on `[0, φ]`. -/
private lemma gb_α₁_anti (hB : P.Bounds) :
    AntitoneOn (fun t => (1 - cos t) / 2 - 2 * P.a₁ * sin t) (Icc 0 P.φ) := by
  refine gb_antitoneOn_Icc (f' := fun t => sin t / 2 - 2 * P.a₁ * cos t) (fun t => ?_)
    (fun t ht => ?_)
  · have := (((hasDerivAt_cos t).const_sub 1).div_const 2).sub
      ((hasDerivAt_sin t).const_mul (2 * P.a₁))
    convert this using 1; ring
  · have := gs_φ_hi hB
    have ha := gs_a₁_lo hB
    have h1 := sin_le ht.1.le
    have h2 := one_sub_sq_div_two_le_cos (x := t)
    have h3 : 0.99 ≤ cos t := by
      nlinarith [mul_nonneg ht.1.le (show 0 ≤ 0.04 - t by linarith [ht.2])]
    have h4 : 1.21 * 0.99 ≤ P.a₁ * cos t := mul_le_mul (by linarith) h3 (by norm_num) (by linarith)
    show sin t / 2 - 2 * P.a₁ * cos t ≤ 0
    linarith [ht.2]

/-- `β₁` is antitone on `[0, φ]`. -/
private lemma gb_β₁_anti (hB : P.Bounds) :
    AntitoneOn (fun t => 2 * P.a₁ * cos t - sin t / 2 - 1) (Icc 0 P.φ) := by
  refine gb_antitoneOn_Icc (f' := fun t => -(2 * P.a₁ * sin t) - cos t / 2) (fun t => ?_)
    (fun t ht => ?_)
  · have := (((hasDerivAt_cos t).const_mul (2 * P.a₁)).sub
      ((hasDerivAt_sin t).div_const 2)).sub_const 1
    convert this using 1; ring
  · have := gs_φ_hi hB
    have ha := gs_a₁_lo hB
    have h1 : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith [pi_gt_three, ht.2])
    have h2 : 0 ≤ cos t :=
      cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos, ht.1], by linarith [pi_gt_three, ht.2]⟩
    have h3 : 0 ≤ P.a₁ * sin t := mul_nonneg (by linarith) h1
    show -(2 * P.a₁ * sin t) - cos t / 2 ≤ 0
    linarith

/-- `β₂` is antitone on `[0, ∞)`. -/
private lemma gb_β₂_anti (hB : P.Bounds) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    1 / 2 - y ^ 2 / 4 + P.b₁ * y + P.b₂ ≤ 1 / 2 - x ^ 2 / 4 + P.b₁ * x + P.b₂ := by
  have := gs_b₁_hi hB
  nlinarith [mul_nonneg (sub_nonneg.2 hxy) (add_nonneg hx (hx.trans hxy)),
    mul_nonneg (sub_nonneg.2 hxy) (show 0 ≤ -P.b₁ by linarith)]

/-- `α` is antitone on `[0, π/2]` (phase by phase, glued at the breakpoints). -/
lemma gb_α_antitoneOn (hP : P.IsSolution) (hB : P.Bounds) : AntitoneOn P.gs_α (Icc 0 (π / 2)) := by
  obtain ⟨o1, o2, o3, o4, o5⟩ := gb_order hP
  have h1 : AntitoneOn P.gs_α (Icc 0 P.φ) := by
    intro x hx y hy hxy
    rw [gs_α_eq hP (gs_piece₀ hx.2), gs_α_eq hP (gs_piece₀ hy.2), gs_α₁_eq hP, gs_α₁_eq hP]
    exact gb_α₁_anti hB hx hy hxy
  have h2 : AntitoneOn P.gs_α (Icc P.φ P.θ) := by
    intro x hx y hy hxy
    rw [gs_α_eq hP (gs_piece₁ hx.1 hx.2), gs_α_eq hP (gs_piece₁ hy.1 hy.2), gs_α₂_eq, gs_α₂_eq]
    linarith
  have h3 : AntitoneOn P.gs_α (Icc P.θ (π / 2 - P.θ)) := by
    intro x hx y hy hxy
    rw [gs_α_eq hP (gs_piece₂ hx.1 hx.2), gs_α_eq hP (gs_piece₂ hy.1 hy.2), gs_α₃_eq hP,
      gs_α₃_eq hP]
    linarith
  have h4 : AntitoneOn P.gs_α (Icc (π / 2 - P.θ) (π / 2 - P.φ)) := by
    intro x hx y hy hxy
    rw [gs_α_eq hP (gs_piece₃ hx.1 hx.2), gs_α_eq hP (gs_piece₃ hy.1 hy.2), gb_α₄ hP, gb_α₄ hP]
    have := gb_β₂_anti hB (x := π / 2 - y) (y := π / 2 - x) (by linarith [hy.2]) (by linarith)
    linarith
  have h5 : AntitoneOn P.gs_α (Icc (π / 2 - P.φ) (π / 2)) := by
    intro x hx y hy hxy
    rw [gs_α_eq hP (gs_piece₄ hx.1), gs_α_eq hP (gs_piece₄ hy.1), gb_α₅ hP, gb_α₅ hP]
    have h : 2 * P.a₁ * cos (π / 2 - x) - sin (π / 2 - x) / 2 - 1 ≤
        2 * P.a₁ * cos (π / 2 - y) - sin (π / 2 - y) / 2 - 1 :=
      gb_β₁_anti hB (a := π / 2 - y) (b := π / 2 - x)
        ⟨by linarith [hy.2], by linarith [hy.1]⟩ ⟨by linarith [hx.2], by linarith [hx.1]⟩
        (by linarith)
    linarith
  exact gb_antitoneOn_union (by linarith) o5.le (gb_antitoneOn_union (by linarith) o4.le
    (gb_antitoneOn_union (by linarith) o3.le (gb_antitoneOn_union o1.le o2.le h1 h2) h3) h4) h5

/-- `β` is antitone on `[0, π/2]` (phase by phase, glued at the breakpoints). -/
lemma gb_β_antitoneOn (hP : P.IsSolution) (hB : P.Bounds) : AntitoneOn P.gs_β (Icc 0 (π / 2)) := by
  obtain ⟨o1, o2, o3, o4, o5⟩ := gb_order hP
  have h1 : AntitoneOn P.gs_β (Icc 0 P.φ) := by
    intro x hx y hy hxy
    rw [gs_β_eq hP (gs_piece₀ hx.2), gs_β_eq hP (gs_piece₀ hy.2), gs_β₁_eq hP, gs_β₁_eq hP]
    exact gb_β₁_anti hB hx hy hxy
  have h2 : AntitoneOn P.gs_β (Icc P.φ P.θ) := by
    intro x hx y hy hxy
    rw [gs_β_eq hP (gs_piece₁ hx.1 hx.2), gs_β_eq hP (gs_piece₁ hy.1 hy.2), gs_β₂_eq, gs_β₂_eq]
    exact gb_β₂_anti hB (by linarith [hx.1]) hxy
  have h3 : AntitoneOn P.gs_β (Icc P.θ (π / 2 - P.θ)) := by
    intro x hx y hy hxy
    rw [gs_β_eq hP (gs_piece₂ hx.1 hx.2), gs_β_eq hP (gs_piece₂ hy.1 hy.2), gs_β₃_eq, gs_β₃_eq]
    linarith
  have h4 : AntitoneOn P.gs_β (Icc (π / 2 - P.θ) (π / 2 - P.φ)) := by
    intro x hx y hy hxy
    rw [gs_β_eq hP (gs_piece₃ hx.1 hx.2), gs_β_eq hP (gs_piece₃ hy.1 hy.2), gb_β₄ hP, gb_β₄ hP]
    linarith
  have h5 : AntitoneOn P.gs_β (Icc (π / 2 - P.φ) (π / 2)) := by
    intro x hx y hy hxy
    rw [gs_β_eq hP (gs_piece₄ hx.1), gs_β_eq hP (gs_piece₄ hy.1), gb_β₅ hP, gb_β₅ hP]
    have h : (1 - cos (π / 2 - x)) / 2 - 2 * P.a₁ * sin (π / 2 - x) ≤
        (1 - cos (π / 2 - y)) / 2 - 2 * P.a₁ * sin (π / 2 - y) :=
      gb_α₁_anti hB (a := π / 2 - y) (b := π / 2 - x)
        ⟨by linarith [hy.2], by linarith [hy.1]⟩ ⟨by linarith [hx.2], by linarith [hx.1]⟩
        (by linarith)
    linarith
  exact gb_antitoneOn_union (by linarith) o5.le (gb_antitoneOn_union (by linarith) o4.le
    (gb_antitoneOn_union (by linarith) o3.le (gb_antitoneOn_union o1.le o2.le h1 h2) h3) h4) h5

/-- `|α|/β` is nondecreasing on `(0, π/2)`, in cross-multiplied form. -/
lemma gb_ratio_mono (hP : P.IsSolution) (hB : P.Bounds) :
    ∀ r ∈ Ioo 0 (π / 2), ∀ r' ∈ Ioo 0 (π / 2), r ≤ r' →
      -P.gs_α r * P.gs_β r' ≤ -P.gs_α r' * P.gs_β r := by
  intro r hr r' hr' hrr'
  have hα := gb_α_antitoneOn hP hB (Ioo_subset_Icc_self hr) (Ioo_subset_Icc_self hr') hrr'
  have hβ := gb_β_antitoneOn hP hB (Ioo_subset_Icc_self hr) (Ioo_subset_Icc_self hr') hrr'
  have ha' := gs_α_neg hP hB hr'.1 hr'.2.le
  have hb' := gs_β_pos hP hB hr'.1.le hr'.2
  have h1 : -P.gs_α r * P.gs_β r' ≤ -P.gs_α r' * P.gs_β r' :=
    mul_le_mul_of_nonneg_right (by linarith) hb'.le
  have h2 : -P.gs_α r' * P.gs_β r' ≤ -P.gs_α r' * P.gs_β r :=
    mul_le_mul_of_nonneg_left hβ (by linarith)
  linarith

/-! ### Bounds on the curvature radii -/

/-- `ρ_A ≤ 1` on `[s_A, π/2]` (`ρ_A(0.62) ≈ 0.99703`). -/
lemma gb_rhoA_le (hP : P.IsSolution) (hB : P.Bounds) :
    ∀ t ∈ Icc (0.62 : ℝ) (π / 2), gb_rhoA P t ≤ 1 := by
  intro t ht
  obtain ⟨o1, o2, o3, o4, o5⟩ := gb_order hP
  have := gs_φ_hi hB
  have := gs_θ_lo hB
  have := gs_θ_hi hB
  have := gs_b₁_lo hB
  have := gs_b₁_hi hB
  have := gs_b₂_hi hB
  have := gs_c₁_hi hB
  unfold gb_rhoA
  split_ifs with c1 c2 c3 c4
  · linarith [ht.1]
  · rw [gs_ρA₂_eq]
    nlinarith [ht.1, mul_nonneg (show 0 ≤ t - 0.62 by linarith [ht.1]) (show 0 ≤ -P.b₁ by linarith),
      mul_nonneg (show 0 ≤ t - 0.62 by linarith [ht.1]) (show 0 ≤ t + 0.62 by linarith [ht.1])]
  · rw [gs_ρA₃_eq]; linarith
  · rw [gb_ρA₄ hP]; linarith
  · rw [gs_ρA₅_eq]; norm_num

/-- `ρ_A < 1` on `[t₃, π/2]`. -/
lemma gb_rhoA_lt (hP : P.IsSolution) (hB : P.Bounds) :
    ∀ t ∈ Icc (π / 2 - P.θ) (π / 2), gb_rhoA P t < 1 := by
  intro t ht
  obtain ⟨o1, o2, o3, o4, o5⟩ := gb_order hP
  have := gs_θ_lo hB
  have := gs_θ_hi hB
  have := gs_b₁_lo hB
  have := gs_c₁_hi hB
  have := pi_gt_d6
  unfold gb_rhoA
  split_ifs with c1 c2 c3 c4
  · linarith [ht.1]
  · linarith [ht.1]
  · rw [gs_ρA₃_eq]; linarith [ht.1]
  · rw [gb_ρA₄ hP]; linarith [ht.1]
  · rw [gs_ρA₅_eq]; norm_num

/-- `ρ_C ≤ 1` on `[0, s_C]` (`ρ_C(0.95) ≈ 0.9964`). -/
lemma gb_rhoC_le (hP : P.IsSolution) (hB : P.Bounds) :
    ∀ t ∈ Icc 0 (0.95 : ℝ), gb_rhoC P t ≤ 1 := by
  intro t ht
  obtain ⟨o1, o2, o3, o4, o5⟩ := gb_order hP
  have := gs_θ_lo hB
  have := gs_θ_hi hB
  have := gs_b₁_lo hB
  have := gs_b₁_hi hB
  have := gs_b₂_hi hB
  have := gs_c₁_hi hB
  have := pi_gt_d6
  have := pi_lt_d6
  unfold gb_rhoC
  split_ifs with c1 c2 c3 c4
  · rw [gs_ρC₁_eq]; norm_num
  · rw [gs_ρC₂_eq]; linarith
  · rw [gs_ρC₃_eq hP]; linarith
  · rw [gb_ρC₄ hP]
    have h1 : 0.6207 ≤ π / 2 - t := by linarith [ht.2]
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (show 0 ≤ -P.b₁ by linarith),
      mul_nonneg (sub_nonneg.2 h1) (show 0 ≤ π / 2 - t + 0.6207 by linarith)]
  · rw [gs_ρC₅_eq]; norm_num

/-- `ρ_C < 1` on `[0, t₂]`. -/
lemma gb_rhoC_lt (hP : P.IsSolution) (hB : P.Bounds) : ∀ t ∈ Icc 0 P.θ, gb_rhoC P t < 1 := by
  intro t ht
  obtain ⟨o1, o2, o3, o4, o5⟩ := gb_order hP
  have := gs_θ_hi hB
  have := gs_b₁_lo hB
  have := gs_c₁_hi hB
  have := pi_gt_d6
  unfold gb_rhoC
  split_ifs with c1 c2 c3 c4
  · rw [gs_ρC₁_eq]; norm_num
  · rw [gs_ρC₂_eq]; linarith [ht.2]
  · rw [gs_ρC₃_eq hP]; linarith [ht.2]
  · linarith [ht.2]
  · linarith [ht.2]

/-! ### The niche inequalities -/

/-- `(X(a) - X(s)) · u_s` for a phase `X = R_t (w₁, w₂) + κ`. -/
private lemma gb_dot_X_sub_uvec (Φ : gs_Phase) (a s : ℝ) :
    dot (Φ.X a - Φ.X s) (uvec s) = Φ.w₁ a * cos (s - a) + Φ.w₂ a * sin (s - a) - Φ.w₁ s := by
  simp only [gs_Phase.X, rot, dot, uvec, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    cos_sub, sin_sub]
  linear_combination (-Φ.w₁ s) * sin_sq_add_cos_sq s

/-- `(X(a) - X(s)) · v_s` for a phase `X = R_t (w₁, w₂) + κ`. -/
private lemma gb_dot_X_sub_vvec (Φ : gs_Phase) (a s : ℝ) :
    dot (Φ.X a - Φ.X s) (vvec s) = Φ.w₂ a * cos (a - s) + Φ.w₁ a * sin (a - s) - Φ.w₂ s := by
  simp only [gs_Phase.X, rot, dot, vvec, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    cos_sub, sin_sub]
  linear_combination (-Φ.w₂ s) * sin_sq_add_cos_sq s

/-- The enclosures of `W₁ = -φ²/4 + b₁ φ + b₂` and `W₂ = φ/2 - b₁ - 1`. -/
private lemma gb_W_bounds (hB : P.Bounds) :
    0 ≤ -P.φ ^ 2 / 4 + P.b₁ * P.φ + P.b₂ ∧ -P.φ ^ 2 / 4 + P.b₁ * P.φ + P.b₂ ≤ 0.8992039 ∧
      0.8992 ≤ -P.φ ^ 2 / 4 + P.b₁ * P.φ + P.b₂ ∧
      -0.4527869 ≤ P.φ / 2 - P.b₁ - 1 ∧ P.φ / 2 - P.b₁ - 1 ≤ 0 := by
  have := gs_φ_lo hB
  have := gs_φ_hi hB
  have := gs_b₁_lo hB
  have := gs_b₁_hi hB
  have := gs_b₂_lo hB
  have := gs_b₂_hi hB
  have h1 : 0 ≤ P.φ - 0.039177264 := by linarith
  have h2 : 0 ≤ 0.039177465 - P.φ := by linarith
  have h3 : 0 ≤ -P.b₁ := by linarith
  refine ⟨by nlinarith, ?_, ?_, by linarith, by linarith⟩
  · nlinarith [mul_nonneg h1 (show 0 ≤ P.φ + 0.039177264 by linarith), mul_nonneg h3 h1]
  · nlinarith [mul_nonneg h2 (show 0 ≤ P.φ + 0.039177465 by linarith), mul_nonneg h3 h2]

/-- `(𝐱(t₁) - 𝐱(s)) · u_s ≥ 0` on `[t₁, s_A]`: on phase 2, with `σ = s - φ`, this is `gb_core`. -/
lemma gb_I_nonneg (hP : P.IsSolution) (hB : P.Bounds) :
    ∀ s ∈ Icc P.φ (0.62 : ℝ), 0 ≤ dot (P.path P.φ - P.path s) (uvec s) := by
  intro s hs
  obtain ⟨o1, o2, o3, o4, o5⟩ := gb_order hP
  have := gs_θ_lo hB
  have := gs_φ_lo hB
  have hsθ : s ≤ P.θ := by linarith [hs.2]
  rw [gs_path_eq_phase hP (gs_piece₁ le_rfl o2.le), gs_path_eq_phase hP (gs_piece₁ hs.1 hsθ),
    gb_dot_X_sub_uvec]
  have key : (P.gs_phase 1).w₁ P.φ * cos (s - P.φ) + (P.gs_phase 1).w₂ P.φ * sin (s - P.φ) -
      (P.gs_phase 1).w₁ s = (s - P.φ) + (s - P.φ) ^ 2 / 4 -
        (-P.φ ^ 2 / 4 + P.b₁ * P.φ + P.b₂) * (1 - cos (s - P.φ)) +
        (P.φ / 2 - P.b₁ - 1) * ((s - P.φ) + sin (s - P.φ)) := by
    simp only [gs_phase, gs_ph2]; ring
  rw [key]
  obtain ⟨hW1, hW2, -, hW3, hW4⟩ := gb_W_bounds hB
  exact gb_core hW1 hW2 hW3 hW4 (by linarith [hs.1]) (by linarith [hs.2])

/-- `(𝐱(t₄) - 𝐱(s)) · v_s ≥ 0` on `[s_C, t₄]`: on phase 4, with `τ = π/2 - φ - s`, this is
`gb_core`. -/
lemma gb_I'_nonneg (hP : P.IsSolution) (hB : P.Bounds) :
    ∀ s ∈ Icc (0.95 : ℝ) (π / 2 - P.φ), 0 ≤ dot (P.path (π / 2 - P.φ) - P.path s) (vvec s) := by
  intro s hs
  obtain ⟨o1, o2, o3, o4, o5⟩ := gb_order hP
  have := gs_θ_lo hB
  have := gs_φ_lo hB
  have := pi_lt_d6
  have hs3 : π / 2 - P.θ ≤ s := by linarith [hs.1]
  rw [gs_path_eq_phase hP (gs_piece₃ o4.le le_rfl), gs_path_eq_phase hP (gs_piece₃ hs3 hs.2),
    gb_dot_X_sub_vvec]
  have key : (P.gs_phase 3).w₂ (π / 2 - P.φ) * cos (π / 2 - P.φ - s) +
      (P.gs_phase 3).w₁ (π / 2 - P.φ) * sin (π / 2 - P.φ - s) - (P.gs_phase 3).w₂ s =
      (π / 2 - P.φ - s) + (π / 2 - P.φ - s) ^ 2 / 4 -
        (-P.φ ^ 2 / 4 + P.b₁ * P.φ + P.b₂) * (1 - cos (π / 2 - P.φ - s)) +
        (P.φ / 2 - P.b₁ - 1) * ((π / 2 - P.φ - s) + sin (π / 2 - P.φ - s)) := by
    simp only [gs_phase, gs_ph4, gs_d₁ hP, gs_d₂ hP]; ring
  rw [key]
  obtain ⟨hW1, hW2, -, hW3, hW4⟩ := gb_W_bounds hB
  exact gb_core hW1 hW2 hW3 hW4 (by linarith [hs.2]) (by linarith [hs.1])

/-- The derivative of `r ↦ 𝐱(r) · w`. -/
private lemma gb_hasDerivAt_dot_path (hP : P.IsSolution) (w : ℝ × ℝ) (r : ℝ) :
    HasDerivAt (fun r => dot (P.path r) w) (dot (P.gs_pathD r) w) r :=
  gb_hasDerivAt_dot (gs_hasDerivAt_path hP r) w

private lemma gb_pathD_phase (hP : P.IsSolution) {i : ℕ} {t : ℝ} (h : gs_piece P i t) :
    P.gs_pathD t = (P.gs_phase i).α t • uvec t + (P.gs_phase i).β t • vvec t := by
  rw [gs_pathD_eq_phase hP h]; rfl

/-- The base inequality for `gb_corner_B` and `gb_corner_D`: on `[0, φ]`,
`α₁(r) sin(θ + r) + β₁(r) cos(θ + r) ≥ 0`. -/
private lemma gb_corner_ineq (hB : P.Bounds) {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ P.φ) :
    0 ≤ ((1 - cos r) / 2 - 2 * P.a₁ * sin r) * sin (P.θ + r) +
      (2 * P.a₁ * cos r - sin r / 2 - 1) * cos (P.θ + r) := by
  have := gs_φ_hi hB
  have := gs_θ_lo hB
  have := gs_θ_hi hB
  have ha := gs_a₁_lo hB
  have ha' := gs_a₁_hi hB
  have hs := sin_le h0
  have hs0 : 0 ≤ sin r := sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [pi_gt_three])
  have hc := one_sub_sq_div_two_le_cos (x := r)
  have hc1 := cos_le_one r
  have hcθ := one_sub_sq_div_two_le_cos (x := P.θ + r)
  have hsθ := sin_le_one (P.θ + r)
  have hsθ0 : 0 ≤ sin (P.θ + r) :=
    sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_gt_three])
  -- `α₁ ≥ -0.1`
  have hα1 : -0.1 ≤ (1 - cos r) / 2 - 2 * P.a₁ * sin r := by
    have h2 : P.a₁ * sin r ≤ 1.211 * 0.04 :=
      mul_le_mul (by linarith) (by linarith) hs0 (by norm_num)
    linarith
  -- `β₁ ≥ 1.39`
  have hβ : 1.39 ≤ 2 * P.a₁ * cos r - sin r / 2 - 1 := by
    have h3 : 0.999 ≤ cos r := by nlinarith [mul_nonneg h0 (show 0 ≤ 0.04 - r by linarith)]
    have h4 : 1.21 * 0.999 ≤ P.a₁ * cos r := mul_le_mul (by linarith) h3 (by norm_num) (by linarith)
    linarith
  have hcθ' : 0.74 ≤ cos (P.θ + r) := by
    nlinarith [mul_nonneg (show 0 ≤ P.θ + r by linarith) (show 0 ≤ 0.7206 - (P.θ + r) by linarith)]
  have h5 : -0.1 ≤ ((1 - cos r) / 2 - 2 * P.a₁ * sin r) * sin (P.θ + r) := by
    nlinarith [mul_nonneg (show 0 ≤ (1 - cos r) / 2 - 2 * P.a₁ * sin r + 0.1 by linarith) hsθ0]
  have h6 : 1.39 * 0.74 ≤ (2 * P.a₁ * cos r - sin r / 2 - 1) * cos (P.θ + r) :=
    mul_le_mul hβ hcθ' (by norm_num) (by linarith)
  linarith

/-- `(𝐱(t₁) - 𝐱(s)) · u_{t₃} ≥ 0` on `[0, t₁]`: `s ↦ 𝐱(s) · u_{t₃}` is monotone there. -/
lemma gb_corner_B (hP : P.IsSolution) (hB : P.Bounds) :
    ∀ s ∈ Icc 0 P.φ, 0 ≤ dot (P.path P.φ - P.path s) (uvec (π / 2 - P.θ)) := by
  intro s hs
  obtain ⟨o1, o2, o3, o4, o5⟩ := gb_order hP
  have hmono : MonotoneOn (fun r => dot (P.path r) (uvec (π / 2 - P.θ))) (Icc 0 P.φ) := by
    refine gb_monotoneOn_Icc (gb_hasDerivAt_dot_path hP _) (fun r hr => ?_)
    show 0 ≤ dot (P.gs_pathD r) (uvec (π / 2 - P.θ))
    have e1 : cos (r - (π / 2 - P.θ)) = sin (P.θ + r) := by
      rw [show r - (π / 2 - P.θ) = P.θ + r - π / 2 by ring, cos_sub_pi_div_two]
    have e2 : sin (π / 2 - P.θ - r) = cos (P.θ + r) := by
      rw [show π / 2 - P.θ - r = π / 2 - (P.θ + r) by ring, sin_pi_div_two_sub]
    rw [gb_pathD_phase hP (gs_piece₀ hr.2.le), dot_add_left, dot_smul_left, dot_smul_left,
      dot_uvec_uvec, dot_vvec_uvec', gs_α₁_eq hP, gs_β₁_eq hP, e1, e2]
    exact gb_corner_ineq hB hr.1.le hr.2.le
  have h : dot (P.path s) (uvec (π / 2 - P.θ)) ≤ dot (P.path P.φ) (uvec (π / 2 - P.θ)) :=
    hmono hs ⟨o1.le, le_rfl⟩ hs.2
  rw [dot_sub_left]
  linarith

/-- `(𝐱(t₄) - 𝐱(s)) · v_{t₂} ≥ 0` on `[t₄, π/2]`: `s ↦ 𝐱(s) · v_{t₂}` is antitone there. -/
lemma gb_corner_D (hP : P.IsSolution) (hB : P.Bounds) :
    ∀ s ∈ Icc (π / 2 - P.φ) (π / 2), 0 ≤ dot (P.path (π / 2 - P.φ) - P.path s) (vvec P.θ) := by
  intro s hs
  obtain ⟨o1, o2, o3, o4, o5⟩ := gb_order hP
  have hanti : AntitoneOn (fun r => dot (P.path r) (vvec P.θ)) (Icc (π / 2 - P.φ) (π / 2)) := by
    refine gb_antitoneOn_Icc (gb_hasDerivAt_dot_path hP _) (fun r hr => ?_)
    show dot (P.gs_pathD r) (vvec P.θ) ≤ 0
    have e1 : sin (r - P.θ) = cos (P.θ + (π / 2 - r)) := by
      rw [show r - P.θ = π / 2 - (P.θ + (π / 2 - r)) by ring, sin_pi_div_two_sub]
    have e2 : cos (r - P.θ) = sin (P.θ + (π / 2 - r)) := by
      rw [show r - P.θ = π / 2 - (P.θ + (π / 2 - r)) by ring, cos_pi_div_two_sub]
    rw [gb_pathD_phase hP (gs_piece₄ hr.1.le), dot_add_left, dot_smul_left, dot_smul_left,
      dot_uvec_vvec', dot_vvec_vvec, gb_α₅ hP, gb_β₅ hP, e1, e2]
    have := gb_corner_ineq hB (r := π / 2 - r) (by linarith [hr.2]) (by linarith [hr.1])
    linarith
  have h : dot (P.path s) (vvec P.θ) ≤ dot (P.path (π / 2 - P.φ)) (vvec P.θ) :=
    hanti ⟨le_rfl, o5.le⟩ hs hs.1
  rw [dot_sub_left]
  linarith

/-! ### Positivity of the height of the rotation path on `[t₁, t₄]` -/

/-- `𝐱'_y ≥ 0` on phase 2. -/
private lemma gb_y'₂ (hB : P.Bounds) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ P.θ) :
    0 ≤ (2 * P.b₁ + 1 - t) * sin t + (1 / 2 - t ^ 2 / 4 + P.b₁ * t + P.b₂) * cos t := by
  have := gs_θ_hi hB
  have := gs_b₁_lo hB
  have := gs_b₁_hi hB
  have := gs_b₂_lo hB
  have hs := sin_le h0
  have hs0 : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [pi_gt_three])
  have hc := one_sub_sq_div_two_le_cos (x := t)
  have hc' : 0.767 ≤ cos t := by nlinarith [mul_nonneg h0 (show 0 ≤ 0.6814 - t by linarith)]
  have hβ : 0.944 ≤ 1 / 2 - t ^ 2 / 4 + P.b₁ * t + P.b₂ := by
    nlinarith [mul_nonneg (show 0 ≤ P.b₁ + 0.527624699 by linarith) h0,
      mul_nonneg (show 0 ≤ 0.6814 - t by linarith) (show 0 ≤ 0.6814 + t by linarith)]
  have h2 : -(2 * P.b₁ + 1 - t) * sin t ≤ 0.737 * 0.6814 :=
    mul_le_mul (by linarith) (by linarith) hs0 (by norm_num)
  have h3 : 0.944 * 0.767 ≤ (1 / 2 - t ^ 2 / 4 + P.b₁ * t + P.b₂) * cos t :=
    mul_le_mul hβ hc' (by norm_num) (by linarith)
  linarith

/-- `𝐱'_y` on phase 3 has the sign of `π/4 - t`. -/
private lemma gb_y'₃ (hB : P.Bounds) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ π / 2 - P.θ) :
    (π / 2 - 1 - P.c₁ - t) * sin t + (1 + P.c₁ - t) * cos t =
      (1 + P.c₁ - t) * (cos t - sin t) + (π / 2 - 2 * t) * sin t ∧ 0 ≤ 1 + P.c₁ - t ∧
      0 ≤ sin t := by
  have := gs_θ_lo hB
  have := gs_c₁_lo hB
  have := pi_lt_d2
  refine ⟨by ring, by linarith, sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [pi_pos])⟩

/-- `𝐱(t)_y > 0` on `[t₁, t₄]`: `𝐱_y` increases on `[t₁, π/4]` and decreases on `[π/4, t₄]`,
and `𝐱(t₁)_y = 𝐱(t₄)_y ≈ 0.0552`. -/
lemma gb_x_pos (hP : P.IsSolution) (hB : P.Bounds) :
    ∀ t ∈ Icc P.φ (π / 2 - P.φ), 0 < (P.path t).2 := by
  intro t ht
  obtain ⟨o1, o2, o3, o4, o5⟩ := gb_order hP
  have hθ' : P.θ < π / 4 := (gs_ord hP).2.2
  have hy : ∀ r, HasDerivAt (fun r => (P.path r).2) (P.gs_pathD r).2 r :=
    fun r => gb_hasDerivAt_snd (gs_hasDerivAt_path hP r)
  have hd : ∀ {i : ℕ} {r : ℝ}, gs_piece P i r →
      (P.gs_pathD r).2 = (P.gs_phase i).α r * sin r + (P.gs_phase i).β r * cos r := by
    intro i r h
    rw [gb_pathD_phase hP h]
    simp [uvec, vvec]
  have hmono : MonotoneOn (fun r => (P.path r).2) (Icc P.φ (π / 4)) := by
    refine gb_monotoneOn_Icc hy (fun r hr => ?_)
    show 0 ≤ (P.gs_pathD r).2
    rcases le_or_gt r P.θ with h | h
    · rw [hd (gs_piece₁ hr.1.le h), gs_α₂_eq, gs_β₂_eq]
      exact gb_y'₂ hB (by linarith [hr.1]) h
    · rw [hd (gs_piece₂ h.le (by linarith [hr.2])), gs_α₃_eq hP, gs_β₃_eq]
      obtain ⟨e, h1, h2⟩ := gb_y'₃ hB (t := r) (by linarith) (by linarith [hr.2])
      have h3 : sin r ≤ cos r := by
        rw [← cos_pi_div_two_sub]
        exact cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos])
          (by linarith [hr.2])
      rw [e]
      exact add_nonneg (mul_nonneg h1 (by linarith)) (mul_nonneg (by linarith [hr.2]) h2)
  have hanti : AntitoneOn (fun r => (P.path r).2) (Icc (π / 4) (π / 2 - P.φ)) := by
    refine gb_antitoneOn_Icc hy (fun r hr => ?_)
    show (P.gs_pathD r).2 ≤ 0
    rcases le_or_gt r (π / 2 - P.θ) with h | h
    · rw [hd (gs_piece₂ (by linarith [hr.1]) h), gs_α₃_eq hP, gs_β₃_eq]
      obtain ⟨e, h1, h2⟩ := gb_y'₃ hB (t := r) (by linarith [hr.1, pi_pos]) h
      have h3 : cos r ≤ sin r := by
        rw [← cos_pi_div_two_sub]
        exact cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [hr.2, pi_pos])
          (by linarith [hr.1])
      rw [e]
      have h4 : (1 + P.c₁ - r) * (cos r - sin r) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos h1 (by linarith)
      have h5 : (π / 2 - 2 * r) * sin r ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith [hr.1]) h2
      linarith
    · rw [hd (gs_piece₃ h.le hr.2.le), gb_α₄ hP, gb_β₄ hP, ← cos_pi_div_two_sub r,
        ← sin_pi_div_two_sub r]
      have := gb_y'₂ hB (t := π / 2 - r) (by linarith [hr.2]) (by linarith)
      linarith
  -- the values at the endpoints
  obtain ⟨-, -, hW1', hW3, hW4⟩ := gb_W_bounds hB
  have hend : ∀ κ : ℝ, 0.472406519 ≤ κ →
      0 < sin P.φ * (-P.φ ^ 2 / 4 + P.b₁ * P.φ + P.b₂) + cos P.φ * (P.φ / 2 - P.b₁ - 1) + κ := by
    intro κ hκ
    have := gs_φ_lo hB
    have := gs_φ_hi hB
    have h1 := sin_ge_sub_cube o1.le
    have h2 := cos_le_one P.φ
    have h3' : P.φ ^ 3 ≤ 0.039177465 ^ 3 := pow_le_pow_left₀ o1.le (by linarith) 3
    have h3 : 0.039167 ≤ sin P.φ := by norm_num at h3'; linarith
    have h4 : 0.039167 * 0.8992 ≤ sin P.φ * (-P.φ ^ 2 / 4 + P.b₁ * P.φ + P.b₂) :=
      mul_le_mul h3 hW1' (by norm_num) (by linarith)
    have h5 : P.φ / 2 - P.b₁ - 1 ≤ cos P.φ * (P.φ / 2 - P.b₁ - 1) := by
      nlinarith [mul_nonneg (show 0 ≤ -(P.φ / 2 - P.b₁ - 1) by linarith)
        (show 0 ≤ 1 - cos P.φ by linarith)]
    linarith
  have hφ : 0 < (P.path P.φ).2 := by
    rw [gs_path_eq_phase hP (gs_piece₁ le_rfl o2.le)]
    have e : ((P.gs_phase 1).X P.φ).2 = sin P.φ * (-P.φ ^ 2 / 4 + P.b₁ * P.φ + P.b₂) +
        cos P.φ * (P.φ / 2 - P.b₁ - 1) + P.κ₂.2 := by
      simp only [gs_phase, gs_Phase.X, gs_ph2, rot, Prod.snd_add]
    rw [e]
    exact hend P.κ₂.2 hB.κ₂₂_mem.1
  have hφ' : 0 < (P.path (π / 2 - P.φ)).2 := by
    rw [gs_path_eq_phase hP (gs_piece₃ o4.le le_rfl)]
    have e : ((P.gs_phase 3).X (π / 2 - P.φ)).2 = sin P.φ * (-P.φ ^ 2 / 4 + P.b₁ * P.φ + P.b₂) +
        cos P.φ * (P.φ / 2 - P.b₁ - 1) + P.κ₄.2 := by
      simp only [gs_phase, gs_Phase.X, gs_ph4, rot, Prod.snd_add, sin_pi_div_two_sub,
        cos_pi_div_two_sub, gs_d₁ hP, gs_d₂ hP]
      ring
    rw [e]
    exact hend P.κ₄.2 hB.κ₄₂_mem.1
  rcases le_total t (π / 4) with h | h
  · have h1 : (P.path P.φ).2 ≤ (P.path t).2 := hmono ⟨le_rfl, by linarith⟩ ⟨ht.1, h⟩ ht.1
    linarith
  · have h1 : (P.path (π / 2 - P.φ)).2 ≤ (P.path t).2 :=
      hanti ⟨h, ht.2⟩ ⟨by linarith [pi_pos], le_rfl⟩ ht.2
    linarith

/-! ### Regularity of the curvature radii -/

private lemma gb_continuous_ρA (i : ℕ) : Continuous (P.gs_phase i).ρA := by
  match i with
  | 0 => unfold gs_Phase.ρA; simp only [gs_phase, gs_ph1]; fun_prop
  | 1 => unfold gs_Phase.ρA; simp only [gs_phase, gs_ph2]; fun_prop
  | 2 => unfold gs_Phase.ρA; simp only [gs_phase, gs_ph3]; fun_prop
  | 3 => unfold gs_Phase.ρA; simp only [gs_phase, gs_ph4]; fun_prop
  | n + 4 =>
    show Continuous (P.gs_phase 4).ρA
    unfold gs_Phase.ρA; simp only [gs_phase, gs_ph5]; fun_prop

private lemma gb_continuous_ρC (i : ℕ) : Continuous (P.gs_phase i).ρC := by
  match i with
  | 0 => unfold gs_Phase.ρC; simp only [gs_phase, gs_ph1]; fun_prop
  | 1 => unfold gs_Phase.ρC; simp only [gs_phase, gs_ph2]; fun_prop
  | 2 => unfold gs_Phase.ρC; simp only [gs_phase, gs_ph3]; fun_prop
  | 3 => unfold gs_Phase.ρC; simp only [gs_phase, gs_ph4]; fun_prop
  | n + 4 =>
    show Continuous (P.gs_phase 4).ρC
    unfold gs_Phase.ρC; simp only [gs_phase, gs_ph5]; fun_prop

lemma gb_rhoA_measurable : Measurable (gb_rhoA P) := by
  unfold gb_rhoA
  exact Measurable.ite measurableSet_Iio (gb_continuous_ρA 0).measurable
    (Measurable.ite measurableSet_Iio (gb_continuous_ρA 1).measurable
      (Measurable.ite measurableSet_Iic (gb_continuous_ρA 2).measurable
        (Measurable.ite measurableSet_Iic (gb_continuous_ρA 3).measurable
          (gb_continuous_ρA 4).measurable)))

lemma gb_rhoC_measurable : Measurable (gb_rhoC P) := by
  unfold gb_rhoC
  exact Measurable.ite measurableSet_Iio (gb_continuous_ρC 0).measurable
    (Measurable.ite measurableSet_Iio (gb_continuous_ρC 1).measurable
      (Measurable.ite measurableSet_Iic (gb_continuous_ρC 2).measurable
        (Measurable.ite measurableSet_Iic (gb_continuous_ρC 3).measurable
          (gb_continuous_ρC 4).measurable)))

lemma gb_rhoA_bdd : ∃ M, ∀ t ∈ Icc 0 (π / 2), |gb_rhoA P t| ≤ M := by
  have hc : Continuous fun t => |(P.gs_phase 0).ρA t| + |(P.gs_phase 1).ρA t| +
      |(P.gs_phase 2).ρA t| + |(P.gs_phase 3).ρA t| + |(P.gs_phase 4).ρA t| :=
    (((((gb_continuous_ρA 0).abs.add (gb_continuous_ρA 1).abs).add (gb_continuous_ρA 2).abs).add
      (gb_continuous_ρA 3).abs).add (gb_continuous_ρA 4).abs)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := π / 2)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨M, fun t ht => ?_⟩
  have h : ‖|(P.gs_phase 0).ρA t| + |(P.gs_phase 1).ρA t| + |(P.gs_phase 2).ρA t| +
      |(P.gs_phase 3).ρA t| + |(P.gs_phase 4).ρA t|‖ ≤ M := hM t ht
  rw [Real.norm_eq_abs] at h
  have := le_abs_self (|(P.gs_phase 0).ρA t| + |(P.gs_phase 1).ρA t| + |(P.gs_phase 2).ρA t| +
      |(P.gs_phase 3).ρA t| + |(P.gs_phase 4).ρA t|)
  have := abs_nonneg ((P.gs_phase 0).ρA t)
  have := abs_nonneg ((P.gs_phase 1).ρA t)
  have := abs_nonneg ((P.gs_phase 2).ρA t)
  have := abs_nonneg ((P.gs_phase 3).ρA t)
  have := abs_nonneg ((P.gs_phase 4).ρA t)
  unfold gb_rhoA
  split_ifs <;> linarith

lemma gb_rhoC_bdd : ∃ M, ∀ t ∈ Icc 0 (π / 2), |gb_rhoC P t| ≤ M := by
  have hc : Continuous fun t => |(P.gs_phase 0).ρC t| + |(P.gs_phase 1).ρC t| +
      |(P.gs_phase 2).ρC t| + |(P.gs_phase 3).ρC t| + |(P.gs_phase 4).ρC t| :=
    (((((gb_continuous_ρC 0).abs.add (gb_continuous_ρC 1).abs).add (gb_continuous_ρC 2).abs).add
      (gb_continuous_ρC 3).abs).add (gb_continuous_ρC 4).abs)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := π / 2)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨M, fun t ht => ?_⟩
  have h : ‖|(P.gs_phase 0).ρC t| + |(P.gs_phase 1).ρC t| + |(P.gs_phase 2).ρC t| +
      |(P.gs_phase 3).ρC t| + |(P.gs_phase 4).ρC t|‖ ≤ M := hM t ht
  rw [Real.norm_eq_abs] at h
  have := le_abs_self (|(P.gs_phase 0).ρC t| + |(P.gs_phase 1).ρC t| + |(P.gs_phase 2).ρC t| +
      |(P.gs_phase 3).ρC t| + |(P.gs_phase 4).ρC t|)
  have := abs_nonneg ((P.gs_phase 0).ρC t)
  have := abs_nonneg ((P.gs_phase 1).ρC t)
  have := abs_nonneg ((P.gs_phase 2).ρC t)
  have := abs_nonneg ((P.gs_phase 3).ρC t)
  have := abs_nonneg ((P.gs_phase 4).ρC t)
  unfold gb_rhoC
  split_ifs <;> linarith

/-! ### Identities at the breakpoints and the endpoints -/

/-- `𝐁(t₃) = 𝐱(t₁)` (Romik's (43)). -/
lemma gb_B_t₃ (hP : P.IsSolution) :
    P.path (π / 2 - P.θ) + P.gs_α (π / 2 - P.θ) • vvec (π / 2 - P.θ) = P.path P.φ :=
  gs_contactB_t₃ hP

/-- `𝐃(t₂) = 𝐱(t₄)` (Romik's (44)). -/
lemma gb_D_t₂ (hP : P.IsSolution) :
    P.path P.θ - P.gs_β P.θ • uvec P.θ = P.path (π / 2 - P.φ) :=
  gs_contactD_t₂ hP

/-- `𝐁(π/2)_y = 0`. -/
lemma gb_B_end (hP : P.IsSolution) :
    (P.path (π / 2) + P.gs_α (π / 2) • vvec (π / 2)).2 = 0 :=
  gs_contactB_pi_div_two_snd hP

/-- `𝐃(0)_y = 0`. -/
lemma gb_D_end (hP : P.IsSolution) : (P.path 0 - P.gs_β 0 • uvec 0).2 = 0 :=
  gs_contactD_zero_snd hP

end GerverParams

end MovingSofa
