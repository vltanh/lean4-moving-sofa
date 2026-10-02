module

public import MovingSofa.Gerver.Bounds
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The rotating frame of Gerver's rotation path

Infrastructure for `MovingSofa.Gerver.Structure` (package GS, see `notes/gerver_plan.md`).

On each phase `i` Romik's rotation path is `𝐱(t) = R_t (w₁ t, w₂ t) + κ_i`. A `gs_Phase` records
`w₁, w₂`, their first two derivatives and `κ`; `gs_Phase.Valid` says that the derivatives are
correct. For such a phase `Φ`:
* `Φ.X t = R_t (w₁ t, w₂ t) + κ` (the phase formula of `𝐱`), `Φ.X' t = α t • u_t + β t • v_t`
  with `Φ.α = w₁' - w₂`, `Φ.β = w₂' + w₁` (`gs_Phase.hasDerivAt_X`);
* `Φ.ρA = w₁'' + w₁ + 1`, `Φ.ρC = w₂'' + w₂ + 1`;
* the contact curves `Φ.A = R_t (w₁ + 1, w₁') + κ`, `Φ.B = R_t (w₁, w₁') + κ`,
  `Φ.C = R_t (-w₂', w₂ + 1) + κ`, `Φ.D = R_t (-w₂', w₂) + κ`, with `Φ.A_eq : Φ.A t = Φ.X t +
  Φ.α t • v_t + u_t` (and `B_eq`, `C_eq`, `D_eq`) and derivatives `hasDerivAt_A : 𝐀' = ρA v`,
  `hasDerivAt_B : 𝐁' = (ρA - 1) v`, `hasDerivAt_C : 𝐂' = -ρC u`, `hasDerivAt_D : 𝐃' = (1 - ρC) u`.

The five phases of `P : GerverParams` are `P.gs_ph1, …, P.gs_ph5` (`P.gs_phase i`, `i = 0, …, 4`),
with `P.x₁ = P.gs_ph1.X` (`gs_x₁_eq`, …). For a solution `hP : P.IsSolution`:
* `gs_piece P i t`: the closed phase intervals `(-∞, φ]`, `[φ, θ]`, `[θ, π/2 - θ]`,
  `[π/2 - θ, π/2 - φ]`, `[π/2 - φ, ∞)`; `gs_opiece` the open ones, `gs_rpiece` the half-open
  `[t_{i-1}, t_i)`;
* `gs_path_eq_phase hP : gs_piece P i t → P.path t = (P.gs_phase i).X t`;
* `gs_hasDerivAt_path hP t : HasDerivAt P.path (P.gs_pathD t) t` for every `t : ℝ`, with
  `gs_pathD_eq_phase hP : gs_piece P i t → P.gs_pathD t = (P.gs_phase i).X' t`,
  `gs_deriv_path_eq hP : gs_piece P i t → deriv P.path t = α • u_t + β • v_t`,
  `gs_continuous_pathD`, `gs_contDiff_path : ContDiff ℝ 1 P.path`;
* `P.gs_α t = ⟨𝐱'(t), u_t⟩`, `P.gs_β t = ⟨𝐱'(t), v_t⟩` (continuous: `gs_continuous_α/β`), with
  `gs_α_eq hP : gs_piece P i t → P.gs_α t = (P.gs_phase i).α t` (and `gs_β_eq`), and the explicit
  formulas `gs_α₁_eq … gs_β₅_eq`, `gs_ρA₁_eq … gs_ρC₅_eq` (phases 4–5 in the variable
  `π/2 - s`, where they are minus the formulas of phases 2–1);
* `gs_contactA_eq hP : gs_piece P i t → contactA P.path t = (P.gs_phase i).A t` (and `B`, `C`,
  `D`), and `gs_contactA_eq' : contactA P.path t = P.path t + P.gs_α t • v_t + u_t` (and `B`,
  `C`, `D`);
* `gs_hasDerivAt_contactA/B/C/D hP : gs_opiece P i t → HasDerivAt (contactX P.path) _ t`
  and the right derivatives `gs_hasDerivWithinAt_contactA/C hP : gs_rpiece P i t → …`;
* identities: `gs_path_zero : 𝐱(0) = 0`, `gs_path_pi_div_two_snd : 𝐱(π/2)_y = 0`,
  `gs_contactB_t₃ : 𝐁(π/2 - θ) = 𝐱(φ)`, `gs_contactD_t₂ : 𝐃(θ) = 𝐱(π/2 - φ)`,
  `gs_contactB_pi_div_two_snd : 𝐁(π/2)_y = 0`, `gs_contactD_zero_snd : 𝐃(0)_y = 0`.

Under the enclosures `hB : P.Bounds`: `gs_α_neg : 0 < t → t ≤ π/2 → P.gs_α t < 0`,
`gs_β_pos : 0 ≤ t → t < π/2 → 0 < P.gs_β t`, `gs_α_zero`, `gs_β_pi_div_two`, `gs_α_nonpos`,
`gs_β_nonneg`, and `gs_ρ_nonneg : gs_rpiece P i t → 0 ≤ t → t ≤ π/2 → 0 ≤ ρA ∧ 0 ≤ ρC`.
-/

@[expose] public section

open Real Set Filter Topology

namespace MovingSofa

/-- One phase of a rotation path in the rotating frame: `𝐱(t) = R_t (w₁ t, w₂ t) + κ`, with the
first two derivatives of `w₁` and `w₂`. -/
structure gs_Phase where
  w₁ : ℝ → ℝ
  w₂ : ℝ → ℝ
  w₁' : ℝ → ℝ
  w₂' : ℝ → ℝ
  w₁'' : ℝ → ℝ
  w₂'' : ℝ → ℝ
  κ : ℝ × ℝ

namespace gs_Phase

variable (Φ : gs_Phase)

/-- The derivatives recorded in a phase are the derivatives of its functions. -/
structure Valid : Prop where
  d₁ : ∀ t, HasDerivAt Φ.w₁ (Φ.w₁' t) t
  d₂ : ∀ t, HasDerivAt Φ.w₂ (Φ.w₂' t) t
  dd₁ : ∀ t, HasDerivAt Φ.w₁' (Φ.w₁'' t) t
  dd₂ : ∀ t, HasDerivAt Φ.w₂' (Φ.w₂'' t) t

/-- The rotation path of the phase, `𝐱(t) = R_t (w₁ t, w₂ t) + κ`. -/
noncomputable def X (t : ℝ) : ℝ × ℝ := rot t (Φ.w₁ t, Φ.w₂ t) + Φ.κ
/-- `α = ⟨𝐱', u_t⟩ = w₁' - w₂`. -/
def α (t : ℝ) : ℝ := Φ.w₁' t - Φ.w₂ t
/-- `β = ⟨𝐱', v_t⟩ = w₂' + w₁`. -/
def β (t : ℝ) : ℝ := Φ.w₂' t + Φ.w₁ t
/-- The derivative `𝐱'(t) = α u_t + β v_t`. -/
noncomputable def X' (t : ℝ) : ℝ × ℝ := Φ.α t • uvec t + Φ.β t • vvec t
/-- `ρ_A = w₁'' + w₁ + 1`, with `𝐀' = ρ_A v_t`. -/
def ρA (t : ℝ) : ℝ := Φ.w₁'' t + Φ.w₁ t + 1
/-- `ρ_C = w₂'' + w₂ + 1`, with `𝐂' = -ρ_C u_t`. -/
def ρC (t : ℝ) : ℝ := Φ.w₂'' t + Φ.w₂ t + 1
/-- The contact curve `𝐀 = 𝐱 + α v + u` of the phase. -/
noncomputable def A (t : ℝ) : ℝ × ℝ := rot t (Φ.w₁ t + 1, Φ.w₁' t) + Φ.κ
/-- The contact curve `𝐁 = 𝐱 + α v` of the phase. -/
noncomputable def B (t : ℝ) : ℝ × ℝ := rot t (Φ.w₁ t, Φ.w₁' t) + Φ.κ
/-- The contact curve `𝐂 = 𝐱 - β u + v` of the phase. -/
noncomputable def C (t : ℝ) : ℝ × ℝ := rot t (-Φ.w₂' t, Φ.w₂ t + 1) + Φ.κ
/-- The contact curve `𝐃 = 𝐱 - β u` of the phase. -/
noncomputable def D (t : ℝ) : ℝ × ℝ := rot t (-Φ.w₂' t, Φ.w₂ t) + Φ.κ

end gs_Phase

lemma gs_rot_pair (t a b : ℝ) : rot t (a, b) = a • uvec t + b • vvec t := by
  ext <;> simp [rot, uvec, vvec] <;> ring

/-- The derivative of `t ↦ R_t (a t, b t) + κ`. -/
lemma gs_hasDerivAt_frame {a b : ℝ → ℝ} {a' b' t : ℝ} (κ : ℝ × ℝ) (ha : HasDerivAt a a' t)
    (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => rot s (a s, b s) + κ) ((a' - b t) • uvec t + (b' + a t) • vvec t) t := by
  have h1 := ((hasDerivAt_cos t).mul ha).sub ((hasDerivAt_sin t).mul hb)
  have h2 := ((hasDerivAt_sin t).mul ha).add ((hasDerivAt_cos t).mul hb)
  have h : HasDerivAt (fun s => rot s (a s, b s) + κ) _ t := (h1.prodMk h2).add_const κ
  refine h.congr_deriv ?_
  ext <;> simp [uvec, vvec] <;> ring

namespace gs_Phase

variable {Φ : gs_Phase}

lemma hasDerivAt_X (hΦ : Φ.Valid) (t : ℝ) : HasDerivAt Φ.X (Φ.X' t) t :=
  gs_hasDerivAt_frame Φ.κ (hΦ.d₁ t) (hΦ.d₂ t)

lemma hasDerivAt_A (hΦ : Φ.Valid) (t : ℝ) : HasDerivAt Φ.A (Φ.ρA t • vvec t) t := by
  refine (gs_hasDerivAt_frame Φ.κ ((hΦ.d₁ t).add_const 1) (hΦ.dd₁ t)).congr_deriv ?_
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, uvec,
    vvec, ρA] <;> ring

lemma hasDerivAt_B (hΦ : Φ.Valid) (t : ℝ) : HasDerivAt Φ.B ((Φ.ρA t - 1) • vvec t) t := by
  refine (gs_hasDerivAt_frame Φ.κ (hΦ.d₁ t) (hΦ.dd₁ t)).congr_deriv ?_
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, uvec,
    vvec, ρA] <;> ring

lemma hasDerivAt_C (hΦ : Φ.Valid) (t : ℝ) : HasDerivAt Φ.C (-Φ.ρC t • uvec t) t := by
  refine (gs_hasDerivAt_frame Φ.κ (hΦ.dd₂ t).neg ((hΦ.d₂ t).add_const 1)).congr_deriv ?_
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, uvec,
    vvec, ρC, Pi.neg_apply] <;> ring

lemma hasDerivAt_D (hΦ : Φ.Valid) (t : ℝ) : HasDerivAt Φ.D ((1 - Φ.ρC t) • uvec t) t := by
  refine (gs_hasDerivAt_frame Φ.κ (hΦ.dd₂ t).neg (hΦ.d₂ t)).congr_deriv ?_
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, uvec,
    vvec, ρC, Pi.neg_apply] <;> ring

variable (Φ)

lemma dot_X'_uvec (t : ℝ) : dot (Φ.X' t) (uvec t) = Φ.α t := by
  simp [X', dot_add_left, dot_smul_left]

lemma dot_X'_vvec (t : ℝ) : dot (Φ.X' t) (vvec t) = Φ.β t := by
  simp [X', dot_add_left, dot_smul_left]

lemma A_eq (t : ℝ) : Φ.A t = Φ.X t + Φ.α t • vvec t + uvec t := by
  simp only [A, X, α, gs_rot_pair]; ext <;> simp <;> ring

lemma B_eq (t : ℝ) : Φ.B t = Φ.X t + Φ.α t • vvec t := by
  simp only [B, X, α, gs_rot_pair]; ext <;> simp <;> ring

lemma C_eq (t : ℝ) : Φ.C t = Φ.X t - Φ.β t • uvec t + vvec t := by
  simp only [C, X, β, gs_rot_pair]; ext <;> simp <;> ring

lemma D_eq (t : ℝ) : Φ.D t = Φ.X t - Φ.β t • uvec t := by
  simp only [D, X, β, gs_rot_pair]; ext <;> simp <;> ring

end gs_Phase

end MovingSofa


namespace MovingSofa

/-! ### Gluing along the five phases -/

/-- A function glued from five functions along the phases of Gerver's rotation path. -/
noncomputable def gs_pw (P : GerverParams) {E : Type*} (f₁ f₂ f₃ f₄ f₅ : ℝ → E) (t : ℝ) : E :=
  if t < P.φ then f₁ t else if t < P.θ then f₂ t else if t ≤ π / 2 - P.θ then f₃ t
  else if t ≤ π / 2 - P.φ then f₄ t else f₅ t

/-- The ordering `0 < φ < θ < π/4` of the phase angles. -/
def gs_Ord (P : GerverParams) : Prop := 0 < P.φ ∧ P.φ < P.θ ∧ P.θ < π / 4

/-- Five functions agree at the four breakpoints of the phases. -/
def gs_Match (P : GerverParams) {E : Type*} (f₁ f₂ f₃ f₄ f₅ : ℝ → E) : Prop :=
  f₁ P.φ = f₂ P.φ ∧ f₂ P.θ = f₃ P.θ ∧ f₃ (π / 2 - P.θ) = f₄ (π / 2 - P.θ) ∧
    f₄ (π / 2 - P.φ) = f₅ (π / 2 - P.φ)

section pw

variable {P : GerverParams} {E : Type*} {f₁ f₂ f₃ f₄ f₅ : ℝ → E}

lemma gs_Ord.θ_lt (hO : gs_Ord P) : P.θ < π / 2 - P.θ := by
  obtain ⟨h1, h2, h3⟩ := hO; linarith

lemma gs_Ord.φ_lt_θ (hO : gs_Ord P) : P.φ < P.θ := hO.2.1

lemma gs_Ord.φ_pos (hO : gs_Ord P) : 0 < P.φ := hO.1

lemma gs_Ord.lt_φ' (hO : gs_Ord P) : π / 2 - P.θ < π / 2 - P.φ := by
  obtain ⟨h1, h2, h3⟩ := hO; linarith

lemma gs_pw_eq₁ (hO : gs_Ord P) (hm : gs_Match P f₁ f₂ f₃ f₄ f₅) {t : ℝ} (ht : t ≤ P.φ) :
    gs_pw P f₁ f₂ f₃ f₄ f₅ t = f₁ t := by
  unfold gs_pw
  rcases ht.lt_or_eq with h | rfl
  · rw [ite_eq_left h]
  · rw [ite_eq_right (lt_irrefl _), ite_eq_left hO.φ_lt_θ, hm.1]

lemma gs_pw_eq₂ (hO : gs_Ord P) (hm : gs_Match P f₁ f₂ f₃ f₄ f₅) {t : ℝ} (ht₁ : P.φ ≤ t)
    (ht₂ : t ≤ P.θ) : gs_pw P f₁ f₂ f₃ f₄ f₅ t = f₂ t := by
  unfold gs_pw
  rw [ite_eq_right (not_lt.2 ht₁)]
  rcases ht₂.lt_or_eq with h | rfl
  · rw [ite_eq_left h]
  · rw [ite_eq_right (lt_irrefl _), ite_eq_left hO.θ_lt.le, hm.2.1]

lemma gs_pw_eq₃ (hO : gs_Ord P) {t : ℝ} (ht₁ : P.θ ≤ t)
    (ht₂ : t ≤ π / 2 - P.θ) : gs_pw P f₁ f₂ f₃ f₄ f₅ t = f₃ t := by
  unfold gs_pw
  rw [ite_eq_right (not_lt.2 (hO.φ_lt_θ.le.trans ht₁)), ite_eq_right (not_lt.2 ht₁),
    ite_eq_left ht₂]

lemma gs_pw_eq₄ (hO : gs_Ord P) (hm : gs_Match P f₁ f₂ f₃ f₄ f₅) {t : ℝ}
    (ht₁ : π / 2 - P.θ ≤ t) (ht₂ : t ≤ π / 2 - P.φ) : gs_pw P f₁ f₂ f₃ f₄ f₅ t = f₄ t := by
  unfold gs_pw
  have h1 : P.θ ≤ t := hO.θ_lt.le.trans ht₁
  rw [ite_eq_right (not_lt.2 (hO.φ_lt_θ.le.trans h1)), ite_eq_right (not_lt.2 h1)]
  rcases ht₁.lt_or_eq with h | rfl
  · rw [ite_eq_right (not_le.2 h), ite_eq_left ht₂]
  · rw [ite_eq_left le_rfl, hm.2.2.1]

lemma gs_pw_eq₅ (hO : gs_Ord P) (hm : gs_Match P f₁ f₂ f₃ f₄ f₅) {t : ℝ}
    (ht₁ : π / 2 - P.φ ≤ t) : gs_pw P f₁ f₂ f₃ f₄ f₅ t = f₅ t := by
  unfold gs_pw
  have h0 : π / 2 - P.θ < t := hO.lt_φ'.trans_le ht₁
  have h1 : P.θ ≤ t := (hO.θ_lt.trans h0).le
  rw [ite_eq_right (not_lt.2 (hO.φ_lt_θ.le.trans h1)), ite_eq_right (not_lt.2 h1),
    ite_eq_right (not_le.2 h0)]
  rcases ht₁.lt_or_eq with h | rfl
  · rw [ite_eq_right (not_le.2 h)]
  · rw [ite_eq_left le_rfl, hm.2.2.2]

/-- Gluing two differentiable functions at a point. -/
lemma gs_hasDerivAt_glue [NormedAddCommGroup E] [NormedSpace ℝ E] {F G H : ℝ → E} {F' : E}
    {a t b : ℝ} (ha : a < t) (hb : t < b) (hG : ∀ s ∈ Icc a t, F s = G s)
    (hH : ∀ s ∈ Icc t b, F s = H s) (hG' : HasDerivAt G F' t) (hH' : HasDerivAt H F' t) :
    HasDerivAt F F' t := by
  have h1 : HasDerivWithinAt F F' (Iic t) t :=
    (hG'.hasDerivWithinAt.congr hG (hG t ⟨ha.le, le_rfl⟩)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLE ha)
  have h2 : HasDerivWithinAt F F' (Ici t) t :=
    (hH'.hasDerivWithinAt.congr hH (hH t ⟨le_rfl, hb.le⟩)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE hb)
  have := h1.union h2
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this

/-- Gluing two continuous functions at a point. -/
lemma gs_continuousAt_glue [TopologicalSpace E] {F G H : ℝ → E} {a t b : ℝ} (ha : a < t)
    (hb : t < b) (hG : ∀ s ∈ Icc a t, F s = G s) (hH : ∀ s ∈ Icc t b, F s = H s)
    (hG' : ContinuousAt G t) (hH' : ContinuousAt H t) : ContinuousAt F t := by
  rw [continuousAt_iff_continuous_left_right]
  constructor
  · exact (hG'.continuousWithinAt.congr hG (hG t ⟨ha.le, le_rfl⟩)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLE ha)
  · exact (hH'.continuousWithinAt.congr hH (hH t ⟨le_rfl, hb.le⟩)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE hb)

/-- The closed phase intervals `(-∞, φ]`, `[φ, θ]`, `[θ, π/2 - θ]`, `[π/2 - θ, π/2 - φ]`,
`[π/2 - φ, ∞)`, indexed by `0, …, 4`. -/
def gs_piece (P : GerverParams) : ℕ → ℝ → Prop
  | 0, t => t ≤ P.φ
  | 1, t => P.φ ≤ t ∧ t ≤ P.θ
  | 2, t => P.θ ≤ t ∧ t ≤ π / 2 - P.θ
  | 3, t => π / 2 - P.θ ≤ t ∧ t ≤ π / 2 - P.φ
  | _, t => π / 2 - P.φ ≤ t

/-- Selection of one of five functions. -/
def gs_sel {E : Type*} (f₁ f₂ f₃ f₄ f₅ : ℝ → E) : ℕ → ℝ → E
  | 0 => f₁
  | 1 => f₂
  | 2 => f₃
  | 3 => f₄
  | _ => f₅

lemma gs_pw_eq_sel (hO : gs_Ord P) (hm : gs_Match P f₁ f₂ f₃ f₄ f₅) {i : ℕ} {t : ℝ}
    (h : gs_piece P i t) : gs_pw P f₁ f₂ f₃ f₄ f₅ t = gs_sel f₁ f₂ f₃ f₄ f₅ i t := by
  match i, h with
  | 0, h => exact gs_pw_eq₁ hO hm h
  | 1, h => exact gs_pw_eq₂ hO hm h.1 h.2
  | 2, h => exact gs_pw_eq₃ hO h.1 h.2
  | 3, h => exact gs_pw_eq₄ hO hm h.1 h.2
  | n + 4, h => exact gs_pw_eq₅ hO hm h

/-- Every point has a left neighbourhood inside one closed phase interval and a right
neighbourhood inside one closed phase interval. -/
lemma gs_local (hO : gs_Ord P) (t : ℝ) :
    ∃ a b i j, a < t ∧ t < b ∧ (∀ s ∈ Icc a t, gs_piece P i s) ∧
      (∀ s ∈ Icc t b, gs_piece P j s) := by
  have o1 := hO.φ_lt_θ
  have o2 := hO.θ_lt
  have o3 := hO.lt_φ'
  rcases lt_trichotomy t P.φ with h | h | h
  · exact ⟨t - 1, P.φ, 0, 0, by linarith, h, fun s hs => (show s ≤ P.φ by linarith [hs.2]),
      fun s hs => (show s ≤ P.φ from hs.2)⟩
  · subst h
    exact ⟨P.φ - 1, P.θ, 0, 1, by linarith, o1, fun s hs => (show s ≤ P.φ from hs.2),
      fun s hs => (show P.φ ≤ s ∧ s ≤ P.θ from hs)⟩
  rcases lt_trichotomy t P.θ with h₂ | h₂ | h₂
  · exact ⟨P.φ, P.θ, 1, 1, h, h₂, fun s hs => (show P.φ ≤ s ∧ s ≤ P.θ from ⟨hs.1, by
      linarith [hs.2]⟩), fun s hs => (show P.φ ≤ s ∧ s ≤ P.θ from ⟨by linarith [hs.1], hs.2⟩)⟩
  · subst h₂
    exact ⟨P.φ, π / 2 - P.θ, 1, 2, h, o2, fun s hs => (show P.φ ≤ s ∧ s ≤ P.θ from hs),
      fun s hs => (show P.θ ≤ s ∧ s ≤ π / 2 - P.θ from hs)⟩
  rcases lt_trichotomy t (π / 2 - P.θ) with h₃ | h₃ | h₃
  · exact ⟨P.θ, π / 2 - P.θ, 2, 2, h₂, h₃, fun s hs => (show P.θ ≤ s ∧ s ≤ π / 2 - P.θ from
      ⟨hs.1, by linarith [hs.2]⟩), fun s hs => (show P.θ ≤ s ∧ s ≤ π / 2 - P.θ from
      ⟨by linarith [hs.1], hs.2⟩)⟩
  · rw [h₃]
    exact ⟨P.θ, π / 2 - P.φ, 2, 3, o2, o3, fun s hs => (show P.θ ≤ s ∧ s ≤ π / 2 - P.θ from hs),
      fun s hs => (show π / 2 - P.θ ≤ s ∧ s ≤ π / 2 - P.φ from hs)⟩
  rcases lt_trichotomy t (π / 2 - P.φ) with h₄ | h₄ | h₄
  · exact ⟨π / 2 - P.θ, π / 2 - P.φ, 3, 3, h₃, h₄,
      fun s hs => (show π / 2 - P.θ ≤ s ∧ s ≤ π / 2 - P.φ from ⟨hs.1, by linarith [hs.2]⟩),
      fun s hs => (show π / 2 - P.θ ≤ s ∧ s ≤ π / 2 - P.φ from ⟨by linarith [hs.1], hs.2⟩)⟩
  · rw [h₄]
    exact ⟨π / 2 - P.θ, π / 2 - P.φ + 1, 3, 4, o3, by linarith,
      fun s hs => (show π / 2 - P.θ ≤ s ∧ s ≤ π / 2 - P.φ from hs),
      fun s hs => (show π / 2 - P.φ ≤ s from hs.1)⟩
  · exact ⟨π / 2 - P.φ, t + 1, 4, 4, h₄, by linarith,
      fun s hs => (show π / 2 - P.φ ≤ s from hs.1),
      fun s hs => (show π / 2 - P.φ ≤ s by linarith [hs.1])⟩

lemma gs_hasDerivAt_pw [NormedAddCommGroup E] [NormedSpace ℝ E] {g₁ g₂ g₃ g₄ g₅ : ℝ → E}
    (hO : gs_Ord P) (hm : gs_Match P f₁ f₂ f₃ f₄ f₅) (hm' : gs_Match P g₁ g₂ g₃ g₄ g₅)
    (hd : ∀ i t, HasDerivAt (gs_sel f₁ f₂ f₃ f₄ f₅ i) (gs_sel g₁ g₂ g₃ g₄ g₅ i t) t) (t : ℝ) :
    HasDerivAt (gs_pw P f₁ f₂ f₃ f₄ f₅) (gs_pw P g₁ g₂ g₃ g₄ g₅ t) t := by
  obtain ⟨a, b, i, j, ha, hb, hi, hj⟩ := gs_local hO t
  refine gs_hasDerivAt_glue ha hb (fun s hs => gs_pw_eq_sel hO hm (hi s hs))
    (fun s hs => gs_pw_eq_sel hO hm (hj s hs)) ?_ ?_
  · rw [gs_pw_eq_sel hO hm' (hi t ⟨ha.le, le_rfl⟩)]; exact hd i t
  · rw [gs_pw_eq_sel hO hm' (hj t ⟨le_rfl, hb.le⟩)]; exact hd j t

lemma gs_continuous_pw [TopologicalSpace E] (hO : gs_Ord P) (hm : gs_Match P f₁ f₂ f₃ f₄ f₅)
    (hc : ∀ i, Continuous (gs_sel f₁ f₂ f₃ f₄ f₅ i)) : Continuous (gs_pw P f₁ f₂ f₃ f₄ f₅) := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  obtain ⟨a, b, i, j, ha, hb, hi, hj⟩ := gs_local hO t
  exact gs_continuousAt_glue ha hb (fun s hs => gs_pw_eq_sel hO hm (hi s hs))
    (fun s hs => gs_pw_eq_sel hO hm (hj s hs)) (hc i).continuousAt (hc j).continuousAt

end pw

end MovingSofa


namespace MovingSofa

namespace GerverParams

variable (P : GerverParams)

/-! ### The five phases in the rotating frame -/

/-- Phase 1, Romik's (SOL1). -/
noncomputable def gs_ph1 : gs_Phase where
  w₁ t := P.a₁ * cos t + P.a₂ * sin t - 1
  w₂ t := -P.a₂ * cos t + P.a₁ * sin t - 1 / 2
  w₁' t := -P.a₁ * sin t + P.a₂ * cos t
  w₂' t := P.a₂ * sin t + P.a₁ * cos t
  w₁'' t := -P.a₁ * cos t - P.a₂ * sin t
  w₂'' t := P.a₂ * cos t - P.a₁ * sin t
  κ := P.κ₁

/-- Phase 2, Romik's (SOL2). -/
noncomputable def gs_ph2 : gs_Phase where
  w₁ t := -t ^ 2 / 4 + P.b₁ * t + P.b₂
  w₂ t := t / 2 - P.b₁ - 1
  w₁' t := -t / 2 + P.b₁
  w₂' _ := 1 / 2
  w₁'' _ := -1 / 2
  w₂'' _ := 0
  κ := P.κ₂

/-- Phase 3, Romik's (SOL3). -/
noncomputable def gs_ph3 : gs_Phase where
  w₁ t := P.c₁ - t
  w₂ t := P.c₂ + t
  w₁' _ := -1
  w₂' _ := 1
  w₁'' _ := 0
  w₂'' _ := 0
  κ := P.κ₃

/-- Phase 4, Romik's (SOL4). -/
noncomputable def gs_ph4 : gs_Phase where
  w₁ t := -t / 2 + P.d₁ - 1
  w₂ t := -t ^ 2 / 4 + P.d₁ * t + P.d₂
  w₁' _ := -1 / 2
  w₂' t := -t / 2 + P.d₁
  w₁'' _ := 0
  w₂'' _ := -1 / 2
  κ := P.κ₄

/-- Phase 5, Romik's (SOL5). -/
noncomputable def gs_ph5 : gs_Phase where
  w₁ t := P.e₁ * cos t + P.e₂ * sin t - 1 / 2
  w₂ t := -P.e₂ * cos t + P.e₁ * sin t - 1
  w₁' t := -P.e₁ * sin t + P.e₂ * cos t
  w₂' t := P.e₂ * sin t + P.e₁ * cos t
  w₁'' t := -P.e₁ * cos t - P.e₂ * sin t
  w₂'' t := P.e₂ * cos t - P.e₁ * sin t
  κ := P.κ₅

lemma gs_x₁_eq : P.x₁ = P.gs_ph1.X := rfl
lemma gs_x₂_eq : P.x₂ = P.gs_ph2.X := rfl
lemma gs_x₃_eq : P.x₃ = P.gs_ph3.X := rfl
lemma gs_x₄_eq : P.x₄ = P.gs_ph4.X := rfl
lemma gs_x₅_eq : P.x₅ = P.gs_ph5.X := rfl

lemma gs_hasDerivAt_trig {f : ℝ → ℝ} {t d : ℝ} (p q r : ℝ)
    (hf : ∀ s, f s = p * cos s + q * sin s + r) (hd : d = -p * sin t + q * cos t) :
    HasDerivAt f d t := by
  have := (((hasDerivAt_cos t).const_mul p).add ((hasDerivAt_sin t).const_mul q)).add_const r
  rw [show f = fun s => p * cos s + q * sin s + r from funext hf, hd]
  exact this.congr_deriv (by ring)

lemma gs_hasDerivAt_quad {f : ℝ → ℝ} {t d : ℝ} (p q r : ℝ)
    (hf : ∀ s, f s = p * s ^ 2 + q * s + r) (hd : d = 2 * p * t + q) :
    HasDerivAt f d t := by
  have := (((hasDerivAt_pow 2 t).const_mul p).add ((hasDerivAt_id t).const_mul q)).add_const r
  rw [show f = fun s => p * s ^ 2 + q * s + r from funext hf, hd]
  exact this.congr_deriv (by simp; ring)

lemma gs_valid₁ : P.gs_ph1.Valid where
  d₁ _ := gs_hasDerivAt_trig P.a₁ P.a₂ (-1) (fun s => by simp only [gs_ph1]; ring)
    (by simp only [gs_ph1])
  d₂ _ := gs_hasDerivAt_trig (-P.a₂) P.a₁ (-1 / 2) (fun s => by simp only [gs_ph1]; ring)
    (by simp only [gs_ph1]; ring)
  dd₁ _ := gs_hasDerivAt_trig P.a₂ (-P.a₁) 0 (fun s => by simp only [gs_ph1]; ring)
    (by simp only [gs_ph1]; ring)
  dd₂ _ := gs_hasDerivAt_trig P.a₁ P.a₂ 0 (fun s => by simp only [gs_ph1]; ring)
    (by simp only [gs_ph1]; ring)

lemma gs_valid₂ : P.gs_ph2.Valid where
  d₁ _ := gs_hasDerivAt_quad (-1 / 4) P.b₁ P.b₂ (fun s => by simp only [gs_ph2]; ring)
    (by simp only [gs_ph2]; ring)
  d₂ _ := gs_hasDerivAt_quad 0 (1 / 2) (-P.b₁ - 1) (fun s => by simp only [gs_ph2]; ring)
    (by simp only [gs_ph2]; ring)
  dd₁ _ := gs_hasDerivAt_quad 0 (-1 / 2) P.b₁ (fun s => by simp only [gs_ph2]; ring)
    (by simp only [gs_ph2]; ring)
  dd₂ _ := gs_hasDerivAt_quad 0 0 (1 / 2) (fun s => by simp only [gs_ph2]; ring)
    (by simp only [gs_ph2]; ring)

lemma gs_valid₃ : P.gs_ph3.Valid where
  d₁ _ := gs_hasDerivAt_quad 0 (-1) P.c₁ (fun s => by simp only [gs_ph3]; ring)
    (by simp only [gs_ph3]; ring)
  d₂ _ := gs_hasDerivAt_quad 0 1 P.c₂ (fun s => by simp only [gs_ph3]; ring)
    (by simp only [gs_ph3]; ring)
  dd₁ _ := gs_hasDerivAt_quad 0 0 (-1) (fun s => by simp only [gs_ph3]; ring)
    (by simp only [gs_ph3]; ring)
  dd₂ _ := gs_hasDerivAt_quad 0 0 1 (fun s => by simp only [gs_ph3]; ring)
    (by simp only [gs_ph3]; ring)

lemma gs_valid₄ : P.gs_ph4.Valid where
  d₁ _ := gs_hasDerivAt_quad 0 (-1 / 2) (P.d₁ - 1) (fun s => by simp only [gs_ph4]; ring)
    (by simp only [gs_ph4]; ring)
  d₂ _ := gs_hasDerivAt_quad (-1 / 4) P.d₁ P.d₂ (fun s => by simp only [gs_ph4]; ring)
    (by simp only [gs_ph4]; ring)
  dd₁ _ := gs_hasDerivAt_quad 0 0 (-1 / 2) (fun s => by simp only [gs_ph4]; ring)
    (by simp only [gs_ph4]; ring)
  dd₂ _ := gs_hasDerivAt_quad 0 (-1 / 2) P.d₁ (fun s => by simp only [gs_ph4]; ring)
    (by simp only [gs_ph4]; ring)

lemma gs_valid₅ : P.gs_ph5.Valid where
  d₁ _ := gs_hasDerivAt_trig P.e₁ P.e₂ (-1 / 2) (fun s => by simp only [gs_ph5]; ring)
    (by simp only [gs_ph5])
  d₂ _ := gs_hasDerivAt_trig (-P.e₂) P.e₁ (-1) (fun s => by simp only [gs_ph5]; ring)
    (by simp only [gs_ph5]; ring)
  dd₁ _ := gs_hasDerivAt_trig P.e₂ (-P.e₁) 0 (fun s => by simp only [gs_ph5]; ring)
    (by simp only [gs_ph5]; ring)
  dd₂ _ := gs_hasDerivAt_trig P.e₁ P.e₂ 0 (fun s => by simp only [gs_ph5]; ring)
    (by simp only [gs_ph5]; ring)

end GerverParams

end MovingSofa


namespace MovingSofa

namespace GerverParams

variable {P : GerverParams}

/-! ### The equations of `IsSolution` -/

lemma gs_ord (hP : P.IsSolution) : gs_Ord P := ⟨hP.1, hP.2.1, hP.2.2.1⟩

lemma gs_e₁ (hP : P.IsSolution) : P.e₁ = P.a₁ := hP.2.2.2.1
lemma gs_e₂ (hP : P.IsSolution) : P.e₂ = -P.a₂ := hP.2.2.2.2.1
lemma gs_d₁ (hP : P.IsSolution) : P.d₁ = π / 4 - P.b₁ := hP.2.2.2.2.2.1
lemma gs_d₂ (hP : P.IsSolution) : P.d₂ = P.b₂ + π / 4 * (2 * P.b₁ - π / 4) :=
  hP.2.2.2.2.2.2.1
lemma gs_c₂ (hP : P.IsSolution) : P.c₂ = P.c₁ - π / 2 := hP.2.2.2.2.2.2.2.1
lemma gs_κ₁₁ (hP : P.IsSolution) : P.κ₁.1 = 1 - P.a₁ := hP.2.2.2.2.2.2.2.2.1
lemma gs_κ₁₂ (hP : P.IsSolution) : P.κ₁.2 = 1 / 4 := hP.2.2.2.2.2.2.2.2.2.1
lemma gs_a₂ (hP : P.IsSolution) : P.a₂ = -1 / 4 := hP.2.2.2.2.2.2.2.2.2.2.1

lemma gs_matchX (hP : P.IsSolution) :
    gs_Match P P.gs_ph1.X P.gs_ph2.X P.gs_ph3.X P.gs_ph4.X P.gs_ph5.X := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h1, -, h2, -, h3, -, h4, -, -, -⟩ := hP
  exact ⟨h1, h2, h3, h4⟩

lemma gs_matchX' (hP : P.IsSolution) :
    gs_Match P P.gs_ph1.X' P.gs_ph2.X' P.gs_ph3.X' P.gs_ph4.X' P.gs_ph5.X' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h1, -, h2, -, h3, -, h4, -, -⟩ := hP
  rw [gs_x₁_eq, gs_x₂_eq, gs_x₃_eq, gs_x₄_eq, gs_x₅_eq] at *
  rw [((gs_Phase.hasDerivAt_X P.gs_valid₁) _).deriv,
    ((gs_Phase.hasDerivAt_X P.gs_valid₂) _).deriv] at h1
  rw [((gs_Phase.hasDerivAt_X P.gs_valid₂) _).deriv,
    ((gs_Phase.hasDerivAt_X P.gs_valid₃) _).deriv] at h2
  rw [((gs_Phase.hasDerivAt_X P.gs_valid₃) _).deriv,
    ((gs_Phase.hasDerivAt_X P.gs_valid₄) _).deriv] at h3
  rw [((gs_Phase.hasDerivAt_X P.gs_valid₄) _).deriv,
    ((gs_Phase.hasDerivAt_X P.gs_valid₅) _).deriv] at h4
  exact ⟨h1, h2, h3, h4⟩

/-! ### The rotation path and its derivative -/

variable (P) in
/-- The phase of the rotation path at index `i`. -/
noncomputable def gs_phase (i : ℕ) : gs_Phase :=
  match i with
  | 0 => P.gs_ph1
  | 1 => P.gs_ph2
  | 2 => P.gs_ph3
  | 3 => P.gs_ph4
  | _ => P.gs_ph5

lemma gs_valid (i : ℕ) : (P.gs_phase i).Valid := by
  match i with
  | 0 => exact P.gs_valid₁
  | 1 => exact P.gs_valid₂
  | 2 => exact P.gs_valid₃
  | 3 => exact P.gs_valid₄
  | n + 4 => exact P.gs_valid₅

variable (P) in
/-- The derivative of the rotation path. -/
noncomputable def gs_pathD : ℝ → ℝ × ℝ :=
  gs_pw P P.gs_ph1.X' P.gs_ph2.X' P.gs_ph3.X' P.gs_ph4.X' P.gs_ph5.X'

lemma gs_path_eq : P.path = gs_pw P P.gs_ph1.X P.gs_ph2.X P.gs_ph3.X P.gs_ph4.X P.gs_ph5.X :=
  rfl

lemma gs_sel_X (i : ℕ) :
    gs_sel P.gs_ph1.X P.gs_ph2.X P.gs_ph3.X P.gs_ph4.X P.gs_ph5.X i = (P.gs_phase i).X := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | n + 4 => rfl

lemma gs_sel_X' (i : ℕ) :
    gs_sel P.gs_ph1.X' P.gs_ph2.X' P.gs_ph3.X' P.gs_ph4.X' P.gs_ph5.X' i = (P.gs_phase i).X' := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | n + 4 => rfl

lemma gs_path_eq_phase (hP : P.IsSolution) {i : ℕ} {t : ℝ} (h : gs_piece P i t) :
    P.path t = (P.gs_phase i).X t := by
  rw [gs_path_eq, gs_pw_eq_sel (gs_ord hP) (gs_matchX hP) h, gs_sel_X]

lemma gs_pathD_eq_phase (hP : P.IsSolution) {i : ℕ} {t : ℝ} (h : gs_piece P i t) :
    P.gs_pathD t = (P.gs_phase i).X' t := by
  rw [gs_pathD, gs_pw_eq_sel (gs_ord hP) (gs_matchX' hP) h, gs_sel_X']

lemma gs_hasDerivAt_path (hP : P.IsSolution) (t : ℝ) : HasDerivAt P.path (P.gs_pathD t) t := by
  rw [gs_path_eq]
  refine gs_hasDerivAt_pw (gs_ord hP) (gs_matchX hP) (gs_matchX' hP) (fun i s => ?_) t
  rw [gs_sel_X, gs_sel_X']
  exact gs_Phase.hasDerivAt_X (gs_valid (P := P) i) s

lemma gs_deriv_path (hP : P.IsSolution) (t : ℝ) : deriv P.path t = P.gs_pathD t :=
  (gs_hasDerivAt_path hP t).deriv

lemma gs_deriv_path_eq (hP : P.IsSolution) {i : ℕ} {t : ℝ} (h : gs_piece P i t) :
    deriv P.path t = (P.gs_phase i).α t • uvec t + (P.gs_phase i).β t • vvec t := by
  rw [gs_deriv_path hP, gs_pathD_eq_phase hP h]; rfl

lemma gs_dot_smul_vvec_vvec (c t : ℝ) : dot (c • vvec t) (vvec t) = c := by
  rw [dot_smul_left, dot_vvec_self, mul_one]

lemma gs_dot_smul_uvec_uvec (c t : ℝ) : dot (c • uvec t) (uvec t) = c := by
  rw [dot_smul_left, dot_uvec_self, mul_one]

end GerverParams

end MovingSofa


namespace MovingSofa

namespace gs_Phase

variable {Φ : gs_Phase}

lemma continuous_X' (hΦ : Φ.Valid) : Continuous Φ.X' := by
  have h₁ : Continuous Φ.w₁ := continuous_iff_continuousAt.2 fun t => (hΦ.d₁ t).continuousAt
  have h₂ : Continuous Φ.w₂ := continuous_iff_continuousAt.2 fun t => (hΦ.d₂ t).continuousAt
  have h₁' : Continuous Φ.w₁' := continuous_iff_continuousAt.2 fun t => (hΦ.dd₁ t).continuousAt
  have h₂' : Continuous Φ.w₂' := continuous_iff_continuousAt.2 fun t => (hΦ.dd₂ t).continuousAt
  have hu : Continuous uvec := continuous_cos.prodMk continuous_sin
  have hv : Continuous vvec := continuous_sin.neg.prodMk continuous_cos
  exact ((h₁'.sub h₂).smul hu).add ((h₂'.add h₁).smul hv)

end gs_Phase

namespace GerverParams

variable {P : GerverParams}

lemma gs_continuous_pathD (hP : P.IsSolution) : Continuous P.gs_pathD := by
  refine gs_continuous_pw (gs_ord hP) (gs_matchX' hP) fun i => ?_
  rw [gs_sel_X']
  exact gs_Phase.continuous_X' (gs_valid i)

lemma gs_continuous_path (hP : P.IsSolution) : Continuous P.path :=
  continuous_iff_continuousAt.2 fun t => (gs_hasDerivAt_path hP t).continuousAt

lemma gs_contDiff_path (hP : P.IsSolution) : ContDiff ℝ 1 P.path := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (gs_hasDerivAt_path hP t).differentiableAt, ?_⟩
  have : deriv P.path = P.gs_pathD := funext (gs_deriv_path hP)
  rw [this]
  exact gs_continuous_pathD hP

/-- `α(t) = ⟨𝐱'(t), u_t⟩`. -/
noncomputable def gs_α (t : ℝ) : ℝ := dot (deriv P.path t) (uvec t)
/-- `β(t) = ⟨𝐱'(t), v_t⟩`. -/
noncomputable def gs_β (t : ℝ) : ℝ := dot (deriv P.path t) (vvec t)

lemma gs_α_eq (hP : P.IsSolution) {i : ℕ} {t : ℝ} (h : gs_piece P i t) :
    P.gs_α t = (P.gs_phase i).α t := by
  rw [gs_α, gs_deriv_path hP, gs_pathD_eq_phase hP h, gs_Phase.dot_X'_uvec]

lemma gs_β_eq (hP : P.IsSolution) {i : ℕ} {t : ℝ} (h : gs_piece P i t) :
    P.gs_β t = (P.gs_phase i).β t := by
  rw [gs_β, gs_deriv_path hP, gs_pathD_eq_phase hP h, gs_Phase.dot_X'_vvec]

lemma gs_continuous_α (hP : P.IsSolution) : Continuous P.gs_α := by
  have : P.gs_α = fun t => dot (P.gs_pathD t) (uvec t) := funext fun t => by
    rw [gs_α, gs_deriv_path hP]
  rw [this]
  have := gs_continuous_pathD hP
  simp only [dot, uvec]
  fun_prop

lemma gs_continuous_β (hP : P.IsSolution) : Continuous P.gs_β := by
  have : P.gs_β = fun t => dot (P.gs_pathD t) (vvec t) := funext fun t => by
    rw [gs_β, gs_deriv_path hP]
  rw [this]
  have := gs_continuous_pathD hP
  simp only [dot, vvec]
  fun_prop

lemma gs_contactA_eq (hP : P.IsSolution) {i : ℕ} {t : ℝ} (h : gs_piece P i t) :
    contactA P.path t = (P.gs_phase i).A t := by
  rw [contactA, gs_deriv_path hP, gs_pathD_eq_phase hP h, gs_Phase.dot_X'_uvec,
    gs_path_eq_phase hP h, gs_Phase.A_eq]

lemma gs_contactB_eq (hP : P.IsSolution) {i : ℕ} {t : ℝ} (h : gs_piece P i t) :
    contactB P.path t = (P.gs_phase i).B t := by
  rw [contactB, gs_deriv_path hP, gs_pathD_eq_phase hP h, gs_Phase.dot_X'_uvec,
    gs_path_eq_phase hP h, gs_Phase.B_eq]

lemma gs_contactC_eq (hP : P.IsSolution) {i : ℕ} {t : ℝ} (h : gs_piece P i t) :
    contactC P.path t = (P.gs_phase i).C t := by
  rw [contactC, gs_deriv_path hP, gs_pathD_eq_phase hP h, gs_Phase.dot_X'_vvec,
    gs_path_eq_phase hP h, gs_Phase.C_eq]

lemma gs_contactD_eq (hP : P.IsSolution) {i : ℕ} {t : ℝ} (h : gs_piece P i t) :
    contactD P.path t = (P.gs_phase i).D t := by
  rw [contactD, gs_deriv_path hP, gs_pathD_eq_phase hP h, gs_Phase.dot_X'_vvec,
    gs_path_eq_phase hP h, gs_Phase.D_eq]

lemma gs_contactA_eq' (t : ℝ) :
    contactA P.path t = P.path t + P.gs_α t • vvec t + uvec t := rfl

lemma gs_contactB_eq' (t : ℝ) :
    contactB P.path t = P.path t + P.gs_α t • vvec t := rfl

lemma gs_contactC_eq' (t : ℝ) :
    contactC P.path t = P.path t - P.gs_β t • uvec t + vvec t := rfl

lemma gs_contactD_eq' (t : ℝ) :
    contactD P.path t = P.path t - P.gs_β t • uvec t := rfl

lemma gs_continuous_contactA (hP : P.IsSolution) : Continuous (contactA P.path) := by
  have h1 := gs_continuous_path hP
  have h2 := gs_continuous_α hP
  have hu : Continuous uvec := continuous_cos.prodMk continuous_sin
  have hv : Continuous vvec := continuous_sin.neg.prodMk continuous_cos
  exact (h1.add (h2.smul hv)).add hu

lemma gs_continuous_contactC (hP : P.IsSolution) : Continuous (contactC P.path) := by
  have h1 := gs_continuous_path hP
  have h2 := gs_continuous_β hP
  have hu : Continuous uvec := continuous_cos.prodMk continuous_sin
  have hv : Continuous vvec := continuous_sin.neg.prodMk continuous_cos
  exact (h1.sub (h2.smul hu)).add hv

/-! ### Open and half-open phase intervals -/

variable (P) in
/-- The open phase intervals. -/
def gs_opiece : ℕ → ℝ → Prop
  | 0, t => t < P.φ
  | 1, t => P.φ < t ∧ t < P.θ
  | 2, t => P.θ < t ∧ t < π / 2 - P.θ
  | 3, t => π / 2 - P.θ < t ∧ t < π / 2 - P.φ
  | _, t => π / 2 - P.φ < t

variable (P) in
/-- The half-open phase intervals `[t_{i-1}, t_i)`. -/
def gs_rpiece : ℕ → ℝ → Prop
  | 0, t => t < P.φ
  | 1, t => P.φ ≤ t ∧ t < P.θ
  | 2, t => P.θ ≤ t ∧ t < π / 2 - P.θ
  | 3, t => π / 2 - P.θ ≤ t ∧ t < π / 2 - P.φ
  | _, t => π / 2 - P.φ ≤ t

lemma gs_opiece_nhds {i : ℕ} {t : ℝ} (h : gs_opiece P i t) : ∀ᶠ s in 𝓝 t, gs_piece P i s := by
  match i, h with
  | 0, h => filter_upwards [Iio_mem_nhds h] with s hs using (show s ≤ P.φ from le_of_lt hs)
  | 1, h => filter_upwards [Ioo_mem_nhds h.1 h.2] with s hs using
      (show P.φ ≤ s ∧ s ≤ P.θ from ⟨hs.1.le, hs.2.le⟩)
  | 2, h => filter_upwards [Ioo_mem_nhds h.1 h.2] with s hs using
      (show P.θ ≤ s ∧ s ≤ π / 2 - P.θ from ⟨hs.1.le, hs.2.le⟩)
  | 3, h => filter_upwards [Ioo_mem_nhds h.1 h.2] with s hs using
      (show π / 2 - P.θ ≤ s ∧ s ≤ π / 2 - P.φ from ⟨hs.1.le, hs.2.le⟩)
  | n + 4, h => filter_upwards [Ioi_mem_nhds h] with s hs using
      (show π / 2 - P.φ ≤ s from le_of_lt hs)

lemma gs_rpiece_nhds {i : ℕ} {t : ℝ} (h : gs_rpiece P i t) :
    ∀ᶠ s in 𝓝[≥] t, gs_piece P i s := by
  match i, h with
  | 0, h => filter_upwards [Ico_mem_nhdsGE h] with s hs using (show s ≤ P.φ from hs.2.le)
  | 1, h => filter_upwards [Ico_mem_nhdsGE h.2] with s hs using
      (show P.φ ≤ s ∧ s ≤ P.θ from ⟨h.1.trans hs.1, hs.2.le⟩)
  | 2, h => filter_upwards [Ico_mem_nhdsGE h.2] with s hs using
      (show P.θ ≤ s ∧ s ≤ π / 2 - P.θ from ⟨h.1.trans hs.1, hs.2.le⟩)
  | 3, h => filter_upwards [Ico_mem_nhdsGE h.2] with s hs using
      (show π / 2 - P.θ ≤ s ∧ s ≤ π / 2 - P.φ from ⟨h.1.trans hs.1, hs.2.le⟩)
  | n + 4, h => filter_upwards [self_mem_nhdsWithin] with s hs using
      (show π / 2 - P.φ ≤ s from h.trans hs)

lemma gs_piece_of_opiece {i : ℕ} {t : ℝ} (h : gs_opiece P i t) : gs_piece P i t :=
  (gs_opiece_nhds h).self_of_nhds

lemma gs_piece_of_rpiece {i : ℕ} {t : ℝ} (h : gs_rpiece P i t) : gs_piece P i t := by
  match i, h with
  | 0, h => exact (show t ≤ P.φ from h.le)
  | 1, h => exact (show P.φ ≤ t ∧ t ≤ P.θ from ⟨h.1, h.2.le⟩)
  | 2, h => exact (show P.θ ≤ t ∧ t ≤ π / 2 - P.θ from ⟨h.1, h.2.le⟩)
  | 3, h => exact (show π / 2 - P.θ ≤ t ∧ t ≤ π / 2 - P.φ from ⟨h.1, h.2.le⟩)
  | n + 4, h => exact h

variable (P) in
/-- The index of the half-open phase interval containing `t`. -/
noncomputable def gs_ridx (t : ℝ) : ℕ :=
  if t < P.φ then 0 else if t < P.θ then 1 else if t < π / 2 - P.θ then 2
  else if t < π / 2 - P.φ then 3 else 4

lemma gs_rpiece_ridx (t : ℝ) : gs_rpiece P (P.gs_ridx t) t := by
  unfold gs_ridx
  split_ifs with h1 h2 h3 h4
  · exact h1
  · exact ⟨not_lt.1 h1, h2⟩
  · exact ⟨not_lt.1 h2, h3⟩
  · exact ⟨not_lt.1 h3, h4⟩
  · exact not_lt.1 h4

/-! ### Derivatives of the contact curves -/

lemma gs_hasDerivAt_contactA (hP : P.IsSolution) {i : ℕ} {t : ℝ} (h : gs_opiece P i t) :
    HasDerivAt (contactA P.path) ((P.gs_phase i).ρA t • vvec t) t :=
  (gs_Phase.hasDerivAt_A (gs_valid i) t).congr_of_eventuallyEq
    ((gs_opiece_nhds h).mono fun _ hs => gs_contactA_eq hP hs)

lemma gs_hasDerivAt_contactB (hP : P.IsSolution) {i : ℕ} {t : ℝ} (h : gs_opiece P i t) :
    HasDerivAt (contactB P.path) (((P.gs_phase i).ρA t - 1) • vvec t) t :=
  (gs_Phase.hasDerivAt_B (gs_valid i) t).congr_of_eventuallyEq
    ((gs_opiece_nhds h).mono fun _ hs => gs_contactB_eq hP hs)

lemma gs_hasDerivAt_contactC (hP : P.IsSolution) {i : ℕ} {t : ℝ} (h : gs_opiece P i t) :
    HasDerivAt (contactC P.path) (-(P.gs_phase i).ρC t • uvec t) t :=
  (gs_Phase.hasDerivAt_C (gs_valid i) t).congr_of_eventuallyEq
    ((gs_opiece_nhds h).mono fun _ hs => gs_contactC_eq hP hs)

lemma gs_hasDerivAt_contactD (hP : P.IsSolution) {i : ℕ} {t : ℝ} (h : gs_opiece P i t) :
    HasDerivAt (contactD P.path) ((1 - (P.gs_phase i).ρC t) • uvec t) t :=
  (gs_Phase.hasDerivAt_D (gs_valid i) t).congr_of_eventuallyEq
    ((gs_opiece_nhds h).mono fun _ hs => gs_contactD_eq hP hs)

lemma gs_hasDerivWithinAt_contactA (hP : P.IsSolution) {i : ℕ} {t : ℝ} (h : gs_rpiece P i t) :
    HasDerivWithinAt (contactA P.path) ((P.gs_phase i).ρA t • vvec t) (Ici t) t :=
  (gs_Phase.hasDerivAt_A (gs_valid i) t).hasDerivWithinAt.congr_of_eventuallyEq
    ((gs_rpiece_nhds h).mono fun _ hs => gs_contactA_eq hP hs)
    (gs_contactA_eq hP (gs_piece_of_rpiece h))

lemma gs_hasDerivWithinAt_contactC (hP : P.IsSolution) {i : ℕ} {t : ℝ} (h : gs_rpiece P i t) :
    HasDerivWithinAt (contactC P.path) (-(P.gs_phase i).ρC t • uvec t) (Ici t) t :=
  (gs_Phase.hasDerivAt_C (gs_valid i) t).hasDerivWithinAt.congr_of_eventuallyEq
    ((gs_rpiece_nhds h).mono fun _ hs => gs_contactC_eq hP hs)
    (gs_contactC_eq hP (gs_piece_of_rpiece h))

end GerverParams

end MovingSofa


namespace MovingSofa

namespace GerverParams

variable {P : GerverParams}

/-! ### Elementary inequalities from the enclosures -/

lemma gs_φ_lo (hB : P.Bounds) : 0.039177264 ≤ P.φ := hB.φ_mem.1
lemma gs_φ_hi (hB : P.Bounds) : P.φ ≤ 0.039177465 := hB.φ_mem.2
lemma gs_θ_lo (hB : P.Bounds) : 0.681301409 ≤ P.θ := hB.θ_mem.1
lemma gs_θ_hi (hB : P.Bounds) : P.θ ≤ 0.68130161 := hB.θ_mem.2
lemma gs_a₁_lo (hB : P.Bounds) : 1.210322322 ≤ P.a₁ := hB.a₁_mem.1
lemma gs_a₁_hi (hB : P.Bounds) : P.a₁ ≤ 1.210322523 := hB.a₁_mem.2
lemma gs_b₁_lo (hB : P.Bounds) : -0.527624699 ≤ P.b₁ := hB.b₁_mem.1
lemma gs_b₁_hi (hB : P.Bounds) : P.b₁ ≤ -0.527624498 := hB.b₁_mem.2
lemma gs_b₂_lo (hB : P.Bounds) : 0.920258285 ≤ P.b₂ := hB.b₂_mem.1
lemma gs_b₂_hi (hB : P.Bounds) : P.b₂ ≤ 0.920258486 := hB.b₂_mem.2
lemma gs_c₁_lo (hB : P.Bounds) : 0.626045422 ≤ P.c₁ := hB.c₁_mem.1
lemma gs_c₁_hi (hB : P.Bounds) : P.c₁ ≤ 0.626045623 := hB.c₁_mem.2

/-- `α₁ < 0` on `(0, φ]` (base inequality, phase 1). -/
lemma gs_ineq_α₁ (hB : P.Bounds) {s : ℝ} (hs0 : 0 < s) (hs : s ≤ P.φ) :
    (1 - cos s) / 2 - 2 * P.a₁ * sin s < 0 := by
  have h1 := one_sub_sq_div_two_le_cos (x := s)
  have h2 := sin_gt_sub_cube hs0
  have := gs_φ_hi hB
  have := gs_a₁_lo hB
  have hs1 : s ≤ 0.04 := by linarith
  have h3 : 0 < s - s ^ 3 / 6 := by nlinarith
  have h4 : 2 * P.a₁ * (s - s ^ 3 / 6) < 2 * P.a₁ * sin s := by
    apply mul_lt_mul_of_pos_left h2; linarith
  nlinarith

/-- `β₁ > 0` on `[0, φ]` (base inequality, phase 1). -/
lemma gs_ineq_β₁ (hB : P.Bounds) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ P.φ) :
    0 < 2 * P.a₁ * cos s - sin s / 2 - 1 := by
  have h1 := one_sub_sq_div_two_le_cos (x := s)
  have h2 := sin_le hs0
  have := gs_φ_hi hB
  have := gs_a₁_lo hB
  have hs1 : s ≤ 0.04 := by linarith
  have h3 : 2 * P.a₁ * (1 - s ^ 2 / 2) ≤ 2 * P.a₁ * cos s := by
    apply mul_le_mul_of_nonneg_left h1; linarith
  have h4 : 0.999 ≤ 1 - s ^ 2 / 2 := by nlinarith
  have h5 : 2 * P.a₁ * 0.999 ≤ 2 * P.a₁ * (1 - s ^ 2 / 2) := by
    apply mul_le_mul_of_nonneg_left h4; linarith
  linarith

/-- `α₂ < 0` on `[φ, θ]` (base inequality, phase 2). -/
lemma gs_ineq_α₂ (hB : P.Bounds) {s : ℝ} (hs0 : 0 ≤ s) : 2 * P.b₁ + 1 - s < 0 := by
  have := gs_b₁_hi hB
  linarith

/-- `β₂ > 0` on `[0, θ]` (base inequality, phase 2). -/
lemma gs_ineq_β₂ (hB : P.Bounds) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ P.θ) :
    0 < 1 / 2 - s ^ 2 / 4 + P.b₁ * s + P.b₂ := by
  have := gs_θ_hi hB
  have := gs_b₁_lo hB
  have := gs_b₂_lo hB
  have hs1 : s ≤ 0.69 := by linarith
  nlinarith

/-- `0 < ρ_C < 1` on `[0, θ]` (base inequality, phase 2). -/
lemma gs_ineq_ρC₂ (hB : P.Bounds) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ P.θ) :
    0 < s / 2 - P.b₁ ∧ s / 2 - P.b₁ < 1 := by
  have := gs_θ_hi hB
  have := gs_b₁_lo hB
  have := gs_b₁_hi hB
  constructor <;> linarith

/-- The signs on phase 3. -/
lemma gs_ineq₃ (hB : P.Bounds) {t : ℝ} (ht₁ : P.θ ≤ t) (ht₂ : t ≤ π / 2 - P.θ) :
    π / 2 - 1 - P.c₁ - t < 0 ∧ 0 < 1 + P.c₁ - t := by
  have := gs_θ_lo hB
  have := gs_c₁_lo hB
  have := pi_lt_d2
  constructor <;> linarith

/-- The height of the rotation path on phase 2, without the translation. -/
lemma gs_ineq_y₂ (hB : P.Bounds) (hP : P.IsSolution) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ P.θ) :
    sin s * (-s ^ 2 / 4 + P.b₁ * s + P.b₂) + cos s * (s / 2 - P.b₁ - 1) ≤ 0.52 := by
  have := gs_θ_hi hB
  have := gs_b₁_lo hB
  have := gs_b₁_hi hB
  have := gs_b₂_lo hB
  have := gs_b₂_hi hB
  have hs1 : s ≤ 0.69 := by linarith
  have hθ := (gs_ord hP).2.2
  have hcos : 0 ≤ cos s := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith⟩
  have hsin := sin_le hs0
  have hsin0 : 0 ≤ sin s := sin_nonneg_of_nonneg_of_le_pi hs0 (by linarith [pi_gt_three])
  have hw₁ : 0 ≤ -s ^ 2 / 4 + P.b₁ * s + P.b₂ := by nlinarith
  have hw₂ : s / 2 - P.b₁ - 1 ≤ 0 := by linarith
  have h1 : sin s * (-s ^ 2 / 4 + P.b₁ * s + P.b₂) ≤ s * (-s ^ 2 / 4 + P.b₁ * s + P.b₂) :=
    mul_le_mul_of_nonneg_right hsin hw₁
  have h2 : cos s * (s / 2 - P.b₁ - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hcos hw₂
  nlinarith [sq_nonneg (s - 0.87)]

/-- The height of the rotation path on phase 1, without the translation. -/
lemma gs_ineq_y₁ (hB : P.Bounds) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ P.φ) :
    sin s * (P.a₁ * cos s - sin s / 4 - 1) + cos s * (cos s / 4 + P.a₁ * sin s - 1 / 2) ≤ 0.7 := by
  have := gs_φ_hi hB
  have := gs_a₁_lo hB
  have := gs_a₁_hi hB
  have hs1 : s ≤ 0.04 := by linarith
  have hcos : 0 ≤ cos s := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith [pi_gt_three]⟩
  have hcos1 := cos_le_one s
  have hsin := sin_le hs0
  have hsin0 : 0 ≤ sin s := sin_nonneg_of_nonneg_of_le_pi hs0 (by linarith [pi_gt_three])
  have h1 : cos s / 4 + P.a₁ * sin s - 1 / 2 ≤ 0 := by nlinarith
  have h2 : cos s * (cos s / 4 + P.a₁ * sin s - 1 / 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hcos h1
  have h3 : sin s * (P.a₁ * cos s - sin s / 4 - 1) ≤ sin s * (P.a₁ - 1) := by
    apply mul_le_mul_of_nonneg_left _ hsin0; nlinarith
  nlinarith

/-- The height of the rotation path on phase 3, without the translation. -/
lemma gs_ineq_y₃ (hB : P.Bounds) (hP : P.IsSolution) {t : ℝ} (ht₁ : P.θ ≤ t)
    (ht₂ : t ≤ π / 2 - P.θ) : sin t * (P.c₁ - t) + cos t * (P.c₂ + t) ≤ 0 := by
  have := gs_θ_lo hB
  have := gs_c₁_hi hB
  have hc₂ := gs_c₂ hP
  have hθ := (gs_ord hP).2.2
  have hcos : 0 ≤ cos t := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith⟩
  have hsin0 : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos])
  have h1 : sin t * (P.c₁ - t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hsin0 (by linarith)
  have h2 : cos t * (P.c₂ + t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hcos (by linarith)
  linarith

end GerverParams

end MovingSofa


namespace MovingSofa

namespace GerverParams

variable {P : GerverParams}

lemma gs_cases (t : ℝ) : t ≤ P.φ ∨ (P.φ < t ∧ t ≤ P.θ) ∨ (P.θ < t ∧ t ≤ π / 2 - P.θ) ∨
    (π / 2 - P.θ < t ∧ t ≤ π / 2 - P.φ) ∨ π / 2 - P.φ < t := by
  rcases le_or_gt t P.φ with h1 | h1
  · exact Or.inl h1
  rcases le_or_gt t P.θ with h2 | h2
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  rcases le_or_gt t (π / 2 - P.θ) with h3 | h3
  · exact Or.inr (Or.inr (Or.inl ⟨h2, h3⟩))
  rcases le_or_gt t (π / 2 - P.φ) with h4 | h4
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, h4⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h4)))

lemma gs_α₁_eq (hP : P.IsSolution) (t : ℝ) :
    (P.gs_phase 0).α t = (1 - cos t) / 2 - 2 * P.a₁ * sin t := by
  simp only [gs_phase, gs_Phase.α, gs_ph1, gs_a₂ hP]; ring

lemma gs_β₁_eq (hP : P.IsSolution) (t : ℝ) :
    (P.gs_phase 0).β t = 2 * P.a₁ * cos t - sin t / 2 - 1 := by
  simp only [gs_phase, gs_Phase.β, gs_ph1, gs_a₂ hP]; ring

lemma gs_α₂_eq (t : ℝ) : (P.gs_phase 1).α t = 2 * P.b₁ + 1 - t := by
  simp only [gs_phase, gs_Phase.α, gs_ph2]; ring

lemma gs_β₂_eq (t : ℝ) : (P.gs_phase 1).β t = 1 / 2 - t ^ 2 / 4 + P.b₁ * t + P.b₂ := by
  simp only [gs_phase, gs_Phase.β, gs_ph2]; ring

lemma gs_α₃_eq (hP : P.IsSolution) (t : ℝ) : (P.gs_phase 2).α t = π / 2 - 1 - P.c₁ - t := by
  simp only [gs_phase, gs_Phase.α, gs_ph3, gs_c₂ hP]; ring

lemma gs_β₃_eq (t : ℝ) : (P.gs_phase 2).β t = 1 + P.c₁ - t := by
  simp only [gs_phase, gs_Phase.β, gs_ph3]; ring

/-- On phase 4, `α(π/2 - s) = -β₂(s)`. -/
lemma gs_α₄_eq (hP : P.IsSolution) (s : ℝ) :
    (P.gs_phase 3).α (π / 2 - s) = -(1 / 2 - s ^ 2 / 4 + P.b₁ * s + P.b₂) := by
  simp only [gs_phase, gs_Phase.α, gs_ph4, gs_d₁ hP, gs_d₂ hP]; ring

/-- On phase 4, `β(π/2 - s) = -α₂(s)`. -/
lemma gs_β₄_eq (hP : P.IsSolution) (s : ℝ) :
    (P.gs_phase 3).β (π / 2 - s) = -(2 * P.b₁ + 1 - s) := by
  simp only [gs_phase, gs_Phase.β, gs_ph4, gs_d₁ hP]; ring

/-- On phase 5, `α(π/2 - s) = -β₁(s)`. -/
lemma gs_α₅_eq (hP : P.IsSolution) (s : ℝ) :
    (P.gs_phase 4).α (π / 2 - s) = -(2 * P.a₁ * cos s - sin s / 2 - 1) := by
  simp only [gs_phase, gs_Phase.α, gs_ph5, gs_e₁ hP, gs_e₂ hP, gs_a₂ hP, sin_pi_div_two_sub,
    cos_pi_div_two_sub]; ring

/-- On phase 5, `β(π/2 - s) = -α₁(s)`. -/
lemma gs_β₅_eq (hP : P.IsSolution) (s : ℝ) :
    (P.gs_phase 4).β (π / 2 - s) = -((1 - cos s) / 2 - 2 * P.a₁ * sin s) := by
  simp only [gs_phase, gs_Phase.β, gs_ph5, gs_e₁ hP, gs_e₂ hP, gs_a₂ hP, sin_pi_div_two_sub,
    cos_pi_div_two_sub]; ring

lemma gs_piece₀ {t : ℝ} (h : t ≤ P.φ) : gs_piece P 0 t := h
lemma gs_piece₁ {t : ℝ} (h₁ : P.φ ≤ t) (h₂ : t ≤ P.θ) : gs_piece P 1 t := ⟨h₁, h₂⟩
lemma gs_piece₂ {t : ℝ} (h₁ : P.θ ≤ t) (h₂ : t ≤ π / 2 - P.θ) : gs_piece P 2 t := ⟨h₁, h₂⟩
lemma gs_piece₃ {t : ℝ} (h₁ : π / 2 - P.θ ≤ t) (h₂ : t ≤ π / 2 - P.φ) : gs_piece P 3 t :=
  ⟨h₁, h₂⟩
lemma gs_piece₄ {t : ℝ} (h : π / 2 - P.φ ≤ t) : gs_piece P 4 t := h

/-- **Injectivity signs.** `α < 0` on `(0, π/2]`. -/
lemma gs_α_neg (hP : P.IsSolution) (hB : P.Bounds) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ π / 2) :
    P.gs_α t < 0 := by
  have hO := gs_ord hP
  rcases gs_cases (P := P) t with h | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | h
  · rw [gs_α_eq hP (gs_piece₀ h), gs_α₁_eq hP]; exact gs_ineq_α₁ hB h0 h
  · rw [gs_α_eq hP (gs_piece₁ ha.le hb), gs_α₂_eq]; exact gs_ineq_α₂ hB h0.le
  · rw [gs_α_eq hP (gs_piece₂ ha.le hb), gs_α₃_eq hP]; exact (gs_ineq₃ hB ha.le hb).1
  · rw [gs_α_eq hP (gs_piece₃ ha.le hb), show t = π / 2 - (π / 2 - t) by ring, gs_α₄_eq hP]
    have := gs_ineq_β₂ hB (s := π / 2 - t) (by linarith [hO.1]) (by linarith)
    linarith
  · rw [gs_α_eq hP (gs_piece₄ h.le), show t = π / 2 - (π / 2 - t) by ring, gs_α₅_eq hP]
    have := gs_ineq_β₁ hB (s := π / 2 - t) (by linarith) (by linarith)
    linarith

/-- **Injectivity signs.** `β > 0` on `[0, π/2)`. -/
lemma gs_β_pos (hP : P.IsSolution) (hB : P.Bounds) {t : ℝ} (h0 : 0 ≤ t) (h1 : t < π / 2) :
    0 < P.gs_β t := by
  have hO := gs_ord hP
  rcases gs_cases (P := P) t with h | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | h
  · rw [gs_β_eq hP (gs_piece₀ h), gs_β₁_eq hP]; exact gs_ineq_β₁ hB h0 h
  · rw [gs_β_eq hP (gs_piece₁ ha.le hb), gs_β₂_eq]; exact gs_ineq_β₂ hB h0 hb
  · rw [gs_β_eq hP (gs_piece₂ ha.le hb), gs_β₃_eq]; exact (gs_ineq₃ hB ha.le hb).2
  · rw [gs_β_eq hP (gs_piece₃ ha.le hb), show t = π / 2 - (π / 2 - t) by ring, gs_β₄_eq hP]
    have := gs_ineq_α₂ hB (s := π / 2 - t) (by linarith [hO.1])
    linarith
  · rw [gs_β_eq hP (gs_piece₄ h.le), show t = π / 2 - (π / 2 - t) by ring, gs_β₅_eq hP]
    have := gs_ineq_α₁ hB (s := π / 2 - t) (by linarith) (by linarith)
    linarith

lemma gs_α_zero (hP : P.IsSolution) : P.gs_α 0 = 0 := by
  rw [gs_α_eq hP (gs_piece₀ (gs_ord hP).1.le), gs_α₁_eq hP]; simp

lemma gs_β_pi_div_two (hP : P.IsSolution) : P.gs_β (π / 2) = 0 := by
  have hO := gs_ord hP
  rw [gs_β_eq hP (gs_piece₄ (by linarith [hO.1])), show π / 2 = π / 2 - 0 by ring,
    gs_β₅_eq hP]; simp

lemma gs_α_nonpos (hP : P.IsSolution) (hB : P.Bounds) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ π / 2) :
    P.gs_α t ≤ 0 := by
  rcases h0.lt_or_eq with h | rfl
  · exact (gs_α_neg hP hB h h1).le
  · rw [gs_α_zero hP]

lemma gs_β_nonneg (hP : P.IsSolution) (hB : P.Bounds) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ π / 2) :
    0 ≤ P.gs_β t := by
  rcases h1.lt_or_eq with h | rfl
  · exact (gs_β_pos hP hB h0 h).le
  · rw [gs_β_pi_div_two hP]

end GerverParams

end MovingSofa


namespace MovingSofa

namespace GerverParams

variable {P : GerverParams}

lemma gs_ρA₁_eq (t : ℝ) : (P.gs_phase 0).ρA t = 0 := by
  simp only [gs_phase, gs_Phase.ρA, gs_ph1]; ring
lemma gs_ρC₁_eq (t : ℝ) : (P.gs_phase 0).ρC t = 1 / 2 := by
  simp only [gs_phase, gs_Phase.ρC, gs_ph1]; ring
lemma gs_ρA₂_eq (t : ℝ) : (P.gs_phase 1).ρA t = 1 / 2 - t ^ 2 / 4 + P.b₁ * t + P.b₂ := by
  simp only [gs_phase, gs_Phase.ρA, gs_ph2]; ring
lemma gs_ρC₂_eq (t : ℝ) : (P.gs_phase 1).ρC t = t / 2 - P.b₁ := by
  simp only [gs_phase, gs_Phase.ρC, gs_ph2]; ring
lemma gs_ρA₃_eq (t : ℝ) : (P.gs_phase 2).ρA t = 1 + P.c₁ - t := by
  simp only [gs_phase, gs_Phase.ρA, gs_ph3]; ring
lemma gs_ρC₃_eq (hP : P.IsSolution) (t : ℝ) : (P.gs_phase 2).ρC t = -(π / 2 - 1 - P.c₁ - t) := by
  simp only [gs_phase, gs_Phase.ρC, gs_ph3, gs_c₂ hP]; ring
lemma gs_ρA₄_eq (hP : P.IsSolution) (s : ℝ) : (P.gs_phase 3).ρA (π / 2 - s) = s / 2 - P.b₁ := by
  simp only [gs_phase, gs_Phase.ρA, gs_ph4, gs_d₁ hP]; ring
lemma gs_ρC₄_eq (hP : P.IsSolution) (s : ℝ) :
    (P.gs_phase 3).ρC (π / 2 - s) = 1 / 2 - s ^ 2 / 4 + P.b₁ * s + P.b₂ := by
  simp only [gs_phase, gs_Phase.ρC, gs_ph4, gs_d₁ hP, gs_d₂ hP]; ring
lemma gs_ρA₅_eq (t : ℝ) : (P.gs_phase 4).ρA t = 1 / 2 := by
  simp only [gs_phase, gs_Phase.ρA, gs_ph5]; ring
lemma gs_ρC₅_eq (t : ℝ) : (P.gs_phase 4).ρC t = 0 := by
  simp only [gs_phase, gs_Phase.ρC, gs_ph5]; ring

/-- `ρ_A ≥ 0` and `ρ_C ≥ 0` on the half-open phase intervals inside `[0, π/2]`. -/
lemma gs_ρ_nonneg (hP : P.IsSolution) (hB : P.Bounds) {i : ℕ} {t : ℝ} (h : gs_rpiece P i t)
    (h0 : 0 ≤ t) (h1 : t ≤ π / 2) : 0 ≤ (P.gs_phase i).ρA t ∧ 0 ≤ (P.gs_phase i).ρC t := by
  have hO := gs_ord hP
  match i, h with
  | 0, _ => rw [gs_ρA₁_eq, gs_ρC₁_eq]; norm_num
  | 1, h =>
    rw [gs_ρA₂_eq, gs_ρC₂_eq]
    exact ⟨(gs_ineq_β₂ hB h0 h.2.le).le, (gs_ineq_ρC₂ hB h0 h.2.le).1.le⟩
  | 2, h =>
    have h2 : t ≤ π / 2 - P.θ := h.2.le
    rw [gs_ρA₃_eq, gs_ρC₃_eq hP]
    exact ⟨(gs_ineq₃ hB h.1 h2).2.le, by linarith [(gs_ineq₃ hB h.1 h2).1]⟩
  | 3, h =>
    rw [show t = π / 2 - (π / 2 - t) by ring, gs_ρA₄_eq hP, gs_ρC₄_eq hP]
    have h2 : π / 2 - t ≤ P.θ := by linarith [h.1]
    have h3 : 0 ≤ π / 2 - t := by linarith [h.2, hO.1]
    exact ⟨(gs_ineq_ρC₂ hB h3 h2).1.le, (gs_ineq_β₂ hB h3 h2).le⟩
  | n + 4, _ =>
    rw [show P.gs_phase (n + 4) = P.gs_phase 4 from rfl, gs_ρA₅_eq, gs_ρC₅_eq]; norm_num

end GerverParams

end MovingSofa


namespace MovingSofa

namespace gs_Phase

variable {Φ : gs_Phase}

lemma contactA_X (hΦ : Φ.Valid) (t : ℝ) : GerverParams.contactA Φ.X t = Φ.A t := by
  rw [GerverParams.contactA, (hasDerivAt_X hΦ t).deriv, dot_X'_uvec, A_eq]

lemma contactB_X (hΦ : Φ.Valid) (t : ℝ) : GerverParams.contactB Φ.X t = Φ.B t := by
  rw [GerverParams.contactB, (hasDerivAt_X hΦ t).deriv, dot_X'_uvec, B_eq]

lemma contactC_X (hΦ : Φ.Valid) (t : ℝ) : GerverParams.contactC Φ.X t = Φ.C t := by
  rw [GerverParams.contactC, (hasDerivAt_X hΦ t).deriv, dot_X'_vvec, C_eq]

lemma contactD_X (hΦ : Φ.Valid) (t : ℝ) : GerverParams.contactD Φ.X t = Φ.D t := by
  rw [GerverParams.contactD, (hasDerivAt_X hΦ t).deriv, dot_X'_vvec, D_eq]

end gs_Phase

namespace GerverParams

variable {P : GerverParams}

/-- `𝐱(0) = 0` (Romik's (34)). -/
lemma gs_path_zero (hP : P.IsSolution) : P.path 0 = 0 := by
  rw [gs_path_eq_phase hP (gs_piece₀ (gs_ord hP).1.le)]
  simp only [gs_phase, gs_Phase.X, gs_ph1, rot, cos_zero, sin_zero]
  ext
  · simp only [Prod.fst_add, Prod.fst_zero, gs_κ₁₁ hP]; ring
  · simp only [Prod.snd_add, Prod.snd_zero, gs_κ₁₂ hP, gs_a₂ hP]; ring

/-- `𝐱(π/2)` lies on the `x`-axis: `𝐱(π/2)_y = 0`. -/
lemma gs_path_pi_div_two_snd (hP : P.IsSolution) : (P.path (π / 2)).2 = 0 := by
  have hO := gs_ord hP
  rw [gs_path_eq_phase hP (gs_piece₄ (by linarith [hO.1]))]
  obtain ⟨-, -, -, he₁, he₂, hd₁, hd₂, hc₂, -, hκ, ha₂, h1, -, h2, -, h3, -, h4, -, -, -⟩ := hP
  have h1 := congrArg Prod.snd h1
  have h2 := congrArg Prod.snd h2
  have h3 := congrArg Prod.snd h3
  have h4 := congrArg Prod.snd h4
  simp only [x₁, x₂, x₃, x₄, x₅, rot, Prod.snd_add, sin_pi_div_two_sub, cos_pi_div_two_sub]
    at h1 h2 h3 h4
  simp only [gs_phase, gs_Phase.X, gs_ph5, rot, Prod.snd_add, sin_pi_div_two, cos_pi_div_two]
  rw [hd₁, hd₂] at h3 h4
  rw [he₁, he₂] at h4 ⊢
  rw [hc₂] at h2 h3
  rw [ha₂] at h1 h4 ⊢
  rw [hκ] at h1
  linear_combination -(h1 + h2 + h3 + h4)

/-- Romik's (43): `𝐁(t₃) = 𝐱(t₁)`. -/
lemma gs_contactB_t₃ (hP : P.IsSolution) : contactB P.path (π / 2 - P.θ) = P.path P.φ := by
  have hO := gs_ord hP
  have h43 : P.x₁ P.φ = contactB P.x₄ (π / 2 - P.θ) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [gs_contactB_eq hP (gs_piece₃ le_rfl hO.lt_φ'.le), gs_path_eq_phase hP (gs_piece₀ le_rfl),
    show P.gs_phase 0 = P.gs_ph1 from rfl, ← gs_x₁_eq, h43, gs_x₄_eq,
    gs_Phase.contactB_X P.gs_valid₄]
  rfl

/-- Romik's (44): `𝐃(t₂) = 𝐱(t₄)`. -/
lemma gs_contactD_t₂ (hP : P.IsSolution) : contactD P.path P.θ = P.path (π / 2 - P.φ) := by
  have hO := gs_ord hP
  have h44 : P.x₅ (π / 2 - P.φ) = contactD P.x₂ P.θ := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [gs_contactD_eq hP (gs_piece₁ hO.φ_lt_θ.le le_rfl), gs_path_eq_phase hP (gs_piece₄ le_rfl),
    show P.gs_phase 4 = P.gs_ph5 from rfl, ← gs_x₅_eq, h44, gs_x₂_eq,
    gs_Phase.contactD_X P.gs_valid₂]
  rfl

/-- `𝐁(t₅)` lies on the `x`-axis. -/
lemma gs_contactB_pi_div_two_snd (hP : P.IsSolution) : (contactB P.path (π / 2)).2 = 0 := by
  rw [gs_contactB_eq', Prod.snd_add, gs_path_pi_div_two_snd hP]
  simp [vvec]

/-- `𝐃(t₀)` lies on the `x`-axis. -/
lemma gs_contactD_zero_snd (hP : P.IsSolution) : (contactD P.path 0).2 = 0 := by
  rw [gs_contactD_eq', Prod.snd_sub, gs_path_zero hP]
  simp [uvec]

end GerverParams

end MovingSofa
