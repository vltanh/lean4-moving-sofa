module

public import MovingSofa.Basic.Plane
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# The niche of a rotation path is the region under an envelope

The paper (Theorem 8.4.1 (2)) uses without proof that the niche of the cap of Gerver's sofa is the
region enclosed by the curves `𝐃`, `𝐱|_{[t₁, t₄]}`, `𝐁` and the `x`-axis. This file proves the
geometric part of an abstract version of this statement (the area is computed in
`MovingSofa.Gerver.EnvelopeArea`); `notes/gerver_plan.md`, section "Niche structure", reduces the
statement for Gerver's sofa to it.

## Setting

`x : ℝ → ℝ²` is a rotation path on `[0, π/2]` with `x' = α u + β v`, and
`𝐁 = x + α v`, `𝐃 = x - β u` (`envB`, `envD`), with `𝐁' = (ρ_A - 1) v` and `𝐃' = (1 - ρ_C) u`
off the breakpoints `t₁ < t₂ < t₃ < t₄`. The quadrant at `s` is
`Q⁻(s) = {q : (q - x(s)) · u_s < 0, (q - x(s)) · v_s < 0}` (`envQuad`) and the niche is
`N = {q₂ ≥ 0} ∩ ⋃_{s ∈ (0, π/2)} Q⁻(s)` (`envNiche`). The hypotheses `EnvHyp` are the one-variable
facts that hold for Gerver's path (with `t₁ = φ`, `t₂ = θ`, `t₃ = π/2 - θ`, `t₄ = π/2 - φ`,
`s_A = 0.62`, `s_C = 0.95`). Let `Γ = 𝐁([t₃, π/2]) ∪ x([t₁, t₄]) ∪ 𝐃([0, t₂])` (`envCurve`).

## Main results

* `env_not_mem`: the points of `Γ` lie in no quadrant `Q⁻(s)`, `s ∈ (0, π/2)`; hence not in `N`
  (`env_not_mem_niche`);
* `env_mem_closure`: the points of `Γ` lie in the closure of `N`;
* `env_subset_niche`, `env_niche_subset_strict`, `env_niche_subset`, `env_niche_eq`: `N` is the set
  of points `q` with `q₂ ≥ 0` lying strictly below a point of `Γ` (`envUnderStrict`), and hence lies
  in the set of points lying on or below a point of `Γ` (`envUnder`).

## Proof

* *Principle P* (`env_not_mem_of_dot`): if `(p - x(s)) · u_σ ≥ 0` for some `σ ∈ [s, s + π/2]`, then
  `p ∉ Q⁻(s)`, because `u_σ = cos(σ - s) u_s + sin(σ - s) v_s` with nonnegative coefficients.
* *Envelope facts*: `f_s(𝐁(s)) = 0` and `g_s(𝐃(s)) = 0`, where `f_s(p) = (p - x(s)) · u_s` and
  `g_s(p) = (p - x(s)) · v_s`; `r ↦ f_s(𝐁(r))` has derivative `(ρ_A(r) - 1) sin(s - r)` and
  `r ↦ g_s(𝐃(r))` has derivative `(1 - ρ_C(r)) sin(r - s)` off the breakpoints, which gives their
  monotonicity (`env_phi_mono`, `env_phi_anti`, `env_psi_mono`, `env_psi_anti`; monotonicity from
  the sign of a derivative off a finite set is `env_monotoneOn` and its variants).
* `I(s) = (x(t₁) - x(s)) · u_s ≥ 0` on `[t₁, π/2)` and `J(s) = (x(t₄) - x(s)) · v_s ≥ 0` on
  `(0, t₄]` (`env_I_nonneg`, `env_J_nonneg`), from `I_nonneg`, `I'_nonneg` and the envelope facts.
* *Points `x(τ)`* (`env_wit_x`): for `τ ≤ s`, `F(τ') = f_s(x(τ'))` has `F' = α cos(s - τ') +
  β sin(s - τ')`, which stays negative once negative since `|α|/β` is nondecreasing
  (`env_sign_aux`), so `F(τ) ≥ min(F(t₁), F(s)) = min(I(s), 0) = 0` (`env_min_le`); the case
  `τ ≥ s` is the mirror image with `g_s` and `J`.
* *Points `𝐁(τ)`, `𝐃(τ)`* (`env_wit_B`, `env_wit_D`): the envelope facts for `s` near the curve,
  and the angles `σ = t₃` (with `corner_B`), resp. `σ = t₂ + π/2` (with `corner_D`), otherwise.
* *The region* (`env_niche_subset_strict`): a point `q` of `N` with `q₁` outside
  `[𝐃(0)₁, 𝐁(π/2)₁]` is excluded by the witness angle of `𝐁(π/2)` (in `[0, π/2]`) or of `𝐃(0)`
  (in `[π/2, π]`); otherwise some `γ ∈ Γ` has `γ₁ = q₁` by the intermediate value theorem, and
  `q₂ ≥ γ₂` is excluded by the witness angle of `γ` (in `[0, π]`). Conversely
  (`env_subset_niche`), `γ - b e₂ ∈ Q⁻(τ)` for `γ = x(τ), 𝐁(τ), 𝐃(τ)` and `b > 0`.
-/

@[expose] public section

open Real Set

namespace MovingSofa

/-- The open quadrant `Q⁻(s) = {q : (q - x(s)) · u_s < 0, (q - x(s)) · v_s < 0}` at the point
`x s`. -/
def envQuad (x : ℝ → ℝ × ℝ) (s : ℝ) : Set (ℝ × ℝ) :=
  {q | dot (q - x s) (uvec s) < 0 ∧ dot (q - x s) (vvec s) < 0}

/-- The niche of a rotation path: `{q₂ ≥ 0} ∩ ⋃_{s ∈ (0, π/2)} Q⁻(s)`. -/
def envNiche (x : ℝ → ℝ × ℝ) : Set (ℝ × ℝ) := {q | 0 ≤ q.2} ∩ ⋃ s ∈ Ioo 0 (π / 2), envQuad x s

/-- The curve `𝐁 = 𝐱 + α v`. -/
noncomputable def envB (x : ℝ → ℝ × ℝ) (α : ℝ → ℝ) (t : ℝ) : ℝ × ℝ := x t + α t • vvec t

/-- The curve `𝐃 = 𝐱 - β u`. -/
noncomputable def envD (x : ℝ → ℝ × ℝ) (β : ℝ → ℝ) (t : ℝ) : ℝ × ℝ := x t - β t • uvec t

/-- The curve `Γ = 𝐁([t₃, π/2]) ∪ 𝐱([t₁, t₄]) ∪ 𝐃([0, t₂])`. -/
def envCurve (t₁ t₂ t₃ t₄ : ℝ) (x : ℝ → ℝ × ℝ) (α β : ℝ → ℝ) : Set (ℝ × ℝ) :=
  envB x α '' Icc t₃ (π / 2) ∪ x '' Icc t₁ t₄ ∪ envD x β '' Icc 0 t₂

/-- The points `q` with `q₂ ≥ 0` lying on or below a point of `Γ`. -/
def envUnder (Γ : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := {q | 0 ≤ q.2 ∧ ∃ γ ∈ Γ, γ.1 = q.1 ∧ q.2 ≤ γ.2}

/-- The points `q` with `q₂ ≥ 0` lying strictly below a point of `Γ`. -/
def envUnderStrict (Γ : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {q | 0 ≤ q.2 ∧ ∃ γ ∈ Γ, γ.1 = q.1 ∧ q.2 < γ.2}

/-- Hypotheses of the envelope theorem (all verified for Gerver's path, with
`t₁ = φ, t₂ = θ, t₃ = π/2 - θ, t₄ = π/2 - φ, sA = 0.62, sC = 0.95`). -/
structure EnvHyp (t₁ t₂ t₃ t₄ sA sC : ℝ) (x : ℝ → ℝ × ℝ) (α β ρA ρC : ℝ → ℝ) : Prop where
  ht : 0 < t₁ ∧ t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < t₄ ∧ t₄ < π / 2
  hsA : t₁ ≤ sA ∧ sA ≤ t₃
  hsC : t₂ ≤ sC ∧ sC ≤ t₄
  x_cont : ContinuousOn x (Icc 0 (π / 2))
  x_deriv : ∀ t ∈ Ioo 0 (π / 2), HasDerivAt x (α t • uvec t + β t • vvec t) t
  α_cont : ContinuousOn α (Icc 0 (π / 2))
  β_cont : ContinuousOn β (Icc 0 (π / 2))
  B_deriv : ∀ t ∈ Ioo 0 (π / 2), t ∉ ({t₁, t₂, t₃, t₄} : Set ℝ) →
    HasDerivAt (envB x α) ((ρA t - 1) • vvec t) t
  D_deriv : ∀ t ∈ Ioo 0 (π / 2), t ∉ ({t₁, t₂, t₃, t₄} : Set ℝ) →
    HasDerivAt (envD x β) ((1 - ρC t) • uvec t) t
  α_neg : ∀ t ∈ Ioo 0 (π / 2), α t < 0
  β_pos : ∀ t ∈ Ioo 0 (π / 2), 0 < β t
  ratio_mono : ∀ r ∈ Ioo 0 (π / 2), ∀ r' ∈ Ioo 0 (π / 2), r ≤ r' → -α r * β r' ≤ -α r' * β r
  ρA_le : ∀ t ∈ Icc sA (π / 2), ρA t ≤ 1
  ρA_lt : ∀ t ∈ Icc t₃ (π / 2), ρA t < 1
  ρC_le : ∀ t ∈ Icc 0 sC, ρC t ≤ 1
  ρC_lt : ∀ t ∈ Icc 0 t₂, ρC t < 1
  I_nonneg : ∀ s ∈ Icc t₁ sA, 0 ≤ dot (x t₁ - x s) (uvec s)
  I'_nonneg : ∀ s ∈ Icc sC t₄, 0 ≤ dot (x t₄ - x s) (vvec s)
  corner_B : ∀ s ∈ Icc 0 t₁, 0 ≤ dot (x t₁ - x s) (uvec t₃)
  corner_D : ∀ s ∈ Icc t₄ (π / 2), 0 ≤ dot (x t₄ - x s) (vvec t₂)
  x_pos : ∀ t ∈ Icc t₁ t₄, 0 < (x t).2
  B_t₃ : envB x α t₃ = x t₁
  D_t₂ : envD x β t₂ = x t₄
  B_end : (envB x α (π / 2)).2 = 0
  D_end : (envD x β 0).2 = 0

/-! ### Elementary facts -/

/-- The first coordinate of a differentiable curve. -/
lemma env_hasDerivAt_fst {p : ℝ → ℝ × ℝ} {p' : ℝ × ℝ} {t : ℝ} (hp : HasDerivAt p p' t) :
    HasDerivAt (fun t => (p t).1) p'.1 t :=
  HasFDerivAt.comp_hasDerivAt t (hasFDerivAt_fst (𝕜 := ℝ) (p := p t)) hp

/-- The second coordinate of a differentiable curve. -/
lemma env_hasDerivAt_snd {p : ℝ → ℝ × ℝ} {p' : ℝ × ℝ} {t : ℝ} (hp : HasDerivAt p p' t) :
    HasDerivAt (fun t => (p t).2) p'.2 t :=
  HasFDerivAt.comp_hasDerivAt t (hasFDerivAt_snd (𝕜 := ℝ) (p := p t)) hp

/-- The derivative of `t ↦ p(t) · w`. -/
lemma env_hasDerivAt_dot {p : ℝ → ℝ × ℝ} {p' : ℝ × ℝ} {t : ℝ} (hp : HasDerivAt p p' t)
    (w : ℝ × ℝ) : HasDerivAt (fun t => dot (p t) w) (dot p' w) t := by
  unfold dot
  exact ((env_hasDerivAt_fst hp).mul_const w.1).add ((env_hasDerivAt_snd hp).mul_const w.2)

/-- Continuity of `t ↦ p(t) · w`. -/
lemma env_continuousOn_dot {p : ℝ → ℝ × ℝ} {S : Set ℝ} (hp : ContinuousOn p S) (w : ℝ × ℝ) :
    ContinuousOn (fun t => dot (p t) w) S := by
  unfold dot
  exact (hp.fst.mul continuousOn_const).add (hp.snd.mul continuousOn_const)

/-- `t ↦ u_t` is continuous. -/
lemma env_continuous_uvec : Continuous uvec := by unfold uvec; fun_prop

/-- `t ↦ v_t` is continuous. -/
lemma env_continuous_vvec : Continuous vvec := by unfold vvec; fun_prop

/-- Envelope fact: `f_s(𝐁(s)) = (𝐁(s) - x(s)) · u_s = 0`. -/
lemma env_dot_B_self (x : ℝ → ℝ × ℝ) (α : ℝ → ℝ) (s : ℝ) :
    dot (envB x α s - x s) (uvec s) = 0 := by
  simp [envB, dot_smul_left]

/-- Envelope fact: `g_s(𝐃(s)) = (𝐃(s) - x(s)) · v_s = 0`. -/
lemma env_dot_D_self (x : ℝ → ℝ × ℝ) (β : ℝ → ℝ) (s : ℝ) :
    dot (envD x β s - x s) (vvec s) = 0 := by
  simp [envD, dot_neg_left, dot_smul_left]

/-- The set of breakpoints is finite. -/
lemma env_bp_finite (t₁ t₂ t₃ t₄ : ℝ) : ({t₁, t₂, t₃, t₄} : Set ℝ).Finite := Set.toFinite _

/-! ### Principle P -/

/-- `u_σ = cos(σ - s) u_s + sin(σ - s) v_s`, paired with a vector `p`. -/
lemma env_dot_uvec_eq (p : ℝ × ℝ) (s σ : ℝ) :
    dot p (uvec σ) = cos (σ - s) * dot p (uvec s) + sin (σ - s) * dot p (vvec s) := by
  have h1 : cos σ = cos (σ - s) * cos s - sin (σ - s) * sin s := by
    rw [← cos_add, sub_add_cancel]
  have h2 : sin σ = sin (σ - s) * cos s + cos (σ - s) * sin s := by
    rw [← sin_add, sub_add_cancel]
  simp only [dot, uvec, vvec]
  rw [h1, h2]; ring

/-- **Principle P.** If `(p - x(s)) · u_σ ≥ 0` for some `σ ∈ [s, s + π/2]`, then `p ∉ Q⁻(s)`. -/
lemma env_not_mem_of_dot {x : ℝ → ℝ × ℝ} {s σ : ℝ} {p : ℝ × ℝ} (hσ : σ ∈ Icc s (s + π / 2))
    (h : 0 ≤ dot (p - x s) (uvec σ)) : p ∉ envQuad x s := by
  rintro ⟨hf, hg⟩
  rw [env_dot_uvec_eq _ s σ] at h
  have hc : 0 ≤ cos (σ - s) :=
    cos_nonneg_of_mem_Icc ⟨by linarith [hσ.1, pi_pos], by linarith [hσ.2]⟩
  have hs : 0 ≤ sin (σ - s) := sin_nonneg_of_nonneg_of_le_pi (by linarith [hσ.1])
    (by linarith [hσ.2, pi_pos])
  have h1 := sin_sq_add_cos_sq (σ - s)
  rcases hc.lt_or_eq with hc' | hc'
  · nlinarith [mul_neg_of_pos_of_neg hc' hf, mul_nonpos_of_nonneg_of_nonpos hs hg.le]
  · rw [← hc'] at h1 h
    have : sin (σ - s) = 1 := by nlinarith
    rw [this] at h
    linarith

/-! ### Monotonicity from the sign of a derivative off a finite set -/

private lemma env_le_aux {f f' : ℝ → ℝ} (T : Finset ℝ) :
    ∀ a b : ℝ, a ≤ b → ContinuousOn f (Icc a b) →
      (∀ t ∈ Ioo a b, t ∉ (T : Set ℝ) → HasDerivAt f (f' t) t ∧ 0 ≤ f' t) → f a ≤ f b := by
  induction T using Finset.induction_on with
  | empty =>
    intro a b hab hc hd
    rcases hab.eq_or_lt with rfl | hab'
    · exact le_rfl
    obtain ⟨c, hc', hfc⟩ :=
      exists_hasDerivAt_eq_slope f f' hab' hc (fun t ht => (hd t ht (by simp)).1)
    have h1 := (hd c hc' (by simp)).2
    rw [hfc] at h1
    have h2 := mul_nonneg h1 (sub_pos.2 hab').le
    rw [div_mul_cancel₀ _ (sub_pos.2 hab').ne'] at h2
    linarith
  | insert c T hcT ih =>
    intro a b hab hcont hd
    by_cases hc : c ∈ Ioo a b
    · have h1 : f a ≤ f c := ih a c hc.1.le (hcont.mono (Icc_subset_Icc le_rfl hc.2.le))
        (fun t ht htT => hd t ⟨ht.1, ht.2.trans hc.2⟩ (by
          simp only [Finset.coe_insert, mem_insert_iff, not_or]; exact ⟨ht.2.ne, htT⟩))
      have h2 : f c ≤ f b := ih c b hc.2.le (hcont.mono (Icc_subset_Icc hc.1.le le_rfl))
        (fun t ht htT => hd t ⟨hc.1.trans ht.1, ht.2⟩ (by
          simp only [Finset.coe_insert, mem_insert_iff, not_or]; exact ⟨ht.1.ne', htT⟩))
      exact h1.trans h2
    · exact ih a b hab hcont (fun t ht htT => hd t ht (by
        simp only [Finset.coe_insert, mem_insert_iff, not_or]
        exact ⟨fun h => hc (h ▸ ht), htT⟩))

private lemma env_lt_aux {f f' : ℝ → ℝ} (T : Finset ℝ) :
    ∀ a b : ℝ, a < b → ContinuousOn f (Icc a b) →
      (∀ t ∈ Ioo a b, t ∉ (T : Set ℝ) → HasDerivAt f (f' t) t ∧ 0 < f' t) → f a < f b := by
  induction T using Finset.induction_on with
  | empty =>
    intro a b hab hc hd
    obtain ⟨c, hc', hfc⟩ :=
      exists_hasDerivAt_eq_slope f f' hab hc (fun t ht => (hd t ht (by simp)).1)
    have h1 := (hd c hc' (by simp)).2
    rw [hfc] at h1
    have h2 := mul_pos h1 (sub_pos.2 hab)
    rw [div_mul_cancel₀ _ (sub_pos.2 hab).ne'] at h2
    linarith
  | insert c T hcT ih =>
    intro a b hab hcont hd
    by_cases hc : c ∈ Ioo a b
    · have h1 : f a < f c := ih a c hc.1 (hcont.mono (Icc_subset_Icc le_rfl hc.2.le))
        (fun t ht htT => hd t ⟨ht.1, ht.2.trans hc.2⟩ (by
          simp only [Finset.coe_insert, mem_insert_iff, not_or]; exact ⟨ht.2.ne, htT⟩))
      have h2 : f c < f b := ih c b hc.2 (hcont.mono (Icc_subset_Icc hc.1.le le_rfl))
        (fun t ht htT => hd t ⟨hc.1.trans ht.1, ht.2⟩ (by
          simp only [Finset.coe_insert, mem_insert_iff, not_or]; exact ⟨ht.1.ne', htT⟩))
      exact h1.trans h2
    · exact ih a b hab hcont (fun t ht htT => hd t ht (by
        simp only [Finset.coe_insert, mem_insert_iff, not_or]
        exact ⟨fun h => hc (h ▸ ht), htT⟩))

/-- A continuous function with a nonnegative derivative off a finite set is monotone. -/
lemma env_monotoneOn {f f' : ℝ → ℝ} {a b : ℝ} {S : Set ℝ} (hS : S.Finite)
    (hc : ContinuousOn f (Icc a b)) (hd : ∀ t ∈ Ioo a b, t ∉ S → HasDerivAt f (f' t) t)
    (hpos : ∀ t ∈ Ioo a b, t ∉ S → 0 ≤ f' t) : MonotoneOn f (Icc a b) := by
  intro u hu v hv huv
  refine env_le_aux (f' := f') hS.toFinset u v huv (hc.mono (Icc_subset_Icc hu.1 hv.2)) ?_
  intro t ht htS
  rw [Set.Finite.coe_toFinset] at htS
  have ht' : t ∈ Ioo a b := ⟨hu.1.trans_lt ht.1, ht.2.trans_le hv.2⟩
  exact ⟨hd t ht' htS, hpos t ht' htS⟩

/-- A continuous function with a nonpositive derivative off a finite set is antitone. -/
lemma env_antitoneOn {f f' : ℝ → ℝ} {a b : ℝ} {S : Set ℝ} (hS : S.Finite)
    (hc : ContinuousOn f (Icc a b)) (hd : ∀ t ∈ Ioo a b, t ∉ S → HasDerivAt f (f' t) t)
    (hneg : ∀ t ∈ Ioo a b, t ∉ S → f' t ≤ 0) : AntitoneOn f (Icc a b) := by
  have := env_monotoneOn (f := fun t => -f t) (f' := fun t => -f' t) hS hc.neg
    (fun t ht htS => (hd t ht htS).neg) (fun t ht htS => neg_nonneg.2 (hneg t ht htS))
  exact fun u hu v hv huv => neg_le_neg_iff.1 (this hu hv huv)

/-- A continuous function with a positive derivative off a finite set is strictly monotone. -/
lemma env_strictMonoOn {f f' : ℝ → ℝ} {a b : ℝ} {S : Set ℝ} (hS : S.Finite)
    (hc : ContinuousOn f (Icc a b)) (hd : ∀ t ∈ Ioo a b, t ∉ S → HasDerivAt f (f' t) t)
    (hpos : ∀ t ∈ Ioo a b, t ∉ S → 0 < f' t) : StrictMonoOn f (Icc a b) := by
  intro u hu v hv huv
  refine env_lt_aux (f' := f') hS.toFinset u v huv (hc.mono (Icc_subset_Icc hu.1 hv.2)) ?_
  intro t ht htS
  rw [Set.Finite.coe_toFinset] at htS
  have ht' : t ∈ Ioo a b := ⟨hu.1.trans_lt ht.1, ht.2.trans_le hv.2⟩
  exact ⟨hd t ht' htS, hpos t ht' htS⟩

/-- A continuous function with a negative derivative off a finite set is strictly antitone. -/
lemma env_strictAntiOn {f f' : ℝ → ℝ} {a b : ℝ} {S : Set ℝ} (hS : S.Finite)
    (hc : ContinuousOn f (Icc a b)) (hd : ∀ t ∈ Ioo a b, t ∉ S → HasDerivAt f (f' t) t)
    (hneg : ∀ t ∈ Ioo a b, t ∉ S → f' t < 0) : StrictAntiOn f (Icc a b) := by
  have := env_strictMonoOn (f := fun t => -f t) (f' := fun t => -f' t) hS hc.neg
    (fun t ht htS => (hd t ht htS).neg) (fun t ht htS => neg_pos.2 (hneg t ht htS))
  exact fun u hu v hv huv => neg_lt_neg_iff.1 (this hu hv huv)

/-- If `F'` stays negative once it is negative, then `F` is at least the smaller of its values at
the endpoints. -/
lemma env_min_le {F F' : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn F (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt F (F' t) t)
    (hsign : ∀ t₀ ∈ Ioo a b, ∀ t₁ ∈ Ioo a b, t₀ ≤ t₁ → F' t₀ < 0 → F' t₁ < 0) :
    ∀ t ∈ Icc a b, min (F a) (F b) ≤ F t := by
  intro t ht
  by_contra hlt
  push Not at hlt
  have h1 : F t < F a := lt_of_lt_of_le hlt (min_le_left _ _)
  have h2 : F t < F b := lt_of_lt_of_le hlt (min_le_right _ _)
  have hat : a < t := lt_of_le_of_ne ht.1 (by rintro rfl; exact lt_irrefl _ h1)
  have htb : t < b := lt_of_le_of_ne ht.2 (by rintro rfl; exact lt_irrefl _ h2)
  obtain ⟨c, hc1, hc2⟩ := exists_hasDerivAt_eq_slope F F' hat
    (hc.mono (Icc_subset_Icc le_rfl ht.2)) (fun u hu => hd u ⟨hu.1, hu.2.trans htb⟩)
  obtain ⟨d, hd1, hd2⟩ := exists_hasDerivAt_eq_slope F F' htb
    (hc.mono (Icc_subset_Icc ht.1 le_rfl)) (fun u hu => hd u ⟨hat.trans hu.1, hu.2⟩)
  have hc3 : F' c < 0 := by rw [hc2]; exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hd3 : 0 < F' d := by rw [hd2]; exact div_pos (by linarith) (by linarith)
  have := hsign c ⟨hc1.1, hc1.2.trans htb⟩ d ⟨hat.trans hd1.1, hd1.2⟩ (hc1.2.trans hd1.1).le hc3
  linarith

/-- The algebraic core of the sign argument: with `|α|/β` nondecreasing and the angle decreasing,
`α cos θ + β sin θ` stays negative once it is negative. -/
lemma env_sign_aux {a₀ b₀ a₁ b₁ c₀ s₀ c₁ s₁ : ℝ} (hb₀ : 0 < b₀) (hb₁ : 0 < b₁)
    (hab : a₁ * b₀ ≤ a₀ * b₁) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hcs : s₁ * c₀ ≤ s₀ * c₁)
    (h : a₀ * c₀ + b₀ * s₀ < 0) : a₁ * c₁ + b₁ * s₁ < 0 := by
  have key : (a₁ * c₁ + b₁ * s₁) * (b₀ * c₀) < 0 := by
    nlinarith [mul_le_mul_of_nonneg_right hab (mul_pos hc₀ hc₁).le,
      mul_lt_mul_of_pos_left h (mul_pos hb₁ hc₁),
      mul_le_mul_of_nonneg_left hcs (mul_pos hb₀ hb₁).le]
  by_contra hcon
  push Not at hcon
  nlinarith [mul_nonneg hcon (mul_pos hb₀ hc₀).le]

section geometry

variable {t₁ t₂ t₃ t₄ sA sC : ℝ} {x : ℝ → ℝ × ℝ} {α β ρA ρC : ℝ → ℝ}

/-- `𝐁` is continuous on `[0, π/2]`. -/
lemma env_B_cont (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) :
    ContinuousOn (envB x α) (Icc 0 (π / 2)) :=
  h.x_cont.add (h.α_cont.smul env_continuous_vvec.continuousOn)

/-- `𝐃` is continuous on `[0, π/2]`. -/
lemma env_D_cont (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) :
    ContinuousOn (envD x β) (Icc 0 (π / 2)) :=
  h.x_cont.sub (h.β_cont.smul env_continuous_uvec.continuousOn)

/-- The derivative of `r ↦ f_s(𝐁(r))` off the breakpoints. -/
lemma env_phi_deriv (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) {s r : ℝ}
    (hr : r ∈ Ioo 0 (π / 2)) (hr' : r ∉ ({t₁, t₂, t₃, t₄} : Set ℝ)) :
    HasDerivAt (fun r => dot (envB x α r - x s) (uvec s)) ((ρA r - 1) * sin (s - r)) r := by
  have := env_hasDerivAt_dot ((h.B_deriv r hr hr').sub_const (x s)) (uvec s)
  convert this using 1
  rw [dot_smul_left, dot_vvec_uvec']

/-- The derivative of `r ↦ g_s(𝐃(r))` off the breakpoints. -/
lemma env_psi_deriv (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) {s r : ℝ}
    (hr : r ∈ Ioo 0 (π / 2)) (hr' : r ∉ ({t₁, t₂, t₃, t₄} : Set ℝ)) :
    HasDerivAt (fun r => dot (envD x β r - x s) (vvec s)) ((1 - ρC r) * sin (r - s)) r := by
  have := env_hasDerivAt_dot ((h.D_deriv r hr hr').sub_const (x s)) (vvec s)
  convert this using 1
  rw [dot_smul_left, dot_uvec_vvec']

/-- The derivative of `F(τ) = f_s(x(τ))`. -/
lemma env_F_deriv (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) {s τ : ℝ}
    (hτ : τ ∈ Ioo 0 (π / 2)) :
    HasDerivAt (fun τ => dot (x τ - x s) (uvec s)) (α τ * cos (τ - s) + β τ * sin (s - τ)) τ := by
  have := env_hasDerivAt_dot ((h.x_deriv τ hτ).sub_const (x s)) (uvec s)
  convert this using 1
  rw [dot_add_left, dot_smul_left, dot_smul_left, dot_uvec_uvec, dot_vvec_uvec']

/-- The derivative of `G(τ) = g_s(x(τ))`. -/
lemma env_G_deriv (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) {s τ : ℝ}
    (hτ : τ ∈ Ioo 0 (π / 2)) :
    HasDerivAt (fun τ => dot (x τ - x s) (vvec s)) (α τ * sin (τ - s) + β τ * cos (τ - s)) τ := by
  have := env_hasDerivAt_dot ((h.x_deriv τ hτ).sub_const (x s)) (vvec s)
  convert this using 1
  rw [dot_add_left, dot_smul_left, dot_smul_left, dot_uvec_vvec', dot_vvec_vvec]

/-- `r ↦ f_s(𝐁(r))` is nondecreasing on `[max s s_A, π/2]`. -/
lemma env_phi_mono (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) {s : ℝ}
    (hs : s ∈ Ioo 0 (π / 2)) :
    MonotoneOn (fun r => dot (envB x α r - x s) (uvec s)) (Icc (max s sA) (π / 2)) := by
  have hsub : Icc (max s sA) (π / 2) ⊆ Icc 0 (π / 2) :=
    Icc_subset_Icc (le_max_of_le_left hs.1.le) le_rfl
  refine env_monotoneOn (env_bp_finite t₁ t₂ t₃ t₄)
    (env_continuousOn_dot (((env_B_cont h).mono hsub).sub continuousOn_const) _)
    (fun r hr hr' => env_phi_deriv h ⟨(lt_max_of_lt_left hs.1).trans hr.1, hr.2⟩ hr') ?_
  intro r hr _
  have h1 : ρA r - 1 ≤ 0 := by
    linarith [h.ρA_le r ⟨(le_max_right _ _).trans hr.1.le, hr.2.le⟩]
  have h2 : sin (s - r) ≤ 0 := sin_nonpos_of_nonpos_of_neg_pi_le
    (by linarith [le_max_left s sA, hr.1]) (by linarith [hr.2, hs.1, pi_pos])
  nlinarith

/-- `r ↦ f_s(𝐁(r))` is nonincreasing on `[s_A, s]`. -/
lemma env_phi_anti (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) {s : ℝ}
    (hs : s ∈ Ioo 0 (π / 2)) :
    AntitoneOn (fun r => dot (envB x α r - x s) (uvec s)) (Icc sA s) := by
  have hsA : 0 < sA := h.ht.1.trans_le h.hsA.1
  have hsub : Icc sA s ⊆ Icc 0 (π / 2) := Icc_subset_Icc hsA.le hs.2.le
  refine env_antitoneOn (env_bp_finite t₁ t₂ t₃ t₄)
    (env_continuousOn_dot (((env_B_cont h).mono hsub).sub continuousOn_const) _)
    (fun r hr hr' => env_phi_deriv h ⟨hsA.trans hr.1, hr.2.trans hs.2⟩ hr') ?_
  intro r hr _
  have h1 : ρA r - 1 ≤ 0 := by
    linarith [h.ρA_le r ⟨hr.1.le, (hr.2.trans hs.2).le⟩]
  have h2 : 0 ≤ sin (s - r) := sin_nonneg_of_nonneg_of_le_pi
    (by linarith [hr.2]) (by linarith [hr.1, hs.2, pi_pos])
  nlinarith

/-- `r ↦ g_s(𝐃(r))` is nondecreasing on `[s, s_C]`. -/
lemma env_psi_mono (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) {s : ℝ}
    (hs : s ∈ Ioo 0 (π / 2)) :
    MonotoneOn (fun r => dot (envD x β r - x s) (vvec s)) (Icc s sC) := by
  have hsC : sC < π / 2 := h.hsC.2.trans_lt h.ht.2.2.2.2
  have hsub : Icc s sC ⊆ Icc 0 (π / 2) := Icc_subset_Icc hs.1.le hsC.le
  refine env_monotoneOn (env_bp_finite t₁ t₂ t₃ t₄)
    (env_continuousOn_dot (((env_D_cont h).mono hsub).sub continuousOn_const) _)
    (fun r hr hr' => env_psi_deriv h ⟨hs.1.trans hr.1, hr.2.trans hsC⟩ hr') ?_
  intro r hr _
  have h1 : 0 ≤ 1 - ρC r := by
    linarith [h.ρC_le r ⟨(hs.1.trans hr.1).le, hr.2.le⟩]
  have h2 : 0 ≤ sin (r - s) := sin_nonneg_of_nonneg_of_le_pi
    (by linarith [hr.1]) (by linarith [hr.2, hsC, hs.1, pi_pos])
  nlinarith

/-- `r ↦ g_s(𝐃(r))` is nonincreasing on `[0, min s s_C]`. -/
lemma env_psi_anti (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) {s : ℝ}
    (hs : s ∈ Ioo 0 (π / 2)) :
    AntitoneOn (fun r => dot (envD x β r - x s) (vvec s)) (Icc 0 (min s sC)) := by
  have hsub : Icc 0 (min s sC) ⊆ Icc 0 (π / 2) :=
    Icc_subset_Icc le_rfl ((min_le_left _ _).trans hs.2.le)
  refine env_antitoneOn (env_bp_finite t₁ t₂ t₃ t₄)
    (env_continuousOn_dot (((env_D_cont h).mono hsub).sub continuousOn_const) _)
    (fun r hr hr' => env_psi_deriv h ⟨hr.1, hr.2.trans_le ((min_le_left _ _).trans hs.2.le)⟩ hr')
    ?_
  intro r hr _
  have h1 : 0 ≤ 1 - ρC r := by
    linarith [h.ρC_le r ⟨hr.1.le, (hr.2.trans_le (min_le_right _ _)).le⟩]
  have h2 : sin (r - s) ≤ 0 := sin_nonpos_of_nonpos_of_neg_pi_le
    (by linarith [hr.2, min_le_left s sC]) (by linarith [hr.1, hs.2, pi_pos])
  nlinarith

/-- `I(s) = (𝐱(t₁) - 𝐱(s)) · u_s ≥ 0` for `s ∈ [t₁, π/2)`. -/
lemma env_I_nonneg (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) {s : ℝ} (hs : s ∈ Ico t₁ (π / 2)) :
    0 ≤ dot (x t₁ - x s) (uvec s) := by
  obtain ⟨ht₁, ht₁₂, ht₂₃, ht₃₄, ht₄⟩ := h.ht
  rcases le_total s sA with hsA | hsA
  · exact h.I_nonneg s ⟨hs.1, hsA⟩
  have hs' : s ∈ Ioo 0 (π / 2) := ⟨ht₁.trans_le hs.1, hs.2⟩
  have e : dot (x t₁ - x s) (uvec s) = dot (envB x α t₃ - x s) (uvec s) := by rw [h.B_t₃]
  rw [e, ← env_dot_B_self x α s]
  rcases le_total s t₃ with hst | hst
  · have hm := max_eq_left hsA
    exact env_phi_mono h hs' ⟨(max_le le_rfl hsA), hs.2.le⟩
      ⟨max_le hst h.hsA.2, (ht₃₄.trans ht₄).le⟩ hst
  · exact env_phi_anti h hs' ⟨h.hsA.2, hst⟩ ⟨hsA, le_rfl⟩ hst

/-- `J(s) = (𝐱(t₄) - 𝐱(s)) · v_s ≥ 0` for `s ∈ (0, t₄]`. -/
lemma env_J_nonneg (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) {s : ℝ} (hs : s ∈ Ioc 0 t₄) :
    0 ≤ dot (x t₄ - x s) (vvec s) := by
  obtain ⟨ht₁, ht₁₂, ht₂₃, ht₃₄, ht₄⟩ := h.ht
  rcases le_total sC s with hsC | hsC
  · exact h.I'_nonneg s ⟨hsC, hs.2⟩
  have hs' : s ∈ Ioo 0 (π / 2) := ⟨hs.1, hs.2.trans_lt ht₄⟩
  have e : dot (x t₄ - x s) (vvec s) = dot (envD x β t₂ - x s) (vvec s) := by rw [h.D_t₂]
  rw [e, ← env_dot_D_self x β s]
  rcases le_total s t₂ with hst | hst
  · exact env_psi_mono h hs' ⟨le_rfl, hsC⟩ ⟨hst, h.hsC.1⟩ hst
  · exact env_psi_anti h hs' ⟨(ht₁.trans ht₁₂).le, le_min hst h.hsC.1⟩
      ⟨hs.1.le, le_min le_rfl hsC⟩ hst

/-- Witness for `𝐱(τ) ∉ Q⁻(s)`. -/
lemma env_wit_x (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) {s τ : ℝ}
    (hs : s ∈ Ioo 0 (π / 2)) (hτ : τ ∈ Icc t₁ t₄) :
    ∃ σ ∈ Icc s (s + π / 2), 0 ≤ dot (x τ - x s) (uvec σ) := by
  obtain ⟨ht₁, ht₁₂, ht₂₃, ht₃₄, ht₄⟩ := h.ht
  rcases le_total τ s with hτs | hτs
  · -- `σ = s`: the function `F(τ') = f_s(𝐱(τ'))` on `[t₁, s]`
    refine ⟨s, ⟨le_rfl, by linarith [pi_pos]⟩, ?_⟩
    have hsub : Icc t₁ s ⊆ Icc 0 (π / 2) := Icc_subset_Icc ht₁.le hs.2.le
    have hmin := env_min_le (F := fun τ => dot (x τ - x s) (uvec s))
      (F' := fun τ => α τ * cos (τ - s) + β τ * sin (s - τ))
      (env_continuousOn_dot ((h.x_cont.mono hsub).sub continuousOn_const) _)
      (fun τ' hτ' => env_F_deriv h ⟨ht₁.trans hτ'.1, hτ'.2.trans hs.2⟩) ?_ τ ⟨hτ.1, hτs⟩
    · have hI := env_I_nonneg h ⟨hτ.1.trans hτs, hs.2⟩
      simp only [sub_self, dot_zero_left] at hmin
      exact (le_min hI le_rfl).trans hmin
    · intro τ₀ hτ₀ τ₁ hτ₁ h01 hneg
      have hτ₀' : τ₀ ∈ Ioo 0 (π / 2) := ⟨ht₁.trans hτ₀.1, hτ₀.2.trans hs.2⟩
      have hτ₁' : τ₁ ∈ Ioo 0 (π / 2) := ⟨ht₁.trans hτ₁.1, hτ₁.2.trans hs.2⟩
      refine env_sign_aux (h.β_pos τ₀ hτ₀') (h.β_pos τ₁ hτ₁') ?_ ?_ ?_ ?_ hneg
      · linarith [h.ratio_mono τ₀ hτ₀' τ₁ hτ₁' h01]
      · exact cos_pos_of_mem_Ioo ⟨by linarith [hτ₀'.1, hs.2], by linarith [hτ₀.2, pi_pos]⟩
      · exact cos_pos_of_mem_Ioo ⟨by linarith [hτ₁'.1, hs.2], by linarith [hτ₁.2, pi_pos]⟩
      · have e1 : sin (τ₁ - τ₀) = sin (s - τ₀) * cos (s - τ₁) - cos (s - τ₀) * sin (s - τ₁) := by
          rw [← sin_sub]; congr 1; ring
        have e2 : cos (τ₁ - s) = cos (s - τ₁) := by rw [← cos_neg, neg_sub]
        have e3 : cos (τ₀ - s) = cos (s - τ₀) := by rw [← cos_neg, neg_sub]
        have : 0 ≤ sin (τ₁ - τ₀) := sin_nonneg_of_nonneg_of_le_pi (by linarith)
          (by linarith [hτ₁.2, hτ₀.1, hs.2, pi_pos])
        rw [e2, e3]
        linarith
  · -- `σ = s + π/2`: the function `G(τ') = g_s(𝐱(τ'))` on `[s, t₄]`
    refine ⟨s + π / 2, ⟨by linarith [pi_pos], le_rfl⟩, ?_⟩
    rw [uvec_add_pi_div_two]
    have hsub : Icc s t₄ ⊆ Icc 0 (π / 2) := Icc_subset_Icc hs.1.le ht₄.le
    have hmin := env_min_le (F := fun τ => dot (x τ - x s) (vvec s))
      (F' := fun τ => α τ * sin (τ - s) + β τ * cos (τ - s))
      (env_continuousOn_dot ((h.x_cont.mono hsub).sub continuousOn_const) _)
      (fun τ' hτ' => env_G_deriv h ⟨hs.1.trans hτ'.1, hτ'.2.trans ht₄⟩) ?_ τ ⟨hτs, hτ.2⟩
    · have hJ := env_J_nonneg h ⟨hs.1, hτs.trans hτ.2⟩
      simp only [sub_self, dot_zero_left] at hmin
      exact (le_min le_rfl hJ).trans hmin
    · intro τ₀ hτ₀ τ₁ hτ₁ h01 hneg
      have hτ₀' : τ₀ ∈ Ioo 0 (π / 2) := ⟨hs.1.trans hτ₀.1, hτ₀.2.trans ht₄⟩
      have hτ₁' : τ₁ ∈ Ioo 0 (π / 2) := ⟨hs.1.trans hτ₁.1, hτ₁.2.trans ht₄⟩
      refine env_sign_aux (h.β_pos τ₀ hτ₀') (h.β_pos τ₁ hτ₁') ?_ ?_ ?_ ?_ hneg
      · linarith [h.ratio_mono τ₀ hτ₀' τ₁ hτ₁' h01]
      · exact sin_pos_of_pos_of_lt_pi (by linarith [hτ₀.1]) (by linarith [hτ₀'.2, hs.1, pi_pos])
      · exact sin_pos_of_pos_of_lt_pi (by linarith [hτ₁.1]) (by linarith [hτ₁'.2, hs.1, pi_pos])
      · have e1 : sin (τ₁ - τ₀) = sin (τ₁ - s) * cos (τ₀ - s) - cos (τ₁ - s) * sin (τ₀ - s) := by
          rw [← sin_sub]; congr 1; ring
        have : 0 ≤ sin (τ₁ - τ₀) := sin_nonneg_of_nonneg_of_le_pi (by linarith)
          (by linarith [hτ₁.2, hτ₀.1, hs.1, ht₄, pi_pos])
        linarith

/-- Witness for `𝐁(τ) ∉ Q⁻(s)`, with an angle `σ ≤ π/2`. -/
lemma env_wit_B (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) {s τ : ℝ}
    (hs : s ∈ Ioo 0 (π / 2)) (hτ : τ ∈ Icc t₃ (π / 2)) :
    ∃ σ ∈ Icc s (s + π / 2), σ ≤ π / 2 ∧ 0 ≤ dot (envB x α τ - x s) (uvec σ) := by
  obtain ⟨ht₁, ht₁₂, ht₂₃, ht₃₄, ht₄⟩ := h.ht
  rcases le_total t₁ s with hts | hts
  · refine ⟨s, ⟨le_rfl, by linarith [pi_pos]⟩, hs.2.le, ?_⟩
    rw [← env_dot_B_self x α s]
    rcases le_total s t₃ with hs3 | hs3
    · have hI := env_I_nonneg h ⟨hts, hs.2⟩
      have e : dot (x t₁ - x s) (uvec s) = dot (envB x α t₃ - x s) (uvec s) := by rw [h.B_t₃]
      have hm := env_phi_mono h hs ⟨max_le hs3 h.hsA.2, (ht₃₄.trans ht₄).le⟩
        ⟨(max_le hs3 h.hsA.2).trans hτ.1, hτ.2⟩ hτ.1
      simp only at hm
      rw [env_dot_B_self x α s]
      linarith
    · have hsA : sA ≤ s := h.hsA.2.trans hs3
      rcases le_total s τ with hsτ | hsτ
      · exact env_phi_mono h hs ⟨max_le le_rfl hsA, hs.2.le⟩
          ⟨(max_le le_rfl hsA).trans hsτ, hτ.2⟩ hsτ
      · exact env_phi_anti h hs ⟨h.hsA.2.trans hτ.1, hsτ⟩ ⟨hsA, le_rfl⟩ hsτ
  · refine ⟨t₃, ⟨by linarith, by linarith [hs.1]⟩, by linarith, ?_⟩
    have ht₃ : t₃ ∈ Ioo 0 (π / 2) := ⟨by linarith, by linarith⟩
    have hm := env_phi_mono h ht₃ ⟨max_le le_rfl h.hsA.2, (ht₃₄.trans ht₄).le⟩
      ⟨max_le hτ.1 (h.hsA.2.trans hτ.1), hτ.2⟩ hτ.1
    simp only [env_dot_B_self] at hm
    have hc := h.corner_B s ⟨hs.1.le, hts⟩
    have e : envB x α τ - x s = (envB x α τ - x t₃) + (x t₁ - x s) - (envB x α t₃ - x t₃) := by
      rw [h.B_t₃]; abel
    rw [e, dot_sub_left, dot_add_left, env_dot_B_self]
    linarith

/-- Witness for `𝐃(τ) ∉ Q⁻(s)`, with an angle `σ ≥ π/2`. -/
lemma env_wit_D (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) {s τ : ℝ}
    (hs : s ∈ Ioo 0 (π / 2)) (hτ : τ ∈ Icc 0 t₂) :
    ∃ σ ∈ Icc s (s + π / 2), π / 2 ≤ σ ∧ 0 ≤ dot (envD x β τ - x s) (uvec σ) := by
  obtain ⟨ht₁, ht₁₂, ht₂₃, ht₃₄, ht₄⟩ := h.ht
  rcases le_total s t₄ with hst | hst
  · refine ⟨s + π / 2, ⟨by linarith [pi_pos], le_rfl⟩, by linarith [hs.1], ?_⟩
    rw [uvec_add_pi_div_two, ← env_dot_D_self x β s]
    rcases le_total t₂ s with hs2 | hs2
    · have hJ := env_J_nonneg h ⟨hs.1, hst⟩
      have e : dot (x t₄ - x s) (vvec s) = dot (envD x β t₂ - x s) (vvec s) := by rw [h.D_t₂]
      have hm := env_psi_anti h hs ⟨hτ.1, le_min (hτ.2.trans hs2) (hτ.2.trans h.hsC.1)⟩
        ⟨by linarith, le_min hs2 h.hsC.1⟩ hτ.2
      simp only at hm
      rw [env_dot_D_self x β s]
      linarith
    · have hsC : s ≤ sC := hs2.trans h.hsC.1
      rcases le_total τ s with hτs | hτs
      · exact env_psi_anti h hs ⟨hτ.1, le_min hτs (hτs.trans hsC)⟩ ⟨hs.1.le, le_min le_rfl hsC⟩ hτs
      · exact env_psi_mono h hs ⟨le_rfl, hsC⟩ ⟨hτs, hτ.2.trans h.hsC.1⟩ hτs
  · refine ⟨t₂ + π / 2, ⟨by linarith [hs.2], by linarith⟩, by linarith [hs.1], ?_⟩
    rw [uvec_add_pi_div_two]
    have ht₂ : t₂ ∈ Ioo 0 (π / 2) := ⟨by linarith, by linarith⟩
    have hm := env_psi_anti h ht₂ ⟨hτ.1, le_min hτ.2 (hτ.2.trans h.hsC.1)⟩
      ⟨(ht₁.trans ht₁₂).le, le_min le_rfl h.hsC.1⟩ hτ.2
    simp only [env_dot_D_self] at hm
    have hc := h.corner_D s ⟨hst, hs.2.le⟩
    have e : envD x β τ - x s = (envD x β τ - x t₂) + (x t₄ - x s) - (envD x β t₂ - x t₂) := by
      rw [h.D_t₂]; abel
    rw [e, dot_sub_left, dot_add_left, env_dot_D_self]
    linarith

/-- **The curves lie outside every quadrant `Q⁻(s)`.** -/
theorem env_not_mem (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) {s : ℝ}
    (hs : s ∈ Ioo 0 (π / 2)) :
    (∀ τ ∈ Icc t₁ t₄, x τ ∉ envQuad x s) ∧
      (∀ τ ∈ Icc t₃ (π / 2), envB x α τ ∉ envQuad x s) ∧
      (∀ τ ∈ Icc 0 t₂, envD x β τ ∉ envQuad x s) := by
  refine ⟨fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ => ?_⟩
  · obtain ⟨σ, hσ, hdot⟩ := env_wit_x h hs hτ
    exact env_not_mem_of_dot hσ hdot
  · obtain ⟨σ, hσ, -, hdot⟩ := env_wit_B h hs hτ
    exact env_not_mem_of_dot hσ hdot
  · obtain ⟨σ, hσ, -, hdot⟩ := env_wit_D h hs hτ
    exact env_not_mem_of_dot hσ hdot

/-- The curves lie outside the niche. -/
theorem env_not_mem_niche (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) :
    (∀ τ ∈ Icc t₁ t₄, x τ ∉ envNiche x) ∧
      (∀ τ ∈ Icc t₃ (π / 2), envB x α τ ∉ envNiche x) ∧
      (∀ τ ∈ Icc 0 t₂, envD x β τ ∉ envNiche x) := by
  refine ⟨fun τ hτ hmem => ?_, fun τ hτ hmem => ?_, fun τ hτ hmem => ?_⟩ <;>
  obtain ⟨s, hs, hq⟩ := mem_iUnion₂.1 hmem.2
  · exact (env_not_mem h hs).1 τ hτ hq
  · exact (env_not_mem h hs).2.1 τ hτ hq
  · exact (env_not_mem h hs).2.2 τ hτ hq

/-! ### Monotonicity of the coordinates of the curves -/

/-- `x₁` is strictly decreasing on `[t₁, t₄]`. -/
lemma env_x₁_strictAnti (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) :
    StrictAntiOn (fun t => (x t).1) (Icc t₁ t₄) := by
  obtain ⟨ht₁, ht₁₂, ht₂₃, ht₃₄, ht₄⟩ := h.ht
  have hsub : Icc t₁ t₄ ⊆ Icc 0 (π / 2) := Icc_subset_Icc ht₁.le ht₄.le
  refine env_strictAntiOn (S := ∅) (f' := fun t => (α t • uvec t + β t • vvec t).1)
    finite_empty (h.x_cont.mono hsub).fst
    (fun t ht _ => env_hasDerivAt_fst (h.x_deriv t ⟨ht₁.trans ht.1, ht.2.trans ht₄⟩)) ?_
  intro t ht _
  have ht' : t ∈ Ioo 0 (π / 2) := ⟨ht₁.trans ht.1, ht.2.trans ht₄⟩
  have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht'.1, pi_pos], ht'.2⟩
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht'.1 (by linarith [ht'.2, pi_pos])
  simp only [Prod.fst_add, Prod.smul_fst, uvec_fst, vvec_fst, smul_eq_mul]
  nlinarith [mul_neg_of_neg_of_pos (h.α_neg t ht') hc, mul_pos (h.β_pos t ht') hs]

/-- `𝐁₁` is strictly increasing on `[t₃, π/2]`. -/
lemma env_B₁_strictMono (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) :
    StrictMonoOn (fun t => (envB x α t).1) (Icc t₃ (π / 2)) := by
  obtain ⟨ht₁, ht₁₂, ht₂₃, ht₃₄, ht₄⟩ := h.ht
  have hsub : Icc t₃ (π / 2) ⊆ Icc 0 (π / 2) := Icc_subset_Icc (by linarith) le_rfl
  refine env_strictMonoOn (f' := fun t => ((ρA t - 1) • vvec t).1) (env_bp_finite t₁ t₂ t₃ t₄)
    ((env_B_cont h).mono hsub).fst
    (fun t ht ht' => env_hasDerivAt_fst (h.B_deriv t ⟨by linarith [ht.1], ht.2⟩ ht')) ?_
  intro t ht _
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, pi_pos])
  have hρ : ρA t - 1 < 0 := by linarith [h.ρA_lt t ⟨ht.1.le, ht.2.le⟩]
  simp only [Prod.smul_fst, vvec_fst, smul_eq_mul]
  nlinarith

/-- `𝐁₂` is strictly decreasing on `[t₃, π/2]`. -/
lemma env_B₂_strictAnti (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) :
    StrictAntiOn (fun t => (envB x α t).2) (Icc t₃ (π / 2)) := by
  obtain ⟨ht₁, ht₁₂, ht₂₃, ht₃₄, ht₄⟩ := h.ht
  have hsub : Icc t₃ (π / 2) ⊆ Icc 0 (π / 2) := Icc_subset_Icc (by linarith) le_rfl
  refine env_strictAntiOn (f' := fun t => ((ρA t - 1) • vvec t).2) (env_bp_finite t₁ t₂ t₃ t₄)
    ((env_B_cont h).mono hsub).snd
    (fun t ht ht' => env_hasDerivAt_snd (h.B_deriv t ⟨by linarith [ht.1], ht.2⟩ ht')) ?_
  intro t ht _
  have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩
  have hρ : ρA t - 1 < 0 := by linarith [h.ρA_lt t ⟨ht.1.le, ht.2.le⟩]
  simp only [Prod.smul_snd, vvec_snd, smul_eq_mul]
  nlinarith

/-- `𝐃₁` is strictly increasing on `[0, t₂]`. -/
lemma env_D₁_strictMono (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) :
    StrictMonoOn (fun t => (envD x β t).1) (Icc 0 t₂) := by
  obtain ⟨ht₁, ht₁₂, ht₂₃, ht₃₄, ht₄⟩ := h.ht
  have hsub : Icc 0 t₂ ⊆ Icc 0 (π / 2) := Icc_subset_Icc le_rfl (by linarith)
  refine env_strictMonoOn (f' := fun t => ((1 - ρC t) • uvec t).1) (env_bp_finite t₁ t₂ t₃ t₄)
    ((env_D_cont h).mono hsub).fst
    (fun t ht ht' => env_hasDerivAt_fst (h.D_deriv t ⟨ht.1, by linarith [ht.2]⟩ ht')) ?_
  intro t ht _
  have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
  have hρ : 0 < 1 - ρC t := by linarith [h.ρC_lt t ⟨ht.1.le, ht.2.le⟩]
  simp only [Prod.smul_fst, uvec_fst, smul_eq_mul]
  positivity

/-- `𝐃₂` is strictly increasing on `[0, t₂]`. -/
lemma env_D₂_strictMono (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) :
    StrictMonoOn (fun t => (envD x β t).2) (Icc 0 t₂) := by
  obtain ⟨ht₁, ht₁₂, ht₂₃, ht₃₄, ht₄⟩ := h.ht
  have hsub : Icc 0 t₂ ⊆ Icc 0 (π / 2) := Icc_subset_Icc le_rfl (by linarith)
  refine env_strictMonoOn (f' := fun t => ((1 - ρC t) • uvec t).2) (env_bp_finite t₁ t₂ t₃ t₄)
    ((env_D_cont h).mono hsub).snd
    (fun t ht ht' => env_hasDerivAt_snd (h.D_deriv t ⟨ht.1, by linarith [ht.2]⟩ ht')) ?_
  intro t ht _
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
  have hρ : 0 < 1 - ρC t := by linarith [h.ρC_lt t ⟨ht.1.le, ht.2.le⟩]
  simp only [Prod.smul_snd, uvec_snd, smul_eq_mul]
  positivity

/-- `𝐁₂ > 0` on `[t₃, π/2)`. -/
lemma env_B₂_pos (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) {τ : ℝ} (hτ : τ ∈ Ico t₃ (π / 2)) :
    0 < (envB x α τ).2 := by
  have := env_B₂_strictAnti h ⟨hτ.1, hτ.2.le⟩ ⟨hτ.1.trans hτ.2.le, le_rfl⟩ hτ.2
  simp only at this
  rw [h.B_end] at this
  exact this

/-- `𝐃₂ > 0` on `(0, t₂]`. -/
lemma env_D₂_pos (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) {τ : ℝ} (hτ : τ ∈ Ioc 0 t₂) :
    0 < (envD x β τ).2 := by
  have := env_D₂_strictMono h ⟨le_rfl, hτ.1.le.trans hτ.2⟩ ⟨hτ.1.le, hτ.2⟩ hτ.1
  simp only at this
  rw [h.D_end] at this
  exact this

/-! ### The niche is the region under `Γ` -/

/-- `(q - p) · u_σ = (γ - p) · u_σ + (q₁ - γ₁) cos σ + (q₂ - γ₂) sin σ`. -/
lemma env_dot_shift (q γ p : ℝ × ℝ) (σ : ℝ) :
    dot (q - p) (uvec σ) = dot (γ - p) (uvec σ) + (q.1 - γ.1) * cos σ + (q.2 - γ.2) * sin σ := by
  simp only [dot, uvec, Prod.fst_sub, Prod.snd_sub]; ring

/-- For `q₁ = γ₁`: `(q - p) · w = (γ - p) · w + (q₂ - γ₂) w₂`. -/
lemma env_dot_shift_snd {q γ : ℝ × ℝ} (p w : ℝ × ℝ) (h1 : γ.1 = q.1) :
    dot (q - p) w = dot (γ - p) w + (q.2 - γ.2) * w.2 := by
  simp only [dot, Prod.fst_sub, Prod.snd_sub]; rw [h1]; ring

/-- Witness for `γ ∉ Q⁻(s)`, `γ ∈ Γ`. -/
lemma env_wit_curve (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) {s : ℝ} (hs : s ∈ Ioo 0 (π / 2))
    {γ : ℝ × ℝ} (hγ : γ ∈ envCurve t₁ t₂ t₃ t₄ x α β) :
    ∃ σ ∈ Icc s (s + π / 2), 0 ≤ dot (γ - x s) (uvec σ) := by
  rcases hγ with (⟨τ, hτ, rfl⟩ | ⟨τ, hτ, rfl⟩) | ⟨τ, hτ, rfl⟩
  · obtain ⟨σ, hσ, -, hd⟩ := env_wit_B h hs hτ; exact ⟨σ, hσ, hd⟩
  · exact env_wit_x h hs hτ
  · obtain ⟨σ, hσ, -, hd⟩ := env_wit_D h hs hτ; exact ⟨σ, hσ, hd⟩

/-- Every abscissa between `𝐃(0)₁` and `𝐁(π/2)₁` is the abscissa of a point of `Γ`. -/
lemma env_exists_curve_fst (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) {c : ℝ}
    (hc : c ∈ Icc (envD x β 0).1 (envB x α (π / 2)).1) :
    ∃ γ ∈ envCurve t₁ t₂ t₃ t₄ x α β, γ.1 = c := by
  obtain ⟨ht₁, ht₁₂, ht₂₃, ht₃₄, ht₄⟩ := h.ht
  have hD : uIcc (envD x β 0).1 (x t₄).1 ⊆ (fun t => (envD x β t).1) '' uIcc 0 t₂ := by
    rw [← h.D_t₂]
    refine intermediate_value_uIcc (((env_D_cont h).mono ?_).fst)
    rw [uIcc_of_le (by linarith)]; exact Icc_subset_Icc le_rfl (by linarith)
  have hx : uIcc (x t₄).1 (x t₁).1 ⊆ (fun t => (x t).1) '' uIcc t₄ t₁ := by
    refine intermediate_value_uIcc ((h.x_cont.mono ?_).fst)
    rw [uIcc_of_ge (by linarith)]; exact Icc_subset_Icc ht₁.le ht₄.le
  have hB : uIcc (x t₁).1 (envB x α (π / 2)).1 ⊆
      (fun t => (envB x α t).1) '' uIcc t₃ (π / 2) := by
    rw [← h.B_t₃]
    refine intermediate_value_uIcc (((env_B_cont h).mono ?_).fst)
    rw [uIcc_of_le (by linarith)]; exact Icc_subset_Icc (by linarith) le_rfl
  rcases uIcc_subset_uIcc_union_uIcc (b := (x t₄).1) (Icc_subset_uIcc hc) with hc' | hc'
  · obtain ⟨t, ht, hte⟩ := hD hc'
    rw [uIcc_of_le (by linarith)] at ht
    exact ⟨envD x β t, Or.inr ⟨t, ht, rfl⟩, hte⟩
  · rcases uIcc_subset_uIcc_union_uIcc (b := (x t₁).1) hc' with hc'' | hc''
    · obtain ⟨t, ht, hte⟩ := hx hc''
      rw [uIcc_of_ge (by linarith)] at ht
      exact ⟨x t, Or.inl (Or.inr ⟨t, ht, rfl⟩), hte⟩
    · obtain ⟨t, ht, hte⟩ := hB hc''
      rw [uIcc_of_le (by linarith)] at ht
      exact ⟨envB x α t, Or.inl (Or.inl ⟨t, ht, rfl⟩), hte⟩

/-- **The niche lies strictly under `Γ`.** -/
theorem env_niche_subset_strict (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) :
    envNiche x ⊆ envUnderStrict (envCurve t₁ t₂ t₃ t₄ x α β) := by
  obtain ⟨ht₁, ht₁₂, ht₂₃, ht₃₄, ht₄⟩ := h.ht
  rintro q ⟨hq2, hq⟩
  obtain ⟨s, hs, hqs⟩ := mem_iUnion₂.1 hq
  have hq2 : 0 ≤ q.2 := hq2
  refine ⟨hq2, ?_⟩
  have hπ := pi_pos
  by_cases hR : (envB x α (π / 2)).1 < q.1
  · exfalso
    obtain ⟨σ, hσ, hσ2, hd⟩ := env_wit_B h hs (τ := π / 2) ⟨by linarith, le_rfl⟩
    refine env_not_mem_of_dot hσ ?_ hqs
    rw [env_dot_shift q (envB x α (π / 2)) (x s) σ, h.B_end]
    have hc : 0 ≤ cos σ := cos_nonneg_of_mem_Icc ⟨by linarith [hσ.1, hs.1], hσ2⟩
    have hsn : 0 ≤ sin σ := sin_nonneg_of_nonneg_of_le_pi (by linarith [hσ.1, hs.1]) (by linarith)
    nlinarith [mul_nonneg (sub_pos.2 hR).le hc, mul_nonneg hq2 hsn]
  by_cases hL : q.1 < (envD x β 0).1
  · exfalso
    obtain ⟨σ, hσ, hσ2, hd⟩ := env_wit_D h hs (τ := 0) ⟨le_rfl, by linarith⟩
    refine env_not_mem_of_dot hσ ?_ hqs
    rw [env_dot_shift q (envD x β 0) (x s) σ, h.D_end]
    have hc : cos σ ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le hσ2 (by linarith [hσ.2, hs.2])
    have hsn : 0 ≤ sin σ :=
      sin_nonneg_of_nonneg_of_le_pi (by linarith [hσ.1, hs.1]) (by linarith [hσ.2, hs.2])
    nlinarith [mul_nonneg_of_nonpos_of_nonpos (sub_neg.2 hL).le hc, mul_nonneg hq2 hsn]
  push Not at hR hL
  obtain ⟨γ, hγ, hγ1⟩ := env_exists_curve_fst h ⟨hL, hR⟩
  refine ⟨γ, hγ, hγ1, ?_⟩
  by_contra hle
  push Not at hle
  obtain ⟨σ, hσ, hd⟩ := env_wit_curve h hs hγ
  refine env_not_mem_of_dot hσ ?_ hqs
  rw [env_dot_shift q γ (x s) σ, hγ1, sub_self, zero_mul, add_zero]
  have hsn : 0 ≤ sin σ :=
    sin_nonneg_of_nonneg_of_le_pi (by linarith [hσ.1, hs.1]) (by linarith [hσ.2, hs.2])
  nlinarith [mul_nonneg (sub_nonneg.2 hle) hsn]

/-- **The niche lies under `Γ`.** -/
theorem env_niche_subset (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) :
    envNiche x ⊆ envUnder (envCurve t₁ t₂ t₃ t₄ x α β) := fun q hq => by
  obtain ⟨h2, γ, hγ, h1, hlt⟩ := env_niche_subset_strict h hq
  exact ⟨h2, γ, hγ, h1, hlt.le⟩

/-- **The region strictly under `Γ` lies in the niche.** -/
theorem env_subset_niche (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) :
    envUnderStrict (envCurve t₁ t₂ t₃ t₄ x α β) ⊆ envNiche x := by
  obtain ⟨ht₁, ht₁₂, ht₂₃, ht₃₄, ht₄⟩ := h.ht
  rintro q ⟨hq2, γ, hγ, hγ1, hlt⟩
  refine ⟨hq2, mem_iUnion₂.2 ?_⟩
  have hπ := pi_pos
  have hb : q.2 - γ.2 < 0 := by linarith
  rcases hγ with (⟨τ, hτ, rfl⟩ | ⟨τ, hτ, rfl⟩) | ⟨τ, hτ, rfl⟩
  · rcases hτ.2.lt_or_eq with hτlt | hτe
    · have hτ' : τ ∈ Ioo 0 (π / 2) := ⟨by linarith [hτ.1], hτlt⟩
      have hc : 0 < cos τ := cos_pos_of_mem_Ioo ⟨by linarith [hτ'.1], hτ'.2⟩
      have hsn : 0 < sin τ := sin_pos_of_pos_of_lt_pi hτ'.1 (by linarith [hτ'.2])
      refine ⟨τ, hτ', ?_, ?_⟩
      · rw [env_dot_shift_snd _ _ hγ1, env_dot_B_self, uvec_snd]
        nlinarith [mul_neg_of_neg_of_pos hb hsn]
      · rw [env_dot_shift_snd _ _ hγ1, vvec_snd]
        have e : dot (envB x α τ - x τ) (vvec τ) = α τ := by
          simp [envB, dot_smul_left]
        rw [e]
        nlinarith [mul_neg_of_neg_of_pos hb hc, h.α_neg τ hτ']
    · subst hτe
      rw [h.B_end] at hlt
      linarith
  · have hτ' : τ ∈ Ioo 0 (π / 2) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hc : 0 < cos τ := cos_pos_of_mem_Ioo ⟨by linarith [hτ'.1], hτ'.2⟩
    have hsn : 0 < sin τ := sin_pos_of_pos_of_lt_pi hτ'.1 (by linarith [hτ'.2])
    refine ⟨τ, hτ', ?_, ?_⟩
    · rw [env_dot_shift_snd _ _ hγ1, sub_self, dot_zero_left, uvec_snd]
      nlinarith [mul_neg_of_neg_of_pos hb hsn]
    · rw [env_dot_shift_snd _ _ hγ1, sub_self, dot_zero_left, vvec_snd]
      nlinarith [mul_neg_of_neg_of_pos hb hc]
  · rcases hτ.1.lt_or_eq with hτlt | hτe
    · have hτ' : τ ∈ Ioo 0 (π / 2) := ⟨hτlt, by linarith [hτ.2]⟩
      have hc : 0 < cos τ := cos_pos_of_mem_Ioo ⟨by linarith [hτ'.1], hτ'.2⟩
      have hsn : 0 < sin τ := sin_pos_of_pos_of_lt_pi hτ'.1 (by linarith [hτ'.2])
      refine ⟨τ, hτ', ?_, ?_⟩
      · rw [env_dot_shift_snd _ _ hγ1, uvec_snd]
        have e : dot (envD x β τ - x τ) (uvec τ) = -β τ := by
          simp [envD, dot_neg_left, dot_smul_left]
        rw [e]
        nlinarith [mul_neg_of_neg_of_pos hb hsn, h.β_pos τ hτ']
      · rw [env_dot_shift_snd _ _ hγ1, env_dot_D_self, vvec_snd]
        nlinarith [mul_neg_of_neg_of_pos hb hc]
    · subst hτe
      rw [h.D_end] at hlt
      linarith

/-- The niche is exactly the region strictly under `Γ`. -/
theorem env_niche_eq (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) :
    envNiche x = envUnderStrict (envCurve t₁ t₂ t₃ t₄ x α β) :=
  (env_niche_subset_strict h).antisymm (env_subset_niche h)

/-! ### The curves lie on the boundary of the niche -/

/-- A point of `Γ` above the `x`-axis is in the closure of the niche. -/
lemma env_mem_closure_of_pos (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) {γ : ℝ × ℝ}
    (hγ : γ ∈ envCurve t₁ t₂ t₃ t₄ x α β) (hpos : 0 < γ.2) : γ ∈ closure (envNiche x) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hm : 0 < min (ε / 2) γ.2 := lt_min (half_pos hε) hpos
  refine ⟨(γ.1, γ.2 - min (ε / 2) γ.2), env_subset_niche h ⟨?_, γ, hγ, rfl, ?_⟩, ?_⟩
  · show 0 ≤ γ.2 - min (ε / 2) γ.2
    linarith [min_le_right (ε / 2) γ.2]
  · show γ.2 - min (ε / 2) γ.2 < γ.2
    linarith
  · rw [Prod.dist_eq]
    simp only [dist_self, Real.dist_eq]
    rw [show γ.2 - (γ.2 - min (ε / 2) γ.2) = min (ε / 2) γ.2 by ring, abs_of_pos hm,
      max_eq_right hm.le]
    exact (min_le_left _ _).trans_lt (half_lt_self hε)

/-- **The curves lie in the closure of the niche.** -/
theorem env_mem_closure (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) :
    (∀ τ ∈ Icc t₁ t₄, x τ ∈ closure (envNiche x)) ∧
      (∀ τ ∈ Icc t₃ (π / 2), envB x α τ ∈ closure (envNiche x)) ∧
      (∀ τ ∈ Icc 0 t₂, envD x β τ ∈ closure (envNiche x)) := by
  obtain ⟨ht₁, ht₁₂, ht₂₃, ht₃₄, ht₄⟩ := h.ht
  refine ⟨fun τ hτ => env_mem_closure_of_pos h (Or.inl (Or.inr ⟨τ, hτ, rfl⟩)) (h.x_pos τ hτ),
    ?_, ?_⟩
  · have hB : ∀ τ ∈ Ico t₃ (π / 2), envB x α τ ∈ closure (envNiche x) := fun τ hτ =>
      env_mem_closure_of_pos h (Or.inl (Or.inl ⟨τ, Ico_subset_Icc_self hτ, rfl⟩))
        (env_B₂_pos h hτ)
    intro τ hτ
    rcases hτ.2.lt_or_eq with hlt | rfl
    · exact hB τ ⟨hτ.1, hlt⟩
    · have hcw : ContinuousWithinAt (envB x α) (Ico t₃ (π / 2)) (π / 2) :=
        ((env_B_cont h) (π / 2) ⟨by linarith, le_rfl⟩).mono
          (fun t ht => ⟨by linarith [ht.1], ht.2.le⟩)
      have hmem : π / 2 ∈ closure (Ico t₃ (π / 2)) := by
        rw [closure_Ico (by linarith : t₃ ≠ π / 2)]; exact ⟨by linarith, le_rfl⟩
      have hsub : envB x α '' Ico t₃ (π / 2) ⊆ closure (envNiche x) := by
        rintro _ ⟨τ, hτ, rfl⟩; exact hB τ hτ
      exact closure_minimal hsub isClosed_closure (hcw.mem_closure_image hmem)
  · have hD : ∀ τ ∈ Ioc 0 t₂, envD x β τ ∈ closure (envNiche x) := fun τ hτ =>
      env_mem_closure_of_pos h (Or.inr ⟨τ, Ioc_subset_Icc_self hτ, rfl⟩) (env_D₂_pos h hτ)
    intro τ hτ
    rcases hτ.1.lt_or_eq with hlt | rfl
    · exact hD τ ⟨hlt, hτ.2⟩
    · have hcw : ContinuousWithinAt (envD x β) (Ioc 0 t₂) 0 :=
        ((env_D_cont h) 0 ⟨le_rfl, by linarith⟩).mono
          (fun t ht => ⟨ht.1.le, by linarith [ht.2]⟩)
      have hmem : (0 : ℝ) ∈ closure (Ioc 0 t₂) := by
        rw [closure_Ioc (by linarith : (0 : ℝ) ≠ t₂)]; exact ⟨le_rfl, by linarith⟩
      have hsub : envD x β '' Ioc 0 t₂ ⊆ closure (envNiche x) := by
        rintro _ ⟨τ, hτ, rfl⟩; exact hD τ hτ
      exact closure_minimal hsub isClosed_closure (hcw.mem_closure_image hmem)

end geometry

end MovingSofa
