module

public import MovingSofa.Optimality.Variation
public import MovingSofa.Gerver.Structure
public import MovingSofa.Gerver.Romik
public import MovingSofa.Gerver.Niche
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

/-!
# Gerver's sofa (§8.4)

Definitions 8.4.1 (`def:gerver-intervals`), 8.4.2–8.4.3 (the curves `𝐱, 𝐀, 𝐁, 𝐂, 𝐃`, in
`MovingSofa.Gerver.Defs`), 8.4.7 (`def:interval-j`); Theorems 8.4.1 (`thm:gerver-monotone`), 8.4.2
(`thm:gerver-odes`), 8.4.3 (`thm:gerver-left-right`), Proposition 8.4.4 (`pro:measure-translation`),
Theorems 8.4.5–8.4.6, and Theorem 6.1.2 (`thm:injectivity-gerver`).

Throughout, `P` is a solution of Romik's system in the box of `GerverParams.InBox`, `G` is
`gerverSofa P`, `K = 𝓒(G)` its cap, and `φ = P.φ`, `θ = P.θ`.

**Theorem 8.4.1.** The paper states it without proof (its Remark 8.4.1 notes that the properties are
verified numerically and assumed in the earlier literature). Part (2), that the niche is the region
enclosed by the curves `𝐁` (reversed), `𝐱|_{[t_1, t_4]}`, `𝐃` (reversed) and a segment of the `x`-axis,
is stated here as what the paper uses from it: the curves lie on the boundary of the niche, and the
area of the niche is `𝒥(𝐱|_{[t_1,t_4]}) - 𝒥(𝐁) - 𝒥(𝐃)`.

**Proofs of Theorems 8.4.3–8.4.6.** They follow the paper from Theorems 8.4.1–8.4.2 and 6.1.2. The
helper lemmas (prefix `gm_`) establish that Gerver's rotation path is `C¹` (from the matching
conditions of Romik's system), that `𝐃(t)` (resp. `𝐁(t)`) lies on the supporting line of `D_K` at
`3π/2 + t` (resp. of `B_K` at `π + t`), and that `D_K` (resp. `B_K`) has a single vertex `𝐱_K^L`
(resp. `𝐱_K^R`) between these angles and `3π/2 + φ^L` (resp. `π + φ^R`). The surface area measures
are computed on intervals from the distribution function `sigmaFun` and the fundamental theorem of
calculus, and the curve areas `𝒥(𝐁)`, `𝒥(𝐃)` from the piecewise `C¹` parametrizations.
-/

@[expose] public section

open Real Set MeasureTheory

namespace MovingSofa

namespace GerverParams

variable (P : GerverParams)

/-- The partition `(t_0, …, t_5) = (0, φ, θ, π/2 - θ, π/2 - φ, π/2)` (Definition 8.4.1). -/
noncomputable def tPt : ℕ → ℝ
  | 0 => 0
  | 1 => P.φ
  | 2 => P.θ
  | 3 => π / 2 - P.θ
  | 4 => π / 2 - P.φ
  | _ => π / 2

/-- The cap `K = 𝓒(G)` of Gerver's sofa. -/
def cap : Set (ℝ × ℝ) := capOf (gerverSofa P) (π / 2)

/-- The contact path `𝐀` of Gerver's rotation path (Definition 8.4.3). -/
noncomputable def curveA (t : ℝ) : ℝ × ℝ := contactA P.path t
/-- The contact path `𝐁` on `[t_3, t_5]` (Definition 8.4.3). -/
noncomputable def curveB (t : ℝ) : ℝ × ℝ := contactB P.path t
/-- The contact path `𝐂` (Definition 8.4.3). -/
noncomputable def curveC (t : ℝ) : ℝ × ℝ := contactC P.path t
/-- The contact path `𝐃` on `[t_0, t_2]` (Definition 8.4.3). -/
noncomputable def curveD (t : ℝ) : ℝ × ℝ := contactD P.path t

end GerverParams

open GerverParams

/-- **Theorem 8.4.1** (`thm:gerver-monotone`): Gerver's sofa is a monotone sofa, and (1) its cap has
vertices `A_K(t) = 𝐀(t)`, `C_K(t) = 𝐂(t)` and inner corner `𝐱_K(t) = 𝐱(t)` for `t ∈ [0, π/2]`. -/
theorem theorem8_4_1_monotone {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    IsMonotoneSofa (gerverSofa P) (π / 2) ∧
      ∀ t ∈ Icc 0 (π / 2), aK P.cap t = P.curveA t ∧ cK P.cap t = P.curveC t ∧
        innerCorner P.cap t = P.path t := by
  have h := gv_monotone hP (GerverParams.romik_bounds hP hbox)
  exact ⟨h.1, fun t ht => h.2 t ht⟩

/-- **Theorem 8.4.1** (2), as used by the paper (see the module docstring): the curves `𝐁`,
`𝐱|_{[t_1, t_4]}`, `𝐃` lie on the boundary of the niche, with matching endpoints
`𝐁(t_3) = 𝐱(t_1)` and `𝐱(t_4) = 𝐃(t_2)`, `𝐃(t_0)` and `𝐁(t_5)` on the `x`-axis, and
`|𝒩(K)| = 𝒥(𝐱|_{[t_1, t_4]}) - 𝒥(𝐁|_{[t_3, t_5]}) - 𝒥(𝐃|_{[t_0, t_2]})`. -/
theorem theorem8_4_1_niche {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (∀ t ∈ Icc (P.tPt 3) (P.tPt 5), P.curveB t ∈ closure (niche P.cap (π / 2)) \ niche P.cap (π / 2)) ∧
      (∀ t ∈ Icc (P.tPt 1) (P.tPt 4), P.path t ∈ closure (niche P.cap (π / 2)) \ niche P.cap (π / 2)) ∧
      (∀ t ∈ Icc (P.tPt 0) (P.tPt 2), P.curveD t ∈ closure (niche P.cap (π / 2)) \ niche P.cap (π / 2)) ∧
      P.curveB (P.tPt 3) = P.path (P.tPt 1) ∧ P.path (P.tPt 4) = P.curveD (P.tPt 2) ∧
      (P.curveD (P.tPt 0)).2 = 0 ∧ (P.curveB (P.tPt 5)).2 = 0 ∧
      area (niche P.cap (π / 2)) = curveArea P.path (P.tPt 1) (P.tPt 4) -
        curveArea P.curveB (P.tPt 3) (P.tPt 5) - curveArea P.curveD (P.tPt 0) (P.tPt 2) := by
  have h := gv_niche hP (GerverParams.romik_bounds hP hbox)
  simp only [GerverParams.tPt]
  exact h

/-- **Theorem 8.4.1** (3): `b⃗_K(t)` passes through `𝐁(t)` for `t ∈ [t_3, t_5]`, and `d⃗_K(t)` through
`𝐃(t)` for `t ∈ [t_0, t_2]`. -/
theorem theorem8_4_1_walls {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (∀ t ∈ Icc (P.tPt 3) (P.tPt 5), P.curveB t ∈ wallBVec P.cap t) ∧
      ∀ t ∈ Icc (P.tPt 0) (P.tPt 2), P.curveD t ∈ wallDVec P.cap t := by
  have h := gv_walls hP (GerverParams.romik_bounds hP hbox)
  simp only [GerverParams.tPt]
  exact h

/-- **Theorem 8.4.1** (4): `𝐁'(t)` is a negative multiple of `v_t` and `𝐃'(t)` a positive multiple of
`u_t`, on the open phases where these curves are differentiable. -/
theorem theorem8_4_1_tangents {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (∀ t ∈ Ioo (P.tPt 3) (P.tPt 5), t ≠ P.tPt 4 →
        ∃ c < (0 : ℝ), HasDerivAt P.curveB (c • vvec t) t) ∧
      ∀ t ∈ Ioo (P.tPt 0) (P.tPt 2), t ≠ P.tPt 1 →
        ∃ c > (0 : ℝ), HasDerivAt P.curveD (c • uvec t) t := by
  have h := gv_tangents hP (GerverParams.romik_bounds hP hbox)
  simp only [GerverParams.tPt]
  exact h

/-- **Theorem 8.4.2** (`thm:gerver-odes`): Romik's balancing ODEs on the open phases. -/
theorem theorem8_4_2 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (∀ t ∈ Ioo (P.tPt 0) (P.tPt 1),
        dot (deriv P.curveA t) (vvec t) = 0 ∧
        dot (-deriv P.curveC t) (uvec t) = dot (deriv P.curveD t) (uvec t)) ∧
      (∀ t ∈ Ioo (P.tPt 1) (P.tPt 2),
        dot (deriv P.curveA t) (vvec t) = dot (deriv P.path t) (vvec t) ∧
        dot (-deriv P.curveC t) (uvec t) = dot (deriv P.curveD t - deriv P.path t) (uvec t)) ∧
      (∀ t ∈ Ioo (P.tPt 2) (P.tPt 3),
        dot (deriv P.curveA t) (vvec t) = dot (deriv P.path t) (vvec t) ∧
        dot (-deriv P.curveC t) (uvec t) = dot (-deriv P.path t) (uvec t)) ∧
      (∀ t ∈ Ioo (P.tPt 3) (P.tPt 4),
        dot (deriv P.curveA t) (vvec t) = dot (-deriv P.curveB t + deriv P.path t) (vvec t) ∧
        dot (-deriv P.curveC t) (uvec t) = dot (-deriv P.path t) (uvec t)) ∧
      (∀ t ∈ Ioo (P.tPt 4) (P.tPt 5),
        dot (deriv P.curveA t) (vvec t) = dot (-deriv P.curveB t) (vvec t) ∧
        dot (-deriv P.curveC t) (uvec t) = 0) := by
  have h := gv_odes hP (GerverParams.romik_bounds hP hbox)
  simp only [GerverParams.tPt]
  exact h

/-- **Theorem 6.1.2** (`thm:injectivity-gerver`). The cap of Gerver's sofa satisfies the injectivity
condition. -/
theorem theorem6_1_2 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    SatisfiesInjectivity P.cap := by
  exact gv_injectivity hP (GerverParams.romik_bounds hP hbox)

/-- Gerver's sofa has area at least `2.2` (its area is `2.2195…`; Romik, Section 8 of the companion
package). -/
theorem gerverSofa_area {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    2.2 ≤ area (gerverSofa P) := by
  exact gv_area hP (GerverParams.romik_bounds hP hbox)

open Filter Topology
open scoped ContDiff ENNReal Interval


/-! ### Regularity of Gerver's rotation path -/

/-- A function glued from five pieces with matching values at the junctions is continuous. -/
lemma gm_continuous_pw5 {E : Type*} [TopologicalSpace E] {a b c d : ℝ}
    {f₁ f₂ f₃ f₄ f₅ : ℝ → E} (h₁ : Continuous f₁) (h₂ : Continuous f₂) (h₃ : Continuous f₃)
    (h₄ : Continuous f₄) (h₅ : Continuous f₅) (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (e₁ : f₁ a = f₂ a) (e₂ : f₂ b = f₃ b) (e₃ : f₃ c = f₄ c) (e₄ : f₄ d = f₅ d) :
    Continuous (fun t => if t < a then f₁ t else if t < b then f₂ t else if t ≤ c then f₃ t
      else if t ≤ d then f₄ t else f₅ t) := by
  have H4 : Continuous (fun t => if t ≤ d then f₄ t else f₅ t) :=
    continuous_if_le continuous_id continuous_const h₄.continuousOn h₅.continuousOn
      (fun x hx => by
        have hx' : x = d := hx
        rw [hx', e₄])
  have H3 : Continuous (fun t => if t ≤ c then f₃ t else if t ≤ d then f₄ t else f₅ t) :=
    continuous_if_le continuous_id continuous_const h₃.continuousOn H4.continuousOn
      (fun x hx => by
        have hx' : x = c := hx
        rw [hx', ite_eq_left hcd.le, e₃])
  have H2 : Continuous (fun t => if t < b then f₂ t else if t ≤ c then f₃ t else
      if t ≤ d then f₄ t else f₅ t) := by
    have : (fun t => if t < b then f₂ t else if t ≤ c then f₃ t else
        if t ≤ d then f₄ t else f₅ t) = (fun t => if b ≤ t then
          (if t ≤ c then f₃ t else if t ≤ d then f₄ t else f₅ t) else f₂ t) := by
      funext t; by_cases h : b ≤ t
      · rw [ite_eq_right (not_lt.2 h), ite_eq_left h]
      · rw [ite_eq_left (not_le.1 h), ite_eq_right h]
    rw [this]
    exact continuous_if_le continuous_const continuous_id H3.continuousOn h₂.continuousOn
      (fun x hx => by
        have hx' : b = x := hx
        rw [← hx', ite_eq_left hbc, e₂])
  have : (fun t => if t < a then f₁ t else if t < b then f₂ t else if t ≤ c then f₃ t
      else if t ≤ d then f₄ t else f₅ t) = (fun t => if a ≤ t then
        (if t < b then f₂ t else if t ≤ c then f₃ t else if t ≤ d then f₄ t else f₅ t)
        else f₁ t) := by
    funext t; by_cases h : a ≤ t
    · rw [ite_eq_right (not_lt.2 h), ite_eq_left h]
    · rw [ite_eq_left (not_le.1 h), ite_eq_right h]
  rw [this]
  exact continuous_if_le continuous_const continuous_id H2.continuousOn h₁.continuousOn
    (fun x hx => by
      have hx' : a = x := hx
      rw [← hx', ite_eq_left hab, e₁])

/-- Gluing two one-sided derivatives. -/
lemma gm_hasDerivAt_glue {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g h : ℝ → E} {a : ℝ} {e : E} (hg : HasDerivAt g e a) (hh : HasDerivAt h e a)
    (hfg : ∀ᶠ t in 𝓝[≤] a, f t = g t) (hfh : ∀ᶠ t in 𝓝[≥] a, f t = h t) : HasDerivAt f e a := by
  have ha : f a = g a := hfg.self_of_nhdsWithin self_mem_Iic
  have ha' : f a = h a := hfh.self_of_nhdsWithin self_mem_Ici
  have A : HasDerivWithinAt f e (Iic a) a := hg.hasDerivWithinAt.congr_of_eventuallyEq hfg ha
  have B : HasDerivWithinAt f e (Ici a) a := hh.hasDerivWithinAt.congr_of_eventuallyEq hfh ha'
  have := A.union B
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this

namespace GerverParams

variable {P : GerverParams}

lemma gm_contDiff_x₁ (P : GerverParams) : ContDiff ℝ ∞ P.x₁ := by unfold x₁ rot; fun_prop
lemma gm_contDiff_x₂ (P : GerverParams) : ContDiff ℝ ∞ P.x₂ := by unfold x₂ rot; fun_prop
lemma gm_contDiff_x₃ (P : GerverParams) : ContDiff ℝ ∞ P.x₃ := by unfold x₃ rot; fun_prop
lemma gm_contDiff_x₄ (P : GerverParams) : ContDiff ℝ ∞ P.x₄ := by unfold x₄ rot; fun_prop
lemma gm_contDiff_x₅ (P : GerverParams) : ContDiff ℝ ∞ P.x₅ := by unfold x₅ rot; fun_prop

section
variable (hP : P.IsSolution)
include hP

lemma gm_φ_pos : 0 < P.φ := hP.1
lemma gm_φ_lt_θ : P.φ < P.θ := hP.2.1
lemma gm_θ_lt : P.θ < π / 4 := hP.2.2.1

lemma gm_e₁ : P.x₁ P.φ = P.x₂ P.φ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hP; exact h
lemma gm_e₁' : deriv P.x₁ P.φ = deriv P.x₂ P.φ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hP; exact h
lemma gm_e₂ : P.x₂ P.θ = P.x₃ P.θ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hP; exact h
lemma gm_e₂' : deriv P.x₂ P.θ = deriv P.x₃ P.θ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hP; exact h
lemma gm_e₃ : P.x₃ (π / 2 - P.θ) = P.x₄ (π / 2 - P.θ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hP; exact h
lemma gm_e₃' : deriv P.x₃ (π / 2 - P.θ) = deriv P.x₄ (π / 2 - P.θ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hP; exact h
lemma gm_e₄ : P.x₄ (π / 2 - P.φ) = P.x₅ (π / 2 - P.φ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hP; exact h
lemma gm_e₄' : deriv P.x₄ (π / 2 - P.φ) = deriv P.x₅ (π / 2 - P.φ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hP; exact h

lemma gm_θ_lt_c : P.θ < π / 2 - P.θ := by have := gm_θ_lt hP; linarith
lemma gm_c_lt_d : π / 2 - P.θ < π / 2 - P.φ := by have := gm_φ_lt_θ hP; linarith
lemma gm_d_lt : π / 2 - P.φ < π / 2 := by have := gm_φ_pos hP; linarith

lemma gm_path_eq_x₁ {t : ℝ} (ht : t ≤ P.φ) : P.path t = P.x₁ t := by
  unfold path
  rcases ht.lt_or_eq with h | rfl
  · rw [ite_eq_left h]
  · rw [ite_eq_right (lt_irrefl _), ite_eq_left (gm_φ_lt_θ hP)]
    exact (gm_e₁ hP).symm

lemma gm_path_eq_x₂ {t : ℝ} (ht : t ∈ Icc P.φ P.θ) : P.path t = P.x₂ t := by
  unfold path
  rw [ite_eq_right (not_lt.2 ht.1)]
  rcases ht.2.lt_or_eq with h | rfl
  · rw [ite_eq_left h]
  · rw [ite_eq_right (lt_irrefl _), ite_eq_left (gm_θ_lt_c hP).le]
    exact (gm_e₂ hP).symm

lemma gm_path_eq_x₃ {t : ℝ} (ht : t ∈ Icc P.θ (π / 2 - P.θ)) : P.path t = P.x₃ t := by
  unfold path
  have h1 : ¬ t < P.φ := not_lt.2 ((gm_φ_lt_θ hP).le.trans ht.1)
  rw [ite_eq_right h1, ite_eq_right (not_lt.2 ht.1), ite_eq_left ht.2]

lemma gm_path_eq_x₄ {t : ℝ} (ht : t ∈ Icc (π / 2 - P.θ) (π / 2 - P.φ)) : P.path t = P.x₄ t := by
  unfold path
  have h0 := gm_θ_lt_c hP
  have h1 : ¬ t < P.φ := not_lt.2 (by linarith [ht.1, gm_φ_lt_θ hP])
  have h2 : ¬ t < P.θ := not_lt.2 (by linarith [ht.1])
  rw [ite_eq_right h1, ite_eq_right h2]
  rcases ht.1.lt_or_eq with h | h
  · rw [ite_eq_right (not_le.2 h), ite_eq_left ht.2]
  · rw [← h, ite_eq_left le_rfl]
    exact gm_e₃ hP

lemma gm_path_eq_x₅ {t : ℝ} (ht : π / 2 - P.φ ≤ t) : P.path t = P.x₅ t := by
  unfold path
  have h1 : ¬ t < P.φ := not_lt.2 (by linarith [gm_φ_lt_θ hP, gm_c_lt_d hP, gm_θ_lt_c hP])
  have h2 : ¬ t < P.θ := not_lt.2 (by linarith [gm_c_lt_d hP, gm_θ_lt_c hP])
  have h3 : ¬ t ≤ π / 2 - P.θ := not_le.2 (by linarith [gm_c_lt_d hP])
  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
  rcases ht.lt_or_eq with h | h
  · rw [ite_eq_right (not_le.2 h)]
  · rw [← h, ite_eq_left le_rfl]
    exact gm_e₄ hP

end


lemma gm_hasDerivAt_x₁ (t : ℝ) : HasDerivAt P.x₁ (deriv P.x₁ t) t :=
  ((P.gm_contDiff_x₁.differentiable (by simp)) t).hasDerivAt
lemma gm_hasDerivAt_x₂ (t : ℝ) : HasDerivAt P.x₂ (deriv P.x₂ t) t :=
  ((P.gm_contDiff_x₂.differentiable (by simp)) t).hasDerivAt
lemma gm_hasDerivAt_x₃ (t : ℝ) : HasDerivAt P.x₃ (deriv P.x₃ t) t :=
  ((P.gm_contDiff_x₃.differentiable (by simp)) t).hasDerivAt
lemma gm_hasDerivAt_x₄ (t : ℝ) : HasDerivAt P.x₄ (deriv P.x₄ t) t :=
  ((P.gm_contDiff_x₄.differentiable (by simp)) t).hasDerivAt
lemma gm_hasDerivAt_x₅ (t : ℝ) : HasDerivAt P.x₅ (deriv P.x₅ t) t :=
  ((P.gm_contDiff_x₅.differentiable (by simp)) t).hasDerivAt

/-- The derivative of Gerver's rotation path, glued from the derivatives of the five pieces. -/
noncomputable def gm_dpath (P : GerverParams) (t : ℝ) : ℝ × ℝ :=
  if t < P.φ then deriv P.x₁ t else if t < P.θ then deriv P.x₂ t else
    if t ≤ π / 2 - P.θ then deriv P.x₃ t else if t ≤ π / 2 - P.φ then deriv P.x₄ t
    else deriv P.x₅ t

section
variable (hP : P.IsSolution)
include hP

lemma gm_hasDerivAt_path (t : ℝ) : HasDerivAt P.path (P.gm_dpath t) t := by
  have h01 := gm_φ_lt_θ hP
  have h12 := gm_θ_lt_c hP
  have h23 := gm_c_lt_d hP
  unfold gm_dpath
  rcases lt_trichotomy t P.φ with h | rfl | h
  · rw [ite_eq_left h]
    exact (gm_hasDerivAt_x₁ t).congr_of_eventuallyEq
      (eventually_of_mem (Iio_mem_nhds h) (fun s hs => gm_path_eq_x₁ hP (le_of_lt hs)))
  · rw [ite_eq_right (lt_irrefl _), ite_eq_left h01]
    refine gm_hasDerivAt_glue (g := P.x₁) ((gm_e₁' hP) ▸ gm_hasDerivAt_x₁ _)
      (gm_hasDerivAt_x₂ _) ?_ ?_
    · exact eventually_nhdsWithin_of_forall (fun s hs => gm_path_eq_x₁ hP hs)
    · exact eventually_of_mem (Icc_mem_nhdsGE h01) (fun s hs => gm_path_eq_x₂ hP hs)
  rw [ite_eq_right (not_lt.2 h.le)]
  rcases lt_trichotomy t P.θ with h1 | rfl | h1
  · rw [ite_eq_left h1]
    exact (gm_hasDerivAt_x₂ t).congr_of_eventuallyEq
      (eventually_of_mem (Ioo_mem_nhds h h1) (fun s hs => gm_path_eq_x₂ hP ⟨hs.1.le, hs.2.le⟩))
  · rw [ite_eq_right (lt_irrefl _), ite_eq_left h12.le]
    refine gm_hasDerivAt_glue (g := P.x₂) ((gm_e₂' hP) ▸ gm_hasDerivAt_x₂ _)
      (gm_hasDerivAt_x₃ _) ?_ ?_
    · exact eventually_of_mem (Icc_mem_nhdsLE h) (fun s hs => gm_path_eq_x₂ hP hs)
    · exact eventually_of_mem (Icc_mem_nhdsGE h12) (fun s hs => gm_path_eq_x₃ hP hs)
  rw [ite_eq_right (not_lt.2 h1.le)]
  rcases lt_trichotomy t (π / 2 - P.θ) with h2 | h2 | h2
  · rw [ite_eq_left h2.le]
    exact (gm_hasDerivAt_x₃ t).congr_of_eventuallyEq
      (eventually_of_mem (Ioo_mem_nhds h1 h2) (fun s hs => gm_path_eq_x₃ hP ⟨hs.1.le, hs.2.le⟩))
  · subst h2
    rw [ite_eq_left le_rfl]
    refine gm_hasDerivAt_glue (g := P.x₃) (gm_hasDerivAt_x₃ _)
      ((gm_e₃' hP) ▸ gm_hasDerivAt_x₄ _) ?_ ?_
    · exact eventually_of_mem (Icc_mem_nhdsLE h1) (fun s hs => gm_path_eq_x₃ hP hs)
    · exact eventually_of_mem (Icc_mem_nhdsGE h23) (fun s hs => gm_path_eq_x₄ hP hs)
  rw [ite_eq_right (not_le.2 h2)]
  rcases lt_trichotomy t (π / 2 - P.φ) with h3 | h3 | h3
  · rw [ite_eq_left h3.le]
    exact (gm_hasDerivAt_x₄ t).congr_of_eventuallyEq
      (eventually_of_mem (Ioo_mem_nhds h2 h3) (fun s hs => gm_path_eq_x₄ hP ⟨hs.1.le, hs.2.le⟩))
  · subst h3
    rw [ite_eq_left le_rfl]
    refine gm_hasDerivAt_glue (g := P.x₄) (gm_hasDerivAt_x₄ _)
      ((gm_e₄' hP) ▸ gm_hasDerivAt_x₅ _) ?_ ?_
    · exact eventually_of_mem (Icc_mem_nhdsLE h2) (fun s hs => gm_path_eq_x₄ hP hs)
    · exact eventually_nhdsWithin_of_forall (fun s hs => gm_path_eq_x₅ hP hs)
  · rw [ite_eq_right (not_le.2 h3)]
    exact (gm_hasDerivAt_x₅ t).congr_of_eventuallyEq
      (eventually_of_mem (Ioi_mem_nhds h3) (fun s hs => gm_path_eq_x₅ hP (le_of_lt hs)))

lemma gm_deriv_path : deriv P.path = P.gm_dpath :=
  funext fun t => (gm_hasDerivAt_path hP t).deriv

lemma gm_continuous_dpath : Continuous P.gm_dpath :=
  gm_continuous_pw5 (P.gm_contDiff_x₁.continuous_deriv (by simp))
    (P.gm_contDiff_x₂.continuous_deriv (by simp)) (P.gm_contDiff_x₃.continuous_deriv (by simp))
    (P.gm_contDiff_x₄.continuous_deriv (by simp)) (P.gm_contDiff_x₅.continuous_deriv (by simp))
    (gm_φ_lt_θ hP) (gm_θ_lt_c hP).le (gm_c_lt_d hP) (gm_e₁' hP) (gm_e₂' hP) (gm_e₃' hP)
    (gm_e₄' hP)

lemma gm_differentiable_path : Differentiable ℝ P.path :=
  fun t => (gm_hasDerivAt_path hP t).differentiableAt

lemma gm_continuous_path : Continuous P.path := (gm_differentiable_path hP).continuous

lemma gm_continuous_deriv_path : Continuous (deriv P.path) :=
  (gm_deriv_path hP) ▸ gm_continuous_dpath hP

lemma gm_contDiff_path : ContDiff ℝ 1 P.path :=
  contDiff_one_iff_deriv.2 ⟨gm_differentiable_path hP, gm_continuous_deriv_path hP⟩

end

end GerverParams

/-! ### The contact curves -/

/-- A pointwise operator on curves depending on the value and the derivative. -/
lemma gm_op_eventuallyEq {x y : ℝ → ℝ × ℝ} {t : ℝ} (h : x =ᶠ[𝓝 t] y)
    (F : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ × ℝ) :
    (fun s => F s (x s) (deriv x s)) =ᶠ[𝓝 t] (fun s => F s (y s) (deriv y s)) := by
  filter_upwards [h, h.deriv] with s h1 h2
  rw [h1, h2]

lemma gm_contDiff_contactA {x : ℝ → ℝ × ℝ} (hx : ContDiff ℝ 2 x) :
    ContDiff ℝ 1 (GerverParams.contactA x) := by
  have hx1 : ContDiff ℝ 1 x := hx.of_le (by norm_num)
  have hdx : ContDiff ℝ 1 (deriv x) := hx.deriv'
  unfold GerverParams.contactA dot uvec vvec
  fun_prop

lemma gm_contDiff_contactB {x : ℝ → ℝ × ℝ} (hx : ContDiff ℝ 2 x) :
    ContDiff ℝ 1 (GerverParams.contactB x) := by
  have hx1 : ContDiff ℝ 1 x := hx.of_le (by norm_num)
  have hdx : ContDiff ℝ 1 (deriv x) := hx.deriv'
  unfold GerverParams.contactB dot uvec vvec
  fun_prop

lemma gm_contDiff_contactC {x : ℝ → ℝ × ℝ} (hx : ContDiff ℝ 2 x) :
    ContDiff ℝ 1 (GerverParams.contactC x) := by
  have hx1 : ContDiff ℝ 1 x := hx.of_le (by norm_num)
  have hdx : ContDiff ℝ 1 (deriv x) := hx.deriv'
  unfold GerverParams.contactC dot uvec vvec
  fun_prop

lemma gm_contDiff_contactD {x : ℝ → ℝ × ℝ} (hx : ContDiff ℝ 2 x) :
    ContDiff ℝ 1 (GerverParams.contactD x) := by
  have hx1 : ContDiff ℝ 1 x := hx.of_le (by norm_num)
  have hdx : ContDiff ℝ 1 (deriv x) := hx.deriv'
  unfold GerverParams.contactD dot uvec vvec
  fun_prop

namespace GerverParams

variable {P : GerverParams}

section
variable (hP : P.IsSolution)
include hP

lemma gm_dpath_eq_x₁ {t : ℝ} (ht : t ≤ P.φ) : deriv P.path t = deriv P.x₁ t := by
  rw [gm_deriv_path hP]; unfold gm_dpath
  rcases ht.lt_or_eq with h | rfl
  · rw [ite_eq_left h]
  · rw [ite_eq_right (lt_irrefl _), ite_eq_left (gm_φ_lt_θ hP)]
    exact (gm_e₁' hP).symm

lemma gm_dpath_eq_x₂ {t : ℝ} (ht : t ∈ Icc P.φ P.θ) : deriv P.path t = deriv P.x₂ t := by
  rw [gm_deriv_path hP]; unfold gm_dpath
  rw [ite_eq_right (not_lt.2 ht.1)]
  rcases ht.2.lt_or_eq with h | rfl
  · rw [ite_eq_left h]
  · rw [ite_eq_right (lt_irrefl _), ite_eq_left (gm_θ_lt_c hP).le]
    exact (gm_e₂' hP).symm

lemma gm_dpath_eq_x₃ {t : ℝ} (ht : t ∈ Icc P.θ (π / 2 - P.θ)) :
    deriv P.path t = deriv P.x₃ t := by
  rw [gm_deriv_path hP]; unfold gm_dpath
  have h1 : ¬ t < P.φ := not_lt.2 ((gm_φ_lt_θ hP).le.trans ht.1)
  rw [ite_eq_right h1, ite_eq_right (not_lt.2 ht.1), ite_eq_left ht.2]

lemma gm_dpath_eq_x₄ {t : ℝ} (ht : t ∈ Icc (π / 2 - P.θ) (π / 2 - P.φ)) :
    deriv P.path t = deriv P.x₄ t := by
  rw [gm_deriv_path hP]; unfold gm_dpath
  have h0 := gm_θ_lt_c hP
  have h1 : ¬ t < P.φ := not_lt.2 (by linarith [ht.1, gm_φ_lt_θ hP])
  have h2 : ¬ t < P.θ := not_lt.2 (by linarith [ht.1])
  rw [ite_eq_right h1, ite_eq_right h2]
  rcases ht.1.lt_or_eq with h | h
  · rw [ite_eq_right (not_le.2 h), ite_eq_left ht.2]
  · rw [← h, ite_eq_left le_rfl]
    exact gm_e₃' hP

lemma gm_dpath_eq_x₅ {t : ℝ} (ht : π / 2 - P.φ ≤ t) : deriv P.path t = deriv P.x₅ t := by
  rw [gm_deriv_path hP]; unfold gm_dpath
  have h1 : ¬ t < P.φ := not_lt.2 (by linarith [gm_φ_lt_θ hP, gm_c_lt_d hP, gm_θ_lt_c hP])
  have h2 : ¬ t < P.θ := not_lt.2 (by linarith [gm_c_lt_d hP, gm_θ_lt_c hP])
  have h3 : ¬ t ≤ π / 2 - P.θ := not_le.2 (by linarith [gm_c_lt_d hP])
  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
  rcases ht.lt_or_eq with h | h
  · rw [ite_eq_right (not_le.2 h)]
  · rw [← h, ite_eq_left le_rfl]
    exact gm_e₄' hP

/-- Away from the junctions, the rotation path is locally one of the smooth pieces. -/
lemma gm_path_locally {t : ℝ}
    (ht : t ∉ ({P.φ, P.θ, π / 2 - P.θ, π / 2 - P.φ} : Set ℝ)) :
    ∃ y : ℝ → ℝ × ℝ, ContDiff ℝ ∞ y ∧ P.path =ᶠ[𝓝 t] y := by
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at ht
  obtain ⟨h1, h2, h3, h4⟩ := ht
  rcases lt_or_gt_of_ne h1 with h1 | h1
  · exact ⟨P.x₁, P.gm_contDiff_x₁,
      eventually_of_mem (Iio_mem_nhds h1) (fun s hs => gm_path_eq_x₁ hP (le_of_lt hs))⟩
  rcases lt_or_gt_of_ne h2 with h2 | h2
  · exact ⟨P.x₂, P.gm_contDiff_x₂, eventually_of_mem (Ioo_mem_nhds h1 h2)
      (fun s hs => gm_path_eq_x₂ hP ⟨hs.1.le, hs.2.le⟩)⟩
  rcases lt_or_gt_of_ne h3 with h3 | h3
  · exact ⟨P.x₃, P.gm_contDiff_x₃, eventually_of_mem (Ioo_mem_nhds h2 h3)
      (fun s hs => gm_path_eq_x₃ hP ⟨hs.1.le, hs.2.le⟩)⟩
  rcases lt_or_gt_of_ne h4 with h4 | h4
  · exact ⟨P.x₄, P.gm_contDiff_x₄, eventually_of_mem (Ioo_mem_nhds h3 h4)
      (fun s hs => gm_path_eq_x₄ hP ⟨hs.1.le, hs.2.le⟩)⟩
  · exact ⟨P.x₅, P.gm_contDiff_x₅,
      eventually_of_mem (Ioi_mem_nhds h4) (fun s hs => gm_path_eq_x₅ hP (le_of_lt hs))⟩

omit hP in
lemma gm_junctions_countable :
    ({P.φ, P.θ, π / 2 - P.θ, π / 2 - P.φ} : Set ℝ).Countable :=
  (Set.toFinite _).countable

lemma gm_continuous_curveA : Continuous P.curveA := by
  have h1 := gm_continuous_path hP
  have h2 := gm_continuous_deriv_path hP
  unfold curveA contactA dot uvec vvec
  fun_prop

lemma gm_continuous_curveB : Continuous P.curveB := by
  have h1 := gm_continuous_path hP
  have h2 := gm_continuous_deriv_path hP
  unfold curveB contactB dot uvec vvec
  fun_prop

lemma gm_continuous_curveC : Continuous P.curveC := by
  have h1 := gm_continuous_path hP
  have h2 := gm_continuous_deriv_path hP
  unfold curveC contactC dot uvec vvec
  fun_prop

lemma gm_continuous_curveD : Continuous P.curveD := by
  have h1 := gm_continuous_path hP
  have h2 := gm_continuous_deriv_path hP
  unfold curveD contactD dot uvec vvec
  fun_prop

lemma gm_differentiableAt_curveA {t : ℝ}
    (ht : t ∉ ({P.φ, P.θ, π / 2 - P.θ, π / 2 - P.φ} : Set ℝ)) :
    DifferentiableAt ℝ P.curveA t := by
  obtain ⟨y, hy, hpy⟩ := gm_path_locally hP ht
  have := gm_op_eventuallyEq hpy (fun s p q => p + dot q (uvec s) • vvec s + uvec s)
  exact ((gm_contDiff_contactA (hy.of_le (by simp))).differentiable (by simp)
    t).congr_of_eventuallyEq this

lemma gm_differentiableAt_curveC {t : ℝ}
    (ht : t ∉ ({P.φ, P.θ, π / 2 - P.θ, π / 2 - P.φ} : Set ℝ)) :
    DifferentiableAt ℝ P.curveC t := by
  obtain ⟨y, hy, hpy⟩ := gm_path_locally hP ht
  have := gm_op_eventuallyEq hpy (fun s p q => p - dot q (vvec s) • uvec s + vvec s)
  exact ((gm_contDiff_contactC (hy.of_le (by simp))).differentiable (by simp)
    t).congr_of_eventuallyEq this

end

end GerverParams

/-! ### Convex geometry helpers -/

lemma gm_isClosed_halfPlus (t h : ℝ) : IsClosed (halfPlus t h) :=
  isClosed_le continuous_const (by unfold dot; fun_prop)

lemma gm_convex_halfPlus (t h : ℝ) : Convex ℝ (halfPlus t h) := by
  have : IsLinearMap ℝ (fun p : ℝ × ℝ => dot p (uvec t)) :=
    ⟨fun p q => dot_add_left p q _, fun c p => dot_smul_left c p _⟩
  exact convex_halfSpace_ge this h

lemma gm_isClosed_fan (w : ℝ) : IsClosed (fan w) :=
  (gm_isClosed_halfPlus _ _).inter (gm_isClosed_halfPlus _ _)

lemma gm_mem_edge_iff {C : Set (ℝ × ℝ)} {t : ℝ} {p : ℝ × ℝ} :
    p ∈ edge C t ↔ p ∈ C ∧ dot p (uvec t) = supp C t := Iff.rfl

/-- The support function at an attained maximum. -/
lemma gm_supp_eq_of_max {C : Set (ℝ × ℝ)} {q : ℝ × ℝ} (hq : q ∈ C) {t : ℝ}
    (h : ∀ p ∈ C, dot p (uvec t) ≤ dot q (uvec t)) : supp C t = dot q (uvec t) := by
  unfold supp
  apply IsGreatest.csSup_eq
  exact ⟨⟨q, hq, rfl⟩, by rintro _ ⟨p, hp, rfl⟩; exact h p hp⟩

lemma gm_dot_uvec_comb (p : ℝ × ℝ) (α β s : ℝ) :
    sin (β - α) * dot p (uvec s) = sin (β - s) * dot p (uvec α) + sin (s - α) * dot p (uvec β) := by
  simp only [dot, uvec, sin_sub]
  ring

/-- A point on two supporting lines of a convex body is the whole boundary between them. -/
lemma gm_corner {C : Set (ℝ × ℝ)} (hC : IsConvexBody C) {x : ℝ × ℝ} (hx : x ∈ C) {α β : ℝ}
    (hαβ : α < β) (hβα : β < α + π) (hxα : dot x (uvec α) = supp C α)
    (hxβ : dot x (uvec β) = supp C β) :
    (∀ s ∈ Icc α β, supp C s = dot x (uvec s)) ∧ ∀ s ∈ Ioo α β, edge C s = {x} := by
  have hS : 0 < sin (β - α) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have key : ∀ s ∈ Icc α β, ∀ p ∈ C, dot p (uvec s) ≤ dot x (uvec s) := by
    intro s hs p hp
    have h1 : 0 ≤ sin (β - s) := sin_nonneg_of_nonneg_of_le_pi (by linarith [hs.2])
      (by linarith [hs.1])
    have h2 : 0 ≤ sin (s - α) := sin_nonneg_of_nonneg_of_le_pi (by linarith [hs.1])
      (by linarith [hs.2])
    have hpα : dot p (uvec α) ≤ dot x (uvec α) := hxα ▸ dot_le_supp hC.2.1 hp α
    have hpβ : dot p (uvec β) ≤ dot x (uvec β) := hxβ ▸ dot_le_supp hC.2.1 hp β
    have e1 := gm_dot_uvec_comb p α β s
    have e2 := gm_dot_uvec_comb x α β s
    have : sin (β - α) * dot p (uvec s) ≤ sin (β - α) * dot x (uvec s) := by
      rw [e1, e2]
      exact add_le_add (mul_le_mul_of_nonneg_left hpα h1) (mul_le_mul_of_nonneg_left hpβ h2)
    exact le_of_mul_le_mul_left this hS
  refine ⟨fun s hs => gm_supp_eq_of_max hx (key s hs), fun s hs => ?_⟩
  have hsupp := gm_supp_eq_of_max hx (key s (Ioo_subset_Icc_self hs))
  ext p
  simp only [mem_singleton_iff, gm_mem_edge_iff]
  constructor
  · rintro ⟨hp, hps⟩
    have h1 : 0 < sin (β - s) := sin_pos_of_pos_of_lt_pi (by linarith [hs.2]) (by linarith [hs.1])
    have h2 : 0 < sin (s - α) := sin_pos_of_pos_of_lt_pi (by linarith [hs.1]) (by linarith [hs.2])
    have hpα : dot p (uvec α) ≤ dot x (uvec α) := hxα ▸ dot_le_supp hC.2.1 hp α
    have hpβ : dot p (uvec β) ≤ dot x (uvec β) := hxβ ▸ dot_le_supp hC.2.1 hp β
    have e1 := gm_dot_uvec_comb p α β s
    have e2 := gm_dot_uvec_comb x α β s
    rw [hsupp] at hps
    have eα : dot p (uvec α) = dot x (uvec α) := by
      by_contra hne
      have hlt := lt_of_le_of_ne hpα hne
      have : sin (β - α) * dot p (uvec s) < sin (β - α) * dot x (uvec s) := by
        rw [e1, e2]
        exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hlt h1)
          (mul_le_mul_of_nonneg_left hpβ h2.le)
      rw [hps] at this; exact lt_irrefl _ this
    have eβ : dot p (uvec β) = dot x (uvec β) := by
      by_contra hne
      have hlt := lt_of_le_of_ne hpβ hne
      have : sin (β - α) * dot p (uvec s) < sin (β - α) * dot x (uvec s) := by
        rw [e1, e2]
        exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hpα h1.le)
          (mul_lt_mul_of_pos_left hlt h2)
      rw [hps] at this; exact lt_irrefl _ this
    simp only [dot, uvec] at eα eβ
    have hS' : sin (β - α) ≠ 0 := hS.ne'
    rw [sin_sub] at hS'
    have k1 : (p.1 - x.1) * (sin β * cos α - cos β * sin α) = 0 := by
      linear_combination sin β * eα - sin α * eβ
    have k2 : (p.2 - x.2) * (sin β * cos α - cos β * sin α) = 0 := by
      linear_combination -(cos β * eα) + cos α * eβ
    have q1 : p.1 = x.1 := by
      have := (mul_eq_zero.1 k1).resolve_right hS'; linarith
    have q2 : p.2 = x.2 := by
      have := (mul_eq_zero.1 k2).resolve_right hS'; linarith
    exact Prod.ext q1 q2
  · rintro rfl
    exact ⟨hx, hsupp.symm⟩

/-- Squeeze in segments. -/
lemma gm_tendsto_of_segment {l : Filter ℝ} {f g h : ℝ → ℝ × ℝ} {L : ℝ × ℝ}
    (hg : Tendsto g l (𝓝 L)) (hh : Tendsto h l (𝓝 L))
    (hf : ∀ᶠ s in l, f s ∈ segment ℝ (g s) (h s)) : Tendsto f l (𝓝 L) := by
  rw [Metric.tendsto_nhds] at hg hh ⊢
  intro ε hε
  filter_upwards [hg ε hε, hh ε hε, hf] with s h1 h2 h3
  exact (convex_ball L ε).segment_subset h1 h2 h3

lemma gm_tendsto_add_right_nhdsGT (ψ t : ℝ) :
    Tendsto (fun s => ψ + s) (𝓝[>] t) (𝓝[>] (ψ + t)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact ((continuous_const.add continuous_id).tendsto t).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    show ψ + t < ψ + s
    linarith [mem_Ioi.1 hs]

lemma gm_tendsto_add_right_nhdsLT (ψ t : ℝ) :
    Tendsto (fun s => ψ + s) (𝓝[<] t) (𝓝[<] (ψ + t)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact ((continuous_const.add continuous_id).tendsto t).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    show ψ + s < ψ + t
    linarith [mem_Iio.1 hs]

/-- A continuous curve running along the edges `e_C(ψ + s)` meets `v_C⁺(ψ + t)` at `t`. -/
lemma gm_eq_vplus_of_right {C : Set (ℝ × ℝ)} (hC : IsConvexBody C) {f : ℝ → ℝ × ℝ} {ψ t : ℝ}
    (hf : ContinuousWithinAt f (Ioi t) t) (he : ∀ᶠ s in 𝓝[>] t, f s ∈ edge C (ψ + s)) :
    f t = vplus C (ψ + t) := by
  have h1 := gm_tendsto_add_right_nhdsGT ψ t
  have hm := (tendsto_vminus_right hC (ψ + t)).comp h1
  have hp := (tendsto_vplus_right hC (ψ + t)).comp h1
  have hseg : ∀ᶠ s in 𝓝[>] t, f s ∈ segment ℝ (vminus C (ψ + s)) (vplus C (ψ + s)) :=
    he.mono (fun s hs => by rwa [edge_eq_segment hC] at hs)
  exact tendsto_nhds_unique hf (gm_tendsto_of_segment hm hp hseg)

/-- A continuous curve running along the edges `e_C(ψ + s)` meets `v_C⁻(ψ + t)` at `t`. -/
lemma gm_eq_vminus_of_left {C : Set (ℝ × ℝ)} (hC : IsConvexBody C) {f : ℝ → ℝ × ℝ} {ψ t : ℝ}
    (hf : ContinuousWithinAt f (Iio t) t) (he : ∀ᶠ s in 𝓝[<] t, f s ∈ edge C (ψ + s)) :
    f t = vminus C (ψ + t) := by
  have h1 := gm_tendsto_add_right_nhdsLT ψ t
  have hm := (tendsto_vminus_left hC (ψ + t)).comp h1
  have hp := (tendsto_vplus_left hC (ψ + t)).comp h1
  have hseg : ∀ᶠ s in 𝓝[<] t, f s ∈ segment ℝ (vminus C (ψ + s)) (vplus C (ψ + s)) :=
    he.mono (fun s hs => by rwa [edge_eq_segment hC] at hs)
  exact tendsto_nhds_unique hf (gm_tendsto_of_segment hm hp hseg)

/-- `v_C⁺(a) = x` if `v_C⁺ = x` just after `a`. -/
lemma gm_vplus_eq_of_right {C : Set (ℝ × ℝ)} (hC : IsConvexBody C) {a b : ℝ} (hab : a < b)
    {x : ℝ × ℝ} (h : ∀ s ∈ Ioo a b, vplus C s = x) : vplus C a = x := by
  have h1 := tendsto_vplus_right hC a
  have h2 : Tendsto (vplus C) (𝓝[>] a) (𝓝 x) :=
    tendsto_const_nhds.congr' (eventually_of_mem (Ioo_mem_nhdsGT hab) (fun s hs => (h s hs).symm))
  exact tendsto_nhds_unique h1 h2

/-- `v_C⁻(b) = x` if `v_C⁻ = x` just before `b`. -/
lemma gm_vminus_eq_of_left {C : Set (ℝ × ℝ)} (hC : IsConvexBody C) {a b : ℝ} (hab : a < b)
    {x : ℝ × ℝ} (h : ∀ s ∈ Ioo a b, vminus C s = x) : vminus C b = x := by
  have h1 := tendsto_vminus_left hC b
  have h2 : Tendsto (vminus C) (𝓝[<] b) (𝓝 x) :=
    tendsto_const_nhds.congr' (eventually_of_mem (Ioo_mem_nhdsLT hab) (fun s hs => (h s hs).symm))
  exact tendsto_nhds_unique h1 h2

/-- Monotonicity of a function with nonpositive derivative off one point. -/
lemma gm_le_of_deriv_nonpos {f : ℝ → ℝ} {a m b : ℝ} (ham : a ≤ m) (hmb : m ≤ b)
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, x ≠ m → ∃ f', HasDerivAt f f' x ∧ f' ≤ 0) :
    ∀ x ∈ Icc a b, f b ≤ f x := by
  have A : ∀ {u v : ℝ}, a ≤ u → v ≤ b → (Ioo u v ∩ {m} = ∅) → AntitoneOn f (Icc u v) := by
    intro u v hu hv hm
    apply antitoneOn_of_deriv_nonpos (convex_Icc u v) (hc.mono (Icc_subset_Icc hu hv))
    · intro x hx
      rw [interior_Icc] at hx
      have hxm : x ≠ m := fun h => by
        have : x ∈ Ioo u v ∩ {m} := ⟨hx, h⟩
        rw [hm] at this; exact this
      obtain ⟨f', hf', -⟩ := hd x ⟨by linarith [hx.1], by linarith [hx.2]⟩ hxm
      exact hf'.differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxm : x ≠ m := fun h => by
        have : x ∈ Ioo u v ∩ {m} := ⟨hx, h⟩
        rw [hm] at this; exact this
      obtain ⟨f', hf', hf'0⟩ := hd x ⟨by linarith [hx.1], by linarith [hx.2]⟩ hxm
      rw [hf'.deriv]; exact hf'0
  have A1 : AntitoneOn f (Icc a m) := A le_rfl hmb (by
    ext x; simp only [mem_inter_iff, mem_Ioo, mem_singleton_iff, mem_empty_iff_false, iff_false]
    rintro ⟨⟨-, h⟩, rfl⟩; exact lt_irrefl _ h)
  have A2 : AntitoneOn f (Icc m b) := A ham le_rfl (by
    ext x; simp only [mem_inter_iff, mem_Ioo, mem_singleton_iff, mem_empty_iff_false, iff_false]
    rintro ⟨⟨h, -⟩, rfl⟩; exact lt_irrefl _ h)
  intro x hx
  have hmb' : f b ≤ f m := A2 ⟨le_rfl, hmb⟩ ⟨hmb, le_rfl⟩ hmb
  rcases le_total x m with hxm | hxm
  · exact hmb'.trans (A1 ⟨hx.1, hxm⟩ ⟨ham, le_rfl⟩ hxm)
  · exact A2 ⟨hxm, hx.2⟩ ⟨hmb, le_rfl⟩ hx.2

/-- Monotonicity of a function with nonnegative derivative off one point. -/
lemma gm_le_of_deriv_nonneg {f : ℝ → ℝ} {a m b : ℝ} (ham : a ≤ m) (hmb : m ≤ b)
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, x ≠ m → ∃ f', HasDerivAt f f' x ∧ 0 ≤ f') :
    ∀ x ∈ Icc a b, f a ≤ f x := by
  have A : ∀ {u v : ℝ}, a ≤ u → v ≤ b → (Ioo u v ∩ {m} = ∅) → MonotoneOn f (Icc u v) := by
    intro u v hu hv hm
    apply monotoneOn_of_deriv_nonneg (convex_Icc u v) (hc.mono (Icc_subset_Icc hu hv))
    · intro x hx
      rw [interior_Icc] at hx
      have hxm : x ≠ m := fun h => by
        have : x ∈ Ioo u v ∩ {m} := ⟨hx, h⟩
        rw [hm] at this; exact this
      obtain ⟨f', hf', -⟩ := hd x ⟨by linarith [hx.1], by linarith [hx.2]⟩ hxm
      exact hf'.differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxm : x ≠ m := fun h => by
        have : x ∈ Ioo u v ∩ {m} := ⟨hx, h⟩
        rw [hm] at this; exact this
      obtain ⟨f', hf', hf'0⟩ := hd x ⟨by linarith [hx.1], by linarith [hx.2]⟩ hxm
      rw [hf'.deriv]; exact hf'0
  have A1 : MonotoneOn f (Icc a m) := A le_rfl hmb (by
    ext x; simp only [mem_inter_iff, mem_Ioo, mem_singleton_iff, mem_empty_iff_false, iff_false]
    rintro ⟨⟨-, h⟩, rfl⟩; exact lt_irrefl _ h)
  have A2 : MonotoneOn f (Icc m b) := A ham le_rfl (by
    ext x; simp only [mem_inter_iff, mem_Ioo, mem_singleton_iff, mem_empty_iff_false, iff_false]
    rintro ⟨⟨h, -⟩, rfl⟩; exact lt_irrefl _ h)
  intro x hx
  have ham' : f a ≤ f m := A1 ⟨le_rfl, ham⟩ ⟨ham, le_rfl⟩ ham
  rcases le_total x m with hxm | hxm
  · exact A1 ⟨le_rfl, ham⟩ ⟨hx.1, hxm⟩ hx.1
  · exact ham'.trans (A2 ⟨le_rfl, hmb⟩ ⟨hxm, hx.2⟩ hxm)

lemma gm_hasDerivAt_fst {f : ℝ → ℝ × ℝ} {f' : ℝ × ℝ} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun s => (f s).1) f'.1 x :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt x hf

lemma gm_hasDerivAt_snd {f : ℝ → ℝ × ℝ} {f' : ℝ × ℝ} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun s => (f s).2) f'.2 x :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt x hf

lemma gm_hasDerivAt_dot {f g : ℝ → ℝ × ℝ} {f' g' : ℝ × ℝ} {x : ℝ} (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) :
    HasDerivAt (fun s => dot (f s) (g s)) (dot f' (g x) + dot (f x) g') x := by
  have := ((gm_hasDerivAt_fst hf).mul (gm_hasDerivAt_fst hg)).add
    ((gm_hasDerivAt_snd hf).mul (gm_hasDerivAt_snd hg))
  convert this using 1
  · funext s; simp only [dot, Pi.add_apply, Pi.mul_apply]
  · simp only [dot]; ring

lemma gm_hasDerivAt_dot_const {f : ℝ → ℝ × ℝ} {f' : ℝ × ℝ} {x : ℝ} (hf : HasDerivAt f f' x)
    (w : ℝ × ℝ) : HasDerivAt (fun s => dot (f s) w) (dot f' w) x := by
  have := gm_hasDerivAt_dot hf (hasDerivAt_const x w)
  simpa using this

lemma gm_hasDerivAt_uvec (x : ℝ) : HasDerivAt uvec (vvec x) x :=
  (Real.hasDerivAt_cos x).prodMk (Real.hasDerivAt_sin x)

lemma gm_hasDerivAt_vvec (x : ℝ) : HasDerivAt vvec (-uvec x) x := by
  have := (Real.hasDerivAt_sin x).neg.prodMk (Real.hasDerivAt_cos x)
  have e : -uvec x = (-cos x, -sin x) := rfl
  rw [e]; exact this

lemma gm_continuous_dot_const {f : ℝ → ℝ × ℝ} (hf : Continuous f) (w : ℝ × ℝ) :
    Continuous (fun s => dot (f s) w) := by
  unfold dot; fun_prop

/-- The left body is a convex body. -/
lemma gm_isConvexBody_leftBody {φ : ℝ} {K : Set (ℝ × ℝ)} (hK : IsConvexBody K)
    (hne : (leftBody φ K).Nonempty) : IsConvexBody (leftBody φ K) :=
  ⟨hne, hK.2.1.inter_right (isClosed_biInter fun _ _ => gm_isClosed_halfPlus _ _),
    hK.2.2.inter (convex_iInter₂ fun _ _ => gm_convex_halfPlus _ _)⟩

/-- The right body is a convex body. -/
lemma gm_isConvexBody_rightBody {φ : ℝ} {K : Set (ℝ × ℝ)} (hK : IsConvexBody K)
    (hne : (rightBody φ K).Nonempty) : IsConvexBody (rightBody φ K) :=
  ⟨hne, hK.2.1.inter_right (isClosed_biInter fun _ _ => gm_isClosed_halfPlus _ _),
    hK.2.2.inter (convex_iInter₂ fun _ _ => gm_convex_halfPlus _ _)⟩

lemma gm_leftBody_subset {φ : ℝ} {K : Set (ℝ × ℝ)} {s : ℝ} (hs : s ∈ Icc 0 (π / 2 - φ)) :
    leftBody φ K ⊆ halfD K s := fun _ hp => mem_iInter₂.1 hp.2 s hs

lemma gm_rightBody_subset {φ : ℝ} {K : Set (ℝ × ℝ)} {s : ℝ} (hs : s ∈ Icc φ (π / 2)) :
    rightBody φ K ⊆ halfB K s := fun _ hp => mem_iInter₂.1 hp.2 s hs

/-- A point of `D_K` on the line `d_K(s)` lies on the supporting line `l_{D_K}(3π/2 + s)`. -/
lemma gm_supp_leftBody_of {φ : ℝ} {K : Set (ℝ × ℝ)} {s : ℝ} (hs : s ∈ Icc 0 (π / 2 - φ))
    {q : ℝ × ℝ} (hq : q ∈ leftBody φ K)
    (hqd : dot q (uvec (s + π / 2)) = supp K (s + π / 2) - 1) :
    supp (leftBody φ K) (3 * π / 2 + s) = 1 - supp K (s + π / 2) ∧
      q ∈ edge (leftBody φ K) (3 * π / 2 + s) := by
  have hu : uvec (3 * π / 2 + s) = -uvec (s + π / 2) := by
    rw [show 3 * π / 2 + s = (s + π / 2) + π by ring, uvec_add_pi]
  have key : ∀ p ∈ leftBody φ K, dot p (uvec (3 * π / 2 + s)) ≤ dot q (uvec (3 * π / 2 + s)) := by
    intro p hp
    have h1 : supp K (s + π / 2) - 1 ≤ dot p (uvec (s + π / 2)) := gm_leftBody_subset hs hp
    rw [hu, dot_neg_right, dot_neg_right, hqd]
    linarith
  have hsupp := gm_supp_eq_of_max hq key
  refine ⟨by rw [hsupp, hu, dot_neg_right, hqd]; ring, hq, hsupp.symm⟩

/-- A point of `B_K` on the line `b_K(s)` lies on the supporting line `l_{B_K}(π + s)`. -/
lemma gm_supp_rightBody_of {φ : ℝ} {K : Set (ℝ × ℝ)} {s : ℝ} (hs : s ∈ Icc φ (π / 2))
    {q : ℝ × ℝ} (hq : q ∈ rightBody φ K) (hqb : dot q (uvec s) = supp K s - 1) :
    supp (rightBody φ K) (π + s) = 1 - supp K s ∧ q ∈ edge (rightBody φ K) (π + s) := by
  have hu : uvec (π + s) = -uvec s := by rw [add_comm, uvec_add_pi]
  have key : ∀ p ∈ rightBody φ K, dot p (uvec (π + s)) ≤ dot q (uvec (π + s)) := by
    intro p hp
    have h1 : supp K s - 1 ≤ dot p (uvec s) := gm_rightBody_subset hs hp
    rw [hu, dot_neg_right, dot_neg_right, hqb]
    linarith
  have hsupp := gm_supp_eq_of_max hq key
  refine ⟨by rw [hsupp, hu, dot_neg_right, hqb]; ring, hq, hsupp.symm⟩

/-! ### The cap of Gerver's sofa -/

lemma gm_fan_snd {p : ℝ × ℝ} (hp : p ∈ fan (π / 2)) : 0 ≤ p.2 := by
  have h : 0 ≤ dot p (uvec (π / 2)) := hp.2
  simpa [dot, uvec] using h

/-- `x_K(s)` lies on `b_K(s)` and on `d_K(s)`. -/
lemma gm_innerCorner_dot (K : Set (ℝ × ℝ)) (s : ℝ) :
    dot (innerCorner K s) (uvec s) = supp K s - 1 ∧
      dot (innerCorner K s) (uvec (s + π / 2)) = supp K (s + π / 2) - 1 := by
  rw [proposition2_2_2_innerCorner, uvec_add_pi_div_two]
  simp only [dot_add_left, dot_smul_left, dot_uvec_self, dot_vvec_uvec, dot_uvec_vvec,
    dot_vvec_self]
  constructor <;> ring


lemma gm_mem_niche_of {K : Set (ℝ × ℝ)} {p : ℝ × ℝ} {s : ℝ} (hs : s ∈ Ioo 0 (π / 2))
    (hf : p ∈ fan (π / 2)) (hq : p ∈ qMinus K s) : p ∈ niche K (π / 2) :=
  ⟨hf, mem_biUnion hs hq⟩


namespace GerverParams

variable {P : GerverParams}

section
variable (hP : P.IsSolution) (hbox : P.InBox)
include hP hbox

lemma gm_isMonotone : IsMonotoneSofa (gerverSofa P) (π / 2) :=
  (theorem8_4_1_monotone hP hbox).1

lemma gm_movingSofa_std : IsMovingSofaWithAngle (gerverSofa P) (π / 2) ∧
    IsStandardPosition (gerverSofa P) (π / 2) := by
  obtain ⟨hω, S', hS', hstd, hS⟩ := gm_isMonotone hP hbox
  have := theorem2_3_2 hω hS' hstd
  rw [hS]; exact ⟨this.1, this.2.1⟩

lemma gm_isCap : IsCap P.cap (π / 2) :=
  theorem2_4_1 pi_div_two_mem_Ioc (gm_movingSofa_std hP hbox).1 (gm_movingSofa_std hP hbox).2

lemma gm_isConvexBody_cap : IsConvexBody P.cap := (gm_isCap hP hbox).2.1

lemma gm_supp_cap_pi_div_two : supp P.cap (π / 2) = 1 := (gm_isCap hP hbox).2.2.2.1

lemma gm_niche_subset : niche P.cap (π / 2) ⊆ P.cap :=
  (theorem2_5_9 (gm_isCap hP hbox)).1 ⟨gerverSofa P, gm_isMonotone hP hbox, rfl⟩

lemma gm_sofaArea_cap : sofaArea (π / 2) P.cap = area (gerverSofa P) :=
  theorem2_5_10 (gm_isMonotone hP hbox)

lemma gm_area_cap : 2.2 ≤ area P.cap := by
  have h1 := gerverSofa_area hP hbox
  have h2 := gm_sofaArea_cap hP hbox
  unfold sofaArea at h2
  have h3 : 0 ≤ area (niche P.cap (π / 2)) := ENNReal.toReal_nonneg
  linarith

lemma gm_isKi : IsKi P.cap := ⟨gm_isCap hP hbox, theorem6_1_2 hP hbox, gm_area_cap hP hbox⟩

lemma gm_innerCorner {t : ℝ} (ht : t ∈ Icc 0 (π / 2)) : innerCorner P.cap t = P.path t :=
  ((theorem8_4_1_monotone hP hbox).2 t ht).2.2

lemma gm_aK {t : ℝ} (ht : t ∈ Icc 0 (π / 2)) : aK P.cap t = P.curveA t :=
  ((theorem8_4_1_monotone hP hbox).2 t ht).1

lemma gm_cK {t : ℝ} (ht : t ∈ Icc 0 (π / 2)) : cK P.cap t = P.curveC t :=
  ((theorem8_4_1_monotone hP hbox).2 t ht).2.1

omit hP in
lemma gm_φ_mem : P.φ ∈ Icc (0.039 : ℝ) 0.04 := hbox.1

lemma gm_φ_mem_Ioo : P.φ ∈ Ioo 0 (π / 4) :=
  ⟨gm_φ_pos hP, by have := hbox.1.2; have := two_le_pi; linarith⟩

lemma gm_closure_niche_subset_cap : closure (niche P.cap (π / 2)) ⊆ P.cap :=
  closure_minimal (gm_niche_subset hP hbox) (gm_isConvexBody_cap hP hbox).isClosed

omit hP hbox in
lemma gm_closure_niche_subset_fan : closure (niche P.cap (π / 2)) ⊆ fan (π / 2) :=
  closure_minimal inter_subset_left (gm_isClosed_fan _)

end

end GerverParams

/-! ### The left body `D_K` and the curve `𝐃` -/

namespace GerverParams

variable {P : GerverParams}

section
variable (hP : P.IsSolution) (hbox : P.InBox)
include hP hbox

omit hbox in
lemma gm_θ_pos : 0 < P.θ := (gm_φ_pos hP).trans (gm_φ_lt_θ hP)

omit hbox in
lemma gm_θ_le : P.θ ≤ π / 2 - P.φ := by
  have := gm_θ_lt hP; have := gm_φ_lt_θ hP; linarith

lemma gm_D_mem {t : ℝ} (ht : t ∈ Icc 0 P.θ) :
    P.curveD t ∈ closure (niche P.cap (π / 2)) \ niche P.cap (π / 2) :=
  (theorem8_4_1_niche hP hbox).2.2.1 t ht

lemma gm_D_θ : P.curveD P.θ = xLeft P.φ P.cap := by
  have h := (theorem8_4_1_niche hP hbox).2.2.2.2.1
  have h2 := gm_innerCorner hP hbox (t := π / 2 - P.φ)
    ⟨by linarith [gm_d_lt hP, gm_φ_pos hP, gm_c_lt_d hP, gm_θ_lt_c hP, gm_θ_pos hP],
      by linarith [gm_φ_pos hP]⟩
  unfold xLeft; rw [h2]; exact h.symm

lemma gm_D_mem_hLeft {t : ℝ} (ht : t ∈ Icc 0 P.θ) : P.curveD t ∈ hLeft P.φ P.cap := by
  show supp P.cap (π / 2 - P.φ + π / 2) - 1 ≤ dot (P.curveD t) (uvec (π / 2 - P.φ + π / 2))
  have hθ : dot (P.curveD P.θ) (uvec (π / 2 - P.φ + π / 2)) =
      supp P.cap (π / 2 - P.φ + π / 2) - 1 := by
    rw [gm_D_θ hP hbox]; exact (gm_innerCorner_dot P.cap (π / 2 - P.φ)).2
  rw [← hθ]
  have hcont := gm_continuous_dot_const (gm_continuous_curveD hP) (uvec (π / 2 - P.φ + π / 2))
  refine gm_le_of_deriv_nonpos (f := fun s => dot (P.curveD s) (uvec (π / 2 - P.φ + π / 2)))
    (gm_φ_pos hP).le (gm_φ_lt_θ hP).le hcont.continuousOn ?_ t ht
  intro x hx hxm
  obtain ⟨c, hc, hd⟩ := (theorem8_4_1_tangents hP hbox).2 x hx hxm
  refine ⟨dot (c • uvec x) (uvec (π / 2 - P.φ + π / 2)), gm_hasDerivAt_dot_const hd _, ?_⟩
  rw [dot_smul_left, dot_uvec_uvec]
  apply mul_nonpos_of_nonneg_of_nonpos hc.le
  rw [show x - (π / 2 - P.φ + π / 2) = (x + P.φ) - π by ring, cos_sub_pi, neg_nonpos]
  have hx' : x ∈ Ioo 0 P.θ := hx
  have h2 : x + P.φ < π / 2 := by linarith [hx'.2, gm_θ_lt hP, gm_φ_lt_θ hP]
  exact (cos_pos_of_mem_Ioo ⟨by linarith [hx'.1, gm_φ_pos hP, pi_pos], h2⟩).le

lemma gm_D_mem_leftBody {t : ℝ} (ht : t ∈ Icc 0 P.θ) :
    P.curveD t ∈ leftBody P.φ P.cap := by
  have hm := gm_D_mem hP hbox ht
  refine ⟨gm_closure_niche_subset_cap hP hbox hm.1, mem_iInter₂.2 fun s hs => ?_⟩
  rcases hs.1.lt_or_eq with hs0 | hs0
  · rcases hs.2.lt_or_eq with hs1 | hs1
    · by_contra hn
      have h1 := (lemma8_1_6_left (gm_φ_mem_Ioo hP hbox) (gm_isKi hP hbox) ⟨hs.1, hs1⟩).2.1
      have h2 : P.curveD t ∈ hLeft P.φ P.cap ∩ qMinus P.cap s := by
        rw [h1]; exact ⟨gm_D_mem_hLeft hP hbox ht, hn⟩
      exact hm.2 (gm_mem_niche_of ⟨hs0, by linarith [gm_φ_pos hP]⟩
        ((gm_closure_niche_subset_fan (P := P)) hm.1) h2.2)
    · rw [hs1]; exact gm_D_mem_hLeft hP hbox ht
  · rw [← hs0]
    show supp P.cap (0 + π / 2) - 1 ≤ dot (P.curveD t) (uvec (0 + π / 2))
    rw [zero_add, gm_supp_cap_pi_div_two hP hbox, sub_self]
    exact ((gm_closure_niche_subset_fan (P := P)) hm.1).2

lemma gm_D_wallD {t : ℝ} (ht : t ∈ Icc 0 P.θ) :
    dot (P.curveD t) (uvec (t + π / 2)) = supp P.cap (t + π / 2) - 1 := by
  have h := (theorem8_4_1_walls hP hbox).2 t ht
  have h2 : P.curveD t ∈ wallD P.cap t := image_mono (fun p hp => hp.1) h
  rw [proposition2_2_2_wallD] at h2
  exact h2

lemma gm_isConvexBody_D : IsConvexBody (leftBody P.φ P.cap) :=
  gm_isConvexBody_leftBody (gm_isConvexBody_cap hP hbox)
    ⟨_, gm_D_mem_leftBody hP hbox ⟨le_rfl, (gm_θ_pos hP).le⟩⟩

lemma gm_D_edge {t : ℝ} (ht : t ∈ Icc 0 P.θ) :
    supp (leftBody P.φ P.cap) (3 * π / 2 + t) = 1 - supp P.cap (t + π / 2) ∧
      P.curveD t ∈ edge (leftBody P.φ P.cap) (3 * π / 2 + t) :=
  gm_supp_leftBody_of ⟨ht.1, ht.2.trans (gm_θ_le hP)⟩ (gm_D_mem_leftBody hP hbox ht)
    (gm_D_wallD hP hbox ht)

lemma gm_D_vplus_vminus {t : ℝ} (ht : t ∈ Ioo 0 P.θ) :
    P.curveD t = vplus (leftBody P.φ P.cap) (3 * π / 2 + t) ∧
      P.curveD t = vminus (leftBody P.φ P.cap) (3 * π / 2 + t) := by
  have hD := gm_isConvexBody_D hP hbox
  have hc := (gm_continuous_curveD hP).continuousAt (x := t)
  constructor
  · apply gm_eq_vplus_of_right hD hc.continuousWithinAt
    filter_upwards [Ioo_mem_nhdsGT ht.2] with s hs
    exact (gm_D_edge hP hbox ⟨by linarith [ht.1, hs.1], hs.2.le⟩).2
  · apply gm_eq_vminus_of_left hD hc.continuousWithinAt
    filter_upwards [Ioo_mem_nhdsLT ht.1] with s hs
    exact (gm_D_edge hP hbox ⟨hs.1.le, by linarith [ht.2, hs.2]⟩).2

lemma gm_D_vplus_zero : vplus (leftBody P.φ P.cap) (3 * π / 2) = P.curveD 0 := by
  have hD := gm_isConvexBody_D hP hbox
  have := gm_eq_vplus_of_right (ψ := 3 * π / 2) (t := 0) hD
    (gm_continuous_curveD hP).continuousAt.continuousWithinAt (by
      filter_upwards [Ioo_mem_nhdsGT (gm_θ_pos hP)] with s hs
      exact (gm_D_edge hP hbox ⟨hs.1.le, hs.2.le⟩).2)
  rw [add_zero] at this; exact this.symm

lemma gm_D_vminus_θ : vminus (leftBody P.φ P.cap) (3 * π / 2 + P.θ) = P.curveD P.θ := by
  have hD := gm_isConvexBody_D hP hbox
  have := gm_eq_vminus_of_left (ψ := 3 * π / 2) (t := P.θ) hD
    (gm_continuous_curveD hP).continuousAt.continuousWithinAt (by
      filter_upwards [Ioo_mem_nhdsLT (gm_θ_pos hP)] with s hs
      exact (gm_D_edge hP hbox ⟨hs.1.le, hs.2.le⟩).2)
  exact this.symm

lemma gm_D_corner : ∀ s ∈ Ioo (3 * π / 2 + P.θ) (3 * π / 2 + (π / 2 - P.φ)),
    edge (leftBody P.φ P.cap) s = {P.curveD P.θ} := by
  have hD := gm_isConvexBody_D hP hbox
  have hθ := gm_θ_lt hP; have hφθ := gm_φ_lt_θ hP; have hφ := gm_φ_pos hP
  have hx : P.curveD P.θ ∈ leftBody P.φ P.cap := gm_D_mem_leftBody hP hbox ⟨(gm_θ_pos hP).le, le_rfl⟩
  apply (gm_corner hD hx (by linarith) (by linarith) _ _).2
  · exact (gm_D_edge hP hbox ⟨(gm_θ_pos hP).le, le_rfl⟩).2.2
  · have := gm_supp_leftBody_of (s := π / 2 - P.φ) ⟨by linarith, le_rfl⟩ hx (by
      rw [gm_D_θ hP hbox]; exact (gm_innerCorner_dot P.cap (π / 2 - P.φ)).2)
    exact this.2.2

lemma gm_D_vplus_θ : vplus (leftBody P.φ P.cap) (3 * π / 2 + P.θ) = P.curveD P.θ := by
  have hD := gm_isConvexBody_D hP hbox
  have hθ := gm_θ_lt hP; have hφθ := gm_φ_lt_θ hP
  refine gm_vplus_eq_of_right hD (b := 3 * π / 2 + (π / 2 - P.φ)) (by linarith) fun s hs => ?_
  have := vplus_mem_edge hD s
  rwa [gm_D_corner hP hbox s hs] at this

lemma gm_D_vminus_end :
    vminus (leftBody P.φ P.cap) (3 * π / 2 + (π / 2 - P.φ)) = P.curveD P.θ := by
  have hD := gm_isConvexBody_D hP hbox
  have hθ := gm_θ_lt hP; have hφθ := gm_φ_lt_θ hP
  refine gm_vminus_eq_of_left hD (a := 3 * π / 2 + P.θ) (by linarith) fun s hs => ?_
  have := vminus_mem_edge hD s
  rwa [gm_D_corner hP hbox s hs] at this

/-- `v_{D_K}⁺(3π/2 + t) = 𝐃(t)` on `[t_0, t_2]`. -/
lemma gm_D_vplus {t : ℝ} (ht : t ∈ Icc 0 P.θ) :
    vplus (leftBody P.φ P.cap) (3 * π / 2 + t) = P.curveD t := by
  rcases ht.1.lt_or_eq with h0 | h0
  · rcases ht.2.lt_or_eq with h1 | h1
    · exact (gm_D_vplus_vminus hP hbox ⟨h0, h1⟩).1.symm
    · rw [h1]; exact gm_D_vplus_θ hP hbox
  · rw [← h0, add_zero]; exact gm_D_vplus_zero hP hbox

/-- The edge `e_{D_K}(3π/2 + t_2)` is the single point `𝐃(t_2)`. -/
lemma gm_D_edge_θ : edge (leftBody P.φ P.cap) (3 * π / 2 + P.θ) = {P.curveD P.θ} := by
  rw [edge_eq_segment (gm_isConvexBody_D hP hbox), gm_D_vminus_θ hP hbox,
    gm_D_vplus_θ hP hbox, segment_same]

end

end GerverParams

/-! ### The right body `B_K` and the curve `𝐁` -/

namespace GerverParams

variable {P : GerverParams}

section
variable (hP : P.IsSolution) (hbox : P.InBox)
include hP hbox

omit hbox in
lemma gm_φ_le_c : P.φ ≤ π / 2 - P.θ := by
  have := gm_θ_lt hP; have := gm_φ_lt_θ hP; linarith

lemma gm_B_mem {t : ℝ} (ht : t ∈ Icc (π / 2 - P.θ) (π / 2)) :
    P.curveB t ∈ closure (niche P.cap (π / 2)) \ niche P.cap (π / 2) :=
  (theorem8_4_1_niche hP hbox).1 t ht

lemma gm_B_c : P.curveB (π / 2 - P.θ) = xRight P.φ P.cap := by
  have h := (theorem8_4_1_niche hP hbox).2.2.2.1
  have h2 := gm_innerCorner hP hbox (t := P.φ)
    ⟨(gm_φ_pos hP).le, by linarith [gm_φ_le_c hP, gm_θ_pos hP]⟩
  unfold xRight; rw [h2]; exact h

lemma gm_B_mem_hRight {t : ℝ} (ht : t ∈ Icc (π / 2 - P.θ) (π / 2)) :
    P.curveB t ∈ hRight P.φ P.cap := by
  show supp P.cap P.φ - 1 ≤ dot (P.curveB t) (uvec P.φ)
  have hc : dot (P.curveB (π / 2 - P.θ)) (uvec P.φ) = supp P.cap P.φ - 1 := by
    rw [gm_B_c hP hbox]; exact (gm_innerCorner_dot P.cap P.φ).1
  rw [← hc]
  have hcont := gm_continuous_dot_const (gm_continuous_curveB hP) (uvec P.φ)
  refine gm_le_of_deriv_nonneg (f := fun s => dot (P.curveB s) (uvec P.φ))
    (gm_c_lt_d hP).le (gm_d_lt hP).le hcont.continuousOn ?_ t ht
  intro x hx hxm
  obtain ⟨c, hc, hd⟩ := (theorem8_4_1_tangents hP hbox).1 x hx hxm
  refine ⟨dot (c • vvec x) (uvec P.φ), gm_hasDerivAt_dot_const hd _, ?_⟩
  rw [dot_smul_left, dot_vvec_uvec']
  have hx' : x ∈ Ioo (π / 2 - P.θ) (π / 2) := hx
  have h1 : P.φ - x < 0 := by linarith [hx'.1, gm_φ_le_c hP, gm_θ_pos hP]
  have h2 : -π < P.φ - x := by linarith [hx'.2, gm_φ_pos hP, pi_pos]
  exact (mul_pos_of_neg_of_neg hc (sin_neg_of_neg_of_neg_pi_lt h1 h2)).le

lemma gm_B_mem_rightBody {t : ℝ} (ht : t ∈ Icc (π / 2 - P.θ) (π / 2)) :
    P.curveB t ∈ rightBody P.φ P.cap := by
  have hm := gm_B_mem hP hbox ht
  refine ⟨gm_closure_niche_subset_cap hP hbox hm.1, mem_iInter₂.2 fun s hs => ?_⟩
  rcases hs.2.lt_or_eq with hs1 | hs1
  · rcases hs.1.lt_or_eq with hs0 | hs0
    · by_contra hn
      have h1 := (lemma8_1_6_right (gm_φ_mem_Ioo hP hbox) (gm_isKi hP hbox) ⟨hs0, hs.2⟩).2.1
      have h2 : P.curveB t ∈ hRight P.φ P.cap ∩ qMinus P.cap s := by
        rw [h1]; exact ⟨gm_B_mem_hRight hP hbox ht, hn⟩
      exact hm.2 (gm_mem_niche_of ⟨by linarith [gm_φ_pos hP], hs1⟩
        ((gm_closure_niche_subset_fan (P := P)) hm.1) h2.2)
    · rw [← hs0]; exact gm_B_mem_hRight hP hbox ht
  · rw [hs1]
    show supp P.cap (π / 2) - 1 ≤ dot (P.curveB t) (uvec (π / 2))
    rw [gm_supp_cap_pi_div_two hP hbox, sub_self]
    exact ((gm_closure_niche_subset_fan (P := P)) hm.1).2

lemma gm_B_wallB {t : ℝ} (ht : t ∈ Icc (π / 2 - P.θ) (π / 2)) :
    dot (P.curveB t) (uvec t) = supp P.cap t - 1 := by
  have h := (theorem8_4_1_walls hP hbox).1 t ht
  have h2 : P.curveB t ∈ wallB P.cap t := image_mono (fun p hp => hp.1) h
  rw [proposition2_2_2_wallB] at h2
  exact h2

lemma gm_isConvexBody_B : IsConvexBody (rightBody P.φ P.cap) :=
  gm_isConvexBody_rightBody (gm_isConvexBody_cap hP hbox)
    ⟨_, gm_B_mem_rightBody hP hbox ⟨(gm_c_lt_d hP).le.trans (gm_d_lt hP).le, le_rfl⟩⟩

lemma gm_B_edge {t : ℝ} (ht : t ∈ Icc (π / 2 - P.θ) (π / 2)) :
    supp (rightBody P.φ P.cap) (π + t) = 1 - supp P.cap t ∧
      P.curveB t ∈ edge (rightBody P.φ P.cap) (π + t) :=
  gm_supp_rightBody_of ⟨(gm_φ_le_c hP).trans ht.1, ht.2⟩ (gm_B_mem_rightBody hP hbox ht)
    (gm_B_wallB hP hbox ht)

lemma gm_B_vplus_vminus {t : ℝ} (ht : t ∈ Ioo (π / 2 - P.θ) (π / 2)) :
    P.curveB t = vplus (rightBody P.φ P.cap) (π + t) ∧
      P.curveB t = vminus (rightBody P.φ P.cap) (π + t) := by
  have hB := gm_isConvexBody_B hP hbox
  have hc := (gm_continuous_curveB hP).continuousAt (x := t)
  constructor
  · apply gm_eq_vplus_of_right hB hc.continuousWithinAt
    filter_upwards [Ioo_mem_nhdsGT ht.2] with s hs
    exact (gm_B_edge hP hbox ⟨by linarith [ht.1, hs.1], hs.2.le⟩).2
  · apply gm_eq_vminus_of_left hB hc.continuousWithinAt
    filter_upwards [Ioo_mem_nhdsLT ht.1] with s hs
    exact (gm_B_edge hP hbox ⟨hs.1.le, by linarith [ht.2, hs.2]⟩).2

lemma gm_B_vplus_c : vplus (rightBody P.φ P.cap) (π + (π / 2 - P.θ)) = P.curveB (π / 2 - P.θ) := by
  have hB := gm_isConvexBody_B hP hbox
  have hcd : π / 2 - P.θ < π / 2 := (gm_c_lt_d hP).trans (gm_d_lt hP)
  have := gm_eq_vplus_of_right (ψ := π) (t := π / 2 - P.θ) hB
    (gm_continuous_curveB hP).continuousAt.continuousWithinAt (by
      filter_upwards [Ioo_mem_nhdsGT hcd] with s hs
      exact (gm_B_edge hP hbox ⟨hs.1.le, hs.2.le⟩).2)
  exact this.symm

lemma gm_B_vminus_end : vminus (rightBody P.φ P.cap) (π + π / 2) = P.curveB (π / 2) := by
  have hB := gm_isConvexBody_B hP hbox
  have hcd : π / 2 - P.θ < π / 2 := (gm_c_lt_d hP).trans (gm_d_lt hP)
  have := gm_eq_vminus_of_left (ψ := π) (t := π / 2) hB
    (gm_continuous_curveB hP).continuousAt.continuousWithinAt (by
      filter_upwards [Ioo_mem_nhdsLT hcd] with s hs
      exact (gm_B_edge hP hbox ⟨hs.1.le, hs.2.le⟩).2)
  exact this.symm

lemma gm_B_corner : ∀ s ∈ Ioo (π + P.φ) (π + (π / 2 - P.θ)),
    edge (rightBody P.φ P.cap) s = {P.curveB (π / 2 - P.θ)} := by
  have hB := gm_isConvexBody_B hP hbox
  have hθ := gm_θ_lt hP; have hφθ := gm_φ_lt_θ hP; have hφ := gm_φ_pos hP
  have hcd : π / 2 - P.θ < π / 2 := (gm_c_lt_d hP).trans (gm_d_lt hP)
  have hx : P.curveB (π / 2 - P.θ) ∈ rightBody P.φ P.cap :=
    gm_B_mem_rightBody hP hbox ⟨le_rfl, hcd.le⟩
  apply (gm_corner hB hx (by linarith) (by linarith) _ _).2
  · have := gm_supp_rightBody_of (s := P.φ) ⟨le_rfl, by linarith⟩ hx (by
      rw [gm_B_c hP hbox]; exact (gm_innerCorner_dot P.cap P.φ).1)
    exact this.2.2
  · exact (gm_B_edge hP hbox ⟨le_rfl, hcd.le⟩).2.2

lemma gm_B_vplus_φ : vplus (rightBody P.φ P.cap) (π + P.φ) = P.curveB (π / 2 - P.θ) := by
  have hB := gm_isConvexBody_B hP hbox
  have hθ := gm_θ_lt hP; have hφθ := gm_φ_lt_θ hP
  refine gm_vplus_eq_of_right hB (b := π + (π / 2 - P.θ)) (by linarith) fun s hs => ?_
  have := vplus_mem_edge hB s
  rwa [gm_B_corner hP hbox s hs] at this

lemma gm_B_vminus_c :
    vminus (rightBody P.φ P.cap) (π + (π / 2 - P.θ)) = P.curveB (π / 2 - P.θ) := by
  have hB := gm_isConvexBody_B hP hbox
  have hθ := gm_θ_lt hP; have hφθ := gm_φ_lt_θ hP
  refine gm_vminus_eq_of_left hB (a := π + P.φ) (by linarith) fun s hs => ?_
  have := vminus_mem_edge hB s
  rwa [gm_B_corner hP hbox s hs] at this

lemma gm_B_edge_c : edge (rightBody P.φ P.cap) (π + (π / 2 - P.θ)) = {P.curveB (π / 2 - P.θ)} := by
  rw [edge_eq_segment (gm_isConvexBody_B hP hbox), gm_B_vminus_c hP hbox,
    gm_B_vplus_c hP hbox, segment_same]

/-- `v_{B_K}⁺(π + t) = 𝐁(t)` on `[t_3, t_5)`. -/
lemma gm_B_vplus {t : ℝ} (ht : t ∈ Ico (π / 2 - P.θ) (π / 2)) :
    vplus (rightBody P.φ P.cap) (π + t) = P.curveB t := by
  rcases ht.1.lt_or_eq with h0 | h0
  · exact (gm_B_vplus_vminus hP hbox ⟨h0, ht.2⟩).1.symm
  · rw [← h0]; exact gm_B_vplus_c hP hbox

end

end GerverParams

namespace GerverParams

variable {P : GerverParams}

section
variable (hP : P.IsSolution) (hbox : P.InBox)
include hP hbox

lemma gm_tailD : tailD P.φ (leftBody P.φ P.cap) = P.curveD '' Icc 0 P.θ := by
  have hD := gm_isConvexBody_D hP hbox
  have hθ0 := gm_θ_pos hP
  have hθle := gm_θ_le hP
  ext p
  simp only [tailD, convexCurve, mem_union, mem_singleton_iff, mem_iUnion, mem_image, exists_prop]
  constructor
  · rintro ((h | ⟨s, hs, hp⟩) | h)
    · exact ⟨0, ⟨le_rfl, hθ0.le⟩, by rw [h, gm_D_vplus_zero hP hbox]⟩
    · rcases lt_trichotomy s (3 * π / 2 + P.θ) with h1 | h1 | h1
      · have hτ : s - 3 * π / 2 ∈ Ioo 0 P.θ := ⟨by linarith [hs.1], by linarith⟩
        have e := gm_D_vplus_vminus hP hbox hτ
        rw [show s = 3 * π / 2 + (s - 3 * π / 2) by ring, edge_eq_segment hD, ← e.1, ← e.2,
          segment_same, mem_singleton_iff] at hp
        exact ⟨s - 3 * π / 2, Ioo_subset_Icc_self hτ, hp.symm⟩
      · rw [h1, gm_D_edge_θ hP hbox, mem_singleton_iff] at hp
        exact ⟨P.θ, ⟨hθ0.le, le_rfl⟩, hp.symm⟩
      · rw [gm_D_corner hP hbox s ⟨h1, hs.2⟩, mem_singleton_iff] at hp
        exact ⟨P.θ, ⟨hθ0.le, le_rfl⟩, hp.symm⟩
    · exact ⟨P.θ, ⟨hθ0.le, le_rfl⟩, by rw [h, gm_D_vminus_end hP hbox]⟩
  · rintro ⟨τ, hτ, rfl⟩
    rcases hτ.1.lt_or_eq with h0 | h0
    · rcases hτ.2.lt_or_eq with h1 | h1
      · left; right
        exact ⟨3 * π / 2 + τ, ⟨by linarith, by linarith⟩, (gm_D_edge hP hbox hτ).2⟩
      · right; rw [h1, gm_D_vminus_end hP hbox]
    · left; left; rw [← h0, gm_D_vplus_zero hP hbox]

lemma gm_tailB : tailB P.φ (rightBody P.φ P.cap) = P.curveB '' Icc (π / 2 - P.θ) (π / 2) := by
  have hB := gm_isConvexBody_B hP hbox
  have hcd : π / 2 - P.θ < π / 2 := (gm_c_lt_d hP).trans (gm_d_lt hP)
  have hφc := gm_φ_le_c hP
  have h32 : (3 : ℝ) * π / 2 = π + π / 2 := by ring
  ext p
  simp only [tailB, convexCurve, mem_union, mem_singleton_iff, mem_iUnion, mem_image, exists_prop]
  constructor
  · rintro ((h | ⟨s, hs, hp⟩) | h)
    · exact ⟨π / 2 - P.θ, ⟨le_rfl, hcd.le⟩, by rw [h, gm_B_vplus_φ hP hbox]⟩
    · rcases lt_trichotomy s (π + (π / 2 - P.θ)) with h1 | h1 | h1
      · rw [gm_B_corner hP hbox s ⟨hs.1, h1⟩, mem_singleton_iff] at hp
        exact ⟨π / 2 - P.θ, ⟨le_rfl, hcd.le⟩, hp.symm⟩
      · rw [h1, gm_B_edge_c hP hbox, mem_singleton_iff] at hp
        exact ⟨π / 2 - P.θ, ⟨le_rfl, hcd.le⟩, hp.symm⟩
      · have hτ : s - π ∈ Ioo (π / 2 - P.θ) (π / 2) := ⟨by linarith, by linarith [hs.2]⟩
        have e := gm_B_vplus_vminus hP hbox hτ
        rw [show s = π + (s - π) by ring, edge_eq_segment hB, ← e.1, ← e.2, segment_same,
          mem_singleton_iff] at hp
        exact ⟨s - π, Ioo_subset_Icc_self hτ, hp.symm⟩
    · refine ⟨π / 2, ⟨hcd.le, le_rfl⟩, ?_⟩
      rw [h, h32, gm_B_vminus_end hP hbox]
  · rintro ⟨τ, hτ, rfl⟩
    rcases hτ.1.lt_or_eq with h0 | h0
    · rcases hτ.2.lt_or_eq with h1 | h1
      · left; right
        exact ⟨π + τ, ⟨by linarith, by linarith⟩, (gm_B_edge hP hbox hτ).2⟩
      · right; rw [h1, h32, gm_B_vminus_end hP hbox]
    · left; left; rw [← h0, gm_B_vplus_φ hP hbox]

end

end GerverParams


/-! ### Measures on intervals of angles -/

lemma gm_ae_restrict_of_countable {s E : Set ℝ} (hs : MeasurableSet s) (hE : E.Countable)
    {p : ℝ → Prop} (h : ∀ t ∈ s, t ∉ E → p t) : ∀ᵐ t ∂(volume.restrict s), p t := by
  rw [ae_restrict_iff' hs]
  filter_upwards [hE.ae_notMem volume] with t ht hts using h t hts ht

/-- Two measures agreeing on the intervals `(a, b] ⊆ (c, d]` agree on `(c, d]`. -/
lemma gm_restrict_Ioc_eq {μ ν : Measure ℝ} {c d : ℝ}
    (hfin : ∀ a b, c ≤ a → a < b → b ≤ d → μ (Ioc a b) ≠ ⊤)
    (h : ∀ a b, c ≤ a → a < b → b ≤ d → μ (Ioc a b) = ν (Ioc a b)) :
    μ.restrict (Ioc c d) = ν.restrict (Ioc c d) := by
  refine Measure.ext_of_Ioc' _ _ (fun a b _ => ?_) (fun a b _ => ?_)
  · rw [Measure.restrict_apply measurableSet_Ioc, Ioc_inter_Ioc]
    by_cases h' : a ⊔ c < b ⊓ d
    · exact hfin _ _ le_sup_right h' inf_le_right
    · rw [Ioc_eq_empty h']; simp
  · rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc,
      Ioc_inter_Ioc]
    by_cases h' : a ⊔ c < b ⊓ d
    · exact h _ _ le_sup_right h' inf_le_right
    · rw [Ioc_eq_empty h']; simp

/-- Two measures agreeing on the intervals `(c, b]`, `b < d`, agree on `(c, d)`. -/
lemma gm_restrict_Ioo_eq {μ ν : Measure ℝ} {c d : ℝ}
    (h : ∀ b < d, μ.restrict (Ioc c b) = ν.restrict (Ioc c b)) :
    μ.restrict (Ioo c d) = ν.restrict (Ioo c d) := by
  have hU : Ioo c d = ⋃ n : ℕ, Ioc c (d - 1 / ((n : ℝ) + 1)) := by
    ext t; simp only [mem_Ioo, mem_iUnion, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h2)
      exact ⟨n, h1, by linarith⟩
    · rintro ⟨n, h1, h2⟩
      exact ⟨h1, by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                    linarith⟩
  have hdir : Directed (· ⊆ ·) (fun n : ℕ => Ioc c (d - 1 / ((n : ℝ) + 1))) := by
    apply Monotone.directed_le
    intro m n hmn
    apply Ioc_subset_Ioc le_rfl
    have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hmn 1
    linarith
  ext s hs
  rw [hU, Measure.restrict_iUnion_apply_eq_iSup hdir hs,
    Measure.restrict_iUnion_apply_eq_iSup hdir hs]
  congr 1; funext n
  rw [h _ (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
              linarith)]

/-- Two measures without atom at `c`, agreeing on the intervals `(a, b] ⊆ [c, d)`, agree on
`[c, d)`. -/
lemma gm_restrict_Ico_eq {μ ν : Measure ℝ} {c d : ℝ} (hcd : c < d) (hμ : μ {c} = 0)
    (hν : ν {c} = 0) (hfin : ∀ a b, c ≤ a → a < b → b < d → μ (Ioc a b) ≠ ⊤)
    (h : ∀ a b, c ≤ a → a < b → b < d → μ (Ioc a b) = ν (Ioc a b)) :
    μ.restrict (Ico c d) = ν.restrict (Ico c d) := by
  have e : Ico c d = {c} ∪ Ioo c d := by rw [← Ioo_insert_left hcd, insert_eq]
  have hdisj : Disjoint ({c} : Set ℝ) (Ioo c d) := by simp
  rw [e, Measure.restrict_union hdisj measurableSet_Ioo, Measure.restrict_union hdisj
    measurableSet_Ioo, Measure.restrict_eq_zero.2 hμ, Measure.restrict_eq_zero.2 hν, zero_add,
    zero_add]
  apply gm_restrict_Ioo_eq
  intro b hb
  apply gm_restrict_Ioc_eq
  · intro a b' ha hab hb'; exact hfin a b' ha hab (lt_of_le_of_lt hb' hb)
  · intro a b' ha hab hb'; exact h a b' ha hab (lt_of_le_of_lt hb' hb)

lemma gm_withDensity_restrict_self {S : Set ℝ} (hS : MeasurableSet S) (f : ℝ → ℝ≥0∞) :
    ((volume.restrict S).withDensity f).restrict S = (volume.restrict S).withDensity f := by
  rw [restrict_withDensity hS, Measure.restrict_restrict_of_subset subset_rfl]

lemma gm_withDensity_Ioc {S : Set ℝ} (f : ℝ → ℝ≥0∞) {a b : ℝ} (hab : Ioc a b ⊆ S) :
    (volume.restrict S).withDensity f (Ioc a b) = ∫⁻ t in Ioc a b, f t := by
  rw [withDensity_apply f measurableSet_Ioc, Measure.restrict_restrict_of_subset hab]

lemma gm_withDensity_singleton {S : Set ℝ} (f : ℝ → ℝ≥0∞) (c : ℝ) :
    (volume.restrict S).withDensity f {c} = 0 := by
  rw [withDensity_apply f (measurableSet_singleton c)]
  apply setLIntegral_measure_zero
  apply nonpos_iff_eq_zero.1
  calc (volume.restrict S) {c} ≤ volume {c} := Measure.restrict_apply_le _ _
    _ = 0 := Real.volume_singleton

/-- The surface area measure of an interval of angles along which `v_C⁺` follows a curve `γ`
(through `sigmaFun` and the fundamental theorem of calculus). -/
lemma gm_sigma_Ioc {C : Set (ℝ × ℝ)} (hC : IsConvexBody C) {ψ a b : ℝ} (hab : a ≤ b)
    {γ γ' : ℝ → ℝ × ℝ} {E : Set ℝ} (hE : E.Countable)
    (hv : ∀ t ∈ Icc a b, vplus C (t + ψ) = γ t) (hc : ContinuousOn γ (Icc a b))
    (hd : ∀ t ∈ Ioo a b \ E, HasDerivAt γ (γ' t) t) :
    sigma C (Ioc (a + ψ) (b + ψ)) =
        ∫⁻ t in Ioc a b, ENNReal.ofReal (dot (γ' t) (vvec (t + ψ))) ∧
      ∀ t ∈ Ioo a b \ E, 0 ≤ dot (γ' t) (vvec (t + ψ)) := by
  set ρ : ℝ → ℝ := fun t => dot (γ' t) (vvec (t + ψ)) with hρ
  set F : ℝ → ℝ := fun t => sigmaFun C (t + ψ) with hF
  set I : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..(t + ψ), supp C s with hI
  set G : ℝ → ℝ := fun t => dot (γ t) (vvec (t + ψ)) + I t with hG
  have hcs : Continuous (supp C) := continuous_supp hC.2.1 hC.1
  have hId : ∀ t, HasDerivAt I (supp C (t + ψ)) t := fun t =>
    ((hcs.integral_hasStrictDerivAt 0 (t + ψ)).hasDerivAt).comp_add_const t ψ
  have hIc : Continuous I := continuous_iff_continuousAt.2 fun t => (hId t).continuousAt
  have hFG : ∀ t ∈ Icc a b, F t = G t := by
    intro t ht; simp only [hF, hG, hI, sigmaFun, hv t ht]
  have hGd : ∀ t ∈ Ioo a b \ E, HasDerivAt G (ρ t) t := by
    intro t ht
    have h1 := gm_hasDerivAt_dot (hd t ht) ((gm_hasDerivAt_vvec (t + ψ)).comp_add_const t ψ)
    have h3 := h1.add (hId t)
    convert h3 using 1
    have : dot (γ t) (uvec (t + ψ)) = supp C (t + ψ) := by
      rw [← hv t ⟨ht.1.1.le, ht.1.2.le⟩]; exact dot_vplus_uvec C _
    simp only [hρ, dot_neg_right, this]; ring
  have hFd : ∀ t ∈ Ioo a b \ E, HasDerivAt F (ρ t) t := by
    intro t ht
    apply (hGd t ht).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1.1 ht.1.2] with s hs
    exact hFG s (Ioo_subset_Icc_self hs)
  have hmono : Monotone F := fun x y hxy => monotone_sigmaFun hC (by linarith : x + ψ ≤ y + ψ)
  have hpos : ∀ t ∈ Ioo a b \ E, 0 ≤ ρ t := by
    intro t ht; rw [← (hFd t ht).deriv]; exact hmono.deriv_nonneg
  have hint : IntervalIntegrable ρ volume a b := by
    have h1 : IntervalIntegrable (deriv F) volume a b :=
      (hmono.monotoneOn _).intervalIntegrable_deriv
    apply h1.congr_ae
    rw [uIoc_of_le hab]
    refine gm_ae_restrict_of_countable measurableSet_Ioc (hE.union (countable_singleton b))
      (fun t ht htE => ?_)
    have ht' : t ∈ Ioo a b \ E := ⟨⟨ht.1, lt_of_le_of_ne ht.2 (fun h => htE (Or.inr h))⟩,
      fun h => htE (Or.inl h)⟩
    exact (hFd t ht').deriv
  have hGc : ContinuousOn G (Icc a b) := by
    have hv' : Continuous (fun t => vvec (t + ψ)) := by unfold vvec; fun_prop
    have : ContinuousOn (fun t => dot (γ t) (vvec (t + ψ))) (Icc a b) := by
      unfold dot
      exact ((hc.fst.mul hv'.fst.continuousOn).add (hc.snd.mul hv'.snd.continuousOn))
    exact this.add hIc.continuousOn
  have hftc : ∫ t in a..b, ρ t = G b - G a :=
    integral_eq_of_hasDerivAt_off_countable_of_le G ρ hab hE hGc hGd hint
  refine ⟨?_, hpos⟩
  rw [sigma_Ioc hC, show sigmaFun C (b + ψ) - sigmaFun C (a + ψ) = F b - F a from rfl,
    hFG b ⟨hab, le_rfl⟩, hFG a ⟨le_rfl, hab⟩, ← hftc, intervalIntegral.integral_of_le hab]
  apply ofReal_integral_eq_lintegral_ofReal ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hint)
  refine gm_ae_restrict_of_countable measurableSet_Ioc (hE.union (countable_singleton b))
    (fun t ht htE => ?_)
  exact hpos t ⟨⟨ht.1, lt_of_le_of_ne ht.2 (fun h => htE (Or.inr h))⟩, fun h => htE (Or.inl h)⟩

/-- An atom-free point: `σ_C({t}) = 0` when the edge `e_C(t)` is a point. -/
lemma gm_sigma_singleton {C : Set (ℝ × ℝ)} (hC : IsConvexBody C) {t : ℝ}
    (h : vplus C t = vminus C t) : sigma C {t} = 0 := by
  have h2 := (proposition2_1_2 hC t).1
  rw [h, sub_self] at h2
  have h3 : sigmaAt C t = 0 := by rw [h2]; simp [norm2, dot]
  have hfin : sigma C {t} ≠ ⊤ := (isCompact_singleton.measure_lt_top).ne
  rcases (ENNReal.toReal_eq_zero_iff _).1 h3 with h4 | h4
  · exact h4
  · exact absurd h4 hfin

/-- `σ_C` vanishes between two supporting lines through a common point. -/
lemma gm_sigma_corner {C : Set (ℝ × ℝ)} (hC : IsConvexBody C) {x : ℝ × ℝ} {α β : ℝ}
    (hv : ∀ s ∈ Ioo α β, vplus C s = x) : sigma C (Ioo α β) = 0 := by
  have hU : Ioo α β ⊆ ⋃ n : ℕ, Ioc (α + 1 / ((n : ℝ) + 1)) (β - 1 / ((n : ℝ) + 1)) := by
    intro t ht
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min (sub_pos.2 ht.1) (sub_pos.2 ht.2))
    exact mem_iUnion.2 ⟨n, by linarith [min_le_left (t - α) (β - t)],
      by linarith [min_le_right (t - α) (β - t)]⟩
  apply measure_mono_null hU
  apply measure_iUnion_null
  intro n
  set e : ℝ := 1 / ((n : ℝ) + 1)
  have he : 0 < e := by positivity
  by_cases hn : α + e < β - e
  · have := (gm_sigma_Ioc (ψ := 0) (γ := fun _ => x) (γ' := fun _ => 0) (E := ∅) hC hn.le
      countable_empty (fun t ht => by
        rw [add_zero]; exact hv t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      continuousOn_const (fun t _ => hasDerivAt_const t x)).1
    simp only [add_zero, dot_zero_left, ENNReal.ofReal_zero, lintegral_const, zero_mul] at this
    exact this
  · rw [Ioc_eq_empty hn]; exact measure_empty

/-- **Theorem 8.4.3** (`thm:gerver-left-right`) (1): `𝐃(t) = v_{D_K}^±(3π/2 + t)` on `(t_0, t_2)` and
`𝐁(t) = v_{B_K}^±(π + t)` on `(t_3, t_5)`. -/
theorem theorem8_4_3_one {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (∀ t ∈ Ioo (P.tPt 0) (P.tPt 2), P.curveD t = vplus (leftBody P.φ P.cap) (3 * π / 2 + t) ∧
        P.curveD t = vminus (leftBody P.φ P.cap) (3 * π / 2 + t)) ∧
      ∀ t ∈ Ioo (P.tPt 3) (P.tPt 5), P.curveB t = vplus (rightBody P.φ P.cap) (π + t) ∧
        P.curveB t = vminus (rightBody P.φ P.cap) (π + t) :=
  ⟨fun _ ht => gm_D_vplus_vminus hP hbox ht, fun _ ht => gm_B_vplus_vminus hP hbox ht⟩

/-- **Theorem 8.4.3** (2): `𝐱_K^L = Y_{D_K} = 𝐃(t_2)` and `𝐝_{D_K}` is the curve `𝐃`;
`𝐱_K^R = X_{B_K} = 𝐁(t_3)` (the paper writes `𝐃(t_3)`) and `𝐛_{B_K}` is the curve `𝐁`. -/
theorem theorem8_4_3_two {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    xLeft P.φ P.cap = yD P.φ (leftBody P.φ P.cap) ∧ yD P.φ (leftBody P.φ P.cap) = P.curveD (P.tPt 2) ∧
      tailD P.φ (leftBody P.φ P.cap) = P.curveD '' Icc (P.tPt 0) (P.tPt 2) ∧
      xRight P.φ P.cap = xB P.φ (rightBody P.φ P.cap) ∧
      xB P.φ (rightBody P.φ P.cap) = P.curveB (P.tPt 3) ∧
      tailB P.φ (rightBody P.φ P.cap) = P.curveB '' Icc (P.tPt 3) (P.tPt 5) := by
  have hyD : yD P.φ (leftBody P.φ P.cap) = P.curveD P.θ := gm_D_vminus_end hP hbox
  have hxB : xB P.φ (rightBody P.φ P.cap) = P.curveB (π / 2 - P.θ) := gm_B_vplus_φ hP hbox
  exact ⟨by rw [hyD, gm_D_θ hP hbox], hyD, gm_tailD hP hbox, by rw [hxB, gm_B_c hP hbox], hxB,
    gm_tailB hP hbox⟩

/-- **Theorem 8.4.3** (3): `h_K(π/2 + t) + h_{D_K}(3π/2 + t) = 1` on `[t_0, t_2]` and
`h_K(t) + h_{B_K}(π + t) = 1` on `[t_3, t_5]`. -/
theorem theorem8_4_3_three {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (∀ t ∈ Icc (P.tPt 0) (P.tPt 2),
        supp P.cap (π / 2 + t) + supp (leftBody P.φ P.cap) (3 * π / 2 + t) = 1) ∧
      ∀ t ∈ Icc (P.tPt 3) (P.tPt 5), supp P.cap t + supp (rightBody P.φ P.cap) (π + t) = 1 := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · rw [(gm_D_edge hP hbox ht).1, add_comm (π / 2) t]; ring
  · rw [(gm_B_edge hP hbox ht).1]; ring

/-! ### Proposition 8.4.4 -/

lemma gm_sigmaBreve_apply (C : Set (ℝ × ℝ)) {S : Set ℝ} (hS : MeasurableSet S) :
    sigmaBreve C S = sigma C ((fun t => t - π) ⁻¹' S) :=
  Measure.map_apply (measurable_id.sub_const π) hS

lemma gm_preimage_sub_Ioc (a b c : ℝ) : (fun t => t - c) ⁻¹' Ioc a b = Ioc (a + c) (b + c) := by
  ext t; simp only [mem_preimage, mem_Ioc]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma gm_preimage_sub_Ioo (a b c : ℝ) : (fun t => t - c) ⁻¹' Ioo a b = Ioo (a + c) (b + c) := by
  ext t; simp only [mem_preimage, mem_Ioo]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma gm_preimage_sub_singleton (a c : ℝ) : (fun t => t - c) ⁻¹' {a} = {a + c} := by
  ext t; simp only [mem_preimage, mem_singleton_iff]
  constructor <;> intro h <;> linarith

lemma gm_vvec_sub_pi_div_two (t : ℝ) : vvec t = -uvec (t - π / 2) := by
  have := vvec_add_pi_div_two (t - π / 2)
  rwa [sub_add_cancel] at this

lemma gm_neg_vvec_eq (t : ℝ) : -vvec t = uvec (t - π / 2) := by
  rw [gm_vvec_sub_pi_div_two, neg_neg]

namespace GerverParams

variable {P : GerverParams}

section
variable (hP : P.IsSolution) (hbox : P.InBox)
include hP hbox

lemma gm_injCond1 : InjCond1 P.cap := (theorem6_1_2 hP hbox).1

lemma gm_vplus_cap_A {t : ℝ} (ht : t ∈ Ico 0 (π / 2)) : vplus P.cap t = P.curveA t := by
  have h := ((proposition6_4_5 (gm_isCap hP hbox) (gm_injCond1 hP hbox)).1 t ht).1
  have h2 := gm_aK hP hbox (Ico_subset_Icc_self ht)
  exact h.trans h2

lemma gm_vplus_cap_C {s : ℝ} (hs : s ∈ Icc (π / 2) π) :
    vplus P.cap s = P.curveC (s - π / 2) := by
  have h := gm_cK hP hbox (t := s - π / 2) ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have : vplus P.cap s = cK P.cap (s - π / 2) := by simp only [cK, cPlus, sub_add_cancel]
  rw [this, h]

lemma gm_sigma_cap_zero : sigma P.cap {0} = 0 := by
  obtain ⟨r, s, -, -, -, -, h1, -⟩ := gm_injCond1 hP hbox
  have : (sigma P.cap).restrict (Ico 0 (π / 2)) {0} = 0 := by
    rw [h1]; exact gm_withDensity_singleton _ _
  have hsub : ({0} : Set ℝ) ⊆ Ico 0 (π / 2) := singleton_subset_iff.2 ⟨le_rfl, by positivity⟩
  rwa [Measure.restrict_apply (measurableSet_singleton 0), inter_eq_left.2 hsub] at this

lemma gm_prop844_one : (sigma P.cap).restrict (Ico 0 (π / 2)) =
    (volume.restrict (Ico 0 (π / 2))).withDensity
      (fun t => ENNReal.ofReal (dot (deriv P.curveA t) (vvec t))) := by
  rw [← gm_withDensity_restrict_self measurableSet_Ico]
  apply gm_restrict_Ico_eq (by positivity) (gm_sigma_cap_zero hP hbox)
    (gm_withDensity_singleton _ _)
  · intro a b _ _ _; exact measure_Ioc_lt_top.ne
  · intro a b ha hab hb
    rw [gm_withDensity_Ioc (S := Ico 0 (π / 2)) _
      (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)]
    have := (gm_sigma_Ioc (ψ := 0) (γ := P.curveA) (γ' := deriv P.curveA)
      (gm_isConvexBody_cap hP hbox) hab.le (gm_junctions_countable (P := P))
      (fun t ht => by
        rw [add_zero]; exact gm_vplus_cap_A hP hbox ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (gm_continuous_curveA hP).continuousOn
      (fun t ht => (gm_differentiableAt_curveA hP ht.2).hasDerivAt)).1
    simp only [add_zero] at this
    exact this

lemma gm_prop844_two : (sigmaBreve (rightBody P.φ P.cap)).restrict (Ico (π / 2 - P.θ) (π / 2)) =
    (volume.restrict (Ico (π / 2 - P.θ) (π / 2))).withDensity
      (fun t => ENNReal.ofReal (dot (-deriv P.curveB t) (vvec t))) := by
  have hB := gm_isConvexBody_B hP hbox
  have hcd : π / 2 - P.θ < π / 2 := (gm_c_lt_d hP).trans (gm_d_lt hP)
  rw [← gm_withDensity_restrict_self measurableSet_Ico]
  apply gm_restrict_Ico_eq hcd ?_ (gm_withDensity_singleton _ _)
  · intro a b _ _ _
    rw [gm_sigmaBreve_apply _ measurableSet_Ioc, gm_preimage_sub_Ioc]
    exact measure_Ioc_lt_top.ne
  · intro a b ha hab hb
    rw [gm_withDensity_Ioc (S := Ico (π / 2 - P.θ) (π / 2)) _
      (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩),
      gm_sigmaBreve_apply _ measurableSet_Ioc, gm_preimage_sub_Ioc]
    have := (gm_sigma_Ioc (ψ := π) (γ := P.curveB) (γ' := deriv P.curveB)
      (E := {π / 2 - P.φ}) hB hab.le (countable_singleton _)
      (fun t ht => by
        rw [add_comm]; exact gm_B_vplus hP hbox ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (gm_continuous_curveB hP).continuousOn (fun t ht => ?_)).1
    · rw [this]
      congr 1; funext t; congr 1
      rw [vvec_add_pi, dot_neg_right, dot_neg_left]
    · obtain ⟨c, -, hd⟩ := (theorem8_4_1_tangents hP hbox).1 t
        ⟨show π / 2 - P.θ < t by linarith [ht.1.1], show t < π / 2 by linarith [ht.1.2]⟩ ht.2
      exact hd.differentiableAt.hasDerivAt
  · rw [gm_sigmaBreve_apply _ (measurableSet_singleton _), gm_preimage_sub_singleton,
      add_comm]
    exact gm_sigma_singleton hB (by rw [gm_B_vplus_c hP hbox, gm_B_vminus_c hP hbox])

lemma gm_prop844_three : (sigma P.cap).restrict (Ioc (π / 2) π) =
    (volume.restrict (Ioc (π / 2) π)).withDensity
      (fun t => ENNReal.ofReal (dot (-deriv P.curveC (t - π / 2)) (uvec (t - π / 2)))) := by
  rw [← gm_withDensity_restrict_self measurableSet_Ioc]
  apply gm_restrict_Ioc_eq
  · intro a b _ _ _; exact measure_Ioc_lt_top.ne
  · intro a b ha hab hb
    rw [gm_withDensity_Ioc _ (Ioc_subset_Ioc ha hb)]
    have := (gm_sigma_Ioc (ψ := 0) (γ := fun s => P.curveC (s - π / 2))
      (γ' := fun s => deriv P.curveC (s - π / 2))
      (E := (fun t => t + π / 2) '' {P.φ, P.θ, π / 2 - P.θ, π / 2 - P.φ})
      (gm_isConvexBody_cap hP hbox) hab.le ((gm_junctions_countable (P := P)).image _)
      (fun t ht => by
        rw [add_zero]; exact gm_vplus_cap_C hP hbox ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      ((gm_continuous_curveC hP).comp (continuous_sub_right _)).continuousOn
      (fun t ht => ?_)).1
    · simp only [add_zero] at this
      rw [this]
      congr 1; funext t; congr 1
      rw [gm_vvec_sub_pi_div_two, dot_neg_right, dot_neg_left]
    · have hJ : t - π / 2 ∉ ({P.φ, P.θ, π / 2 - P.θ, π / 2 - P.φ} : Set ℝ) :=
        fun h => ht.2 ⟨t - π / 2, h, by ring⟩
      exact (gm_differentiableAt_curveC hP hJ).hasDerivAt.comp_sub_const t (π / 2)

lemma gm_prop844_four : (sigmaBreve (leftBody P.φ P.cap)).restrict (Ioc (π / 2) (π / 2 + P.θ)) =
    (volume.restrict (Ioc (π / 2) (π / 2 + P.θ))).withDensity
      (fun t => ENNReal.ofReal (dot (deriv P.curveD (t - π / 2)) (uvec (t - π / 2)))) := by
  have hD := gm_isConvexBody_D hP hbox
  rw [← gm_withDensity_restrict_self measurableSet_Ioc]
  apply gm_restrict_Ioc_eq
  · intro a b _ _ _
    rw [gm_sigmaBreve_apply _ measurableSet_Ioc, gm_preimage_sub_Ioc]
    exact measure_Ioc_lt_top.ne
  · intro a b ha hab hb
    rw [gm_withDensity_Ioc _ (Ioc_subset_Ioc ha hb), gm_sigmaBreve_apply _ measurableSet_Ioc,
      gm_preimage_sub_Ioc]
    have := (gm_sigma_Ioc (ψ := π) (γ := fun t => P.curveD (t - π / 2))
      (γ' := fun t => deriv P.curveD (t - π / 2)) (E := {π / 2 + P.φ}) hD hab.le
      (countable_singleton _) (fun t ht => ?_)
      ((gm_continuous_curveD hP).comp (continuous_sub_right _)).continuousOn
      (fun t ht => ?_)).1
    · rw [this]
      congr 1; funext t; congr 1
      rw [vvec_add_pi, gm_neg_vvec_eq]
    · have := gm_D_vplus hP hbox (t := t - π / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩
      rwa [show 3 * π / 2 + (t - π / 2) = t + π by ring] at this
    · have ht' : t - π / 2 ∈ Ioo (P.tPt 0) (P.tPt 2) :=
        ⟨show 0 < t - π / 2 by linarith [ht.1.1], show t - π / 2 < P.θ by linarith [ht.1.2]⟩
      have hne : t - π / 2 ≠ P.tPt 1 := fun h => ht.2 (by
        rw [mem_singleton_iff]; change t - π / 2 = P.φ at h; linarith)
      obtain ⟨c, -, hd⟩ := (theorem8_4_1_tangents hP hbox).2 (t - π / 2) ht' hne
      exact hd.differentiableAt.hasDerivAt.comp_sub_const t (π / 2)

end

end GerverParams

/-- **Proposition 8.4.4** (`pro:measure-translation`): the surface area measures of `K`, `B_K`, `D_K`
in terms of the boundary curves.

The paper states (4) on `(t₀, t₂]` with `⟨𝐃'(t), u_t⟩`; as `𝐃(s) = v_{D_K}(3π/2 + s)`, the measure
`σ̆_D` lives at `π/2 + s` (as Theorem 8.4.5 uses), which we state. -/
theorem proposition8_4_4 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (sigma P.cap).restrict (Ico 0 (π / 2)) =
        (volume.restrict (Ico 0 (π / 2))).withDensity
          (fun t => ENNReal.ofReal (dot (deriv P.curveA t) (vvec t))) ∧
      (sigmaBreve (rightBody P.φ P.cap)).restrict (Ico (P.tPt 3) (P.tPt 5)) =
        (volume.restrict (Ico (P.tPt 3) (P.tPt 5))).withDensity
          (fun t => ENNReal.ofReal (dot (-deriv P.curveB t) (vvec t))) ∧
      (sigma P.cap).restrict (Ioc (π / 2) π) =
        (volume.restrict (Ioc (π / 2) π)).withDensity
          (fun t => ENNReal.ofReal (dot (-deriv P.curveC (t - π / 2)) (uvec (t - π / 2)))) ∧
      (sigmaBreve (leftBody P.φ P.cap)).restrict (Ioc (π / 2 + P.tPt 0) (π / 2 + P.tPt 2)) =
        (volume.restrict (Ioc (π / 2 + P.tPt 0) (π / 2 + P.tPt 2))).withDensity
          (fun t => ENNReal.ofReal (dot (deriv P.curveD (t - π / 2)) (uvec (t - π / 2)))) := by
  have e : π / 2 + P.tPt 0 = π / 2 := add_zero _
  refine ⟨gm_prop844_one hP hbox, gm_prop844_two hP hbox, gm_prop844_three hP hbox, ?_⟩
  rw [e]; exact gm_prop844_four hP hbox

/-- The intervals `J_i = [t_{i-1}, t_i)` for `1 ≤ i ≤ 5` and `J_i = π - J_{11 - i}` for `6 ≤ i ≤ 10`
(Definition 8.4.7, `def:interval-j`). -/
noncomputable def GerverParams.jInt (P : GerverParams) (i : ℕ) : Set ℝ :=
  if i ≤ 5 then Ico (P.tPt (i - 1)) (P.tPt i)
  else (fun s => π - s) '' Ico (P.tPt (10 - i)) (P.tPt (11 - i))

/-! ### Theorem 8.4.5 -/

lemma gm_image_pi_sub_Ico (a b : ℝ) : (fun s => π - s) '' Ico a b = Ioc (π - b) (π - a) := by
  ext t; simp only [mem_image, mem_Ico, mem_Ioc]
  constructor
  · rintro ⟨s, ⟨h1, h2⟩, rfl⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; exact ⟨π - t, ⟨by linarith, by linarith⟩, by ring⟩

lemma gm_measurable_dot {f g : ℝ → ℝ × ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun t => dot (f t) (g t)) := by
  unfold dot; fun_prop

lemma gm_withDensity_congr {T : Set ℝ} (hT : MeasurableSet T) {E : Set ℝ} (hE : E.Countable)
    {f g : ℝ → ℝ≥0∞} (h : ∀ t ∈ T, t ∉ E → f t = g t) :
    (volume.restrict T).withDensity f = (volume.restrict T).withDensity g :=
  withDensity_congr_ae (gm_ae_restrict_of_countable hT hE h)

namespace GerverParams

variable {P : GerverParams}

lemma gm_jInt_1 (P : GerverParams) : P.jInt 1 = Ico 0 P.φ := rfl
lemma gm_jInt_2 (P : GerverParams) : P.jInt 2 = Ico P.φ P.θ := rfl
lemma gm_jInt_3 (P : GerverParams) : P.jInt 3 = Ico P.θ (π / 2 - P.θ) := rfl
lemma gm_jInt_4 (P : GerverParams) : P.jInt 4 = Ico (π / 2 - P.θ) (π / 2 - P.φ) := rfl
lemma gm_jInt_5 (P : GerverParams) : P.jInt 5 = Ico (π / 2 - P.φ) (π / 2) := rfl
lemma gm_jInt_6 (P : GerverParams) : P.jInt 6 = Ioc (π / 2) (π / 2 + P.φ) := by
  show (fun s => π - s) '' Ico (π / 2 - P.φ) (π / 2) = _
  rw [gm_image_pi_sub_Ico]; congr 1 <;> ring
lemma gm_jInt_7 (P : GerverParams) : P.jInt 7 = Ioc (π / 2 + P.φ) (π / 2 + P.θ) := by
  show (fun s => π - s) '' Ico (π / 2 - P.θ) (π / 2 - P.φ) = _
  rw [gm_image_pi_sub_Ico]; congr 1 <;> ring
lemma gm_jInt_8 (P : GerverParams) : P.jInt 8 = Ioc (π / 2 + P.θ) (π - P.θ) := by
  show (fun s => π - s) '' Ico P.θ (π / 2 - P.θ) = _
  rw [gm_image_pi_sub_Ico]; congr 1; ring
lemma gm_jInt_9 (P : GerverParams) : P.jInt 9 = Ioc (π - P.θ) (π - P.φ) := by
  show (fun s => π - s) '' Ico P.φ P.θ = _
  rw [gm_image_pi_sub_Ico]
lemma gm_jInt_10 (P : GerverParams) : P.jInt 10 = Ioc (π - P.φ) π := by
  show (fun s => π - s) '' Ico 0 P.φ = _
  rw [gm_image_pi_sub_Ico, sub_zero]

section
variable (hP : P.IsSolution) (hbox : P.InBox)
include hP hbox

lemma gm_sigma_restrict_A {T : Set ℝ} (hT : MeasurableSet T) (hTS : T ⊆ Ico 0 (π / 2)) :
    (sigma P.cap).restrict T = (volume.restrict T).withDensity
      (fun t => ENNReal.ofReal (dot (deriv P.curveA t) (vvec t))) := by
  rw [← Measure.restrict_restrict_of_subset hTS, gm_prop844_one hP hbox, restrict_withDensity hT,
    Measure.restrict_restrict_of_subset hTS]

lemma gm_sigma_restrict_C {T : Set ℝ} (hT : MeasurableSet T) (hTS : T ⊆ Ioc (π / 2) π) :
    (sigma P.cap).restrict T = (volume.restrict T).withDensity
      (fun t => ENNReal.ofReal (dot (-deriv P.curveC (t - π / 2)) (uvec (t - π / 2)))) := by
  rw [← Measure.restrict_restrict_of_subset hTS, gm_prop844_three hP hbox,
    restrict_withDensity hT, Measure.restrict_restrict_of_subset hTS]

lemma gm_sigmaBreve_restrict_B {T : Set ℝ} (hT : MeasurableSet T)
    (hTS : T ⊆ Ico (π / 2 - P.θ) (π / 2)) :
    (sigmaBreve (rightBody P.φ P.cap)).restrict T = (volume.restrict T).withDensity
      (fun t => ENNReal.ofReal (dot (-deriv P.curveB t) (vvec t))) := by
  rw [← Measure.restrict_restrict_of_subset hTS, gm_prop844_two hP hbox,
    restrict_withDensity hT, Measure.restrict_restrict_of_subset hTS]

lemma gm_sigmaBreve_restrict_D {T : Set ℝ} (hT : MeasurableSet T)
    (hTS : T ⊆ Ioc (π / 2) (π / 2 + P.θ)) :
    (sigmaBreve (leftBody P.φ P.cap)).restrict T = (volume.restrict T).withDensity
      (fun t => ENNReal.ofReal (dot (deriv P.curveD (t - π / 2)) (uvec (t - π / 2)))) := by
  rw [← Measure.restrict_restrict_of_subset hTS, gm_prop844_four hP hbox,
    restrict_withDensity hT, Measure.restrict_restrict_of_subset hTS]

omit hP hbox in
lemma gm_iota_restrict {K : Set (ℝ × ℝ)} {T : Set ℝ} (hT : MeasurableSet T)
    (hTS : T ⊆ Icc 0 π) :
    (iota K).restrict T = (volume.restrict T).withDensity (fun t => ENNReal.ofReal (iFun K t)) := by
  unfold iota; rw [restrict_withDensity hT, Measure.restrict_restrict_of_subset hTS]

lemma gm_deriv_innerCorner {t : ℝ} (ht : t ∈ Ioo 0 (π / 2)) :
    deriv (innerCorner P.cap) t = deriv P.path t := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact gm_innerCorner hP hbox (Ioo_subset_Icc_self hs)

lemma gm_iFun_lo {t : ℝ} (ht : t ∈ Ioo 0 (π / 2)) :
    iFun P.cap t = dot (deriv P.path t) (vvec t) := by
  rw [iFun, ite_eq_left ht.2.le, gm_deriv_innerCorner hP hbox ht]

lemma gm_iFun_hi {t : ℝ} (ht : t ∈ Ioo (π / 2) π) :
    iFun P.cap t = dot (-deriv P.path (t - π / 2)) (uvec (t - π / 2)) := by
  rw [iFun, ite_eq_right (not_le.2 ht.1),
    gm_deriv_innerCorner hP hbox ⟨by linarith [ht.1], by linarith [ht.2]⟩, dot_neg_left]

lemma gm_iFun_lo_pos {t : ℝ} (ht : t ∈ Ioo 0 (π / 2)) : 0 ≤ dot (deriv P.path t) (vvec t) := by
  rw [← gm_deriv_innerCorner hP hbox ht]
  exact ((theorem6_1_2 hP hbox).2.2 t ht).2.le

lemma gm_iFun_hi_pos {τ : ℝ} (hτ : τ ∈ Ioo 0 (π / 2)) :
    0 ≤ dot (-deriv P.path τ) (uvec τ) := by
  rw [← gm_deriv_innerCorner hP hbox hτ, dot_neg_left]
  linarith [((theorem6_1_2 hP hbox).2.2 τ hτ).1]

lemma gm_rhoB_pos {t : ℝ} (ht : t ∈ Ioo (π / 2 - P.θ) (π / 2)) (htd : t ≠ π / 2 - P.φ) :
    0 ≤ dot (-deriv P.curveB t) (vvec t) := by
  obtain ⟨c, hc, hd⟩ := (theorem8_4_1_tangents hP hbox).1 t ht htd
  rw [hd.deriv, dot_neg_left, dot_smul_left, dot_vvec_self]
  linarith

lemma gm_rhoD_pos {t : ℝ} (ht : t ∈ Ioo 0 P.θ) (htd : t ≠ P.φ) :
    0 ≤ dot (deriv P.curveD t) (uvec t) := by
  obtain ⟨c, hc, hd⟩ := (theorem8_4_1_tangents hP hbox).2 t ht htd
  rw [hd.deriv, dot_smul_left, dot_uvec_self]
  linarith

omit hP hbox in
lemma gm_measurable_rhoB : Measurable (fun t => ENNReal.ofReal (dot (-deriv P.curveB t) (vvec t))) :=
  (gm_measurable_dot (measurable_deriv _).neg (by unfold vvec; fun_prop)).ennreal_ofReal

omit hP hbox in
lemma gm_measurable_rhoD :
    Measurable (fun t => ENNReal.ofReal (dot (deriv P.curveD (t - π / 2)) (uvec (t - π / 2)))) :=
  (gm_measurable_dot ((measurable_deriv _).comp (measurable_id.sub_const _))
    (by unfold uvec; fun_prop)).ennreal_ofReal

end

end GerverParams

/-- **Theorem 8.4.5** (`thm:upper-bound-q-gerver`): Romik's ODEs as equalities of measures. -/
theorem theorem8_4_5 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (sigma P.cap).restrict (P.jInt 1) = 0 ∧
      (sigma P.cap).restrict (P.jInt 2 ∪ P.jInt 3) = (iota P.cap).restrict (P.jInt 2 ∪ P.jInt 3) ∧
      (sigma P.cap).restrict (P.jInt 4) =
        (sigmaBreve (rightBody P.φ P.cap)).restrict (P.jInt 4) + (iota P.cap).restrict (P.jInt 4) ∧
      (sigma P.cap).restrict (P.jInt 5) = (sigmaBreve (rightBody P.φ P.cap)).restrict (P.jInt 5) ∧
      (sigma P.cap).restrict (P.jInt 6) = (sigmaBreve (leftBody P.φ P.cap)).restrict (P.jInt 6) ∧
      (sigma P.cap).restrict (P.jInt 7) =
        (sigmaBreve (leftBody P.φ P.cap)).restrict (P.jInt 7) + (iota P.cap).restrict (P.jInt 7) ∧
      (sigma P.cap).restrict (P.jInt 8 ∪ P.jInt 9) = (iota P.cap).restrict (P.jInt 8 ∪ P.jInt 9) ∧
      (sigma P.cap).restrict (P.jInt 10) = 0 := by
  have h01 := gm_φ_pos hP
  have h12 := gm_φ_lt_θ hP
  have h23 := gm_θ_lt_c hP
  have h34 := gm_c_lt_d hP
  have h45 := gm_d_lt hP
  have hode := theorem8_4_2 hP hbox
  rw [gm_jInt_1, gm_jInt_2, gm_jInt_3, gm_jInt_4, gm_jInt_5, gm_jInt_6, gm_jInt_7, gm_jInt_8,
    gm_jInt_9, gm_jInt_10]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `J_1`
    rw [gm_sigma_restrict_A hP hbox measurableSet_Ico
      (Ico_subset_Ico le_rfl (by linarith)), ← withDensity_zero]
    apply gm_withDensity_congr measurableSet_Ico (countable_singleton 0)
    intro t ht ht0
    have ht' : t ∈ Ioo (P.tPt 0) (P.tPt 1) := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩
    simp only [Pi.zero_apply, (hode.1 t ht').1, ENNReal.ofReal_zero]
  · -- `J_2 ∪ J_3`
    have hT : Ico P.φ P.θ ∪ Ico P.θ (π / 2 - P.θ) ⊆ Ico 0 (π / 2) := by
      rintro t (ht | ht) <;> exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hm : MeasurableSet (Ico P.φ P.θ ∪ Ico P.θ (π / 2 - P.θ)) :=
      measurableSet_Ico.union measurableSet_Ico
    rw [gm_sigma_restrict_A hP hbox hm hT,
      gm_iota_restrict hm (hT.trans (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl (by linarith))))]
    apply gm_withDensity_congr hm ((countable_singleton P.φ).insert P.θ)
    intro t ht htE
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at htE
    have hlo : t ∈ Ioo 0 (π / 2) := ⟨by rcases ht with ht | ht <;> linarith [ht.1],
      by rcases ht with ht | ht <;> linarith [ht.2]⟩
    rw [gm_iFun_lo hP hbox hlo]
    rcases ht with ht | ht
    · rw [(hode.2.1 t ⟨lt_of_le_of_ne ht.1 (Ne.symm htE.2), ht.2⟩).1]
    · rw [(hode.2.2.1 t ⟨lt_of_le_of_ne ht.1 (Ne.symm htE.1), ht.2⟩).1]
  · -- `J_4`
    have hT : Ico (π / 2 - P.θ) (π / 2 - P.φ) ⊆ Ico 0 (π / 2) :=
      Ico_subset_Ico (by linarith) h45.le
    rw [gm_sigma_restrict_A hP hbox measurableSet_Ico hT,
      gm_sigmaBreve_restrict_B hP hbox measurableSet_Ico (Ico_subset_Ico le_rfl h45.le),
      gm_iota_restrict measurableSet_Ico
        (hT.trans (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl (by linarith)))),
      ← withDensity_add_left (gm_measurable_rhoB (P := P))]
    apply gm_withDensity_congr measurableSet_Ico (countable_singleton (π / 2 - P.θ))
    intro t ht htE
    have ht' : t ∈ Ioo (P.tPt 3) (P.tPt 4) := ⟨lt_of_le_of_ne ht.1 (Ne.symm htE), ht.2⟩
    have hlo : t ∈ Ioo 0 (π / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simp only [Pi.add_apply]
    rw [gm_iFun_lo hP hbox hlo, (hode.2.2.2.1 t ht').1, dot_add_left,
      ENNReal.ofReal_add (gm_rhoB_pos hP hbox ⟨ht'.1, by linarith [ht.2]⟩ (ne_of_lt ht.2))
        (gm_iFun_lo_pos hP hbox hlo)]
  · -- `J_5`
    rw [gm_sigma_restrict_A hP hbox measurableSet_Ico (Ico_subset_Ico (by linarith) le_rfl),
      gm_sigmaBreve_restrict_B hP hbox measurableSet_Ico (Ico_subset_Ico h34.le le_rfl)]
    apply gm_withDensity_congr measurableSet_Ico (countable_singleton (π / 2 - P.φ))
    intro t ht htE
    have ht' : t ∈ Ioo (P.tPt 4) (P.tPt 5) := ⟨lt_of_le_of_ne ht.1 (Ne.symm htE), ht.2⟩
    rw [(hode.2.2.2.2 t ht').1]
  · -- `J_6`
    rw [gm_sigma_restrict_C hP hbox measurableSet_Ioc (Ioc_subset_Ioc le_rfl (by linarith)),
      gm_sigmaBreve_restrict_D hP hbox measurableSet_Ioc (Ioc_subset_Ioc le_rfl (by linarith))]
    apply gm_withDensity_congr measurableSet_Ioc (countable_singleton (π / 2 + P.φ))
    intro t ht htE
    have ht' : t - π / 2 ∈ Ioo (P.tPt 0) (P.tPt 1) :=
      ⟨show 0 < t - π / 2 by linarith [ht.1],
        show t - π / 2 < P.φ by linarith [lt_of_le_of_ne ht.2 htE]⟩
    rw [(hode.1 _ ht').2]
  · -- `J_7`
    have hT : Ioc (π / 2 + P.φ) (π / 2 + P.θ) ⊆ Ioc (π / 2) π :=
      Ioc_subset_Ioc (by linarith) (by linarith)
    rw [gm_sigma_restrict_C hP hbox measurableSet_Ioc hT,
      gm_sigmaBreve_restrict_D hP hbox measurableSet_Ioc (Ioc_subset_Ioc (by linarith) le_rfl),
      gm_iota_restrict measurableSet_Ioc (hT.trans Ioc_subset_Icc_self |>.trans
        (Icc_subset_Icc (by linarith) le_rfl)),
      ← withDensity_add_left (gm_measurable_rhoD (P := P))]
    apply gm_withDensity_congr measurableSet_Ioc (countable_singleton (π / 2 + P.θ))
    intro t ht htE
    have ht' : t - π / 2 ∈ Ioo (P.tPt 1) (P.tPt 2) :=
      ⟨show P.φ < t - π / 2 by linarith [ht.1],
        show t - π / 2 < P.θ by linarith [lt_of_le_of_ne ht.2 htE]⟩
    have hhi : t ∈ Ioo (π / 2) π := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hτ : t - π / 2 ∈ Ioo 0 (π / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have key : dot (deriv P.curveD (t - π / 2) - deriv P.path (t - π / 2)) (uvec (t - π / 2)) =
        dot (deriv P.curveD (t - π / 2)) (uvec (t - π / 2)) +
          dot (-deriv P.path (t - π / 2)) (uvec (t - π / 2)) := by
      rw [dot_sub_left, dot_neg_left]; ring
    simp only [Pi.add_apply]
    rw [gm_iFun_hi hP hbox hhi, (hode.2.1 _ ht').2, key,
      ENNReal.ofReal_add (gm_rhoD_pos hP hbox ⟨by linarith [ht.1], ht'.2⟩ (ne_of_gt ht'.1))
        (gm_iFun_hi_pos hP hbox hτ)]
  · -- `J_8 ∪ J_9`
    have hT : Ioc (π / 2 + P.θ) (π - P.θ) ∪ Ioc (π - P.θ) (π - P.φ) ⊆ Ioc (π / 2) π := by
      rintro t (ht | ht) <;> exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hm : MeasurableSet (Ioc (π / 2 + P.θ) (π - P.θ) ∪ Ioc (π - P.θ) (π - P.φ)) :=
      measurableSet_Ioc.union measurableSet_Ioc
    rw [gm_sigma_restrict_C hP hbox hm hT, gm_iota_restrict hm (hT.trans Ioc_subset_Icc_self |>.trans
        (Icc_subset_Icc (by linarith) le_rfl))]
    apply gm_withDensity_congr hm ((countable_singleton (π - P.θ)).insert (π - P.φ))
    intro t ht htE
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at htE
    have hhi : t ∈ Ioo (π / 2) π := ⟨by rcases ht with ht | ht <;> linarith [ht.1],
      by rcases ht with ht | ht <;> linarith [ht.2]⟩
    rw [gm_iFun_hi hP hbox hhi]
    rcases ht with ht | ht
    · have ht' : t - π / 2 ∈ Ioo (P.tPt 2) (P.tPt 3) :=
        ⟨show P.θ < t - π / 2 by linarith [ht.1],
          show t - π / 2 < π / 2 - P.θ by linarith [lt_of_le_of_ne ht.2 htE.2]⟩
      rw [(hode.2.2.1 _ ht').2]
    · have ht' : t - π / 2 ∈ Ioo (P.tPt 3) (P.tPt 4) :=
        ⟨show π / 2 - P.θ < t - π / 2 by linarith [ht.1],
          show t - π / 2 < π / 2 - P.φ by linarith [lt_of_le_of_ne ht.2 htE.1]⟩
      rw [(hode.2.2.2.1 _ ht').2]
  · -- `J_10`
    rw [gm_sigma_restrict_C hP hbox measurableSet_Ioc (Ioc_subset_Ioc (by linarith) le_rfl),
      ← withDensity_zero]
    apply gm_withDensity_congr measurableSet_Ioc (countable_singleton π)
    intro t ht htE
    have ht' : t - π / 2 ∈ Ioo (P.tPt 4) (P.tPt 5) :=
      ⟨show π / 2 - P.φ < t - π / 2 by linarith [ht.1],
        show t - π / 2 < π / 2 by linarith [lt_of_le_of_ne ht.2 htE]⟩
    simp only [Pi.zero_apply, (hode.2.2.2.2 _ ht').2, ENNReal.ofReal_zero]

/-! ### Theorem 8.4.6 -/

lemma gm_bv_union {f : ℝ → ℝ × ℝ} {a m b : ℝ} (ham : a ≤ m) (hmb : m ≤ b)
    (h1 : BoundedVariationOn f (Icc a m)) (h2 : BoundedVariationOn f (Icc m b)) :
    BoundedVariationOn f (Icc a b) := by
  have := eVariationOn.Icc_add_Icc f (s := univ) ham hmb (mem_univ m)
  simp only [univ_inter] at this
  unfold BoundedVariationOn at *
  rw [← this]
  exact ENNReal.add_ne_top.2 ⟨h1, h2⟩

lemma gm_bv_of_contDiffOn {f : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ 1 f (Icc a b)) : BoundedVariationOn f (Icc a b) := by
  rw [← uIcc_of_le hab] at hf ⊢
  exact hf.absolutelyContinuousOnInterval.boundedVariationOn

lemma gm_continuousOn_cross {f g : ℝ → ℝ × ℝ} {s : Set ℝ} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (fun t => cross (f t) (g t)) s := by
  unfold cross
  exact (hf.fst.mul hg.snd).sub (hf.snd.mul hg.fst)

/-- The curve area functional of a curve which is `C¹` on two adjacent closed intervals. -/
lemma gm_curveArea_two {x : ℝ → ℝ × ℝ} {a m b : ℝ} (ham : a < m) (hmb : m < b)
    (hc : ContinuousOn x (Icc a b)) (h1 : ContDiffOn ℝ 1 x (Icc a m))
    (h2 : ContDiffOn ℝ 1 x (Icc m b)) {ρ : ℝ → ℝ}
    (hρ : ∀ t ∈ Ioo a b, t ≠ m → cross (x t) (deriv x t) = ρ t) :
    curveArea x a b = (1 / 2) * ∫ t in a..b, ρ t := by
  have hcbv : IsCBV x a b :=
    ⟨hc, gm_bv_union ham.le hmb.le (gm_bv_of_contDiffOn ham.le h1) (gm_bv_of_contDiffOn hmb.le h2)⟩
  have piece : ∀ {u v : ℝ}, u < v → ContDiffOn ℝ 1 x (Icc u v) → Ioo u v ⊆ Ioo a b →
      m ∉ Ioo u v →
      (∫ t in u..v, cross (x t) (derivWithin x (Icc u v) t)) = (∫ t in u..v, ρ t) ∧
        IntervalIntegrable ρ volume u v := by
    intro u v huv hx hsub hm
    have hint : IntervalIntegrable (fun t => cross (x t) (derivWithin x (Icc u v) t)) volume u v := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le huv.le]
      exact gm_continuousOn_cross hx.continuousOn (hx.continuousOn_derivWithin (uniqueDiffOn_Icc huv) le_rfl)
    have hae : ∀ᵐ t ∂volume, t ∈ Ι u v →
        cross (x t) (derivWithin x (Icc u v) t) = ρ t := by
      filter_upwards [(countable_singleton v).ae_notMem volume] with t htv ht
      rw [uIoc_of_le huv.le] at ht
      have ht' : t ∈ Ioo u v := ⟨ht.1, lt_of_le_of_ne ht.2 htv⟩
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht'.1 ht'.2)]
      exact hρ t (hsub ht') (fun h => hm (h ▸ ht'))
    refine ⟨intervalIntegral.integral_congr_ae hae, hint.congr_ae ?_⟩
    rw [EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact hae
  obtain ⟨e1, i1⟩ := piece ham h1 (Ioo_subset_Ioo le_rfl hmb.le) (fun h => lt_irrefl _ h.2)
  obtain ⟨e2, i2⟩ := piece hmb h2 (Ioo_subset_Ioo ham.le le_rfl) (fun h => lt_irrefl _ h.1)
  rw [proposition7_2_6 ham.le hmb.le hcbv, curveArea_eq_integral ham.le h1,
    curveArea_eq_integral hmb.le h2, e1, e2, ← mul_add,
    intervalIntegral.integral_add_adjacent_intervals i1 i2]

/-- The curve area functional only depends on the curve on `[a, b]` (for `C¹` curves). -/
lemma gm_curveArea_congr {x y : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a ≤ b)
    (hx : ContDiffOn ℝ 1 x (Icc a b)) (h : EqOn x y (Icc a b)) :
    curveArea x a b = curveArea y a b := by
  rw [curveArea_eq_integral hab hx, curveArea_eq_integral hab (hx.congr fun t ht => (h ht).symm)]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  simp only
  rw [h ht, derivWithin_congr (fun s hs => (h hs).symm) (h ht).symm]

namespace GerverParams

variable {P : GerverParams}

section
variable (hP : P.IsSolution) (hbox : P.InBox)
include hP hbox

omit hbox in
lemma gm_contDiffOn_B₄ : ContDiffOn ℝ 1 P.curveB (Icc (π / 2 - P.θ) (π / 2 - P.φ)) :=
  (gm_contDiff_contactB (P.gm_contDiff_x₄.of_le (by simp))).contDiffOn.congr fun t ht => by
    simp only [curveB, contactB, gm_path_eq_x₄ hP ht, gm_dpath_eq_x₄ hP ht]

omit hbox in
lemma gm_contDiffOn_B₅ : ContDiffOn ℝ 1 P.curveB (Icc (π / 2 - P.φ) (π / 2)) :=
  (gm_contDiff_contactB (P.gm_contDiff_x₅.of_le (by simp))).contDiffOn.congr fun t ht => by
    simp only [curveB, contactB, gm_path_eq_x₅ hP ht.1, gm_dpath_eq_x₅ hP ht.1]

omit hbox in
lemma gm_contDiffOn_D₁ : ContDiffOn ℝ 1 P.curveD (Icc 0 P.φ) :=
  (gm_contDiff_contactD (P.gm_contDiff_x₁.of_le (by simp))).contDiffOn.congr fun t ht => by
    simp only [curveD, contactD, gm_path_eq_x₁ hP ht.2, gm_dpath_eq_x₁ hP ht.2]

omit hbox in
lemma gm_contDiffOn_D₂ : ContDiffOn ℝ 1 P.curveD (Icc P.φ P.θ) :=
  (gm_contDiff_contactD (P.gm_contDiff_x₂.of_le (by simp))).contDiffOn.congr fun t ht => by
    simp only [curveD, contactD, gm_path_eq_x₂ hP ht, gm_dpath_eq_x₂ hP ht]

lemma gm_curveArea_B : curveArea P.curveB (π / 2 - P.θ) (π / 2) =
    (1 / 2) * ∫ t in (π / 2 - P.θ)..(π / 2),
      dot (-deriv P.curveB t) (vvec t) * supp (rightBody P.φ P.cap) (t + π) := by
  apply gm_curveArea_two (gm_c_lt_d hP) (gm_d_lt hP) (gm_continuous_curveB hP).continuousOn
    (gm_contDiffOn_B₄ hP) (gm_contDiffOn_B₅ hP)
  intro t ht htd
  obtain ⟨c, -, hd⟩ := (theorem8_4_1_tangents hP hbox).1 t ht htd
  rw [hd.deriv, cross_smul_right, cross_vvec, gm_B_wallB hP hbox ⟨ht.1.le, ht.2.le⟩,
    dot_neg_left, dot_smul_left, dot_vvec_self, add_comm t π,
    (gm_B_edge hP hbox ⟨ht.1.le, ht.2.le⟩).1]
  ring

lemma gm_curveArea_D : curveArea P.curveD 0 P.θ =
    (1 / 2) * ∫ t in (0 : ℝ)..P.θ,
      dot (deriv P.curveD t) (uvec t) * supp (leftBody P.φ P.cap) (3 * π / 2 + t) := by
  apply gm_curveArea_two (gm_φ_pos hP) (gm_φ_lt_θ hP) (gm_continuous_curveD hP).continuousOn
    (gm_contDiffOn_D₁ hP) (gm_contDiffOn_D₂ hP)
  intro t ht htd
  obtain ⟨c, -, hd⟩ := (theorem8_4_1_tangents hP hbox).2 t ht htd
  have hw := gm_D_wallD hP hbox ⟨ht.1.le, ht.2.le⟩
  rw [uvec_add_pi_div_two] at hw
  rw [hd.deriv, cross_smul_right, cross_uvec, hw, dot_smul_left, dot_uvec_self,
    (gm_D_edge hP hbox ⟨ht.1.le, ht.2.le⟩).1]
  ring

/-- `σ̆_{B_K}` vanishes on `(φ, t_3)`. -/
lemma gm_sigmaBreve_B_restrict :
    (sigmaBreve (rightBody P.φ P.cap)).restrict (Ioo P.φ (π / 2)) =
      (sigmaBreve (rightBody P.φ P.cap)).restrict (Ico (π / 2 - P.θ) (π / 2)) := by
  have hφc := gm_φ_le_c hP
  have hc2 : π / 2 - P.θ < π / 2 := (gm_c_lt_d hP).trans (gm_d_lt hP)
  have e : Ioo P.φ (π / 2) = Ioo P.φ (π / 2 - P.θ) ∪ Ico (π / 2 - P.θ) (π / 2) :=
    (Ioo_union_Ico_eq_Ioo (by linarith [gm_θ_lt hP, gm_φ_lt_θ hP]) hc2.le).symm
  have hz : sigmaBreve (rightBody P.φ P.cap) (Ioo P.φ (π / 2 - P.θ)) = 0 := by
    rw [gm_sigmaBreve_apply _ measurableSet_Ioo, gm_preimage_sub_Ioo, add_comm P.φ,
      add_comm (π / 2 - P.θ)]
    apply gm_sigma_corner (gm_isConvexBody_B hP hbox) (x := P.curveB (π / 2 - P.θ))
    intro s hs
    have := vplus_mem_edge (gm_isConvexBody_B hP hbox) s
    rwa [gm_B_corner hP hbox s hs] at this
  rw [e, Measure.restrict_union
    (Set.disjoint_left.2 fun t h1 h2 => absurd h2.1 (not_le.2 h1.2)) measurableSet_Ico,
    Measure.restrict_eq_zero.2 hz, zero_add]

/-- `σ̆_{D_K}` vanishes on `(π/2 + t_2, π - φ)`. -/
lemma gm_sigmaBreve_D_restrict :
    (sigmaBreve (leftBody P.φ P.cap)).restrict (Ioo (π / 2) (π / 2 + (π / 2 - P.φ))) =
      (sigmaBreve (leftBody P.φ P.cap)).restrict (Ioc (π / 2) (π / 2 + P.θ)) := by
  have hθ := gm_θ_le hP
  have hθ' : P.θ < π / 2 - P.φ := by linarith [gm_θ_lt hP, gm_φ_lt_θ hP]
  have e : Ioo (π / 2) (π / 2 + (π / 2 - P.φ)) =
      Ioc (π / 2) (π / 2 + P.θ) ∪ Ioo (π / 2 + P.θ) (π / 2 + (π / 2 - P.φ)) :=
    (Ioc_union_Ioo_eq_Ioo (by linarith [gm_θ_pos hP]) (by linarith)).symm
  have hz : sigmaBreve (leftBody P.φ P.cap) (Ioo (π / 2 + P.θ) (π / 2 + (π / 2 - P.φ))) = 0 := by
    rw [gm_sigmaBreve_apply _ measurableSet_Ioo, gm_preimage_sub_Ioo,
      show π / 2 + P.θ + π = 3 * π / 2 + P.θ by ring,
      show π / 2 + (π / 2 - P.φ) + π = 3 * π / 2 + (π / 2 - P.φ) by ring]
    apply gm_sigma_corner (gm_isConvexBody_D hP hbox) (x := P.curveD P.θ)
    intro s hs
    have := vplus_mem_edge (gm_isConvexBody_D hP hbox) s
    rwa [gm_D_corner hP hbox s hs] at this
  rw [e, Measure.restrict_union
    (Set.disjoint_left.2 fun t h1 h2 => absurd h1.2 (not_le.2 h2.1)) measurableSet_Ioo,
    Measure.restrict_eq_zero.2 hz, add_zero]

end

end GerverParams

namespace GerverParams

variable {P : GerverParams}

section
variable (hP : P.IsSolution) (hbox : P.InBox)
include hP hbox

lemma gm_convexCurveArea_B : convexCurveArea (rightBody P.φ P.cap) (π + P.φ) (3 * π / 2) =
    (1 / 2) * ∫ t in (π / 2 - P.θ)..(π / 2),
      dot (-deriv P.curveB t) (vvec t) * supp (rightBody P.φ P.cap) (t + π) := by
  have hB := gm_isConvexBody_B hP hbox
  have hc2 : π / 2 - P.θ < π / 2 := (gm_c_lt_d hP).trans (gm_d_lt hP)
  have hcont : Continuous (suppBreve (rightBody P.φ P.cap)) :=
    (continuous_supp hB.2.1 hB.1).comp (continuous_id.add continuous_const)
  unfold convexCurveArea
  congr 1
  have h1 : ∫ t in Ioo (π + P.φ) (3 * π / 2), supp (rightBody P.φ P.cap) t
        ∂(sigma (rightBody P.φ P.cap)) =
      ∫ t in Ioo P.φ (π / 2), suppBreve (rightBody P.φ P.cap) t
        ∂(sigmaBreve (rightBody P.φ P.cap)) := by
    unfold sigmaBreve
    rw [setIntegral_map measurableSet_Ioo hcont.aestronglyMeasurable
      (by fun_prop : Measurable (fun t : ℝ => t - π)).aemeasurable, gm_preimage_sub_Ioo,
      show P.φ + π = π + P.φ by ring, show π / 2 + π = 3 * π / 2 by ring]
    congr 1; funext t; simp only [suppBreve, sub_add_cancel]
  rw [h1, gm_sigmaBreve_B_restrict hP hbox, gm_prop844_two hP hbox,
    integral_withDensity_eq_integral_toReal_smul (gm_measurable_rhoB (P := P))
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hc2.le]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(countable_singleton (π / 2 - P.φ)).ae_notMem volume,
    (countable_singleton (π / 2)).ae_notMem volume] with t htd ht2 ht
  rw [uIoc_of_le hc2.le] at ht
  have ht' : t ∈ Ioo (π / 2 - P.θ) (π / 2) := ⟨ht.1, lt_of_le_of_ne ht.2 ht2⟩
  rw [ENNReal.toReal_ofReal (gm_rhoB_pos hP hbox ht' htd), smul_eq_mul]
  rfl

lemma gm_convexCurveArea_D :
    convexCurveArea (leftBody P.φ P.cap) (3 * π / 2) (3 * π / 2 + (π / 2 - P.φ)) =
      (1 / 2) * ∫ t in (0 : ℝ)..P.θ,
        dot (deriv P.curveD t) (uvec t) * supp (leftBody P.φ P.cap) (3 * π / 2 + t) := by
  have hD := gm_isConvexBody_D hP hbox
  have hθ0 := gm_θ_pos hP
  have hcont : Continuous (suppBreve (leftBody P.φ P.cap)) :=
    (continuous_supp hD.2.1 hD.1).comp (continuous_id.add continuous_const)
  unfold convexCurveArea
  congr 1
  have h1 : ∫ t in Ioo (3 * π / 2) (3 * π / 2 + (π / 2 - P.φ)), supp (leftBody P.φ P.cap) t
        ∂(sigma (leftBody P.φ P.cap)) =
      ∫ t in Ioo (π / 2) (π / 2 + (π / 2 - P.φ)), suppBreve (leftBody P.φ P.cap) t
        ∂(sigmaBreve (leftBody P.φ P.cap)) := by
    unfold sigmaBreve
    rw [setIntegral_map measurableSet_Ioo hcont.aestronglyMeasurable
      (by fun_prop : Measurable (fun t : ℝ => t - π)).aemeasurable, gm_preimage_sub_Ioo,
      show π / 2 + π = 3 * π / 2 by ring,
      show π / 2 + (π / 2 - P.φ) + π = 3 * π / 2 + (π / 2 - P.φ) by ring]
    congr 1; funext t; simp only [suppBreve, sub_add_cancel]
  have hle : π / 2 ≤ π / 2 + P.θ := by linarith
  rw [h1, gm_sigmaBreve_D_restrict hP hbox, gm_prop844_four hP hbox,
    integral_withDensity_eq_integral_toReal_smul (gm_measurable_rhoD (P := P))
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ← intervalIntegral.integral_of_le hle]
  have e2 : (∫ t in (0 : ℝ)..P.θ,
      dot (deriv P.curveD t) (uvec t) * supp (leftBody P.φ P.cap) (3 * π / 2 + t)) =
      ∫ t in (0 : ℝ)..P.θ, (fun s => dot (deriv P.curveD (s - π / 2)) (uvec (s - π / 2)) *
        suppBreve (leftBody P.φ P.cap) s) (t + π / 2) := by
    congr 1; funext t
    simp only [suppBreve, add_sub_cancel_right]
    congr 2; ring
  have e3 := intervalIntegral.integral_comp_add_right
    (fun s => dot (deriv P.curveD (s - π / 2)) (uvec (s - π / 2)) *
      suppBreve (leftBody P.φ P.cap) s) (a := 0) (b := P.θ) (π / 2)
  rw [e2, e3, zero_add, add_comm P.θ]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(countable_singleton (π / 2 + P.φ)).ae_notMem volume,
    (countable_singleton (π / 2 + P.θ)).ae_notMem volume] with t htd ht2 ht
  rw [uIoc_of_le hle] at ht
  have ht' : t - π / 2 ∈ Ioo 0 P.θ :=
    ⟨by linarith [ht.1], by linarith [lt_of_le_of_ne ht.2 ht2]⟩
  have hne : t - π / 2 ≠ P.φ := fun h => htd (by rw [mem_singleton_iff]; linarith)
  rw [ENNReal.toReal_ofReal (gm_rhoD_pos hP hbox ht' hne), smul_eq_mul]

end

end GerverParams

/-- **Theorem 8.4.6** (`thm:upper-bound-q-gerver-match`). `𝒜(K) = 𝒬(K, B_K, D_K)` for the cap of
Gerver's sofa. -/
theorem theorem8_4_6 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    sofaArea (π / 2) P.cap = upperQ P.φ P.cap (rightBody P.φ P.cap) (leftBody P.φ P.cap) := by
  obtain ⟨h1, -, -, h4, -, -⟩ := theorem8_4_3_two hP hbox
  have hN : area (niche P.cap (π / 2)) = curveArea P.path P.φ (π / 2 - P.φ) -
      curveArea P.curveB (π / 2 - P.θ) (π / 2) - curveArea P.curveD 0 P.θ :=
    (theorem8_4_1_niche hP hbox).2.2.2.2.2.2.2
  have hle : P.φ ≤ π / 2 - P.φ := by linarith [gm_φ_lt_θ hP, gm_θ_lt hP]
  have hsub : Icc P.φ (π / 2 - P.φ) ⊆ Icc 0 (π / 2) :=
    Icc_subset_Icc (gm_φ_pos hP).le (by linarith [gm_φ_pos hP])
  have hx : curveArea (innerCorner P.cap) P.φ (π / 2 - P.φ) =
      curveArea P.path P.φ (π / 2 - P.φ) :=
    gm_curveArea_congr hle ((gm_contDiff_path hP).contDiffOn.congr fun t ht =>
      gm_innerCorner hP hbox (hsub ht)) fun t ht => gm_innerCorner hP hbox (hsub ht)
  have eB : convexCurveArea (rightBody P.φ P.cap) (π + P.φ) (3 * π / 2) =
      curveArea P.curveB (π / 2 - P.θ) (π / 2) :=
    (gm_convexCurveArea_B hP hbox).trans (gm_curveArea_B hP hbox).symm
  have eD : convexCurveArea (leftBody P.φ P.cap) (3 * π / 2) (3 * π / 2 + (π / 2 - P.φ)) =
      curveArea P.curveD 0 P.θ :=
    (gm_convexCurveArea_D hP hbox).trans (gm_curveArea_D hP hbox).symm
  unfold sofaArea upperQ
  rw [hN, ← h1, ← h4, hx, eB, eD]
  simp only [segArea, cross_self, zero_div]
  ring

end MovingSofa
