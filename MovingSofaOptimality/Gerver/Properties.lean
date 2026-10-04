module

public import MovingSofaOptimality.Optimality.Variation
public import MovingSofaOptimality.Gerver.Structure
public import MovingSofaOptimality.External.Romik
public import MovingSofaOptimality.Gerver.Niche
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

/-!
# Gerver's sofa (§8.4)

Definitions 8.4.1 (`def:gerver-intervals`), 8.4.2–8.4.3 (the curves `𝐱, 𝐀, 𝐁, 𝐂, 𝐃`, in
`MovingSofaOptimality.Gerver.Defs`), 8.4.7 (`def:interval-j`); Theorems 8.4.1
(`thm:gerver-monotone`), 8.4.2 (`thm:gerver-odes`), 8.4.3 (`thm:gerver-left-right`), Proposition
8.4.4 (`pro:measure-translation`), Theorems 8.4.5–8.4.6, and Theorem 6.1.2
(`thm:injectivity-gerver`).

Throughout, `P` is a solution of Romik's system in the box of `GerverParams.InBox`, `G` is
`gerverSofa P`, `K = 𝓒(G)` its cap, and `φ = P.φ`, `θ = P.θ`.

**Theorem 8.4.1.** The paper states it without proof (its Remark 8.4.1 notes that the properties
are easy to verify numerically and implicitly assumed in the earlier literature); it is proved in
`MovingSofaOptimality.Gerver.Structure` and `MovingSofaOptimality.Gerver.Niche`. Part (2), that the
niche is the region enclosed by the curves `𝐁` (reversed), `𝐱|_{[t_1, t_4]}`, `𝐃` (reversed) and a
segment of the `x`-axis, is stated here as what the paper uses from it: the curves lie on the
boundary of the niche, and the area of the niche is `𝒥(𝐱|_{[t_1,t_4]}) - 𝒥(𝐁) - 𝒥(𝐃)`.

**Proofs of Theorems 8.4.3–8.4.6.** They follow the paper from Theorems 8.4.1–8.4.2 and 6.1.2.
The helper lemmas (prefix `gm_`) establish, in order:
* the regularity of the contact curves (continuity, differentiability off the four junctions, `C¹`
  on each phase), from the phase description of the rotation path in
  `MovingSofaOptimality.Gerver.Frame`;
* that `𝐃(t)` (resp. `𝐁(t)`) lies in `D_K` (resp. `B_K`) and on its supporting line at `3π/2 + t`
  (resp. `π + t`) (`gm_D_edge`, `gm_B_edge`), and that `D_K` (resp. `B_K`) has a single vertex
  `𝐱_K^L` (resp. `𝐱_K^R`) between these angles and `3π/2 + φ^L` (resp. `π + φ^R`)
  (`gm_D_corner`, `gm_B_corner`);
* the surface area measures on intervals, as in the paper's proof of Proposition 8.4.4: the
  `v_t`-component of `d v⁺ = v_t σ` (Theorem 5.2.2) along the piecewise `C¹` curves, whose
  Lebesgue–Stieltjes measures are `𝐀' dt`, …, `𝐃' dt` (`gm_sigma_Ioc`);
* the curve areas `𝒥(𝐁)`, `𝒥(𝐃)`, from the piecewise `C¹` parametrizations (`gm_curveArea_two`),
  and `𝒥(𝐛_{B_K})`, `𝒥(𝐝_{D_K})` from the densities of Proposition 8.4.4: their equality is the part
  of Theorem 8.4.3 (2) that Theorem 8.4.6 uses, so `theorem8_4_3_two` comes after these helpers.
-/

@[expose] public section

open Real Set MeasureTheory

namespace MovingSofaOptimality

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
vertices `A_K(t) = 𝐀(t)`, `C_K(t) = 𝐂(t)` and inner corner `𝐱_K(t) = 𝐱(t)` for `t ∈ [0, π/2]`.

Departure from the paper: the paper states Theorem 8.4.1 without proof, as properties easy to verify
numerically and implicitly assumed in the earlier literature (Remark 8.4.1); this proof derives all
four parts from Romik's equations (`MovingSofaOptimality.Gerver.Structure`,
`MovingSofaOptimality.Gerver.Niche`), because the paper gives no argument to follow. -/
theorem theorem8_4_1_monotone {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    IsMonotoneSofa (gerverSofa P) (π / 2) ∧
      ∀ t ∈ Icc 0 (π / 2), aK P.cap t = P.curveA t ∧ cK P.cap t = P.curveC t ∧
        innerCorner P.cap t = P.path t :=
  gv_monotone hP (GerverParams.romik_bounds hP hbox)

/-- **Theorem 8.4.1** (`thm:gerver-monotone`) (2), as used by the paper (see the module docstring):
the curves `𝐁`, `𝐱|_{[t_1, t_4]}`, `𝐃` lie on the boundary of the niche, with matching endpoints
`𝐁(t_3) = 𝐱(t_1)` and `𝐱(t_4) = 𝐃(t_2)`, `𝐃(t_0)` and `𝐁(t_5)` on the `x`-axis, and
`|𝒩(K)| = 𝒥(𝐱|_{[t_1, t_4]}) - 𝒥(𝐁|_{[t_3, t_5]}) - 𝒥(𝐃|_{[t_0, t_2]})`.

Departure from the paper: the paper gives no proof (see `theorem8_4_1_monotone`); this proof shows
from Romik's equations that the niche is the region under the curves and computes its area
directly, because the paper gives no argument to follow. -/
theorem theorem8_4_1_niche {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (∀ t ∈ Icc (P.tPt 3) (P.tPt 5),
        P.curveB t ∈ closure (niche P.cap (π / 2)) \ niche P.cap (π / 2)) ∧
      (∀ t ∈ Icc (P.tPt 1) (P.tPt 4),
        P.path t ∈ closure (niche P.cap (π / 2)) \ niche P.cap (π / 2)) ∧
      (∀ t ∈ Icc (P.tPt 0) (P.tPt 2),
        P.curveD t ∈ closure (niche P.cap (π / 2)) \ niche P.cap (π / 2)) ∧
      P.curveB (P.tPt 3) = P.path (P.tPt 1) ∧ P.path (P.tPt 4) = P.curveD (P.tPt 2) ∧
      (P.curveD (P.tPt 0)).2 = 0 ∧ (P.curveB (P.tPt 5)).2 = 0 ∧
      area (niche P.cap (π / 2)) = curveArea P.path (P.tPt 1) (P.tPt 4) -
        curveArea P.curveB (P.tPt 3) (P.tPt 5) - curveArea P.curveD (P.tPt 0) (P.tPt 2) := by
  simp only [GerverParams.tPt]
  exact gv_niche hP (GerverParams.romik_bounds hP hbox)

/-- **Theorem 8.4.1** (`thm:gerver-monotone`) (3): `b⃗_K(t)` passes through `𝐁(t)` for
`t ∈ [t_3, t_5]`, and `d⃗_K(t)` through `𝐃(t)` for `t ∈ [t_0, t_2]`.

Departure from the paper: the paper gives no proof (see `theorem8_4_1_monotone`); this proof derives
the statement from Romik's equations, because the paper gives no argument to follow. -/
theorem theorem8_4_1_walls {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (∀ t ∈ Icc (P.tPt 3) (P.tPt 5), P.curveB t ∈ wallBVec P.cap t) ∧
      ∀ t ∈ Icc (P.tPt 0) (P.tPt 2), P.curveD t ∈ wallDVec P.cap t := by
  simp only [GerverParams.tPt]
  exact gv_walls hP (GerverParams.romik_bounds hP hbox)

/-- **Theorem 8.4.1** (`thm:gerver-monotone`) (4): `𝐁'(t)` is a negative multiple of `v_t` and
`𝐃'(t)` a positive multiple of `u_t`, on the open phases where these curves are differentiable.

Departure from the paper: the paper gives no proof (see `theorem8_4_1_monotone`); this proof derives
the statement from Romik's equations, because the paper gives no argument to follow. -/
theorem theorem8_4_1_tangents {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (∀ t ∈ Ioo (P.tPt 3) (P.tPt 5), t ≠ P.tPt 4 →
        ∃ c < (0 : ℝ), HasDerivAt P.curveB (c • vvec t) t) ∧
      ∀ t ∈ Ioo (P.tPt 0) (P.tPt 2), t ≠ P.tPt 1 →
        ∃ c > (0 : ℝ), HasDerivAt P.curveD (c • uvec t) t := by
  simp only [GerverParams.tPt]
  exact gv_tangents hP (GerverParams.romik_bounds hP hbox)

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
  simp only [GerverParams.tPt]
  exact gv_odes hP (GerverParams.romik_bounds hP hbox)

/-- **Theorem 6.1.2** (`thm:injectivity-gerver`). The cap of Gerver's sofa satisfies the
injectivity condition.

Departure from the paper: the paper reads from Theorem 2 of Gerver (1992) that Gerver's sofa is a
balanced maximum sofa and applies Theorem 6.1.1; this proof checks the injectivity condition from
Romik's equations (`gv_injectivity`), because Gerver's Theorem 2 shows only that Gerver's sofa is
balanced, not that it is a limit of maximum polygon sofas. -/
theorem theorem6_1_2 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    SatisfiesInjectivity P.cap :=
  gv_injectivity hP (GerverParams.romik_bounds hP hbox)

/-- Gerver's sofa has area at least `2.2` (its area is `2.2195…`; Romik, Section 8 of the companion
package). -/
theorem gerverSofa_area {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    2.2 ≤ area (gerverSofa P) :=
  gv_area hP (GerverParams.romik_bounds hP hbox)

open Filter Topology
open scoped ContDiff ENNReal Interval

/-! ### Regularity of Gerver's rotation path and of the contact curves

The rotation path is `C¹`, glued from five smooth phases (`MovingSofaOptimality.Gerver.Frame`);
the contact curves are continuous, differentiable off the four junctions, and `C¹` on each closed
phase interval. -/

/-- The contact curve `𝐁 = 𝐱 + ⟨𝐱', u_t⟩ v_t` of a `C²` path is `C¹`. -/
lemma gm_contDiff_contactB {x : ℝ → ℝ × ℝ} (hx : ContDiff ℝ 2 x) :
    ContDiff ℝ 1 (GerverParams.contactB x) := by
  have hx1 : ContDiff ℝ 1 x := hx.of_le (by norm_num)
  have hdx : ContDiff ℝ 1 (deriv x) := hx.deriv'
  unfold GerverParams.contactB dot uvec vvec
  fun_prop

/-- The contact curve `𝐃 = 𝐱 - ⟨𝐱', v_t⟩ u_t` of a `C²` path is `C¹`. -/
lemma gm_contDiff_contactD {x : ℝ → ℝ × ℝ} (hx : ContDiff ℝ 2 x) :
    ContDiff ℝ 1 (GerverParams.contactD x) := by
  have hx1 : ContDiff ℝ 1 x := hx.of_le (by norm_num)
  have hdx : ContDiff ℝ 1 (deriv x) := hx.deriv'
  unfold GerverParams.contactD dot uvec vvec
  fun_prop

namespace GerverParams

variable {P : GerverParams}

lemma gm_contDiff_x₁ (P : GerverParams) : ContDiff ℝ ∞ P.x₁ := by unfold x₁ rot; fun_prop
lemma gm_contDiff_x₂ (P : GerverParams) : ContDiff ℝ ∞ P.x₂ := by unfold x₂ rot; fun_prop
lemma gm_contDiff_x₄ (P : GerverParams) : ContDiff ℝ ∞ P.x₄ := by unfold x₄ rot; fun_prop
lemma gm_contDiff_x₅ (P : GerverParams) : ContDiff ℝ ∞ P.x₅ := by unfold x₅ rot; fun_prop

/-- Every parameter other than the four junctions lies in an open phase interval. -/
lemma gm_exists_opiece {t : ℝ} (ht : t ∉ ({P.φ, P.θ, π / 2 - P.θ, π / 2 - P.φ} : Set ℝ)) :
    ∃ i, gs_opiece P i t := by
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at ht
  obtain ⟨h1, h2, h3, h4⟩ := ht
  rcases lt_or_gt_of_ne h1 with h1 | h1
  · exact ⟨0, h1⟩
  rcases lt_or_gt_of_ne h2 with h2 | h2
  · exact ⟨1, h1, h2⟩
  rcases lt_or_gt_of_ne h3 with h3 | h3
  · exact ⟨2, h2, h3⟩
  rcases lt_or_gt_of_ne h4 with h4 | h4
  · exact ⟨3, h3, h4⟩
  · exact ⟨4, h4⟩

lemma gm_junctions_countable :
    ({P.φ, P.θ, π / 2 - P.θ, π / 2 - P.φ} : Set ℝ).Countable :=
  (Set.toFinite _).countable

section
variable (hP : P.IsSolution)
include hP

lemma gm_φ_pos : 0 < P.φ := hP.1
lemma gm_φ_lt_θ : P.φ < P.θ := hP.2.1
lemma gm_θ_lt : P.θ < π / 4 := hP.2.2.1
lemma gm_θ_lt_c : P.θ < π / 2 - P.θ := (gs_ord hP).θ_lt
lemma gm_c_lt_d : π / 2 - P.θ < π / 2 - P.φ := (gs_ord hP).lt_φ'
lemma gm_d_lt : π / 2 - P.φ < π / 2 := by have := gm_φ_pos hP; linarith

lemma gm_continuous_curveB : Continuous P.curveB :=
  (gs_continuous_path hP).add ((gs_continuous_α hP).smul continuous_vvec)

lemma gm_continuous_curveD : Continuous P.curveD :=
  (gs_continuous_path hP).sub ((gs_continuous_β hP).smul continuous_uvec)

/-- `𝐀` is differentiable off the four junctions. -/
lemma gm_differentiableAt_curveA {t : ℝ}
    (ht : t ∉ ({P.φ, P.θ, π / 2 - P.θ, π / 2 - P.φ} : Set ℝ)) :
    DifferentiableAt ℝ P.curveA t :=
  have ⟨_, hi⟩ := gm_exists_opiece ht
  (gs_hasDerivAt_contactA hP hi).differentiableAt

/-- `𝐂` is differentiable off the four junctions. -/
lemma gm_differentiableAt_curveC {t : ℝ}
    (ht : t ∉ ({P.φ, P.θ, π / 2 - P.θ, π / 2 - P.φ} : Set ℝ)) :
    DifferentiableAt ℝ P.curveC t :=
  have ⟨_, hi⟩ := gm_exists_opiece ht
  (gs_hasDerivAt_contactC hP hi).differentiableAt

lemma gm_contDiffOn_B₄ : ContDiffOn ℝ 1 P.curveB (Icc (π / 2 - P.θ) (π / 2 - P.φ)) :=
  (gm_contDiff_contactB ((gm_contDiff_x₄ P).of_le (by simp))).contDiffOn.congr fun t ht =>
    (gs_contactB_eq hP (i := 3) ht).trans (gs_Phase.contactB_X P.gs_valid₄ t).symm

lemma gm_contDiffOn_B₅ : ContDiffOn ℝ 1 P.curveB (Icc (π / 2 - P.φ) (π / 2)) :=
  (gm_contDiff_contactB ((gm_contDiff_x₅ P).of_le (by simp))).contDiffOn.congr fun t ht =>
    (gs_contactB_eq hP (i := 4) ht.1).trans (gs_Phase.contactB_X P.gs_valid₅ t).symm

lemma gm_contDiffOn_D₁ : ContDiffOn ℝ 1 P.curveD (Icc 0 P.φ) :=
  (gm_contDiff_contactD ((gm_contDiff_x₁ P).of_le (by simp))).contDiffOn.congr fun t ht =>
    (gs_contactD_eq hP (i := 0) ht.2).trans (gs_Phase.contactD_X P.gs_valid₁ t).symm

lemma gm_contDiffOn_D₂ : ContDiffOn ℝ 1 P.curveD (Icc P.φ P.θ) :=
  (gm_contDiff_contactD ((gm_contDiff_x₂ P).of_le (by simp))).contDiffOn.congr fun t ht =>
    (gs_contactD_eq hP (i := 1) ht).trans (gs_Phase.contactD_X P.gs_valid₂ t).symm

end

end GerverParams

/-! ### Convex geometry helpers -/

/-- A point `x ∈ C` on the supporting lines of a convex body `C` at two angles `α < β < α + π`
is a vertex: the edges `e_C(s)`, `s ∈ (α, β)`, are `{x}`. -/
lemma gm_corner {C : Set (ℝ × ℝ)} (hC : IsConvexBody C) {x : ℝ × ℝ} (hx : x ∈ C) {α β : ℝ}
    (hαβ : α < β) (hβα : β < α + π) (hxα : dot x (uvec α) = supp C α)
    (hxβ : dot x (uvec β) = supp C β) : ∀ s ∈ Ioo α β, edge C s = {x} := by
  intro s hs
  have hS : 0 < sin (β - α) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h1 : 0 < sin (β - s) := sin_pos_of_pos_of_lt_pi (by linarith [hs.2]) (by linarith [hs.1])
  have h2 : 0 < sin (s - α) := sin_pos_of_pos_of_lt_pi (by linarith [hs.1]) (by linarith [hs.2])
  -- Every `p ∈ C` has `⟨p, u_α⟩ ≤ ⟨x, u_α⟩` and `⟨p, u_β⟩ ≤ ⟨x, u_β⟩`; as
  -- `sin(β - α) u_s = sin(β - s) u_α + sin(s - α) u_β`, also `⟨p, u_s⟩ ≤ ⟨x, u_s⟩`, with equality
  -- only if both inequalities are equalities, that is, only if `p = x`.
  refine cvx_edge_eq_singleton hx fun p hp hne => lt_of_le_of_ne ?_ fun heq => hne ?_
  · have hpα : dot p (uvec α) ≤ dot x (uvec α) := hxα ▸ dot_le_supp hC.2.1 hp α
    have hpβ : dot p (uvec β) ≤ dot x (uvec β) := hxβ ▸ dot_le_supp hC.2.1 hp β
    refine le_of_mul_le_mul_left ?_ hS
    rw [dot_uvec_comb p α β s, dot_uvec_comb x α β s]
    exact add_le_add (mul_le_mul_of_nonneg_left hpα h1.le) (mul_le_mul_of_nonneg_left hpβ h2.le)
  · have hA := mul_nonneg h1.le (sub_nonneg.2 (hxα ▸ dot_le_supp hC.2.1 hp α))
    have hB := mul_nonneg h2.le (sub_nonneg.2 (hxβ ▸ dot_le_supp hC.2.1 hp β))
    obtain ⟨eα, eβ⟩ := (add_eq_zero_iff_of_nonneg hA hB).1 (by
      linear_combination dot_uvec_comb p α β s - dot_uvec_comb x α β s - sin (β - α) * heq)
    exact eq_of_dot_uvec_eq hS.ne'
      (by linarith [(mul_eq_zero.1 eα).resolve_left h1.ne'])
      (by linarith [(mul_eq_zero.1 eβ).resolve_left h2.ne'])

/-- Squeeze in segments. -/
lemma gm_tendsto_of_segment {l : Filter ℝ} {f g h : ℝ → ℝ × ℝ} {L : ℝ × ℝ}
    (hg : Tendsto g l (𝓝 L)) (hh : Tendsto h l (𝓝 L))
    (hf : ∀ᶠ s in l, f s ∈ segment ℝ (g s) (h s)) : Tendsto f l (𝓝 L) := by
  rw [Metric.tendsto_nhds] at hg hh ⊢
  intro ε hε
  filter_upwards [hg ε hε, hh ε hε, hf] with s h1 h2 h3
  exact (convex_ball L ε).segment_subset h1 h2 h3

/-- A continuous curve running along the edges `e_C(ψ + s)` meets `v_C⁺(ψ + t)` at `t`. -/
lemma gm_eq_vplus_of_right {C : Set (ℝ × ℝ)} (hC : IsConvexBody C) {f : ℝ → ℝ × ℝ} {ψ t : ℝ}
    (hf : ContinuousWithinAt f (Ioi t) t) (he : ∀ᶠ s in 𝓝[>] t, f s ∈ edge C (ψ + s)) :
    f t = vplus C (ψ + t) := by
  have h1 : Tendsto (ψ + ·) (𝓝[>] t) (𝓝[>] (ψ + t)) := map_add_left_nhdsGT.le
  have hseg : ∀ᶠ s in 𝓝[>] t, f s ∈ segment ℝ (vminus C (ψ + s)) (vplus C (ψ + s)) :=
    he.mono fun s hs => by rwa [edge_eq_segment hC] at hs
  exact tendsto_nhds_unique hf (gm_tendsto_of_segment ((tendsto_vminus_right hC _).comp h1)
    ((tendsto_vplus_right hC _).comp h1) hseg)

/-- A continuous curve running along the edges `e_C(ψ + s)` meets `v_C⁻(ψ + t)` at `t`. -/
lemma gm_eq_vminus_of_left {C : Set (ℝ × ℝ)} (hC : IsConvexBody C) {f : ℝ → ℝ × ℝ} {ψ t : ℝ}
    (hf : ContinuousWithinAt f (Iio t) t) (he : ∀ᶠ s in 𝓝[<] t, f s ∈ edge C (ψ + s)) :
    f t = vminus C (ψ + t) := by
  have h1 : Tendsto (ψ + ·) (𝓝[<] t) (𝓝[<] (ψ + t)) := map_add_left_nhdsLT.le
  have hseg : ∀ᶠ s in 𝓝[<] t, f s ∈ segment ℝ (vminus C (ψ + s)) (vplus C (ψ + s)) :=
    he.mono fun s hs => by rwa [edge_eq_segment hC] at hs
  exact tendsto_nhds_unique hf (gm_tendsto_of_segment ((tendsto_vminus_left hC _).comp h1)
    ((tendsto_vplus_left hC _).comp h1) hseg)

/-- `v_C⁺(a) = x` if `v_C⁺ = x` just after `a`. -/
lemma gm_vplus_eq_of_right {C : Set (ℝ × ℝ)} (hC : IsConvexBody C) {a b : ℝ} (hab : a < b)
    {x : ℝ × ℝ} (h : ∀ s ∈ Ioo a b, vplus C s = x) : vplus C a = x :=
  tendsto_nhds_unique (tendsto_vplus_right hC a) <| tendsto_const_nhds.congr' <|
    eventually_of_mem (Ioo_mem_nhdsGT hab) fun s hs => (h s hs).symm

/-- `v_C⁻(b) = x` if `v_C⁻ = x` just before `b`. -/
lemma gm_vminus_eq_of_left {C : Set (ℝ × ℝ)} (hC : IsConvexBody C) {a b : ℝ} (hab : a < b)
    {x : ℝ × ℝ} (h : ∀ s ∈ Ioo a b, vminus C s = x) : vminus C b = x :=
  tendsto_nhds_unique (tendsto_vminus_left hC b) <| tendsto_const_nhds.congr' <|
    eventually_of_mem (Ioo_mem_nhdsLT hab) fun s hs => (h s hs).symm

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
    have h1 : supp K (s + π / 2) - 1 ≤ dot p (uvec (s + π / 2)) := mem_iInter₂.1 hp.2 s hs
    rw [hu, dot_neg_right, dot_neg_right, hqd]
    linarith
  have hsupp := cvx_supp_eq_of_isGreatest hq key
  exact ⟨by rw [hsupp, hu, dot_neg_right, hqd]; ring, hq, hsupp.symm⟩

/-- A point of `B_K` on the line `b_K(s)` lies on the supporting line `l_{B_K}(π + s)`. -/
lemma gm_supp_rightBody_of {φ : ℝ} {K : Set (ℝ × ℝ)} {s : ℝ} (hs : s ∈ Icc φ (π / 2))
    {q : ℝ × ℝ} (hq : q ∈ rightBody φ K) (hqb : dot q (uvec s) = supp K s - 1) :
    supp (rightBody φ K) (π + s) = 1 - supp K s ∧ q ∈ edge (rightBody φ K) (π + s) := by
  have hu : uvec (π + s) = -uvec s := by rw [add_comm, uvec_add_pi]
  have key : ∀ p ∈ rightBody φ K, dot p (uvec (π + s)) ≤ dot q (uvec (π + s)) := by
    intro p hp
    have h1 : supp K s - 1 ≤ dot p (uvec s) := mem_iInter₂.1 hp.2 s hs
    rw [hu, dot_neg_right, dot_neg_right, hqb]
    linarith
  have hsupp := cvx_supp_eq_of_isGreatest hq key
  exact ⟨by rw [hsupp, hu, dot_neg_right, hqb]; ring, hq, hsupp.symm⟩

/-! ### The cap of Gerver's sofa -/

namespace GerverParams

variable {P : GerverParams}

section
variable (hP : P.IsSolution) (hbox : P.InBox)
include hP hbox

lemma gm_isMonotone : IsMonotoneSofa (gerverSofa P) (π / 2) :=
  (theorem8_4_1_monotone hP hbox).1

/-- Gerver's sofa is a moving sofa with rotation angle `π/2` in standard position. -/
lemma gm_movingSofa_std : IsMovingSofaWithAngle (gerverSofa P) (π / 2) ∧
    IsStandardPosition (gerverSofa P) (π / 2) :=
  ⟨(gm_isMonotone hP hbox).isMovingSofaWithAngle, (gm_isMonotone hP hbox).isStandardPosition⟩

lemma gm_isCap : IsCap P.cap (π / 2) :=
  theorem2_4_1 pi_div_two_mem_Ioc (gm_movingSofa_std hP hbox).1 (gm_movingSofa_std hP hbox).2

lemma gm_isConvexBody_cap : IsConvexBody P.cap := (gm_isCap hP hbox).2.1

lemma gm_supp_cap_pi_div_two : supp P.cap (π / 2) = 1 := (gm_isCap hP hbox).2.2.2.1

lemma gm_sofaArea_cap : sofaArea (π / 2) P.cap = area (gerverSofa P) :=
  theorem2_5_10 (gm_isMonotone hP hbox)

/-- The cap of Gerver's sofa lies in `𝒦^i`: it is a cap, it satisfies the injectivity condition
(Theorem 6.1.2), and its area is at least that of Gerver's sofa, hence at least `2.2`. -/
lemma gm_isKi : IsKi P.cap := by
  refine ⟨gm_isCap hP hbox, theorem6_1_2 hP hbox, ?_⟩
  have h1 := gerverSofa_area hP hbox
  have h2 := gm_sofaArea_cap hP hbox
  have h3 : 0 ≤ area (niche P.cap (π / 2)) := ENNReal.toReal_nonneg
  unfold sofaArea at h2
  linarith

lemma gm_innerCorner {t : ℝ} (ht : t ∈ Icc 0 (π / 2)) : innerCorner P.cap t = P.path t :=
  ((theorem8_4_1_monotone hP hbox).2 t ht).2.2

lemma gm_aK {t : ℝ} (ht : t ∈ Icc 0 (π / 2)) : aK P.cap t = P.curveA t :=
  ((theorem8_4_1_monotone hP hbox).2 t ht).1

lemma gm_cK {t : ℝ} (ht : t ∈ Icc 0 (π / 2)) : cK P.cap t = P.curveC t :=
  ((theorem8_4_1_monotone hP hbox).2 t ht).2.1

lemma gm_φ_mem_Ioo : P.φ ∈ Ioo 0 (π / 4) :=
  ⟨gm_φ_pos hP, by have := hbox.1.2; have := two_le_pi; linarith⟩

lemma gm_closure_niche_subset_cap : closure (niche P.cap (π / 2)) ⊆ P.cap :=
  closure_minimal ((theorem2_5_9 (gm_isCap hP hbox)).1 ⟨gerverSofa P, gm_isMonotone hP hbox, rfl⟩)
    (gm_isConvexBody_cap hP hbox).isClosed

omit hP hbox in
lemma gm_closure_niche_subset_fan : closure (niche P.cap (π / 2)) ⊆ fan (π / 2) :=
  closure_minimal inter_subset_left (isClosed_fan _)

omit hbox in
lemma gm_θ_pos : 0 < P.θ := (gm_φ_pos hP).trans (gm_φ_lt_θ hP)

omit hbox in
lemma gm_θ_le : P.θ ≤ π / 2 - P.φ := by
  have := gm_θ_lt hP; have := gm_φ_lt_θ hP; linarith

omit hbox in
lemma gm_φ_le_c : P.φ ≤ π / 2 - P.θ := by
  have := gm_θ_lt hP; have := gm_φ_lt_θ hP; linarith

/-! ### The left body `D_K` and the curve `𝐃` -/

/-- `𝐃(t_2) = 𝐱_K^L`, the inner corner at `π/2 - φ`. -/
lemma gm_D_θ : P.curveD P.θ = xLeft P.φ P.cap := by
  have h2 := gm_innerCorner hP hbox (t := π / 2 - P.φ)
    ⟨by linarith [gm_d_lt hP, gm_φ_pos hP, gm_c_lt_d hP, gm_θ_lt_c hP, gm_θ_pos hP],
      by linarith [gm_φ_pos hP]⟩
  unfold xLeft; rw [h2]; exact (theorem8_4_1_niche hP hbox).2.2.2.2.1.symm

/-- `𝐃(t) ∈ H̆_K^L` for `t ∈ [t_0, t_2]`: along `𝐃`, `⟨𝐃(s), u_{π - φ}⟩` is nonincreasing (as
`𝐃'(s)` is a positive multiple of `u_s` with `s + φ < π/2`), and equals `h_K(π - φ) - 1` at
`s = t_2`, where `𝐃(t_2) = 𝐱_K^L`. -/
lemma gm_D_mem_hLeft {t : ℝ} (ht : t ∈ Icc 0 P.θ) : P.curveD t ∈ hLeft P.φ P.cap := by
  set w := π / 2 - P.φ + π / 2
  show supp P.cap w - 1 ≤ dot (P.curveD t) (uvec w)
  have hθ : dot (P.curveD P.θ) (uvec w) = supp P.cap w - 1 := by
    rw [gm_D_θ hP hbox]; exact (cn_innerCorner_dot P.cap (π / 2 - P.φ)).2
  rw [← hθ]
  refine env_antitoneOn (f' := fun s => dot (deriv P.curveD s) (uvec w)) (finite_singleton P.φ)
    (continuousOn_dot (gm_continuous_curveD hP).continuousOn _) (fun s hs hsφ => ?_)
    (fun s hs hsφ => ?_) ht ⟨(gm_θ_pos hP).le, le_rfl⟩ ht.2
  · obtain ⟨c, -, hd⟩ := (theorem8_4_1_tangents hP hbox).2 s hs hsφ
    simpa only [hd.deriv] using hasDerivAt_dot hd (uvec w)
  · obtain ⟨c, hc, hd⟩ := (theorem8_4_1_tangents hP hbox).2 s hs hsφ
    have h2 : s + P.φ < π / 2 := by linarith [hs.2, gm_θ_lt hP, gm_φ_lt_θ hP]
    have hcos := cos_pos_of_mem_Ioo ⟨by linarith [hs.1, gm_φ_pos hP, pi_pos], h2⟩
    show dot (deriv P.curveD s) (uvec w) ≤ 0
    rw [hd.deriv, dot_smul_left, dot_uvec_uvec, show s - w = (s + P.φ) - π by ring, cos_sub_pi]
    nlinarith

/-- `𝐃(t) ∈ D_K` for `t ∈ [t_0, t_2]`: `𝐃(t)` is in the closure of the niche but not in the
niche, so it lies in `K` and in no quadrant `Q_K⁻(s)`; by Lemma 8.1.6 it then lies in every
half-plane `H_K^d(s)`, `s ∈ [0, π/2 - φ]`. -/
lemma gm_D_mem_leftBody {t : ℝ} (ht : t ∈ Icc 0 P.θ) :
    P.curveD t ∈ leftBody P.φ P.cap := by
  have hm := (theorem8_4_1_niche hP hbox).2.2.1 t ht
  have hfan := gm_closure_niche_subset_fan hm.1
  refine ⟨gm_closure_niche_subset_cap hP hbox hm.1, mem_iInter₂.2 fun s hs => ?_⟩
  rcases hs.1.lt_or_eq with hs0 | rfl
  · rcases hs.2.lt_or_eq with hs1 | rfl
    · by_contra hn
      have h1 := (lemma8_1_6_left (gm_φ_mem_Ioo hP hbox) (gm_isKi hP hbox) ⟨hs.1, hs1⟩).2.1
      have h2 : P.curveD t ∈ hLeft P.φ P.cap ∩ qMinus P.cap s := by
        rw [h1]; exact ⟨gm_D_mem_hLeft hP hbox ht, hn⟩
      exact hm.2 ⟨hfan, mem_biUnion ⟨hs0, by linarith [gm_φ_pos hP]⟩ h2.2⟩
    · exact gm_D_mem_hLeft hP hbox ht
  · show supp P.cap (0 + π / 2) - 1 ≤ dot (P.curveD t) (uvec (0 + π / 2))
    rw [zero_add, gm_supp_cap_pi_div_two hP hbox, sub_self]
    exact hfan.2

/-- `𝐃(t)` lies on the inner wall line `d_K(t)` for `t ∈ [t_0, t_2]`. -/
lemma gm_D_wallD {t : ℝ} (ht : t ∈ Icc 0 P.θ) :
    dot (P.curveD t) (uvec (t + π / 2)) = supp P.cap (t + π / 2) - 1 := by
  have h : P.curveD t ∈ wallD P.cap t :=
    image_mono (fun p hp => hp.1) ((theorem8_4_1_walls hP hbox).2 t ht)
  rwa [proposition2_2_2_wallD] at h

lemma gm_isConvexBody_D : IsConvexBody (leftBody P.φ P.cap) :=
  opt_leftBody_isConvexBody (gm_φ_pos hP).le (gm_isCap hP hbox)

/-- `𝐃(t)` lies on the supporting line `l_{D_K}(3π/2 + t)`, and
`h_{D_K}(3π/2 + t) = 1 - h_K(π/2 + t)`, for `t ∈ [t_0, t_2]`. -/
lemma gm_D_edge {t : ℝ} (ht : t ∈ Icc 0 P.θ) :
    supp (leftBody P.φ P.cap) (3 * π / 2 + t) = 1 - supp P.cap (t + π / 2) ∧
      P.curveD t ∈ edge (leftBody P.φ P.cap) (3 * π / 2 + t) :=
  gm_supp_leftBody_of ⟨ht.1, ht.2.trans (gm_θ_le hP)⟩ (gm_D_mem_leftBody hP hbox ht)
    (gm_D_wallD hP hbox ht)

/-- `𝐃(t) = v_{D_K}^±(3π/2 + t)` on `(t_0, t_2)`: the continuous curve `𝐃` runs along the edges. -/
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

/-- `v_{D_K}⁺(3π/2) = 𝐃(t_0)`. -/
lemma gm_D_vplus_zero : vplus (leftBody P.φ P.cap) (3 * π / 2) = P.curveD 0 := by
  have := gm_eq_vplus_of_right (ψ := 3 * π / 2) (t := 0) (gm_isConvexBody_D hP hbox)
    (gm_continuous_curveD hP).continuousAt.continuousWithinAt (by
      filter_upwards [Ioo_mem_nhdsGT (gm_θ_pos hP)] with s hs
      exact (gm_D_edge hP hbox ⟨hs.1.le, hs.2.le⟩).2)
  rw [add_zero] at this; exact this.symm

/-- `v_{D_K}⁻(3π/2 + t_2) = 𝐃(t_2)`. -/
lemma gm_D_vminus_θ : vminus (leftBody P.φ P.cap) (3 * π / 2 + P.θ) = P.curveD P.θ :=
  (gm_eq_vminus_of_left (ψ := 3 * π / 2) (t := P.θ) (gm_isConvexBody_D hP hbox)
    (gm_continuous_curveD hP).continuousAt.continuousWithinAt (by
      filter_upwards [Ioo_mem_nhdsLT (gm_θ_pos hP)] with s hs
      exact (gm_D_edge hP hbox ⟨hs.1.le, hs.2.le⟩).2)).symm

/-- `D_K` has the vertex `𝐃(t_2) = 𝐱_K^L` between the angles `3π/2 + t_2` and `3π/2 + φ^L`. -/
lemma gm_D_corner : ∀ s ∈ Ioo (3 * π / 2 + P.θ) (3 * π / 2 + (π / 2 - P.φ)),
    edge (leftBody P.φ P.cap) s = {P.curveD P.θ} := by
  have hθ := gm_θ_lt hP; have hφθ := gm_φ_lt_θ hP; have hφ := gm_φ_pos hP
  have hx := gm_D_mem_leftBody hP hbox ⟨(gm_θ_pos hP).le, le_rfl⟩
  refine gm_corner (gm_isConvexBody_D hP hbox) hx (by linarith) (by linarith)
    (gm_D_edge hP hbox ⟨(gm_θ_pos hP).le, le_rfl⟩).2.2 ?_
  -- `𝐃(t_2) = 𝐱_K^L` lies on `d_K^L`, the supporting line `l_{D_K}(3π/2 + φ^L)` (Lemma 8.1.7 (4))
  show P.curveD P.θ ∈ suppLine (leftBody P.φ P.cap) (3 * π / 2 + (π / 2 - P.φ))
  rw [(lemma8_1_7_four hbox.1 (gm_isKi hP hbox)).2.2.2, proposition2_2_2_wallD, gm_D_θ hP hbox]
  exact (cn_innerCorner_dot P.cap (π / 2 - P.φ)).2

/-- `v_{D_K}⁺(3π/2 + t_2) = 𝐃(t_2)`, by the vertex `gm_D_corner`. -/
lemma gm_D_vplus_θ : vplus (leftBody P.φ P.cap) (3 * π / 2 + P.θ) = P.curveD P.θ := by
  have hD := gm_isConvexBody_D hP hbox
  have hθ := gm_θ_lt hP; have hφθ := gm_φ_lt_θ hP
  refine gm_vplus_eq_of_right hD (b := 3 * π / 2 + (π / 2 - P.φ)) (by linarith) fun s hs => ?_
  have := vplus_mem_edge hD s
  rwa [gm_D_corner hP hbox s hs] at this

/-- `Y_{D_K} = v_{D_K}⁻(3π/2 + φ^L) = 𝐃(t_2)`, by the vertex `gm_D_corner`. -/
lemma gm_D_vminus_end :
    vminus (leftBody P.φ P.cap) (3 * π / 2 + (π / 2 - P.φ)) = P.curveD P.θ := by
  have hD := gm_isConvexBody_D hP hbox
  have hθ := gm_θ_lt hP; have hφθ := gm_φ_lt_θ hP
  refine gm_vminus_eq_of_left hD (a := 3 * π / 2 + P.θ) (by linarith) fun s hs => ?_
  have := vminus_mem_edge hD s
  rwa [gm_D_corner hP hbox s hs] at this

/-- The edge `e_{D_K}(3π/2 + t_2)` is the single point `𝐃(t_2)`. -/
lemma gm_D_edge_θ : edge (leftBody P.φ P.cap) (3 * π / 2 + P.θ) = {P.curveD P.θ} := by
  rw [edge_eq_segment (gm_isConvexBody_D hP hbox), gm_D_vminus_θ hP hbox,
    gm_D_vplus_θ hP hbox, segment_same]

/-! ### The right body `B_K` and the curve `𝐁` -/

/-- `𝐁(t_3) = 𝐱_K^R`, the inner corner at `φ`. -/
lemma gm_B_c : P.curveB (π / 2 - P.θ) = xRight P.φ P.cap := by
  have h2 := gm_innerCorner hP hbox (t := P.φ)
    ⟨(gm_φ_pos hP).le, by linarith [gm_φ_le_c hP, gm_θ_pos hP]⟩
  unfold xRight; rw [h2]; exact (theorem8_4_1_niche hP hbox).2.2.2.1

/-- `𝐁(t) ∈ H̆_K^R` for `t ∈ [t_3, t_5]`: along `𝐁`, `⟨𝐁(s), u_φ⟩` is nondecreasing (as `𝐁'(s)`
is a negative multiple of `v_s` with `s > φ`), and equals `h_K(φ) - 1` at `s = t_3`, where
`𝐁(t_3) = 𝐱_K^R`. -/
lemma gm_B_mem_hRight {t : ℝ} (ht : t ∈ Icc (π / 2 - P.θ) (π / 2)) :
    P.curveB t ∈ hRight P.φ P.cap := by
  show supp P.cap P.φ - 1 ≤ dot (P.curveB t) (uvec P.φ)
  have hc : dot (P.curveB (π / 2 - P.θ)) (uvec P.φ) = supp P.cap P.φ - 1 := by
    rw [gm_B_c hP hbox]; exact (cn_innerCorner_dot P.cap P.φ).1
  rw [← hc]
  refine env_monotoneOn (f' := fun s => dot (deriv P.curveB s) (uvec P.φ))
    (finite_singleton (π / 2 - P.φ)) (continuousOn_dot (gm_continuous_curveB hP).continuousOn _)
    (fun s hs hsφ => ?_) (fun s hs hsφ => ?_)
    ⟨le_rfl, ((gm_c_lt_d hP).trans (gm_d_lt hP)).le⟩ ht ht.1
  · obtain ⟨c, -, hd⟩ := (theorem8_4_1_tangents hP hbox).1 s hs hsφ
    simpa only [hd.deriv] using hasDerivAt_dot hd (uvec P.φ)
  · obtain ⟨c, hc, hd⟩ := (theorem8_4_1_tangents hP hbox).1 s hs hsφ
    have h1 : P.φ - s < 0 := by linarith [hs.1, gm_φ_le_c hP, gm_θ_pos hP]
    have h2 : -π < P.φ - s := by linarith [hs.2, gm_φ_pos hP, pi_pos]
    show 0 ≤ dot (deriv P.curveB s) (uvec P.φ)
    rw [hd.deriv, dot_smul_left, dot_vvec_uvec']
    exact (mul_pos_of_neg_of_neg hc (sin_neg_of_neg_of_neg_pi_lt h1 h2)).le

/-- `𝐁(t) ∈ B_K` for `t ∈ [t_3, t_5]` (the mirror image of `gm_D_mem_leftBody`). -/
lemma gm_B_mem_rightBody {t : ℝ} (ht : t ∈ Icc (π / 2 - P.θ) (π / 2)) :
    P.curveB t ∈ rightBody P.φ P.cap := by
  have hm := (theorem8_4_1_niche hP hbox).1 t ht
  have hfan := gm_closure_niche_subset_fan hm.1
  refine ⟨gm_closure_niche_subset_cap hP hbox hm.1, mem_iInter₂.2 fun s hs => ?_⟩
  rcases hs.2.lt_or_eq with hs1 | rfl
  · rcases hs.1.lt_or_eq with hs0 | rfl
    · by_contra hn
      have h1 := (lemma8_1_6_right (gm_φ_mem_Ioo hP hbox) (gm_isKi hP hbox) ⟨hs0, hs.2⟩).2.1
      have h2 : P.curveB t ∈ hRight P.φ P.cap ∩ qMinus P.cap s := by
        rw [h1]; exact ⟨gm_B_mem_hRight hP hbox ht, hn⟩
      exact hm.2 ⟨hfan, mem_biUnion ⟨by linarith [gm_φ_pos hP], hs1⟩ h2.2⟩
    · exact gm_B_mem_hRight hP hbox ht
  · show supp P.cap (π / 2) - 1 ≤ dot (P.curveB t) (uvec (π / 2))
    rw [gm_supp_cap_pi_div_two hP hbox, sub_self]
    exact hfan.2

/-- `𝐁(t)` lies on the inner wall line `b_K(t)` for `t ∈ [t_3, t_5]`. -/
lemma gm_B_wallB {t : ℝ} (ht : t ∈ Icc (π / 2 - P.θ) (π / 2)) :
    dot (P.curveB t) (uvec t) = supp P.cap t - 1 := by
  have h : P.curveB t ∈ wallB P.cap t :=
    image_mono (fun p hp => hp.1) ((theorem8_4_1_walls hP hbox).1 t ht)
  rwa [proposition2_2_2_wallB] at h

lemma gm_isConvexBody_B : IsConvexBody (rightBody P.φ P.cap) :=
  opt_rightBody_isConvexBody (gm_φ_pos hP).le (gm_isCap hP hbox)

/-- `𝐁(t)` lies on the supporting line `l_{B_K}(π + t)`, and `h_{B_K}(π + t) = 1 - h_K(t)`, for
`t ∈ [t_3, t_5]`. -/
lemma gm_B_edge {t : ℝ} (ht : t ∈ Icc (π / 2 - P.θ) (π / 2)) :
    supp (rightBody P.φ P.cap) (π + t) = 1 - supp P.cap t ∧
      P.curveB t ∈ edge (rightBody P.φ P.cap) (π + t) :=
  gm_supp_rightBody_of ⟨(gm_φ_le_c hP).trans ht.1, ht.2⟩ (gm_B_mem_rightBody hP hbox ht)
    (gm_B_wallB hP hbox ht)

/-- `𝐁(t) = v_{B_K}^±(π + t)` on `(t_3, t_5)`: the continuous curve `𝐁` runs along the edges. -/
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

/-- `v_{B_K}⁺(π + t_3) = 𝐁(t_3)`. -/
lemma gm_B_vplus_c :
    vplus (rightBody P.φ P.cap) (π + (π / 2 - P.θ)) = P.curveB (π / 2 - P.θ) :=
  (gm_eq_vplus_of_right (ψ := π) (t := π / 2 - P.θ) (gm_isConvexBody_B hP hbox)
    (gm_continuous_curveB hP).continuousAt.continuousWithinAt (by
      filter_upwards [Ioo_mem_nhdsGT ((gm_c_lt_d hP).trans (gm_d_lt hP))] with s hs
      exact (gm_B_edge hP hbox ⟨hs.1.le, hs.2.le⟩).2)).symm

/-- `v_{B_K}⁻(3π/2) = 𝐁(t_5)`. -/
lemma gm_B_vminus_end : vminus (rightBody P.φ P.cap) (π + π / 2) = P.curveB (π / 2) :=
  (gm_eq_vminus_of_left (ψ := π) (t := π / 2) (gm_isConvexBody_B hP hbox)
    (gm_continuous_curveB hP).continuousAt.continuousWithinAt (by
      filter_upwards [Ioo_mem_nhdsLT ((gm_c_lt_d hP).trans (gm_d_lt hP))] with s hs
      exact (gm_B_edge hP hbox ⟨hs.1.le, hs.2.le⟩).2)).symm

/-- `B_K` has the vertex `𝐁(t_3) = 𝐱_K^R` between the angles `π + φ^R` and `π + t_3`. -/
lemma gm_B_corner : ∀ s ∈ Ioo (π + P.φ) (π + (π / 2 - P.θ)),
    edge (rightBody P.φ P.cap) s = {P.curveB (π / 2 - P.θ)} := by
  have hθ := gm_θ_lt hP; have hφθ := gm_φ_lt_θ hP; have hφ := gm_φ_pos hP
  have hcd : π / 2 - P.θ < π / 2 := (gm_c_lt_d hP).trans (gm_d_lt hP)
  have hx := gm_B_mem_rightBody hP hbox ⟨le_rfl, hcd.le⟩
  refine gm_corner (gm_isConvexBody_B hP hbox) hx (by linarith) (by linarith) ?_
    (gm_B_edge hP hbox ⟨le_rfl, hcd.le⟩).2.2
  -- `𝐁(t_3) = 𝐱_K^R` lies on `b_K^R`, the supporting line `l_{B_K}(π + φ^R)` (Lemma 8.1.7 (2))
  show P.curveB (π / 2 - P.θ) ∈ suppLine (rightBody P.φ P.cap) (π + P.φ)
  rw [(lemma8_1_7_two hbox.1 (gm_isKi hP hbox)).2.2.2, proposition2_2_2_wallB, gm_B_c hP hbox]
  exact (cn_innerCorner_dot P.cap P.φ).1

/-- `X_{B_K} = v_{B_K}⁺(π + φ^R) = 𝐁(t_3)`, by the vertex `gm_B_corner`. -/
lemma gm_B_vplus_φ : vplus (rightBody P.φ P.cap) (π + P.φ) = P.curveB (π / 2 - P.θ) := by
  have hB := gm_isConvexBody_B hP hbox
  have hθ := gm_θ_lt hP; have hφθ := gm_φ_lt_θ hP
  refine gm_vplus_eq_of_right hB (b := π + (π / 2 - P.θ)) (by linarith) fun s hs => ?_
  have := vplus_mem_edge hB s
  rwa [gm_B_corner hP hbox s hs] at this

/-- `v_{B_K}⁻(π + t_3) = 𝐁(t_3)`, by the vertex `gm_B_corner`. -/
lemma gm_B_vminus_c :
    vminus (rightBody P.φ P.cap) (π + (π / 2 - P.θ)) = P.curveB (π / 2 - P.θ) := by
  have hB := gm_isConvexBody_B hP hbox
  have hθ := gm_θ_lt hP; have hφθ := gm_φ_lt_θ hP
  refine gm_vminus_eq_of_left hB (a := π + P.φ) (by linarith) fun s hs => ?_
  have := vminus_mem_edge hB s
  rwa [gm_B_corner hP hbox s hs] at this

/-- The edge `e_{B_K}(π + t_3)` is the single point `𝐁(t_3)`. -/
lemma gm_B_edge_c :
    edge (rightBody P.φ P.cap) (π + (π / 2 - P.θ)) = {P.curveB (π / 2 - P.θ)} := by
  rw [edge_eq_segment (gm_isConvexBody_B hP hbox), gm_B_vminus_c hP hbox,
    gm_B_vplus_c hP hbox, segment_same]

/-! ### The tails `𝐝_{D_K}` and `𝐛_{B_K}` -/

/-- The tail `𝐝_{D_K}` (the boundary of `D_K` between the angles `3π/2` and `3π/2 + φ^L`) is the
curve `𝐃|_{[t_0, t_2]}`. -/
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
    rcases hτ.1.lt_or_eq with h0 | rfl
    · rcases hτ.2.lt_or_eq with h1 | rfl
      · exact Or.inl (Or.inr ⟨3 * π / 2 + τ, ⟨by linarith, by linarith⟩, (gm_D_edge hP hbox hτ).2⟩)
      · exact Or.inr (gm_D_vminus_end hP hbox).symm
    · exact Or.inl (Or.inl (gm_D_vplus_zero hP hbox).symm)

/-- The tail `𝐛_{B_K}` (the boundary of `B_K` between the angles `π + φ^R` and `3π/2`) is the
curve `𝐁|_{[t_3, t_5]}`. -/
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
    · exact ⟨π / 2, ⟨hcd.le, le_rfl⟩, by rw [h, h32, gm_B_vminus_end hP hbox]⟩
  · rintro ⟨τ, hτ, rfl⟩
    rcases hτ.1.lt_or_eq with h0 | rfl
    · rcases hτ.2.lt_or_eq with h1 | rfl
      · exact Or.inl (Or.inr ⟨π + τ, ⟨by linarith, by linarith⟩, (gm_B_edge hP hbox hτ).2⟩)
      · exact Or.inr (by rw [h32, gm_B_vminus_end hP hbox])
    · exact Or.inl (Or.inl (gm_B_vplus_φ hP hbox).symm)

end

end GerverParams

/-! ### Measures on intervals of angles -/

lemma gm_ae_restrict_of_countable {s E : Set ℝ} (hs : MeasurableSet s) (hE : E.Countable)
    {p : ℝ → Prop} (h : ∀ t ∈ s, t ∉ E → p t) : ∀ᵐ t ∂(volume.restrict s), p t := by
  rw [ae_restrict_iff' hs]
  filter_upwards [hE.ae_notMem volume] with t ht hts using h t hts ht

/-- Densities that agree off a countable set define the same measure. -/
lemma gm_withDensity_congr {T : Set ℝ} (hT : MeasurableSet T) {E : Set ℝ} (hE : E.Countable)
    {f g : ℝ → ℝ≥0∞} (h : ∀ t ∈ T, t ∉ E → f t = g t) :
    (volume.restrict T).withDensity f = (volume.restrict T).withDensity g :=
  withDensity_congr_ae (gm_ae_restrict_of_countable hT hE h)

lemma gm_measurable_dot {f g : ℝ → ℝ × ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun t => dot (f t) (g t)) := by
  unfold dot; fun_prop

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
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  -- `(c, d)` is the increasing union of the intervals `(c, d - 1/(n + 1)]`.
  have hU : Ioo c d = ⋃ n : ℕ, Ioc c (d - 1 / ((n : ℝ) + 1)) := by
    ext t; simp only [mem_Ioo, mem_iUnion, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h2)
      exact ⟨n, h1, by linarith⟩
    · rintro ⟨n, h1, h2⟩
      exact ⟨h1, by linarith [hpos n]⟩
  have hdir : Directed (· ⊆ ·) (fun n : ℕ => Ioc c (d - 1 / ((n : ℝ) + 1))) := by
    refine Monotone.directed_le fun m n hmn => Ioc_subset_Ioc le_rfl ?_
    have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
    linarith
  ext s hs
  rw [hU, Measure.restrict_iUnion_apply_eq_iSup hdir hs,
    Measure.restrict_iUnion_apply_eq_iSup hdir hs]
  congr 1; funext n
  rw [h _ (by linarith [hpos n])]

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
  refine gm_restrict_Ioo_eq fun b hb => gm_restrict_Ioc_eq ?_ ?_
  · exact fun a b' ha hab hb' => hfin a b' ha hab (lt_of_le_of_lt hb' hb)
  · exact fun a b' ha hab hb' => h a b' ha hab (lt_of_le_of_lt hb' hb)

lemma gm_withDensity_restrict_self {S : Set ℝ} (hS : MeasurableSet S) (f : ℝ → ℝ≥0∞) :
    ((volume.restrict S).withDensity f).restrict S = (volume.restrict S).withDensity f := by
  rw [restrict_withDensity hS, Measure.restrict_restrict_of_subset subset_rfl]

/-- A measure with density `f` on `S` has density `f` on every measurable `T ⊆ S`. -/
lemma gm_restrict_eq_withDensity_of_subset {μ : Measure ℝ} {S T : Set ℝ} {f : ℝ → ℝ≥0∞}
    (h : μ.restrict S = (volume.restrict S).withDensity f) (hT : MeasurableSet T) (hTS : T ⊆ S) :
    μ.restrict T = (volume.restrict T).withDensity f := by
  rw [← Measure.restrict_restrict_of_subset hTS, h, restrict_withDensity hT,
    Measure.restrict_restrict_of_subset hTS]

lemma gm_withDensity_Ioc {S : Set ℝ} (f : ℝ → ℝ≥0∞) {a b : ℝ} (hab : Ioc a b ⊆ S) :
    (volume.restrict S).withDensity f (Ioc a b) = ∫⁻ t in Ioc a b, f t := by
  rw [withDensity_apply f measurableSet_Ioc, Measure.restrict_restrict_of_subset hab]

/-- The surface area measure of an interval of angles along which `v_C⁺` follows a curve `γ`:
if `v_C⁺(t + ψ) = γ(t)` on `[a, b]`, with `γ` continuous and differentiable off a countable set,
with a bounded measurable derivative `γ'`, then
`σ_C((a + ψ, b + ψ]) = ∫_{(a, b]} ⟨γ'(t), v_{t + ψ}⟩ dt`. This is the paper's argument for
Proposition 8.4.4: `d v_C⁺ = v_t σ_C` (Theorem 5.2.2); on `[a + ψ, b + ψ]`, `v_C⁺ = γ(· - ψ)`, so
`d v_C⁺ = γ'(· - ψ) dt`; and the `v_t`-components of the two sides are `σ_C` (as `⟨v_t, v_t⟩ = 1`)
and `⟨γ'(t - ψ), v_t⟩ dt`. -/
private lemma gm_sigma_Ioc {C : Set (ℝ × ℝ)} (hC : IsConvexBody C) {ψ a b : ℝ} (hab : a ≤ b)
    {γ γ' : ℝ → ℝ × ℝ} {E : Set ℝ} (hE : E.Countable)
    (hv : ∀ t ∈ Icc a b, vplus C (t + ψ) = γ t) (hc : ContinuousOn γ (Icc a b))
    (hd : ∀ t ∈ Ioo a b \ E, HasDerivAt γ (γ' t) t) (hm : Measurable γ') {M : ℝ}
    (hM : ∀ t ∈ Icc a b, ‖γ' t‖ ≤ M) :
    sigma C (Ioc (a + ψ) (b + ψ)) =
      ∫⁻ t in Ioc a b, ENNReal.ofReal (dot (γ' t) (vvec (t + ψ))) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  have hcd : a + ψ < b + ψ := by linarith
  have hmem : ∀ s ∈ Icc (a + ψ) (b + ψ), s - ψ ∈ Icc a b := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  -- `v_C⁺ = γ(· - ψ)` on `[a + ψ, b + ψ]`, with the bounded derivative `γ'(· - ψ)`
  have hvx : ∀ s ∈ Icc (a + ψ) (b + ψ), vplus C s = γ (s - ψ) := fun s hs => by
    rw [← hv _ (hmem s hs), sub_add_cancel]
  have hm' : Measurable fun s => γ' (s - ψ) := hm.comp (measurable_id.sub_const ψ)
  have hi : IntegrableOn (fun s => γ' (s - ψ)) (Icc (a + ψ) (b + ψ)) :=
    Measure.integrableOn_of_bounded (M := M) measure_Icc_lt_top.ne hm'.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Icc).2
        (Filter.Eventually.of_forall fun s hs => hM _ (hmem s hs)))
  have hgc : ContinuousOn (fun s => γ (s - ψ)) (Icc (a + ψ) (b + ψ)) :=
    hc.comp (continuous_sub_right ψ).continuousOn hmem
  -- `d v_C⁺ = γ'(· - ψ) dt` on `[a + ψ, b + ψ]` (fundamental theorem of calculus for `γ(· - ψ)`)
  have hls : lsMeasure (vplus C) (a + ψ) (b + ψ) =
      (volume.restrict (Icc (a + ψ) (b + ψ))).withDensityᵥ fun s => γ' (s - ψ) := by
    refine cvx_lsMeasure_eq_withDensityᵥ hcd.le hi (fun s hs => ?_) (lemma5_2_1 hC _ _)
      (hgc.congr hvx)
    have hsub : Icc (a + ψ) s ⊆ Icc (a + ψ) (b + ψ) := Icc_subset_Icc_right hs.2
    rw [hvx s hs, hvx _ ⟨le_rfl, hcd.le⟩, integral_eq_of_hasDerivAt_off_countable_of_le
      (fun s => γ (s - ψ)) _ hs.1 (hE.image fun t => t + ψ) (hgc.mono hsub) (fun u hu => ?_)
      ((hi.mono_set (by rw [uIcc_of_le hs.1]; exact hsub)).intervalIntegrable)]
    · abel
    · have hu' : u - ψ ∈ Ioo a b \ E := ⟨⟨by linarith [hu.1.1], by linarith [hu.1.2, hs.2]⟩,
        fun h => hu.2 ⟨u - ψ, h, sub_add_cancel u ψ⟩⟩
      exact (hd _ hu').comp_sub_const u ψ
  -- Theorem 5.2.2: `d v_C⁺ = v_t σ_C` on `(a + ψ, b + ψ]`
  have key : (volume.restrict (Ioc (a + ψ) (b + ψ))).withDensityᵥ (fun s => γ' (s - ψ)) =
      ((sigma C).restrict (Ioc (a + ψ) (b + ψ))).withDensityᵥ vvec := by
    rw [← theorem5_2_2 hC hcd, hls, cvx_withDensityᵥ_restrict hi measurableSet_Ioc,
      Measure.restrict_restrict_of_subset Ioc_subset_Icc_self]
  -- the `v_t`-components: `∫_X ⟨γ'(s - ψ), v_s⟩ ds = σ_C(X)` for `X ⊆ (a + ψ, b + ψ]`
  have : IsFiniteMeasure ((sigma C).restrict (Ioc (a + ψ) (b + ψ))) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hi' : Integrable (fun s => γ' (s - ψ)) (volume.restrict (Ioc (a + ψ) (b + ψ))) :=
    hi.mono_set Ioc_subset_Icc_self
  have hvi : Integrable vvec ((sigma C).restrict (Ioc (a + ψ) (b + ψ))) :=
    continuous_vvec.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hρi : Integrable (fun s => dot (γ' (s - ψ)) (vvec s))
      (volume.restrict (Ioc (a + ψ) (b + ψ))) :=
    Measure.integrableOn_of_bounded (M := 2 * M) measure_Ioc_lt_top.ne
      (gm_measurable_dot hm' continuous_vvec.measurable).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun s hs => by
        have h1 := abs_dot_le (γ' (s - ψ)) (vvec s)
        have h2 := hM _ (hmem s (Ioc_subset_Icc_self hs))
        have h3 := norm_vvec_le s
        rw [Real.norm_eq_abs]
        nlinarith [norm_nonneg (γ' (s - ψ)), norm_nonneg (vvec s)]))
  have hcomp : ∀ X, MeasurableSet X →
      ∫ s in X, dot (γ' (s - ψ)) (vvec s) ∂(volume.restrict (Ioc (a + ψ) (b + ψ))) =
        ((sigma C).restrict (Ioc (a + ψ) (b + ψ))).real X := by
    intro X hX
    have hg : ∀ (ν : Measure ℝ) [IsFiniteMeasure ν], Integrable (X.indicator uvec) ν :=
      fun ν _ => (Integrable.of_bound continuous_uvec.aestronglyMeasurable 1
        (Filter.Eventually.of_forall norm_uvec_le)).indicator hX
    have h := congrArg (fun ν => ∫ᵛ s, X.indicator uvec s ∂[crossCLM; ν]) key
    rw [cvx_integral_withDensityᵥ hi' (M := M.toNNReal) ((ae_restrict_iff' measurableSet_Ioc).2
        (Filter.Eventually.of_forall fun s hs => (hM _ (hmem s (Ioc_subset_Icc_self hs))).trans
          (Real.le_coe_toNNReal M))) crossCLM (hg _),
      cvx_integral_withDensityᵥ hvi (M := 1)
        (Filter.Eventually.of_forall fun s => by simpa using norm_vvec_le s) crossCLM (hg _)] at h
    have e1 : ∀ s, crossCLM (X.indicator uvec s) (γ' (s - ψ)) =
        X.indicator (fun s => dot (γ' (s - ψ)) (vvec s)) s := fun s => by
      by_cases hs : s ∈ X
      · simp [hs, cross_anticomm (uvec s), cross_uvec]
      · simp [hs]
    have e2 : ∀ s, crossCLM (X.indicator uvec s) (vvec s) = X.indicator 1 s := fun s => by
      by_cases hs : s ∈ X
      · simp [hs, cross_vvec]
      · simp [hs]
    simp_rw [e1, e2] at h
    rwa [integral_indicator hX, integral_indicator_one hX] at h
  -- `σ_C ≥ 0` makes the density nonnegative
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (a + ψ) (b + ψ))] fun s => dot (γ' (s - ψ)) (vvec s) :=
    ae_nonneg_of_forall_setIntegral_nonneg hρi fun X hX _ => (hcomp X hX).symm ▸ measureReal_nonneg
  have h1 : sigma C (Ioc (a + ψ) (b + ψ)) =
      ∫⁻ s in Ioc (a + ψ) (b + ψ), ENNReal.ofReal (dot (γ' (s - ψ)) (vvec s)) := by
    have h := hcomp univ MeasurableSet.univ
    rw [Measure.restrict_univ, measureReal_restrict_apply_univ] at h
    rw [← ofReal_integral_eq_lintegral_ofReal hρi hnn, h, ofReal_measureReal measure_Ioc_lt_top.ne]
  -- translate by `ψ`
  have htr := (measurePreserving_add_right volume ψ).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addRight ψ) (fun s => ENNReal.ofReal (dot (γ' (s - ψ)) (vvec s)))
    (Ioc (a + ψ) (b + ψ))
  rw [preimage_add_const_Ioc, add_sub_cancel_right, add_sub_cancel_right] at htr
  rw [h1, ← htr]
  simp only [add_sub_cancel_right]

/-- **Theorem 8.4.3** (`thm:gerver-left-right`) (1): `𝐃(t) = v_{D_K}^±(3π/2 + t)` on `(t_0, t_2)`
and `𝐁(t) = v_{B_K}^±(π + t)` on `(t_3, t_5)`. -/
theorem theorem8_4_3_one {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (∀ t ∈ Ioo (P.tPt 0) (P.tPt 2), P.curveD t = vplus (leftBody P.φ P.cap) (3 * π / 2 + t) ∧
        P.curveD t = vminus (leftBody P.φ P.cap) (3 * π / 2 + t)) ∧
      ∀ t ∈ Ioo (P.tPt 3) (P.tPt 5), P.curveB t = vplus (rightBody P.φ P.cap) (π + t) ∧
        P.curveB t = vminus (rightBody P.φ P.cap) (π + t) :=
  ⟨fun _ ht => gm_D_vplus_vminus hP hbox ht, fun _ ht => gm_B_vplus_vminus hP hbox ht⟩

/-- **Theorem 8.4.3** (`thm:gerver-left-right`) (3): `h_K(π/2 + t) + h_{D_K}(3π/2 + t) = 1` on
`[t_0, t_2]` and `h_K(t) + h_{B_K}(π + t) = 1` on `[t_3, t_5]`. -/
theorem theorem8_4_3_three {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (∀ t ∈ Icc (P.tPt 0) (P.tPt 2),
        supp P.cap (π / 2 + t) + supp (leftBody P.φ P.cap) (3 * π / 2 + t) = 1) ∧
      ∀ t ∈ Icc (P.tPt 3) (P.tPt 5), supp P.cap t + supp (rightBody P.φ P.cap) (π + t) = 1 := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · rw [(gm_D_edge hP hbox ht).1, add_comm (π / 2) t]; ring
  · rw [(gm_B_edge hP hbox ht).1]; ring

/-! ### Proposition 8.4.4 -/

lemma gm_sigmaBreve_apply (C : Set (ℝ × ℝ)) (S : Set ℝ) :
    sigmaBreve C S = sigma C ((fun t => t - π) ⁻¹' S) :=
  (measurableEmbedding_subRight π).map_apply _ _

lemma gm_preimage_sub_singleton (a c : ℝ) : (fun t => t - c) ⁻¹' {a} = {a + c} := by
  ext t; simp only [mem_preimage, mem_singleton_iff]
  constructor <;> intro h <;> linarith

lemma gm_vvec_sub_pi_div_two (t : ℝ) : vvec t = -uvec (t - π / 2) := by
  simpa using vvec_add_pi_div_two (t - π / 2)

namespace GerverParams

variable {P : GerverParams}

/-- A curve whose right derivative at every `t` is `ρ_i(t) w(t)`, for the half-open phase interval
`i` of `t`, with continuous `ρ_i` and `‖w‖ ≤ 1`, has a bounded derivative on `[0, π/2]`: where the
curve is differentiable, its derivative is that right derivative, and elsewhere it is `0`. This
bounds the densities `𝐀' dt`, …, `𝐃' dt` in the proof of Proposition 8.4.4. -/
private lemma gm_exists_bound_deriv {γ w : ℝ → ℝ × ℝ} {ρ : ℕ → ℝ → ℝ}
    (hρ : ∀ i, Continuous (ρ i)) (hw : ∀ t, ‖w t‖ ≤ 1)
    (hγ : ∀ t, HasDerivWithinAt γ (ρ (P.gs_ridx t) t • w t) (Ici t) t) :
    ∃ M, ∀ t ∈ Icc 0 (π / 2), ‖deriv γ t‖ ≤ M := by
  obtain ⟨M, hM⟩ := gs_exists_bound_of_sel (f := fun t => ρ (P.gs_ridx t) t) hρ
    (fun t => ⟨_, gs_ridx_lt t, rfl⟩) 0 (π / 2)
  refine ⟨max M 0, fun t ht => ?_⟩
  by_cases hd : DifferentiableAt ℝ γ t
  · rw [(uniqueDiffWithinAt_Ici t).eq_deriv _ hd.hasDerivAt.hasDerivWithinAt (hγ t), norm_smul]
    exact le_max_of_le_left ((mul_le_of_le_one_right (norm_nonneg _) (hw t)).trans (hM t ht))
  · rw [deriv_zero_of_not_differentiableAt hd, norm_zero]
    exact le_max_right _ _

section
variable (hP : P.IsSolution) (hbox : P.InBox)
include hP hbox

lemma gm_injCond1 : InjCond1 P.cap := (theorem6_1_2 hP hbox).1

omit hbox in
/-- The piecewise `C¹` curves `𝐀`, `𝐁`, `𝐂`, `𝐃` have bounded derivatives on `[0, π/2]`
(`𝐀' = ρ_A v_t`, `𝐁 = 𝐀 - u_t`, `𝐂' = -ρ_C u_t`, `𝐃 = 𝐂 - v_t` on the phases), so that their
Lebesgue–Stieltjes measures are `𝐀' dt`, …, `𝐃' dt` with bounded densities (Proposition 8.4.4). -/
private lemma gm_bound_deriv :
    (∃ M, ∀ t ∈ Icc 0 (π / 2), ‖deriv P.curveA t‖ ≤ M) ∧
      (∃ M, ∀ t ∈ Icc 0 (π / 2), ‖deriv P.curveB t‖ ≤ M) ∧
      (∃ M, ∀ t ∈ Icc 0 (π / 2), ‖deriv P.curveC t‖ ≤ M) ∧
      ∃ M, ∀ t ∈ Icc 0 (π / 2), ‖deriv P.curveD t‖ ≤ M := by
  have hA := fun t => gs_hasDerivWithinAt_contactA hP (gs_rpiece_ridx (P := P) t)
  have hC := fun t => gs_hasDerivWithinAt_contactC hP (gs_rpiece_ridx (P := P) t)
  have eB : P.curveB = fun t => P.curveA t - uvec t := by
    funext t; simp only [curveA, curveB, gs_contactA_eq', gs_contactB_eq']; abel
  have eD : P.curveD = fun t => P.curveC t - vvec t := by
    funext t; simp only [curveC, curveD, gs_contactC_eq', gs_contactD_eq']; abel
  refine ⟨gm_exists_bound_deriv (ρ := fun i => (P.gs_phase i).ρA) gs_continuous_ρA norm_vvec_le hA,
    ?_, gm_exists_bound_deriv (ρ := fun i t => -(P.gs_phase i).ρC t)
      (fun i => (gs_continuous_ρC i).neg) norm_uvec_le hC, ?_⟩
  · rw [eB]
    refine gm_exists_bound_deriv (P := P) (ρ := fun i t => (P.gs_phase i).ρA t - 1)
      (fun i => (gs_continuous_ρA i).sub continuous_const) norm_vvec_le fun t => ?_
    exact ((hA t).sub (hasDerivAt_uvec t).hasDerivWithinAt).congr_deriv
      (by simp only [sub_smul, one_smul])
  · rw [eD]
    refine gm_exists_bound_deriv (P := P) (ρ := fun i t => 1 - (P.gs_phase i).ρC t)
      (fun i => continuous_const.sub (gs_continuous_ρC i)) norm_uvec_le fun t => ?_
    exact ((hC t).sub (hasDerivAt_vvec t).hasDerivWithinAt).congr_deriv
      (by simp only [sub_smul, one_smul, neg_smul]; abel)

lemma gm_vplus_cap_A {t : ℝ} (ht : t ∈ Ico 0 (π / 2)) : vplus P.cap t = P.curveA t :=
  ((proposition6_4_5 (gm_isCap hP hbox) (gm_injCond1 hP hbox)).1 t ht).1.trans
    (gm_aK hP hbox (Ico_subset_Icc_self ht))

lemma gm_vplus_cap_C {s : ℝ} (hs : s ∈ Icc (π / 2) π) :
    vplus P.cap s = P.curveC (s - π / 2) := by
  rw [← gm_cK hP hbox ⟨by linarith [hs.1], by linarith [hs.2]⟩]
  simp only [cK, cPlus, sub_add_cancel]

/-- `σ_K` has no atom at `0` (by the injectivity condition). -/
lemma gm_sigma_cap_zero : sigma P.cap {0} = 0 := by
  obtain ⟨r, s, -, -, -, -, h1, -⟩ := gm_injCond1 hP hbox
  have : (sigma P.cap).restrict (Ico 0 (π / 2)) {0} = 0 := by
    rw [h1]; exact measure_singleton _
  have hsub : ({0} : Set ℝ) ⊆ Ico 0 (π / 2) := singleton_subset_iff.2 ⟨le_rfl, by positivity⟩
  rwa [Measure.restrict_apply (measurableSet_singleton 0), inter_eq_left.2 hsub] at this

/-- Proposition 8.4.4 (1): `σ_K = ⟨𝐀', v_t⟩ dt` on `[0, π/2)`. -/
lemma gm_prop844_one : (sigma P.cap).restrict (Ico 0 (π / 2)) =
    (volume.restrict (Ico 0 (π / 2))).withDensity
      (fun t => ENNReal.ofReal (dot (deriv P.curveA t) (vvec t))) := by
  obtain ⟨M, hM⟩ := (gm_bound_deriv hP).1
  rw [← gm_withDensity_restrict_self measurableSet_Ico]
  apply gm_restrict_Ico_eq (by positivity) (gm_sigma_cap_zero hP hbox) (measure_singleton _)
  · intro a b _ _ _; exact measure_Ioc_lt_top.ne
  · intro a b ha hab hb
    rw [gm_withDensity_Ioc (S := Ico 0 (π / 2)) _
      (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)]
    simpa only [add_zero] using gm_sigma_Ioc (ψ := 0) (γ := P.curveA) (γ' := deriv P.curveA)
      (gm_isConvexBody_cap hP hbox) hab.le (gm_junctions_countable (P := P))
      (fun t ht => by
        rw [add_zero]; exact gm_vplus_cap_A hP hbox ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (gs_continuous_contactA hP).continuousOn
      (fun t ht => (gm_differentiableAt_curveA hP ht.2).hasDerivAt) (measurable_deriv _)
      (fun t ht => hM t ⟨by linarith [ht.1], by linarith [ht.2]⟩)

/-- Proposition 8.4.4 (2): `σ̆_{B_K} = ⟨-𝐁', v_t⟩ dt` on `[t_3, t_5)`. -/
lemma gm_prop844_two :
    (sigmaBreve (rightBody P.φ P.cap)).restrict (Ico (π / 2 - P.θ) (π / 2)) =
      (volume.restrict (Ico (π / 2 - P.θ) (π / 2))).withDensity
        (fun t => ENNReal.ofReal (dot (-deriv P.curveB t) (vvec t))) := by
  have hB := gm_isConvexBody_B hP hbox
  have hcd : π / 2 - P.θ < π / 2 := (gm_c_lt_d hP).trans (gm_d_lt hP)
  obtain ⟨M, hM⟩ := (gm_bound_deriv hP).2.1
  rw [← gm_withDensity_restrict_self measurableSet_Ico]
  apply gm_restrict_Ico_eq hcd ?_ (measure_singleton _)
  · intro a b _ _ _
    rw [gm_sigmaBreve_apply, preimage_sub_const_Ioc]
    exact measure_Ioc_lt_top.ne
  · intro a b ha hab hb
    rw [gm_withDensity_Ioc (S := Ico (π / 2 - P.θ) (π / 2)) _
      (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩),
      gm_sigmaBreve_apply, preimage_sub_const_Ioc]
    have := gm_sigma_Ioc (ψ := π) (γ := P.curveB) (γ' := deriv P.curveB)
      (E := {π / 2 - P.φ}) hB hab.le (countable_singleton _)
      (fun t ht => by
        -- `𝐁(t) = v_{B_K}⁺(π + t)` on `(t_3, t_5)` (Theorem 8.4.3 (1)) and at `t_3`
        rw [add_comm]
        rcases (show π / 2 - P.θ ≤ t by linarith [ht.1]).lt_or_eq with h | h
        · exact ((theorem8_4_3_one hP hbox).2 t ⟨h, show t < π / 2 by linarith [ht.2]⟩).1.symm
        · rw [← h]; exact gm_B_vplus_c hP hbox)
      (gm_continuous_curveB hP).continuousOn (fun t ht => ?_) (measurable_deriv _)
      (fun t ht => hM t ⟨by linarith [ht.1, gm_θ_lt hP, pi_pos], by linarith [ht.2]⟩)
    · rw [this]
      congr 1; funext t; congr 1
      rw [vvec_add_pi, dot_neg_right, dot_neg_left]
    · obtain ⟨c, -, hd⟩ := (theorem8_4_1_tangents hP hbox).1 t
        ⟨show π / 2 - P.θ < t by linarith [ht.1.1], show t < π / 2 by linarith [ht.1.2]⟩ ht.2
      exact hd.differentiableAt.hasDerivAt
  · rw [gm_sigmaBreve_apply, gm_preimage_sub_singleton, add_comm]
    exact inj_sigma_singleton_eq_zero hB (by rw [gm_B_vplus_c hP hbox, gm_B_vminus_c hP hbox])

/-- Proposition 8.4.4 (3): `σ_K = ⟨-𝐂'(t - π/2), u_{t - π/2}⟩ dt` on `(π/2, π]`. -/
lemma gm_prop844_three : (sigma P.cap).restrict (Ioc (π / 2) π) =
    (volume.restrict (Ioc (π / 2) π)).withDensity
      (fun t => ENNReal.ofReal (dot (-deriv P.curveC (t - π / 2)) (uvec (t - π / 2)))) := by
  obtain ⟨M, hM⟩ := (gm_bound_deriv hP).2.2.1
  rw [← gm_withDensity_restrict_self measurableSet_Ioc]
  apply gm_restrict_Ioc_eq
  · intro a b _ _ _; exact measure_Ioc_lt_top.ne
  · intro a b ha hab hb
    rw [gm_withDensity_Ioc _ (Ioc_subset_Ioc ha hb)]
    have := gm_sigma_Ioc (ψ := 0) (γ := fun s => P.curveC (s - π / 2))
      (γ' := fun s => deriv P.curveC (s - π / 2))
      (E := (fun t => t + π / 2) '' {P.φ, P.θ, π / 2 - P.θ, π / 2 - P.φ})
      (gm_isConvexBody_cap hP hbox) hab.le ((gm_junctions_countable (P := P)).image _)
      (fun t ht => by
        rw [add_zero]; exact gm_vplus_cap_C hP hbox ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      ((gs_continuous_contactC hP).comp (continuous_sub_right _)).continuousOn
      (fun t ht => ?_) ((measurable_deriv _).comp (measurable_id.sub_const _))
      (fun t ht => hM _ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    · simp only [add_zero] at this
      rw [this]
      congr 1; funext t; congr 1
      rw [gm_vvec_sub_pi_div_two, dot_neg_right, dot_neg_left]
    · have hJ : t - π / 2 ∉ ({P.φ, P.θ, π / 2 - P.θ, π / 2 - P.φ} : Set ℝ) :=
        fun h => ht.2 ⟨t - π / 2, h, by ring⟩
      exact (gm_differentiableAt_curveC hP hJ).hasDerivAt.comp_sub_const t (π / 2)

/-- Proposition 8.4.4 (4): `σ̆_{D_K} = ⟨𝐃'(t - π/2), u_{t - π/2}⟩ dt` on
`(π/2, π/2 + t_2]`. -/
lemma gm_prop844_four :
    (sigmaBreve (leftBody P.φ P.cap)).restrict (Ioc (π / 2) (π / 2 + P.θ)) =
      (volume.restrict (Ioc (π / 2) (π / 2 + P.θ))).withDensity
        (fun t => ENNReal.ofReal (dot (deriv P.curveD (t - π / 2)) (uvec (t - π / 2)))) := by
  have hD := gm_isConvexBody_D hP hbox
  obtain ⟨M, hM⟩ := (gm_bound_deriv hP).2.2.2
  rw [← gm_withDensity_restrict_self measurableSet_Ioc]
  apply gm_restrict_Ioc_eq
  · intro a b _ _ _
    rw [gm_sigmaBreve_apply, preimage_sub_const_Ioc]
    exact measure_Ioc_lt_top.ne
  · intro a b ha hab hb
    rw [gm_withDensity_Ioc _ (Ioc_subset_Ioc ha hb), gm_sigmaBreve_apply, preimage_sub_const_Ioc]
    have := gm_sigma_Ioc (ψ := π) (γ := fun t => P.curveD (t - π / 2))
      (γ' := fun t => deriv P.curveD (t - π / 2)) (E := {π / 2 + P.φ}) hD hab.le
      (countable_singleton _) (fun t ht => ?_)
      ((gm_continuous_curveD hP).comp (continuous_sub_right _)).continuousOn
      (fun t ht => ?_) ((measurable_deriv _).comp (measurable_id.sub_const _))
      (fun t ht => hM _ ⟨by linarith [ht.1], by linarith [ht.2, gm_θ_lt hP, pi_pos]⟩)
    · rw [this]
      congr 1; funext t; congr 1
      rw [vvec_add_pi, gm_vvec_sub_pi_div_two, neg_neg]
    · -- `𝐃(s) = v_{D_K}⁺(3π/2 + s)` on `(t_0, t_2)` (Theorem 8.4.3 (1)) and at `t_0`, `t_2`
      have key : vplus (leftBody P.φ P.cap) (3 * π / 2 + (t - π / 2)) = P.curveD (t - π / 2) := by
        rcases (show 0 ≤ t - π / 2 by linarith [ht.1]).lt_or_eq with h0 | h0
        · rcases (show t - π / 2 ≤ P.θ by linarith [ht.2]).lt_or_eq with h1 | h1
          · exact ((theorem8_4_3_one hP hbox).1 (t - π / 2) ⟨h0, h1⟩).1.symm
          · rw [h1]; exact gm_D_vplus_θ hP hbox
        · rw [← h0, add_zero]; exact gm_D_vplus_zero hP hbox
      rwa [show 3 * π / 2 + (t - π / 2) = t + π by ring] at key
    · have ht' : t - π / 2 ∈ Ioo (P.tPt 0) (P.tPt 2) :=
        ⟨show 0 < t - π / 2 by linarith [ht.1.1], show t - π / 2 < P.θ by linarith [ht.1.2]⟩
      have hne : t - π / 2 ≠ P.tPt 1 := fun h => ht.2 (by
        rw [mem_singleton_iff]; change t - π / 2 = P.φ at h; linarith)
      obtain ⟨c, -, hd⟩ := (theorem8_4_1_tangents hP hbox).2 (t - π / 2) ht' hne
      exact hd.differentiableAt.hasDerivAt.comp_sub_const t (π / 2)

end

end GerverParams

/-- **Proposition 8.4.4** (`pro:measure-translation`): the surface area measures of `K`, `B_K`,
`D_K` in terms of the boundary curves.

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
  refine ⟨gm_prop844_one hP hbox, gm_prop844_two hP hbox, gm_prop844_three hP hbox, ?_⟩
  rw [show π / 2 + P.tPt 0 = π / 2 from add_zero _]; exact gm_prop844_four hP hbox

/-- The intervals `J_i = [t_{i-1}, t_i)` for `1 ≤ i ≤ 5` and `J_i = π - J_{11 - i}` for `6 ≤ i ≤ 10`
(Definition 8.4.7, `def:interval-j`). -/
noncomputable def GerverParams.jInt (P : GerverParams) (i : ℕ) : Set ℝ :=
  if i ≤ 5 then Ico (P.tPt (i - 1)) (P.tPt i)
  else (fun s => π - s) '' Ico (P.tPt (10 - i)) (P.tPt (11 - i))

/-! ### Theorem 8.4.5 -/

namespace GerverParams

variable {P : GerverParams}

lemma gm_jInt_1 (P : GerverParams) : P.jInt 1 = Ico 0 P.φ := rfl
lemma gm_jInt_2 (P : GerverParams) : P.jInt 2 = Ico P.φ P.θ := rfl
lemma gm_jInt_3 (P : GerverParams) : P.jInt 3 = Ico P.θ (π / 2 - P.θ) := rfl
lemma gm_jInt_4 (P : GerverParams) : P.jInt 4 = Ico (π / 2 - P.θ) (π / 2 - P.φ) := rfl
lemma gm_jInt_5 (P : GerverParams) : P.jInt 5 = Ico (π / 2 - P.φ) (π / 2) := rfl
lemma gm_jInt_6 (P : GerverParams) : P.jInt 6 = Ioc (π / 2) (π / 2 + P.φ) := by
  show (fun s => π - s) '' Ico (π / 2 - P.φ) (π / 2) = _
  rw [image_const_sub_Ico]; congr 1 <;> ring
lemma gm_jInt_7 (P : GerverParams) : P.jInt 7 = Ioc (π / 2 + P.φ) (π / 2 + P.θ) := by
  show (fun s => π - s) '' Ico (π / 2 - P.θ) (π / 2 - P.φ) = _
  rw [image_const_sub_Ico]; congr 1 <;> ring
lemma gm_jInt_8 (P : GerverParams) : P.jInt 8 = Ioc (π / 2 + P.θ) (π - P.θ) := by
  show (fun s => π - s) '' Ico P.θ (π / 2 - P.θ) = _
  rw [image_const_sub_Ico]; congr 1; ring
lemma gm_jInt_9 (P : GerverParams) : P.jInt 9 = Ioc (π - P.θ) (π - P.φ) := by
  show (fun s => π - s) '' Ico P.φ P.θ = _
  rw [image_const_sub_Ico]
lemma gm_jInt_10 (P : GerverParams) : P.jInt 10 = Ioc (π - P.φ) π := by
  show (fun s => π - s) '' Ico 0 P.φ = _
  rw [image_const_sub_Ico, sub_zero]

section
variable (hP : P.IsSolution) (hbox : P.InBox)
include hP hbox

/-! The densities of Proposition 8.4.4 restricted to subintervals. -/

lemma gm_sigma_restrict_A {T : Set ℝ} (hT : MeasurableSet T) (hTS : T ⊆ Ico 0 (π / 2)) :
    (sigma P.cap).restrict T = (volume.restrict T).withDensity
      (fun t => ENNReal.ofReal (dot (deriv P.curveA t) (vvec t))) :=
  gm_restrict_eq_withDensity_of_subset (proposition8_4_4 hP hbox).1 hT hTS

lemma gm_sigma_restrict_C {T : Set ℝ} (hT : MeasurableSet T) (hTS : T ⊆ Ioc (π / 2) π) :
    (sigma P.cap).restrict T = (volume.restrict T).withDensity
      (fun t => ENNReal.ofReal (dot (-deriv P.curveC (t - π / 2)) (uvec (t - π / 2)))) :=
  gm_restrict_eq_withDensity_of_subset (proposition8_4_4 hP hbox).2.2.1 hT hTS

lemma gm_sigmaBreve_restrict_B {T : Set ℝ} (hT : MeasurableSet T)
    (hTS : T ⊆ Ico (π / 2 - P.θ) (π / 2)) :
    (sigmaBreve (rightBody P.φ P.cap)).restrict T = (volume.restrict T).withDensity
      (fun t => ENNReal.ofReal (dot (-deriv P.curveB t) (vvec t))) :=
  gm_restrict_eq_withDensity_of_subset (proposition8_4_4 hP hbox).2.1 hT hTS

lemma gm_sigmaBreve_restrict_D {T : Set ℝ} (hT : MeasurableSet T)
    (hTS : T ⊆ Ioc (π / 2) (π / 2 + P.θ)) :
    (sigmaBreve (leftBody P.φ P.cap)).restrict T = (volume.restrict T).withDensity
      (fun t => ENNReal.ofReal (dot (deriv P.curveD (t - π / 2)) (uvec (t - π / 2)))) := by
  have h := (proposition8_4_4 hP hbox).2.2.2
  rw [show π / 2 + P.tPt 0 = π / 2 from add_zero _] at h
  exact gm_restrict_eq_withDensity_of_subset h hT hTS

omit hP hbox in
lemma gm_iota_restrict {K : Set (ℝ × ℝ)} {T : Set ℝ} (hT : MeasurableSet T)
    (hTS : T ⊆ Icc 0 π) :
    (iota K).restrict T = (volume.restrict T).withDensity (fun t => ENNReal.ofReal (iFun K t)) :=
  gm_restrict_eq_withDensity_of_subset (gm_withDensity_restrict_self measurableSet_Icc _) hT hTS

/-- `𝐱_K' = 𝐱'` on `(0, π/2)`. -/
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

/-- The density `⟨-𝐁', v_t⟩` of `σ̆_{B_K}` is nonnegative. -/
lemma gm_rhoB_pos {t : ℝ} (ht : t ∈ Ioo (π / 2 - P.θ) (π / 2)) (htd : t ≠ π / 2 - P.φ) :
    0 ≤ dot (-deriv P.curveB t) (vvec t) := by
  obtain ⟨c, hc, hd⟩ := (theorem8_4_1_tangents hP hbox).1 t ht htd
  rw [hd.deriv, dot_neg_left, dot_smul_left, dot_vvec_self]
  linarith

/-- The density `⟨𝐃', u_t⟩` of `σ̆_{D_K}` is nonnegative. -/
lemma gm_rhoD_pos {t : ℝ} (ht : t ∈ Ioo 0 P.θ) (htd : t ≠ P.φ) :
    0 ≤ dot (deriv P.curveD t) (uvec t) := by
  obtain ⟨c, hc, hd⟩ := (theorem8_4_1_tangents hP hbox).2 t ht htd
  rw [hd.deriv, dot_smul_left, dot_uvec_self]
  linarith

omit hP hbox in
lemma gm_measurable_rhoB :
    Measurable (fun t => ENNReal.ofReal (dot (-deriv P.curveB t) (vvec t))) :=
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
      gm_iota_restrict hm
        (hT.trans (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl (by linarith))))]
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
    rw [gm_sigma_restrict_C hP hbox hm hT,
      gm_iota_restrict hm (hT.trans Ioc_subset_Icc_self |>.trans
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

lemma gm_bv_of_contDiffOn {f : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ 1 f (Icc a b)) : BoundedVariationOn f (Icc a b) := by
  rw [← uIcc_of_le hab] at hf ⊢
  exact hf.absolutelyContinuousOnInterval.boundedVariationOn

/-- The curve area functional of a curve which is `C¹` on two adjacent closed intervals
`[a, m]` and `[m, b]`: `𝒥(x) = ½ ∫_a^b ρ` for any `ρ` with `x × x' = ρ` off `m`. -/
lemma gm_curveArea_two {x : ℝ → ℝ × ℝ} {a m b : ℝ} (ham : a < m) (hmb : m < b)
    (h1 : ContDiffOn ℝ 1 x (Icc a m)) (h2 : ContDiffOn ℝ 1 x (Icc m b)) {ρ : ℝ → ℝ}
    (hρ : ∀ t ∈ Ioo a b, t ≠ m → cross (x t) (deriv x t) = ρ t) :
    curveArea x a b = (1 / 2) * ∫ t in a..b, ρ t := by
  have hcbv : IsCBV x a b := isCBV_append ham.le hmb.le
    ⟨h1.continuousOn, gm_bv_of_contDiffOn ham.le h1⟩
    ⟨h2.continuousOn, gm_bv_of_contDiffOn hmb.le h2⟩
  -- On each piece `[u, v]`, `x × x' = ρ` off the endpoints, and `x × x'` is continuous.
  have piece : ∀ {u v : ℝ}, u < v → ContDiffOn ℝ 1 x (Icc u v) → Ioo u v ⊆ Ioo a b →
      m ∉ Ioo u v →
      (∫ t in u..v, cross (x t) (derivWithin x (Icc u v) t)) = (∫ t in u..v, ρ t) ∧
        IntervalIntegrable ρ volume u v := by
    intro u v huv hx hsub hm
    have hint :
        IntervalIntegrable (fun t => cross (x t) (derivWithin x (Icc u v) t)) volume u v := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le huv.le]
      exact continuousOn_cross hx.continuousOn
        (hx.continuousOn_derivWithin (uniqueDiffOn_Icc huv) le_rfl)
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

namespace GerverParams

variable {P : GerverParams}

section
variable (hP : P.IsSolution) (hbox : P.InBox)
include hP hbox

/-- `𝒥(𝐁|_{[t_3, t_5]}) = ½ ∫ ⟨-𝐁', v_t⟩ h_{B_K}(t + π) dt`, since `𝐁` lies on the supporting
line `l_{B_K}(π + t)` with `𝐁' ∥ v_t`. -/
lemma gm_curveArea_B : curveArea P.curveB (π / 2 - P.θ) (π / 2) =
    (1 / 2) * ∫ t in (π / 2 - P.θ)..(π / 2),
      dot (-deriv P.curveB t) (vvec t) * supp (rightBody P.φ P.cap) (t + π) := by
  apply gm_curveArea_two (gm_c_lt_d hP) (gm_d_lt hP) (gm_contDiffOn_B₄ hP) (gm_contDiffOn_B₅ hP)
  intro t ht htd
  obtain ⟨c, -, hd⟩ := (theorem8_4_1_tangents hP hbox).1 t ht htd
  rw [hd.deriv, cross_smul_right, cross_vvec, gm_B_wallB hP hbox ⟨ht.1.le, ht.2.le⟩,
    dot_neg_left, dot_smul_left, dot_vvec_self, add_comm t π,
    (gm_B_edge hP hbox ⟨ht.1.le, ht.2.le⟩).1]
  ring

/-- `𝒥(𝐃|_{[t_0, t_2]}) = ½ ∫ ⟨𝐃', u_t⟩ h_{D_K}(3π/2 + t) dt`, since `𝐃` lies on the supporting
line `l_{D_K}(3π/2 + t)` with `𝐃' ∥ u_t`. -/
lemma gm_curveArea_D : curveArea P.curveD 0 P.θ =
    (1 / 2) * ∫ t in (0 : ℝ)..P.θ,
      dot (deriv P.curveD t) (uvec t) * supp (leftBody P.φ P.cap) (3 * π / 2 + t) := by
  apply gm_curveArea_two (gm_φ_pos hP) (gm_φ_lt_θ hP) (gm_contDiffOn_D₁ hP) (gm_contDiffOn_D₂ hP)
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
  have hc2 : π / 2 - P.θ < π / 2 := (gm_c_lt_d hP).trans (gm_d_lt hP)
  have e : Ioo P.φ (π / 2) = Ioo P.φ (π / 2 - P.θ) ∪ Ico (π / 2 - P.θ) (π / 2) :=
    (Ioo_union_Ico_eq_Ioo (by linarith [gm_θ_lt hP, gm_φ_lt_θ hP]) hc2.le).symm
  have hz : sigmaBreve (rightBody P.φ P.cap) (Ioo P.φ (π / 2 - P.θ)) = 0 := by
    rw [gm_sigmaBreve_apply, preimage_sub_const_Ioo, add_comm P.φ, add_comm (π / 2 - P.θ)]
    refine sigma_Ioo_eq_zero_of_vplus_const (gm_isConvexBody_B hP hbox)
      (by linarith [gm_θ_lt hP, gm_φ_lt_θ hP]) (q := P.curveB (π / 2 - P.θ)) fun s hs => ?_
    rcases hs.1.eq_or_lt with rfl | hs1
    · exact gm_B_vplus_φ hP hbox
    · have := vplus_mem_edge (gm_isConvexBody_B hP hbox) s
      rwa [gm_B_corner hP hbox s ⟨hs1, hs.2⟩] at this
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
    rw [gm_sigmaBreve_apply, preimage_sub_const_Ioo,
      show π / 2 + P.θ + π = 3 * π / 2 + P.θ by ring,
      show π / 2 + (π / 2 - P.φ) + π = 3 * π / 2 + (π / 2 - P.φ) by ring]
    refine sigma_Ioo_eq_zero_of_vplus_const (gm_isConvexBody_D hP hbox) (by linarith)
      (q := P.curveD P.θ) fun s hs => ?_
    rcases hs.1.eq_or_lt with rfl | hs1
    · exact gm_D_vplus_θ hP hbox
    · have := vplus_mem_edge (gm_isConvexBody_D hP hbox) s
      rwa [gm_D_corner hP hbox s ⟨hs1, hs.2⟩] at this
  rw [e, Measure.restrict_union
    (Set.disjoint_left.2 fun t h1 h2 => absurd h1.2 (not_le.2 h2.1)) measurableSet_Ioo,
    Measure.restrict_eq_zero.2 hz, add_zero]

/-- `𝒥(𝐛_{B_K})` (from `σ_{B_K}` on `(π + φ, 3π/2)`) equals the same integral as `𝒥(𝐁)`, by
Proposition 8.4.4 (2), since `σ̆_{B_K}` vanishes on `(φ, t_3)`. -/
lemma gm_convexCurveArea_B : convexCurveArea (rightBody P.φ P.cap) (π + P.φ) (3 * π / 2) =
    (1 / 2) * ∫ t in (π / 2 - P.θ)..(π / 2),
      dot (-deriv P.curveB t) (vvec t) * supp (rightBody P.φ P.cap) (t + π) := by
  have hc2 : π / 2 - P.θ < π / 2 := (gm_c_lt_d hP).trans (gm_d_lt hP)
  unfold convexCurveArea
  congr 1
  have h1 : ∫ t in Ioo (π + P.φ) (3 * π / 2), supp (rightBody P.φ P.cap) t
        ∂(sigma (rightBody P.φ P.cap)) =
      ∫ t in Ioo P.φ (π / 2), suppBreve (rightBody P.φ P.cap) t
        ∂(sigmaBreve (rightBody P.φ P.cap)) := by
    rw [sigmaBreve, (measurableEmbedding_subRight π).setIntegral_map, preimage_sub_const_Ioo,
      show P.φ + π = π + P.φ by ring, show π / 2 + π = 3 * π / 2 by ring]
    simp only [suppBreve, sub_add_cancel]
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

/-- `𝒥(𝐝_{D_K})` (from `σ_{D_K}` on `(3π/2, 3π/2 + φ^L)`) equals the same integral as `𝒥(𝐃)`,
by Proposition 8.4.4 (4), since `σ̆_{D_K}` vanishes on `(π/2 + t_2, π - φ)`. -/
lemma gm_convexCurveArea_D :
    convexCurveArea (leftBody P.φ P.cap) (3 * π / 2) (3 * π / 2 + (π / 2 - P.φ)) =
      (1 / 2) * ∫ t in (0 : ℝ)..P.θ,
        dot (deriv P.curveD t) (uvec t) * supp (leftBody P.φ P.cap) (3 * π / 2 + t) := by
  have hθ0 := gm_θ_pos hP
  unfold convexCurveArea
  congr 1
  have h1 : ∫ t in Ioo (3 * π / 2) (3 * π / 2 + (π / 2 - P.φ)), supp (leftBody P.φ P.cap) t
        ∂(sigma (leftBody P.φ P.cap)) =
      ∫ t in Ioo (π / 2) (π / 2 + (π / 2 - P.φ)), suppBreve (leftBody P.φ P.cap) t
        ∂(sigmaBreve (leftBody P.φ P.cap)) := by
    rw [sigmaBreve, (measurableEmbedding_subRight π).setIntegral_map, preimage_sub_const_Ioo,
      show π / 2 + π = 3 * π / 2 by ring,
      show π / 2 + (π / 2 - P.φ) + π = 3 * π / 2 + (π / 2 - P.φ) by ring]
    simp only [suppBreve, sub_add_cancel]
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

/-- **Theorem 8.4.3** (`thm:gerver-left-right`) (2): `𝐱_K^L = Y_{D_K} = 𝐃(t_2)` and `𝐝_{D_K}` is the
curve `𝐃`; `𝐱_K^R = X_{B_K} = 𝐁(t_3)` (the paper writes `𝐃(t_3)`) and `𝐛_{B_K}` is the curve `𝐁`.
That `𝐝_{D_K}` is `𝐃` as oriented curves is formalized as the equality of the sets together with
the equality `𝒥(𝐝_{D_K}) = 𝒥(𝐃)` of the curve area functionals, and the same for `𝐛_{B_K}` and `𝐁`.

Departure from the paper: the paper does not prove the two equalities of curve area functionals
separately (they follow from `𝐝_{D_K} = 𝐃` as oriented curves). This proof computes `𝒥(𝐝_{D_K})`
and `𝒥(𝐛_{B_K})` from the densities of `σ̆` (the computation of Proposition 8.4.4, through
Theorem 5.2.2), and `𝒥(𝐃)`, `𝒥(𝐁)` from the derivatives of the curves (Theorem 8.4.1 (3), (4)),
which give the same integrals, because `𝒥` of a convex arc is defined as `½ ∫ h dσ` and
orientations of curves are not formalized (reason 3). -/
theorem theorem8_4_3_two {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    xLeft P.φ P.cap = yD P.φ (leftBody P.φ P.cap) ∧
      yD P.φ (leftBody P.φ P.cap) = P.curveD (P.tPt 2) ∧
      tailD P.φ (leftBody P.φ P.cap) = P.curveD '' Icc (P.tPt 0) (P.tPt 2) ∧
      convexCurveArea (leftBody P.φ P.cap) (3 * π / 2) (3 * π / 2 + (π / 2 - P.φ)) =
        curveArea P.curveD 0 P.θ ∧
      xRight P.φ P.cap = xB P.φ (rightBody P.φ P.cap) ∧
      xB P.φ (rightBody P.φ P.cap) = P.curveB (P.tPt 3) ∧
      tailB P.φ (rightBody P.φ P.cap) = P.curveB '' Icc (P.tPt 3) (P.tPt 5) ∧
      convexCurveArea (rightBody P.φ P.cap) (π + P.φ) (3 * π / 2) =
        curveArea P.curveB (π / 2 - P.θ) (π / 2) := by
  have hyD : yD P.φ (leftBody P.φ P.cap) = P.curveD P.θ := gm_D_vminus_end hP hbox
  have hxB : xB P.φ (rightBody P.φ P.cap) = P.curveB (π / 2 - P.θ) := gm_B_vplus_φ hP hbox
  exact ⟨by rw [hyD, gm_D_θ hP hbox], hyD, gm_tailD hP hbox,
    (gm_convexCurveArea_D hP hbox).trans (gm_curveArea_D hP hbox).symm,
    by rw [hxB, gm_B_c hP hbox], hxB, gm_tailB hP hbox,
    (gm_convexCurveArea_B hP hbox).trans (gm_curveArea_B hP hbox).symm⟩

/-- **Theorem 8.4.6** (`thm:upper-bound-q-gerver-match`). `𝒜(K) = 𝒬(K, B_K, D_K)` for the cap of
Gerver's sofa. -/
theorem theorem8_4_6 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    sofaArea (π / 2) P.cap = upperQ P.φ P.cap (rightBody P.φ P.cap) (leftBody P.φ P.cap) := by
  obtain ⟨h1, -, -, eD, h4, -, -, eB⟩ := theorem8_4_3_two hP hbox
  have hN : area (niche P.cap (π / 2)) = curveArea P.path P.φ (π / 2 - P.φ) -
      curveArea P.curveB (π / 2 - P.θ) (π / 2) - curveArea P.curveD 0 P.θ :=
    (theorem8_4_1_niche hP hbox).2.2.2.2.2.2.2
  have hsub : Icc P.φ (π / 2 - P.φ) ⊆ Icc 0 (π / 2) :=
    Icc_subset_Icc (gm_φ_pos hP).le (by linarith [gm_φ_pos hP])
  have hx : curveArea (innerCorner P.cap) P.φ (π / 2 - P.φ) =
      curveArea P.path P.φ (π / 2 - P.φ) :=
    curveArea_congr (by linarith [gm_φ_lt_θ hP, gm_θ_lt hP])
      fun t ht => gm_innerCorner hP hbox (hsub ht)
  unfold sofaArea upperQ
  rw [hN, ← h1, ← h4, hx, eB, eD]
  simp only [segArea, cross_self, zero_div]
  ring

end MovingSofaOptimality
