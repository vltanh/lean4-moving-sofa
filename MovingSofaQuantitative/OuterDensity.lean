module

public import MovingSofaQuantitative.TurningCap
public import MovingSofaStability.Margins

/-!
# Whole-phase curvature margins of Gerver's outer cap

Uncompiled proof source. The density lower bound is restricted to the arcs
where it is true. The two endpoint normal gaps have zero density and cannot
absorb a negative perturbation. All estimates below use the exact phase
formulas and the already established parameter box, not a sampled mesh.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaStability MovingSofaOptimality.GerverParams

namespace MovingSofaQuantitative

def outerDensityR (P : GerverParams) (t : ℝ) : ℝ := (P.gs_phase (P.gs_ridx t)).ρA t

def outerDensityL (P : GerverParams) (t : ℝ) : ℝ := (P.gs_phase (P.gs_ridx t)).ρC t

private theorem quadratic_density_bounds {b₁ b₂ s : ℝ}
    (hb₁ : b₁ ∈ Icc (-528 / 1000 : ℝ) (-527 / 1000))
    (hb₂ : b₂ ∈ Icc (920 / 1000 : ℝ) (921 / 1000))
    (hs : s ∈ Icc (0 : ℝ) (682 / 1000)) :
    (1 / 2 : ℝ) ≤ 1 / 2 - s ^ 2 / 4 + b₁ * s + b₂ ∧
      1 / 2 - s ^ 2 / 4 + b₁ * s + b₂ ≤ 2 := by
  have hprod := mul_le_mul_of_nonneg_right hb₁.1 hs.1
  have hprod0 := mul_nonpos_of_nonpos_of_nonneg (by linarith [hb₁.2] : b₁ ≤ 0) hs.1
  have hsq := mul_self_le_mul_self hs.1 hs.2
  constructor <;> nlinarith [hb₂.1, hb₂.2, hs.1, hs.2, sq_nonneg s]

private theorem affine_density_bounds {b₁ s : ℝ}
    (hb₁ : b₁ ∈ Icc (-528 / 1000 : ℝ) (-527 / 1000))
    (hs : s ∈ Icc (0 : ℝ) (682 / 1000)) :
    (1 / 2 : ℝ) ≤ s / 2 - b₁ ∧ s / 2 - b₁ ≤ 2 := by
  constructor <;> linarith [hb₁.1, hb₁.2, hs.1, hs.2]

/-- Both outer densities lie in [0,2], and away from the normal gaps they
have the positive margin needed for one-sided smoothing. The strictness at
the left gap endpoint reflects the RIGHT phase selection. -/
theorem outer_phase_margins {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {i : Fin 5} {t : ℝ} (hi : P.gs_rpiece i t) (ht : t ∈ Icc (0 : ℝ) (π / 2)) :
    (0 ≤ (P.gs_phase i).ρA t ∧ (P.gs_phase i).ρA t ≤ 2) ∧
    (0 ≤ (P.gs_phase i).ρC t ∧ (P.gs_phase i).ρC t ≤ 2) ∧
    (P.φ ≤ t → (1 / 2 : ℝ) ≤ (P.gs_phase i).ρA t) ∧
    (t < π / 2 - P.φ → (1 / 2 : ℝ) ≤ (P.gs_phase i).ρC t) := by
  have hB := romik_bounds hP hbox
  have hb₁ : P.b₁ ∈ Icc (-528 / 1000 : ℝ) (-527 / 1000) := by
    constructor <;> linarith [hB.b₁_mem.1, hB.b₁_mem.2]
  have hb₂ : P.b₂ ∈ Icc (920 / 1000 : ℝ) (921 / 1000) := by
    constructor <;> linarith [hB.b₂_mem.1, hB.b₂_mem.2]
  have hθ : P.θ < 682 / 1000 := by linarith [hB.θ_mem.2]
  have hθ₀ : (68 / 100 : ℝ) < P.θ := by linarith [hB.θ_mem.1]
  have hc : P.c₁ ∈ Icc (626 / 1000 : ℝ) (627 / 1000) := by
    constructor <;> linarith [hB.c₁_mem.1, hB.c₁_mem.2]
  have hπ : π < 22 / 7 := pi_lt_d20.trans (by norm_num)
  fin_cases i
  · have hit : t < P.φ := hi
    rw [gs_ρA₁_eq, gs_ρC₁_eq]
    refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · intro h
      exact (not_lt_of_ge h hit).elim
    · intro _
      norm_num
  · have hit : P.φ ≤ t ∧ t < P.θ := hi
    have hs : t ∈ Icc (0 : ℝ) (682 / 1000) := ⟨ht.1, hit.2.le.trans hθ.le⟩
    have hA := quadratic_density_bounds hb₁ hb₂ hs
    have hC := affine_density_bounds hb₁ hs
    rw [gs_ρA₂_eq, gs_ρC₂_eq]
    constructor
    · constructor <;> linarith [hA.1, hA.2]
    constructor
    · constructor <;> linarith [hC.1, hC.2]
    exact ⟨fun _ => hA.1, fun _ => hC.1⟩
  · have hit : P.θ ≤ t ∧ t < π / 2 - P.θ := hi
    rw [gs_ρA₃_eq, gs_ρC₃_eq hP]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, (fun _ => ?_), (fun _ => ?_)⟩ <;>
      linarith [hit.1, hit.2, hc.1, hc.2, ht.1, ht.2]
  · have hit : π / 2 - P.θ ≤ t ∧ t < π / 2 - P.φ := hi
    have hs : π / 2 - t ∈ Icc (0 : ℝ) (682 / 1000) := by
      constructor <;> linarith [ht.2, hit.1]
    have hA := affine_density_bounds hb₁ hs
    have hC := quadratic_density_bounds hb₁ hb₂ hs
    rw [gs_ρA₄_eq' hP, gs_ρC₄_eq' hP]
    constructor
    · constructor <;> linarith [hA.1, hA.2]
    constructor
    · constructor <;> linarith [hC.1, hC.2]
    exact ⟨fun _ => hA.1, fun _ => hC.1⟩
  · have hit : π / 2 - P.φ ≤ t := hi
    rw [gs_ρA₅_eq hP, gs_ρC₅_eq hP]
    refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · intro _
      norm_num
    · intro h
      exact (not_lt_of_ge hit h).elim

/-- The selected one-sided densities obey the same whole-interval bounds. -/
theorem outer_density_margins {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (π / 2)) :
    (0 ≤ outerDensityR P t ∧ outerDensityR P t ≤ 2) ∧
    (0 ≤ outerDensityL P t ∧ outerDensityL P t ≤ 2) ∧
    (P.φ ≤ t → (1 / 2 : ℝ) ≤ outerDensityR P t) ∧
    (t < π / 2 - P.φ → (1 / 2 : ℝ) ≤ outerDensityL P t) :=
  outer_phase_margins hP hbox (gs_rpiece_ridx t) ht

/-- The top edge has a strict length reserve under the reference enclosures. -/
theorem outer_top_length {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (3 / 2 : ℝ) < (contactA P.path (π / 2)).1 - (contactC P.path 0).1 := by
  have hB := romik_bounds hP hbox
  have hx := gs_X₀_bounds hP hB
  rw [gs_A_pi_div_two hP, gs_C_zero hP]
  simp only
  linarith [hB.a₁_mem.1, hx.1]

/-- The right normal gap is genuinely flat in the supporting curve. -/
theorem outerDensityR_gap {P : GerverParams} {t : ℝ} (ht : t < P.φ) :
    outerDensityR P t = 0 := by
  unfold outerDensityR gs_ridx
  simp only [if_pos ht, gs_ρA₁_eq]

/-- The reflected gap includes its first point for the right-selected density. -/
theorem outerDensityL_gap {P : GerverParams} (hP : P.IsSolution) {t : ℝ}
    (ht : π / 2 - P.φ ≤ t) : outerDensityL P t = 0 := by
  have hO := gs_ord hP
  have h1 : ¬t < P.φ := by linarith [hO.1]
  have h2 : ¬t < P.θ := by linarith [hO.1]
  have h3 : ¬t < π / 2 - P.θ := by linarith [hO.1]
  unfold outerDensityL gs_ridx
  simp only [if_neg h1, if_neg h2, if_neg h3, if_neg (not_lt.mpr ht)]
  exact gs_ρC₅_eq hP t

end MovingSofaQuantitative
