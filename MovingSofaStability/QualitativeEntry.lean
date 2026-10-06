module

public import MovingSofaStability.SofaLimitMotion

/-!
# Qualitative entry into the quantitative neighborhood

Compactness supplies entry into a fixed neighborhood, not a rate. The limit
motion is constructed from supporting constraints. A limit of normalized sofas
whose areas tend to `|G|` has area `|G|`, so it is Gerver's sofa, by the
optimality and uniqueness theorems of the coercive route
(`MovingSofaExtremal.area_le_gerver`, `pinned_maximizer_eq_gerver`).
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter Topology TopologicalSpace
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

def compactShapeOfMoving {S : Set Point} (hS : IsMovingSofa S) : CompactShape where
  carrier := S
  isCompact' := isCompact_of_isMovingSofa hS
  nonempty' := hS.choose_spec.2.1.nonempty

def gerverCompactShape {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) : CompactShape :=
  compactShapeOfMoving ⟨π / 2, (GerverParams.gm_movingSofa_std hP hbox).1⟩

theorem maximizing_subsequence {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (K : ℕ → CompactShape) (ωn : ℕ → ℝ)
    (hmove : ∀ n, IsMovingSofaWithAngle (K n : Set Point) (ωn n))
    (hangles : ∀ n, ωn n ∈ Icc (arccos (5 / 11)) (π / 2))
    (htops : ∀ n, supp (K n : Set Point) (π / 2) = 1)
    (hlefts : ∀ n, supp (K n : Set Point) π = supp (gerverSofa P) π)
    (harea : Tendsto (fun n => area (K n : Set Point)) atTop (𝓝 (area (gerverSofa P)))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (K ∘ σ) atTop (𝓝 (gerverCompactShape hP hbox)) ∧
      Tendsto (ωn ∘ σ) atTop (𝓝 (π / 2)) := by
  let B := {L : CompactShape | (L : Set Point) ⊆ normalizedBox P}
  have hB : IsCompact B := NonemptyCompacts.isCompact_subsets_of_isCompact (normalizedBox_compact P)
  have hprod : IsCompact (B ×ˢ Icc (arccos (5 / 11 : ℝ)) (π / 2)) := hB.prod isCompact_Icc
  have hmem : ∀ n, (K n, ωn n) ∈ B ×ˢ Icc (arccos (5 / 11 : ℝ)) (π / 2) := by
    intro n
    exact ⟨pinned_sofa_subset_box (hmove n) (quarter_le_reduced_angle.trans (hangles n).1)
      (htops n) (hlefts n), hangles n⟩
  obtain ⟨⟨L, ω⟩, hLω, σ, hσ, hlim⟩ := hprod.tendsto_subseq hmem
  have hKlim : Tendsto (K ∘ σ) atTop (𝓝 L) := (continuous_fst.tendsto _).comp hlim
  have hωlim : Tendsto (ωn ∘ σ) atTop (𝓝 ω) := (continuous_snd.tendsto _).comp hlim
  obtain ⟨hLmove, hω, htop, hleft⟩ := normalized_moving_limit hKlim hωlim
    (fun n => hmove (σ n)) (fun n => hangles (σ n)) (fun n => htops (σ n)) (fun n => hlefts (σ n))
  have hareaLim := harea.comp hσ.tendsto_atTop
  have hmax : area (L : Set Point) = area (gerverSofa P) := le_antisymm
    (MovingSofaExtremal.area_le_gerver hP hbox ⟨ω, hLmove⟩)
    (compactShape_area_limsup hKlim hareaLim)
  have hset : (L : Set Point) = gerverSofa P := pinned_maximizer_eq_gerver hP hbox
    ⟨ω, hLmove⟩ htop hleft hmax
  have hLeq : L = gerverCompactShape hP hbox := NonemptyCompacts.ext hset
  have hωeq : ω = π / 2 := by
    by_contra hne
    obtain ⟨p, hp, q, hq, hgt⟩ := gerver_width_gt_one hP hbox
      ⟨(arccos_nonneg _).trans hω.1, hω.2.trans (by linarith [pi_pos])⟩ hne
    rw [hset] at hLmove
    have hle := moving_terminal_projection hLmove hq hp
    linarith
  exact ⟨σ, hσ, hLeq ▸ hKlim, hωeq ▸ hωlim⟩

theorem near_maximizers_enter_neighborhood {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {ρ α₀ : ℝ} (hρ : 0 < ρ) (hα₀ : 0 < α₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ S : Set Point, ∀ ω : ℝ,
      IsMovingSofaWithAngle S ω → ω ∈ Icc (arccos (5 / 11)) (π / 2) →
      sofaDeficit P S < ε₀ →
      EuclideanClose ρ (normalizedSofa P S) (gerverSofa P) ∧ π / 2 - ω < α₀ := by
  classical
  by_contra hn
  have counter (ε : ℝ) (hε : 0 < ε) :
      ∃ S : Set Point, ∃ ω : ℝ, IsMovingSofaWithAngle S ω ∧
        ω ∈ Icc (arccos (5 / 11)) (π / 2) ∧ sofaDeficit P S < ε ∧
        ¬(EuclideanClose ρ (normalizedSofa P S) (gerverSofa P) ∧ π / 2 - ω < α₀) := by
    by_contra hc
    apply hn
    refine ⟨ε, hε, ?_⟩
    intro S ω hS hω hdef
    by_contra hbad
    exact hc ⟨S, ω, hS, hω, hdef, hbad⟩
  choose S ω hS hω hdef hbad using fun n : ℕ => counter (1 / ((n : ℝ) + 1)) (by positivity)
  let K : ℕ → CompactShape := fun n => compactShapeOfMoving (normalizedSofa_moving P ⟨ω n, hS n⟩)
  have hmove : ∀ n, IsMovingSofaWithAngle (K n : Set Point) (ω n) :=
    fun n => normalizedSofa_movingWithAngle P (hS n)
  have htop : ∀ n, supp (K n : Set Point) (π / 2) = 1 := fun n =>
    normalizedSofa_top P (ms_isCompact_of_isMovingSofaWithAngle (hS n)) (hS n).2.1.nonempty
  have hleft : ∀ n, supp (K n : Set Point) π = supp (gerverSofa P) π := fun n =>
    normalizedSofa_left P (ms_isCompact_of_isMovingSofaWithAngle (hS n)) (hS n).2.1.nonempty
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hdef0 : Tendsto (fun n => sofaDeficit P (S n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => sofaDeficit_nonneg hP hbox ⟨ω n, hS n⟩) (fun n => (hdef n).le) hinv
  have harea : Tendsto (fun n => area (K n : Set Point)) atTop (𝓝 (area (gerverSofa P))) := by
    have he := (tendsto_const_nhds (x := area (gerverSofa P))).sub hdef0
    simpa only [K, compactShapeOfMoving, NonemptyCompacts.coe_mk, Compacts.coe_mk, sofaDeficit,
      sub_sub_cancel, sub_zero, area_normalizedSofa] using he
  obtain ⟨σ, hσ, hKlim, hωlim⟩ := maximizing_subsequence hP hbox K ω hmove hω htop hleft harea
  have evK := Metric.tendsto_nhds.1 hKlim (ρ / 2) (by positivity)
  have evω := Metric.tendsto_nhds.1 hωlim α₀ hα₀
  obtain ⟨n, hnK, hnω⟩ := (evK.and evω).exists
  rw [Function.comp_apply] at hnK hnω
  have hclose := compactShape_euclideanClose (K (σ n)) (gerverCompactShape hP hbox)
  have hclose' : EuclideanClose ρ (normalizedSofa P (S (σ n))) (gerverSofa P) :=
    hclose.mono (by linarith)
  have hang : π / 2 - ω (σ n) < α₀ := by
    rw [Real.dist_eq] at hnω
    have he := (abs_lt.mp hnω).1
    linarith
  exact hbad (σ n) ⟨hclose', hang⟩

end MovingSofaStability
