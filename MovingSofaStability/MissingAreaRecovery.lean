module

public import MovingSofaStability.CapShape
public import MovingSofaStability.TerminalBookkeeping

/-!
# Recovering a nonconvex set from an erosion and a missing-area bound

The geometric hypothesis is an explicit uniform interior-ball condition on the
reference set, not an assumed stability theorem. An inscribed square provides
the area lower bound, so no Euclidean disk-volume conversion for the ambient
product space is required.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality

namespace MovingSofaStability

def euclideanBall (p : Point) (r : ℝ) : Set Point := {q | euclideanDist p q ≤ r}

/-- A reference set has a ball at every point and every sufficiently small scale. -/
def HasInteriorBalls (G : Set Point) (κ r₀ : ℝ) : Prop :=
  ∀ p ∈ G, ∀ ρ : ℝ, 0 < ρ → ρ ≤ r₀ →
    ∃ z, euclideanBall z (κ * ρ) ⊆ G ∩ euclideanBall p ρ

/-- Square of side length a centered at z. -/
def centeredSquare (z : Point) (a : ℝ) : Set Point :=
  Icc (z.1 - a / 2) (z.1 + a / 2) ×ˢ Icc (z.2 - a / 2) (z.2 + a / 2)

theorem area_centeredSquare (z : Point) {a : ℝ} (ha : 0 ≤ a) :
    area (centeredSquare z a) = a ^ 2 := by
  have hm : volume (centeredSquare z a) = ENNReal.ofReal a * ENNReal.ofReal a := by
    simp only [centeredSquare, Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_Icc]
    congr 1 <;> congr 1 <;> ring
  unfold area
  rw [hm, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha]
  ring

theorem centeredSquare_subset_ball (z : Point) {a : ℝ} :
    centeredSquare z a ⊆ euclideanBall z a := by
  rintro q ⟨hx, hy⟩
  have hx' : |z.1 - q.1| ≤ a / 2 := abs_le.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hy' : |z.2 - q.2| ≤ a / 2 := abs_le.2 ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hn : ‖z - q‖ ≤ a / 2 := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le hx' hy'
  change norm2 (z - q) ≤ a
  have h := norm2_le_two_product_norm (z - q)
  linarith

/-- Shrinking an interior ball by r leaves it inside the r-erosion. -/
theorem ball_subset_erosion {G : Set Point} {z : Point} {a r R : ℝ}
    (hball : euclideanBall z R ⊆ G) (har : a + r ≤ R) :
    euclideanBall z a ⊆ euclideanErosion r G := by
  intro q hq p hp
  apply hball
  exact (euclideanDist_triangle z q p).trans ((add_le_add hq hp).trans har)

/-- At a fixed scale, a missing region smaller than an inscribed square cannot
remove every nearby point of the target. Neither G nor S is assumed convex. -/
theorem directedClose_of_missing_area {G U S : Set Point} {κ r₀ r ρ η : ℝ}
    (hκ : 0 < κ) (hρ : 0 < ρ) (hρ₀ : ρ ≤ r₀)
    (hballs : HasInteriorBalls G κ r₀)
    (herosion : euclideanErosion r G ⊆ U)
    (hr : r ≤ κ * ρ / 2)
    (hUf : volume U ≠ ⊤) (hmissing : area (U \ S) ≤ η)
    (hsmall : η < (κ * ρ / 2) ^ 2) : DirectedClose ρ G S := by
  intro p hp
  by_contra hnone
  obtain ⟨z, hz⟩ := hballs p hp ρ hρ hρ₀
  let a := κ * ρ / 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have halarge : a ≤ κ * ρ := by dsimp [a]; nlinarith
  have hsmallball : euclideanBall z a ⊆ euclideanErosion r G :=
    ball_subset_erosion (fun q hq => (hz hq).1) (by dsimp [a] at *; linarith)
  have hsq : centeredSquare z a ⊆ U \ S := by
    intro q hq
    have hqball := centeredSquare_subset_ball z hq
    have hqG := hz (hqball.trans halarge)
    refine ⟨herosion (hsmallball hqball), ?_⟩
    intro hqS
    exact hnone ⟨q, hqS, hqG.2⟩
  have harea := area_mono_of_finite hsq (volume_ne_top_of_subset sdiff_subset hUf)
  rw [area_centeredSquare z ha] at harea
  have ha2 : a ^ 2 ≤ η := harea.trans hmissing
  exact (not_lt_of_ge ha2) hsmall

/-- A square-root scale suffices when the erosion radius is already O(sqrt ε).
The coefficient is not optimized and is independent of the smaller set S. -/
theorem directedClose_sqrt_of_missing_area {G U S : Set Point} {κ r₀ r A ε : ℝ}
    (hκ : 0 < κ) (hA : 0 ≤ A) (hε : 0 < ε)
    (hballs : HasInteriorBalls G κ r₀)
    (herosion : euclideanErosion r G ⊆ U)
    (hr : r ≤ A * sqrt ε)
    (hscale : (4 * (A + 1) / κ) * sqrt ε ≤ r₀)
    (hUf : volume U ≠ ⊤) (hmissing : area (U \ S) ≤ 2 * ε) :
    DirectedClose ((4 * (A + 1) / κ) * sqrt ε) G S := by
  let ρ := (4 * (A + 1) / κ) * sqrt ε
  have hs : 0 < sqrt ε := sqrt_pos.2 hε
  have hs2 : sqrt ε ^ 2 = ε := sq_sqrt hε.le
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have he : κ * ρ / 2 = 2 * (A + 1) * sqrt ε := by
    dsimp [ρ]
    field_simp [hκ.ne']
    ring
  apply directedClose_of_missing_area hκ hρ hscale hballs herosion
  · rw [he]
    nlinarith
  · exact hUf
  · exact hmissing
  · rw [he]
    have hAl : 1 ≤ (A + 1) ^ 2 := by nlinarith
    have hprod := mul_le_mul_of_nonneg_right hAl hε.le
    nlinarith [sq_nonneg (A + 1), mul_pow (2 * (A + 1)) (sqrt ε) 2]

/-- The cap erosion lemma can be inserted without a geometric regularity assumption on K. -/
theorem reference_to_sofa_recovery {K₀ K S : Set Point} {δ κ r₀ A ε : ℝ}
    (h₀ : IsCap K₀ (π / 2)) (hK : IsCap K (π / 2))
    (hδ : 0 ≤ δ) (hclose : UpperSupportClose δ K K₀)
    (hκ : 0 < κ) (hA : 0 ≤ A) (hε : 0 < ε)
    (hballs : HasInteriorBalls (capShape K₀) κ r₀)
    (hδbound : 2 * δ ≤ A * sqrt ε)
    (hscale : (4 * (A + 1) / κ) * sqrt ε ≤ r₀)
    (hUf : volume (capShape K) ≠ ⊤)
    (hmissing : area (capShape K \ S) ≤ 2 * ε) :
    DirectedClose ((4 * (A + 1) / κ) * sqrt ε) (capShape K₀) S :=
  directedClose_sqrt_of_missing_area hκ hA hε hballs
    (reference_erosion_subset hδ h₀ hK hclose) hδbound hscale hUf hmissing

end MovingSofaStability
