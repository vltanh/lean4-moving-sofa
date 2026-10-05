module

public import MovingSofaStability.ResidualPropagation

/-!
# Four-arc coercivity with an explicit non-sharp constant

Uncompiled proof source. This proves a complete analytic estimate with constant
80. Unlike the separate sharp Green-norm formulas, it needs neither Fubini nor
an unproved kernel-integral identification. The hypotheses describe continuity,
right derivatives and integrability, not a stability estimate in disguise.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory

namespace MovingSofaStability

structure FourResidualData (φ : ℝ) (f df : ℝ → ℝ) : Prop where
  continuous : Continuous f
  rightDeriv : ∀ t ∈ Ioo (0 : ℝ) π, HasDerivWithinAt f (df t) (Ioi t) t
  top_zero : f (π / 2) = 0
  left_zero : f π = 0
  first : IntervalIntegrable (tangentResidual (π / 2) f df) volume 0 φ
  middle : IntervalIntegrable (cornerResidual f df) volume φ (π / 2 - φ)
  third : IntervalIntegrable (tangentResidual (π - φ) f df) volume (π / 2 - φ) (π / 2)
  last : IntervalIntegrable (tangentResidual π f df) volume (π / 2) π
  first_sq : IntervalIntegrable (fun t => tangentResidual (π / 2) f df t ^ 2) volume 0 φ
  middle_sq : IntervalIntegrable (fun t => cornerResidual f df t ^ 2) volume φ (π / 2 - φ)
  third_sq : IntervalIntegrable (fun t => tangentResidual (π - φ) f df t ^ 2)
    volume (π / 2 - φ) (π / 2)
  last_sq : IntervalIntegrable (fun t => tangentResidual π f df t ^ 2) volume (π / 2) π

def fourResidualMass (φ : ℝ) (f df : ℝ → ℝ) : ℝ :=
  arcMass 0 φ (tangentResidual (π / 2) f df) +
  arcMass φ (π / 2 - φ) (cornerResidual f df) +
  arcMass (π / 2 - φ) (π / 2) (tangentResidual (π - φ) f df) +
  arcMass (π / 2) π (tangentResidual π f df)

def fourResidualEnergy (φ : ℝ) (f df : ℝ → ℝ) : ℝ :=
  (arcSquare 0 φ (tangentResidual (π / 2) f df) +
   arcSquare φ (π / 2 - φ) (cornerResidual f df) +
   arcSquare (π / 2 - φ) (π / 2) (tangentResidual (π - φ) f df) +
   arcSquare (π / 2) π (tangentResidual π f df)) / 2

/-- The short first and third arcs have no small denominator. -/
theorem cos_ge_half_of_small {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ht : t ∈ Icc 0 φ) : (1 / 2 : ℝ) ≤ cos t := by
  have hφ1 : φ < 1 := by linarith [hφ.2, pi_lt_four]
  have h := one_sub_sq_div_two_le_cos (x := t)
  nlinarith [ht.1, ht.2]

theorem fourResidualEnergy_nonneg {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (f df : ℝ → ℝ) : 0 ≤ fourResidualEnergy φ f df := by
  have hpi := pi_pos
  have h₁ := arcSquare_nonneg hφ.1.le (tangentResidual (π / 2) f df)
  have h₂ := arcSquare_nonneg (by linarith [hφ.2] : φ ≤ π / 2 - φ) (cornerResidual f df)
  have h₃ := arcSquare_nonneg (by linarith [hφ.1] : π / 2 - φ ≤ π / 2)
    (tangentResidual (π - φ) f df)
  have h₄ := arcSquare_nonneg (by linarith : π / 2 ≤ π) (tangentResidual π f df)
  unfold fourResidualEnergy
  positivity

/-- First-moment propagation from the pinned endpoints over all four arcs. -/
theorem four_arc_mass_bound {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {f df : ℝ → ℝ} (h : FourResidualData φ f df) :
    ∀ t ∈ Icc 0 π, |f t| ≤ 20 * fourResidualMass φ f df := by
  have hpi := pi_pos
  have hp4 := pi_lt_four
  let b : ℝ := π / 2 - φ
  let T : ℝ := π - φ
  let m₁ := arcMass 0 φ (tangentResidual (π / 2) f df)
  let m₂ := arcMass φ b (cornerResidual f df)
  let m₃ := arcMass b (π / 2) (tangentResidual T f df)
  let m₄ := arcMass (π / 2) π (tangentResidual π f df)
  let M := m₁ + m₂ + m₃ + m₄
  have hφb : φ < b := by dsimp [b]; linarith [hφ.2]
  have hb0 : 0 < b := hφ.1.trans hφb
  have hbtop : b < π / 2 := by dsimp [b]; linarith [hφ.1]
  have hTlast : T ∈ Icc (π / 2) π := by dsimp [T]; constructor <;> linarith [hφ.1, hφ.2]
  have hm₁ : 0 ≤ m₁ := arcMass_nonneg hφ.1.le _
  have hm₂ : 0 ≤ m₂ := arcMass_nonneg hφb.le _
  have hm₃ : 0 ≤ m₃ := arcMass_nonneg hbtop.le _
  have hm₄ : 0 ≤ m₄ := arcMass_nonneg (by linarith) _
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have h₁M : m₁ ≤ M := by dsimp [M]; linarith
  have h₂M : m₂ ≤ M := by dsimp [M]; linarith
  have h₃M : m₃ ≤ M := by dsimp [M]; linarith
  have h₄M : m₄ ≤ M := by dsimp [M]; linarith
  have last_bound : ∀ t ∈ Icc (π / 2) π, |f t| ≤ m₄ := by
    intro t ht
    exact last_arc_mass_bound h.continuous.continuousOn
      (fun u hu => h.rightDeriv u ⟨by linarith [hu.1], hu.2⟩)
      h.top_zero h.left_zero h.last ht
  have third_bound : ∀ t ∈ Icc b (π / 2), |f t| ≤ 5 * M := by
    intro t ht
    have hden : ∀ u ∈ Icc t (π / 2), (1 / 2 : ℝ) ≤ sin (T - u) := by
      intro u hu
      rw [show T - u = π / 2 - (u - b) by dsimp [T, b]; ring, sin_pi_div_two_sub]
      exact cos_ge_half_of_small hφ ⟨by linarith [ht.1, hu.1], by dsimp [b]; linarith [hu.2]⟩
    have hr := intervalIntegrable_subinterval h.third ht.1 ht.2 le_rfl
    have he := tangent_regular_arc_bound ht.2 h.continuous.continuousOn
      (fun u hu => h.rightDeriv u ⟨by linarith [hu.1, ht.1], by linarith [hu.2]⟩) hden hr
    have hm := arcMass_mono ht.1 ht.2 le_rfl h.third
    have hfT := last_bound T hTlast
    rw [h.top_zero, abs_zero] at he
    change |f t| ≤ 2 * 0 + 3 * |f T| +
      2 * arcMass t (π / 2) (tangentResidual T f df) at he
    linarith
  have middle_bound : ∀ t ∈ Icc φ b, |f t| ≤ 8 * M := by
    intro t ht
    have hr := intervalIntegrable_subinterval h.middle ht.1 ht.2 le_rfl
    have hshift : IntervalIntegrable (fun u => f (u + π / 2)) volume t b :=
      (h.continuous.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
    have hdf : IntervalIntegrable df volume t b := by
      have hi := hshift.sub hr
      have he : (fun u => f (u + π / 2) - cornerResidual f df u) = df := by
        funext u
        simp [cornerResidual]
      rwa [he] at hi
    have he := corner_reconstruct ht.2 h.continuous.continuousOn
      (fun u hu => h.rightDeriv u ⟨by linarith [hu.1, ht.1, hφ.1],
        by linarith [hu.2, hbtop]⟩) hdf hshift
    have hshift_bound : |∫ u in t..b, f (u + π / 2)| ≤ (b - t) * m₄ := by
      apply abs_integral_le_length_mul ht.2
      intro u hu
      exact last_bound (u + π / 2)
        ⟨by linarith [hu.1, ht.1, hφ.1], by linarith [hu.2, hbtop]⟩
    have hm := arcMass_mono ht.1 ht.2 le_rfl h.middle
    have hri : |∫ u in t..b, cornerResidual f df u| ≤ arcMass t b (cornerResidual f df) :=
      intervalIntegral.abs_integral_le_integral_abs ht.2
    have hfb := third_bound b ⟨le_rfl, hbtop.le⟩
    have hlen : b - t ≤ 2 := by dsimp [b]; linarith [ht.1, hφ.1]
    have hlenprod := mul_le_mul_of_nonneg_right hlen hm₄
    have htri := abs_add_le (f b - ∫ u in t..b, f (u + π / 2))
      (∫ u in t..b, cornerResidual f df u)
    have hsub := abs_sub (f b) (∫ u in t..b, f (u + π / 2))
    rw [he]
    linarith
  have first_bound : ∀ t ∈ Icc 0 φ, |f t| ≤ 18 * M := by
    intro t ht
    have hden : ∀ u ∈ Icc t φ, (1 / 2 : ℝ) ≤ sin (π / 2 - u) := by
      intro u hu
      rw [sin_pi_div_two_sub]
      exact cos_ge_half_of_small hφ ⟨ht.1.trans hu.1, hu.2⟩
    have hr := intervalIntegrable_subinterval h.first ht.1 ht.2 le_rfl
    have he := tangent_regular_arc_bound ht.2 h.continuous.continuousOn
      (fun u hu => h.rightDeriv u ⟨by linarith [hu.1, ht.1],
        by linarith [hu.2, hφ.2]⟩) hden hr
    have hm := arcMass_mono ht.1 ht.2 le_rfl h.first
    have hfφ := middle_bound φ ⟨le_rfl, hφb.le⟩
    rw [h.top_zero, abs_zero] at he
    linarith
  intro t ht
  change |f t| ≤ 20 * M
  by_cases ht₁ : t ≤ φ
  · have := first_bound t ⟨ht.1, ht₁⟩
    linarith
  by_cases ht₂ : t ≤ b
  · have := middle_bound t ⟨(not_le.mp ht₁).le, ht₂⟩
    linarith
  by_cases ht₃ : t ≤ π / 2
  · have := third_bound t ⟨(not_le.mp ht₂).le, ht₃⟩
    linarith
  · have := last_bound t ⟨(not_le.mp ht₃).le, ht.2⟩
    linarith

/-- The total first moment is controlled by the actual residual square integrals. -/
theorem fourResidualMass_le {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {f df : ℝ → ℝ} (h : FourResidualData φ f df) :
    fourResidualMass φ f df ≤ 4 * sqrt (fourResidualEnergy φ f df) := by
  have hp := pi_pos
  have hp4 := pi_lt_four
  have h₁ := arcMass_sq_le hφ.1.le h.first h.first_sq
  have h₂ := arcMass_sq_le (by linarith [hφ.2]) h.middle h.middle_sq
  have h₃ := arcMass_sq_le (by linarith [hφ.1]) h.third h.third_sq
  have h₄ := arcMass_sq_le (by linarith) h.last h.last_sq
  have q₁ := arcSquare_nonneg hφ.1.le (tangentResidual (π / 2) f df)
  have q₂ := arcSquare_nonneg (by linarith [hφ.2] : φ ≤ π / 2 - φ) (cornerResidual f df)
  have q₃ := arcSquare_nonneg (by linarith [hφ.1] : π / 2 - φ ≤ π / 2)
    (tangentResidual (π - φ) f df)
  have q₄ := arcSquare_nonneg (by linarith : π / 2 ≤ π) (tangentResidual π f df)
  apply four_masses_le_four_sqrt
    (q₁ := arcSquare 0 φ (tangentResidual (π / 2) f df))
    (q₂ := arcSquare φ (π / 2 - φ) (cornerResidual f df))
    (q₃ := arcSquare (π / 2 - φ) (π / 2) (tangentResidual (π - φ) f df))
    (q₄ := arcSquare (π / 2) π (tangentResidual π f df))
    (arcMass_nonneg hφ.1.le _) (arcMass_nonneg (by linarith [hφ.2]) _)
    (arcMass_nonneg (by linarith [hφ.1]) _) (arcMass_nonneg (by linarith) _)
    (fourResidualEnergy_nonneg hφ f df)
  · nlinarith [hφ.1, hφ.2]
  · nlinarith [hφ.1, hφ.2]
  · nlinarith [hφ.1, hφ.2]
  · nlinarith
  · unfold fourResidualEnergy
    ring

/-- Complete non-sharp coercivity; no squared-estimate hypothesis is assumed. -/
theorem four_arc_coercivity {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {f df : ℝ → ℝ} (h : FourResidualData φ f df) {t : ℝ} (ht : t ∈ Icc 0 π) :
    |f t| ≤ 80 * sqrt (fourResidualEnergy φ f df) := by
  have hm := four_arc_mass_bound hφ h t ht
  have he := fourResidualMass_le hφ h
  linarith

end MovingSofaStability
