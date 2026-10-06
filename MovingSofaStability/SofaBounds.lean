module

public import MovingSofaStability.CompactSetLimits

/-!
# A compact containing rectangle for the original sofa sets

Uncompiled proof source. Connectedness bounds a supporting inner corner and
the pi/4 hallway bounds horizontal span. No balancedness is assumed.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- Coordinate proof of rotation linearity used in the canonical limit motion. -/
theorem rot_sub_vec (t : ℝ) (p q : Point) : rot t (p - q) = rot t p - rot t q := by
  ext <;> simp only [rot, Prod.fst_sub, Prod.snd_sub] <;> ring

theorem connected_corner_height {S : Set Point} (hS : IsCompact S) (hne : S.Nonempty)
    (hconn : IsConnected S) (hstrip : S ⊆ hStrip) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (π / 2))
    (hslack : ∀ p ∈ S, 0 ≤ max (innerSlackU S t p) (innerSlackV S t p)) :
    (innerCorner S t).2 ≤ 1 := by
  sorry

theorem moving_horizontal_span_le_six {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) (hω : π / 4 ≤ ω)
    (htop : supp S (π / 2) = 1) {p q : Point} (hp : p ∈ S) (hq : q ∈ S) :
    p.1 - q.1 ≤ 6 := by
  have hcpt := ms_isCompact_of_isMovingSofaWithAngle hS
  have hstrip := moving_strip_of_top ⟨ω, hS⟩ htop
  have hheight := connected_corner_height hcpt hS.2.1.nonempty hS.2.1 hstrip
    (t := π / 4) ⟨by positivity, by linarith [pi_pos]⟩
    (fun p hp => moving_hallway_slacks hS hp ⟨by positivity, hω⟩)
  have hu := dot_le_supp hcpt hp (π / 4)
  have hv := dot_le_supp hcpt hq (π / 4 + π / 2)
  rw [uvec_add_pi_div_two] at hv
  rw [proposition2_2_2_innerCorner] at hheight
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, uvec_snd, vvec_snd,
    sin_pi_div_four, cos_pi_div_four] at hheight
  simp only [dot, uvec, vvec, sin_pi_div_four, cos_pi_div_four] at hu hv
  have hr0 := sqrt_nonneg (2 : ℝ)
  have hr2 : sqrt (2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num)
  have hrlo : 1 ≤ sqrt (2 : ℝ) := by nlinarith
  have hrhi : sqrt (2 : ℝ) ≤ 2 := by nlinarith
  have hsum := add_le_add hu hv
  have hmul := mul_le_mul_of_nonneg_right hsum hr0
  have hpy := (hstrip hp).1
  have hqy := (hstrip hq).1
  have hy := mul_nonneg (add_nonneg hpy hqy) hr0
  have hp2 : p.1 * (sqrt (2 : ℝ)) ^ 2 = 2 * p.1 := by rw [hr2]; ring
  have hq2 : q.1 * (sqrt (2 : ℝ)) ^ 2 = 2 * q.1 := by rw [hr2]; ring
  have hpy2 : p.2 * (sqrt (2 : ℝ)) ^ 2 = 2 * p.2 := by rw [hr2]; ring
  have hqy2 : q.2 * (sqrt (2 : ℝ)) ^ 2 = 2 * q.2 := by rw [hr2]; ring
  nlinarith

def normalizedBox (P : GerverParams) : Set Point :=
  Icc (-supp (gerverSofa P) π) (-supp (gerverSofa P) π + 6) ×ˢ Icc (0 : ℝ) 1

theorem normalizedBox_compact (P : GerverParams) : IsCompact (normalizedBox P) :=
  isCompact_Icc.prod isCompact_Icc

theorem pinned_sofa_subset_box {P : GerverParams} {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) (hω : π / 4 ≤ ω)
    (htop : supp S (π / 2) = 1) (hleft : supp S π = supp (gerverSofa P) π) :
    S ⊆ normalizedBox P := by
  have hcpt := ms_isCompact_of_isMovingSofaWithAngle hS
  obtain ⟨q, hq, he⟩ := exists_dot_eq_supp hcpt hS.2.1.nonempty π
  simp only [dot, uvec_pi] at he
  intro p hp
  have hl := dot_le_supp hcpt hp π
  simp only [dot, uvec_pi, hleft] at hl
  have hw := moving_horizontal_span_le_six hS hω htop hp hq
  rw [hleft] at he
  exact ⟨⟨by linarith, by linarith⟩, moving_strip_of_top ⟨ω, hS⟩ htop hp⟩

theorem quarter_le_reduced_angle : π / 4 ≤ arccos (5 / 11 : ℝ) := by
  have hs0 := sqrt_nonneg (2 : ℝ)
  have hs2 := sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hcos : (5 / 11 : ℝ) ≤ cos (π / 4) := by rw [cos_pi_div_four]; nlinarith
  have he := arccos_le_arccos hcos
  rwa [arccos_cos (by positivity : (0 : ℝ) ≤ π / 4) (by linarith [pi_pos])] at he

theorem normalizedSofa_subset_box {P : GerverParams} {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) (hω : ω ∈ Icc (arccos (5 / 11)) (π / 2)) :
    normalizedSofa P S ⊆ normalizedBox P :=
  pinned_sofa_subset_box (normalizedSofa_movingWithAngle P hS)
    (quarter_le_reduced_angle.trans hω.1)
    (normalizedSofa_top P (ms_isCompact_of_isMovingSofaWithAngle hS) hS.2.1.nonempty)
    (normalizedSofa_left P (ms_isCompact_of_isMovingSofaWithAngle hS) hS.2.1.nonempty)

end MovingSofaStability
