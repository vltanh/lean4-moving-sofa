module

public import MovingSofaQuantitative.OuterDensity
public import MovingSofaQuantitative.ScalarTaylor

/-!
# A nondegenerate reference gap on the inactive auxiliary wall arc

Uncompiled proof source. The gap vanishes linearly at phi and quadratically at
c = pi/2-theta. Explicit phase formulas give a positive weighted lower bound
on the ENTIRE interval. Thus a perturbation with the same endpoint jets can
be absorbed uniformly, including arbitrarily close to either endpoint.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaStability MovingSofaOptimality.GerverParams

namespace MovingSofaQuantitative

private def gapPolynomial (x : ℝ) : ℝ :=
  93 / 1000 - (901 / 2000 - 1 / 4) * x + 451 / 6000 * x^2 +
    898 / 24000 * x^3 - 451 / 120000 * x^4 - 901 / 720000 * x^5

/-- Positive Bernstein coefficients certify the polynomial over its complete
rational interval, not only at the six coefficients or sampled abscissas. -/
private theorem gapPolynomial_lower {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (643 / 1000)) :
    (1 / 250 : ℝ) ≤ gapPolynomial x := by
  let z := x / (643 / 1000)
  have hz : z ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hx.1 (by norm_num)
    · exact (div_le_one (by norm_num)).mpr hx.2
  have hid : gapPolynomial x - 1 / 250 =
      (89 / 1000 : ℝ) * (1-z)^5 +
      5 * (632157 / 10000000 : ℝ) * z * (1-z)^4 +
      10 * (2432349499 / 60000000000 : ℝ) * z^2 * (1-z)^3 +
      10 * (2635810614443 / 120000000000000 : ℝ) * z^3 * (1-z)^2 +
      5 * (1671942791587983 / 200000000000000000 : ℝ) * z^4 * (1-z) +
      (232720325784783857 / 720000000000000000000 : ℝ) * z^5 := by
    dsimp [gapPolynomial, z]
    ring
  have hnonneg : 0 ≤ gapPolynomial x - 1 / 250 := by
    rw [hid]
    have hz0 := hz.1
    have h1z : 0 ≤ 1-z := sub_nonneg.mpr hz.2
    positivity
  linarith

/-- Phase 2: the nonnegative trigonometric remainder has an explicit linear
lower bound, with coarse rational boxes for the three scalar coefficients. -/
private theorem quadratic_phase_gap_lower {x u w a : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (643 / 1000))
    (hu : u ∈ Icc (898 / 1000 : ℝ) (901 / 1000))
    (hw : w ≤ -(451 / 1000 : ℝ)) (ha : (93 / 1000 : ℝ) ≤ a) :
    x / 250 ≤ a*x + u*(cos x-1) + w*(sin x-x) + x^2/4 := by
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hw0 : w ≤ 0 := by linarith
  have hcos := mul_le_mul_of_nonneg_left (cosPoly6_le_cos hx.1) hu0
  have hsin := mul_le_mul_of_nonpos_left (sin_le_sinPoly5 hx.1) hw0
  have h2 := mul_nonneg (sub_nonneg.mpr hu.2) (pow_nonneg hx.1 2)
  have h4 := mul_nonneg (sub_nonneg.mpr hu.1) (pow_nonneg hx.1 4)
  have h6 := mul_nonneg (sub_nonneg.mpr hu.2) (pow_nonneg hx.1 6)
  have hbase := mul_le_mul_of_nonneg_right ha hx.1
  have hp : 0 ≤ x^3/6-x^5/120 := by
    have hs := mul_self_le_mul_self hx.1 hx.2
    have hm := mul_nonneg (pow_nonneg hx.1 3) (show 0 ≤ 20-x^2 by nlinarith)
    nlinarith only [hm]
  have hw' := mul_le_mul_of_nonneg_right (show 451/1000 ≤ -w by linarith) hp
  have hpoly := mul_le_mul_of_nonneg_left (gapPolynomial_lower hx) hx.1
  unfold sinPoly5 cosPoly6 gapPolynomial at hcos hsin hpoly
  nlinarith only [hcos, hsin, h2, h4, h6, hbase, hw', hpoly]

/-- Phase 3: both the value and first derivative vanish at the right endpoint. -/
private theorem linear_phase_gap_lower {x a : ℝ} (hx : x ∈ Icc (0 : ℝ) (1/4))
    (ha : (1/4 : ℝ) ≤ a) : x^2/16 ≤ a*(1-cos x)+sin x-x := by
  have hcos := cos_le_cosPoly4 hx.1
  have hsin := sinPoly3_le_sin hx.1
  have h1 := mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr (cos_le_one x))
  have h2 := mul_nonneg (pow_nonneg hx.1 2) (sub_nonneg.mpr hx.2)
  have hs := mul_self_le_mul_self hx.1 hx.2
  have h4 := mul_nonneg (pow_nonneg hx.1 2) (show 0 ≤ 1/16-x^2 by nlinarith only [hs])
  unfold cosPoly4 sinPoly3 at hcos hsin
  nlinarith only [hcos, hsin, h1, h2, h4]

/-- The inner wall gap seen from the first point of Gerver's B contact arc. -/
def referenceRightGap (P : GerverParams) (t : ℝ) : ℝ :=
  dot (contactB P.path (π / 2 - P.θ) - P.path t) (uvec t)

private theorem rotated_projection (a t : ℝ) (p : Point) :
    dot (rot a p) (uvec t) = p.1*cos(t-a)+p.2*sin(t-a) := by
  simp only [dot, uvec, rot, cos_sub, sin_sub]
  ring

/-- The initial contact is the corner at phi, so the phase-2 shifts cancel. -/
theorem referenceRightGap_phase2 {P : GerverParams} (hP : P.IsSolution)
    {t : ℝ} (ht : t ∈ Icc P.φ P.θ) :
    referenceRightGap P t =
      (P.φ-2*P.b₁-1)*(t-P.φ) +
      (-P.φ^2/4+P.b₁*P.φ+P.b₂)*(cos(t-P.φ)-1) +
      (P.φ/2-P.b₁-1)*(sin(t-P.φ)-(t-P.φ)) + (t-P.φ)^2/4 := by
  have hO := gs_ord hP
  rw [referenceRightGap, gs_contactB_t₃ hP,
    gs_path_eq_phase hP (i := 1) (show gs_piece P 1 P.φ from ⟨le_rfl, hO.2.1.le⟩),
    gs_path_eq_phase hP (i := 1) (show gs_piece P 1 t from ht)]
  simp only [gs_phase, gs_ph2, gs_Phase.X, add_sub_add_right_eq_sub, dot_sub_left,
    rotated_projection, sub_self, cos_zero, sin_zero, mul_one, mul_zero, add_zero]
  ring

/-- At c the B contact and the phase-3 corner have exactly the required jet.
The identity has no rounded reference constants. -/
theorem referenceRightGap_phase3 {P : GerverParams} (hP : P.IsSolution)
    {t : ℝ} (ht : t ∈ Icc P.θ (π / 2-P.θ)) :
    referenceRightGap P t =
      (π/2-P.θ-P.c₁)*(1-cos(π/2-P.θ-t)) +
        sin(π/2-P.θ-t)-(π/2-P.θ-t) := by
  have hO := gs_ord hP
  rw [referenceRightGap,
    gs_contactB_eq hP (i := 2)
      (show gs_piece P 2 (π/2-P.θ) from ⟨hO.θ_lt.le, le_rfl⟩),
    gs_path_eq_phase hP (i := 2) (show gs_piece P 2 t from ht)]
  simp only [gs_phase, gs_ph3, gs_Phase.B, gs_Phase.X,
    add_sub_add_right_eq_sub, dot_sub_left, rotated_projection,
    sub_self, cos_zero, sin_zero, mul_one, mul_zero, add_zero]
  rw [show t-(π/2-P.θ) = -(π/2-P.θ-t) by ring, cos_neg, sin_neg]
  ring

/-- A weighted whole-interval margin at the inactive wall, including its two
vanishing endpoints. It replaces an unquantified appeal to strictness. -/
theorem referenceRightGap_lower {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t ∈ Icc P.φ (π/2-P.θ)) :
    (1/250 : ℝ)*(t-P.φ)*(π/2-P.θ-t)^2 ≤ referenceRightGap P t := by
  have hB := romik_bounds hP hbox
  have hO := gs_ord hP
  have hp := hbox.1
  have hb1 : P.b₁ ∈ Icc (-528/1000 : ℝ) (-527/1000) := by
    constructor <;> linarith [hB.b₁_mem.1, hB.b₁_mem.2]
  have hb2 : P.b₂ ∈ Icc (920/1000 : ℝ) (921/1000) := by
    constructor <;> linarith [hB.b₂_mem.1, hB.b₂_mem.2]
  have hθ : P.θ ∈ Icc (68/100 : ℝ) (682/1000) := by
    constructor <;> linarith [hB.θ_mem.1, hB.θ_mem.2]
  have hc1 : P.c₁ ≤ 627/1000 := by linarith [hB.c₁_mem.2]
  have hπl : (314/100 : ℝ) < π := (by norm_num : (314/100 : ℝ) < 3.14159265358979323846).trans pi_gt_d20
  have hπu : π < 22/7 := pi_lt_d20.trans (by norm_num)
  have hspan : π/2-P.θ-P.φ ≤ 1 := by linarith [hp.1, hθ.1]
  have hleft : 0 ≤ t-P.φ := sub_nonneg.mpr ht.1
  have hright : 0 ≤ π/2-P.θ-t := sub_nonneg.mpr ht.2
  by_cases htθ : t ≤ P.θ
  · rw [referenceRightGap_phase2 hP ⟨ht.1, htθ⟩]
    have hx : t-P.φ ∈ Icc (0 : ℝ) (643/1000) := ⟨hleft, by linarith [hp.1, hθ.2]⟩
    have hu : -P.φ^2/4+P.b₁*P.φ+P.b₂ ∈ Icc (898/1000 : ℝ) (901/1000) := by
      have hmullo := mul_le_mul_of_nonneg_right hb1.1 (show 0 ≤ P.φ by linarith [hp.1])
      have hmulhi := mul_le_mul_of_nonneg_right hb1.2 (show 0 ≤ P.φ by linarith [hp.1])
      have hs := mul_self_le_mul_self (show 0 ≤ P.φ by linarith [hp.1]) hp.2
      constructor <;> nlinarith [hp.1, hp.2, hb2.1, hb2.2, sq_nonneg P.φ]
    have hgap := quadratic_phase_gap_lower hx hu
      (show P.φ/2-P.b₁-1 ≤ -(451/1000 : ℝ) by linarith [hp.2, hb1.1])
      (show (93/1000 : ℝ) ≤ P.φ-2*P.b₁-1 by linarith [hp.1, hb1.2])
    have hsq : (π/2-P.θ-t)^2 ≤ 1 := by
      have hh : π/2-P.θ-t ≤ 1 := by linarith [ht.1]
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ (t-P.φ)/250 by positivity)
    nlinarith only [hgap, hm]
  · rw [referenceRightGap_phase3 hP ⟨(not_le.mp htθ).le, ht.2⟩]
    have hx : π/2-P.θ-t ∈ Icc (0 : ℝ) (1/4) :=
      ⟨hright, by linarith [hθ.1]⟩
    have hg := linear_phase_gap_lower hx
      (show (1/4 : ℝ) ≤ π/2-P.θ-P.c₁ by linarith [hθ.2])
    have hsmall : t-P.φ ≤ 1 := by linarith [ht.2]
    have hm := mul_nonneg (show 0 ≤ 1/16-(t-P.φ)/250 by linarith) (sq_nonneg (π/2-P.θ-t))
    nlinarith only [hg, hm]

end MovingSofaQuantitative
