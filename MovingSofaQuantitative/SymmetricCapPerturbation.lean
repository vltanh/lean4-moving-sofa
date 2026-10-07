module

public import MovingSofaQuantitative.OuterDensity
public import MovingSofaQuantitative.TwoSidedPieces

/-!
# Small support perturbations are actual caps

Uncompiled proof source. The hypotheses concern scalar functions and their
one-sided derivatives, not the existence of a convex body. Positively turning
arcs construct that body. The left derivative on the endpoint normal gap is
kept distinct from the right derivative on the smoothing interval.
-/

@[expose] public section
noncomputable section

open Real Set Filter Topology MeasureTheory
open MovingSofaOptimality MovingSofaStability MovingSofaOptimality.GerverParams

namespace MovingSofaQuantitative

/-- Analytic data on the first half of a symmetric perturbation. Outside
[0,pi/2], values serve only to give ordinary derivative statements. -/
structure HalfCapProfile (φ : ℝ) where
  value : ℝ → ℝ
  first : ℝ → ℝ
  secondR : ℝ → ℝ
  secondL : ℝ → ℝ
  curvatureBound : ℝ
  bound_nonneg : 0 ≤ curvatureBound
  derivative : ∀ t, HasDerivAt value (first t) t
  first_continuous : Continuous first
  second_right : ∀ t, HasDerivWithinAt first (secondR t) (Ici t) t
  second_left : ∀ t, HasDerivWithinAt first (secondL t) (Iic t) t
  top_zero : value (π / 2) = 0
  endpoint_up : 0 ≤ first 0
  gap_right : ∀ t ∈ Ico (0 : ℝ) φ, secondR t + value t = 0
  gap_left : ∀ t ∈ Icc (0 : ℝ) φ, secondL t + value t = 0
  central_right : ∀ t ∈ Icc φ (π / 2), |secondR t + value t| ≤ curvatureBound
  central_left : ∀ t ∈ Icc φ (π / 2), |secondL t + value t| ≤ curvatureBound

namespace HalfCapProfile

variable {φ : ℝ} (F : HalfCapProfile φ)

theorem continuous_value : Continuous F.value :=
  continuous_iff_continuousAt.mpr fun t => (F.derivative t).continuousAt

def symmetricValue (t : ℝ) : ℝ :=
  if t ≤ π / 2 then F.value t else F.value (π - t)

def rightOffset (t : ℝ) : Point := F.value t • uvec t + F.first t • vvec t

def leftOffset (s : ℝ) : Point :=
  F.value (π / 2 - s) • vvec s + F.first (π / 2 - s) • uvec s

theorem rightOffset_continuous : Continuous F.rightOffset :=
  (F.continuous_value.smul continuous_uvec).add (F.first_continuous.smul continuous_vvec)

theorem leftOffset_continuous : Continuous F.leftOffset := by
  unfold leftOffset
  exact ((F.continuous_value.comp (continuous_const.sub continuous_id)).smul continuous_vvec).add
    ((F.first_continuous.comp (continuous_const.sub continuous_id)).smul continuous_uvec)

theorem rightOffset_derivative (t : ℝ) :
    HasDerivWithinAt F.rightOffset ((F.secondR t + F.value t) • vvec t) (Ici t) t := by
  have h1 := (F.derivative t).hasDerivWithinAt.smul (hasDerivAt_uvec t).hasDerivWithinAt
  have h2 := (F.second_right t).smul (hasDerivAt_vvec t).hasDerivWithinAt
  convert h1.add h2 using 1
  · rfl
  · simp only [smul_neg, add_smul]
    abel

theorem leftOffset_derivative (s : ℝ) :
    HasDerivWithinAt F.leftOffset (-(F.secondL (π / 2 - s) + F.value (π / 2 - s)) • uvec s)
      (Ici s) s := by
  have harg := ((hasDerivAt_id s).const_sub (π / 2)).hasDerivWithinAt (s := Ici s)
  have hmap : MapsTo (fun t : ℝ => π / 2 - t) (Ici s) (Iic (π / 2 - s)) := by
    intro t ht
    change π / 2 - t ≤ π / 2 - s
    linarith [ht]
  have hf := (F.derivative (π / 2 - s)).comp_hasDerivWithinAt s harg
  have hd := (F.second_left (π / 2 - s)).comp s harg hmap
  have h1 := hf.smul (hasDerivAt_vvec s).hasDerivWithinAt
  have h2 := hd.smul (hasDerivAt_uvec s).hasDerivWithinAt
  convert h1.add h2 using 1
  · rfl
  · simp only [mul_neg_one, neg_smul, smul_neg, neg_add_rev, add_smul]
    abel

/-- A single explicit amplitude controls densities and the top-edge reserve. -/
def safeAmplitude : ℝ := 1 / (16 * (1 + F.curvatureBound + |F.first (π / 2)|))

theorem safeAmplitude_pos : 0 < F.safeAmplitude := by
  unfold safeAmplitude
  positivity

theorem amplitude_curvature {τ : ℝ} (hτ : 0 ≤ τ) (hsmall : τ ≤ F.safeAmplitude) :
    τ * F.curvatureBound ≤ 1 / 16 := by
  have hden : 0 < 16 * (1 + F.curvatureBound + |F.first (π / 2)|) := by positivity
  have hτ' := (le_div_iff₀ hden).mp hsmall
  have hprod := mul_nonneg hτ (abs_nonneg (F.first (π / 2)))
  nlinarith [hτ', hprod]

theorem amplitude_top {τ : ℝ} (hτ : 0 ≤ τ) (hsmall : τ ≤ F.safeAmplitude) :
    2 * τ * |F.first (π / 2)| ≤ 1 / 8 := by
  have hden : 0 < 16 * (1 + F.curvatureBound + |F.first (π / 2)|) := by positivity
  have hτ' := (le_div_iff₀ hden).mp hsmall
  have hprod := mul_nonneg hτ F.bound_nonneg
  nlinarith [hτ', hprod]

end HalfCapProfile

/-- Constructing the two real outer curves requires no symmetry assumption
on a competing cap: this is a deliberately chosen symmetric trial family. -/
def perturbedTurningCap {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (F : HalfCapProfile P.φ) (τ : ℝ) (hτ : 0 ≤ τ) (hsmall : τ ≤ F.safeAmplitude) : TurningCapData where
  rightArc t := contactA P.path t + τ • F.rightOffset t
  leftArc t := contactC P.path t + τ • F.leftOffset t
  rightDensity t := outerDensityR P t + τ * (F.secondR t + F.value t)
  leftDensity t := outerDensityL P t + τ * (F.secondL (π / 2 - t) + F.value (π / 2 - t))
  right_continuous := ((gs_continuous_contactA hP).add (F.rightOffset_continuous.const_smul τ)).continuousOn
  left_continuous := ((gs_continuous_contactC hP).add (F.leftOffset_continuous.const_smul τ)).continuousOn
  right_derivative t ht := by
    have hr := gs_hasDerivWithinAt_contactA hP (gs_rpiece_ridx t)
    have hf := (F.rightOffset_derivative t).const_smul τ
    convert hr.add hf using 1
    · rfl
    · simp only [outerDensityR, add_smul, mul_smul]
  left_derivative t ht := by
    have hr := gs_hasDerivWithinAt_contactC hP (gs_rpiece_ridx t)
    have hf := (F.leftOffset_derivative t).const_smul τ
    convert hr.add hf using 1
    · rfl
    · simp only [outerDensityL, neg_add_rev, add_smul, neg_smul, smul_neg, mul_smul]
      abel
  right_nonneg t ht := by
    have hm := outer_density_margins hP hbox ⟨ht.1, ht.2.le⟩
    by_cases hg : t < P.φ
    · rw [F.gap_right t ⟨ht.1, hg⟩, mul_zero, add_zero]
      exact hm.1.1
    · have hb := F.central_right t ⟨not_lt.mp hg, ht.2.le⟩
      have hl := (abs_le.mp hb).1
      have hmul := mul_le_mul_of_nonneg_left hl hτ
      have ha := F.amplitude_curvature hτ hsmall
      linarith [hm.2.2.1 (not_lt.mp hg)]
  left_nonneg t ht := by
    have hm := outer_density_margins hP hbox ⟨ht.1, ht.2.le⟩
    by_cases hg : P.φ < π / 2 - t
    · have hb := F.central_left (π / 2 - t) ⟨hg.le, by linarith [ht.1]⟩
      have hmul := mul_le_mul_of_nonneg_left (abs_le.mp hb).1 hτ
      have ha := F.amplitude_curvature hτ hsmall
      linarith [hm.2.2.2 (by linarith : t < π / 2 - P.φ)]
    · rw [F.gap_left (π / 2 - t) ⟨by linarith [ht.2], not_lt.mp hg⟩,
        mul_zero, add_zero]
      exact hm.2.1.1
  right_top := by
    simp [HalfCapProfile.rightOffset, gs_A_pi_div_two hP, F.top_zero, uvec, vvec]
  left_top := by
    simp [HalfCapProfile.leftOffset, gs_C_zero hP, F.top_zero, uvec, vvec]
  top_order := by
    have hlen := outer_top_length hP hbox
    have ha := F.amplitude_top hτ hsmall
    have hprod := mul_le_mul_of_nonneg_left (le_abs_self (F.first (π / 2))) hτ
    simp only [HalfCapProfile.rightOffset, HalfCapProfile.leftOffset,
      gs_A_pi_div_two hP, gs_C_zero hP, sub_zero, F.top_zero,
      Prod.fst_add, Prod.smul_fst, smul_eq_mul, uvec, vvec,
      sin_zero, cos_zero, sin_pi_div_two, cos_pi_div_two, neg_zero,
      zero_mul, mul_zero, mul_one, mul_neg_one, add_zero, zero_add] at ⊢
    linarith
  right_floor := by
    simpa [HalfCapProfile.rightOffset, gs_A_zero hP, uvec, vvec] using mul_nonneg hτ F.endpoint_up
  left_floor := by
    simpa [HalfCapProfile.leftOffset, gs_C_pi_div_two hP, uvec, vvec] using mul_nonneg hτ F.endpoint_up

/-- The trial set is a genuine normalized right-angle cap. -/
def perturbedCap {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (F : HalfCapProfile P.φ) (τ : ℝ) (hτ : 0 ≤ τ) (hsmall : τ ≤ F.safeAmplitude) : ConvexBodySet :=
  ⟨(perturbedTurningCap hP hbox F τ hτ hsmall).body,
    (perturbedTurningCap hP hbox F τ hτ hsmall).body_convexBody⟩

theorem perturbedCap_isCap {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (F : HalfCapProfile P.φ) (τ : ℝ) (hτ : 0 ≤ τ) (hsmall : τ ≤ F.safeAmplitude) :
    IsCap (perturbedCap hP hbox F τ hτ hsmall).1 (π / 2) :=
  (perturbedTurningCap hP hbox F τ hτ hsmall).body_isCap

/-- Exact support, not just a first-order asymptotic expansion. -/
theorem perturbedCap_support {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (F : HalfCapProfile P.φ) (τ : ℝ) (hτ : 0 ≤ τ) (hsmall : τ ≤ F.safeAmplitude)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) π) :
    supp (perturbedCap hP hbox F τ hτ hsmall).1 t =
      supp P.cap t + τ * F.symmetricValue t := by
  rw [(perturbedTurningCap hP hbox F τ hτ hsmall).body_support ht,
    gerver_cap_explicit hP hbox, gs_supp_K hP (romik_bounds hP hbox) ht.1 ht.2]
  unfold TurningCapData.support HalfCapProfile.symmetricValue
  split_ifs with htv
  · rw [gs_H_eq_A htv]
    simp only [perturbedTurningCap, HalfCapProfile.rightOffset, dot_add_left,
      dot_smul_left, dot_uvec_self, dot_vvec_uvec, mul_one, mul_zero, add_zero]
  · rw [gs_H_eq_C hP (not_le.mp htv).le]
    have he : π / 2 - (t - π / 2) = π - t := by ring
    have hu : uvec t = vvec (t - π / 2) := by
      rw [← uvec_add_pi_div_two, sub_add_cancel]
    simp only [perturbedTurningCap, HalfCapProfile.leftOffset, he, hu,
      dot_add_left, dot_smul_left, dot_uvec_vvec, dot_vvec_self,
      mul_one, mul_zero, add_zero]

end MovingSofaQuantitative
