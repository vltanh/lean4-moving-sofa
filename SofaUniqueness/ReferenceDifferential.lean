module

public import SofaUniqueness.ReferenceDomainBounds

/-!
# Differential identities for the reference equations

All derivatives in this module are explicit. The global phi comparison uses
an auxiliary derivative whose theta derivative is a sum of nonpositive terms,
with one strictly negative term. This avoids a grid certificate for that sign.
The bound `phi <= 1/2` is sufficient and was proved for every solution in
`ReferenceDomainBounds`. Uncompiled source.
-/

@[expose] public section
noncomputable section

open Set Real

namespace SofaUniqueness.Reference

def gap (φ θ : ℝ) : ℝ := θ - φ

def frameDen (φ θ : ℝ) : ℝ := cos φ - slope φ θ * sin φ

def frameOffset (φ θ : ℝ) : ℝ :=
  sin φ * (1 + offset φ θ) + (1 - cos φ) / 2

def minOffset (φ θ : ℝ) : ℝ := gap φ θ / 2 + gap φ θ ^ 2 / 4

def qPhi (φ θ : ℝ) : ℝ :=
  -den φ θ * cos φ * offset φ θ -
    num φ θ * (sin φ / 2 + slope φ θ * cos φ) +
      3 * sin φ * frameOffset φ θ

def qTheta (φ θ : ℝ) : ℝ :=
  ((1 - gap φ θ) * frameDen φ θ - frameOffset φ θ) * sin θ +
    (3 * (1 - gap φ θ) * cos φ - 3 * sin φ + sin θ - 1) * sin φ / 2

def qPhiMin (φ θ : ℝ) : ℝ :=
  -den φ θ * cos φ * minOffset φ θ -
    num φ θ * (sin φ / 2 + slope φ θ * cos φ) +
      3 * sin φ * (sin φ * (1 + minOffset φ θ) + (1 - cos φ) / 2)

/-- A manifest-sign form of the theta derivative of qPhiMin. -/
def qPhiMinTheta (φ θ : ℝ) : ℝ :=
  (-6 * gap φ θ * (cos φ ^ 2 - sin φ ^ 2) +
    6 * sin φ * (sin φ - cos φ) - 2 * cos φ ^ 2 +
    4 * cos φ * (cos θ - cos φ) - 2 * cos φ +
    cos φ * sin θ * (gap φ θ ^ 2 - 2) +
    2 * sin φ * sin θ * (gap φ θ - 1)) / 4

theorem reducedQ_frame (φ θ : ℝ) :
    reducedQ φ θ = num φ θ * frameDen φ θ - den φ θ * frameOffset φ θ := by
  unfold reducedQ frameDen frameOffset
  ring

theorem num_phi_deriv (φ θ : ℝ) :
    HasDerivAt (fun p => num p θ) (den φ θ) φ := by
  convert ((((((hasDerivAt_id φ).const_sub θ).mul_const (cos θ)).add
    ((hasDerivAt_sin φ).const_mul 3)).sub_const (sin θ)).sub_const (cos θ)).add_const 1
    using 1 <;> simp only [num, den] <;> ring

theorem num_theta_deriv (φ θ : ℝ) :
    HasDerivAt (fun t => num φ t) ((1 - gap φ θ) * sin θ) θ := by
  convert (((((((hasDerivAt_id θ).sub_const φ).mul (hasDerivAt_cos θ)).add_const
    (3 * sin φ)).sub (hasDerivAt_sin θ)).sub (hasDerivAt_cos θ)).add_const 1)
    using 1 <;> simp only [num, gap] <;> ring

theorem den_phi_deriv (φ θ : ℝ) :
    HasDerivAt (fun p => den p θ) (-3 * sin φ) φ := by
  convert ((hasDerivAt_cos φ).const_mul 3).sub_const (cos θ) using 1 <;>
    simp only [den] <;> ring

theorem den_theta_deriv (φ θ : ℝ) :
    HasDerivAt (fun t => den φ t) (sin θ) θ := by
  convert (hasDerivAt_cos θ).const_sub (3 * cos φ) using 1 <;>
    simp only [den] <;> ring

theorem slope_phi_deriv (φ θ : ℝ) :
    HasDerivAt (fun p => slope p θ) (-1 / 2) φ := by
  convert (((hasDerivAt_id φ).const_sub θ).div_const 2).const_add 1 using 1 <;>
    simp only [slope] <;> ring

theorem slope_theta_deriv (φ θ : ℝ) :
    HasDerivAt (fun t => slope φ t) (1 / 2) θ := by
  convert (((hasDerivAt_id θ).sub_const φ).div_const 2).const_add 1 using 1 <;>
    simp only [slope] <;> ring

theorem offset_phi_deriv (φ θ : ℝ) :
    HasDerivAt (fun p => offset p θ) (-slope φ θ - 1 / 2) φ := by
  have hg := (hasDerivAt_id φ).const_sub θ
  convert ((((hasDerivAt_id φ).const_sub (π / 2)).sub_const θ).add
    (hg.div_const 2)).add ((hg.pow 2).div_const 4) using 1 <;>
    simp only [offset, slope] <;> ring

theorem offset_theta_deriv (φ θ : ℝ) :
    HasDerivAt (fun t => offset φ t) ((gap φ θ - 1) / 2) θ := by
  have hg := (hasDerivAt_id θ).sub_const φ
  convert (((hasDerivAt_id θ).const_sub (π / 2 - φ)).add
    (hg.div_const 2)).add ((hg.pow 2).div_const 4) using 1 <;>
    simp only [offset, gap] <;> ring

theorem frameDen_phi_deriv (φ θ : ℝ) :
    HasDerivAt (fun p => frameDen p θ) (-sin φ / 2 - slope φ θ * cos φ) φ := by
  convert (hasDerivAt_cos φ).sub ((slope_phi_deriv φ θ).mul (hasDerivAt_sin φ))
    using 1 <;> simp only [frameDen] <;> ring

theorem frameDen_theta_deriv (φ θ : ℝ) :
    HasDerivAt (fun t => frameDen φ t) (-sin φ / 2) θ := by
  convert ((slope_theta_deriv φ θ).mul_const (sin φ)).const_sub (cos φ)
    using 1 <;> simp only [frameDen] <;> ring

theorem frameOffset_phi_deriv (φ θ : ℝ) :
    HasDerivAt (fun p => frameOffset p θ)
      (cos φ * (1 + offset φ θ) - slope φ θ * sin φ) φ := by
  convert ((hasDerivAt_sin φ).mul ((offset_phi_deriv φ θ).const_add 1)).add
    (((hasDerivAt_cos φ).const_sub 1).div_const 2) using 1 <;>
    simp only [frameOffset] <;> ring

theorem frameOffset_theta_deriv (φ θ : ℝ) :
    HasDerivAt (fun t => frameOffset φ t) (sin φ * (gap φ θ - 1) / 2) θ := by
  convert (((offset_theta_deriv φ θ).const_add 1).const_mul (sin φ)).add_const
    ((1 - cos φ) / 2) using 1 <;> simp only [frameOffset] <;> ring

theorem reducedQ_phi_deriv (φ θ : ℝ) :
    HasDerivAt (fun p => reducedQ p θ) (qPhi φ θ) φ := by
  have hd := ((num_phi_deriv φ θ).mul (frameDen_phi_deriv φ θ)).sub
    ((den_phi_deriv φ θ).mul (frameOffset_phi_deriv φ θ))
  convert hd using 1
  · funext p
    exact reducedQ_frame p θ
  · unfold qPhi frameDen frameOffset
    ring

theorem reducedQ_theta_deriv (φ θ : ℝ) :
    HasDerivAt (fun t => reducedQ φ t) (qTheta φ θ) θ := by
  have hd := ((num_theta_deriv φ θ).mul (frameDen_theta_deriv φ θ)).sub
    ((den_theta_deriv φ θ).mul (frameOffset_theta_deriv φ θ))
  convert hd using 1
  · funext t
    exact reducedQ_frame φ t
  · unfold qTheta gap frameDen frameOffset num den slope
    ring

theorem qPhiMin_theta_deriv (φ θ : ℝ) :
    HasDerivAt (fun t => qPhiMin φ t) (qPhiMinTheta φ θ) θ := by
  have hg := (hasDerivAt_id θ).sub_const φ
  have hm : HasDerivAt (fun t => minOffset φ t) (1 / 2 + gap φ θ / 2) θ := by
    convert (hg.div_const 2).add ((hg.pow 2).div_const 4) using 1 <;>
      simp only [minOffset, gap] <;> ring
  have hd := ((((den_theta_deriv φ θ).neg.mul_const (cos φ)).mul hm).sub
    ((num_theta_deriv φ θ).mul (((slope_theta_deriv φ θ).mul_const (cos φ)).const_add
      (sin φ / 2)))).add
    (((((hm.const_add 1).const_mul (sin φ)).add_const ((1 - cos φ) / 2)).const_mul
      (3 * sin φ))
  convert hd using 1
  · funext t
    unfold qPhiMin
    ring
  · unfold qPhiMinTheta gap minOffset slope num den
    ring

/-- The sign proof is a sum of signed terms, not a finite computation. -/
theorem qPhiMinTheta_neg {φ θ : ℝ} (hφ : 0 ≤ φ) (horder : φ ≤ θ)
    (hθ : θ ≤ π / 4) : qPhiMinTheta φ θ < 0 := by
  obtain ⟨hs, hsc, hc, hcc, hts, htc, hsum⟩ := triangle_trig hφ horder hθ
  have hg0 : 0 ≤ gap φ θ := sub_nonneg.mpr horder
  have hg1 : gap φ θ ≤ 1 := by unfold gap; linarith [pi_lt_four]
  have hsq : 0 ≤ cos φ ^ 2 - sin φ ^ 2 := by nlinarith
  have h0 := mul_nonpos_of_nonpos_of_nonneg (show -6 * gap φ θ ≤ 0 by positivity) hsq
  have h1 := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 6 * sin φ by positivity)
    (sub_nonpos.mpr hsc)
  have h2 := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 4 * cos φ by positivity)
    (sub_nonpos.mpr hcc)
  have hg2 : gap φ θ ^ 2 - 2 ≤ 0 := by nlinarith
  have h3 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hc.le hts) hg2
  have h4 := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ 2 * sin φ * sin θ by positivity) (sub_nonpos.mpr hg1)
  unfold qPhiMinTheta
  nlinarith [sq_nonneg (cos φ)]

theorem qPhiMin_diagonal_nonpos {φ : ℝ} (hφ : 0 ≤ φ) (hφu : φ ≤ π / 4) :
    qPhiMin φ φ ≤ 0 := by
  obtain ⟨hs, hsc, hc, _, _, _, _⟩ := triangle_trig hφ le_rfl hφu
  have he : qPhiMin φ φ = (sin φ - cos φ) * (1 - cos φ + 2 * sin φ) := by
    unfold qPhiMin minOffset gap num den slope
    ring
  rw [he]
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hsc)
    (by linarith [cos_le_one φ])

/-- The actual partial derivative is bounded above by the auxiliary one. -/
theorem qPhi_le_min {φ θ : ℝ} (hφ : 0 ≤ φ) (hφh : φ ≤ 1 / 2)
    (horder : φ ≤ θ) (hθ : θ ≤ π / 4) : qPhi φ θ ≤ qPhiMin φ θ := by
  obtain ⟨hs, hsc, hc, hcc, hts, htc, hsum⟩ := triangle_trig hφ horder hθ
  have hsHalf : sin φ ≤ 1 / 2 := (sin_le hφ).trans hφh
  have hcLower : (7 / 8 : ℝ) ≤ cos φ := by
    have h := one_sub_sq_div_two_le_cos (x := φ)
    nlinarith
  have hden : 2 * cos φ ≤ den φ θ := by unfold den; linarith
  have hdenMul := mul_le_mul_of_nonneg_right hden hc.le
  have hcoeff : -den φ θ * cos φ + 3 * sin φ ^ 2 ≤ 0 := by nlinarith
  have hgap : 0 ≤ π / 2 - φ - θ := by linarith
  have hprod := mul_nonpos_of_nonpos_of_nonneg hcoeff hgap
  have he : qPhi φ θ - qPhiMin φ θ =
      (-den φ θ * cos φ + 3 * sin φ ^ 2) * (π / 2 - φ - θ) := by
    unfold qPhi qPhiMin frameOffset offset minOffset gap
    ring
  linarith

/-- Strict phi monotonicity on the portion containing every possible root. -/
theorem qPhi_neg {φ θ : ℝ} (hφ : 0 ≤ φ) (hφh : φ ≤ 1 / 2)
    (horder : φ < θ) (hθ : θ ≤ π / 4) : qPhi φ θ < 0 := by
  have ha : StrictAntiOn (qPhiMin φ) (Icc φ θ) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc φ θ)
    · exact fun t _ => (qPhiMin_theta_deriv φ t).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(qPhiMin_theta_deriv φ t).deriv]
      exact qPhiMinTheta_neg hφ ht.1.le (ht.2.le.trans hθ)
  have hlt := ha ⟨le_rfl, horder.le⟩ ⟨horder.le, le_rfl⟩ horder
  exact (qPhi_le_min hφ hφh horder.le hθ).trans_lt
    (hlt.trans_le (qPhiMin_diagonal_nonpos hφ (horder.le.trans hθ)))

end SofaUniqueness.Reference
