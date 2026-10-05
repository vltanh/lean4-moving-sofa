module

public import MovingSofaStability.ReferenceCoreVariation

/-!
# First variation of Q on the enlarged domain

Uncompiled proof source. The reference cap belongs to Ki and its two tails
meet its core. The competing triple is only in the enlarged nonsmooth domain.
All derivatives of corner paths below belong to the reference cap.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality

namespace MovingSofaStability

/-- The nonsmooth-competitor version of source Theorem 8.5.6. -/
theorem wide_reference_firstVariation {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (x xs : WideTriple φ) (hK : IsKi x.1.1.1)
    (hX : xB φ x.1.2.1.1 = xRight φ x.1.1.1)
    (hY : yD φ x.1.2.2.1 = xLeft φ x.1.1.1) :
    (wideDomain φ).dirDeriv (wideUpperQ φ) x xs =
      (∫ t in Icc 0 π, (supp xs.1.1.1 t - supp x.1.1.1 t) ∂(sigma x.1.1.1)) -
        (∫ t in Icc φ (π / 2 - φ) ∪ Icc (φ + π / 2) (π - φ),
          (supp xs.1.1.1 t - supp x.1.1.1 t) * iFun x.1.1.1 t) +
        (∫ t in Ioo φ (π / 2),
          (suppBreve xs.1.2.1.1 t - suppBreve x.1.2.1.1 t) ∂(sigmaBreve x.1.2.1.1)) +
        (∫ t in Ioo (π / 2) (π / 2 + (π / 2 - φ)),
          (suppBreve xs.1.2.2.1 t - suppBreve x.1.2.2.1 t) ∂(sigmaBreve x.1.2.2.1)) := by
  have hpi := pi_pos
  have hφ0 := hφ.1
  have hφ4 := hφ.2
  have d1 : HasDerivWithinAt (fun c => area ((wideDomain φ).comb c x xs).1.1.1)
      (∫ t in Icc 0 π, (supp xs.1.1.1 t - supp x.1.1.1 t) ∂(sigma x.1.1.1)) (Icc 0 1) 0 := by
    have h := opt_quadratic_hasDerivWithinAt theorem7_1_3_quadratic x.1.1 xs.1.1
    rw [area_firstVariation_caps x.1.1 xs.1.1 x.2.1 xs.2.1] at h
    exact opt_hasDerivWithinAt_comp (x := x) (xs := xs)
      (f := fun K : ConvexBodySet => area K.1) (wide_projK_linear φ) h
  have d2 : HasDerivWithinAt
      (fun c => convexCurveArea ((wideDomain φ).comb c x xs).1.2.2.1 (3 * π / 2)
        (3 * π / 2 + (π / 2 - φ)))
      ((∫ t in Ioo (3 * π / 2) (3 * π / 2 + (π / 2 - φ)),
          (supp xs.1.2.2.1 t - supp x.1.2.2.1 t) ∂(sigma x.1.2.2.1)) +
        (segArea (yD φ x.1.2.2.1) (yD φ xs.1.2.2.1) -
          segArea (vplus x.1.2.2.1 (3 * π / 2)) (vplus xs.1.2.2.1 (3 * π / 2))))
      (Icc 0 1) 0 := by
    have hT := theorem8_5_2 (a := 3 * π / 2) (b := 3 * π / 2 + (π / 2 - φ))
      (by linarith) (by linarith)
    have h := opt_quadratic_hasDerivWithinAt hT.1 x.1.2.2 xs.1.2.2
    rw [hT.2] at h
    exact opt_hasDerivWithinAt_comp (x := x) (xs := xs)
      (f := fun K : ConvexBodySet => convexCurveArea K.1 (3 * π / 2) (3 * π / 2 + (π / 2 - φ)))
      (wide_projD_linear φ) h
  have hP3 : (wideDomain φ).IsConvexLinear (vectorDomain ((ℝ × ℝ) × (ℝ × ℝ)))
      (fun v : WideTriple φ => (yD φ v.1.2.2.1, xLeft φ v.1.1.1)) :=
    opt_isConvexLinear_pair
      (opt_isConvexLinear_comp (f := fun v : WideTriple φ => v.1.2.2)
        (g := fun K : ConvexBodySet => vminus K.1 (3 * π / 2 + (π / 2 - φ)))
        (wide_projD_linear φ) (opt_vminus_linear _))
      (opt_isConvexLinear_comp (f := fun v : WideTriple φ => v.1.1)
        (g := fun K : ConvexBodySet => innerCorner K.1 (π / 2 - φ))
        (wide_projK_linear φ) (opt_innerCorner_linear _))
  have d3 : HasDerivWithinAt
      (fun c => segArea (yD φ ((wideDomain φ).comb c x xs).1.2.2.1)
        (xLeft φ ((wideDomain φ).comb c x xs).1.1.1))
      ((1 / 2) * (cross (yD φ xs.1.2.2.1 + xLeft φ xs.1.1.1)
          (xLeft φ x.1.1.1 - yD φ x.1.2.2.1) -
          2 * cross (yD φ x.1.2.2.1) (xLeft φ x.1.1.1)) +
        (segArea (xLeft φ x.1.1.1) (xLeft φ xs.1.1.1) -
          segArea (yD φ x.1.2.2.1) (yD φ xs.1.2.2.1))) (Icc 0 1) 0 := by
    have h := opt_quadratic_hasDerivWithinAt theorem8_5_3.1
      (yD φ x.1.2.2.1, xLeft φ x.1.1.1) (yD φ xs.1.2.2.1, xLeft φ xs.1.1.1)
    rw [theorem8_5_3.2] at h
    exact opt_hasDerivWithinAt_comp (x := x) (xs := xs)
      (f := fun p : (ℝ × ℝ) × (ℝ × ℝ) => segArea p.1 p.2) hP3 h
  have d4 : HasDerivWithinAt
      (fun c => curveArea (innerCorner ((wideDomain φ).comb c x xs).1.1.1) φ (π / 2 - φ))
      ((∫ t in Icc φ (π / 2 - φ) ∪ Icc (φ + π / 2) (π - φ),
          (supp xs.1.1.1 t - supp x.1.1.1 t) * iFun x.1.1.1 t) +
        (segArea (xLeft φ x.1.1.1) (xLeft φ xs.1.1.1) -
          segArea (xRight φ x.1.1.1) (xRight φ xs.1.1.1))) (Icc 0 1) 0 := by
    have h := opt_quadratic_hasDerivWithinAt (coreArea_quadratic hφ) x.1.1 xs.1.1
    rw [reference_core_firstVariation hφ x.1.1 xs.1.1 hK] at h
    exact opt_hasDerivWithinAt_comp (x := x) (xs := xs)
      (f := fun K : ConvexBodySet => curveArea (innerCorner K.1) φ (π / 2 - φ))
      (wide_projK_linear φ) h
  have hP5 : (wideDomain φ).IsConvexLinear (vectorDomain ((ℝ × ℝ) × (ℝ × ℝ)))
      (fun v : WideTriple φ => (xRight φ v.1.1.1, xB φ v.1.2.1.1)) :=
    opt_isConvexLinear_pair
      (opt_isConvexLinear_comp (f := fun v : WideTriple φ => v.1.1)
        (g := fun K : ConvexBodySet => innerCorner K.1 φ)
        (wide_projK_linear φ) (opt_innerCorner_linear _))
      (opt_isConvexLinear_comp (f := fun v : WideTriple φ => v.1.2.1)
        (g := fun K : ConvexBodySet => vplus K.1 (π + φ))
        (wide_projB_linear φ) (opt_vplus_linear _))
  have d5 : HasDerivWithinAt
      (fun c => segArea (xRight φ ((wideDomain φ).comb c x xs).1.1.1)
        (xB φ ((wideDomain φ).comb c x xs).1.2.1.1))
      ((1 / 2) * (cross (xRight φ xs.1.1.1 + xB φ xs.1.2.1.1)
          (xB φ x.1.2.1.1 - xRight φ x.1.1.1) -
          2 * cross (xRight φ x.1.1.1) (xB φ x.1.2.1.1)) +
        (segArea (xB φ x.1.2.1.1) (xB φ xs.1.2.1.1) -
          segArea (xRight φ x.1.1.1) (xRight φ xs.1.1.1))) (Icc 0 1) 0 := by
    have h := opt_quadratic_hasDerivWithinAt theorem8_5_3.1
      (xRight φ x.1.1.1, xB φ x.1.2.1.1) (xRight φ xs.1.1.1, xB φ xs.1.2.1.1)
    rw [theorem8_5_3.2] at h
    exact opt_hasDerivWithinAt_comp (x := x) (xs := xs)
      (f := fun p : (ℝ × ℝ) × (ℝ × ℝ) => segArea p.1 p.2) hP5 h
  have d6 : HasDerivWithinAt
      (fun c => convexCurveArea ((wideDomain φ).comb c x xs).1.2.1.1 (π + φ) (3 * π / 2))
      ((∫ t in Ioo (π + φ) (3 * π / 2),
          (supp xs.1.2.1.1 t - supp x.1.2.1.1 t) ∂(sigma x.1.2.1.1)) +
        (segArea (vminus x.1.2.1.1 (3 * π / 2)) (vminus xs.1.2.1.1 (3 * π / 2)) -
          segArea (xB φ x.1.2.1.1) (xB φ xs.1.2.1.1))) (Icc 0 1) 0 := by
    have hT := theorem8_5_2 (a := π + φ) (b := 3 * π / 2) (by linarith) (by linarith)
    have h := opt_quadratic_hasDerivWithinAt hT.1 x.1.2.1 xs.1.2.1
    rw [hT.2] at h
    exact opt_hasDerivWithinAt_comp (x := x) (xs := xs)
      (f := fun K : ConvexBodySet => convexCurveArea K.1 (π + φ) (3 * π / 2))
      (wide_projB_linear φ) h
  have hd : HasDerivWithinAt
      (fun c => wideUpperQ φ ((wideDomain φ).comb c x xs)) _ (Icc 0 1) 0 :=
    ((((d1.add d2).add d3).sub d4).add d5).add d6
  rw [opt_dirDeriv_eq hd]
  have z1 : segArea (vplus x.1.2.2.1 (3 * π / 2)) (vplus xs.1.2.2.1 (3 * π / 2)) = 0 :=
    segArea_of_snd_eq_zero (opt_snd_vplus_three_pi_div_two (inWideL_supp x.2).2.1)
      (opt_snd_vplus_three_pi_div_two (inWideL_supp xs.2).2.1)
  have z2 : segArea (vminus x.1.2.1.1 (3 * π / 2)) (vminus xs.1.2.1.1 (3 * π / 2)) = 0 :=
    segArea_of_snd_eq_zero (opt_snd_vminus_three_pi_div_two (inWideL_supp x.2).1)
      (opt_snd_vminus_three_pi_div_two (inWideL_supp xs.2).1)
  have c3 : cross (yD φ xs.1.2.2.1 + xLeft φ xs.1.1.1)
      (xLeft φ x.1.1.1 - yD φ x.1.2.2.1) = 0 := by
    rw [hY, sub_self]; simp [cross]
  have c3' : cross (yD φ x.1.2.2.1) (xLeft φ x.1.1.1) = 0 := by
    rw [hY, cross_self]
  have c5 : cross (xRight φ xs.1.1.1 + xB φ xs.1.2.1.1)
      (xB φ x.1.2.1.1 - xRight φ x.1.1.1) = 0 := by
    rw [hX, sub_self]; simp [cross]
  have c5' : cross (xRight φ x.1.1.1) (xB φ x.1.2.1.1) = 0 := by
    rw [hX, cross_self]
  have b1 := opt_breve_integral x.1.2.1.1 xs.1.2.1.1 (a := φ) (b := π / 2)
    (a' := π + φ) (b' := 3 * π / 2) (by ring) (by ring)
  have b2 := opt_breve_integral x.1.2.2.1 xs.1.2.2.1
    (a := π / 2) (b := π / 2 + (π / 2 - φ)) (a' := 3 * π / 2)
    (b' := 3 * π / 2 + (π / 2 - φ)) (by ring) (by ring)
  rw [b1, b2, z1, z2, c3, c3', c5, c5']
  ring

end MovingSofaStability
