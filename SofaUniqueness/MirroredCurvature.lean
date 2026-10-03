module

public import SofaUniqueness.SelectedCurvature
public import SofaUniqueness.MirrorMaximality
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Both curvature bounds for the specified maximizer

Reflection sends `[0, pi/2)` to `(pi/2, pi]`. The strict and non-strict
endpoints are preserved explicitly below. The arm identity exchanges plus
with minus, so no absence of atoms is assumed to prove absence of atoms.

This is an uncompiled source proof. In particular the measure transport is
written as ordinary equalities of restricted measures and lower integrals,
not an external numerical calculation or a decision procedure.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofa

namespace SofaUniqueness

/-- The involution on normal angles induced by the right-angle cap mirror. -/
def normalReflection : ℝ ≃ᵐ ℝ where
  toFun t := π - t
  invFun t := π - t
  left_inv t := by dsimp; ring
  right_inv t := by dsimp; ring
  measurable_toFun := measurable_const.sub measurable_id
  measurable_invFun := measurable_const.sub measurable_id

@[simp] theorem normalReflection_apply (t : ℝ) : normalReflection t = π - t := rfl

/-- Reflection of real normal angles preserves Lebesgue measure. -/
theorem normalReflection_measurePreserving :
    MeasurePreserving normalReflection (volume : Measure ℝ) volume := by
  refine ⟨normalReflection.measurable, ?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply normalReflection.measurable hA]
  have heq : normalReflection ⁻¹' A =
      (fun t : ℝ => (-1 : ℝ) * t) ⁻¹' ((fun t : ℝ => π + t) ⁻¹' A) := by
    ext t
    simp only [mem_preimage, normalReflection_apply, neg_one_mul, sub_eq_add_neg]
  rw [heq, Real.volume_preimage_mul_left (by norm_num), measure_preimage_add]
  norm_num

/-- Curvature reflection, with the output cap identified as the original set. -/
theorem sigma_eq_map_mirror {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) :
    sigma K = Measure.map normalReflection (sigma (mirrorCap K (π / 2))) := by
  have h := proposition2_5_4_sigma (proposition2_5_4_isCap hK)
  rw [mirrorCap_rightAngle_involutive] at h
  change sigma K = Measure.map (fun t : ℝ => π - t) (sigma (mirrorCap K (π / 2)))
  simpa only [show π / 2 + π / 2 = π by ring] using h

/-- Push the first-half bound for the reflected cap to the second half of K.
This lemma does not require either cap to maximize the area functional. -/
theorem secondCurvature_of_mirror_first {K : Set (ℝ × ℝ)}
    (hK : IsCap K (π / 2))
    (hfirst : FirstCurvatureBound (mirrorCap K (π / 2))) : SecondCurvatureBound K := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.restrict_apply hA, withDensity_apply _ hA,
    Measure.restrict_restrict hA]
  let B := A ∩ Ioc (π / 2) π
  have hB : MeasurableSet B := hA.inter measurableSet_Ioc
  have hpre : MeasurableSet (normalReflection ⁻¹' B) := normalReflection.measurable hB
  have hsub : normalReflection ⁻¹' B ⊆ Ico 0 (π / 2) := by
    intro t ht
    have hb : π / 2 < π - t ∧ π - t ≤ π := ht.2
    constructor <;> linarith [hb.1, hb.2]
  have hmass : sigma K B =
      sigma (mirrorCap K (π / 2)) (normalReflection ⁻¹' B) := by
    rw [sigma_eq_map_mirror hK, Measure.map_apply normalReflection.measurable hB]
  have hb := Measure.le_iff'.mp hfirst (normalReflection ⁻¹' B)
  rw [Measure.restrict_apply hpre, inter_eq_left.mpr hsub,
    withDensity_apply _ hpre, Measure.restrict_restrict hpre,
    inter_eq_left.mpr hsub] at hb
  change sigma K B ≤ ∫⁻ t in B, ENNReal.ofReal (k0 (fMinus K (t - π / 2)))
  calc
    sigma K B = sigma (mirrorCap K (π / 2)) (normalReflection ⁻¹' B) := hmass
    _ ≤ ∫⁻ t in normalReflection ⁻¹' B,
        ENNReal.ofReal (k0 (gPlus (mirrorCap K (π / 2)) t)) := hb
    _ = ∫⁻ t in normalReflection ⁻¹' B,
        ENNReal.ofReal (k0 (fMinus K (normalReflection t - π / 2))) := by
      apply lintegral_congr
      intro t
      rw [gPlus_mirror_eq_fMinus, normalReflection_apply,
        show π - t - π / 2 = π / 2 - t by ring]
    _ = ∫⁻ t in B, ENNReal.ofReal (k0 (fMinus K (t - π / 2))) :=
      normalReflection_measurePreserving.setLIntegral_comp_preimage_emb
        normalReflection.measurableEmbedding
        (fun t => ENNReal.ofReal (k0 (fMinus K (t - π / 2)))) B

/-- The second curvature inequality includes the endpoint pi. -/
theorem secondCurvature_of_maximal_positive {K : Set (ℝ × ℝ)}
    (hK : IsCap K (π / 2)) (hpositive : 0 < sofaArea (π / 2) K)
    (hmax : ∀ C, IsCap C (π / 2) → sofaArea (π / 2) C ≤ sofaArea (π / 2) K) :
    SecondCurvatureBound K := by
  apply secondCurvature_of_mirror_first hK
  apply firstCurvature_of_maximal_positive (proposition2_5_4_isCap hK)
  · simpa only [sofaArea_mirror] using hpositive
  · exact maximal_sofaArea_mirror hmax

/-- Both endpoint-safe inequalities for the same specified maximizing cap. -/
theorem curvature_of_maximal_positive {K : Set (ℝ × ℝ)}
    (hK : IsCap K (π / 2)) (hpositive : 0 < sofaArea (π / 2) K)
    (hmax : ∀ C, IsCap C (π / 2) → sofaArea (π / 2) C ≤ sofaArea (π / 2) K) :
    FirstCurvatureBound K ∧ SecondCurvatureBound K :=
  ⟨firstCurvature_of_maximal_positive hK hpositive hmax,
    secondCurvature_of_maximal_positive hK hpositive hmax⟩

end SofaUniqueness
