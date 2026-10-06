module

public import MovingSofaStability.ArcAtoms

/-!
# Atom-aware cap Mamikon bookkeeping

Uncompiled proof source. Every supporting-face contribution is retained and
then cancelled against its adjacent Mamikon connector segments. In particular,
no equality of `vminus` and `vplus` is assumed at a cut or endpoint.

The result writes `mamikonS + upperP` as a sum of affine terms. Unlike the
source Ki-only proof, the displayed boundary term has no vertex coordinates:
the top face cancels those as well.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality

namespace MovingSofaStability

/-- The boundary part left after all five supporting faces have been joined. -/
def capAffineBoundary (φ : ℝ) (K : Set (ℝ × ℝ)) : ℝ :=
  supp K 0 + supp K π + (2 * sin φ - supp K φ - supp K (π - φ)) / (2 * cos φ)

def rightSegmentRemainder (φ : ℝ) (K : Set (ℝ × ℝ)) : ℝ :=
  segArea (tangentParam K (π / 2) φ) (outerCorner K φ) -
    segArea (wRight φ K) (xRight φ K)

def leftSegmentRemainder (φ : ℝ) (K : Set (ℝ × ℝ)) : ℝ :=
  segArea (tangentParam K (π / 2 + (π / 2 - φ)) (π / 2))
      (outerCorner K (π / 2 - φ)) -
    segArea (zLeft φ K) (xLeft φ K)

/-- Generalized Mamikon bookkeeping for arbitrary normalized right-angle caps. -/
theorem mamikonS_add_upperP_nonsmooth {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) :
    mamikonS φ K + upperP φ K = capAffineBoundary φ K + rightSegmentRemainder φ K +
      (curveArea (outerCorner K) φ (π / 2 - φ) -
        curveArea (innerCorner K) φ (π / 2 - φ)) - leftSegmentRemainder φ K := by
  have hpi := pi_pos
  have hφ0 := hφ.1
  have hφ4 := hφ.2
  have hφ2 : φ ∈ Ioo 0 (π / 2) := ⟨hφ0, by linarith⟩
  have hcb := hK.2.1
  have htop : supp K (π / 2) = 1 := hK.2.2.2.1
  have hc : cos φ ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith, hφ2.2⟩).ne'
  let b : ℝ := π / 2 - φ
  let T : ℝ := π / 2 + (π / 2 - φ)
  have hb : b = π / 2 - φ := rfl
  have hT : T = π / 2 + (π / 2 - φ) := rfl
  have hb0 : 0 < b := by dsimp [b]; linarith
  have hbv : b < π / 2 := by dsimp [b]; linarith
  have hvT : π / 2 < T := by dsimp [T]; linarith
  have c1 := (theorem8_3_1 hcb (t := π / 2) (a := 0) (b := φ)
    (by linarith) hφ0.le (by linarith)).2.2
  have c3 := (theorem8_3_1 hcb (t := T) (a := b) (b := π / 2)
    (by dsimp [T, b]; linarith) hbv.le hvT.le).2.2
  have c4 := (theorem8_3_1 hcb (t := π) (a := π / 2) (b := π)
    (by linarith) (by linarith) le_rfl).2.2
  have l10 : tangentParam K (π / 2) 0 = (supp K 0, 1) := by
    simp only [tangentParam, show (0 : ℝ) < π / 2 by linarith, ↓reduceIte,
      vint, htop, sub_zero, cos_pi_div_two, sin_pi_div_two, uvec_zero, vvec_zero]
    ext <;> simp
  have l3b : tangentParam K T b = outerCorner K b := by
    change tangentParam K (π / 2 + b) b = _
    rw [show π / 2 + b = b + π / 2 by ring]
    simp only [tangentParam, show b < b + π / 2 by linarith, ↓reduceIte, vint,
      show b + π / 2 - b = π / 2 by ring, cos_pi_div_two, sin_pi_div_two,
      mul_zero, sub_zero, div_one, proposition2_2_2_outerCorner]
  have l4v : tangentParam K π (π / 2) = (-supp K π, 1) := by
    simp only [tangentParam, show π / 2 < π by linarith, ↓reduceIte, vint, htop,
      show π - π / 2 = π / 2 by ring, cos_pi_div_two, sin_pi_div_two,
      mul_zero, sub_zero, div_one, uvec_pi_div_two, vvec_pi_div_two]
    ext <;> simp
  have l4π : tangentParam K π π = vminus K π := by
    simp only [tangentParam, lt_irrefl, ↓reduceIte]
  have l10mem : tangentParam K (π / 2) 0 ∈ line 0 (supp K 0) := by
    simp only [tangentParam, show (0 : ℝ) < π / 2 by linarith, ↓reduceIte]
    exact vint_mem_line_left K 0 (π / 2)
  have l1φmem : tangentParam K (π / 2) φ ∈ line φ (supp K φ) := by
    simp only [tangentParam, hφ2.2, ↓reduceIte]
    exact vint_mem_line_left K φ (π / 2)
  have l3vmem : tangentParam K T (π / 2) ∈ line (π / 2) (supp K (π / 2)) := by
    simp only [tangentParam, hvT, ↓reduceIte]
    exact vint_mem_line_left K (π / 2) T
  have l4vmem : tangentParam K π (π / 2) ∈ line (π / 2) (supp K (π / 2)) := by
    simp only [tangentParam, show π / 2 < π by linarith, ↓reduceIte]
    exact vint_mem_line_left K (π / 2) π
  have l4vleft : tangentParam K π (π / 2) ∈ line π (supp K π) := by
    rw [l4v]
    simp [line, dot, uvec]
  have e0 : edgeArea K 0 + segArea (vplus K 0) (tangentParam K (π / 2) 0) =
      supp K 0 / 2 := by
    calc
      _ = segArea (vminus K 0) (tangentParam K (π / 2) 0) :=
        segArea_add_of_mem_line (dot_vminus_uvec K 0) (dot_vplus_uvec K 0) l10mem
      _ = _ := by
        rw [(inj_cap_consecutive hK).1, l10]
        simp only [segArea, cross]
        ring
  have eφ : segArea (tangentParam K (π / 2) φ) (vminus K φ) +
      segArea (vplus K φ) (outerCorner K φ) + edgeArea K φ =
      segArea (tangentParam K (π / 2) φ) (outerCorner K φ) :=
    segArea_join_face l1φmem (dot_vminus_uvec K φ) (dot_vplus_uvec K φ)
      (inj_dot_outerCorner_uvec K φ)
  have eb : segArea (outerCorner K b) (vminus K b) +
      segArea (vplus K b) (outerCorner K b) + edgeArea K b = 0 := by
    have he := segArea_join_face (inj_dot_outerCorner_uvec K b)
      (dot_vminus_uvec K b) (dot_vplus_uvec K b) (inj_dot_outerCorner_uvec K b)
    rw [segArea_self] at he
    exact he
  have ev : segArea (tangentParam K T (π / 2)) (vminus K (π / 2)) +
      segArea (vplus K (π / 2)) (tangentParam K π (π / 2)) + edgeArea K (π / 2) =
      segArea (tangentParam K T (π / 2)) (tangentParam K π (π / 2)) :=
    segArea_join_face l3vmem (dot_vminus_uvec K (π / 2))
      (dot_vplus_uvec K (π / 2)) l4vmem
  have eπ : segArea (tangentParam K π (π / 2)) (vminus K π) + edgeArea K π =
      supp K π / 2 := by
    calc
      _ = segArea (tangentParam K π (π / 2)) (vplus K π) :=
        segArea_add_of_mem_line l4vleft (dot_vminus_uvec K π) (dot_vplus_uvec K π)
      _ = _ := by
        rw [l4v, opt_cap_vplus_pi hK]
        simp only [segArea, cross]
        ring
  have hboundary : supp K 0 / 2 +
      segArea (tangentParam K (π / 2) 0) (tangentParam K (π / 2) φ) +
      segArea (tangentParam K T (π / 2)) (tangentParam K π (π / 2)) + supp K π / 2 =
      capAffineBoundary φ K := by
    rw [l10, l4v, opt_tangent_right_eq hφ2 htop]
    change supp K 0 / 2 +
      segArea (supp K 0, 1) (wRight φ K + ((1 - sin φ) / cos φ, 1)) +
      segArea (tangentParam K (π / 2 + (π / 2 - φ)) (π / 2)) (-supp K π, 1) +
      supp K π / 2 = _
    rw [opt_tangent_left_eq hφ2 htop, opt_wRight_eq, opt_zLeft_eq]
    simp only [capAffineBoundary, segArea, cross, Prod.fst_add, Prod.snd_add]
    field_simp [hc]
    ring
  have harea := cap_area_four_arcs hφ hK
  have swR := segArea_swap (xRight φ K) (wRight φ K)
  have swL := segArea_swap (outerCorner K b) (tangentParam K T (π / 2))
  change mamikonS φ K + upperP φ K = capAffineBoundary φ K +
      (segArea (tangentParam K (π / 2) φ) (outerCorner K φ) -
        segArea (wRight φ K) (xRight φ K)) +
      (curveArea (outerCorner K) φ b - curveArea (innerCorner K) φ b) -
      (segArea (tangentParam K T (π / 2)) (outerCorner K b) -
        segArea (zLeft φ K) (xLeft φ K))
  simp only [mamikonS, mamikon, upperP]
  change _ = _ at harea
  simp only [← hb] at *
  rw [c1, c3, c4, l3b, l4π]
  simp only [segArea_self]
  linarith only [harea, e0, eφ, eb, ev, eπ, hboundary, swR, swL]

end MovingSofaStability
