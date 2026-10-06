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
  sorry

end MovingSofaStability
