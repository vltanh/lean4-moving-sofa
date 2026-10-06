module

public import MovingSofaStability.CoreRegionGeometry
public import MovingSofaStability.TerminalBookkeeping

/-!
# The local core-area inequality

Uncompiled proof source. The core is a continuous Lipschitz graph with a
strictly positive height. Its under-graph region and two endpoint triangles
are disjoint subsets of the middle niche. Their areas give the same signed
curve bound as Baek's smooth proof.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality

namespace MovingSofaStability

/-- Core-area lower bound under the exact geometric hypotheses used locally. -/
theorem positive_core_area_le {φ c : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set Point} (hK : IsCap K (π / 2))
    (hcore : CoreArmMargin K φ (π / 2 - φ) c) (hc : 0 < c)
    (hsep : CutSeparated φ K)
    (hheight : ∀ t ∈ Icc φ (π / 2 - φ), 0 < (innerCorner K t).2) :
    segArea (wRight φ K) (xRight φ K) + curveArea (innerCorner K) φ (π / 2 - φ) +
      segArea (xLeft φ K) (zLeft φ K) ≤
      area ((niche K (π / 2) \ hRight φ K) \ hLeft φ K) := by
  sorry

end MovingSofaStability
