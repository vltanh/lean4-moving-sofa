module

public import MovingSofa.Angle.HorizontalSide
public import MovingSofa.Intro.RotationAngleBound
public import Mathlib.Analysis.Convex.Function

/-!
# Right rotation angle (§4.2) and Theorem 1.5.2

Proposition 4.2.1 (`pro:omega-gap`), Definitions 4.2.2–4.2.4, Lemmas 4.2.2–4.2.4, Theorem 4.2.5
(`thm:balanced-consumed`) and Theorem 1.5.2 (`thm:angle`). Definition 4.2.1 (right triangles with a
base and an angle) is only used in prose inside proofs and is not formalized.

**Reading of Lemma 4.2.4.** The paper states it for `ω ∈ [tan⁻¹(2.2), π/2)`; its proof treats
`ω ∈ [sec⁻¹(2.2), tan⁻¹(2.2))` as well, and Theorem 4.2.5 applies it on all of
`[sec⁻¹(2.2), π/2)`. We state it on `[sec⁻¹(2.2), π/2)`.
-/

@[expose] public section

open Real Set

namespace MovingSofa

/-- `c_ω = tan((π/2 - ω)/2)` (Proposition 4.2.1). -/
noncomputable def cOmega (ω : ℝ) : ℝ := tan ((π / 2 - ω) / 2)

/-- **Proposition 4.2.1** (`pro:omega-gap`). For `ω ∈ [0, π/2)`: `o_ω - v_0 = c_ω u_0`,
`o_ω - u_ω = c_ω v_ω`, the base `e_{P_ω}(3π/2)` of `P_ω` is the segment from `O` to `(sec ω, 0)`,
and `c_ω = sec ω - tan ω`. -/
theorem proposition4_2_1 {ω : ℝ} (hω : ω ∈ Ico 0 (π / 2)) :
    oPt ω - vvec 0 = cOmega ω • uvec 0 ∧ oPt ω - uvec ω = cOmega ω • vvec ω ∧
      edge (para ω) (3 * π / 2) = segment ℝ (0, 0) (1 / cos ω, 0) ∧
      cOmega ω = 1 / cos ω - tan ω := by
  sorry

/-- `d_{ω,min}`: `1.25` if `ω < tan⁻¹(2.2)` and `1.1` otherwise (Definition 4.2.2, `def:d-min`). -/
noncomputable def dMin (ω : ℝ) : ℝ := if ω < arctan 2.2 then 1.25 else 1.1

/-- `R_{ω,d} = P_ω ∩ H₋(0, d + c_ω) ∩ H₋(ω + π/2, d + c_ω)` (Definition 4.2.3, `def:cap-clipped`). -/
def clippedRegion (ω d : ℝ) : Set (ℝ × ℝ) :=
  para ω ∩ halfMinus 0 (d + cOmega ω) ∩ halfMinus (ω + π / 2) (d + cOmega ω)

/-- **Lemma 4.2.2** (`lem:cap-support-elementary-bound`). For `ω ∈ [sec⁻¹(2.2), π/2)`, the region
`R_{ω, d_{ω,min}}` has area less than `2.2`. -/
theorem lemma4_2_2 {ω : ℝ} (hω : ω ∈ Ico arcsec22 (π / 2)) : area (clippedRegion ω (dMin ω)) < 2.2 := by
  sorry

/-- **Lemma 4.2.3** (`lem:calculation-convex`). For `d ≥ 1`, `(1 - d cot ω)²` and `cos² ω` are convex
on `[π/4, π/2]`. -/
theorem lemma4_2_3 {d : ℝ} (hd : 1 ≤ d) :
    ConvexOn ℝ (Icc (π / 4) (π / 2)) (fun ω => (1 - d * cot ω) ^ 2) ∧
      ConvexOn ℝ (Icc (π / 4) (π / 2)) (fun ω => cos ω ^ 2) := by
  sorry

/-- `r_y = 1 - d cot ω` (Definition 4.2.4, `def:calculation-variables`). -/
noncomputable def calcRy (ω d : ℝ) : ℝ := 1 - d * cot ω
/-- `g = √(1 - r_y²)` (Definition 4.2.4). -/
noncomputable def calcG (ω d : ℝ) : ℝ := Real.sqrt (1 - calcRy ω d ^ 2)
/-- `q_0 = o_ω - v_0 + d u_0` (Definition 4.2.4). -/
noncomputable def calcQ0 (ω d : ℝ) : ℝ × ℝ := oPt ω - vvec 0 + d • uvec 0
/-- `q_1 = o_ω - g u_0` (Definition 4.2.4). -/
noncomputable def calcQ1 (ω d : ℝ) : ℝ × ℝ := oPt ω - calcG ω d • uvec 0

/-- **Lemma 4.2.4** (`lem:calculation-inequalities`), on `ω ∈ [sec⁻¹(2.2), π/2)` (see the module
docstring). For `d ∈ [d_{ω,min}, tan ω]` with `r_y ≥ 0`:
(1) `(q_0 - (o_ω - v_0)) · u_{π/2 - ω} > 1`; (2) `(q_1 - (o_ω - u_ω)) · v_{π/2 - ω} > 1`. -/
theorem lemma4_2_4 {ω d : ℝ} (hω : ω ∈ Ico arcsec22 (π / 2)) (hd : d ∈ Icc (dMin ω) (tan ω))
    (hry : 0 ≤ calcRy ω d) :
    1 < dot (calcQ0 ω d - (oPt ω - vvec 0)) (uvec (π / 2 - ω)) ∧
      1 < dot (calcQ1 ω d - (oPt ω - uvec ω)) (vvec (π / 2 - ω)) := by
  sorry

/-- **Theorem 4.2.5** (`thm:balanced-consumed`). Let `ω ∈ [sec⁻¹(2.2), π/2)` and let `K` be a balanced
maximum cap with rotation angle `ω` and `𝒜_ω(K) ≥ 2.2`. Then for some `t ∈ (0, ω)` the three points
`O`, `o_ω - v_0`, `o_ω - u_ω` lie in the closure of `Q_K⁻(t)`. -/
theorem theorem4_2_5 {K : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ico arcsec22 (π / 2))
    (hK : IsBalancedMaxCap K ω) (harea : 2.2 ≤ sofaArea ω K) :
    ∃ t ∈ Ioo 0 ω, (0, 0) ∈ closure (qMinus K t) ∧ oPt ω - vvec 0 ∈ closure (qMinus K t) ∧
      oPt ω - uvec ω ∈ closure (qMinus K t) := by
  sorry

/-- **Theorem 1.5.2** (`thm:angle`). A balanced maximum sofa `S_ω` of area at least `2.2` with
rotation angle `ω ∈ [sec⁻¹(2.2), π/2]` has a rotated copy admitting a movement with rotation angle
`π/2`. -/
theorem theorem1_5_2 {S : Set (ℝ × ℝ)} {ω : ℝ} (hS : IsBalancedMaxSofa S ω) (harea : 2.2 ≤ area S)
    (hω : ω ∈ Icc arcsec22 (π / 2)) : ∃ s : ℝ, IsMovingSofaWithAngle (rot s '' S) (π / 2) := by
  sorry

end MovingSofa
