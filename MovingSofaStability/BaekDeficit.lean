module

public import MovingSofaStability.MamikonEnergy

/-!
# Quantitative energy bounds for Baek's existing triple domain

Uncompiled proof source. Unlike the generic algebraic results, the theorems
below use the repository's actual `upperQL`, Gerver parameters, and cap/niche
area functional. Their domain is the existing `LTriple`, whose cap lies in Ki.

This file does NOT claim the nonsmooth enlarged-domain theorem of note 05.
The midpoint energies are identified with displacement-square integrals by
`mamikon_midpoint_energy` term by term; here they are grouped as cap, right,
and left energies. The two nonnegative auxiliary energies can be discarded.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness
open GerverParams

namespace MovingSofaStability

/-- The triple combination has the expected three convex-body components. -/
theorem triple_comb_val {φ c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (x y : LTriple φ) :
    ((lDomain φ).comb c x y).1 =
      (convexBodyComb c x.1.1 y.1.1,
        convexBodyComb c x.1.2.1 y.1.2.1,
        convexBodyComb c x.1.2.2 y.1.2.2) := by
  simp only [lDomain, LTriple.comb, hc, ↓reduceDIte]

def capMidpointEnergy {φ : ℝ} (x y : LTriple φ) : ℝ :=
  4 * ((mamikonS φ x.1.1.1 + mamikonS φ y.1.1.1) / 2 -
    mamikonS φ ((lDomain φ).comb (1 / 2) x y).1.1.1)

def rightMidpointEnergy {φ : ℝ} (x y : LTriple φ) : ℝ :=
  4 * ((mamikonR φ x.1.2.1.1 + mamikonR φ y.1.2.1.1) / 2 -
    mamikonR φ ((lDomain φ).comb (1 / 2) x y).1.2.1.1)

def leftMidpointEnergy {φ : ℝ} (x y : LTriple φ) : ℝ :=
  4 * ((mamikonL φ x.1.2.2.1 + mamikonL φ y.1.2.2.1) / 2 -
    mamikonL φ ((lDomain φ).comb (1 / 2) x y).1.2.2.1)

/-- All three grouped energies are nonnegative. No claim of positive
 definiteness in the auxiliary-body variables is made. -/
theorem midpoint_energies_nonneg {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (x y : LTriple φ) :
    0 ≤ capMidpointEnergy x y ∧ 0 ≤ rightMidpointEnergy x y ∧
      0 ≤ leftMidpointEnergy x y := by
  obtain ⟨-, cS, -, cR, -, cL⟩ := lemma8_3_3 hφ
  have hc : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  let z := (lDomain φ).comb (1 / 2) x y
  have hzv := triple_comb_val hc x y
  let kx : KiSet := ⟨x.1.1, x.2.1⟩
  let ky : KiSet := ⟨y.1.1, y.2.1⟩
  let kz : KiSet := ⟨z.1.1, z.2.1⟩
  have hkz : kz = kiComb (1 / 2) kx ky := by
    apply Subtype.ext
    show z.1.1 = (kiComb (1 / 2) kx ky).1
    simp only [kiComb, hc, ↓reduceDIte]
    exact congrArg Prod.fst hzv
  have hS := cS kx ky (1 / 2) hc
  rw [show kiDomain.comb (1 / 2) kx ky = kz from hkz.symm] at hS
  have hR := cR x.1.2.1 y.1.2.1 (1 / 2) hc
  have hL := cL x.1.2.2 y.1.2.2 (1 / 2) hc
  have hB : z.1.2.1 = convexBodyComb (1 / 2) x.1.2.1 y.1.2.1 := by
    exact congrArg (fun w => w.2.1) hzv
  have hD : z.1.2.2 = convexBodyComb (1 / 2) x.1.2.2 y.1.2.2 := by
    exact congrArg (fun w => w.2.2) hzv
  change mamikonS φ z.1.1.1 ≤
    (1 - 1 / 2) * mamikonS φ x.1.1.1 + (1 / 2) * mamikonS φ y.1.1.1 at hS
  change mamikonR φ (convexBodyComb (1 / 2) x.1.2.1 y.1.2.1).1 ≤
    (1 - 1 / 2) * mamikonR φ x.1.2.1.1 + (1 / 2) * mamikonR φ y.1.2.1.1 at hR
  change mamikonL φ (convexBodyComb (1 / 2) x.1.2.2 y.1.2.2).1 ≤
    (1 - 1 / 2) * mamikonL φ x.1.2.2.1 + (1 / 2) * mamikonL φ y.1.2.2.1 at hL
  rw [← hB] at hR
  rw [← hD] at hL
  constructor
  · change 0 ≤ 4 * ((mamikonS φ x.1.1.1 + mamikonS φ y.1.1.1) / 2 -
      mamikonS φ z.1.1.1)
    linarith
  constructor
  · change 0 ≤ 4 * ((mamikonR φ x.1.2.1.1 + mamikonR φ y.1.2.1.1) / 2 -
      mamikonR φ z.1.2.1.1)
    linarith
  · change 0 ≤ 4 * ((mamikonL φ x.1.2.2.1 + mamikonL φ y.1.2.2.1) / 2 -
      mamikonL φ z.1.2.2.1)
    linarith

/-- Exact decomposition of the quadratic energy of Q into its three groups. -/
theorem qEnergy_eq_sum {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) (x y : LTriple φ) :
    segmentEnergy (lDomain φ) (upperQL φ) x y =
      capMidpointEnergy x y + rightMidpointEnergy x y + leftMidpointEnergy x y := by
  have hc : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  let z := (lDomain φ).comb (1 / 2) x y
  let kx : KiSet := ⟨x.1.1, x.2.1⟩
  let ky : KiSet := ⟨y.1.1, y.2.1⟩
  let kz : KiSet := ⟨z.1.1, z.2.1⟩
  have hkz : kz = kiComb (1 / 2) kx ky := by
    apply Subtype.ext
    show z.1.1 = (kiComb (1 / 2) kx ky).1
    simp only [kiComb, hc, ↓reduceDIte]
    exact congrArg Prod.fst (triple_comb_val hc x y)
  have hLin := lemma8_3_7 hφ (1 / 2) hc kx ky
  rw [show kiDomain.comb (1 / 2) kx ky = kz from hkz.symm] at hLin
  change mamikonS φ z.1.1.1 - -upperP φ z.1.1.1 =
    (1 - 1 / 2) * (mamikonS φ x.1.1.1 - -upperP φ x.1.1.1) +
      (1 / 2) * (mamikonS φ y.1.1.1 - -upperP φ y.1.1.1) at hLin
  have hQ : ∀ w : LTriple φ,
      upperQL φ w = upperP φ w.1.1.1 - mamikonR φ w.1.2.1.1 -
        mamikonL φ w.1.2.2.1 := by
    intro w
    exact lemma8_3_4 hφ w.2
  change 4 * (upperQL φ z - (upperQL φ x + upperQL φ y) / 2) =
    4 * ((mamikonS φ x.1.1.1 + mamikonS φ y.1.1.1) / 2 - mamikonS φ z.1.1.1) +
    4 * ((mamikonR φ x.1.2.1.1 + mamikonR φ y.1.2.1.1) / 2 - mamikonR φ z.1.2.1.1) +
    4 * ((mamikonL φ x.1.2.2.1 + mamikonL φ y.1.2.2.1) / 2 - mamikonL φ z.1.2.2.1)
  rw [hQ z, hQ x, hQ y]
  linarith

theorem capEnergy_le_qEnergy {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (x y : LTriple φ) :
    capMidpointEnergy x y ≤ segmentEnergy (lDomain φ) (upperQL φ) x y := by
  obtain ⟨-, hR, hL⟩ := midpoint_energies_nonneg hφ x y
  rw [qEnergy_eq_sum hφ]
  linarith

/-- The reference value of the actual Q is the area of Gerver's sofa. -/
theorem gerver_upperQL_eq_area {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    upperQL P.φ (gerverTriple hP hbox) = area (gerverSofa P) := by
  change upperQ P.φ P.cap (rightBody P.φ P.cap) (leftBody P.φ P.cap) = _
  have h₁ := theorem8_4_6 hP hbox
  have h₂ := gm_sofaArea_cap hP hbox
  linarith

/-- Concrete quantitative strengthening of Baek's upper bound on LTriple. -/
theorem gerver_energy_le_deficit {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) (x : LTriple P.φ) :
    segmentEnergy (lDomain P.φ) (upperQL P.φ) (gerverTriple hP hbox) x ≤
      area (gerverSofa P) - upperQL P.φ x := by
  have h := segmentEnergy_le_deficit (lDomain P.φ)
    (proposition8_2_1 (gm_φ_mem_Ioo hP hbox)) (upperQL_le_gerver hP hbox) x
  rwa [gerver_upperQL_eq_area hP hbox] at h

/-- The cap part alone is controlled by the Q deficit; auxiliary null directions
are harmless for this estimate. -/
theorem gerver_capEnergy_le_deficit {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) (x : LTriple P.φ) :
    capMidpointEnergy (gerverTriple hP hbox) x ≤
      area (gerverSofa P) - upperQL P.φ x :=
  (capEnergy_le_qEnergy (gm_φ_mem_Ioo hP hbox) _ _).trans
    (gerver_energy_le_deficit hP hbox x)

/-- A genuine cap-area-deficit result, with Ki explicitly retained. -/
theorem ki_capEnergy_le_sofa_deficit {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {K : Set (ℝ × ℝ)} (hK : IsKi K) :
    capMidpointEnergy (gerverTriple hP hbox) (kiExtensionTriple hbox.1 hK) ≤
      area (gerverSofa P) - sofaArea (π / 2) K := by
  have h := gerver_capEnergy_le_deficit hP hbox (kiExtensionTriple hbox.1 hK)
  have hl : sofaArea (π / 2) K ≤ upperQL P.φ (kiExtensionTriple hbox.1 hK) :=
    theorem8_2_4 hbox.1 hK
  linarith

end MovingSofaStability
