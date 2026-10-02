module

public import MovingSofa.Main
public import MovingSofa.Convex.QuadraticEquality

/-!
# Equality conditions for the optimal sofa

This module begins the uniqueness argument, rather than asserting uniqueness of the shape.
A competing maximizer of `upperQL` has zero first variation at Gerver's triple, and every
Minkowski segment joining it to Gerver's triple saturates all three Mamikon convexity
inequalities separately. The final lemmas apply these conditions to caps in `𝒦^i` that attain
Gerver's sofa area.

What remains is geometric rigidity of these equality cases, modulo the relevant rigid
motions, and equality in the reductions from arbitrary moving sofas to caps. In particular,
uniqueness of Romik's parameters is not uniqueness of all area-maximizing moving sofas.
-/

@[expose] public section

open Real Set MeasureTheory

namespace MovingSofa

open GerverParams

/-- Equality in each of the three convexity inequalities used to prove concavity of `upperQL`.
The cap and the two auxiliary bodies are kept separate so no cancellation can hide a gap. -/
structure MamikonSegmentEquality (φ : ℝ) (x y : LTriple φ) (c : ℝ) : Prop where
  middle : mamikonS φ ((lDomain φ).comb c x y).1.1.1 =
    (1 - c) * mamikonS φ x.1.1.1 + c * mamikonS φ y.1.1.1
  right : mamikonR φ ((lDomain φ).comb c x y).1.2.1.1 =
    (1 - c) * mamikonR φ x.1.2.1.1 + c * mamikonR φ y.1.2.1.1
  left : mamikonL φ ((lDomain φ).comb c x y).1.2.2.1 =
    (1 - c) * mamikonL φ x.1.2.2.1 + c * mamikonL φ y.1.2.2.1

/-- If two triples maximize `upperQL`, the three Mamikon convexity gaps vanish individually
along their entire segment. This is the equality case of the proof of Theorem 8.3.8. -/
theorem mamikonSegmentEquality_of_isMax {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {x y : LTriple φ} (hmax : ∀ z, upperQL φ z ≤ upperQL φ x)
    (hxy : upperQL φ y = upperQL φ x) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    MamikonSegmentEquality φ x y c := by
  obtain ⟨-, cS, -, cR, -, cL⟩ := lemma8_3_3 hφ
  have hLin := lemma8_3_7 hφ
  set z := (lDomain φ).comb c x y with hz
  have hzv : z.1 = (convexBodyComb c x.1.1 y.1.1, convexBodyComb c x.1.2.1 y.1.2.1,
      convexBodyComb c x.1.2.2 y.1.2.2) := by
    simp only [hz, lDomain, LTriple.comb, hc, ↓reduceDIte]
  set kx : KiSet := ⟨x.1.1, x.2.1⟩
  set ky : KiSet := ⟨y.1.1, y.2.1⟩
  set kz : KiSet := ⟨z.1.1, z.2.1⟩
  have hkz : kz = kiComb c kx ky := by
    apply Subtype.ext
    show z.1.1 = (kiComb c kx ky).1
    simp only [kiComb, hc, ↓reduceDIte]
    rw [hzv]
  have hQ : ∀ w : LTriple φ, upperQL φ w = (mamikonS φ w.1.1.1 - -upperP φ w.1.1.1) -
      mamikonS φ w.1.1.1 - mamikonR φ w.1.2.1.1 - mamikonL φ w.1.2.2.1 := by
    intro w
    simp only [upperQL]
    rw [lemma8_3_4 hφ w.2]
    ring
  have hB : z.1.2.1 = convexBodyComb c x.1.2.1 y.1.2.1 := by rw [hzv]
  have hD : z.1.2.2 = convexBodyComb c x.1.2.2 y.1.2.2 := by rw [hzv]
  have e1 : mamikonS φ z.1.1.1 - -upperP φ z.1.1.1 =
      (1 - c) * (mamikonS φ x.1.1.1 - -upperP φ x.1.1.1) +
        c * (mamikonS φ y.1.1.1 - -upperP φ y.1.1.1) := by
    have h := hLin c hc kx ky
    rw [show kiDomain.comb c kx ky = kz from hkz.symm] at h
    exact h
  have e2 : mamikonS φ z.1.1.1 ≤
      (1 - c) * mamikonS φ x.1.1.1 + c * mamikonS φ y.1.1.1 := by
    have h := cS kx ky c hc
    rw [show kiDomain.comb c kx ky = kz from hkz.symm] at h
    exact h
  have e3 : mamikonR φ z.1.2.1.1 ≤
      (1 - c) * mamikonR φ x.1.2.1.1 + c * mamikonR φ y.1.2.1.1 := by
    rw [hB]
    exact cR x.1.2.1 y.1.2.1 c hc
  have e4 : mamikonL φ z.1.2.2.1 ≤
      (1 - c) * mamikonL φ x.1.2.2.1 + c * mamikonL φ y.1.2.2.1 := by
    rw [hD]
    exact cL x.1.2.2 y.1.2.2 c hc
  have hflat : upperQL φ z = (1 - c) * upperQL φ x + c * upperQL φ y := by
    have h := (lDomain φ).eq_on_segment_of_isMax (theorem8_3_8 hφ) hmax hxy hc
    change upperQL φ z = upperQL φ x at h
    rw [h, hxy]
    ring
  rw [hQ, hQ, hQ] at hflat
  change MamikonSegmentEquality φ x y c
  constructor
  · change mamikonS φ z.1.1.1 = _
    linarith
  · change mamikonR φ z.1.2.1.1 = _
    linarith
  · change mamikonL φ z.1.2.2.1 = _
    linarith

/-- Corollary 8.5.8 in the bundled-triple vocabulary. -/
theorem upperQL_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : LTriple P.φ) : upperQL P.φ x ≤ upperQL P.φ (gerverTriple hP hbox) :=
  corollary8_5_8 hP hbox x.2

/-- Any other maximizing triple is joined to Gerver's triple by an entire segment of
maximizers. This does not identify the two triples. -/
theorem upperQL_eq_gerver_on_segment {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {x : LTriple P.φ} (hx : upperQL P.φ x = upperQL P.φ (gerverTriple hP hbox))
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    upperQL P.φ ((lDomain P.φ).comb c (gerverTriple hP hbox) x) =
      upperQL P.φ (gerverTriple hP hbox) :=
  (lDomain P.φ).eq_on_segment_of_isMax (theorem8_3_8 (gm_φ_mem_Ioo hP hbox))
    (upperQL_le_gerver hP hbox) hx hc

/-- Equality in the optimal upper bound forces zero first variation at Gerver's triple. -/
theorem gerver_dirDeriv_eq_zero_of_upperQL_eq {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {x : LTriple P.φ}
    (hx : upperQL P.φ x = upperQL P.φ (gerverTriple hP hbox)) :
    (lDomain P.φ).dirDeriv (upperQL P.φ) (gerverTriple hP hbox) x = 0 :=
  (lDomain P.φ).dirDeriv_eq_zero_of_isMax (proposition8_2_1 (gm_φ_mem_Ioo hP hbox))
    (theorem8_3_8 (gm_φ_mem_Ioo hP hbox)) (upperQL_le_gerver hP hbox) hx

/-- Every competitor attaining Gerver's upper bound saturates the three Mamikon convexity
inequalities separately, for every combination parameter in `[0, 1]`. -/
theorem gerver_mamikonSegmentEquality {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {x : LTriple P.φ} (hx : upperQL P.φ x = upperQL P.φ (gerverTriple hP hbox))
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    MamikonSegmentEquality P.φ (gerverTriple hP hbox) x c :=
  mamikonSegmentEquality_of_isMax (gm_φ_mem_Ioo hP hbox) (upperQL_le_gerver hP hbox) hx hc

/-- The canonical extension of a cap in `𝒦^i` to a triple in `𝓛`. -/
noncomputable def kiExtensionTriple {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04)
    {K : Set (ℝ × ℝ)} (hK : IsKi K) : LTriple φ :=
  ⟨(⟨K, hK.1.2.1⟩, ⟨rightBody φ K, (theorem8_1_8 hφ hK).2.1⟩,
    ⟨leftBody φ K, (theorem8_1_8 hφ hK).2.2.1⟩), theorem8_1_8 hφ hK⟩

/-- If the sofa-area functional of a cap in `𝒦^i` attains Gerver's area, its canonical triple
attains Gerver's upper bound. This records equality in both bounding steps, rather than
assuming equality for the auxiliary functional. -/
theorem ki_upperQL_eq_gerver_of_sofaArea_eq {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {K : Set (ℝ × ℝ)} (hK : IsKi K)
    (harea : sofaArea (π / 2) K = area (gerverSofa P)) :
    upperQL P.φ (kiExtensionTriple hbox.1 hK) = upperQL P.φ (gerverTriple hP hbox) := by
  change upperQ P.φ K (rightBody P.φ K) (leftBody P.φ K) =
    upperQ P.φ P.cap (rightBody P.φ P.cap) (leftBody P.φ P.cap)
  have hLower := theorem8_2_4 hbox.1 hK
  have hUpper := corollary8_5_8 hP hbox (theorem8_1_8 hbox.1 hK)
  have hG := theorem8_4_6 hP hbox
  have hGarea := gm_sofaArea_cap hP hbox
  linarith

/-- Necessary equality conditions for an area-maximizing cap in `𝒦^i`. Geometric rigidity
and the passage back to the original moving sofa remain separate proof obligations. -/
theorem ki_maximizer_equality_conditions {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {K : Set (ℝ × ℝ)} (hK : IsKi K)
    (harea : sofaArea (π / 2) K = area (gerverSofa P)) :
    (lDomain P.φ).dirDeriv (upperQL P.φ) (gerverTriple hP hbox)
        (kiExtensionTriple hbox.1 hK) = 0 ∧
      ∀ c ∈ Icc (0 : ℝ) 1,
        MamikonSegmentEquality P.φ (gerverTriple hP hbox) (kiExtensionTriple hbox.1 hK) c := by
  have hx := ki_upperQL_eq_gerver_of_sofaArea_eq hP hbox hK harea
  exact ⟨gerver_dirDeriv_eq_zero_of_upperQL_eq hP hbox hx,
    fun _ hc => gerver_mamikonSegmentEquality hP hbox hx hc⟩

end MovingSofa
