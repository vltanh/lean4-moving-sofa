module

public import MovingSofa.Monotone.SupportingHallway

/-!
# Monotone sofas (§2.3)

Proposition 2.3.1 (`pro:standard-position-shape`, also Proposition 1.2.1), Theorem 2.3.2
(`thm:monotonization`), Propositions 2.3.3–2.3.4, Lemma 2.3.5 (`lem:cap-same-support-function`) and
Theorem 2.3.6 (`thm:monotonization-is-connected`).
-/

@[expose] public section

open Real Set

namespace MovingSofa

/-- **Proposition 2.3.1** (`pro:standard-position-shape`), existence: a moving sofa with rotation
angle `ω ∈ (0, π/2]` has a translation in standard position. -/
theorem proposition2_3_1_exists {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) :
    ∃ v : ℝ × ℝ, IsStandardPosition ((fun p => p + v) '' S) ω := by
  sorry

/-- **Proposition 2.3.1** (i): for `ω < π/2` the translation in standard position is unique. -/
theorem proposition2_3_1_unique {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioo 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) {v v' : ℝ × ℝ}
    (hv : IsStandardPosition ((fun p => p + v) '' S) ω)
    (hv' : IsStandardPosition ((fun p => p + v') '' S) ω) : v = v' := by
  sorry

/-- **Proposition 2.3.1** (ii): for `ω = π/2` it is unique up to horizontal translations. -/
theorem proposition2_3_1_unique_horizontal {S : Set (ℝ × ℝ)}
    (hS : IsMovingSofaWithAngle S (π / 2)) {v v' : ℝ × ℝ}
    (hv : IsStandardPosition ((fun p => p + v) '' S) (π / 2))
    (hv' : IsStandardPosition ((fun p => p + v') '' S) (π / 2)) : v.2 = v'.2 := by
  sorry

/-- **Proposition 2.3.1**, last claim: a moving sofa in standard position lies in `P_ω`. -/
theorem proposition2_3_1_subset {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) : S ⊆ para ω := by
  sorry

/-- **Proposition 2.3.3** (`pro:monotonization-contains-sofa`). `S ⊆ 𝓘(S)`. -/
theorem proposition2_3_3 {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) :
    S ⊆ monotonization S ω := by
  sorry

/-- **Proposition 2.3.4** (`pro:cap-contains-sofa`). `S ⊆ 𝓘(S) ⊆ 𝓒(S)`. -/
theorem proposition2_3_4 {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) :
    S ⊆ monotonization S ω ∧ monotonization S ω ⊆ capOf S ω := by
  sorry

/-- **Lemma 2.3.5** (`lem:cap-same-support-function`). The support functions of `S`, `𝓘(S)` and
`𝓒(S)` agree on `J_ω`. -/
theorem lemma2_3_5_supp {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) {t : ℝ} (ht : t ∈ jSet ω) :
    supp (monotonization S ω) t = supp S t ∧ supp (capOf S ω) t = supp S t := by
  sorry

/-- **Lemma 2.3.5**, consequence: the supporting hallways of `S`, `𝓘(S)` and `𝓒(S)` agree for
`t ∈ [0, ω]`. -/
theorem lemma2_3_5_hallway {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) {t : ℝ} (ht : t ∈ Icc 0 ω) :
    suppHallway (monotonization S ω) t = suppHallway S t ∧
      suppHallway (capOf S ω) t = suppHallway S t := by
  sorry

/-- **Theorem 2.3.6** (`thm:monotonization-is-connected`). `𝓘(S)` is connected. -/
theorem theorem2_3_6 {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) :
    IsConnected (monotonization S ω) := by
  sorry

/-- **Theorem 2.3.2** (`thm:monotonization`). For a moving sofa `S` with rotation angle
`ω ∈ (0, π/2]` in standard position, `𝓘(S)` is a moving sofa with the same rotation angle, in
standard position, containing `S`. -/
theorem theorem2_3_2 {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) :
    IsMovingSofaWithAngle (monotonization S ω) ω ∧ IsStandardPosition (monotonization S ω) ω ∧
      S ⊆ monotonization S ω := by
  sorry

end MovingSofa
