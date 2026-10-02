module

public import MovingSofa.Monotone.MonotoneSofa

/-!
# Cap and niche (§2.4)

Theorems 2.4.1 (`thm:cap-hallway-intersection`), 2.4.2 (`thm:monotonization-structure`), 2.4.3
(`thm:monotone-sofa-structure`) and 2.4.4 (`thm:monotonization-idempotent`).
-/

@[expose] public section

open Real Set

namespace MovingSofa

/-- **Theorem 2.4.1** (`thm:cap-hallway-intersection`). For a moving sofa `S` with rotation angle
`ω ∈ (0, π/2]` in standard position, `𝓒(S)` is a cap with rotation angle `ω`. -/
theorem theorem2_4_1 {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) : IsCap (capOf S ω) ω := by
  sorry

/-- **Theorem 2.4.2** (`thm:monotonization-structure`). `𝓘(S) = K \ 𝒩(K)` for the cap
`K = 𝓒(S)`. -/
theorem theorem2_4_2 {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) :
    monotonization S ω = capOf S ω \ niche (capOf S ω) ω := by
  sorry

/-- **Theorem 2.4.3** (`thm:monotone-sofa-structure`). A monotone sofa `S` with cap `K = 𝓒(S)` is
`K \ 𝒩(K)`. -/
theorem theorem2_4_3 {S : Set (ℝ × ℝ)} {ω : ℝ} (hS : IsMonotoneSofa S ω) :
    S = capOf S ω \ niche (capOf S ω) ω := by
  sorry

/-- **Theorem 2.4.4** (`thm:monotonization-idempotent`), first claim: `𝓘(𝓘(S')) = 𝓘(S')`. -/
theorem theorem2_4_4 {S' : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S' ω) (hstd : IsStandardPosition S' ω) :
    monotonization (monotonization S' ω) ω = monotonization S' ω := by
  sorry

/-- **Theorem 2.4.4**, second claim: a moving sofa `S` in standard position satisfies `S = 𝓘(S)` if
and only if it is a monotone sofa. -/
theorem theorem2_4_4_iff {S : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (hstd : IsStandardPosition S ω) :
    S = monotonization S ω ↔ IsMonotoneSofa S ω := by
  sorry

end MovingSofa
