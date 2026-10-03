module

public import MovingSofa.Gerver.Envelope
public import Mathlib.Analysis.Convex.Topology

/-!
# Regular-closed cap complements without choosing an envelope inverse

The closed region below a compact nonnegative envelope is compact. A cap point
outside that closed region is approximable by interior points of the sofa.
An envelope point below height one can be moved slightly upward; a possible
unique height-one contact can instead be approached along the top edge.

This proves a general geometric lemma used to formalize paper note 07. It does
not assume that the competing sofa is regular closed. The concrete Gerver
hypotheses must still be supplied separately.

Uncompiled proof scripts; no admissions or external computation.
-/

@[expose] public section
noncomputable section

open Real Set MovingSofa

namespace SofaUniqueness

/-- The closed region under a compact nonnegative envelope is compact. -/
theorem isCompact_envUnder {Γ : Set (ℝ × ℝ)} (hΓ : IsCompact Γ)
    (hΓ0 : ∀ p ∈ Γ, 0 ≤ p.2) : IsCompact (envUnder Γ) := by
  let F : (ℝ × ℝ) × ℝ → ℝ × ℝ := fun q => (q.1.1, q.2 * q.1.2)
  have hF : Continuous F := by unfold F; fun_prop
  have he : envUnder Γ = F '' (Γ ×ˢ Icc (0 : ℝ) 1) := by
    ext p
    constructor
    · rintro ⟨hp0, γ, hγ, hγx, hpγ⟩
      by_cases hγ0 : γ.2 = 0
      · have hp2 : p.2 = 0 := by linarith
        refine ⟨(γ, 0), ⟨hγ, le_rfl, zero_le_one⟩, ?_⟩
        ext <;> simp [F, hγx, hp2]
      · have hγpos : 0 < γ.2 := lt_of_le_of_ne (hΓ0 γ hγ) (Ne.symm hγ0)
        refine ⟨(γ, p.2 / γ.2), ⟨hγ, div_nonneg hp0 hγpos.le,
          (div_le_one hγpos).mpr hpγ⟩, ?_⟩
        ext
        · exact hγx
        · exact div_mul_cancel₀ _ hγ0
    · rintro ⟨⟨γ, t⟩, ⟨hγ, ht0, ht1⟩, rfl⟩
      refine ⟨mul_nonneg ht0 (hΓ0 γ hγ), γ, hγ, rfl, ?_⟩
      dsimp [F]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ht1 (hΓ0 γ hγ)
  rw [he]
  exact (hΓ.prod isCompact_Icc).image hF

/-- Take the endpoint of a continuous path in a closed set, without a sequence
or a choice of inverse parameterization. -/
theorem mem_closed_of_positive_path {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) (q : ℝ → X) (hq : Continuous q)
    (hmem : ∀ t ∈ Ioo (0 : ℝ) 1, q t ∈ A) : q 0 ∈ A := by
  sorry

/-- Outside a closed excluded region, regular-closedness of the cap survives. -/
theorem outside_closed_envelope_subset {X : Type*} [TopologicalSpace X]
    {K U N : Set X} (hK : closure (interior K) = K) (hU : IsClosed U)
    (hNU : N ⊆ U) : K \ U ⊆ closure (interior (K \ N)) := by
  sorry

/-- Removing a strict niche under a compact envelope leaves a regular-closed
sofa, provided the cap contains the full top rectangle and the envelope has at
most one contact at height one.

No monotonicity or inverse parameterization of the envelope is required here.
The hypotheses apply to the envelope as a set of points, including its ends.
-/
theorem regularClosed_cap_sdiff_envelope {K Γ : Set (ℝ × ℝ)} {a b : ℝ}
    (hab : a < b) (hK : closure (interior K) = K)
    (hKstrip : ∀ p ∈ K, 0 ≤ p.2 ∧ p.2 ≤ 1)
    (hrect : ∀ x ∈ Icc a b, ∀ y ∈ Icc (0 : ℝ) 1, (x, y) ∈ K)
    (hΓ : IsCompact Γ)
    (hΓbounds : ∀ p ∈ Γ, p.1 ∈ Icc a b ∧ p.2 ∈ Icc (0 : ℝ) 1)
    (hΓtop : ∀ p ∈ Γ, ∀ q ∈ Γ, p.2 = 1 → q.2 = 1 → p = q)
    (hclosed : IsClosed (K \ envUnderStrict Γ)) :
    closure (interior (K \ envUnderStrict Γ)) = K \ envUnderStrict Γ := by
  sorry

end SofaUniqueness
