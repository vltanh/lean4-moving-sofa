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
hypotheses are supplied in `GerverRegularClosed`.
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
  have hsub : Ioo (0 : ℝ) 1 ⊆ q ⁻¹' A := fun t ht => hmem t ht
  have h := closure_minimal hsub (hA.preimage hq)
  apply h
  rw [closure_Ioo zero_ne_one]
  exact ⟨le_rfl, zero_le_one⟩

/-- Outside a closed excluded region, regular-closedness of the cap survives. -/
theorem outside_closed_envelope_subset {X : Type*} [TopologicalSpace X]
    {K U N : Set X} (hK : closure (interior K) = K) (hU : IsClosed U)
    (hNU : N ⊆ U) : K \ U ⊆ closure (interior (K \ N)) := by
  intro p hp
  have hnear : p ∈ Uᶜ ∩ closure (interior K) := by
    exact ⟨hp.2, by rw [hK]; exact hp.1⟩
  have hcl : p ∈ closure (Uᶜ ∩ interior K) := hU.isOpen_compl.inter_closure hnear
  have hsub : Uᶜ ∩ interior K ⊆ interior (K \ N) := by
    apply interior_maximal
    · intro q hq
      exact ⟨interior_subset hq.2, fun hqN => hq.1 (hNU hqN)⟩
    · exact hU.isOpen_compl.inter isOpen_interior
  exact closure_mono hsub hcl

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
  let C := closure (interior (K \ envUnderStrict Γ))
  have hCclosed : IsClosed C := isClosed_closure
  have hUclosed : IsClosed (envUnder Γ) :=
    (isCompact_envUnder hΓ (fun p hp => (hΓbounds p hp).2.1)).isClosed
  have hNU : envUnderStrict Γ ⊆ envUnder Γ := by
    rintro p ⟨hp0, γ, hγ, hγx, hpγ⟩
    exact ⟨hp0, γ, hγ, hγx, hpγ.le⟩
  have hout : K \ envUnder Γ ⊆ C :=
    outside_closed_envelope_subset hK hUclosed hNU
  apply Set.Subset.antisymm (closure_minimal interior_subset hclosed)
  intro p hp
  by_cases hpU : p ∈ envUnder Γ
  · obtain ⟨hp0, γ, hγ, hγx, hpγ⟩ := hpU
    have hpI : p.1 ∈ Icc a b := by rw [← hγx]; exact (hΓbounds γ hγ).1
    obtain ⟨hpy0, hpy1⟩ := hKstrip p hp.1
    rcases lt_or_eq_of_le hpy1 with hplt | hpone
    · let q : ℝ → ℝ × ℝ := fun t => (p.1, (1 - t) * p.2 + t)
      have hq : Continuous q := by unfold q; fun_prop
      have hmem : ∀ t ∈ Ioo (0 : ℝ) 1, q t ∈ C := by
        intro t ht
        have hygt : p.2 < (q t).2 := by
          dsimp [q]; nlinarith [mul_pos ht.1 (sub_pos.mpr hplt)]
        have hylo : 0 ≤ (q t).2 := hpy0.trans hygt.le
        have hyhi : (q t).2 ≤ 1 := by
          dsimp [q]; nlinarith [mul_nonneg (sub_nonneg.mpr ht.2.le) (sub_nonneg.mpr hpy1)]
        apply hout
        refine ⟨hrect _ hpI _ ⟨hylo, hyhi⟩, ?_⟩
        rintro ⟨_, δ, hδ, hδx, hqδ⟩
        apply hp.2
        exact ⟨hpy0, δ, hδ, hδx, hygt.trans_le hqδ⟩
      have h := mem_closed_of_positive_path hCclosed q hq hmem
      simpa [q] using h
    · have hγone : γ.2 = 1 := le_antisymm (hΓbounds γ hγ).2.2 (by linarith)
      have hγp : γ = p := by
        apply Prod.ext hγx
        exact hγone.trans hpone.symm
      have hpΓ : p ∈ Γ := hγp ▸ hγ
      obtain ⟨v, hv, hvne⟩ : ∃ v ∈ Icc a b, v ≠ p.1 := by
        by_cases ha : a = p.1
        · exact ⟨b, ⟨hab.le, le_rfl⟩, by rw [← ha]; exact ne_of_gt hab⟩
        · exact ⟨a, ⟨le_rfl, hab.le⟩, ha⟩
      let q : ℝ → ℝ × ℝ := fun t => ((1 - t) * p.1 + t * v, 1)
      have hq : Continuous q := by unfold q; fun_prop
      have hmem : ∀ t ∈ Ioo (0 : ℝ) 1, q t ∈ C := by
        intro t ht
        have h1t : 0 ≤ 1 - t := by linarith [ht.2]
        have hxlo : a ≤ (q t).1 := by
          calc
            a = (1 - t) * a + t * a := by ring
            _ ≤ (1 - t) * p.1 + t * v :=
              add_le_add (mul_le_mul_of_nonneg_left hpI.1 h1t)
                (mul_le_mul_of_nonneg_left hv.1 ht.1.le)
        have hxhi : (q t).1 ≤ b := by
          calc
            (1 - t) * p.1 + t * v ≤ (1 - t) * b + t * b :=
              add_le_add (mul_le_mul_of_nonneg_left hpI.2 h1t)
                (mul_le_mul_of_nonneg_left hv.2 ht.1.le)
            _ = b := by ring
        apply hout
        refine ⟨hrect _ ⟨hxlo, hxhi⟩ 1 ⟨zero_le_one, le_rfl⟩, ?_⟩
        rintro ⟨_, δ, hδ, hδx, hqδ⟩
        have hδone : δ.2 = 1 := le_antisymm (hΓbounds δ hδ).2.2 hqδ
        have hδp := hΓtop δ hδ p hpΓ hδone hpone
        have hx : (1 - t) * p.1 + t * v = p.1 := by
          calc
            _ = δ.1 := hδx.symm
            _ = p.1 := congrArg Prod.fst hδp
        have hprod : t * (v - p.1) = 0 := by nlinarith
        exact hvne (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left ht.1.ne'))
      have h := mem_closed_of_positive_path hCclosed q hq hmem
      have hq0 : q 0 = p := by
        ext
        · simp [q]
        · simp [q, hpone]
      rw [hq0] at h
      exact h
  · exact hout ⟨hp.1, hpU⟩

end SofaUniqueness
