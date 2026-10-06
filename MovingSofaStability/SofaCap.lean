module

public import MovingSofaStability.SofaCoordinates

/-!
# A full-angle cap without extending the sofa's motion

Uncompiled proof source. The downward completion contains the normalized
original set and preserves all upper supports. The actual set need not be
convex and need not admit a full-angle movement.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness
open GerverParams

namespace MovingSofaStability

def sofaCap (S : Set Point) : Set Point :=
  {p | 0 ≤ p.2 ∧ ∀ t ∈ Icc (0 : ℝ) π, dot p (uvec t) ≤ supp S t}

@[simp] theorem sofaCap_mem (S : Set Point) (p : Point) :
    p ∈ sofaCap S ↔ 0 ≤ p.2 ∧ ∀ t ∈ Icc (0 : ℝ) π, dot p (uvec t) ≤ supp S t := Iff.rfl

theorem subset_sofaCap {S : Set Point} (hS : IsCompact S) (hstrip : S ⊆ hStrip) : S ⊆ sofaCap S :=
  fun p hp => ⟨(hstrip hp).1, fun t ht => dot_le_supp hS hp t⟩

theorem sofaCap_down {S : Set Point} {p : Point} (hp : p ∈ sofaCap S)
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ p.2) : (p.1, y) ∈ sofaCap S := by
  refine ⟨hy0, ?_⟩
  intro t ht
  have he := hp.2 t ht
  have hs := sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2
  simp only [dot, uvec] at he ⊢
  nlinarith

theorem sofaCap_closed (S : Set Point) : IsClosed (sofaCap S) := by
  have he : sofaCap S = halfPlus (π / 2) 0 ∩ ⋂ t ∈ Icc (0 : ℝ) π, halfMinus t (supp S t) := by
    ext p
    simp only [sofaCap, halfPlus, halfMinus, mem_inter_iff, mem_iInter,
      mem_setOf_eq, dot_uvec_pi_div_two]
  rw [he]
  exact (isClosed_halfPlus _ _).inter (isClosed_biInter fun t ht => isClosed_halfMinus _ _)

theorem sofaCap_convex (S : Set Point) : Convex ℝ (sofaCap S) := by
  intro p hp q hq a b ha hb hab
  refine ⟨by simpa only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] using
    add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1), ?_⟩
  intro t ht
  have h1 := mul_le_mul_of_nonneg_left (hp.2 t ht) ha
  have h2 := mul_le_mul_of_nonneg_left (hq.2 t ht) hb
  have h3 : a * supp S t + b * supp S t = supp S t := by rw [← add_mul, hab, one_mul]
  rw [dot_add_left, dot_smul_left, dot_smul_left]
  linarith

theorem sofaCap_compact {S : Set Point} (htop : supp S (π / 2) = 1) : IsCompact (sofaCap S) := by
  have hb : IsCompact (Icc (-supp S π) (supp S 0) ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  apply hb.of_isClosed_subset (sofaCap_closed S)
  intro p hp
  have h0 := hp.2 0 ⟨le_rfl, pi_pos.le⟩
  have hπ := hp.2 π ⟨pi_pos.le, le_rfl⟩
  have hv := hp.2 (π / 2) ⟨by positivity, by linarith [pi_pos]⟩
  rw [dot_uvec_zero] at h0
  simp only [dot, uvec_pi] at hπ
  rw [dot_uvec_pi_div_two, htop] at hv
  exact ⟨⟨by linarith, h0⟩, hp.1, hv⟩

theorem sofaCap_upper_support {S : Set Point} (hS : IsCompact S) (hne : S.Nonempty)
    (hstrip : S ⊆ hStrip) (htop : supp S (π / 2) = 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) π) : supp (sofaCap S) t = supp S t := by
  have hsub := subset_sofaCap hS hstrip
  exact le_antisymm (supp_le_of_forall (hne.mono hsub) (fun p hp => hp.2 t ht))
    (supp_mono hsub hne (sofaCap_compact htop) t)

theorem sofaCap_isCap {S : Set Point} (hS : IsCompact S) (hne : S.Nonempty)
    (hstrip : S ⊆ hStrip) (htop : supp S (π / 2) = 1) : IsCap (sofaCap S) (π / 2) := by
  have hsub := subset_sofaCap hS hstrip
  have hcpt := sofaCap_compact htop
  have hneC := hne.mono hsub
  have htopC : supp (sofaCap S) (π / 2) = 1 :=
    (sofaCap_upper_support hS hne hstrip htop ⟨by positivity, by linarith [pi_pos]⟩).trans htop
  obtain ⟨p, hp⟩ := id hneC
  have hfloor : (p.1, 0) ∈ sofaCap S := sofaCap_down hp le_rfl hp.1
  have hbottom : supp (sofaCap S) (3 * π / 2) = 0 := by
    apply le_antisymm
    · apply supp_le_of_forall hneC
      intro q hq
      rw [dot_uvec_three_pi_div_two]
      linarith [hq.1]
    · have he := dot_le_supp hcpt hfloor (3 * π / 2)
      simpa only [dot_uvec_three_pi_div_two, neg_zero] using he
  refine ⟨⟨by positivity, le_rfl⟩, ⟨hneC, hcpt, sofaCap_convex S⟩,
    htopC, htopC, ?_, hbottom, ?_⟩
  · simpa only [show π / 2 + π = 3 * π / 2 by ring] using hbottom
  · let I := ↥(Icc (0 : ℝ) π)
    refine ⟨Option I, (fun i => i.elim (3 * π / 2) Subtype.val),
      (fun i => i.elim 0 (fun t => supp S t.1)), ?_, ?_⟩
    · intro i
      cases i with
      | none => exact Or.inr (by simp)
      | some t =>
        apply Or.inl
        by_cases ht : t.1 ≤ π / 2
        · exact Or.inl ⟨t.2.1, ht⟩
        · exact Or.inr ⟨(not_le.mp ht).le, show t.1 ≤ π / 2 + π / 2 by linarith [t.2.2]⟩
    · ext q
      simp only [mem_iInter]
      constructor
      · intro h i
        cases i with
        | none => simpa only [Option.elim_none, halfMinus, mem_ofPred_eq,
            dot_uvec_three_pi_div_two, neg_nonpos] using h.1
        | some t => exact h.2 t.1 t.2
      · intro h
        have hf := h none
        have hf' : 0 ≤ q.2 := by
          simpa only [Option.elim_none, halfMinus, mem_ofPred_eq,
            dot_uvec_three_pi_div_two, neg_nonpos] using hf
        exact ⟨hf', fun t ht => h (some ⟨t, ht⟩)⟩

@[simp] theorem sofaCap_of_cap {K : Set Point} (hK : IsCap K (π / 2)) : sofaCap K = K := by
  ext p
  exact (cap_mem_iff_upper hK p).symm

theorem sofaCap_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    sofaCap (gerverSofa P) = P.cap := by
  ext p
  rw [cap_mem_iff_upper (gm_isCap hP hbox)]
  constructor
  · intro hp
    refine ⟨hp.1, ?_⟩
    intro t ht
    rw [gerver_upper_support hP hbox ht]
    exact hp.2 t ht
  · intro hp
    refine ⟨hp.1, ?_⟩
    intro t ht
    rw [← gerver_upper_support hP hbox ht]
    exact hp.2 t ht

theorem sofaCap_close_to_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Point} (hS : IsCompact S) (hne : S.Nonempty) (hstrip : S ⊆ hStrip)
    (htop : supp S (π / 2) = 1) {δ : ℝ} (hclose : EuclideanClose δ S (gerverSofa P)) :
    UpperSupportClose δ (sofaCap S) P.cap := by
  intro t ht
  rw [sofaCap_upper_support hS hne hstrip htop ht, gerver_upper_support hP hbox ht]
  have hG := (gm_movingSofa_std hP hbox).1
  exact hclose.abs_supp_sub_le hS (ms_isCompact_of_isMovingSofaWithAngle hG) hne hG.2.1.nonempty t

theorem sofaCap_partial_constraints {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) (hω : ω ∈ Icc (0 : ℝ) (π / 2))
    (htop : supp S (π / 2) = 1) : PartialSofaConstraints (sofaCap S) S ω := by
  have hcpt := ms_isCompact_of_isMovingSofaWithAngle hS
  have hne := hS.2.1.nonempty
  have hstrip := moving_strip_of_top ⟨ω, hS⟩ htop
  have hs : ∀ {t : ℝ}, t ∈ Icc (0 : ℝ) π → supp (sofaCap S) t = supp S t :=
    sofaCap_upper_support hcpt hne hstrip htop
  refine ⟨subset_sofaCap hcpt hstrip, ?_, ?_⟩
  · intro p hp t ht
    have h0 := moving_hallway_slacks hS hp ht
    have h1 := hs ⟨ht.1, ht.2.trans (hω.2.trans (by linarith [pi_pos]))⟩
    have h2 := hs (t := t + π / 2) ⟨by linarith [ht.1, pi_pos], by linarith [ht.2, hω.2]⟩
    simpa only [innerSlackU, innerSlackV, h1, h2] using h0
  · intro p hp
    rw [hs ⟨hω.1, by linarith [hω.2, pi_pos]⟩]
    exact moving_terminal_lower hS hp

end MovingSofaStability
