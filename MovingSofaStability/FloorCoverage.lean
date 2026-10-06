module

public import MovingSofaStability.LocalUpperBound

/-!
# The interior niche floor is already removed before the terminal angle

Uncompiled proof source. A directed compact-cover argument supplies a uniform
strict slack and an angle bounded away from pi/2. The fixed floor interval is
chosen first; no unsupported rate of compactness is used.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaUniqueness
open GerverParams

namespace MovingSofaStability

/-- Gerver's roof has positive height at every abscissa strictly between its endpoints. -/
theorem gerver_floor_mem_niche {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {x : ℝ} (hx : x ∈ Ioo (gerverRoofLeft P) (gerverRoofRight P)) :
    (x, 0) ∈ niche P.cap (π / 2) := by
  sorry

/-- Compact sets of floor points in the reference niche have uniform strict
witnesses whose angles stay away from both endpoints. -/
theorem compact_floor_witnesses {K₀ : Set Point} {I : Set ℝ} (hI : IsCompact I)
    (hfloor : ∀ x ∈ I, (x, 0) ∈ niche K₀ (π / 2)) :
    ∃ e : ℝ, 0 < e ∧ ∀ x ∈ I, ∃ t ∈ Ioo e (π / 2 - e),
      innerSlackU K₀ t (x, 0) < -e ∧ innerSlackV K₀ t (x, 0) < -e := by
  sorry

/-- A fixed interior floor slab is removed by angles uniformly below pi/2,
even after a sufficiently small perturbation of the cap support. -/
theorem gerver_floor_slab_covered {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {l r : ℝ} (hl : gerverRoofLeft P < l) (hr : r < gerverRoofRight P) :
    ∃ e δ : ℝ, 0 < e ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ K : Set Point, UpperSupportClose δ K P.cap →
      ∀ p ∈ Icc l r ×ˢ Icc (0 : ℝ) δ,
        ∃ t ∈ Ioo (0 : ℝ) (π / 2 - e),
          innerSlackU K t p < 0 ∧ innerSlackV K t p < 0 := by
  obtain ⟨e, he, hw⟩ := compact_floor_witnesses isCompact_Icc
    (fun x hx => gerver_floor_mem_niche hP hbox ⟨hl.trans_le hx.1, hx.2.trans_lt hr⟩)
  let δ := min 1 (e / 4)
  have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδe : δ ≤ e / 4 := min_le_right _ _
  refine ⟨e, δ, he, hδ, min_le_left _ _, ?_⟩
  intro K hclose p hp
  obtain ⟨t, ht, hU, hV⟩ := hw p.1 hp.1
  have htv : t ∈ Ioo (0 : ℝ) (π / 2) := ⟨he.trans ht.1, by linarith [ht.2]⟩
  have hs1 := (abs_le.mp (hclose t ⟨htv.1.le, by linarith [htv.2, pi_pos]⟩)).1
  have hs2 := (abs_le.mp (hclose (t + π / 2) ⟨by linarith [htv.1, pi_pos], by linarith [htv.2]⟩)).1
  have hu : p.2 * sin t ≤ δ := (mul_le_mul_of_nonneg_left (sin_le_one t) hp.2.1).trans
    (by simpa only [mul_one] using hp.2.2)
  have hv : p.2 * cos t ≤ δ := (mul_le_mul_of_nonneg_left (cos_le_one t) hp.2.1).trans
    (by simpa only [mul_one] using hp.2.2)
  refine ⟨t, ⟨htv.1, ht.2⟩, ?_, ?_⟩
  · simp only [innerSlackU, dot, uvec] at hU ⊢
    nlinarith
  · simp only [innerSlackV, dot, vvec] at hV ⊢
    nlinarith

end MovingSofaStability
