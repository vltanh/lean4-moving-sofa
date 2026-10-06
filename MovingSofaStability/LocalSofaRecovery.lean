module

public import MovingSofaStability.SofaCap

/-!
# Local quantitative recovery of the actual sofa

Uncompiled proof source. All cap, terminal, erosion and reference-roof
hypotheses are assembled here. Only entry into a fixed neighborhood remains
for the global step. The smaller sofa need not be contained in its full-angle
shape, and the conclusion concerns its actual nonconvex points.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- A single explicit threshold controls a fixed coefficient times sqrt epsilon. -/
theorem exists_sqrt_threshold {A r : ℝ} (hA : 0 ≤ A) (hr : 0 < r) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ → A * sqrt ε < r := by
  let q := r / (A + 1)
  have hq : 0 < q := div_pos hr (by linarith)
  let ε₀ := min 1 (q ^ 2)
  have he : 0 < ε₀ := lt_min (by norm_num) (sq_pos_of_pos hq)
  refine ⟨ε₀, he, min_le_left _ _, ?_⟩
  intro ε hε hsmall
  have hsq := sq_sqrt hε
  have hs := sqrt_nonneg ε
  have hεq : ε < q ^ 2 := hsmall.trans_le (min_le_right _ _)
  have hslt : sqrt ε < q := by nlinarith
  have hqr : (A + 1) * q = r := by dsimp [q]; field_simp
  have hm := mul_le_mul_of_nonneg_left hslt.le hA
  nlinarith

theorem self_le_sqrt_of_unit {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) 1) : ε ≤ sqrt ε := by
  have hs := sqrt_nonneg ε
  have hsq := sq_sqrt hε.1
  have hs1 : sqrt ε ≤ 1 := by nlinarith [hε.2]
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hs1)]

/-- The local unrestricted rate, with the cap and terminal constraints explicitly
constructed elsewhere. No smoothness or injectivity of K is assumed. -/
theorem local_positive_sofa_hausdorff {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ C c δ α₀ ε₀ : ℝ,
      0 < C ∧ 0 < c ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < α₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ∀ K : Set Point, IsCap K (π / 2) → supp K π = supp P.cap π →
      UpperSupportClose δ K P.cap → ∀ S : Set Point, MeasurableSet S →
      ∀ ω ∈ Icc (0 : ℝ) (π / 2), π / 2 - ω ≤ α₀ → PartialSofaConstraints K S ω →
      ∀ ε : ℝ, ε = area (gerverSofa P) - area S → 0 < ε → ε < ε₀ →
        EuclideanClose (C * sqrt ε) S (gerverSofa P) ∧ π / 2 - ω ≤ ε / c := by
  obtain ⟨c, δT, α₀, R, hc, hδT, hδT1, hα₀, hR, hterminal⟩ := nearby_terminal_comparison hP hbox
  obtain ⟨δK, hδK, hδK1, hcapestimate⟩ := nearby_cap_distance hP hbox
  obtain ⟨H, L, γ, cr, τ, d₀, κ, r₀, hroof, hcr, hτ, hd₀, hκ, hr₀,
    hslack, houter, hballs⟩ := gerver_recovery_constants hP hbox
  let B := 4 * R / c
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let Cf := max 1 (1 / cr) * (80 + B)
  let Cb := 4 * (160 + 1) / κ
  let C := max 1 (max Cf Cb)
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hCb : 0 ≤ Cb := by dsimp [Cb]; positivity
  obtain ⟨εd, hεd, hεd1, hsmallD⟩ := exists_sqrt_threshold (A := 80) (by norm_num) hd₀
  obtain ⟨εt, hεt, hεt1, hsmallT⟩ := exists_sqrt_threshold (A := 80 + B) (by linarith) hτ
  obtain ⟨εr, hεr, hεr1, hsmallR⟩ := exists_sqrt_threshold hCb hr₀
  let ε₀ := min εd (min εt εr)
  let δ := min δT δK
  have hε₀ : 0 < ε₀ := lt_min hεd (lt_min hεt hεr)
  have hδ : 0 < δ := lt_min hδT hδK
  have dT : δ ≤ δT := min_le_left _ _
  have dK : δ ≤ δK := min_le_right _ _
  have ed : ε₀ ≤ εd := min_le_left _ _
  have et : ε₀ ≤ εt := (min_le_right _ _).trans (min_le_left _ _)
  have er : ε₀ ≤ εr := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨C, c, δ, α₀, ε₀, hC, hc, hδ, dT.trans hδT1, hα₀, hε₀, ed.trans hεd1, ?_⟩
  intro K hK hleft hclose S hS ω hω hα hconstraints ε hεeq hε hεsmall
  obtain ⟨hloss, hangle, hdeficit, hSU, hUS, hhall⟩ :=
    hterminal K hK (hclose.mono dT) S hS ω hω hα hconstraints
  rw [← hεeq] at hangle hdeficit hSU hUS
  obtain ⟨hNK, hAM, hdist⟩ := hcapestimate K hK (hclose.mono dK)
  rw [shiftedReferenceCap_eq_of_left_support hleft] at hdist
  have hdist' : EuclideanClose (80 * sqrt ε) K P.cap := hdist.mono
    (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hdeficit) (by norm_num))
  have hsupport : UpperSupportClose (80 * sqrt ε) K P.cap :=
    fun t ht => hdist'.abs_supp_sub_le hK.2.1.2.1 hroof.cap.2.1.2.1 hK.2.1.1 hroof.cap.2.1.1 t
  have hε1 : ε ≤ 1 := hεsmall.le.trans (ed.trans hεd1)
  have hεsqrt := self_le_sqrt_of_unit ⟨hε.le, hε1⟩
  have hζ : 4 * R * (π / 2 - ω) ≤ B * sqrt ε := by
    have he := mul_le_mul_of_nonneg_left hangle (show 0 ≤ 4 * R by linarith)
    have he' := mul_le_mul_of_nonneg_left hεsqrt hB
    dsimp [B] at *
    nlinarith [show 4 * R * (ε / c) = (4 * R / c) * ε by ring]
  have hhall' : ApproxHallways K S (B * sqrt ε) := by
    intro p hp t ht
    exact (neg_le_neg hζ).trans (hhall p hp t ht)
  have hsmall1 := hsmallD ε hε.le (hεsmall.trans_le ed)
  have hsmall2 : 80 * sqrt ε + B * sqrt ε < τ := by
    have he := hsmallT ε hε.le (hεsmall.trans_le et)
    nlinarith
  have hfront := directed_to_reference_of_margins hroof hK hcr
    (show 0 ≤ 80 * sqrt ε by positivity) (mul_nonneg hB (sqrt_nonneg ε))
    hsupport houter hsmall1 hsmall2 hslack hconstraints.1 hhall'
  rw [gerver_shape_eq hP hbox] at hfront
  have hback := reference_to_sofa_recovery hroof.cap hK
    (show 0 ≤ 80 * sqrt ε by positivity) hsupport hκ (A := 160) (by norm_num) hε
    (by simpa only [gerver_shape_eq hP hbox] using hballs)
    (by ring_nf; exact le_rfl)
    (hsmallR ε hε.le (hεsmall.trans_le er)).le
    (volume_ne_top_of_subset sdiff_subset hK.2.1.2.1.measure_lt_top.ne) hUS
  rw [gerver_shape_eq hP hbox] at hback
  refine ⟨⟨hfront.mono ?_, hback.mono ?_⟩, hangle⟩
  · have hle : Cf ≤ C := (le_max_left _ _).trans (le_max_right _ _)
    have he := mul_le_mul_of_nonneg_right hle (sqrt_nonneg ε)
    dsimp [Cf] at he
    nlinarith
  · exact mul_le_mul_of_nonneg_right
      ((le_max_right Cf Cb).trans (le_max_right 1 (max Cf Cb))) (sqrt_nonneg ε)

end MovingSofaStability
