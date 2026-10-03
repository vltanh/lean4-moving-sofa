module

public import MovingSofaOptimality.Balanced.BalancedMaximumSofa
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Horizontal side lengths (§4.1)

Definition 4.1.1 (`def:wedge-gap-infimum`), Lemma 4.1.1 (`lem:wedge-gap-limit`), Theorem 4.1.2
(`thm:balanced-polygon-sofa-ineq`), Theorem 4.1.3 (`thm:surface-area-weak-convergence`, Schneider
Theorem 4.2.1) and Theorem 4.1.4 (`thm:balanced-maximum-sofa-ineq`).

**Proofs.** Theorem 4.1.2 bounds the part of the polygon niche on the `x`-axis (Lemma 3.4.5 (2))
by the wedge endpoints `W_K(t)`, `t ∈ Θ`, and uses balancedness (Theorem 3.4.9); the `z`-part is
the same argument on the line `l(ω, 0)` (instead of the mirror symmetry used in the paper), and the
`z`-part of Theorem 4.1.4 uses the analogue of Lemma 4.1.1 for the left wedge gaps. Theorem 4.1.3
is proved by integration by parts against the Stieltjes function `sigmaFun` for `C¹` integrands,
dominated convergence (the vertices `v_{K_n}⁺(t)` converge at every `t` where `K` has no edge) and
uniform approximation by averages over short intervals. Theorem 4.1.4 uses the upper
semicontinuity of edge lengths directly: `σ_K(t) sin δ ≤ h_K(t + δ) + h_K(t - δ) - 2 h_K(t) cos δ`,
and the right-hand side divided by `sin δ` tends to `σ_K(t)` as `δ → 0⁺`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace MovingSofaOptimality

/-- `w_K° = inf_{t ∈ (0, ω)} w_K(t)` (Definition 4.1.1, `def:wedge-gap-infimum`). -/
noncomputable def wedgeGapWInf (K : Set (ℝ × ℝ)) (ω : ℝ) : ℝ := ⨅ t : Ioo 0 ω, wedgeGapW K t

/-- `z_K° = inf_{t ∈ (0, ω)} z_K(t)` (Definition 4.1.1). -/
noncomputable def wedgeGapZInf (K : Set (ℝ × ℝ)) (ω : ℝ) : ℝ := ⨅ t : Ioo 0 ω, wedgeGapZ K ω t

/-! ### Helper lemmas -/

lemma ang_uvec_zero : uvec 0 = (1, 0) := by simp [uvec]
lemma ang_vvec_zero : vvec 0 = (0, 1) := by simp [vvec]
lemma ang_uvec_pi_div_two : uvec (π / 2) = (0, 1) := by simp [uvec]
lemma ang_vvec_pi_div_two : vvec (π / 2) = (-1, 0) := by simp [vvec]
lemma ang_uvec_three_pi_div_two : uvec (3 * π / 2) = (0, -1) := by
  rw [show 3 * π / 2 = π / 2 + π by ring, uvec_add_pi, ang_uvec_pi_div_two]; simp
lemma ang_vvec_three_pi_div_two : vvec (3 * π / 2) = (1, 0) := by
  rw [show 3 * π / 2 = π / 2 + π by ring, vvec_add_pi, ang_vvec_pi_div_two]; simp
lemma ang_dot_uvec_zero (p : ℝ × ℝ) : dot p (uvec 0) = p.1 := by simp [dot, uvec]
lemma ang_dot_uvec_pi_div_two (p : ℝ × ℝ) : dot p (uvec (π / 2)) = p.2 := by simp [dot, uvec]
lemma ang_dot_uvec_three_pi_div_two (p : ℝ × ℝ) : dot p (uvec (3 * π / 2)) = -p.2 := by
  rw [ang_uvec_three_pi_div_two]; simp [dot]
lemma ang_dot_vvec_three_pi_div_two (p : ℝ × ℝ) : dot p (vvec (3 * π / 2)) = p.1 := by
  rw [ang_vvec_three_pi_div_two]; simp [dot]
lemma ang_dot_uvec_add_pi (p : ℝ × ℝ) (t : ℝ) : dot p (uvec (t + π)) = -dot p (uvec t) := by
  rw [uvec_add_pi, dot_neg_right]
lemma ang_supp_le {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {t c : ℝ}
    (h : ∀ p ∈ S, dot p (uvec t) ≤ c) : supp S t ≤ c :=
  csSup_le (hne.image _) (forall_mem_image.2 h)

/-- The support function of a compact set is bounded. -/
lemma ang_exists_abs_supp_le {S : Set (ℝ × ℝ)} (hS : IsCompact S) (hne : S.Nonempty) :
    ∃ R, ∀ t, |supp S t| ≤ R := by
  obtain ⟨R, hR⟩ := hS.isBounded.exists_norm_le
  refine ⟨2 * R, fun t => ?_⟩
  obtain ⟨p, hp, hpt⟩ := exists_dot_eq_supp hS hne t
  rw [← hpt]
  have h1 : |p.1| ≤ R := (norm_fst_le p).trans (hR p hp)
  have h2 : |p.2| ≤ R := (norm_snd_le p).trans (hR p hp)
  have hc := abs_cos_le_one t
  have hs := abs_sin_le_one t
  simp only [dot, uvec]
  calc |p.1 * cos t + p.2 * sin t| ≤ |p.1 * cos t| + |p.2 * sin t| := abs_add_le _ _
    _ = |p.1| * |cos t| + |p.2| * |sin t| := by rw [abs_mul, abs_mul]
    _ ≤ R * 1 + R * 1 := by gcongr <;> linarith [abs_nonneg p.1, abs_nonneg p.2]
    _ = 2 * R := by ring

lemma ang_abs_supp_sub_le_hausdorffDist {K K' : Set (ℝ × ℝ)} (hK : IsConvexBody K)
    (hK' : IsConvexBody K') (t : ℝ) : |supp K t - supp K' t| ≤ hausdorffDist K K' := by
  obtain ⟨R, hR⟩ := ang_exists_abs_supp_le hK.2.1 hK.1
  obtain ⟨R', hR'⟩ := ang_exists_abs_supp_le hK'.2.1 hK'.1
  refine le_ciSup (f := fun t => |supp K t - supp K' t|) ⟨R + R', ?_⟩ t
  rintro _ ⟨s, rfl⟩
  calc |supp K s - supp K' s| ≤ |supp K s| + |supp K' s| := abs_sub _ _
    _ ≤ R + R' := add_le_add (hR s) (hR' s)

lemma ang_hausdorffDist_nonneg {K K' : Set (ℝ × ℝ)} (hK : IsConvexBody K)
    (hK' : IsConvexBody K') : 0 ≤ hausdorffDist K K' :=
  (abs_nonneg _).trans (ang_abs_supp_sub_le_hausdorffDist hK hK' 0)

lemma ang_tendsto_supp {Ks : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)} (hKs : ∀ n, IsConvexBody (Ks n))
    (hK : IsConvexBody K) (hlim : HausdorffTendsto Ks K) (t : ℝ) :
    Tendsto (fun n => supp (Ks n) t) atTop (𝓝 (supp K t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _)
    (fun n => ang_abs_supp_sub_le_hausdorffDist (hKs n) hK t) hlim

/-! ### Caps -/

/-- A point lies in a half-plane intersection if it lies in the supporting half-planes of the
normal angles. -/
lemma ang_mem_of_halfPlaneInter {K : Set (ℝ × ℝ)} {A : Set ℝ} (hK : IsHalfPlaneInter K A)
    (hne : K.Nonempty) {q : ℝ × ℝ} (hq : ∀ t ∈ A, dot q (uvec t) ≤ supp K t) : q ∈ K := by
  obtain ⟨ι, t, c, ht, rfl⟩ := hK
  refine mem_iInter.2 fun i => ?_
  have h1 : supp (⋂ i, halfMinus (t i) (c i)) (t i) ≤ c i :=
    ang_supp_le hne fun p hp => mem_iInter.1 hp i
  exact (hq (t i) (ht i)).trans h1

lemma ang_mem_para_iff {ω : ℝ} {p : ℝ × ℝ} :
    p ∈ para ω ↔ 0 ≤ p.2 ∧ p.2 ≤ 1 ∧ 0 ≤ dot p (uvec ω) ∧ dot p (uvec ω) ≤ 1 := by
  have key : ∀ q : ℝ × ℝ, dot (rot ω q) (uvec ω) = q.1 := fun q => by
    have := dot_rot_uvec ω 0 q; rw [zero_add] at this; rw [this, ang_dot_uvec_zero]
  constructor
  · rintro ⟨⟨h1, h2⟩, q, ⟨hq1, hq2⟩, rfl⟩
    exact ⟨h1, h2, (key q).symm ▸ hq1, (key q).symm ▸ hq2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hp : rot ω (rot (-ω) p) = p := rot_rot_neg ω p
    refine ⟨⟨h1, h2⟩, rot (-ω) p, ⟨?_, ?_⟩, hp⟩
    · have := key (rot (-ω) p); rw [hp] at this; linarith
    · have := key (rot (-ω) p); rw [hp] at this; linarith

lemma ang_cap_props {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) {p : ℝ × ℝ} (hp : p ∈ K) :
    0 ≤ p.2 ∧ p.2 ≤ 1 ∧ 0 ≤ dot p (uvec ω) ∧ dot p (uvec ω) ≤ 1 := by
  obtain ⟨-, hcb, h1, h2, h3, h4, -⟩ := hK
  have hc := hcb.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := dot_le_supp hc hp (3 * π / 2)
    rw [h4, ang_dot_uvec_three_pi_div_two] at this; linarith
  · have := dot_le_supp hc hp (π / 2); rwa [h2, ang_dot_uvec_pi_div_two] at this
  · have := dot_le_supp hc hp (ω + π); rw [h3, ang_dot_uvec_add_pi] at this; linarith
  · have := dot_le_supp hc hp ω; rwa [h1] at this

lemma ang_cap_subset_para {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) : K ⊆ para ω :=
  fun _ hp => ang_mem_para_iff.2 (ang_cap_props hK hp)

lemma ang_cos_pos_of_cap {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) (hω2 : ω < π / 2) : 0 < cos ω :=
  cos_pos_of_mem_Ioo ⟨by linarith [hω.1, pi_pos], hω2⟩

lemma ang_cap_supp_nonneg {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (hω : ω < π / 2) {t : ℝ}
    (ht : t ∈ jSet ω ∪ {ω + π, 3 * π / 2}) : 0 ≤ supp K t := by
  have hcos := ang_cos_pos_of_cap hK.1 hω
  have hω0 := hK.1.1
  have hc := hK.2.1.2.1
  have hne := hK.2.1.1
  rcases ht with (ht | ht) | ht
  · -- `t ∈ [0, ω]`: a point of `K` on the `x`-axis
    obtain ⟨p, hp, hpt⟩ := exists_dot_eq_supp hc hne (3 * π / 2)
    rw [hK.2.2.2.2.2.1, ang_dot_uvec_three_pi_div_two] at hpt
    have hp2 : p.2 = 0 := by linarith
    have h3 := (ang_cap_props hK hp).2.2.1
    simp only [dot, uvec, hp2, zero_mul, add_zero] at h3
    have hp1 : 0 ≤ p.1 := by
      by_contra h; rw [not_le] at h; nlinarith
    have hct : 0 ≤ cos t := cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
    calc (0 : ℝ) ≤ dot p (uvec t) := by simp only [dot, uvec, hp2, zero_mul, add_zero]; positivity
      _ ≤ supp K t := dot_le_supp hc hp t
  · -- `t ∈ [π/2, ω + π/2]`: a point of `K` on the line `l(ω, 0)`
    obtain ⟨p, hp, hpt⟩ := exists_dot_eq_supp hc hne (ω + π)
    rw [hK.2.2.2.2.1, ang_dot_uvec_add_pi] at hpt
    have h0 : p.1 * cos ω + p.2 * sin ω = 0 := by simp only [dot, uvec] at hpt; linarith
    have hp2 := (ang_cap_props hK hp).1
    have hs : 0 ≤ sin (t - ω) := sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1])
      (by linarith [ht.2, hω0])
    have key : dot p (uvec t) * cos ω = p.2 * sin (t - ω) := by
      simp only [dot, uvec, sin_sub]; linear_combination (cos t) * h0
    have : 0 ≤ dot p (uvec t) := by
      by_contra h; rw [not_le] at h; nlinarith [mul_nonneg hp2 hs]
    exact this.trans (dot_le_supp hc hp t)
  · rcases ht with ht | ht
    · rw [ht, hK.2.2.2.2.1]
    · rw [ht, hK.2.2.2.2.2.1]

lemma ang_cap_origin_mem {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (hω : ω < π / 2) :
    ((0 : ℝ), (0 : ℝ)) ∈ K :=
  ang_mem_of_halfPlaneInter hK.2.2.2.2.2.2 hK.2.1.1 fun _ ht => by
    simpa [dot] using ang_cap_supp_nonneg hK hω ht

lemma ang_cap_corner_mem {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (hω : ω < π / 2) :
    (supp K 0, (0 : ℝ)) ∈ K := by
  have hcos := ang_cos_pos_of_cap hK.1 hω
  have hω0 := hK.1.1
  have hc := hK.2.1.2.1
  have hne := hK.2.1.1
  have h00 : 0 ≤ supp K 0 := ang_cap_supp_nonneg hK hω (Or.inl (Or.inl ⟨le_rfl, hω0.le⟩))
  refine ang_mem_of_halfPlaneInter hK.2.2.2.2.2.2 hne fun t ht => ?_
  rcases ht with (ht | ht) | ht
  · obtain ⟨p, hp, hpt⟩ := exists_dot_eq_supp hc hne 0
    rw [ang_dot_uvec_zero] at hpt
    have hp2 := (ang_cap_props hK hp).1
    have hst : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, pi_pos])
    calc dot (supp K 0, (0 : ℝ)) (uvec t) ≤ dot p (uvec t) := by
          simp only [dot, uvec, ← hpt, zero_mul, add_zero]; nlinarith [mul_nonneg hp2 hst]
      _ ≤ supp K t := dot_le_supp hc hp t
  · have hct : cos t ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le ht.1 (by linarith [ht.2, pi_pos])
    calc dot (supp K 0, (0 : ℝ)) (uvec t) ≤ 0 := by
          simp only [dot, uvec, zero_mul, add_zero]; nlinarith
      _ ≤ supp K t := ang_cap_supp_nonneg hK hω (Or.inl (Or.inr ht))
  · rcases ht with ht | ht
    · rw [ht, hK.2.2.2.2.1, ang_dot_uvec_add_pi]
      simp only [dot, uvec, zero_mul, add_zero]; nlinarith
    · rw [ht, hK.2.2.2.2.2.1, ang_dot_uvec_three_pi_div_two]; simp

/-- `tan(π/4 - ω/2) cos ω = 1 - sin ω`. -/
lemma ang_tan_mul_cos (ω : ℝ) (h : cos (π / 4 - ω / 2) ≠ 0) :
    tan (π / 4 - ω / 2) * cos ω = 1 - sin ω := by
  set α := π / 4 - ω / 2 with hα
  have hω : ω = π / 2 - 2 * α := by rw [hα]; ring
  have hc : cos ω = 2 * sin α * cos α := by rw [hω, cos_pi_div_two_sub, sin_two_mul]
  have hs : sin ω = 1 - 2 * sin α ^ 2 := by
    rw [hω, sin_pi_div_two_sub, cos_two_mul]; linear_combination 2 * sin_sq_add_cos_sq α
  rw [hc, hs, tan_eq_sin_div_cos]
  field_simp
  ring

lemma ang_cos_quarter_pos {ω : ℝ} (hω : ω ∈ Icc 0 (π / 2)) : 0 < cos (π / 4 - ω / 2) :=
  cos_pos_of_mem_Ioo ⟨by linarith [hω.2, pi_pos], by linarith [hω.1, pi_pos]⟩

lemma ang_dot_oPt_uvec {ω : ℝ} (hω : ω ∈ Icc 0 (π / 2)) : dot (oPt ω) (uvec ω) = 1 := by
  have := ang_tan_mul_cos ω (ang_cos_quarter_pos hω).ne'
  simp only [dot, oPt, uvec]; linarith

lemma ang_cap_oPt_mem {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (hω : ω < π / 2) :
    oPt ω ∈ K := by
  have hcos := ang_cos_pos_of_cap hK.1 hω
  have hω0 := hK.1.1
  have hc := hK.2.1.2.1
  have hne := hK.2.1.1
  have ho := ang_dot_oPt_uvec ⟨hω0.le, hω.le⟩
  refine ang_mem_of_halfPlaneInter hK.2.2.2.2.2.2 hne fun t ht => ?_
  rcases ht with (ht | ht) | ht
  · obtain ⟨p, hp, hpt⟩ := exists_dot_eq_supp hc hne ω
    rw [hK.2.2.1] at hpt
    have hp2 := (ang_cap_props hK hp).2.1
    have hs : sin (t - ω) ≤ 0 := sin_nonpos_of_nonpos_of_neg_pi_le (by linarith [ht.2])
      (by linarith [ht.1, pi_pos, hω])
    have hD : dot (p - oPt ω) (uvec ω) = 0 := by rw [dot_sub_left, hpt, ho]; ring
    have hD2 : (p - oPt ω).2 ≤ 0 := by simp only [Prod.snd_sub, oPt]; linarith
    have key : dot (p - oPt ω) (uvec t) * cos ω = (p - oPt ω).2 * sin (t - ω) := by
      simp only [dot, uvec, sin_sub] at hD ⊢; linear_combination (cos t) * hD
    have h1 : 0 ≤ dot (p - oPt ω) (uvec t) := by
      by_contra h; rw [not_le] at h; nlinarith [mul_nonneg_of_nonpos_of_nonpos hD2 hs]
    rw [dot_sub_left] at h1
    linarith [dot_le_supp hc hp t]
  · obtain ⟨p, hp, hpt⟩ := exists_dot_eq_supp hc hne (π / 2)
    rw [hK.2.2.2.1, ang_dot_uvec_pi_div_two] at hpt
    have hpω := (ang_cap_props hK hp).2.2.2
    have hct : cos t ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le ht.1 (by linarith [ht.2, pi_pos])
    have hD1 : p.1 - (oPt ω).1 ≤ 0 := by
      have : dot (p - oPt ω) (uvec ω) ≤ 0 := by rw [dot_sub_left, ho]; linarith
      simp only [dot, uvec, Prod.fst_sub, Prod.snd_sub, oPt, hpt, sub_self, zero_mul,
        add_zero] at this ⊢
      by_contra h; rw [not_le] at h; nlinarith
    have h1 : 0 ≤ dot (p - oPt ω) (uvec t) := by
      have e : dot (p - oPt ω) (uvec t) = (p.1 - (oPt ω).1) * cos t := by
        simp only [dot, uvec, Prod.fst_sub, Prod.snd_sub, oPt, hpt, sub_self, zero_mul, add_zero]
      rw [e]; nlinarith
    rw [dot_sub_left] at h1
    linarith [dot_le_supp hc hp t]
  · rcases ht with ht | ht
    · rw [ht, hK.2.2.2.2.1, ang_dot_uvec_add_pi, ho]; norm_num
    · rw [ht, hK.2.2.2.2.2.1, ang_dot_uvec_three_pi_div_two]; simp [oPt]

/-- The point `h_K(ω + π/2) v_ω` (the corner `C_K⁺(ω)`) lies in a cap with `ω < π/2`. -/
lemma ang_cap_corner2_mem {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (hω : ω < π / 2) :
    supp K (ω + π / 2) • vvec ω ∈ K := by
  have hcos := ang_cos_pos_of_cap hK.1 hω
  have hω0 := hK.1.1
  have hc := hK.2.1.2.1
  have hne := hK.2.1.1
  have hh0 : 0 ≤ supp K (ω + π / 2) :=
    ang_cap_supp_nonneg hK hω (Or.inl (Or.inr ⟨by linarith, le_rfl⟩))
  have hq : ∀ t, dot (supp K (ω + π / 2) • vvec ω) (uvec t) = supp K (ω + π / 2) * sin (t - ω) :=
    fun t => by rw [dot_smul_left, dot_vvec_uvec']
  refine ang_mem_of_halfPlaneInter hK.2.2.2.2.2.2 hne fun t ht => ?_
  rw [hq]
  rcases ht with (ht | ht) | ht
  · have hs : sin (t - ω) ≤ 0 :=
      sin_nonpos_of_nonpos_of_neg_pi_le (by linarith [ht.2]) (by linarith [ht.1, pi_pos])
    exact (mul_nonpos_of_nonneg_of_nonpos hh0 hs).trans
      (ang_cap_supp_nonneg hK hω (Or.inl (Or.inl ht)))
  · obtain ⟨p, hp, hpt⟩ := exists_dot_eq_supp hc hne (ω + π / 2)
    rw [uvec_add_pi_div_two] at hpt
    have hpω := (ang_cap_props hK hp).2.2.1
    have hct : 0 ≤ cos (t - ω) :=
      cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
    have key : dot p (uvec t) = dot p (uvec ω) * cos (t - ω) + dot p (vvec ω) * sin (t - ω) := by
      simp only [dot, uvec, vvec, cos_sub, sin_sub]
      linear_combination (-(p.1 * cos t) - p.2 * sin t) * sin_sq_add_cos_sq ω
    calc supp K (ω + π / 2) * sin (t - ω) ≤ dot p (uvec t) := by
          rw [key, hpt]; nlinarith [mul_nonneg hpω hct]
      _ ≤ supp K t := dot_le_supp hc hp t
  · rcases ht with ht | ht
    · rw [ht, hK.2.2.2.2.1, show ω + π - ω = π by ring, sin_pi, mul_zero]
    · rw [ht, hK.2.2.2.2.2.1, show 3 * π / 2 - ω = π / 2 - ω + π by ring, sin_add_pi,
        sin_pi_div_two_sub]
      nlinarith

/-! ### Wedge gaps -/

lemma ang_wedgeGapW_eq (K : Set (ℝ × ℝ)) (t : ℝ) :
    wedgeGapW K t = supp K 0 - (supp K t - 1) / cos t := by
  simp only [wedgeGapW, aMinus, wedgeW, dot_sub_left, dot_vminus_uvec]
  simp [dot, uvec]

lemma ang_cos_pos_of_mem_Icc {ω t : ℝ} (hω : ω < π / 2) (ht : t ∈ Icc 0 ω) : 0 < cos t :=
  cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩

lemma ang_continuousOn_wedgeGapW {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {ω : ℝ}
    (hω : ω < π / 2) : ContinuousOn (wedgeGapW K) (Icc 0 ω) := by
  have hcont := continuous_supp hK.2.1
  have : wedgeGapW K = fun t => supp K 0 - (supp K t - 1) / cos t :=
    funext (ang_wedgeGapW_eq K)
  rw [this]
  refine continuousOn_const.sub ((hcont.sub continuous_const).continuousOn.div
    continuous_cos.continuousOn fun t ht => (ang_cos_pos_of_mem_Icc hω ht).ne')

lemma ang_bddBelow_wedgeGapW {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {ω : ℝ}
    (hω : ω < π / 2) : BddBelow (range fun t : Ioo 0 ω => wedgeGapW K t) := by
  refine (isCompact_Icc.bddBelow_image (ang_continuousOn_wedgeGapW hK hω)).mono ?_
  rintro _ ⟨t, rfl⟩
  exact ⟨t, Ioo_subset_Icc_self t.2, rfl⟩

lemma ang_wedgeGapWInf_le {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {ω t : ℝ}
    (hω : ω < π / 2) (ht : t ∈ Ioo 0 ω) : wedgeGapWInf K ω ≤ wedgeGapW K t :=
  ciInf_le (ang_bddBelow_wedgeGapW hK hω) ⟨t, ht⟩

lemma ang_le_wedgeGapWInf {K : Set (ℝ × ℝ)} {ω a : ℝ} (hω : 0 < ω)
    (h : ∀ t ∈ Ioo 0 ω, a ≤ wedgeGapW K t) : a ≤ wedgeGapWInf K ω := by
  have : Nonempty (Ioo 0 ω) := ⟨⟨ω / 2, by constructor <;> linarith⟩⟩
  exact le_ciInf fun t => h t t.2

/-- `w_K° ≤ h_K(0)`: the wedge gap `w_K(t)` tends to `h_K(0)` as `t → ω⁻`. -/
lemma ang_wedgeGapWInf_le_supp_zero {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω)
    (hω : ω < π / 2) : wedgeGapWInf K ω ≤ supp K 0 := by
  have hcb := hK.2.1
  have hω0 := hK.1.1
  have hcos := ang_cos_pos_of_cap hK.1 hω
  have hcont : ContinuousAt (fun t => supp K 0 - (supp K t - 1) / cos t) ω :=
    continuousAt_const.sub (((continuous_supp hcb.2.1).continuousAt.sub
      continuousAt_const).div continuous_cos.continuousAt hcos.ne')
  have hval : supp K 0 - (supp K ω - 1) / cos ω = supp K 0 := by rw [hK.2.2.1]; simp
  have htend : Tendsto (wedgeGapW K) (𝓝[<] ω) (𝓝 (supp K 0)) := by
    rw [show wedgeGapW K = fun t => supp K 0 - (supp K t - 1) / cos t from
      funext (ang_wedgeGapW_eq K)]
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio ω))
    rwa [hval] at this
  refine ge_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsLT hω0] with t ht
  exact ang_wedgeGapWInf_le hcb hω ht

/-! ### The left wedge gaps -/

lemma ang_wedgeGapZ_eq (K : Set (ℝ × ℝ)) (ω t : ℝ) :
    wedgeGapZ K ω t = supp K (ω + π / 2) - (supp K (t + π / 2) - 1) / cos (ω - t) := by
  simp only [wedgeGapZ, cPlus, wedgeZ, dot_sub_left, dot_smul_left, dot_vvec_self, mul_one]
  rw [← uvec_add_pi_div_two, dot_vplus_uvec]

lemma ang_cos_sub_pos_of_mem_Icc {ω t : ℝ} (hω : ω < π / 2) (ht : t ∈ Icc 0 ω) :
    0 < cos (ω - t) :=
  cos_pos_of_mem_Ioo ⟨by linarith [ht.2, pi_pos, ht.1], by linarith [ht.1]⟩

lemma ang_continuousOn_wedgeGapZ {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {ω : ℝ}
    (hω : ω < π / 2) : ContinuousOn (wedgeGapZ K ω) (Icc 0 ω) := by
  have hcont := continuous_supp hK.2.1
  have : wedgeGapZ K ω = fun t => supp K (ω + π / 2) - (supp K (t + π / 2) - 1) / cos (ω - t) :=
    funext (ang_wedgeGapZ_eq K ω)
  rw [this]
  refine continuousOn_const.sub (((hcont.comp (continuous_id.add continuous_const)).sub
    continuous_const).continuousOn.div (continuous_cos.comp (continuous_const.sub
    continuous_id)).continuousOn fun t ht => (ang_cos_sub_pos_of_mem_Icc hω ht).ne')

lemma ang_bddBelow_wedgeGapZ {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {ω : ℝ}
    (hω : ω < π / 2) : BddBelow (range fun t : Ioo 0 ω => wedgeGapZ K ω t) := by
  refine (isCompact_Icc.bddBelow_image (ang_continuousOn_wedgeGapZ hK hω)).mono ?_
  rintro _ ⟨t, rfl⟩
  exact ⟨t, Ioo_subset_Icc_self t.2, rfl⟩

lemma ang_wedgeGapZInf_le {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {ω t : ℝ}
    (hω : ω < π / 2) (ht : t ∈ Ioo 0 ω) : wedgeGapZInf K ω ≤ wedgeGapZ K ω t :=
  ciInf_le (ang_bddBelow_wedgeGapZ hK hω) ⟨t, ht⟩

lemma ang_le_wedgeGapZInf {K : Set (ℝ × ℝ)} {ω a : ℝ} (hω : 0 < ω)
    (h : ∀ t ∈ Ioo 0 ω, a ≤ wedgeGapZ K ω t) : a ≤ wedgeGapZInf K ω := by
  have : Nonempty (Ioo 0 ω) := ⟨⟨ω / 2, by constructor <;> linarith⟩⟩
  exact le_ciInf fun t => h t t.2

/-- `z_K° ≤ h_K(ω + π/2)`: the wedge gap `z_K(t)` tends to `h_K(ω + π/2)` as `t → 0⁺`. -/
lemma ang_wedgeGapZInf_le_supp {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω)
    (hω : ω < π / 2) : wedgeGapZInf K ω ≤ supp K (ω + π / 2) := by
  have hcb := hK.2.1
  have hω0 := hK.1.1
  have hcos := ang_cos_pos_of_cap hK.1 hω
  have hcont : ContinuousAt
      (fun t => supp K (ω + π / 2) - (supp K (t + π / 2) - 1) / cos (ω - t)) 0 :=
    continuousAt_const.sub ((((continuous_supp hcb.2.1).comp
      (continuous_id.add continuous_const)).continuousAt.sub continuousAt_const).div
      (continuous_cos.comp (continuous_const.sub continuous_id)).continuousAt
      (by simpa using hcos.ne'))
  have hval : supp K (ω + π / 2) - (supp K (0 + π / 2) - 1) / cos (ω - 0) =
      supp K (ω + π / 2) := by rw [zero_add, hK.2.2.2.1]; simp
  have htend : Tendsto (wedgeGapZ K ω) (𝓝[>] 0) (𝓝 (supp K (ω + π / 2))) := by
    rw [show wedgeGapZ K ω = fun t => supp K (ω + π / 2) - (supp K (t + π / 2) - 1) / cos (ω - t)
      from funext (ang_wedgeGapZ_eq K ω)]
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    rwa [hval] at this
  refine ge_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsGT hω0] with t ht
  exact ang_wedgeGapZInf_le hcb hω ht

/-- **Lemma 4.1.1** (`lem:wedge-gap-limit`). For caps `K, K'` with rotation angle `ω < π/2` at
Hausdorff distance `ε`, `|w_K° - w_{K'}°| ≤ (1 + sec ω) ε`. -/
theorem lemma4_1_1 {K K' : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω < π / 2) (hK : IsCap K ω)
    (hK' : IsCap K' ω) :
    |wedgeGapWInf K ω - wedgeGapWInf K' ω| ≤ (1 + 1 / cos ω) * hausdorffDist K K' := by
  have hcb := hK.2.1
  have hcb' := hK'.2.1
  have hω0 := hK.1.1
  have hcos := ang_cos_pos_of_cap hK.1 hω
  set ε := hausdorffDist K K' with hεdef
  have hε : 0 ≤ ε := ang_hausdorffDist_nonneg hcb hcb'
  have key : ∀ t ∈ Ioo 0 ω, |wedgeGapW K t - wedgeGapW K' t| ≤ (1 + 1 / cos ω) * ε := by
    intro t ht
    have hct : cos ω ≤ cos t :=
      cos_le_cos_of_nonneg_of_le_pi ht.1.le (by linarith [pi_pos]) ht.2.le
    have hct0 : 0 < cos t := by linarith
    rw [ang_wedgeGapW_eq, ang_wedgeGapW_eq]
    have h0 := ang_abs_supp_sub_le_hausdorffDist hcb hcb' 0
    have h1 := ang_abs_supp_sub_le_hausdorffDist hcb hcb' t
    have e : supp K 0 - (supp K t - 1) / cos t - (supp K' 0 - (supp K' t - 1) / cos t) =
        (supp K 0 - supp K' 0) - (supp K t - supp K' t) / cos t := by
      field_simp; ring
    rw [e]
    calc |(supp K 0 - supp K' 0) - (supp K t - supp K' t) / cos t|
        ≤ |supp K 0 - supp K' 0| + |(supp K t - supp K' t) / cos t| := abs_sub _ _
      _ = |supp K 0 - supp K' 0| + |supp K t - supp K' t| / cos t := by
          rw [abs_div, abs_of_pos hct0]
      _ ≤ ε + ε / cos t := by gcongr
      _ ≤ ε + ε / cos ω := by gcongr
      _ = (1 + 1 / cos ω) * ε := by ring
  rw [abs_le]
  constructor
  · have : wedgeGapWInf K' ω - (1 + 1 / cos ω) * ε ≤ wedgeGapWInf K ω := by
      refine ang_le_wedgeGapWInf hω0 fun t ht => ?_
      have h1 := ang_wedgeGapWInf_le hcb' hω ht
      have h2 := (abs_le.1 (key t ht)).1
      linarith
    linarith
  · have : wedgeGapWInf K ω - (1 + 1 / cos ω) * ε ≤ wedgeGapWInf K' ω := by
      refine ang_le_wedgeGapWInf hω0 fun t ht => ?_
      have h1 := ang_wedgeGapWInf_le hcb hω ht
      have h2 := (abs_le.1 (key t ht)).2
      linarith
    linarith

/-! ### Edge lengths -/

lemma ang_continuous_dot (v : ℝ × ℝ) : Continuous fun p : ℝ × ℝ => dot p v := by
  unfold dot; fun_prop

lemma ang_dot_vplus_vvec (K : Set (ℝ × ℝ)) (t : ℝ) :
    dot (vplus K t) (vvec t) = sSup ((fun p => dot p (vvec t)) '' edge K t) := by
  simp [vplus, dot_add_left, dot_smul_left]

lemma ang_dot_vminus_vvec (K : Set (ℝ × ℝ)) (t : ℝ) :
    dot (vminus K t) (vvec t) = sInf ((fun p => dot p (vvec t)) '' edge K t) := by
  simp [vminus, dot_add_left, dot_smul_left]

lemma ang_sigmaAt_eq_sub {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    sigmaAt K t = dot (vplus K t) (vvec t) - dot (vminus K t) (vvec t) := by
  rw [(proposition2_1_2 hK t).2, dot_add_left, dot_smul_left, dot_vvec_self]; ring

/-- The bottom edge `e_K(3π/2)` of a cap contains `O` and `(h_K(0), 0)`, so it has length at least
`h_K(0)`. -/
lemma ang_supp_zero_le_sigmaAt {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (hω : ω < π / 2) :
    supp K 0 ≤ sigmaAt K (3 * π / 2) := by
  have hcb := hK.2.1
  have hc := hcb.2.1
  have hb := hc.bddAbove_image (ang_continuous_dot (vvec (3 * π / 2))).continuousOn
  have hb' := hc.bddBelow_image (ang_continuous_dot (vvec (3 * π / 2))).continuousOn
  have hsub : edge K (3 * π / 2) ⊆ K := inter_subset_left
  have hE1 : (supp K 0, (0 : ℝ)) ∈ edge K (3 * π / 2) :=
    ⟨ang_cap_corner_mem hK hω, by
      simp [suppLine, line, ang_dot_uvec_three_pi_div_two, hK.2.2.2.2.2.1]⟩
  have hE0 : ((0 : ℝ), (0 : ℝ)) ∈ edge K (3 * π / 2) :=
    ⟨ang_cap_origin_mem hK hω, by
      simp [suppLine, line, ang_dot_uvec_three_pi_div_two, hK.2.2.2.2.2.1]⟩
  rw [ang_sigmaAt_eq_sub hcb, ang_dot_vplus_vvec, ang_dot_vminus_vvec]
  have h1 := le_csSup (hb.mono (image_mono hsub))
    (mem_image_of_mem (fun p => dot p (vvec (3 * π / 2))) hE1)
  have h2 := csInf_le (hb'.mono (image_mono hsub))
    (mem_image_of_mem (fun p => dot p (vvec (3 * π / 2))) hE0)
  simp only [ang_dot_vvec_three_pi_div_two] at h1 h2 ⊢
  linarith

/-- The part of the polygon niche on the `x`-axis lies in `(0, max_Θ W_K(t))`. -/
lemma ang_lineLength_polyNiche_le {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hω : Θ.ω < π / 2) {W : ℝ}
    (hW : ∀ t ∈ Θ.angles, (supp K t - 1) / cos t ≤ W) :
    lineLength (π / 2) 0 (polyNiche Θ K) ≤ max W 0 := by
  have hcos : 0 < cos Θ.ω := ang_cos_pos_of_cap Θ.hω hω
  unfold lineLength
  have hsub : {s : ℝ | (0 : ℝ) • uvec (π / 2) + s • vvec (π / 2) ∈ polyNiche Θ K} ⊆
      Ioc (-W) 0 := by
    intro s hs
    simp only [mem_ofPred_eq, zero_smul, zero_add, ang_vvec_pi_div_two] at hs
    obtain ⟨⟨hf1, -⟩, hU⟩ := hs
    simp only [halfPlus, mem_ofPred_eq, dot, uvec, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hf1
    obtain ⟨t, ht, hq⟩ := mem_iUnion₂.1 hU
    rw [proposition2_2_2_qMinus] at hq
    obtain ⟨hq1, -⟩ := hq
    simp only [halfMinusOpen, mem_ofPred_eq, dot, uvec, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hq1
    have htt := Θ.subset t ht
    have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [htt.1, pi_pos], by linarith [htt.2]⟩
    have hWt := hW t ht
    rw [div_le_iff₀ hct] at hWt
    constructor
    · by_contra h
      rw [not_lt] at h
      nlinarith [mul_le_mul_of_nonneg_right h hct.le]
    · by_contra h
      rw [not_le] at h
      nlinarith [mul_pos h hcos]
  calc (volume {s : ℝ | (0 : ℝ) • uvec (π / 2) + s • vvec (π / 2) ∈ polyNiche Θ K}).toReal
      ≤ (volume (Ioc (-W) 0)).toReal :=
        ENNReal.toReal_mono (by simp [Real.volume_Ioc]) (measure_mono hsub)
    _ = max W 0 := by rw [Real.volume_Ioc, ENNReal.toReal_ofReal']; ring_nf

lemma ang_theorem4_1_2_w {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap Θ K)
    (hω : Θ.ω < π / 2) : wedgeGapWInf K Θ.ω ≤ sigmaAt K (π / 2) := by
  have hcap : IsCap K Θ.ω := hK.1.1
  have hcb := hcap.2.1
  obtain ⟨t₀, ht₀, hmax⟩ :=
    Θ.angles.exists_max_image (fun t => (supp K t - 1) / cos t) Θ.nonempty
  have hℓ := ang_lineLength_polyNiche_le (K := K) hω hmax
  have h352 := (lemma3_4_5_two hK.1 (t := π / 2) (Or.inr rfl)).2
  rw [show π / 2 + π = 3 * π / 2 by ring] at h352
  have hbal := theorem3_4_9 hK (π / 2) (Or.inr (Or.inr rfl))
  have hσ := ang_supp_zero_le_sigmaAt hcap hω
  have h1 := ang_wedgeGapWInf_le_supp_zero hcap hω
  have h2 := ang_wedgeGapWInf_le hcb hω (Θ.subset t₀ ht₀)
  rw [ang_wedgeGapW_eq] at h2
  rcases le_total ((supp K t₀ - 1) / cos t₀) 0 with hW | hW
  · rw [max_eq_right hW] at hℓ; linarith
  · rw [max_eq_left hW] at hℓ; linarith

/-- The edge `e_K(ω + π)` of a cap contains `O` and `h_K(ω + π/2) v_ω`, so it has length at least
`h_K(ω + π/2)`. -/
lemma ang_supp_le_sigmaAt_add_pi {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (hω : ω < π / 2) :
    supp K (ω + π / 2) ≤ sigmaAt K (ω + π) := by
  have hcb := hK.2.1
  have hc := hcb.2.1
  have hb := hc.bddAbove_image (ang_continuous_dot (vvec (ω + π))).continuousOn
  have hb' := hc.bddBelow_image (ang_continuous_dot (vvec (ω + π))).continuousOn
  have hsub : edge K (ω + π) ⊆ K := inter_subset_left
  have hE1 : supp K (ω + π / 2) • vvec ω ∈ edge K (ω + π) := by
    refine ⟨ang_cap_corner2_mem hK hω, ?_⟩
    show dot (supp K (ω + π / 2) • vvec ω) (uvec (ω + π)) = supp K (ω + π)
    rw [hK.2.2.2.2.1, dot_smul_left, ang_dot_uvec_add_pi, dot_vvec_uvec]; ring
  have hE0 : ((0 : ℝ), (0 : ℝ)) ∈ edge K (ω + π) := by
    refine ⟨ang_cap_origin_mem hK hω, ?_⟩
    show dot ((0 : ℝ), (0 : ℝ)) (uvec (ω + π)) = supp K (ω + π)
    rw [hK.2.2.2.2.1]; simp [dot]
  rw [ang_sigmaAt_eq_sub hcb, ang_dot_vplus_vvec, ang_dot_vminus_vvec]
  have h1 := le_csSup (hb.mono (image_mono hsub))
    (mem_image_of_mem (fun p => dot p (vvec (ω + π))) hE0)
  have h2 := csInf_le (hb'.mono (image_mono hsub))
    (mem_image_of_mem (fun p => dot p (vvec (ω + π))) hE1)
  have e1 : dot ((0 : ℝ), (0 : ℝ)) (vvec (ω + π)) = 0 := by simp [dot]
  have e2 : dot (supp K (ω + π / 2) • vvec ω) (vvec (ω + π)) = -supp K (ω + π / 2) := by
    rw [vvec_add_pi, dot_smul_left, dot_neg_right, dot_vvec_self]; ring
  simp only [e1, e2] at h1 h2
  linarith

/-- The part of the polygon niche on the line `l(ω, 0)` lies in `[0, max_Θ Z_K(t))`. -/
lemma ang_lineLength_polyNiche_le_z {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hω : Θ.ω < π / 2) {Z : ℝ}
    (hZ : ∀ t ∈ Θ.angles, (supp K (t + π / 2) - 1) / cos (Θ.ω - t) ≤ Z) :
    lineLength Θ.ω 0 (polyNiche Θ K) ≤ max Z 0 := by
  have hcos : 0 < cos Θ.ω := ang_cos_pos_of_cap Θ.hω hω
  unfold lineLength
  have hsub : {s : ℝ | (0 : ℝ) • uvec Θ.ω + s • vvec Θ.ω ∈ polyNiche Θ K} ⊆ Ico 0 Z := by
    intro s hs
    simp only [mem_ofPred_eq, zero_smul, zero_add] at hs
    obtain ⟨⟨-, hf2⟩, hU⟩ := hs
    have hf2' : 0 ≤ dot (s • vvec Θ.ω) (uvec (π / 2)) := hf2
    rw [ang_dot_uvec_pi_div_two] at hf2'
    simp only [Prod.smul_snd, vvec, smul_eq_mul] at hf2'
    obtain ⟨t, ht, hq⟩ := mem_iUnion₂.1 hU
    rw [proposition2_2_2_qMinus] at hq
    obtain ⟨-, hq2⟩ := hq
    have hq2' : dot (s • vvec Θ.ω) (uvec (t + π / 2)) < supp K (t + π / 2) - 1 := hq2
    rw [dot_smul_left, uvec_add_pi_div_two, dot_vvec_vvec] at hq2'
    have htt := Θ.subset t ht
    have hct : 0 < cos (Θ.ω - t) := ang_cos_sub_pos_of_mem_Icc hω ⟨htt.1.le, htt.2.le⟩
    have hZt := hZ t ht
    rw [div_le_iff₀ hct] at hZt
    constructor
    · by_contra h
      rw [not_le] at h
      nlinarith [mul_pos (neg_pos.2 h) hcos]
    · by_contra h
      rw [not_lt] at h
      nlinarith [mul_le_mul_of_nonneg_right h hct.le]
  calc (volume {s : ℝ | (0 : ℝ) • uvec Θ.ω + s • vvec Θ.ω ∈ polyNiche Θ K}).toReal
      ≤ (volume (Ico 0 Z)).toReal :=
        ENNReal.toReal_mono (by simp [Real.volume_Ico]) (measure_mono hsub)
    _ = max Z 0 := by rw [Real.volume_Ico, ENNReal.toReal_ofReal', sub_zero]

lemma ang_theorem4_1_2_z {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap Θ K)
    (hω : Θ.ω < π / 2) : wedgeGapZInf K Θ.ω ≤ sigmaAt K Θ.ω := by
  have hcap : IsCap K Θ.ω := hK.1.1
  have hcb := hcap.2.1
  obtain ⟨t₀, ht₀, hmax⟩ :=
    Θ.angles.exists_max_image (fun t => (supp K (t + π / 2) - 1) / cos (Θ.ω - t)) Θ.nonempty
  have hℓ := ang_lineLength_polyNiche_le_z (K := K) hω hmax
  have h352 := (lemma3_4_5_two hK.1 (t := Θ.ω) (Or.inl rfl)).2
  have hbal := theorem3_4_9 hK Θ.ω (Or.inr (Or.inl rfl))
  have hσ := ang_supp_le_sigmaAt_add_pi hcap hω
  have h1 := ang_wedgeGapZInf_le_supp hcap hω
  have h2 := ang_wedgeGapZInf_le hcb hω (Θ.subset t₀ ht₀)
  rw [ang_wedgeGapZ_eq] at h2
  rcases le_total ((supp K (t₀ + π / 2) - 1) / cos (Θ.ω - t₀)) 0 with hW | hW
  · rw [max_eq_right hW] at hℓ; linarith
  · rw [max_eq_left hW] at hℓ; linarith

/-! ### Mirror symmetry -/

/-- The reflection `t ↦ ω - t` of `(0, ω)`. -/
def ang_IooReflect (ω : ℝ) : Ioo (0 : ℝ) ω ≃ Ioo (0 : ℝ) ω where
  toFun t := ⟨ω - t, by constructor <;> linarith [t.2.1, t.2.2]⟩
  invFun t := ⟨ω - t, by constructor <;> linarith [t.2.1, t.2.2]⟩
  left_inv t := by ext; simp
  right_inv t := by ext; simp

lemma ang_wedgeGapWInf_mirror {K : Set (ℝ × ℝ)} {ω : ℝ} :
    wedgeGapWInf (mirrorCap K ω) ω = wedgeGapZInf K ω := by
  unfold wedgeGapWInf wedgeGapZInf
  calc ⨅ t : Ioo 0 ω, wedgeGapW (mirrorCap K ω) t
      = ⨅ t : Ioo 0 ω, wedgeGapZ K ω (ang_IooReflect ω t) := by
        congr 1; ext t; exact (proposition2_5_4_gaps (K := K) (ω := ω) t).1
    _ = ⨅ t : Ioo 0 ω, wedgeGapZ K ω t :=
        (ang_IooReflect ω).iInf_comp (g := fun s : Ioo 0 ω => wedgeGapZ K ω s)

lemma ang_sigmaAt_mirror {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (t : ℝ) :
    sigmaAt (mirrorCap K ω) t = sigmaAt K (ω + π / 2 - t) := by
  unfold sigmaAt
  rw [proposition2_5_4_sigma hK, Measure.map_apply (by fun_prop) (measurableSet_singleton t)]
  congr 2
  ext s
  simp only [mem_preimage, mem_singleton_iff]
  constructor <;> intro h <;> linarith

/-- **Theorem 4.1.2** (`thm:balanced-polygon-sofa-ineq`). For a maximum polygon cap with rotation
angle `ω < π/2`, `w_K° ≤ σ_K(π/2)` and `z_K° ≤ σ_K(ω)`. -/
theorem theorem4_1_2 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap Θ K)
    (hω : Θ.ω < π / 2) :
    wedgeGapWInf K Θ.ω ≤ sigmaAt K (π / 2) ∧ wedgeGapZInf K Θ.ω ≤ sigmaAt K Θ.ω := by
  exact ⟨ang_theorem4_1_2_w hK hω, ang_theorem4_1_2_z hK hω⟩

/-! ### Upper semicontinuity of edge lengths and weak convergence of `σ_K` -/

lemma ang_vplus_eq (K : Set (ℝ × ℝ)) (t : ℝ) :
    vplus K t = supp K t • uvec t + dot (vplus K t) (vvec t) • vvec t := by
  conv_lhs => rw [eq_dot_uvec_smul_add (vplus K t) t, dot_vplus_uvec]

lemma ang_vminus_eq (K : Set (ℝ × ℝ)) (t : ℝ) :
    vminus K t = supp K t • uvec t + dot (vminus K t) (vvec t) • vvec t := by
  conv_lhs => rw [eq_dot_uvec_smul_add (vminus K t) t, dot_vminus_uvec]

lemma ang_dplus_mul_sin_le {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t δ : ℝ) :
    dot (vplus K t) (vvec t) * sin δ ≤ supp K (t + δ) - supp K t * cos δ := by
  have h1 : dot (vplus K t) (uvec (t + δ)) ≤ supp K (t + δ) :=
    dot_le_supp hK.2.1 (vplus_mem_edge hK t).1 _
  have e1 : dot (vplus K t) (uvec (t + δ)) =
      supp K t * cos δ + dot (vplus K t) (vvec t) * sin δ := by
    conv_lhs => rw [ang_vplus_eq K t]
    rw [dot_add_left, dot_smul_left, dot_smul_left, dot_uvec_uvec, dot_vvec_uvec',
      show t - (t + δ) = -δ by ring, show t + δ - t = δ by ring, cos_neg]
  linarith

lemma ang_le_dminus_mul_sin {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t δ : ℝ) :
    supp K t * cos δ - supp K (t - δ) ≤ dot (vminus K t) (vvec t) * sin δ := by
  have h2 : dot (vminus K t) (uvec (t - δ)) ≤ supp K (t - δ) :=
    dot_le_supp hK.2.1 (vminus_mem_edge hK t).1 _
  have e2 : dot (vminus K t) (uvec (t - δ)) =
      supp K t * cos δ - dot (vminus K t) (vvec t) * sin δ := by
    conv_lhs => rw [ang_vminus_eq K t]
    rw [dot_add_left, dot_smul_left, dot_smul_left, dot_uvec_uvec, dot_vvec_uvec',
      show t - (t - δ) = δ by ring, show t - δ - t = -δ by ring, sin_neg]
    ring
  linarith

/-- `σ_K(t) sin δ ≤ h_K(t + δ) + h_K(t - δ) - 2 h_K(t) cos δ` for a convex body `K`. -/
lemma ang_sigmaAt_mul_sin_le {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t δ : ℝ) :
    sigmaAt K t * sin δ ≤ supp K (t + δ) + supp K (t - δ) - 2 * supp K t * cos δ := by
  have h1 := ang_dplus_mul_sin_le hK t δ
  have h2 := ang_le_dminus_mul_sin hK t δ
  rw [ang_sigmaAt_eq_sub hK]
  linarith

lemma ang_tendsto_add_nhdsGT (t : ℝ) :
    Tendsto (fun δ : ℝ => t + δ) (𝓝[>] 0) (𝓝[>] t) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have : Tendsto (fun δ : ℝ => t + δ) (𝓝 0) (𝓝 (t + 0)) :=
      (continuous_const.add continuous_id).tendsto 0
    rw [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact lt_add_of_pos_right t hδ

lemma ang_tendsto_sub_nhdsGT (t : ℝ) :
    Tendsto (fun δ : ℝ => t - δ) (𝓝[>] 0) (𝓝[<] t) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have : Tendsto (fun δ : ℝ => t - δ) (𝓝 0) (𝓝 (t - 0)) :=
      (continuous_const.sub continuous_id).tendsto 0
    rw [sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact sub_lt_self t hδ

lemma ang_tendsto_slope_cos : Tendsto (fun δ : ℝ => (1 - cos δ) / δ) (𝓝[>] 0) (𝓝 0) := by
  have h := (hasDerivAt_cos 0).tendsto_slope_zero_right
  rw [sin_zero, neg_zero] at h
  have := h.neg
  rw [neg_zero] at this
  refine this.congr fun δ => ?_
  simp only [zero_add, cos_zero, smul_eq_mul]
  field_simp
  ring

lemma ang_tendsto_div_sin : Tendsto (fun δ : ℝ => δ / sin δ) (𝓝[>] 0) (𝓝 1) := by
  have h := (hasDerivAt_sin 0).tendsto_slope_zero_right
  rw [cos_zero] at h
  have := h.inv₀ one_ne_zero
  rw [inv_one] at this
  refine this.congr fun δ => ?_
  simp only [zero_add, sin_zero, sub_zero, smul_eq_mul, mul_inv, inv_inv]
  ring

/-- `(h_K(t + δ) - h_K(t) cos δ) / sin δ → v_K⁺(t) · v_t` as `δ → 0⁺`. -/
lemma ang_tendsto_upper {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (fun δ => (supp K (t + δ) - supp K t * cos δ) / sin δ) (𝓝[>] 0)
      (𝓝 (dot (vplus K t) (vvec t))) := by
  have hA : Tendsto (fun δ : ℝ => (supp K (t + δ) - supp K t) / δ) (𝓝[>] 0)
      (𝓝 (dot (vplus K t) (vvec t))) := by
    have h := (hasDerivWithinAt_iff_tendsto_slope.1 (hasDerivWithinAt_supp_right hK t))
    rw [Ici_sdiff_left] at h
    have := h.comp (ang_tendsto_add_nhdsGT t)
    refine this.congr fun δ => ?_
    simp only [Function.comp_apply, slope_def_field, add_sub_cancel_left]
  have hlim := ang_tendsto_div_sin.mul (hA.add (ang_tendsto_slope_cos.const_mul (supp K t)))
  rw [mul_zero, add_zero, one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT pi_pos] with δ hδ
  have hs : sin δ ≠ 0 := (sin_pos_of_pos_of_lt_pi hδ.1 hδ.2).ne'
  have hd : δ ≠ 0 := hδ.1.ne'
  field_simp
  ring

/-- `(h_K(t) cos δ - h_K(t - δ)) / sin δ → v_K⁻(t) · v_t` as `δ → 0⁺`. -/
lemma ang_tendsto_lower {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (fun δ => (supp K t * cos δ - supp K (t - δ)) / sin δ) (𝓝[>] 0)
      (𝓝 (dot (vminus K t) (vvec t))) := by
  have hB : Tendsto (fun δ : ℝ => (supp K t - supp K (t - δ)) / δ) (𝓝[>] 0)
      (𝓝 (dot (vminus K t) (vvec t))) := by
    have h := (hasDerivWithinAt_iff_tendsto_slope.1 (hasDerivWithinAt_supp_left hK t))
    rw [Iic_sdiff_right] at h
    have := h.comp (ang_tendsto_sub_nhdsGT t)
    refine this.congr fun δ => ?_
    simp only [Function.comp_apply, slope_def_field, sub_sub_cancel_left]
    rw [div_neg, ← neg_div, neg_sub]
  have hlim := ang_tendsto_div_sin.mul (hB.sub (ang_tendsto_slope_cos.const_mul (supp K t)))
  rw [mul_zero, sub_zero, one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT pi_pos] with δ hδ
  have hs : sin δ ≠ 0 := (sin_pos_of_pos_of_lt_pi hδ.1 hδ.2).ne'
  have hd : δ ≠ 0 := hδ.1.ne'
  field_simp
  ring

/-- `(h_K(t + δ) + h_K(t - δ) - 2 h_K(t) cos δ) / sin δ → σ_K(t)` as `δ → 0⁺`. -/
lemma ang_tendsto_edge_quotient {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (fun δ => (supp K (t + δ) + supp K (t - δ) - 2 * supp K t * cos δ) / sin δ)
      (𝓝[>] 0) (𝓝 (sigmaAt K t)) := by
  rw [ang_sigmaAt_eq_sub hK]
  refine ((ang_tendsto_upper hK t).sub (ang_tendsto_lower hK t)).congr fun δ => ?_
  ring

/-- Integration by parts against a Stieltjes measure for a `C¹` function. -/
lemma ang_integral_Ioc_stieltjes (F : StieltjesFunction ℝ) {g g' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g') :
    ∫ x in Ioc a b, g x ∂F.measure = g b * F b - g a * F a - ∫ x in a..b, g' x * F x := by
  set μ := F.measure.restrict (Ioc a b) with hμ
  set ν := (volume : Measure ℝ).restrict (Ioc a b) with hν
  have hμu : μ univ = ENNReal.ofReal (F b - F a) := by
    rw [hμ, Measure.restrict_apply_univ, F.measure_Ioc]
  have : IsFiniteMeasure μ := ⟨by rw [hμu]; exact ENNReal.ofReal_lt_top⟩
  have : IsFiniteMeasure ν :=
    ⟨by rw [hν, Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  set k : ℝ → ℝ → ℝ := fun x y => if x ≤ y then g' y else 0 with hk
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg'.continuousOn (s := Icc a b))
  have hkm : Measurable (Function.uncurry k) :=
    Measurable.ite (measurableSet_le measurable_fst measurable_snd)
      (hg'.measurable.comp measurable_snd) measurable_const
  have hkint : Integrable (Function.uncurry k) (μ.prod ν) := by
    refine Integrable.of_bound hkm.aestronglyMeasurable C ?_
    have hae : ∀ᵐ p ∂(μ.prod ν), p.2 ∈ Ioc a b :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hae] with p hp
    simp only [Function.uncurry, hk]
    split_ifs
    · exact hC p.2 (Ioc_subset_Icc_self hp)
    · simp only [norm_zero]; exact (norm_nonneg _).trans (hC p.2 (Ioc_subset_Icc_self hp))
  -- the fundamental theorem of calculus
  have hftc : ∀ x ∈ Ioc a b, g x = g b - ∫ y, k x y ∂ν := by
    intro x hx
    have h1 : ∫ y in x..b, g' y = g b - g x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hg y) (hg'.intervalIntegrable x b)
    have h2 : ∫ y, k x y ∂ν = ∫ y in x..b, g' y := by
      have e : (fun y => k x y) = (Ici x).indicator g' := by
        funext y; simp only [hk, indicator, mem_Ici]
      rw [e, hν, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
        intervalIntegral.integral_of_le hx.2, ← integral_Icc_eq_integral_Ioc]
      congr 2
      ext y; simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
      constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith [hx.1], h3⟩
    linarith
  -- the inner integral after swapping
  have hinner : ∀ y ∈ Ioc a b, ∫ x, k x y ∂μ = g' y * (F y - F a) := by
    intro y hy
    have e : (fun x => k x y) = (Iic y).indicator (fun _ => g' y) := by
      funext x; simp only [hk, indicator, mem_Iic]
    rw [e, integral_indicator_const _ measurableSet_Iic, smul_eq_mul, Measure.real,
      hμ, Measure.restrict_apply measurableSet_Iic]
    have : Iic y ∩ Ioc a b = Ioc a y := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hy.2⟩
    rw [this, F.measure_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 (F.mono hy.1.le))]
    ring
  have hswap := integral_integral_swap hkint
  have hint1 : Integrable (fun x => ∫ y, k x y ∂ν) μ := hkint.integral_prod_left
  calc ∫ x in Ioc a b, g x ∂F.measure = ∫ x, (g b - ∫ y, k x y ∂ν) ∂μ := by
        rw [hμ]; exact setIntegral_congr_fun measurableSet_Ioc hftc
    _ = g b * (F b - F a) - ∫ x, ∫ y, k x y ∂ν ∂μ := by
        rw [integral_sub (integrable_const _) hint1, integral_const, smul_eq_mul, Measure.real,
          hμu, ENNReal.toReal_ofReal (sub_nonneg.2 (F.mono hab))]
        ring
    _ = g b * (F b - F a) - ∫ y, g' y * (F y - F a) ∂ν := by
        rw [hswap, hν]
        congr 1
        exact setIntegral_congr_fun measurableSet_Ioc hinner
    _ = g b * F b - g a * F a - ∫ x in a..b, g' x * F x := by
        have h1 : ∫ y in a..b, g' y = g b - g a :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hg y)
            (hg'.intervalIntegrable a b)
        have hFi : IntervalIntegrable (fun y => g' y * F y) volume a b :=
          (F.mono.intervalIntegrable).continuousOn_mul hg'.continuousOn
        have e : ∫ y, g' y * (F y - F a) ∂ν = (∫ x in a..b, g' x * F x) - F a * (g b - g a) := by
          rw [hν, ← intervalIntegral.integral_of_le hab, ← h1,
            ← intervalIntegral.integral_const_mul]
          have e2 : ∫ x in a..b, g' x * (F x - F a) = ∫ x in a..b, (g' x * F x - F a * g' x) := by
            congr 1; ext x; ring
          rw [e2, intervalIntegral.integral_sub hFi ((hg'.intervalIntegrable a b).const_mul (F a))]
        rw [e]; ring

lemma ang_sigmaStieltjes_apply {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    sigmaStieltjes K t = sigmaFun K t := by
  simp [sigmaStieltjes, hK]

lemma ang_sigma_eq {K : Set (ℝ × ℝ)} : sigma K = (sigmaStieltjes K).measure := rfl

lemma ang_vplus_add_two_pi (K : Set (ℝ × ℝ)) (t : ℝ) : vplus K (t + 2 * π) = vplus K t := by
  simp only [vplus, edge, suppLine, line, supp_add_two_pi, uvec_add_two_pi, vvec_add_two_pi]

lemma ang_sigmaFun_two_pi (K : Set (ℝ × ℝ)) :
    sigmaFun K (2 * π) = sigmaFun K 0 + ∫ s in (0 : ℝ)..(2 * π), supp K s := by
  have h := ang_vplus_add_two_pi K 0
  have hv := vvec_add_two_pi 0
  rw [zero_add] at h hv
  simp only [sigmaFun, h, hv, intervalIntegral.integral_same, add_zero]

/-- For a `C¹` function `g` with `g(0) = g(2π)`,
`∫_{[0, 2π)} g dσ_K = g(0) ∫₀^{2π} h_K - ∫₀^{2π} g' F_K`, where `F_K` is the distribution function
of `σ_K`. -/
lemma ang_integral_sigma_eq {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {g g' : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g') (hg0 : g 0 = g (2 * π)) :
    ∫ t in Ico 0 (2 * π), g t ∂(sigma K) =
      g 0 * (∫ s in (0 : ℝ)..(2 * π), supp K s) - ∫ t in (0 : ℝ)..(2 * π), g' t * sigmaFun K t := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  -- `∫_{[0, 2π)} = ∫_{(0, 2π]}` by periodicity
  have hint : IntegrableOn g (Icc 0 (2 * π)) (sigma K) :=
    hgc.continuousOn.integrableOn_compact isCompact_Icc
  have hIco : ∫ t in Icc 0 (2 * π), g t ∂(sigma K) =
      (∫ t in Ico 0 (2 * π), g t ∂(sigma K)) + ∫ t in ({2 * π} : Set ℝ), g t ∂(sigma K) := by
    rw [← Ico_union_right h2π, setIntegral_union (by simp) (measurableSet_singleton _)
      (hint.mono_set Ico_subset_Icc_self)
      (hint.mono_set (singleton_subset_iff.2 ⟨h2π, le_rfl⟩))]
  have hIoc : ∫ t in Icc 0 (2 * π), g t ∂(sigma K) =
      (∫ t in ({0} : Set ℝ), g t ∂(sigma K)) + ∫ t in Ioc 0 (2 * π), g t ∂(sigma K) := by
    rw [← Ioc_insert_left h2π, insert_eq, setIntegral_union (by simp) measurableSet_Ioc
      (hint.mono_set (singleton_subset_iff.2 ⟨le_rfl, h2π⟩)) (hint.mono_set Ioc_subset_Icc_self)]
  have hsing : ∫ t in ({2 * π} : Set ℝ), g t ∂(sigma K) =
      ∫ t in ({0} : Set ℝ), g t ∂(sigma K) := by
    rw [integral_singleton, integral_singleton, ← hg0]
    congr 1
    have := sigma_periodic hK {0}
    rw [image_singleton, zero_add] at this
    simp only [Measure.real, this]
  have hIP := ang_integral_Ioc_stieltjes (sigmaStieltjes K) h2π hg hg'
  rw [← ang_sigma_eq, ang_sigmaStieltjes_apply hK, ang_sigmaStieltjes_apply hK] at hIP
  simp_rw [ang_sigmaStieltjes_apply hK] at hIP
  rw [ang_sigmaFun_two_pi, ← hg0] at hIP
  have : ∫ t in Ico 0 (2 * π), g t ∂(sigma K) = ∫ t in Ioc 0 (2 * π), g t ∂(sigma K) := by
    linarith
  rw [this, hIP]
  ring

/-! ### Convergence of the distribution functions -/

/-- At an angle where `K` has no edge, `v_{K_n}⁺(t) · v_t → v_K⁺(t) · v_t`. -/
lemma ang_tendsto_dplus {Ks : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)}
    (hKs : ∀ n, IsConvexBody (Ks n)) (hK : IsConvexBody K) (hlim : HausdorffTendsto Ks K) {t : ℝ}
    (ht : sigmaAt K t = 0) :
    Tendsto (fun n => dot (vplus (Ks n) t) (vvec t)) atTop (𝓝 (dot (vplus K t) (vvec t))) := by
  have hDm : dot (vminus K t) (vvec t) = dot (vplus K t) (vvec t) := by
    have := ang_sigmaAt_eq_sub hK t; rw [ht] at this; linarith
  rw [tendsto_order]
  constructor
  · intro a ha
    have hlow := ang_tendsto_lower hK t
    rw [hDm] at hlow
    obtain ⟨δ, hδa, hδ⟩ :=
      ((hlow.eventually (lt_mem_nhds ha)).and (Ioo_mem_nhdsGT pi_pos)).exists
    have hsin : 0 < sin δ := sin_pos_of_pos_of_lt_pi hδ.1 hδ.2
    have hconv : Tendsto (fun n => (supp (Ks n) t * cos δ - supp (Ks n) (t - δ)) / sin δ) atTop
        (𝓝 ((supp K t * cos δ - supp K (t - δ)) / sin δ)) :=
      (((ang_tendsto_supp hKs hK hlim t).mul_const (cos δ)).sub
        (ang_tendsto_supp hKs hK hlim (t - δ))).div_const _
    filter_upwards [hconv.eventually (lt_mem_nhds hδa)] with n hn
    have h1 := ang_le_dminus_mul_sin (hKs n) t δ
    have h2 := dot_vminus_le_dot_vplus (hKs n) t
    have h3 : (supp (Ks n) t * cos δ - supp (Ks n) (t - δ)) / sin δ ≤
        dot (vminus (Ks n) t) (vvec t) := by
      rw [div_le_iff₀ hsin]; exact h1
    linarith
  · intro b hb
    have hup := ang_tendsto_upper hK t
    obtain ⟨δ, hδb, hδ⟩ :=
      ((hup.eventually (gt_mem_nhds hb)).and (Ioo_mem_nhdsGT pi_pos)).exists
    have hsin : 0 < sin δ := sin_pos_of_pos_of_lt_pi hδ.1 hδ.2
    have hconv : Tendsto (fun n => (supp (Ks n) (t + δ) - supp (Ks n) t * cos δ) / sin δ) atTop
        (𝓝 ((supp K (t + δ) - supp K t * cos δ) / sin δ)) :=
      (((ang_tendsto_supp hKs hK hlim (t + δ))).sub
        ((ang_tendsto_supp hKs hK hlim t).mul_const (cos δ))).div_const _
    filter_upwards [hconv.eventually (gt_mem_nhds hδb)] with n hn
    have h1 := ang_dplus_mul_sin_le (hKs n) t δ
    have h3 : dot (vplus (Ks n) t) (vvec t) ≤
        (supp (Ks n) (t + δ) - supp (Ks n) t * cos δ) / sin δ := by
      rw [le_div_iff₀ hsin]; exact h1
    linarith

lemma ang_tendsto_sigmaFun {Ks : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)}
    (hKs : ∀ n, IsConvexBody (Ks n)) (hK : IsConvexBody K) (hlim : HausdorffTendsto Ks K) {t : ℝ}
    (ht : sigmaAt K t = 0) : Tendsto (fun n => sigmaFun (Ks n) t) atTop (𝓝 (sigmaFun K t)) := by
  refine (ang_tendsto_dplus hKs hK hlim ht).add ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun n => hausdorffDist (Ks n) K * |t - 0|) atTop (𝓝 0) := by
    simpa using hlim.mul_const |t - 0|
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0
  have hc1 := continuous_supp (hKs n).2.1
  have hc2 := continuous_supp hK.2.1
  rw [← intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => ?_
  rw [Real.norm_eq_abs]
  exact ang_abs_supp_sub_le_hausdorffDist (hKs n) hK s

lemma ang_abs_sigmaFun_le {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {R : ℝ}
    (hR : ∀ s, |supp K s| ≤ R) (t : ℝ) : |sigmaFun K t| ≤ R * (1 + |t|) := by
  have h1 := ang_dplus_mul_sin_le hK t (π / 2)
  have h2 := ang_le_dminus_mul_sin hK t (π / 2)
  have h3 := dot_vminus_le_dot_vplus hK t
  rw [sin_pi_div_two, cos_pi_div_two] at h1 h2
  have hR1 := abs_le.1 (hR (t + π / 2))
  have hR2 := abs_le.1 (hR (t - π / 2))
  have hD : |dot (vplus K t) (vvec t)| ≤ R := by
    rw [abs_le]; constructor <;> linarith
  have hI : ‖∫ s in (0 : ℝ)..t, supp K s‖ ≤ R * |t - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => by
      rw [Real.norm_eq_abs]; exact hR s
  rw [Real.norm_eq_abs, sub_zero] at hI
  unfold sigmaFun
  calc |dot (vplus K t) (vvec t) + ∫ s in (0 : ℝ)..t, supp K s|
      ≤ |dot (vplus K t) (vvec t)| + |∫ s in (0 : ℝ)..t, supp K s| := abs_add_le _ _
    _ ≤ R + R * |t| := add_le_add hD hI
    _ = R * (1 + |t|) := by ring

lemma ang_countable_sigmaAt_ne (K : Set (ℝ × ℝ)) : Set.Countable {t | sigmaAt K t ≠ 0} := by
  refine (sigmaStieltjes K).countable_leftLim_ne.mono fun t ht => ?_
  simp only [mem_ofPred_eq] at ht ⊢
  intro h
  apply ht
  unfold sigmaAt
  rw [ang_sigma_eq, StieltjesFunction.measure_singleton, h, sub_self, ENNReal.ofReal_zero,
    ENNReal.toReal_zero]

/-- Dominated convergence for `∫₀^{2π} g' F_{K_n}`. -/
lemma ang_tendsto_integral_sigmaFun {Ks : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)}
    (hKs : ∀ n, IsConvexBody (Ks n)) (hK : IsConvexBody K) (hlim : HausdorffTendsto Ks K)
    {g' : ℝ → ℝ} (hg' : Continuous g') :
    Tendsto (fun n => ∫ t in (0 : ℝ)..(2 * π), g' t * sigmaFun (Ks n) t) atTop
      (𝓝 (∫ t in (0 : ℝ)..(2 * π), g' t * sigmaFun K t)) := by
  obtain ⟨R, hR⟩ := ang_exists_abs_supp_le hK.2.1 hK.1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hg'.continuousOn (s := Icc 0 (2 * π)))
  have hev : ∀ᶠ n in atTop, ∀ s, |supp (Ks n) s| ≤ R + 1 := by
    filter_upwards [hlim.eventually (gt_mem_nhds one_pos)] with n hn s
    have h1 := abs_le.1 (ang_abs_supp_sub_le_hausdorffDist (hKs n) hK s)
    have h2 := abs_le.1 (hR s)
    rw [abs_le]; constructor <;> linarith
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => C * ((R + 1) * (1 + 2 * π))) ?_ ?_ intervalIntegrable_const ?_
  · exact Eventually.of_forall fun n =>
      (hg'.measurable.mul (monotone_sigmaFun (hKs n)).measurable).aestronglyMeasurable
  · filter_upwards [hev] with n hn
    refine Eventually.of_forall fun x hx => ?_
    rw [uIoc_of_le (by positivity)] at hx
    have hb := ang_abs_sigmaFun_le (hKs n) hn x
    rw [abs_of_pos hx.1] at hb
    have hCx := hC x (Ioc_subset_Icc_self hx)
    rw [norm_mul, Real.norm_eq_abs]
    have hR0 : 0 ≤ R + 1 := (abs_nonneg _).trans (hn 0)
    have h1 : |sigmaFun (Ks n) x| ≤ (R + 1) * (1 + 2 * π) := hb.trans (by gcongr; exact hx.2)
    exact mul_le_mul hCx h1 (abs_nonneg _) ((norm_nonneg _).trans hCx)
  · have hnull := (ang_countable_sigmaAt_ne K).measure_zero volume
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx _
    simp only [not_not] at hx
    exact tendsto_const_nhds.mul (ang_tendsto_sigmaFun hKs hK hlim hx)

/-! ### Approximation by `C¹` functions -/

/-- A continuous `2π`-periodic function is uniformly approximated on `[0, 2π]` by `C¹` functions
`g` with `g(0) = g(2π)`: its averages over short intervals. -/
lemma ang_exists_C1_approx {f : ℝ → ℝ} (hf : Continuous f) (hper : Function.Periodic f (2 * π))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g g' : ℝ → ℝ, (∀ x, HasDerivAt g (g' x) x) ∧ Continuous g' ∧ g 0 = g (2 * π) ∧
      ∀ x ∈ Icc 0 (2 * π), |f x - g x| ≤ ε := by
  have huc := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π + 1)).uniformContinuousOn_of_continuous
    hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨η, hη, hηf⟩ := huc ε hε
  set δ := min (η / 2) 1 with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) one_pos
  have hδη : δ < η := (min_le_left _ _).trans_lt (by linarith)
  have hδ1 : δ ≤ 1 := min_le_right _ _
  set Φ : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, f s with hΦ
  have hΦd : ∀ x, HasDerivAt Φ (f x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hgΦ : ∀ x, ∫ s in x..x + δ, f s = Φ (x + δ) - Φ x := fun x =>
    (intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _)).symm
  refine ⟨fun x => δ⁻¹ * ∫ s in x..x + δ, f s, fun x => δ⁻¹ * (f (x + δ) - f x), ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [hgΦ]
    have h1 : HasDerivAt (fun x => Φ (x + δ)) (f (x + δ)) x :=
      HasDerivAt.comp_add_const x δ (hΦd (x + δ))
    exact (h1.sub (hΦd x)).const_mul δ⁻¹
  · fun_prop
  · simp only
    congr 1
    have := intervalIntegral.integral_comp_add_right (fun s => f s) (a := 0) (b := δ) (2 * π)
    simp only [zero_add] at this
    rw [zero_add, add_comm (2 * π) δ, ← this]
    exact intervalIntegral.integral_congr fun s _ => (hper s).symm
  · intro x hx
    have hbound : ∀ s ∈ Set.uIoc x (x + δ), ‖f x - f s‖ ≤ ε := by
      intro s hs
      rw [uIoc_of_le (by linarith)] at hs
      have h1 : x ∈ Icc 0 (2 * π + 1) := ⟨hx.1, by linarith [hx.2]⟩
      have h2 : s ∈ Icc 0 (2 * π + 1) := ⟨by linarith [hx.1, hs.1], by linarith [hx.2, hs.2]⟩
      have h3 : dist x s < η := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith [hs.1])]; linarith [hs.2]
      exact (hηf x h1 s h2 h3).le
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hf.intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul, show x + δ - x = δ by ring,
      abs_of_pos hδ0, Real.norm_eq_abs] at hint
    have e : f x - δ⁻¹ * ∫ s in x..x + δ, f s = δ⁻¹ * (δ * f x - ∫ s in x..x + δ, f s) := by
      field_simp
    show |f x - δ⁻¹ * ∫ s in x..x + δ, f s| ≤ ε
    rw [e, abs_mul, abs_of_pos (inv_pos.2 hδ0)]
    calc δ⁻¹ * |δ * f x - ∫ s in x..x + δ, f s| ≤ δ⁻¹ * (ε * δ) := by gcongr
      _ = ε := by field_simp

/-! ### Theorem 4.1.3 -/

lemma ang_tendsto_integral_supp {Ks : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)}
    (hKs : ∀ n, IsConvexBody (Ks n)) (hK : IsConvexBody K) (hlim : HausdorffTendsto Ks K)
    (a b : ℝ) :
    Tendsto (fun n => ∫ s in a..b, supp (Ks n) s) atTop (𝓝 (∫ s in a..b, supp K s)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun n => hausdorffDist (Ks n) K * |b - a|) atTop (𝓝 0) := by
    simpa using hlim.mul_const |b - a|
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0
  have hc1 := continuous_supp (hKs n).2.1
  have hc2 := continuous_supp hK.2.1
  rw [← intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => ?_
  rw [Real.norm_eq_abs]
  exact ang_abs_supp_sub_le_hausdorffDist (hKs n) hK s

/-- **Theorem 4.1.3** (`thm:surface-area-weak-convergence`, Schneider Theorem 4.2.1). If convex bodies
`K_n` converge to `K` in the Hausdorff distance, then `σ_{K_n} → σ_K` weakly as measures on `S¹`:
for every continuous `2π`-periodic `f`, `∫_{[0, 2π)} f dσ_{K_n} → ∫_{[0, 2π)} f dσ_K`. -/
theorem theorem4_1_3 {Ks : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)} (hKs : ∀ n, IsConvexBody (Ks n))
    (hK : IsConvexBody K) (hlim : HausdorffTendsto Ks K) {f : ℝ → ℝ} (hf : Continuous f)
    (hper : Function.Periodic f (2 * π)) :
    Tendsto (fun n => ∫ t in Ico 0 (2 * π), f t ∂(sigma (Ks n))) atTop
      (𝓝 (∫ t in Ico 0 (2 * π), f t ∂(sigma K))) := by
  -- convergence for `C¹` functions, by integration by parts
  have hC1 : ∀ g g' : ℝ → ℝ, (∀ x, HasDerivAt g (g' x) x) → Continuous g' → g 0 = g (2 * π) →
      Tendsto (fun n => ∫ t in Ico 0 (2 * π), g t ∂(sigma (Ks n))) atTop
        (𝓝 (∫ t in Ico 0 (2 * π), g t ∂(sigma K))) := by
    intro g g' hg hg' hg0
    have e : (fun n => ∫ t in Ico 0 (2 * π), g t ∂(sigma (Ks n))) = fun n =>
        g 0 * (∫ s in (0 : ℝ)..(2 * π), supp (Ks n) s) -
          ∫ t in (0 : ℝ)..(2 * π), g' t * sigmaFun (Ks n) t :=
      funext fun n => ang_integral_sigma_eq (hKs n) hg hg' hg0
    rw [e, ang_integral_sigma_eq hK hg hg' hg0]
    exact ((ang_tendsto_integral_supp hKs hK hlim 0 (2 * π)).const_mul (g 0)).sub
      (ang_tendsto_integral_sigmaFun hKs hK hlim hg')
  -- the total masses converge
  have hmass : ∀ L : Set (ℝ × ℝ), ∫ t in Ico 0 (2 * π), (1 : ℝ) ∂(sigma L) =
      (sigma L (Ico 0 (2 * π))).toReal := fun L => by
    rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real]
  have hm := hC1 (fun _ => 1) (fun _ => 0) (fun x => hasDerivAt_const x 1) continuous_const rfl
  simp only [hmass] at hm
  -- an `ε / 3` argument
  rw [Metric.tendsto_atTop]
  intro ε hε
  set M := (sigma K (Ico 0 (2 * π))).toReal with hM
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  set η := ε / (6 * (M + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨g, g', hg, hg', hg0, happrox⟩ := ang_exists_C1_approx hf hper hη0
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  have hconv := hC1 g g' hg hg' hg0
  rw [Metric.tendsto_atTop] at hconv hm
  obtain ⟨N1, hN1⟩ := hconv (ε / 3) (by positivity)
  obtain ⟨N2, hN2⟩ := hm 1 one_pos
  -- `|∫ f dσ_L - ∫ g dσ_L| ≤ η σ_L([0, 2π))`
  have happ : ∀ L : Set (ℝ × ℝ), |(∫ t in Ico 0 (2 * π), f t ∂(sigma L)) -
      ∫ t in Ico 0 (2 * π), g t ∂(sigma L)| ≤ η * (sigma L (Ico 0 (2 * π))).toReal := by
    intro L
    have hfi : IntegrableOn f (Ico 0 (2 * π)) (sigma L) :=
      (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ico_subset_Icc_self
    have hgi : IntegrableOn g (Ico 0 (2 * π)) (sigma L) :=
      (hgc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ico_subset_Icc_self
    rw [← integral_sub hfi hgi, ← Real.norm_eq_abs]
    have := norm_setIntegral_le_of_norm_le_const (μ := sigma L) (s := Ico 0 (2 * π))
      (f := fun x => f x - g x) (C := η) measure_Ico_lt_top fun x hx => by
        rw [Real.norm_eq_abs]; exact happrox x (Ico_subset_Icc_self hx)
    exact this
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have e1 := happ (Ks n)
  have e2 := happ K
  have e3 := hN1 n (le_of_max_le_left hn)
  have e4 := hN2 n (le_of_max_le_right hn)
  rw [Real.dist_eq] at e3 e4 ⊢
  have hmn : (sigma (Ks n) (Ico 0 (2 * π))).toReal < M + 1 := by
    have := (abs_lt.1 e4).2; linarith
  have hmn0 : 0 ≤ (sigma (Ks n) (Ico 0 (2 * π))).toReal := ENNReal.toReal_nonneg
  have hη1 : η * (sigma (Ks n) (Ico 0 (2 * π))).toReal + η * M ≤ ε / 3 := by
    have : η * (sigma (Ks n) (Ico 0 (2 * π))).toReal + η * M ≤ η * (2 * (M + 1)) := by
      nlinarith
    calc η * (sigma (Ks n) (Ico 0 (2 * π))).toReal + η * M ≤ η * (2 * (M + 1)) := this
      _ = ε / 3 := by rw [hη]; field_simp; ring
  set A := ∫ t in Ico 0 (2 * π), f t ∂(sigma (Ks n))
  set B := ∫ t in Ico 0 (2 * π), g t ∂(sigma (Ks n))
  set C := ∫ t in Ico 0 (2 * π), g t ∂(sigma K)
  set D := ∫ t in Ico 0 (2 * π), f t ∂(sigma K)
  have t1 := abs_sub_le A B D
  have t2 := abs_sub_le B C D
  rw [abs_sub_comm C D] at t2
  linarith

/-- The analogue of Lemma 4.1.1 for the left wedge gaps: `|z_K° - z_{K'}°| ≤ (1 + sec ω) ε`. -/
lemma ang_abs_wedgeGapZInf_sub_le {K K' : Set (ℝ × ℝ)} {ω : ℝ} (hω : ω < π / 2) (hK : IsCap K ω)
    (hK' : IsCap K' ω) :
    |wedgeGapZInf K ω - wedgeGapZInf K' ω| ≤ (1 + 1 / cos ω) * hausdorffDist K K' := by
  have hcb := hK.2.1
  have hcb' := hK'.2.1
  have hω0 := hK.1.1
  have hcos := ang_cos_pos_of_cap hK.1 hω
  set ε := hausdorffDist K K' with hεdef
  have hε : 0 ≤ ε := ang_hausdorffDist_nonneg hcb hcb'
  have key : ∀ t ∈ Ioo 0 ω, |wedgeGapZ K ω t - wedgeGapZ K' ω t| ≤ (1 + 1 / cos ω) * ε := by
    intro t ht
    have hct : cos ω ≤ cos (ω - t) :=
      cos_le_cos_of_nonneg_of_le_pi (by linarith [ht.2]) (by linarith [pi_pos]) (by linarith [ht.1])
    have hct0 : 0 < cos (ω - t) := by linarith
    rw [ang_wedgeGapZ_eq, ang_wedgeGapZ_eq]
    have h0 := ang_abs_supp_sub_le_hausdorffDist hcb hcb' (ω + π / 2)
    have h1 := ang_abs_supp_sub_le_hausdorffDist hcb hcb' (t + π / 2)
    have e : supp K (ω + π / 2) - (supp K (t + π / 2) - 1) / cos (ω - t) -
        (supp K' (ω + π / 2) - (supp K' (t + π / 2) - 1) / cos (ω - t)) =
        (supp K (ω + π / 2) - supp K' (ω + π / 2)) -
          (supp K (t + π / 2) - supp K' (t + π / 2)) / cos (ω - t) := by
      field_simp; ring
    rw [e]
    calc |(supp K (ω + π / 2) - supp K' (ω + π / 2)) -
          (supp K (t + π / 2) - supp K' (t + π / 2)) / cos (ω - t)|
        ≤ |supp K (ω + π / 2) - supp K' (ω + π / 2)| +
          |(supp K (t + π / 2) - supp K' (t + π / 2)) / cos (ω - t)| := abs_sub _ _
      _ = |supp K (ω + π / 2) - supp K' (ω + π / 2)| +
          |supp K (t + π / 2) - supp K' (t + π / 2)| / cos (ω - t) := by
          rw [abs_div, abs_of_pos hct0]
      _ ≤ ε + ε / cos (ω - t) := by gcongr
      _ ≤ ε + ε / cos ω := by gcongr
      _ = (1 + 1 / cos ω) * ε := by ring
  rw [abs_le]
  constructor
  · have : wedgeGapZInf K' ω - (1 + 1 / cos ω) * ε ≤ wedgeGapZInf K ω := by
      refine ang_le_wedgeGapZInf hω0 fun t ht => ?_
      have h1 := ang_wedgeGapZInf_le hcb' hω ht
      have h2 := (abs_le.1 (key t ht)).1
      linarith
    linarith
  · have : wedgeGapZInf K ω - (1 + 1 / cos ω) * ε ≤ wedgeGapZInf K' ω := by
      refine ang_le_wedgeGapZInf hω0 fun t ht => ?_
      have h1 := ang_wedgeGapZInf_le hcb hω ht
      have h2 := (abs_le.1 (key t ht)).2
      linarith
    linarith

/-- If `a_n ≤ σ_{K_n}(t)`, `a_n → a` and `K_n → K`, then `a ≤ σ_K(t)` (upper semicontinuity of the
edge lengths). -/
lemma ang_le_sigmaAt_of_tendsto {Ks : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)}
    (hKs : ∀ n, IsConvexBody (Ks n)) (hK : IsConvexBody K) (hlim : HausdorffTendsto Ks K)
    {a : ℕ → ℝ} {a₀ t : ℝ} (ha : Tendsto a atTop (𝓝 a₀)) (hle : ∀ n, a n ≤ sigmaAt (Ks n) t) :
    a₀ ≤ sigmaAt K t := by
  have hQ : ∀ δ ∈ Ioo 0 π,
      a₀ ≤ (supp K (t + δ) + supp K (t - δ) - 2 * supp K t * cos δ) / sin δ := by
    intro δ hδ
    have hsin : 0 < sin δ := sin_pos_of_pos_of_lt_pi hδ.1 hδ.2
    have hconv := (((ang_tendsto_supp hKs hK hlim (t + δ)).add
      (ang_tendsto_supp hKs hK hlim (t - δ))).sub
      ((ang_tendsto_supp hKs hK hlim t).const_mul 2 |>.mul_const (cos δ))).div_const (sin δ)
    refine le_of_tendsto_of_tendsto' ha hconv fun n => ?_
    have h2 := ang_sigmaAt_mul_sin_le (hKs n) t δ
    rw [le_div_iff₀ hsin]
    nlinarith [hle n]
  refine ge_of_tendsto (ang_tendsto_edge_quotient hK t) ?_
  filter_upwards [Ioo_mem_nhdsGT pi_pos] with δ hδ using hQ δ hδ

/-- **Theorem 4.1.4** (`thm:balanced-maximum-sofa-ineq`). For `ω < π/2`, a balanced maximum cap
satisfies `σ_K(π/2) ≥ w_K°` and `σ_K(ω) ≥ z_K°`. -/
theorem theorem4_1_4 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsBalancedMaxCap K ω) (hω : ω < π / 2) :
    wedgeGapWInf K ω ≤ sigmaAt K (π / 2) ∧ wedgeGapZInf K ω ≤ sigmaAt K ω := by
  obtain ⟨hω', hcap, k, Ks, -, hmax, hlim⟩ := hK
  have hcapn : ∀ i, IsCap (Ks i) ω := fun i => (hmax i).1.1
  have hcbn : ∀ i, IsConvexBody (Ks i) := fun i => (hcapn i).2.1
  have h0 : Tendsto (fun i => (1 + 1 / cos ω) * hausdorffDist (Ks i) K) atTop (𝓝 0) := by
    simpa using hlim.const_mul (1 + 1 / cos ω)
  constructor
  · have hw : Tendsto (fun i => wedgeGapWInf (Ks i) ω) atTop (𝓝 (wedgeGapWInf K ω)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun _ => norm_nonneg _) (fun i => lemma4_1_1 hω (hcapn i) hcap) h0
    exact ang_le_sigmaAt_of_tendsto hcbn hcap.2.1 hlim hw fun i => ang_theorem4_1_2_w (hmax i) hω
  · have hz : Tendsto (fun i => wedgeGapZInf (Ks i) ω) atTop (𝓝 (wedgeGapZInf K ω)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun _ => norm_nonneg _)
        (fun i => ang_abs_wedgeGapZInf_sub_le hω (hcapn i) hcap) h0
    exact ang_le_sigmaAt_of_tendsto hcbn hcap.2.1 hlim hz fun i => ang_theorem4_1_2_z (hmax i) hω

end MovingSofaOptimality
