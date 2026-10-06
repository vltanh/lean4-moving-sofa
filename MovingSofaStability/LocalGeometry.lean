module

public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import MovingSofaStability.Margins

/-!
# The geometry of a cap near Gerver's cap

The exposed faces, arm margins and core of a right-angle cap whose upper support function is close to
Gerver's persist under small perturbations; its niche lies in the cap, and its canonical triple lies in
`T̄`.

The sections below follow the steps of the proof.
-/

@[expose] public section
noncomputable section

/-!
## Uniform stability of exposed-face properties

A positive continuous property on the reference exposed faces persists for every
point of every nearby exposed face. This covers atoms in the competitor and does
not presume derivative convergence at a multiple-point face of the reference.

The proof takes a minimum of a membership/face defect on a fixed compact set.
It does not require a metric or a differentiable structure on the space of caps.
-/

section ExposedFaceStability

open Real Set Metric
open scoped Pointwise
open MovingSofaOptimality

namespace MovingSofaStability

/-- Caps in a unit support neighborhood share a fixed compact containing body. -/
theorem cap_subset_unit_parallel {K K₀ : Set Point} (hK : IsCap K (π / 2))
    (h₀ : IsCap K₀ (π / 2)) {δ : ℝ} (hδ : δ ≤ 1)
    (hclose : UpperSupportClose δ K K₀) : K ⊆ K₀ + euclideanDisk 1 := by
  intro p hp
  have hsum := convexBody_add h₀.2.1 (euclideanDisk_isConvexBody (by norm_num : (0 : ℝ) ≤ 1))
  apply (mem_iff_forall_dot_le_supp hsum p).2
  intro t
  rw [supp_add_euclideanDisk h₀.2.1 (by norm_num)]
  have he := (abs_le.mp (upperSupportClose_all hK h₀ hclose t)).2
  have hpoint := dot_le_supp hK.2.1.2.1 hp t
  linarith

/-- Strict continuous inequalities on exposed faces are uniform under cap perturbation. -/
theorem exposed_face_property_stable {K₀ : Set Point} (h₀ : IsCap K₀ (π / 2))
    {I : Set ℝ} (hI : IsCompact I) (hIupper : I ⊆ Icc (0 : ℝ) π)
    (F : Point → ℝ → ℝ)
    (hF : ContinuousOn (fun z : Point × ℝ => F z.1 z.2)
      ((K₀ + euclideanDisk 1) ×ˢ I))
    (hpositive : ∀ t ∈ I, ∀ p ∈ edge K₀ t, 0 < F p t) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K K₀ →
        ∀ t ∈ I, ∀ p ∈ edge K t, 0 < F p t := by
  classical
  let B := K₀ + euclideanDisk 1
  have hB : IsCompact B :=
    (convexBody_add h₀.2.1 (euclideanDisk_isConvexBody (by norm_num : (0 : ℝ) ≤ 1))).2.1
  have : CompactSpace ↥B := isCompact_iff_compactSpace.mp hB
  have : CompactSpace ↥I := isCompact_iff_compactSpace.mp hI
  let defect : ↥B × ↥I → ℝ := fun z => Metric.infDist z.1.1 K₀ +
    |dot z.1.1 (uvec z.2.1) - supp K₀ z.2.1|
  let property : ↥B × ↥I → ℝ := fun z => F z.1.1 z.2.1
  have hmap : Continuous (fun z : ↥B × ↥I => (z.1.1, z.2.1)) := by fun_prop
  have hprop : Continuous property := by
    exact hF.comp_continuous hmap (fun z => ⟨z.1.2, z.2.2⟩)
  have hdef : Continuous defect := by
    apply Continuous.add
    · exact (Metric.continuous_infDist_pt K₀).comp (continuous_subtype_val.comp continuous_fst)
    · apply Continuous.abs
      apply Continuous.sub
      · exact continuous_dot_pair.comp
          ((continuous_subtype_val.comp continuous_fst).prodMk
            (continuous_uvec.comp (continuous_subtype_val.comp continuous_snd)))
      · exact h₀.2.1.continuous_supp.comp (continuous_subtype_val.comp continuous_snd)
  let bad : Set (↥B × ↥I) := {z | property z ≤ 0}
  have hbad : IsCompact bad := (isClosed_le hprop continuous_const).isCompact
  have hpos : ∀ z ∈ bad, 0 < defect z := by
    intro z hz
    by_contra hnot
    have hdist0 : Metric.infDist z.1.1 K₀ = 0 := by
      have hn := Metric.infDist_nonneg (x := z.1.1) (s := K₀)
      have ha := abs_nonneg (dot z.1.1 (uvec z.2.1) - supp K₀ z.2.1)
      change ¬0 < Metric.infDist z.1.1 K₀ +
        |dot z.1.1 (uvec z.2.1) - supp K₀ z.2.1| at hnot
      linarith
    have hgap0 : dot z.1.1 (uvec z.2.1) = supp K₀ z.2.1 := by
      change ¬0 < Metric.infDist z.1.1 K₀ +
        |dot z.1.1 (uvec z.2.1) - supp K₀ z.2.1| at hnot
      rw [hdist0, zero_add] at hnot
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (not_lt.mp hnot) (abs_nonneg _)))
    have hp : z.1.1 ∈ K₀ := (h₀.2.1.2.1.isClosed.mem_iff_infDist_zero h₀.2.1.1).2 hdist0
    have hh := hpositive z.2.1 z.2.2 z.1.1 ⟨hp, hgap0⟩
    exact (not_lt_of_ge hz) hh
  obtain ⟨m, hm, hmin⟩ := hbad.exists_forall_le' hdef.continuousOn hpos
  let δ := min 1 (m / 4)
  have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδm : 2 * δ < m := by
    have h := min_le_right (1 : ℝ) (m / 4)
    change δ ≤ m / 4 at h
    linarith
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro K hK hclose t ht p hp
  have hpB := cap_subset_unit_parallel hK h₀ hδ1 hclose hp.1
  let z : ↥B × ↥I := (⟨p, hpB⟩, ⟨t, ht⟩)
  by_contra hnot
  have hzbad : z ∈ bad := not_lt.mp hnot
  have hd : m ≤ defect z := hmin z hzbad
  have hcapclose := upperSupportClose_euclidean hδ.le hK h₀ hclose
  obtain ⟨q, hq, hpq⟩ := hcapclose.1 p hp.1
  have hdist : Metric.infDist p K₀ ≤ δ := by
    have hprod : dist p q ≤ euclideanDist p q := by
      rw [dist_eq_norm]
      exact product_norm_le_norm2 (p - q)
    exact (Metric.infDist_le_dist_of_mem hq).trans (hprod.trans hpq)
  have hsupport : |dot p (uvec t) - supp K₀ t| ≤ δ := by
    rw [hp.2]
    exact hclose t (hIupper ht)
  change m ≤ Metric.infDist p K₀ + |dot p (uvec t) - supp K₀ t| at hd
  linarith


end MovingSofaStability

end ExposedFaceStability

/-!
## Uniform arm margins near an injective reference

The reference cap is injective; a competitor need only be a normalized cap. Both
endpoints of every competing exposed face satisfy the margin, so polygonal and
other nonsmooth competitors are included.
-/

section LocalArmMargins

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

theorem UpperSupportClose.mono {δ R : ℝ} {K L : Set Point}
    (h : UpperSupportClose δ K L) (hδ : δ ≤ R) : UpperSupportClose R K L :=
  fun t ht => (h t ht).trans hδ

theorem injective_face_eq_aK {K : Set Point} (hK : IsCap K (π / 2)) (hI : InjCond1 K)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) (π / 2)) {p : Point} (hp : p ∈ edge K t) : p = aK K t := by
  have he := inj_vplus_eq_vminus_of_injCond1 hK.2.1 hI (Or.inl ht)
  rw [edge_eq_segment hK.2.1 t, he, segment_same] at hp
  exact mem_singleton_iff.mp hp

theorem injective_face_eq_cK {K : Set Point} (hK : IsCap K (π / 2)) (hI : InjCond1 K)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) (π / 2)) {p : Point} (hp : p ∈ edge K (t + π / 2)) :
    p = cK K t := by
  have he := inj_vplus_eq_vminus_of_injCond1 hK.2.1 hI (t := t + π / 2)
    (Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  rw [edge_eq_segment hK.2.1 (t + π / 2), ← he, segment_same] at hp
  exact mem_singleton_iff.mp hp

/-- A margin for all contacts at all normals of a compact interior angular interval. -/
def CoreArmMargin (K : Set Point) (a b c : ℝ) : Prop :=
  (∀ t ∈ Icc a b, ∀ p ∈ edge K t,
      1 + c ≤ supp K (t + π / 2) - dot p (vvec t)) ∧
  (∀ t ∈ Icc a b, ∀ p ∈ edge K (t + π / 2),
      1 + c ≤ supp K t - dot p (uvec t))

/-- The needed regularity is on the reference, not on every cap in its neighborhood. -/
theorem core_arm_margin_near_reference {K₀ : Set Point} (h₀ : IsKi K₀)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < π / 2) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K K₀ →
        CoreArmMargin K a b c := by
  have hcap := h₀.1
  have hI := h₀.2.1.1
  have hsub : Icc a b ⊆ Icc (0 : ℝ) (π / 2) := Icc_subset_Icc ha.le hb.le
  obtain ⟨-, -, hfc, hgc⟩ := proposition6_4_6_continuous hcap hI
  have hpositive : ∀ t ∈ Icc a b, 0 < min (fK K₀ t - 1) (gK K₀ t - 1) := by
    intro t ht
    have hti : t ∈ Ioo (0 : ℝ) (π / 2) := ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
    -- The source returns gPlus first, fMinus second.
    obtain ⟨hg, hf⟩ := opt_arm_gt_one h₀ hti
    exact lt_min (sub_pos.mpr hf) (sub_pos.mpr hg)
  obtain ⟨m, hm, hmle⟩ := isCompact_Icc.exists_forall_le'
    (((hfc.mono hsub).sub continuousOn_const).inf ((hgc.mono hsub).sub continuousOn_const))
    hpositive
  let FA := fun p : Point => fun t : ℝ => supp K₀ (t + π / 2) - dot p (vvec t) - 1 - m / 2
  let FC := fun p : Point => fun t : ℝ => supp K₀ (t - π / 2) - dot p (uvec (t - π / 2)) - 1 - m / 2
  have hFA : Continuous (fun z : Point × ℝ => FA z.1 z.2) := by
    apply Continuous.sub
    apply Continuous.sub
    apply Continuous.sub
    · exact hcap.2.1.continuous_supp.comp (continuous_snd.add continuous_const)
    · exact continuous_dot_pair.comp (continuous_fst.prodMk (continuous_vvec.comp continuous_snd))
    · exact continuous_const
    · exact continuous_const
  have hFC : Continuous (fun z : Point × ℝ => FC z.1 z.2) := by
    apply Continuous.sub
    apply Continuous.sub
    apply Continuous.sub
    · exact hcap.2.1.continuous_supp.comp (continuous_snd.sub continuous_const)
    · exact continuous_dot_pair.comp
        (continuous_fst.prodMk (continuous_uvec.comp (continuous_snd.sub continuous_const)))
    · exact continuous_const
    · exact continuous_const
  obtain ⟨δA, hδA, -, hA⟩ := exposed_face_property_stable hcap isCompact_Icc
    (I := Icc a b)
    (fun t ht => ⟨ha.le.trans ht.1, ht.2.trans hb.le |>.trans (by linarith [pi_pos])⟩)
    FA hFA.continuousOn (by
      intro t ht p hp
      have he := injective_face_eq_aK hcap hI
        ⟨ha.le.trans ht.1, ht.2.trans_lt hb⟩ hp
      rw [he]
      have hf : m ≤ fK K₀ t - 1 := (hmle t ht).trans (min_le_left _ _)
      have hform : supp K₀ (t + π / 2) - dot (aK K₀ t) (vvec t) = fK K₀ t := by
        exact (inj_fMinus_eq K₀ t).symm
      change 0 < supp K₀ (t + π / 2) - dot (aK K₀ t) (vvec t) - 1 - m / 2
      rw [hform]
      linarith)
  obtain ⟨δC, hδC, -, hC⟩ := exposed_face_property_stable hcap isCompact_Icc
    (I := Icc (a + π / 2) (b + π / 2))
    (fun t ht => ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩)
    FC hFC.continuousOn (by
      intro t ht p hp
      have hti : t - π / 2 ∈ Icc a b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hp' : p ∈ edge K₀ ((t - π / 2) + π / 2) := by simpa only [sub_add_cancel] using hp
      have he := injective_face_eq_cK hcap hI
        ⟨by linarith [hti.1], by linarith [hti.2]⟩ hp'
      rw [he]
      have hg : m ≤ gK K₀ (t - π / 2) - 1 := (hmle (t - π / 2) hti).trans (min_le_right _ _)
      have hform : supp K₀ (t - π / 2) - dot (cK K₀ (t - π / 2)) (uvec (t - π / 2)) =
          gK K₀ (t - π / 2) := by
        simp only [gK, gPlus, dot_sub_left, inj_dot_outerCorner_uvec, cK]
      change 0 < supp K₀ (t - π / 2) - dot (cK K₀ (t - π / 2)) (uvec (t - π / 2)) - 1 - m / 2
      rw [hform]
      linarith)
  let δ := min 1 (min (m / 4) (min δA δC))
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min (by linarith) (lt_min hδA hδC))
  have hδm : δ ≤ m / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδA' : δ ≤ δA := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδC' : δ ≤ δC := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨m / 4, δ, by linarith, hδ, min_le_left _ _, ?_⟩
  intro K hK hclose
  constructor
  · intro t ht p hp
    have hh := hA K hK (hclose.mono hδA') t ht p hp
    have he := (abs_le.mp (hclose (t + π / 2)
      ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩)).1
    change 0 < supp K₀ (t + π / 2) - dot p (vvec t) - 1 - m / 2 at hh
    linarith
  · intro t ht p hp
    have hh := hC K hK (hclose.mono hδC') (t + π / 2)
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ p hp
    have he := (abs_le.mp (hclose t ⟨by linarith [ht.1], by linarith [ht.2, pi_pos]⟩)).1
    change 0 < supp K₀ (t + π / 2 - π / 2) - dot p (uvec (t + π / 2 - π / 2)) - 1 - m / 2 at hh
    rw [add_sub_cancel_right] at hh
    linarith

/-- One-sided arm values inherit the all-face margin. -/
theorem CoreArmMargin.oneSided {K : Set Point} (hK : IsCap K (π / 2))
    {a b c : ℝ} (h : CoreArmMargin K a b c) {t : ℝ} (ht : t ∈ Icc a b) :
    1 + c ≤ fPlus K t ∧ 1 + c ≤ fMinus K t ∧
      1 + c ≤ gPlus K t ∧ 1 + c ≤ gMinus K t := by
  have h1 := h.1 t ht (vplus K t) (vplus_mem_edge hK.2.1 t)
  have h2 := h.1 t ht (vminus K t) (vminus_mem_edge hK.2.1 t)
  have h3 := h.2 t ht (vplus K (t + π / 2)) (vplus_mem_edge hK.2.1 _)
  have h4 := h.2 t ht (vminus K (t + π / 2)) (vminus_mem_edge hK.2.1 _)
  rw [← inj_fPlus_eq] at h1
  rw [← inj_fMinus_eq] at h2
  simp only [gPlus, gMinus, cPlus, cMinus, dot_sub_left, inj_dot_outerCorner_uvec]
  exact ⟨h1, h2, h3, h4⟩

end MovingSofaStability

end LocalArmMargins

/-!
## Core monotonicity without differentiating through curvature atoms

The one-sided fundamental theorem bounds increments by a constant derivative
bound; no integrability or continuity of the competing right derivative is
presumed. This is enough for a strictly monotone core graph and for the local
cut-separation argument.
-/

section CoreMonotonicity

open Real Set MeasureTheory
open MovingSofaOptimality

namespace MovingSofaStability

def cornerRightVelocity (K : Set Point) (t : ℝ) : Point :=
  -(fPlus K t - 1) • uvec t + (gPlus K t - 1) • vvec t

theorem corner_hasRightDeriv {K : Set Point} (hK : IsCap K (π / 2)) (t : ℝ) :
    HasDerivWithinAt (innerCorner K) (cornerRightVelocity K t) (Ioi t) t :=
  (theorem6_2_3_right hK).2.mono Ioi_subset_Ici_self

/-- Project a vector right derivative onto a fixed unit normal. -/
theorem hasRightDeriv_dot_uvec {x dx : ℝ → Point} {t d : ℝ}
    (h : HasDerivWithinAt x (dx t) (Ioi t) t) :
    HasDerivWithinAt (fun s => dot (x s) (uvec d)) (dot (dx t) (uvec d)) (Ioi t) t := by
  have h1 : HasDerivWithinAt (fun s => (x s).1) (dx t).1 (Ioi t) t :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := x t)).comp_hasDerivWithinAt t h
  have h2 : HasDerivWithinAt (fun s => (x s).2) (dx t).2 (Ioi t) t :=
    (hasFDerivAt_snd (𝕜 := ℝ) (p := x t)).comp_hasDerivWithinAt t h
  exact (h1.mul_const (cos d)).add (h2.mul_const (sin d))

/-- The constant comparison version of the one-sided fundamental theorem. -/
theorem right_derivative_increment_le {f df : ℝ → ℝ} {a b B : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hB : ∀ t ∈ Ioo a b, df t ≤ B) : f b - f a ≤ B * (b - a) := by
  have h := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab hf hd
    (φ := fun _ => B) (continuousOn_const.integrableOn_compact isCompact_Icc) hB
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h

theorem right_derivative_increment_ge {f df : ℝ → ℝ} {a b B : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hB : ∀ t ∈ Ioo a b, B ≤ df t) : B * (b - a) ≤ f b - f a := by
  have h := right_derivative_increment_le hab hf.neg
    (fun t ht => (hd t ht).neg) (B := -B) (fun t ht => neg_le_neg (hB t ht))
  simp only [Pi.neg_apply] at h
  linarith

theorem sin_add_cos_ge_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (π / 2)) :
    1 ≤ sin t + cos t := by
  have hs := sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, pi_pos])
  have hc := cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, pi_pos], ht.2⟩
  have h := sin_sq_add_cos_sq t
  nlinarith [sin_le_one t, cos_le_one t]

/-- The core's horizontal velocity has a uniform strictly negative upper bound. -/
theorem CoreArmMargin.velocity_fst_le {K : Set Point} (hK : IsCap K (π / 2))
    {a b c t : ℝ} (h : CoreArmMargin K a b c) (hc : 0 ≤ c)
    (ht : t ∈ Icc a b) (hti : t ∈ Icc (0 : ℝ) (π / 2)) :
    (cornerRightVelocity K t).1 ≤ -c := by
  obtain ⟨hf, -, hg, -⟩ := h.oneSided hK ht
  have hs := sin_nonneg_of_nonneg_of_le_pi hti.1 (by linarith [hti.2, pi_pos])
  have hcos := cos_nonneg_of_mem_Icc ⟨by linarith [hti.1, pi_pos], hti.2⟩
  have hfc := mul_le_mul_of_nonneg_right (show c ≤ fPlus K t - 1 by linarith) hcos
  have hgs := mul_le_mul_of_nonneg_right (show c ≤ gPlus K t - 1 by linarith) hs
  have hcprod := mul_le_mul_of_nonneg_left (sin_add_cos_ge_one hti) hc
  simp only [cornerRightVelocity, Prod.fst_add, Prod.smul_fst, smul_eq_mul, uvec_fst, vvec_fst]
  nlinarith

/-- Every core chord has a definite horizontal decrease. -/
theorem CoreArmMargin.horizontal_decrease {K : Set Point} (hK : IsCap K (π / 2))
    {a b c : ℝ} (h : CoreArmMargin K a b c) (hc : 0 ≤ c)
    (ha : 0 ≤ a) (hb : b ≤ π / 2) {u v : ℝ}
    (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u ≤ v) :
    (innerCorner K v).1 - (innerCorner K u).1 ≤ -c * (v - u) := by
  apply right_derivative_increment_le huv (opt_innerCorner_continuous hK.2.1).fst.continuousOn
    (fun t ht => (corner_hasRightDeriv hK t).fst)
  intro t ht
  exact h.velocity_fst_le hK hc ⟨hu.1.trans ht.1.le, ht.2.le.trans hv.2⟩
    ⟨ha.trans (hu.1.trans ht.1.le), (ht.2.le.trans hv.2).trans hb⟩

theorem CoreArmMargin.strictAnti_core {K : Set Point} (hK : IsCap K (π / 2))
    {a b c : ℝ} (h : CoreArmMargin K a b c) (hc : 0 < c)
    (ha : 0 ≤ a) (hb : b ≤ π / 2) :
    StrictAntiOn (fun t => (innerCorner K t).1) (Icc a b) := by
  intro u hu v hv huv
  have hdec := h.horizontal_decrease hK hc.le ha hb hu hv huv.le
  have hneg : -c * (v - u) < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos hc) (sub_pos.mpr huv)
  linarith

/-- Projection onto an earlier cut normal decreases at a fixed rate. -/
theorem CoreArmMargin.right_cut_velocity {K : Set Point} (hK : IsCap K (π / 2))
    {a b c t d : ℝ} (h : CoreArmMargin K a b c) (hc : 0 ≤ c)
    (ht : t ∈ Icc a b) (hangle : t - d ∈ Icc (0 : ℝ) (π / 2)) :
    dot (cornerRightVelocity K t) (uvec d) ≤ -c := by
  obtain ⟨hf, -, hg, -⟩ := h.oneSided hK ht
  have hs := sin_nonneg_of_nonneg_of_le_pi hangle.1 (by linarith [hangle.2, pi_pos])
  have hcos := cos_nonneg_of_mem_Icc ⟨by linarith [hangle.1, pi_pos], hangle.2⟩
  have he : dot (cornerRightVelocity K t) (uvec d) =
      -(fPlus K t - 1) * cos (t - d) - (gPlus K t - 1) * sin (t - d) := by
    simp only [cornerRightVelocity, dot_add_left, dot_smul_left, dot_uvec_uvec, dot_vvec_uvec']
    rw [show d - t = -(t - d) by ring, sin_neg]
    ring
  have hm1 := mul_le_mul_of_nonneg_right (show c ≤ fPlus K t - 1 by linarith) hcos
  have hm2 := mul_le_mul_of_nonneg_right (show c ≤ gPlus K t - 1 by linarith) hs
  have hm3 := mul_le_mul_of_nonneg_left (sin_add_cos_ge_one hangle) hc
  rw [he]
  nlinarith

/-- Projection onto the left cut normal increases when approaching the cut from the left. -/
theorem CoreArmMargin.left_cut_velocity {K : Set Point} (hK : IsCap K (π / 2))
    {a b c t d : ℝ} (h : CoreArmMargin K a b c) (hc : 0 ≤ c)
    (ht : t ∈ Icc a b) (hangle : d - t ∈ Icc (0 : ℝ) (π / 2)) :
    c ≤ dot (cornerRightVelocity K t) (uvec (d + π / 2)) := by
  obtain ⟨hf, -, hg, -⟩ := h.oneSided hK ht
  have hs := sin_nonneg_of_nonneg_of_le_pi hangle.1 (by linarith [hangle.2, pi_pos])
  have hcos := cos_nonneg_of_mem_Icc ⟨by linarith [hangle.1, pi_pos], hangle.2⟩
  have he : dot (cornerRightVelocity K t) (uvec (d + π / 2)) =
      (fPlus K t - 1) * sin (d - t) + (gPlus K t - 1) * cos (d - t) := by
    simp only [cornerRightVelocity, dot_add_left, dot_smul_left, dot_uvec_uvec, dot_vvec_uvec']
    rw [show t - (d + π / 2) = -(d - t) - π / 2 by ring,
      cos_sub_pi_div_two, sin_neg,
      show d + π / 2 - t = (d - t) + π / 2 by ring, sin_add_pi_div_two]
    ring
  have hm1 := mul_le_mul_of_nonneg_right (show c ≤ fPlus K t - 1 by linarith) hs
  have hm2 := mul_le_mul_of_nonneg_right (show c ≤ gPlus K t - 1 by linarith) hcos
  have hm3 := mul_le_mul_of_nonneg_left (sin_add_cos_ge_one hangle) hc
  rw [he]
  nlinarith

end MovingSofaStability

end CoreMonotonicity

/-!
## Uniform bounds in a cap neighborhood

Coarse Euclidean constants are intentional. They control changing hallway angles
and support perturbations independently of any regularity of the cap boundary.
-/

section UniformGeometryBounds

open Real Set
open scoped Pointwise
open MovingSofaOptimality

namespace MovingSofaStability

theorem abs_dot_le_norm2_mul (p q : Point) : |dot p q| ≤ norm2 p * norm2 q := by
  apply abs_le.mpr
  constructor
  · have h := dot_le_norm2_mul (-p) q
    rw [norm2_neg] at h
    simp only [dot, Prod.fst_neg, Prod.snd_neg] at h ⊢
    nlinarith
  · exact dot_le_norm2_mul p q

theorem norm2_uvec_sub_le (s t : ℝ) : norm2 (uvec s - uvec t) ≤ 2 * |s - t| := by
  have h := norm2_le_abs_add (uvec s - uvec t)
  have hc := abs_cos_sub_cos_le s t
  have hs := abs_sin_sub_sin_le s t
  simp only [Prod.fst_sub, Prod.snd_sub, uvec_fst, uvec_snd] at h
  linarith

theorem norm2_vvec (t : ℝ) : norm2 (vvec t) = 1 := by
  rw [← uvec_add_pi_div_two]
  exact norm2_uvec _

theorem norm2_vvec_sub_le (s t : ℝ) : norm2 (vvec s - vvec t) ≤ 2 * |s - t| := by
  rw [← uvec_add_pi_div_two, ← uvec_add_pi_div_two]
  simpa only [add_sub_add_right_eq_sub] using norm2_uvec_sub_le (s + π / 2) (t + π / 2)

theorem exists_uniform_cap_radius {K₀ : Set Point} (h₀ : IsCap K₀ (π / 2)) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ K : Set Point, IsCap K (π / 2) →
      UpperSupportClose 1 K K₀ → ∀ p ∈ K, norm2 p ≤ R := by
  let B := K₀ + euclideanDisk 1
  have hB := convexBody_add h₀.2.1 (euclideanDisk_isConvexBody (by norm_num : (0 : ℝ) ≤ 1))
  obtain ⟨M, hM⟩ := hB.2.1.exists_bound_of_continuousOn continuous_norm2.continuousOn
  refine ⟨max 1 M, le_max_left _ _, ?_⟩
  intro K hK hclose p hp
  have hpB := cap_subset_unit_parallel hK h₀ le_rfl hclose hp
  have hb : norm2 p ≤ M := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm2_nonneg p)] using hM p hpB
  exact hb.trans (le_max_right _ _)

/-- A radius bound controls every support, including negative supports. -/
theorem support_abs_le_radius {K : Set Point} (hK : IsConvexBody K) {R : ℝ}
    (hR : ∀ p ∈ K, norm2 p ≤ R) (t : ℝ) : |supp K t| ≤ R := by
  obtain ⟨p, hp, hs⟩ := exists_dot_eq_supp hK.2.1 hK.1 t
  rw [← hs]
  have h := abs_dot_le_norm2_mul p (uvec t)
  rw [norm2_uvec, mul_one] at h
  exact h.trans (hR p hp)

/-- Support functions have a uniform angular Lipschitz constant in a bounded cap family. -/
theorem support_angle_bound {K : Set Point} (hK : IsConvexBody K) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ p ∈ K, norm2 p ≤ R) (s t : ℝ) :
    |supp K s - supp K t| ≤ 2 * R * |s - t| := by
  have one_way : ∀ s t, supp K s - supp K t ≤ 2 * R * |s - t| := by
    intro s t
    obtain ⟨p, hp, hs⟩ := exists_dot_eq_supp hK.2.1 hK.1 s
    have ht := dot_le_supp hK.2.1 hp t
    have hd := abs_dot_le_norm2_mul p (uvec s - uvec t)
    have hb := mul_le_mul (hR p hp) (norm2_uvec_sub_le s t)
      (norm2_nonneg _) hR0
    have hh := (le_abs_self _).trans (hd.trans hb)
    rw [dot_sub_right] at hh
    nlinarith
  have h1 := one_way s t
  have h2 := one_way t s
  rw [abs_sub_comm t s] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

theorem innerCorner_support_error {δ : ℝ} {K L : Set Point}
    (h : UpperSupportClose δ K L) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (π / 2)) :
    euclideanDist (innerCorner K t) (innerCorner L t) ≤ 2 * δ := by
  have h1 := h t ⟨ht.1, by linarith [ht.2, pi_pos]⟩
  have h2 := h (t + π / 2) ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
  have he : innerCorner K t - innerCorner L t =
      (supp K t - supp L t) • uvec t +
      (supp K (t + π / 2) - supp L (t + π / 2)) • vvec t := by
    rw [proposition2_2_2_innerCorner, proposition2_2_2_innerCorner]
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
  unfold euclideanDist
  rw [he]
  have hh := norm2_add_le ((supp K t - supp L t) • uvec t)
    ((supp K (t + π / 2) - supp L (t + π / 2)) • vvec t)
  rw [norm2_smul, norm2_smul, norm2_uvec, norm2_vvec, mul_one, mul_one] at hh
  linarith

/-- The inner-wall slacks are uniformly Lipschitz in the hallway angle. -/
theorem innerSlack_angle_bound {K : Set Point} (hK : IsConvexBody K) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ p ∈ K, norm2 p ≤ R) {p : Point} (hp : p ∈ K) (s t : ℝ) :
    |innerSlackU K s p - innerSlackU K t p| ≤ 4 * R * |s - t| ∧
      |innerSlackV K s p - innerSlackV K t p| ≤ 4 * R * |s - t| := by
  have hU : |dot p (uvec s - uvec t)| ≤ 2 * R * |s - t| := by
    have h := (abs_dot_le_norm2_mul p (uvec s - uvec t)).trans
      (mul_le_mul (hR p hp) (norm2_uvec_sub_le s t) (norm2_nonneg _) hR0)
    nlinarith
  have hV : |dot p (vvec s - vvec t)| ≤ 2 * R * |s - t| := by
    have h := (abs_dot_le_norm2_mul p (vvec s - vvec t)).trans
      (mul_le_mul (hR p hp) (norm2_vvec_sub_le s t) (norm2_nonneg _) hR0)
    nlinarith
  have hs := support_angle_bound hK hR0 hR s t
  have hsq := support_angle_bound hK hR0 hR (s + π / 2) (t + π / 2)
  rw [add_sub_add_right_eq_sub] at hsq
  constructor
  · have he : innerSlackU K s p - innerSlackU K t p =
        dot p (uvec s - uvec t) - (supp K s - supp K t) := by
      rw [dot_sub_right]
      unfold innerSlackU
      ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith)
  · have he : innerSlackV K s p - innerSlackV K t p =
        dot p (vvec s - vvec t) - (supp K (s + π / 2) - supp K (t + π / 2)) := by
      rw [dot_sub_right]
      unfold innerSlackV
      ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith)

/-- A partial-angle sofa satisfies the missing full-angle inequalities with a linear allowance. -/
theorem approximate_full_angle_slack {K S : Set Point} (hK : IsCap K (π / 2))
    {R ω : ℝ} (hR0 : 0 ≤ R) (hR : ∀ p ∈ K, norm2 p ≤ R)
    (hω : ω ∈ Icc (0 : ℝ) (π / 2)) (hSK : S ⊆ K)
    (hpartial : ∀ p ∈ S, ∀ t ∈ Icc (0 : ℝ) ω,
      0 ≤ max (innerSlackU K t p) (innerSlackV K t p)) :
    ApproxHallways K S (4 * R * (π / 2 - ω)) := by
  intro p hp t ht
  by_cases htw : t ≤ ω
  · have hz : 0 ≤ 4 * R * (π / 2 - ω) := by nlinarith [hω.2]
    exact (neg_nonpos.mpr hz).trans (hpartial p hp t ⟨ht.1.le, htw⟩)
  have hwt : ω < t := not_le.mp htw
  have he := innerSlack_angle_bound hK.2.1 hR0 hR (hSK hp) t ω
  have hs := hpartial p hp ω ⟨hω.1, le_rfl⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hwt.le)] at he
  have hU := (abs_le.mp he.1).1
  have hV := (abs_le.mp he.2).1
  have hmax : max (innerSlackU K ω p) (innerSlackV K ω p) ≤
      max (innerSlackU K t p) (innerSlackV K t p) + 4 * R * (t - ω) := by
    apply max_le
    · linarith [le_max_left (innerSlackU K t p) (innerSlackV K t p)]
    · linarith [le_max_right (innerSlackU K t p) (innerSlackV K t p)]
  nlinarith [ht.2]

end MovingSofaStability

end UniformGeometryBounds

/-!
## Exposed faces with a varying normal

At a multiple-point reference face the conclusion is containment near the whole
face, not convergence to a selected endpoint. This is the form needed near the
top edge to control wedge feet uniformly.
-/

section AngularFaceStability

open Real Set Metric
open scoped Pointwise
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- A strict property on one reference face persists as the body and normal vary. -/
theorem face_property_stable_in_angle {K₀ : Set Point} (h₀ : IsCap K₀ (π / 2))
    (t₀ : ℝ) (F : Point → ℝ) (hF : Continuous F)
    (hpositive : ∀ p ∈ edge K₀ t₀, 0 < F p) :
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧ δ ≤ 1 ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K K₀ →
        ∀ t ∈ Icc (0 : ℝ) π, |t - t₀| ≤ ρ → ∀ p ∈ edge K t, 0 < F p := by
  classical
  let B := K₀ + euclideanDisk 1
  have hB := convexBody_add h₀.2.1 (euclideanDisk_isConvexBody (by norm_num : (0 : ℝ) ≤ 1))
  have hK₀B : K₀ ⊆ B := by
    intro p hp
    exact ⟨p, hp, 0, by simp [euclideanDisk], by simp⟩
  obtain ⟨R', hR'⟩ := hB.2.1.exists_bound_of_continuousOn continuous_norm2.continuousOn
  let R := max 1 R'
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR0 : 0 ≤ R := by linarith
  have hR : ∀ p ∈ B, norm2 p ≤ R := by
    intro p hp
    have h := hR' p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (norm2_nonneg p)] at h
    exact h.trans (le_max_right _ _)
  let defect : Point → ℝ := fun p => Metric.infDist p K₀ + |dot p (uvec t₀) - supp K₀ t₀|
  have hdef : Continuous defect :=
    (Metric.continuous_infDist_pt K₀).add ((continuous_dot _).sub continuous_const).abs
  let bad : Set Point := B ∩ {p | F p ≤ 0}
  have hbad : IsCompact bad := hB.2.1.inter_right (isClosed_le hF continuous_const)
  have hdpos : ∀ p ∈ bad, 0 < defect p := by
    intro p hp
    by_contra hnot
    have hi0 : Metric.infDist p K₀ = 0 := by
      have hi := Metric.infDist_nonneg (x := p) (s := K₀)
      have ha := abs_nonneg (dot p (uvec t₀) - supp K₀ t₀)
      change ¬0 < Metric.infDist p K₀ + |dot p (uvec t₀) - supp K₀ t₀| at hnot
      linarith
    have hg0 : dot p (uvec t₀) = supp K₀ t₀ := by
      change ¬0 < Metric.infDist p K₀ + |dot p (uvec t₀) - supp K₀ t₀| at hnot
      rw [hi0, zero_add] at hnot
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (not_lt.mp hnot) (abs_nonneg _)))
    have hm : p ∈ K₀ := (h₀.2.1.2.1.isClosed.mem_iff_infDist_zero h₀.2.1.1).2 hi0
    exact (not_lt_of_ge hp.2) (hpositive p ⟨hm, hg0⟩)
  obtain ⟨m, hm, hmle⟩ := hbad.exists_forall_le' hdef.continuousOn hdpos
  let δ := min 1 (m / 8)
  let ρ := m / (16 * (R + 1))
  have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδm : δ ≤ m / 8 := min_le_right _ _
  have hρeq : 16 * (R + 1) * ρ = m := by
    dsimp [ρ]
    field_simp
  refine ⟨δ, ρ, hδ, hρ, hδ1, ?_⟩
  intro K hK hclose t ht htρ p hp
  have hpB := cap_subset_unit_parallel hK h₀ hδ1 hclose hp.1
  by_contra hnot
  have hbadp : p ∈ bad := ⟨hpB, not_lt.mp hnot⟩
  have hlower := hmle p hbadp
  obtain ⟨q, hq, hdq⟩ := (upperSupportClose_euclidean hδ.le hK h₀ hclose).1 p hp.1
  have hid : Metric.infDist p K₀ ≤ δ := by
    have hprod : dist p q ≤ euclideanDist p q := by
      rw [dist_eq_norm]
      exact product_norm_le_norm2 (p - q)
    exact (Metric.infDist_le_dist_of_mem hq).trans (hprod.trans hdq)
  have hsupport := hclose t ht
  have hangle := support_angle_bound h₀.2.1 hR0 (fun p hp => hR p (hK₀B hp)) t t₀
  have hdot : |dot p (uvec t₀) - dot p (uvec t)| ≤ 2 * R * |t - t₀| := by
    rw [← dot_sub_right]
    have h := (abs_dot_le_norm2_mul p (uvec t₀ - uvec t)).trans
      (mul_le_mul (hR p hpB) (norm2_uvec_sub_le t₀ t) (norm2_nonneg _) hR0)
    rw [abs_sub_comm t₀ t] at h
    nlinarith
  have hgap : |dot p (uvec t₀) - supp K₀ t₀| ≤ δ + 4 * R * |t - t₀| := by
    have he : dot p (uvec t₀) - supp K₀ t₀ =
        (dot p (uvec t₀) - dot p (uvec t)) + (supp K t - supp K₀ t) +
          (supp K₀ t - supp K₀ t₀) := by rw [hp.2]; ring
    rw [he]
    have h1 := abs_add_le (dot p (uvec t₀) - dot p (uvec t)) (supp K t - supp K₀ t)
    have h2 := abs_add_le ((dot p (uvec t₀) - dot p (uvec t)) + (supp K t - supp K₀ t))
      (supp K₀ t - supp K₀ t₀)
    linarith
  change m ≤ Metric.infDist p K₀ + |dot p (uvec t₀) - supp K₀ t₀| at hlower
  have hmul := mul_le_mul_of_nonneg_left htρ (show 0 ≤ 4 * R by positivity)
  nlinarith

/-- Gerver's full top face lies between its two contact endpoints. -/
theorem gerver_top_face_bounds {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {p : Point} (hp : p ∈ edge P.cap (π / 2)) :
    gerverRoofLeft P ≤ p.1 ∧ p.1 ≤ gerverRoofRight P := by
  have hcb := GerverParams.gm_isConvexBody_cap hP hbox
  have ha : vminus P.cap (π / 2) = (gerverRoofRight P, 1) := by
    have he := ((theorem8_4_1_monotone hP hbox).2 (π / 2) ⟨by positivity, le_rfl⟩).1
    exact he.trans (gerver_contactA_pi_div_two hP (GerverParams.romik_bounds hP hbox))
  have hc : vplus P.cap (π / 2) = (gerverRoofLeft P, 1) := by
    have he := ((theorem8_4_1_monotone hP hbox).2 0 ⟨le_rfl, by positivity⟩).2.1
    simpa only [cK, cPlus, zero_add, gerverRoofLeft] using
      he.trans (gerver_contactC_zero hP (GerverParams.romik_bounds hP hbox))
  have h1 := dot_vminus_le_dot hcb.2.1 hp
  have h2 := dot_le_dot_vplus hcb.2.1 hp
  rw [ha] at h1
  rw [hc] at h2
  simp only [dot, vvec_pi_div_two] at h1 h2
  constructor <;> linarith

/-- Uniformly control all nearby top contacts, including the ends of vertical or oblique faces. -/
theorem gerver_near_top_contacts {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧ δ ≤ 1 ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K P.cap →
        ∀ t ∈ Icc (0 : ℝ) π, |t - π / 2| ≤ ρ → ∀ p ∈ edge K t,
          gerverRoofLeft P - η < p.1 ∧ p.1 < gerverRoofRight P + η := by
  let F : Point → ℝ := fun p => min (p.1 - (gerverRoofLeft P - η))
    (gerverRoofRight P + η - p.1)
  have hF : Continuous F :=
    (continuous_fst.sub continuous_const).min (continuous_const.sub continuous_fst)
  obtain ⟨δ, ρ, hδ, hρ, hδ1, h⟩ := face_property_stable_in_angle (GerverParams.gm_isCap hP hbox)
    (π / 2) F hF (by
      intro p hp
      obtain ⟨hl, hr⟩ := gerver_top_face_bounds hP hbox hp
      exact lt_min (by linarith) (by linarith))
  refine ⟨δ, ρ, hδ, hρ, hδ1, ?_⟩
  intro K hK hclose t ht hnear p hp
  have hh := h K hK hclose t ht hnear p hp
  have hmin := lt_min_iff.mp hh
  constructor <;> linarith

end MovingSofaStability

end AngularFaceStability

/-!
## Feet of forbidden wedges and horizontal niche localization

The potentially small sine/cosine denominators at the endpoint angles are
controlled by nearby top contacts, not by dividing a uniform support error by a
quantity tending to zero.
-/

section NicheFeet

open Real Set
open MovingSofaOptimality MovingSofaUniqueness
open GerverParams

namespace MovingSofaStability

def wedgeRightFoot (K : Set Point) (t : ℝ) : ℝ := (supp K t - 1) / cos t

def wedgeLeftFoot (K : Set Point) (t : ℝ) : ℝ := (1 - supp K (t + π / 2)) / sin t

theorem wedge_floor_slacks (K : Set Point) {t x : ℝ}
    (hs : sin t ≠ 0) (hc : cos t ≠ 0) :
    innerSlackU K t (x, 0) = cos t * (x - wedgeRightFoot K t) ∧
      innerSlackV K t (x, 0) = -sin t * (x - wedgeLeftFoot K t) := by
  constructor <;> simp only [innerSlackU, innerSlackV, wedgeRightFoot, wedgeLeftFoot, dot, uvec, vvec] <;>
    field_simp [hs, hc] <;> ring

theorem wedge_feet_height (K : Set Point) {t : ℝ} (hs : sin t ≠ 0) (hc : cos t ≠ 0) :
    (innerCorner K t).2 = sin t * cos t * (wedgeRightFoot K t - wedgeLeftFoot K t) := by
  rw [proposition2_2_2_innerCorner]
  simp only [wedgeRightFoot, wedgeLeftFoot, Prod.snd_add, Prod.smul_snd,
    smul_eq_mul, uvec_snd, vvec_snd]
  field_simp [hs, hc]
  ring

/-- Every point in a positive-height wedge lies strictly between its floor feet. -/
theorem wedge_point_between_feet {K : Set Point} {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (π / 2)) {p : Point} (hpy : 0 ≤ p.2)
    (hu : innerSlackU K t p < 0) (hv : innerSlackV K t p < 0) :
    wedgeLeftFoot K t < p.1 ∧ p.1 < wedgeRightFoot K t := by
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
  have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩
  constructor
  · rw [wedgeLeftFoot, div_lt_iff₀ hs]
    have hterm := mul_nonneg hpy hc.le
    simp only [innerSlackV, dot, vvec] at hv
    nlinarith
  · rw [wedgeRightFoot, lt_div_iff₀ hc]
    have hterm := mul_nonneg hpy hs.le
    simp only [innerSlackU, dot, uvec] at hu
    nlinarith

/-- A floor point strictly between the feet belongs to the niche. -/
theorem floor_between_feet_mem_niche {K : Set Point} {t x : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (π / 2)) (hx : wedgeLeftFoot K t < x ∧ x < wedgeRightFoot K t) :
    (x, 0) ∈ niche K (π / 2) := by
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
  have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩
  obtain ⟨heU, heV⟩ := wedge_floor_slacks K (x := x) hs.ne' hc.ne'
  apply (mem_niche_iff_slacks K (x, 0)).2
  refine ⟨le_rfl, t, ht, ?_, ?_⟩
  · rw [heU]
    exact mul_neg_of_pos_of_neg hc (sub_neg.mpr hx.2)
  · rw [heV]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hs) (sub_pos.mpr hx.1)

/-- Gerver's entire open-angle corner path is above the floor, including the two unexposed phases. -/
theorem gerver_path_height_pos {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (π / 2)) : 0 < (P.path t).2 := by
  have henv := gn_envHyp hP (romik_bounds hP hbox)
  have hheight : ∀ u ∈ Icc (0 : ℝ) (π / 2), (P.path u).2 < 1 :=
    fun u hu => path_snd_lt_one hP (romik_bounds hP hbox) hu.1 hu.2
  have hbounds := envelope_bounds_of_path_height henv hheight
  by_cases hfirst : t < P.φ
  · have hD : envD P.path P.gs_β t ∈ gerverEnvelope P :=
      Or.inr ⟨t, ⟨ht.1.le, hfirst.le.trans henv.ht.2.1.le⟩, rfl⟩
    have hDy := (hbounds _ hD).2.1
    have hp := mul_pos (henv.β_pos t ht)
      (sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos]))
    simp only [envD, Prod.snd_sub, Prod.smul_snd, smul_eq_mul, uvec_snd] at hDy
    linarith
  by_cases hlast : π / 2 - P.φ < t
  · have hB : envB P.path P.gs_α t ∈ gerverEnvelope P :=
      Or.inl (Or.inl ⟨t, ⟨henv.ht.2.2.2.1.le.trans hlast.le, ht.2.le⟩, rfl⟩)
    have hBy := (hbounds _ hB).2.1
    have hp := mul_neg_of_neg_of_pos (henv.α_neg t ht)
      (cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩)
    simp only [envB, Prod.snd_add, Prod.smul_snd, smul_eq_mul, vvec_snd] at hBy
    linarith
  exact henv.x_pos t ⟨not_lt.mp hfirst, not_lt.mp hlast⟩

/-- Both Gerver wedge feet lie between the two roof endpoints at every open angle. -/
theorem gerver_wedge_feet_bounds {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (π / 2)) :
    gerverRoofLeft P ≤ wedgeLeftFoot P.cap t ∧
      wedgeRightFoot P.cap t ≤ gerverRoofRight P := by
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
  have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩
  have hp := gerver_path_height_pos hP hbox ht
  have hpath := ((theorem8_4_1_monotone hP hbox).2 t ⟨ht.1.le, ht.2.le⟩).2.2
  rw [← hpath, wedge_feet_height P.cap hs.ne' hc.ne'] at hp
  have hZW : wedgeLeftFoot P.cap t < wedgeRightFoot P.cap t := by
    have hmul := mul_pos hs hc
    exact sub_pos.mp (pos_of_mul_pos_right hp hmul.le)
  obtain ⟨H, L, γ, hroof⟩ := gerver_roof_data hP hbox
  have hfloorbounds : ∀ x, wedgeLeftFoot P.cap t < x → x < wedgeRightFoot P.cap t →
      x ∈ Icc (gerverRoofLeft P) (gerverRoofRight P) := by
    intro x hx1 hx2
    have h := floor_between_feet_mem_niche ht ⟨hx1, hx2⟩
    rw [hroof.niche_eq] at h
    exact h.1
  constructor
  · by_contra hnot
    have hlt := not_le.mp hnot
    let y := min (gerverRoofLeft P) (wedgeRightFoot P.cap t)
    have hy : wedgeLeftFoot P.cap t < y := lt_min hlt hZW
    let x := (wedgeLeftFoot P.cap t + y) / 2
    have hx := hfloorbounds x (by dsimp [x]; linarith)
      (by have hh := min_le_right (gerverRoofLeft P) (wedgeRightFoot P.cap t); dsimp [x, y] at *; linarith)
    have hya : y ≤ gerverRoofLeft P := min_le_left _ _
    dsimp [x] at hx
    linarith [hx.1]
  · by_contra hnot
    have hlt := not_le.mp hnot
    let y := max (gerverRoofRight P) (wedgeLeftFoot P.cap t)
    have hy : y < wedgeRightFoot P.cap t := max_lt hlt hZW
    let x := (y + wedgeRightFoot P.cap t) / 2
    have hx := hfloorbounds x
      (by have hh := le_max_right (gerverRoofRight P) (wedgeLeftFoot P.cap t); dsimp [x, y] at *; linarith)
      (by dsimp [x]; linarith)
    have hyb : gerverRoofRight P ≤ y := le_max_left _ _
    dsimp [x] at hx
    linarith [hx.2]

/-- Nearby niches stay in an arbitrarily small horizontal expansion of the reference roof interval. -/
theorem nearby_niche_horizontal_localization {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K P.cap →
      ∀ p ∈ niche K (π / 2), gerverRoofLeft P - η ≤ p.1 ∧ p.1 ≤ gerverRoofRight P + η := by
  obtain ⟨δ₀, ρ₀, hδ₀, hρ₀, hδ₀1, htop⟩ := gerver_near_top_contacts hP hbox hη
  let ρ := min ρ₀ (π / 4)
  have hρ : 0 < ρ := lt_min hρ₀ (by positivity)
  have hρ₀' : ρ ≤ ρ₀ := min_le_left _ _
  have hρ4 : ρ ≤ π / 4 := min_le_right _ _
  have hsρ : 0 < sin ρ := sin_pos_of_pos_of_lt_pi hρ (by linarith [pi_pos])
  let δ := min δ₀ (η * sin ρ)
  have hδ : 0 < δ := lt_min hδ₀ (mul_pos hη hsρ)
  have hδ₀' : δ ≤ δ₀ := min_le_left _ _
  have hδρ : δ ≤ η * sin ρ := min_le_right _ _
  refine ⟨δ, hδ, hδ₀'.trans hδ₀1, ?_⟩
  intro K hK hclose p hp
  obtain ⟨hpy, t, ht, hu, hv⟩ := (mem_niche_iff_slacks K p).1 hp
  obtain ⟨hleft, hright⟩ := wedge_point_between_feet ht hpy hu hv
  obtain ⟨hrefL, hrefR⟩ := gerver_wedge_feet_bounds hP hbox ht
  have hsin : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
  have hcos : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩
  constructor
  · by_cases hnear : t ≤ ρ
    · let q := vplus K (t + π / 2)
      have hq := vplus_mem_edge hK.2.1 (t + π / 2)
      have hqx := (htop K hK (hclose.mono hδ₀') (t + π / 2)
        ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
        (by rw [add_sub_cancel_right, abs_of_pos ht.1]; exact hnear.trans hρ₀') q hq).1
      have hqy := hK.snd_le_one hq.1
      have hqy0 := hK.snd_nonneg hq.1
      have he : wedgeLeftFoot K t = q.1 + (1 - q.2 * cos t) / sin t := by
        unfold wedgeLeftFoot
        rw [← hq.2, uvec_add_pi_div_two]
        simp only [dot, vvec, q]
        field_simp [hsin.ne']
        ring
      have hnon : 0 ≤ (1 - q.2 * cos t) / sin t := by
        apply div_nonneg _ hsin.le
        nlinarith [cos_le_one t]
      rw [he] at hleft
      linarith
    · have hden : sin ρ ≤ sin t := by
        have hh := cos_le_cos_of_nonneg_of_le_pi
          (x := π / 2 - t) (y := π / 2 - ρ)
          (by linarith [ht.2]) (by linarith [hρ, pi_pos]) (by linarith [not_le.mp hnear])
        simpa only [cos_pi_div_two_sub] using hh
      have herr := (abs_le.mp (hclose (t + π / 2)
        ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩)).2
      have he : wedgeLeftFoot P.cap t - η ≤ wedgeLeftFoot K t := by
        unfold wedgeLeftFoot
        apply (le_div_iff₀ hsin).2
        have hηden := mul_le_mul_of_nonneg_left hden hη.le
        have hcanc : ((1 - supp P.cap (t + π / 2)) / sin t) * sin t =
            1 - supp P.cap (t + π / 2) := div_mul_cancel₀ _ hsin.ne'
        nlinarith
      linarith
  · by_cases hnear : π / 2 - ρ ≤ t
    · let q := vplus K t
      have hq := vplus_mem_edge hK.2.1 t
      have hqx := (htop K hK (hclose.mono hδ₀') t
        ⟨ht.1.le, by linarith [ht.2, pi_pos]⟩
        (by rw [abs_of_nonpos (by linarith [ht.2] : t - π / 2 ≤ 0)]; linarith) q hq).2
      have hqy := hK.snd_le_one hq.1
      have hqy0 := hK.snd_nonneg hq.1
      have he : wedgeRightFoot K t = q.1 + (q.2 * sin t - 1) / cos t := by
        unfold wedgeRightFoot
        rw [← hq.2]
        simp only [dot, uvec, q]
        field_simp [hcos.ne']
        ring
      have hnon : (q.2 * sin t - 1) / cos t ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg _ hcos.le
        nlinarith [sin_le_one t]
      rw [he] at hright
      linarith
    · have hden : sin ρ ≤ cos t := by
        have hh := cos_le_cos_of_nonneg_of_le_pi
          (x := t) (y := π / 2 - ρ) ht.1.le
          (by linarith [hρ, pi_pos]) (not_le.mp hnear).le
        simpa only [cos_pi_div_two_sub] using hh
      have herr := (abs_le.mp (hclose t ⟨ht.1.le, by linarith [ht.2, pi_pos]⟩)).2
      have he : wedgeRightFoot K t ≤ wedgeRightFoot P.cap t + η := by
        unfold wedgeRightFoot
        apply (div_le_iff₀ hcos).2
        have hηden := mul_le_mul_of_nonneg_left hden hη.le
        have hcanc : ((supp P.cap t - 1) / cos t) * cos t = supp P.cap t - 1 :=
          div_mul_cancel₀ _ hcos.ne'
        nlinarith
      linarith

end MovingSofaStability

end NicheFeet

/-!
## Local containment of the whole niche

A normalized cap near Gerver need not be injective. Horizontal wedge-foot
localization and a uniform height bound instead put its niche in a fixed
rectangle separated from the reference upper boundary.
-/

section NicheContainment

open Real Set
open MovingSofaOptimality MovingSofaUniqueness
open GerverParams

namespace MovingSofaStability

/-- A compact rectangle strictly below an interior horizontal chord has a
uniform margin from every upper supporting line of the cap. -/
theorem cap_rectangle_upper_margin {K : Set Point} (hK : IsCap K (π / 2))
    {a b h H : ℝ} (hab : a < b) (ha : -supp K π < a) (hb : b < supp K 0)
    (hh : h < H) (hleft : (a, H) ∈ K) (hright : (b, H) ∈ K) :
    ∃ m : ℝ, 0 < m ∧ ∀ p ∈ Icc a b ×ˢ Icc (0 : ℝ) h,
      ∀ t ∈ Icc (0 : ℝ) π, m ≤ supp K t - dot p (uvec t) := by
  let R : Set Point := Icc a b ×ˢ Icc (0 : ℝ) h
  let F := fun z : Point × ℝ => supp K z.2 - dot z.1 (uvec z.2)
  have hc : Continuous F :=
    (hK.2.1.continuous_supp.comp continuous_snd).sub
      (continuous_dot_pair.comp (continuous_fst.prodMk (continuous_uvec.comp continuous_snd)))
  have hpos : ∀ z ∈ R ×ˢ Icc (0 : ℝ) π, 0 < F z := by
    rintro ⟨p, t⟩ ⟨hp, ht⟩
    by_cases ht0 : t = 0
    · subst t
      change 0 < supp K 0 - dot p (uvec 0)
      rw [dot_uvec_zero]
      linarith [hp.1.2]
    by_cases htπ : t = π
    · subst t
      change 0 < supp K π - dot p (uvec π)
      simp only [dot, uvec_pi]
      linarith [hp.1.1]
    have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi
      (lt_of_le_of_ne ht.1 (Ne.symm ht0)) (lt_of_le_of_ne ht.2 htπ)
    have hHt : (p.1, H) ∈ K := by
      let c := (p.1 - a) / (b - a)
      have hba : 0 < b - a := sub_pos.mpr hab
      have hc : c ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (sub_nonneg.mpr hp.1.1) hba.le,
          (div_le_one hba).2 (by linarith [hp.1.2])⟩
      have he := hK.2.1.2.2.add_smul_sub_mem hleft hright hc
      convert he using 1
      apply Prod.ext
      · dsimp [c]
        field_simp [hba.ne']
        ring
      · simp
    have hup := dot_le_supp hK.2.1.2.1 hHt t
    have hgap := mul_pos (show 0 < H - p.2 by linarith [hp.2.2]) hs
    change 0 < supp K t - dot p (uvec t)
    simp only [dot, uvec] at hup ⊢
    nlinarith
  obtain ⟨m, hm, hmin⟩ := ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).exists_forall_le'
    hc.continuousOn hpos
  exact ⟨m, hm, fun p hp t ht => hmin (p, t) ⟨hp, ht⟩⟩

theorem point_below_corner_of_negative_slacks {K : Set Point} {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (π / 2)) {p : Point}
    (hu : innerSlackU K t p < 0) (hv : innerSlackV K t p < 0) :
    p.2 < (innerCorner K t).2 := by
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
  have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩
  have hU := mul_neg_of_neg_of_pos hu hs
  have hV := mul_neg_of_neg_of_pos hv hc
  have he : p.2 - (innerCorner K t).2 =
      innerSlackU K t p * sin t + innerSlackV K t p * cos t := by
    rw [proposition2_2_2_innerCorner]
    simp only [innerSlackU, innerSlackV, dot, uvec, vvec, Prod.snd_add,
      Prod.smul_snd, smul_eq_mul]
    have htrig : p.2 * (sin t ^ 2 + cos t ^ 2) = p.2 := by rw [sin_sq_add_cos_sq, mul_one]
    nlinarith
  linarith

/-- The entire niche remains uniformly below height one in a fixed neighborhood. -/
theorem nearby_niche_height {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ H δ : ℝ, H < 1 ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K P.cap →
        ∀ p ∈ niche K (π / 2), p.2 ≤ H := by
  have henv := gn_envHyp hP (romik_bounds hP hbox)
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) (π / 2)).Nonempty from ⟨0, le_rfl, by positivity⟩) henv.x_cont.snd
  let M := (P.path t).2
  have hM : M < 1 := path_snd_lt_one hP (romik_bounds hP hbox) ht.1 ht.2
  let H := (M + 1) / 2
  let δ := min 1 ((1 - M) / 4)
  have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδM : δ ≤ (1 - M) / 4 := min_le_right _ _
  refine ⟨H, δ, by dsimp [H]; linarith, hδ, min_le_left _ _, ?_⟩
  intro K hK hclose p hp
  obtain ⟨-, s, hs, hu, hv⟩ := (mem_niche_iff_slacks K p).1 hp
  have hbelow := point_below_corner_of_negative_slacks hs hu hv
  have hd := innerCorner_support_error hclose ⟨hs.1.le, hs.2.le⟩
  have hy := abs_snd_le_norm2 (innerCorner K s - innerCorner P.cap s)
  have hpoint := ((theorem8_4_1_monotone hP hbox).2 s ⟨hs.1.le, hs.2.le⟩).2.2
  have hupper := hmax ⟨hs.1.le, hs.2.le⟩
  rw [hpoint] at hd hy
  have hdiff : (innerCorner K s).2 - (P.path s).2 ≤ 2 * δ :=
    (le_abs_self _).trans (hy.trans hd)
  dsimp [H, M] at *
  linarith

/-- Clamping an abscissa to an interval moves it by at most its known excess. -/
theorem clamp_interval_bound {a b x η : ℝ} (hab : a ≤ b) (hη : 0 ≤ η)
    (hx : a - η ≤ x ∧ x ≤ b + η) :
    max a (min x b) ∈ Icc a b ∧ |x - max a (min x b)| ≤ η := by
  constructor
  · exact ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  · by_cases hxa : x ≤ a
    · rw [min_eq_left (hxa.trans hab), max_eq_left hxa, abs_of_nonpos (sub_nonpos.mpr hxa)]
      linarith [hx.1]
    by_cases hbx : b ≤ x
    · rw [min_eq_right hbx, max_eq_right hab, abs_of_nonneg (sub_nonneg.mpr hbx)]
      linarith [hx.2]
    · rw [min_eq_left (not_le.mp hbx).le, max_eq_right (not_le.mp hxa).le, sub_self, abs_zero]
      exact hη

/-- A nearby cap contains its niche without acquiring the global injectivity condition. -/
theorem nearby_niche_subset_cap {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K P.cap → niche K (π / 2) ⊆ K := by
  obtain ⟨H, δH, hH, hδH, hδH1, hheight⟩ := nearby_niche_height hP hbox
  obtain ⟨H₀, L, γ, hroof⟩ := gerver_roof_data hP hbox
  have hA : (gerverRoofLeft P, 1) ∈ P.cap :=
    hroof.rectangle ⟨⟨le_rfl, hroof.order.le⟩, by norm_num, le_rfl⟩
  have hB : (gerverRoofRight P, 1) ∈ P.cap :=
    hroof.rectangle ⟨⟨hroof.order.le, le_rfl⟩, by norm_num, le_rfl⟩
  obtain ⟨m, hm, hmargin⟩ := cap_rectangle_upper_margin hroof.cap hroof.order
    hroof.left_wing hroof.right_wing hH hA hB
  let η := m / 4
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨δN, hδN, hδN1, hwidth⟩ := nearby_niche_horizontal_localization hP hbox hη
  let δ := min δH (min δN (m / 4))
  have hδ : 0 < δ := lt_min hδH (lt_min hδN (by linarith))
  have hδH' : δ ≤ δH := min_le_left _ _
  have hδN' : δ ≤ δN := (min_le_right _ _).trans (min_le_left _ _)
  have hδm : δ ≤ m / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ, hδH'.trans hδH1, ?_⟩
  intro K hK hclose p hp
  have hxy := hwidth K hK (hclose.mono hδN') p hp
  have hy := hheight K hK (hclose.mono hδH') p hp
  have hy0 := ((mem_niche_iff_slacks K p).1 hp).1
  let q : Point := (max (gerverRoofLeft P) (min p.1 (gerverRoofRight P)), p.2)
  obtain ⟨hqx, hqd⟩ := clamp_interval_bound hroof.order.le hη.le hxy
  have hq : q ∈ Icc (gerverRoofLeft P) (gerverRoofRight P) ×ˢ Icc (0 : ℝ) H :=
    ⟨hqx, hy0, hy⟩
  have hpq : euclideanDist p q ≤ η := by
    change sqrt ((p.1 - q.1) * (p.1 - q.1) + (p.2 - p.2) * (p.2 - p.2)) ≤ η
    rw [sub_self, zero_mul, add_zero, ← pow_two, Real.sqrt_sq_eq_abs]
    exact hqd
  apply (cap_mem_iff_upper hK p).2
  refine ⟨hy0, ?_⟩
  intro t ht
  have hr := hmargin q hq t ht
  have hd := dot_uvec_le_norm2 (p - q) t
  rw [dot_sub_left] at hd
  have he := (abs_le.mp (hclose t ht)).1
  change norm2 (p - q) ≤ η at hpq
  dsimp [η] at *
  linarith

end MovingSofaStability

end NicheContainment

/-!
## Cut geometry from a lower bound on bottom width

A width of 21/10 suffices for the fixed small cut angles. This avoids assuming
area continuity, curvature regularity, or Ki membership of the competing cap
when locating its cut feet.
-/

section CapWidthGeometry

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

def bottomWidth (K : Set Point) : ℝ := supp K 0 + supp K π

theorem area_le_bottomWidth {K : Set Point} (hK : IsCap K (π / 2)) : area K ≤ bottomWidth K := by
  have h := opt_area_le_of_fst_bounds hK (fun p hp => opt_cap_fst_le hK hp)
  simpa only [bottomWidth, sub_neg_eq_add, add_comm] using h

/-- Gerver's cap has enough bottom width even after a fixed support perturbation. -/
theorem nearby_bottomWidth {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hclose : UpperSupportClose (1 / 20) K P.cap) :
    (21 / 10 : ℝ) ≤ bottomWidth K := by
  have hKi := theorem8_1_1_gerver hP hbox
  have hw := area_le_bottomWidth hKi.1
  have ha := hKi.2.2
  have h0 := (abs_le.mp (hclose 0 ⟨le_rfl, pi_pos.le⟩)).1
  have hπ := (abs_le.mp (hclose π ⟨pi_pos.le, le_rfl⟩)).1
  unfold bottomWidth at *
  linarith

/-- Both cut feet lie on the bottom face, strictly between its endpoints. -/
theorem cut_feet_mem_of_width {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04)
    {K : Set Point} (hK : IsCap K (π / 2)) (hwidth : (21 / 10 : ℝ) ≤ bottomWidth K) :
    wRight φ K ∈ edge K (3 * π / 2) \ {aK K 0, cK K (π / 2)} ∧
      zLeft φ K ∈ edge K (3 * π / 2) \ {aK K 0, cK K (π / 2)} := by
  obtain ⟨hφ0, hφ4, hs4, hc9, hs0⟩ := opt_phi_bounds hφ
  have hc : 0 < cos φ := by linarith
  have hpi := pi_pos
  have hφ' : φ ∈ Ioo 0 (π / 2) := ⟨hφ0, by linarith⟩
  have hψ' : π / 2 - φ ∈ Ioo 0 (π / 2) := ⟨by linarith, by linarith⟩
  have hW : (21 / 10 : ℝ) * cos φ > 1 := by linarith
  have hwidthmul : 1 < bottomWidth K * cos φ :=
    hW.trans_le (mul_le_mul_of_nonneg_right hwidth hc.le)
  have hA := dot_le_supp hK.2.1.2.1 (opt_cap_A_mem hK) φ
  have hC := dot_le_supp hK.2.1.2.1 (opt_cap_C_mem hK) (π - φ)
  simp only [dot, uvec, cos_pi_sub, sin_pi_sub, zero_mul, add_zero] at hA hC
  unfold bottomWidth at hwidthmul
  constructor
  · rw [opt_wRight_eq]
    apply opt_mem_bottom_edge hK
    · rw [lt_div_iff₀ hc]
      nlinarith
    · have h := (theorem2_5_5_supp hK hφ').1
      rw [div_lt_iff₀ hc]
      linarith
  · rw [opt_zLeft_eq]
    apply opt_mem_bottom_edge hK
    · have h := (theorem2_5_5_supp hK hψ').2
      rw [show π / 2 - φ + π / 2 = π - φ by ring, add_halves, sub_sub_cancel] at h
      rw [lt_div_iff₀ hc]
      linarith
    · rw [div_lt_iff₀ hc]
      nlinarith

/-- The two cut half-planes do not meet inside a sufficiently wide cap. -/
theorem cut_regions_disjoint_of_width {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04)
    {K : Set Point} (hK : IsCap K (π / 2)) (hwidth : (21 / 10 : ℝ) ≤ bottomWidth K) :
    Disjoint (K ∩ hRight φ K) (K ∩ hLeft φ K) := by
  obtain ⟨hφ0, hφ4, hs4, hc9, hs0⟩ := opt_phi_bounds hφ
  have hc : 0 ≤ cos φ := by linarith
  have hA := dot_le_supp hK.2.1.2.1 (opt_cap_A_mem hK) φ
  have hC := dot_le_supp hK.2.1.2.1 (opt_cap_C_mem hK) (π - φ)
  simp only [dot, uvec, cos_pi_sub, sin_pi_sub, zero_mul, add_zero] at hA hC
  have hwidthmul := mul_le_mul_of_nonneg_right hwidth hc
  unfold bottomWidth at hwidthmul
  rw [Set.disjoint_left]
  rintro p ⟨hpK, hpR⟩ ⟨-, hpL⟩
  have hy := hK.snd_le_one hpK
  change supp K φ - 1 ≤ dot p (uvec φ) at hpR
  change supp K (π / 2 - φ + π / 2) - 1 ≤ dot p (uvec (π / 2 - φ + π / 2)) at hpL
  rw [show π / 2 - φ + π / 2 = π - φ by ring] at hpL
  simp only [dot, uvec, cos_pi_sub, sin_pi_sub] at hpR hpL
  have hys := mul_le_mul_of_nonneg_right hy hs0.le
  nlinarith


end MovingSofaStability

end CapWidthGeometry

/-!
## Canonical tail contacts without global injectivity

The topmost-point proof of the source endpoint contact theorem needs only a cap,
a cut foot in that cap, and one strict arm inequality at the cut. Those
sufficient hypotheses are exposed here.
-/

section CanonicalContacts

open Real Set
open MovingSofaOptimality

namespace MovingSofaStability

/-- The right canonical body touches its cut line from a single strict g-arm inequality. -/
theorem canonical_right_contact {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set Point} (hcap : IsCap K (π / 2)) (hW : wRight φ K ∈ K)
    (hg : 1 < gPlus K φ) :
    ∃ p ∈ rightBody φ K, dot p (uvec φ) = supp K φ - 1 := by
  have hφ0 := hφ.1
  have hφ4 := hφ.2
  have hpi := pi_pos
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcb := hcap.2.1
  let L := K ∩ line φ (supp K φ - 1)
  have hWL : wRight φ K ∈ L := by
    refine ⟨hW, ?_⟩
    simp only [line, mem_ofPred_eq, opt_wRight_eq, dot, uvec, zero_mul, add_zero]
    field_simp [hc.ne']
  obtain ⟨p, ⟨hpK, hpl⟩, hpmax⟩ := (hcb.2.1.inter_right (isClosed_line _ _)).exists_isMaxOn
    ⟨_, hWL⟩ (continuous_dot (vvec φ)).continuousOn
  have hpl' : dot p (uvec φ) = supp K φ - 1 := hpl
  obtain ⟨θ, hθ, hpθ⟩ := opt_exists_normal_of_isMax hcb hpK hpl'
    (fun q hq hql => hpmax ⟨hq, hql⟩)
  have hp2 := inj_cap_strip hcap hpK
  have hθ2 : θ ≤ φ + π / 2 := by
    by_contra hnot
    have hgt := not_le.mp hnot
    let c := vplus K (φ + π / 2)
    have hcK : c ∈ K := (vplus_mem_edge hcb _).1
    have h1 : dot p (uvec (φ + π / 2)) ≤ dot c (uvec (φ + π / 2)) := by
      rw [show dot c (uvec (φ + π / 2)) = supp K (φ + π / 2) from dot_vplus_uvec K _]
      exact dot_le_supp hcb.2.1 hpK _
    have h2 : dot c (uvec θ) ≤ dot p (uvec θ) := by
      rw [hpθ]
      exact dot_le_supp hcb.2.1 hcK _
    have ep := dot_uvec_eq_cos_add_sin p θ φ
    have ec := dot_uvec_eq_cos_add_sin c θ φ
    rw [← uvec_add_pi_div_two] at ep ec
    have hcos : cos (θ - φ) < 0 :=
      cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [hθ.2])
    have hsin : 0 ≤ sin (θ - φ) := sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    have key : dot p (uvec φ) ≤ dot c (uvec φ) := by
      nlinarith [mul_le_mul_of_nonneg_left h1 hsin]
    have hg' := hg
    rw [inj_gPlus_eq, vvec_add_pi_div_two, dot_neg_right] at hg'
    change 1 < supp K φ + -dot c (uvec φ) at hg'
    linarith
  refine ⟨p, ⟨hpK, ?_⟩, hpl'⟩
  simp only [mem_iInter₂]
  intro s hs
  change supp K s - 1 ≤ dot p (uvec s)
  rcases le_or_gt s θ with hsθ | hsθ
  · rcases eq_or_lt_of_le hθ.1 with hθφ | hθφ
    · have he : s = φ := le_antisymm (hθφ ▸ hsθ) hs.1
      rw [he]
      linarith
    · have hI := opt_supp_interp hcb hs.1 hsθ (by linarith)
      have hE := dot_uvec_comb p φ θ s
      have hsinpos : 0 < sin (θ - φ) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have hmono : sin (θ - s) ≤ sin (θ - φ) :=
        sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith [hs.1])
      have hs1 : 0 ≤ sin (s - φ) := sin_nonneg_of_nonneg_of_le_pi (by linarith [hs.1]) (by linarith)
      rw [hpθ, hpl'] at hE
      nlinarith
  · have hθπ : θ < π / 2 := hsθ.trans_le hs.2
    have hI := opt_supp_interp hcb hsθ.le hs.2 (by linarith [hθ.1])
    have hE := dot_uvec_comb p θ (π / 2) s
    rw [hcap.2.2.2.1] at hI
    rw [hpθ, dot_uvec_pi_div_two] at hE
    have hcpos : 0 < sin (π / 2 - θ) := by
      rw [sin_pi_div_two_sub]
      exact cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθπ⟩
    have hmono : sin (s - θ) ≤ sin (π / 2 - θ) :=
      sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith [hθ.1]) (by linarith [hs.2])
    have hs1 : 0 ≤ sin (s - θ) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθ.1, hs.2])
    nlinarith [mul_le_mul_of_nonneg_left hp2.2 hs1, mul_nonneg hs1 hp2.1]

/-- The left canonical contact requires only the matching f-arm inequality. -/
theorem canonical_left_contact {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set Point} (hcap : IsCap K (π / 2)) (hZ : zLeft φ K ∈ K)
    (hf : 1 < fMinus K (π / 2 - φ)) :
    ∃ p ∈ leftBody φ K, dot p (vvec (π / 2 - φ)) = supp K (π / 2 - φ + π / 2) - 1 := by
  have hφ0 := hφ.1
  have hφ4 := hφ.2
  have hpi := pi_pos
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcb := hcap.2.1
  let L := K ∩ {q | dot q (vvec (π / 2 - φ)) = supp K (π / 2 - φ + π / 2) - 1}
  have hLc : IsCompact L := hcb.2.1.inter_right (isClosed_eq (continuous_dot _) continuous_const)
  have hZL : zLeft φ K ∈ L := by
    refine ⟨hZ, ?_⟩
    simp only [mem_ofPred_eq, opt_zLeft_eq, dot, vvec, sin_pi_div_two_sub, zero_mul, add_zero,
      show π / 2 - φ + π / 2 = π - φ by ring]
    field_simp [hc.ne']
    ring
  obtain ⟨p, ⟨hpK, hpl⟩, hpmax⟩ :=
    hLc.exists_isMaxOn ⟨_, hZL⟩ (continuous_dot (uvec (π / 2 - φ))).continuousOn
  have hpl' : dot p (vvec (π / 2 - φ)) = supp K (π / 2 - φ + π / 2) - 1 := hpl
  have hu : ∀ q : Point, dot q (uvec (-φ)) = -dot q (vvec (π / 2 - φ)) := by
    intro q
    simp only [dot, uvec, vvec, cos_neg, sin_neg, sin_pi_div_two_sub, cos_pi_div_two_sub]
    ring
  have hv : ∀ q : Point, dot q (vvec (-φ)) = dot q (uvec (π / 2 - φ)) := by
    intro q
    simp only [dot, uvec, vvec, cos_neg, sin_neg, sin_pi_div_two_sub, cos_pi_div_two_sub]
    ring
  obtain ⟨θ, hθ, hpθ⟩ := opt_exists_normal_of_isMax hcb hpK (α := -φ)
    (c := -(supp K (π / 2 - φ + π / 2) - 1)) (by rw [hu, hpl])
    (fun q hq hql => by
      rw [hv, hv]
      apply hpmax ⟨hq, ?_⟩
      change dot q (vvec (π / 2 - φ)) = _
      rw [hu] at hql
      linarith)
  have hp2 := inj_cap_strip hcap hpK
  have hθ2 : π / 2 - φ ≤ θ := by
    by_contra hnot
    have hgt := not_le.mp hnot
    let a := vminus K (π / 2 - φ)
    have haK : a ∈ K := (vminus_mem_edge hcb _).1
    have h1 : dot p (uvec (π / 2 - φ)) ≤ dot a (uvec (π / 2 - φ)) := by
      rw [show dot a (uvec (π / 2 - φ)) = supp K (π / 2 - φ) from dot_vminus_uvec K _]
      exact dot_le_supp hcb.2.1 hpK _
    have h2 : dot a (uvec θ) ≤ dot p (uvec θ) := by rw [hpθ]; exact dot_le_supp hcb.2.1 haK θ
    have ep := dot_uvec_eq_cos_add_sin p θ (π / 2 - φ)
    have ea := dot_uvec_eq_cos_add_sin a θ (π / 2 - φ)
    have hcos : 0 ≤ cos (θ - (π / 2 - φ)) :=
      cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith⟩
    have hsin : sin (θ - (π / 2 - φ)) < 0 :=
      sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith [hθ.1])
    have key : dot p (vvec (π / 2 - φ)) ≤ dot a (vvec (π / 2 - φ)) := by
      nlinarith [mul_le_mul_of_nonneg_left h1 hcos]
    have hf' := hf
    rw [inj_fMinus_eq] at hf'
    change 1 < supp K (π / 2 - φ + π / 2) - dot a (vvec (π / 2 - φ)) at hf'
    linarith
  have hp1 : dot p (uvec (π - φ)) = supp K (π - φ) - 1 := by
    rw [show π - φ = π / 2 - φ + π / 2 by ring, uvec_add_pi_div_two]
    exact hpl
  have key : ∀ t ∈ Icc (π / 2) (π - φ), supp K t - 1 ≤ dot p (uvec t) := by
    intro t ht
    rcases le_or_gt θ t with hθt | hθt
    · rcases eq_or_lt_of_le hθ.2 with hθe | hθe
      · have he : t = π - φ := le_antisymm ht.2 (by linarith)
        rw [he]
        linarith
      · have hI := opt_supp_interp hcb hθt ht.2 (by linarith)
        have hE := dot_uvec_comb p θ (π - φ) t
        have hsinpos : 0 < sin (π - φ - θ) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
        have hmono : sin (t - θ) ≤ sin (π - φ - θ) :=
          sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith [ht.2])
        have hs1 : 0 ≤ sin (π - φ - t) := sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.2]) (by linarith [ht.1])
        rw [hpθ, hp1] at hE
        nlinarith
    · have hθπ : π / 2 < θ := ht.1.trans_lt hθt
      have hI := opt_supp_interp hcb ht.1 hθt.le (by linarith [hθ.2])
      have hE := dot_uvec_comb p (π / 2) θ t
      rw [hcap.2.2.2.1] at hI
      rw [hpθ, dot_uvec_pi_div_two] at hE
      have hsinpos : 0 < sin (θ - π / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ.2])
      have hmono : sin (θ - t) ≤ sin (θ - π / 2) :=
        sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith [hθ.2]) (by linarith [ht.1])
      have hs1 : 0 ≤ sin (θ - t) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθ.2, ht.1])
      have hs2 : 0 ≤ sin (t - π / 2) := sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht.2])
      nlinarith [mul_le_mul_of_nonneg_left hp2.2 hs1, mul_nonneg hs1 hp2.1]
  refine ⟨p, ⟨hpK, ?_⟩, hpl⟩
  simp only [mem_iInter₂]
  intro s hs
  change supp K (s + π / 2) - 1 ≤ dot p (uvec (s + π / 2))
  exact key _ ⟨by linarith [hs.1], by linarith [hs.2]⟩

end MovingSofaStability

end CanonicalContacts

/-!
## Canonical triples for nearby nonsmooth caps

All endpoint contacts and linear wall constraints are proved. The final
neighborhood result supplies an actual WideTriple and does not assume Ki of the
competing cap or feasibility of its canonical tails. The geometric inequality A
<= Q is a subsequent, separate result.
-/

section CanonicalTriple

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- The right-body wall inequalities hold for all caps once the cut is nonnegative. -/
theorem canonical_right_wall {φ : ℝ} (hφ : 0 ≤ φ) {K : Set Point} (hK : IsCap K (π / 2))
    {t : ℝ} (ht : t ∈ Icc φ (π / 2)) :
    supp K t + supp (rightBody φ K) (π + t) ≤ 1 := by
  have hB := opt_rightBody_isConvexBody hφ hK
  have hbound : ∀ p ∈ rightBody φ K, dot p (uvec (π + t)) ≤ 1 - supp K t := by
    intro p hp
    have h := mem_iInter₂.mp hp.2 t ht
    change supp K t - 1 ≤ dot p (uvec t) at h
    rw [show π + t = t + π by ring, uvec_add_pi, dot_neg_right]
    linarith
  have h := supp_le_of_forall hB.1 hbound
  linarith

/-- The left-body inequalities are likewise independent of curvature regularity. -/
theorem canonical_left_wall {φ : ℝ} (hφ : 0 ≤ φ) {K : Set Point} (hK : IsCap K (π / 2))
    {t : ℝ} (ht : t ∈ Icc 0 (π / 2 - φ)) :
    supp K (π / 2 + t) + supp (leftBody φ K) (3 * π / 2 + t) ≤ 1 := by
  have hD := opt_leftBody_isConvexBody hφ hK
  have hbound : ∀ p ∈ leftBody φ K, dot p (uvec (3 * π / 2 + t)) ≤ 1 - supp K (π / 2 + t) := by
    intro p hp
    have h := mem_iInter₂.mp hp.2 t ht
    change supp K (t + π / 2) - 1 ≤ dot p (uvec (t + π / 2)) at h
    rw [uvec_add_pi_div_two] at h
    rw [show 3 * π / 2 + t = (t + π / 2) + π by ring, uvec_add_pi,
      dot_neg_right, uvec_add_pi_div_two]
    rw [show π / 2 + t = t + π / 2 by ring]
    linarith
  have h := supp_le_of_forall hD.1 hbound
  linarith

/-- Feasibility of the canonical triple needs only width and the two cut-arm inequalities. -/
theorem canonical_inWideL_of_cut_arms {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04)
    {K : Set Point} (hK : IsCap K (π / 2)) (hwidth : (21 / 10 : ℝ) ≤ bottomWidth K)
    (hg : 1 < gPlus K φ) (hf : 1 < fMinus K (π / 2 - φ)) :
    InWideL φ K (rightBody φ K) (leftBody φ K) := by
  obtain ⟨hφ0, hφ4, -, -, -⟩ := opt_phi_bounds hφ
  have hφ' : φ ∈ Ioo 0 (π / 4) := ⟨hφ0, hφ4⟩
  have hp := pi_pos
  have hB := opt_rightBody_isConvexBody hφ0.le hK
  have hD := opt_leftBody_isConvexBody hφ0.le hK
  obtain ⟨hW, hZ⟩ := cut_feet_mem_of_width hφ hK hwidth
  obtain ⟨p, hpB, hpR⟩ := canonical_right_contact hφ' hK hW.1.1 hg
  obtain ⟨q, hqD, hqL⟩ := canonical_left_contact hφ' hK hZ.1.1 hf
  have hR : supp K φ + supp (rightBody φ K) (π + φ) = 1 := by
    have hlo := dot_le_supp hB.2.1 hpB (π + φ)
    rw [show π + φ = φ + π by ring, uvec_add_pi, dot_neg_right, hpR] at hlo
    have hhi := canonical_right_wall hφ0.le hK ⟨le_rfl, by linarith⟩
    rw [show φ + π = π + φ by ring] at hlo
    linarith
  have hL : supp K (π / 2 + (π / 2 - φ)) +
      supp (leftBody φ K) (3 * π / 2 + (π / 2 - φ)) = 1 := by
    have hlo := dot_le_supp hD.2.1 hqD (3 * π / 2 + (π / 2 - φ))
    rw [show 3 * π / 2 + (π / 2 - φ) = ((π / 2 - φ) + π / 2) + π by ring,
      uvec_add_pi, dot_neg_right, uvec_add_pi_div_two, hqL] at hlo
    have hhi := canonical_left_wall hφ0.le hK ⟨by linarith, le_rfl⟩
    have ea : π / 2 + (π / 2 - φ) = π / 2 - φ + π / 2 := by ring
    have eb : ((π / 2 - φ) + π / 2) + π = 3 * π / 2 + (π / 2 - φ) := by ring
    rw [eb] at hlo
    rw [ea] at hhi ⊢
    linarith
  have hB0 := opt_supp_three_pi_div_two_eq_zero hK hB inter_subset_left
    (opt_rightBody_A_mem hφ0.le hK)
  have hD0 := opt_supp_three_pi_div_two_eq_zero hK hD inter_subset_left
    (opt_leftBody_C_mem hφ0.le hK)
  refine ⟨hK, hB, hD, inter_subset_left, inter_subset_left,
    fun t ht => canonical_right_wall hφ0.le hK ht, hR, ?_,
    fun t ht => canonical_left_wall hφ0.le hK ht, ?_, hL⟩
  · rw [show π + π / 2 = 3 * π / 2 by ring, hB0, hK.2.2.2.1]
    norm_num
  · rw [add_zero, add_zero, hD0, hK.2.2.2.1]
    norm_num

/-- An open neighborhood of Gerver has feasible canonical triples on the nonsmooth domain. -/
theorem nearby_canonical_inWideL {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K P.cap →
      InWideL P.φ K (rightBody P.φ K) (leftBody P.φ K) := by
  have hKi := theorem8_1_1_gerver hP hbox
  have hφ := GerverParams.gm_φ_mem_Ioo hP hbox
  obtain ⟨c, δA, hc, hδA, hδA1, hA⟩ := core_arm_margin_near_reference hKi
    (a := P.φ) (b := π / 2 - P.φ) hφ.1 (by linarith [hφ.2]) (by linarith [hφ.1])
  let δ := min δA (1 / 20)
  have hδ : 0 < δ := lt_min hδA (by norm_num)
  have hδA' : δ ≤ δA := min_le_left _ _
  have hδw : δ ≤ (1 / 20 : ℝ) := min_le_right _ _
  refine ⟨δ, hδ, hδA'.trans hδA1, ?_⟩
  intro K hK hclose
  have hwidth := nearby_bottomWidth hP hbox (hclose.mono hδw)
  have hcore := hA K hK (hclose.mono hδA')
  have hφarm := hcore.oneSided hK (t := P.φ) ⟨le_rfl, by linarith [hφ.2]⟩
  have hbarm := hcore.oneSided hK (t := π / 2 - P.φ) ⟨by linarith [hφ.2], le_rfl⟩
  exact canonical_inWideL_of_cut_arms hbox.1 hK hwidth
    (by linarith [hφarm.2.2.1]) (by linarith [hbarm.2.1])

/-- Package the canonical bodies without introducing a choice of auxiliary solver output. -/
def canonicalWideTriple {φ : ℝ} {K : Set Point}
    (h : InWideL φ K (rightBody φ K) (leftBody φ K)) : WideTriple φ :=
  ⟨(⟨K, h.1.2.1⟩, ⟨rightBody φ K, h.2.1⟩, ⟨leftBody φ K, h.2.2.1⟩), h⟩

end MovingSofaStability

end CanonicalTriple
