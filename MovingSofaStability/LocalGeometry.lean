module

public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import MovingSofaStability.Margins

/-!
# The geometry of a cap near Gerver's cap

Let `K` be a right-angle cap whose upper support function is uniformly close to Gerver's. Then the
arms of `K` keep a margin above one on a compact interval of interior angles
(`core_arm_margin_near_reference`), so its core moves left at a definite speed
(`CoreArmMargin.horizontal_decrease`); its niche lies over a small enlargement of Gerver's roof
interval (`nearby_niche_horizontal_localization`) and inside `K` (`nearby_niche_subset_cap`); and
its canonical triple lies in the enlarged domain `T̄` (`nearby_canonical_inWideL`).
-/

@[expose] public section
noncomputable section

open Real Set
open scoped Pointwise
open MovingSofaOptimality MovingSofaUniqueness
open GerverParams

namespace MovingSofaStability

/-! ## Uniform bounds near a reference cap -/

/-- A support neighborhood grows with its radius. -/
theorem UpperSupportClose.mono {δ R : ℝ} {K L : Set Point}
    (h : UpperSupportClose δ K L) (hδ : δ ≤ R) : UpperSupportClose R K L :=
  fun t ht => (h t ht).trans hδ

/-- Caps in a unit support neighborhood of `K₀` lie in the unit parallel body of `K₀`. -/
theorem cap_subset_unit_parallel {K K₀ : Set Point} (hK : IsCap K (π / 2))
    (h₀ : IsCap K₀ (π / 2)) {δ : ℝ} (hδ : δ ≤ 1)
    (hclose : UpperSupportClose δ K K₀) : K ⊆ K₀ + euclideanDisk 1 := fun p hp =>
  (mem_iff_forall_dot_le_supp (convexBody_add h₀.2.1 (euclideanDisk_isConvexBody zero_le_one))
    p).2 fun t => by
      rw [supp_add_euclideanDisk h₀.2.1 zero_le_one]
      linarith [(abs_le.mp (upperSupportClose_all hK h₀ hclose t)).2, dot_le_supp hK.2.1.2.1 hp t]

/-- Caps in a unit support neighborhood of `K₀` lie in a common disk centered at the origin. -/
theorem exists_uniform_cap_radius {K₀ : Set Point} (h₀ : IsCap K₀ (π / 2)) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ K : Set Point, IsCap K (π / 2) →
      UpperSupportClose 1 K K₀ → ∀ p ∈ K, norm2 p ≤ R := by
  obtain ⟨M, hM⟩ := (convexBody_add h₀.2.1 (euclideanDisk_isConvexBody zero_le_one)).2.1
    |>.exists_bound_of_continuousOn continuous_norm2.continuousOn
  exact ⟨max 1 M, le_max_left _ _, fun K hK hclose p hp => (Real.le_norm_self _).trans
    ((hM p (cap_subset_unit_parallel hK h₀ le_rfl hclose hp)).trans (le_max_right _ _))⟩

/-- The Cauchy–Schwarz inequality for `|dot p q|`. -/
theorem abs_dot_le_norm2_mul (p q : Point) : |dot p q| ≤ norm2 p * norm2 q := by
  have h := dot_le_norm2_mul (-p) q
  rw [dot_neg_left, norm2_neg] at h
  exact abs_le.mpr ⟨by linarith, dot_le_norm2_mul p q⟩

/-- The unit vector `uvec` is `2`-Lipschitz for the Euclidean norm. -/
private theorem norm2_uvec_sub_le (s t : ℝ) : norm2 (uvec s - uvec t) ≤ 2 * |s - t| := by
  have h := norm2_le_abs_add (uvec s - uvec t)
  simp only [Prod.fst_sub, Prod.snd_sub, uvec_fst, uvec_snd] at h
  linarith [abs_cos_sub_cos_le s t, abs_sin_sub_sin_le s t]

/-- The vector `vvec t` has unit length. -/
theorem norm2_vvec (t : ℝ) : norm2 (vvec t) = 1 := by
  rw [← uvec_add_pi_div_two, norm2_uvec]

/-- The projections of a point of norm at most `R` onto two unit normals differ by at most `2R`
times the angle between the normals. -/
private theorem abs_dot_uvec_sub_le {p : Point} {R : ℝ} (hR : 0 ≤ R) (hp : norm2 p ≤ R)
    (s t : ℝ) : |dot p (uvec s - uvec t)| ≤ 2 * R * |s - t| :=
  (abs_dot_le_norm2_mul p _).trans <|
    (mul_le_mul hp (norm2_uvec_sub_le s t) (norm2_nonneg _) hR).trans_eq (by ring)

/-- The support function of a body in the disk of radius `R` is at most `R` in absolute value. -/
theorem support_abs_le_radius {K : Set Point} (hK : IsConvexBody K) {R : ℝ}
    (hR : ∀ p ∈ K, norm2 p ≤ R) (t : ℝ) : |supp K t| ≤ R := by
  obtain ⟨p, hp, hs⟩ := exists_dot_eq_supp hK.2.1 hK.1 t
  have h := abs_dot_le_norm2_mul p (uvec t)
  rw [norm2_uvec, mul_one, hs] at h
  exact h.trans (hR p hp)

/-- The support function of a body in the disk of radius `R` is `2R`-Lipschitz. -/
theorem support_angle_bound {K : Set Point} (hK : IsConvexBody K) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ p ∈ K, norm2 p ≤ R) (s t : ℝ) :
    |supp K s - supp K t| ≤ 2 * R * |s - t| := by
  have one_way : ∀ s t, supp K s - supp K t ≤ 2 * R * |s - t| := fun s t => by
    obtain ⟨p, hp, hs⟩ := exists_dot_eq_supp hK.2.1 hK.1 s
    have h := abs_dot_uvec_sub_le hR0 (hR p hp) s t
    rw [dot_sub_right, hs] at h
    linarith [dot_le_supp hK.2.1 hp t, le_abs_self (supp K s - dot p (uvec t))]
  refine abs_sub_le_iff.2 ⟨one_way s t, ?_⟩
  rw [abs_sub_comm]
  exact one_way t s

/-- If the upper support functions of `K` and `L` differ by at most `δ`, their inner corners at an
angle of `[0, π/2]` are at distance at most `2δ`. -/
theorem innerCorner_support_error {δ : ℝ} {K L : Set Point}
    (h : UpperSupportClose δ K L) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (π / 2)) :
    euclideanDist (innerCorner K t) (innerCorner L t) ≤ 2 * δ := by
  have h1 := h t ⟨ht.1, by linarith [ht.2, pi_pos]⟩
  have h2 := h (t + π / 2) ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
  have he : innerCorner K t - innerCorner L t =
      (supp K t - supp L t) • uvec t + (supp K (t + π / 2) - supp L (t + π / 2)) • vvec t := by
    rw [proposition2_2_2_innerCorner, proposition2_2_2_innerCorner]
    module
  have h3 := norm2_add_le ((supp K t - supp L t) • uvec t)
    ((supp K (t + π / 2) - supp L (t + π / 2)) • vvec t)
  rw [← he, norm2_smul, norm2_smul, norm2_uvec, norm2_vvec, mul_one, mul_one] at h3
  rw [euclideanDist]
  linarith

/-- The inner-wall slacks of a point of a body in the disk of radius `R` are `4R`-Lipschitz in the
angle. -/
private theorem innerSlack_angle_bound {K : Set Point} (hK : IsConvexBody K) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ p ∈ K, norm2 p ≤ R) {p : Point} (hp : p ∈ K) (s t : ℝ) :
    innerSlackU K s p - innerSlackU K t p ≤ 4 * R * |s - t| ∧
      innerSlackV K s p - innerSlackV K t p ≤ 4 * R * |s - t| := by
  have hU := abs_dot_uvec_sub_le hR0 (hR p hp) s t
  have hV := abs_dot_uvec_sub_le hR0 (hR p hp) (s + π / 2) (t + π / 2)
  have hs := support_angle_bound hK hR0 hR s t
  have hsq := support_angle_bound hK hR0 hR (s + π / 2) (t + π / 2)
  rw [add_sub_add_right_eq_sub] at hV hsq
  rw [dot_sub_right, uvec_add_pi_div_two, uvec_add_pi_div_two] at hV
  rw [dot_sub_right] at hU
  simp only [innerSlackU, innerSlackV]
  constructor <;> linarith [le_abs_self (dot p (uvec s) - dot p (uvec t)),
    le_abs_self (dot p (vvec s) - dot p (vvec t)), neg_le_abs (supp K s - supp K t),
    neg_le_abs (supp K (s + π / 2) - supp K (t + π / 2))]

/-- A subset of a cap in the disk of radius `R` that satisfies the hallway inequalities at the
angles of `[0, ω]` satisfies them at all angles of `(0, π/2)` up to the error `4R (π/2 - ω)`. -/
theorem approximate_full_angle_slack {K S : Set Point} (hK : IsCap K (π / 2))
    {R ω : ℝ} (hR0 : 0 ≤ R) (hR : ∀ p ∈ K, norm2 p ≤ R)
    (hω : ω ∈ Icc (0 : ℝ) (π / 2)) (hSK : S ⊆ K)
    (hpartial : ∀ p ∈ S, ∀ t ∈ Icc (0 : ℝ) ω,
      0 ≤ max (innerSlackU K t p) (innerSlackV K t p)) :
    ApproxHallways K S (4 * R * (π / 2 - ω)) := by
  intro p hp t ht
  by_cases htw : t ≤ ω
  · have : 0 ≤ 4 * R * (π / 2 - ω) := mul_nonneg (by positivity) (by linarith [hω.2])
    linarith [hpartial p hp t ⟨ht.1.le, htw⟩]
  -- the slacks at `t` are at most `4R (t - ω) ≤ 4R (π/2 - ω)` below those at `ω`
  obtain ⟨hU, hV⟩ := innerSlack_angle_bound hK.2.1 hR0 hR (hSK hp) ω t
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (not_le.mp htw).le)] at hU hV
  have : 4 * R * (t - ω) ≤ 4 * R * (π / 2 - ω) := by gcongr; exact ht.2.le
  rcases le_max_iff.mp (hpartial p hp ω ⟨hω.1, le_rfl⟩) with h | h
  · linarith [le_max_left (innerSlackU K t p) (innerSlackV K t p)]
  · linarith [le_max_right (innerSlackU K t p) (innerSlackV K t p)]

/-! ## Exposed faces of nearby caps

A strict continuous inequality on exposed faces of a reference cap holds on the exposed faces of
nearby caps. Each proof takes the minimum, over a compact set, of the defect of a point from a
reference face. Neither proof needs a metric or a differentiable structure on the space of caps, or
any convergence of faces: a face of the reference may be a segment.
-/

/-- The points of a nearby cap lie within the support error of the reference cap. -/
private theorem infDist_le_of_close {K K₀ : Set Point} (hK : IsCap K (π / 2))
    (h₀ : IsCap K₀ (π / 2)) {δ : ℝ} (hδ : 0 ≤ δ) (hclose : UpperSupportClose δ K K₀)
    {p : Point} (hp : p ∈ K) : Metric.infDist p K₀ ≤ δ := by
  obtain ⟨q, hq, hpq⟩ := (upperSupportClose_euclidean hδ hK h₀ hclose).1 p hp
  refine (Metric.infDist_le_dist_of_mem hq).trans (le_trans ?_ hpq)
  rw [dist_eq_norm]
  exact product_norm_le_norm2 (p - q)

/-- A point at distance zero from `K₀` on the supporting line of `K₀` at `t` lies on the face
of `K₀` at `t`. -/
private theorem mem_edge_of_defect_nonpos {K₀ : Set Point} (h₀ : IsConvexBody K₀) {p : Point}
    {t : ℝ} (h : Metric.infDist p K₀ + |dot p (uvec t) - supp K₀ t| ≤ 0) : p ∈ edge K₀ t := by
  have h1 := Metric.infDist_nonneg (x := p) (s := K₀)
  have h2 := abs_nonneg (dot p (uvec t) - supp K₀ t)
  exact ⟨(h₀.2.1.isClosed.mem_iff_infDist_zero h₀.1).2 (by linarith),
    sub_eq_zero.mp (abs_eq_zero.mp (by linarith))⟩

/-- A strict continuous inequality on the faces of `K₀` at the normals of a compact set `I` holds on
the faces of every nearby cap at these normals. -/
theorem exposed_face_property_stable {K₀ : Set Point} (h₀ : IsCap K₀ (π / 2))
    {I : Set ℝ} (hI : IsCompact I) (hIupper : I ⊆ Icc (0 : ℝ) π)
    (F : Point → ℝ → ℝ)
    (hF : ContinuousOn (fun z : Point × ℝ => F z.1 z.2)
      ((K₀ + euclideanDisk 1) ×ˢ I))
    (hpositive : ∀ t ∈ I, ∀ p ∈ edge K₀ t, 0 < F p t) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K K₀ →
        ∀ t ∈ I, ∀ p ∈ edge K t, 0 < F p t := by
  have hB := (convexBody_add h₀.2.1 (euclideanDisk_isConvexBody zero_le_one)).2.1
  -- On the compact set of pairs `(p, t)` of `(K₀ + euclideanDisk 1) × I` where the inequality
  -- fails, the defect of `p` from the face of `K₀` at `t` has a positive minimum `m`.
  obtain ⟨m, hm, hmin⟩ := ((hB.prod hI).of_isClosed_subset
      (hF.preimage_isClosed_of_isClosed (hB.isClosed.prod hI.isClosed) isClosed_Iic)
      inter_subset_left).exists_forall_le'
    (f := fun z : Point × ℝ => Metric.infDist z.1 K₀ + |dot z.1 (uvec z.2) - supp K₀ z.2|)
    (((Metric.continuous_infDist_pt K₀).comp continuous_fst).add
      ((continuous_dot_pair.comp (continuous_fst.prodMk (continuous_uvec.comp continuous_snd))).sub
        (h₀.2.1.continuous_supp.comp continuous_snd)).abs).continuousOn
    fun z hz => lt_of_not_ge fun h =>
      not_lt.mpr hz.2 (hpositive z.2 hz.1.2 z.1 (mem_edge_of_defect_nonpos h₀.2.1 h))
  -- On the faces of a `δ`-close cap, the defect is at most `2δ < m`.
  refine ⟨min 1 (m / 4), by positivity, min_le_left _ _, fun K hK hclose t ht p hp => ?_⟩
  by_contra hnot
  have h1 : m ≤ Metric.infDist p K₀ + |dot p (uvec t) - supp K₀ t| :=
    hmin (p, t) ⟨⟨cap_subset_unit_parallel hK h₀ (min_le_left _ _) hclose hp.1, ht⟩,
      not_lt.mp hnot⟩
  have h2 := infDist_le_of_close hK h₀ (by positivity) hclose hp.1
  have h3 : |dot p (uvec t) - supp K₀ t| ≤ min 1 (m / 4) := by
    rw [hp.2]
    exact hclose t (hIupper ht)
  linarith [min_le_right 1 (m / 4)]

/-- A strict continuous inequality on the face of `K₀` at `t₀` holds on the faces of every nearby
cap at the normals near `t₀`. -/
theorem face_property_stable_in_angle {K₀ : Set Point} (h₀ : IsCap K₀ (π / 2))
    (t₀ : ℝ) (F : Point → ℝ) (hF : Continuous F)
    (hpositive : ∀ p ∈ edge K₀ t₀, 0 < F p) :
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧ δ ≤ 1 ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K K₀ →
        ∀ t ∈ Icc (0 : ℝ) π, |t - t₀| ≤ ρ → ∀ p ∈ edge K t, 0 < F p := by
  obtain ⟨R, hR1, hR⟩ := exists_uniform_cap_radius h₀
  have hR0 : 0 < R := by linarith
  have hB := (convexBody_add h₀.2.1 (euclideanDisk_isConvexBody zero_le_one)).2.1
  -- On the compact set of points of `K₀ + euclideanDisk 1` where the inequality fails, the defect
  -- from the face of `K₀` at `t₀` has a positive minimum `m`.
  obtain ⟨m, hm, hmin⟩ := (hB.inter_right (isClosed_le hF continuous_const)).exists_forall_le'
    (f := fun p => Metric.infDist p K₀ + |dot p (uvec t₀) - supp K₀ t₀|)
    ((Metric.continuous_infDist_pt K₀).add
      ((continuous_dot _).sub continuous_const).abs).continuousOn
    fun p hp => lt_of_not_ge fun h =>
      not_lt.mpr hp.2 (hpositive p (mem_edge_of_defect_nonpos h₀.2.1 h))
  -- On the face at `t` of a `δ`-close cap, the defect is at most `2δ + 4R|t - t₀| < m`.
  refine ⟨min 1 (m / 8), m / (16 * R), by positivity, by positivity, min_le_left _ _,
    fun K hK hclose t ht htρ p hp => ?_⟩
  by_contra hnot
  have h1 : m ≤ Metric.infDist p K₀ + |dot p (uvec t₀) - supp K₀ t₀| :=
    hmin p ⟨cap_subset_unit_parallel hK h₀ (min_le_left _ _) hclose hp.1, not_lt.mp hnot⟩
  have h2 := infDist_le_of_close hK h₀ (by positivity) hclose hp.1
  have h3 := abs_dot_uvec_sub_le hR0.le (hR K hK (hclose.mono (min_le_left _ _)) p hp.1) t₀ t
  rw [dot_sub_right, hp.2, abs_sub_comm t₀ t] at h3
  have h4 := support_angle_bound h₀.2.1 hR0.le (hR K₀ h₀ fun s _ => by simp) t t₀
  have h5 : 4 * R * |t - t₀| ≤ m / 4 :=
    calc 4 * R * |t - t₀| ≤ 4 * R * (m / (16 * R)) := by gcongr
      _ = m / 4 := by field_simp; ring
  linarith [hclose t ht, min_le_right 1 (m / 8),
    abs_sub_le (dot p (uvec t₀)) (supp K t) (supp K₀ t),
    abs_sub_le (dot p (uvec t₀)) (supp K₀ t) (supp K₀ t₀)]

/-! ## Arm margins near an injective reference

The reference cap is injective; a nearby cap need only be a cap. The margin holds at every point of
every exposed face, so it covers both endpoints of the faces of polygonal and other nonsmooth caps.
-/

/-- `K` has arm margin `c` on `[a, b]`: for `t ∈ [a, b]`, every point of the face of `K` at `t`
lies at distance at least `1 + c` from the supporting line of `K` at `t + π/2`, and every point of
the face at `t + π/2` at distance at least `1 + c` from the supporting line at `t`. -/
def CoreArmMargin (K : Set Point) (a b c : ℝ) : Prop :=
  (∀ t ∈ Icc a b, ∀ p ∈ edge K t,
      1 + c ≤ supp K (t + π / 2) - dot p (vvec t)) ∧
  (∀ t ∈ Icc a b, ∀ p ∈ edge K (t + π / 2),
      1 + c ≤ supp K t - dot p (uvec t))

/-- Near a cap of `𝒦^i`, every cap has a uniform arm margin on a compact interval of interior
angles. -/
theorem core_arm_margin_near_reference {K₀ : Set Point} (h₀ : IsKi K₀)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < π / 2) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K K₀ →
        CoreArmMargin K a b c := by
  have hcb := h₀.1.2.1
  have hI := h₀.2.1.1
  -- the arms of `K₀` exceed `1 + m` on `[a, b]`
  obtain ⟨-, -, hfc, hgc⟩ := proposition6_4_6_continuous h₀.1 hI
  have hsub : Icc a b ⊆ Icc (0 : ℝ) (π / 2) := Icc_subset_Icc ha.le hb.le
  obtain ⟨m, hm, hmle⟩ := isCompact_Icc.exists_forall_le'
    (((hfc.mono hsub).sub continuousOn_const).inf ((hgc.mono hsub).sub continuousOn_const))
    fun t ht => by
      obtain ⟨hg, hf⟩ := opt_arm_gt_one h₀ ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
      exact lt_min (sub_pos.mpr hf) (sub_pos.mpr hg)
  -- The faces of `K₀` at these normals are points, at which the arms exceed `1 + m / 2`;
  -- this persists on the faces of nearby caps.
  obtain ⟨δA, hδA, hδA1, hA⟩ := exposed_face_property_stable h₀.1 isCompact_Icc
    (I := Icc a b) (fun t ht => ⟨ha.le.trans ht.1, by linarith [ht.2, pi_pos]⟩)
    (fun p t => supp K₀ (t + π / 2) - dot p (vvec t) - (1 + m / 2))
    (Continuous.continuousOn <| by
      refine .sub (.sub ?_ ?_) continuous_const
      · exact hcb.continuous_supp.comp (continuous_snd.add continuous_const)
      · exact continuous_dot_pair.comp
          (continuous_fst.prodMk (continuous_vvec.comp continuous_snd)))
    fun t ht p hp => by
      rw [edge_eq_segment hcb, inj_vplus_eq_vminus_of_injCond1 hcb hI (t := t)
        (Or.inl ⟨ha.le.trans ht.1, ht.2.trans_lt hb⟩), segment_same, mem_singleton_iff] at hp
      have : m ≤ fMinus K₀ t - 1 := (hmle t ht).trans (min_le_left _ _)
      rw [inj_fMinus_eq, ← hp] at this
      linarith
  obtain ⟨δC, hδC, -, hC⟩ := exposed_face_property_stable h₀.1 isCompact_Icc
    (I := Icc (a + π / 2) (b + π / 2))
    (fun t ht => ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩)
    (fun p t => supp K₀ (t - π / 2) - dot p (uvec (t - π / 2)) - (1 + m / 2))
    (Continuous.continuousOn <| by
      refine .sub (.sub ?_ ?_) continuous_const
      · exact hcb.continuous_supp.comp (continuous_snd.sub continuous_const)
      · exact continuous_dot_pair.comp
          (continuous_fst.prodMk (continuous_uvec.comp (continuous_snd.sub continuous_const))))
    fun t ht p hp => by
      have hs : t - π / 2 ∈ Icc a b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      rw [edge_eq_segment hcb, ← inj_vplus_eq_vminus_of_injCond1 hcb hI (t := t)
        (Or.inr ⟨by linarith [hs.1], by linarith [hs.2]⟩), segment_same, mem_singleton_iff] at hp
      have : m ≤ gPlus K₀ (t - π / 2) - 1 := (hmle _ hs).trans (min_le_right _ _)
      rw [gPlus, cPlus, sub_add_cancel, dot_sub_left, inj_dot_outerCorner_uvec, ← hp] at this
      linarith
  -- a support error at most `m / 4` leaves a margin `m / 4`
  refine ⟨m / 4, min (m / 4) (min δA δC), by positivity, by positivity,
    (min_le_right _ _).trans ((min_le_left _ _).trans hδA1),
    fun K hK hclose => ⟨fun t ht p hp => ?_, fun t ht p hp => ?_⟩⟩
  · have h1 : 0 < supp K₀ (t + π / 2) - dot p (vvec t) - (1 + m / 2) :=
      hA K hK (hclose.mono ((min_le_right _ _).trans (min_le_left _ _))) t ht p hp
    have h2 := (abs_le.mp (hclose (t + π / 2) ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩)).1
    linarith [min_le_left (m / 4) (min δA δC)]
  · have h1 : 0 < supp K₀ t - dot p (uvec t) - (1 + m / 2) := by
      simpa only [add_sub_cancel_right] using hC K hK
        (hclose.mono ((min_le_right _ _).trans (min_le_right _ _))) (t + π / 2)
        ⟨by linarith [ht.1], by linarith [ht.2]⟩ p hp
    have h2 := (abs_le.mp (hclose t ⟨by linarith [ht.1], by linarith [ht.2, pi_pos]⟩)).1
    linarith [min_le_left (m / 4) (min δA δC)]

/-- The one-sided arm lengths inherit an arm margin. -/
theorem CoreArmMargin.oneSided {K : Set Point} (hK : IsCap K (π / 2))
    {a b c : ℝ} (h : CoreArmMargin K a b c) {t : ℝ} (ht : t ∈ Icc a b) :
    1 + c ≤ fPlus K t ∧ 1 + c ≤ fMinus K t ∧
      1 + c ≤ gPlus K t ∧ 1 + c ≤ gMinus K t := by
  rw [inj_fPlus_eq, inj_fMinus_eq]
  simp only [gPlus, gMinus, cPlus, cMinus, dot_sub_left, inj_dot_outerCorner_uvec]
  exact ⟨h.1 t ht _ (vplus_mem_edge hK.2.1 t), h.1 t ht _ (vminus_mem_edge hK.2.1 t),
    h.2 t ht _ (vplus_mem_edge hK.2.1 _), h.2 t ht _ (vminus_mem_edge hK.2.1 _)⟩

/-! ## The core moves left at a definite speed

A one-sided mean value inequality bounds increments by a constant bound on the right derivative; it
presumes neither integrability nor continuity of the right derivative. With an arm margin, this
makes the core strictly monotone and separates it from the cuts.
-/

/-- The right derivative of the inner corner of a cap. -/
def cornerRightVelocity (K : Set Point) (t : ℝ) : Point :=
  -(fPlus K t - 1) • uvec t + (gPlus K t - 1) • vvec t

/-- The inner corner of a cap has right derivative `cornerRightVelocity`. -/
theorem corner_hasRightDeriv {K : Set Point} (hK : IsCap K (π / 2)) (t : ℝ) :
    HasDerivWithinAt (innerCorner K) (cornerRightVelocity K t) (Ioi t) t :=
  (theorem6_2_3_right hK).2.mono Ioi_subset_Ici_self

/-- Projection onto a fixed unit vector preserves right derivatives. -/
theorem hasRightDeriv_dot_uvec {x dx : ℝ → Point} {t d : ℝ}
    (h : HasDerivWithinAt x (dx t) (Ioi t) t) :
    HasDerivWithinAt (fun s => dot (x s) (uvec d)) (dot (dx t) (uvec d)) (Ioi t) t := by
  have h1 : HasDerivWithinAt (fun s => (x s).1) (dx t).1 (Ioi t) t :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := x t)).comp_hasDerivWithinAt t h
  have h2 : HasDerivWithinAt (fun s => (x s).2) (dx t).2 (Ioi t) t :=
    (hasFDerivAt_snd (𝕜 := ℝ) (p := x t)).comp_hasDerivWithinAt t h
  exact (h1.mul_const (cos d)).add (h2.mul_const (sin d))

/-- An upper bound on the right derivative bounds the increments from above. -/
theorem right_derivative_increment_le {f df : ℝ → ℝ} {a b B : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hB : ∀ t ∈ Ioo a b, df t ≤ B) : f b - f a ≤ B * (b - a) := by
  have h := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab hf hd
    (φ := fun _ => B) (continuousOn_const.integrableOn_compact isCompact_Icc) hB
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h

/-- A lower bound on the right derivative bounds the increments from below. -/
theorem right_derivative_increment_ge {f df : ℝ → ℝ} {a b B : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hB : ∀ t ∈ Ioo a b, B ≤ df t) : B * (b - a) ≤ f b - f a := by
  have h := right_derivative_increment_le hab hf.neg
    (fun t ht => (hd t ht).neg) (B := -B) (fun t ht => neg_le_neg (hB t ht))
  simp only [Pi.neg_apply] at h
  linarith

/-- With an arm margin `c`, the projection of the core onto the normal `uvec d` of an earlier cut,
`t - d ∈ [0, π/2]`, decreases at speed at least `c`. -/
theorem CoreArmMargin.right_cut_velocity {K : Set Point} (hK : IsCap K (π / 2))
    {a b c t d : ℝ} (h : CoreArmMargin K a b c) (hc : 0 ≤ c)
    (ht : t ∈ Icc a b) (hangle : t - d ∈ Icc (0 : ℝ) (π / 2)) :
    dot (cornerRightVelocity K t) (uvec d) ≤ -c := by
  obtain ⟨hf, -, hg, -⟩ := h.oneSided hK ht
  have hs := sin_nonneg_of_nonneg_of_le_pi hangle.1 (by linarith [hangle.2, pi_pos])
  have hco := cos_nonneg_of_mem_Icc ⟨by linarith [hangle.1, pi_pos], hangle.2⟩
  -- `sin (t - d) + cos (t - d) ≥ sin² (t - d) + cos² (t - d) = 1`
  have h1 : 1 ≤ sin (t - d) + cos (t - d) := by
    nlinarith [sin_sq_add_cos_sq (t - d), sin_le_one (t - d), cos_le_one (t - d)]
  simp only [cornerRightVelocity, dot_add_left, dot_smul_left, dot_uvec_uvec, dot_vvec_uvec']
  rw [show d - t = -(t - d) by ring, sin_neg]
  linarith [mul_le_mul_of_nonneg_right (show c ≤ fPlus K t - 1 by linarith) hco,
    mul_le_mul_of_nonneg_right (show c ≤ gPlus K t - 1 by linarith) hs,
    mul_le_mul_of_nonneg_left h1 hc]

/-- With an arm margin `c`, the core moves left at speed at least `c`. -/
theorem CoreArmMargin.velocity_fst_le {K : Set Point} (hK : IsCap K (π / 2))
    {a b c t : ℝ} (h : CoreArmMargin K a b c) (hc : 0 ≤ c)
    (ht : t ∈ Icc a b) (hti : t ∈ Icc (0 : ℝ) (π / 2)) :
    (cornerRightVelocity K t).1 ≤ -c := by
  simpa only [dot_uvec_zero] using h.right_cut_velocity hK hc ht (d := 0) (by rwa [sub_zero])

/-- With an arm margin `c`, the core moves left by at least `c` times the angle. -/
theorem CoreArmMargin.horizontal_decrease {K : Set Point} (hK : IsCap K (π / 2))
    {a b c : ℝ} (h : CoreArmMargin K a b c) (hc : 0 ≤ c)
    (ha : 0 ≤ a) (hb : b ≤ π / 2) {u v : ℝ}
    (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u ≤ v) :
    (innerCorner K v).1 - (innerCorner K u).1 ≤ -c * (v - u) :=
  right_derivative_increment_le huv (opt_innerCorner_continuous hK.2.1).fst.continuousOn
    (fun t _ => (corner_hasRightDeriv hK t).fst) fun _ ht =>
      h.velocity_fst_le hK hc ⟨hu.1.trans ht.1.le, ht.2.le.trans hv.2⟩
        ⟨ha.trans (hu.1.trans ht.1.le), (ht.2.le.trans hv.2).trans hb⟩

/-- With a positive arm margin, the abscissa of the core is strictly decreasing. -/
theorem CoreArmMargin.strictAnti_core {K : Set Point} (hK : IsCap K (π / 2))
    {a b c : ℝ} (h : CoreArmMargin K a b c) (hc : 0 < c)
    (ha : 0 ≤ a) (hb : b ≤ π / 2) :
    StrictAntiOn (fun t => (innerCorner K t).1) (Icc a b) := fun u hu v hv huv => by
  have := h.horizontal_decrease hK hc.le ha hb hu hv huv.le
  linarith [mul_pos hc (sub_pos.mpr huv)]

/-- With an arm margin `c`, the projection of the core onto the normal `uvec (d + π/2)` of a later
cut, `d - t ∈ [0, π/2]`, increases at speed at least `c`; this is `right_cut_velocity` at the
angle `d - π/2`. -/
theorem CoreArmMargin.left_cut_velocity {K : Set Point} (hK : IsCap K (π / 2))
    {a b c t d : ℝ} (h : CoreArmMargin K a b c) (hc : 0 ≤ c)
    (ht : t ∈ Icc a b) (hangle : d - t ∈ Icc (0 : ℝ) (π / 2)) :
    c ≤ dot (cornerRightVelocity K t) (uvec (d + π / 2)) := by
  have := h.right_cut_velocity hK hc ht (d := d - π / 2)
    ⟨by linarith [hangle.2], by linarith [hangle.1]⟩
  rw [show d + π / 2 = d - π / 2 + π by ring, dot_uvec_add_pi]
  linarith

/-! ## Horizontal localization of the niche

A point of the niche lies in a forbidden wedge at an angle `t ∈ (0, π/2)`, strictly between the feet
of the wedge on the floor. The feet are quotients by `sin t` and `cos t`; near the endpoint angles,
where these are small, the top contacts of the cap bound the feet instead of the support error.
-/

/-- The abscissa at which the inner wall `b_K(t)` meets the floor. -/
def wedgeRightFoot (K : Set Point) (t : ℝ) : ℝ := (supp K t - 1) / cos t

/-- The abscissa at which the inner wall `d_K(t)` meets the floor. -/
def wedgeLeftFoot (K : Set Point) (t : ℝ) : ℝ := (1 - supp K (t + π / 2)) / sin t

/-- Sine and cosine are positive on `(0, π/2)`. -/
private theorem sin_cos_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (π / 2)) : 0 < sin t ∧ 0 < cos t :=
  ⟨sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos]),
    cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩⟩

/-- A point of a forbidden wedge above the floor lies strictly between the feet of the wedge. -/
theorem wedge_point_between_feet {K : Set Point} {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (π / 2)) {p : Point} (hpy : 0 ≤ p.2)
    (hu : innerSlackU K t p < 0) (hv : innerSlackV K t p < 0) :
    wedgeLeftFoot K t < p.1 ∧ p.1 < wedgeRightFoot K t := by
  obtain ⟨hs, hc⟩ := sin_cos_pos ht
  simp only [innerSlackU, innerSlackV, dot, uvec, vvec] at hu hv
  rw [wedgeLeftFoot, wedgeRightFoot, div_lt_iff₀ hs, lt_div_iff₀ hc]
  constructor <;> linarith [mul_nonneg hpy hc.le, mul_nonneg hpy hs.le]

/-- A floor point strictly between the feet of a wedge lies in the niche. -/
private theorem floor_between_feet_mem_niche {K : Set Point} {t x : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (π / 2)) (hx : x ∈ Ioo (wedgeLeftFoot K t) (wedgeRightFoot K t)) :
    (x, 0) ∈ niche K (π / 2) := by
  obtain ⟨hs, hc⟩ := sin_cos_pos ht
  have h1 := hx.1
  have h2 := hx.2
  rw [wedgeLeftFoot, div_lt_iff₀ hs] at h1
  rw [wedgeRightFoot, lt_div_iff₀ hc] at h2
  refine (mem_niche_iff_slacks K (x, 0)).2 ⟨le_rfl, t, ht, ?_, ?_⟩ <;>
    simp only [innerSlackU, innerSlackV, dot, uvec, vvec] <;> linarith

/-- Gerver's inner corner is above the floor at every open angle, including the two phases where
it is not a contact. -/
private theorem gerver_path_height_pos {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (π / 2)) : 0 < (P.path t).2 := by
  have henv := gn_envHyp hP (romik_bounds hP hbox)
  have hbounds := envelope_bounds_of_path_height henv
    fun u hu => path_snd_lt_one hP (romik_bounds hP hbox) hu.1 hu.2
  obtain ⟨hs, hc⟩ := sin_cos_pos ht
  by_cases hfirst : t < P.φ
  · have hD : envD P.path P.gs_β t ∈ gerverEnvelope P :=
      Or.inr ⟨t, ⟨ht.1.le, hfirst.le.trans henv.ht.2.1.le⟩, rfl⟩
    have hDy := (hbounds _ hD).2.1
    simp only [envD, Prod.snd_sub, Prod.smul_snd, smul_eq_mul, uvec_snd] at hDy
    linarith [mul_pos (henv.β_pos t ht) hs]
  by_cases hlast : π / 2 - P.φ < t
  · have hB : envB P.path P.gs_α t ∈ gerverEnvelope P :=
      Or.inl (Or.inl ⟨t, ⟨henv.ht.2.2.2.1.le.trans hlast.le, ht.2.le⟩, rfl⟩)
    have hBy := (hbounds _ hB).2.1
    simp only [envB, Prod.snd_add, Prod.smul_snd, smul_eq_mul, vvec_snd] at hBy
    linarith [mul_neg_of_neg_of_pos (henv.α_neg t ht) hc]
  exact henv.x_pos t ⟨not_lt.mp hfirst, not_lt.mp hlast⟩

/-- Both wedge feet of Gerver's cap lie in the roof interval at every open angle. -/
theorem gerver_wedge_feet_bounds {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (π / 2)) :
    gerverRoofLeft P ≤ wedgeLeftFoot P.cap t ∧
      wedgeRightFoot P.cap t ≤ gerverRoofRight P := by
  obtain ⟨hs, hc⟩ := sin_cos_pos ht
  -- the feet are in order, since the inner corner is above the floor
  have hZW : wedgeLeftFoot P.cap t < wedgeRightFoot P.cap t := by
    have hp := gerver_path_height_pos hP hbox ht
    rw [← ((theorem8_4_1_monotone hP hbox).2 t ⟨ht.1.le, ht.2.le⟩).2.2,
      proposition2_2_2_innerCorner] at hp
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, uvec_snd, vvec_snd] at hp
    rw [wedgeLeftFoot, wedgeRightFoot, div_lt_div_iff₀ hs hc]
    linarith
  -- the floor points between the feet lie in Gerver's niche, hence over the roof interval
  obtain ⟨H, L, γ, hroof⟩ := gerver_roof_data hP hbox
  refine (Icc_subset_Icc_iff hZW.le).1 ?_
  rw [← closure_Ioo hZW.ne, isClosed_Icc.closure_subset_iff]
  intro x hx
  have h := floor_between_feet_mem_niche ht hx
  rw [hroof.niche_eq] at h
  exact h.1

/-- Gerver's top face lies between its two contact endpoints. -/
private theorem gerver_top_face_bounds {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {p : Point} (hp : p ∈ edge P.cap (π / 2)) :
    gerverRoofLeft P ≤ p.1 ∧ p.1 ≤ gerverRoofRight P := by
  have hcb := gm_isConvexBody_cap hP hbox
  have ha : vminus P.cap (π / 2) = (gerverRoofRight P, 1) :=
    ((theorem8_4_1_monotone hP hbox).2 (π / 2) ⟨by positivity, le_rfl⟩).1.trans
      (gerver_contactA_pi_div_two hP (romik_bounds hP hbox))
  have hc : vplus P.cap (π / 2) = (gerverRoofLeft P, 1) := by
    simpa only [cK, cPlus, zero_add, gerverRoofLeft] using
      ((theorem8_4_1_monotone hP hbox).2 0 ⟨le_rfl, by positivity⟩).2.1.trans
        (gerver_contactC_zero hP (romik_bounds hP hbox))
  have h1 := dot_vminus_le_dot hcb.2.1 hp
  have h2 := dot_le_dot_vplus hcb.2.1 hp
  rw [ha] at h1
  rw [hc] at h2
  simp only [dot, vvec_pi_div_two] at h1 h2
  constructor <;> linarith

/-- Every point of a face of a nearby cap at a normal near `π/2` lies strictly over the
`η`-enlargement of Gerver's roof interval. -/
theorem gerver_near_top_contacts {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧ δ ≤ 1 ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K P.cap →
        ∀ t ∈ Icc (0 : ℝ) π, |t - π / 2| ≤ ρ → ∀ p ∈ edge K t,
          gerverRoofLeft P - η < p.1 ∧ p.1 < gerverRoofRight P + η := by
  obtain ⟨δ, ρ, hδ, hρ, hδ1, h⟩ := face_property_stable_in_angle (gm_isCap hP hbox) (π / 2)
    (fun p => min (p.1 - (gerverRoofLeft P - η)) (gerverRoofRight P + η - p.1))
    ((continuous_fst.sub continuous_const).min (continuous_const.sub continuous_fst))
    fun p hp => by
      obtain ⟨hl, hr⟩ := gerver_top_face_bounds hP hbox hp
      exact lt_min (by linarith) (by linarith)
  refine ⟨δ, ρ, hδ, hρ, hδ1, fun K hK hclose t ht hnear p hp => ?_⟩
  have := lt_min_iff.mp (h K hK hclose t ht hnear p hp)
  constructor <;> linarith [this.1, this.2]

/-- The niches of nearby caps lie over an arbitrarily small enlargement of Gerver's roof
interval. -/
theorem nearby_niche_horizontal_localization {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K P.cap →
      ∀ p ∈ niche K (π / 2), gerverRoofLeft P - η ≤ p.1 ∧ p.1 ≤ gerverRoofRight P + η := by
  obtain ⟨δ₀, ρ₀, hδ₀, hρ₀, hδ₀1, htop⟩ := gerver_near_top_contacts hP hbox hη
  obtain ⟨ρ, hρ, hρ₀, hρ4⟩ : ∃ ρ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ ρ ≤ π / 4 :=
    ⟨min ρ₀ (π / 4), lt_min hρ₀ (by positivity), min_le_left _ _, min_le_right _ _⟩
  have hsρ : 0 < sin ρ := sin_pos_of_pos_of_lt_pi hρ (by linarith [pi_pos])
  refine ⟨min δ₀ (η * sin ρ), lt_min hδ₀ (mul_pos hη hsρ), (min_le_left _ _).trans hδ₀1,
    fun K hK hclose p hp => ?_⟩
  have hδρ := min_le_right δ₀ (η * sin ρ)
  have hclose₀ := hclose.mono (min_le_left _ _)
  obtain ⟨hpy, t, ht, hu, hv⟩ := (mem_niche_iff_slacks K p).1 hp
  obtain ⟨hleft, hright⟩ := wedge_point_between_feet ht hpy hu hv
  obtain ⟨hrefL, hrefR⟩ := gerver_wedge_feet_bounds hP hbox ht
  obtain ⟨hs, hc⟩ := sin_cos_pos ht
  constructor
  · by_cases hnear : t ≤ ρ
    · -- the left foot is right of the top contact `vplus K (t + π / 2)`, which is near the roof
      have hq := vplus_mem_edge hK.2.1 (t + π / 2)
      have hqx := (htop K hK hclose₀ (t + π / 2) ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
        (by rw [add_sub_cancel_right, abs_of_pos ht.1]; linarith) _ hq).1
      have : (vplus K (t + π / 2)).1 ≤ wedgeLeftFoot K t := by
        rw [wedgeLeftFoot, le_div_iff₀ hs, ← hq.2, uvec_add_pi_div_two]
        simp only [dot, vvec]
        linarith [mul_le_mul (hK.snd_le_one hq.1) (cos_le_one t) hc.le zero_le_one]
      linarith
    · -- `sin t ≥ sin ρ`, so the support error moves the left foot by at most `η`
      have hden : sin ρ ≤ sin t :=
        sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) ht.2.le (not_le.mp hnear).le
      have herr := (abs_le.mp (hclose (t + π / 2)
        ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩)).2
      have hcanc := div_mul_cancel₀ (1 - supp P.cap (t + π / 2)) hs.ne'
      have : wedgeLeftFoot P.cap t - η ≤ wedgeLeftFoot K t := by
        rw [wedgeLeftFoot, wedgeLeftFoot, le_div_iff₀ hs]
        linarith [mul_le_mul_of_nonneg_left hden hη.le]
      linarith
  · by_cases hnear : π / 2 - ρ ≤ t
    · -- the right foot is left of the top contact `vplus K t`, which is near the roof
      have hq := vplus_mem_edge hK.2.1 t
      have hqx := (htop K hK hclose₀ t ⟨ht.1.le, by linarith [ht.2, pi_pos]⟩
        (by rw [abs_of_nonpos (by linarith [ht.2] : t - π / 2 ≤ 0)]; linarith) _ hq).2
      have : wedgeRightFoot K t ≤ (vplus K t).1 := by
        rw [wedgeRightFoot, div_le_iff₀ hc, ← hq.2]
        simp only [dot, uvec]
        linarith [mul_le_mul (hK.snd_le_one hq.1) (sin_le_one t) hs.le zero_le_one]
      linarith
    · -- `cos t ≥ sin ρ`, so the support error moves the right foot by at most `η`
      have hden : sin ρ ≤ cos t := by
        rw [← sin_pi_div_two_sub]
        exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) (by linarith [ht.1])
          (by linarith [not_le.mp hnear])
      have herr := (abs_le.mp (hclose t ⟨ht.1.le, by linarith [ht.2, pi_pos]⟩)).2
      have hcanc := div_mul_cancel₀ (supp P.cap t - 1) hc.ne'
      have : wedgeRightFoot K t ≤ wedgeRightFoot P.cap t + η := by
        rw [wedgeRightFoot, wedgeRightFoot, div_le_iff₀ hc]
        linarith [mul_le_mul_of_nonneg_left hden hη.le]
      linarith

/-! ## The niche lies in the cap

A cap near Gerver's need not be injective. Instead, the horizontal localization of its niche and a
uniform height bound place the niche in a fixed rectangle under Gerver's roof, at a positive
distance from the upper walls of Gerver's cap.
-/

/-- A compact rectangle strictly below an interior horizontal chord of a cap has a uniform margin
from every upper supporting line of the cap. -/
theorem cap_rectangle_upper_margin {K : Set Point} (hK : IsCap K (π / 2))
    {a b h H : ℝ} (hab : a < b) (ha : -supp K π < a) (hb : b < supp K 0)
    (hh : h < H) (hleft : (a, H) ∈ K) (hright : (b, H) ∈ K) :
    ∃ m : ℝ, 0 < m ∧ ∀ p ∈ Icc a b ×ˢ Icc (0 : ℝ) h,
      ∀ t ∈ Icc (0 : ℝ) π, m ≤ supp K t - dot p (uvec t) := by
  have hpos : ∀ z ∈ (Icc a b ×ˢ Icc (0 : ℝ) h) ×ˢ Icc (0 : ℝ) π,
      0 < supp K z.2 - dot z.1 (uvec z.2) := by
    rintro ⟨p, t⟩ ⟨hp, ht⟩
    dsimp only at hp ht ⊢
    rcases ht.1.eq_or_lt with rfl | ht0
    · rw [dot_uvec_zero]
      linarith [hp.1.2]
    rcases ht.2.eq_or_lt with rfl | htπ
    · rw [dot_uvec_pi]
      linarith [hp.1.1]
    -- the point `(p.1, H)` of the chord lies in `K`, above `p`
    have hHt : (p.1, H) ∈ K := by
      have hba : 0 < b - a := sub_pos.mpr hab
      convert hK.2.1.2.2.add_smul_sub_mem hleft hright
        ⟨div_nonneg (sub_nonneg.mpr hp.1.1) hba.le, (div_le_one hba).2 (by linarith [hp.1.2])⟩
        using 1
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
        field_simp
        ring
      · simp
    have h1 := dot_le_supp hK.2.1.2.1 hHt t
    have h2 := mul_pos (show 0 < H - p.2 by linarith [hp.2.2]) (sin_pos_of_pos_of_lt_pi ht0 htπ)
    simp only [dot, uvec] at h1 ⊢
    linarith
  obtain ⟨m, hm, hmin⟩ := ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).exists_forall_le'
    ((hK.2.1.continuous_supp.comp continuous_snd).sub (continuous_dot_pair.comp
      (continuous_fst.prodMk (continuous_uvec.comp continuous_snd)))).continuousOn hpos
  exact ⟨m, hm, fun p hp t ht => hmin (p, t) ⟨hp, ht⟩⟩

/-- A point of a forbidden wedge lies strictly below the inner corner. -/
theorem point_below_corner_of_negative_slacks {K : Set Point} {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (π / 2)) {p : Point}
    (hu : innerSlackU K t p < 0) (hv : innerSlackV K t p < 0) :
    p.2 < (innerCorner K t).2 := by
  obtain ⟨hs, hc⟩ := sin_cos_pos ht
  have he : p.2 - (innerCorner K t).2 =
      innerSlackU K t p * sin t + innerSlackV K t p * cos t := by
    rw [proposition2_2_2_innerCorner]
    simp only [innerSlackU, innerSlackV, dot, uvec, vvec, Prod.snd_add,
      Prod.smul_snd, smul_eq_mul]
    linear_combination -p.2 * sin_sq_add_cos_sq t
  linarith [mul_neg_of_neg_of_pos hu hs, mul_neg_of_neg_of_pos hv hc]

/-- The niches of nearby caps lie uniformly below height one. -/
theorem nearby_niche_height {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ H δ : ℝ, H < 1 ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K P.cap →
        ∀ p ∈ niche K (π / 2), p.2 ≤ H := by
  -- Gerver's rotation path has a highest point, below one
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) (π / 2)).Nonempty from ⟨0, le_rfl, by positivity⟩)
    (gn_envHyp hP (romik_bounds hP hbox)).x_cont.snd
  have hM : (P.path t).2 < 1 := path_snd_lt_one hP (romik_bounds hP hbox) ht.1 ht.2
  refine ⟨((P.path t).2 + 1) / 2, min 1 ((1 - (P.path t).2) / 4), by linarith,
    lt_min one_pos (by linarith), min_le_left _ _, fun K hK hclose p hp => ?_⟩
  -- `p` lies below the inner corner of `K`, which is `2δ`-close to Gerver's
  obtain ⟨-, s, hs, hu, hv⟩ := (mem_niche_iff_slacks K p).1 hp
  have hd := innerCorner_support_error hclose ⟨hs.1.le, hs.2.le⟩
  have hy := abs_snd_le_norm2 (innerCorner K s - innerCorner P.cap s)
  rw [((theorem8_4_1_monotone hP hbox).2 s ⟨hs.1.le, hs.2.le⟩).2.2] at hd hy
  have hupper : (P.path s).2 ≤ (P.path t).2 := hmax ⟨hs.1.le, hs.2.le⟩
  have hdiff : (innerCorner K s).2 - (P.path s).2 ≤ 2 * min 1 ((1 - (P.path t).2) / 4) :=
    (le_abs_self _).trans (hy.trans hd)
  linarith [point_below_corner_of_negative_slacks hs hu hv,
    min_le_right 1 ((1 - (P.path t).2) / 4)]

/-- Clamping `x` to `[a, b]` moves it by at most its distance `η` outside `[a, b]`. -/
private theorem clamp_interval_bound {a b x η : ℝ} (hab : a ≤ b) (hη : 0 ≤ η)
    (hx : a - η ≤ x ∧ x ≤ b + η) :
    max a (min x b) ∈ Icc a b ∧ |x - max a (min x b)| ≤ η := by
  refine ⟨⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩, ?_⟩
  by_cases hxa : x ≤ a
  · rw [min_eq_left (hxa.trans hab), max_eq_left hxa, abs_of_nonpos (sub_nonpos.mpr hxa)]
    linarith [hx.1]
  by_cases hbx : b ≤ x
  · rw [min_eq_right hbx, max_eq_right hab, abs_of_nonneg (sub_nonneg.mpr hbx)]
    linarith [hx.2]
  rw [min_eq_left (not_le.mp hbx).le, max_eq_right (not_le.mp hxa).le, sub_self, abs_zero]
  exact hη

/-- The niche of a nearby cap lies in the cap, without any injectivity of the cap. -/
theorem nearby_niche_subset_cap {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K P.cap → niche K (π / 2) ⊆ K := by
  obtain ⟨H, δH, hH, hδH, hδH1, hheight⟩ := nearby_niche_height hP hbox
  obtain ⟨H₀, L, γ, hroof⟩ := gerver_roof_data hP hbox
  -- the rectangle of height `H` under the roof keeps a margin `m` from the upper walls of the cap
  obtain ⟨m, hm, hmargin⟩ := cap_rectangle_upper_margin hroof.cap hroof.order
    hroof.left_wing hroof.right_wing hH
    (hroof.rectangle ⟨⟨le_rfl, hroof.order.le⟩, zero_le_one, le_rfl⟩)
    (hroof.rectangle ⟨⟨hroof.order.le, le_rfl⟩, zero_le_one, le_rfl⟩)
  obtain ⟨δN, hδN, -, hwidth⟩ := nearby_niche_horizontal_localization hP hbox
    (show 0 < m / 4 by positivity)
  refine ⟨min δH (min δN (m / 4)), by positivity, (min_le_left _ _).trans hδH1,
    fun K hK hclose p hp => ?_⟩
  have hδm := (min_le_right δH _).trans (min_le_right δN (m / 4))
  have hy0 := ((mem_niche_iff_slacks K p).1 hp).1
  -- `p` is horizontally within `m / 4` of the point `(x, p.2)` of the rectangle
  obtain ⟨hx, hpx⟩ := clamp_interval_bound hroof.order.le (by positivity)
    (hwidth K hK (hclose.mono ((min_le_right _ _).trans (min_le_left _ _))) p hp)
  set x := max (gerverRoofLeft P) (min p.1 (gerverRoofRight P))
  have hq := hmargin (x, p.2) ⟨hx, hy0, hheight K hK (hclose.mono (min_le_left _ _)) p hp⟩
  refine (cap_mem_iff_upper hK p).2 ⟨hy0, fun t ht => ?_⟩
  have hcos : (p.1 - x) * cos t ≤ m / 4 := (le_abs_self _).trans <| (abs_mul _ _).trans_le <|
    (mul_le_mul hpx (abs_cos_le_one t) (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  have he := (abs_le.mp (hclose t ht)).1
  simp only [dot, uvec] at hq ⊢
  linarith [hq t ht]

/-! ## Cut feet from the bottom width

A bottom width of `21/10` puts the cut feet for the small cut angles on the bottom face and keeps
the two cut regions apart. This needs neither continuity of the area, nor regularity of the
curvature, nor injectivity of the cap.
-/

/-- The width `h_K(0) + h_K(π)` of the bottom face of a cap. -/
def bottomWidth (K : Set Point) : ℝ := supp K 0 + supp K π

/-- The area of a cap is at most its bottom width. -/
theorem area_le_bottomWidth {K : Set Point} (hK : IsCap K (π / 2)) : area K ≤ bottomWidth K := by
  simpa only [bottomWidth, sub_neg_eq_add, add_comm] using
    opt_area_le_of_fst_bounds hK fun p hp => opt_cap_fst_le hK hp

/-- A cap within support distance `1/20` of Gerver's cap has bottom width at least `21/10`. -/
theorem nearby_bottomWidth {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hclose : UpperSupportClose (1 / 20) K P.cap) :
    (21 / 10 : ℝ) ≤ bottomWidth K := by
  have hKi := theorem8_1_1_gerver hP hbox
  have hw := area_le_bottomWidth hKi.1
  have h0 := (abs_le.mp (hclose 0 ⟨le_rfl, pi_pos.le⟩)).1
  have hπ := (abs_le.mp (hclose π ⟨pi_pos.le, le_rfl⟩)).1
  unfold bottomWidth at *
  linarith [hKi.2.2]

/-- Both cut feet lie on the bottom face, strictly between its endpoints. -/
theorem cut_feet_mem_of_width {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04)
    {K : Set Point} (hK : IsCap K (π / 2)) (hwidth : (21 / 10 : ℝ) ≤ bottomWidth K) :
    wRight φ K ∈ edge K (3 * π / 2) \ {aK K 0, cK K (π / 2)} ∧
      zLeft φ K ∈ edge K (3 * π / 2) \ {aK K 0, cK K (π / 2)} := by
  obtain ⟨hφ0, hφ4, -, hc9, -⟩ := opt_phi_bounds hφ
  have hc : 0 < cos φ := by linarith
  have hwidthmul := mul_le_mul_of_nonneg_right hwidth hc.le
  have hA := dot_le_supp hK.2.1.2.1 (opt_cap_A_mem hK) φ
  have hC := dot_le_supp hK.2.1.2.1 (opt_cap_C_mem hK) (π - φ)
  simp only [dot, uvec, cos_pi_sub, sin_pi_sub, zero_mul, add_zero] at hA hC
  unfold bottomWidth at hwidthmul
  constructor
  · rw [opt_wRight_eq]
    refine opt_mem_bottom_edge hK ?_ ?_
    · rw [lt_div_iff₀ hc]
      linarith
    · rw [div_lt_iff₀ hc]
      linarith [(theorem2_5_5_supp hK (t := φ) ⟨hφ0, by linarith⟩).1]
  · rw [opt_zLeft_eq]
    refine opt_mem_bottom_edge hK ?_ ?_
    · have h := (theorem2_5_5_supp hK (t := π / 2 - φ) ⟨by linarith, by linarith⟩).2
      rw [show π / 2 - φ + π / 2 = π - φ by ring, add_halves, sub_sub_cancel] at h
      rw [lt_div_iff₀ hc]
      linarith
    · rw [div_lt_iff₀ hc]
      linarith

/-- The two cut half-planes do not meet inside a cap of bottom width at least `21/10`. -/
theorem cut_regions_disjoint_of_width {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04)
    {K : Set Point} (hK : IsCap K (π / 2)) (hwidth : (21 / 10 : ℝ) ≤ bottomWidth K) :
    Disjoint (K ∩ hRight φ K) (K ∩ hLeft φ K) := by
  obtain ⟨-, -, hs4, hc9, hs0⟩ := opt_phi_bounds hφ
  have hA := dot_le_supp hK.2.1.2.1 (opt_cap_A_mem hK) φ
  have hC := dot_le_supp hK.2.1.2.1 (opt_cap_C_mem hK) (π - φ)
  simp only [dot, uvec, cos_pi_sub, sin_pi_sub, zero_mul, add_zero] at hA hC
  have hwidthmul := mul_le_mul_of_nonneg_right hwidth (by linarith : (0 : ℝ) ≤ cos φ)
  unfold bottomWidth at hwidthmul
  rw [Set.disjoint_left]
  rintro p ⟨hpK, hpR⟩ ⟨-, hpL⟩
  change supp K φ - 1 ≤ dot p (uvec φ) at hpR
  change supp K (π / 2 - φ + π / 2) - 1 ≤ dot p (uvec (π / 2 - φ + π / 2)) at hpL
  rw [show π / 2 - φ + π / 2 = π - φ by ring] at hpL
  simp only [dot, uvec, cos_pi_sub, sin_pi_sub] at hpR hpL
  linarith [mul_le_mul_of_nonneg_right (hK.snd_le_one hpK) hs0.le]

/-! ## The canonical triple

The topmost-point proof of the endpoint contacts in the optimality proof needs only a cap, a cut
foot in the cap and one strict arm inequality at the cut. With these contacts, the canonical
triple of every cap near Gerver's lies in `T̄`, without injectivity of the cap or feasibility of its
canonical tails.
-/

/-- The right canonical body touches its cut line, given the strict `g`-arm inequality at the
cut. -/
theorem canonical_right_contact {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set Point} (hcap : IsCap K (π / 2)) (hW : wRight φ K ∈ K)
    (hg : 1 < gPlus K φ) :
    ∃ p ∈ rightBody φ K, dot p (uvec φ) = supp K φ - 1 := by
  obtain ⟨hφ0, hφ4⟩ := hφ
  have hcb := hcap.2.1
  -- the point `p` of `K` on the cut line farthest in the direction `vvec φ`
  have hWL : wRight φ K ∈ K ∩ line φ (supp K φ - 1) := by
    refine ⟨hW, ?_⟩
    simp only [line, mem_ofPred_eq, opt_wRight_eq, dot, uvec, zero_mul, add_zero]
    field_simp [(cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩ : 0 < cos φ).ne']
  obtain ⟨p, ⟨hpK, hpl : dot p (uvec φ) = supp K φ - 1⟩, hpmax⟩ :=
    (hcb.2.1.inter_right (isClosed_line _ _)).exists_isMaxOn
      ⟨_, hWL⟩ (continuous_dot (vvec φ)).continuousOn
  -- `p` is a contact of `K` at some normal `θ ∈ [φ, φ + π/2]`
  obtain ⟨θ, hθ, hpθ⟩ := opt_exists_normal_of_isMax hcb hpK hpl
    (fun q hq hql => hpmax ⟨hq, hql⟩)
  have hp2 := inj_cap_strip hcap hpK
  have hθ2 : θ ≤ φ + π / 2 := by
    by_contra hnot
    let c := vplus K (φ + π / 2)
    have h1 : dot p (uvec (φ + π / 2)) ≤ dot c (uvec (φ + π / 2)) :=
      (dot_le_supp hcb.2.1 hpK _).trans_eq (dot_vplus_uvec K _).symm
    have h2 : dot c (uvec θ) ≤ dot p (uvec θ) :=
      hpθ ▸ dot_le_supp hcb.2.1 (vplus_mem_edge hcb _).1 _
    have ep := dot_uvec_eq_cos_add_sin p θ φ
    have ec := dot_uvec_eq_cos_add_sin c θ φ
    rw [← uvec_add_pi_div_two] at ep ec
    have hcos : cos (θ - φ) < 0 :=
      cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [hθ.2])
    have hsin : 0 ≤ sin (θ - φ) :=
      sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    have key : dot p (uvec φ) ≤ dot c (uvec φ) := by
      nlinarith [mul_le_mul_of_nonneg_left h1 hsin]
    rw [inj_gPlus_eq, vvec_add_pi_div_two, dot_neg_right] at hg
    change 1 < supp K φ + -dot c (uvec φ) at hg
    linarith
  -- the sublinearity of the support function between `φ` and `θ`, and between `θ` and `π/2`
  refine ⟨p, ⟨hpK, mem_iInter₂.2 fun s hs => ?_⟩, hpl⟩
  change supp K s - 1 ≤ dot p (uvec s)
  rcases le_or_gt s θ with hsθ | hsθ
  · rcases hθ.1.eq_or_lt with hθφ | hθφ
    · rw [le_antisymm (hθφ ▸ hsθ) hs.1]
      linarith
    · have hI := opt_supp_interp hcb hs.1 hsθ (by linarith)
      have hE := dot_uvec_comb p φ θ s
      have hsinpos : 0 < sin (θ - φ) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have hmono : sin (θ - s) ≤ sin (θ - φ) :=
        sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith [hs.1])
      have hs1 : 0 ≤ sin (s - φ) :=
        sin_nonneg_of_nonneg_of_le_pi (by linarith [hs.1]) (by linarith)
      rw [hpθ, hpl] at hE
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
    have hs1 : 0 ≤ sin (s - θ) :=
      sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθ.1, hs.2])
    nlinarith [mul_le_mul_of_nonneg_left hp2.2 hs1, mul_nonneg hs1 hp2.1]

/-- The left canonical body touches its cut line, given the strict `f`-arm inequality at the cut. -/
theorem canonical_left_contact {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set Point} (hcap : IsCap K (π / 2)) (hZ : zLeft φ K ∈ K)
    (hf : 1 < fMinus K (π / 2 - φ)) :
    ∃ p ∈ leftBody φ K, dot p (vvec (π / 2 - φ)) = supp K (π / 2 - φ + π / 2) - 1 := by
  obtain ⟨hφ0, hφ4⟩ := hφ
  have hcb := hcap.2.1
  -- the point `p` of `K` on the cut line farthest in the direction `uvec (π / 2 - φ)`
  have hZL : zLeft φ K ∈ K ∩ {q | dot q (vvec (π / 2 - φ)) = supp K (π / 2 - φ + π / 2) - 1} := by
    refine ⟨hZ, ?_⟩
    simp only [mem_ofPred_eq, opt_zLeft_eq, dot, vvec, sin_pi_div_two_sub, zero_mul, add_zero,
      show π / 2 - φ + π / 2 = π - φ by ring]
    field_simp [(cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩ : 0 < cos φ).ne']
    ring
  obtain ⟨p, ⟨hpK, hpl : dot p (vvec (π / 2 - φ)) = supp K (π / 2 - φ + π / 2) - 1⟩, hpmax⟩ :=
    (hcb.2.1.inter_right (isClosed_eq (continuous_dot _) continuous_const)).exists_isMaxOn
      ⟨_, hZL⟩ (continuous_dot (uvec (π / 2 - φ))).continuousOn
  -- `p` is a contact of `K` at some normal `θ ∈ [π/2 - φ, π - φ]`
  have hu : ∀ q : Point, dot q (uvec (-φ)) = -dot q (vvec (π / 2 - φ)) := fun q => by
    simp only [dot, uvec, vvec, cos_neg, sin_neg, sin_pi_div_two_sub, cos_pi_div_two_sub]
    ring
  have hv : ∀ q : Point, dot q (vvec (-φ)) = dot q (uvec (π / 2 - φ)) := fun q => by
    simp only [dot, uvec, vvec, cos_neg, sin_neg, sin_pi_div_two_sub, cos_pi_div_two_sub]
    ring
  obtain ⟨θ, hθ, hpθ⟩ := opt_exists_normal_of_isMax hcb hpK (α := -φ)
    (c := -(supp K (π / 2 - φ + π / 2) - 1)) (by rw [hu, hpl])
    (fun q hq hql => by
      rw [hv, hv]
      refine hpmax ⟨hq, ?_⟩
      change dot q (vvec (π / 2 - φ)) = _
      rw [hu] at hql
      linarith)
  have hp2 := inj_cap_strip hcap hpK
  have hθ2 : π / 2 - φ ≤ θ := by
    by_contra hnot
    let a := vminus K (π / 2 - φ)
    have h1 : dot p (uvec (π / 2 - φ)) ≤ dot a (uvec (π / 2 - φ)) :=
      (dot_le_supp hcb.2.1 hpK _).trans_eq (dot_vminus_uvec K _).symm
    have h2 : dot a (uvec θ) ≤ dot p (uvec θ) :=
      hpθ ▸ dot_le_supp hcb.2.1 (vminus_mem_edge hcb _).1 θ
    have ep := dot_uvec_eq_cos_add_sin p θ (π / 2 - φ)
    have ea := dot_uvec_eq_cos_add_sin a θ (π / 2 - φ)
    have hcos : 0 ≤ cos (θ - (π / 2 - φ)) :=
      cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith⟩
    have hsin : sin (θ - (π / 2 - φ)) < 0 :=
      sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith [hθ.1])
    have key : dot p (vvec (π / 2 - φ)) ≤ dot a (vvec (π / 2 - φ)) := by
      nlinarith [mul_le_mul_of_nonneg_left h1 hcos]
    rw [inj_fMinus_eq] at hf
    change 1 < supp K (π / 2 - φ + π / 2) - dot a (vvec (π / 2 - φ)) at hf
    linarith
  -- the sublinearity of the support function between `π/2` and `θ`, and between `θ` and `π - φ`
  have hp1 : dot p (uvec (π - φ)) = supp K (π - φ) - 1 := by
    rw [show π - φ = π / 2 - φ + π / 2 by ring, uvec_add_pi_div_two]
    exact hpl
  have key : ∀ t ∈ Icc (π / 2) (π - φ), supp K t - 1 ≤ dot p (uvec t) := by
    intro t ht
    rcases le_or_gt θ t with hθt | hθt
    · rcases hθ.2.eq_or_lt with hθe | hθe
      · rw [le_antisymm ht.2 (by linarith)]
        linarith
      · have hI := opt_supp_interp hcb hθt ht.2 (by linarith)
        have hE := dot_uvec_comb p θ (π - φ) t
        have hsinpos : 0 < sin (π - φ - θ) :=
          sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
        have hmono : sin (t - θ) ≤ sin (π - φ - θ) :=
          sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith [ht.2])
        have hs1 : 0 ≤ sin (π - φ - t) :=
          sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.2]) (by linarith [ht.1])
        rw [hpθ, hp1] at hE
        nlinarith
    · have hθπ : π / 2 < θ := ht.1.trans_lt hθt
      have hI := opt_supp_interp hcb ht.1 hθt.le (by linarith [hθ.2])
      have hE := dot_uvec_comb p (π / 2) θ t
      rw [hcap.2.2.2.1] at hI
      rw [hpθ, dot_uvec_pi_div_two] at hE
      have hsinpos : 0 < sin (θ - π / 2) :=
        sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ.2])
      have hmono : sin (θ - t) ≤ sin (θ - π / 2) :=
        sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith [hθ.2]) (by linarith [ht.1])
      have hs1 : 0 ≤ sin (θ - t) :=
        sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθ.2, ht.1])
      nlinarith [mul_le_mul_of_nonneg_left hp2.2 hs1, mul_nonneg hs1 hp2.1]
  refine ⟨p, ⟨hpK, mem_iInter₂.2 fun s hs => ?_⟩, hpl⟩
  change supp K (s + π / 2) - 1 ≤ dot p (uvec (s + π / 2))
  exact key _ ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- The wall inequalities of the right canonical body hold for every cap. -/
private theorem canonical_right_wall {φ : ℝ} (hφ : 0 ≤ φ) {K : Set Point}
    (hK : IsCap K (π / 2)) {t : ℝ} (ht : t ∈ Icc φ (π / 2)) :
    supp K t + supp (rightBody φ K) (π + t) ≤ 1 := by
  have h := supp_le_of_forall (opt_rightBody_isConvexBody hφ hK).1
    (t := π + t) (c := 1 - supp K t) fun p hp => by
      have h := mem_iInter₂.mp hp.2 t ht
      change supp K t - 1 ≤ dot p (uvec t) at h
      rw [add_comm, dot_uvec_add_pi]
      linarith
  linarith

/-- The wall inequalities of the left canonical body hold for every cap. -/
private theorem canonical_left_wall {φ : ℝ} (hφ : 0 ≤ φ) {K : Set Point}
    (hK : IsCap K (π / 2)) {t : ℝ} (ht : t ∈ Icc 0 (π / 2 - φ)) :
    supp K (π / 2 + t) + supp (leftBody φ K) (3 * π / 2 + t) ≤ 1 := by
  have h := supp_le_of_forall (opt_leftBody_isConvexBody hφ hK).1
    (t := 3 * π / 2 + t) (c := 1 - supp K (π / 2 + t)) fun p hp => by
      have h := mem_iInter₂.mp hp.2 t ht
      change supp K (t + π / 2) - 1 ≤ dot p (uvec (t + π / 2)) at h
      rw [show 3 * π / 2 + t = (t + π / 2) + π by ring, dot_uvec_add_pi, add_comm (π / 2)]
      linarith
  linarith

/-- The canonical triple of a cap lies in `T̄`, given bottom width at least `21/10` and the two
strict arm inequalities at the cuts. -/
theorem canonical_inWideL_of_cut_arms {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04)
    {K : Set Point} (hK : IsCap K (π / 2)) (hwidth : (21 / 10 : ℝ) ≤ bottomWidth K)
    (hg : 1 < gPlus K φ) (hf : 1 < fMinus K (π / 2 - φ)) :
    InWideL φ K (rightBody φ K) (leftBody φ K) := by
  obtain ⟨hφ0, hφ4, -, -, -⟩ := opt_phi_bounds hφ
  have hB := opt_rightBody_isConvexBody hφ0.le hK
  have hD := opt_leftBody_isConvexBody hφ0.le hK
  obtain ⟨hW, hZ⟩ := cut_feet_mem_of_width hφ hK hwidth
  obtain ⟨p, hpB, hpR⟩ := canonical_right_contact ⟨hφ0, hφ4⟩ hK hW.1.1 hg
  obtain ⟨q, hqD, hqL⟩ := canonical_left_contact ⟨hφ0, hφ4⟩ hK hZ.1.1 hf
  -- the contacts turn the wall inequalities at the cuts into equalities
  have hR : supp K φ + supp (rightBody φ K) (π + φ) = 1 := by
    have hlo := dot_le_supp hB.2.1 hpB (π + φ)
    rw [add_comm π, dot_uvec_add_pi, hpR, add_comm φ] at hlo
    linarith [canonical_right_wall hφ0.le hK ⟨le_rfl, by linarith⟩ (t := φ)]
  have hL : supp K (π / 2 + (π / 2 - φ)) +
      supp (leftBody φ K) (3 * π / 2 + (π / 2 - φ)) = 1 := by
    have hlo := dot_le_supp hD.2.1 hqD (3 * π / 2 + (π / 2 - φ))
    rw [show 3 * π / 2 + (π / 2 - φ) = ((π / 2 - φ) + π / 2) + π by ring, dot_uvec_add_pi,
      uvec_add_pi_div_two, hqL] at hlo
    have hhi := canonical_left_wall hφ0.le hK (t := π / 2 - φ) ⟨by linarith, le_rfl⟩
    rw [show π / 2 + (π / 2 - φ) = π / 2 - φ + π / 2 by ring,
      show 3 * π / 2 + (π / 2 - φ) = ((π / 2 - φ) + π / 2) + π by ring] at hhi ⊢
    linarith
  refine ⟨hK, hB, hD, inter_subset_left, inter_subset_left,
    fun t ht => canonical_right_wall hφ0.le hK ht, hR, ?_,
    fun t ht => canonical_left_wall hφ0.le hK ht, ?_, hL⟩
  · rw [show π + π / 2 = 3 * π / 2 by ring, hK.2.2.2.1,
      opt_supp_three_pi_div_two_eq_zero hK hB inter_subset_left (opt_rightBody_A_mem hφ0.le hK)]
    norm_num
  · rw [add_zero, add_zero, hK.2.2.2.1,
      opt_supp_three_pi_div_two_eq_zero hK hD inter_subset_left (opt_leftBody_C_mem hφ0.le hK)]
    norm_num

/-- Every cap near Gerver's has its canonical triple in `T̄`. -/
theorem nearby_canonical_inWideL {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K P.cap →
      InWideL P.φ K (rightBody P.φ K) (leftBody P.φ K) := by
  have hφ := gm_φ_mem_Ioo hP hbox
  obtain ⟨c, δA, hc, hδA, hδA1, hA⟩ := core_arm_margin_near_reference
    (theorem8_1_1_gerver hP hbox) (a := P.φ) (b := π / 2 - P.φ) hφ.1 (by linarith [hφ.2])
    (by linarith [hφ.1])
  refine ⟨min δA (1 / 20), lt_min hδA (by norm_num), (min_le_left _ _).trans hδA1,
    fun K hK hclose => ?_⟩
  have hcore := hA K hK (hclose.mono (min_le_left _ _))
  have hφarm := hcore.oneSided hK (t := P.φ) ⟨le_rfl, by linarith [hφ.2]⟩
  have hbarm := hcore.oneSided hK (t := π / 2 - P.φ) ⟨by linarith [hφ.2], le_rfl⟩
  exact canonical_inWideL_of_cut_arms hbox.1 hK
    (nearby_bottomWidth hP hbox (hclose.mono (min_le_right _ _)))
    (by linarith [hφarm.2.2.1]) (by linarith [hbarm.2.1])

/-- The canonical triple of a cap, as a point of `T̄`. -/
def canonicalWideTriple {φ : ℝ} {K : Set Point}
    (h : InWideL φ K (rightBody φ K) (leftBody φ K)) : WideTriple φ :=
  ⟨(⟨K, h.1.2.1⟩, ⟨rightBody φ K, h.2.1⟩, ⟨leftBody φ K, h.2.2.1⟩), h⟩

end MovingSofaStability
