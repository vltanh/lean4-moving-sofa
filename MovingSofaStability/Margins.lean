module

public import MovingSofaUniqueness.RegularClosed
public import MovingSofaStability.Basic
public import MovingSofaStability.CapEstimate

/-!
# The margins of Gerver's sofa

The shape of a cap and the slacks of the hallway walls; the recovery of a set from an erosion and
a missing area, given uniform interior balls; interior balls of convex bodies and of a strip under
a Lipschitz roof; the slope of the envelope of the inner corner and the slack below it; caps whose
niche lies under a Lipschitz roof (`CapRoofData`) and the directed distance from an approximately
feasible set to their shape (`directed_to_reference_of_margins`). For Gerver's cap, the roof, the
outer margin, the slack below the envelope and uniform interior balls carry bounds from the cap to
the sofa (`gerver_recovery_constants`).

The sections below follow the steps of the proof.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness GerverParams

namespace MovingSofaStability

/-!
## The cap shape and the slacks of the walls

The shape of a cap `K` is `K` minus its niche. A point lies in the quadrant `Q⁻_K(t)` when both of
its slacks at the inner walls of the hallway at angle `t` are negative.
-/

/-- The shape `K \ 𝒩(K)` of a cap. -/
def capShape (K : Set Point) : Set Point := K \ niche K (π / 2)

/-- The upper support functions of `K` and `L` differ by at most `δ` on `[0, π]`. -/
def UpperSupportClose (δ : ℝ) (K L : Set Point) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) π, |supp K t - supp L t| ≤ δ

/-- The slack `p · u_t - h_K(t) + 1` of `p` at the inner wall of normal `u_t`. -/
def innerSlackU (K : Set Point) (t : ℝ) (p : Point) : ℝ := dot p (uvec t) - supp K t + 1

/-- The slack `p · v_t - h_K(t + π/2) + 1` of `p` at the inner wall of normal `v_t`. -/
def innerSlackV (K : Set Point) (t : ℝ) (p : Point) : ℝ :=
  dot p (vvec t) - supp K (t + π / 2) + 1

/-- The erosion of `S` by closed Euclidean balls of radius `r`. -/
def euclideanErosion (r : ℝ) (S : Set Point) : Set Point :=
  {p | ∀ q, euclideanDist p q ≤ r → q ∈ S}

/-- A cap is the set of points above the floor and below its upper supporting lines. -/
theorem cap_mem_iff_upper {K : Set Point} (hK : IsCap K (π / 2)) (p : Point) :
    p ∈ K ↔ 0 ≤ p.2 ∧ ∀ t ∈ Icc (0 : ℝ) π, dot p (uvec t) ≤ supp K t := by
  refine ⟨fun hp => ⟨hK.snd_nonneg hp, fun t _ => dot_le_supp hK.2.1.2.1 hp t⟩,
    fun ⟨hpy, h⟩ => (mem_iff_forall_dot_le_supp hK.2.1 p).2 fun t => ?_⟩
  by_cases hs : 0 ≤ sin t
  · obtain ⟨s, hsI, hu, -⟩ := upper_normal_representative t hs
    simpa only [supp, hu] using h s hsI
  -- below the horizontal, the support is that of an end of the floor
  have hs' := (not_le.mp hs).le
  have hy := mul_nonpos_of_nonneg_of_nonpos hpy hs'
  have h0 := h 0 ⟨le_rfl, pi_pos.le⟩
  have hπ := h π ⟨pi_pos.le, le_rfl⟩
  simp only [dot, uvec_zero, uvec_pi] at h0 hπ
  simp only [dot, uvec]
  rcases le_total 0 (cos t) with hc | hc
  · rw [cap_lower_right_support hK hs' hc]
    linarith [mul_le_mul_of_nonneg_right h0 hc]
  · rw [cap_lower_left_support hK hs' hc]
    linarith [mul_le_mul_of_nonpos_right (show -supp K π ≤ p.1 by linarith) hc]

/-- The quadrant `Q⁻_K(t)` is the set where both slacks are negative. -/
theorem mem_qMinus_iff_slacks (K : Set Point) (t : ℝ) (p : Point) :
    p ∈ qMinus K t ↔ innerSlackU K t p < 0 ∧ innerSlackV K t p < 0 := by
  rw [ms_mem_qMinus_iff, innerSlackU, innerSlackV]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The niche is the set of points above the floor with both slacks negative at an angle in
`(0, π/2)`. -/
theorem mem_niche_iff_slacks (K : Set Point) (p : Point) :
    p ∈ niche K (π / 2) ↔ 0 ≤ p.2 ∧
      ∃ t ∈ Ioo (0 : ℝ) (π / 2), innerSlackU K t p < 0 ∧ innerSlackV K t p < 0 := by
  simp only [niche, mem_inter_iff, mem_fan_iff, dot_uvec_pi_div_two, and_self,
    mem_iUnion, exists_prop, mem_qMinus_iff_slacks]

/-- At an angle `t` with inner corner `x_K(t) = x`, the slacks of the point `q` lowered by `d` are
`(q - x) · u_t - d sin t` and `(q - x) · v_t - d cos t`. -/
theorem innerSlack_down {K : Set Point} {t d : ℝ} {x : Point} (hx : innerCorner K t = x)
    (q : Point) :
    innerSlackU K t (q.1, q.2 - d) = dot (q - x) (uvec t) - d * sin t ∧
      innerSlackV K t (q.1, q.2 - d) = dot (q - x) (vvec t) - d * cos t := by
  rw [← hx, proposition2_2_2_innerCorner]
  simp only [innerSlackU, innerSlackV, dot_sub_left, dot_add_left, dot_smul_left, dot_uvec_self,
    dot_vvec_uvec, dot_uvec_vvec, dot_vvec_self]
  simp only [dot, uvec, vvec]
  constructor <;> ring

/-- The `2δ`-erosion of the shape of a cap `K₀` lies in the shape of every cap `K` whose upper
supports are `δ`-close; the coefficient two is not sharp. -/
theorem reference_erosion_subset {δ : ℝ} (hδ : 0 ≤ δ) {K₀ K : Set Point}
    (h₀ : IsCap K₀ (π / 2)) (hK : IsCap K (π / 2))
    (hclose : UpperSupportClose δ K K₀) :
    euclideanErosion (2 * δ) (capShape K₀) ⊆ capShape K := by
  intro p hp
  -- `p` lies below the upper supporting lines of `K`, since `p + δ u_t` lies in `K₀`
  have hpK : p ∈ K := by
    refine (cap_mem_iff_upper hK p).2
      ⟨h₀.snd_nonneg (hp p (by rw [euclideanDist_self]; positivity)).1, fun t ht => ?_⟩
    have hq := (hp (p + δ • uvec t) (by
      rw [euclideanDist, sub_add_cancel_left, norm2_neg, norm2_smul, norm2_uvec,
        abs_of_nonneg hδ]
      linarith)).1
    have hs := dot_le_supp h₀.2.1.2.1 hq t
    rw [dot_add_left, dot_smul_left, dot_uvec_self, mul_one] at hs
    linarith [(abs_le.mp (hclose t ht)).1]
  -- if `p` lay in the niche of `K`, then `p - δ u_t - δ v_t` would lie in the niche of `K₀`
  refine ⟨hpK, fun hn => ?_⟩
  obtain ⟨-, t, ht, hu, hv⟩ := (mem_niche_iff_slacks K p).1 hn
  have hq := hp (p - δ • uvec t - δ • vvec t) (by
    have hv1 : norm2 (vvec t) = 1 := by rw [← uvec_add_pi_div_two, norm2_uvec]
    have h := norm2_add_le (δ • uvec t) (δ • vvec t)
    rw [norm2_smul, norm2_smul, norm2_uvec, hv1, abs_of_nonneg hδ] at h
    rw [euclideanDist, show p - (p - δ • uvec t - δ • vvec t) = δ • uvec t + δ • vvec t by abel]
    linarith)
  have hU := (abs_le.mp (hclose t ⟨ht.1.le, by linarith [ht.2, pi_pos]⟩)).2
  have hV := (abs_le.mp (hclose (t + π / 2) ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩)).2
  simp only [innerSlackU, innerSlackV] at hu hv
  refine hq.2 ((mem_niche_iff_slacks K₀ _).2 ⟨h₀.snd_nonneg hq.1, t, ht, ?_, ?_⟩) <;>
    simp only [innerSlackU, innerSlackV, dot_sub_left, dot_smul_left, dot_uvec_self,
      dot_vvec_uvec, dot_uvec_vvec, dot_vvec_self] <;> linarith

/-!
## Recovery from an erosion and a missing area

The reference set has uniform interior balls; it is not assumed convex. An inscribed square bounds
the missing area from below.
-/

/-- The closed Euclidean ball of radius `r` about `p`. -/
def euclideanBall (p : Point) (r : ℝ) : Set Point := {q | euclideanDist p q ≤ r}

/-- Uniform interior balls: for every point `p` of `G` and every scale `0 < ρ ≤ r₀`, a ball of
radius `κ ρ` lies in `G ∩ B(p, ρ)`. -/
def HasInteriorBalls (G : Set Point) (κ r₀ : ℝ) : Prop :=
  ∀ p ∈ G, ∀ ρ : ℝ, 0 < ρ → ρ ≤ r₀ →
    ∃ z, euclideanBall z (κ * ρ) ⊆ G ∩ euclideanBall p ρ

/-- The Euclidean norm is at most the sum of the absolute values of the coordinates. -/
theorem norm2_le_abs_add (p : Point) : norm2 p ≤ |p.1| + |p.2| := by
  have hs := norm2_sq p
  simp only [dot] at hs
  nlinarith [norm2_nonneg p, abs_nonneg p.1, abs_nonneg p.2, sq_abs p.1, sq_abs p.2,
    mul_nonneg (abs_nonneg p.1) (abs_nonneg p.2)]

/-- The closed square of side `a` centred at `z`. -/
def centeredSquare (z : Point) (a : ℝ) : Set Point :=
  Icc (z.1 - a / 2) (z.1 + a / 2) ×ˢ Icc (z.2 - a / 2) (z.2 + a / 2)

theorem area_centeredSquare (z : Point) {a : ℝ} (ha : 0 ≤ a) :
    area (centeredSquare z a) = a ^ 2 := by
  rw [area, centeredSquare, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
    Real.volume_Icc, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal (by linarith)]
  ring

theorem centeredSquare_subset_ball (z : Point) {a : ℝ} :
    centeredSquare z a ⊆ euclideanBall z a := by
  rintro q ⟨⟨hx₁, hx₂⟩, hy₁, hy₂⟩
  have h₁ : |z.1 - q.1| ≤ a / 2 := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have h₂ : |z.2 - q.2| ≤ a / 2 := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have h := norm2_le_abs_add (z - q)
  simp only [Prod.fst_sub, Prod.snd_sub] at h
  show norm2 (z - q) ≤ a
  linarith

/-- At a fixed scale `ρ`, a missing region smaller than an inscribed square cannot remove every
point of `S` near a point of `G`. Neither `G` nor `S` is assumed convex. -/
theorem directedClose_of_missing_area {G U S : Set Point} {κ r₀ r ρ η : ℝ}
    (hκ : 0 < κ) (hρ : 0 < ρ) (hρ₀ : ρ ≤ r₀)
    (hballs : HasInteriorBalls G κ r₀)
    (herosion : euclideanErosion r G ⊆ U)
    (hr : r ≤ κ * ρ / 2)
    (hUf : volume U ≠ ⊤) (hmissing : area (U \ S) ≤ η)
    (hsmall : η < (κ * ρ / 2) ^ 2) : DirectedClose ρ G S := by
  intro p hp
  by_contra hnone
  obtain ⟨z, hz⟩ := hballs p hp ρ hρ hρ₀
  have hκρ := mul_pos hκ hρ
  -- the square of side `κ ρ / 2` centred at `z` lies in the erosion, hence in `U`, and misses `S`
  have hsq : centeredSquare z (κ * ρ / 2) ⊆ U \ S := fun q hq => by
    have hqz : euclideanDist z q ≤ κ * ρ / 2 := centeredSquare_subset_ball z hq
    refine ⟨herosion fun q' hq' => (hz ?_).1, fun hqS => hnone ⟨q, hqS, (hz ?_).2⟩⟩
    · show euclideanDist z q' ≤ κ * ρ
      linarith [euclideanDist_triangle z q q']
    · show euclideanDist z q ≤ κ * ρ
      linarith
  have harea := area_mono_of_finite hsq (volume_ne_top_of_subset sdiff_subset hUf)
  rw [area_centeredSquare z (by positivity)] at harea
  linarith

/-- If the upper supports of a cap `K` are `δ`-close to those of `K₀`, with `2δ ≤ A √ε`, and `S`
misses at most `2ε` of the shape of `K`, then every point of the shape of `K₀` lies within
`4(A + 1) √ε / κ` of `S`. No regularity of `K` is assumed. -/
theorem reference_to_sofa_recovery {K₀ K S : Set Point} {δ κ r₀ A ε : ℝ}
    (h₀ : IsCap K₀ (π / 2)) (hK : IsCap K (π / 2))
    (hδ : 0 ≤ δ) (hclose : UpperSupportClose δ K K₀)
    (hκ : 0 < κ) (hA : 0 ≤ A) (hε : 0 < ε)
    (hballs : HasInteriorBalls (capShape K₀) κ r₀)
    (hδbound : 2 * δ ≤ A * sqrt ε)
    (hscale : (4 * (A + 1) / κ) * sqrt ε ≤ r₀)
    (hUf : volume (capShape K) ≠ ⊤)
    (hmissing : area (capShape K \ S) ≤ 2 * ε) :
    DirectedClose ((4 * (A + 1) / κ) * sqrt ε) (capShape K₀) S := by
  have hs : 0 < sqrt ε := sqrt_pos.2 hε
  have he : κ * ((4 * (A + 1) / κ) * sqrt ε) / 2 = 2 * (A + 1) * sqrt ε := by
    field_simp
    ring
  refine directedClose_of_missing_area hκ (by positivity) hscale hballs
    (reference_erosion_subset hδ h₀ hK hclose) ?_ hUf hmissing ?_ <;> rw [he]
  · linarith [mul_nonneg (by linarith : 0 ≤ A + 2) hs.le]
  · rw [mul_pow, sq_sqrt hε.le]
    linarith [mul_nonneg (mul_nonneg hA hA) hε.le, mul_nonneg hA hε.le]

/-!
## Interior balls of convex bodies and unions

Shrinking one interior ball toward each point of a convex body gives uniform interior balls; a
union of finitely many pieces with uniform interior balls has them too, though it need not be
convex.
-/

/-- In a convex set containing `B(c, s)` and within distance `D` of `c`, the homothety of ratio
`ρ / (D + s)` about a point maps `B(c, s)` into the set, to a ball of radius `s ρ / (D + s)` within
distance `ρ` of the point. -/
theorem convex_interiorBalls_of_ball {C : Set Point} (hC : Convex ℝ C)
    {c : Point} {s D : ℝ} (hs : 0 < s) (hD : 0 ≤ D)
    (hball : euclideanBall c s ⊆ C)
    (hbound : ∀ p ∈ C, euclideanDist p c ≤ D) :
    HasInteriorBalls C (s / (D + s)) (D + s) := by
  intro p hp ρ hρ hρmax
  have hden : 0 < D + s := by linarith
  set μ := ρ / (D + s) with hμ_def
  have hμ : 0 < μ := div_pos hρ hden
  have hμρ : μ * (D + s) = ρ := div_mul_cancel₀ _ hden.ne'
  -- the homothety maps `c` to `z` and `B(c, s)` to `B(z, μ s)`
  set z := (1 - μ) • p + μ • c with hz
  refine ⟨z, fun q hq => ?_⟩
  replace hq : euclideanDist z q ≤ μ * s := le_of_le_of_eq hq (by rw [hμ_def]; ring)
  constructor
  · -- `q` is the image of the point `c + μ⁻¹ (q - z)` of `B(c, s)`
    have hw : c + μ⁻¹ • (q - z) ∈ C := hball (by
      show norm2 (c - (c + _)) ≤ s
      rw [sub_add_cancel_left, norm2_neg, norm2_smul, abs_of_pos (inv_pos.2 hμ),
        inv_mul_le_iff₀ hμ, ← norm2_neg, neg_sub]
      exact hq)
    convert hC hp hw (sub_nonneg.2 ((div_le_one hden).2 hρmax)) hμ.le (sub_add_cancel 1 μ)
      using 1
    rw [smul_add, smul_inv_smul₀ hμ.ne', hz]
    abel
  · have hpz : euclideanDist p z ≤ μ * D := by
      rw [euclideanDist, hz, show p - ((1 - μ) • p + μ • c) = μ • (p - c) by
        rw [smul_sub, sub_smul, one_smul]; abel, norm2_smul, abs_of_pos hμ]
      exact mul_le_mul_of_nonneg_left (hbound p hp) hμ.le
    show euclideanDist p q ≤ ρ
    linarith [euclideanDist_triangle p z q]

/-- A set with nonempty interior contains a closed Euclidean ball of positive radius: the topology
of `ℝ × ℝ` comes from the sup norm, which is at most the Euclidean norm. -/
theorem exists_euclideanBall_subset_of_interior {C : Set Point}
    (hne : (interior C).Nonempty) :
    ∃ c s, 0 < s ∧ euclideanBall c s ⊆ C := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hc)
  refine ⟨c, r / 2, by linarith, fun q hq => hball ?_⟩
  rw [Metric.mem_ball, dist_comm, dist_eq_norm]
  exact (product_norm_le_norm2 (c - q)).trans_lt
    (lt_of_le_of_lt (hq : euclideanDist c q ≤ r / 2) (by linarith))

/-- A convex body with nonempty interior has uniform interior balls. -/
theorem convexBody_hasInteriorBalls {C : Set Point} (hC : IsConvexBody C)
    (hne : (interior C).Nonempty) :
    ∃ κ r₀ : ℝ, 0 < κ ∧ 0 < r₀ ∧ HasInteriorBalls C κ r₀ := by
  obtain ⟨c, s, hs, hball⟩ := exists_euclideanBall_subset_of_interior hne
  obtain ⟨D, hD⟩ := hC.2.1.exists_bound_of_continuousOn
    (continuous_norm2.comp (continuous_id.sub continuous_const) :
      Continuous fun p : Point => euclideanDist p c).continuousOn
  have hbound : ∀ p ∈ C, euclideanDist p c ≤ D := fun p hp => (Real.le_norm_self _).trans (hD p hp)
  have hD0 : 0 ≤ D := (euclideanDist_nonneg c c).trans
    (hbound c (hball (by simp only [euclideanBall, mem_ofPred_eq, euclideanDist_self, hs.le])))
  exact ⟨s / (D + s), D + s, by positivity, by positivity,
    convex_interiorBalls_of_ball hC.2.2 hs hD0 hball hbound⟩

/-- A set containing a nondegenerate box has nonempty interior. -/
theorem interior_nonempty_of_box {C : Set Point} {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hbox : Icc a b ×ˢ Icc c d ⊆ C) :
    (interior C).Nonempty := by
  refine ⟨((a + b) / 2, (c + d) / 2), interior_mono hbox ?_⟩
  rw [interior_prod_eq, interior_Icc, interior_Icc]
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- Interior balls persist when the constants decrease. -/
theorem HasInteriorBalls.mono_constants {G : Set Point} {κ r₀ κ' r₀' : ℝ}
    (h : HasInteriorBalls G κ r₀) (hκ : κ' ≤ κ) (hr : r₀' ≤ r₀) :
    HasInteriorBalls G κ' r₀' := by
  intro p hp ρ hρ hρmax
  obtain ⟨z, hz⟩ := h p hp ρ hρ (hρmax.trans hr)
  exact ⟨z, fun q hq => hz (hq.trans (mul_le_mul_of_nonneg_right hκ hρ.le))⟩

/-- Interior balls of two sets give interior balls of their union, with the smaller constants. -/
theorem exists_interiorBalls_union {G H : Set Point}
    (hG : ∃ κ r₀ : ℝ, 0 < κ ∧ 0 < r₀ ∧ HasInteriorBalls G κ r₀)
    (hH : ∃ κ r₀ : ℝ, 0 < κ ∧ 0 < r₀ ∧ HasInteriorBalls H κ r₀) :
    ∃ κ r₀ : ℝ, 0 < κ ∧ 0 < r₀ ∧ HasInteriorBalls (G ∪ H) κ r₀ := by
  obtain ⟨κG, rG, hκG, hrG, hG⟩ := hG
  obtain ⟨κH, rH, hκH, hrH, hH⟩ := hH
  refine ⟨min κG κH, min rG rH, lt_min hκG hκH, lt_min hrG hrH, ?_⟩
  rintro p (hp | hp) ρ hρ hρmax
  · obtain ⟨z, hz⟩ := hG.mono_constants (min_le_left _ _) (min_le_left _ _) p hp ρ hρ hρmax
    exact ⟨z, hz.trans (inter_subset_inter_left _ subset_union_left)⟩
  · obtain ⟨z, hz⟩ := hH.mono_constants (min_le_right _ _) (min_le_right _ _) p hp ρ hρ hρmax
    exact ⟨z, hz.trans (inter_subset_inter_left _ subset_union_right)⟩

/-!
## Interior balls under a Lipschitz roof

The strip between a Lipschitz roof and the height one has uniform interior balls when the roof
stays below a height `H < 1`; the Lipschitz bound and the gap below the height one are hypotheses.
-/

/-- The strip between the graph of `γ` over `[a, b]` and the height one. -/
def roofStrip (a b : ℝ) (γ : ℝ → ℝ) : Set Point :=
  {p | p.1 ∈ Icc a b ∧ γ p.1 ≤ p.2 ∧ p.2 ≤ 1}

/-- Within distance `ρ` of a low point of the strip, a ball of radius `w = ρ / (4(L + 2))` lies in
the strip: its centre is the point moved by `2w` toward the farther end of `[a, b]` and raised by
`(3L + 2)w`. -/
theorem roofStrip_low_ball {a b H L : ℝ} {γ : ℝ → ℝ}
    (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |γ x - γ y| ≤ L * |x - y|)
    {p : Point} (hp : p ∈ roofStrip a b γ) (hpy : p.2 ≤ (1 + H) / 2)
    {ρ : ℝ} (hρ : 0 < ρ) (hρwidth : ρ ≤ b - a) (hρheight : ρ ≤ (1 - H) / 2) :
    ∃ z, euclideanBall z (1 / (4 * (L + 2)) * ρ) ⊆ roofStrip a b γ ∩ euclideanBall p ρ := by
  obtain ⟨hpx, hpγ, -⟩ := hp
  set w := 1 / (4 * (L + 2)) * ρ with hw_def
  have hw : 0 < w := by positivity
  have hwρ : 4 * (L + 2) * w = ρ := by rw [hw_def]; field_simp
  have hLw := mul_nonneg hL hw.le
  obtain ⟨x, hx, hxa, hxb⟩ : ∃ x, |p.1 - x| = 2 * w ∧ a + w ≤ x ∧ x + w ≤ b := by
    rcases le_total p.1 ((a + b) / 2) with hmid | hmid
    · refine ⟨p.1 + 2 * w, ?_, by linarith [hpx.1], by linarith⟩
      rw [sub_add_cancel_left, abs_neg, abs_of_pos (by positivity)]
    · refine ⟨p.1 - 2 * w, ?_, by linarith, by linarith [hpx.2]⟩
      rw [sub_sub_cancel, abs_of_pos (by positivity)]
  refine ⟨(x, p.2 + (3 * L + 2) * w), fun q hq => ?_⟩
  have hq' : euclideanDist (x, p.2 + (3 * L + 2) * w) q ≤ w := hq
  have hdx := abs_le.1 ((abs_fst_le_norm2 _).trans hq')
  have hdy := abs_le.1 ((abs_snd_le_norm2 _).trans hq')
  have hx' := abs_le.1 hx.le
  simp only [Prod.fst_sub, Prod.snd_sub] at hdx hdy
  have hqx : q.1 ∈ Icc a b := ⟨by linarith, by linarith⟩
  -- the roof rises by at most `3Lw` over the ball
  have hγ : γ q.1 ≤ γ p.1 + L * (3 * w) := by
    have h3 : |q.1 - p.1| ≤ 3 * w := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    linarith [le_of_abs_le (hLip q.1 hqx p.1 hpx), mul_le_mul_of_nonneg_left h3 hL]
  have hpz : euclideanDist p (x, p.2 + (3 * L + 2) * w) ≤ 2 * w + (3 * L + 2) * w := by
    refine (norm2_le_abs_add _).trans_eq ?_
    simp only [Prod.fst_sub, Prod.snd_sub, sub_add_cancel_left, abs_neg, hx]
    rw [abs_of_nonneg (by positivity)]
  refine ⟨⟨hqx, by linarith, by linarith⟩, ?_⟩
  show euclideanDist p q ≤ ρ
  linarith [euclideanDist_triangle p (x, p.2 + (3 * L + 2) * w) q]

/-- The strip under a Lipschitz roof of height at most `H < 1` has uniform interior balls: the low
points use `roofStrip_low_ball`, and the high points lie in the rectangle `[a, b] × [H, 1]`. -/
theorem roofStrip_hasInteriorBalls {a b H L : ℝ} {γ : ℝ → ℝ}
    (hab : a < b) (hH : H < 1) (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |γ x - γ y| ≤ L * |x - y|)
    (hheight : ∀ x ∈ Icc a b, γ x ≤ H) :
    ∃ κ r₀ : ℝ, 0 < κ ∧ 0 < r₀ ∧ HasInteriorBalls (roofStrip a b γ) κ r₀ := by
  obtain ⟨κR, rR, hκR, hrR, hballsR⟩ := convexBody_hasInteriorBalls (C := Icc a b ×ˢ Icc H 1)
    ⟨⟨(a, H), ⟨le_rfl, hab.le⟩, le_rfl, hH.le⟩, isCompact_Icc.prod isCompact_Icc,
      (convex_Icc a b).prod (convex_Icc H 1)⟩ (interior_nonempty_of_box hab hH subset_rfl)
  refine ⟨min κR (1 / (4 * (L + 2))), min rR (min (b - a) ((1 - H) / 2)),
    lt_min hκR (by positivity), lt_min hrR (lt_min (sub_pos.2 hab) (by linarith)), ?_⟩
  intro p hp ρ hρ hρmax
  by_cases hlow : p.2 ≤ (1 + H) / 2
  · obtain ⟨z, hz⟩ := roofStrip_low_ball hL hLip hp hlow hρ
      (hρmax.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (hρmax.trans ((min_le_right _ _).trans (min_le_right _ _)))
    exact ⟨z, fun q hq => hz (hq.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hρ.le))⟩
  · obtain ⟨z, hz⟩ := hballsR.mono_constants (min_le_left _ _) (min_le_left _ _) p
      ⟨hp.1, by linarith [not_le.mp hlow], hp.2.2⟩ ρ hρ hρmax
    exact ⟨z, hz.trans (inter_subset_inter_left _
      fun q hq => ⟨hq.1, (hheight _ hq.1).trans hq.2.1, hq.2.2⟩)⟩

/-!
## Lipschitz roofs from monotone arcs

A bound on the slopes of the velocities off a finite set bounds the slopes of the chords; arcs
with a common point on a separating vertical line join, and a set over `[a, b]` with a slope bound
is the graph of a Lipschitz function.
-/

/-- Every chord of `Γ` has slope at most `L` in absolute value. -/
def VerticalSlopeBound (Γ : Set Point) (L : ℝ) : Prop :=
  ∀ p ∈ Γ, ∀ q ∈ Γ, |p.2 - q.2| ≤ L * |p.1 - q.1|

/-- If `0 ≤ X'` and `|Y'| ≤ L X'` off a finite set, then every chord of `(X, Y)` has slope at most
`L`: `L X + Y` and `L X - Y` are monotone. -/
theorem scalar_graph_slope {a b L : ℝ} {X Y dX dY : ℝ → ℝ} {F : Set ℝ}
    (hF : F.Finite) (hX : ContinuousOn X (Icc a b)) (hY : ContinuousOn Y (Icc a b))
    (hdX : ∀ t ∈ Ioo a b, t ∉ F → HasDerivAt X (dX t) t)
    (hdY : ∀ t ∈ Ioo a b, t ∉ F → HasDerivAt Y (dY t) t)
    (hcone : ∀ t ∈ Ioo a b, t ∉ F → 0 ≤ dX t ∧ |dY t| ≤ L * dX t) :
    ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |Y u - Y v| ≤ L * |X u - X v| := by
  have hmono := env_monotoneOn hF hX hdX fun t ht he => (hcone t ht he).1
  have hplus := env_monotoneOn hF (hX.const_mul L |>.add hY)
    (fun t ht he => ((hdX t ht he).const_mul L).add (hdY t ht he))
    fun t ht he => by linarith [(abs_le.mp (hcone t ht he).2).1]
  have hminus := env_monotoneOn hF (hX.const_mul L |>.sub hY)
    (fun t ht he => ((hdX t ht he).const_mul L).sub (hdY t ht he))
    fun t ht he => by linarith [(abs_le.mp (hcone t ht he).2).2]
  have ordered : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v → |Y u - Y v| ≤ L * |X u - X v| := by
    intro u hu v hv huv
    have hp : L * X u + Y u ≤ L * X v + Y v := hplus hu hv huv
    have hn : L * X u - Y u ≤ L * X v - Y v := hminus hu hv huv
    rw [abs_of_nonpos (sub_nonpos.mpr (hmono hu hv huv)), abs_le]
    constructor <;> linarith
  intro u hu v hv
  rcases le_total u v with huv | hvu
  · exact ordered u hu v hv huv
  · simpa only [abs_sub_comm] using ordered v hv u hu hvu

/-- A curve with velocity `k(t) w(t)` off a finite set, where `k ≥ 0`, `w₁ ≥ 1/2` and `|w₂| ≤ 1`,
has slope at most two. -/
theorem slope_two_of_velocity {a b : ℝ} {F : Set ℝ} {f w : ℝ → Point} {k : ℝ → ℝ}
    (hF : F.Finite) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, t ∉ F → HasDerivAt f (k t • w t) t)
    (hk : ∀ t ∈ Ioo a b, 0 ≤ k t) (hw : ∀ t ∈ Ioo a b, 1 / 2 ≤ (w t).1 ∧ |(w t).2| ≤ 1) :
    VerticalSlopeBound (f '' Icc a b) 2 := by
  have hs := scalar_graph_slope (L := 2) hF hf.fst hf.snd
    (dX := fun t => k t * (w t).1) (dY := fun t => k t * (w t).2)
    (fun t ht he => by
      simpa only [Prod.smul_fst, smul_eq_mul] using hasDerivAt_fst (hd t ht he))
    (fun t ht he => by
      simpa only [Prod.smul_snd, smul_eq_mul] using hasDerivAt_snd (hd t ht he))
    fun t ht _ => by
      have hm := mul_le_mul_of_nonneg_left
        (show |(w t).2| ≤ 2 * (w t).1 by linarith [hw t ht]) (hk t ht)
      rw [abs_mul, abs_of_nonneg (hk t ht)]
      exact ⟨mul_nonneg (hk t ht) (by linarith [hw t ht]), by linarith⟩
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  exact hs u hu v hv

theorem VerticalSlopeBound.mono_constant {Γ : Set Point} {L C : ℝ}
    (h : VerticalSlopeBound Γ L) (hLC : L ≤ C) : VerticalSlopeBound Γ C :=
  fun p hp q hq => (h p hp q hq).trans (mul_le_mul_of_nonneg_right hLC (abs_nonneg _))

/-- Two sets with slope bound `L` and a common point `z`, the first left and the second right of
the vertical line through `z`, have a union with slope bound `L`: a chord across the line splits at
`z`. -/
theorem verticalSlopeBound_join {Γ₁ Γ₂ : Set Point} {z : Point} {L : ℝ}
    (h₁ : VerticalSlopeBound Γ₁ L) (h₂ : VerticalSlopeBound Γ₂ L)
    (hz₁ : z ∈ Γ₁) (hz₂ : z ∈ Γ₂)
    (hleft : ∀ p ∈ Γ₁, p.1 ≤ z.1) (hright : ∀ p ∈ Γ₂, z.1 ≤ p.1) :
    VerticalSlopeBound (Γ₁ ∪ Γ₂) L := by
  have cross : ∀ p ∈ Γ₁, ∀ q ∈ Γ₂, |p.2 - q.2| ≤ L * |p.1 - q.1| := by
    intro p hp q hq
    have hA := h₁ p hp z hz₁
    have hB := h₂ z hz₂ q hq
    rw [abs_of_nonpos (sub_nonpos.2 (hleft p hp))] at hA
    rw [abs_of_nonpos (sub_nonpos.2 (hright q hq))] at hB
    rw [abs_of_nonpos (sub_nonpos.2 ((hleft p hp).trans (hright q hq)))]
    linarith [abs_sub_le p.2 z.2 q.2]
  rintro p (hp | hp) q (hq | hq)
  · exact h₁ p hp q hq
  · exact cross p hp q hq
  · simpa only [abs_sub_comm] using cross q hq p hp
  · exact h₂ p hp q hq

/-- A set with a slope bound has at most one point over each abscissa. -/
theorem eq_of_same_abscissa {Γ : Set Point} {L : ℝ} (h : VerticalSlopeBound Γ L)
    {p q : Point} (hp : p ∈ Γ) (hq : q ∈ Γ) (he : p.1 = q.1) : p = q := by
  have hh := h p hp q hq
  rw [he, sub_self, abs_zero, mul_zero, abs_nonpos_iff, sub_eq_zero] at hh
  exact Prod.ext he hh

/-- A set over `[a, b]` with slope bound `L` that meets every vertical line over `[a, b]` is the
graph of an `L`-Lipschitz function. -/
theorem exists_roof_function {Γ : Set Point} {a b L : ℝ}
    (hrange : ∀ p ∈ Γ, p.1 ∈ Icc a b)
    (hcover : ∀ x ∈ Icc a b, ∃ p ∈ Γ, p.1 = x)
    (hLip : VerticalSlopeBound Γ L) :
    ∃ γ : ℝ → ℝ,
      (∀ p : Point, p ∈ Γ ↔ p.1 ∈ Icc a b ∧ p.2 = γ p.1) ∧
      (∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |γ x - γ y| ≤ L * |x - y|) := by
  classical
  let γ := fun x : ℝ => if hx : x ∈ Icc a b then (hcover x hx).choose.2 else 0
  have graph_mem : ∀ x ∈ Icc a b, (x, γ x) ∈ Γ := by
    intro x hx
    obtain ⟨hp, hpx⟩ := (hcover x hx).choose_spec
    convert hp using 1
    exact Prod.ext hpx.symm (by simp only [γ, hx, ↓reduceDIte])
  refine ⟨γ, fun p => ⟨fun hp => ?_, fun ⟨hx, hy⟩ => ?_⟩,
    fun x hx y hy => hLip _ (graph_mem x hx) _ (graph_mem y hy)⟩
  · have hx := hrange p hp
    exact ⟨hx, congrArg Prod.snd (eq_of_same_abscissa hLip hp (graph_mem p.1 hx) rfl)⟩
  · convert graph_mem p.1 hx using 1
    exact Prod.ext rfl hy

/-!
## The slope of the envelope and the slack below it

Under `EnvHyp`, the tails `D` and `B` of the envelope have slope at most two, since their angles
stay within a quarter turn of the floor; on the compact middle arc the horizontal speed of the path
is bounded away from zero; the three bounds join at the matching points `x(t₄)` and `x(t₁)`. Below
the envelope, the slacks of the walls are uniformly negative: at a point of a tail the inactive
wall has slack `α ≤ -τ` or `-β ≤ -τ`, also at the floor, and the active walls have vertical
coefficients bounded away from zero.
-/

section Envelope

variable {t₁ t₂ t₃ t₄ sA sC : ℝ} {x : ℝ → Point} {α β ρA ρC : ℝ → ℝ}
  (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC)
include h

theorem envelope_left_slope (ht₂ : t₂ < π / 4) :
    VerticalSlopeBound (envD x β '' Icc 0 t₂) 2 := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  refine slope_two_of_velocity (k := fun t => 1 - ρC t) (w := uvec) (env_bp_finite t₁ t₂ t₃ t₄)
    ((env_D_cont h).mono (Icc_subset_Icc le_rfl (by linarith)))
    (fun t ht he => h.D_deriv t ⟨ht.1, by linarith [ht.2]⟩ he)
    (fun t ht => by linarith [h.ρC_lt t ⟨ht.1.le, ht.2.le⟩]) fun t ht => ?_
  rw [uvec_fst, uvec_snd]
  exact ⟨cos_ge_half_of_small ⟨h1.trans h12, ht₂⟩ ⟨ht.1.le, ht.2.le⟩, abs_sin_le_one t⟩

theorem envelope_right_slope (ht₃ : π / 4 < t₃) :
    VerticalSlopeBound (envB x α '' Icc t₃ (π / 2)) 2 := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  refine slope_two_of_velocity (k := fun t => 1 - ρA t) (w := fun t => -vvec t)
    (env_bp_finite t₁ t₂ t₃ t₄) ((env_B_cont h).mono (Icc_subset_Icc (by linarith) le_rfl))
    (fun t ht he => by
      convert h.B_deriv t ⟨by linarith [ht.1], ht.2⟩ he using 1
      rw [smul_neg, ← neg_smul, neg_sub])
    (fun t ht => by linarith [h.ρA_lt t ⟨ht.1.le, ht.2.le⟩]) fun t ht => ?_
  have hsin := cos_ge_half_of_small (φ := π / 2 - t₃) (t := π / 2 - t)
    ⟨by linarith, by linarith⟩ ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rw [cos_pi_div_two_sub] at hsin
  rw [Prod.fst_neg, Prod.snd_neg, vvec_fst, vvec_snd, neg_neg, abs_neg]
  exact ⟨hsin, abs_cos_le_one t⟩

/-- The middle arc has a finite slope bound: its horizontal speed is bounded away from zero. -/
theorem envelope_core_slope :
    ∃ L : ℝ, 0 ≤ L ∧ VerticalSlopeBound (x '' Icc t₁ t₄) L := by
  obtain ⟨h1, -, -, -, h4⟩ := h.ht
  have hsub : Icc t₁ t₄ ⊆ Icc 0 (π / 2) := Icc_subset_Icc h1.le h4.le
  have hα := h.α_cont.mono hsub
  have hβ := h.β_cont.mono hsub
  have hpos : ∀ t ∈ Icc t₁ t₄, 0 < -α t * cos t + β t * sin t := fun t ht => by
    have hti : t ∈ Ioo 0 (π / 2) := ⟨h1.trans_le ht.1, ht.2.trans_lt h4⟩
    exact add_pos (mul_pos (neg_pos.2 (h.α_neg t hti))
      (cos_pos_of_mem_Ioo ⟨by linarith [hti.1, pi_pos], hti.2⟩))
      (mul_pos (h.β_pos t hti) (sin_pos_of_pos_of_lt_pi hti.1 (by linarith [hti.2, pi_pos])))
  obtain ⟨m, hm, hmle⟩ := isCompact_Icc.exists_forall_le' (by fun_prop) hpos
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (by fun_prop : ContinuousOn (fun t => α t * sin t + β t * cos t) (Icc t₁ t₄))
  have hL : 0 ≤ (|B| + 1) / m := by positivity
  have hc := h.x_cont.mono hsub
  have hs := scalar_graph_slope (L := (|B| + 1) / m) finite_empty hc.fst.neg hc.snd
    (dX := fun t => -α t * cos t + β t * sin t) (dY := fun t => α t * sin t + β t * cos t)
    (fun t ht _ => by
      convert (hasDerivAt_fst (h.x_deriv t ⟨by linarith [ht.1], by linarith [ht.2]⟩)).neg
        using 1
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, uvec_fst, vvec_fst]
      ring)
    (fun t ht _ => by
      simpa only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, uvec_snd, vvec_snd] using
        hasDerivAt_snd (h.x_deriv t ⟨by linarith [ht.1], by linarith [ht.2]⟩))
    fun t ht _ => ⟨(hpos t ⟨ht.1.le, ht.2.le⟩).le, by
      have hb : |α t * sin t + β t * cos t| ≤ B := hB t ⟨ht.1.le, ht.2.le⟩
      calc _ ≤ |B| + 1 := by linarith [le_abs_self B]
        _ = (|B| + 1) / m * m := (div_mul_cancel₀ _ hm.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (hmle t ⟨ht.1.le, ht.2.le⟩) hL⟩
  refine ⟨_, hL, ?_⟩
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  simpa only [Pi.neg_apply, neg_sub_neg, abs_sub_comm] using hs u hu v hv

/-- The envelope has a finite slope bound. -/
theorem envelope_slope_bound (ht₂ : t₂ < π / 4) (ht₃ : π / 4 < t₃) :
    ∃ L : ℝ, 0 ≤ L ∧ VerticalSlopeBound (envCurve t₁ t₂ t₃ t₄ x α β) L := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  obtain ⟨L₀, hL₀, hcore⟩ := envelope_core_slope h
  have hxanti := (env_x₁_strictAnti h).antitoneOn
  -- `D` lies left of `x(t₄)`, the middle arc between `x(t₄)` and `x(t₁)`, and `B` right of `x(t₁)`
  have hdmax : ∀ p ∈ envD x β '' Icc 0 t₂, p.1 ≤ (x t₄).1 := by
    rintro _ ⟨t, ht, rfl⟩
    simpa only [h.D_t₂] using (env_D₁_strictMono h).monotoneOn ht ⟨by linarith, le_rfl⟩ ht.2
  have hDC := verticalSlopeBound_join
    ((envelope_left_slope h ht₂).mono_constant (le_max_left 2 L₀))
    (hcore.mono_constant (le_max_right 2 L₀)) ⟨t₂, ⟨by linarith, le_rfl⟩, h.D_t₂⟩
    ⟨t₄, ⟨by linarith, le_rfl⟩, rfl⟩ hdmax
    (by rintro _ ⟨t, ht, rfl⟩; exact hxanti ht ⟨by linarith, le_rfl⟩ ht.2)
  have hj := verticalSlopeBound_join hDC
    ((envelope_right_slope h ht₃).mono_constant (le_max_left 2 L₀))
    (Or.inr ⟨t₁, ⟨le_rfl, by linarith⟩, rfl⟩) ⟨t₃, ⟨le_rfl, by linarith⟩, h.B_t₃⟩
    (by
      rintro _ (hp | ⟨t, ht, rfl⟩)
      · exact (hdmax _ hp).trans (envelope_endpoint_order h).2.1.le
      · exact hxanti ⟨le_rfl, by linarith⟩ ht ht.1)
    (by
      rintro _ ⟨t, ht, rfl⟩
      simpa only [h.B_t₃] using (env_B₁_strictMono h).monotoneOn ⟨le_rfl, by linarith⟩ ht ht.1)
  refine ⟨max 2 L₀, le_max_of_le_left zero_le_two, ?_⟩
  rwa [union_comm, union_comm (envD x β '' _), ← union_assoc] at hj

/-- The tails start and end with nonzero speed: `β(0) > 0` and `α(π/2) < 0`, because the abscissa of
the path decreases on `[0, π/2]`. -/
theorem envelope_endpoint_speeds : 0 < β 0 ∧ α (π / 2) < 0 := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  obtain ⟨ho1, ho2, ho3⟩ := envelope_endpoint_order h
  have hanti : StrictAntiOn (fun t => (x t).1) (Icc 0 (π / 2)) := by
    refine env_strictAntiOn (S := ∅) finite_empty h.x_cont.fst
      (fun t ht _ => hasDerivAt_fst (h.x_deriv t ht)) fun t ht _ => ?_
    simp only [Prod.fst_add, Prod.smul_fst, uvec_fst, vvec_fst, smul_eq_mul]
    linarith [mul_neg_of_neg_of_pos (h.α_neg t ht)
      (cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩),
      mul_pos (h.β_pos t ht) (sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos]))]
  have hx1 : (x t₁).1 < (x 0).1 := hanti ⟨le_rfl, by positivity⟩ ⟨h1.le, by linarith⟩ h1
  have hx4 : (x (π / 2)).1 < (x t₄).1 := hanti ⟨by linarith, h4.le⟩ ⟨by positivity, le_rfl⟩ h4
  simp only [envD, envB, Prod.fst_sub, Prod.fst_add, Prod.smul_fst, smul_eq_mul, uvec_fst,
    vvec_fst, cos_zero, sin_pi_div_two, mul_one, mul_neg] at ho1 ho3
  constructor <;> linarith

/-- Lowering a point of the envelope by `d` makes both slacks at most `-min (c d) τ` at some angle:
on the path both walls are active, on a tail one wall is active and the other inactive. -/
theorem envelope_downward_slack {K : Set Point}
    (hpath : ∀ t ∈ Icc (0 : ℝ) (π / 2), innerCorner K t = x t) :
    ∃ c τ : ℝ, 0 < c ∧ 0 < τ ∧
      ∀ q ∈ envCurve t₁ t₂ t₃ t₄ x α β, ∀ d : ℝ, 0 < d → 0 ≤ q.2 - d →
        ∃ t ∈ Ioo (0 : ℝ) (π / 2),
          innerSlackU K t (q.1, q.2 - d) ≤ -min (c * d) τ ∧
          innerSlackV K t (q.1, q.2 - d) ≤ -min (c * d) τ := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  obtain ⟨hβ0, hαv⟩ := envelope_endpoint_speeds h
  -- the inactive slacks `-β` on `[0, t₂]` and `α` on `[t₃, π/2]` are at most `-τ`
  obtain ⟨τD, hτD, hD⟩ := isCompact_Icc.exists_forall_le' (s := Icc 0 t₂)
    (h.β_cont.mono (Icc_subset_Icc le_rfl (by linarith))) fun t ht => by
      rcases ht.1.eq_or_lt with rfl | hp
      exacts [hβ0, h.β_pos t ⟨hp, by linarith [ht.2]⟩]
  obtain ⟨τB, hτB, hB⟩ := isCompact_Icc.exists_forall_le' (s := Icc t₃ (π / 2))
    (f := fun t => -α t) (h.α_cont.mono (Icc_subset_Icc (by linarith) le_rfl)).neg fun t ht => by
      rcases ht.2.eq_or_lt with rfl | hp
      exacts [neg_pos.2 hαv, neg_pos.2 (h.α_neg t ⟨by linarith [ht.1], hp⟩)]
  -- the vertical coefficients `cos t` on `[0, t₄]` and `sin t` on `[t₁, π/2]` are at least `c`
  obtain ⟨cD, hcD, hcos⟩ := isCompact_Icc.exists_forall_le' (s := Icc 0 t₄)
    continuous_cos.continuousOn fun t ht =>
      cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
  obtain ⟨cB, hcB, hsin⟩ := isCompact_Icc.exists_forall_le' (s := Icc t₁ (π / 2))
    continuous_sin.continuousOn fun t ht =>
      sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, pi_pos])
  refine ⟨min cD cB, min τD τB, lt_min hcD hcB, lt_min hτD hτB, ?_⟩
  intro q hq d hd hfloor
  -- lowering by `d` takes an active slack `≤ 0` of coefficient `≥ c` below `-c d`, and keeps an
  -- inactive slack below `-τ`
  have active : ∀ {s k : ℝ}, s ≤ 0 → min cD cB ≤ k →
      s - d * k ≤ -min (min cD cB * d) (min τD τB) := fun hs hk => by
    linarith [min_le_left (min cD cB * d) (min τD τB), mul_le_mul_of_nonneg_left hk hd.le]
  have inactive : ∀ {s k : ℝ}, s ≤ -min τD τB → 0 ≤ k →
      s - d * k ≤ -min (min cD cB * d) (min τD τB) := fun hs hk => by
    linarith [min_le_right (min cD cB * d) (min τD τB), mul_nonneg hd.le hk]
  rcases hq with (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩
  · -- `B(t)`, `t ∈ [t₃, π/2)`: the wall of normal `u_t` is active
    have hti : t ∈ Ioo (0 : ℝ) (π / 2) :=
      ⟨by linarith [ht.1], ht.2.lt_of_ne (by rintro rfl; rw [h.B_end] at hfloor; linarith)⟩
    obtain ⟨hU, hV⟩ := innerSlack_down (d := d) (hpath t ⟨hti.1.le, hti.2.le⟩) (envB x α t)
    refine ⟨t, hti, ?_, ?_⟩
    · rw [hU, env_dot_B_self]
      exact active le_rfl ((min_le_right _ _).trans (hsin t ⟨by linarith [ht.1], ht.2⟩))
    · rw [hV, show dot (envB x α t - x t) (vvec t) = α t by simp [envB, dot_smul_left]]
      exact inactive (by linarith [min_le_right τD τB, hB t ht])
        (cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, pi_pos], ht.2⟩)
  · -- `x(t)`, `t ∈ [t₁, t₄]`: both walls are active
    have hti : t ∈ Ioo (0 : ℝ) (π / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    obtain ⟨hU, hV⟩ := innerSlack_down (d := d) (hpath t ⟨hti.1.le, hti.2.le⟩) (x t)
    refine ⟨t, hti, ?_, ?_⟩
    · rw [hU, sub_self, dot_zero_left]
      exact active le_rfl ((min_le_right _ _).trans (hsin t ⟨ht.1, by linarith [ht.2]⟩))
    · rw [hV, sub_self, dot_zero_left]
      exact active le_rfl ((min_le_left _ _).trans (hcos t ⟨by linarith [ht.1], ht.2⟩))
  · -- `D(t)`, `t ∈ (0, t₂]`: the wall of normal `v_t` is active
    have hti : t ∈ Ioo (0 : ℝ) (π / 2) :=
      ⟨ht.1.lt_of_ne (by rintro rfl; rw [h.D_end] at hfloor; linarith), by linarith [ht.2]⟩
    obtain ⟨hU, hV⟩ := innerSlack_down (d := d) (hpath t ⟨hti.1.le, hti.2.le⟩) (envD x β t)
    refine ⟨t, hti, ?_, ?_⟩
    · rw [hU, show dot (envD x β t - x t) (uvec t) = -β t by
        simp [envD, dot_neg_left, dot_smul_left]]
      exact inactive (by linarith [min_le_left τD τB, hD t ht])
        (sin_nonneg_of_nonneg_of_le_pi hti.1.le (by linarith [hti.2, pi_pos]))
    · rw [hV, env_dot_D_self]
      exact active le_rfl ((min_le_left _ _).trans (hcos t ⟨ht.1, by linarith [ht.2]⟩))

end Envelope

/-!
## Caps with a Lipschitz niche roof

`CapRoofData` records the geometry of the boundary; it assumes no stability estimate. The shape is
the union of two convex wings and a strip under the roof, so it has uniform interior balls; the
niche keeps a positive distance from the upper supporting lines.
-/

/-- A cap whose niche is the region strictly under a Lipschitz roof `γ ≥ 0` over `[a, b]`, of
height at most `H < 1` and vanishing at `a` and `b`, with `[a, b] × [0, 1]` inside the cap and
`[a, b]` strictly inside its floor. -/
structure CapRoofData (K : Set Point) (a b H L : ℝ) (γ : ℝ → ℝ) : Prop where
  cap : IsCap K (π / 2)
  order : a < b
  left_wing : -supp K π < a
  right_wing : b < supp K 0
  height : H < 1
  slope_nonneg : 0 ≤ L
  roof_nonneg : ∀ x ∈ Icc a b, 0 ≤ γ x
  roof_le : ∀ x ∈ Icc a b, γ x ≤ H
  roof_lipschitz : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |γ x - γ y| ≤ L * |x - y|
  left_zero : γ a = 0
  right_zero : γ b = 0
  rectangle : Icc a b ×ˢ Icc (0 : ℝ) 1 ⊆ K
  niche_eq : niche K (π / 2) = {p | p.1 ∈ Icc a b ∧ 0 ≤ p.2 ∧ p.2 < γ p.1}

/-- A cap contains the rectangle below each of its horizontal chords. -/
theorem cap_horizontal_rectangle {K : Set Point} (hK : IsCap K (π / 2))
    {a b h : ℝ} (hab : a < b) (ha : (a, h) ∈ K) (hb : (b, h) ∈ K) :
    Icc a b ×ˢ Icc (0 : ℝ) h ⊆ K := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  have hseg : (x, h) ∈ segment ℝ (a, h) (b, h) := by
    rw [← Prod.image_mk_segment_left, segment_eq_Icc hab.le]
    exact ⟨x, hx, rfl⟩
  exact opt_cap_down hK (hK.2.1.2.2.segment_subset ha hb hseg) hy.1 hy.2

/-- The part of `K` left of the vertical line through `a`. -/
def leftWing (K : Set Point) (a : ℝ) : Set Point := K ∩ {p | p.1 ≤ a}

/-- The part of `K` right of the vertical line through `b`. -/
def rightWing (K : Set Point) (b : ℝ) : Set Point := K ∩ {p | b ≤ p.1}

/-- The two wings are convex bodies with nonempty interior: each contains a box below the midpoint
of `(a, 1)` or `(b, 1)` and an end of the floor. -/
theorem CapRoofData.wings {K : Set Point} {a b H L : ℝ} {γ : ℝ → ℝ}
    (h : CapRoofData K a b H L γ) :
    (IsConvexBody (leftWing K a) ∧ (interior (leftWing K a)).Nonempty) ∧
      (IsConvexBody (rightWing K b) ∧ (interior (rightWing K b)).Nonempty) := by
  have hK := h.cap.2.1.2
  have hl := h.left_wing
  have hr := h.right_wing
  have hleft : (a, 1) ∈ K := h.rectangle ⟨⟨le_rfl, h.order.le⟩, zero_le_one, le_rfl⟩
  have hright : (b, 1) ∈ K := h.rectangle ⟨⟨h.order.le, le_rfl⟩, zero_le_one, le_rfl⟩
  have hmidL : ((-supp K π + a) / 2, (1 / 2 : ℝ)) ∈ K := by
    convert hK.2 (opt_cap_C_mem h.cap) hleft (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) using 1
    ext <;> simp
    ring
  have hmidR : ((b + supp K 0) / 2, (1 / 2 : ℝ)) ∈ K := by
    convert hK.2 hright (opt_cap_A_mem h.cap) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) using 1
    ext <;> simp
    ring
  have hLi := interior_nonempty_of_box (C := leftWing K a) (by linarith : (-supp K π + a) / 2 < a)
    (by norm_num : (0 : ℝ) < 1 / 2) fun p hp => ⟨cap_horizontal_rectangle h.cap
      (by linarith) hmidL (opt_cap_down h.cap hleft (by norm_num) (by norm_num)) hp, hp.1.2⟩
  have hRi := interior_nonempty_of_box (C := rightWing K b) (by linarith : b < (b + supp K 0) / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) fun p hp => ⟨cap_horizontal_rectangle h.cap
      (by linarith) (opt_cap_down h.cap hright (by norm_num) (by norm_num)) hmidR hp, hp.1.1⟩
  refine ⟨⟨⟨hLi.mono interior_subset, hK.1.inter_right
      (isClosed_le continuous_fst continuous_const), ?_⟩, hLi⟩,
    ⟨⟨hRi.mono interior_subset, hK.1.inter_right
      (isClosed_le continuous_const continuous_fst), ?_⟩, hRi⟩⟩
  · simpa only [leftWing, halfMinus, dot_uvec_zero] using hK.2.inter (convex_halfMinus 0 a)
  · simpa only [rightWing, halfPlus, dot_uvec_zero] using hK.2.inter (convex_halfPlus 0 b)

/-- The shape is the union of the two wings and the strip under the roof. -/
theorem CapRoofData.shape_decomposition {K : Set Point} {a b H L : ℝ} {γ : ℝ → ℝ}
    (h : CapRoofData K a b H L γ) :
    capShape K = (leftWing K a ∪ roofStrip a b γ) ∪ rightWing K b := by
  ext p
  rw [capShape, mem_sdiff, h.niche_eq]
  constructor
  · rintro ⟨hp, hn⟩
    by_cases ha : p.1 ≤ a
    · exact Or.inl (Or.inl ⟨hp, ha⟩)
    by_cases hb : b ≤ p.1
    · exact Or.inr ⟨hp, hb⟩
    have hx : p.1 ∈ Icc a b := ⟨(not_le.mp ha).le, (not_le.mp hb).le⟩
    exact Or.inl (Or.inr ⟨hx, not_lt.mp fun hy => hn ⟨hx, h.cap.snd_nonneg hp, hy⟩,
      h.cap.snd_le_one hp⟩)
  · rintro ((⟨hp, ha⟩ | ⟨hx, hγ, h1⟩) | ⟨hp, hb⟩)
    · refine ⟨hp, fun ⟨hx, hy, hlt⟩ => ?_⟩
      rw [le_antisymm ha hx.1, h.left_zero] at hlt
      linarith
    · exact ⟨h.rectangle ⟨hx, (h.roof_nonneg _ hx).trans hγ, h1⟩,
        fun ⟨_, _, hlt⟩ => (not_lt.2 hγ) hlt⟩
    · refine ⟨hp, fun ⟨hx, hy, hlt⟩ => ?_⟩
      rw [le_antisymm hx.2 hb, h.right_zero] at hlt
      linarith

/-- The shape of a cap with a Lipschitz niche roof has uniform interior balls. -/
theorem CapRoofData.interiorBalls {K : Set Point} {a b H L : ℝ} {γ : ℝ → ℝ}
    (h : CapRoofData K a b H L γ) :
    ∃ κ r₀ : ℝ, 0 < κ ∧ 0 < r₀ ∧ HasInteriorBalls (capShape K) κ r₀ := by
  obtain ⟨hL, hR⟩ := h.wings
  rw [h.shape_decomposition]
  exact exists_interiorBalls_union (exists_interiorBalls_union
    (convexBody_hasInteriorBalls hL.1 hL.2)
    (roofStrip_hasInteriorBalls h.order h.height h.slope_nonneg h.roof_lipschitz h.roof_le))
    (convexBody_hasInteriorBalls hR.1 hR.2)

/-- The niche keeps a positive distance from every upper supporting line: the gap is positive on
the compact set `[a, b] × [0, H] × [0, π]`. -/
theorem CapRoofData.outer_margin {K : Set Point} {a b H L : ℝ} {γ : ℝ → ℝ}
    (h : CapRoofData K a b H L γ) :
    ∃ d : ℝ, 0 < d ∧ ∀ p ∈ niche K (π / 2), ∀ t ∈ Icc (0 : ℝ) π,
      d ≤ supp K t - dot p (uvec t) := by
  have hpos : ∀ p ∈ Icc a b ×ˢ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) π,
      0 < supp K t - dot p (uvec t) := by
    rintro p ⟨hpx, hpy⟩ t ht
    rcases ht.1.eq_or_lt with rfl | ht0
    · rw [dot_uvec_zero]
      linarith [hpx.2, h.right_wing]
    rcases ht.2.eq_or_lt with rfl | htπ
    · simp only [dot, uvec_pi]
      linarith [hpx.1, h.left_wing]
    -- `(p.1, 1)` lies in the cap, and `p` lies below it
    have hs := dot_le_supp h.cap.2.1.2.1
      (h.rectangle ⟨hpx, zero_le_one, le_rfl⟩ : (p.1, (1 : ℝ)) ∈ K) t
    have hgap := mul_pos (by linarith [hpy.2, h.height] : 0 < 1 - p.2)
      (sin_pos_of_pos_of_lt_pi ht0 htπ)
    simp only [dot, uvec] at hs ⊢
    linarith
  obtain ⟨d, hd, hdle⟩ := ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).exists_forall_le'
    (f := fun z : Point × ℝ => supp K z.2 - dot z.1 (uvec z.2))
    ((h.cap.2.1.continuous_supp.comp continuous_snd).sub (continuous_dot_pair.comp
      (continuous_fst.prodMk (continuous_uvec.comp continuous_snd)))).continuousOn
    fun z hz => hpos z.1 hz.1 z.2 hz.2
  refine ⟨d, hd, fun p hp t ht => ?_⟩
  rw [h.niche_eq] at hp
  exact hdle (p, t) ⟨⟨hp.1, hp.2.1, hp.2.2.le.trans (h.roof_le p.1 hp.1)⟩, ht⟩

/-- Two nonnegative roofs with the same strict subgraph have the same height: a point of `Γ` lies
on the graph of `γ`. -/
theorem roof_value_of_envelope {K Γ : Set Point} {a b H L LΓ : ℝ} {γ : ℝ → ℝ}
    (hroof : CapRoofData K a b H L γ)
    (henv : niche K (π / 2) = envUnderStrict Γ)
    (hΓ : VerticalSlopeBound Γ LΓ)
    (hbounds : ∀ q ∈ Γ, q.1 ∈ Icc a b ∧ 0 ≤ q.2)
    {q : Point} (hq : q ∈ Γ) : q.2 = γ q.1 := by
  obtain ⟨hx, hq0⟩ := hbounds q hq
  have hγ0 := hroof.roof_nonneg q.1 hx
  -- the point halfway between the two heights lies under one roof and not under the other
  rcases lt_trichotomy q.2 (γ q.1) with hlt | heq | hlt
  · have hp : (q.1, (γ q.1 + q.2) / 2) ∈ niche K (π / 2) := by
      rw [hroof.niche_eq]
      exact ⟨hx, by dsimp only; linarith, by dsimp only; linarith⟩
    rw [henv] at hp
    obtain ⟨-, q', hq', hqx, hheight⟩ := hp
    rw [eq_of_same_abscissa hΓ hq' hq hqx] at hheight
    dsimp only at hheight
    linarith
  · exact heq
  · have hp : (q.1, (γ q.1 + q.2) / 2) ∈ niche K (π / 2) := by
      rw [henv]
      exact ⟨by dsimp only; linarith, q, hq, rfl, by dsimp only; linarith⟩
    rw [hroof.niche_eq] at hp
    have hh := hp.2.2
    dsimp only at hh
    linarith

/-!
## Roof margins and approximate hallways

A set `S` in a cap `K` close to the reference cap `K₀` may violate the hallway constraints by a
slack `ζ`, and need not lie in the shape of `K`. A positive margin below the roof of `K₀` turns
this slack into a point of the shape of `K₀` nearby.
-/

/-- Close upper supports of two caps are close in every direction: below the horizontal, the
support of a cap is that of an end of its floor. -/
theorem upperSupportClose_all {δ : ℝ} {K L : Set Point}
    (hK : IsCap K (π / 2)) (hL : IsCap L (π / 2))
    (h : UpperSupportClose δ K L) : ∀ t, |supp K t - supp L t| ≤ δ := by
  intro t
  by_cases hs : 0 ≤ sin t
  · obtain ⟨s, hsi, hu, -⟩ := upper_normal_representative t hs
    simpa only [supp, hu] using h s hsi
  have hs' := (not_le.mp hs).le
  rcases le_total 0 (cos t) with hc | hc
  · rw [cap_lower_right_support hK hs' hc, cap_lower_right_support hL hs' hc, ← sub_mul, abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one t)).trans
      (h 0 ⟨le_rfl, pi_pos.le⟩)
  · rw [cap_lower_left_support hK hs' hc, cap_lower_left_support hL hs' hc, ← sub_mul, abs_mul,
      neg_sub_neg, abs_sub_comm]
    exact (mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one t)).trans
      (h π ⟨pi_pos.le, le_rfl⟩)

/-- Caps with `δ`-close upper supports are `δ`-close in the Euclidean Hausdorff sense. -/
theorem upperSupportClose_euclidean {δ : ℝ} (hδ : 0 ≤ δ) {K L : Set Point}
    (hK : IsCap K (π / 2)) (hL : IsCap L (π / 2)) (h : UpperSupportClose δ K L) :
    EuclideanClose δ K L :=
  euclideanClose_of_support_bound hK.2.1 hL.2.1 hδ (upperSupportClose_all hK hL h)

/-- Wall margins along the roof: at depth `γ(p.1) - p.2` below the roof, a point of the niche has
both slacks at most `-min (c (γ(p.1) - p.2)) τ` at some angle. -/
def RoofSlackMargin (K : Set Point) (γ : ℝ → ℝ) (c τ : ℝ) : Prop :=
  ∀ p ∈ niche K (π / 2), ∃ t ∈ Ioo (0 : ℝ) (π / 2),
    innerSlackU K t p ≤ -min (c * (γ p.1 - p.2)) τ ∧
      innerSlackV K t p ≤ -min (c * (γ p.1 - p.2)) τ

/-- Every point of `S` violates each hallway constraint of `K` by at most `ζ`: at every angle in
`(0, π/2)`, one of its two slacks is at least `-ζ`. -/
def ApproxHallways (K S : Set Point) (ζ : ℝ) : Prop :=
  ∀ p ∈ S, ∀ t ∈ Ioo (0 : ℝ) (π / 2),
    -ζ ≤ max (innerSlackU K t p) (innerSlackV K t p)

/-- Let the upper supports of a cap `K` be `δ`-close to those of `K₀`, and let `S ⊆ K` satisfy the
hallway constraints of `K` up to `ζ`. Then every point of `S` lies within `max 1 (1 / c) · (δ + ζ)`
of the shape of `K₀`, also when it lies outside the shape of `K`. -/
theorem directed_to_reference_of_margins {K₀ K S : Set Point}
    {a b H L c τ d₀ δ ζ : ℝ} {γ : ℝ → ℝ}
    (hroof : CapRoofData K₀ a b H L γ) (hK : IsCap K (π / 2))
    (hc : 0 < c) (hδ : 0 ≤ δ) (hζ : 0 ≤ ζ)
    (hclose : UpperSupportClose δ K K₀)
    (houter : ∀ q ∈ niche K₀ (π / 2), ∀ t ∈ Icc (0 : ℝ) π,
      d₀ ≤ supp K₀ t - dot q (uvec t))
    (hδsmall : δ < d₀) (hsmall : δ + ζ < τ)
    (hslack : RoofSlackMargin K₀ γ c τ)
    (hSK : S ⊆ K) (hhall : ApproxHallways K S ζ) :
    DirectedClose (max 1 (1 / c) * (δ + ζ)) S (capShape K₀) := by
  have hδζ := add_nonneg hδ hζ
  have hδC : δ ≤ max 1 (1 / c) * (δ + ζ) := by
    linarith [mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) (1 / c)) hδζ]
  intro p hp
  have hpK := hSK hp
  by_cases hp₀ : p ∈ K₀
  · by_cases hpG : p ∈ capShape K₀
    · exact ⟨p, hpG, by rw [euclideanDist_self]; positivity⟩
    have hpN : p ∈ niche K₀ (π / 2) := by_contra fun hn => hpG ⟨hp₀, hn⟩
    have hn := hpN
    rw [hroof.niche_eq] at hn
    obtain ⟨t, ht, hu, hv⟩ := hslack p hpN
    -- the depth of `p` below the roof is at most `(δ + ζ) / c`
    have hdepth : c * (γ p.1 - p.2) ≤ δ + ζ := by
      by_contra he
      have hm : δ + ζ < min (c * (γ p.1 - p.2)) τ := lt_min (not_le.mp he) hsmall
      have hU := (abs_le.mp (hclose t ⟨ht.1.le, by linarith [ht.2, pi_pos]⟩)).1
      have hV := (abs_le.mp (hclose (t + π / 2)
        ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩)).1
      have hh := hhall p hp t ht
      simp only [innerSlackU, innerSlackV] at hu hv hh
      exact (not_lt_of_ge hh) (max_lt (by linarith) (by linarith))
    -- the point `(p.1, γ(p.1))` of the roof lies in the shape of `K₀`
    refine ⟨(p.1, γ p.1), hroof.shape_decomposition ▸ Or.inl (Or.inr
      ⟨hn.1, le_rfl, (hroof.roof_le _ hn.1).trans hroof.height.le⟩), ?_⟩
    have hd : euclideanDist p (p.1, γ p.1) = γ p.1 - p.2 := by
      simp only [euclideanDist, norm2, dot, Prod.fst_sub, Prod.snd_sub, sub_self, mul_zero,
        zero_add]
      rw [← pow_two, Real.sqrt_sq_eq_abs, abs_sub_comm, abs_of_pos (sub_pos.2 hn.2.2)]
    rw [hd]
    calc γ p.1 - p.2 ≤ (δ + ζ) / c := (le_div_iff₀ hc).2 (by linarith)
      _ = 1 / c * (δ + ζ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hδζ
  · -- `p` is `δ`-close to a point `q` of `K₀`, which is outside the niche by the outer margin
    obtain ⟨q, hq, hpq⟩ := (upperSupportClose_euclidean hδ hK hroof.cap hclose).1 p hpK
    refine ⟨q, ⟨hq, fun hqN => hp₀ ((cap_mem_iff_upper hroof.cap p).2
      ⟨hK.snd_nonneg hpK, fun t ht => ?_⟩)⟩, hpq.trans hδC⟩
    have hproj := dot_uvec_le_norm2 (p - q) t
    rw [dot_sub_left] at hproj
    have hmargin := houter q hqN t ht
    change norm2 (p - q) ≤ δ at hpq
    linarith

/-!
## Gerver's roof and the recovery constants

The roof of Gerver's niche is the envelope of the inner corner, a graph of finite slope strictly
below the top of the cap; the two wings have positive width because the vertical supporting lines
of the cap meet it in single points.
-/

/-- The abscissa `D(0)₁` of the left end of Gerver's roof. -/
def gerverRoofLeft (P : GerverParams) : ℝ := (envD P.path P.gs_β 0).1

/-- The abscissa `B(π/2)₁` of the right end of Gerver's roof. -/
def gerverRoofRight (P : GerverParams) : ℝ := (envB P.path P.gs_α (π / 2)).1

/-- The envelope of the inner corner of Gerver's rotation path. -/
def gerverEnvelope (P : GerverParams) : Set Point :=
  envCurve P.φ P.θ (π / 2 - P.θ) (π / 2 - P.φ) P.path P.gs_α P.gs_β

theorem gerver_cap_explicit {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    P.cap = P.gs_K := (gs_monotone_K hP (romik_bounds hP hbox)).2

/-- The shape of Gerver's cap is Gerver's sofa. -/
theorem gerver_shape_eq {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    capShape P.cap = gerverSofa P := by
  rw [capShape, gerver_cap_explicit hP hbox]
  exact (gs_gerverSofa_eq hP (romik_bounds hP hbox)).symm

/-- The niche of Gerver's cap is the region strictly under the envelope. -/
theorem gerver_niche_envelope {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    niche P.cap (π / 2) = envUnderStrict (gerverEnvelope P) := by
  rw [gerver_cap_explicit hP hbox]
  exact gerver_niche_eq_envUnderStrict hP (romik_bounds hP hbox)

/-- A point `(a, 1)` of a cap satisfying the first injectivity condition lies strictly between the
ends of the floor: the vertical supporting lines meet the cap in single points of the floor. -/
theorem cap_top_strict_between_floor_endpoints {K : Set Point}
    (hK : IsCap K (π / 2)) (h1 : InjCond1 K) {a : ℝ} (ha : (a, 1) ∈ K) :
    -supp K π < a ∧ a < supp K 0 := by
  have hb := opt_cap_fst_le hK ha
  have hleft : vplus K π = vminus K π := by
    simpa only [cPlus, cMinus, add_halves] using
      ((proposition6_4_5 hK h1).2 (π / 2) ⟨by positivity, le_rfl⟩).1
  have hright : vplus K 0 = vminus K 0 :=
    ((proposition6_4_5 hK h1).1 0 ⟨le_rfl, by positivity⟩).1
  refine ⟨hb.1.lt_of_ne fun he => ?_, hb.2.lt_of_ne fun he => ?_⟩
  · have hp : (a, (1 : ℝ)) ∈ edge K π := ⟨ha, by
      change dot (a, 1) (uvec π) = supp K π
      simp only [dot, uvec_pi]
      linarith⟩
    rw [edge_eq_segment hK.2.1 π, ← hleft, opt_cap_vplus_pi hK, segment_same] at hp
    simp at hp
  · have hp : (a, (1 : ℝ)) ∈ edge K 0 := ⟨ha, by
      change dot (a, 1) (uvec 0) = supp K 0
      simpa only [uvec_zero, dot, mul_one, mul_zero, add_zero] using he⟩
    rw [edge_eq_segment hK.2.1 0, hright, (inj_cap_consecutive hK).1, segment_same] at hp
    simp at hp

/-- Gerver's niche is the region under a nonnegative roof of finite slope strictly below one: the
envelope, which is a graph by `exists_roof_function`. -/
theorem gerver_roof_data {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ H L : ℝ, ∃ γ : ℝ → ℝ,
      CapRoofData P.cap (gerverRoofLeft P) (gerverRoofRight P) H L γ := by
  have hB := romik_bounds hP hbox
  have henv := gn_envHyp hP hB
  have hc : IsCap P.cap (π / 2) := gm_isCap hP hbox
  have hI : InjCond1 P.cap := (theorem6_1_2 hP hbox).1
  have hΓ := envelope_bounds_of_path_height henv fun t ht => path_snd_lt_one hP hB ht.1 ht.2
  obtain ⟨L, hL, hSlope⟩ :=
    envelope_slope_bound henv (by linarith [henv.ht.2.2.1]) (by linarith [henv.ht.2.2.1])
  obtain ⟨γ, hgraph, hLip⟩ := exists_roof_function (fun p hp => (hΓ p hp).1)
    (fun x hx => env_exists_curve_fst henv hx) hSlope
  have hγmem : ∀ x ∈ Icc (gerverRoofLeft P) (gerverRoofRight P), (x, γ x) ∈ gerverEnvelope P :=
    fun x hx => (hgraph _).2 ⟨hx, rfl⟩
  -- the roof vanishes at its ends `D(0)` and `B(π/2)` and attains a maximum height `H < 1`
  have hDmem : envD P.path P.gs_β 0 ∈ gerverEnvelope P :=
    Or.inr ⟨0, ⟨le_rfl, (henv.ht.1.trans henv.ht.2.1).le⟩, rfl⟩
  have hBmem : envB P.path P.gs_α (π / 2) ∈ gerverEnvelope P :=
    Or.inl (Or.inl ⟨π / 2, ⟨by linarith [henv.ht.2.2.2.1, henv.ht.2.2.2.2], le_rfl⟩, rfl⟩)
  obtain ⟨pmax, hpmax, hmax⟩ :=
    (envelope_isCompact henv).exists_isMaxOn ⟨_, hDmem⟩ continuous_snd.continuousOn
  obtain ⟨ho1, ho2, ho3⟩ := envelope_endpoint_order henv
  have hab : gerverRoofLeft P < gerverRoofRight P := ho1.trans (ho2.trans ho3)
  -- the ends `(a, 1)` and `(b, 1)` of the top edge of the cap
  have ha : (gerverRoofLeft P, 1) ∈ P.cap := by
    simpa only [gerver_cap_explicit hP hbox, gerverRoofLeft, gerver_contactC_zero hP hB] using
      gs_C_mem_K hP hB (τ := 0) le_rfl (by positivity)
  have hb : (gerverRoofRight P, 1) ∈ P.cap := by
    simpa only [gerver_cap_explicit hP hbox, gerverRoofRight, gerver_contactA_pi_div_two hP hB]
      using gs_A_mem_K hP hB (τ := π / 2) (by positivity) le_rfl
  refine ⟨pmax.2, L, γ, hc, hab, (cap_top_strict_between_floor_endpoints hc hI ha).1,
    (cap_top_strict_between_floor_endpoints hc hI hb).2, (hΓ pmax hpmax).2.2, hL,
    fun x hx => (hΓ _ (hγmem x hx)).2.1, fun x hx => hmax (hγmem x hx), hLip,
    ((hgraph _).1 hDmem).2.symm.trans henv.D_end, ((hgraph _).1 hBmem).2.symm.trans henv.B_end,
    cap_horizontal_rectangle hc hab ha hb, ?_⟩
  -- the niche is the region strictly under the roof
  rw [gerver_niche_envelope hP hbox]
  ext p
  constructor
  · rintro ⟨hpy, q, hq, hqx, hpq⟩
    obtain ⟨hx, hy⟩ := (hgraph q).1 hq
    rw [hqx] at hx hy
    exact ⟨hx, hpy, hpq.trans_eq hy⟩
  · rintro ⟨hx, hpy, hy⟩
    exact ⟨hpy, _, hγmem p.1 hx, rfl, hy⟩

/-- The slack below the envelope gives the wall margins along any roof of Gerver's niche. -/
theorem gerver_roof_slack_margin {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {H L : ℝ} {γ : ℝ → ℝ}
    (hroof : CapRoofData P.cap (gerverRoofLeft P) (gerverRoofRight P) H L γ) :
    ∃ c τ : ℝ, 0 < c ∧ 0 < τ ∧ RoofSlackMargin P.cap γ c τ := by
  have hB := romik_bounds hP hbox
  have henv := gn_envHyp hP hB
  obtain ⟨LΓ, -, hΓ⟩ :=
    envelope_slope_bound henv (by linarith [henv.ht.2.2.1]) (by linarith [henv.ht.2.2.1])
  have hbounds := envelope_bounds_of_path_height henv fun t ht => path_snd_lt_one hP hB ht.1 ht.2
  have hniche := gerver_niche_envelope hP hbox
  obtain ⟨c, τ, hc, hτ, hslack⟩ := envelope_downward_slack henv
    (K := P.cap) (fun t ht => ((theorem8_4_1_monotone hP hbox).2 t ht).2.2)
  refine ⟨c, τ, hc, hτ, fun p hp => ?_⟩
  rw [hniche] at hp
  obtain ⟨hpy, q, hq, hqx, hlt⟩ := hp
  -- `p` lies at depth `q.2 - p.2 = γ(p.1) - p.2` below the point `q` of the envelope
  have hγq := roof_value_of_envelope hroof hniche hΓ
    (fun p hp => ⟨(hbounds p hp).1, (hbounds p hp).2.1⟩) hq
  obtain ⟨t, ht, hU, hV⟩ := hslack q hq (q.2 - p.2) (sub_pos.2 hlt) (by linarith)
  rw [show (q.1, q.2 - (q.2 - p.2)) = p from Prod.ext hqx (sub_sub_cancel _ _), hγq, hqx]
    at hU hV
  exact ⟨t, ht, hU, hV⟩

/-- The constants of the directed recovery from a near-optimal sofa to Gerver's sofa depend on
Gerver's sofa alone: a roof, wall margins along it, an outer margin and uniform interior balls. -/
theorem gerver_recovery_constants {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ H L : ℝ, ∃ γ : ℝ → ℝ, ∃ c τ d₀ κ r₀ : ℝ,
      CapRoofData P.cap (gerverRoofLeft P) (gerverRoofRight P) H L γ ∧
      0 < c ∧ 0 < τ ∧ 0 < d₀ ∧ 0 < κ ∧ 0 < r₀ ∧
      RoofSlackMargin P.cap γ c τ ∧
      (∀ p ∈ niche P.cap (π / 2), ∀ t ∈ Icc (0 : ℝ) π,
        d₀ ≤ supp P.cap t - dot p (uvec t)) ∧
      HasInteriorBalls (gerverSofa P) κ r₀ := by
  obtain ⟨H, L, γ, hroof⟩ := gerver_roof_data hP hbox
  obtain ⟨c, τ, hc, hτ, hslack⟩ := gerver_roof_slack_margin hP hbox hroof
  obtain ⟨d₀, hd₀, houter⟩ := hroof.outer_margin
  obtain ⟨κ, r₀, hκ, hr₀, hballs⟩ := hroof.interiorBalls
  rw [gerver_shape_eq hP hbox] at hballs
  exact ⟨H, L, γ, c, τ, d₀, κ, r₀, hroof, hc, hτ, hd₀, hκ, hr₀, hslack, houter, hballs⟩

end MovingSofaStability
