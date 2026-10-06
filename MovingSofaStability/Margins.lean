module

public import MovingSofaUniqueness.RegularClosed
public import MovingSofaStability.Basic
public import MovingSofaStability.CapEstimate

/-!
# The margins of Gerver's sofa

The shape of a cap and its missing area, interior balls, and the roof of Gerver's sofa: the outer margin,
the slack of its envelope and the uniform interior balls that carry bounds from the cap to the sofa
(`gerver_recovery_constants`).

The sections below follow the steps of the proof.
-/

@[expose] public section
noncomputable section

/-!
## The actual nonconvex cap shape and robust hallway inequalities

The erosion inclusion is proved for arbitrary pairs of normalized right-angle
caps, not just Gerver and not just injective caps. It keeps the actual set
difference K minus its niche throughout.
-/

section CapShape

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

def capShape (K : Set Point) : Set Point := K \ niche K (π / 2)

def UpperSupportClose (δ : ℝ) (K L : Set Point) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) π, |supp K t - supp L t| ≤ δ

def innerSlackU (K : Set Point) (t : ℝ) (p : Point) : ℝ := dot p (uvec t) - supp K t + 1

def innerSlackV (K : Set Point) (t : ℝ) (p : Point) : ℝ :=
  dot p (vvec t) - supp K (t + π / 2) + 1

/-- Closed Euclidean-ball erosion, convenient for point witnesses. -/
def euclideanErosion (r : ℝ) (S : Set Point) : Set Point :=
  {p | ∀ q, euclideanDist p q ≤ r → q ∈ S}

/-- A cap is determined by its upper half-planes and the floor. -/
theorem cap_mem_iff_upper {K : Set Point} (hK : IsCap K (π / 2)) (p : Point) :
    p ∈ K ↔ 0 ≤ p.2 ∧ ∀ t ∈ Icc (0 : ℝ) π, dot p (uvec t) ≤ supp K t := by
  constructor
  · intro hp
    exact ⟨hK.snd_nonneg hp, fun t _ => dot_le_supp hK.2.1.2.1 hp t⟩
  · rintro ⟨hpy, h⟩
    apply (mem_iff_forall_dot_le_supp hK.2.1 p).2
    intro t
    by_cases hs : 0 ≤ sin t
    · obtain ⟨s, hsI, hu, -⟩ := upper_normal_representative t hs
      have he : supp K s = supp K t := by simp only [supp, hu]
      have hh := h s hsI
      simpa only [hu, he] using hh
    have hs' := (not_le.mp hs).le
    have hys : p.2 * sin t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpy hs'
    by_cases hc : 0 ≤ cos t
    · rw [cap_lower_right_support hK hs' hc]
      have hx := h 0 ⟨le_rfl, pi_pos.le⟩
      simp only [uvec_zero, dot] at hx
      have hm := mul_le_mul_of_nonneg_right hx hc
      simp only [dot, uvec]
      linarith
    · rw [cap_lower_left_support hK hs' (not_le.mp hc).le]
      have hx := h π ⟨pi_pos.le, le_rfl⟩
      simp only [uvec_pi, dot] at hx
      have hm : p.1 * cos t ≤ -supp K π * cos t :=
        mul_le_mul_of_nonpos_right (by linarith) (not_le.mp hc).le
      simp only [dot, uvec]
      linarith

/-- The actual forbidden quadrant is described by two strict slack inequalities. -/
theorem mem_qMinus_iff_slacks (K : Set Point) (t : ℝ) (p : Point) :
    p ∈ qMinus K t ↔ innerSlackU K t p < 0 ∧ innerSlackV K t p < 0 := by
  rw [ms_mem_qMinus_iff]
  unfold innerSlackU innerSlackV
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem mem_niche_iff_slacks (K : Set Point) (p : Point) :
    p ∈ niche K (π / 2) ↔ 0 ≤ p.2 ∧
      ∃ t ∈ Ioo (0 : ℝ) (π / 2), innerSlackU K t p < 0 ∧ innerSlackV K t p < 0 := by
  simp only [niche, mem_inter_iff, mem_fan_iff, dot_uvec_pi_div_two, and_self,
    mem_iUnion, exists_prop, mem_qMinus_iff_slacks]

theorem slackU_support_error {δ : ℝ} {K L : Set Point} (h : UpperSupportClose δ K L)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) π) (p : Point) :
    |innerSlackU K t p - innerSlackU L t p| ≤ δ := by
  have he : innerSlackU K t p - innerSlackU L t p = supp L t - supp K t := by
    unfold innerSlackU
    ring
  rw [he, abs_sub_comm]
  exact h t ht

theorem slackV_support_error {δ : ℝ} {K L : Set Point} (h : UpperSupportClose δ K L)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (π / 2)) (p : Point) :
    |innerSlackV K t p - innerSlackV L t p| ≤ δ := by
  have he : innerSlackV K t p - innerSlackV L t p =
      supp L (t + π / 2) - supp K (t + π / 2) := by
    unfold innerSlackV
    ring
  rw [he, abs_sub_comm]
  exact h _ ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩

/-- A reference erosion is contained in the perturbed nonconvex shape.
The coefficient two is convenient and non-sharp. -/
theorem reference_erosion_subset {δ : ℝ} (hδ : 0 ≤ δ) {K₀ K : Set Point}
    (h₀ : IsCap K₀ (π / 2)) (hK : IsCap K (π / 2))
    (hclose : UpperSupportClose δ K K₀) :
    euclideanErosion (2 * δ) (capShape K₀) ⊆ capShape K := by
  intro p hp
  have hp0 : p ∈ capShape K₀ := hp p (by simpa only [euclideanDist_self] using mul_nonneg (by norm_num) hδ)
  have hpK : p ∈ K := by
    apply (cap_mem_iff_upper hK p).2
    refine ⟨h₀.snd_nonneg hp0.1, ?_⟩
    intro t ht
    have hd : euclideanDist p (p + δ • uvec t) ≤ 2 * δ := by
      change norm2 (p - (p + δ • uvec t)) ≤ 2 * δ
      rw [show p - (p + δ • uvec t) = -(δ • uvec t) by abel,
        norm2_neg, norm2_smul, norm2_uvec, mul_one, abs_of_nonneg hδ]
      linarith
    have hq := (hp (p + δ • uvec t) hd).1
    have hs := dot_le_supp h₀.2.1.2.1 hq t
    rw [dot_add_left, dot_smul_left, dot_uvec_self, mul_one] at hs
    have herr := (abs_le.mp (hclose t ht)).1
    linarith
  refine ⟨hpK, ?_⟩
  intro hn
  obtain ⟨-, t, ht, hu, hv⟩ := (mem_niche_iff_slacks K p).1 hn
  let q := p - δ • uvec t - δ • vvec t
  have hd : euclideanDist p q ≤ 2 * δ := by
    change norm2 (p - (p - δ • uvec t - δ • vvec t)) ≤ 2 * δ
    rw [show p - (p - δ • uvec t - δ • vvec t) = δ • uvec t + δ • vvec t by abel]
    have hh := norm2_add_le (δ • uvec t) (δ • vvec t)
    have hnv : norm2 (vvec t) = 1 := by simp [norm2]
    rw [norm2_smul, norm2_smul, norm2_uvec, hnv, abs_of_nonneg hδ] at hh
    nlinarith
  have hq := hp q hd
  have herrU := (abs_le.mp (hclose t ⟨ht.1.le, by linarith [ht.2, pi_pos]⟩)).2
  have herrV := (abs_le.mp (hclose (t + π / 2)
    ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩)).2
  have eqU : innerSlackU K₀ t q = innerSlackU K t p + supp K t - supp K₀ t - δ := by
    simp only [innerSlackU, q, dot_sub_left, dot_smul_left, dot_uvec_self, dot_vvec_uvec]
    ring
  have eqV : innerSlackV K₀ t q = innerSlackV K t p +
      supp K (t + π / 2) - supp K₀ (t + π / 2) - δ := by
    simp only [innerSlackV, q, dot_sub_left, dot_smul_left, dot_uvec_vvec, dot_vvec_self]
    ring
  apply hq.2
  apply (mem_niche_iff_slacks K₀ q).2
  exact ⟨h₀.snd_nonneg hq.1, t, ht, by rw [eqU]; linarith, by rw [eqV]; linarith⟩

end MovingSofaStability

end CapShape

/-!
## Recovering a nonconvex set from an erosion and a missing-area bound

The geometric hypothesis is an explicit uniform interior-ball condition on the
reference set, not an assumed stability theorem. An inscribed square provides
the area lower bound, so no Euclidean disk-volume conversion for the ambient
product space is required.
-/

section MissingAreaRecovery

open Real Set MeasureTheory
open MovingSofaOptimality

namespace MovingSofaStability

def euclideanBall (p : Point) (r : ℝ) : Set Point := {q | euclideanDist p q ≤ r}

/-- A reference set has a ball at every point and every sufficiently small scale. -/
def HasInteriorBalls (G : Set Point) (κ r₀ : ℝ) : Prop :=
  ∀ p ∈ G, ∀ ρ : ℝ, 0 < ρ → ρ ≤ r₀ →
    ∃ z, euclideanBall z (κ * ρ) ⊆ G ∩ euclideanBall p ρ

/-- Square of side length a centered at z. -/
def centeredSquare (z : Point) (a : ℝ) : Set Point :=
  Icc (z.1 - a / 2) (z.1 + a / 2) ×ˢ Icc (z.2 - a / 2) (z.2 + a / 2)

theorem area_centeredSquare (z : Point) {a : ℝ} (ha : 0 ≤ a) :
    area (centeredSquare z a) = a ^ 2 := by
  have hm : volume (centeredSquare z a) = ENNReal.ofReal a * ENNReal.ofReal a := by
    simp only [centeredSquare, Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_Icc]
    congr 1 <;> congr 1 <;> ring
  unfold area
  rw [hm, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha]
  ring

theorem centeredSquare_subset_ball (z : Point) {a : ℝ} :
    centeredSquare z a ⊆ euclideanBall z a := by
  rintro q ⟨hx, hy⟩
  have hx' : |z.1 - q.1| ≤ a / 2 := abs_le.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hy' : |z.2 - q.2| ≤ a / 2 := abs_le.2 ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hn : ‖z - q‖ ≤ a / 2 := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le hx' hy'
  change norm2 (z - q) ≤ a
  have h := norm2_le_two_product_norm (z - q)
  linarith

/-- Shrinking an interior ball by r leaves it inside the r-erosion. -/
theorem ball_subset_erosion {G : Set Point} {z : Point} {a r R : ℝ}
    (hball : euclideanBall z R ⊆ G) (har : a + r ≤ R) :
    euclideanBall z a ⊆ euclideanErosion r G := by
  intro q hq p hp
  apply hball
  exact (euclideanDist_triangle z q p).trans ((add_le_add hq hp).trans har)

/-- At a fixed scale, a missing region smaller than an inscribed square cannot
remove every nearby point of the target. Neither G nor S is assumed convex. -/
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
  let a := κ * ρ / 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have halarge : a ≤ κ * ρ := by dsimp [a]; nlinarith
  have hsmallball : euclideanBall z a ⊆ euclideanErosion r G :=
    ball_subset_erosion (fun q hq => (hz hq).1) (by dsimp [a] at *; linarith)
  have hsq : centeredSquare z a ⊆ U \ S := by
    intro q hq
    have hqball := centeredSquare_subset_ball z hq
    have hqG := hz (hqball.trans halarge)
    refine ⟨herosion (hsmallball hqball), ?_⟩
    intro hqS
    exact hnone ⟨q, hqS, hqG.2⟩
  have harea := area_mono_of_finite hsq (volume_ne_top_of_subset sdiff_subset hUf)
  rw [area_centeredSquare z ha] at harea
  have ha2 : a ^ 2 ≤ η := harea.trans hmissing
  exact (not_lt_of_ge ha2) hsmall

/-- A square-root scale suffices when the erosion radius is already O(sqrt ε).
The coefficient is not optimized and is independent of the smaller set S. -/
theorem directedClose_sqrt_of_missing_area {G U S : Set Point} {κ r₀ r A ε : ℝ}
    (hκ : 0 < κ) (hA : 0 ≤ A) (hε : 0 < ε)
    (hballs : HasInteriorBalls G κ r₀)
    (herosion : euclideanErosion r G ⊆ U)
    (hr : r ≤ A * sqrt ε)
    (hscale : (4 * (A + 1) / κ) * sqrt ε ≤ r₀)
    (hUf : volume U ≠ ⊤) (hmissing : area (U \ S) ≤ 2 * ε) :
    DirectedClose ((4 * (A + 1) / κ) * sqrt ε) G S := by
  let ρ := (4 * (A + 1) / κ) * sqrt ε
  have hs : 0 < sqrt ε := sqrt_pos.2 hε
  have hs2 : sqrt ε ^ 2 = ε := sq_sqrt hε.le
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have he : κ * ρ / 2 = 2 * (A + 1) * sqrt ε := by
    dsimp [ρ]
    field_simp [hκ.ne']
    ring
  apply directedClose_of_missing_area hκ hρ hscale hballs herosion
  · rw [he]
    nlinarith
  · exact hUf
  · exact hmissing
  · rw [he]
    have hAl : 1 ≤ (A + 1) ^ 2 := by nlinarith
    have hprod := mul_le_mul_of_nonneg_right hAl hε.le
    nlinarith [sq_nonneg (A + 1), mul_pow (2 * (A + 1)) (sqrt ε) 2]

/-- The cap erosion lemma can be inserted without a geometric regularity assumption on K. -/
theorem reference_to_sofa_recovery {K₀ K S : Set Point} {δ κ r₀ A ε : ℝ}
    (h₀ : IsCap K₀ (π / 2)) (hK : IsCap K (π / 2))
    (hδ : 0 ≤ δ) (hclose : UpperSupportClose δ K K₀)
    (hκ : 0 < κ) (hA : 0 ≤ A) (hε : 0 < ε)
    (hballs : HasInteriorBalls (capShape K₀) κ r₀)
    (hδbound : 2 * δ ≤ A * sqrt ε)
    (hscale : (4 * (A + 1) / κ) * sqrt ε ≤ r₀)
    (hUf : volume (capShape K) ≠ ⊤)
    (hmissing : area (capShape K \ S) ≤ 2 * ε) :
    DirectedClose ((4 * (A + 1) / κ) * sqrt ε) (capShape K₀) S :=
  directedClose_sqrt_of_missing_area hκ hA hε hballs
    (reference_erosion_subset hδ h₀ hK hclose) hδbound hscale hUf hmissing

end MovingSofaStability

end MissingAreaRecovery

/-!
## Uniform interior balls from convex pieces

The construction shrinks one fixed interior ball about each point of a convex
piece. The union lemmas permit a nonconvex reference to be assembled from
finitely many such pieces.
-/

section InteriorBalls

open Real Set
open MovingSofaOptimality

namespace MovingSofaStability

/-- Shrinking a ball inside a convex set gives a ball at every boundary point. -/
theorem convex_interiorBalls_of_ball {C : Set Point} (hC : Convex ℝ C)
    {c : Point} {s D : ℝ} (hs : 0 < s) (hD : 0 ≤ D)
    (hball : euclideanBall c s ⊆ C)
    (hbound : ∀ p ∈ C, euclideanDist p c ≤ D) :
    HasInteriorBalls C (s / (D + s)) (D + s) := by
  intro p hp ρ hρ hρmax
  have hden : 0 < D + s := by linarith
  let μ := ρ / (D + s)
  let z := (1 - μ) • p + μ • c
  have hμ : 0 < μ := div_pos hρ hden
  have hμ1 : μ ≤ 1 := (div_le_one hden).2 hρmax
  have hμden : μ * (D + s) = ρ := div_mul_cancel₀ _ hden.ne'
  have hrad : s / (D + s) * ρ = μ * s := by dsimp [μ]; ring
  refine ⟨z, ?_⟩
  intro q hq
  rw [hrad] at hq
  let w := c + μ⁻¹ • (q - z)
  have hwball : w ∈ euclideanBall c s := by
    change norm2 (c - (c + μ⁻¹ • (q - z))) ≤ s
    rw [show c - (c + μ⁻¹ • (q - z)) = -(μ⁻¹ • (q - z)) by abel,
      norm2_neg, norm2_smul, abs_of_pos (inv_pos.mpr hμ)]
    have hq' : norm2 (q - z) ≤ μ * s := by
      rw [← norm2_neg, neg_sub]
      exact hq
    have hmul := mul_le_mul_of_nonneg_left hq' (inv_nonneg.mpr hμ.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hμ.ne', one_mul] using hmul
  have hqC : q ∈ C := by
    have h := hC hp (hball hwball) (sub_nonneg.mpr hμ1) hμ.le (by ring : 1 - μ + μ = 1)
    have he : (1 - μ) • p + μ • w = q := by
      have hw : μ • w = μ • c + (q - z) := by
        simp only [w, smul_add, smul_inv_smul₀ hμ.ne']
      rw [hw]
      simp only [z]
      abel
    rwa [he] at h
  have hzp : euclideanDist p z ≤ μ * D := by
    change norm2 (p - ((1 - μ) • p + μ • c)) ≤ μ * D
    rw [show p - ((1 - μ) • p + μ • c) = μ • (p - c) by
      ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring,
      norm2_smul, abs_of_pos hμ]
    exact mul_le_mul_of_nonneg_left (hbound p hp) hμ.le
  refine ⟨hqC, ?_⟩
  change euclideanDist p q ≤ ρ
  have hh := euclideanDist_triangle p z q
  have he : μ * D + μ * s = ρ := by rw [← mul_add, hμden]
  exact hh.trans ((add_le_add hzp hq).trans_eq he)

/-- A nonempty interior supplies a closed Euclidean ball even though the ambient
product-space topology is originally presented with the sup norm. -/
theorem exists_euclideanBall_subset_of_interior {C : Set Point}
    (hne : (interior C).Nonempty) :
    ∃ c s, 0 < s ∧ euclideanBall c s ⊆ C := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hc)
  refine ⟨c, r / 2, by linarith, ?_⟩
  intro q hq
  apply hball
  change dist q c < r
  have hd : dist q c ≤ euclideanDist c q := by
    rw [dist_comm, dist_eq_norm]
    exact product_norm_le_norm2 (c - q)
  exact (hd.trans hq).trans_lt (by linarith)

/-- Compact convex bodies with interior have uniform interior balls at all small scales. -/
theorem convexBody_hasInteriorBalls {C : Set Point} (hC : IsConvexBody C)
    (hne : (interior C).Nonempty) :
    ∃ κ r₀ : ℝ, 0 < κ ∧ 0 < r₀ ∧ HasInteriorBalls C κ r₀ := by
  obtain ⟨c, s, hs, hball⟩ := exists_euclideanBall_subset_of_interior hne
  have hc : c ∈ C := hball (by simpa only [euclideanBall, mem_ofPred_eq, euclideanDist_self] using hs.le)
  have hcont : Continuous (fun p : Point => euclideanDist p c) := by
    exact continuous_norm2.comp (continuous_id.sub continuous_const)
  obtain ⟨D, hD⟩ := hC.2.1.exists_bound_of_continuousOn hcont.continuousOn
  have hD0 : 0 ≤ D := by simpa only [euclideanDist_self, norm_zero] using hD c hc
  have hbound : ∀ p ∈ C, euclideanDist p c ≤ D := by
    intro p hp
    have h := hD p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg (euclideanDist_nonneg p c)] using h
  refine ⟨s / (D + s), D + s, by positivity, by positivity, ?_⟩
  exact convex_interiorBalls_of_ball hC.2.2 hs hD0 hball hbound

/-- An interior-ball statement persists when its constants are decreased. -/
theorem HasInteriorBalls.mono_constants {G : Set Point} {κ r₀ κ' r₀' : ℝ}
    (h : HasInteriorBalls G κ r₀) (hκ : κ' ≤ κ) (hr : r₀' ≤ r₀) :
    HasInteriorBalls G κ' r₀' := by
  intro p hp ρ hρ hρmax
  obtain ⟨z, hz⟩ := h p hp ρ hρ (hρmax.trans hr)
  refine ⟨z, ?_⟩
  intro q hq
  exact hz (hq.trans (mul_le_mul_of_nonneg_right hκ hρ.le))

/-- A finite union need not be convex; a containing piece provides the local ball. -/
theorem interiorBalls_union {G H : Set Point} {κ r₀ : ℝ}
    (hG : HasInteriorBalls G κ r₀) (hH : HasInteriorBalls H κ r₀) :
    HasInteriorBalls (G ∪ H) κ r₀ := by
  intro p hp ρ hρ hρmax
  rcases hp with hp | hp
  · obtain ⟨z, hz⟩ := hG p hp ρ hρ hρmax
    exact ⟨z, fun q hq => ⟨Or.inl (hz hq).1, (hz hq).2⟩⟩
  · obtain ⟨z, hz⟩ := hH p hp ρ hρ hρmax
    exact ⟨z, fun q hq => ⟨Or.inr (hz hq).1, (hz hq).2⟩⟩

/-- Existential interior-ball constants combine without a shared initial scale. -/
theorem exists_interiorBalls_union {G H : Set Point}
    (hG : ∃ κ r₀ : ℝ, 0 < κ ∧ 0 < r₀ ∧ HasInteriorBalls G κ r₀)
    (hH : ∃ κ r₀ : ℝ, 0 < κ ∧ 0 < r₀ ∧ HasInteriorBalls H κ r₀) :
    ∃ κ r₀ : ℝ, 0 < κ ∧ 0 < r₀ ∧ HasInteriorBalls (G ∪ H) κ r₀ := by
  obtain ⟨κG, rG, hκG, hrG, hG⟩ := hG
  obtain ⟨κH, rH, hκH, hrH, hH⟩ := hH
  refine ⟨min κG κH, min rG rH, lt_min hκG hκH, lt_min hrG hrH, ?_⟩
  exact interiorBalls_union
    (hG.mono_constants (min_le_left _ _) (min_le_left _ _))
    (hH.mono_constants (min_le_right _ _) (min_le_right _ _))

end MovingSofaStability

end InteriorBalls

/-!
## Interior balls for a Lipschitz roof under a fixed ceiling

This is the elementary geometric ingredient for the middle part of Gerver's
sofa. It does not infer the absence of cusps merely from a piecewise-smooth
parametrization: the horizontal Lipschitz estimate and the positive gap below
the ceiling are explicit hypotheses.
-/

section EpigraphBalls

open Real Set
open MovingSofaOptimality

namespace MovingSofaStability

theorem norm2_le_abs_add (p : Point) : norm2 p ≤ |p.1| + |p.2| := by
  have hs := norm2_sq p
  simp only [dot] at hs
  have hprod := mul_nonneg (abs_nonneg p.1) (abs_nonneg p.2)
  nlinarith [norm2_nonneg p, abs_nonneg p.1, abs_nonneg p.2, sq_abs p.1, sq_abs p.2]

def roofStrip (a b : ℝ) (γ : ℝ → ℝ) : Set Point :=
  {p | p.1 ∈ Icc a b ∧ γ p.1 ≤ p.2 ∧ p.2 ≤ 1}

/-- A low point can be shifted up and toward the farther side to make room for a ball. -/
theorem roofStrip_low_ball {a b H L : ℝ} {γ : ℝ → ℝ}
    (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |γ x - γ y| ≤ L * |x - y|)
    {p : Point} (hp : p ∈ roofStrip a b γ) (hpy : p.2 ≤ (1 + H) / 2)
    {ρ : ℝ} (hρ : 0 < ρ) (hρwidth : ρ ≤ b - a) (hρheight : ρ ≤ (1 - H) / 2) :
    ∃ z, euclideanBall z (ρ / (4 * (L + 2))) ⊆
      roofStrip a b γ ∩ euclideanBall p ρ := by
  let w := ρ / (4 * (L + 2))
  have hw : 0 < w := by dsimp [w]; positivity
  have hwid : 4 * (L + 2) * w = ρ := by
    dsimp [w]
    field_simp
  have hw8 : 8 * w ≤ ρ := by nlinarith
  have hspace : 6 * w ≤ b - a := by linarith
  have hvertical : (3 * L + 3) * w ≤ ρ := by nlinarith
  have hdist : (3 * L + 5) * w ≤ ρ := by nlinarith
  let x := if p.1 ≤ (a + b) / 2 then p.1 + 2 * w else p.1 - 2 * w
  let z : Point := (x, p.2 + (3 * L + 2) * w)
  have hx : |x - p.1| = 2 * w := by
    dsimp [x]
    split_ifs
    · rw [add_sub_cancel_left, abs_of_pos (by positivity)]
    · have he : p.1 - 2 * w - p.1 = -(2 * w) := by ring
      rw [he, abs_neg, abs_of_pos (by positivity)]
  have hxleft : a + w ≤ x := by
    dsimp [x]
    split_ifs with hmid
    · linarith [hp.1.1]
    · have hgt := not_le.mp hmid
      linarith
  have hxright : x + w ≤ b := by
    dsimp [x]
    split_ifs with hmid
    · linarith
    · linarith [hp.1.2]
  refine ⟨z, ?_⟩
  intro q hq
  change euclideanDist z q ≤ w at hq
  have hdx : |z.1 - q.1| ≤ w := (abs_fst_le_norm2 (z - q)).trans hq
  have hdy : |z.2 - q.2| ≤ w := (abs_snd_le_norm2 (z - q)).trans hq
  have hqxl : a ≤ q.1 := by
    have := (abs_le.mp hdx).2
    change x - q.1 ≤ w at this
    linarith
  have hqxr : q.1 ≤ b := by
    have := (abs_le.mp hdx).1
    change -w ≤ x - q.1 at this
    linarith
  have hqx : q.1 ∈ Icc a b := ⟨hqxl, hqxr⟩
  have hqpx : |q.1 - p.1| ≤ 3 * w := by
    have he : q.1 - p.1 = (q.1 - x) + (x - p.1) := by ring
    rw [he]
    have hdx' : |q.1 - x| ≤ w := by simpa only [z, abs_sub_comm] using hdx
    exact (abs_add_le _ _).trans (by rw [hx]; linarith)
  have hglip := hLip q.1 hqx p.1 hp.1
  have hgupper : γ q.1 ≤ γ p.1 + 3 * L * w := by
    have h := (le_abs_self _).trans (hglip.trans
      (mul_le_mul_of_nonneg_left hqpx hL))
    nlinarith
  have hqbottom : γ q.1 ≤ q.2 := by
    have hy := (abs_le.mp hdy).2
    change p.2 + (3 * L + 2) * w - q.2 ≤ w at hy
    nlinarith [hp.2.1]
  have hqtop : q.2 ≤ 1 := by
    have hy := (abs_le.mp hdy).1
    change -w ≤ p.2 + (3 * L + 2) * w - q.2 at hy
    nlinarith
  have hpz : euclideanDist p z ≤ (3 * L + 4) * w := by
    change norm2 (p - z) ≤ _
    have h := norm2_le_abs_add (p - z)
    have he₁ : |p.1 - z.1| = 2 * w := by simpa only [z, abs_sub_comm] using hx
    have he₂ : |p.2 - z.2| = (3 * L + 2) * w := by
      change |p.2 - (p.2 + (3 * L + 2) * w)| = _
      rw [show p.2 - (p.2 + (3 * L + 2) * w) = -((3 * L + 2) * w) by ring,
        abs_neg, abs_of_nonneg (by positivity)]
    simp only [Prod.fst_sub, Prod.snd_sub] at h
    rw [he₁, he₂] at h
    nlinarith
  exact ⟨⟨hqx, hqbottom, hqtop⟩,
    (euclideanDist_triangle p z q).trans (by nlinarith)⟩

/-- The whole epigraph strip has uniform balls when its roof stays below one. -/
theorem roofStrip_hasInteriorBalls {a b H L : ℝ} {γ : ℝ → ℝ}
    (hab : a < b) (hH : H < 1) (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |γ x - γ y| ≤ L * |x - y|)
    (hheight : ∀ x ∈ Icc a b, γ x ≤ H) :
    ∃ κ r₀ : ℝ, 0 < κ ∧ 0 < r₀ ∧ HasInteriorBalls (roofStrip a b γ) κ r₀ := by
  let R : Set Point := Icc a b ×ˢ Icc H 1
  have hR : IsConvexBody R :=
    ⟨⟨(a, H), ⟨⟨le_rfl, hab.le⟩, ⟨le_rfl, hH.le⟩⟩⟩,
      isCompact_Icc.prod isCompact_Icc, (convex_Icc a b).prod (convex_Icc H 1)⟩
  have hRint : (interior R).Nonempty := by
    have hsub : Ioo a b ×ˢ Ioo H 1 ⊆ R := fun p hp =>
      ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
    have hi := interior_maximal hsub (isOpen_Ioo.prod isOpen_Ioo)
    refine ⟨((a + b) / 2, (H + 1) / 2), hi ?_⟩
    constructor <;> constructor <;> dsimp <;> linarith
  have hRE : R ⊆ roofStrip a b γ := by
    intro p hp
    exact ⟨hp.1, (hheight p.1 hp.1).trans hp.2.1, hp.2.2⟩
  obtain ⟨κR, rR, hκR, hrR, hballsR⟩ := convexBody_hasInteriorBalls hR hRint
  let κ := min κR (1 / (4 * (L + 2)))
  let r₀ := min rR (min (b - a) ((1 - H) / 2))
  have hκ : 0 < κ := lt_min hκR (by positivity)
  have hr₀ : 0 < r₀ := lt_min hrR (lt_min (sub_pos.mpr hab) (by linarith))
  refine ⟨κ, r₀, hκ, hr₀, ?_⟩
  intro p hp ρ hρ hρmax
  by_cases hlow : p.2 ≤ (1 + H) / 2
  · obtain ⟨z, hz⟩ := roofStrip_low_ball hL hLip hp hlow hρ
      (hρmax.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (hρmax.trans ((min_le_right _ _).trans (min_le_right _ _)))
    refine ⟨z, ?_⟩
    intro q hq
    apply hz
    have hk := mul_le_mul_of_nonneg_right (min_le_right κR (1 / (4 * (L + 2)))) hρ.le
    have he : 1 / (4 * (L + 2)) * ρ = ρ / (4 * (L + 2)) := by ring
    exact hq.trans (hk.trans_eq he)
  · have hpR : p ∈ R := ⟨hp.1, by constructor <;> linarith [hp.2.2, not_le.mp hlow]⟩
    obtain ⟨z, hz⟩ := hballsR p hpR ρ hρ (hρmax.trans (min_le_left _ _))
    refine ⟨z, ?_⟩
    intro q hq
    have hqR := hz (hq.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hρ.le))
    exact ⟨hRE hqR.1, hqR.2⟩

end MovingSofaStability

end EpigraphBalls

/-!
## Lipschitz roof graphs from monotone boundary arcs

Finite exceptional sets of phase junctions are allowed. The derivative condition
controls vertical displacement by horizontal displacement; this supplies a graph
rather than assuming one from a picture.
-/

section CurveRoof

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

def VerticalSlopeBound (Γ : Set Point) (L : ℝ) : Prop :=
  ∀ p ∈ Γ, ∀ q ∈ Γ, |p.2 - q.2| ≤ L * |p.1 - q.1|

/-- A derivative cone controls all chords, even across finitely many junctions. -/
theorem scalar_graph_slope {a b L : ℝ} {X Y dX dY : ℝ → ℝ} {F : Set ℝ}
    (hF : F.Finite) (hX : ContinuousOn X (Icc a b)) (hY : ContinuousOn Y (Icc a b))
    (hdX : ∀ t ∈ Ioo a b, t ∉ F → HasDerivAt X (dX t) t)
    (hdY : ∀ t ∈ Ioo a b, t ∉ F → HasDerivAt Y (dY t) t)
    (hpos : ∀ t ∈ Ioo a b, t ∉ F → 0 ≤ dX t)
    (hcone : ∀ t ∈ Ioo a b, t ∉ F → |dY t| ≤ L * dX t) :
    ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |Y u - Y v| ≤ L * |X u - X v| := by
  have hmono := env_monotoneOn hF hX hdX hpos
  have hplus : MonotoneOn (fun t => L * X t + Y t) (Icc a b) := by
    apply env_monotoneOn hF (hX.const_mul L |>.add hY)
      (fun t ht he => ((hdX t ht he).const_mul L).add (hdY t ht he))
    intro t ht he
    have h := (abs_le.mp (hcone t ht he)).1
    linarith
  have hminus : MonotoneOn (fun t => L * X t - Y t) (Icc a b) := by
    apply env_monotoneOn hF (hX.const_mul L |>.sub hY)
      (fun t ht he => ((hdX t ht he).const_mul L).sub (hdY t ht he))
    intro t ht he
    have h := (abs_le.mp (hcone t ht he)).2
    linarith
  have ordered : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v →
      |Y u - Y v| ≤ L * |X u - X v| := by
    intro u hu v hv huv
    have hm := hmono hu hv huv
    have hp := hplus hu hv huv
    have hn := hminus hu hv huv
    rw [abs_of_nonpos (sub_nonpos.mpr hm)]
    apply abs_le.mpr
    constructor <;> nlinarith
  intro u hu v hv
  rcases le_total u v with huv | hvu
  · exact ordered u hu v hv huv
  · simpa only [abs_sub_comm] using ordered v hv u hu hvu

theorem VerticalSlopeBound.mono_constant {Γ : Set Point} {L C : ℝ}
    (h : VerticalSlopeBound Γ L) (hLC : L ≤ C) : VerticalSlopeBound Γ C := by
  intro p hp q hq
  exact (h p hp q hq).trans (mul_le_mul_of_nonneg_right hLC (abs_nonneg _))

/-- Two graphs meeting at one separating vertical line retain a common slope bound. -/
theorem verticalSlopeBound_join {Γ₁ Γ₂ : Set Point} {z : Point} {L : ℝ}
    (h₁ : VerticalSlopeBound Γ₁ L) (h₂ : VerticalSlopeBound Γ₂ L)
    (hz₁ : z ∈ Γ₁) (hz₂ : z ∈ Γ₂)
    (hleft : ∀ p ∈ Γ₁, p.1 ≤ z.1) (hright : ∀ p ∈ Γ₂, z.1 ≤ p.1) :
    VerticalSlopeBound (Γ₁ ∪ Γ₂) L := by
  have cross_bound : ∀ p ∈ Γ₁, ∀ q ∈ Γ₂, |p.2 - q.2| ≤ L * |p.1 - q.1| := by
    intro p hp q hq
    have hl := hleft p hp
    have hr := hright q hq
    have hA := h₁ p hp z hz₁
    have hB := h₂ z hz₂ q hq
    rw [abs_of_nonpos (sub_nonpos.mpr hl)] at hA
    rw [abs_of_nonpos (sub_nonpos.mpr hr)] at hB
    rw [abs_of_nonpos (sub_nonpos.mpr (hl.trans hr))]
    have ht := abs_add_le (p.2 - z.2) (z.2 - q.2)
    rw [sub_add_sub_cancel] at ht
    nlinarith
  intro p hp q hq
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact h₁ p hp q hq
  · exact cross_bound p hp q hq
  · simpa only [abs_sub_comm] using cross_bound q hq p hp
  · exact h₂ p hp q hq

/-- A vertically Lipschitz set has at most one point over each abscissa. -/
theorem eq_of_same_abscissa {Γ : Set Point} {L : ℝ} (h : VerticalSlopeBound Γ L)
    {p q : Point} (hp : p ∈ Γ) (hq : q ∈ Γ) (he : p.1 = q.1) : p = q := by
  have hh := h p hp q hq
  rw [he, sub_self, abs_zero, mul_zero] at hh
  have hy : p.2 = q.2 := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))
  exact Prod.ext he hy

/-- A curve with all abscissas and a chord-slope bound is a genuine Lipschitz graph. -/
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
    have he : (hcover x hx).choose = (x, γ x) := by
      apply Prod.ext
      · exact hpx
      · simp only [γ, hx, ↓reduceDIte]
    rwa [he] at hp
  refine ⟨γ, ?_, ?_⟩
  · intro p
    constructor
    · intro hp
      have hx := hrange p hp
      have he := eq_of_same_abscissa hLip hp (graph_mem p.1 hx) rfl
      exact ⟨hx, congrArg Prod.snd he⟩
    · rintro ⟨hx, hy⟩
      have he : p = (p.1, γ p.1) := Prod.ext rfl hy
      rw [he]
      exact graph_mem p.1 hx
  · intro x hx y hy
    exact hLip (x, γ x) (graph_mem x hx) (y, γ y) (graph_mem y hy)

end MovingSofaStability

end CurveRoof

/-!
## The niche envelope has a finite vertical slope bound

The two tails have slope at most two when their angles stay within a quarter
turn of the floor. On the compact middle arc, the negative horizontal speed has
a positive minimum. The three bounds are joined at the actual matching
endpoints.
-/

section EnvelopeSlope

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

section Envelope

variable {t₁ t₂ t₃ t₄ sA sC : ℝ} {x : ℝ → Point} {α β ρA ρC : ℝ → ℝ}
variable (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC)
-- The statements below do not mention `h`, so it is included explicitly.
include h

theorem envelope_left_slope (ht₂ : t₂ < π / 4) :
    VerticalSlopeBound (envD x β '' Icc 0 t₂) 2 := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  have hθ : t₂ ∈ Ioo 0 (π / 4) := ⟨h1.trans h12, ht₂⟩
  have hc : ContinuousOn (envD x β) (Icc 0 t₂) :=
    (env_D_cont h).mono (Icc_subset_Icc le_rfl (by linarith))
  have hs := scalar_graph_slope (L := 2) (env_bp_finite t₁ t₂ t₃ t₄) hc.fst hc.snd
    (dX := fun t => (1 - ρC t) * cos t) (dY := fun t => (1 - ρC t) * sin t)
    (fun t ht he => by
      simpa only [Prod.smul_fst, smul_eq_mul, uvec_fst] using
        hasDerivAt_fst (h.D_deriv t ⟨ht.1, by linarith [ht.2]⟩ he))
    (fun t ht he => by
      simpa only [Prod.smul_snd, smul_eq_mul, uvec_snd] using
        hasDerivAt_snd (h.D_deriv t ⟨ht.1, by linarith [ht.2]⟩ he))
    (fun t ht _ => by
      have hp : 0 ≤ 1 - ρC t := by linarith [h.ρC_lt t ⟨ht.1.le, ht.2.le⟩]
      have hcos := cos_ge_half_of_small hθ ⟨ht.1.le, ht.2.le⟩
      exact mul_nonneg hp (by linarith))
    (fun t ht _ => by
      have hp : 0 ≤ 1 - ρC t := by linarith [h.ρC_lt t ⟨ht.1.le, ht.2.le⟩]
      have hsin : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith [ht.2, pi_pos])
      have hcos := cos_ge_half_of_small hθ ⟨ht.1.le, ht.2.le⟩
      rw [abs_of_nonneg (mul_nonneg hp hsin)]
      have hm := mul_le_mul_of_nonneg_left (show sin t ≤ 2 * cos t by linarith [sin_le_one t]) hp
      nlinarith)
  rintro p ⟨u, hu, rfl⟩ q ⟨v, hv, rfl⟩
  exact hs u hu v hv

theorem envelope_right_slope (ht₃ : π / 4 < t₃) :
    VerticalSlopeBound (envB x α '' Icc t₃ (π / 2)) 2 := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  have hsφ : π / 2 - t₃ ∈ Ioo 0 (π / 4) := ⟨by linarith, by linarith⟩
  have hc : ContinuousOn (envB x α) (Icc t₃ (π / 2)) :=
    (env_B_cont h).mono (Icc_subset_Icc (by linarith) le_rfl)
  have hs := scalar_graph_slope (L := 2) (env_bp_finite t₁ t₂ t₃ t₄) hc.fst hc.snd
    (dX := fun t => (1 - ρA t) * sin t) (dY := fun t => -(1 - ρA t) * cos t)
    (fun t ht he => by
      convert hasDerivAt_fst (h.B_deriv t ⟨by linarith [ht.1], ht.2⟩ he) using 1
      simp only [Prod.smul_fst, smul_eq_mul, vvec_fst]
      ring)
    (fun t ht he => by
      convert hasDerivAt_snd (h.B_deriv t ⟨by linarith [ht.1], ht.2⟩ he) using 1
      simp only [Prod.smul_snd, smul_eq_mul, vvec_snd]
      ring)
    (fun t ht _ => by
      have hp : 0 ≤ 1 - ρA t := by linarith [h.ρA_lt t ⟨ht.1.le, ht.2.le⟩]
      exact mul_nonneg hp
        (sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht.2, pi_pos])))
    (fun t ht _ => by
      have hp : 0 ≤ 1 - ρA t := by linarith [h.ρA_lt t ⟨ht.1.le, ht.2.le⟩]
      have hcos : 0 ≤ cos t := cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, pi_pos], ht.2.le⟩
      have hsin := cos_ge_half_of_small hsφ
        (t := π / 2 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
      rw [cos_pi_div_two_sub] at hsin
      rw [neg_mul, abs_neg, abs_of_nonneg (mul_nonneg hp hcos)]
      have hm := mul_le_mul_of_nonneg_left (show cos t ≤ 2 * sin t by linarith [cos_le_one t]) hp
      nlinarith)
  rintro p ⟨u, hu, rfl⟩ q ⟨v, hv, rfl⟩
  exact hs u hu v hv

/-- The middle arc is a Lipschitz graph because its horizontal speed is uniformly nonzero. -/
theorem envelope_core_slope :
    ∃ L : ℝ, 0 ≤ L ∧ VerticalSlopeBound (x '' Icc t₁ t₄) L := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  have hsub : Icc t₁ t₄ ⊆ Icc 0 (π / 2) := Icc_subset_Icc h1.le h4.le
  let dX : ℝ → ℝ := fun t => -α t * cos t + β t * sin t
  let dY : ℝ → ℝ := fun t => α t * sin t + β t * cos t
  have hdx : ContinuousOn dX (Icc t₁ t₄) :=
    ((h.α_cont.mono hsub).neg.mul continuous_cos.continuousOn).add
      ((h.β_cont.mono hsub).mul continuous_sin.continuousOn)
  have hdy : ContinuousOn dY (Icc t₁ t₄) :=
    ((h.α_cont.mono hsub).mul continuous_sin.continuousOn).add
      ((h.β_cont.mono hsub).mul continuous_cos.continuousOn)
  have hpositive : ∀ t ∈ Icc t₁ t₄, 0 < dX t := by
    intro t ht
    have hti : t ∈ Ioo 0 (π / 2) := ⟨h1.trans_le ht.1, ht.2.trans_lt h4⟩
    have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [hti.1, pi_pos], hti.2⟩
    have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi hti.1 (by linarith [hti.2, pi_pos])
    exact add_pos (mul_pos (neg_pos.mpr (h.α_neg t hti)) hc) (mul_pos (h.β_pos t hti) hs)
  obtain ⟨m, hm, hmle⟩ := isCompact_Icc.exists_forall_le' hdx hpositive
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hdy
  let L := (|B| + 1) / m
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hLm : L * m = |B| + 1 := by dsimp [L]; exact div_mul_cancel₀ _ hm.ne'
  have hc := h.x_cont.mono hsub
  have hs := scalar_graph_slope (L := L) (Set.finite_empty : (∅ : Set ℝ).Finite)
    hc.fst.neg hc.snd
    (dX := dX) (dY := dY)
    (fun t ht _ => by
      convert (hasDerivAt_fst (h.x_deriv t ⟨by linarith [ht.1], by linarith [ht.2]⟩)).neg
        using 1
      simp only [dX, Prod.fst_add, Prod.smul_fst, smul_eq_mul, uvec_fst, vvec_fst]
      ring)
    (fun t ht _ => by
      simpa only [dY, Prod.snd_add, Prod.smul_snd, smul_eq_mul, uvec_snd, vvec_snd] using
        hasDerivAt_snd (h.x_deriv t ⟨by linarith [ht.1], by linarith [ht.2]⟩))
    (fun t ht _ => (hpositive t ⟨ht.1.le, ht.2.le⟩).le)
    (fun t ht _ => by
      have hbnd : |dY t| ≤ B := by simpa only [Real.norm_eq_abs] using hB t ⟨ht.1.le, ht.2.le⟩
      have hbnd' : |dY t| ≤ |B| + 1 := by linarith [le_abs_self B]
      have hprod := mul_le_mul_of_nonneg_left (hmle t ⟨ht.1.le, ht.2.le⟩) hL
      rw [hLm] at hprod
      exact hbnd'.trans hprod)
  refine ⟨L, hL, ?_⟩
  rintro p ⟨u, hu, rfl⟩ q ⟨v, hv, rfl⟩
  simpa only [Pi.neg_apply, neg_sub_neg, abs_sub_comm] using hs u hu v hv

/-- The whole three-piece envelope inherits a single finite slope bound. -/
theorem envelope_slope_bound (ht₂ : t₂ < π / 4) (ht₃ : π / 4 < t₃) :
    ∃ L : ℝ, 0 ≤ L ∧ VerticalSlopeBound (envCurve t₁ t₂ t₃ t₄ x α β) L := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  obtain ⟨L₀, hL₀, hcore⟩ := envelope_core_slope h
  let L := max 2 L₀
  let D := envD x β '' Icc 0 t₂
  let C := x '' Icc t₁ t₄
  let B := envB x α '' Icc t₃ (π / 2)
  have hD : VerticalSlopeBound D L :=
    (envelope_left_slope h ht₂).mono_constant (le_max_left _ _)
  have hC : VerticalSlopeBound C L := hcore.mono_constant (le_max_right _ _)
  have hB : VerticalSlopeBound B L :=
    (envelope_right_slope h ht₃).mono_constant (le_max_left _ _)
  have hzD : x t₄ ∈ D := ⟨t₂, ⟨by linarith, le_rfl⟩, h.D_t₂⟩
  have hzC : x t₄ ∈ C := ⟨t₄, ⟨by linarith, le_rfl⟩, rfl⟩
  have hdmax : ∀ p ∈ D, p.1 ≤ (x t₄).1 := by
    rintro p ⟨t, ht, rfl⟩
    have he := (env_D₁_strictMono h).monotoneOn ht ⟨by linarith, le_rfl⟩ ht.2
    simpa only [h.D_t₂] using he
  have hcmin : ∀ p ∈ C, (x t₄).1 ≤ p.1 := by
    rintro p ⟨t, ht, rfl⟩
    exact (env_x₁_strictAnti h).antitoneOn ht ⟨by linarith, le_rfl⟩ ht.2
  have hDC := verticalSlopeBound_join hD hC hzD hzC hdmax hcmin
  have hzDC : x t₁ ∈ D ∪ C := Or.inr ⟨t₁, ⟨le_rfl, by linarith⟩, rfl⟩
  have hzB : x t₁ ∈ B := ⟨t₃, ⟨le_rfl, by linarith⟩, h.B_t₃⟩
  have hdcmax : ∀ p ∈ D ∪ C, p.1 ≤ (x t₁).1 := by
    intro p hp
    rcases hp with hp | ⟨t, ht, rfl⟩
    · exact (hdmax p hp).trans (envelope_endpoint_order h).2.1.le
    · exact (env_x₁_strictAnti h).antitoneOn ⟨le_rfl, by linarith⟩ ht ht.1
  have hbmin : ∀ p ∈ B, (x t₁).1 ≤ p.1 := by
    rintro p ⟨t, ht, rfl⟩
    have he := (env_B₁_strictMono h).monotoneOn ⟨le_rfl, by linarith⟩ ht ht.1
    simpa only [h.B_t₃] using he
  have hj := verticalSlopeBound_join hDC hB hzDC hzB hdcmax hbmin
  have he : (D ∪ C) ∪ B = envCurve t₁ t₂ t₃ t₄ x α β := by
    ext p
    simp only [D, C, B, envCurve, mem_union]
    tauto
  refine ⟨L, (show (0 : ℝ) ≤ 2 by norm_num).trans (le_max_left _ _), ?_⟩
  rwa [he] at hj

end Envelope

end MovingSofaStability

end EnvelopeSlope

/-!
## Geometric consequences of a cap with a Lipschitz niche roof

`CapRoofData` records concrete boundary geometry; it does not assume a stability
estimate. The nonconvex set is decomposed into two convex wings and a
positive-height epigraph strip, and its uniform interior-ball property is proved
from that decomposition.
-/

section RoofGeometry

open Real Set
open MovingSofaOptimality

namespace MovingSofaStability

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

/-- Fill downward below a horizontal chord of a cap. -/
theorem cap_horizontal_rectangle {K : Set Point} (hK : IsCap K (π / 2))
    {a b h : ℝ} (hab : a < b) (ha : (a, h) ∈ K) (hb : (b, h) ∈ K) :
    Icc a b ×ˢ Icc (0 : ℝ) h ⊆ K := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  let c := (x - a) / (b - a)
  have hba : 0 < b - a := sub_pos.mpr hab
  have hc : c ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hx.1) hba.le,
      (div_le_one hba).2 (by linarith [hx.2])⟩
  have htop := hK.2.1.2.2.add_smul_sub_mem ha hb hc
  have he : (a, h) + c • ((b, h) - (a, h)) = (x, h) := by
    apply Prod.ext
    · dsimp [c]
      field_simp [hba.ne']
      ring
    · simp
  rw [he] at htop
  exact opt_cap_down hK htop hy.1 hy.2

/-- A nondegenerate box inside a set witnesses nonempty interior. -/
theorem interior_nonempty_of_box {C : Set Point} {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hbox : Icc a b ×ˢ Icc c d ⊆ C) :
    (interior C).Nonempty := by
  have hi : Ioo a b ×ˢ Ioo c d ⊆ C := fun p hp =>
    hbox ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  have hint := interior_maximal hi (isOpen_Ioo.prod isOpen_Ioo)
  refine ⟨((a + b) / 2, (c + d) / 2), hint ?_⟩
  constructor <;> constructor <;> dsimp <;> linarith

def leftWing (K : Set Point) (a : ℝ) : Set Point := K ∩ {p | p.1 ≤ a}
def rightWing (K : Set Point) (b : ℝ) : Set Point := K ∩ {p | b ≤ p.1}

/-- The two wings are genuinely two-dimensional convex bodies. -/
theorem CapRoofData.wings {K : Set Point} {a b H L : ℝ} {γ : ℝ → ℝ}
    (h : CapRoofData K a b H L γ) :
    (IsConvexBody (leftWing K a) ∧ (interior (leftWing K a)).Nonempty) ∧
      (IsConvexBody (rightWing K b) ∧ (interior (rightWing K b)).Nonempty) := by
  have hleft : (a, 1) ∈ K := h.rectangle ⟨⟨le_rfl, h.order.le⟩, ⟨by norm_num, le_rfl⟩⟩
  have hright : (b, 1) ∈ K := h.rectangle ⟨⟨h.order.le, le_rfl⟩, ⟨by norm_num, le_rfl⟩⟩
  let l := -supp K π
  let r := supp K 0
  have hll : l < a := h.left_wing
  have hrr : b < r := h.right_wing
  have hmidL : ((l + a) / 2, (1 / 2 : ℝ)) ∈ K := by
    have hh := h.cap.2.1.2.2 (opt_cap_C_mem h.cap) hleft
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    convert hh using 1
    ext <;> simp only [l, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
  have hmidR : ((b + r) / 2, (1 / 2 : ℝ)) ∈ K := by
    have hh := h.cap.2.1.2.2 hright (opt_cap_A_mem h.cap)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    convert hh using 1
    ext <;> simp only [r, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
  have hboxL : Icc ((l + a) / 2) a ×ˢ Icc (0 : ℝ) (1 / 2) ⊆ leftWing K a := by
    have hh := cap_horizontal_rectangle h.cap (by linarith : (l + a) / 2 < a)
      hmidL (opt_cap_down h.cap hleft (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    exact fun p hp => ⟨hh hp, hp.1.2⟩
  have hboxR : Icc b ((b + r) / 2) ×ˢ Icc (0 : ℝ) (1 / 2) ⊆ rightWing K b := by
    have hh := cap_horizontal_rectangle h.cap (by linarith : b < (b + r) / 2)
      (opt_cap_down h.cap hright (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)) hmidR
    exact fun p hp => ⟨hh hp, hp.1.1⟩
  have hLi := interior_nonempty_of_box (by linarith : (l + a) / 2 < a)
    (by norm_num : (0 : ℝ) < 1 / 2) hboxL
  have hRi := interior_nonempty_of_box (by linarith : b < (b + r) / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) hboxR
  have hLc : IsCompact (leftWing K a) :=
    h.cap.2.1.2.1.of_isClosed_subset
      (h.cap.2.1.2.1.isClosed.inter (isClosed_le continuous_fst continuous_const)) inter_subset_left
  have hRc : IsCompact (rightWing K b) :=
    h.cap.2.1.2.1.of_isClosed_subset
      (h.cap.2.1.2.1.isClosed.inter (isClosed_le continuous_const continuous_fst)) inter_subset_left
  have hLv : Convex ℝ (leftWing K a) := by
    have hh := h.cap.2.1.2.2.inter (convex_halfMinus 0 a)
    simpa only [leftWing, halfMinus, dot_uvec_zero] using hh
  have hRv : Convex ℝ (rightWing K b) := by
    have hh := h.cap.2.1.2.2.inter (convex_halfPlus 0 b)
    simpa only [rightWing, halfPlus, dot_uvec_zero] using hh
  exact ⟨⟨⟨hLi.mono interior_subset, hLc, hLv⟩, hLi⟩,
    ⟨⟨hRi.mono interior_subset, hRc, hRv⟩, hRi⟩⟩

/-- The nonconvex shape is exactly its two wings and its roof strip. -/
theorem CapRoofData.shape_decomposition {K : Set Point} {a b H L : ℝ} {γ : ℝ → ℝ}
    (h : CapRoofData K a b H L γ) :
    capShape K = (leftWing K a ∪ roofStrip a b γ) ∪ rightWing K b := by
  ext p
  constructor
  · rintro ⟨hp, hn⟩
    by_cases ha : p.1 ≤ a
    · exact Or.inl (Or.inl ⟨hp, ha⟩)
    by_cases hb : b ≤ p.1
    · exact Or.inr ⟨hp, hb⟩
    have hx : p.1 ∈ Icc a b := ⟨(not_le.mp ha).le, (not_le.mp hb).le⟩
    have hy : γ p.1 ≤ p.2 := by
      by_contra hbad
      apply hn
      rw [h.niche_eq]
      exact ⟨hx, h.cap.snd_nonneg hp, not_le.mp hbad⟩
    exact Or.inl (Or.inr ⟨hx, hy, h.cap.snd_le_one hp⟩)
  · rintro ((hp | hp) | hp)
    · refine ⟨hp.1, ?_⟩
      rw [h.niche_eq]
      rintro ⟨hx, hy, hγ⟩
      have he : p.1 = a := le_antisymm hp.2 hx.1
      rw [he, h.left_zero] at hγ
      linarith
    · have hpK := h.rectangle ⟨hp.1, (h.roof_nonneg p.1 hp.1).trans hp.2.1, hp.2.2⟩
      refine ⟨hpK, ?_⟩
      rw [h.niche_eq]
      rintro ⟨-, -, hy⟩
      exact (not_lt_of_ge hp.2.1) hy
    · refine ⟨hp.1, ?_⟩
      rw [h.niche_eq]
      rintro ⟨hx, hy, hγ⟩
      have he : p.1 = b := le_antisymm hx.2 hp.2
      rw [he, h.right_zero] at hγ
      linarith

/-- The uniform interior-ball property follows from concrete cap/roof data. -/
theorem CapRoofData.interiorBalls {K : Set Point} {a b H L : ℝ} {γ : ℝ → ℝ}
    (h : CapRoofData K a b H L γ) :
    ∃ κ r₀ : ℝ, 0 < κ ∧ 0 < r₀ ∧ HasInteriorBalls (capShape K) κ r₀ := by
  obtain ⟨hL, hR⟩ := h.wings
  have left := convexBody_hasInteriorBalls hL.1 hL.2
  have middle := roofStrip_hasInteriorBalls h.order h.height h.slope_nonneg h.roof_lipschitz h.roof_le
  have right := convexBody_hasInteriorBalls hR.1 hR.2
  rw [h.shape_decomposition]
  exact exists_interiorBalls_union (exists_interiorBalls_union left middle) right

end MovingSofaStability

end RoofGeometry

/-!
## Gerver's reference roof and uniform interior balls

All reference geometry is derived from the existing Gerver envelope, contact and
injectivity theorems. The two convex wings have positive width because the cap
has no vertical supporting faces.
-/

section GerverRoof

open Real Set
open MovingSofaOptimality MovingSofaUniqueness
open GerverParams

namespace MovingSofaStability

def gerverRoofLeft (P : GerverParams) : ℝ := (envD P.path P.gs_β 0).1

def gerverRoofRight (P : GerverParams) : ℝ := (envB P.path P.gs_α (π / 2)).1

def gerverEnvelope (P : GerverParams) : Set Point :=
  envCurve P.φ P.θ (π / 2 - P.θ) (π / 2 - P.φ) P.path P.gs_α P.gs_β

theorem gerver_cap_explicit {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    P.cap = P.gs_K := (gs_monotone_K hP (romik_bounds hP hbox)).2

theorem gerver_shape_eq {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    capShape P.cap = gerverSofa P := by
  rw [capShape, gerver_cap_explicit hP hbox]
  exact (gs_gerverSofa_eq hP (romik_bounds hP hbox)).symm

theorem gerver_niche_envelope {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    niche P.cap (π / 2) = envUnderStrict (gerverEnvelope P) := by
  rw [gerver_cap_explicit hP hbox]
  exact gerver_niche_eq_envUnderStrict hP (romik_bounds hP hbox)

/-- A top point cannot lie on either vertical supporting face when those faces are points. -/
theorem cap_top_strict_between_floor_endpoints {K : Set Point}
    (hK : IsCap K (π / 2)) (h1 : InjCond1 K) {a : ℝ} (ha : (a, 1) ∈ K) :
    -supp K π < a ∧ a < supp K 0 := by
  have hb := opt_cap_fst_le hK ha
  have hleft : vplus K π = vminus K π := by
    have h := ((proposition6_4_5 hK h1).2 (π / 2) ⟨by positivity, le_rfl⟩).1
    simpa only [cPlus, cMinus, add_halves] using h
  have hright : vplus K 0 = vminus K 0 :=
    ((proposition6_4_5 hK h1).1 0 ⟨le_rfl, by positivity⟩).1
  constructor
  · apply lt_of_le_of_ne hb.1
    intro he
    have hp : (a, 1) ∈ edge K π := by
      refine ⟨ha, ?_⟩
      change dot (a, 1) (uvec π) = supp K π
      simp only [dot, uvec_pi]
      linarith
    rw [edge_eq_segment hK.2.1 π, ← hleft, opt_cap_vplus_pi hK, segment_same] at hp
    have hs := congrArg Prod.snd (mem_singleton_iff.mp hp)
    norm_num at hs
  · apply lt_of_le_of_ne hb.2
    intro he
    have hp : (a, 1) ∈ edge K 0 := by
      refine ⟨ha, ?_⟩
      change dot (a, 1) (uvec 0) = supp K 0
      simpa only [uvec_zero, dot, mul_one, mul_zero, add_zero] using he
    rw [edge_eq_segment hK.2.1 0, hright, (inj_cap_consecutive hK).1, segment_same] at hp
    have hs := congrArg Prod.snd (mem_singleton_iff.mp hp)
    norm_num at hs

/-- Gerver's niche is the region under a nonnegative, finite-slope roof strictly below one. -/
theorem gerver_roof_data {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ H L : ℝ, ∃ γ : ℝ → ℝ,
      CapRoofData P.cap (gerverRoofLeft P) (gerverRoofRight P) H L γ := by
  have hB := romik_bounds hP hbox
  have henv := gn_envHyp hP hB
  have hc : IsCap P.cap (π / 2) := gm_isCap hP hbox
  have hI : InjCond1 P.cap := (theorem6_1_2 hP hbox).1
  have hheight : ∀ t ∈ Icc (0 : ℝ) (π / 2), (P.path t).2 < 1 :=
    fun t ht => path_snd_lt_one hP hB ht.1 ht.2
  have hΓc : IsCompact (gerverEnvelope P) := envelope_isCompact henv
  have hΓbounds : ∀ p ∈ gerverEnvelope P,
      p.1 ∈ Icc (gerverRoofLeft P) (gerverRoofRight P) ∧ p.2 ∈ Ico (0 : ℝ) 1 :=
    envelope_bounds_of_path_height henv hheight
  have hcover : ∀ x ∈ Icc (gerverRoofLeft P) (gerverRoofRight P),
      ∃ p ∈ gerverEnvelope P, p.1 = x := fun x hx => env_exists_curve_fst henv hx
  have hθ : P.θ < π / 4 := by linarith [henv.ht.2.2.1]
  obtain ⟨L, hL, hSlope⟩ := envelope_slope_bound henv hθ (by linarith)
  obtain ⟨γ, hgraph, hLip⟩ := exists_roof_function
    (fun p hp => (hΓbounds p hp).1) hcover hSlope
  have hDmem : envD P.path P.gs_β 0 ∈ gerverEnvelope P :=
    Or.inr ⟨0, ⟨le_rfl, (henv.ht.1.trans henv.ht.2.1).le⟩, rfl⟩
  have hBmem : envB P.path P.gs_α (π / 2) ∈ gerverEnvelope P :=
    Or.inl (Or.inl ⟨π / 2, ⟨by linarith [henv.ht.2.2.2.1, henv.ht.2.2.2.2], le_rfl⟩, rfl⟩)
  obtain ⟨pmax, hpmax, hmax⟩ := hΓc.exists_isMaxOn ⟨_, hDmem⟩ continuous_snd.continuousOn
  let H := pmax.2
  have hH : H < 1 := (hΓbounds pmax hpmax).2.2
  have hγmem : ∀ x ∈ Icc (gerverRoofLeft P) (gerverRoofRight P), (x, γ x) ∈ gerverEnvelope P :=
    fun x hx => (hgraph (x, γ x)).2 ⟨hx, rfl⟩
  have hγnonneg : ∀ x ∈ Icc (gerverRoofLeft P) (gerverRoofRight P), 0 ≤ γ x :=
    fun x hx => (hΓbounds (x, γ x) (hγmem x hx)).2.1
  have hγheight : ∀ x ∈ Icc (gerverRoofLeft P) (gerverRoofRight P), γ x ≤ H :=
    fun x hx => hmax (hγmem x hx)
  have hγa : γ (gerverRoofLeft P) = 0 := by
    have h := ((hgraph _).1 hDmem).2
    rw [henv.D_end] at h
    exact h.symm
  have hγb : γ (gerverRoofRight P) = 0 := by
    have h := ((hgraph _).1 hBmem).2
    rw [henv.B_end] at h
    exact h.symm
  obtain ⟨ho1, ho2, ho3⟩ := envelope_endpoint_order henv
  have hab : gerverRoofLeft P < gerverRoofRight P := ho1.trans (ho2.trans ho3)
  have ha : (gerverRoofLeft P, 1) ∈ P.cap := by
    rw [gerver_cap_explicit hP hbox]
    have h := gs_C_mem_K hP hB (τ := 0) le_rfl (by positivity)
    rwa [gerver_contactC_zero hP hB] at h
  have hb : (gerverRoofRight P, 1) ∈ P.cap := by
    rw [gerver_cap_explicit hP hbox]
    have h := gs_A_mem_K hP hB (τ := π / 2) (by positivity) le_rfl
    rwa [gerver_contactA_pi_div_two hP hB] at h
  have hn : niche P.cap (π / 2) =
      {p : Point | p.1 ∈ Icc (gerverRoofLeft P) (gerverRoofRight P) ∧
        0 ≤ p.2 ∧ p.2 < γ p.1} := by
    rw [gerver_niche_envelope hP hbox]
    ext p
    constructor
    · rintro ⟨hpy, q, hq, hqx, hpq⟩
      obtain ⟨hx, hy⟩ := (hgraph q).1 hq
      rw [hqx] at hx
      rw [hy, hqx] at hpq
      exact ⟨hx, hpy, hpq⟩
    · rintro ⟨hx, hpy, hy⟩
      exact ⟨hpy, (p.1, γ p.1), hγmem p.1 hx, rfl, hy⟩
  exact ⟨H, L, γ, hc, hab, (cap_top_strict_between_floor_endpoints hc hI ha).1,
    (cap_top_strict_between_floor_endpoints hc hI hb).2, hH, hL,
    hγnonneg, hγheight, hLip, hγa, hγb, cap_horizontal_rectangle hc hab ha hb, hn⟩

/-- The actual nonconvex Gerver sofa satisfies the uniform interior-ball condition. -/
theorem gerver_interiorBalls {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ κ r₀ : ℝ, 0 < κ ∧ 0 < r₀ ∧ HasInteriorBalls (gerverSofa P) κ r₀ := by
  obtain ⟨H, L, γ, hroof⟩ := gerver_roof_data hP hbox
  have h := hroof.interiorBalls
  rwa [gerver_shape_eq hP hbox] at h

end MovingSofaStability

end GerverRoof

/-!
## Quantitative roof margins and approximate hallway recovery

The smaller set may violate the omitted full-angle constraints by a controlled
slack. It is not assumed to lie in its full-angle cap shape. A positive
reference roof margin converts this slack into an actual point of the reference
sofa.
-/

section RoofMargins

open Real Set
open MovingSofaOptimality

namespace MovingSofaStability

/-- Unpinned cap support control extends to the lower semicircle as well. -/
theorem upperSupportClose_all {δ : ℝ} {K L : Set Point}
    (hK : IsCap K (π / 2)) (hL : IsCap L (π / 2))
    (h : UpperSupportClose δ K L) : ∀ t, |supp K t - supp L t| ≤ δ := by
  intro t
  by_cases hs : 0 ≤ sin t
  · obtain ⟨s, hsi, hu, -⟩ := upper_normal_representative t hs
    have hK' : supp K s = supp K t := by simp only [supp, hu]
    have hL' : supp L s = supp L t := by simp only [supp, hu]
    simpa only [hK', hL'] using h s hsi
  have hs' := (not_le.mp hs).le
  by_cases hc : 0 ≤ cos t
  · rw [cap_lower_right_support hK hs' hc, cap_lower_right_support hL hs' hc,
      ← sub_mul, abs_mul]
    exact ((mul_le_mul_of_nonneg_left (abs_cos_le_one t) (abs_nonneg _)).trans_eq
      (mul_one _)).trans (h 0 ⟨le_rfl, pi_pos.le⟩)
  · rw [cap_lower_left_support hK hs' (not_le.mp hc).le,
      cap_lower_left_support hL hs' (not_le.mp hc).le]
    have he : -supp K π * cos t - -supp L π * cos t = -(supp K π - supp L π) * cos t := by ring
    rw [he, abs_mul, abs_neg]
    exact ((mul_le_mul_of_nonneg_left (abs_cos_le_one t) (abs_nonneg _)).trans_eq
      (mul_one _)).trans (h π ⟨pi_pos.le, le_rfl⟩)

theorem upperSupportClose_euclidean {δ : ℝ} (hδ : 0 ≤ δ) {K L : Set Point}
    (hK : IsCap K (π / 2)) (hL : IsCap L (π / 2)) (h : UpperSupportClose δ K L) :
    EuclideanClose δ K L :=
  euclideanClose_of_support_bound hK.2.1 hL.2.1 hδ (upperSupportClose_all hK hL h)

/-- Every roof point belongs to the actual nonconvex reference shape. -/
theorem CapRoofData.roof_mem {K : Set Point} {a b H L : ℝ} {γ : ℝ → ℝ}
    (h : CapRoofData K a b H L γ) {x : ℝ} (hx : x ∈ Icc a b) :
    (x, γ x) ∈ capShape K := by
  refine ⟨h.rectangle ⟨hx, h.roof_nonneg x hx, (h.roof_le x hx).trans h.height.le⟩, ?_⟩
  rw [h.niche_eq]
  rintro ⟨-, -, hh⟩
  exact (lt_irrefl (γ x)) hh

/-- The reference niche has a uniform positive margin from every upper supporting wall. -/
theorem CapRoofData.outer_margin {K : Set Point} {a b H L : ℝ} {γ : ℝ → ℝ}
    (h : CapRoofData K a b H L γ) :
    ∃ d : ℝ, 0 < d ∧ ∀ p ∈ niche K (π / 2), ∀ t ∈ Icc (0 : ℝ) π,
      d ≤ supp K t - dot p (uvec t) := by
  let R : Set Point := Icc a b ×ˢ Icc (0 : ℝ) H
  let F := fun z : Point × ℝ => supp K z.2 - dot z.1 (uvec z.2)
  have hc : Continuous F :=
    (h.cap.2.1.continuous_supp.comp continuous_snd).sub
      (continuous_dot_pair.comp (continuous_fst.prodMk (continuous_uvec.comp continuous_snd)))
  have hpos : ∀ z ∈ R ×ˢ Icc (0 : ℝ) π, 0 < F z := by
    rintro ⟨p, t⟩ ⟨hp, ht⟩
    change p ∈ R at hp
    change t ∈ Icc 0 π at ht
    rcases eq_or_lt_of_le ht.1 with he | ht0
    · subst t
      change 0 < supp K 0 - dot p (uvec 0)
      rw [dot_uvec_zero]
      linarith [hp.1.2, h.right_wing]
    rcases eq_or_lt_of_le ht.2 with he | htπ
    · subst t
      change 0 < supp K π - dot p (uvec π)
      simp only [dot, uvec_pi]
      linarith [hp.1.1, h.left_wing]
    have htop : (p.1, (1 : ℝ)) ∈ K := h.rectangle ⟨hp.1, by norm_num, le_rfl⟩
    have hs := dot_le_supp h.cap.2.1.2.1 htop t
    have hsin : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 htπ
    have hgap : 0 < (1 - p.2) * sin t :=
      mul_pos (by linarith [hp.2.2, h.height]) hsin
    change 0 < supp K t - dot p (uvec t)
    simp only [dot, uvec] at hs ⊢
    nlinarith
  obtain ⟨d, hd, hdle⟩ := ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).exists_forall_le'
    hc.continuousOn hpos
  refine ⟨d, hd, ?_⟩
  intro p hp t ht
  rw [h.niche_eq] at hp
  exact hdle (p, t) ⟨⟨hp.1, hp.2.1, hp.2.2.le.trans (h.roof_le p.1 hp.1)⟩, ht⟩

/-- Primitive wall-margin condition along a reference roof. -/
def RoofSlackMargin (K : Set Point) (γ : ℝ → ℝ) (c τ : ℝ) : Prop :=
  ∀ p ∈ niche K (π / 2), ∃ t ∈ Ioo (0 : ℝ) (π / 2),
    innerSlackU K t p ≤ -min (c * (γ p.1 - p.2)) τ ∧
      innerSlackV K t p ≤ -min (c * (γ p.1 - p.2)) τ

def ApproxHallways (K S : Set Point) (ζ : ℝ) : Prop :=
  ∀ p ∈ S, ∀ t ∈ Ioo (0 : ℝ) (π / 2),
    -ζ ≤ max (innerSlackU K t p) (innerSlackV K t p)

/-- A support perturbation and an approximate hallway bound control the
S-to-reference directed distance, including points outside the full-angle shape. -/
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
  have hC : 0 ≤ max (1 : ℝ) (1 / c) := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hδC : δ ≤ max 1 (1 / c) * (δ + ζ) := by
    have hm := mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) (1 / c)) (add_nonneg hδ hζ)
    nlinarith
  have hcapclose := upperSupportClose_euclidean hδ hK hroof.cap hclose
  intro p hp
  have hpK := hSK hp
  by_cases hp₀ : p ∈ K₀
  · by_cases hpG : p ∈ capShape K₀
    · exact ⟨p, hpG, by simpa only [euclideanDist_self] using mul_nonneg hC (add_nonneg hδ hζ)⟩
    have hpN : p ∈ niche K₀ (π / 2) := by
      by_contra hn
      exact hpG ⟨hp₀, hn⟩
    have hn := hpN
    rw [hroof.niche_eq] at hn
    let depth := γ p.1 - p.2
    have hdpos : 0 < depth := sub_pos.mpr hn.2.2
    obtain ⟨t, ht, hu, hv⟩ := hslack p hpN
    have hU := (abs_le.mp (slackU_support_error hclose
      ⟨ht.1.le, by linarith [ht.2, pi_pos]⟩ p)).2
    have hV := (abs_le.mp (slackV_support_error hclose ⟨ht.1.le, ht.2.le⟩ p)).2
    have hdepth : c * depth ≤ δ + ζ := by
      by_contra he
      have hm : δ + ζ < min (c * depth) τ := lt_min (not_le.mp he) hsmall
      have hu' : innerSlackU K t p < -ζ := by linarith
      have hv' : innerSlackV K t p < -ζ := by linarith
      exact (not_lt_of_ge (hhall p hp t ht)) (max_lt hu' hv')
    let q : Point := (p.1, γ p.1)
    have hq : q ∈ capShape K₀ := hroof.roof_mem hn.1
    have hd : euclideanDist p q = depth := by
      change sqrt ((p.1 - p.1) * (p.1 - p.1) + (p.2 - γ p.1) * (p.2 - γ p.1)) = depth
      rw [sub_self, zero_mul, zero_add, ← pow_two, Real.sqrt_sq_eq_abs,
        abs_of_nonpos (by linarith : p.2 - γ p.1 ≤ 0)]
      dsimp [depth]
      ring
    refine ⟨q, hq, ?_⟩
    rw [hd]
    have hdiv : depth ≤ (δ + ζ) / c := (le_div_iff₀ hc).2 (by nlinarith)
    have hmul := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) (1 / c)) (add_nonneg hδ hζ)
    have he : (1 / c) * (δ + ζ) = (δ + ζ) / c := by ring
    exact hdiv.trans (by simpa only [he] using hmul)
  · obtain ⟨q, hq, hpq⟩ := hcapclose.1 p hpK
    by_cases hqG : q ∈ capShape K₀
    · exact ⟨q, hqG, hpq.trans hδC⟩
    have hqN : q ∈ niche K₀ (π / 2) := by
      by_contra hn
      exact hqG ⟨hq, hn⟩
    have hpinside : p ∈ K₀ := by
      apply (cap_mem_iff_upper hroof.cap p).2
      refine ⟨hK.snd_nonneg hpK, ?_⟩
      intro t ht
      have hproj := dot_uvec_le_norm2 (p - q) t
      rw [dot_sub_left] at hproj
      have hmargin := houter q hqN t ht
      change norm2 (p - q) ≤ δ at hpq
      linarith
    exact (hp₀ hpinside).elim

end MovingSofaStability

end RoofMargins

/-!
## Uniform slack below an envelope roof

The inactive tail wall has a strictly negative slack on its entire compact
parameter interval, including its floor endpoint. The active wall's vertical
coefficient is uniformly positive. This is proved from `EnvHyp`, rather than
assumed as a local error bound.
-/

section EnvelopeSlack

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

theorem innerSlackU_eq_dot (K : Set Point) (t : ℝ) (p : Point) :
    innerSlackU K t p = dot (p - innerCorner K t) (uvec t) := by
  rw [dot_sub_left, proposition2_2_2_innerCorner]
  simp only [dot_add_left, dot_smul_left, dot_uvec_self, dot_vvec_uvec, mul_one,
    mul_zero, add_zero, innerSlackU]
  ring

theorem innerSlackV_eq_dot (K : Set Point) (t : ℝ) (p : Point) :
    innerSlackV K t p = dot (p - innerCorner K t) (vvec t) := by
  rw [dot_sub_left, proposition2_2_2_innerCorner]
  simp only [dot_add_left, dot_smul_left, dot_uvec_vvec, dot_vvec_self, mul_one,
    mul_zero, zero_add, innerSlackV]
  ring

theorem innerSlackU_down (K : Set Point) (t d : ℝ) (q : Point) :
    innerSlackU K t (q.1, q.2 - d) = innerSlackU K t q - d * sin t := by
  simp only [innerSlackU, dot, uvec]
  ring

theorem innerSlackV_down (K : Set Point) (t d : ℝ) (q : Point) :
    innerSlackV K t (q.1, q.2 - d) = innerSlackV K t q - d * cos t := by
  simp only [innerSlackV, dot, vvec]
  ring

section Envelope

variable {t₁ t₂ t₃ t₄ sA sC : ℝ} {x : ℝ → Point} {α β ρA ρC : ℝ → ℝ}
variable (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC)
-- The statements below do not mention `h`, so it is included explicitly.
include h

/-- The path's abscissa decreases even outside the middle exposed arc. -/
theorem envelope_path_fst_strictAnti : StrictAntiOn (fun t => (x t).1) (Icc 0 (π / 2)) := by
  apply env_strictAntiOn (Set.finite_empty : (∅ : Set ℝ).Finite) h.x_cont.fst
    (f' := fun t => α t * cos t - β t * sin t)
  · intro t ht _
    convert hasDerivAt_fst (h.x_deriv t ht) using 1
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, uvec_fst, vvec_fst]
    ring
  · intro t ht _
    have hcos : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩
    have hsin : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
    have h1 := mul_neg_of_neg_of_pos (h.α_neg t ht) hcos
    have h2 := mul_pos (h.β_pos t ht) hsin
    linarith

/-- The inactive tail slacks stay strict at the two floor endpoints as well. -/
theorem envelope_endpoint_speeds : 0 < β 0 ∧ α (π / 2) < 0 := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  obtain ⟨ho1, ho2, ho3⟩ := envelope_endpoint_order h
  have hx1 : (x t₁).1 < (x 0).1 := envelope_path_fst_strictAnti h
    ⟨le_rfl, by positivity⟩ ⟨h1.le, by linarith⟩ h1
  have hx4 : (x (π / 2)).1 < (x t₄).1 := envelope_path_fst_strictAnti h
    ⟨by linarith, h4.le⟩ ⟨by positivity, le_rfl⟩ h4
  have hD : (envD x β 0).1 = (x 0).1 - β 0 := by
    simp [envD, uvec]
  have hB : (envB x α (π / 2)).1 = (x (π / 2)).1 - α (π / 2) := by
    simp [envB, vvec, sub_eq_add_neg]
  rw [hD] at ho1
  rw [hB] at ho3
  constructor <;> linarith

/-- A common positive margin works for all three roof pieces. -/
theorem envelope_downward_slack {K : Set Point}
    (hpath : ∀ t ∈ Icc (0 : ℝ) (π / 2), innerCorner K t = x t) :
    ∃ c τ : ℝ, 0 < c ∧ 0 < τ ∧
      ∀ q ∈ envCurve t₁ t₂ t₃ t₄ x α β, ∀ d : ℝ, 0 < d → 0 ≤ q.2 - d →
        ∃ t ∈ Ioo (0 : ℝ) (π / 2),
          innerSlackU K t (q.1, q.2 - d) ≤ -min (c * d) τ ∧
          innerSlackV K t (q.1, q.2 - d) ≤ -min (c * d) τ := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  obtain ⟨hβ0, hαv⟩ := envelope_endpoint_speeds h
  have hβpos : ∀ t ∈ Icc (0 : ℝ) t₂, 0 < β t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with he | hp
    · simpa only [← he] using hβ0
    · exact h.β_pos t ⟨hp, by linarith [ht.2]⟩
  have hαpos : ∀ t ∈ Icc t₃ (π / 2), 0 < -α t := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with he | hp
    · simpa only [he] using neg_pos.mpr hαv
    · exact neg_pos.mpr (h.α_neg t ⟨by linarith [ht.1], hp⟩)
  obtain ⟨τD, hτD, hD⟩ := isCompact_Icc.exists_forall_le'
    (h.β_cont.mono (Icc_subset_Icc le_rfl (by linarith))) hβpos
  obtain ⟨τB, hτB, hB⟩ := isCompact_Icc.exists_forall_le'
    ((h.α_cont.mono (Icc_subset_Icc (by linarith) le_rfl)).neg) hαpos
  have corepos : ∀ t ∈ Icc t₁ t₄, 0 < min (sin t) (cos t) := by
    intro t ht
    exact lt_min
      (sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, pi_pos]))
      (cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩)
  obtain ⟨cC, hcC, hC⟩ := isCompact_Icc.exists_forall_le'
    (continuous_sin.min continuous_cos).continuousOn corepos
  obtain ⟨cD, hcD, hcos⟩ := isCompact_Icc.exists_forall_le'
    continuous_cos.continuousOn (s := Icc (0 : ℝ) t₂)
    (fun t ht => cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩)
  obtain ⟨cB, hcB, hsin⟩ := isCompact_Icc.exists_forall_le'
    continuous_sin.continuousOn (s := Icc t₃ (π / 2))
    (fun t ht => sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, pi_pos]))
  let c := min cC (min cD cB)
  let τ := min τD τB
  have hc : 0 < c := lt_min hcC (lt_min hcD hcB)
  have hτ : 0 < τ := lt_min hτD hτB
  have hcC' : c ≤ cC := min_le_left _ _
  have hcD' : c ≤ cD := (min_le_right _ _).trans (min_le_left _ _)
  have hcB' : c ≤ cB := (min_le_right _ _).trans (min_le_right _ _)
  have hτD' : τ ≤ τD := min_le_left _ _
  have hτB' : τ ≤ τB := min_le_right _ _
  refine ⟨c, τ, hc, hτ, ?_⟩
  intro q hq d hd hfloor
  rcases hq with (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩
  · have htv : t < π / 2 := lt_of_le_of_ne ht.2 (by
      intro he
      rw [he, h.B_end] at hfloor
      linarith)
    have hti : t ∈ Ioo (0 : ℝ) (π / 2) := ⟨by linarith [ht.1], htv⟩
    have heU : innerSlackU K t (envB x α t) = 0 := by
      rw [innerSlackU_eq_dot, hpath t ⟨hti.1.le, hti.2.le⟩]
      exact env_dot_B_self x α t
    have heV : innerSlackV K t (envB x α t) = α t := by
      rw [innerSlackV_eq_dot, hpath t ⟨hti.1.le, hti.2.le⟩]
      simp [envB, dot_smul_left]
    have hcoef : c ≤ sin t := hcB'.trans (hsin t ht)
    have hinactive : τ ≤ -α t := hτB'.trans (hB t ht)
    have hcos0 : 0 ≤ cos t := cos_nonneg_of_mem_Icc ⟨by linarith [hti.1, pi_pos], ht.2⟩
    refine ⟨t, hti, ?_, ?_⟩
    · rw [innerSlackU_down, heU, zero_sub]
      have hm := mul_le_mul_of_nonneg_left hcoef hd.le
      have hmin := min_le_left (c * d) τ
      nlinarith
    · rw [innerSlackV_down, heV]
      have hp := mul_nonneg hd.le hcos0
      have hmin := min_le_right (c * d) τ
      linarith
  · have hti : t ∈ Ioo (0 : ℝ) (π / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have heU : innerSlackU K t (x t) = 0 := by
      rw [innerSlackU_eq_dot, hpath t ⟨hti.1.le, hti.2.le⟩]
      simp [dot]
    have heV : innerSlackV K t (x t) = 0 := by
      rw [innerSlackV_eq_dot, hpath t ⟨hti.1.le, hti.2.le⟩]
      simp [dot]
    have hcu : c ≤ sin t := (hcC'.trans (hC t ht)).trans (min_le_left _ _)
    have hcv : c ≤ cos t := (hcC'.trans (hC t ht)).trans (min_le_right _ _)
    refine ⟨t, hti, ?_, ?_⟩
    · rw [innerSlackU_down, heU, zero_sub]
      have hm := mul_le_mul_of_nonneg_left hcu hd.le
      have hmin := min_le_left (c * d) τ
      nlinarith
    · rw [innerSlackV_down, heV, zero_sub]
      have hm := mul_le_mul_of_nonneg_left hcv hd.le
      have hmin := min_le_left (c * d) τ
      nlinarith
  · have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by
      intro he
      rw [← he, h.D_end] at hfloor
      linarith)
    have hti : t ∈ Ioo (0 : ℝ) (π / 2) := ⟨ht0, by linarith [ht.2]⟩
    have heU : innerSlackU K t (envD x β t) = -β t := by
      rw [innerSlackU_eq_dot, hpath t ⟨hti.1.le, hti.2.le⟩]
      simp [envD, dot_neg_left, dot_smul_left]
    have heV : innerSlackV K t (envD x β t) = 0 := by
      rw [innerSlackV_eq_dot, hpath t ⟨hti.1.le, hti.2.le⟩]
      exact env_dot_D_self x β t
    have hcoef : c ≤ cos t := hcD'.trans (hcos t ht)
    have hinactive : τ ≤ β t := hτD'.trans (hD t ht)
    have hsin0 : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht0.le (by linarith [hti.2, pi_pos])
    refine ⟨t, hti, ?_, ?_⟩
    · rw [innerSlackU_down, heU]
      have hp := mul_nonneg hd.le hsin0
      have hmin := min_le_right (c * d) τ
      linarith
    · rw [innerSlackV_down, heV, zero_sub]
      have hm := mul_le_mul_of_nonneg_left hcoef hd.le
      have hmin := min_le_left (c * d) τ
      nlinarith

end Envelope

end MovingSofaStability

end EnvelopeSlack

/-!
## Gerver's quantitative roof margin

A roof function is identified with the existing three-piece envelope through
equality of their strict subgraphs. The reference error bound then follows from
the proved envelope slack estimates.
-/

section GerverMargins

open Real Set
open MovingSofaOptimality MovingSofaUniqueness
open GerverParams

namespace MovingSofaStability

/-- Two nonnegative graph roofs with the same strict subgraph have the same height. -/
theorem roof_value_of_envelope {K Γ : Set Point} {a b H L LΓ : ℝ} {γ : ℝ → ℝ}
    (hroof : CapRoofData K a b H L γ)
    (henv : niche K (π / 2) = envUnderStrict Γ)
    (hΓ : VerticalSlopeBound Γ LΓ)
    (hbounds : ∀ q ∈ Γ, q.1 ∈ Icc a b ∧ 0 ≤ q.2)
    {q : Point} (hq : q ∈ Γ) : q.2 = γ q.1 := by
  have hx := (hbounds q hq).1
  have hq0 := (hbounds q hq).2
  have hγ0 := hroof.roof_nonneg q.1 hx
  apply le_antisymm
  · by_contra hnot
    have hlt : γ q.1 < q.2 := not_le.mp hnot
    let p : Point := (q.1, (γ q.1 + q.2) / 2)
    have hp : p ∈ niche K (π / 2) := by
      rw [henv]
      exact ⟨by dsimp [p]; linarith, q, hq, rfl, by dsimp [p]; linarith⟩
    rw [hroof.niche_eq] at hp
    have hh := hp.2.2
    change (γ q.1 + q.2) / 2 < γ q.1 at hh
    linarith
  · by_contra hnot
    have hlt : q.2 < γ q.1 := not_le.mp hnot
    let p : Point := (q.1, (γ q.1 + q.2) / 2)
    have hp : p ∈ niche K (π / 2) := by
      rw [hroof.niche_eq]
      exact ⟨hx, by dsimp [p]; linarith, by dsimp [p]; linarith⟩
    rw [henv] at hp
    obtain ⟨-, q', hq', hqx, hheight⟩ := hp
    have he : q' = q := eq_of_same_abscissa hΓ hq' hq hqx
    rw [he] at hheight
    change (γ q.1 + q.2) / 2 < q.2 at hheight
    linarith

/-- The uniform roof-wall certificate is supplied by Gerver's established envelope geometry. -/
theorem gerver_roof_slack_margin {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {H L : ℝ} {γ : ℝ → ℝ}
    (hroof : CapRoofData P.cap (gerverRoofLeft P) (gerverRoofRight P) H L γ) :
    ∃ c τ : ℝ, 0 < c ∧ 0 < τ ∧ RoofSlackMargin P.cap γ c τ := by
  have hB := romik_bounds hP hbox
  have henv := gn_envHyp hP hB
  have hθ : P.θ < π / 4 := by linarith [henv.ht.2.2.1]
  obtain ⟨LΓ, -, hΓ⟩ := envelope_slope_bound henv hθ (by linarith)
  have hheight : ∀ t ∈ Icc (0 : ℝ) (π / 2), (P.path t).2 < 1 :=
    fun t ht => path_snd_lt_one hP hB ht.1 ht.2
  have hbounds := envelope_bounds_of_path_height henv hheight
  have hniche := gerver_niche_envelope hP hbox
  have hgraph : ∀ q ∈ gerverEnvelope P, q.2 = γ q.1 := by
    intro q hq
    exact roof_value_of_envelope hroof hniche hΓ
      (fun p hp => ⟨(hbounds p hp).1, (hbounds p hp).2.1⟩) hq
  obtain ⟨c, τ, hc, hτ, hslack⟩ := envelope_downward_slack henv
    (K := P.cap) (fun t ht => ((theorem8_4_1_monotone hP hbox).2 t ht).2.2)
  refine ⟨c, τ, hc, hτ, ?_⟩
  intro p hp
  rw [hniche] at hp
  obtain ⟨hpy, q, hq, hqx, hlt⟩ := hp
  let d := q.2 - p.2
  have hd : 0 < d := sub_pos.mpr hlt
  have hfloor : 0 ≤ q.2 - d := by dsimp [d]; linarith
  obtain ⟨t, ht, hU, hV⟩ := hslack q hq d hd hfloor
  have he : (q.1, q.2 - d) = p := by
    apply Prod.ext
    · exact hqx
    · dsimp [d]
      ring
  have hdγ : d = γ p.1 - p.2 := by
    dsimp [d]
    rw [hgraph q hq, hqx]
  rw [he, hdγ] at hU hV
  exact ⟨t, ht, hU, hV⟩

/-- All constants needed for the S-to-G directed recovery are properties of Gerver,
not additional assumptions on a near-optimal competing sofa. -/
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
  obtain ⟨κ, r₀, hκ, hr₀, hballs⟩ := gerver_interiorBalls hP hbox
  exact ⟨H, L, γ, c, τ, d₀, κ, r₀, hroof, hc, hτ, hd₀, hκ, hr₀, hslack, houter, hballs⟩

end MovingSofaStability

end GerverMargins
