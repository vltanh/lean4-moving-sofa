module

public import MovingSofaStability.NicheFeet

/-!
# Local containment of the whole niche

A normalized cap near Gerver need not be injective. Horizontal wedge-foot
localization and a uniform height bound instead put its niche in a fixed
rectangle separated from the reference upper boundary.
-/

@[expose] public section
noncomputable section

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
