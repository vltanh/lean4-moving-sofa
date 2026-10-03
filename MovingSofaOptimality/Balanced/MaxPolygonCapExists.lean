module

public import MovingSofaOptimality.Balanced.CapGeometry

/-!
# Existence of maximum polygon caps (§3.4)

Definition 3.4.1 (`IsMaxPolygonCap`, `def:maximum-polygon-cap`), Lemma 3.4.1 (`lemma3_4_1`,
`lem:maximum-polygon-cap-mirror`), Lemma 3.4.2 (`lemma3_4_2`, `lem:polygon-cap-bounded`) and
Theorem 3.4.3 (`theorem3_4_3`, `thm:maximum-polygon-cap`): maximum polygon caps exist. This is the
second of the four modules of §3.4 (see `MaximumPolygonCap`).

**Organization.**
* Definition 3.4.1 and Lemma 3.4.1: the mirror reflection of a polygon cap with angle set `Θ` is a
  polygon cap with angle set `ω - Θ` (`AngleSet.mirror`) and the same polygon sofa area
  (`mpc_mirror_polycap`).
* Lemma 3.4.2 (width): for `ω < π/2` the width is at most that of `P_ω` (`mpc_width_le_of_lt`); for
  `ω = π/2` a wide cap has a rectangle in its niche (`mpc_wedge_rect`) larger than the cap.
* Theorem 3.4.3: instead of the Blaschke selection theorem, a subsequence along which the support
  values converge on the finite set `Θ^◇` (`mpc_limit_polycap`, `mpc_exists_limit_polycap`), along
  which `𝒜_Θ` is upper semicontinuous (`mpc_le_limit_objective`).
-/

@[expose] public section

open Real Set

namespace MovingSofaOptimality

/-! ## Maximum polygon caps (Definition 3.4.1) and their mirror images (Lemma 3.4.1) -/

/-- A maximum polygon cap with angle set `Θ` (Definition 3.4.1, `def:maximum-polygon-cap`): a
polygon cap containing `o_ω` that maximizes `𝒜_Θ` over the polygon caps with angle set `Θ`. -/
def IsMaxPolygonCap (Θ : AngleSet) (K : Set (ℝ × ℝ)) : Prop :=
  IsPolygonCap Θ K ∧ oPt Θ.ω ∈ K ∧ ∀ K', IsPolygonCap Θ K' → polyArea Θ K' ≤ polyArea Θ K

/-- The mirror angle set `ω - Θ`. -/
noncomputable def AngleSet.mirror (Θ : AngleSet) : AngleSet where
  ω := Θ.ω
  angles := Θ.angles.image (fun t => Θ.ω - t)
  hω := Θ.hω
  nonempty := Θ.nonempty.image _
  subset := by
    intro t ht
    simp only [Finset.mem_image] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    have := Θ.subset s hs
    constructor <;> linarith [this.1, this.2]

section Mirror

open MeasureTheory

/-- The mirror reflection `M_ω` as a linear map given by its matrix. -/
lemma mpc_mirror_eq_toLin (ω : ℝ) :
    mirror ω = Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      !![cos (π / 2 + ω), sin (π / 2 + ω); sin (π / 2 + ω), -cos (π / 2 + ω)] := by
  funext p
  rw [Matrix.toLin_finTwoProd_apply]
  simp only [mirror]; ext <;> ring

/-- The mirror reflection preserves the Lebesgue measure. -/
lemma mpc_volume_preimage_mirror (ω : ℝ) (A : Set (ℝ × ℝ)) :
    volume (mirror ω ⁻¹' A) = volume A := by
  rw [mpc_mirror_eq_toLin]
  refine volume_preimage_linearMap ?_ A
  rw [LinearMap.det_toLin, Matrix.det_fin_two_of, abs_eq zero_le_one]
  exact Or.inr (by linear_combination -cos_sq_add_sin_sq (π / 2 + ω))

/-- The mirror reflection preserves areas. -/
lemma mpc_area_mirror (ω : ℝ) (A : Set (ℝ × ℝ)) : area (mirror ω '' A) = area A := by
  rw [area, area, cn_mirror_image_eq, mpc_volume_preimage_mirror]

/-- The mirror reflection fixes `o_ω`. -/
lemma mpc_mirror_oPt {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) : mirror ω (oPt ω) = oPt ω := by
  apply eq_of_dot_uvec_eq (a := ω) (b := ω + π / 2)
  · rw [show ω + π / 2 - ω = π / 2 by ring, sin_pi_div_two]; norm_num
  · rw [cn_dot_mirror_uvec, show ω + π / 2 - ω = π / 2 by ring, dot_uvec_pi_div_two,
      mpc_oPt_snd, oPt_dot_uvec (Ioc_subset_Icc_self hω)]
  · rw [cn_dot_mirror_uvec, sub_self, dot_uvec_zero,
      uvec_add_pi_div_two, mpc_oPt_dot_vvec hω]
    rfl

/-- `ω - (ω - Θ) = Θ`. -/
lemma mpc_mirror_mirror_angleSet (Θ : AngleSet) : Θ.mirror.mirror = Θ := by
  obtain ⟨ω, angles, hω, hne, hsub⟩ := Θ
  simp only [AngleSet.mirror, AngleSet.mk.injEq, true_and]
  rw [Finset.image_image]
  convert Finset.image_id (s := angles) using 2
  funext t
  simp

/-- Membership in the mirror angle set `ω - Θ`. -/
lemma mpc_mem_mirror_angles {Θ : AngleSet} {s : ℝ} :
    s ∈ Θ.mirror.angles ↔ Θ.ω - s ∈ Θ.angles := by
  simp only [AngleSet.mirror, Finset.mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩; simpa using ht
  · intro h; exact ⟨_, h, by ring⟩

open Classical in
/-- The normal angle of the mirror image of a half-plane, normalized into `Θ^◇ ∪ {ω + π, 3π/2}`. -/
noncomputable def mpcMirrorAngle (ω s : ℝ) : ℝ :=
  π / 2 + ω - s + if s = ω + π ∨ s = 3 * π / 2 then 2 * π else 0

lemma mpc_uvec_mirrorAngle (ω s : ℝ) : uvec (mpcMirrorAngle ω s) = uvec (ω + π / 2 - s) := by
  rw [mpcMirrorAngle, add_comm (π / 2) ω]
  split_ifs
  · exact uvec_add_two_pi _
  · rw [add_zero]

/-- The mirror reflection maps the normal angles of polygon caps with angle set `Θ` to those
of polygon caps with angle set `ω - Θ`. -/
lemma mpc_mirrorAngle_mem {Θ : AngleSet} {s : ℝ} (hs : s ∈ Θ.capAngles) :
    mpcMirrorAngle Θ.ω s ∈ Θ.mirror.capAngles := by
  have hω0 := mpc_omega_pos Θ
  have hω2 := mpc_omega_le Θ
  rcases mpc_capAngles_cases hs with hs' | rfl | rfl
  · have hne : ¬ (s = Θ.ω + π ∨ s = 3 * π / 2) := by
      have := mpc_diamond_lt_pi hs'
      rintro (h | h) <;> linarith [pi_pos]
    rw [mpcMirrorAngle, ite_eq_right hne, add_zero]
    left
    rcases mpc_diamond_cases hs' with h | ⟨u, hu, rfl⟩ | rfl | rfl
    · -- `t ∈ Θ ↦ (ω - t) + π/2 ∈ Θ.mirror + π/2`
      refine Or.inl (Or.inr ⟨Θ.ω - s, Finset.mem_coe.2 (mpc_mem_mirror_angles.2 ?_), by ring⟩)
      simpa using h
    · refine Or.inl (Or.inl (Finset.mem_coe.2 (mpc_mem_mirror_angles.2 ?_)))
      show Θ.ω - (π / 2 + Θ.ω - (u + π / 2)) ∈ Θ.angles
      rw [show Θ.ω - (π / 2 + Θ.ω - (u + π / 2)) = u by ring]; exact hu
    · right; right; show π / 2 + Θ.ω - Θ.ω = π / 2; ring
    · right; left; show π / 2 + Θ.ω - π / 2 = Θ.ω; ring
  · rw [mpcMirrorAngle, ite_eq_left (Or.inl rfl)]
    right; right; show π / 2 + Θ.ω - (Θ.ω + π) + 2 * π = 3 * π / 2; ring
  · rw [mpcMirrorAngle, ite_eq_left (Or.inr rfl)]
    right; left; show π / 2 + Θ.ω - 3 * π / 2 + 2 * π = Θ.ω + π; ring

/-- The mirror reflection of a polygon cap with angle set `Θ` is a polygon cap with angle set
`ω - Θ`, with the same polygon sofa area. -/
lemma mpc_mirror_polycap {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) :
    IsPolygonCap Θ.mirror (mirrorCap K Θ.ω) ∧
      polyArea Θ.mirror (mirrorCap K Θ.ω) = polyArea Θ K := by
  -- the defining half-planes are mirrored
  have hhpi : IsHalfPlaneInter (mirrorCap K Θ.ω) Θ.mirror.capAngles := by
    obtain ⟨ι, t, c, ht, hKeq⟩ := hK.2
    refine ⟨ι, fun i => mpcMirrorAngle Θ.ω (t i), c, fun i => mpc_mirrorAngle_mem (ht i), ?_⟩
    ext p
    rw [mirrorCap, cn_mem_mirror_image, hKeq]
    simp only [mem_iInter, halfMinus, mem_ofPred_eq, mpc_uvec_mirrorAngle, cn_dot_mirror_uvec]
  have hK' : IsPolygonCap Θ.mirror (mirrorCap K Θ.ω) := ⟨proposition2_5_4_isCap hK.1, hhpi⟩
  -- the polygon niche is mirrored wedge by wedge (Proposition 2.5.4)
  have hniche : polyNiche Θ.mirror (mirrorCap K Θ.ω) = mirror Θ.ω '' polyNiche Θ K := by
    have e : ∀ (Θ' : AngleSet) L, polyNiche Θ' L = ⋃ t ∈ Θ'.angles, wedge L Θ'.ω t :=
      fun Θ' L => by simp only [polyNiche, wedge, inter_iUnion₂]
    have hw : ∀ t, wedge (mirrorCap K Θ.ω) Θ.ω t = mirror Θ.ω '' wedge K Θ.ω (Θ.ω - t) :=
      fun t => (proposition2_5_4_sets t).2.1
    rw [e, e, image_iUnion₂]
    simp only [AngleSet.mirror, Finset.set_biUnion_finset_image, hw, sub_sub_cancel]
  refine ⟨hK', ?_⟩
  rw [theorem3_2_3 hK', theorem3_2_3 hK, hniche, mpc_area_mirror, mirrorCap, mpc_area_mirror]

end Mirror

/-- **Lemma 3.4.1** (`lem:maximum-polygon-cap-mirror`). The mirror reflection of a maximum polygon
cap is a maximum polygon cap with the angle set `ω - Θ`. -/
theorem lemma3_4_1 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap Θ K) :
    IsMaxPolygonCap Θ.mirror (mirrorCap K Θ.ω) := by
  obtain ⟨hcap, ho, hmax⟩ := hK
  obtain ⟨hK', hA'⟩ := mpc_mirror_polycap hcap
  refine ⟨hK', ⟨oPt Θ.ω, ho, mpc_mirror_oPt Θ.hω⟩, fun K'' hK'' => ?_⟩
  obtain ⟨h1, h2⟩ := mpc_mirror_polycap hK''
  rw [mpc_mirror_mirror_angleSet] at h1 h2
  rw [hA', ← h2]
  exact hmax _ h1

/-! ## The width of polygon caps of positive polygon area (Lemma 3.4.2) -/

section Width

open MeasureTheory

/-- The area of a rectangle. -/
lemma mpc_volume_prod (s t : Set ℝ) : volume (s ×ˢ t) = volume s * volume t := by
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl, Measure.prod_prod]

/-- The width of a cap along `u_0` is at most the width of `P_ω` when `ω < π/2`. -/
lemma mpc_width_le_of_lt {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) (hlt : ω < π / 2) {K : Set (ℝ × ℝ)}
    (hK : IsCap K ω) : width K 0 ≤ 1 / cos ω + tan ω := by
  have hc : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [hω.1], hlt⟩
  have hs : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω.1 (by linarith [pi_pos])
  rw [width, zero_add]
  -- `x ≤ 1 / cos ω` and `-x ≤ tan ω` on `P_ω`
  have h0 : supp K 0 ≤ 1 / cos ω := supp_le_of_forall hK.2.1.1 fun p hp => by
    have e1 := hK.dot_omega_le_one hp
    have e2 := hK.snd_nonneg hp
    rw [dot_uvec_zero, le_div_iff₀ hc]
    simp only [dot, uvec] at e1
    nlinarith
  have hpi : supp K π ≤ tan ω := supp_le_of_forall hK.2.1.1 fun p hp => by
    have e1 := hK.dot_omega_nonneg hp
    have e2 := hK.snd_le_one hp
    rw [dot_uvec_pi, tan_eq_sin_div_cos, le_div_iff₀ hc]
    simp only [dot, uvec] at e1
    nlinarith
  linarith

/-- The area of a cap is at most its width along `u_0`. -/
lemma mpc_area_le_width {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) : area K ≤ width K 0 := by
  have hKb := hK.2.1
  have hd : width K 0 = supp K 0 + supp K π := by rw [width, zero_add]
  have hd0 : 0 ≤ supp K 0 + supp K π := by
    obtain ⟨p, hp⟩ := hKb.1
    have e1 := dot_le_supp hKb.2.1 hp 0
    have e2 := dot_le_supp hKb.2.1 hp π
    rw [dot_uvec_zero] at e1
    rw [dot_uvec_pi] at e2
    linarith
  have hsub : K ⊆ Icc (-supp K π) (supp K 0) ×ˢ Icc 0 1 := by
    intro p hp
    have e1 := dot_le_supp hKb.2.1 hp 0
    have e2 := dot_le_supp hKb.2.1 hp π
    rw [dot_uvec_zero] at e1
    rw [dot_uvec_pi] at e2
    exact ⟨⟨by linarith, e1⟩, ⟨hK.snd_nonneg hp, hK.snd_le_one hp⟩⟩
  have hle := measure_mono (μ := volume) hsub
  rw [mpc_volume_prod, Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_mul (by linarith),
    sub_zero, mul_one, sub_neg_eq_add, add_comm (supp K 0)] at hle
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rw [ENNReal.toReal_ofReal (by linarith)] at this
  rw [hd]; simp only [area]; linarith

/-- The arithmetic of Lemma 3.4.2: for `d > 2s` and `d > 32/m`, the rectangle of side lengths
`L/2` and `Lm/4`, with `L = d - s > d/2`, has area larger than `d`. -/
lemma mpc_wedge_arith {d s m L : ℝ} (hm : 0 < m) (hs : 0 < s) (hd1 : 2 * s < d)
    (hd2 : 32 / m < d) (hL : L = d - s) : d < L / 2 * (L * m / 4) := by
  have hd : 0 < d := by linarith
  have hL2 : d / 2 < L := by rw [hL]; linarith
  have hdm : 32 < d * m := by rwa [div_lt_iff₀ hm] at hd2
  have h1 : d / 2 * (d / 2) * m < L * L * m :=
    mul_lt_mul_of_pos_right (mul_lt_mul'' hL2 hL2 (by linarith) (by linarith)) hm
  nlinarith

/-- For `ω = π/2`, a rectangle of area `L² m / 8` lies in the wedge `F_ω ∩ Q_K⁻(t)`, where `L` is
the width of the cap minus `1 / cos t + 1 / sin t`, and `m ≤ min (cot t) (tan t)`. -/
lemma mpc_wedge_rect {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K)
    (hω : Θ.ω = π / 2) {t : ℝ} (htΘ : t ∈ Θ.angles) {L m : ℝ}
    (hL : L = supp K 0 - 1 / cos t - (-supp K π + 1 / sin t))
    (hm1 : m ≤ cos t / sin t) (hm2 : m ≤ sin t / cos t) :
    Ioo (-supp K π + 1 / sin t + L / 4) (supp K 0 - 1 / cos t - L / 4) ×ˢ Ioo 0 (L * m / 4) ⊆
      polyNiche Θ K := by
  have ht := mpc_angles_bounds htΘ
  rw [hω] at ht
  have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩
  have hst : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
  have hKb := hK.1.2.1
  -- the walls `l(t, h_K(t) - 1)` and `l(t + π/2, h_K(t + π/2) - 1)` cross the axis `y = 0` right
  -- of `x = h_K(0) - 1 / cos t` and left of `x = -h_K(π) + 1 / sin t`
  have hA : supp K 0 * cos t ≤ supp K t := by
    obtain ⟨p, hp, hpe⟩ := exists_dot_eq_supp hKb.2.1 hKb.1 0
    rw [dot_uvec_zero] at hpe
    have e := dot_le_supp hKb.2.1 hp t
    have e4 := hK.1.snd_nonneg hp
    simp only [dot, uvec] at e
    rw [← hpe]; nlinarith
  have hC : supp K π * sin t ≤ supp K (t + π / 2) := by
    obtain ⟨p, hp, hpe⟩ := exists_dot_eq_supp hKb.2.1 hKb.1 π
    rw [dot_uvec_pi] at hpe
    have e := dot_le_supp hKb.2.1 hp (t + π / 2)
    have e4 := hK.1.snd_nonneg hp
    rw [uvec_add_pi_div_two] at e
    simp only [dot, vvec] at e
    have : supp K π = -p.1 := by linarith
    rw [this]; nlinarith
  rintro ⟨x, y⟩ ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  have hL0 : 0 < L := by
    have := lt_trans hx1 hx2
    linarith
  refine ⟨⟨?_, ?_⟩, mem_iUnion₂.2 ⟨t, htΘ, ?_⟩⟩
  · show 0 ≤ dot (x, y) (uvec Θ.ω)
    rw [hω, dot_uvec_pi_div_two]; exact hy1.le
  · show 0 ≤ dot (x, y) (uvec (π / 2))
    rw [dot_uvec_pi_div_two]; exact hy1.le
  · rw [proposition2_2_2_qMinus]
    constructor
    · show dot (x, y) (uvec t) < supp K t - 1
      simp only [dot, uvec]
      have h1 : y < L / 4 * cos t / sin t := by
        calc y < L * m / 4 := hy2
          _ ≤ L * (cos t / sin t) / 4 := by gcongr
          _ = L / 4 * cos t / sin t := by ring
      have h2 := (lt_div_iff₀ hst).1 h1
      have h3 : x * cos t < (supp K 0 - 1 / cos t - L / 4) * cos t :=
        mul_lt_mul_of_pos_right hx2 hct
      have e : (supp K 0 - 1 / cos t - L / 4) * cos t = supp K 0 * cos t - 1 - L / 4 * cos t := by
        field_simp
      linarith
    · show dot (x, y) (uvec (t + π / 2)) < supp K (t + π / 2) - 1
      rw [uvec_add_pi_div_two]
      simp only [dot, vvec]
      have h1 : y < L / 4 * sin t / cos t := by
        calc y < L * m / 4 := hy2
          _ ≤ L * (sin t / cos t) / 4 := by gcongr
          _ = L / 4 * sin t / cos t := by ring
      have h2 := (lt_div_iff₀ hct).1 h1
      have h3 : (-supp K π + 1 / sin t + L / 4) * sin t < x * sin t :=
        mul_lt_mul_of_pos_right hx1 hst
      have e : (-supp K π + 1 / sin t + L / 4) * sin t = -supp K π * sin t + 1 + L / 4 * sin t := by
        field_simp
      linarith

end Width

/-- **Lemma 3.4.2** (`lem:polygon-cap-bounded`). For `t ∈ (0, ω)` there is `c_{ω,t} > 0` such that
every polygon cap `K` with an angle set containing `t` and with `𝒜_Θ(K) > 0` has width at most
`c_{ω,t}` along `u_0`. -/
theorem lemma3_4_2 {ω t : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) (ht : t ∈ Ioo 0 ω) :
    ∃ c > 0, ∀ Θ : AngleSet, Θ.ω = ω → t ∈ Θ.angles → ∀ K, IsPolygonCap Θ K →
      0 < polyArea Θ K → width K 0 ≤ c := by
  rcases lt_or_eq_of_le hω.2 with hlt | heq
  · have hc : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [hω.1], hlt⟩
    have htan : 0 < tan ω := tan_pos_of_pos_of_lt_pi_div_two hω.1 hlt
    refine ⟨1 / cos ω + tan ω, by positivity, fun Θ hΘ _ K hK _ => ?_⟩
    subst hΘ
    exact mpc_width_le_of_lt hω hlt hK.1
  · -- `ω = π/2`: a wide cap has a large wedge `T_K(t)`
    subst heq
    have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩
    have hst : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
    set s := 1 / cos t + 1 / sin t with hs_def
    set m := min (sin t / cos t) (cos t / sin t) with hm_def
    have hm : 0 < m := lt_min (by positivity) (by positivity)
    have hs : 0 < s := by positivity
    refine ⟨max (2 * s) (32 / m) + 1, by positivity, fun Θ hΘ htΘ K hK hpos => ?_⟩
    by_contra hwide
    push Not at hwide
    have hd : width K 0 = supp K 0 + supp K π := by rw [width, zero_add]
    have hd1 : 2 * s < width K 0 := by linarith [le_max_left (2 * s) (32 / m)]
    have hd2 : 32 / m < width K 0 := by linarith [le_max_right (2 * s) (32 / m)]
    set L := supp K 0 - 1 / cos t - (-supp K π + 1 / sin t) with hL
    have hLd : L = width K 0 - s := by rw [hL, hd, hs_def]; ring
    have hLpos : 0 < L := by rw [hLd]; linarith
    have hsub := mpc_wedge_rect hK hΘ htΘ hL (min_le_right _ _) (min_le_left _ _)
    have hvolR : area (Ioo (-supp K π + 1 / sin t + L / 4) (supp K 0 - 1 / cos t - L / 4) ×ˢ
        Ioo 0 (L * m / 4)) = L / 2 * (L * m / 4) := by
      simp only [area]
      have e1 : supp K 0 - 1 / cos t - L / 4 - (-supp K π + 1 / sin t + L / 4) = L / 2 := by
        rw [hL]; ring
      rw [mpc_volume_prod, Real.volume_Ioo, Real.volume_Ioo, e1, sub_zero,
        ← ENNReal.ofReal_mul (by linarith), ENNReal.toReal_ofReal]
      have := mul_pos (half_pos hLpos) (div_pos (mul_pos hLpos hm) (by norm_num : (0 : ℝ) < 4))
      linarith
    have hareaN : L / 2 * (L * m / 4) ≤ area (polyNiche Θ K) := by
      rw [← hvolR]
      exact ENNReal.toReal_mono (mpc_isBounded_polyNiche hK).measure_lt_top.ne
        (MeasureTheory.measure_mono hsub)
    have hpoly : polyArea Θ K = area K - area (polyNiche Θ K) := theorem3_2_3 hK
    have hareaK := mpc_area_le_width hK.1
    have hbig := mpc_wedge_arith hm hs hd1 hd2 hLd
    linarith

/-! ## Existence of maximum polygon caps (Theorem 3.4.3)

The paper takes a maximizing sequence and applies the Blaschke selection theorem. Here the
maximizing sequence lies in a fixed box (Lemma 3.4.2), and it suffices to extract a subsequence
along which the support values converge on the finite set `Θ^◇`: the limit is the polygon cap
`𝓒_Θ(h_∞)` (`mpc_limit_polycap`), and the area and the niche area are semicontinuous along the
subsequence. -/

section Existence

open Filter Topology MeasureTheory

/-- `o_ω · u_s ≤ 1` for the angles `s ∈ (0, π)` outside `(ω, π/2)`. -/
lemma mpc_oPt_dot_le {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) {s : ℝ} (hs0 : 0 < s) (hsπ : s < π)
    (hs : s ≤ ω ∨ π / 2 ≤ s) : dot (oPt ω) (uvec s) ≤ 1 := by
  set a := π / 4 - ω / 2 with ha
  have ha0 : 0 ≤ a := by rw [ha]; linarith [hω.2]
  have ha1 : a < π / 4 := by rw [ha]; linarith [hω.1]
  have hca : 0 < cos a := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  simp only [oPt, dot, uvec]
  rw [← ha, tan_eq_sin_div_cos]
  have key : sin (a + s) ≤ cos a := by
    rw [← sin_pi_div_two_sub]
    rcases hs with hs | hs
    · apply sin_le_sin_of_le_of_le_pi_div_two <;> linarith
    · rw [← sin_pi_sub (a + s)]
      apply sin_le_sin_of_le_of_le_pi_div_two <;> linarith
  rw [sin_add] at key
  rw [div_mul_eq_mul_div, div_add' _ _ _ hca.ne', div_le_one hca]
  linarith

/-- The polygon cap `K₁ = 𝓒_Θ(1)` of the paper: it contains `o_ω`, its polygon niche is empty, and
its area is positive. -/
lemma mpc_K1 (Θ : AngleSet) :
    IsPolygonCap Θ (capH Θ (fun _ => 1)) ∧ oPt Θ.ω ∈ capH Θ (fun _ => 1) ∧
      polyNiche Θ (capH Θ (fun _ => 1)) = ∅ ∧ 0 < area (capH Θ (fun _ => 1)) := by
  have hω0 := mpc_omega_pos Θ
  have hω2 := mpc_omega_le Θ
  set K₁ := capH Θ (fun _ => 1) with hK₁
  have hmem : ∀ p, p ∈ K₁ ↔ (∀ s ∈ Θ.diamond, dot p (uvec s) ≤ 1) ∧ 0 ≤ dot p (uvec Θ.ω) ∧
      0 ≤ dot p (uvec (π / 2)) := by
    intro p; rw [hK₁, nef_mem_capH_iff]; simp
  have hc : IsCompact K₁ := mpc_isCompact_capH Θ _
  -- Step 1: `o_ω` and the origin lie in `K₁`.
  have ho : oPt Θ.ω ∈ K₁ := by
    rw [hmem]
    refine ⟨fun s hs => ?_, ?_, ?_⟩
    · apply mpc_oPt_dot_le Θ.hω (mpc_diamond_bounds hs).1 (mpc_diamond_lt_pi hs)
      rcases mpc_diamond_cases hs with h | ⟨u, hu, rfl⟩ | rfl | rfl
      · exact Or.inl (mpc_angles_bounds h).2.le
      · right; linarith [(mpc_angles_bounds hu).1]
      · exact Or.inl le_rfl
      · exact Or.inr le_rfl
    · rw [oPt_dot_uvec (Ioc_subset_Icc_self Θ.hω)]; norm_num
    · rw [dot_uvec_pi_div_two, mpc_oPt_snd]; norm_num
  have hO : (0 : ℝ × ℝ) ∈ K₁ := by
    rw [hmem]; simp
  -- Step 2: the support values of a cap, attained at `o_ω` and at the origin.
  have hcap : IsPolygonCap Θ K₁ := by
    refine mpc_capH_isPolygonCap ⟨_, hO⟩ ?_ ?_ ?_ ?_
    · exact supp_eq_of_mem hc (fun p hp => ((hmem p).1 hp).1 _ (Or.inr (Or.inl rfl))) ho
        (oPt_dot_uvec (Ioc_subset_Icc_self Θ.hω))
    · exact supp_eq_of_mem hc (fun p hp => ((hmem p).1 hp).1 _ (Or.inr (Or.inr rfl))) ho
        (by rw [dot_uvec_pi_div_two, mpc_oPt_snd])
    · refine supp_eq_of_mem hc (fun p hp => ?_) hO (dot_zero_left _)
      rw [dot_uvec_add_pi]; linarith [((hmem p).1 hp).2.1]
    · refine supp_eq_of_mem hc (fun p hp => ?_) hO (dot_zero_left _)
      rw [dot_uvec_three_pi_div_two]; linarith [((hmem p).1 hp).2.2, dot_uvec_pi_div_two p]
  refine ⟨hcap, ho, ?_, ?_⟩
  · -- Step 3: the niche is empty, since `h_{K₁} ≤ 1` on `Θ^◇`: a point of `F_ω` cannot have both
    -- `p · u_t < 0` and `p · v_t < 0`.
    rw [eq_empty_iff_forall_notMem]
    intro p hp
    rw [mpc_polyNiche_eq hcap, mem_ofPred_eq, mpc_lt_mpcTop_iff] at hp
    obtain ⟨h1, t, ht, h3, h4⟩ := hp
    have e1 : supp K₁ t ≤ 1 :=
      supp_le_of_forall ⟨_, hO⟩ fun q hq => ((hmem q).1 hq).1 t (Or.inl (Or.inl ht))
    have e2 : supp K₁ (t + π / 2) ≤ 1 :=
      supp_le_of_forall ⟨_, hO⟩ fun q hq => ((hmem q).1 hq).1 _ (Or.inl (Or.inr ⟨t, ht, rfl⟩))
    have hlow : 0 ≤ p.2 := by
      have e : mpcL K₁ (π / 2) p.1 ≤ mpcLow Θ K₁ p.1 := le_max_right _ _
      rw [mpc_mpcL_pi_div_two hcap] at e
      exact e.trans h1
    simp only [mpcL, mpcLineY] at h3 h4
    have htb := mpc_angles_bounds ht
    have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
    have hst : 0 < sin t := sin_pos_of_pos_of_lt_pi htb.1 (by linarith [pi_pos])
    rw [lt_div_iff₀ hst] at h3
    rw [sin_add_pi_div_two, cos_add_pi_div_two, lt_div_iff₀ hct] at h4
    nlinarith [mul_pos hst hct, sin_sq_add_cos_sq t]
  · -- Step 4: `K₁` contains the square `[0, 1/4]²`.
    have hsq : Icc (0 : ℝ) (1 / 4) ×ˢ Icc (0 : ℝ) (1 / 4) ⊆ K₁ := by
      rintro ⟨x, y⟩ ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
      rw [hmem]
      refine ⟨fun s _ => ?_, ?_, ?_⟩
      · simp only [dot, uvec]
        nlinarith [cos_le_one s, sin_le_one s, neg_one_le_cos s, neg_one_le_sin s]
      · simp only [dot, uvec]
        have : 0 ≤ cos Θ.ω := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hω2⟩
        have : 0 ≤ sin Θ.ω := sin_nonneg_of_nonneg_of_le_pi hω0.le (by linarith [pi_pos])
        positivity
      · rw [dot_uvec_pi_div_two]; exact hy0
    have hle := ENNReal.toReal_mono hc.measure_lt_top.ne (measure_mono (μ := volume) hsq)
    rw [mpc_volume_prod, Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num),
      ENNReal.toReal_ofReal (by norm_num)] at hle
    simp only [area]
    linarith

/-- Horizontal translates of polygon caps with `ω = π/2` are polygon caps with the same polygon
sofa area. -/
lemma mpc_translate_polycap {Θ : AngleSet} (hω : Θ.ω = π / 2) {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (a : ℝ) :
    IsPolygonCap Θ ((fun p => p + (a, 0)) '' K) ∧
      polyArea Θ ((fun p => p + (a, 0)) '' K) = polyArea Θ K := by
  have hKb := hK.1.2.1
  set K' := (fun p => p + ((a, 0) : ℝ × ℝ)) '' K
  -- a horizontal translation does not change the support values at angles with `cos s = 0`
  have hs : ∀ s, cos s = 0 → supp K' s = supp K s := by
    intro s hs
    rw [supp_translate K _ s hKb.2.1 hKb.1]
    simp [dot, uvec, hs]
  have hcos1 : cos Θ.ω = 0 := by rw [hω, cos_pi_div_two]
  have hcos2 : cos (π / 2) = 0 := cos_pi_div_two
  have hcos3 : cos (Θ.ω + π) = 0 := by rw [cos_add_pi, hcos1, neg_zero]
  have hcos4 : cos (3 * π / 2) = 0 := by
    rw [show 3 * π / 2 = π / 2 + π by ring, cos_add_pi, hcos2, neg_zero]
  have hK' : IsPolygonCap Θ K' := by
    refine ⟨⟨Θ.hω, nef_isConvexBody_translate hKb _, ?_, ?_, ?_, ?_,
      nef_isHalfPlaneInter_translate hK.1.2.2.2.2.2.2 _⟩, nef_isHalfPlaneInter_translate hK.2 _⟩
    · rw [hs _ hcos1]; exact hK.1.2.2.1
    · rw [hs _ hcos2]; exact hK.1.2.2.2.1
    · rw [hs _ hcos3]; exact hK.1.2.2.2.2.1
    · rw [hs _ hcos4]; exact hK.1.2.2.2.2.2.1
  refine ⟨hK', ?_⟩
  rw [← (proposition3_3_5 hK').2, ← (theorem3_3_6 hK _).2]
  rfl

/-- Every polygon cap has the polygon sofa area of a polygon cap containing `o_ω`: for `ω < π/2`
it contains `o_ω` already, and for `ω = π/2` a horizontal translate does. -/
lemma mpc_exists_oPt_mem {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) :
    ∃ K', IsPolygonCap Θ K' ∧ oPt Θ.ω ∈ K' ∧ polyArea Θ K' = polyArea Θ K := by
  rcases (mpc_omega_le Θ).lt_or_eq with hlt | heq
  · exact ⟨K, hK, hK.1.oPt_mem hlt, rfl⟩
  · obtain ⟨p, hp, hpe⟩ := exists_dot_eq_supp hK.1.2.1.2.1 hK.1.2.1.1 (π / 2)
    rw [hK.1.2.2.2.1, dot_uvec_pi_div_two] at hpe
    obtain ⟨hK', hA'⟩ := mpc_translate_polycap heq hK (-p.1)
    refine ⟨_, hK', ⟨p, hp, ?_⟩, hA'⟩
    simp only [oPt, heq, show π / 4 - π / 2 / 2 = 0 by ring, tan_zero]
    ext
    · simp
    · simp [hpe]

section Limit

variable {Θ : AngleSet} {K : ℕ → Set (ℝ × ℝ)} {hinf : ℝ → ℝ}

/-- Along polygon caps `K_n` whose support values converge to `h_∞` on `Θ^◇`, the limit heights at
the bottom angles are `h_∞(ω) = h_∞(π/2) = 1`. -/
lemma mpc_limit_bot (hK : ∀ n, IsPolygonCap Θ (K n))
    (hlim : ∀ s ∈ Θ.diamond, Tendsto (fun n => supp (K n) s) atTop (𝓝 (hinf s)))
    {s : ℝ} (hs : s ∈ ({Θ.ω, π / 2} : Set ℝ)) : hinf s = 1 := by
  refine tendsto_nhds_unique (hlim s (nef_pair_mem_diamond hs)) ?_
  simp only [fun n => (mpc_supp_bot (hK n).1 hs).1]
  exact tendsto_const_nhds

/-- Limits of points of a subsequence of the `K_n` lie in `𝓒_Θ(h_∞)`. -/
lemma mpc_limit_mem (hK : ∀ n, IsPolygonCap Θ (K n))
    (hlim : ∀ s ∈ Θ.diamond, Tendsto (fun n => supp (K n) s) atTop (𝓝 (hinf s)))
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ) {q : ℕ → ℝ × ℝ} {q₀ : ℝ × ℝ} (hq : ∀ k, q k ∈ K (ψ k))
    (hqlim : Tendsto q atTop (𝓝 q₀)) : q₀ ∈ capH Θ hinf := by
  have hdot : ∀ v : ℝ × ℝ, Tendsto (fun k => dot (q k) v) atTop (𝓝 (dot q₀ v)) :=
    fun v => ((continuous_dot v).tendsto q₀).comp hqlim
  rw [nef_mem_capH_iff, mpc_limit_bot hK hlim (s := Θ.ω) (Or.inl rfl),
    mpc_limit_bot hK hlim (s := π / 2) (Or.inr rfl), sub_self]
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · exact le_of_tendsto_of_tendsto (hdot _) ((hlim s hs).comp hψ.tendsto_atTop)
      (Eventually.of_forall fun k => dot_le_supp (hK (ψ k)).1.2.1.2.1 (hq k) s)
  · exact ge_of_tendsto (hdot _)
      (Eventually.of_forall fun k => (hK (ψ k)).1.dot_omega_nonneg (hq k))
  · exact ge_of_tendsto (hdot _) (Eventually.of_forall fun k => by
      rw [dot_uvec_pi_div_two]; exact (hK (ψ k)).1.snd_nonneg (hq k))

/-- If the `K_n` lie in a fixed compact set, every limit of support values `h_{K_n}(r)` is attained
at a point of `𝓒_Θ(h_∞)`. -/
lemma mpc_limit_attained (hK : ∀ n, IsPolygonCap Θ (K n)) {B : Set (ℝ × ℝ)} (hB : IsCompact B)
    (hKB : ∀ n, K n ⊆ B)
    (hlim : ∀ s ∈ Θ.diamond, Tendsto (fun n => supp (K n) s) atTop (𝓝 (hinf s)))
    {r c : ℝ} (hrc : Tendsto (fun n => supp (K n) r) atTop (𝓝 c)) :
    ∃ q ∈ capH Θ hinf, dot q (uvec r) = c := by
  choose q hqK hqe using fun n => exists_dot_eq_supp (hK n).1.2.1.2.1 (hK n).1.2.1.1 r
  obtain ⟨q₀, -, ψ, hψ, hqψ⟩ := hB.tendsto_subseq fun n => hKB n (hqK n)
  refine ⟨q₀, mpc_limit_mem hK hlim hψ (fun k => hqK (ψ k)) hqψ, ?_⟩
  have h1 := ((continuous_dot (uvec r)).tendsto q₀).comp hqψ
  exact tendsto_nhds_unique (h1.congr fun k => by simp [Function.comp, hqe])
    (hrc.comp hψ.tendsto_atTop)

/-- Upper semicontinuity of the area along the `K_n`: `|K_n| ≤ |𝓒_Θ(h_∞)| + ε` eventually. -/
lemma mpc_limit_area_usc (hK : ∀ n, IsPolygonCap Θ (K n))
    (hlim : ∀ s ∈ Θ.diamond, Tendsto (fun n => supp (K n) s) atTop (𝓝 (hinf s)))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n in atTop, area (K n) ≤ area (capH Θ hinf) + ε := by
  set c := mpcCapC Θ hinf
  have hω1 := mpc_limit_bot hK hlim (s := Θ.ω) (Or.inl rfl)
  have hπ1 := mpc_limit_bot hK hlim (s := π / 2) (Or.inr rfl)
  -- `𝓒_Θ(h_∞)` is the parallel set `mpcOuter Θ.capAngles c 0`, and the parallel sets are bounded
  have hLeq : mpcOuter Θ.capAngles c 0 = capH Θ hinf := by
    ext p
    simp only [mpcOuter, mem_ofPred_eq, add_zero]
    rw [mpc_mem_capH_iff_capAngles]
  have hb : Bornology.IsBounded (mpcOuter Θ.capAngles c 1) := by
    obtain ⟨t, ht⟩ := Θ.nonempty
    have htb := mpc_angles_bounds ht
    have hω := mpc_omega_le Θ
    apply mpc_isBounded_of_strip htb.1 (by linarith) (a := -(c (3 * π / 2) + 1))
      (b := c (π / 2) + 1) (c₁ := c t + 1) (c₂ := c (t + π / 2) + 1)
    intro p hp
    have e1 := hp _ (Or.inr (Or.inr rfl))
    have e2 := hp _ (Or.inl (Or.inr (Or.inr rfl)))
    rw [dot_uvec_three_pi_div_two] at e1
    rw [dot_uvec_pi_div_two] at e2
    exact ⟨by linarith, e2, hp t (Or.inl (Or.inl (Or.inl ht))),
      hp _ (Or.inl (Or.inl (Or.inr ⟨t, ht, rfl⟩)))⟩
  obtain ⟨δ, hδ, hδ1, hle⟩ := mpc_area_outer_eventually_le one_pos hb hε
  rw [hLeq] at hle
  -- eventually the `K_n` lie in the parallel set `mpcOuter Θ.capAngles c δ`
  have hev : ∀ᶠ n in atTop, ∀ s ∈ mpcDiamond Θ, supp (K n) s < hinf s + δ := by
    rw [Filter.eventually_all_finset]
    intro s hs
    exact (hlim s (mpc_mem_mpcDiamond.1 hs)).eventually (gt_mem_nhds (lt_add_of_pos_right _ hδ))
  filter_upwards [hev] with n hn
  have hsub : K n ⊆ mpcOuter Θ.capAngles c δ := by
    intro p hp s hs
    have e := dot_le_supp (hK n).1.2.1.2.1 hp s
    rcases mpc_capAngles_cases hs with hs' | rfl | rfl
    · have := hn s (mpc_mem_mpcDiamond.2 hs')
      rw [show c s = hinf s by simp [c, mpcCapC, hs']]
      linarith
    · have hnd : Θ.ω + π ∉ Θ.diamond := fun h => by
        linarith [mpc_diamond_lt_pi h, pi_pos, mpc_omega_pos Θ]
      rw [show c (Θ.ω + π) = 0 by simp [c, mpcCapC, hnd, hω1], (hK n).1.2.2.2.2.1] at *
      linarith
    · have hnd : 3 * π / 2 ∉ Θ.diamond := fun h => by
        linarith [mpc_diamond_lt_pi h, pi_pos]
      rw [show c (3 * π / 2) = 0 by
        simp [c, mpcCapC, hnd, show 3 * π / 2 - π = π / 2 by ring, hπ1],
        (hK n).1.2.2.2.2.2.1] at *
      linarith
  have hfin : volume (mpcOuter Θ.capAngles c δ) ≠ ⊤ :=
    (hb.subset (mpc_outer_mono _ _ hδ1)).measure_lt_top.ne
  exact (ENNReal.toReal_mono hfin (measure_mono hsub)).trans hle

/-- Lower semicontinuity of the niche area along the `K_n`:
`|𝒩_Θ(𝓒_Θ(h_∞))| - ε ≤ |𝒩_Θ(K_n)|` eventually. -/
lemma mpc_limit_niche_lsc (hK : ∀ n, IsPolygonCap Θ (K n)) {B : Set (ℝ × ℝ)} (hB : IsCompact B)
    (hKB : ∀ n, K n ⊆ B)
    (hlim : ∀ s ∈ Θ.diamond, Tendsto (fun n => supp (K n) s) atTop (𝓝 (hinf s)))
    (hsuppL : ∀ s ∈ Θ.diamond, supp (capH Θ hinf) s = hinf s) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, area (polyNiche Θ (capH Θ hinf)) - ε ≤ area (polyNiche Θ (K n)) := by
  -- a uniform bound `R` on the support values of the `K_n`
  obtain ⟨R, hR⟩ := exists_abs_supp_le hB ((hK 0).1.2.1.1.mono (hKB 0))
  have hRn : ∀ n s, supp (K n) s ≤ R := fun n s =>
    (supp_mono (hKB n) (hK n).1.2.1.1 hB s).trans ((le_abs_self _).trans (hR s))
  apply mpc_area_lsc (B := ⋃ t ∈ Θ.angles, {p : ℝ × ℝ | 0 ≤ dot p (uvec Θ.ω) ∧
      0 ≤ dot p (uvec (π / 2)) ∧ dot p (uvec t) < R ∧ dot p (vvec t) < R}) _
    ((Bornology.isBounded_biUnion_finset _).2 fun t ht => by
      obtain ⟨ht0, htω, hω⟩ := nef_angle_mem ht
      exact nef_wedge_isBounded ht0 htω hω) _ hε
  · -- every point of the limit niche lies eventually in the niches of the `K_n`
    rintro p ⟨hpf, hpq⟩
    obtain ⟨t, ht, hq⟩ := mem_iUnion₂.1 hpq
    have htd : t ∈ Θ.diamond := Or.inl (Or.inl ht)
    have htd2 : t + π / 2 ∈ Θ.diamond := Or.inl (Or.inr ⟨t, ht, rfl⟩)
    rw [proposition2_2_2_qMinus] at hq
    have e1 : dot p (uvec t) + 1 < hinf t := by
      have : dot p (uvec t) < supp (capH Θ hinf) t - 1 := hq.1
      rw [hsuppL t htd] at this; linarith
    have e2 : dot p (uvec (t + π / 2)) + 1 < hinf (t + π / 2) := by
      have : dot p (uvec (t + π / 2)) < supp (capH Θ hinf) (t + π / 2) - 1 := hq.2
      rw [hsuppL _ htd2] at this; linarith
    filter_upwards [(hlim t htd).eventually (lt_mem_nhds e1),
      (hlim _ htd2).eventually (lt_mem_nhds e2)] with n h1 h2
    refine ⟨hpf, mem_iUnion₂.2 ⟨t, ht, ?_⟩⟩
    rw [proposition2_2_2_qMinus]
    exact ⟨show dot p (uvec t) < supp (K n) t - 1 by linarith,
      show dot p (uvec (t + π / 2)) < supp (K n) (t + π / 2) - 1 by linarith⟩
  · -- the niches of the `K_n` lie in a fixed bounded set
    refine Eventually.of_forall fun n p hp => ?_
    obtain ⟨hpf, hpq⟩ := hp
    obtain ⟨t, ht, hq⟩ := mem_iUnion₂.1 hpq
    rw [proposition2_2_2_qMinus] at hq
    have e1 : dot p (uvec t) < supp (K n) t - 1 := hq.1
    have e2 : dot p (vvec t) < supp (K n) (t + π / 2) - 1 := by
      rw [← uvec_add_pi_div_two]; exact hq.2
    exact mem_iUnion₂.2 ⟨t, ht, hpf.1, hpf.2, by linarith [hRn n t],
      by linarith [hRn n (t + π / 2)]⟩

end Limit

/-- Limits of polygon caps lying in a fixed compact set, with converging support values on `Θ^◇`:
the limit `𝓒_Θ(h_∞)` is a polygon cap with the limit support values on `Θ^◇`, it contains the
points lying eventually in the `K_n`, and along the `K_n` the area is upper semicontinuous and the
niche area lower semicontinuous. -/
lemma mpc_limit_polycap {Θ : AngleSet} {K : ℕ → Set (ℝ × ℝ)} (hK : ∀ n, IsPolygonCap Θ (K n))
    {B : Set (ℝ × ℝ)} (hB : IsCompact B) (hKB : ∀ n, K n ⊆ B) {hinf : ℝ → ℝ}
    (hlim : ∀ s ∈ Θ.diamond, Tendsto (fun n => supp (K n) s) atTop (𝓝 (hinf s))) :
    IsPolygonCap Θ (capH Θ hinf) ∧ (∀ s ∈ Θ.diamond, supp (capH Θ hinf) s = hinf s) ∧
      (∀ p, (∀ᶠ n in atTop, p ∈ K n) → p ∈ capH Θ hinf) ∧
      (∀ ε > 0, ∀ᶠ n in atTop, area (K n) ≤ area (capH Θ hinf) + ε) ∧
      (∀ ε > 0, ∀ᶠ n in atTop,
        area (polyNiche Θ (capH Θ hinf)) - ε ≤ area (polyNiche Θ (K n))) := by
  set L := capH Θ hinf with hL
  have hLc : IsCompact L := mpc_isCompact_capH Θ hinf
  have hω1 := mpc_limit_bot hK hlim (s := Θ.ω) (Or.inl rfl)
  have hπ1 := mpc_limit_bot hK hlim (s := π / 2) (Or.inr rfl)
  have hmemL : ∀ p, p ∈ L ↔ (∀ s ∈ Θ.diamond, dot p (uvec s) ≤ hinf s) ∧
      0 ≤ dot p (uvec Θ.ω) ∧ 0 ≤ dot p (uvec (π / 2)) := by
    intro p; rw [hL, nef_mem_capH_iff, hω1, hπ1, sub_self]
  -- Step 1: the support values of `L` on `Θ^◇` are the limits `h_∞`.
  have hsuppL : ∀ s ∈ Θ.diamond, supp L s = hinf s := by
    intro s hs
    obtain ⟨q, hq, hqe⟩ := mpc_limit_attained hK hB hKB hlim (hlim s hs)
    exact supp_eq_of_mem hLc (fun p hp => ((hmemL p).1 hp).1 s hs) hq hqe
  -- Step 2: the bottom support values of `L` vanish, as those of the `K_n` do.
  have hbot : ∀ r, (∀ n, supp (K n) r = 0) → (∀ p ∈ L, dot p (uvec r) ≤ 0) → supp L r = 0 := by
    intro r h0 hle
    obtain ⟨q, hq, hqe⟩ := mpc_limit_attained hK hB hKB hlim (r := r) (c := 0)
      (by simp only [h0]; exact tendsto_const_nhds)
    exact supp_eq_of_mem hLc hle hq hqe
  obtain ⟨q₀, hq₀, -⟩ := mpc_limit_attained hK hB hKB hlim (hlim _ (Or.inr (Or.inl rfl)))
  have hLcap : IsPolygonCap Θ L := by
    refine mpc_capH_isPolygonCap ⟨q₀, hq₀⟩ (by rw [hsuppL _ (Or.inr (Or.inl rfl)), hω1])
      (by rw [hsuppL _ (Or.inr (Or.inr rfl)), hπ1]) ?_ ?_
    · refine hbot _ (fun n => (hK n).1.2.2.2.2.1) fun p hp => ?_
      rw [dot_uvec_add_pi]; linarith [((hmemL p).1 hp).2.1]
    · refine hbot _ (fun n => (hK n).1.2.2.2.2.2.1) fun p hp => ?_
      rw [dot_uvec_three_pi_div_two]; linarith [((hmemL p).1 hp).2.2, dot_uvec_pi_div_two p]
  refine ⟨hLcap, hsuppL, fun p hp => ?_, fun ε hε => mpc_limit_area_usc hK hlim hε,
    fun ε hε => mpc_limit_niche_lsc hK hB hKB hlim hsuppL hε⟩
  -- Step 3: a point lying eventually in the `K_n` is a (constant) limit of their points.
  obtain ⟨N, hN⟩ := hp.exists_forall_of_atTop
  exact mpc_limit_mem hK hlim (ψ := fun k => k + N) (fun a b h => by simp only; omega)
    (q := fun _ => p) (fun k => hN _ (Nat.le_add_left N k)) tendsto_const_nhds

/-- A sequence of polygon caps in a common box `[-R, R] × [0, 1]` has a subsequence whose support
values on `Θ^◇` converge, to those of a polygon cap `𝓒_Θ(h_∞)`; the conclusions of
`mpc_limit_polycap` hold along it. -/
lemma mpc_exists_limit_polycap {Θ : AngleSet} {K : ℕ → Set (ℝ × ℝ)}
    (hK : ∀ n, IsPolygonCap Θ (K n)) {R : ℝ} (hbox : ∀ n, K n ⊆ Icc (-R) R ×ˢ Icc 0 1) :
    ∃ (φ : ℕ → ℕ) (hinf : ℝ → ℝ), StrictMono φ ∧
      (∀ s ∈ Θ.diamond, Tendsto (fun n => supp (K (φ n)) s) atTop (𝓝 (hinf s))) ∧
      IsPolygonCap Θ (capH Θ hinf) ∧ (∀ s ∈ Θ.diamond, supp (capH Θ hinf) s = hinf s) ∧
      (∀ p, (∀ᶠ n in atTop, p ∈ K (φ n)) → p ∈ capH Θ hinf) ∧
      (∀ ε > 0, ∀ᶠ n in atTop, area (K (φ n)) ≤ area (capH Θ hinf) + ε) ∧
      (∀ ε > 0, ∀ᶠ n in atTop,
        area (polyNiche Θ (capH Θ hinf)) - ε ≤ area (polyNiche Θ (K (φ n)))) := by
  -- the support values on the finite set `Θ^◇` stay in a compact ball
  obtain ⟨p, hp⟩ := (hK 0).1.2.1.1
  have hR : 0 ≤ R := by linarith [(hbox 0 hp).1.1, (hbox 0 hp).1.2]
  let v : ℕ → ({s // s ∈ mpcDiamond Θ} → ℝ) := fun n s => supp (K n) s.1
  have hvb : ∀ n, v n ∈ Metric.closedBall (0 : {s // s ∈ mpcDiamond Θ} → ℝ) (R + 1) := by
    intro n
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by linarith)]
    exact fun s => abs_supp_le_box (hK n).1.2.1 (hbox n) s.1
  obtain ⟨a, -, φ, hφ, hvlim⟩ := (isCompact_closedBall _ _).tendsto_subseq hvb
  let hinf : ℝ → ℝ := fun s => if hs : s ∈ mpcDiamond Θ then a ⟨s, hs⟩ else 0
  have hlim : ∀ s ∈ Θ.diamond, Tendsto (fun n => supp (K (φ n)) s) atTop (𝓝 (hinf s)) := by
    intro s hs
    have hs' := mpc_mem_mpcDiamond.2 hs
    simpa [hinf, hs'] using tendsto_pi_nhds.1 hvlim ⟨s, hs'⟩
  exact ⟨φ, hinf, hφ, hlim, mpc_limit_polycap (fun n => hK (φ n))
    (isCompact_Icc.prod isCompact_Icc) (fun n => hbox (φ n)) hlim⟩

/-- Along a subsequence as in `mpc_exists_limit_polycap`, the objective `𝒜_Θ - P` with a penalty
`P` converging along the subsequence is upper semicontinuous: if `M - 1/(n + 1) < 𝒜_Θ(K_n) - P_n`
for all `n`, then `M ≤ 𝒜_Θ(L) - lim P_{φ(n)}`. -/
lemma mpc_le_limit_objective {Θ : AngleSet} {K : ℕ → Set (ℝ × ℝ)}
    (hK : ∀ n, IsPolygonCap Θ (K n)) {L : Set (ℝ × ℝ)} (hL : IsPolygonCap Θ L) {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (husc : ∀ ε > 0, ∀ᶠ n in atTop, area (K (φ n)) ≤ area L + ε)
    (hlsc : ∀ ε > 0, ∀ᶠ n in atTop, area (polyNiche Θ L) - ε ≤ area (polyNiche Θ (K (φ n))))
    {P : ℕ → ℝ} {p M : ℝ} (hP : Tendsto (fun n => P (φ n)) atTop (𝓝 p))
    (hnear : ∀ n : ℕ, M - 1 / ((n : ℝ) + 1) < polyArea Θ (K n) - P n) :
    M ≤ polyArea Θ L - p := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show 0 < ε / 4 by positivity)
  have hnear' : ∀ᶠ n in atTop, M - ε / 4 < polyArea Θ (K (φ n)) - P (φ n) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have h : (1 : ℝ) / (φ n + 1) ≤ 1 / (N + 1) := by
      apply div_le_div_of_nonneg_left zero_le_one (by positivity)
      have : (N : ℝ) ≤ φ n := by exact_mod_cast hn.trans (hφ.id_le n)
      linarith
    linarith [hnear (φ n)]
  have hP' : ∀ᶠ n in atTop, p - ε / 4 < P (φ n) := hP.eventually (Ioi_mem_nhds (by linarith))
  obtain ⟨n, h1, h2, h3, h4⟩ := (hnear'.and ((husc (ε / 4) (by positivity)).and
    ((hlsc (ε / 4) (by positivity)).and hP'))).exists
  rw [theorem3_2_3 hL]
  rw [theorem3_2_3 (hK (φ n))] at h1
  linarith

/-- **Theorem 3.4.3** (`thm:maximum-polygon-cap`). A maximum polygon cap exists for every angle
set. -/
theorem theorem3_4_3 (Θ : AngleSet) : ∃ K, IsMaxPolygonCap Θ K := by
  classical
  -- Step 1: `𝒜_Θ` is bounded above (Lemma 3.4.2), and positive at `K₁ = 𝓒_Θ(1)`.
  obtain ⟨hK₁, -, hN₁, harea₁⟩ := mpc_K1 Θ
  have hpa₁ : polyArea Θ (capH Θ fun _ => 1) = area (capH Θ fun _ => 1) := by
    rw [theorem3_2_3 hK₁, hN₁]; simp [area]
  obtain ⟨t₀, ht₀⟩ := Θ.nonempty
  obtain ⟨c, hc, hcK⟩ := lemma3_4_2 Θ.hω (mpc_angles_bounds ht₀)
  have hbound : ∀ K, IsPolygonCap Θ K → polyArea Θ K ≤ c := by
    intro K hK
    by_cases hpos : 0 < polyArea Θ K
    · have h2 : 0 ≤ area (polyNiche Θ K) := ENNReal.toReal_nonneg
      rw [theorem3_2_3 hK]
      linarith [hcK Θ rfl ht₀ K hK hpos, mpc_area_le_width hK.1]
    · linarith
  set A : Set ℝ := {x | ∃ K, IsPolygonCap Θ K ∧ polyArea Θ K = x} with hA
  have hAbdd : BddAbove A := ⟨c, by rintro _ ⟨K, hK, rfl⟩; exact hbound K hK⟩
  have hA₁ : polyArea Θ (capH Θ fun _ => 1) ∈ A := ⟨_, hK₁, rfl⟩
  set M := sSup A with hM
  have hMpos : 0 < M := by linarith [le_csSup hAbdd hA₁]
  -- Step 2: a maximizing sequence of polygon caps `K_n` containing `o_ω`, with `𝒜_Θ(K_n) > 0`.
  have hseq : ∀ n : ℕ, ∃ K, IsPolygonCap Θ K ∧ oPt Θ.ω ∈ K ∧
      M - 1 / (n + 1) < polyArea Θ K ∧ 0 < polyArea Θ K := by
    intro n
    have hn : (0 : ℝ) < 1 / (n + 1) := by positivity
    have hlt : max (M - 1 / (n + 1)) (M / 2) < M := max_lt (by linarith) (by linarith)
    obtain ⟨_, ⟨K, hK, rfl⟩, hK2⟩ := exists_lt_of_lt_csSup ⟨_, hA₁⟩ hlt
    obtain ⟨K', hK', ho, hA'⟩ := mpc_exists_oPt_mem hK
    rw [← hA'] at hK2
    exact ⟨K', hK', ho, (le_max_left _ _).trans_lt hK2,
      by linarith [(le_max_right (M - 1 / (n + 1)) (M / 2)).trans_lt hK2]⟩
  choose Ks hKs hoKs hlowKs hposKs using hseq
  -- Step 3: the `K_n` lie in a fixed box: they contain `o_ω` and have width at most `c`.
  set R := |(oPt Θ.ω).1| + c with hR
  have hbox : ∀ n, Ks n ⊆ Icc (-R) R ×ˢ Icc 0 1 := by
    intro n p hp
    have hw := hcK Θ rfl ht₀ (Ks n) (hKs n) (hposKs n)
    have hKc := (hKs n).1.2.1.2.1
    have e1 := dot_le_supp hKc hp 0
    have e2 := dot_le_supp hKc (hoKs n) π
    have e3 := dot_le_supp hKc hp π
    have e4 := dot_le_supp hKc (hoKs n) 0
    rw [dot_uvec_zero] at e1 e4
    rw [dot_uvec_pi] at e2 e3
    rw [width, zero_add] at hw
    have a1 := neg_abs_le (oPt Θ.ω).1
    have a2 := le_abs_self (oPt Θ.ω).1
    exact ⟨⟨by linarith, by linarith⟩, (hKs n).1.snd_nonneg hp,
      (hKs n).1.snd_le_one hp⟩
  -- Step 4: along a subsequence the `K_n` converge to a polygon cap `𝓒_Θ(h_∞)`, which contains
  -- `o_ω`, and `𝒜_Θ(𝓒_Θ(h_∞)) ≥ M` by semicontinuity.
  obtain ⟨φ, hinf, hφ, -, hLcap, -, hmemL, husc, hlsc⟩ := mpc_exists_limit_polycap hKs hbox
  refine ⟨capH Θ hinf, hLcap, hmemL _ (Eventually.of_forall fun n => hoKs (φ n)),
    fun K' hK' => ?_⟩
  have hML := mpc_le_limit_objective hKs hLcap hφ husc hlsc (P := fun _ => 0)
    tendsto_const_nhds fun n => by simpa using hlowKs n
  linarith [le_csSup hAbdd ⟨K', hK', rfl⟩]

end Existence

end MovingSofaOptimality
