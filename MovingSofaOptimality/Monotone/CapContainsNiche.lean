module

public import MovingSofaOptimality.Monotone.CapNiche
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The cap contains the niche (§2.5)

Propositions 2.5.1–2.5.4, Theorem 2.5.5 (`thm:wedge-ends-in-cap`), Lemmas 2.5.6–2.5.7, Theorems
2.5.8 (`thm:monotonization-connected-iff`), 2.5.9 (`thm:niche-in-cap`), 2.5.10
(`thm:sofa-area-functional`) and Remark 2.5.2 (`rem:niche-not-in-cap`).
-/

@[expose] public section

open Real Set

namespace MovingSofaOptimality

/-! ### Helper lemmas: basic properties of a cap -/

section Cap

variable {K : Set (ℝ × ℝ)} {ω : ℝ}

private lemma IsCap.omega_mem (hK : IsCap K ω) : ω ∈ Ioc 0 (π / 2) := hK.1
private lemma IsCap.isCompact (hK : IsCap K ω) : IsCompact K := hK.2.1.2.1
private lemma IsCap.nonempty (hK : IsCap K ω) : K.Nonempty := hK.2.1.1
private lemma IsCap.convex (hK : IsCap K ω) : Convex ℝ K := hK.2.1.2.2
private lemma IsCap.supp_omega (hK : IsCap K ω) : supp K ω = 1 := hK.2.2.1
private lemma IsCap.supp_pi_div_two (hK : IsCap K ω) : supp K (π / 2) = 1 := hK.2.2.2.1
private lemma IsCap.supp_omega_add_pi (hK : IsCap K ω) : supp K (ω + π) = 0 := hK.2.2.2.2.1
private lemma IsCap.supp_three_pi_div_two (hK : IsCap K ω) : supp K (3 * π / 2) = 0 :=
  hK.2.2.2.2.2.1

private lemma IsCap.dot_le (hK : IsCap K ω) {p : ℝ × ℝ} (hp : p ∈ K) (t : ℝ) :
    dot p (uvec t) ≤ supp K t := dot_le_supp hK.isCompact hp t

/-- Membership criterion for a cap: a point of the fan lies in the cap iff it satisfies the
supporting half-plane constraints with normal angles in `J_ω`. -/
private lemma IsCap.mem_iff (hK : IsCap K ω) (p : ℝ × ℝ) :
    p ∈ K ↔ p ∈ fan ω ∧ ∀ s ∈ jSet ω, dot p (uvec s) ≤ supp K s := by
  refine ⟨fun hp => ⟨hK.subset_fan hp, fun s _ => hK.dot_le hp s⟩, ?_⟩
  rintro ⟨hpF, hpJ⟩
  rw [mem_fan_iff] at hpF
  obtain ⟨ι, t, c, ht, hKeq⟩ := hK.2.2.2.2.2.2
  rw [hKeq, mem_iInter]
  intro i
  -- the offset of a defining half-plane is at least the support function in its direction
  have hci : supp K (t i) ≤ c i :=
    supp_le_of_forall hK.nonempty fun q hq => by rw [hKeq] at hq; exact mem_iInter.1 hq i
  show dot p (uvec (t i)) ≤ c i
  rcases ht i with hJ | hi | hi
  · exact (hpJ _ hJ).trans hci
  · rw [hi, hK.supp_omega_add_pi] at hci
    rw [hi, dot_uvec_add_pi]
    linarith [hpF.1]
  · rw [mem_singleton_iff] at hi
    rw [hi, hK.supp_three_pi_div_two] at hci
    rw [hi, dot_uvec_three_pi_div_two]
    linarith [hpF.2]

end Cap

/-! ### Helper lemmas: trigonometry -/

/-- If `p` is strictly less far than `q` in the directions `u_a` and `u_b`, then also in any
direction `u_s` strictly between them. -/
private lemma cn_dot_lt_of_between {p q : ℝ × ℝ} {a b s : ℝ} (hab : 0 < sin (b - a))
    (h1 : 0 < sin (b - s)) (h2 : 0 < sin (s - a)) (ha : dot p (uvec a) < dot q (uvec a))
    (hb : dot p (uvec b) < dot q (uvec b)) : dot p (uvec s) < dot q (uvec s) := by
  refine lt_of_mul_lt_mul_left ?_ hab.le
  linarith [dot_uvec_comb p a b s, dot_uvec_comb q a b s, mul_lt_mul_of_pos_left ha h1,
    mul_lt_mul_of_pos_left hb h2]

/-- `u_{t+π/2} = cos(ω - t) u_{ω+π/2} + sin(ω - t) u_ω`. -/
private lemma cn_dot_uvec_decomp (q : ℝ × ℝ) (ω t : ℝ) :
    dot q (uvec (t + π / 2)) =
      cos (ω - t) * dot q (uvec (ω + π / 2)) + sin (ω - t) * dot q (uvec ω) := by
  simp only [dot, uvec, cos_add_pi_div_two, sin_add_pi_div_two, sin_sub, cos_sub]
  linear_combination (q.1 * sin t - q.2 * cos t) * sin_sq_add_cos_sq ω

private lemma cn_trig_of_mem {ω t : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) (ht : t ∈ Ioo 0 ω) :
    0 < cos t ∧ 0 < sin t ∧ sin t < 1 ∧ 0 < cos (ω - t) ∧ 0 < sin (ω - t) ∧ sin (ω - t) < 1 := by
  obtain ⟨hω0, hω1⟩ := hω
  obtain ⟨ht0, ht1⟩ := ht
  have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 (by linarith)
  have hc' : 0 < cos (ω - t) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs' : 0 < sin (ω - t) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  refine ⟨hc, hs, ?_, hc', hs', ?_⟩
  · nlinarith [sin_sq_add_cos_sq t]
  · nlinarith [sin_sq_add_cos_sq (ω - t)]

private lemma cn_jSet_subset {ω : ℝ} : jSet ω ⊆ Icc 0 (ω + π / 2) := by
  rintro s (hs | hs)
  · exact ⟨hs.1, by linarith [hs.2, pi_pos]⟩
  · exact ⟨by linarith [hs.1, pi_pos], hs.2⟩

/-! ### Helper lemmas: the inequalities behind `w_K(t), z_K(t) > 0` -/

section Gap

variable {K : Set (ℝ × ℝ)} {ω : ℝ}

/-- The inequality behind `w_K(t) > 0`: `h_K(t) - 1 < h_K(0) cos t`. -/
private lemma IsCap.gapW_ineq (hK : IsCap K ω) {t : ℝ} (ht : t ∈ Ioo 0 ω) :
    supp K t - 1 < supp K 0 * cos t := by
  obtain ⟨hc, hs, hs1, -⟩ := cn_trig_of_mem hK.omega_mem ht
  obtain ⟨q, hqK, hq⟩ := exists_dot_eq_supp hK.isCompact hK.nonempty t
  have h0 := hK.dot_le hqK 0
  rw [dot_uvec_zero] at h0
  have h1 := hK.snd_le_one hqK
  have h2 := hK.snd_nonneg hqK
  rw [← hq]
  simp only [dot, uvec]
  nlinarith [mul_le_mul_of_nonneg_right h0 hc.le, mul_le_mul_of_nonneg_right h1 hs.le]

/-- The inequality behind `z_K(t) > 0`: `h_K(t + π/2) - 1 < h_K(ω + π/2) cos(ω - t)`. -/
private lemma IsCap.gapZ_ineq (hK : IsCap K ω) {t : ℝ} (ht : t ∈ Ioo 0 ω) :
    supp K (t + π / 2) - 1 < supp K (ω + π / 2) * cos (ω - t) := by
  obtain ⟨-, -, -, hc, hs, hs1⟩ := cn_trig_of_mem hK.omega_mem ht
  obtain ⟨q, hqK, hq⟩ := exists_dot_eq_supp hK.isCompact hK.nonempty (t + π / 2)
  have h0 := hK.dot_le hqK (ω + π / 2)
  have h1 := hK.dot_omega_le_one hqK
  rw [← hq, cn_dot_uvec_decomp q ω t]
  nlinarith [mul_le_mul_of_nonneg_left h0 hc.le, mul_le_mul_of_nonneg_left h1 hs.le]

end Gap

/-! ### Helper lemmas: moving points inside the fan -/

/-- Moving a point of the fan in a direction `u_s`, `s ∈ [0, ω + π/2]`, keeps it in the fan. -/
private lemma cn_add_smul_uvec_mem_fan {ω s ε : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hs : s ∈ Icc 0 (ω + π / 2)) (hε : 0 ≤ ε) {p : ℝ × ℝ} (hp : p ∈ fan ω) :
    p + ε • uvec s ∈ fan ω := by
  obtain ⟨hω0, hω1⟩ := hω
  obtain ⟨hs0, hs1⟩ := hs
  have hcos : 0 ≤ cos (s - ω) := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hsin : 0 ≤ sin s := sin_nonneg_of_nonneg_of_le_pi hs0 (by linarith)
  obtain ⟨h1, h2⟩ := mem_fan_iff.1 hp
  rw [mem_fan_iff, dot_add_left, dot_smul_left, dot_uvec_uvec]
  simp only [Prod.snd_add, Prod.smul_snd, uvec_snd, smul_eq_mul]
  constructor <;> positivity

private lemma cn_tendsto_add_smul (p v : ℝ × ℝ) :
    Filter.Tendsto (fun ε : ℝ => p + ε • v) (nhdsWithin 0 (Ioi 0)) (nhds p) := by
  have : Continuous (fun ε : ℝ => p + ε • v) := by fun_prop
  simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds

private lemma cn_upperBoundary_subset (K : Set (ℝ × ℝ)) (ω : ℝ) : upperBoundary K ω ⊆ K :=
  iUnion₂_subset fun _ _ => inter_subset_left

/-- **Proposition 2.5.1** (`pro:upper-boundary-interior`). The upper boundary `δK` is the boundary
of `K` in the subspace topology of the fan `F_ω`, that is `K ∩ closure (F_ω \ K)`. -/
theorem proposition2_5_1 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    upperBoundary K ω = K ∩ closure (fan ω \ K) := by
  ext z
  constructor
  · -- a point of an edge `e_K(t)` is a limit of the points `z + ε u_t ∈ F_ω \ K`
    intro hz
    obtain ⟨t, ht, hzK, hzl⟩ := mem_iUnion₂.1 hz
    refine ⟨hzK, mem_closure_of_tendsto (cn_tendsto_add_smul z (uvec t)) ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine ⟨cn_add_smul_uvec_mem_fan hK.omega_mem ht hε.le (hK.subset_fan hzK), fun h => ?_⟩
    have h1 := hK.dot_le h t
    rw [dot_add_left, dot_smul_left, dot_uvec_self, hzl] at h1
    linarith
  · -- otherwise the gap `h_K(t) - z · u_t` has a positive minimum `m` on `[0, ω + π/2]`, and the
    -- points of `F_ω` at distance `< m/2` from `z` lie in `K`
    rintro ⟨hzK, hzc⟩
    by_contra hz
    have hlt : ∀ t ∈ Icc 0 (ω + π / 2), dot z (uvec t) < supp K t := fun t ht =>
      lt_of_le_of_ne (hK.dot_le hzK t) fun h => hz (mem_iUnion₂.2 ⟨t, ht, hzK, h⟩)
    have hcont : Continuous fun t => supp K t - dot z (uvec t) :=
      (continuous_supp hK.isCompact).sub (by simp only [dot, uvec]; fun_prop)
    obtain ⟨t0, ht0, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := ω + π / 2)).exists_isMinOn
      (nonempty_Icc.2 (by linarith [hK.omega_mem.1, pi_pos])) hcont.continuousOn
    have hm : 0 < supp K t0 - dot z (uvec t0) := sub_pos.2 (hlt t0 ht0)
    obtain ⟨p, ⟨hpF, hpK⟩, hdist⟩ := Metric.mem_closure_iff.1 hzc _ (half_pos hm)
    refine hpK ((hK.mem_iff p).2 ⟨hpF, fun s hs => ?_⟩)
    have h1 : supp K t0 - dot z (uvec t0) ≤ supp K s - dot z (uvec s) := hmin (cn_jSet_subset hs)
    linarith [(abs_le.1 (abs_dot_uvec_sub_le p z s)).2, dist_comm z p]

/-- **Proposition 2.5.2** (`pro:upper-boundary-connected`). The upper boundary of a cap is
connected. -/
theorem proposition2_5_2 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    IsConnected (upperBoundary K ω) := by
  have hKc := hK.isConvexBody
  set I := Icc (0 : ℝ) (ω + π / 2) with hI
  have hI0 : (0 : ℝ) ∈ I := ⟨le_rfl, by linarith [hK.omega_mem.1, pi_pos]⟩
  have hsub : ∀ t ∈ I, edge K t ⊆ upperBoundary K ω := fun t ht =>
    subset_biUnion_of_mem (u := fun t => edge K t) ht
  have hconv : ∀ t, IsPreconnected (edge K t) := fun t =>
    (hK.convex.inter (convex_line t (supp K t))).isPreconnected
  refine ⟨⟨vplus K 0, hsub 0 hI0 (vplus_mem_edge hKc 0)⟩, ?_⟩
  rw [isPreconnected_iff_subset_of_disjoint]
  intro U V hU hV hcover hdisj
  -- no vertex `v_K⁺(t)`, `t ∈ I`, lies in both `U` and `V`
  have hUV : ∀ t ∈ I, vplus K t ∈ U → vplus K t ∈ V → False := fun t ht h1 h2 =>
    eq_empty_iff_forall_notMem.1 hdisj _ ⟨hsub t ht (vplus_mem_edge hKc t), h1, h2⟩
  -- each edge, being connected, lies in `U` or in `V`
  have hside : ∀ t ∈ I, edge K t ⊆ U ∨ edge K t ⊆ V := fun t ht =>
    isPreconnected_iff_subset_of_disjoint.1 (hconv t) U V hU hV ((hsub t ht).trans hcover)
      (subset_empty_iff.1 fun x hx => hdisj ▸ ⟨hsub t ht hx.1, hx.2⟩)
  -- the vertex `v_K⁺(r)` stays near the edge `e_K(t)` for `r` near `t`
  have hloc : ∀ t ∈ I, ∀ W, IsOpen W → edge K t ⊆ W → ∀ᶠ r in nhds t, vplus K r ∈ W := by
    intro t _ W hW hsubW
    have h1 : vplus K t ∈ W := hsubW (vplus_mem_edge hKc t)
    have h2 : vminus K t ∈ W := hsubW (vminus_mem_edge hKc t)
    have hr : ∀ᶠ r in nhdsWithin t (Ioi t), vplus K r ∈ W :=
      tendsto_vplus_right hKc t (hW.mem_nhds h1)
    have hl : ∀ᶠ r in nhdsWithin t (Iio t), vplus K r ∈ W :=
      tendsto_vplus_left hKc t (hW.mem_nhds h2)
    have hge : ∀ᶠ r in nhdsWithin t (Ici t), vplus K r ∈ W := by
      rw [← Ioi_insert, nhdsWithin_insert]
      exact Filter.eventually_sup.2 ⟨h1, hr⟩
    rw [← nhdsLT_sup_nhdsGE]
    exact Filter.eventually_sup.2 ⟨hl, hge⟩
  -- the parameters whose nearby vertices lie in `U`, resp. `V`, form open sets covering `I`
  set U' := {t : ℝ | ∀ᶠ r in nhds t, r ∈ I → vplus K r ∈ U}
  set V' := {t : ℝ | ∀ᶠ r in nhds t, r ∈ I → vplus K r ∈ V}
  have hU' : IsOpen U' := isOpen_setOfPred_eventually_nhds
  have hV' : IsOpen V' := isOpen_setOfPred_eventually_nhds
  have hcov' : I ⊆ U' ∪ V' := by
    intro t ht
    rcases hside t ht with h | h
    · exact Or.inl ((hloc t ht U hU h).mono fun r hr _ => hr)
    · exact Or.inr ((hloc t ht V hV h).mono fun r hr _ => hr)
  have hdisj' : I ∩ (U' ∩ V') = ∅ := subset_empty_iff.1 fun t ⟨ht, htU, htV⟩ =>
    hUV t ht (htU.self_of_nhds ht) (htV.self_of_nhds ht)
  -- if all the vertices lie in `W`, then so do all the edges
  have key : ∀ W W' : Set (ℝ × ℝ), (∀ t ∈ I, edge K t ⊆ W ∨ edge K t ⊆ W') →
      (∀ t ∈ I, vplus K t ∈ W → vplus K t ∈ W' → False) →
      I ⊆ {t : ℝ | ∀ᶠ r in nhds t, r ∈ I → vplus K r ∈ W} → upperBoundary K ω ⊆ W := by
    intro W W' hs hd hI' z hz
    obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.1 hz
    exact (hs t ht).resolve_right
      (fun h => hd t ht ((hI' ht).self_of_nhds ht) (h (vplus_mem_edge hKc t))) hzt
  -- the interval `I` is connected
  rcases isPreconnected_iff_subset_of_disjoint.1 isPreconnected_Icc U' V' hU' hV' hcov' hdisj'
    with h | h
  · exact Or.inl (key U V hside hUV h)
  · exact Or.inr (key V U (fun t ht => (hside t ht).symm) (fun t ht h1 h2 => hUV t ht h2 h1) h)

/-- **Proposition 2.5.3** (`pro:wedge`). The niche is the union of the wedges. -/
theorem proposition2_5_3 (K : Set (ℝ × ℝ)) (ω : ℝ) :
    niche K ω = ⋃ t ∈ Ioo 0 ω, wedge K ω t := by
  rw [niche, inter_iUnion₂]; rfl

/-! ### Helper lemmas: the mirror reflection `M_ω` -/

private lemma cn_mirror_apply (ω : ℝ) (p : ℝ × ℝ) :
    mirror ω p = (-sin ω * p.1 + cos ω * p.2, cos ω * p.1 + sin ω * p.2) := by
  simp only [mirror, show π / 2 + ω = ω + π / 2 by ring, cos_add_pi_div_two, sin_add_pi_div_two]
  ext
  · simp only
  · simp only; ring

/-- The mirror reflection `M_ω` is an involution. -/
lemma cn_mirror_mirror (ω : ℝ) (p : ℝ × ℝ) : mirror ω (mirror ω p) = p := by
  rw [cn_mirror_apply, cn_mirror_apply]
  ext
  · simp only; linear_combination p.1 * sin_sq_add_cos_sq ω
  · simp only; linear_combination p.2 * sin_sq_add_cos_sq ω

private lemma cn_mirror_involutive (ω : ℝ) : Function.Involutive (mirror ω) := cn_mirror_mirror ω

/-- The mirror reflection of a set is an involution. -/
lemma mirrorCap_mirrorCap (K : Set (ℝ × ℝ)) (ω : ℝ) : mirrorCap (mirrorCap K ω) ω = K := by
  simp only [mirrorCap, Set.image_image, cn_mirror_mirror, Set.image_id']

private lemma cn_mirror_injective (ω : ℝ) : Function.Injective (mirror ω) :=
  (cn_mirror_involutive ω).injective

lemma cn_mirror_image_eq (ω : ℝ) (X : Set (ℝ × ℝ)) : mirror ω '' X = mirror ω ⁻¹' X :=
  congrFun (cn_mirror_involutive ω).image_eq_preimage_symm X

lemma cn_mem_mirror_image {ω : ℝ} {X : Set (ℝ × ℝ)} {p : ℝ × ℝ} :
    p ∈ mirror ω '' X ↔ mirror ω p ∈ X := by
  rw [cn_mirror_image_eq]; rfl

/-- `M_ω(p) · u_t = p · u_{ω + π/2 - t}`. -/
lemma cn_dot_mirror_uvec (ω t : ℝ) (p : ℝ × ℝ) :
    dot (mirror ω p) (uvec t) = dot p (uvec (ω + π / 2 - t)) := by
  rw [cn_mirror_apply, show ω + π / 2 - t = (ω - t) + π / 2 by ring]
  simp only [dot, uvec, cos_add_pi_div_two, sin_add_pi_div_two, sin_sub, cos_sub]
  ring

private lemma cn_dot_mirror_vvec (ω t : ℝ) (p : ℝ × ℝ) :
    dot (mirror ω p) (vvec t) = -dot p (vvec (ω + π / 2 - t)) := by
  rw [cn_mirror_apply, show ω + π / 2 - t = (ω - t) + π / 2 by ring]
  simp only [dot, vvec, cos_add_pi_div_two, sin_add_pi_div_two, sin_sub, cos_sub]
  ring

private lemma cn_mirror_add (ω : ℝ) (p q : ℝ × ℝ) : mirror ω (p + q) = mirror ω p + mirror ω q := by
  simp only [mirror, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
  congr 1 <;> ring

lemma cn_mirror_smul (ω c : ℝ) (p : ℝ × ℝ) : mirror ω (c • p) = c • mirror ω p := by
  simp only [mirror, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.smul_mk]
  congr 1 <;> ring

private lemma cn_mirror_sub (ω : ℝ) (p q : ℝ × ℝ) : mirror ω (p - q) = mirror ω p - mirror ω q := by
  simp only [mirror, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
  congr 1 <;> ring

private lemma cn_mirror_uvec (ω s : ℝ) : mirror ω (uvec s) = uvec (ω + π / 2 - s) := by
  rw [cn_mirror_apply, show ω + π / 2 - s = (ω - s) + π / 2 by ring]
  simp only [uvec, cos_add_pi_div_two, sin_add_pi_div_two, sin_sub, cos_sub]
  ext
  · simp only; ring
  · simp only

private lemma cn_mirror_vvec (ω s : ℝ) : mirror ω (vvec s) = -vvec (ω + π / 2 - s) := by
  rw [cn_mirror_apply, show ω + π / 2 - s = (ω - s) + π / 2 by ring]
  simp only [vvec, cos_add_pi_div_two, sin_add_pi_div_two, sin_sub, cos_sub, Prod.neg_mk]
  ext
  · simp only; ring
  · simp only; ring

/-- `M_ω ∘ R_s = R_{ω - s} ∘ swap`: the swap of coordinates is the reflection of `L`. -/
private lemma cn_mirror_rot (ω s : ℝ) (q : ℝ × ℝ) :
    mirror ω (rot s q) = rot (ω - s) (Prod.swap q) := by
  rw [cn_mirror_apply]
  simp only [rot, Prod.fst_swap, Prod.snd_swap, sin_sub, cos_sub]
  ext
  · simp only; ring
  · simp only; ring

private lemma cn_mirror_continuous (ω : ℝ) : Continuous (mirror ω) := by
  unfold mirror; fun_prop

private lemma cn_mirror_isLinearMap (ω : ℝ) : IsLinearMap ℝ (mirror ω) :=
  ⟨cn_mirror_add ω, cn_mirror_smul ω⟩

/-- `h_{M_ω(K)}(t) = h_K(ω + π/2 - t)`, for every set `K`. -/
private lemma cn_supp_mirror (ω t : ℝ) (K : Set (ℝ × ℝ)) :
    supp (mirror ω '' K) t = supp K (ω + π / 2 - t) := by
  unfold supp
  rw [image_image]
  simp only [cn_dot_mirror_uvec]

private lemma cn_hallwayMap_mirror (ω t : ℝ) (K : Set (ℝ × ℝ)) (q : ℝ × ℝ) :
    hallwayMap (mirror ω '' K) t (Prod.swap q) = mirror ω (hallwayMap K (ω - t) q) := by
  simp only [hallwayMap, cn_supp_mirror, cn_mirror_add, cn_mirror_smul, cn_mirror_rot,
    cn_mirror_uvec, cn_mirror_vvec]
  rw [show ω - (ω - t) = t by ring, show ω + π / 2 - (ω - t) = t + π / 2 by ring,
    show ω + π / 2 - (t + π / 2) = ω - t by ring, show ω + π / 2 - t = ω - t + π / 2 by ring,
    uvec_add_pi_div_two, vvec_add_pi_div_two]
  simp only [neg_neg]
  abel

private lemma cn_image_hallwayMap_mirror (ω t : ℝ) (K X : Set (ℝ × ℝ)) :
    hallwayMap (mirror ω '' K) t '' X =
      mirror ω '' (hallwayMap K (ω - t) '' (Prod.swap '' X)) := by
  rw [image_image, image_image]
  refine image_congr fun q _ => ?_
  rw [← cn_hallwayMap_mirror, Prod.swap_swap]

private lemma cn_swap_hallway : Prod.swap '' hallway = hallway := by
  rw [image_swap_eq_preimage_swap]; ext p
  simp only [mem_preimage, hallway, horizSide, vertSide, mem_union, mem_ofPred_eq, Prod.fst_swap,
    Prod.snd_swap]
  tauto

private lemma cn_swap_aL : Prod.swap '' aL = cL := by
  rw [image_swap_eq_preimage_swap]; ext p; simp [aL, cL]

private lemma cn_swap_bL : Prod.swap '' bL = dL := by
  rw [image_swap_eq_preimage_swap]; ext p; simp [bL, dL]

private lemma cn_swap_cL : Prod.swap '' cL = aL := by
  rw [image_swap_eq_preimage_swap]; ext p; simp [aL, cL]

private lemma cn_swap_dL : Prod.swap '' dL = bL := by
  rw [image_swap_eq_preimage_swap]; ext p; simp [bL, dL]

private lemma cn_swap_qMinusL : Prod.swap '' qMinusL = qMinusL := by
  rw [image_swap_eq_preimage_swap]; ext p; simp [qMinusL, and_comm]

section MirrorParts

variable (K : Set (ℝ × ℝ)) (ω t : ℝ)

private lemma cn_suppHallway_mirror :
    suppHallway (mirror ω '' K) t = mirror ω '' suppHallway K (ω - t) := by
  rw [suppHallway, cn_image_hallwayMap_mirror, cn_swap_hallway]; rfl

private lemma cn_qMinus_mirror : qMinus (mirror ω '' K) t = mirror ω '' qMinus K (ω - t) := by
  rw [qMinus, cn_image_hallwayMap_mirror, cn_swap_qMinusL]; rfl

private lemma cn_innerCorner_mirror :
    innerCorner (mirror ω '' K) t = mirror ω (innerCorner K (ω - t)) := by
  rw [innerCorner, show xL = Prod.swap xL from rfl, cn_hallwayMap_mirror]; rfl

private lemma cn_outerCorner_mirror :
    outerCorner (mirror ω '' K) t = mirror ω (outerCorner K (ω - t)) := by
  rw [outerCorner, show yL = Prod.swap yL from rfl, cn_hallwayMap_mirror]; rfl

private lemma cn_edge_mirror : edge (mirror ω '' K) t = mirror ω '' edge K (ω + π / 2 - t) := by
  ext p
  rw [cn_mem_mirror_image]
  simp only [edge, suppLine, line, mem_inter_iff, mem_ofPred_eq, cn_mem_mirror_image,
    cn_supp_mirror]
  rw [← cn_dot_mirror_uvec, cn_mirror_mirror]

private lemma cn_vplus_mirror :
    vplus (mirror ω '' K) t = mirror ω (vminus K (ω + π / 2 - t)) := by
  rw [vplus, vminus, cn_edge_mirror, image_image, cn_supp_mirror, cn_mirror_add, cn_mirror_smul,
    cn_mirror_smul, cn_mirror_uvec, cn_mirror_vvec, show ω + π / 2 - (ω + π / 2 - t) = t by ring]
  simp only [cn_dot_mirror_vvec]
  rw [← image_image (g := Neg.neg), image_neg_eq_neg, Real.sSup_neg]
  simp only [neg_smul, smul_neg]

private lemma cn_vminus_mirror :
    vminus (mirror ω '' K) t = mirror ω (vplus K (ω + π / 2 - t)) := by
  rw [vplus, vminus, cn_edge_mirror, image_image, cn_supp_mirror, cn_mirror_add, cn_mirror_smul,
    cn_mirror_smul, cn_mirror_uvec, cn_mirror_vvec, show ω + π / 2 - (ω + π / 2 - t) = t by ring]
  simp only [cn_dot_mirror_vvec]
  rw [← image_image (g := Neg.neg), image_neg_eq_neg, Real.sInf_neg]
  simp only [neg_smul, smul_neg]

private lemma cn_fan_mirror : mirror ω '' fan ω = fan ω := by
  ext p
  rw [cn_mem_mirror_image]
  simp only [fan, halfPlus, mem_inter_iff, mem_ofPred_eq, cn_dot_mirror_uvec,
    show ω + π / 2 - ω = π / 2 by ring, show ω + π / 2 - π / 2 = ω by ring]
  exact and_comm

private lemma cn_halfMinus_mirror (s c : ℝ) :
    mirror ω '' halfMinus s c = halfMinus (ω + π / 2 - s) c := by
  ext p
  rw [cn_mem_mirror_image]
  simp only [halfMinus, mem_ofPred_eq, cn_dot_mirror_uvec]

end MirrorParts

/-! **Proposition 2.5.4** (`pro:mirror-reflection`). The parts of the supporting hallway, the cap
and the niche are equivariant under `M_ω`. The paper writes `?_{K^m}(t) = M_ω(?_K(ω - t))` also for
`? = a, b, c, d, W, Z`; since the reflection exchanges the two arms of the hallway, the correct
statement exchanges `a ↔ c`, `b ↔ d` and `W ↔ Z`, as the paper's own next items (`A ↔ C` and
`w ↔ z`) do. The statements below are the corrected ones. -/

/-- **Proposition 2.5.4** (`pro:mirror-reflection`), the cap: the mirror reflection
`K^m = M_ω(K)` of a cap is a cap with the same rotation angle. -/
theorem proposition2_5_4_isCap {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    IsCap (mirrorCap K ω) ω := by
  have hω := hK.omega_mem
  have hpi := pi_pos
  refine ⟨hω, ⟨hK.nonempty.image _, hK.isCompact.image (cn_mirror_continuous ω),
    hK.convex.is_linear_image (cn_mirror_isLinearMap ω)⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mirrorCap, cn_supp_mirror, show ω + π / 2 - ω = π / 2 by ring]
    exact hK.supp_pi_div_two
  · rw [mirrorCap, cn_supp_mirror, show ω + π / 2 - π / 2 = ω by ring]
    exact hK.supp_omega
  · rw [mirrorCap, cn_supp_mirror, show ω + π / 2 - (ω + π) = 3 * π / 2 - 2 * π by ring,
      ← supp_add_two_pi, sub_add_cancel]
    exact hK.supp_three_pi_div_two
  · rw [mirrorCap, cn_supp_mirror, show ω + π / 2 - 3 * π / 2 = (ω + π) - 2 * π by ring,
      ← supp_add_two_pi, sub_add_cancel]
    exact hK.supp_omega_add_pi
  · -- reflect the half-planes; the normal angles `ω + π, 3π/2` are exchanged modulo `2π`
    obtain ⟨ι, t, c, ht, hKeq⟩ := hK.2.2.2.2.2.2
    refine ⟨ι, fun i => if t i ≤ π then ω + π / 2 - t i else ω + π / 2 - t i + 2 * π, c, ?_, ?_⟩
    · intro i
      obtain ⟨hω0, hω1⟩ := hω
      dsimp only
      rcases ht i with (⟨h1, h2⟩ | ⟨h1, h2⟩) | h | h
      · rw [ite_eq_left (by linarith)]
        exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)
      · rw [ite_eq_left (by linarith)]
        exact Or.inl (Or.inl ⟨by linarith, by linarith⟩)
      · rw [ite_eq_right (by linarith), h]
        exact Or.inr (Or.inr (mem_singleton_iff.2 (by ring)))
      · rw [mem_singleton_iff] at h
        rw [ite_eq_right (by linarith), h]
        exact Or.inr (Or.inl (by ring))
    · rw [mirrorCap, hKeq, image_iInter (cn_mirror_involutive ω).bijective]
      congr 1; funext i
      rw [cn_halfMinus_mirror]
      dsimp only
      split_ifs
      · rfl
      · ext p; simp only [halfMinus, mem_ofPred_eq, uvec_add_two_pi]

/-- **Proposition 2.5.4** (`pro:mirror-reflection`), the support function:
`h_{K^m}(t) = h_K(ω + π/2 - t)`. -/
theorem proposition2_5_4_supp {K : Set (ℝ × ℝ)} {ω : ℝ} (t : ℝ) :
    supp (mirrorCap K ω) t = supp K (ω + π / 2 - t) :=
  cn_supp_mirror ω t K

/-- **Proposition 2.5.4** (`pro:mirror-reflection`), the supporting hallway:
`L_{K^m}(t) = M_ω(L_K(ω - t))`, with its inner and outer corners, and with the walls `a ↔ c`,
`b ↔ d` and the wedge endpoints `W ↔ Z` exchanged. -/
theorem proposition2_5_4_hallway {K : Set (ℝ × ℝ)} {ω : ℝ} (t : ℝ) :
    suppHallway (mirrorCap K ω) t = mirror ω '' suppHallway K (ω - t) ∧
      innerCorner (mirrorCap K ω) t = mirror ω (innerCorner K (ω - t)) ∧
      outerCorner (mirrorCap K ω) t = mirror ω (outerCorner K (ω - t)) ∧
      wallA (mirrorCap K ω) t = mirror ω '' wallC K (ω - t) ∧
      wallB (mirrorCap K ω) t = mirror ω '' wallD K (ω - t) ∧
      wallC (mirrorCap K ω) t = mirror ω '' wallA K (ω - t) ∧
      wallD (mirrorCap K ω) t = mirror ω '' wallB K (ω - t) ∧
      wedgeW (mirrorCap K ω) t = mirror ω (wedgeZ K ω (ω - t)) ∧
      wedgeZ (mirrorCap K ω) ω t = mirror ω (wedgeW K (ω - t)) := by
  refine ⟨cn_suppHallway_mirror K ω t, cn_innerCorner_mirror K ω t, cn_outerCorner_mirror K ω t,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mirrorCap, wallA, cn_image_hallwayMap_mirror, cn_swap_aL]; rfl
  · rw [mirrorCap, wallB, cn_image_hallwayMap_mirror, cn_swap_bL]; rfl
  · rw [mirrorCap, wallC, cn_image_hallwayMap_mirror, cn_swap_cL]; rfl
  · rw [mirrorCap, wallD, cn_image_hallwayMap_mirror, cn_swap_dL]; rfl
  · rw [mirrorCap, wedgeW, wedgeZ, cn_supp_mirror, cn_mirror_smul, cn_mirror_vvec,
      show ω - (ω - t) = t by ring, show ω - t + π / 2 = ω + π / 2 - t by ring,
      show ω + π / 2 - ω = π / 2 by ring]
    ext <;> simp [vvec]
  · rw [mirrorCap, wedgeW, wedgeZ, cn_supp_mirror, cn_mirror_apply,
      show ω + π / 2 - (t + π / 2) = ω - t by ring]
    ext
    · simp [vvec]; ring
    · simp [vvec]; ring

/-- **Proposition 2.5.4** (`pro:mirror-reflection`), the vertices:
`A_{K^m}^±(t) = M_ω(C_K^∓(ω - t))` and `C_{K^m}^±(t) = M_ω(A_K^∓(ω - t))`. -/
theorem proposition2_5_4_vertices {K : Set (ℝ × ℝ)} {ω : ℝ} (t : ℝ) :
    aPlus (mirrorCap K ω) t = mirror ω (cMinus K (ω - t)) ∧
      aMinus (mirrorCap K ω) t = mirror ω (cPlus K (ω - t)) ∧
      cPlus (mirrorCap K ω) t = mirror ω (aMinus K (ω - t)) ∧
      cMinus (mirrorCap K ω) t = mirror ω (aPlus K (ω - t)) := by
  simp only [aPlus, aMinus, cPlus, cMinus, mirrorCap, cn_vplus_mirror, cn_vminus_mirror,
    show ω - t + π / 2 = ω + π / 2 - t by ring, show ω + π / 2 - (t + π / 2) = ω - t by ring,
    and_self]

/-- **Proposition 2.5.4** (`pro:mirror-reflection`), the wedge gaps: `w_{K^m}(t) = z_K(ω - t)` and
`z_{K^m}(t) = w_K(ω - t)`. -/
theorem proposition2_5_4_gaps {K : Set (ℝ × ℝ)} {ω : ℝ} (t : ℝ) :
    wedgeGapW (mirrorCap K ω) t = wedgeGapZ K ω (ω - t) ∧
      wedgeGapZ (mirrorCap K ω) ω t = wedgeGapW K (ω - t) := by
  obtain ⟨-, -, -, -, -, -, -, hW, hZ⟩ := proposition2_5_4_hallway (K := K) (ω := ω) t
  obtain ⟨-, hA0, -, -⟩ := proposition2_5_4_vertices (K := K) (ω := ω) 0
  obtain ⟨-, -, hCω, -⟩ := proposition2_5_4_vertices (K := K) (ω := ω) ω
  constructor
  · rw [wedgeGapW, wedgeGapZ, hA0, hW, ← cn_mirror_sub, cn_dot_mirror_uvec, sub_zero, sub_zero,
      ← uvec_add_pi_div_two]
  · rw [wedgeGapW, wedgeGapZ, hCω, hZ, ← cn_mirror_sub, cn_dot_mirror_vvec, sub_self,
      show ω + π / 2 - ω = 0 + π / 2 by ring, vvec_add_pi_div_two, dot_neg_right, neg_neg]

/-- **Proposition 2.5.4** (`pro:mirror-reflection`), the sets: the upper boundary, the wedge
`T_{K^m}(t)` and the niche of `K^m` are the reflections of the upper boundary, the wedge
`T_K(ω - t)` and the niche of `K`. -/
theorem proposition2_5_4_sets {K : Set (ℝ × ℝ)} {ω : ℝ} (t : ℝ) :
    upperBoundary (mirrorCap K ω) ω = mirror ω '' upperBoundary K ω ∧
      wedge (mirrorCap K ω) ω t = mirror ω '' wedge K ω (ω - t) ∧
      niche (mirrorCap K ω) ω = mirror ω '' niche K ω := by
  refine ⟨?_, ?_, ?_⟩
  · ext p
    rw [cn_mem_mirror_image]
    simp only [upperBoundary, mirrorCap, mem_iUnion, cn_edge_mirror, cn_mem_mirror_image, mem_Icc,
      exists_prop]
    constructor
    · rintro ⟨s, hs, h⟩
      exact ⟨ω + π / 2 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, h⟩
    · rintro ⟨s, hs, h⟩
      refine ⟨ω + π / 2 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, ?_⟩
      rwa [show ω + π / 2 - (ω + π / 2 - s) = s by ring]
  · rw [wedge, wedge, mirrorCap, cn_qMinus_mirror, image_inter (cn_mirror_injective ω),
      cn_fan_mirror]
  · ext p
    have hF : p ∈ fan ω ↔ mirror ω p ∈ fan ω := by
      conv_lhs => rw [← cn_fan_mirror]
      exact cn_mem_mirror_image
    rw [cn_mem_mirror_image]
    simp only [niche, mirrorCap, mem_inter_iff, mem_iUnion, cn_qMinus_mirror, cn_mem_mirror_image,
      mem_Ioo, exists_prop, hF]
    constructor
    · rintro ⟨h1, s, hs, h⟩
      exact ⟨h1, ω - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, h⟩
    · rintro ⟨h1, s, hs, h⟩
      refine ⟨h1, ω - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, ?_⟩
      rwa [show ω - (ω - s) = s by ring]

/-- **Proposition 2.5.4** (`pro:mirror-reflection`), the surface area measure: `σ_{K^m}` is the
image of `σ_K` under `t ↦ ω + π/2 - t`. -/
theorem proposition2_5_4_sigma {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    sigma (mirrorCap K ω) = (sigma K).map (fun s => ω + π / 2 - s) := by
  have hKc := hK.isConvexBody
  have hK'c := (proposition2_5_4_isCap hK).isConvexBody
  have hcont : Continuous (supp K) := continuous_supp hK.isCompact
  have hint : ∀ a b, IntervalIntegrable (supp K) MeasureTheory.volume a b :=
    fun a b => hcont.intervalIntegrable a b
  -- the distribution function of `σ_{K^m}` in terms of the left limits of that of `σ_K`
  have hmir : ∀ t, sigmaFun (mirrorCap K ω) t =
      -(dot (vminus K (ω + π / 2 - t)) (vvec (ω + π / 2 - t)) +
        ∫ s in (0 : ℝ)..(ω + π / 2 - t), supp K s) + ∫ s in (0 : ℝ)..(ω + π / 2), supp K s := by
    intro t
    rw [sigmaFun, mirrorCap, cn_vplus_mirror, cn_dot_mirror_vvec]
    simp only [cn_supp_mirror]
    rw [intervalIntegral.integral_comp_sub_left (fun s => supp K s) (ω + π / 2), sub_zero,
      ← intervalIntegral.integral_interval_sub_left (hint 0 (ω + π / 2)) (hint 0 (ω + π / 2 - t))]
    ring
  apply MeasureTheory.Measure.ext_of_Ioc
  intro a b hab
  have hmeas : Measurable fun s : ℝ => ω + π / 2 - s := by fun_prop
  rw [sigma_Ioc hK'c, MeasureTheory.Measure.map_apply hmeas measurableSet_Ioc]
  have hpre : (fun s => ω + π / 2 - s) ⁻¹' Ioc a b = Ico (ω + π / 2 - b) (ω + π / 2 - a) := by
    ext s
    simp only [mem_preimage, mem_Ioc, mem_Ico]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [hpre, sigma, sigmaStieltjes, dite_eq_left hKc, StieltjesFunction.measure_Ico]
  change ENNReal.ofReal _ =
    ENNReal.ofReal (Function.leftLim (sigmaFun K) _ - Function.leftLim (sigmaFun K) _)
  rw [hmir, hmir, leftLim_sigmaFun hKc, leftLim_sigmaFun hKc]
  congr 1
  ring

/-- **Theorem 2.5.5** (`thm:wedge-ends-in-cap`). The wedge gaps are positive. -/
theorem theorem2_5_5 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) {t : ℝ} (ht : t ∈ Ioo 0 ω) :
    0 < wedgeGapW K t ∧ 0 < wedgeGapZ K ω t := by
  obtain ⟨hc, -, -, hc', -, -⟩ := cn_trig_of_mem hK.omega_mem ht
  constructor
  · rw [wedgeGapW, aMinus, dot_sub_left, dot_vminus_uvec, wedgeW, dot_uvec_zero]
    have := hK.gapW_ineq ht
    rw [sub_pos, div_lt_iff₀ hc]; linarith
  · rw [wedgeGapZ, cPlus, dot_sub_left, wedgeZ, ← uvec_add_pi_div_two, dot_vplus_uvec,
      dot_smul_left, dot_uvec_self, mul_one]
    have := hK.gapZ_ineq ht
    rw [sub_pos, div_lt_iff₀ hc']; linarith

/-- **Theorem 2.5.5** in terms of support values: for `t ∈ (0, ω)`,
`h_K(t) - 1 < h_K(0) cos t` and `h_K(t + π/2) - 1 < h_K(ω + π/2) cos (ω - t)`. -/
theorem theorem2_5_5_supp {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) {t : ℝ}
    (ht : t ∈ Ioo 0 ω) :
    supp K t - 1 < supp K 0 * cos t ∧
      supp K (t + π / 2) - 1 < supp K (ω + π / 2) * cos (ω - t) := by
  obtain ⟨hW, hZ⟩ := theorem2_5_5 hK ht
  obtain ⟨hc, -, -, hc', -, -⟩ := cn_trig_of_mem hK.omega_mem ht
  rw [wedgeGapW, aMinus, dot_sub_left, dot_vminus_uvec, wedgeW, dot_uvec_zero, sub_pos,
    div_lt_iff₀ hc] at hW
  rw [wedgeGapZ, cPlus, dot_sub_left, wedgeZ, ← uvec_add_pi_div_two, dot_vplus_uvec,
    dot_smul_left, dot_uvec_self, mul_one, sub_pos, div_lt_iff₀ hc'] at hZ
  constructor <;> linarith

/-! ### Helper lemmas: the quadrant `Q_K⁻(t)` and the wedges -/

private lemma cn_mem_qMinus {K : Set (ℝ × ℝ)} {t : ℝ} {p : ℝ × ℝ} :
    p ∈ qMinus K t ↔ dot p (uvec t) < supp K t - 1 ∧
      dot p (uvec (t + π / 2)) < supp K (t + π / 2) - 1 := by
  rw [proposition2_2_2_qMinus]; rfl

/-- The inner corner `x_K(t)` lies on the lines `l(t, h_K(t) - 1)` and
`l(t + π/2, h_K(t + π/2) - 1)`. -/
lemma cn_innerCorner_dot (K : Set (ℝ × ℝ)) (t : ℝ) :
    dot (innerCorner K t) (uvec t) = supp K t - 1 ∧
      dot (innerCorner K t) (uvec (t + π / 2)) = supp K (t + π / 2) - 1 := by
  rw [proposition2_2_2_innerCorner, uvec_add_pi_div_two]
  simp only [dot_add_left, dot_smul_left, dot_uvec_self, dot_vvec_uvec, dot_uvec_vvec,
    dot_vvec_self]
  constructor <;> ring

/-- The corner `h_K(ω + π/2) v_ω` of a cap, on the line `l(ω, 0)`, lies in the cap. -/
lemma IsCap.corner_mem {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    supp K (ω + π / 2) • vvec ω ∈ K := by
  set H := supp K (ω + π / 2)
  obtain ⟨hω0, hω1⟩ := hK.omega_mem
  have hpu : dot (H • vvec ω) (uvec ω) = 0 := by
    rw [dot_smul_left, dot_vvec_uvec, mul_zero]
  have hpv : dot (H • vvec ω) (vvec ω) = H := by
    rw [dot_smul_left, dot_vvec_self, mul_one]
  obtain ⟨q, hqK, hq⟩ := exists_dot_eq_supp hK.isCompact hK.nonempty (ω + π / 2)
  rw [uvec_add_pi_div_two] at hq
  have hq1 := hK.dot_omega_nonneg hqK
  rw [hK.mem_iff, mem_fan_iff]
  refine ⟨⟨hpu.ge, ?_⟩, fun s hs => ?_⟩
  · -- `H cos ω ≥ 1 - sin ω ≥ 0`, using a point `q'` of `K` with `q' · u_{π/2} = 1`
    obtain ⟨q', hq'K, hq'⟩ := exists_dot_eq_supp hK.isCompact hK.nonempty (π / 2)
    rw [hK.supp_pi_div_two, dot_uvec_eq_cos_add_sin _ _ ω, cos_pi_div_two_sub,
      sin_pi_div_two_sub] at hq'
    have h1 := hK.dot_omega_le_one hq'K
    have h2 := hK.dot_le hq'K (ω + π / 2)
    rw [uvec_add_pi_div_two] at h2
    have hs : 0 ≤ sin ω := sin_nonneg_of_nonneg_of_le_pi hω0.le (by linarith [pi_pos])
    have hc : 0 ≤ cos ω := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hω1⟩
    simp only [Prod.smul_snd, vvec_snd, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 hs, mul_le_mul_of_nonneg_left h2 hc, sin_le_one ω]
  · have hsI := cn_jSet_subset hs
    have hc : 0 ≤ cos (s - ω) := cos_nonneg_of_mem_Icc ⟨by linarith [hsI.1], by linarith [hsI.2]⟩
    refine le_trans ?_ (hK.dot_le hqK s)
    rw [dot_uvec_eq_cos_add_sin _ s ω, dot_uvec_eq_cos_add_sin q s ω, hpu, hpv, hq]
    nlinarith [mul_nonneg hc hq1]

/-- `C_K⁺(ω) = h_K(ω + π/2) v_ω`: the vertex `C_K⁺(ω)` lies on the line `l(ω, 0)`, which the paper
uses without proof (E4 (a)). The corner `h_K(ω + π/2) v_ω` lies on the edge `e_K(ω + π/2)`, of which
`C_K⁺(ω)` is the point farthest in the direction `v_{ω+π/2} = -u_ω`, and `K ⊆ H₊(ω, 0)`. -/
private lemma IsCap.cPlus_eq_corner {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    cPlus K ω = supp K (ω + π / 2) • vvec ω := by
  have hce : supp K (ω + π / 2) • vvec ω ∈ edge K (ω + π / 2) := by
    refine mem_edge_iff.2 ⟨hK.corner_mem, ?_⟩
    rw [uvec_add_pi_div_two, dot_smul_left, dot_vvec_self, mul_one]
  have h1 := dot_le_dot_vplus hK.isCompact hce
  have h2 := hK.dot_omega_nonneg (vplus_mem_edge hK.isConvexBody (ω + π / 2)).1
  rw [vvec_add_pi_div_two, dot_neg_right, dot_neg_right, dot_smul_left, dot_vvec_uvec,
    mul_zero, neg_zero] at h1
  have h3 := dot_vplus_uvec K (ω + π / 2)
  rw [uvec_add_pi_div_two] at h3
  rw [cPlus, eq_dot_uvec_smul_add (vplus K (ω + π / 2)) ω, h3,
    le_antisymm (by linarith) h2, zero_smul, zero_add]

/-- `A_K⁻(0) = (h_K(0), 0)`: the vertex `A_K⁻(0)` lies on the line `l(π/2, 0)`, which the paper uses
without proof (E4 (a)). By Proposition 2.5.4 it is the reflection of the vertex `C_{K^m}⁺(ω)` of the
mirror cap, which lies on `l(ω, 0)`. -/
private lemma IsCap.aMinus_eq_corner {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    aMinus K 0 = (supp K 0, 0) := by
  have h := (proposition2_5_4_vertices (K := K) (ω := ω) ω).2.2.1
  rw [sub_self, (proposition2_5_4_isCap hK).cPlus_eq_corner, proposition2_5_4_supp, sub_self] at h
  rw [← cn_mirror_mirror ω (aMinus K 0), ← h, cn_mirror_smul, cn_mirror_vvec,
    show ω + π / 2 - ω = 0 + π / 2 by ring, vvec_add_pi_div_two, neg_neg, uvec_zero]
  simp

/-- The origin `O` lies in every cap with `ω < π/2`, which the paper uses without proof (E4 (b)):
every defining half-plane `H₋(s, h_K(s))`, `s ∈ J_ω`, contains `O`, as `h_K(s) ≥ A_K⁻(0) · u_s ≥ 0`
for `s ∈ [0, ω]` and `h_K(s) ≥ C_K⁺(ω) · u_s ≥ 0` for `s ∈ [π/2, ω + π/2]` (by E4 (a), and as both
vertices lie in `F_ω`). -/
private lemma IsCap.zero_mem {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (hω : ω < π / 2) :
    (0 : ℝ × ℝ) ∈ K := by
  have hA := (vminus_mem_edge hK.isConvexBody 0).1
  have hC := (vplus_mem_edge hK.isConvexBody (ω + π / 2)).1
  rw [← aMinus, hK.aMinus_eq_corner] at hA
  rw [← cPlus, hK.cPlus_eq_corner] at hC
  obtain ⟨hω0, -⟩ := hK.omega_mem
  have hcos : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω⟩
  have hA0 : 0 ≤ supp K 0 := by
    have h := hK.dot_omega_nonneg hA
    simp only [dot, uvec, zero_mul, add_zero] at h
    exact nonneg_of_mul_nonneg_left h hcos
  have hC0 : 0 ≤ supp K (ω + π / 2) := by
    have h := hK.snd_nonneg hC
    simp only [Prod.smul_snd, vvec_snd, smul_eq_mul] at h
    exact nonneg_of_mul_nonneg_left h hcos
  rw [hK.mem_iff]
  refine ⟨mem_fan_iff.2 (by simp), fun s hs => ?_⟩
  rw [dot_zero_left]
  rcases hs with hs | hs
  · refine le_trans ?_ (hK.dot_le hA s)
    simp only [dot, uvec, zero_mul, add_zero]
    exact mul_nonneg hA0 (cos_nonneg_of_mem_Icc ⟨by linarith [hs.1, pi_pos], by linarith [hs.2]⟩)
  · refine le_trans ?_ (hK.dot_le hC s)
    rw [dot_smul_left, dot_vvec_uvec']
    exact mul_nonneg hC0 (sin_nonneg_of_nonneg_of_le_pi (by linarith [hs.1])
      (by linarith [hs.2, pi_pos]))

/-- The step "a polygon whose vertices lie in the convex set `K` lies in `K`" of Lemma 2.5.6, for a
triangle `P₀ P₁ P₂`: a point `q` whose coordinates in the frame `(u_t, v_t)` are those of
`P₀ + a (P₁ - P₀) + b (P₂ - P₀)`, with `a, b ≥ 0` and `a + b ≤ 1`, lies in `K`. -/
private lemma cn_mem_of_combo {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) {P₀ P₁ P₂ q : ℝ × ℝ}
    (h₀ : P₀ ∈ K) (h₁ : P₁ ∈ K) (h₂ : P₂ ∈ K) {t a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1)
    (hu : dot q (uvec t) = dot P₀ (uvec t) + a * (dot P₁ (uvec t) - dot P₀ (uvec t)) +
      b * (dot P₂ (uvec t) - dot P₀ (uvec t)))
    (hv : dot q (vvec t) = dot P₀ (vvec t) + a * (dot P₁ (vvec t) - dot P₀ (vvec t)) +
      b * (dot P₂ (vvec t) - dot P₀ (vvec t))) : q ∈ K := by
  have hq : q = P₀ + a • (P₁ - P₀) + b • (P₂ - P₀) := eq_of_dot_frame (t := t)
    (by simp only [dot_add_left, dot_smul_left, dot_sub_left, hu])
    (by simp only [dot_add_left, dot_smul_left, dot_sub_left, hv])
  have h := hK.sum_mem (t := Finset.univ) (w := ![1 - a - b, a, b]) (z := ![P₀, P₁, P₂])
    (fun i _ => by fin_cases i <;> simp <;> linarith) (by simp [Fin.sum_univ_three]; ring)
    (fun i _ => by fin_cases i <;> simpa)
  rw [hq]; convert h using 1
  simp [Fin.sum_univ_three]; module

/-- A point of the line `l(π/2, 0)` between two points of a convex set on that line lies in the
set. -/
private lemma cn_axis_mem {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) {r s y : ℝ}
    (hr : ((r, 0) : ℝ × ℝ) ∈ K) (hs : ((s, 0) : ℝ × ℝ) ∈ K) (h1 : r ≤ y) (h2 : y ≤ s) :
    ((y, 0) : ℝ × ℝ) ∈ K :=
  (hK.linear_preimage (LinearMap.inl ℝ ℝ ℝ)).ordConnected.out hr hs ⟨h1, h2⟩

/-- **Lemma 2.5.6** (`lem:niche-in-cap`) outside its third case, by the paper's argument: every
vertex of the wedge `T_K(t)` lies in `K`, so `T_K(t) ⊆ K` by convexity. For `ω = π/2`, `T_K(t)` is
the triangle `W_K(t) x_K(t) Z_K(t)`, and `W_K(t)`, `Z_K(t)` lie on the segment
`[C_K⁺(ω), A_K⁻(0)]` of `l(π/2, 0)` by `w_K(t), z_K(t) > 0` (Theorem 2.5.5). For `ω < π/2` the
cases are on whether `O` lies strictly below `b_K(t)` (`h_K(t) - 1 > 0`) and `d_K(t)`
(`h_K(t + π/2) - 1 > 0`): neither (case 1), `d_K(t)` only (case 2) or both (case 4); `h3` excludes
the third case. In case 1, `T_K(t)` is empty (the paper's contradiction there is a slip, E26).
Points are compared through their coordinates in the frame `(u_t, v_t)`. -/
private lemma cn_wedge_subset_aux {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) {t : ℝ}
    (ht : t ∈ Ioo 0 ω) (hx : innerCorner K t ∈ K)
    (h3 : ¬(ω < π / 2 ∧ supp K (t + π / 2) - 1 ≤ 0 ∧ 0 < supp K t - 1)) :
    wedge K ω t ⊆ K := by
  obtain ⟨hc, hs, -, hC, hS, -⟩ := cn_trig_of_mem hK.omega_mem ht
  have hKc := hK.convex
  -- the coordinates of `x_K(t)`, `W_K(t)` and `Z_K(t)` in the frame `(u_t, v_t)`
  obtain ⟨hx1, hx2⟩ := cn_innerCorner_dot K t
  rw [uvec_add_pi_div_two] at hx2
  have hWu : dot (wedgeW K t) (uvec t) = supp K t - 1 := by
    simp only [wedgeW, dot, uvec]; field_simp; ring
  have hWv : dot (wedgeW K t) (vvec t) = -((supp K t - 1) * sin t / cos t) := by
    simp only [wedgeW, dot, vvec]; ring
  have hZu : dot (wedgeZ K ω t) (uvec t) =
      -((supp K (t + π / 2) - 1) * sin (ω - t) / cos (ω - t)) := by
    rw [wedgeZ, dot_smul_left, dot_vvec_uvec', ← neg_sub ω t, sin_neg]; ring
  have hZv : dot (wedgeZ K ω t) (vvec t) = supp K (t + π / 2) - 1 := by
    rw [wedgeZ, dot_smul_left, dot_vvec_vvec]; field_simp
  -- `w_K(t), z_K(t) > 0` (Theorem 2.5.5), with `A_K⁻(0) = (h_K(0), 0)` and
  -- `C_K⁺(ω) = h_K(ω + π/2) v_ω` in `K` (E4 (a))
  obtain ⟨hw, hz⟩ := theorem2_5_5 hK ht
  rw [wedgeGapW, hK.aMinus_eq_corner, dot_uvec_zero, wedgeW, Prod.mk_sub_mk, sub_pos] at hw
  rw [wedgeGapZ, hK.cPlus_eq_corner, wedgeZ, ← sub_smul, dot_smul_left, dot_vvec_self, mul_one,
    sub_pos] at hz
  have hAK : ((supp K 0, 0) : ℝ × ℝ) ∈ K :=
    hK.aMinus_eq_corner ▸ (vminus_mem_edge hK.isConvexBody 0).1
  have hCK : supp K (ω + π / 2) • vvec ω ∈ K :=
    hK.cPlus_eq_corner ▸ (vplus_mem_edge hK.isConvexBody (ω + π / 2)).1
  -- the conditions `p ∈ F_ω` in the frame
  have hy : ∀ p : ℝ × ℝ, p.2 = sin t * dot p (uvec t) + cos t * dot p (vvec t) := fun p => by
    rw [← dot_uvec_pi_div_two, dot_uvec_eq_cos_add_sin p _ t, cos_pi_div_two_sub,
      sin_pi_div_two_sub]
  obtain ⟨hxω, hxy⟩ := mem_fan_iff.1 (hK.subset_fan hx)
  rw [dot_uvec_eq_cos_add_sin _ ω t, hx1, hx2] at hxω
  rw [hy, hx1, hx2] at hxy
  rintro q ⟨hqF, hqQ⟩
  obtain ⟨hqω, hqy⟩ := mem_fan_iff.1 hqF
  rw [dot_uvec_eq_cos_add_sin _ ω t] at hqω
  rw [hy] at hqy
  rw [cn_mem_qMinus, uvec_add_pi_div_two] at hqQ
  obtain ⟨hA, hB⟩ := hqQ
  set c₁ := supp K t - 1
  set c₂ := supp K (t + π / 2) - 1
  set A := dot q (uvec t)
  set B := dot q (vvec t)
  rcases hK.omega_mem.2.lt_or_eq with hω | rfl
  · -- `ω < π/2`: `O ∈ K` (E4 (b)), and `Z_K(t)` lies on the segment `[O, C_K⁺(ω)]` when
    -- `c₂ ≥ 0`, as `z_K(t) > 0`
    have hO := hK.zero_mem hω
    have hZK : 0 ≤ c₂ → wedgeZ K ω t ∈ K := fun h2 => by
      have hH : 0 < supp K (ω + π / 2) := lt_of_le_of_lt (div_nonneg h2 hC.le) hz
      have := hKc.smul_mem_of_zero_mem hO hCK (t := c₂ / cos (ω - t) / supp K (ω + π / 2))
        ⟨div_nonneg (div_nonneg h2 hC.le) hH.le, (div_le_one hH).2 hz.le⟩
      rwa [smul_smul, div_mul_cancel₀ _ hH.ne'] at this
    rcases le_or_gt c₁ 0 with h1 | h1 <;> rcases le_or_gt c₂ 0 with h2 | h2
    · -- case 1: `O` lies on or above `b_K(t)` and `d_K(t)`, so `Q_K⁻(t)` lies strictly below
      -- `l(π/2, 0)` and `T_K(t)` is empty
      nlinarith [mul_lt_mul_of_pos_left hA hs, mul_lt_mul_of_pos_left hB hc]
    · -- case 2: `T_K(t)` is the triangle `x_K(t) Z_K(t) p` with `p = l(ω, 0) ∩ b_K(t)` on the
      -- segment `[O, Z_K(t)]`
      have hZK := hZK h2.le
      have hY : 0 < cos (ω - t) * c₁ + sin (ω - t) * c₂ := by
        nlinarith [mul_pos hC (sub_pos.2 hA), mul_pos hS (sub_pos.2 hB)]
      have hpK : (-c₁ / sin (ω - t)) • vvec ω ∈ K := by
        have hz0 : 0 < c₂ / cos (ω - t) := div_pos h2 hC
        have := hKc.smul_mem_of_zero_mem hO hZK (t := -c₁ / sin (ω - t) / (c₂ / cos (ω - t)))
          ⟨div_nonneg (div_nonneg (neg_nonneg.2 h1) hS.le) hz0.le, by
            rw [div_le_one hz0, div_le_div_iff₀ hS hC]; nlinarith⟩
        rwa [wedgeZ, smul_smul, div_mul_cancel₀ _ hz0.ne'] at this
      have hpu : dot ((-c₁ / sin (ω - t)) • vvec ω) (uvec t) = c₁ := by
        rw [dot_smul_left, dot_vvec_uvec', ← neg_sub ω t, sin_neg]; field_simp
      have hpv : dot ((-c₁ / sin (ω - t)) • vvec ω) (vvec t) = -c₁ / sin (ω - t) * cos (ω - t) := by
        rw [dot_smul_left, dot_vvec_vvec]
      refine cn_mem_of_combo hKc hx hZK hpK (t := t)
        (a := (c₁ - A) * cos (ω - t) / (cos (ω - t) * c₁ + sin (ω - t) * c₂))
        (b := (c₂ - B) * sin (ω - t) / (cos (ω - t) * c₁ + sin (ω - t) * c₂))
        (div_nonneg (mul_nonneg (by linarith) hC.le) hY.le)
        (div_nonneg (mul_nonneg (by linarith) hS.le) hY.le) ?_ ?_ ?_
      · rw [← add_div, div_le_one hY]; nlinarith
      all_goals
        generalize hYd : cos (ω - t) * c₁ + sin (ω - t) * c₂ = Y at hY ⊢
      · rw [hx1, hZu, hpu]; field_simp; rw [← hYd]; ring
      · rw [hx2, hZv, hpv]; field_simp; rw [← hYd]; ring
    · exact absurd ⟨hω, h2, h1⟩ h3
    · -- case 4: `T_K(t)` is the quadrilateral `x_K(t) Z_K(t) O W_K(t)`, with `W_K(t)` on the
      -- segment `[O, A_K⁻(0)]` as `w_K(t) > 0`; its diagonal `O x_K(t)` cuts it into two triangles
      have hZK := hZK h2.le
      have hA0 : 0 < supp K 0 := lt_trans (div_pos h1 hc) hw
      have hWK : wedgeW K t ∈ K := by
        have := hKc.smul_mem_of_zero_mem hO hAK (t := c₁ / cos t / supp K 0)
          ⟨div_nonneg (div_nonneg h1.le hc.le) hA0.le, (div_le_one hA0).2 hw.le⟩
        rw [Prod.smul_mk, smul_eq_mul, smul_zero, div_mul_cancel₀ _ hA0.ne'] at this
        exact this
      have hX : 0 < sin t * c₁ + cos t * c₂ := add_pos (mul_pos hs h1) (mul_pos hc h2)
      have hY : 0 < cos (ω - t) * c₁ + sin (ω - t) * c₂ := add_pos (mul_pos hC h1) (mul_pos hS h2)
      rcases le_total (B * c₁) (A * c₂) with hBA | hAB
      · -- the triangle `O x_K(t) W_K(t)`
        refine cn_mem_of_combo hKc hO hx hWK (t := t)
          (a := (sin t * A + cos t * B) / (sin t * c₁ + cos t * c₂))
          (b := A / c₁ - (sin t * A + cos t * B) / (sin t * c₁ + cos t * c₂))
          (div_nonneg hqy hX.le) ?_ (by rw [add_sub_cancel, div_le_one h1]; exact hA.le) ?_ ?_
        · rw [sub_nonneg, div_le_div_iff₀ hX h1]; nlinarith [mul_le_mul_of_nonneg_left hBA hc.le]
        · rw [dot_zero_left, hx1, hWu]; field_simp; ring
        · rw [dot_zero_left, hx2, hWv]; field_simp; ring
      · -- the triangle `O x_K(t) Z_K(t)`
        refine cn_mem_of_combo hKc hO hx hZK (t := t)
          (a := (cos (ω - t) * A + sin (ω - t) * B) / (cos (ω - t) * c₁ + sin (ω - t) * c₂))
          (b := B / c₂ - (cos (ω - t) * A + sin (ω - t) * B) /
            (cos (ω - t) * c₁ + sin (ω - t) * c₂))
          (div_nonneg hqω hY.le) ?_ (by rw [add_sub_cancel, div_le_one h2]; exact hB.le) ?_ ?_
        · rw [sub_nonneg, div_le_div_iff₀ hY h2]; nlinarith [mul_le_mul_of_nonneg_left hAB hC.le]
        · rw [dot_zero_left, hx1, hZu]; field_simp; ring
        · rw [dot_zero_left, hx2, hZv]; field_simp; ring
  · -- `ω = π/2`: `T_K(t)` is the triangle `W_K(t) x_K(t) Z_K(t)`; `W_K(t)` and `Z_K(t)` lie on the
    -- segment `[C_K⁺(ω), A_K⁻(0)]` of `l(π/2, 0)`, as `w_K(t), z_K(t) > 0` and `W_K(t)` is further
    -- than `Z_K(t)` in the direction `u_0`
    rw [cos_pi_div_two_sub] at hz
    rw [sin_pi_div_two_sub, cos_pi_div_two_sub] at hZu
    rw [vvec_pi_div_two, Prod.smul_mk, smul_eq_mul, smul_eq_mul, mul_neg, mul_one, mul_zero] at hCK
    have hZ : wedgeZ K (π / 2) t = (-(c₂ / sin t), 0) := by
      simp only [wedgeZ, cos_pi_div_two_sub, vvec_pi_div_two, Prod.smul_mk, smul_eq_mul, mul_neg,
        mul_one, mul_zero]
      rfl
    have hX : 0 < sin t * c₁ + cos t * c₂ := by
      nlinarith [mul_pos hs (sub_pos.2 hA), mul_pos hc (sub_pos.2 hB)]
    have hZW : -(c₂ / sin t) ≤ c₁ / cos t := by
      rw [neg_le_iff_add_nonneg, div_add_div _ _ hc.ne' hs.ne']
      exact div_nonneg (by linarith) (mul_pos hc hs).le
    have hWK : wedgeW K t ∈ K := cn_axis_mem hKc hCK hAK (by linarith) hw.le
    have hZK : wedgeZ K (π / 2) t ∈ K := by
      rw [hZ]; exact cn_axis_mem hKc hCK hAK (by linarith) (by linarith)
    refine cn_mem_of_combo hKc hx hWK hZK (t := t)
      (a := (c₂ - B) * cos t / (sin t * c₁ + cos t * c₂))
      (b := (c₁ - A) * sin t / (sin t * c₁ + cos t * c₂))
      (div_nonneg (mul_nonneg (by linarith) hc.le) hX.le)
      (div_nonneg (mul_nonneg (by linarith) hs.le) hX.le) ?_ ?_ ?_
    · rw [← add_div, div_le_one hX]; nlinarith
    all_goals
      generalize hXd : sin t * c₁ + cos t * c₂ = X at hX ⊢
    · rw [hx1, hWu, hZu]; field_simp; rw [← hXd]; ring
    · rw [hx2, hWv, hZv]; field_simp; rw [← hXd]; ring

/-- **Lemma 2.5.6** (`lem:niche-in-cap`). If the inner corner `x_K(t)` lies in `K`, then so does the
wedge `T_K(t)`. As in the paper, every vertex of `T_K(t)` lies in `K`, so `T_K(t) ⊆ K` by convexity
(`cn_wedge_subset_aux`); the third case follows from the second, applied to the mirror reflection
`K^m` (Proposition 2.5.4). -/
theorem lemma2_5_6 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) {t : ℝ} (ht : t ∈ Ioo 0 ω)
    (hx : innerCorner K t ∈ K) : wedge K ω t ⊆ K := by
  by_cases h3 : ω < π / 2 ∧ supp K (t + π / 2) - 1 ≤ 0 ∧ 0 < supp K t - 1
  · -- case 3: apply the second case to `K^m` with angle `ω - t`, and reflect back
    have ht' : ω - t ∈ Ioo 0 ω := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hx' : innerCorner (mirrorCap K ω) (ω - t) ∈ mirrorCap K ω := by
      rw [(proposition2_5_4_hallway (K := K) (ω - t)).2.1, sub_sub_cancel]
      exact mem_image_of_mem _ hx
    have hsub := cn_wedge_subset_aux (proposition2_5_4_isCap hK) ht' hx' (by
      rw [proposition2_5_4_supp, proposition2_5_4_supp,
        show ω + π / 2 - (ω - t + π / 2) = t by ring, show ω + π / 2 - (ω - t) = t + π / 2 by ring]
      exact fun h => absurd h3.2.2 (not_lt.2 h.2.1))
    intro q hq
    have hq' : mirror ω q ∈ wedge (mirrorCap K ω) ω (ω - t) := by
      rw [(proposition2_5_4_sets (K := K) (ω - t)).2.1, sub_sub_cancel]
      exact mem_image_of_mem _ hq
    simpa only [mirrorCap, cn_mem_mirror_image, cn_mirror_mirror] using hsub hq'
  · exact cn_wedge_subset_aux hK ht hx h3

/-- **Lemma 2.5.7** (`lem:cap-ends-not-in-niche`). The endpoints `A_K⁻(0)` and `C_K⁺(ω)` lie in
`K \ 𝒩(K)`. -/
theorem lemma2_5_7 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    aMinus K 0 ∈ K \ niche K ω ∧ cPlus K ω ∈ K \ niche K ω := by
  have hKc := hK.isConvexBody
  refine ⟨⟨(vminus_mem_edge hKc 0).1, ?_⟩, ⟨(vplus_mem_edge hKc _).1, ?_⟩⟩
  · rintro ⟨-, hU⟩
    obtain ⟨t, ht, hq⟩ := mem_iUnion₂.1 hU
    rw [cn_mem_qMinus] at hq
    have h0 : (aMinus K 0).1 = supp K 0 := by
      rw [← dot_uvec_zero, aMinus, dot_vminus_uvec]
    have h2 : 0 ≤ (aMinus K 0).2 := hK.snd_nonneg (vminus_mem_edge hKc 0).1
    -- `w_K(t) > 0` (Theorem 2.5.5): `A_K⁻(0)` is on the right side of `b_K(t)`
    have hgap := (theorem2_5_5_supp hK ht).1
    obtain ⟨hc, hs, -⟩ := cn_trig_of_mem hK.omega_mem ht
    have h3 : dot (aMinus K 0) (uvec t) = (aMinus K 0).1 * cos t + (aMinus K 0).2 * sin t := rfl
    rw [h3, h0] at hq
    nlinarith [mul_nonneg h2 hs.le]
  · rintro ⟨-, hU⟩
    obtain ⟨t, ht, hq⟩ := mem_iUnion₂.1 hU
    rw [cn_mem_qMinus] at hq
    have hq1 := hq.2
    rw [cn_dot_uvec_decomp _ ω t, cPlus, dot_vplus_uvec] at hq1
    have hω0 := hK.dot_omega_nonneg (vplus_mem_edge hKc (ω + π / 2)).1
    -- `z_K(t) > 0` (Theorem 2.5.5): `C_K⁺(ω)` is on the left side of `d_K(t)`
    have hgap := (theorem2_5_5_supp hK ht).2
    obtain ⟨-, -, -, hc', hs', -⟩ := cn_trig_of_mem hK.omega_mem ht
    nlinarith [mul_nonneg hs'.le hω0]

/-! ### Helper lemmas for Theorem 2.5.8 -/

private lemma cn_isOpen_iUnion_qMinus (K : Set (ℝ × ℝ)) (ω : ℝ) :
    IsOpen (⋃ t ∈ Ioo 0 ω, qMinus K t) :=
  isOpen_biUnion fun t _ => ms_isOpen_qMinus K t

/-- `Q_K⁻(t)` is closed in the direction `-v_0` when `t ∈ [0, π/2]`. -/
private lemma cn_qMinus_down {K : Set (ℝ × ℝ)} {t : ℝ} {p : ℝ × ℝ} (hp : p ∈ qMinus K t)
    (hs : 0 ≤ sin t) (hc : 0 ≤ cos t) {y : ℝ} (hy : y ≤ p.2) : (p.1, y) ∈ qMinus K t := by
  rw [cn_mem_qMinus] at hp ⊢
  simp only [dot, uvec, cos_add_pi_div_two, sin_add_pi_div_two] at hp ⊢
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right hy hs, mul_le_mul_of_nonneg_right hy hc]

/-- The points strictly below the inner corner lie in `Q_K⁻(t)`. -/
private lemma cn_below_corner_mem_qMinus {K : Set (ℝ × ℝ)} {t : ℝ} (hs : 0 < sin t)
    (hc : 0 < cos t) {y : ℝ} (hy : y < (innerCorner K t).2) :
    ((innerCorner K t).1, y) ∈ qMinus K t := by
  obtain ⟨h1, h2⟩ := cn_innerCorner_dot K t
  rw [cn_mem_qMinus, ← h1, ← h2]
  simp only [dot, uvec, cos_add_pi_div_two, sin_add_pi_div_two]
  constructor <;> nlinarith [mul_lt_mul_of_pos_right hy hs, mul_lt_mul_of_pos_right hy hc]

private lemma cn_mem_interior_fan_iff {ω : ℝ} {x : ℝ × ℝ} :
    x ∈ interior (fan ω) ↔ 0 < dot x (uvec ω) ∧ 0 < x.2 := by
  constructor
  · -- an interior point can be moved a little in the directions `-u_ω` and `-v_0` inside `F_ω`
    intro hx
    have key : ∀ v : ℝ × ℝ, ∃ ε : ℝ, 0 < ε ∧ x + ε • v ∈ fan ω := fun v =>
      (((cn_tendsto_add_smul x v).eventually_mem (mem_interior_iff_mem_nhds.1 hx)).and
        self_mem_nhdsWithin).exists.imp fun _ h => ⟨h.2, h.1⟩
    obtain ⟨ε, hε, h⟩ := key (-uvec ω)
    obtain ⟨δ, hδ, h'⟩ := key (-uvec (π / 2))
    have h1 := (mem_fan_iff.1 h).1
    have h2 := (mem_fan_iff.1 h').2
    rw [dot_add_left, dot_smul_left, dot_neg_left, dot_uvec_self] at h1
    simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_neg, uvec_snd, sin_pi_div_two,
      smul_eq_mul] at h2
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    have hO : IsOpen ({p : ℝ × ℝ | 0 < dot p (uvec ω)} ∩ {p | 0 < p.2}) :=
      (isOpen_lt continuous_const (continuous_dot _)).inter
        (isOpen_lt continuous_const continuous_snd)
    exact interior_maximal (fun p hp => mem_fan_iff.2 ⟨hp.1.le, hp.2.le⟩) hO ⟨h1, h2⟩

/-- The set `F_ω \ K` is closed in the direction `v_0`. -/
private lemma IsCap.up_not_mem {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) {z : ℝ × ℝ}
    (hzF : z ∈ fan ω) (hzK : z ∉ K) {y : ℝ} (hy : z.2 ≤ y) : (z.1, y) ∉ K := by
  rw [hK.mem_iff] at hzK
  push Not at hzK
  obtain ⟨s, hs, hlt⟩ := hzK hzF
  have hsI := cn_jSet_subset hs
  have hsin : 0 ≤ sin s := sin_nonneg_of_nonneg_of_le_pi hsI.1
    (by linarith [hsI.2, hK.omega_mem.2])
  intro h
  have h1 := hK.dot_le h s
  have h2 : dot (z.1, y) (uvec s) = z.1 * cos s + y * sin s := rfl
  have h3 : dot z (uvec s) = z.1 * cos s + z.2 * sin s := rfl
  nlinarith [mul_le_mul_of_nonneg_right hy hsin]

/-- The vertex `o_ω = (tan(π/4 - ω/2), 1)` of `P_ω` lies on the line `l(ω, 1)`. -/
lemma oPt_dot_uvec {ω : ℝ} (hω : ω ∈ Icc 0 (π / 2)) : dot (oPt ω) (uvec ω) = 1 := by
  -- `tan(π/4 - ω/2) cos ω = 1 - sin ω` is `tan(δ/2) sin δ = 1 - cos δ` for `δ = π/2 - ω`
  have e : (π / 2 - ω) / 2 = π / 4 - ω / 2 := by ring
  have h := tan_half_mul_sin (δ := π / 2 - ω)
    (cos_pos_of_mem_Ioo ⟨by linarith [hω.2, pi_pos], by linarith [hω.1, pi_pos]⟩).ne'
  rw [e, sin_pi_div_two_sub, cos_pi_div_two_sub] at h
  simp only [dot, oPt, uvec]; linarith

/-- The vertex `o_ω` of `P_ω` lies in every cap with `ω < π/2`. -/
lemma IsCap.oPt_mem {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (hω : ω < π / 2) : oPt ω ∈ K := by
  have hω0 := hK.omega_mem.1
  have hcos : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω⟩
  have ho := oPt_dot_uvec ⟨hω0.le, hω.le⟩
  rw [hK.mem_iff, mem_fan_iff]
  refine ⟨⟨ho ▸ zero_le_one, zero_le_one⟩, fun t ht => ?_⟩
  rcases ht with ht | ht
  · obtain ⟨p, hp, hpt⟩ := exists_dot_eq_supp hK.isCompact hK.nonempty ω
    rw [hK.supp_omega] at hpt
    have hp2 := hK.snd_le_one hp
    have hs : sin (t - ω) ≤ 0 := sin_nonpos_of_nonpos_of_neg_pi_le (by linarith [ht.2])
      (by linarith [ht.1, pi_pos, hω])
    have hD : dot (p - oPt ω) (uvec ω) = 0 := by rw [dot_sub_left, hpt, ho]; ring
    have hD2 : (p - oPt ω).2 ≤ 0 := by simp only [Prod.snd_sub, oPt]; linarith
    have key : dot (p - oPt ω) (uvec t) * cos ω = (p - oPt ω).2 * sin (t - ω) := by
      simp only [dot, uvec, sin_sub] at hD ⊢; linear_combination (cos t) * hD
    have h1 : 0 ≤ dot (p - oPt ω) (uvec t) := by
      by_contra h; rw [not_le] at h; nlinarith [mul_nonneg_of_nonpos_of_nonpos hD2 hs]
    rw [dot_sub_left] at h1
    linarith [hK.dot_le hp t]
  · obtain ⟨p, hp, hpt⟩ := exists_dot_eq_supp hK.isCompact hK.nonempty (π / 2)
    rw [hK.supp_pi_div_two, dot_uvec_pi_div_two] at hpt
    have hpω := hK.dot_omega_le_one hp
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
    linarith [hK.dot_le hp t]

/-- A highest point of `K` on a vertical line lies on the upper boundary `δK`. -/
private lemma IsCap.mem_upperBoundary_of_top {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω)
    {q : ℝ × ℝ} (hqK : q ∈ K) (hmax : ∀ z ∈ K, z.1 = q.1 → z.2 ≤ q.2) :
    q ∈ upperBoundary K ω := by
  have hω := hK.omega_mem
  rw [proposition2_5_1 hK]
  refine ⟨hqK, mem_closure_of_tendsto (cn_tendsto_add_smul q (uvec (π / 2))) ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  refine ⟨cn_add_smul_uvec_mem_fan hω ⟨by linarith [pi_pos], by linarith [hω.1]⟩ hε.le
    (hK.subset_fan hqK), fun h => ?_⟩
  have := hmax _ h (by simp)
  simp only [Prod.snd_add, Prod.smul_snd, uvec_snd, sin_pi_div_two, smul_eq_mul, mul_one] at this
  linarith

/-- An inner corner `x_K(t)` strictly above the line `l(π/2, 0)` lies strictly to the left of
`A_K⁻(0)` (this uses `w_K(t) > 0`). -/
private lemma IsCap.innerCorner_fst_lt {K : Set (ℝ × ℝ)} {ω t : ℝ} (hK : IsCap K ω)
    (ht : t ∈ Ioo 0 ω) (hx : 0 < (innerCorner K t).2) :
    (innerCorner K t).1 < (aMinus K 0).1 := by
  obtain ⟨hc, hs, -⟩ := cn_trig_of_mem hK.omega_mem ht
  have hgap := (theorem2_5_5_supp hK ht).1
  have hxt : dot (innerCorner K t) (uvec t) =
      (innerCorner K t).1 * cos t + (innerCorner K t).2 * sin t := rfl
  rw [(cn_innerCorner_dot K t).1] at hxt
  have h0 : (aMinus K 0).1 = supp K 0 := by rw [← dot_uvec_zero, aMinus, dot_vminus_uvec]
  rw [h0]
  refine lt_of_mul_lt_mul_right ?_ hc.le
  nlinarith [mul_pos hx hs]

/-- An inner corner `x_K(t)` strictly above the line `l(ω, 0)` lies strictly to the right of the
corner `h_K(ω + π/2) v_ω` (this uses `z_K(t) > 0`). -/
private lemma IsCap.corner_fst_lt {K : Set (ℝ × ℝ)} {ω t : ℝ} (hK : IsCap K ω)
    (ht : t ∈ Ioo 0 ω) (hx : 0 < dot (innerCorner K t) (uvec ω)) :
    (supp K (ω + π / 2) • vvec ω).1 < (innerCorner K t).1 := by
  obtain ⟨hc, -, -, hc', -, -⟩ := cn_trig_of_mem hK.omega_mem ht
  have hsω : 0 < sin ω :=
    sin_pos_of_pos_of_lt_pi hK.omega_mem.1 (by linarith [hK.omega_mem.2, pi_pos])
  have hgap := (theorem2_5_5_supp hK ht).2
  have hid : ∀ d : ℝ × ℝ, d.1 * cos (ω - t) =
      cos t * dot d (uvec ω) - sin ω * dot d (uvec (t + π / 2)) := by
    intro d
    simp only [dot, uvec, cos_add_pi_div_two, sin_add_pi_div_two, cos_sub]
    ring
  have e1 := hid (innerCorner K t)
  have e2 := hid (supp K (ω + π / 2) • vvec ω)
  rw [(cn_innerCorner_dot K t).2] at e1
  rw [cn_dot_uvec_decomp _ ω t, uvec_add_pi_div_two] at e2
  simp only [dot_smul_left, dot_vvec_uvec, dot_vvec_self] at e2
  refine lt_of_mul_lt_mul_right ?_ hc'.le
  nlinarith [mul_pos hc hx, mul_pos hsω (sub_pos.2 hgap)]

/-- **Theorem 2.5.8** (`thm:monotonization-connected-iff`). For a cap `K`, the following are
equivalent: (1) `𝒩(K) ⊆ K`; (2) `𝒩(K) ⊆ K \ δK`; (3) for every `t ∈ (0, ω)`, either
`x_K(t) ∉ F_ω°` or `x_K(t) ∈ K`; (4) `K \ 𝒩(K)` is connected. -/
theorem theorem2_5_8 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    List.TFAE [niche K ω ⊆ K, niche K ω ⊆ K \ upperBoundary K ω,
      ∀ t ∈ Ioo 0 ω, innerCorner K t ∉ interior (fan ω) ∨ innerCorner K t ∈ K,
      IsConnected (K \ niche K ω)] := by
  have hω := hK.omega_mem
  tfae_have 1 → 2 := by
    -- `𝒩(K)` is open in `F_ω`, and `δK` is the boundary of `K` in `F_ω` (Proposition 2.5.1)
    intro h1 p hp
    refine ⟨h1 hp, fun hpδ => ?_⟩
    rw [proposition2_5_1 hK] at hpδ
    obtain ⟨hpF, hpU⟩ := hp
    obtain ⟨r, hrU, hrF, hrK⟩ :=
      mem_closure_iff.1 hpδ.2 _ (cn_isOpen_iUnion_qMinus K ω) hpU
    exact hrK (h1 ⟨hrF, hrU⟩)
  tfae_have 2 → 1 := fun h2 p hp => (h2 hp).1
  tfae_have 1 → 3 := by
    -- the points just below an inner corner `x_K(t) ∈ F_ω° \ K` are in `𝒩(K) \ K`
    intro h1 t ht
    by_contra hcon
    push Not at hcon
    obtain ⟨hxF, hxK⟩ := hcon
    obtain ⟨hc, hs, -⟩ := cn_trig_of_mem hω ht
    set x := innerCorner K t
    have hev := (cn_tendsto_add_smul x ((0 : ℝ), (-1 : ℝ))).eventually_mem
      ((isOpen_interior.inter hK.isCompact.isClosed.isOpen_compl).mem_nhds ⟨hxF, hxK⟩)
    obtain ⟨ε, ⟨hεF, hεK⟩, hε : 0 < ε⟩ := (hev.and self_mem_nhdsWithin).exists
    have heq : x + ε • ((0 : ℝ), (-1 : ℝ)) = (x.1, x.2 - ε) := by
      ext <;> simp [sub_eq_add_neg]
    rw [heq] at hεF hεK
    exact hεK (h1 ⟨interior_subset hεF,
      mem_iUnion₂.2 ⟨t, ht, cn_below_corner_mem_qMinus hs hc (by linarith)⟩⟩)
  tfae_have 3 → 1 := by
    -- a nonempty wedge forces `x_K(t) ∈ F_ω°`; then Lemma 2.5.6 applies
    intro h3 p hp
    obtain ⟨hpF, hpU⟩ := hp
    obtain ⟨t, ht, hpt⟩ := mem_iUnion₂.1 hpU
    rcases h3 t ht with hx | hx
    · exfalso
      apply hx
      obtain ⟨hc, hs, -, hc', hs', -⟩ := cn_trig_of_mem hω ht
      obtain ⟨hx1, hx2⟩ := cn_innerCorner_dot K t
      rw [cn_mem_qMinus, ← hx1, ← hx2] at hpt
      have hp1 : (0 : ℝ) ≤ dot p (uvec ω) := hpF.1
      have hp2 : (0 : ℝ) ≤ dot p (uvec (π / 2)) := hpF.2
      have hab : 0 < sin (t + π / 2 - t) := by
        rw [show t + π / 2 - t = π / 2 by ring, sin_pi_div_two]; exact one_pos
      rw [cn_mem_interior_fan_iff, ← dot_uvec_pi_div_two]
      constructor
      · refine lt_of_le_of_lt hp1 (cn_dot_lt_of_between hab ?_ ?_ hpt.1 hpt.2)
        · rw [show t + π / 2 - ω = π / 2 - (ω - t) by ring, sin_pi_div_two_sub]; exact hc'
        · exact hs'
      · refine lt_of_le_of_lt hp2 (cn_dot_lt_of_between hab ?_ ?_ hpt.1 hpt.2)
        · rw [show t + π / 2 - π / 2 = t by ring]; exact hs
        · rw [sin_pi_div_two_sub]; exact hc
    · exact lemma2_5_6 hK ht hx ⟨hpF, hpt⟩
  tfae_have 2 → 4 := by
    -- every point of `K \ 𝒩(K)` is joined to the connected set `δK` by a vertical segment
    intro h2
    have hδS : upperBoundary K ω ⊆ K \ niche K ω := fun z hz =>
      ⟨cn_upperBoundary_subset K ω hz, fun hn => (h2 hn).2 hz⟩
    have hδ := proposition2_5_2 hK
    obtain ⟨z0, hz0⟩ := hδ.nonempty
    refine ⟨⟨z0, hδS hz0⟩, isPreconnected_of_forall z0 fun y hy => ?_⟩
    have hM : IsCompact (K ∩ {z : ℝ × ℝ | z.1 = y.1}) :=
      hK.isCompact.inter_right (isClosed_eq continuous_fst continuous_const)
    -- `q` is a highest point of `K` on the vertical line through `y`
    obtain ⟨q, ⟨hqK, hq1' : q.1 = y.1⟩, hqmax⟩ :=
      hM.exists_isMaxOn ⟨y, hy.1, rfl⟩ continuous_snd.continuousOn
    have hqδ := hK.mem_upperBoundary_of_top hqK fun z hz hz1 => hqmax ⟨hz, hz1.trans hq1'⟩
    have hyq : y.2 ≤ q.2 := hqmax ⟨hy.1, rfl⟩
    refine ⟨upperBoundary K ω ∪ segment ℝ y q, union_subset hδS ?_, Or.inl hz0,
      Or.inr (left_mem_segment _ _ _),
      IsPreconnected.union q hqδ (right_mem_segment _ _ _) hδ.isPreconnected
        (convex_segment y q).isPreconnected⟩
    intro z hz
    refine ⟨hK.convex.segment_subset hy.1 hqK hz, fun hzn => hy.2 ?_⟩
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    obtain ⟨-, hzU⟩ := hzn
    obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.1 hzU
    obtain ⟨hc, hs, -⟩ := cn_trig_of_mem hω ht
    refine ⟨hK.subset_fan hy.1, mem_iUnion₂.2 ⟨t, ht, ?_⟩⟩
    have hz1 : (a • y + b • q).1 = y.1 := by
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, hq1']
      rw [← add_mul, hab, one_mul]
    have hz2 : y.2 ≤ (a • y + b • q).2 := by
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      rw [show a = 1 - b by linarith]
      nlinarith [mul_le_mul_of_nonneg_left hyq hb]
    have := cn_qMinus_down hzt hs.le hc.le hz2
    rwa [hz1] at this
  tfae_have 4 → 3 := by
    -- the vertical line through `x_K(t) ∈ F_ω° \ K` would separate `K \ 𝒩(K)`: no point of
    -- `K \ 𝒩(K)` lies on it, while `A_K⁻(0)` lies to its right and `C_K⁺(ω)` to its left, both in
    -- `K \ 𝒩(K)` by Lemma 2.5.7
    intro h4 t ht
    by_contra hcon
    push Not at hcon
    obtain ⟨hxF, hxK⟩ := hcon
    obtain ⟨hc, hs, -⟩ := cn_trig_of_mem hω ht
    set x := innerCorner K t
    obtain ⟨hxω, hx2⟩ := cn_mem_interior_fan_iff.1 hxF
    have hsplit : K \ niche K ω ⊆ {q : ℝ × ℝ | q.1 < x.1} ∪ {q | x.1 < q.1} := by
      rintro q ⟨hqK, hqN⟩
      rcases lt_trichotomy q.1 x.1 with h | h | h
      · exact Or.inl h
      · exfalso
        rcases le_or_gt x.2 q.2 with h' | h'
        · exact hK.up_not_mem (interior_subset hxF) hxK h' (by rw [← h]; exact hqK)
        · apply hqN
          refine ⟨hK.subset_fan hqK, mem_iUnion₂.2 ⟨t, ht, ?_⟩⟩
          have := cn_below_corner_mem_qMinus (K := K) hs hc h'
          rwa [← h] at this
      · exact Or.inr h
    have hdisj : (K \ niche K ω) ∩ ({q : ℝ × ℝ | q.1 < x.1} ∩ {q | x.1 < q.1}) = ∅ := by
      ext q
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h => lt_asymm h.2.1 h.2.2
    rcases isPreconnected_iff_subset_of_disjoint.1 h4.isPreconnected _ _
      (isOpen_lt continuous_fst continuous_const) (isOpen_lt continuous_const continuous_fst)
      hsplit hdisj with h | h
    · have hA := h (lemma2_5_7 hK).1
      rw [mem_ofPred_eq] at hA
      exact lt_asymm hA (hK.innerCorner_fst_lt ht hx2)
    · have hP := h (lemma2_5_7 hK).2
      rw [mem_ofPred_eq, hK.cPlus_eq_corner] at hP
      exact lt_asymm hP (hK.corner_fst_lt ht hxω)
  tfae_finish

/-! ### Helper lemmas for Theorem 2.5.9 -/

private lemma cn_mem_qPlus {S : Set (ℝ × ℝ)} {t : ℝ} {p : ℝ × ℝ} :
    p ∈ qPlus S t ↔ dot p (uvec t) ≤ supp S t ∧
      dot p (uvec (t + π / 2)) ≤ supp S (t + π / 2) := by
  rw [proposition2_2_2_qPlus]; rfl

/-- A cap is its own `𝓒`. -/
private lemma IsCap.capOf_self {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) : capOf K ω = K := by
  ext p
  simp only [capOf, mem_inter_iff, mem_iInter₂, cn_mem_qPlus]
  constructor
  · rintro ⟨hpP, hpQ⟩
    rw [mem_para_iff] at hpP
    rw [hK.mem_iff]
    refine ⟨mem_fan_iff.2 ⟨hpP.2.1, hpP.1.1⟩, fun s hs => ?_⟩
    rcases hs with hs | hs
    · exact (hpQ s hs).1
    · have := (hpQ (s - π / 2) ⟨by linarith [hs.1], by linarith [hs.2]⟩).2
      rwa [sub_add_cancel] at this
  · intro hp
    exact ⟨hK.subset_para hp, fun t _ => ⟨hK.dot_le hp t, hK.dot_le hp (t + π / 2)⟩⟩

private lemma cn_rot_hallwayMap (K : Set (ℝ × ℝ)) (t : ℝ) (q : ℝ × ℝ) :
    rot (-t) (hallwayMap K t q) + (1 - supp K t, 1 - supp K (t + π / 2)) = q := by
  rw [hallwayMap, rot_add_vec, rot_add_vec, rot_neg_rot, rot_smul, rot_smul, rot_uvec, rot_vvec,
    add_neg_cancel]
  ext
  · simp [uvec, vvec]; ring
  · simp [uvec, vvec]; ring

/-- The movement `t ↦ L_K(ωt)`, seen from the sofa, of a subset of a cap lying in all the
supporting hallways `L_K(t)`, `t ∈ [0, ω]`. -/
private lemma cn_isMovement {K S : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) (hSK : S ⊆ K)
    (hSL : ∀ t ∈ Icc 0 ω, S ⊆ suppHallway K t) :
    IsMovement S ω (fun s => -ω * s)
      (fun s => (1 - supp K (ω * s), 1 - supp K (ω * s + π / 2))) where
  continuousOn_angle := by fun_prop
  continuousOn_shift := by
    have := continuous_supp hK.isCompact
    fun_prop
  angle_zero := by simp
  angle_one := by simp
  start p hp := by
    have hpK := hSK hp
    have h0 := hK.dot_le hpK 0
    rw [dot_uvec_zero] at h0
    simp only [mul_zero, zero_add, rot_zero, hK.supp_pi_div_two, sub_self, horizSide,
      mem_ofPred_eq, Prod.fst_add, Prod.snd_add, add_zero]
    exact ⟨by linarith, hK.snd_nonneg hpK, hK.snd_le_one hpK⟩
  inside s hs p hp := by
    have hω := hK.omega_mem
    have hts : ω * s ∈ Icc 0 ω := ⟨mul_nonneg hω.1.le hs.1, by nlinarith [hs.2, hω.1]⟩
    obtain ⟨q, hq, rfl⟩ := hSL _ hts hp
    simpa only [neg_mul, cn_rot_hallwayMap] using hq
  finish p hp := by
    have hpK := hSK hp
    have h := hK.dot_le hpK (ω + π / 2)
    rw [uvec_add_pi_div_two] at h
    simp only [mul_one, hK.supp_omega, sub_self, vertSide, mem_ofPred_eq, Prod.fst_add,
      Prod.snd_add, add_zero, ms_rot_neg_fst, ms_rot_neg_snd]
    exact ⟨hK.dot_omega_nonneg hpK, hK.dot_omega_le_one hpK, by linarith⟩

/-- **Theorem 2.5.9** (`thm:niche-in-cap`). A cap `K` is the cap of a monotone sofa if and only if
it contains its niche. -/
theorem theorem2_5_9 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    (∃ S, IsMonotoneSofa S ω ∧ capOf S ω = K) ↔ niche K ω ⊆ K := by
  have htfae := theorem2_5_8 hK
  constructor
  · -- `S = K \ 𝒩(K)` is connected (Theorem 2.4.3), so (4) ⇒ (1)
    rintro ⟨S, hS, hcap⟩
    have hSeq := theorem2_4_3 hS
    rw [hcap] at hSeq
    have hconn : IsConnected S := hS.isMovingSofaWithAngle.2.1
    rw [hSeq] at hconn
    exact (htfae.out 4 1).1 hconn
  · -- `S = K \ 𝒩(K) = P_ω ∩ ⋂ L_K(t)` is a moving sofa in standard position with cap `K`
    intro h1
    have hω := hK.omega_mem
    have h2 : niche K ω ⊆ K \ upperBoundary K ω := (htfae.out 1 2).1 h1
    have hconn : IsConnected (K \ niche K ω) := (htfae.out 1 4).1 h1
    have hSK : K \ niche K ω ⊆ K := sdiff_subset
    have hδS : upperBoundary K ω ⊆ K \ niche K ω := fun z hz =>
      ⟨cn_upperBoundary_subset K ω hz, fun hn => (h2 hn).2 hz⟩
    have hSeq' : K \ niche K ω = K \ ⋃ t ∈ Ioo 0 ω, qMinus K t := by
      ext p
      constructor
      · rintro ⟨hpK, hpN⟩; exact ⟨hpK, fun h => hpN ⟨hK.subset_fan hpK, h⟩⟩
      · rintro ⟨hpK, hpU⟩; exact ⟨hpK, fun h => hpU h.2⟩
    have hSclosed : IsClosed (K \ niche K ω) := by
      rw [hSeq']; exact hK.isCompact.isClosed.sdiff (cn_isOpen_iUnion_qMinus K ω)
    have hScpt : IsCompact (K \ niche K ω) := hK.isCompact.of_isClosed_subset hSclosed hSK
    have hSne := hconn.nonempty
    -- `δK ⊆ S ⊆ K`, so `h_S = h_K` on `J_ω`
    have hsuppJ : ∀ s ∈ jSet ω, supp (K \ niche K ω) s = supp K s := by
      intro s hs
      refine le_antisymm (supp_mono hSK hSne hK.isCompact s) ?_
      obtain ⟨q, hqK, hq⟩ := exists_dot_eq_supp hK.isCompact hK.nonempty s
      rw [← hq]
      exact dot_le_supp hScpt (hδS (mem_iUnion₂.2 ⟨s, cn_jSet_subset hs, hqK, hq⟩)) s
    have hSL : ∀ t ∈ Icc 0 ω, K \ niche K ω ⊆ suppHallway K t := by
      rintro t ht p ⟨hpK, hpN⟩
      rw [proposition2_2_2_hallway]
      refine ⟨cn_mem_qPlus.2 ⟨hK.dot_le hpK t, hK.dot_le hpK (t + π / 2)⟩, fun hpQ => ?_⟩
      rcases eq_or_lt_of_le ht.1 with h0 | h0
      · subst h0
        have := (cn_mem_qMinus.1 hpQ).2
        rw [zero_add, hK.supp_pi_div_two, dot_uvec_pi_div_two] at this
        linarith [hK.snd_nonneg hpK]
      rcases eq_or_lt_of_le ht.2 with h1 | h1
      · subst h1
        have := (cn_mem_qMinus.1 hpQ).1
        rw [hK.supp_omega] at this
        linarith [hK.dot_omega_nonneg hpK]
      exact hpN ⟨hK.subset_fan hpK, mem_iUnion₂.2 ⟨t, ⟨h0, h1⟩, hpQ⟩⟩
    have hSofa : IsMovingSofaWithAngle (K \ niche K ω) ω :=
      ⟨hSclosed, hconn, _, _, cn_isMovement hK hSK hSL⟩
    have hstd : IsStandardPosition (K \ niche K ω) ω :=
      ⟨(hsuppJ ω (Or.inl ⟨hω.1.le, le_rfl⟩)).trans hK.supp_omega,
        (hsuppJ (π / 2) (Or.inr ⟨le_rfl, by linarith [hω.1]⟩)).trans hK.supp_pi_div_two⟩
    have hcap : capOf (K \ niche K ω) ω = K := (ms_capOf_congr hsuppJ).trans hK.capOf_self
    -- `S = K \ 𝒩(K) = 𝓘(S)` (Theorem 2.4.2), so `S` is monotone (Theorem 2.4.4)
    have hI : K \ niche K ω = monotonization (K \ niche K ω) ω := by
      rw [theorem2_4_2 hω hSofa hstd, hcap]
    exact ⟨K \ niche K ω, (theorem2_4_4_iff hω hSofa hstd).1 hI, hcap⟩

/-- **Remark 2.5.2** (`rem:niche-not-in-cap`). The cap `[0, 100] × [0, 1]` with rotation angle `π/2`
does not contain its niche. -/
theorem remark2_5_2 : IsCap (Icc (0 : ℝ) 100 ×ˢ Icc 0 1) (π / 2) ∧
    ¬ niche (Icc (0 : ℝ) 100 ×ˢ Icc 0 1) (π / 2) ⊆ Icc (0 : ℝ) 100 ×ˢ Icc 0 1 := by
  set K : Set (ℝ × ℝ) := Icc (0 : ℝ) 100 ×ˢ Icc 0 1 with hKdef
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have h00 : ((0 : ℝ), (0 : ℝ)) ∈ K := ⟨⟨le_rfl, by norm_num⟩, ⟨le_rfl, by norm_num⟩⟩
  have hpi := pi_pos
  have h1 : supp K (π / 2) = 1 := by
    unfold supp
    apply IsGreatest.csSup_eq
    refine ⟨⟨((0 : ℝ), (1 : ℝ)), ⟨⟨le_rfl, by norm_num⟩, ⟨by norm_num, le_rfl⟩⟩, by
      dsimp only; rw [dot_uvec_pi_div_two]⟩, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    dsimp only
    rw [dot_uvec_pi_div_two]; exact hp.2.2
  have h3 : supp K (3 * π / 2) = 0 := by
    unfold supp
    apply IsGreatest.csSup_eq
    refine ⟨⟨((0 : ℝ), (0 : ℝ)), h00, by dsimp only; rw [dot_uvec_three_pi_div_two, neg_zero]⟩,
      ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    dsimp only
    rw [dot_uvec_three_pi_div_two]
    linarith [hp.2.1]
  refine ⟨⟨⟨by positivity, le_rfl⟩, ⟨⟨_, h00⟩, hKc, (convex_Icc _ _).prod (convex_Icc _ _)⟩, h1, h1,
    by rw [show π / 2 + π = 3 * π / 2 by ring]; exact h3, h3, ?_⟩, ?_⟩
  · -- `K` is cut out by the half-planes with normal angles `0, π/2, π, 3π/2`
    refine ⟨Fin 4, ![0, π / 2, π, 3 * π / 2], ![100, 1, 0, 0], ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [jSet]
      · right; right; left; positivity
      · left; positivity
      · right; right; positivity
    · ext p
      have e0 : dot p (uvec 0) = p.1 := dot_uvec_zero p
      have e1 : dot p (uvec (π / 2)) = p.2 := dot_uvec_pi_div_two p
      have e2 : dot p (uvec π) = -p.1 := by simp [dot, uvec]
      have e3 : dot p (uvec (3 * π / 2)) = -p.2 := dot_uvec_three_pi_div_two p
      simp only [mem_iInter, Fin.forall_fin_succ, halfMinus, mem_ofPred_eq, Matrix.cons_val_zero,
        Matrix.cons_val_succ, IsEmpty.forall_iff, and_true]
      simp only [hKdef, mem_prod, mem_Icc]
      rw [e0, e1, e2, e3]
      constructor
      · rintro ⟨⟨a, b⟩, c, d⟩
        exact ⟨b, d, by linarith, by linarith⟩
      · rintro ⟨a, b, c, d⟩
        exact ⟨⟨by linarith, a⟩, by linarith, b⟩
  · -- the point `(50, 2)` lies in the wedge `T_K(π/4)` but not in `K`
    intro h
    have hp : ((50 : ℝ), (2 : ℝ)) ∈ niche K (π / 2) := by
      have hs2 := Real.one_lt_sqrt_two
      have hq1 : (101 : ℝ) * (√2 / 2) ≤ supp K (π / 4) := by
        have := dot_le_supp hKc (p := ((100 : ℝ), (1 : ℝ)))
          ⟨⟨by norm_num, le_rfl⟩, ⟨by norm_num, le_rfl⟩⟩ (π / 4)
        simp only [dot, uvec, cos_pi_div_four, sin_pi_div_four] at this
        linarith
      have hq2 : √2 / 2 ≤ supp K (π / 4 + π / 2) := by
        have := dot_le_supp hKc (p := ((0 : ℝ), (1 : ℝ)))
          ⟨⟨le_rfl, by norm_num⟩, ⟨by norm_num, le_rfl⟩⟩ (π / 4 + π / 2)
        simp only [dot, uvec, cos_add_pi_div_two, sin_add_pi_div_two, cos_pi_div_four,
          sin_pi_div_four] at this
        linarith
      refine ⟨mem_fan_iff.2 ⟨by rw [dot_uvec_pi_div_two]; norm_num, by norm_num⟩,
        mem_iUnion₂.2 ⟨π / 4, ⟨by positivity, by linarith⟩, ?_⟩⟩
      rw [cn_mem_qMinus]
      simp only [dot, uvec, cos_add_pi_div_two, sin_add_pi_div_two, cos_pi_div_four,
        sin_pi_div_four]
      constructor <;> nlinarith
    have := (h hp).2.2
    norm_num at this

/-! ### Helper lemmas for Theorem 2.5.10 -/

private lemma cn_measurableSet_niche (K : Set (ℝ × ℝ)) (ω : ℝ) : MeasurableSet (niche K ω) :=
  (isClosed_fan ω).measurableSet.inter (cn_isOpen_iUnion_qMinus K ω).measurableSet

/-- **Theorem 2.5.10** (`thm:sofa-area-functional`). For the cap `K = 𝓒(S)` of a monotone sofa,
`𝒜_ω(K) = |S|`. -/
theorem theorem2_5_10 {S : Set (ℝ × ℝ)} {ω : ℝ} (hS : IsMonotoneSofa S ω) :
    sofaArea ω (capOf S ω) = area S := by
  have hSeq := theorem2_4_3 hS
  have hcap : IsCap (capOf S ω) ω :=
    theorem2_4_1 hS.1 hS.isMovingSofaWithAngle hS.isStandardPosition
  have hsub : niche (capOf S ω) ω ⊆ capOf S ω := (theorem2_5_9 hcap).1 ⟨S, hS, rfl⟩
  have hfin : MeasureTheory.volume (capOf S ω) ≠ ⊤ := hcap.isCompact.measure_lt_top.ne
  rw [sofaArea, show area S = area (capOf S ω \ niche (capOf S ω) ω) from congrArg area hSeq,
    area, area, area, MeasureTheory.measure_sdiff hsub
      (cn_measurableSet_niche _ ω).nullMeasurableSet
      (ne_top_of_le_ne_top hfin (MeasureTheory.measure_mono hsub)),
    ENNReal.toReal_sub_of_le (MeasureTheory.measure_mono hsub) hfin]

end MovingSofaOptimality
