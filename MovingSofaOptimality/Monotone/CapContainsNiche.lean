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

/-! ### Helper lemmas: vectors and the support function -/

private lemma cn_uvec_three_pi_div_two : uvec (3 * π / 2) = -uvec (π / 2) := by
  rw [show 3 * π / 2 = π / 2 + π by ring, uvec_add_pi]

private lemma cn_dot_uvec_zero (p : ℝ × ℝ) : dot p (uvec 0) = p.1 := by simp [dot, uvec]

private lemma cn_dot_uvec_pi_div_two (p : ℝ × ℝ) : dot p (uvec (π / 2)) = p.2 := by
  simp [dot, uvec]

private lemma cn_vvec_eq_uvec (t : ℝ) : vvec t = uvec (t + π / 2) :=
  (uvec_add_pi_div_two t).symm

private lemma cn_continuous_dot : Continuous (fun x : (ℝ × ℝ) × (ℝ × ℝ) => dot x.1 x.2) := by
  unfold dot; fun_prop

private lemma cn_continuous_dot_left (v : ℝ × ℝ) : Continuous fun p : ℝ × ℝ => dot p v := by
  unfold dot; fun_prop

private lemma cn_continuous_vvec : Continuous vvec := by
  unfold vvec; fun_prop

/-- The support function of a nonempty set contained in a half-plane is bounded by its offset. -/
private lemma cn_supp_le_of_subset {K : Set (ℝ × ℝ)} (hne : K.Nonempty) {t c : ℝ}
    (h : K ⊆ halfMinus t c) : supp K t ≤ c := by
  unfold supp
  apply csSup_le (hne.image _)
  rintro _ ⟨p, hp, rfl⟩
  exact h hp

/-! ### Helper lemmas: basic properties of a cap -/

section Cap

variable {K : Set (ℝ × ℝ)} {ω : ℝ}

private lemma IsCap.omega_mem (hK : IsCap K ω) : ω ∈ Ioc 0 (π / 2) := hK.1
private lemma IsCap.isConvexBody (hK : IsCap K ω) : IsConvexBody K := hK.2.1
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

private lemma IsCap.dot_omega_nonneg (hK : IsCap K ω) {p : ℝ × ℝ} (hp : p ∈ K) :
    0 ≤ dot p (uvec ω) := by
  have h := hK.dot_le hp (ω + π)
  rw [uvec_add_pi, dot_neg_right, hK.supp_omega_add_pi] at h
  linarith

private lemma IsCap.snd_nonneg (hK : IsCap K ω) {p : ℝ × ℝ} (hp : p ∈ K) : 0 ≤ p.2 := by
  have h := hK.dot_le hp (3 * π / 2)
  rw [cn_uvec_three_pi_div_two, dot_neg_right, cn_dot_uvec_pi_div_two,
    hK.supp_three_pi_div_two] at h
  linarith

private lemma IsCap.dot_omega_le_one (hK : IsCap K ω) {p : ℝ × ℝ} (hp : p ∈ K) :
    dot p (uvec ω) ≤ 1 := hK.supp_omega ▸ hK.dot_le hp ω

private lemma IsCap.snd_le_one (hK : IsCap K ω) {p : ℝ × ℝ} (hp : p ∈ K) : p.2 ≤ 1 := by
  have h := hK.dot_le hp (π / 2)
  rwa [cn_dot_uvec_pi_div_two, hK.supp_pi_div_two] at h

private lemma IsCap.mem_fan (hK : IsCap K ω) {p : ℝ × ℝ} (hp : p ∈ K) : p ∈ fan ω :=
  ⟨hK.dot_omega_nonneg hp, by
    show (0 : ℝ) ≤ dot p (uvec (π / 2))
    rw [cn_dot_uvec_pi_div_two]; exact hK.snd_nonneg hp⟩

/-- Membership criterion for a cap: a point of the fan lies in the cap iff it satisfies the
supporting half-plane constraints with normal angles in `J_ω`. -/
private lemma IsCap.mem_iff (hK : IsCap K ω) (p : ℝ × ℝ) :
    p ∈ K ↔ p ∈ fan ω ∧ ∀ s ∈ jSet ω, dot p (uvec s) ≤ supp K s := by
  refine ⟨fun hp => ⟨hK.mem_fan hp, fun s _ => hK.dot_le hp s⟩, ?_⟩
  rintro ⟨hpF, hpJ⟩
  obtain ⟨ι, t, c, ht, hKeq⟩ := hK.2.2.2.2.2.2
  have hsub : ∀ i, K ⊆ halfMinus (t i) (c i) := fun i => hKeq ▸ iInter_subset _ i
  rw [hKeq, mem_iInter]
  intro i
  have hci := cn_supp_le_of_subset hK.nonempty (hsub i)
  show dot p (uvec (t i)) ≤ c i
  rcases ht i with hJ | hi
  · exact (hpJ _ hJ).trans hci
  · rcases hi with hi | hi
    · rw [hi] at hci ⊢
      rw [uvec_add_pi, dot_neg_right]
      rw [hK.supp_omega_add_pi] at hci
      have : (0 : ℝ) ≤ dot p (uvec ω) := hpF.1
      linarith
    · rw [Set.mem_singleton_iff] at hi
      rw [hi] at hci ⊢
      rw [cn_uvec_three_pi_div_two, dot_neg_right]
      rw [hK.supp_three_pi_div_two] at hci
      have : (0 : ℝ) ≤ dot p (uvec (π / 2)) := hpF.2
      linarith

end Cap

/-! ### Helper lemmas: trigonometry -/

private lemma cn_comb (p : ℝ × ℝ) (a b s : ℝ) :
    sin (b - a) * dot p (uvec s) = sin (b - s) * dot p (uvec a) + sin (s - a) * dot p (uvec b) := by
  simp only [dot, uvec, sin_sub]; ring

/-- If `p` is not further than `q` in the directions `u_a` and `u_b`, then neither in any direction
`u_s` between them. -/
private lemma cn_dot_le_of_between {p q : ℝ × ℝ} {a b s : ℝ} (hab : 0 < sin (b - a))
    (h1 : 0 ≤ sin (b - s)) (h2 : 0 ≤ sin (s - a)) (ha : dot p (uvec a) ≤ dot q (uvec a))
    (hb : dot p (uvec b) ≤ dot q (uvec b)) : dot p (uvec s) ≤ dot q (uvec s) := by
  have e1 := cn_comb p a b s
  have e2 := cn_comb q a b s
  by_contra h
  push Not at h
  have : sin (b - a) * (dot q (uvec s) - dot p (uvec s)) < 0 :=
    mul_neg_of_pos_of_neg hab (by linarith)
  nlinarith [mul_nonneg h1 (sub_nonneg.2 ha), mul_nonneg h2 (sub_nonneg.2 hb)]

/-- The strict version of `cn_dot_le_of_between`. -/
private lemma cn_dot_lt_of_between {p q : ℝ × ℝ} {a b s : ℝ} (hab : 0 < sin (b - a))
    (h1 : 0 < sin (b - s)) (h2 : 0 < sin (s - a)) (ha : dot p (uvec a) < dot q (uvec a))
    (hb : dot p (uvec b) < dot q (uvec b)) : dot p (uvec s) < dot q (uvec s) := by
  have e1 := cn_comb p a b s
  have e2 := cn_comb q a b s
  by_contra h
  push Not at h
  have : sin (b - a) * (dot q (uvec s) - dot p (uvec s)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hab.le (by linarith)
  nlinarith [mul_pos h1 (sub_pos.2 ha), mul_pos h2 (sub_pos.2 hb)]

/-- `u_{t+π/2} = cos(ω - t) u_{ω+π/2} + sin(ω - t) u_ω`. -/
private lemma cn_dot_uvec_decomp (q : ℝ × ℝ) (ω t : ℝ) :
    dot q (uvec (t + π / 2)) =
      cos (ω - t) * dot q (uvec (ω + π / 2)) + sin (ω - t) * dot q (uvec ω) := by
  simp only [dot, uvec, cos_add_pi_div_two, sin_add_pi_div_two, sin_sub, cos_sub]
  linear_combination (q.1 * sin t - q.2 * cos t) * sin_sq_add_cos_sq ω

/-- `u_s = cos(s - ω) u_ω + sin(s - ω) v_ω`. -/
private lemma cn_dot_uvec_rot (p : ℝ × ℝ) (s ω : ℝ) :
    dot p (uvec s) = cos (s - ω) * dot p (uvec ω) + sin (s - ω) * dot p (vvec ω) := by
  conv_lhs => rw [show s = (s - ω) + ω by ring]
  simp only [dot, uvec, vvec, cos_add, sin_add]; ring

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
  rw [cn_dot_uvec_zero] at h0
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
  have h1 : (0 : ℝ) ≤ dot p (uvec ω) := hp.1
  have h2 : (0 : ℝ) ≤ dot p (uvec (π / 2)) := hp.2
  constructor
  · show (0 : ℝ) ≤ dot (p + ε • uvec s) (uvec ω)
    rw [dot_add_left, dot_smul_left, dot_uvec_uvec]
    positivity
  · show (0 : ℝ) ≤ dot (p + ε • uvec s) (uvec (π / 2))
    rw [dot_add_left, dot_smul_left, dot_uvec_uvec, cos_sub_pi_div_two]
    positivity

private lemma cn_tendsto_add_smul (p v : ℝ × ℝ) :
    Filter.Tendsto (fun ε : ℝ => p + ε • v) (nhdsWithin 0 (Ioi 0)) (nhds p) := by
  have : Continuous (fun ε : ℝ => p + ε • v) := by fun_prop
  simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds

private lemma cn_dot_sub_le (p q : ℝ × ℝ) (s : ℝ) :
    |dot p (uvec s) - dot q (uvec s)| ≤ 2 * dist p q := by
  rw [← dot_sub_left, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  simp only [dot, uvec, Prod.fst_sub, Prod.snd_sub]
  have h1 := abs_cos_le_one s
  have h2 := abs_sin_le_one s
  have h3 := le_max_left |p.1 - q.1| |p.2 - q.2|
  have h4 := le_max_right |p.1 - q.1| |p.2 - q.2|
  calc |(p.1 - q.1) * cos s + (p.2 - q.2) * sin s|
      ≤ |(p.1 - q.1) * cos s| + |(p.2 - q.2) * sin s| := abs_add_le _ _
    _ = |p.1 - q.1| * |cos s| + |p.2 - q.2| * |sin s| := by rw [abs_mul, abs_mul]
    _ ≤ |p.1 - q.1| * 1 + |p.2 - q.2| * 1 := by gcongr
    _ ≤ 2 * max |p.1 - q.1| |p.2 - q.2| := by linarith

/-- **Proposition 2.5.1** (`pro:upper-boundary-interior`). The upper boundary `δK` is the boundary of
`K` in the subspace topology of the fan `F_ω`, that is `K ∩ closure (F_ω \ K)`. -/
theorem proposition2_5_1 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    upperBoundary K ω = K ∩ closure (fan ω \ K) := by
  ext z
  constructor
  · -- a point of an edge `e_K(t)` is a limit of the points `z + ε u_t ∈ F_ω \ K`
    intro hz
    obtain ⟨t, ht, hzK, hzl⟩ := mem_iUnion₂.1 hz
    refine ⟨hzK, mem_closure_of_tendsto (cn_tendsto_add_smul z (uvec t)) ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine ⟨cn_add_smul_uvec_mem_fan hK.omega_mem ht hε.le (hK.mem_fan hzK), fun h => ?_⟩
    have h1 := hK.dot_le h t
    have h2 : dot z (uvec t) = supp K t := hzl
    rw [dot_add_left, dot_smul_left, dot_uvec_self, h2] at h1
    linarith
  · -- otherwise a ball around `z` meets `F_ω` only inside `K`
    rintro ⟨hzK, hzc⟩
    by_contra hz
    have hlt : ∀ t ∈ Icc 0 (ω + π / 2), dot z (uvec t) < supp K t := by
      intro t ht
      exact lt_of_le_of_ne (hK.dot_le hzK t) (fun h => hz (mem_iUnion₂.2 ⟨t, ht, hzK, h⟩))
    have hcont : Continuous fun t => supp K t - dot z (uvec t) := by
      have := continuous_supp hK.isCompact
      have hu : Continuous uvec := by unfold uvec; fun_prop
      exact this.sub (cn_continuous_dot.comp (continuous_const.prodMk hu))
    obtain ⟨t0, ht0, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := ω + π / 2)).exists_isMinOn
      (nonempty_Icc.2 (by linarith [hK.omega_mem.1, pi_pos])) hcont.continuousOn
    have hm : 0 < supp K t0 - dot z (uvec t0) := sub_pos.2 (hlt t0 ht0)
    obtain ⟨p, ⟨hpF, hpK⟩, hdist⟩ := Metric.mem_closure_iff.1 hzc _ (half_pos hm)
    apply hpK
    rw [hK.mem_iff]
    refine ⟨hpF, fun s hs => ?_⟩
    have h1 : supp K t0 - dot z (uvec t0) ≤ supp K s - dot z (uvec s) :=
      hmin (cn_jSet_subset hs)
    have h2 := cn_dot_sub_le p z s
    rw [dist_comm] at hdist
    have h3 := (abs_le.1 h2).2
    linarith

/-- **Proposition 2.5.2** (`pro:upper-boundary-connected`). The upper boundary of a cap is
connected. -/
theorem proposition2_5_2 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    IsConnected (upperBoundary K ω) := by
  have hKc := hK.isConvexBody
  set I := Icc (0 : ℝ) (ω + π / 2) with hI
  have hI0 : (0 : ℝ) ∈ I := ⟨le_rfl, by linarith [hK.omega_mem.1, pi_pos]⟩
  have hsub : ∀ t ∈ I, edge K t ⊆ upperBoundary K ω := fun t ht =>
    subset_biUnion_of_mem (u := fun t => edge K t) ht
  have hconv : ∀ t, IsPreconnected (edge K t) := by
    intro t
    refine (hK.convex.inter ?_).isPreconnected
    have : suppLine K t = {p | dot p (uvec t) = supp K t} := rfl
    rw [this]
    exact (convex_hyperplane (f := fun p : ℝ × ℝ => dot p (uvec t))
      ⟨fun x y => dot_add_left x y _, fun c x => dot_smul_left c x _⟩ _)
  refine ⟨⟨vplus K 0, hsub 0 hI0 (vplus_mem_edge hKc 0)⟩, ?_⟩
  rw [isPreconnected_iff_subset_of_disjoint]
  intro U V hU hV hcover hdisj
  -- each edge, being connected, lies in `U` or in `V`
  have hside : ∀ t ∈ I, edge K t ⊆ U ∨ edge K t ⊆ V := by
    intro t ht
    refine isPreconnected_iff_subset_of_disjoint.1 (hconv t) U V hU hV
      ((hsub t ht).trans hcover) ?_
    apply subset_empty_iff.1
    intro x hx
    rw [← hdisj]
    exact ⟨hsub t ht hx.1, hx.2⟩
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
  set U' := {t : ℝ | ∀ᶠ r in nhds t, r ∈ I → vplus K r ∈ U}
  set V' := {t : ℝ | ∀ᶠ r in nhds t, r ∈ I → vplus K r ∈ V}
  have hU' : IsOpen U' := isOpen_setOfPred_eventually_nhds
  have hV' : IsOpen V' := isOpen_setOfPred_eventually_nhds
  have hcov' : I ⊆ U' ∪ V' := by
    intro t ht
    rcases hside t ht with h | h
    · exact Or.inl ((hloc t ht U hU h).mono fun r hr _ => hr)
    · exact Or.inr ((hloc t ht V hV h).mono fun r hr _ => hr)
  have hdisj' : I ∩ (U' ∩ V') = ∅ := by
    apply subset_empty_iff.1
    rintro t ⟨ht, htU, htV⟩
    have : vplus K t ∈ upperBoundary K ω ∩ (U ∩ V) :=
      ⟨hsub t ht (vplus_mem_edge hKc t), htU.self_of_nhds ht, htV.self_of_nhds ht⟩
    rw [hdisj] at this
    exact this
  have key : ∀ (W W' : Set (ℝ × ℝ)), (∀ t ∈ I, edge K t ⊆ W ∨ edge K t ⊆ W') →
      upperBoundary K ω ∩ (W ∩ W') = ∅ →
      I ⊆ {t : ℝ | ∀ᶠ r in nhds t, r ∈ I → vplus K r ∈ W} → upperBoundary K ω ⊆ W := by
    intro W W' hs hd hI' z hz
    obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.1 hz
    rcases hs t ht with h' | h'
    · exact h' hzt
    · exfalso
      have h1 : vplus K t ∈ W := (hI' ht).self_of_nhds ht
      have h2 : vplus K t ∈ W' := h' (vplus_mem_edge hKc t)
      have : vplus K t ∈ upperBoundary K ω ∩ (W ∩ W') :=
        ⟨hsub t ht (vplus_mem_edge hKc t), h1, h2⟩
      rw [hd] at this
      exact this
  rcases isPreconnected_iff_subset_of_disjoint.1 isPreconnected_Icc U' V' hU' hV' hcov' hdisj'
    with h | h
  · exact Or.inl (key U V hside hdisj h)
  · refine Or.inr (key V U (fun t ht => (hside t ht).symm) ?_ h)
    rw [inter_comm V U]; exact hdisj

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

private lemma cn_mirror_mirror (ω : ℝ) (p : ℝ × ℝ) : mirror ω (mirror ω p) = p := by
  rw [cn_mirror_apply, cn_mirror_apply]
  ext
  · simp only; linear_combination p.1 * sin_sq_add_cos_sq ω
  · simp only; linear_combination p.2 * sin_sq_add_cos_sq ω

private lemma cn_mirror_involutive (ω : ℝ) : Function.Involutive (mirror ω) := cn_mirror_mirror ω

private lemma cn_mirror_injective (ω : ℝ) : Function.Injective (mirror ω) :=
  (cn_mirror_involutive ω).injective

private lemma cn_mirror_image_eq (ω : ℝ) (X : Set (ℝ × ℝ)) : mirror ω '' X = mirror ω ⁻¹' X :=
  congrFun (cn_mirror_involutive ω).image_eq_preimage_symm X

private lemma cn_mem_mirror_image {ω : ℝ} {X : Set (ℝ × ℝ)} {p : ℝ × ℝ} :
    p ∈ mirror ω '' X ↔ mirror ω p ∈ X := by
  rw [cn_mirror_image_eq]; rfl

private lemma cn_dot_mirror_uvec (ω t : ℝ) (p : ℝ × ℝ) :
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
  ext
  · simp only; ring
  · simp only; ring

private lemma cn_mirror_smul (ω c : ℝ) (p : ℝ × ℝ) : mirror ω (c • p) = c • mirror ω p := by
  simp only [mirror, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.smul_mk]
  ext
  · simp only; ring
  · simp only; ring

private lemma cn_mirror_neg (ω : ℝ) (p : ℝ × ℝ) : mirror ω (-p) = -mirror ω p := by
  simp only [mirror, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk]
  ext
  · simp only; ring
  · simp only; ring

private lemma cn_mirror_sub (ω : ℝ) (p q : ℝ × ℝ) : mirror ω (p - q) = mirror ω p - mirror ω q := by
  rw [sub_eq_add_neg, cn_mirror_add, cn_mirror_neg, ← sub_eq_add_neg]

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
      have hω0 := hω.1
      have hω1 := hω.2
      dsimp only
      rcases ht i with (h | h) | h
      · have h' : t i ≤ π := by linarith [h.2]
        simp only [h', ite_true]
        left; right; constructor <;> linarith [h.1, h.2]
      · have h' : t i ≤ π := by linarith [h.2]
        simp only [h', ite_true]
        left; left; constructor <;> linarith [h.1, h.2]
      · rcases h with h | h
        · have h' : ¬ t i ≤ π := by linarith
          rw [ite_eq_right h', h]
          right; right; rw [mem_singleton_iff]; ring
        · rw [mem_singleton_iff] at h
          have h' : ¬ t i ≤ π := by linarith
          rw [ite_eq_right h', h]
          right; left; ring
    · rw [mirrorCap, hKeq, image_iInter (cn_mirror_involutive ω).bijective]
      congr 1; funext i
      rw [cn_halfMinus_mirror]
      dsimp only
      split_ifs
      · rfl
      · ext p; simp only [halfMinus, mem_ofPred_eq, uvec_add_two_pi]

theorem proposition2_5_4_supp {K : Set (ℝ × ℝ)} {ω : ℝ} (t : ℝ) :
    supp (mirrorCap K ω) t = supp K (ω + π / 2 - t) := by
  exact cn_supp_mirror ω t K

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

theorem proposition2_5_4_vertices {K : Set (ℝ × ℝ)} {ω : ℝ} (t : ℝ) :
    aPlus (mirrorCap K ω) t = mirror ω (cMinus K (ω - t)) ∧
      aMinus (mirrorCap K ω) t = mirror ω (cPlus K (ω - t)) ∧
      cPlus (mirrorCap K ω) t = mirror ω (aMinus K (ω - t)) ∧
      cMinus (mirrorCap K ω) t = mirror ω (aPlus K (ω - t)) := by
  simp only [aPlus, aMinus, cPlus, cMinus, mirrorCap, cn_vplus_mirror, cn_vminus_mirror,
    show ω - t + π / 2 = ω + π / 2 - t by ring, show ω + π / 2 - (t + π / 2) = ω - t by ring,
    and_self]

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

/-- The left limit of the distribution function of `σ_K`: `v_K⁺(s) → v_K⁻(t)` as `s → t⁻`. -/
private lemma cn_leftLim_sigmaFun {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (d : ℝ) :
    Function.leftLim (sigmaFun K) d =
      dot (vminus K d) (vvec d) + ∫ s in (0 : ℝ)..d, supp K s := by
  have hcont : Continuous (supp K) := continuous_supp hK.2.1
  apply leftLim_eq_of_tendsto
  have h1 : Filter.Tendsto (vplus K) (nhdsWithin d (Iio d)) (nhds (vminus K d)) :=
    tendsto_vplus_left hK d
  have h2 : Filter.Tendsto vvec (nhdsWithin d (Iio d)) (nhds (vvec d)) :=
    (cn_continuous_vvec.tendsto d).mono_left nhdsWithin_le_nhds
  have h3 : Filter.Tendsto (fun t => ∫ s in (0 : ℝ)..t, supp K s) (nhdsWithin d (Iio d))
      (nhds (∫ s in (0 : ℝ)..d, supp K s)) :=
    ((intervalIntegral.continuous_primitive (fun a b => hcont.intervalIntegrable a b) 0).tendsto
      d).mono_left nhdsWithin_le_nhds
  exact ((cn_continuous_dot.tendsto _).comp (h1.prodMk_nhds h2)).add h3

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
  rw [hmir, hmir, cn_leftLim_sigmaFun hKc, cn_leftLim_sigmaFun hKc]
  congr 1
  ring

/-- **Theorem 2.5.5** (`thm:wedge-ends-in-cap`). The wedge gaps are positive. -/
theorem theorem2_5_5 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) {t : ℝ} (ht : t ∈ Ioo 0 ω) :
    0 < wedgeGapW K t ∧ 0 < wedgeGapZ K ω t := by
  obtain ⟨hc, -, -, hc', -, -⟩ := cn_trig_of_mem hK.omega_mem ht
  constructor
  · rw [wedgeGapW, aMinus, dot_sub_left, dot_vminus_uvec, wedgeW, cn_dot_uvec_zero]
    have := hK.gapW_ineq ht
    rw [sub_pos, div_lt_iff₀ hc]; linarith
  · rw [wedgeGapZ, cPlus, dot_sub_left, wedgeZ, cn_vvec_eq_uvec, dot_vplus_uvec, dot_smul_left,
      dot_uvec_self, mul_one]
    have := hK.gapZ_ineq ht
    rw [sub_pos, div_lt_iff₀ hc']; linarith

/-! ### Helper lemmas: the quadrant `Q_K⁻(t)` and the wedges -/

private lemma cn_mem_qMinus {K : Set (ℝ × ℝ)} {t : ℝ} {p : ℝ × ℝ} :
    p ∈ qMinus K t ↔ dot p (uvec t) < supp K t - 1 ∧
      dot p (uvec (t + π / 2)) < supp K (t + π / 2) - 1 := by
  rw [proposition2_2_2_qMinus]; rfl

private lemma cn_innerCorner_dot (K : Set (ℝ × ℝ)) (t : ℝ) :
    dot (innerCorner K t) (uvec t) = supp K t - 1 ∧
      dot (innerCorner K t) (uvec (t + π / 2)) = supp K (t + π / 2) - 1 := by
  rw [proposition2_2_2_innerCorner, ← cn_vvec_eq_uvec]
  simp only [dot_add_left, dot_smul_left, dot_uvec_self, dot_vvec_uvec, dot_uvec_vvec,
    dot_vvec_self]
  constructor <;> ring

/-- Every point of a wedge satisfies the supporting constraints of `K` with normal angles in
`[0, t]` (this uses only `w_K(t) > 0`). -/
private lemma cn_wedge_dot_le_low {K : Set (ℝ × ℝ)} {ω t : ℝ} (hK : IsCap K ω) (ht : t ∈ Ioo 0 ω)
    {p : ℝ × ℝ} (hp : p ∈ wedge K ω t) {s : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) :
    dot p (uvec s) ≤ supp K s := by
  obtain ⟨hc, hsn, -, -, -, -⟩ := cn_trig_of_mem hK.omega_mem ht
  have hgap := hK.gapW_ineq ht
  obtain ⟨hpF, hpQ⟩ := hp
  rw [cn_mem_qMinus] at hpQ
  have hp2 : (0 : ℝ) ≤ p.2 := by
    have : (0 : ℝ) ≤ dot p (uvec (π / 2)) := hpF.2
    rwa [cn_dot_uvec_pi_div_two] at this
  obtain ⟨q, hqK, hq⟩ := exists_dot_eq_supp hK.isCompact hK.nonempty 0
  rw [cn_dot_uvec_zero] at hq
  have hq2 := hK.snd_nonneg hqK
  have ht1 : t < π := by linarith [ht.2, hK.omega_mem.2, pi_pos]
  refine (cn_dot_le_of_between (a := 0) (b := t) (q := q) ?_ ?_ ?_ ?_ ?_).trans (hK.dot_le hqK s)
  · rw [sub_zero]; exact hsn
  · exact sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  · rw [sub_zero]; exact sin_nonneg_of_nonneg_of_le_pi hs0 (by linarith)
  · -- `p.1 < h_K(0) = q.1`
    rw [cn_dot_uvec_zero, cn_dot_uvec_zero, hq]
    have h1 : dot p (uvec t) = p.1 * cos t + p.2 * sin t := rfl
    have h2 : p.1 * cos t < supp K 0 * cos t := by nlinarith [mul_nonneg hp2 hsn.le]
    exact (lt_of_mul_lt_mul_right h2 hc.le).le
  · have h1 : dot q (uvec t) = q.1 * cos t + q.2 * sin t := rfl
    rw [h1, hq]
    nlinarith [mul_nonneg hq2 hsn.le]

/-- Every point of a wedge satisfies the supporting constraints of `K` with normal angles in
`[t + π/2, ω + π/2]` (this uses only `z_K(t) > 0`). -/
private lemma cn_wedge_dot_le_high {K : Set (ℝ × ℝ)} {ω t : ℝ} (hK : IsCap K ω) (ht : t ∈ Ioo 0 ω)
    {p : ℝ × ℝ} (hp : p ∈ wedge K ω t) {s : ℝ} (hs0 : t + π / 2 ≤ s) (hst : s ≤ ω + π / 2) :
    dot p (uvec s) ≤ supp K s := by
  obtain ⟨-, -, -, hc, hsn, -⟩ := cn_trig_of_mem hK.omega_mem ht
  have hgap := hK.gapZ_ineq ht
  obtain ⟨hpF, hpQ⟩ := hp
  rw [cn_mem_qMinus] at hpQ
  have hp1 : (0 : ℝ) ≤ dot p (uvec ω) := hpF.1
  obtain ⟨q, hqK, hq⟩ := exists_dot_eq_supp hK.isCompact hK.nonempty (ω + π / 2)
  have hq1 := hK.dot_omega_nonneg hqK
  have hω := hK.omega_mem
  refine (cn_dot_le_of_between (a := t + π / 2) (b := ω + π / 2) (q := q) ?_ ?_ ?_ ?_ ?_).trans
    (hK.dot_le hqK s)
  · rw [show ω + π / 2 - (t + π / 2) = ω - t by ring]; exact hsn
  · exact sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [ht.1, ht.2, hω.2, pi_pos])
  · exact sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [ht.1, ht.2, hω.2, pi_pos])
  · rw [cn_dot_uvec_decomp q ω t, hq]
    nlinarith [mul_nonneg hsn.le hq1]
  · -- `p · u_{ω+π/2} < h_K(ω + π/2)`
    rw [hq]
    have h1 := cn_dot_uvec_decomp p ω t
    have h2 : cos (ω - t) * dot p (uvec (ω + π / 2)) < cos (ω - t) * supp K (ω + π / 2) := by
      nlinarith [mul_nonneg hsn.le hp1]
    exact (lt_of_mul_lt_mul_left h2 hc.le).le

/-- **Lemma 2.5.6** (`lem:niche-in-cap`). If the inner corner `x_K(t)` lies in `K`, then so does the
wedge `T_K(t)`. -/
theorem lemma2_5_6 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) {t : ℝ} (ht : t ∈ Ioo 0 ω)
    (hx : innerCorner K t ∈ K) : wedge K ω t ⊆ K := by
  intro p hp
  rw [hK.mem_iff]
  refine ⟨hp.1, fun s hs => ?_⟩
  have hsI := cn_jSet_subset hs
  rcases le_total s t with hst | hts
  · exact cn_wedge_dot_le_low hK ht hp hsI.1 hst
  rcases le_total s (t + π / 2) with hst' | hts'
  · -- between `t` and `t + π/2`: compare with the inner corner
    obtain ⟨hx1, hx2⟩ := cn_innerCorner_dot K t
    have hpQ := hp.2
    rw [cn_mem_qMinus] at hpQ
    refine (cn_dot_le_of_between (a := t) (b := t + π / 2) (q := innerCorner K t)
      ?_ ?_ ?_ ?_ ?_).trans (hK.dot_le hx s)
    · rw [show t + π / 2 - t = π / 2 by ring, sin_pi_div_two]; exact one_pos
    · exact sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos])
    · exact sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos])
    · rw [hx1]; exact hpQ.1.le
    · rw [hx2]; exact hpQ.2.le
  · exact cn_wedge_dot_le_high hK ht hp hts' hsI.2

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
      rw [← cn_dot_uvec_zero, aMinus, dot_vminus_uvec]
    have h2 : 0 ≤ (aMinus K 0).2 := hK.snd_nonneg (vminus_mem_edge hKc 0).1
    have hgap := hK.gapW_ineq ht
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
    have hgap := hK.gapZ_ineq ht
    obtain ⟨-, -, -, hc', hs', -⟩ := cn_trig_of_mem hK.omega_mem ht
    nlinarith [mul_nonneg hs'.le hω0]

/-! ### Helper lemmas for Theorem 2.5.8 -/

private lemma cn_isOpen_qMinus (K : Set (ℝ × ℝ)) (t : ℝ) : IsOpen (qMinus K t) := by
  have : qMinus K t = {p | dot p (uvec t) < supp K t - 1} ∩
      {p | dot p (uvec (t + π / 2)) < supp K (t + π / 2) - 1} := by
    ext p; exact cn_mem_qMinus
  rw [this]
  exact (isOpen_lt (cn_continuous_dot_left _) continuous_const).inter
    (isOpen_lt (cn_continuous_dot_left _) continuous_const)

private lemma cn_isOpen_iUnion_qMinus (K : Set (ℝ × ℝ)) (ω : ℝ) :
    IsOpen (⋃ t ∈ Ioo 0 ω, qMinus K t) :=
  isOpen_biUnion fun t _ => cn_isOpen_qMinus K t

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
  · intro hx
    have key : ∀ v : ℝ × ℝ, ∃ ε : ℝ, 0 < ε ∧ x + ε • v ∈ fan ω := by
      intro v
      have hev := (cn_tendsto_add_smul x v).eventually_mem (mem_interior_iff_mem_nhds.1 hx)
      obtain ⟨ε, h1, h2⟩ := (hev.and self_mem_nhdsWithin).exists
      exact ⟨ε, h2, h1⟩
    obtain ⟨ε, hε, h⟩ := key (-uvec ω)
    obtain ⟨δ, hδ, h'⟩ := key (-uvec (π / 2))
    have h1 : (0 : ℝ) ≤ dot (x + ε • -uvec ω) (uvec ω) := h.1
    have h2 : (0 : ℝ) ≤ dot (x + δ • -uvec (π / 2)) (uvec (π / 2)) := h'.2
    rw [dot_add_left, dot_smul_left, dot_neg_left, dot_uvec_self] at h1 h2
    rw [cn_dot_uvec_pi_div_two] at h2
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    have hO : IsOpen ({p : ℝ × ℝ | 0 < dot p (uvec ω)} ∩ {p | 0 < p.2}) :=
      (isOpen_lt continuous_const (cn_continuous_dot_left _)).inter
        (isOpen_lt continuous_const continuous_snd)
    refine interior_maximal ?_ hO ⟨h1, h2⟩
    rintro p ⟨hp1, hp2⟩
    refine ⟨?_, ?_⟩
    · show (0 : ℝ) ≤ dot p (uvec ω)
      exact le_of_lt hp1
    show (0 : ℝ) ≤ dot p (uvec (π / 2))
    rw [cn_dot_uvec_pi_div_two]; exact le_of_lt hp2

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

/-- The corner `h_K(ω + π/2) v_ω` of a cap, on the line `l(ω, 0)`, lies in the cap. -/
private lemma IsCap.corner_mem {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    supp K (ω + π / 2) • vvec ω ∈ K := by
  set H := supp K (ω + π / 2)
  obtain ⟨hω0, hω1⟩ := hK.omega_mem
  have hpu : dot (H • vvec ω) (uvec ω) = 0 := by
    rw [dot_smul_left, dot_vvec_uvec, mul_zero]
  have hpv : dot (H • vvec ω) (vvec ω) = H := by
    rw [dot_smul_left, dot_vvec_self, mul_one]
  obtain ⟨q, hqK, hq⟩ := exists_dot_eq_supp hK.isCompact hK.nonempty (ω + π / 2)
  rw [← cn_vvec_eq_uvec] at hq
  have hq1 := hK.dot_omega_nonneg hqK
  rw [hK.mem_iff]
  refine ⟨⟨?_, ?_⟩, fun s hs => ?_⟩
  · show (0 : ℝ) ≤ dot (H • vvec ω) (uvec ω)
    rw [hpu]
  · show (0 : ℝ) ≤ dot (H • vvec ω) (uvec (π / 2))
    rw [cn_dot_uvec_rot _ _ ω, hpu, hpv, mul_zero, zero_add, sin_pi_div_two_sub]
    -- `cos ω * H ≥ 1 - sin ω ≥ 0`
    obtain ⟨q', hq'K, hq'⟩ := exists_dot_eq_supp hK.isCompact hK.nonempty (π / 2)
    rw [hK.supp_pi_div_two, cn_dot_uvec_rot _ _ ω, cos_pi_div_two_sub, sin_pi_div_two_sub] at hq'
    have h1 := hK.dot_omega_le_one hq'K
    have h2 := hK.dot_le hq'K (ω + π / 2)
    rw [← cn_vvec_eq_uvec] at h2
    have hs : 0 ≤ sin ω := sin_nonneg_of_nonneg_of_le_pi hω0.le (by linarith [pi_pos])
    have hc : 0 ≤ cos ω := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hω1⟩
    have hs1 : sin ω ≤ 1 := sin_le_one ω
    nlinarith [mul_le_mul_of_nonneg_left h1 hs, mul_le_mul_of_nonneg_left h2 hc]
  · have hsI := cn_jSet_subset hs
    have hc : 0 ≤ cos (s - ω) := cos_nonneg_of_mem_Icc ⟨by linarith [hsI.1], by linarith [hsI.2]⟩
    refine le_trans ?_ (hK.dot_le hqK s)
    rw [cn_dot_uvec_rot _ s ω, cn_dot_uvec_rot q s ω, hpu, hpv, hq]
    nlinarith [mul_nonneg hc hq1]

private lemma IsCap.corner_not_mem_niche {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    supp K (ω + π / 2) • vvec ω ∉ niche K ω := by
  rintro ⟨-, hU⟩
  obtain ⟨t, ht, hq⟩ := mem_iUnion₂.1 hU
  rw [cn_mem_qMinus] at hq
  have hq2 := hq.2
  rw [cn_dot_uvec_decomp _ ω t, ← cn_vvec_eq_uvec, dot_smul_left, dot_vvec_self, mul_one,
    dot_smul_left, dot_vvec_uvec, mul_zero, mul_zero, add_zero] at hq2
  have := hK.gapZ_ineq ht
  linarith

/-- **Theorem 2.5.8** (`thm:monotonization-connected-iff`). For a cap `K`, the following are
equivalent: (1) `𝒩(K) ⊆ K`; (2) `𝒩(K) ⊆ K \ δK`; (3) for every `t ∈ (0, ω)`, either
`x_K(t) ∉ F_ω°` or `x_K(t) ∈ K`; (4) `K \ 𝒩(K)` is connected. -/
theorem theorem2_5_8 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    List.TFAE [niche K ω ⊆ K, niche K ω ⊆ K \ upperBoundary K ω,
      ∀ t ∈ Ioo 0 ω, innerCorner K t ∉ interior (fan ω) ∨ innerCorner K t ∈ K,
      IsConnected (K \ niche K ω)] := by
  have hω := hK.omega_mem
  tfae_have 1 → 2 := by
    -- a point of `δK ∩ 𝒩(K)` could be pushed out of `K` inside the open niche
    intro h1 p hp
    refine ⟨h1 hp, fun hpδ => ?_⟩
    obtain ⟨s, hs, -, hpl⟩ := mem_iUnion₂.1 hpδ
    obtain ⟨hpF, hpU⟩ := hp
    obtain ⟨t, ht, hpt⟩ := mem_iUnion₂.1 hpU
    have hev := (cn_tendsto_add_smul p (uvec s)).eventually_mem
      ((cn_isOpen_qMinus K t).mem_nhds hpt)
    obtain ⟨ε, hεQ, hεpos⟩ := (hev.and self_mem_nhdsWithin).exists
    have hmem : p + ε • uvec s ∈ K :=
      h1 ⟨cn_add_smul_uvec_mem_fan hω hs (le_of_lt hεpos) hpF, mem_iUnion₂.2 ⟨t, ht, hεQ⟩⟩
    have := hK.dot_le hmem s
    have hpl' : dot p (uvec s) = supp K s := hpl
    rw [dot_add_left, dot_smul_left, dot_uvec_self, hpl'] at this
    have hε : (0 : ℝ) < ε := hεpos
    linarith
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
    obtain ⟨ε, ⟨hεF, hεK⟩, hεpos⟩ := (hev.and self_mem_nhdsWithin).exists
    have hε : (0 : ℝ) < ε := hεpos
    have heq : x + ε • ((0 : ℝ), (-1 : ℝ)) = (x.1, x.2 - ε) := by
      ext
      · simp
      · simp; ring
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
      rw [cn_mem_interior_fan_iff, ← cn_dot_uvec_pi_div_two]
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
      ⟨by obtain ⟨s, -, hzK, -⟩ := mem_iUnion₂.1 hz; exact hzK, fun hn => (h2 hn).2 hz⟩
    have hδ := proposition2_5_2 hK
    obtain ⟨z0, hz0⟩ := hδ.nonempty
    refine ⟨⟨z0, hδS hz0⟩, isPreconnected_of_forall z0 fun y hy => ?_⟩
    have hM : IsCompact (K ∩ {z : ℝ × ℝ | z.1 = y.1}) :=
      hK.isCompact.inter_right (isClosed_eq continuous_fst continuous_const)
    obtain ⟨q, ⟨hqK, hq1⟩, hqmax⟩ := hM.exists_isMaxOn ⟨y, hy.1, rfl⟩ continuous_snd.continuousOn
    have hq1' : q.1 = y.1 := hq1
    have hqδ : q ∈ upperBoundary K ω := by
      rw [proposition2_5_1 hK]
      refine ⟨hqK, mem_closure_of_tendsto (cn_tendsto_add_smul q (uvec (π / 2))) ?_⟩
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      refine ⟨cn_add_smul_uvec_mem_fan hω ⟨by linarith [pi_pos], by linarith [hω.1]⟩ hε.le
        (hK.mem_fan hqK), fun h => ?_⟩
      have := hqmax ⟨h, by simp [uvec, hq1']⟩
      simp only [mem_ofPred_eq, Prod.snd_add, Prod.smul_snd, uvec_snd, sin_pi_div_two,
        smul_eq_mul, mul_one] at this
      linarith
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
    refine ⟨hK.mem_fan hy.1, mem_iUnion₂.2 ⟨t, ht, ?_⟩⟩
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
    -- the vertical line through `x_K(t) ∈ F_ω° \ K` would separate `K \ 𝒩(K)`
    intro h4 t ht
    by_contra hcon
    push Not at hcon
    obtain ⟨hxF, hxK⟩ := hcon
    obtain ⟨hc, hs, -, hc', hs', -⟩ := cn_trig_of_mem hω ht
    set x := innerCorner K t with hxdef
    obtain ⟨hxω, hx2⟩ := cn_mem_interior_fan_iff.1 hxF
    obtain ⟨hx1, hx2'⟩ := cn_innerCorner_dot K t
    have hsplit : K \ niche K ω ⊆ {q : ℝ × ℝ | q.1 < x.1} ∪ {q | x.1 < q.1} := by
      rintro q ⟨hqK, hqN⟩
      rcases lt_trichotomy q.1 x.1 with h | h | h
      · exact Or.inl h
      · exfalso
        rcases le_or_gt x.2 q.2 with h' | h'
        · exact hK.up_not_mem (interior_subset hxF) hxK h' (by rw [← h]; exact hqK)
        · apply hqN
          refine ⟨hK.mem_fan hqK, mem_iUnion₂.2 ⟨t, ht, ?_⟩⟩
          have := cn_below_corner_mem_qMinus (K := K) hs hc h'
          rwa [← h] at this
      · exact Or.inr h
    have hdisj : (K \ niche K ω) ∩ ({q : ℝ × ℝ | q.1 < x.1} ∩ {q | x.1 < q.1}) = ∅ := by
      ext q
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro h
      linarith [h.2.1, h.2.2]
    rcases isPreconnected_iff_subset_of_disjoint.1 h4.isPreconnected _ _
      (isOpen_lt continuous_fst continuous_const) (isOpen_lt continuous_const continuous_fst)
      hsplit hdisj with h | h
    · -- `A_K⁻(0)` lies to the right of the line
      have hA := h (lemma2_5_7 hK).1
      have h0 : (aMinus K 0).1 = supp K 0 := by
        rw [← cn_dot_uvec_zero, aMinus, dot_vminus_uvec]
      have hgap := hK.gapW_ineq ht
      have hxt : dot x (uvec t) = x.1 * cos t + x.2 * sin t := rfl
      have : x.1 * cos t < supp K 0 * cos t := by nlinarith [mul_pos hx2 hs]
      have := lt_of_mul_lt_mul_right this hc.le
      simp only [mem_ofPred_eq] at hA
      linarith
    · -- the corner `h_K(ω + π/2) v_ω` lies to the left of the line
      have hP := h ⟨hK.corner_mem, hK.corner_not_mem_niche⟩
      simp only [mem_ofPred_eq] at hP
      set H := supp K (ω + π / 2)
      have hgap := hK.gapZ_ineq ht
      have hsω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω.1 (by linarith [hω.2, pi_pos])
      have hpu : dot (H • vvec ω) (uvec ω) = 0 := by rw [dot_smul_left, dot_vvec_uvec, mul_zero]
      have hpt : dot (H • vvec ω) (uvec (t + π / 2)) = H * cos (ω - t) := by
        rw [cn_dot_uvec_decomp _ ω t, ← cn_vvec_eq_uvec, dot_smul_left, dot_vvec_self, hpu]
        ring
      have hid : ∀ d : ℝ × ℝ, d.1 * cos (ω - t) =
          cos t * dot d (uvec ω) - sin ω * dot d (uvec (t + π / 2)) := by
        intro d
        simp only [dot, uvec, cos_add_pi_div_two, sin_add_pi_div_two, cos_sub]
        ring
      have e := hid (x - H • vvec ω)
      rw [dot_sub_left, dot_sub_left, hpu, hpt, hx2', Prod.fst_sub] at e
      have : 0 < (x - H • vvec ω).1 * cos (ω - t) := by
        rw [Prod.fst_sub] at *
        rw [e]
        nlinarith [mul_pos hc hxω,
          mul_pos hsω (show 0 < H * cos (ω - t) - (supp K (t + π / 2) - 1) by linarith)]
      rw [Prod.fst_sub] at this
      have := pos_of_mul_pos_left this hc'.le
      linarith
  tfae_finish

/-! ### Helper lemmas for Theorem 2.5.9 -/

private lemma cn_mem_vStripRot {ω : ℝ} {p : ℝ × ℝ} :
    p ∈ vStripRot ω ↔ 0 ≤ dot p (uvec ω) ∧ dot p (uvec ω) ≤ 1 := by
  have key : ∀ q : ℝ × ℝ, dot (rot ω q) (uvec ω) = q.1 := by
    intro q
    have := dot_rot_uvec ω 0 q
    rwa [zero_add, cn_dot_uvec_zero] at this
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [key]; exact hq
  · intro h
    refine ⟨rot (-ω) p, ?_, rot_rot_neg ω p⟩
    have : (rot (-ω) p).1 = dot p (uvec ω) := by
      rw [← key (rot (-ω) p), rot_rot_neg]
    show 0 ≤ (rot (-ω) p).1 ∧ (rot (-ω) p).1 ≤ 1
    rw [this]; exact h

private lemma cn_mem_para {ω : ℝ} {p : ℝ × ℝ} :
    p ∈ para ω ↔ (0 ≤ p.2 ∧ p.2 ≤ 1) ∧ (0 ≤ dot p (uvec ω) ∧ dot p (uvec ω) ≤ 1) := by
  rw [para, mem_inter_iff, cn_mem_vStripRot]; rfl

private lemma IsCap.subset_para {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) : K ⊆ para ω :=
  fun _ hp => cn_mem_para.2 ⟨⟨hK.snd_nonneg hp, hK.snd_le_one hp⟩,
    ⟨hK.dot_omega_nonneg hp, hK.dot_omega_le_one hp⟩⟩

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
    rw [cn_mem_para] at hpP
    rw [hK.mem_iff]
    have hp2 : (0 : ℝ) ≤ dot p (uvec (π / 2)) := by
      rw [cn_dot_uvec_pi_div_two]; exact hpP.1.1
    refine ⟨⟨hpP.2.1, hp2⟩, fun s hs => ?_⟩
    rcases hs with hs | hs
    · exact (hpQ s hs).1
    · have := (hpQ (s - π / 2) ⟨by linarith [hs.1], by linarith [hs.2]⟩).2
      rwa [sub_add_cancel] at this
  · intro hp
    exact ⟨hK.subset_para hp, fun t _ => ⟨hK.dot_le hp t, hK.dot_le hp (t + π / 2)⟩⟩

/-- `𝓒(S)` only depends on the support function of `S` on `J_ω`. -/
private lemma cn_capOf_congr {S K : Set (ℝ × ℝ)} {ω : ℝ}
    (h : ∀ s ∈ jSet ω, supp S s = supp K s) : capOf S ω = capOf K ω := by
  have hq : ∀ t ∈ Icc 0 ω, qPlus S t = qPlus K t := by
    intro t ht
    have h1 := h t (Or.inl ht)
    have h2 := h (t + π / 2) (Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have : hallwayMap S t = hallwayMap K t := by
      funext q; rw [hallwayMap, hallwayMap, h1, h2]
    rw [qPlus, qPlus, this]
  ext p
  simp only [capOf, mem_inter_iff, mem_iInter₂]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun t ht => hq t ht ▸ h2 t ht⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun t ht => (hq t ht).symm ▸ h2 t ht⟩

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
    have hc := continuous_supp hK.isCompact
    exact (Continuous.prodMk (continuous_const.sub (hc.comp (continuous_const.mul continuous_id)))
      (continuous_const.sub (hc.comp ((continuous_const.mul continuous_id).add
        continuous_const)))).continuousOn
  angle_zero := by simp
  angle_one := by simp
  start := by
    intro p hp
    have hpK := hSK hp
    have h0 := hK.dot_le hpK 0
    rw [cn_dot_uvec_zero] at h0
    simp only [mul_zero, zero_add, rot_zero, hK.supp_pi_div_two, sub_self]
    refine ⟨?_, ?_, ?_⟩
    · show p.1 + (1 - supp K 0) ≤ 1
      linarith
    · show 0 ≤ p.2 + 0
      linarith [hK.snd_nonneg hpK]
    · show p.2 + 0 ≤ 1
      linarith [hK.snd_le_one hpK]
  inside := by
    intro s hs p hp
    have hω := hK.omega_mem
    have hts : ω * s ∈ Icc 0 ω := ⟨mul_nonneg hω.1.le hs.1, by nlinarith [hs.2, hω.1]⟩
    obtain ⟨q, hq, rfl⟩ := hSL _ hts hp
    show rot (-ω * s) (hallwayMap K (ω * s) q) +
      (1 - supp K (ω * s), 1 - supp K (ω * s + π / 2)) ∈ hallway
    rw [neg_mul, cn_rot_hallwayMap]
    exact hq
  finish := by
    intro p hp
    have hpK := hSK hp
    simp only [mul_one, hK.supp_omega, sub_self]
    have h1 : (rot (-ω) p).1 = dot p (uvec ω) := by
      simp only [rot, dot, uvec, cos_neg, sin_neg]; ring
    have h2 : (rot (-ω) p).2 = dot p (uvec (ω + π / 2)) := by
      simp only [rot, dot, uvec, cos_neg, sin_neg, cos_add_pi_div_two, sin_add_pi_div_two]; ring
    refine ⟨?_, ?_, ?_⟩
    · show 0 ≤ (rot (-ω) p).1 + 0
      rw [h1]; linarith [hK.dot_omega_nonneg hpK]
    · show (rot (-ω) p).1 + 0 ≤ 1
      rw [h1]; linarith [hK.dot_omega_le_one hpK]
    · show (rot (-ω) p).2 + (1 - supp K (ω + π / 2)) ≤ 1
      rw [h2]; linarith [hK.dot_le hpK (ω + π / 2)]

/-- **Theorem 2.5.9** (`thm:niche-in-cap`). A cap `K` is the cap of a monotone sofa if and only if it
contains its niche. -/
theorem theorem2_5_9 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) :
    (∃ S, IsMonotoneSofa S ω ∧ capOf S ω = K) ↔ niche K ω ⊆ K := by
  have htfae := theorem2_5_8 hK
  constructor
  · -- `S = K \ 𝒩(K)` is connected (Theorem 2.4.3), so (4) ⇒ (1)
    rintro ⟨S, hS, hcap⟩
    have hSeq := theorem2_4_3 hS
    rw [hcap] at hSeq
    obtain ⟨hω, S', hS', hstd', hS'eq⟩ := hS
    have hconn : IsConnected S := hS'eq ▸ (theorem2_3_2 hω hS' hstd').1.2.1
    rw [hSeq] at hconn
    exact (htfae.out 4 1).1 hconn
  · -- `S = K \ 𝒩(K) = P_ω ∩ ⋂ L_K(t)` is a moving sofa in standard position with cap `K`
    intro h1
    have hω := hK.omega_mem
    have h2 : niche K ω ⊆ K \ upperBoundary K ω := (htfae.out 1 2).1 h1
    have hconn : IsConnected (K \ niche K ω) := (htfae.out 1 4).1 h1
    have hSK : K \ niche K ω ⊆ K := sdiff_subset
    have hδS : upperBoundary K ω ⊆ K \ niche K ω := fun z hz =>
      ⟨by obtain ⟨s, -, hzK, -⟩ := mem_iUnion₂.1 hz; exact hzK, fun hn => (h2 hn).2 hz⟩
    have hSeq' : K \ niche K ω = K \ ⋃ t ∈ Ioo 0 ω, qMinus K t := by
      ext p
      constructor
      · rintro ⟨hpK, hpN⟩; exact ⟨hpK, fun h => hpN ⟨hK.mem_fan hpK, h⟩⟩
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
        rw [zero_add, hK.supp_pi_div_two, cn_dot_uvec_pi_div_two] at this
        linarith [hK.snd_nonneg hpK]
      rcases eq_or_lt_of_le ht.2 with h1 | h1
      · subst h1
        have := (cn_mem_qMinus.1 hpQ).1
        rw [hK.supp_omega] at this
        linarith [hK.dot_omega_nonneg hpK]
      exact hpN ⟨hK.mem_fan hpK, mem_iUnion₂.2 ⟨t, ⟨h0, h1⟩, hpQ⟩⟩
    have hSofa : IsMovingSofaWithAngle (K \ niche K ω) ω :=
      ⟨hSclosed, hconn, _, _, cn_isMovement hK hSK hSL⟩
    have hstd : IsStandardPosition (K \ niche K ω) ω :=
      ⟨(hsuppJ ω (Or.inl ⟨hω.1.le, le_rfl⟩)).trans hK.supp_omega,
        (hsuppJ (π / 2) (Or.inr ⟨le_rfl, by linarith [hω.1]⟩)).trans hK.supp_pi_div_two⟩
    have hcap : capOf (K \ niche K ω) ω = K := (cn_capOf_congr hsuppJ).trans hK.capOf_self
    refine ⟨K \ niche K ω, ⟨hω, K \ niche K ω, hSofa, hstd, ?_⟩, hcap⟩
    rw [theorem2_4_2 hω hSofa hstd, hcap]

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
      dsimp only; rw [cn_dot_uvec_pi_div_two]⟩, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    dsimp only
    rw [cn_dot_uvec_pi_div_two]; exact hp.2.2
  have h3 : supp K (3 * π / 2) = 0 := by
    unfold supp
    apply IsGreatest.csSup_eq
    refine ⟨⟨((0 : ℝ), (0 : ℝ)), h00, by
      dsimp only; rw [cn_uvec_three_pi_div_two, dot_neg_right, cn_dot_uvec_pi_div_two, neg_zero]⟩,
      ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    dsimp only
    rw [cn_uvec_three_pi_div_two, dot_neg_right, cn_dot_uvec_pi_div_two]
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
      have e0 : dot p (uvec 0) = p.1 := cn_dot_uvec_zero p
      have e1 : dot p (uvec (π / 2)) = p.2 := cn_dot_uvec_pi_div_two p
      have e2 : dot p (uvec π) = -p.1 := by simp [dot, uvec]
      have e3 : dot p (uvec (3 * π / 2)) = -p.2 := by
        rw [cn_uvec_three_pi_div_two, dot_neg_right, e1]
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
      refine ⟨⟨?_, ?_⟩, mem_iUnion₂.2 ⟨π / 4, ⟨by positivity, by linarith⟩, ?_⟩⟩
      · show (0 : ℝ) ≤ dot ((50 : ℝ), (2 : ℝ)) (uvec (π / 2))
        rw [cn_dot_uvec_pi_div_two]; norm_num
      · show (0 : ℝ) ≤ dot ((50 : ℝ), (2 : ℝ)) (uvec (π / 2))
        rw [cn_dot_uvec_pi_div_two]; norm_num
      · rw [cn_mem_qMinus]
        simp only [dot, uvec, cos_add_pi_div_two, sin_add_pi_div_two, cos_pi_div_four,
          sin_pi_div_four]
        constructor <;> nlinarith
    have := (h hp).2.2
    norm_num at this

/-! ### Helper lemmas for Theorem 2.5.10 -/

private lemma cn_isClosed_fan (ω : ℝ) : IsClosed (fan ω) :=
  (isClosed_le continuous_const (cn_continuous_dot_left _)).inter
    (isClosed_le continuous_const (cn_continuous_dot_left _))

private lemma cn_measurableSet_niche (K : Set (ℝ × ℝ)) (ω : ℝ) : MeasurableSet (niche K ω) :=
  (cn_isClosed_fan ω).measurableSet.inter (cn_isOpen_iUnion_qMinus K ω).measurableSet

/-- **Theorem 2.5.10** (`thm:sofa-area-functional`). For the cap `K = 𝓒(S)` of a monotone sofa,
`𝒜_ω(K) = |S|`. -/
theorem theorem2_5_10 {S : Set (ℝ × ℝ)} {ω : ℝ} (hS : IsMonotoneSofa S ω) :
    sofaArea ω (capOf S ω) = area S := by
  have hSeq := theorem2_4_3 hS
  have hS0 := hS
  obtain ⟨hω, S', hS', hstd', hS'eq⟩ := hS
  have hmov := theorem2_3_2 hω hS' hstd'
  rw [← hS'eq] at hmov
  have hcap : IsCap (capOf S ω) ω := theorem2_4_1 hω hmov.1 hmov.2.1
  have hsub : niche (capOf S ω) ω ⊆ capOf S ω := (theorem2_5_9 hcap).1 ⟨S, hS0, rfl⟩
  have hfin : MeasureTheory.volume (capOf S ω) ≠ ⊤ := hcap.isCompact.measure_lt_top.ne
  rw [sofaArea, show area S = area (capOf S ω \ niche (capOf S ω) ω) from congrArg area hSeq,
    area, area, area, MeasureTheory.measure_sdiff hsub
      (cn_measurableSet_niche _ ω).nullMeasurableSet
      (ne_top_of_le_ne_top hfin (MeasureTheory.measure_mono hsub)),
    ENNReal.toReal_sub_of_le (MeasureTheory.measure_mono hsub) hfin]

end MovingSofaOptimality
