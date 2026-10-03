module

public import MovingSofaOptimality.Convex.CurveArea
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Convex curves (§7.3)

Definition 7.3.1 (`def:convex-curve`), Lemma 7.3.1 (`lem:convex-curve-cut`), Theorem 7.3.2
(`thm:convex-curve-area-functional`), Lemmas 7.3.3–7.3.5.

**Reading.** The paper's curve area functional `𝒥(𝐮_K^{a,b})` of the convex arc is defined through
a parametrization of the arc as a Jordan arc, and Theorem 7.3.2 evaluates it to
`½ ∫_{(a,b)} h_K dσ_K`. We name that value `convexCurveArea K a b`; Theorem 7.3.2 exhibits a
parametrization of the arc of bounded variation, from `v_K⁺(a)` to `v_K⁻(b)` and injective unless
the arc is a point, whose curve area functional is this value. Lemma 7.3.5 (1) (the boundary of the
region is a counterclockwise Jordan curve) is replaced by the computation of the area of the region,
which is how the paper uses it.
-/

@[expose] public section

open Real Set MeasureTheory

namespace MovingSofaOptimality

/-- The convex curve `𝐮_K^{a,b} = {v_K⁺(a)} ∪ ⋃_{t ∈ (a,b)} e_K(t) ∪ {v_K⁻(b)}`
(Definition 7.3.1, `def:convex-curve`). -/
def convexCurve (K : Set (ℝ × ℝ)) (a b : ℝ) : Set (ℝ × ℝ) :=
  {vplus K a} ∪ (⋃ t ∈ Ioo a b, edge K t) ∪ {vminus K b}

/-- The value `½ ∫_{(a,b)} h_K dσ_K` of the curve area functional of `𝐮_K^{a,b}` (Theorem 7.3.2). -/
noncomputable def convexCurveArea (K : Set (ℝ × ℝ)) (a b : ℝ) : ℝ :=
  (1 / 2) * ∫ t in Ioo a b, supp K t ∂(sigma K)

/-- The bilinear form `𝓑(K₁, K₂) = ½ ∫_{(a,b)} h_{K₁} dσ_{K₂}` (Lemma 7.3.3). -/
noncomputable def convexCurveBilin (K₁ K₂ : Set (ℝ × ℝ)) (a b : ℝ) : ℝ :=
  (1 / 2) * ∫ t in Ioo a b, supp K₁ t ∂(sigma K₂)

/-! ### Edges and vertices -/

/-- A point of the edge which is furthest in the direction `v_t` is `v_K⁺(t)`. -/
lemma cvx_eq_vplus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {t : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ edge K t) (h : ∀ q ∈ edge K t, dot q (vvec t) ≤ dot p (vvec t)) :
    p = vplus K t := by
  have e : dot p (vvec t) = dot (vplus K t) (vvec t) := by
    refine le_antisymm (dot_le_dot_vplus hK.2.1 hp) ?_
    rw [dot_vplus_vvec]
    exact csSup_le ⟨_, mem_image_of_mem _ hp⟩ (by rintro _ ⟨q, hq, rfl⟩; exact h q hq)
  rw [eq_dot_uvec_smul_add p t, eq_dot_uvec_smul_add (vplus K t) t, e, hp.2, dot_vplus_uvec]

/-- A point of the edge which is furthest in the direction `-v_t` is `v_K⁻(t)`. -/
lemma cvx_eq_vminus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {t : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ edge K t) (h : ∀ q ∈ edge K t, dot p (vvec t) ≤ dot q (vvec t)) :
    p = vminus K t := by
  have e : dot p (vvec t) = dot (vminus K t) (vvec t) := by
    refine le_antisymm ?_ (dot_vminus_le_dot hK.2.1 hp)
    rw [dot_vminus_vvec]
    exact le_csInf ⟨_, mem_image_of_mem _ hp⟩ (by rintro _ ⟨q, hq, rfl⟩; exact h q hq)
  rw [eq_dot_uvec_smul_add p t, eq_dot_uvec_smul_add (vminus K t) t, e, hp.2, dot_vminus_uvec]

/-- **Common points of two edges.** If `t < s < t + π`, a common point of `e_K(t)` and `e_K(s)` is
`v_K⁻(s)`. -/
lemma cvx_edge_inter_eq_vminus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {t s : ℝ} (hts : t < s)
    (hst : s < t + π) {p : ℝ × ℝ} (hpt : p ∈ edge K t) (hps : p ∈ edge K s) :
    p = vminus K s := by
  refine cvx_eq_vminus hK hps fun q hq => ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨d, hqp⟩ : ∃ d, q - p = d • vvec s := ⟨_, sub_eq_smul_vvec (hps.2.trans hq.2.symm)⟩
  have hsin : 0 < sin (s - t) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have key : dot q (uvec t) - dot p (uvec t) = d * -sin (s - t) := by
    rw [← dot_sub_left, hqp, dot_smul_left, dot_vvec_uvec', ← neg_sub s t, sin_neg]
  have hd : d < 0 := by
    have : dot (q - p) (vvec s) = d := by rw [hqp, dot_smul_left, dot_vvec_self, mul_one]
    rw [← this, dot_sub_left]; linarith
  have h1 := dot_le_supp hK.2.1 hq.1 t
  rw [← hpt.2] at h1
  nlinarith

/-- If `t < s < t + π`, a common point of `e_K(t)` and `e_K(s)` is `v_K⁺(t)`. -/
lemma cvx_edge_inter_eq_vplus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {t s : ℝ} (hts : t < s)
    (hst : s < t + π) {p : ℝ × ℝ} (hpt : p ∈ edge K t) (hps : p ∈ edge K s) :
    p = vplus K t := by
  refine cvx_eq_vplus hK hpt fun q hq => ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨d, hqp⟩ : ∃ d, q - p = d • vvec t := ⟨_, sub_eq_smul_vvec (hpt.2.trans hq.2.symm)⟩
  have hsin : 0 < sin (s - t) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have key : dot q (uvec s) - dot p (uvec s) = d * sin (s - t) := by
    rw [← dot_sub_left, hqp, dot_smul_left, dot_vvec_uvec']
  have hd : 0 < d := by
    have : dot (q - p) (vvec t) = d := by rw [hqp, dot_smul_left, dot_vvec_self, mul_one]
    rw [← this, dot_sub_left]; linarith
  have h1 := dot_le_supp hK.2.1 hq.1 s
  rw [← hps.2] at h1
  nlinarith

/-- `v_K(a, b)` is the intersection point of the two supporting lines. -/
lemma cvx_vint_eq {K : Set (ℝ × ℝ)} {a b : ℝ} {p : ℝ × ℝ} (hs : sin (b - a) ≠ 0)
    (ha : dot p (uvec a) = supp K a) (hb : dot p (uvec b) = supp K b) : vint K a b = p :=
  eq_of_dot_uvec_eq hs ((vint_mem_line_left K a b).trans ha.symm)
    ((vint_mem_line_right K hs).trans hb.symm)

/-- If `a < t < b < a + π` and `w · u_a ≤ 0`, `w · u_b ≤ 0`, `w · u_t ≥ 0`, then `w = 0`. -/
lemma cvx_eq_zero_of_dot_le {w : ℝ × ℝ} {a b t : ℝ} (hb : b < a + π)
    (ht : t ∈ Ioo a b) (h1 : dot w (uvec a) ≤ 0) (h2 : dot w (uvec b) ≤ 0)
    (h3 : 0 ≤ dot w (uvec t)) : w = 0 := by
  have hsin : 0 < sin (b - a) :=
    sin_pos_of_pos_of_lt_pi (by linarith [ht.1, ht.2]) (by linarith)
  have hs1 : 0 < sin (b - t) := sin_pos_of_pos_of_lt_pi (by linarith [ht.2]) (by linarith [ht.1])
  have hs2 : 0 < sin (t - a) := sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2])
  have key := dot_uvec_comb w a b t
  have t1 : sin (b - t) * dot w (uvec a) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs1.le h1
  have t2 : sin (t - a) * dot w (uvec b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs2.le h2
  have t3 : 0 ≤ sin (b - a) * dot w (uvec t) := mul_nonneg hsin.le h3
  have e1 : sin (b - t) * dot w (uvec a) = 0 := by linarith
  have e2 : sin (t - a) * dot w (uvec b) = 0 := by linarith
  exact eq_of_dot_uvec_eq (q := 0) hsin.ne'
    (by rw [(mul_eq_zero.1 e1).resolve_left hs1.ne', dot_zero_left])
    (by rw [(mul_eq_zero.1 e2).resolve_left hs2.ne', dot_zero_left])

/-- If `a < t < b < a + π`, `w · u_a ≤ 0` and `w · u_b ≤ 0`, then `w · u_t < 0` unless `w = 0`. -/
lemma cvx_dot_lt_zero {w : ℝ × ℝ} {a b t : ℝ} (hb : b < a + π)
    (ht : t ∈ Ioo a b) (h1 : dot w (uvec a) ≤ 0) (h2 : dot w (uvec b) ≤ 0) (hw : w ≠ 0) :
    dot w (uvec t) < 0 := by
  by_contra h3
  exact hw (cvx_eq_zero_of_dot_le hb ht h1 h2 (not_lt.1 h3))

/-- If `p ∈ L` maximizes `· u_t` on `L`, then `h_L(t) = p · u_t`. -/
lemma cvx_supp_eq_of_isGreatest {L : Set (ℝ × ℝ)} {p : ℝ × ℝ} {t : ℝ} (hp : p ∈ L)
    (h : ∀ q ∈ L, dot q (uvec t) ≤ dot p (uvec t)) : supp L t = dot p (uvec t) :=
  IsGreatest.csSup_eq ⟨mem_image_of_mem _ hp, by rintro _ ⟨q, hq, rfl⟩; exact h q hq⟩

/-- If `p ∈ L` is the unique maximizer of `· u_t` on `L`, then `e_L(t) = {p}`. -/
lemma cvx_edge_eq_singleton {L : Set (ℝ × ℝ)} {p : ℝ × ℝ} {t : ℝ} (hp : p ∈ L)
    (h : ∀ q ∈ L, q ≠ p → dot q (uvec t) < dot p (uvec t)) : edge L t = {p} := by
  have hs : supp L t = dot p (uvec t) := cvx_supp_eq_of_isGreatest hp fun q hq => by
    rcases eq_or_ne q p with rfl | hqp
    exacts [le_rfl, (h q hq hqp).le]
  ext q
  simp only [edge, suppLine, line, mem_inter_iff, mem_ofPred_eq, mem_singleton_iff, hs]
  constructor
  · rintro ⟨hq, hqe⟩
    by_contra hqp
    exact (h q hq hqp).ne hqe
  · rintro rfl; exact ⟨hp, rfl⟩

/-- Cutting `K` by a closed set containing the edge `e_K(t)` does not change that edge. -/
lemma cvx_edge_inter_of_subset {K H : Set (ℝ × ℝ)} (hK : IsConvexBody K) (hH : IsClosed H)
    {t : ℝ} (hsub : edge K t ⊆ H) : edge (K ∩ H) t = edge K t := by
  have hv : vplus K t ∈ K ∩ H := ⟨(vplus_mem_edge hK t).1, hsub (vplus_mem_edge hK t)⟩
  have hs : supp (K ∩ H) t = supp K t := by
    apply le_antisymm (supp_mono inter_subset_left ⟨_, hv⟩ hK.2.1 t)
    rw [← dot_vplus_uvec K t]
    exact dot_le_supp (hK.2.1.inter_right hH) hv t
  ext q
  simp only [edge, suppLine, line, mem_inter_iff, mem_ofPred_eq, hs]
  constructor
  · rintro ⟨⟨hq, _⟩, hqe⟩; exact ⟨hq, hqe⟩
  · rintro ⟨hq, hqe⟩; exact ⟨⟨hq, hsub ⟨hq, hqe⟩⟩, hqe⟩

/-- **Lemma 7.3.1** (`lem:convex-curve-cut`), degenerate case: if `v_K⁺(a) = v_K⁻(b)` then
`v_K(a, b) = v_K⁺(a)` and `𝐮_K^{a,b}` is a single point. -/
theorem lemma7_3_1_degenerate {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b)
    (hb : b < a + π) (h : vplus K a = vminus K b) :
    vint K a b = vplus K a ∧ convexCurve K a b = {vplus K a} := by
  have hsin : 0 < sin (b - a) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hpa := vplus_mem_edge hK a
  have hpb : vplus K a ∈ edge K b := h ▸ vminus_mem_edge hK b
  refine ⟨cvx_vint_eq hsin.ne' hpa.2 hpb.2, ?_⟩
  have hedge : ∀ t ∈ Ioo a b, ∀ q ∈ edge K t, q = vplus K a := by
    intro t ht q hq
    refine sub_eq_zero.1 (cvx_eq_zero_of_dot_le hb ht ?_ ?_ ?_)
    · rw [dot_sub_left, hpa.2]; linarith [dot_le_supp hK.2.1 hq.1 a]
    · rw [dot_sub_left, hpb.2]; linarith [dot_le_supp hK.2.1 hq.1 b]
    · rw [dot_sub_left, hq.2]; linarith [dot_le_supp hK.2.1 hpa.1 t]
  ext q
  simp only [convexCurve, mem_union, mem_singleton_iff, mem_iUnion]
  constructor
  · rintro ((rfl | ⟨t, ht, hq⟩) | rfl)
    · rfl
    · exact hedge t ht q hq
    · exact h.symm
  · rintro rfl; exact Or.inl (Or.inl rfl)


/-- **Lemma 7.3.1** (`lem:convex-curve-cut`), nondegenerate case: if `v_K⁺(a) ≠ v_K⁻(b)`, then
(1) `v_K(a, b)` is not on the line `l'` through `v_K⁺(a)` and `v_K⁻(b)`; (2) the closed half-plane
bounded by `l'` and containing `v_K(a, b)` has normal angle `t' + π` for some `t' ∈ (a, b)`;
(3) `K' = K ∩ H'` is a convex body with (i) `e_{K'}(t) = {v_K⁺(a)}` for `t ∈ (t' - π, a]`,
(ii) `e_{K'}(t) = e_K(t)` for `t ∈ (a, b)`, (iii) `e_{K'}(t) = {v_K⁻(b)}` for `t ∈ [b, t' + π)`,
(iv) `e_{K'}(t' + π)` is the segment from `v_K⁻(b)` to `v_K⁺(a)`. -/
theorem lemma7_3_1 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b)
    (hb : b < a + π) (h : vplus K a ≠ vminus K b) :
    ∃ t' ∈ Ioo a b, ∃ c : ℝ,
      vplus K a ∈ line (t' + π) c ∧ vminus K b ∈ line (t' + π) c ∧
      dot (vint K a b) (uvec (t' + π)) < c ∧
      IsConvexBody (K ∩ halfMinus (t' + π) c) ∧
      (∀ t ∈ Ioc (t' - π) a, edge (K ∩ halfMinus (t' + π) c) t = {vplus K a}) ∧
      (∀ t ∈ Ioo a b, edge (K ∩ halfMinus (t' + π) c) t = edge K t) ∧
      (∀ t ∈ Ico b (t' + π), edge (K ∩ halfMinus (t' + π) c) t = {vminus K b}) ∧
      edge (K ∩ halfMinus (t' + π) c) (t' + π) = segment ℝ (vminus K b) (vplus K a) := by
  set p₁ := vplus K a with hp₁
  set p₂ := vminus K b with hp₂
  set p₀ := vint K a b with hp₀
  have hsin : 0 < sin (b - a) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hpa : p₁ ∈ edge K a := vplus_mem_edge hK a
  have hpb : p₂ ∈ edge K b := vminus_mem_edge hK b
  have h0a : dot p₀ (uvec a) = supp K a := vint_mem_line_left K a b
  have h0b : dot p₀ (uvec b) = supp K b := vint_mem_line_right K hsin.ne'
  have hsab : sin (a - b) = -sin (b - a) := by rw [← sin_neg, neg_sub]
  -- Step 1: `p₀ = v_K(a, b)` is `p₁ + α v_a = p₂ - β v_b` with `α, β > 0`, where `p₁ = v_K⁺(a)` and
  -- `p₂ = v_K⁻(b)` (`α = 0` or `β = 0` would force `p₁ = p₂`).
  obtain ⟨α, hα⟩ : ∃ α, p₀ - p₁ = α • vvec a :=
    ⟨_, sub_eq_smul_vvec (hpa.2.trans h0a.symm)⟩
  obtain ⟨β, hβ⟩ : ∃ β, p₂ - p₀ = β • vvec b :=
    ⟨_, sub_eq_smul_vvec (h0b.trans hpb.2.symm)⟩
  have hα0 : 0 ≤ α := by
    have e : dot (p₀ - p₁) (uvec b) = α * sin (b - a) := by
      rw [hα, dot_smul_left, dot_vvec_uvec']
    have : 0 ≤ dot (p₀ - p₁) (uvec b) := by
      rw [dot_sub_left, h0b]; linarith [dot_le_supp hK.2.1 hpa.1 b]
    by_contra hneg; push Not at hneg; nlinarith
  have hβ0 : 0 ≤ β := by
    have e : dot (p₂ - p₀) (uvec a) = -(β * sin (b - a)) := by
      rw [hβ, dot_smul_left, dot_vvec_uvec', hsab, mul_neg]
    have : dot (p₂ - p₀) (uvec a) ≤ 0 := by
      rw [dot_sub_left, h0a]; linarith [dot_le_supp hK.2.1 hpb.1 a]
    by_contra hneg; push Not at hneg; nlinarith
  have hαpos : 0 < α := by
    rcases hα0.lt_or_eq with hpos | hzero
    · exact hpos
    · exfalso
      have he : p₀ = p₁ := by rw [← sub_eq_zero, hα, ← hzero, zero_smul]
      have h0K : p₀ ∈ K := he ▸ hpa.1
      exact h (he ▸ cvx_edge_inter_eq_vminus hK hab hb ⟨h0K, h0a⟩ ⟨h0K, h0b⟩)
  have hβpos : 0 < β := by
    rcases hβ0.lt_or_eq with hpos | hzero
    · exact hpos
    · exfalso
      have he : p₂ = p₀ := by rw [← sub_eq_zero, hβ, ← hzero, zero_smul]
      have h0K : p₀ ∈ K := he ▸ hpb.1
      exact h ((cvx_edge_inter_eq_vplus hK hab hb ⟨h0K, h0a⟩ ⟨h0K, h0b⟩).symm.trans he.symm)
  -- Step 2: `p₂ - p₁ = α v_a + β v_b` is orthogonal to `u_{t'}` for some `t' ∈ (a, b)`
  -- (intermediate value theorem), so `p₂ - p₁ = τ v_{t'}`, and `τ > 0`.
  have hw : p₂ - p₁ = α • vvec a + β • vvec b := by rw [← hα, ← hβ]; abel
  have hf_cont : Continuous fun θ => dot (p₂ - p₁) (uvec θ) := by
    unfold dot uvec; fun_prop
  have hfa : dot (p₂ - p₁) (uvec a) < 0 := by
    rw [hw, dot_add_left, dot_smul_left, dot_smul_left, dot_vvec_uvec, dot_vvec_uvec', hsab]
    nlinarith
  have hfb : 0 < dot (p₂ - p₁) (uvec b) := by
    rw [hw, dot_add_left, dot_smul_left, dot_smul_left, dot_vvec_uvec, dot_vvec_uvec']
    nlinarith
  obtain ⟨t', ht', hft'⟩ : ∃ t' ∈ Ioo a b, dot (p₂ - p₁) (uvec t') = 0 :=
    intermediate_value_Ioo hab.le hf_cont.continuousOn ⟨hfa, hfb⟩
  set τ := dot (p₂ - p₁) (vvec t') with hτdef
  have hwτ : p₂ - p₁ = τ • vvec t' := eq_smul_vvec_of_dot_uvec_eq_zero hft'
  have hτ : 0 < τ := by
    obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (a + b) / 2 := ⟨_, rfl⟩
    have hc1 : 0 < cos (a - m) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have hc2 : 0 < cos (b - m) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have hc3 : 0 < cos (t' - m) := cos_pos_of_mem_Ioo ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
    have e1 : dot (p₂ - p₁) (vvec m) = α * cos (a - m) + β * cos (b - m) := by
      rw [hw, dot_add_left, dot_smul_left, dot_smul_left, dot_vvec_vvec, dot_vvec_vvec]
    have e2 : dot (p₂ - p₁) (vvec m) = τ * cos (t' - m) := by
      rw [hwτ, dot_smul_left, dot_vvec_vvec]
    have : 0 < τ * cos (t' - m) := by rw [← e2, e1]; positivity
    exact pos_of_mul_pos_left this hc3.le
  -- Step 3: the line `l'` through `p₁` and `p₂` is `l(t' + π, c)`; the closed half-plane
  -- `H' = H(t' + π, c)` is `{q | (q - p₁) · u_{t'} ≥ 0}`.
  have hp₂eq : p₂ = p₁ + τ • vvec t' := by rw [← hwτ]; abel
  have hu : uvec (t' + π) = -uvec t' := uvec_add_pi t'
  set c := dot p₁ (uvec (t' + π)) with hc
  have hp₁line : p₁ ∈ line (t' + π) c := rfl
  have hp₂line : p₂ ∈ line (t' + π) c := by
    show dot p₂ (uvec (t' + π)) = c
    simp only [hc, hp₂eq, dot_add_left, dot_smul_left, hu, dot_neg_right, dot_vvec_uvec,
      mul_zero, add_zero]
  have hsta : 0 < sin (t' - a) :=
    sin_pos_of_pos_of_lt_pi (by linarith [ht'.1]) (by linarith [ht'.2])
  have hsbt : 0 < sin (b - t') :=
    sin_pos_of_pos_of_lt_pi (by linarith [ht'.2]) (by linarith [ht'.1])
  have hH : ∀ q, q ∈ halfMinus (t' + π) c ↔ 0 ≤ dot (q - p₁) (uvec t') := by
    intro q
    show dot q (uvec (t' + π)) ≤ c ↔ _
    rw [hc, hu, dot_neg_right, dot_neg_right, neg_le_neg_iff, dot_sub_left, sub_nonneg]
  have hH₂ : ∀ q, q ∈ halfMinus (t' + π) c ↔ 0 ≤ dot (q - p₂) (uvec t') := by
    intro q
    rw [hH q]
    have : dot (q - p₂) (uvec t') = dot (q - p₁) (uvec t') := by
      rw [hp₂eq, sub_add_eq_sub_sub, dot_sub_left, dot_smul_left, dot_vvec_uvec, mul_zero,
        sub_zero]
    rw [this]
  have hp₁K' : p₁ ∈ K ∩ halfMinus (t' + π) c := ⟨hpa.1, (hH p₁).2 (by simp)⟩
  have hp₂K' : p₂ ∈ K ∩ halfMinus (t' + π) c := ⟨hpb.1, (hH₂ p₂).2 (by simp)⟩
  -- Step 4: the six claims.
  refine ⟨t', ht', c, hp₁line, hp₂line, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the vertex `v_K(a, b)` is strictly inside `H'`
    have e : dot p₀ (uvec (t' + π)) - c = -(α * sin (t' - a)) := by
      rw [hc, ← dot_sub_left, hα, dot_smul_left, hu, dot_neg_right, dot_vvec_uvec']
      ring
    have : 0 < α * sin (t' - a) := mul_pos hαpos hsta
    linarith
  · -- `K'` is a convex body
    exact ⟨⟨p₁, hp₁K'⟩, hK.2.1.inter_right (isClosed_halfMinus _ _),
      hK.2.2.inter (convex_halfMinus _ _)⟩
  · -- (i): for `t ∈ (t' - π, a]`, `p₁` is the unique maximizer of `· u_t` on `K'`
    intro t ht
    apply cvx_edge_eq_singleton hp₁K'
    intro q hq hqp
    rw [← sub_neg, ← dot_sub_left]
    have hq1 : dot (q - p₁) (uvec a) ≤ 0 := by
      rw [dot_sub_left, hpa.2]; linarith [dot_le_supp hK.2.1 hq.1 a]
    have hq2 : dot (q - p₁) (uvec (t' - π)) ≤ 0 := by
      have := (hH q).1 hq.2
      rw [show t' - π = t' + π - 2 * π by ring, ← uvec_add_two_pi (t' + π - 2 * π),
        show t' + π - 2 * π + 2 * π = t' + π by ring, hu, dot_neg_right]
      linarith
    rcases ht.2.lt_or_eq with hta | hta
    · exact cvx_dot_lt_zero (by linarith [ht'.1]) ⟨ht.1, hta⟩ hq2 hq1 (sub_ne_zero.2 hqp)
    · rw [hta]
      by_contra hge
      push Not at hge
      have he : dot (q - p₁) (uvec a) = 0 := le_antisymm hq1 hge
      have hqe : q ∈ edge K a := ⟨hq.1, by
        show dot q (uvec a) = supp K a
        rw [dot_sub_left, hpa.2] at he; linarith⟩
      obtain ⟨d, hd⟩ : ∃ d, q - p₁ = d • vvec a :=
        ⟨_, sub_eq_smul_vvec (hpa.2.trans hqe.2.symm)⟩
      have hd1 : d ≤ 0 := by
        have := dot_le_dot_vplus hK.2.1 hqe
        have e : dot (q - p₁) (vvec a) = d := by rw [hd, dot_smul_left, dot_vvec_self, mul_one]
        rw [dot_sub_left] at e; linarith
      have hd2 : 0 ≤ d := by
        have h3 := (hH q).1 hq.2
        rw [hd, dot_smul_left, dot_vvec_uvec'] at h3
        nlinarith
      apply hqp
      rw [← sub_eq_zero, hd, le_antisymm hd1 hd2, zero_smul]
  · -- (ii): for `t ∈ (a, b)`, the edge `e_K(t)` lies in `H'`
    intro t ht
    apply cvx_edge_inter_of_subset hK (isClosed_halfMinus _ _)
    intro q hqe
    rw [hH q]
    by_contra hlt
    push Not at hlt
    have hqa : dot (q - p₁) (uvec a) ≤ 0 := by
      rw [dot_sub_left, hpa.2]; linarith [dot_le_supp hK.2.1 hqe.1 a]
    have hqt : 0 ≤ dot (q - p₁) (uvec t) := by
      rw [dot_sub_left, hqe.2]; linarith [dot_le_supp hK.2.1 hpa.1 t]
    rcases lt_trichotomy t t' with htt | htt | htt
    · have key := dot_uvec_comb (q - p₁) a t' t
      have s2 : 0 < sin (t' - t) :=
        sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [ht.1, ht'.2])
      have s3 : 0 < sin (t - a) := sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2])
      nlinarith [mul_nonpos_of_nonneg_of_nonpos s2.le hqa, mul_neg_of_pos_of_neg s3 hlt,
        mul_nonneg hsta.le hqt]
    · rw [htt] at hqt; linarith
    · have hlt2 : dot (q - p₂) (uvec t') < 0 := by
        have := (hH₂ q).not.1
        have h' : ¬ (0 ≤ dot (q - p₁) (uvec t')) := not_le.2 hlt
        rw [hH q] at this
        exact not_le.1 (this h')
      have hqb : dot (q - p₂) (uvec b) ≤ 0 := by
        rw [dot_sub_left, hpb.2]; linarith [dot_le_supp hK.2.1 hqe.1 b]
      have hqt2 : 0 ≤ dot (q - p₂) (uvec t) := by
        rw [dot_sub_left, hqe.2]; linarith [dot_le_supp hK.2.1 hpb.1 t]
      have key := dot_uvec_comb (q - p₂) t' b t
      have s2 : 0 < sin (b - t) :=
        sin_pos_of_pos_of_lt_pi (by linarith [ht.2]) (by linarith [ht'.1])
      have s3 : 0 < sin (t - t') :=
        sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [ht.2, ht'.1])
      nlinarith [mul_neg_of_pos_of_neg s2 hlt2, mul_nonpos_of_nonneg_of_nonpos s3.le hqb,
        mul_nonneg hsbt.le hqt2]
  · -- (iii): for `t ∈ [b, t' + π)`, `p₂` is the unique maximizer of `· u_t` on `K'`
    intro t ht
    apply cvx_edge_eq_singleton hp₂K'
    intro q hq hqp
    rw [← sub_neg, ← dot_sub_left]
    have hq1 : dot (q - p₂) (uvec b) ≤ 0 := by
      rw [dot_sub_left, hpb.2]; linarith [dot_le_supp hK.2.1 hq.1 b]
    have hq2 : dot (q - p₂) (uvec (t' + π)) ≤ 0 := by
      have := (hH₂ q).1 hq.2
      rw [hu, dot_neg_right]
      linarith
    rcases ht.1.lt_or_eq with htb | htb
    · exact cvx_dot_lt_zero (by linarith [ht'.2]) ⟨htb, ht.2⟩ hq1 hq2 (sub_ne_zero.2 hqp)
    · rw [← htb]
      by_contra hge
      push Not at hge
      have he : dot (q - p₂) (uvec b) = 0 := le_antisymm hq1 hge
      have hqe : q ∈ edge K b := ⟨hq.1, by
        show dot q (uvec b) = supp K b
        rw [dot_sub_left, hpb.2] at he; linarith⟩
      obtain ⟨d, hd⟩ : ∃ d, q - p₂ = d • vvec b :=
        ⟨_, sub_eq_smul_vvec (hpb.2.trans hqe.2.symm)⟩
      have hd1 : 0 ≤ d := by
        have := dot_vminus_le_dot hK.2.1 hqe
        have e : dot (q - p₂) (vvec b) = d := by rw [hd, dot_smul_left, dot_vvec_self, mul_one]
        rw [dot_sub_left] at e; linarith
      have hd2 : d ≤ 0 := by
        have h3 := (hH₂ q).1 hq.2
        rw [hd, dot_smul_left, dot_vvec_uvec', show t' - b = -(b - t') by ring, sin_neg] at h3
        nlinarith
      apply hqp
      rw [← sub_eq_zero, hd, le_antisymm hd2 hd1, zero_smul]
  · -- (iv): `e_{K'}(t' + π) = K ∩ l'` is the segment `[p₂, p₁]`
    have hs : supp (K ∩ halfMinus (t' + π) c) (t' + π) = c :=
      cvx_supp_eq_of_isGreatest hp₁K' (fun q hq => hq.2)
    ext q
    simp only [edge, suppLine, line, mem_inter_iff, mem_ofPred_eq, hs]
    constructor
    · rintro ⟨⟨hqK, _⟩, hqe⟩
      have hdot : dot (q - p₁) (uvec t') = 0 := by
        have : dot (q - p₁) (uvec (t' + π)) = 0 := by rw [dot_sub_left, hqe, hc, sub_self]
        rw [hu, dot_neg_right] at this; linarith
      obtain ⟨s, hs'⟩ : ∃ s, q - p₁ = s • vvec t' := ⟨_, eq_smul_vvec_of_dot_uvec_eq_zero hdot⟩
      have hs0 : 0 ≤ s := by
        have h1 : dot (q - p₁) (uvec a) ≤ 0 := by
          rw [dot_sub_left, hpa.2]; linarith [dot_le_supp hK.2.1 hqK a]
        rw [hs', dot_smul_left, dot_vvec_uvec', show a - t' = -(t' - a) by ring, sin_neg] at h1
        nlinarith
      have hsτ : s ≤ τ := by
        have h1 : dot (q - p₂) (uvec b) ≤ 0 := by
          rw [dot_sub_left, hpb.2]; linarith [dot_le_supp hK.2.1 hqK b]
        have e : q - p₂ = (s - τ) • vvec t' := by
          rw [hp₂eq, sub_smul, ← hs']; abel
        rw [e, dot_smul_left, dot_vvec_uvec'] at h1
        nlinarith
      refine ⟨s / τ, 1 - s / τ, div_nonneg hs0 hτ.le, by
        rw [sub_nonneg, div_le_one hτ]; exact hsτ, by ring, ?_⟩
      have hq' : q = p₁ + s • vvec t' := by rw [← hs']; abel
      rw [hq', hp₂eq]
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
        field_simp <;> ring
    · intro hq
      have hqK : q ∈ K := hK.2.2.segment_subset hpb.1 hpa.1 hq
      have hqL : q ∈ line (t' + π) c :=
        (convex_line (t' + π) c).segment_subset hp₂line hp₁line hq
      exact ⟨⟨hqK, le_of_eq hqL⟩, hqL⟩


section arc

open Filter Topology Function

/-! ### Measurability and boundedness of the vertices -/

/-- `v_K⁺` is strongly measurable: it is the pointwise limit of clamped functions of bounded
variation. -/
lemma cvx_stronglyMeasurable_vplus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    StronglyMeasurable (vplus K) := by
  refine stronglyMeasurable_of_tendsto Filter.atTop
    (f := fun n : ℕ => clampFun (vplus K) (-(n : ℝ)) n)
    (fun n => (boundedVariationOn_clampFun (neg_le_self n.cast_nonneg)
      (lemma5_2_1 hK _ _)).stronglyMeasurable) ?_
  rw [tendsto_pi_nhds]
  intro t
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_ge_atTop ⌈|t|⌉₊] with n hn
  have h1 : |t| ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  exact (clampFun_of_mem ⟨by linarith [neg_abs_le t], (le_abs_self t).trans h1⟩).symm

/-- `v_K⁻` is strongly measurable: it is the left limit of `v_K⁺`. -/
lemma cvx_stronglyMeasurable_vminus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    StronglyMeasurable (vminus K) := by
  refine stronglyMeasurable_of_tendsto Filter.atTop
    (f := fun n : ℕ => Function.leftLim (clampFun (vplus K) (-(n : ℝ)) n))
    (fun n => (boundedVariationOn_clampFun (neg_le_self n.cast_nonneg)
      (lemma5_2_1 hK _ _)).leftLim.stronglyMeasurable) ?_
  rw [tendsto_pi_nhds]
  intro t
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_gt_atTop ⌈|t|⌉₊] with n hn
  have h1 : |t| < n := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn)
  have hlt : -(n : ℝ) < t := by linarith [neg_abs_le t]
  have hle : t ≤ n := (le_abs_self t).trans h1.le
  symm
  apply leftLim_eq_of_tendsto
  apply (tendsto_vplus_left hK t).congr'
  filter_upwards [Ioo_mem_nhdsLT hlt] with s hs
  exact (clampFun_of_mem ⟨hs.1.le, hs.2.le.trans hle⟩).symm

/-- A convex body is bounded. -/
lemma cvx_exists_bound {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    ∃ R : NNReal, ∀ p ∈ K, ‖p‖ ≤ R := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  exact ⟨R.toNNReal, fun p hp => (hR p hp).trans (Real.le_coe_toNNReal R)⟩

/-- On `(a, b)`, `dv_K⁺ = v_t σ_K` (Theorem 5.2.2) as vector measures restricted to `(a, b)`. -/
lemma cvx_lsMeasure_vplus_restrict_Ioo {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ}
    (hab : a < b) (hb : b < a + π) :
    (lsMeasure (vplus K) a b).restrict (Ioo a b) =
      ((sigma K).restrict (Ioo a b)).withDensityᵥ vvec := by
  have hb' : b ≤ a + 2 * π := by linarith [pi_pos]
  have hvi : Integrable vvec ((sigma K).restrict (Ioc a b)) := by
    have : IsFiniteMeasure ((sigma K).restrict (Ioc a b)) :=
      isFiniteMeasure_restrict.2 (measure_Ioc_lt_top).ne
    exact Integrable.of_bound continuous_vvec.aestronglyMeasurable 1
      (Filter.Eventually.of_forall norm_vvec_le)
  have e : Ioo a b = Ioo a b ∩ Ioc a b := (inter_eq_left.2 Ioo_subset_Ioc_self).symm
  conv_lhs => rw [e, ← VectorMeasure.restrict_restrict _ measurableSet_Ioo measurableSet_Ioc]
  rw [theorem5_2_2 hK hab, cvx_withDensityᵥ_restrict hvi measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo, ← e]

/-- `∫_{(a,b)} g × dv_K⁺ = ∫_{(a,b)} (g · u_t) dσ_K`, since `dv_K⁺ = v_t σ_K` on `(a, b)`. -/
lemma cvx_integral_cross_dvplus' {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b)
    (hb : b < a + π) {g : ℝ → ℝ × ℝ} (hgi : Integrable g ((sigma K).restrict (Ioo a b))) :
    ∫ᵛ t in Ioo a b, g t ∂[crossCLM; lsMeasure (vplus K) a b] =
      ∫ t in Ioo a b, dot (g t) (uvec t) ∂(sigma K) := by
  have : IsFiniteMeasure ((sigma K).restrict (Ioo a b)) :=
    isFiniteMeasure_restrict.2 (measure_Ioo_lt_top).ne
  have hvi : Integrable vvec ((sigma K).restrict (Ioo a b)) :=
    Integrable.of_bound continuous_vvec.aestronglyMeasurable 1 (Eventually.of_forall norm_vvec_le)
  rw [cvx_lsMeasure_vplus_restrict_Ioo hK hab hb,
    cvx_integral_withDensityᵥ hvi (M := 1) (Eventually.of_forall
      (fun t => by exact_mod_cast norm_vvec_le t)) crossCLM hgi]
  simp only [crossCLM_apply, cross_vvec]

/-- `½ ∫_{(a,b)} p_{K₁} × dv_{K₂}⁺ = ½ ∫_{(a,b)} h_{K₁} dσ_{K₂}` for a selection `p_{K₁}(t)` of the
supporting lines of `K₁`. -/
lemma cvx_integral_cross_dvplus {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsConvexBody K₁)
    (h₂ : IsConvexBody K₂) {a b : ℝ} (hab : a < b) (hb : b < a + π) {g : ℝ → ℝ × ℝ}
    (hgm : AEStronglyMeasurable g ((sigma K₂).restrict (Ioo a b)))
    (hgK : ∀ t, g t ∈ K₁) (hgl : ∀ t, dot (g t) (uvec t) = supp K₁ t) :
    ∫ᵛ t in Ioo a b, g t ∂[crossCLM; lsMeasure (vplus K₂) a b] =
      ∫ t in Ioo a b, supp K₁ t ∂(sigma K₂) := by
  have : IsFiniteMeasure ((sigma K₂).restrict (Ioo a b)) :=
    isFiniteMeasure_restrict.2 (measure_Ioo_lt_top).ne
  obtain ⟨R, hR⟩ := cvx_exists_bound h₁
  rw [cvx_integral_cross_dvplus' h₂ hab hb
    (Integrable.of_bound hgm R (Eventually.of_forall fun t => hR _ (hgK t)))]
  simp only [hgl]

/-! ### The generalized inverse of a distribution function -/

/-- The generalized inverse of `t ↦ (f t - f a) / L` on `[a, b]`. -/
noncomputable def cvxQuantile (f : StieltjesFunction ℝ) (a b L r : ℝ) : ℝ :=
  sInf {t | a ≤ t ∧ (b ≤ t ∨ f a + L * r ≤ f t)}

section quantile

variable {f : StieltjesFunction ℝ} {a b L : ℝ}

lemma cvxQuantile_bddBelow (r : ℝ) : BddBelow {t | a ≤ t ∧ (b ≤ t ∨ f a + L * r ≤ f t)} :=
  ⟨a, fun _ ht => ht.1⟩

lemma cvxQuantile_nonempty (hab : a ≤ b) (r : ℝ) :
    {t | a ≤ t ∧ (b ≤ t ∨ f a + L * r ≤ f t)}.Nonempty :=
  ⟨b, hab, Or.inl le_rfl⟩

lemma cvxQuantile_mem_Icc (hab : a ≤ b) (r : ℝ) : cvxQuantile f a b L r ∈ Icc a b :=
  ⟨le_csInf (cvxQuantile_nonempty hab r) (fun _ ht => ht.1),
    csInf_le (cvxQuantile_bddBelow r) ⟨hab, Or.inl le_rfl⟩⟩

lemma cvxQuantile_mono (hab : a ≤ b) (hL : 0 ≤ L) : Monotone (cvxQuantile f a b L) := by
  intro r r' hrr'
  apply csInf_le_csInf (cvxQuantile_bddBelow r) (cvxQuantile_nonempty hab r')
  rintro t ⟨hat, h | h⟩
  · exact ⟨hat, Or.inl h⟩
  · exact ⟨hat, Or.inr (le_trans (by nlinarith) h)⟩

/-- Below the jump at `b`, the generalized inverse lies in `[a, b)` and solves
`f a + L r ≤ f (cvxQuantile r)`. -/
lemma cvxQuantile_spec (hab : a < b) {r : ℝ} (hr : f a + L * r < leftLim f b) :
    cvxQuantile f a b L r < b ∧ f a + L * r ≤ f (cvxQuantile f a b L r) := by
  obtain ⟨t₀, ht₀, ht₀b⟩ : ∃ t₀, f a + L * r < f t₀ ∧ t₀ < b := by
    have hlim := f.mono.tendsto_leftLim b
    exact ((hlim.eventually (lt_mem_nhds hr)).and self_mem_nhdsWithin).exists
  have hxb : cvxQuantile f a b L r < b := by
    have : cvxQuantile f a b L r ≤ max t₀ a :=
      csInf_le (cvxQuantile_bddBelow r)
        ⟨le_max_right _ _, Or.inr (ht₀.le.trans (f.mono (le_max_left _ _)))⟩
    exact this.trans_lt (max_lt ht₀b hab)
  refine ⟨hxb, ?_⟩
  have hcont : Tendsto f (𝓝[>] (cvxQuantile f a b L r)) (𝓝 (f (cvxQuantile f a b L r))) :=
    ((f.right_continuous _).mono Ioi_subset_Ici_self).tendsto
  apply ge_of_tendsto hcont
  filter_upwards [Ioo_mem_nhdsGT hxb] with y hy
  obtain ⟨t, htS, hty⟩ := exists_lt_of_csInf_lt (cvxQuantile_nonempty hab.le r) hy.1
  rcases htS.2 with h | h
  · exact absurd (h.trans_lt (hty.trans hy.2)) (lt_irrefl _)
  · exact h.trans (f.mono hty.le)

/-- The Galois connection between the generalized inverse and `f`. -/
lemma cvxQuantile_le_iff (hab : a < b) {r t : ℝ} (hr : f a + L * r < leftLim f b) (hat : a ≤ t) :
    cvxQuantile f a b L r ≤ t ↔ f a + L * r ≤ f t := by
  constructor
  · intro h; exact (cvxQuantile_spec hab hr).2.trans (f.mono h)
  · intro h; exact csInf_le (cvxQuantile_bddBelow r) ⟨hat, Or.inr h⟩

/-- For `L r > 0`, the generalized inverse is `> a`. -/
lemma cvxQuantile_gt (hab : a < b) {r : ℝ} (hr : f a + L * r < leftLim f b) (hr0 : 0 < L * r) :
    a < cvxQuantile f a b L r := by
  rcases (cvxQuantile_mem_Icc (f := f) (L := L) hab.le r).1.lt_or_eq with h | h
  · exact h
  · have := (cvxQuantile_spec hab hr).2
    rw [← h] at this
    linarith

/-- `(0, 1) ∩ (-∞, s]` is `(0, s]` up to a null set. -/
lemma cvx_Ioo_inter_Iic_ae_eq {s : ℝ} (hs1 : s ≤ 1) :
    (Ioo (0 : ℝ) 1 ∩ Iic s : Set ℝ) =ᵐ[volume] Ioc 0 s := by
  refine ae_eq_set.2 ⟨?_, ?_⟩
  · refine measure_mono_null (fun r hr => ?_) (measure_empty (μ := volume))
    exact hr.2 ⟨hr.1.1.1, hr.1.2⟩
  · refine measure_mono_null (fun r hr => ?_) (measure_singleton (1 : ℝ))
    rw [mem_singleton_iff]
    by_contra hne
    exact hr.2 ⟨⟨hr.1.1, lt_of_le_of_ne (hr.1.2.trans hs1) hne⟩, hr.1.2⟩

/-- `|(0, 1) ∩ (-∞, s]| = s` for `s ≤ 1` (read as `0` for `s < 0`). -/
lemma cvx_volume_Ioo_inter_Iic {s : ℝ} (hs1 : s ≤ 1) :
    volume (Ioo (0 : ℝ) 1 ∩ Iic s) = ENNReal.ofReal s := by
  rw [measure_congr (cvx_Ioo_inter_Iic_ae_eq hs1), Real.volume_Ioc, sub_zero]

/-- For `a ≤ x` and `r ∈ (0, 1)`, the generalized inverse at `r` is at most `x` iff
`r ≤ (f x - f a) / L`. -/
lemma cvxQuantile_preimage_Iic (hab : a < b) (hL : L = leftLim f b - f a) (hLpos : 0 < L)
    {x : ℝ} (hxa : a ≤ x) :
    cvxQuantile f a b L ⁻¹' Iic x ∩ Ioo 0 1 = Ioo 0 1 ∩ Iic ((f x - f a) / L) := by
  have hr1 : ∀ r < 1, f a + L * r < leftLim f b := by
    intro r hr; rw [hL] at hLpos ⊢; nlinarith
  ext r
  simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioo]
  constructor
  · rintro ⟨hθ, hr0, hr1'⟩
    refine ⟨⟨hr0, hr1'⟩, ?_⟩
    rw [le_div_iff₀ hLpos]
    have := (cvxQuantile_le_iff hab (hr1 r hr1') hxa).1 hθ
    linarith
  · rintro ⟨⟨hr0, hr1'⟩, hr⟩
    refine ⟨(cvxQuantile_le_iff hab (hr1 r hr1') hxa).2 ?_, hr0, hr1'⟩
    rw [le_div_iff₀ hLpos] at hr
    linarith

/-- **The quantile transform.** The image of the Lebesgue measure on `(0, 1)` under the generalized
inverse of the normalized distribution function is the normalized Stieltjes measure on `(a, b)`. -/
theorem cvx_map_cvxQuantile (hab : a < b) (hL : L = leftLim f b - f a) (hLpos : 0 < L) :
    Measure.map (cvxQuantile f a b L) (volume.restrict (Ioo 0 1)) =
      (ENNReal.ofReal L)⁻¹ • f.measure.restrict (Ioo a b) := by
  have hmeas : Measurable (cvxQuantile f a b L) := (cvxQuantile_mono hab.le hLpos.le).measurable
  have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  have hLne : ENNReal.ofReal L ≠ 0 := (ENNReal.ofReal_pos.2 hLpos).ne'
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply hmeas measurableSet_Iic, Measure.restrict_apply (hmeas measurableSet_Iic),
    Measure.smul_apply, Measure.restrict_apply measurableSet_Iic, smul_eq_mul]
  rcases lt_or_ge x a with hxa | hxa
  · have h1 : cvxQuantile f a b L ⁻¹' Iic x ∩ Ioo 0 1 = ∅ := by
      ext r
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioo, mem_empty_iff_false, iff_false,
        not_and]
      intro h
      linarith [(cvxQuantile_mem_Icc (f := f) (L := L) hab.le r).1]
    have h2 : Iic x ∩ Ioo a b = ∅ := by
      ext r
      simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_empty_iff_false, iff_false, not_and]
      intro h1 h2; linarith
    simp [h1, h2]
  rcases lt_or_ge x b with hxb | hxb
  · have hsx : f a ≤ f x := f.mono hxa
    have hxl : f x ≤ leftLim f b := f.mono.le_leftLim hxb
    have h2 : Iic x ∩ Ioo a b = Ioc a x := by
      ext r
      simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans_lt hxb⟩
    have hs0 : 0 ≤ (f x - f a) / L := div_nonneg (by linarith) hLpos.le
    have hs1 : (f x - f a) / L ≤ 1 := by
      rw [div_le_one hLpos, hL]; linarith
    rw [cvxQuantile_preimage_Iic hab hL hLpos hxa, h2, cvx_volume_Ioo_inter_Iic hs1,
      StieltjesFunction.measure_Ioc,
      ENNReal.ofReal_div_of_pos hLpos, div_eq_mul_inv, mul_comm]
  · have h1 : cvxQuantile f a b L ⁻¹' Iic x ∩ Ioo 0 1 = Ioo 0 1 := by
      ext r
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioo, and_iff_right_iff_imp]
      intro _
      exact (cvxQuantile_mem_Icc (f := f) (L := L) hab.le r).2.trans hxb
    have h2 : Iic x ∩ Ioo a b = Ioo a b := by
      ext r
      simp only [mem_inter_iff, mem_Iic, mem_Ioo, and_iff_right_iff_imp]
      rintro ⟨_, h⟩; exact h.le.trans hxb
    rw [h1, h2, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, StieltjesFunction.measure_Ioo,
      ← hL, ENNReal.inv_mul_cancel hLne ENNReal.ofReal_ne_top]

/-- Integrals of functions of the quantile. -/
lemma cvx_integral_comp_cvxQuantile {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hab : a < b) (hL : L = leftLim f b - f a) (hLpos : 0 < L) {g : ℝ → E} (hg : Continuous g)
    {A : Set ℝ} (hA : MeasurableSet A) :
    ∫ r in cvxQuantile f a b L ⁻¹' A ∩ Ioo 0 1, g (cvxQuantile f a b L r) =
      L⁻¹ • ∫ t in A ∩ Ioo a b, g t ∂f.measure := by
  have hmeas := (cvxQuantile_mono (f := f) hab.le hLpos.le).measurable
  rw [← Measure.restrict_restrict (hmeas hA), ← setIntegral_map hA hg.aestronglyMeasurable
    hmeas.aemeasurable, cvx_map_cvxQuantile hab hL hLpos, Measure.restrict_smul,
    integral_smul_measure, Measure.restrict_restrict hA, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hLpos.le]

end quantile

/-! ### The arc-length parametrization of a convex arc -/

/-- The length `σ_K((a, b))` of the convex arc `𝐮_K^{a,b}`. -/
noncomputable def cvxArcL (K : Set (ℝ × ℝ)) (a b : ℝ) : ℝ :=
  leftLim (sigmaStieltjes K) b - sigmaStieltjes K a

/-- The normal angle at the point of the arc at normalized arc length `r`. -/
noncomputable def cvxArcθ (K : Set (ℝ × ℝ)) (a b : ℝ) : ℝ → ℝ :=
  cvxQuantile (sigmaStieltjes K) a b (cvxArcL K a b)

/-- The velocity of the normalized arc-length parametrization. -/
noncomputable def cvxArcψ (K : Set (ℝ × ℝ)) (a b : ℝ) (r : ℝ) : ℝ × ℝ :=
  cvxArcL K a b • vvec (cvxArcθ K a b r)

/-- The normalized arc-length parametrization `[0, 1] → 𝐮_K^{a,b}`. -/
noncomputable def cvxArc (K : Set (ℝ × ℝ)) (a b : ℝ) (s : ℝ) : ℝ × ℝ :=
  vplus K a + ∫ r in (0 : ℝ)..s, cvxArcψ K a b r

section param

variable {K : Set (ℝ × ℝ)} {a b : ℝ}

lemma cvxArcL_nonneg (hab : a < b) : 0 ≤ cvxArcL K a b :=
  sub_nonneg.2 ((sigmaStieltjes K).mono.le_leftLim hab)

lemma cvx_sigma_Ioo (K : Set (ℝ × ℝ)) (a b : ℝ) :
    sigma K (Ioo a b) = ENNReal.ofReal (cvxArcL K a b) :=
  (sigmaStieltjes K).measure_Ioo

lemma cvxArcθ_measurable (hab : a < b) : Measurable (cvxArcθ K a b) :=
  (cvxQuantile_mono hab.le (cvxArcL_nonneg hab)).measurable

lemma cvxArcψ_measurable (hab : a < b) : Measurable (cvxArcψ K a b) := by
  show Measurable (fun r => cvxArcL K a b • vvec (cvxArcθ K a b r))
  exact (continuous_vvec.measurable.comp (cvxArcθ_measurable hab)).const_smul (cvxArcL K a b)

lemma cvxArcψ_norm_le (hab : a < b) (r : ℝ) : ‖cvxArcψ K a b r‖ ≤ cvxArcL K a b := by
  rw [cvxArcψ, norm_smul, Real.norm_of_nonneg (cvxArcL_nonneg hab)]
  exact mul_le_of_le_one_right (cvxArcL_nonneg hab) (norm_vvec_le _)

lemma cvxArcψ_integrableOn (hab : a < b) {s : Set ℝ} (hs : volume s ≠ ⊤) :
    IntegrableOn (cvxArcψ K a b) s :=
  Measure.integrableOn_of_bounded (M := cvxArcL K a b) hs
    (cvxArcψ_measurable hab).aestronglyMeasurable
    (Eventually.of_forall (cvxArcψ_norm_le hab))

lemma cvxArcψ_intervalIntegrable (hab : a < b) (u v : ℝ) :
    IntervalIntegrable (cvxArcψ K a b) volume u v :=
  (cvxArcψ_integrableOn hab
    (by rw [Real.volume_interval]; exact ENNReal.ofReal_ne_top)).intervalIntegrable

/-- `∫_{(a, b)} v_t dσ_K(t) = v_K⁻(b) - v_K⁺(a)`. -/
lemma cvx_integral_vvec_Ioo (hK : IsConvexBody K) (hab : a < b) :
    ∫ t in Ioo a b, vvec t ∂(sigma K) = vminus K b - vplus K a := by
  have h1 := vplus_sub_vplus hK hab.le
  have hint : IntegrableOn vvec (Icc a b) (sigma K) := continuous_vvec.integrableOn_Icc
  rw [← Set.Ioo_union_right hab, setIntegral_union (Set.disjoint_left.2 fun t ht ht' => by
      rw [mem_singleton_iff] at ht'; rw [ht'] at ht; exact lt_irrefl _ ht.2)
    (measurableSet_singleton b) (hint.mono_set Ioo_subset_Icc_self)
    (hint.mono_set (by rw [singleton_subset_iff]; exact ⟨hab.le, le_rfl⟩)),
    integral_singleton] at h1
  have h2 := (proposition2_1_2 hK b).2
  rw [sigmaAt, ← measureReal_def] at h2
  rw [h2] at h1
  have e : ∫ t in Ioo a b, vvec t ∂(sigma K) = vminus K b + (sigma K).real {b} • vvec b -
      vplus K a - (sigma K).real {b} • vvec b := by rw [h1]; abel
  rw [e]; abel

lemma cvxArc_zero : cvxArc K a b 0 = vplus K a := by simp [cvxArc]

lemma cvxArc_primitive (s : ℝ) :
    cvxArc K a b s = cvxArc K a b 0 + ∫ r in (0 : ℝ)..s, cvxArcψ K a b r := by
  rw [cvxArc_zero]; rfl

lemma cvxArc_continuous (hab : a < b) : Continuous (cvxArc K a b) :=
  continuous_const.add (intervalIntegral.continuous_primitive (cvxArcψ_intervalIntegrable hab) 0)

/-- The parametrization passes through `v_K⁺(x)` at the normalized arc length of `(a, x]`. -/
lemma cvxArc_vplus (hK : IsConvexBody K) (hab : a < b) (hLpos : 0 < cvxArcL K a b) {x : ℝ}
    (hxa : a ≤ x) (hxb : x < b) :
    cvxArc K a b ((sigmaStieltjes K x - sigmaStieltjes K a) / cvxArcL K a b) = vplus K x := by
  have hs0 : 0 ≤ (sigmaStieltjes K x - sigmaStieltjes K a) / cvxArcL K a b :=
    div_nonneg (sub_nonneg.2 ((sigmaStieltjes K).mono hxa)) hLpos.le
  have hs1 : (sigmaStieltjes K x - sigmaStieltjes K a) / cvxArcL K a b ≤ 1 := by
    rw [div_le_one hLpos]
    unfold cvxArcL
    linarith [(sigmaStieltjes K).mono.le_leftLim hxb]
  have hset : cvxArcθ K a b ⁻¹' Iic x ∩ Ioo 0 1 =ᵐ[volume]
      Ioc 0 ((sigmaStieltjes K x - sigmaStieltjes K a) / cvxArcL K a b) := by
    rw [cvxArcθ, cvxQuantile_preimage_Iic (L := cvxArcL K a b) hab rfl hLpos hxa]
    exact cvx_Ioo_inter_Iic_ae_eq hs1
  have hIoc : Iic x ∩ Ioo a b = Ioc a x := by
    ext r
    simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans_lt hxb⟩
  unfold cvxArc
  rw [intervalIntegral.integral_of_le hs0, ← setIntegral_congr_set hset]
  simp only [cvxArcψ]
  rw [integral_smul, cvxArcθ, cvx_integral_comp_cvxQuantile (L := cvxArcL K a b) hab rfl hLpos
    continuous_vvec measurableSet_Iic, smul_smul, mul_inv_cancel₀ hLpos.ne', one_smul, hIoc,
    ← sigma_eq_measure, ← vplus_sub_vplus hK hxa]
  abel

/-- The parametrization ends at `v_K⁻(b)`. -/
lemma cvxArc_one (hK : IsConvexBody K) (hab : a < b) (hLpos : 0 < cvxArcL K a b) :
    cvxArc K a b 1 = vminus K b := by
  unfold cvxArc
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have e : Ioo (0 : ℝ) 1 = cvxArcθ K a b ⁻¹' univ ∩ Ioo 0 1 := by simp
  rw [e]
  simp only [cvxArcψ]
  rw [integral_smul, cvxArcθ, cvx_integral_comp_cvxQuantile (L := cvxArcL K a b) hab rfl hLpos
    continuous_vvec MeasurableSet.univ, smul_smul, mul_inv_cancel₀ hLpos.ne', one_smul, univ_inter,
    ← sigma_eq_measure, cvx_integral_vvec_Ioo hK hab]
  abel

/-- The parametrization passes through `v_K⁻(x)` at the normalized arc length of `(a, x)`. -/
lemma cvxArc_vminus (hK : IsConvexBody K) (hab : a < b) (hLpos : 0 < cvxArcL K a b) {x : ℝ}
    (hxa : a < x) (hxb : x < b) :
    cvxArc K a b ((leftLim (sigmaStieltjes K) x - sigmaStieltjes K a) / cvxArcL K a b) =
      vminus K x := by
  have h1 : Tendsto (fun x' => cvxArc K a b ((sigmaStieltjes K x' - sigmaStieltjes K a) /
      cvxArcL K a b)) (𝓝[<] x)
      (𝓝 (cvxArc K a b ((leftLim (sigmaStieltjes K) x - sigmaStieltjes K a) / cvxArcL K a b))) := by
    have := (((sigmaStieltjes K).mono.tendsto_leftLim x).sub_const (sigmaStieltjes K a)).div_const
      (cvxArcL K a b)
    exact ((cvxArc_continuous hab).tendsto _).comp this
  have h2 : Tendsto (fun x' => cvxArc K a b ((sigmaStieltjes K x' - sigmaStieltjes K a) /
      cvxArcL K a b)) (𝓝[<] x) (𝓝 (vminus K x)) := by
    apply (tendsto_vplus_left hK x).congr'
    filter_upwards [Ioo_mem_nhdsLT hxa] with x' hx'
    exact (cvxArc_vplus hK hab hLpos hx'.1.le (hx'.2.trans hxb)).symm
  exact tendsto_nhds_unique h1 h2

/-- On the edge `e_K(x)` the parametrization is affine. -/
lemma cvxArc_edge (hK : IsConvexBody K) (hab : a < b) (hLpos : 0 < cvxArcL K a b) {x : ℝ}
    (hxa : a < x) (hxb : x < b) {s : ℝ}
    (hs1 : (leftLim (sigmaStieltjes K) x - sigmaStieltjes K a) / cvxArcL K a b ≤ s)
    (hs2 : s ≤ (sigmaStieltjes K x - sigmaStieltjes K a) / cvxArcL K a b) :
    cvxArc K a b s = vminus K x +
      (cvxArcL K a b * s - (leftLim (sigmaStieltjes K) x - sigmaStieltjes K a)) • vvec x := by
  have hL : cvxArcL K a b = leftLim (sigmaStieltjes K) b - sigmaStieltjes K a := rfl
  have hsx1 : (sigmaStieltjes K x - sigmaStieltjes K a) / cvxArcL K a b ≤ 1 := by
    rw [div_le_one hLpos]
    linarith [(sigmaStieltjes K).mono.le_leftLim hxb]
  have hθ : ∀ r ∈ Ioc ((leftLim (sigmaStieltjes K) x - sigmaStieltjes K a) / cvxArcL K a b) s,
      r ≠ 1 → cvxArcθ K a b r = x := by
    intro r hr hr1
    have hr1' : r < 1 := lt_of_le_of_ne (hr.2.trans (hs2.trans hsx1)) hr1
    have hrl : sigmaStieltjes K a + cvxArcL K a b * r < leftLim (sigmaStieltjes K) b := by
      nlinarith
    apply le_antisymm
    · rw [cvxArcθ, cvxQuantile_le_iff hab hrl hxa.le]
      have := hr.2.trans hs2
      rw [le_div_iff₀ hLpos] at this
      linarith
    · by_contra hlt
      push Not at hlt
      have h1 := (cvxQuantile_spec hab hrl).2
      have h2 : sigmaStieltjes K (cvxArcθ K a b r) ≤ leftLim (sigmaStieltjes K) x :=
        (sigmaStieltjes K).mono.le_leftLim hlt
      have : r ≤ (leftLim (sigmaStieltjes K) x - sigmaStieltjes K a) / cvxArcL K a b := by
        rw [le_div_iff₀ hLpos]
        rw [cvxArcθ] at h2
        linarith
      exact absurd hr.1 (not_lt.2 this)
  have hint : ∫ r in ((leftLim (sigmaStieltjes K) x - sigmaStieltjes K a) / cvxArcL K a b)..s,
      cvxArcψ K a b r = (s - (leftLim (sigmaStieltjes K) x - sigmaStieltjes K a) /
        cvxArcL K a b) • (cvxArcL K a b • vvec x) := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => cvxArcL K a b • vvec x),
      intervalIntegral.integral_const]
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with r hr1 hr
    rw [uIoc_of_le hs1] at hr
    simp only [cvxArcψ, hθ r hr hr1]
  have hsub := intervalIntegral.integral_interval_sub_left
    (cvxArcψ_intervalIntegrable (K := K) hab 0 s)
    (cvxArcψ_intervalIntegrable hab 0
      ((leftLim (sigmaStieltjes K) x - sigmaStieltjes K a) / cvxArcL K a b))
  rw [hint] at hsub
  have hv := cvxArc_vminus hK hab hLpos hxa hxb
  have e1 : cvxArc K a b s = cvxArc K a b ((leftLim (sigmaStieltjes K) x - sigmaStieltjes K a) /
      cvxArcL K a b) + (s - (leftLim (sigmaStieltjes K) x - sigmaStieltjes K a) /
        cvxArcL K a b) • (cvxArcL K a b • vvec x) := by
    simp only [cvxArc]
    rw [← hsub]
    abel
  rw [e1, hv, smul_smul]
  congr 2
  field_simp

/-- At normalized arc length `s ∈ (0, 1)`, the normal angle lies in `(a, b)` and `s` lies in the
range of the corresponding edge. -/
lemma cvxArcθ_spec (hab : a < b) (hLpos : 0 < cvxArcL K a b) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    cvxArcθ K a b s ∈ Ioo a b ∧
      (leftLim (sigmaStieltjes K) (cvxArcθ K a b s) - sigmaStieltjes K a) / cvxArcL K a b ≤ s ∧
      s ≤ (sigmaStieltjes K (cvxArcθ K a b s) - sigmaStieltjes K a) / cvxArcL K a b := by
  have hL : cvxArcL K a b = leftLim (sigmaStieltjes K) b - sigmaStieltjes K a := rfl
  have hrl : sigmaStieltjes K a + cvxArcL K a b * s < leftLim (sigmaStieltjes K) b := by
    nlinarith [hs.2]
  have hspec := cvxQuantile_spec hab hrl
  have hgt := cvxQuantile_gt hab hrl (mul_pos hLpos hs.1)
  refine ⟨⟨hgt, hspec.1⟩, ?_, ?_⟩
  · rw [div_le_iff₀ hLpos]
    have : leftLim (sigmaStieltjes K) (cvxArcθ K a b s) ≤
        sigmaStieltjes K a + cvxArcL K a b * s := by
      apply le_of_tendsto ((sigmaStieltjes K).mono.tendsto_leftLim _)
      filter_upwards [self_mem_nhdsWithin] with y hy
      rcases lt_or_ge y a with hya | hya
      · linarith [(sigmaStieltjes K).mono hya.le, mul_pos hLpos hs.1]
      · by_contra hlt
        push Not at hlt
        have := (cvxQuantile_le_iff hab hrl hya).2 hlt.le
        exact absurd hy (not_lt.2 this)
    linarith
  · rw [le_div_iff₀ hLpos]
    unfold cvxArcθ
    linarith [hspec.2]

/-- A point `v_K⁻(t) + λ v_t` with `0 ≤ λ ≤ σ_K(t)` lies on the edge `e_K(t)`. -/
lemma cvx_mem_edge_of (hK : IsConvexBody K) {t lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ sigmaAt K t) :
    vminus K t + lam • vvec t ∈ edge K t := by
  rw [edge_eq_segment hK, segment_eq_image']
  have hv : vplus K t - vminus K t = sigmaAt K t • vvec t := by
    rw [(proposition2_1_2 hK t).2]; abel
  rcases h0.eq_or_lt with rfl | hpos
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
  · have hσ : 0 < sigmaAt K t := hpos.trans_le h1
    refine ⟨lam / sigmaAt K t, ⟨div_nonneg h0 hσ.le, (div_le_one hσ).2 h1⟩, ?_⟩
    simp only [hv, smul_smul, div_mul_cancel₀ _ hσ.ne']

/-- At `s ∈ (0, 1)` the parametrization lies on the edge with normal angle `cvxArcθ s`. -/
lemma cvxArc_mem_edge (hK : IsConvexBody K) (hab : a < b) (hLpos : 0 < cvxArcL K a b) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) : cvxArc K a b s ∈ edge K (cvxArcθ K a b s) := by
  obtain ⟨hx, h1, h2⟩ := cvxArcθ_spec hab hLpos hs
  rw [cvxArc_edge hK hab hLpos hx.1 hx.2 h1 h2]
  apply cvx_mem_edge_of hK
  · rw [div_le_iff₀ hLpos] at h1; linarith
  · rw [sigmaAt_eq_jump]; rw [le_div_iff₀ hLpos] at h2; linarith

/-- The parametrization sweeps out the convex curve `𝐮_K^{a,b}`. -/
lemma cvxArc_image (hK : IsConvexBody K) (hab : a < b) (hLpos : 0 < cvxArcL K a b) :
    cvxArc K a b '' Icc 0 1 = convexCurve K a b := by
  apply Subset.antisymm
  · rintro _ ⟨s, hs, rfl⟩
    simp only [convexCurve, mem_union, mem_singleton_iff, mem_iUnion, exists_prop]
    rcases hs.1.eq_or_lt with rfl | hs0
    · rw [cvxArc_zero]; exact Or.inl (Or.inl rfl)
    rcases hs.2.eq_or_lt with rfl | hs1
    · rw [cvxArc_one hK hab hLpos]; exact Or.inr rfl
    exact Or.inl (Or.inr ⟨_, (cvxArcθ_spec hab hLpos ⟨hs0, hs1⟩).1,
      cvxArc_mem_edge hK hab hLpos ⟨hs0, hs1⟩⟩)
  · intro q hq
    simp only [convexCurve, mem_union, mem_singleton_iff, mem_iUnion, exists_prop] at hq
    rcases hq with ((rfl | ⟨t, ht, hqt⟩) | rfl)
    · exact ⟨0, ⟨le_rfl, zero_le_one⟩, cvxArc_zero⟩
    · rw [edge_eq_segment hK, segment_eq_image'] at hqt
      obtain ⟨μ, hμ, rfl⟩ := hqt
      have hL : cvxArcL K a b = leftLim (sigmaStieltjes K) b - sigmaStieltjes K a := rfl
      have hl1 : sigmaStieltjes K a ≤ leftLim (sigmaStieltjes K) t :=
        (sigmaStieltjes K).mono.le_leftLim ht.1
      have hl2 : leftLim (sigmaStieltjes K) t ≤ sigmaStieltjes K t :=
        (sigmaStieltjes K).mono.leftLim_le le_rfl
      have hl3 : sigmaStieltjes K t ≤ leftLim (sigmaStieltjes K) b :=
        (sigmaStieltjes K).mono.le_leftLim ht.2
      set s₀ := (leftLim (sigmaStieltjes K) t - sigmaStieltjes K a) / cvxArcL K a b with hs₀
      set s₁ := (sigmaStieltjes K t - sigmaStieltjes K a) / cvxArcL K a b with hs₁
      have h01 : s₀ ≤ s₁ := div_le_div_of_nonneg_right (by linarith) hLpos.le
      have hs₀0 : 0 ≤ s₀ := div_nonneg (by linarith) hLpos.le
      have hs₁1 : s₁ ≤ 1 := by rw [hs₁, div_le_one hLpos]; linarith
      refine ⟨s₀ + μ * (s₁ - s₀), ⟨by nlinarith [hμ.1, hμ.2], by nlinarith [hμ.1, hμ.2]⟩, ?_⟩
      rw [cvxArc_edge hK hab hLpos ht.1 ht.2 (by nlinarith [hμ.1, hμ.2])
        (by nlinarith [hμ.1, hμ.2])]
      have hv : vplus K t - vminus K t = sigmaAt K t • vvec t := by
        rw [(proposition2_1_2 hK t).2]; abel
      show _ = vminus K t + μ • (vplus K t - vminus K t)
      rw [hv, smul_smul, sigmaAt_eq_jump]
      congr 2
      rw [hs₀, hs₁]
      field_simp
      ring
    · exact ⟨1, ⟨zero_le_one, le_rfl⟩, cvxArc_one hK hab hLpos⟩

/-- The cosine of the angle between `v_t` and `v_m` for `t ∈ [a, b]` and the midpoint `m`. -/
lemma cvx_cos_ge {t : ℝ} (ht : t ∈ Icc a b) (hb : b < a + π) :
    cos ((b - a) / 2) ≤ cos (t - (a + b) / 2) := by
  rw [← Real.cos_abs (t - (a + b) / 2)]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [ht.1, ht.2])
  rw [abs_le]; constructor <;> linarith [ht.1, ht.2]

/-- The parametrization is injective: its velocity has a positive component along `v_m`, `m` the
midpoint of `[a, b]`. -/
lemma cvxArc_injOn (hab : a < b) (hb : b < a + π) (hLpos : 0 < cvxArcL K a b) :
    InjOn (cvxArc K a b) (Icc 0 1) := by
  have hcos : 0 < cos ((b - a) / 2) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have key : ∀ s₁ s₂ : ℝ, s₁ < s₂ → cvxArcL K a b * cos ((b - a) / 2) * (s₂ - s₁) ≤
      dot (cvxArc K a b s₂ - cvxArc K a b s₁) (vvec ((a + b) / 2)) := by
    intro s₁ s₂ h12
    have hi := cvxArcψ_intervalIntegrable (K := K) hab s₁ s₂
    have hsub : cvxArc K a b s₂ - cvxArc K a b s₁ = ∫ r in s₁..s₂, cvxArcψ K a b r := by
      simp only [cvxArc]
      rw [add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
        (cvxArcψ_intervalIntegrable hab 0 s₂) (cvxArcψ_intervalIntegrable hab 0 s₁)]
    rw [hsub, ← dotCLM_apply, ← (dotCLM _).intervalIntegral_comp_comm hi]
    have hi' : IntervalIntegrable (fun r => dotCLM (vvec ((a + b) / 2)) (cvxArcψ K a b r))
        volume s₁ s₂ :=
      ⟨(dotCLM _).integrable_comp hi.1, (dotCLM _).integrable_comp hi.2⟩
    calc cvxArcL K a b * cos ((b - a) / 2) * (s₂ - s₁)
        = ∫ _ in s₁..s₂, cvxArcL K a b * cos ((b - a) / 2) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ ≤ ∫ r in s₁..s₂, dotCLM (vvec ((a + b) / 2)) (cvxArcψ K a b r) := by
          apply intervalIntegral.integral_mono_on h12.le intervalIntegrable_const hi'
          intro r _
          rw [dotCLM_apply, cvxArcψ, dot_smul_left, dot_vvec_vvec]
          exact mul_le_mul_of_nonneg_left
            (cvx_cos_ge (cvxQuantile_mem_Icc hab.le r) hb) (cvxArcL_nonneg hab)
  intro s₁ _ s₂ _ heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := key s₁ s₂ h
    rw [heq, sub_self, dot_zero_left] at this
    nlinarith [mul_pos (mul_pos hLpos hcos) (sub_pos.2 h)]
  · have := key s₂ s₁ h
    rw [heq, sub_self, dot_zero_left] at this
    nlinarith [mul_pos (mul_pos hLpos hcos) (sub_pos.2 h)]

/-- The curve area functional of the parametrization is `½ ∫_{(a,b)} h_K dσ_K`. -/
lemma cvxArc_curveArea (hK : IsConvexBody K) (hab : a < b) (hLpos : 0 < cvxArcL K a b) :
    curveArea (cvxArc K a b) 0 1 = convexCurveArea K a b := by
  rw [cvx_curveArea_of_primitive (M := (cvxArcL K a b).toNNReal) zero_le_one
    (cvxArcψ_integrableOn hab (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    (fun r _ => (cvxArcψ_norm_le hab r).trans (Real.le_coe_toNNReal _))
    (fun t _ => cvxArc_primitive t)]
  rw [convexCurveArea, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  congr 1
  have hpt : EqOn (fun r => cross (cvxArc K a b r) (cvxArcψ K a b r))
      (fun r => cvxArcL K a b * supp K (cvxArcθ K a b r)) (Ioo 0 1) := by
    intro r hr
    simp only [cvxArcψ, cross_smul_right, cross_vvec]
    rw [(cvxArc_mem_edge hK hab hLpos hr).2]
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_const_mul]
  have e : Ioo (0 : ℝ) 1 = cvxArcθ K a b ⁻¹' univ ∩ Ioo 0 1 := by simp
  rw [e, cvxArcθ, cvx_integral_comp_cvxQuantile (L := cvxArcL K a b) hab rfl hLpos
    (continuous_supp hK.2.1) MeasurableSet.univ, univ_inter, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hLpos.ne', one_mul, ← sigma_eq_measure]

/-- If the arc degenerates to a point, it carries no surface area measure. -/
lemma cvxArcL_eq_zero (hK : IsConvexBody K) (hab : a < b) (hb : b < a + π)
    (h : vplus K a = vminus K b) : cvxArcL K a b = 0 := by
  have hint := cvx_integral_vvec_Ioo hK hab
  rw [← h, sub_self] at hint
  have : IsFiniteMeasure ((sigma K).restrict (Ioo a b)) :=
    isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  have hcos : 0 < cos ((b - a) / 2) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hvi : IntegrableOn vvec (Ioo a b) (sigma K) :=
    continuous_vvec.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hdot : dotCLM (vvec ((a + b) / 2)) (∫ t in Ioo a b, vvec t ∂(sigma K)) =
      ∫ t in Ioo a b, cos (t - (a + b) / 2) ∂(sigma K) := by
    rw [← (dotCLM _).integral_comp_comm hvi]
    congr 1
    funext t
    rw [dotCLM_apply, dot_vvec_vvec]
  rw [hint, map_zero] at hdot
  have hge : (sigma K).real (Ioo a b) * cos ((b - a) / 2) ≤
      ∫ t in Ioo a b, cos (t - (a + b) / 2) ∂(sigma K) := by
    rw [← smul_eq_mul, ← setIntegral_const]
    apply setIntegral_mono_on (integrableOn_const (measure_Ioo_lt_top.ne))
      ((continuous_cos.comp (continuous_id.sub continuous_const)).integrableOn_Icc.mono_set
        Ioo_subset_Icc_self) measurableSet_Ioo
    intro t ht
    exact cvx_cos_ge ⟨ht.1.le, ht.2.le⟩ hb
  rw [← hdot, measureReal_def, cvx_sigma_Ioo, ENNReal.toReal_ofReal (cvxArcL_nonneg hab)] at hge
  nlinarith [cvxArcL_nonneg (K := K) hab]

end param

end arc

/-- **Theorem 7.3.2** (`thm:convex-curve-area-functional`). For `a < b < a + π`, the convex curve
`𝐮_K^{a,b}` is the image of a continuous curve of bounded variation from `v_K⁺(a)` to `v_K⁻(b)`,
injective unless the curve is a point, whose curve area functional is `½ ∫_{(a,b)} h_K dσ_K`. -/
theorem theorem7_3_2 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b)
    (hb : b < a + π) :
    ∃ γ : ℝ → ℝ × ℝ, IsCBV γ 0 1 ∧ γ '' Icc 0 1 = convexCurve K a b ∧ γ 0 = vplus K a ∧
      γ 1 = vminus K b ∧ (vplus K a ≠ vminus K b → InjOn γ (Icc 0 1)) ∧
      curveArea γ 0 1 = convexCurveArea K a b := by
  by_cases hdeg : vplus K a = vminus K b
  · have hσ0 : sigma K (Ioo a b) = 0 := by
      rw [cvx_sigma_Ioo, cvxArcL_eq_zero hK hab hb hdeg, ENNReal.ofReal_zero]
    refine ⟨fun _ => vplus K a, ⟨continuousOn_const, ?_⟩, ?_, rfl, hdeg, fun h => absurd hdeg h, ?_⟩
    · exact ((eVariationOn.constant_on (by simp)).trans_lt ENNReal.zero_lt_top).ne
    · rw [(lemma7_3_1_degenerate hK hab hb hdeg).2]
      ext q
      simp only [mem_image, mem_singleton_iff]
      constructor
      · rintro ⟨_, _, rfl⟩; rfl
      · rintro rfl; exact ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
    · rw [cvx_curveArea_of_primitive (ψ := fun _ => 0) (M := 0) zero_le_one (integrableOn_zero)
        (by simp) (by simp)]
      simp [convexCurveArea, Measure.restrict_eq_zero.2 hσ0, cross]
  · have hLpos : 0 < cvxArcL K a b := by
      rcases (cvxArcL_nonneg (K := K) hab).lt_or_eq with h | h
      · exact h
      · exfalso
        apply hdeg
        have hσ0 : sigma K (Ioo a b) = 0 := by rw [cvx_sigma_Ioo, ← h, ENNReal.ofReal_zero]
        have := cvx_integral_vvec_Ioo hK hab
        rw [Measure.restrict_eq_zero.2 hσ0, integral_zero_measure] at this
        exact (sub_eq_zero.1 this.symm).symm
    obtain ⟨hbv, hc⟩ := cvx_bv_of_primitive (M := (cvxArcL K a b).toNNReal) zero_le_one
      (cvxArcψ_integrableOn (K := K) hab (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
      (fun r _ => (cvxArcψ_norm_le hab r).trans (Real.le_coe_toNNReal _))
      (fun t _ => cvxArc_primitive t)
    exact ⟨cvxArc K a b, ⟨hc, hbv⟩, cvxArc_image hK hab hLpos, cvxArc_zero,
      cvxArc_one hK hab hLpos, fun _ => cvxArc_injOn hab hb hLpos, cvxArc_curveArea hK hab hLpos⟩


/-- **Theorem 7.3.2**, last claim: `𝒥(𝐮_K^{a,b})` is quadratic in `K`. -/
theorem theorem7_3_2_quadratic {a b : ℝ} :
    convexBodyDomain.IsQuadratic (fun K => convexCurveArea K.1 a b) :=
  ⟨fun K₁ K₂ => convexCurveBilin K₁.1 K₂.1 a b,
    (cvx_integral_supp_sigma_bilin (Metric.isBounded_Ioo a b)).const_mul (1 / 2), fun _ => rfl⟩

/-- **Lemma 7.3.3** (`lem:convex-curve-bilinear-computation`).
`𝓑(K₁, K₂) = ½ ∫_{(a,b)} v_{K₁}⁺ × dv_{K₂}⁺ = ½ ∫_{(a,b)} v_{K₁}⁻ × dv_{K₂}⁺`, and in particular
`𝒥(𝐮_K^{a,b}) = ½ ∫_{(a,b)} v_K⁺ × dv_K⁺`. -/
theorem lemma7_3_3 {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂) {a b : ℝ}
    (hab : a < b) (hb : b < a + π) :
    convexCurveBilin K₁ K₂ a b =
        (1 / 2) * ∫ᵛ t in Ioo a b, vplus K₁ t ∂[crossCLM; lsMeasure (vplus K₂) a b] ∧
      convexCurveBilin K₁ K₂ a b =
        (1 / 2) * ∫ᵛ t in Ioo a b, vminus K₁ t ∂[crossCLM; lsMeasure (vplus K₂) a b] := by
  constructor
  · rw [cvx_integral_cross_dvplus h₁ h₂ hab hb
      (cvx_stronglyMeasurable_vplus h₁).aestronglyMeasurable
      (fun t => (vplus_mem_edge h₁ t).1) (dot_vplus_uvec K₁)]
    rfl
  · rw [cvx_integral_cross_dvplus h₁ h₂ hab hb
      (cvx_stronglyMeasurable_vminus h₁).aestronglyMeasurable
      (fun t => (vminus_mem_edge h₁ t).1) (dot_vminus_uvec K₁)]
    rfl

/-- **Lemma 7.3.3**, the case `K₁ = K₂ = K`: `𝒥(𝐮_K^{a,b}) = ½ ∫_{(a,b)} v_K⁺ × dv_K⁺`. -/
theorem lemma7_3_3_self {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b)
    (hb : b < a + π) :
    convexCurveArea K a b =
      (1 / 2) * ∫ᵛ t in Ioo a b, vplus K t ∂[crossCLM; lsMeasure (vplus K) a b] :=
  (lemma7_3_3 hK hK hab hb).1

/-- **Lemma 7.3.4** (`lem:convex-curve-concat`). For `a < b < c < a + π`, `𝐮_K^{a,c}` is the
concatenation of `𝐮_K^{a,b}`, `e_K(b)` and `𝐮_K^{b,c}`: the union, meeting only at `v_K⁻(b)` and
`v_K⁺(b)`, with additive curve area functionals. -/
theorem lemma7_3_4 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (hc : c < a + π) :
    convexCurve K a c = convexCurve K a b ∪ edge K b ∪ convexCurve K b c ∧
      convexCurve K a b ∩ edge K b = {vminus K b} ∧ edge K b ∩ convexCurve K b c = {vplus K b} ∧
      convexCurveArea K a c =
        convexCurveArea K a b + segArea (vminus K b) (vplus K b) + convexCurveArea K b c := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the union: split the normal angles `t ∈ (a, c)` at `b`
    ext q
    simp only [convexCurve, mem_union, mem_singleton_iff, mem_iUnion, exists_prop, mem_Ioo]
    constructor
    · rintro ((rfl | ⟨t, ⟨hat, htc⟩, hq⟩) | rfl)
      · exact Or.inl (Or.inl (Or.inl (Or.inl rfl)))
      · rcases lt_trichotomy t b with htb | rfl | htb
        · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨t, ⟨hat, htb⟩, hq⟩)))
        · exact Or.inl (Or.inr hq)
        · exact Or.inr (Or.inl (Or.inr ⟨t, ⟨htb, htc⟩, hq⟩))
      · exact Or.inr (Or.inr rfl)
    · rintro ((((rfl | ⟨t, ⟨hat, htb⟩, hq⟩) | rfl) | hq) | ((rfl | ⟨t, ⟨hbt, htc⟩, hq⟩) | rfl))
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr ⟨t, ⟨hat, htb.trans hbc⟩, hq⟩)
      · exact Or.inl (Or.inr ⟨b, ⟨hab, hbc⟩, vminus_mem_edge hK b⟩)
      · exact Or.inl (Or.inr ⟨b, ⟨hab, hbc⟩, hq⟩)
      · exact Or.inl (Or.inr ⟨b, ⟨hab, hbc⟩, vplus_mem_edge hK b⟩)
      · exact Or.inl (Or.inr ⟨t, ⟨hab.trans hbt, htc⟩, hq⟩)
      · exact Or.inr rfl
  · -- the edges `e_K(t)`, `t < b`, meet `e_K(b)` only at `v_K⁻(b)`
    ext q
    simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hq, hqb⟩
      simp only [convexCurve, mem_union, mem_singleton_iff, mem_iUnion, exists_prop] at hq
      rcases hq with ((rfl | ⟨t, ht, hqt⟩) | rfl)
      · exact cvx_edge_inter_eq_vminus hK hab (by linarith) (vplus_mem_edge hK a) hqb
      · exact cvx_edge_inter_eq_vminus hK ht.2 (by linarith [ht.1]) hqt hqb
      · rfl
    · rintro rfl
      exact ⟨by simp [convexCurve], vminus_mem_edge hK b⟩
  · -- the edges `e_K(t)`, `t > b`, meet `e_K(b)` only at `v_K⁺(b)`
    ext q
    simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hqb, hq⟩
      simp only [convexCurve, mem_union, mem_singleton_iff, mem_iUnion, exists_prop] at hq
      rcases hq with ((rfl | ⟨t, ht, hqt⟩) | rfl)
      · rfl
      · exact cvx_edge_inter_eq_vplus hK ht.1 (by linarith [ht.2]) hqb hqt
      · exact cvx_edge_inter_eq_vplus hK hbc (by linarith) hqb (vminus_mem_edge hK c)
    · rintro rfl
      exact ⟨vplus_mem_edge hK b, by simp [convexCurve]⟩
  · -- additivity: `(a, c) = (a, b) ∪ {b} ∪ (b, c)`, and the atom at `b` is `𝒥(v_K⁻(b), v_K⁺(b))`
    have hint : ∀ s ⊆ Icc a c, IntegrableOn (supp K) s (sigma K) := fun s hs =>
      ((continuous_supp hK.2.1).integrableOn_Icc).mono_set hs
    have hsplit : Ioo a c = Ioo a b ∪ {b} ∪ Ioo b c := by
      ext t
      simp only [mem_Ioo, mem_union, mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩
        rcases lt_trichotomy t b with h | h | h
        · exact Or.inl (Or.inl ⟨h1, h⟩)
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨h, h2⟩
      · rintro ((⟨h1, h2⟩ | rfl) | ⟨h1, h2⟩)
        · exact ⟨h1, h2.trans hbc⟩
        · exact ⟨hab, hbc⟩
        · exact ⟨hab.trans h1, h2⟩
    have hseg : segArea (vminus K b) (vplus K b) = supp K b * sigmaAt K b / 2 :=
      proposition7_2_4_line (vminus_mem_edge hK b).2
        (by rw [(proposition2_1_2 hK b).2]; abel)
    simp only [convexCurveArea]
    rw [hsplit, setIntegral_union (Set.disjoint_left.2 fun t ht ht' => by
        rcases ht with ht | rfl
        · exact absurd ht'.1 (not_lt.2 ht.2.le)
        · exact absurd ht'.1 (lt_irrefl _)) measurableSet_Ioo
      (hint _ (fun t ht => by
        rcases ht with ht | rfl
        · exact ⟨ht.1.le, (ht.2.trans hbc).le⟩
        · exact ⟨hab.le, hbc.le⟩))
      (hint _ (fun t ht => ⟨(hab.trans ht.1).le, ht.2.le⟩)),
      setIntegral_union (Set.disjoint_left.2 fun t ht ht' => by
        rw [mem_singleton_iff] at ht'; rw [ht'] at ht; exact lt_irrefl _ ht.2)
      (measurableSet_singleton b) (hint _ (fun t ht => ⟨ht.1.le, (ht.2.trans hbc).le⟩))
      (hint _ (fun t ht => by rw [mem_singleton_iff] at ht; rw [ht]; exact ⟨hab.le, hbc.le⟩)),
      integral_singleton, hseg, sigmaAt, smul_eq_mul, measureReal_def]
    ring

section region

open Filter Topology Function
open scoped Pointwise

variable {K L : Set (ℝ × ℝ)}

/-! ### Periodicity -/

/-- `σ_K` is invariant under translation by multiples of `2π`. -/
lemma cvx_sigma_shift (hK : IsConvexBody K) (k : ℤ) (X : Set ℝ) :
    sigma K ((fun t => t + k * (2 * π)) '' X) = sigma K X := by
  induction k using Int.induction_on generalizing X with
  | zero => simp
  | succ n ih =>
    have e : (fun t => t + ((n : ℤ) + 1 : ℤ) * (2 * π)) '' X =
        (fun t => t + 2 * π) '' ((fun t => t + (n : ℤ) * (2 * π)) '' X) := by
      rw [image_image]; congr 1; funext t; push_cast; ring
    rw [e, sigma_periodic hK, ih]
  | pred n ih =>
    have e : (fun t => t + 2 * π) '' ((fun t => t + (-(n : ℤ) - 1 : ℤ) * (2 * π)) '' X) =
        (fun t => t + (-(n : ℤ) : ℤ) * (2 * π)) '' X := by
      rw [image_image]; congr 1; funext t; push_cast; ring
    rw [← sigma_periodic hK, e, ih]

/-- `σ_K` is invariant under the action of `2πℤ`. -/
lemma cvx_vaddInvariant (hK : IsConvexBody K) :
    VAddInvariantMeasure (AddSubgroup.zmultiples (2 * π)) ℝ (sigma K) := by
  constructor
  rintro ⟨c, hc⟩ s _
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hc
  have e : (fun x => (⟨k • (2 * π), hc⟩ : AddSubgroup.zmultiples (2 * π)) +ᵥ x) ⁻¹' s =
      (fun t => t + ((-k : ℤ) : ℝ) * (2 * π)) '' s := by
    ext x
    simp only [mem_preimage, mem_image]
    constructor
    · intro hx
      refine ⟨_, hx, ?_⟩
      show k • (2 * π) + x + ((-k : ℤ) : ℝ) * (2 * π) = x
      push_cast; rw [zsmul_eq_mul]; ring
    · rintro ⟨y, hy, rfl⟩
      show k • (2 * π) + (y + ((-k : ℤ) : ℝ) * (2 * π)) ∈ s
      convert hy using 1
      push_cast; rw [zsmul_eq_mul]; ring
  rw [e, cvx_sigma_shift hK]

lemma cvx_supp_zsmul (L : Set (ℝ × ℝ)) (k : ℤ) (t : ℝ) : supp L (k • (2 * π) + t) = supp L t := by
  have hper : Function.Periodic (supp L) (2 * π) := supp_add_two_pi L
  rw [add_comm]
  exact (hper.zsmul k) t

/-- The integral of `h_L` against `σ_K` over a period does not depend on the period. -/
lemma cvx_integral_window (hK : IsConvexBody K) (L : Set (ℝ × ℝ)) (s : ℝ) :
    ∫ t in Ioc s (s + 2 * π), supp L t ∂(sigma K) =
      ∫ t in Ioc 0 (0 + 2 * π), supp L t ∂(sigma K) := by
  have := cvx_vaddInvariant hK
  have h2π : 0 < 2 * π := by positivity
  exact IsAddFundamentalDomain.setIntegral_eq (isAddFundamentalDomain_Ioc h2π s (sigma K))
    (isAddFundamentalDomain_Ioc h2π 0 (sigma K)) (fun g x => by
      obtain ⟨c, hc⟩ := g
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hc
      exact cvx_supp_zsmul L k x)

/-! ### The surface area measure where the vertex is constant -/

/-- If the distribution functions of `σ_L` and `σ_K` differ by a constant on `[a, b)`, the
measures agree on `(a, b)`. -/
lemma cvx_sigma_restrict_Ioo_eq (hK : IsConvexBody K) (hL : IsConvexBody L) {a b : ℝ}
    (hab : a < b) (C : ℝ) (h : ∀ t ∈ Ico a b, sigmaFun L t = sigmaFun K t + C) :
    (sigma L).restrict (Ioo a b) = (sigma K).restrict (Ioo a b) := by
  have : IsFiniteMeasure ((sigma L).restrict (Ioo a b)) :=
    isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.restrict_apply measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  rcases le_or_gt x a with hxa | hxa
  · have e : Iic x ∩ Ioo a b = ∅ := by
      ext t; simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_empty_iff_false, iff_false, not_and]
      intro h1 h2; linarith
    simp [e]
  rcases lt_or_ge x b with hxb | hxb
  · have e : Iic x ∩ Ioo a b = Ioc a x := by
      ext t; simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans_lt hxb⟩
    rw [e, sigma_Ioc hL, sigma_Ioc hK, h x ⟨hxa.le, hxb⟩, h a ⟨le_rfl, hab⟩]
    congr 1; ring
  · have e : Iic x ∩ Ioo a b = Ioo a b := by
      ext t; simp only [mem_inter_iff, mem_Iic, mem_Ioo, and_iff_right_iff_imp]
      rintro ⟨_, h2⟩; exact h2.le.trans hxb
    rw [e, sigma_eq_measure, sigma_eq_measure, StieltjesFunction.measure_Ioo,
      StieltjesFunction.measure_Ioo]
    have hlim : leftLim (sigmaStieltjes L) b = leftLim (sigmaStieltjes K) b + C := by
      apply leftLim_eq_of_tendsto
      have := ((sigmaStieltjes K).mono.tendsto_leftLim b).add_const C
      apply this.congr'
      filter_upwards [Ioo_mem_nhdsLT hab] with t ht
      rw [sigmaStieltjes_apply hK, sigmaStieltjes_apply hL, h t ⟨ht.1.le, ht.2⟩]
    rw [hlim, sigmaStieltjes_apply hL a, sigmaStieltjes_apply hK a, h a ⟨le_rfl, hab⟩]
    congr 1; ring

/-- Equal edges have equal support values. -/
lemma cvx_supp_eq_of_edge_eq (hL : IsConvexBody L) {t : ℝ} (h : edge L t = edge K t) :
    supp L t = supp K t := by
  have hv := vplus_mem_edge hL t
  have hv' : vplus L t ∈ edge K t := h ▸ hv
  exact hv.2.symm.trans hv'.2

/-- Equal edges have equal vertices `v⁺`. -/
lemma cvx_vplus_eq_of_edge_eq (hL : IsConvexBody L) {t : ℝ} (h : edge L t = edge K t) :
    vplus L t = vplus K t := by
  simp only [vplus, cvx_supp_eq_of_edge_eq hL h, h]

/-- If the edge `e_L(t)` is a point, both vertices are that point. -/
lemma cvx_eq_of_edge_singleton (hL : IsConvexBody L) {t : ℝ} {p : ℝ × ℝ} (h : edge L t = {p}) :
    vplus L t = p ∧ vminus L t = p := by
  have h1 := vplus_mem_edge hL t
  have h2 := vminus_mem_edge hL t
  rw [h] at h1 h2
  exact ⟨h1, h2⟩

/-- The integral over a period may be taken over `[0, 2π)` or `(0, 2π]`. -/
lemma cvx_integral_Ico_eq_Ioc (hK : IsConvexBody K) (hL : IsConvexBody L) :
    ∫ t in Ico 0 (2 * π), supp L t ∂(sigma K) = ∫ t in Ioc 0 (0 + 2 * π), supp L t ∂(sigma K) := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hint : IntegrableOn (supp L) (Icc 0 (2 * π)) (sigma K) :=
    (continuous_supp hL.2.1).integrableOn_Icc
  rw [zero_add, ← Ioo_insert_left h2π, ← Ioo_union_right h2π, insert_eq,
    setIntegral_union (Set.disjoint_left.2 fun t ht ht' => by
      rw [mem_singleton_iff] at ht; rw [ht] at ht'; exact lt_irrefl _ ht'.1)
      measurableSet_Ioo (hint.mono_set (by rw [singleton_subset_iff]; exact ⟨le_rfl, h2π.le⟩))
      (hint.mono_set Ioo_subset_Icc_self),
    setIntegral_union (Set.disjoint_left.2 fun t ht ht' => by
      rw [mem_singleton_iff] at ht'; rw [ht'] at ht; exact lt_irrefl _ ht.2)
      (measurableSet_singleton _) (hint.mono_set Ioo_subset_Icc_self)
      (hint.mono_set (by rw [singleton_subset_iff]; exact ⟨h2π.le, le_rfl⟩)),
    integral_singleton, integral_singleton]
  have hσ : sigma K {2 * π} = sigma K {0} := by
    rw [← sigma_periodic hK {0}, image_singleton, zero_add]
  have hs : supp L (2 * π) = supp L 0 := by
    have := supp_add_two_pi L 0; rwa [zero_add] at this
  rw [measureReal_def, measureReal_def, hσ, hs]
  ring

/-- **The area of the cut body** `K' = K ∩ H'` of Lemma 7.3.1:
`|K'| = 𝒥(𝐮_K^{a,b}) + 𝒥(v_K⁻(b), v_K⁺(a))` (the two equations in the proof of Theorem 7.3.2). -/
lemma cvx_area_cut (hK : IsConvexBody K) {a b : ℝ} (hab : a < b) (hb : b < a + π)
    {t' c : ℝ} (ht' : t' ∈ Ioo a b)
    (hp₁ : vplus K a ∈ line (t' + π) c) (hp₂ : vminus K b ∈ line (t' + π) c)
    (hK' : IsConvexBody (K ∩ halfMinus (t' + π) c))
    (h1 : ∀ t ∈ Ioc (t' - π) a, edge (K ∩ halfMinus (t' + π) c) t = {vplus K a})
    (h2 : ∀ t ∈ Ioo a b, edge (K ∩ halfMinus (t' + π) c) t = edge K t)
    (h3 : ∀ t ∈ Ico b (t' + π), edge (K ∩ halfMinus (t' + π) c) t = {vminus K b})
    (h4 : edge (K ∩ halfMinus (t' + π) c) (t' + π) = segment ℝ (vminus K b) (vplus K a)) :
    area (K ∩ halfMinus (t' + π) c) =
      convexCurveArea K a b + segArea (vminus K b) (vplus K a) := by
  -- By Theorem 7.1.3, `|K'| = ½ ∫ h_{K'} dσ_{K'}` over a period, which we take to be
  -- `(t' - π, t' + π]`; `σ_{K'}` is concentrated on `(a, b) ∪ {t' + π}`, it equals `σ_K` on
  -- `(a, b)`, and its atom at `t' + π` is the segment `[v_K⁻(b), v_K⁺(a)]`.
  set K' := K ∩ halfMinus (t' + π) c with hK'def
  have hlt1 : t' - π < a := by linarith [ht'.2]
  have hlt2 : b < t' + π := by linarith [ht'.1]
  -- the vertices of `K'` at the normal angle `t' + π`
  obtain ⟨d, hd0, hd⟩ : ∃ d : ℝ, 0 ≤ d ∧ vplus K a - vminus K b = d • vvec (t' + π) := by
    refine ⟨_, ?_, sub_eq_smul_vvec (hp₂.trans hp₁.symm)⟩
    have hle : 0 ≤ dot (vplus K a - vminus K b) (uvec a) := by
      rw [dot_sub_left, (vplus_mem_edge hK a).2]
      linarith [dot_le_supp hK.2.1 (vminus_mem_edge hK b).1 a]
    have hs : 0 < sin (t' - a) :=
      sin_pos_of_pos_of_lt_pi (by linarith [ht'.1]) (by linarith [ht'.2])
    rw [sub_eq_smul_vvec (hp₂.trans hp₁.symm), dot_smul_left, dot_vvec_uvec',
      show a - (t' + π) = (a - t') - π by ring, sin_sub_pi, show a - t' = -(t' - a) by ring,
      sin_neg, neg_neg] at hle
    exact nonneg_of_mul_nonneg_left hle hs
  have hseg : ∀ q ∈ edge K' (t' + π), ∃ θ ∈ Icc (0 : ℝ) 1,
      q = vminus K b + (θ * d) • vvec (t' + π) := by
    intro q hq
    rw [h4, segment_eq_image'] at hq
    obtain ⟨θ, hθ, rfl⟩ := hq
    exact ⟨θ, hθ, by simp only [hd, smul_smul]⟩
  have hvp : vplus K' (t' + π) = vplus K a := by
    refine (cvx_eq_vplus hK' (by rw [h4]; exact right_mem_segment _ _ _) fun q hq => ?_).symm
    obtain ⟨θ, hθ, rfl⟩ := hseg q hq
    have e : vplus K a = vminus K b + d • vvec (t' + π) := by rw [← hd]; abel
    rw [e, dot_add_left, dot_add_left, dot_smul_left, dot_smul_left, dot_vvec_self]
    nlinarith [hθ.2]
  have hvm : vminus K' (t' + π) = vminus K b := by
    refine (cvx_eq_vminus hK' (by rw [h4]; exact left_mem_segment _ _ _) fun q hq => ?_).symm
    obtain ⟨θ, hθ, rfl⟩ := hseg q hq
    rw [dot_add_left, dot_smul_left, dot_vvec_self]
    nlinarith [hθ.1]
  -- `σ_{K'}` vanishes outside `(a, b) ∪ {t' + π}`
  have hz1 : sigma K' (Ioc (t' - π) a) = 0 := by
    refine sigma_Ioc_eq_zero_of_vplus_const hK' hlt1.le (p := vplus K a) fun t ht => ?_
    rcases ht.1.eq_or_lt with h | h
    · rw [← h, ← vplus_add_two_pi, show t' - π + 2 * π = t' + π by ring, hvp]
    · exact (cvx_eq_of_edge_singleton hK' (h1 t ⟨h, ht.2⟩)).1
  have hz2 : sigma K' (Ico b (t' + π)) = 0 := by
    rw [← Ioo_insert_left hlt2, insert_eq]
    refine measure_union_null ?_ ?_
    · have := cvx_eq_of_edge_singleton hK' (h3 b ⟨le_rfl, hlt2⟩)
      exact inj_sigma_singleton_eq_zero hK' (this.1.trans this.2.symm)
    · exact sigma_Ioo_eq_zero_of_vplus_const hK' hlt2 (q := vminus K b)
        fun t ht => (cvx_eq_of_edge_singleton hK' (h3 t ht)).1
  -- `σ_{K'} = σ_K` on `(a, b)`
  have hva : vplus K' a = vplus K a := (cvx_eq_of_edge_singleton hK' (h1 a ⟨hlt1, le_rfl⟩)).1
  have hvab : ∀ t ∈ Ico a b, vplus K' t = vplus K t := by
    intro t ht
    rcases ht.1.eq_or_lt with h | h
    · rw [← h, hva]
    · exact cvx_vplus_eq_of_edge_eq hK' (h2 t ⟨h, ht.2⟩)
  have hsab : ∀ t ∈ Ico a b, supp K' t = supp K t := by
    intro t ht
    rw [← dot_vplus_uvec K' t, hvab t ht, dot_vplus_uvec]
  have hres : (sigma K').restrict (Ioo a b) = (sigma K).restrict (Ioo a b) := by
    have hc := continuous_supp hK.2.1
    have hc' := continuous_supp hK'.2.1
    refine cvx_sigma_restrict_Ioo_eq hK hK' hab (sigmaFun K' a - sigmaFun K a) fun t ht => ?_
    have hI : ∫ s in a..t, supp K' s = ∫ s in a..t, supp K s :=
      intervalIntegral.integral_congr fun s hs => by
        rw [uIcc_of_le ht.1] at hs; exact hsab s ⟨hs.1, hs.2.trans_lt ht.2⟩
    simp only [sigmaFun, hvab t ht, hva]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hc'.intervalIntegrable 0 a)
      (hc'.intervalIntegrable a t), ← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a t), hI]
    ring
  -- the area
  have hint : ∀ X : Set ℝ, X ⊆ Icc (t' - π) (t' + π) → IntegrableOn (supp K') X (sigma K') :=
    fun X hX => ((continuous_supp hK'.2.1).integrableOn_Icc).mono_set hX
  have hae : Ioc (t' - π) (t' + π) =ᵐ[sigma K'] Ioo a b ∪ {t' + π} := by
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · refine measure_mono_null (fun t ht => ?_) (measure_union_null hz1 hz2)
      simp only [Set.mem_sdiff, mem_Ioc, mem_union, mem_Ioo, mem_singleton_iff, not_or, not_and,
        not_lt, mem_Ico] at ht ⊢
      by_cases hta : t ≤ a
      · exact Or.inl ⟨ht.1.1, hta⟩
      · push Not at hta
        right
        refine ⟨?_, lt_of_le_of_ne ht.1.2 ht.2.2⟩
        by_contra htb
        push Not at htb
        exact absurd (ht.2.1 hta) (not_le.2 htb)
    · refine measure_mono_null (fun t ht => ?_) measure_empty
      simp only [Set.mem_sdiff, mem_union, mem_Ioo, mem_singleton_iff, mem_Ioc] at ht
      rcases ht.1 with h | h
      · exact ht.2 ⟨by linarith [h.1], by linarith [h.2]⟩
      · exact ht.2 ⟨by rw [h]; linarith [pi_pos], by rw [h]⟩
  rw [theorem7_1_3 hK', cvx_integral_Ico_eq_Ioc hK' hK', ← cvx_integral_window hK' K' (t' - π),
    show t' - π + 2 * π = t' + π by ring, setIntegral_congr_set hae,
    setIntegral_union (Set.disjoint_left.2 fun t ht ht' => by
      rw [mem_singleton_iff] at ht'; rw [ht'] at ht; exact absurd ht.2 (not_lt.2 hlt2.le))
      (measurableSet_singleton _)
      (hint _ fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (hint _ fun t ht => by
        rw [mem_singleton_iff] at ht; rw [ht]; exact ⟨by linarith [pi_pos], le_rfl⟩),
    integral_singleton, hres]
  have hsupp : EqOn (supp K') (supp K) (Ioo a b) := fun t ht => hsab t ⟨ht.1.le, ht.2⟩
  rw [setIntegral_congr_fun measurableSet_Ioo hsupp]
  -- the atom at `t' + π`
  have hσ := (proposition2_1_2 hK' (t' + π)).2
  rw [hvp, hvm] at hσ
  have hsupp' : supp K' (t' + π) = c := by
    rw [← dot_vplus_uvec K' (t' + π), hvp]; exact hp₁
  have hseg' : segArea (vminus K b) (vplus K a) = c * sigmaAt K' (t' + π) / 2 :=
    proposition7_2_4_line hp₂ (by rw [hσ]; abel)
  rw [hseg', hsupp', convexCurveArea, measureReal_def, smul_eq_mul, sigmaAt]
  ring

/-! ### The area of a triangle -/

/-- A convex combination of `p`, `q`, `r` lies in their convex hull. -/
lemma cvx_mem_convexHull_three {p q r x : ℝ × ℝ} {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hγ : 0 ≤ γ) (hs : α + β + γ = 1) (hx : x = α • p + β • q + γ • r) :
    x ∈ convexHull ℝ {p, q, r} := by
  have hc := convex_convexHull ℝ ({p, q, r} : Set (ℝ × ℝ))
  have mp : p ∈ convexHull ℝ ({p, q, r} : Set (ℝ × ℝ)) := subset_convexHull ℝ _ (by simp)
  have mq : q ∈ convexHull ℝ ({p, q, r} : Set (ℝ × ℝ)) := subset_convexHull ℝ _ (by simp)
  have mr : r ∈ convexHull ℝ ({p, q, r} : Set (ℝ × ℝ)) := subset_convexHull ℝ _ (by simp)
  rcases (add_nonneg hβ hγ).eq_or_lt with h0 | hpos
  · have hβ0 : β = 0 := by linarith
    have hγ0 : γ = 0 := by linarith
    have hα1 : α = 1 := by linarith
    rw [hx, hβ0, hγ0, hα1, one_smul, zero_smul, zero_smul, add_zero, add_zero]
    exact mp
  · have mqr := hc mq mr (div_nonneg hβ hpos.le) (div_nonneg hγ hpos.le)
      (by rw [← add_div, div_self hpos.ne'])
    have := hc mp mqr hα hpos.le (by linarith)
    convert this using 1
    rw [hx, smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hpos.ne',
      mul_div_cancel₀ _ hpos.ne', add_assoc]

/-- The standard triangle `conv{(0, 0), (1, 0), (0, 1)}`. -/
lemma cvx_convexHull_std :
    convexHull ℝ {((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))} =
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} := by
  apply Subset.antisymm
  · apply convexHull_min
    · intro p hp
      simp only [mem_insert_iff, mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl <;> norm_num
    · intro p hp q hq α β hα hβ hαβ
      simp only [mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul] at hp hq ⊢
      refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
    exact cvx_mem_convexHull_three (α := 1 - x - y) (by linarith) hx hy (by ring)
      (by ext <;> simp)

/-- The standard triangle has area `1/2`. -/
lemma cvx_volume_std :
    volume {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} = ENNReal.ofReal (1 / 2) := by
  have hm : MeasurableSet {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} :=
    (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_le (measurable_fst.add measurable_snd) measurable_const))
  rw [Measure.volume_eq_prod, Measure.prod_apply hm]
  have hslice : ∀ x : ℝ, volume (Prod.mk x ⁻¹' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}) =
      (Icc (0 : ℝ) 1).indicator (fun x => ENNReal.ofReal (1 - x)) x := by
    intro x
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · have e : Prod.mk x ⁻¹' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} = Icc 0 (1 - x) := by
        ext y
        simp only [mem_preimage, mem_ofPred_eq, mem_Icc]
        constructor
        · rintro ⟨_, h1, h2⟩; exact ⟨h1, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨hx.1, h1, by linarith⟩
      rw [e, Real.volume_Icc, indicator_of_mem hx, sub_zero]
    · have e : Prod.mk x ⁻¹' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} = ∅ := by
        ext y
        simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
        intro h1 h2
        simp only [mem_Icc, not_and, not_le] at hx
        linarith [hx h1]
      rw [e, measure_empty, indicator_of_notMem hx]
  simp_rw [hslice]
  rw [lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
      integral_id]
    norm_num
  · exact (continuous_const.sub continuous_id).integrableOn_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simp only [Pi.zero_apply]; linarith [hx.2]

/-- **The area of a triangle** `|conv{p, q, r}| = |(q - p) × (r - p)| / 2`. -/
lemma cvx_area_triangle (p q r : ℝ × ℝ) :
    area (convexHull ℝ {p, q, r}) = |cross (q - p) (r - p)| / 2 := by
  set L := Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![(q - p).1, (r - p).1; (q - p).2, (r - p).2] with hL
  have hLapp : ∀ v : ℝ × ℝ, L v = v.1 • (q - p) + v.2 • (r - p) := by
    intro v
    rw [hL, Matrix.toLin_finTwoProd_apply]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Prod.fst_sub, Prod.snd_sub] <;> ring
  have himg : ({p, q, r} : Set (ℝ × ℝ)) =
      p +ᵥ L '' {((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))} := by
    simp only [image_insert_eq, image_singleton, hLapp, vadd_set_insert, vadd_set_singleton,
      vadd_eq_add]
    norm_num
  rw [himg, convexHull_vadd, ← LinearMap.image_convexHull, cvx_convexHull_std, area,
    measure_vadd, Measure.addHaar_image_linearMap, cvx_volume_std, hL, LinearMap.det_toLin,
    Matrix.det_fin_two_of, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    ENNReal.toReal_ofReal (by norm_num)]
  rw [show (q - p).1 * (r - p).2 - (r - p).1 * (q - p).2 = cross (q - p) (r - p) by
    simp only [cross]; ring]
  ring

/-- In the plane, `(A × B) w = (w × B) A + (A × w) B`. -/
lemma cvx_cross_decomp (A B w : ℝ × ℝ) :
    cross A B • w = cross w B • A + cross A w • B := by
  ext <;> simp only [cross, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
    smul_eq_mul] <;> ring

end region

/-- The region of Lemma 7.3.5: the interior of the triangle `v_K⁺(a), v_K(a, b), v_K⁻(b)` outside
`⋂_{t ∈ [a, b]} H_K(t)`. -/
def convexCurveRegion (K : Set (ℝ × ℝ)) (a b : ℝ) : Set (ℝ × ℝ) :=
  interior (convexHull ℝ {vplus K a, vint K a b, vminus K b}) \ ⋂ t ∈ Icc a b, suppHalf K t

/-- **Lemma 7.3.5** (`lem:convex-curve-jordan-curve`) (2) and (3), with (1) replaced by the area of
the region (see the module docstring): the region lies in the interior of `H_K(a) ∩ H_K(b)`, is
disjoint from `⋂_{t ∈ [a,b]} H_K(t)`, and has area
`𝒥(v_K⁺(a), v_K(a,b)) + 𝒥(v_K(a,b), v_K⁻(b)) - 𝒥(𝐮_K^{a,b})`. -/
theorem lemma7_3_5 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b)
    (hb : b < a + π) (h : vplus K a ≠ vminus K b) :
    convexCurveRegion K a b ⊆ interior (suppHalf K a ∩ suppHalf K b) ∧
      Disjoint (convexCurveRegion K a b) (⋂ t ∈ Icc a b, suppHalf K t) ∧
      area (convexCurveRegion K a b) =
        segArea (vplus K a) (vint K a b) + segArea (vint K a b) (vminus K b) -
          convexCurveArea K a b := by
  -- With the cut body `K' = K ∩ H'` of Lemma 7.3.1 and the triangle
  -- `T = conv{v_K⁺(a), v_K(a, b), v_K⁻(b)}`, we show `T ∩ ⋂_{t ∈ [a,b]} H_K(t) = K'`; the region is
  -- then `T° \ K'`, of area `|T| - |K'|`, computed by `cvx_area_triangle` and `cvx_area_cut`.
  obtain ⟨t', ht', c, hp₁l, hp₂l, hp₀lt, hK'cb, h1, h2, h3, h4⟩ := lemma7_3_1 hK hab hb h
  have hsin : 0 < sin (b - a) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hpa : vplus K a ∈ edge K a := vplus_mem_edge hK a
  have hpb : vminus K b ∈ edge K b := vminus_mem_edge hK b
  have h0a : dot (vint K a b) (uvec a) = supp K a := vint_mem_line_left K a b
  have h0b : dot (vint K a b) (uvec b) = supp K b := vint_mem_line_right K hsin.ne'
  have hu : uvec (t' + π) = -uvec t' := uvec_add_pi t'
  have hsta : 0 < sin (t' - a) :=
    sin_pos_of_pos_of_lt_pi (by linarith [ht'.1]) (by linarith [ht'.2])
  have hsbt : 0 < sin (b - t') :=
    sin_pos_of_pos_of_lt_pi (by linarith [ht'.2]) (by linarith [ht'.1])
  -- the three sides
  obtain ⟨α, hα⟩ : ∃ α, vint K a b - vplus K a = α • vvec a :=
    ⟨_, sub_eq_smul_vvec (hpa.2.trans h0a.symm)⟩
  obtain ⟨β, hβ⟩ : ∃ β, vminus K b - vint K a b = β • vvec b :=
    ⟨_, sub_eq_smul_vvec (h0b.trans hpb.2.symm)⟩
  have hαpos : 0 < α := by
    have e : dot (vint K a b - vplus K a) (uvec (t' + π)) = -(α * sin (t' - a)) := by
      rw [hα, dot_smul_left, hu, dot_neg_right, dot_vvec_uvec', mul_neg]
    have : dot (vint K a b - vplus K a) (uvec (t' + π)) < 0 := by
      rw [dot_sub_left]; have := hp₁l; simp only [line, mem_ofPred_eq] at this; linarith
    nlinarith
  have hβpos : 0 < β := by
    have e : dot (vminus K b - vint K a b) (uvec (t' + π)) = β * sin (b - t') := by
      rw [hβ, dot_smul_left, hu, dot_neg_right, dot_vvec_uvec', show t' - b = -(b - t') by ring,
        sin_neg]
      ring
    have : 0 < dot (vminus K b - vint K a b) (uvec (t' + π)) := by
      rw [dot_sub_left]; have := hp₂l; simp only [line, mem_ofPred_eq] at this; linarith
    nlinarith
  -- `T ⊆ H_K(a) ∩ H_K(b)`
  have hTab : convexHull ℝ {vplus K a, vint K a b, vminus K b} ⊆ suppHalf K a ∩ suppHalf K b := by
    apply convexHull_min _ ((convex_halfMinus _ _).inter (convex_halfMinus _ _))
    intro q hq
    simp only [mem_insert_iff, mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨dot_le_supp hK.2.1 hpa.1 a, dot_le_supp hK.2.1 hpa.1 b⟩
    · exact ⟨h0a.le, h0b.le⟩
    · exact ⟨dot_le_supp hK.2.1 hpb.1 a, dot_le_supp hK.2.1 hpb.1 b⟩
  refine ⟨fun q hq => interior_mono hTab hq.1, disjoint_sdiff_left, ?_⟩
  have hc : c = dot (vplus K a) (uvec (t' + π)) := hp₁l.symm
  have hH : ∀ q, q ∈ halfMinus (t' + π) c ↔ 0 ≤ dot (q - vplus K a) (uvec t') := by
    intro q
    show dot q (uvec (t' + π)) ≤ c ↔ _
    rw [hc, hu, dot_neg_right, dot_neg_right, neg_le_neg_iff, dot_sub_left, sub_nonneg]
  -- the triangle is positively oriented
  have hB : vminus K b - vplus K a = α • vvec a + β • vvec b := by rw [← hα, ← hβ]; abel
  have hcvv : ∀ x y : ℝ, cross (vvec x) (vvec y) = sin (y - x) := fun x y => by
    rw [cross_vvec, dot_vvec_uvec']
  have hcpos : 0 < cross (vint K a b - vplus K a) (vminus K b - vplus K a) := by
    rw [hα, hB, cross_add_right, cross_smul_left, cross_smul_right, cross_smul_left,
      cross_smul_right, cross_self, hcvv]
    have := mul_pos (mul_pos hαpos hβpos) hsin
    nlinarith
  -- `v_K⁻(b) - v_K⁺(a)` is a positive multiple of `v_{t'}`
  have hBt : vminus K b - vplus K a =
      dot (vminus K b - vplus K a) (vvec t') • vvec t' := by
    refine eq_smul_vvec_of_dot_uvec_eq_zero ?_
    have e1 := hp₁l; have e2 := hp₂l
    simp only [line, mem_ofPred_eq, hu, dot_neg_right] at e1 e2
    rw [dot_sub_left]; linarith
  have hspos : 0 < dot (vminus K b - vplus K a) (vvec t') := by
    have e : cross (vint K a b - vplus K a) (vminus K b - vplus K a) =
        α * dot (vminus K b - vplus K a) (vvec t') * sin (t' - a) := by
      conv_lhs => rw [hBt, hα]
      rw [cross_smul_left, cross_smul_right, hcvv]; ring
    rw [e] at hcpos
    have := mul_pos hαpos hsta
    by_contra hneg; push Not at hneg
    nlinarith
  -- the triangle and the cut body
  have hsub2 : K ∩ halfMinus (t' + π) c ⊆
      convexHull ℝ {vplus K a, vint K a b, vminus K b} ∩ ⋂ t ∈ Icc a b, suppHalf K t := by
    intro q hq
    refine ⟨?_, mem_iInter₂.2 fun t _ => dot_le_supp hK.2.1 hq.1 t⟩
    obtain ⟨A, hAdef⟩ : ∃ A, A = vint K a b - vplus K a := ⟨_, rfl⟩
    obtain ⟨B, hBdef⟩ : ∃ B, B = vminus K b - vplus K a := ⟨_, rfl⟩
    obtain ⟨w, hwdef⟩ : ∃ w, w = q - vplus K a := ⟨_, rfl⟩
    have hAα : A = α • vvec a := by rw [hAdef, hα]
    have hBt' : B = dot B (vvec t') • vvec t' := by rw [hBdef]; exact hBt
    have hspos' : 0 < dot B (vvec t') := by rw [hBdef]; exact hspos
    have hDpos : 0 < cross A B := by rw [hAdef, hBdef]; exact hcpos
    have hdec := cvx_cross_decomp A B w
    have hl₃ : 0 ≤ cross A w := by
      have e : cross A w = -(α * dot w (uvec a)) := by
        rw [hAα, cross_smul_left, cross_anticomm, cross_vvec]; ring
      rw [e]
      have : dot w (uvec a) ≤ 0 := by
        rw [hwdef, dot_sub_left, hpa.2]; linarith [dot_le_supp hK.2.1 hq.1 a]
      nlinarith
    have hl₂ : 0 ≤ cross w B := by
      have e : cross w B = dot B (vvec t') * dot w (uvec t') := by
        conv_lhs => rw [hBt']
        rw [cross_smul_right, cross_vvec]
      rw [e]
      exact mul_nonneg hspos'.le (by rw [hwdef]; exact (hH q).1 hq.2)
    have hl₁ : 0 ≤ cross A B - cross w B - cross A w := by
      have e : cross A B - cross w B - cross A w =
          cross (vint K a b - q) (vminus K b - vint K a b) := by
        rw [hAdef, hBdef, hwdef]; simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
      rw [e, hβ, cross_smul_right, cross_vvec, dot_sub_left, h0b]
      exact mul_nonneg hβpos.le (sub_nonneg.2 (dot_le_supp hK.2.1 hq.1 b))
    obtain ⟨l₂, hl₂def⟩ : ∃ l, l = cross w B / cross A B := ⟨_, rfl⟩
    obtain ⟨l₃, hl₃def⟩ : ∃ l, l = cross A w / cross A B := ⟨_, rfl⟩
    have hw : w = l₂ • A + l₃ • B := by
      have e : w = (cross A B)⁻¹ • (cross A B • w) := by
        rw [smul_smul, inv_mul_cancel₀ hDpos.ne', one_smul]
      conv_lhs => rw [e]
      rw [hdec, smul_add, smul_smul, smul_smul, inv_mul_eq_div, inv_mul_eq_div, hl₂def, hl₃def]
    refine cvx_mem_convexHull_three (α := 1 - l₂ - l₃) (β := l₂) (γ := l₃) ?_
      (by rw [hl₂def]; exact div_nonneg hl₂ hDpos.le)
      (by rw [hl₃def]; exact div_nonneg hl₃ hDpos.le) (by ring) ?_
    · have : 1 - l₂ - l₃ = (cross A B - cross w B - cross A w) / cross A B := by
        rw [hl₂def, hl₃def]
        field_simp
      rw [this]; exact div_nonneg hl₁ hDpos.le
    · have hq' : q = vplus K a + w := by rw [hwdef]; abel
      have hv0 : vint K a b = vplus K a + A := by rw [hAdef]; abel
      have hv2 : vminus K b = vplus K a + B := by rw [hBdef]; abel
      rw [hq', hw, hv0, hv2]
      module
  have hsub1 : convexHull ℝ {vplus K a, vint K a b, vminus K b} ∩ ⋂ t ∈ Icc a b, suppHalf K t ⊆
      K ∩ halfMinus (t' + π) c := by
    rintro q ⟨hqT, hqX⟩
    refine ⟨?_, ?_⟩
    · rw [mem_iff_forall_dot_le_supp hK]
      intro t
      have h2π : (0 : ℝ) < 2 * π := by positivity
      set t₀ := toIcoMod h2π a t with ht₀
      have hmem := toIcoMod_mem_Ico h2π a t
      have hper_u : uvec t = uvec t₀ := by
        rw [ht₀, ← self_sub_toIcoDiv_zsmul]
        exact (Function.Periodic.sub_zsmul_eq (f := uvec) (c := 2 * π) uvec_add_two_pi _).symm
      have hper_s : supp K t = supp K t₀ := by
        rw [ht₀, ← self_sub_toIcoDiv_zsmul]
        exact (Function.Periodic.sub_zsmul_eq (f := supp K) (c := 2 * π) (supp_add_two_pi K) _).symm
      rw [hper_u, hper_s]
      rcases le_or_gt t₀ b with htb | htb
      · exact (mem_iInter₂.1 hqX) t₀ ⟨hmem.1, htb⟩
      · have hsub :
            convexHull ℝ {vplus K a, vint K a b, vminus K b} ⊆ halfMinus t₀ (supp K t₀) := by
          apply convexHull_min _ (convex_halfMinus _ _)
          intro r hr
          simp only [mem_insert_iff, mem_singleton_iff] at hr
          show dot r (uvec t₀) ≤ supp K t₀
          rcases hr with rfl | rfl | rfl
          · exact dot_le_supp hK.2.1 hpa.1 t₀
          · rcases le_or_gt (sin (t₀ - a)) 0 with hs | hs
            · have e : dot (vint K a b) (uvec t₀) =
                  dot (vplus K a) (uvec t₀) + α * sin (t₀ - a) := by
                rw [show vint K a b = vplus K a + α • vvec a by rw [← hα]; abel, dot_add_left,
                  dot_smul_left, dot_vvec_uvec']
              rw [e]; nlinarith [dot_le_supp hK.2.1 hpa.1 t₀]
            · have hlt : t₀ - a < π := by
                by_contra hge; push Not at hge
                have := Real.sin_nonneg_of_nonneg_of_le_pi (x := t₀ - a - π) (by linarith)
                  (by linarith [hmem.2])
                rw [Real.sin_sub_pi] at this
                linarith
              have hs' : 0 < sin (t₀ - b) :=
                sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
              have e : dot (vint K a b) (uvec t₀) =
                  dot (vminus K b) (uvec t₀) - β * sin (t₀ - b) := by
                rw [show vint K a b = vminus K b - β • vvec b by rw [← hβ]; abel, dot_sub_left,
                  dot_smul_left, dot_vvec_uvec']
              rw [e]; nlinarith [dot_le_supp hK.2.1 hpb.1 t₀]
          · exact dot_le_supp hK.2.1 hpb.1 t₀
        exact hsub hqT
    · have hsub : convexHull ℝ {vplus K a, vint K a b, vminus K b} ⊆ halfMinus (t' + π) c := by
        apply convexHull_min _ (convex_halfMinus _ _)
        intro r hr
        simp only [mem_insert_iff, mem_singleton_iff] at hr
        rcases hr with rfl | rfl | rfl
        · exact le_of_eq hp₁l
        · exact hp₀lt.le
        · exact le_of_eq hp₂l
      exact hsub hqT
  have hTX : convexHull ℝ {vplus K a, vint K a b, vminus K b} ∩ ⋂ t ∈ Icc a b, suppHalf K t =
      K ∩ halfMinus (t' + π) c := Subset.antisymm hsub1 hsub2
  have hK'T : K ∩ halfMinus (t' + π) c ⊆ convexHull ℝ {vplus K a, vint K a b, vminus K b} :=
    fun q hq => (hsub2 hq).1
  have hTc : IsCompact (convexHull ℝ {vplus K a, vint K a b, vminus K b}) :=
    (Set.toFinite _).isCompact_convexHull ℝ
  have hfr : volume (frontier (convexHull ℝ {vplus K a, vint K a b, vminus K b})) = 0 :=
    (convex_convexHull ℝ _).addHaar_frontier (μ := volume)
  have hvol : volume (convexCurveRegion K a b) =
      volume (convexHull ℝ {vplus K a, vint K a b, vminus K b} \ (K ∩ halfMinus (t' + π) c)) := by
    rw [← hTX, Set.sdiff_self_inter]
    apply le_antisymm (measure_mono (sdiff_subset_sdiff_left interior_subset))
    calc volume (convexHull ℝ {vplus K a, vint K a b, vminus K b} \ ⋂ t ∈ Icc a b, suppHalf K t)
        ≤ volume (convexCurveRegion K a b ∪
            frontier (convexHull ℝ {vplus K a, vint K a b, vminus K b})) := by
          apply measure_mono
          rintro q ⟨hqT, hqX⟩
          by_cases hqi : q ∈ interior (convexHull ℝ {vplus K a, vint K a b, vminus K b})
          · exact Or.inl ⟨hqi, hqX⟩
          · exact Or.inr ⟨subset_closure hqT, hqi⟩
      _ ≤ volume (convexCurveRegion K a b) +
            volume (frontier (convexHull ℝ {vplus K a, vint K a b, vminus K b})) :=
          measure_union_le _ _
      _ = volume (convexCurveRegion K a b) := by rw [hfr, add_zero]
  rw [area, hvol, measure_sdiff hK'T hK'cb.isClosed.measurableSet.nullMeasurableSet
    hK'cb.2.1.measure_lt_top.ne, ENNReal.toReal_sub_of_le (measure_mono hK'T)
    hTc.measure_lt_top.ne]
  change area (convexHull ℝ {vplus K a, vint K a b, vminus K b}) -
    area (K ∩ halfMinus (t' + π) c) = _
  rw [cvx_area_triangle, cvx_area_cut hK hab hb ht' hp₁l hp₂l hK'cb h1 h2 h3 h4,
    abs_of_pos hcpos]
  unfold segArea
  simp only [cross, Prod.fst_sub, Prod.snd_sub]
  ring


end MovingSofaOptimality
