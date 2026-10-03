module

public import MovingSofaOptimality.Balanced.PolygonCap

/-!
# Maximum polygon caps (§3.4): the geometry of polygon caps

The preliminaries of §3.4, before Definition 3.4.1; none of them is a numbered result of the paper.
This is the first of the four modules of §3.4, which form a chain of imports ending in
`MaximumPolygonCap`.

**Organization.**
* Preliminaries on convex bodies: corners (`mpc_corner`: when no defining normal angle lies
  strictly between `a` and `b`, the lines `l_K(a)`, `l_K(b)` meet at a point of `K`), and the
  semicontinuity of the area under Hausdorff convergence (`mpc_area_usc`, `mpc_area_lsc`).
* Angle sets and polygon caps: the angles `Θ^◇` (`mpcDiamond`), the vertices `A_K⁻(0)`,
  `C_K⁺(ω)`, `o_ω`, `O`, the walk `v_K⁺(s) - A_K⁻(0) = ∑_{t ≤ s} σ_K(t) v_t` along the upper
  boundary (`mpc_walk`), and the caps `𝓒_Θ(h)`, which are polygon caps as soon as they are
  nonempty with the support values of a cap at `ω`, `π/2`, `ω + π`, `3π/2`
  (`mpc_capH_isPolygonCap`).
* The niche as the region between two graphs: `F_ω \ 𝒩_Θ(K)` is the epigraph of the continuous
  piecewise linear function `mpcG = max mpcLow mpcTop` (`mpc_fan_diff_eq`), built from the walls
  `l(s, h_K(s) - 1)`. Left of `C_K⁺(ω)` and right of `A_K⁻(0)` it is a side of the fan
  (`mpc_left_of_C`, `mpc_right_of_A`), and `C_K⁺(ω)` lies strictly left of `A_K⁻(0)`
  (`mpc_C_lt_A`).
-/

@[expose] public section

open Real Set

namespace MovingSofaOptimality

/-! ## Preliminaries on convex bodies

### Corners -/

/-- **Corner lemma.** Let `K = ⋂ H₋(t_i, c_i)` be a convex body none of whose defining normal angles
lies strictly between `a` and `b` (modulo `2π`), where `0 < b - a < π` in the sense
`sin (b - a) > 0`. Then the supporting lines `l_K(a)` and `l_K(b)` meet at a point of `K`. -/
theorem mpc_corner {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {ι : Type*} {t c : ι → ℝ}
    (hKeq : K = ⋂ i, halfMinus (t i) (c i)) {a b : ℝ} (hab : 0 < sin (b - a))
    (hgap : ∀ i, ¬ (0 < sin (t i - a) ∧ sin (t i - b) < 0)) :
    ∃ q ∈ K, dot q (uvec a) = supp K a ∧ dot q (uvec b) = supp K b := by
  set q := vint K a b with hq
  have hqa : dot q (uvec a) = supp K a := vint_mem_line_left K a b
  have hqb : dot q (uvec b) = supp K b := vint_mem_line_right K hab.ne'
  refine ⟨q, ?_, hqa, hqb⟩
  obtain ⟨pa, hpa, hpae⟩ := exists_dot_eq_supp hK.2.1 hK.1 a
  obtain ⟨pb, hpb, hpbe⟩ := exists_dot_eq_supp hK.2.1 hK.1 b
  have hpab : dot pa (uvec b) ≤ supp K b := dot_le_supp hK.2.1 hpa b
  have hpba : dot pb (uvec a) ≤ supp K a := dot_le_supp hK.2.1 hpb a
  have hA : pa - q = dot (pa - q) (vvec a) • vvec a :=
    eq_smul_vvec_of_dot_uvec_eq_zero (by rw [dot_sub_left, hpae, hqa, sub_self])
  have hB : pb - q = dot (pb - q) (vvec b) • vvec b :=
    eq_smul_vvec_of_dot_uvec_eq_zero (by rw [dot_sub_left, hpbe, hqb, sub_self])
  set α := dot (pa - q) (vvec a)
  set β := dot (pb - q) (vvec b)
  -- `p_a` lies on `l_K(a)` on the side of `q` towards `-v_a`, and `p_b` on `l_K(b)` towards `v_b`
  have hα : α ≤ 0 := by
    have h1 : dot (pa - q) (uvec b) ≤ 0 := by rw [dot_sub_left, hqb]; linarith
    rw [hA, dot_smul_left, dot_vvec_uvec'] at h1
    nlinarith
  have hβ : 0 ≤ β := by
    have h1 : dot (pb - q) (uvec a) ≤ 0 := by rw [dot_sub_left, hqa]; linarith
    rw [hB, dot_smul_left, dot_vvec_uvec', ← neg_sub, sin_neg] at h1
    nlinarith
  -- a half-plane `H₋(t_i, c_i)` missing `q` but containing `p_a` and `p_b` has its normal angle in
  -- the gap between `a` and `b`
  by_contra hqK
  rw [hKeq] at hqK hpa hpb
  simp only [mem_iInter, halfMinus, mem_ofPred_eq, not_forall, not_le] at hqK hpa hpb
  obtain ⟨i, hi⟩ := hqK
  have h1 : 0 < dot (q - pa) (uvec (t i)) := by rw [dot_sub_left]; linarith [hpa i]
  have h2 : 0 < dot (q - pb) (uvec (t i)) := by rw [dot_sub_left]; linarith [hpb i]
  have hqa' : q - pa = (-α) • vvec a := by rw [neg_smul, ← hA, neg_sub]
  have hqb' : q - pb = (-β) • vvec b := by rw [neg_smul, ← hB, neg_sub]
  rw [hqa', dot_smul_left, dot_vvec_uvec'] at h1
  rw [hqb', dot_smul_left, dot_vvec_uvec'] at h2
  exact hgap i ⟨by nlinarith, by nlinarith⟩

/-- Properties of a corner point `q` of a convex body, the intersection of `l_K(a)` and `l_K(b)`:
it is the vertex `v_K⁺(a) = v_K⁻(b)`, it lies on `l_K(s)` for `s` between `a` and `b`, and it is the
whole edge `e_K(s)` for `s` strictly between `a` and `b`. -/
theorem mpc_corner_props {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {q : ℝ × ℝ} (hq : q ∈ K)
    {a b : ℝ} (hab : 0 < sin (b - a)) (hqa : dot q (uvec a) = supp K a)
    (hqb : dot q (uvec b) = supp K b) :
    vplus K a = q ∧ vminus K b = q ∧
      (∀ s, 0 ≤ sin (s - a) → 0 ≤ sin (b - s) → dot q (uvec s) = supp K s) ∧
      (∀ s, 0 < sin (s - a) → 0 < sin (b - s) → vplus K s = q ∧ vminus K s = q) := by
  have hle : ∀ p ∈ K, ∀ r, dot (p - q) (uvec r) ≤ supp K r - dot q (uvec r) := fun p hp r => by
    rw [dot_sub_left]; linarith [dot_le_supp hK.2.1 hp r]
  -- Step 1: the support values between `a` and `b` are attained at `q`, since `u_s` is a
  -- nonnegative combination of `u_a` and `u_b`.
  have hmid : ∀ s, 0 ≤ sin (s - a) → 0 ≤ sin (b - s) → dot q (uvec s) = supp K s := by
    intro s hs1 hs2
    refine le_antisymm (dot_le_supp hK.2.1 hq s) (supp_le_of_forall hK.1 fun p hp => ?_)
    have h1 := dot_le_supp hK.2.1 hp a
    have h2 := dot_le_supp hK.2.1 hp b
    have : sin (b - a) * dot p (uvec s) ≤ sin (b - a) * dot q (uvec s) := by
      rw [dot_uvec_comb p a b s, dot_uvec_comb q a b s, hqa, hqb]
      nlinarith [mul_le_mul_of_nonneg_left h1 hs2, mul_le_mul_of_nonneg_left h2 hs1]
    exact le_of_mul_le_mul_left this hab
  -- Step 2: the vertex `v` of an edge `e_K(r)` is `q` when `q` is extremal on the edge in the
  -- direction of `v_r` (resp. `-v_r`).
  have hvertex : ∀ r, dot q (uvec r) = supp K r →
      (∀ p ∈ edge K r, dot p (vvec r) ≤ dot q (vvec r)) → vplus K r = q := by
    intro r hqr hmax
    have hsup : sSup ((fun p => dot p (vvec r)) '' edge K r) = dot q (vvec r) :=
      IsGreatest.csSup_eq ⟨mem_image_of_mem _ ⟨hq, hqr⟩, forall_mem_image.2 hmax⟩
    rw [vplus, hsup, ← hqr]
    exact (eq_dot_uvec_smul_add q r).symm
  have hvertex' : ∀ r, dot q (uvec r) = supp K r →
      (∀ p ∈ edge K r, dot q (vvec r) ≤ dot p (vvec r)) → vminus K r = q := by
    intro r hqr hmin
    have hinf : sInf ((fun p => dot p (vvec r)) '' edge K r) = dot q (vvec r) :=
      IsLeast.csInf_eq ⟨mem_image_of_mem _ ⟨hq, hqr⟩, forall_mem_image.2 hmin⟩
    rw [vminus, hinf, ← hqr]
    exact (eq_dot_uvec_smul_add q r).symm
  -- a point `p` of `e_K(r)` differs from `q` by a multiple of `v_r`
  have hon : ∀ r, dot q (uvec r) = supp K r → ∀ p ∈ edge K r,
      p - q = dot (p - q) (vvec r) • vvec r := fun r hqr p hp =>
    eq_smul_vvec_of_dot_uvec_eq_zero (by rw [dot_sub_left, hp.2, hqr, sub_self])
  refine ⟨hvertex a hqa fun p hp => ?_, hvertex' b hqb fun p hp => ?_, hmid, ?_⟩
  · have h1 := hle p hp.1 b
    rw [hqb, sub_self, hon a hqa p hp, dot_smul_left, dot_vvec_uvec'] at h1
    have : dot (p - q) (vvec a) ≤ 0 := by nlinarith
    rw [dot_sub_left] at this
    linarith
  · have h1 := hle p hp.1 a
    rw [hqa, sub_self, hon b hqb p hp, dot_smul_left, dot_vvec_uvec',
      show sin (a - b) = -sin (b - a) by rw [← sin_neg, neg_sub]] at h1
    have : 0 ≤ dot (p - q) (vvec b) := by nlinarith
    rw [dot_sub_left] at this
    linarith
  · -- Step 3: strictly between `a` and `b` the edge is the single point `q`.
    intro s hs1 hs2
    have hqs := hmid s hs1.le hs2.le
    have hedge : ∀ p ∈ edge K s, p = q := by
      intro p hp
      have e1 := dot_uvec_comb (p - q) a b s
      have h1 := hle p hp.1 a
      have h2 := hle p hp.1 b
      rw [hqa, sub_self] at h1
      rw [hqb, sub_self] at h2
      rw [dot_sub_left, hp.2, hqs, sub_self, mul_zero] at e1
      have h1' : dot (p - q) (uvec a) = 0 := by
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hs1.le h2]
      have h2' : dot (p - q) (uvec b) = 0 := by
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hs2.le h1]
      exact sub_eq_zero.1 (eq_of_dot_uvec_eq hab.ne' (by simp [h1']) (by simp [h2']))
    exact ⟨hvertex s hqs fun p hp => by rw [hedge p hp],
      hvertex' s hqs fun p hp => by rw [hedge p hp]⟩

/-! ### Hausdorff convergence and semicontinuity of the area -/

section Convergence

open Filter Topology MeasureTheory

/-- Hausdorff convergence of convex bodies gives uniform convergence of the support functions. -/
lemma mpc_supp_uniform {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {Ks : ℕ → Set (ℝ × ℝ)}
    (hKs : ∀ i, IsConvexBody (Ks i)) (hlim : HausdorffTendsto Ks K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ t, |supp (Ks i) t - supp K t| < ε := by
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with i hi t
  exact (abs_supp_sub_le_hausdorffDist (hKs i) hK t).trans_lt hi

/-- A point lying eventually in the convex bodies `K_i → K` lies in `K`. -/
lemma mpc_mem_of_eventually_mem {K : Set (ℝ × ℝ)} (hK : IsConvexBody K)
    {Ks : ℕ → Set (ℝ × ℝ)} (hKs : ∀ i, IsConvexBody (Ks i)) (hlim : HausdorffTendsto Ks K)
    {p : ℝ × ℝ} (hp : ∀ᶠ i in atTop, p ∈ Ks i) : p ∈ K := by
  rw [mem_iff_forall_dot_le_supp hK]
  intro t
  apply ge_of_tendsto (tendsto_supp hKs hK hlim t)
  filter_upwards [hp] with i hi
  exact dot_le_supp (hKs i).2.1 hi t

/-! #### Upper semicontinuity of the area -/

/-- The outer parallel set `{p : p · u_s ≤ h(s) + δ for all s ∈ T}`. -/
def mpcOuter (T : Set ℝ) (h : ℝ → ℝ) (δ : ℝ) : Set (ℝ × ℝ) :=
  {p | ∀ s ∈ T, dot p (uvec s) ≤ h s + δ}

/-- The outer parallel sets are closed. -/
lemma mpc_isClosed_outer (T : Set ℝ) (h : ℝ → ℝ) (δ : ℝ) : IsClosed (mpcOuter T h δ) := by
  have : mpcOuter T h δ = ⋂ s ∈ T, {p : ℝ × ℝ | dot p (uvec s) ≤ h s + δ} := by
    ext p; simp [mpcOuter]
  rw [this]
  exact isClosed_biInter fun s _ => isClosed_le (continuous_dot _) continuous_const

/-- The outer parallel sets increase with `δ`. -/
lemma mpc_outer_mono (T : Set ℝ) (h : ℝ → ℝ) {δ δ' : ℝ} (hδ : δ ≤ δ') :
    mpcOuter T h δ ⊆ mpcOuter T h δ' :=
  fun p hp s hs => (hp s hs).trans (by linarith)

/-- If the outer parallel sets are bounded for some `δ₀ > 0`, then their areas tend to the area of
`mpcOuter T h 0` from above. -/
lemma mpc_area_outer_eventually_le {T : Set ℝ} {h : ℝ → ℝ} {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hb : Bornology.IsBounded (mpcOuter T h δ₀)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, δ ≤ δ₀ ∧ area (mpcOuter T h δ) ≤ area (mpcOuter T h 0) + ε := by
  set s : ℕ → Set (ℝ × ℝ) := fun n => mpcOuter T h (δ₀ / (n + 1)) with hs
  have hanti : Antitone s := by
    intro m n hmn
    apply mpc_outer_mono
    apply div_le_div_of_nonneg_left hδ₀.le (by positivity)
    exact_mod_cast Nat.add_le_add_right hmn 1
  have hinter : (⋂ n, s n) = mpcOuter T h 0 := by
    ext p
    simp only [hs, mem_iInter, mpcOuter, mem_ofPred_eq, add_zero]
    constructor
    · intro hp t ht
      apply le_of_forall_pos_le_add
      intro e he
      obtain ⟨n, hn⟩ := exists_nat_gt (δ₀ / e)
      have h1 := hp n t ht
      have h2 : δ₀ / (n + 1) ≤ e := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_lt_iff₀ he] at hn
        nlinarith
      linarith
    · intro hp n t ht
      have : 0 ≤ δ₀ / (n + 1) := by positivity
      linarith [hp t ht]
  have hfin : ∀ n, volume (s n) ≠ ⊤ := by
    intro n
    apply ne_of_lt
    apply (hb.subset (mpc_outer_mono T h _)).measure_lt_top
    apply div_le_self hδ₀.le
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have ht := tendsto_measure_iInter_atTop (μ := volume)
    (fun n => (mpc_isClosed_outer T h _).measurableSet.nullMeasurableSet) hanti ⟨0, hfin 0⟩
  rw [hinter] at ht
  have hfin0 : volume (mpcOuter T h 0) ≠ ⊤ :=
    ne_of_lt ((hb.subset (mpc_outer_mono T h hδ₀.le)).measure_lt_top)
  have ht' : Tendsto (fun n => (volume (s n)).toReal) atTop (𝓝 (area (mpcOuter T h 0))) :=
    (ENNReal.tendsto_toReal hfin0).comp ht
  obtain ⟨n, hn⟩ := (ht'.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))).exists
  refine ⟨δ₀ / (n + 1), by positivity, div_le_self hδ₀.le ?_, hn.le⟩
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- The outer parallel sets of a convex body are bounded. -/
lemma mpc_isBounded_outer {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (δ : ℝ) :
    Bornology.IsBounded (mpcOuter univ (supp K) δ) := by
  obtain ⟨M, hM⟩ := exists_abs_supp_le hK.2.1 hK.1
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨M + |δ|, fun p hp => ?_⟩
  have h0 := hp 0 (mem_univ _)
  have hpi := hp π (mem_univ _)
  have h2 := hp (π / 2) (mem_univ _)
  have h3 := hp (-(π / 2)) (mem_univ _)
  simp only [dot, uvec, cos_zero, sin_zero, cos_pi, sin_pi, cos_pi_div_two, sin_pi_div_two,
    cos_neg, sin_neg] at h0 hpi h2 h3
  have b0 := abs_le.1 (hM 0)
  have bpi := abs_le.1 (hM π)
  have b2 := abs_le.1 (hM (π / 2))
  have b3 := abs_le.1 (hM (-(π / 2)))
  have hd := le_abs_self δ
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  apply max_le
  · rw [Real.norm_eq_abs, abs_le]; constructor <;> nlinarith
  · rw [Real.norm_eq_abs, abs_le]; constructor <;> nlinarith

/-- A convex body is its own outer parallel set for `δ = 0`. -/
lemma mpc_outer_zero {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) : mpcOuter univ (supp K) 0 = K := by
  ext p
  rw [mem_iff_forall_dot_le_supp hK]
  simp [mpcOuter]

/-- Eventually, the bodies `K_i → K` lie in the outer parallel set `K^δ`. -/
lemma mpc_eventually_subset_outer {K : Set (ℝ × ℝ)} (hK : IsConvexBody K)
    {Ks : ℕ → Set (ℝ × ℝ)} (hKs : ∀ i, IsConvexBody (Ks i)) (hlim : HausdorffTendsto Ks K)
    {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ i in atTop, Ks i ⊆ mpcOuter univ (supp K) δ := by
  filter_upwards [mpc_supp_uniform hK hKs hlim hδ] with i hi
  intro p hp s _
  have h1 := dot_le_supp (hKs i).2.1 hp s
  have h2 := abs_lt.1 (hi s)
  linarith

/-- **Upper semicontinuity of the area** under Hausdorff convergence of convex bodies. -/
lemma mpc_area_usc {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {Ks : ℕ → Set (ℝ × ℝ)}
    (hKs : ∀ i, IsConvexBody (Ks i)) (hlim : HausdorffTendsto Ks K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, area (Ks i) ≤ area K + ε := by
  obtain ⟨δ, hδ, -, hle⟩ := mpc_area_outer_eventually_le one_pos (mpc_isBounded_outer hK 1) hε
  rw [mpc_outer_zero hK] at hle
  filter_upwards [mpc_eventually_subset_outer hK hKs hlim hδ] with i hsub
  have hfin : volume (mpcOuter univ (supp K) δ) ≠ ⊤ :=
    ne_of_lt (mpc_isBounded_outer hK δ).measure_lt_top
  exact (ENNReal.toReal_mono hfin (measure_mono hsub)).trans hle

/-! #### Lower semicontinuity of the area along pointwise eventual membership -/

/-- **Lower semicontinuity of the area.** If every point of `N` lies eventually in `N_i`, and the
`N_i` lie eventually in a fixed bounded set, then `|N| - ε ≤ |N_i|` eventually. -/
lemma mpc_area_lsc {N : Set (ℝ × ℝ)} {Ns : ℕ → Set (ℝ × ℝ)}
    (hN : ∀ p ∈ N, ∀ᶠ i in atTop, p ∈ Ns i) {B : Set (ℝ × ℝ)} (hB : Bornology.IsBounded B)
    (hNs : ∀ᶠ i in atTop, Ns i ⊆ B) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, area N - ε ≤ area (Ns i) := by
  obtain ⟨n₀, hn₀⟩ := hNs.exists_forall_of_atTop
  set M : ℕ → Set (ℝ × ℝ) := fun n => ⋂ i ∈ Ici (max n n₀), Ns i with hM
  have hmono : Monotone M := by
    intro m n hmn
    apply biInter_subset_biInter_left
    intro i hi
    exact le_trans (max_le_max hmn le_rfl) hi
  have hMB : ∀ n, M n ⊆ B := by
    intro n p hp
    have : p ∈ Ns (max n n₀) := mem_iInter₂.1 hp _ (mem_Ici.2 le_rfl)
    exact hn₀ _ (le_max_right _ _) this
  have hNU : N ⊆ ⋃ n, M n := by
    intro p hp
    obtain ⟨m, hm⟩ := (hN p hp).exists_forall_of_atTop
    exact mem_iUnion.2 ⟨m, mem_iInter₂.2 fun i hi => hm i (le_trans (le_max_left _ _) hi)⟩
  have hUB : (⋃ n, M n) ⊆ B := iUnion_subset hMB
  have hfinU : volume (⋃ n, M n) ≠ ⊤ := ne_of_lt ((hB.subset hUB).measure_lt_top)
  have ht := tendsto_measure_iUnion_atTop (μ := volume) hmono
  have ht' : Tendsto (fun n => (volume (M n)).toReal) atTop (𝓝 (volume (⋃ n, M n)).toReal) :=
    (ENNReal.tendsto_toReal hfinU).comp ht
  have hNle : area N ≤ (volume (⋃ n, M n)).toReal :=
    ENNReal.toReal_mono hfinU (measure_mono hNU)
  obtain ⟨n, hn⟩ := (ht'.eventually (lt_mem_nhds (sub_lt_self _ hε))).exists
  filter_upwards [eventually_ge_atTop (max n n₀)] with i hi
  have hsub : M n ⊆ Ns i := biInter_subset_of_mem hi
  have hfin : volume (Ns i) ≠ ⊤ :=
    (hB.subset (hn₀ i ((le_max_right _ _).trans hi))).measure_lt_top.ne
  have h1 : area (M n) ≤ area (Ns i) := ENNReal.toReal_mono hfin (measure_mono hsub)
  change _ < area (M n) at hn
  linarith

end Convergence

/-! ## Angle sets and polygon caps -/

/-! ### The angles `Θ^◇` -/

/-- No angle `c` lies strictly between `r` and `s` modulo `2π`, in the sine form used by
`mpc_corner`. -/
lemma mpc_not_gap {r s c : ℝ} (hrs : r < s)
    (hc : (s ≤ c ∧ c ≤ r + 2 * π) ∨ (s - 2 * π ≤ c ∧ c ≤ r)) :
    ¬ (0 < sin (c - r) ∧ sin (c - s) < 0) := by
  rintro ⟨h1, h2⟩
  rcases hc with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
  · by_cases hcs : c ≤ s + π
    · have : 0 ≤ sin (c - s) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      linarith
    · have : sin (c - r) ≤ 0 := by
        rw [← sin_sub_two_pi]
        exact sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
      linarith
  · by_cases hcr : r - π ≤ c
    · have : sin (c - r) ≤ 0 := sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
      linarith
    · have : 0 ≤ sin (c - s) := by
        rw [← sin_add_two_pi]
        exact sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      linarith

/-- `0 < ω`. -/
lemma mpc_omega_pos (Θ : AngleSet) : 0 < Θ.ω := Θ.hω.1

/-- `ω ≤ π/2`. -/
lemma mpc_omega_le (Θ : AngleSet) : Θ.ω ≤ π / 2 := Θ.hω.2

/-- The angles of `Θ` lie in `(0, ω)`. -/
lemma mpc_angles_bounds {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.angles) : 0 < t ∧ t < Θ.ω :=
  Θ.subset t ht

/-- `Θ^◇` as a finset. -/
noncomputable def mpcDiamond (Θ : AngleSet) : Finset ℝ :=
  Θ.angles ∪ Θ.angles.image (fun t => t + π / 2) ∪ {Θ.ω, π / 2}

/-- Membership in the finset `mpcDiamond Θ` is membership in `Θ^◇`. -/
lemma mpc_mem_mpcDiamond {Θ : AngleSet} {t : ℝ} : t ∈ mpcDiamond Θ ↔ t ∈ Θ.diamond := by
  simp only [mpcDiamond, AngleSet.diamond, Finset.mem_union, Finset.mem_image,
    Finset.mem_insert, Finset.mem_singleton, mem_union, Finset.mem_coe, mem_image,
    mem_insert_iff, mem_singleton_iff]

/-- The four kinds of angles of `Θ^◇`. -/
lemma mpc_diamond_cases {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.diamond) :
    t ∈ Θ.angles ∨ (∃ s ∈ Θ.angles, t = s + π / 2) ∨ t = Θ.ω ∨ t = π / 2 := by
  rcases ht with (h | ⟨s, hs, rfl⟩) | h | h
  exacts [Or.inl h, Or.inr (Or.inl ⟨s, hs, rfl⟩), Or.inr (Or.inr (Or.inl h)),
    Or.inr (Or.inr (Or.inr h))]

/-- The angles of `Θ^◇` lie in `(0, ω + π/2)`. -/
lemma mpc_diamond_bounds {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.diamond) :
    0 < t ∧ t < Θ.ω + π / 2 := by
  obtain ⟨hω0, -⟩ := Θ.hω
  have hpi := pi_pos
  rcases mpc_diamond_cases ht with h | ⟨s, hs, rfl⟩ | rfl | rfl
  · have := mpc_angles_bounds h; constructor <;> linarith
  · have := mpc_angles_bounds hs; constructor <;> linarith
  all_goals constructor <;> linarith

/-- The angles of `Θ^◇` lie below `π`. -/
lemma mpc_diamond_lt_pi {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.diamond) : t < π := by
  linarith [(mpc_diamond_bounds ht).2, mpc_omega_le Θ]

/-- `sin t > 0` for `t ∈ Θ^◇`. -/
lemma mpc_sin_pos_of_diamond {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.diamond) : 0 < sin t :=
  sin_pos_of_pos_of_lt_pi (mpc_diamond_bounds ht).1 (mpc_diamond_lt_pi ht)

/-- Two distinct angles of `Θ^◇` are not parallel. -/
lemma mpc_diamond_sin_sub_ne {Θ : AngleSet} {s s' : ℝ} (hs : s ∈ Θ.diamond)
    (hs' : s' ∈ Θ.diamond) (h : s ≠ s') : sin (s' - s) ≠ 0 := by
  have h1 := mpc_diamond_bounds hs
  have h2 := mpc_diamond_bounds hs'
  have h3 := mpc_diamond_lt_pi hs
  have h4 := mpc_diamond_lt_pi hs'
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  · exact (sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)).ne

/-- The normal angles of a polygon cap: `Θ^◇`, `ω + π` and `3π/2`. -/
lemma mpc_capAngles_cases {Θ : AngleSet} {c : ℝ} (hc : c ∈ Θ.capAngles) :
    c ∈ Θ.diamond ∨ c = Θ.ω + π ∨ c = 3 * π / 2 := hc

/-- `Θ^◇` is nonempty (it contains `ω`). -/
lemma mpc_mpcDiamond_nonempty (Θ : AngleSet) : (mpcDiamond Θ).Nonempty :=
  ⟨Θ.ω, mpc_mem_mpcDiamond.2 (Or.inr (Or.inl rfl))⟩

/-- The largest angle of `Θ^◇` is larger than `π/2`. -/
lemma mpc_max_diamond_gt (Θ : AngleSet) :
    π / 2 < (mpcDiamond Θ).max' (mpc_mpcDiamond_nonempty Θ) := by
  obtain ⟨t, ht⟩ := Θ.nonempty
  have hmem : t + π / 2 ∈ mpcDiamond Θ := mpc_mem_mpcDiamond.2 (Or.inl (Or.inr ⟨t, ht, rfl⟩))
  linarith [(mpcDiamond Θ).le_max' _ hmem, (mpc_angles_bounds ht).1]

/-- The smallest angle of `Θ^◇` is smaller than `ω`. -/
lemma mpc_min_diamond_lt (Θ : AngleSet) :
    (mpcDiamond Θ).min' (mpc_mpcDiamond_nonempty Θ) < Θ.ω := by
  obtain ⟨t, ht⟩ := Θ.nonempty
  have hmem : t ∈ mpcDiamond Θ := mpc_mem_mpcDiamond.2 (Or.inl (Or.inl ht))
  linarith [(mpcDiamond Θ).min'_le _ hmem, (mpc_angles_bounds ht).2]

/-! ### Caps and polygon caps -/

/-- The bottom normal angles: `h_K(t) = 1` and `h_K(t + π) = 0` for a cap `K` and `t ∈ {ω, π/2}`. -/
lemma mpc_supp_bot {K : Set (ℝ × ℝ)} {ω t : ℝ} (hK : IsCap K ω) (ht : t ∈ ({ω, π / 2} : Set ℝ)) :
    supp K t = 1 ∧ supp K (t + π) = 0 := by
  rcases ht with rfl | rfl
  · exact ⟨hK.2.2.1, hK.2.2.2.2.1⟩
  · exact ⟨hK.2.2.2.1, by rw [← nef_three_pi_div_two]; exact hK.2.2.2.2.2.1⟩

/-- Membership in a polygon cap: the supporting half-planes with normal angles in `Θ^◇`, and the
fan `F_ω`. -/
lemma mpc_polycap_mem_iff {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K)
    (p : ℝ × ℝ) :
    p ∈ K ↔ (∀ t ∈ Θ.diamond, dot p (uvec t) ≤ supp K t) ∧ p ∈ fan Θ.ω := by
  rw [Set.ext_iff.1 (nef_eq_setOf_supp hK.1.2.1 hK.2) p, mem_ofPred_eq, AngleSet.capAngles]
  simp only [mem_union, mem_insert_iff, mem_singleton_iff, or_imp, forall_and, forall_eq,
    hK.1.2.2.2.2.1, hK.1.2.2.2.2.2.1, dot_uvec_add_pi, dot_uvec_three_pi_div_two, neg_nonpos,
    fan, halfPlus, mem_inter_iff, mem_ofPred_eq, dot_uvec_pi_div_two]

/-! ### Corners of polygon caps

A polygon cap has no normal angle in the gap between two consecutive angles of
`Θ^◇ ∪ {ω + π, 3π/2}`, so its supporting lines at the two ends of the gap meet at a vertex of the
cap (`mpc_corner`). This gives the vertices `A_K⁻(0)`, `C_K⁺(ω)`, `o_ω` (for `ω < π/2`) and the
origin, the bottom side lengths, and the walk along the upper boundary (`mpc_walk`). -/

/-- The corner of a polygon cap at a gap `(r, s)` of its normal angles. -/
lemma mpc_polycap_corner {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) {r s : ℝ}
    (hrs : r < s) (hsr : s - r < π)
    (hc : ∀ c ∈ Θ.capAngles, (s ≤ c ∧ c ≤ r + 2 * π) ∨ (s - 2 * π ≤ c ∧ c ≤ r)) :
    ∃ q ∈ K, dot q (uvec r) = supp K r ∧ dot q (uvec s) = supp K s ∧ vplus K r = q ∧
      vminus K s = q ∧ (∀ x, r ≤ x → x ≤ s → dot q (uvec x) = supp K x) ∧
      (∀ x, r < x → x < s → vplus K x = q ∧ vminus K x = q) := by
  have hsin : 0 < sin (s - r) := sin_pos_of_pos_of_lt_pi (by linarith) hsr
  obtain ⟨ι, t, c, ht, hKeq⟩ := hK.2
  obtain ⟨q, hq, hqr, hqs⟩ := mpc_corner hK.1.2.1 hKeq hsin
    (fun i => mpc_not_gap hrs (hc _ (ht i)))
  obtain ⟨h1, h2, h3, h4⟩ := mpc_corner_props hK.1.2.1 hq hsin hqr hqs
  refine ⟨q, hq, hqr, hqs, h1, h2, fun x hx1 hx2 => h3 x ?_ ?_, fun x hx1 hx2 => h4 x ?_ ?_⟩
  · exact sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  · exact sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  · exact sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  · exact sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

section Corners

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

/-- The corner `A_K⁻(0) = (h_K(0), 0)` of a polygon cap, between the bottom side `l(3π/2, 0)` and
the first upper side. -/
lemma mpc_aMinus_eq (hK : IsPolygonCap Θ K) :
    aMinus K 0 = (supp K 0, 0) ∧ (supp K 0, (0 : ℝ)) ∈ K ∧
      vminus K ((mpcDiamond Θ).min' (mpc_mpcDiamond_nonempty Θ)) = (supp K 0, 0) := by
  set m := (mpcDiamond Θ).min' (mpc_mpcDiamond_nonempty Θ)
  have hm0 : 0 < m := (mpc_diamond_bounds (mpc_mem_mpcDiamond.1 (Finset.min'_mem _ _))).1
  have hmω := mpc_min_diamond_lt Θ
  have hω := mpc_omega_le Θ
  obtain ⟨q, hq, hq1, -, -, hq4, hq5, hq6⟩ := mpc_polycap_corner hK (r := -(π / 2)) (s := m)
    (by linarith [pi_pos]) (by linarith) (by
      intro c hc
      left
      rcases mpc_capAngles_cases hc with hc | rfl | rfl
      · exact ⟨(mpcDiamond Θ).min'_le _ (mpc_mem_mpcDiamond.2 hc),
          by linarith [mpc_diamond_lt_pi hc, pi_pos]⟩
      all_goals exact ⟨by linarith [pi_pos], by linarith⟩)
  have hqe : q = (supp K 0, 0) := by
    have h0 := hq5 0 (by linarith [pi_pos]) hm0.le
    rw [← supp_add_two_pi, show -(π / 2) + 2 * π = 3 * π / 2 by ring,
      hK.1.2.2.2.2.2.1] at hq1
    rw [dot_uvec_zero] at h0
    ext
    · exact h0
    · simpa [dot, uvec] using hq1
  subst hqe
  exact ⟨(hq6 0 (by linarith [pi_pos]) hm0).2, hq, hq4⟩

/-- The corner `C_K⁺(ω) = h_K(ω + π/2) v_ω` of a polygon cap, between the last upper side and the
bottom side `l(ω + π, 0)`. -/
lemma mpc_cPlus_eq (hK : IsPolygonCap Θ K) :
    cPlus K Θ.ω = supp K (Θ.ω + π / 2) • vvec Θ.ω ∧ cPlus K Θ.ω ∈ K ∧
      vplus K ((mpcDiamond Θ).max' (mpc_mpcDiamond_nonempty Θ)) = cPlus K Θ.ω ∧
      vminus K (Θ.ω + π) = cPlus K Θ.ω ∧ supp K π = -(cPlus K Θ.ω).1 := by
  set M := (mpcDiamond Θ).max' (mpc_mpcDiamond_nonempty Θ)
  have hMd : M ∈ Θ.diamond := mpc_mem_mpcDiamond.1 (Finset.max'_mem _ _)
  have hM1 := mpc_diamond_bounds hMd
  have hM2 := mpc_max_diamond_gt Θ
  have hω := mpc_omega_le Θ
  have hω0 := mpc_omega_pos Θ
  obtain ⟨q, hq, hq1, hq2, hq3, hq4, hq5, hq6⟩ := mpc_polycap_corner hK (r := M)
    (s := Θ.ω + π) (by linarith) (by linarith) (by
      intro c hc
      rcases mpc_capAngles_cases hc with hc | rfl | rfl
      · right
        exact ⟨by linarith [(mpc_diamond_bounds hc).1, pi_pos],
          (mpcDiamond Θ).le_max' _ (mpc_mem_mpcDiamond.2 hc)⟩
      · left; exact ⟨le_rfl, by linarith [pi_pos]⟩
      · left; exact ⟨by linarith, by linarith [pi_pos]⟩)
  have hcp : cPlus K Θ.ω = q := (hq6 (Θ.ω + π / 2) (by linarith) (by linarith [pi_pos])).1
  have hqω : dot q (uvec Θ.ω) = 0 := by
    rw [hK.1.2.2.2.2.1, dot_uvec_add_pi] at hq2
    linarith
  have hqv : dot q (vvec Θ.ω) = supp K (Θ.ω + π / 2) := by
    rw [← uvec_add_pi_div_two]
    exact hq5 _ (by linarith) (by linarith [pi_pos])
  have hpi : supp K π = -q.1 := by
    rw [← hq5 π (by linarith) (by linarith), dot_uvec_pi]
  rw [hcp]
  exact ⟨by simpa [hqω, hqv] using eq_dot_uvec_smul_add q Θ.ω, hq, hq3, hq4, hpi⟩

/-- `o_ω · v_ω = tan (π/4 - ω/2)`. -/
lemma mpc_oPt_dot_vvec {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) :
    dot (oPt ω) (vvec ω) = tan (π / 4 - ω / 2) := by
  set a := π / 4 - ω / 2 with ha
  have hω' : ω = π / 2 - 2 * a := by rw [ha]; ring
  have hca : 0 < cos a :=
    cos_pos_of_mem_Ioo ⟨by linarith [hω.1, hω.2, pi_pos], by linarith [hω.1, hω.2, pi_pos]⟩
  simp only [oPt, dot, vvec]
  rw [← ha, hω', cos_pi_div_two_sub, sin_pi_div_two_sub, sin_two_mul, cos_two_mul,
    tan_eq_sin_div_cos]
  field_simp
  nlinarith [sin_sq_add_cos_sq a]

/-- The vertex `o_ω` lies at height `1`. -/
lemma mpc_oPt_snd (ω : ℝ) : (oPt ω).2 = 1 := rfl

/-- For `ω < π/2`, the origin is the corner between the two bottom sides. -/
lemma mpc_origin_corner (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) :
    (0 : ℝ × ℝ) ∈ K ∧ vplus K (Θ.ω + π) = 0 ∧ vminus K (3 * π / 2) = 0 := by
  have hω0 := mpc_omega_pos Θ
  obtain ⟨q, hq, hq1, hq2, hq3, hq4, -⟩ := mpc_polycap_corner hK (r := Θ.ω + π)
    (s := 3 * π / 2) (by linarith) (by linarith) (by
      intro c hc
      rcases mpc_capAngles_cases hc with hc | rfl | rfl
      · right; exact ⟨by linarith [(mpc_diamond_bounds hc).1, pi_pos],
          by linarith [mpc_diamond_lt_pi hc]⟩
      · right; exact ⟨by linarith [pi_pos], le_rfl⟩
      · left; exact ⟨le_rfl, by linarith [pi_pos]⟩)
  have : q = 0 := by
    apply eq_of_dot_uvec_eq (a := Θ.ω + π) (b := 3 * π / 2)
    · exact (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])).ne'
    · rw [hq1, hK.1.2.2.2.2.1, dot_zero_left]
    · rw [hq2, hK.1.2.2.2.2.2.1, dot_zero_left]
  subst this
  exact ⟨hq, hq3, hq4⟩

/-- `v_K⁺(3π/2) = (h_K(0), 0)`. -/
lemma mpc_vplus_three_pi_div_two (hK : IsPolygonCap Θ K) :
    vplus K (3 * π / 2) = (supp K 0, 0) := by
  obtain ⟨q, -, hq1, hq2, hq3, -⟩ := mpc_polycap_corner hK (r := 3 * π / 2) (s := 2 * π)
    (by linarith [pi_pos]) (by linarith [pi_pos]) (by
      intro c hc
      right
      rcases mpc_capAngles_cases hc with hc | rfl | rfl
      · exact ⟨by linarith [(mpc_diamond_bounds hc).1],
          by linarith [mpc_diamond_lt_pi hc, pi_pos]⟩
      · exact ⟨by linarith [mpc_omega_pos Θ, pi_pos], by linarith [mpc_omega_le Θ]⟩
      · exact ⟨by linarith [pi_pos], le_rfl⟩)
  rw [hK.1.2.2.2.2.2.1, dot_uvec_three_pi_div_two] at hq1
  rw [← zero_add (2 * π), supp_add_two_pi, uvec_add_two_pi, dot_uvec_zero] at hq2
  rw [hq3]
  ext
  · exact hq2
  · simp only; linarith

/-- The bottom side lengths of a polygon cap with `ω < π/2`. -/
lemma mpc_sigma_bottom_lt (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) :
    sigmaAt K (3 * π / 2) = supp K 0 ∧ 0 < supp K 0 ∧
      sigmaAt K (Θ.ω + π) = supp K (Θ.ω + π / 2) ∧ 0 < supp K (Θ.ω + π / 2) := by
  have hω0 := mpc_omega_pos Θ
  have ho := hK.1.oPt_mem hω
  have hta : 0 < tan (π / 4 - Θ.ω / 2) :=
    tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  have h0 : 0 < supp K 0 := by
    have := dot_le_supp hK.1.2.1.2.1 ho 0
    rw [dot_uvec_zero] at this
    exact hta.trans_le this
  have h1 : 0 < supp K (Θ.ω + π / 2) := by
    have := dot_le_supp hK.1.2.1.2.1 ho (Θ.ω + π / 2)
    rw [uvec_add_pi_div_two, mpc_oPt_dot_vvec Θ.hω] at this
    exact hta.trans_le this
  obtain ⟨-, hO1, hO2⟩ := mpc_origin_corner hK hω
  obtain ⟨hC1, -, -, hC4, -⟩ := mpc_cPlus_eq hK
  refine ⟨?_, h0, ?_, h1⟩
  · rw [sigmaAt_eq_dot_sub hK.1.2.1, mpc_vplus_three_pi_div_two hK, hO2,
      vvec_three_pi_div_two]
    simp [dot]
  · rw [sigmaAt_eq_dot_sub hK.1.2.1, hO1, hC4, hC1, vvec_add_pi, dot_zero_left, dot_smul_left,
      dot_neg_right, dot_vvec_self]
    ring

/-- The bottom side length of a polygon cap with `ω = π/2`. -/
lemma mpc_sigma_bottom_eq (hK : IsPolygonCap Θ K) (hω : Θ.ω = π / 2) :
    sigmaAt K (3 * π / 2) = supp K 0 + supp K π := by
  obtain ⟨hC1, -, -, hC4, -⟩ := mpc_cPlus_eq hK
  rw [hω, show π / 2 + π / 2 = π by ring] at hC1
  rw [hω, show π / 2 + π = 3 * π / 2 by ring] at hC4
  rw [sigmaAt_eq_dot_sub hK.1.2.1, mpc_vplus_three_pi_div_two hK, hC4, hC1,
    vvec_three_pi_div_two, vvec_pi_div_two]
  simp [dot]

/-- Consecutive angles `r < s` of `Θ^◇` share a vertex: `v_K⁻(s) = v_K⁺(r)`. -/
lemma mpc_vminus_eq_vplus (hK : IsPolygonCap Θ K) {r s : ℝ} (hr : r ∈ mpcDiamond Θ)
    (hs : s ∈ mpcDiamond Θ) (hrs : r < s) (hgap : ∀ c ∈ mpcDiamond Θ, c < s → c ≤ r) :
    vminus K s = vplus K r := by
  have hsd := mpc_diamond_bounds (mpc_mem_mpcDiamond.1 hs)
  have hrd := mpc_diamond_bounds (mpc_mem_mpcDiamond.1 hr)
  have hspi := mpc_diamond_lt_pi (mpc_mem_mpcDiamond.1 hs)
  obtain ⟨q, -, -, -, hq3, hq4, -, -⟩ := mpc_polycap_corner hK hrs (by linarith) (by
    intro c hc
    rcases mpc_capAngles_cases hc with hc | rfl | rfl
    · by_cases hcr : c ≤ r
      · right; exact ⟨by linarith [(mpc_diamond_bounds hc).1, pi_pos], hcr⟩
      · left
        exact ⟨not_lt.1 fun hcs => hcr (hgap c (mpc_mem_mpcDiamond.2 hc) hcs),
          by linarith [mpc_diamond_lt_pi hc, pi_pos]⟩
    · left; exact ⟨by linarith, by linarith [mpc_omega_le Θ, pi_pos]⟩
    · left; exact ⟨by linarith, by linarith [pi_pos]⟩)
  rw [hq4, hq3]

/-- **Walk along the upper boundary.** For `s ∈ Θ^◇`,
`v_K⁺(s) - A_K⁻(0) = ∑_{t ∈ Θ^◇, t ≤ s} σ_K(t) v_t`. -/
lemma mpc_walk (hK : IsPolygonCap Θ K) {s : ℝ} (hs : s ∈ mpcDiamond Θ) :
    vplus K s - aMinus K 0 =
      ∑ t ∈ (mpcDiamond Θ).filter (· ≤ s), sigmaAt K t • vvec t := by
  set D := mpcDiamond Θ with hD
  -- strong induction on the number of angles of `Θ^◇` below `s`
  suffices H : ∀ n, ∀ s ∈ D, (D.filter (· < s)).card = n →
      vplus K s - aMinus K 0 = ∑ t ∈ D.filter (· ≤ s), sigmaAt K t • vvec t from
    H _ s hs rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hs hcard
  have hvs : vplus K s = vminus K s + sigmaAt K s • vvec s := (proposition2_1_2 hK.1.2.1 s).2
  rcases (D.filter (· < s)).eq_empty_or_nonempty with hemp | hne
  · -- `s` is the first angle of `Θ^◇`, and `v_K⁻(s) = A_K⁻(0)`
    have hnone := Finset.filter_eq_empty_iff.1 hemp
    have hsmin : D.min' (mpc_mpcDiamond_nonempty Θ) = s :=
      le_antisymm (D.min'_le s hs) (not_lt.1 (hnone (D.min'_mem _)))
    have hfil : D.filter (· ≤ s) = {s} := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun ⟨ht, hts⟩ => hts.eq_or_lt.resolve_right (hnone ht), by
        rintro rfl; exact ⟨hs, le_rfl⟩⟩
    have hA := mpc_aMinus_eq hK
    rw [hsmin] at hA
    rw [hfil, Finset.sum_singleton, hvs, hA.1, hA.2.2]
    abel
  · -- the previous angle `r` of `Θ^◇`, with `v_K⁻(s) = v_K⁺(r)`
    set r := (D.filter (· < s)).max' hne
    obtain ⟨hrD, hrs⟩ := Finset.mem_filter.1 (Finset.max'_mem _ hne)
    have hgap : ∀ c ∈ D, c < s → c ≤ r := fun c hc hcs =>
      (D.filter (· < s)).le_max' c (Finset.mem_filter.2 ⟨hc, hcs⟩)
    have hlt : (D.filter (· < r)).card < n := by
      rw [← hcard]
      refine Finset.card_lt_card ⟨fun t ht => ?_, fun h => ?_⟩
      · obtain ⟨htD, htr⟩ := Finset.mem_filter.1 ht
        exact Finset.mem_filter.2 ⟨htD, htr.trans hrs⟩
      · exact lt_irrefl r (Finset.mem_filter.1 (h (Finset.max'_mem _ hne))).2
    have hfil : D.filter (· ≤ s) = insert s (D.filter (· ≤ r)) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨ht, hts⟩
        rcases hts.eq_or_lt with h | h
        · exact Or.inl h
        · exact Or.inr ⟨ht, hgap t ht h⟩
      · rintro (rfl | ⟨ht, htr⟩)
        · exact ⟨hs, le_rfl⟩
        · exact ⟨ht, htr.trans hrs.le⟩
    have hnot : s ∉ D.filter (· ≤ r) := fun h => (Finset.mem_filter.1 h).2.not_gt hrs
    rw [hfil, Finset.sum_insert hnot, ← ih _ hlt r hrD rfl, hvs,
      mpc_vminus_eq_vplus hK hrD hs hrs hgap]
    abel

/-- `C_K⁺(ω) - A_K⁻(0) = ∑_{t ∈ Θ^◇} σ_K(t) v_t`. -/
lemma mpc_walk_total (hK : IsPolygonCap Θ K) :
    cPlus K Θ.ω - aMinus K 0 = ∑ t ∈ mpcDiamond Θ, sigmaAt K t • vvec t := by
  have hM := Finset.max'_mem (mpcDiamond Θ) (mpc_mpcDiamond_nonempty Θ)
  rw [← (mpc_cPlus_eq hK).2.2.1, mpc_walk hK hM, Finset.filter_true_of_mem]
  exact fun t ht => (mpcDiamond Θ).le_max' t ht

/-- `∑_{t ∈ Θ^◇} σ_K(t) sin t = A_K⁻(0)_x - C_K⁺(ω)_x`. -/
lemma mpc_sum_sigma_sin (hK : IsPolygonCap Θ K) :
    ∑ t ∈ mpcDiamond Θ, sigmaAt K t * sin t = (aMinus K 0).1 - (cPlus K Θ.ω).1 := by
  have h := congrArg Prod.fst (mpc_walk_total hK)
  simp only [Prod.fst_sub, Prod.fst_sum, Prod.smul_fst, vvec_fst, smul_eq_mul, mul_neg,
    Finset.sum_neg_distrib] at h
  linarith

end Corners

/-! ### The caps `𝓒_Θ(h)` of height functions -/

open Classical in
/-- The constraint values of `𝓒_Θ(h)` on the angles `Θ^◇ ∪ {ω + π, 3π/2}`. -/
noncomputable def mpcCapC (Θ : AngleSet) (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  if s ∈ Θ.diamond then h s else 1 - h (s - π)

/-- Membership in `𝓒_Θ(h)` through its constraints on the angles `Θ^◇ ∪ {ω + π, 3π/2}`. -/
lemma mpc_mem_capH_iff_capAngles (Θ : AngleSet) (h : ℝ → ℝ) (p : ℝ × ℝ) :
    p ∈ capH Θ h ↔ ∀ s ∈ Θ.capAngles, dot p (uvec s) ≤ mpcCapC Θ h s := by
  have hnd1 : Θ.ω + π ∉ Θ.diamond := fun h => by
    linarith [mpc_diamond_lt_pi h, pi_pos, mpc_omega_pos Θ]
  have hnd2 : 3 * π / 2 ∉ Θ.diamond := fun h => by linarith [mpc_diamond_lt_pi h, pi_pos]
  have e1 : dot p (uvec (Θ.ω + π)) ≤ mpcCapC Θ h (Θ.ω + π) ↔
      h Θ.ω - 1 ≤ dot p (uvec Θ.ω) := by
    rw [mpcCapC, ite_eq_right hnd1, dot_uvec_add_pi, add_sub_cancel_right]
    constructor <;> intro <;> linarith
  have e2 : dot p (uvec (3 * π / 2)) ≤ mpcCapC Θ h (3 * π / 2) ↔
      h (π / 2) - 1 ≤ dot p (uvec (π / 2)) := by
    rw [mpcCapC, ite_eq_right hnd2, dot_uvec_three_pi_div_two, dot_uvec_pi_div_two,
      show 3 * π / 2 - π = π / 2 by ring]
    constructor <;> intro <;> linarith
  rw [nef_mem_capH_iff, AngleSet.capAngles]
  simp only [mem_union, mem_insert_iff, mem_singleton_iff, or_imp, forall_and, forall_eq, e1, e2]
  refine and_congr_left' (forall₂_congr fun s hs => ?_)
  rw [mpcCapC, ite_eq_left hs]

/-- `𝓒_Θ(h)` is an intersection of closed half-planes with normal angles in
`Θ^◇ ∪ {ω + π, 3π/2}`. -/
lemma mpc_capH_halfPlaneInter (Θ : AngleSet) (h : ℝ → ℝ) :
    IsHalfPlaneInter (capH Θ h) Θ.capAngles := by
  refine ⟨Θ.capAngles, fun i => i.1, fun i => mpcCapC Θ h i.1, fun i => i.2, ?_⟩
  ext p
  simp only [mpc_mem_capH_iff_capAngles, mem_iInter, halfMinus, mem_ofPred_eq, Subtype.forall]

/-- A set in a horizontal strip and two half-planes `H₋(t, ·)`, `H₋(t + π/2, ·)` with
`t ∈ (0, π/2)` is bounded. -/
lemma mpc_isBounded_of_strip {S : Set (ℝ × ℝ)} {a b t c₁ c₂ : ℝ} (ht0 : 0 < t)
    (ht1 : t < π / 2)
    (hS : ∀ p ∈ S, a ≤ p.2 ∧ p.2 ≤ b ∧ dot p (uvec t) ≤ c₁ ∧ dot p (uvec (t + π / 2)) ≤ c₂) :
    Bornology.IsBounded S := by
  have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith, ht1⟩
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 (by linarith)
  set Y := |a| + |b|
  apply (Metric.isBounded_Icc (-(c₂ + Y) / sin t) ((c₁ + Y) / cos t)).prod
    (Metric.isBounded_Icc a b) |>.subset
  intro p hp
  obtain ⟨h1, h2, h3, h4⟩ := hS p hp
  rw [uvec_add_pi_div_two] at h4
  simp only [dot, uvec, vvec] at h3 h4
  have hy : |p.2| ≤ Y := by
    rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith
  have hy1 : |p.2 * sin t| ≤ Y := by
    rw [abs_mul]
    nlinarith [abs_sin_le_one t, abs_nonneg p.2, abs_nonneg (sin t)]
  have hy2 : |p.2 * cos t| ≤ Y := by
    rw [abs_mul]
    nlinarith [abs_cos_le_one t, abs_nonneg p.2, abs_nonneg (cos t)]
  have e1 := (abs_le.1 hy1)
  have e2 := (abs_le.1 hy2)
  refine ⟨⟨?_, ?_⟩, ⟨h1, h2⟩⟩
  · rw [div_le_iff₀ hs]; nlinarith
  · rw [le_div_iff₀ hc]; nlinarith

/-- `𝓒_Θ` with separate heights for the upper sides (`hT`) and the bottom sides (`hB`), so that
`𝓒_Θ(h) = mpcCapH2 Θ h h` (`mpc_capH_eq_capH2`). Used to move one side at a time. -/
def mpcCapH2 (Θ : AngleSet) (hT hB : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | (∀ s ∈ Θ.diamond, dot p (uvec s) ≤ hT s) ∧ hB Θ.ω - 1 ≤ dot p (uvec Θ.ω) ∧
    hB (π / 2) - 1 ≤ dot p (uvec (π / 2))}

lemma mpc_capH_eq_capH2 (Θ : AngleSet) (h : ℝ → ℝ) : capH Θ h = mpcCapH2 Θ h h := by
  ext p; rw [nef_mem_capH_iff]; rfl

/-- `mpcCapH2 Θ hT hB` lies in a horizontal strip and two half-planes, so it is bounded. -/
lemma mpc_isBounded_capH2 (Θ : AngleSet) (hT hB : ℝ → ℝ) :
    Bornology.IsBounded (mpcCapH2 Θ hT hB) := by
  obtain ⟨t, ht⟩ := Θ.nonempty
  have htb := mpc_angles_bounds ht
  have hω := mpc_omega_le Θ
  apply mpc_isBounded_of_strip htb.1 (by linarith) (a := hB (π / 2) - 1) (b := hT (π / 2))
    (c₁ := hT t) (c₂ := hT (t + π / 2))
  rintro p ⟨h1, -, h3⟩
  have e := h1 _ (Or.inr (Or.inr rfl))
  rw [dot_uvec_pi_div_two] at e h3
  exact ⟨h3, e, h1 t (Or.inl (Or.inl ht)), h1 _ (Or.inl (Or.inr ⟨t, ht, rfl⟩))⟩

/-- `𝓒_Θ(h)` is compact. -/
lemma mpc_isCompact_capH (Θ : AngleSet) (h : ℝ → ℝ) : IsCompact (capH Θ h) :=
  Metric.isCompact_of_isClosed_isBounded
    (nef_isHalfPlaneInter_isClosed (mpc_capH_halfPlaneInter Θ h))
    (mpc_capH_eq_capH2 Θ h ▸ mpc_isBounded_capH2 Θ h h)

/-- `𝓒_Θ(h)` is a polygon cap as soon as it is nonempty and has the support values of a cap at
`ω`, `π/2`, `ω + π` and `3π/2`. -/
lemma mpc_capH_isPolygonCap {Θ : AngleSet} {h : ℝ → ℝ} (hne : (capH Θ h).Nonempty)
    (h1 : supp (capH Θ h) Θ.ω = 1) (h2 : supp (capH Θ h) (π / 2) = 1)
    (h3 : supp (capH Θ h) (Θ.ω + π) = 0) (h4 : supp (capH Θ h) (3 * π / 2) = 0) :
    IsPolygonCap Θ (capH Θ h) :=
  ⟨⟨Θ.hω, ⟨hne, mpc_isCompact_capH Θ h,
      nef_isHalfPlaneInter_convex (mpc_capH_halfPlaneInter Θ h)⟩, h1, h2, h3, h4,
      nef_isHalfPlaneInter_mono (nef_capAngles_subset Θ) (mpc_capH_halfPlaneInter Θ h)⟩,
    mpc_capH_halfPlaneInter Θ h⟩


/-! ## The niche as the region between two graphs

To study the boundary of `F_ω \ 𝒩_Θ(K)` (Theorem 3.4.4) we describe it in the abscissa: the fan
`F_ω` is the epigraph of `mpcLow`, the union `⋃_{t ∈ Θ} Q_K⁻(t)` is the strict subgraph of `mpcTop`,
so `F_ω \ 𝒩_Θ(K)` is the epigraph of `mpcG = max mpcLow mpcTop`. All these functions are maxima
and minima of the walls `l(s, h_K(s) - 1)`, `s ∈ Θ^◇`, written as graphs (`mpcL`). -/

section Polyline

open Filter Topology

/-! ### Lines as graphs -/

/-- The height at abscissa `x` of the line `l(s, c)` (for `sin s ≠ 0`). -/
noncomputable def mpcLineY (s c x : ℝ) : ℝ := (c - x * cos s) / sin s

/-- `p` lies strictly below the line `l(s, c)` iff `p · u_s < c` (for `sin s > 0`). -/
lemma mpc_dot_lt_iff {s c : ℝ} (hs : 0 < sin s) (p : ℝ × ℝ) :
    dot p (uvec s) < c ↔ p.2 < mpcLineY s c p.1 := by
  simp only [dot, uvec, mpcLineY]
  rw [lt_div_iff₀ hs]
  constructor <;> intro h <;> linarith

/-- `p` lies below the line `l(s, c)` iff `p · u_s ≤ c` (for `sin s > 0`). -/
lemma mpc_dot_le_iff {s c : ℝ} (hs : 0 < sin s) (p : ℝ × ℝ) :
    dot p (uvec s) ≤ c ↔ p.2 ≤ mpcLineY s c p.1 := by
  simp only [dot, uvec, mpcLineY]
  rw [le_div_iff₀ hs]
  constructor <;> intro h <;> linarith

/-- The graph of `mpcLineY s c` lies on `l(s, c)`. -/
lemma mpc_dot_lineY (s c x : ℝ) (hs : sin s ≠ 0) : dot (x, mpcLineY s c x) (uvec s) = c := by
  simp only [dot, uvec, mpcLineY]
  field_simp
  ring

lemma mpc_continuous_lineY (s c : ℝ) : Continuous (mpcLineY s c) := by
  unfold mpcLineY; fun_prop

/-- Two lines with different normal angles (modulo `π`) meet at one abscissa. -/
lemma mpc_lineY_eq_imp {s c s' c' x : ℝ} (hs : sin s ≠ 0) (hs' : sin s' ≠ 0)
    (hss : sin (s' - s) ≠ 0) (h : mpcLineY s c x = mpcLineY s' c' x) :
    x = (c * sin s' - c' * sin s) / sin (s' - s) := by
  rw [eq_div_iff hss, sin_sub]
  simp only [mpcLineY] at h
  rw [div_eq_div_iff hs hs'] at h
  linarith

/-- Parallel lines with different offsets do not meet. -/
lemma mpc_lineY_inj {s c c' x : ℝ} (hs : sin s ≠ 0) (h : mpcLineY s c x = mpcLineY s c' x) :
    c = c' := by
  simp only [mpcLineY] at h
  rw [div_left_inj' hs] at h
  linarith

/-! ### The graphs bounding the polygon niche -/

/-- The line `l(s, h_K(s) - 1)` as a graph. -/
noncomputable def mpcL (K : Set (ℝ × ℝ)) (s x : ℝ) : ℝ := mpcLineY s (supp K s - 1) x

/-- The lower boundary of the fan `F_ω`. -/
noncomputable def mpcLow (Θ : AngleSet) (K : Set (ℝ × ℝ)) (x : ℝ) : ℝ :=
  max (mpcL K Θ.ω x) (mpcL K (π / 2) x)

/-- The upper boundary of `⋃_{t ∈ Θ} Q_K⁻(t)`. -/
noncomputable def mpcTop (Θ : AngleSet) (K : Set (ℝ × ℝ)) (x : ℝ) : ℝ :=
  Θ.angles.sup' Θ.nonempty fun t => min (mpcL K t x) (mpcL K (t + π / 2) x)

/-- The lower boundary of `F_ω \ 𝒩_Θ(K)`. -/
noncomputable def mpcG (Θ : AngleSet) (K : Set (ℝ × ℝ)) (x : ℝ) : ℝ :=
  max (mpcLow Θ K x) (mpcTop Θ K x)

lemma mpc_continuous_mpcL (K : Set (ℝ × ℝ)) (s : ℝ) : Continuous (mpcL K s) :=
  mpc_continuous_lineY _ _

lemma mpc_continuous_mpcLow (Θ : AngleSet) (K : Set (ℝ × ℝ)) : Continuous (mpcLow Θ K) :=
  (mpc_continuous_mpcL K _).max (mpc_continuous_mpcL K _)

/-- `mpcTop` as a supremum of functions. -/
lemma mpc_mpcTop_eq (Θ : AngleSet) (K : Set (ℝ × ℝ)) :
    mpcTop Θ K = Θ.angles.sup' Θ.nonempty (fun t x => min (mpcL K t x) (mpcL K (t + π / 2) x)) := by
  funext x
  rw [Finset.sup'_apply]
  rfl

lemma mpc_continuous_mpcTop (Θ : AngleSet) (K : Set (ℝ × ℝ)) : Continuous (mpcTop Θ K) := by
  rw [mpc_mpcTop_eq]
  apply Finset.sup'_induction (p := Continuous)
  · intro f hf g hg; exact hf.max hg
  · intro t _; exact (mpc_continuous_mpcL K _).min (mpc_continuous_mpcL K _)

lemma mpc_continuous_mpcG (Θ : AngleSet) (K : Set (ℝ × ℝ)) : Continuous (mpcG Θ K) :=
  (mpc_continuous_mpcLow Θ K).max (mpc_continuous_mpcTop Θ K)

/-- A point lies below `mpcTop` iff it lies below both walls of some `t ∈ Θ`. -/
lemma mpc_lt_mpcTop_iff (Θ : AngleSet) (K : Set (ℝ × ℝ)) (x y : ℝ) :
    y < mpcTop Θ K x ↔ ∃ t ∈ Θ.angles, y < mpcL K t x ∧ y < mpcL K (t + π / 2) x := by
  rw [mpcTop, Finset.lt_sup'_iff]
  simp only [lt_min_iff]

section CapGraphs

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

/-- The bottom side `l(π/2, 0)` of the fan is the axis `y = 0`. -/
lemma mpc_mpcL_pi_div_two (hK : IsPolygonCap Θ K) (x : ℝ) : mpcL K (π / 2) x = 0 := by
  simp [mpcL, mpcLineY, hK.1.2.2.2.1]

/-- The bottom side `l(ω, 0)` of the fan as a graph. -/
lemma mpc_mpcL_omega (hK : IsPolygonCap Θ K) (x : ℝ) :
    mpcL K Θ.ω x = -(x * cos Θ.ω) / sin Θ.ω := by
  simp [mpcL, mpcLineY, hK.1.2.2.1]

/-- The fan is the epigraph of `mpcLow`. -/
lemma mpc_fan_eq (hK : IsPolygonCap Θ K) : fan Θ.ω = {p | mpcLow Θ K p.1 ≤ p.2} := by
  have hω := mpc_sin_pos_of_diamond (Θ := Θ) (Or.inr (Or.inl rfl))
  have hπ := mpc_sin_pos_of_diamond (Θ := Θ) (Or.inr (Or.inr rfl))
  ext p
  simp only [fan, halfPlus, mem_inter_iff, mem_ofPred_eq, mpcLow, max_le_iff]
  have e1 : (0 ≤ dot p (uvec Θ.ω)) ↔ mpcL K Θ.ω p.1 ≤ p.2 := by
    rw [mpcL, hK.1.2.2.1, sub_self, ← not_lt, ← not_lt, mpc_dot_lt_iff hω]
  have e2 : (0 ≤ dot p (uvec (π / 2))) ↔ mpcL K (π / 2) p.1 ≤ p.2 := by
    rw [mpc_mpcL_pi_div_two hK, dot_uvec_pi_div_two]
  rw [e1, e2]

/-- The open quarter-plane `Q_K⁻(t)` is the strict subgraph of a tent. -/
lemma mpc_qMinus_eq {t : ℝ} (ht : t ∈ Θ.angles) :
    qMinus K t = {p | p.2 < mpcL K t p.1 ∧ p.2 < mpcL K (t + π / 2) p.1} := by
  have h1 := mpc_sin_pos_of_diamond (Θ := Θ) (Or.inl (Or.inl ht))
  have h2 := mpc_sin_pos_of_diamond (Θ := Θ) (Or.inl (Or.inr ⟨t, ht, rfl⟩))
  rw [proposition2_2_2_qMinus]
  ext p
  simp only [halfMinusOpen, mem_inter_iff, mem_ofPred_eq, mpcL]
  rw [mpc_dot_lt_iff h1, mpc_dot_lt_iff h2]

/-- The polygon niche is the region between `mpcLow` and `mpcTop`. -/
lemma mpc_polyNiche_eq (hK : IsPolygonCap Θ K) :
    polyNiche Θ K = {p | mpcLow Θ K p.1 ≤ p.2 ∧ p.2 < mpcTop Θ K p.1} := by
  ext p
  simp only [polyNiche, mem_inter_iff, mem_iUnion, exists_prop, mem_ofPred_eq]
  rw [mpc_fan_eq hK, mem_ofPred_eq, mpc_lt_mpcTop_iff]
  refine and_congr_right fun _ => exists_congr fun t => and_congr_right fun ht => ?_
  rw [mpc_qMinus_eq ht, mem_ofPred_eq]

/-- `F_ω \ 𝒩_Θ(K)` is the epigraph of `mpcG`. -/
lemma mpc_fan_diff_eq (hK : IsPolygonCap Θ K) :
    fan Θ.ω \ polyNiche Θ K = {p | mpcG Θ K p.1 ≤ p.2} := by
  rw [mpc_fan_eq hK, mpc_polyNiche_eq hK]
  ext p
  simp only [Set.mem_sdiff, mem_ofPred_eq, not_and, not_lt, mpcG, max_le_iff]
  exact ⟨fun h => ⟨h.1, h.2 h.1⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩

end CapGraphs

/-- A point of the closure of `S` whose vertical translates `(p.1, p.2 - δ)`, `δ > 0`, all lie
outside `S` is a frontier point of `S`. -/
lemma mpc_mem_frontier_of_below {S : Set (ℝ × ℝ)} {p : ℝ × ℝ} (hp : p ∈ closure S)
    (hbelow : ∀ δ > 0, (p.1, p.2 - δ) ∉ S) : p ∈ frontier S := by
  refine ⟨hp, fun hint => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
  refine hbelow (ε / 2) (half_pos hε) (hball ?_)
  rw [Metric.mem_ball, Prod.dist_eq]
  simp only [dist_self, Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos (half_pos hε)]
  exact max_lt hε (half_lt_self hε)

/-- The frontier of the epigraph of a continuous function is its graph. -/
lemma mpc_frontier_epigraph {G : ℝ → ℝ} (hG : Continuous G) :
    frontier {p : ℝ × ℝ | G p.1 ≤ p.2} = {p | p.2 = G p.1} := by
  have hcl : IsClosed {p : ℝ × ℝ | G p.1 ≤ p.2} :=
    isClosed_le (hG.comp continuous_fst) continuous_snd
  ext p
  refine ⟨fun h => ?_, fun h => mpc_mem_frontier_of_below (subset_closure h.ge) ?_⟩
  · have hsub : {q : ℝ × ℝ | G q.1 < q.2} ⊆ interior {q : ℝ × ℝ | G q.1 ≤ q.2} :=
      interior_maximal (fun q (hq : G q.1 < q.2) => hq.le)
        (isOpen_lt (hG.comp continuous_fst) continuous_snd)
    exact ((hcl.frontier_subset h).eq_or_lt.resolve_right fun hlt => h.2 (hsub hlt)).symm
  · intro δ hδ hmem
    simp only [mem_ofPred_eq] at hmem h
    linarith

section Boundary

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

/-- The coordinates of `C_K⁺(ω) = h_K(ω + π/2) v_ω`. -/
lemma mpc_cPlus_coords (hK : IsPolygonCap Θ K) :
    (cPlus K Θ.ω).1 = -(supp K (Θ.ω + π / 2) * sin Θ.ω) ∧
      (cPlus K Θ.ω).2 = supp K (Θ.ω + π / 2) * cos Θ.ω := by
  rw [(mpc_cPlus_eq hK).1]
  simp [vvec]

/-- The coordinates of `A_K⁻(0) = (h_K(0), 0)`. -/
lemma mpc_aMinus_coords (hK : IsPolygonCap Θ K) :
    (aMinus K 0).1 = supp K 0 ∧ (aMinus K 0).2 = 0 := by
  rw [(mpc_aMinus_eq hK).1]
  simp

/-- `x cos ω ≤ 0` to the left of `C_K⁺(ω)`. -/
lemma mpc_mul_cos_nonpos (hK : IsPolygonCap Θ K) {x : ℝ} (hx : x ≤ (cPlus K Θ.ω).1) :
    x * cos Θ.ω ≤ 0 := by
  have hω0 := mpc_omega_pos Θ
  rcases lt_or_eq_of_le (mpc_omega_le Θ) with hlt | heq
  · have h1 := (mpc_sigma_bottom_lt hK hlt).2.2.2
    have hs : 0 < sin Θ.ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
    have hc : 0 < cos Θ.ω := cos_pos_of_mem_Ioo ⟨by linarith, hlt⟩
    rw [(mpc_cPlus_coords hK).1] at hx
    have : x ≤ 0 := by nlinarith
    nlinarith
  · rw [heq, cos_pi_div_two, mul_zero]

/-- `x cos ω ≥ 0` to the right of `A_K⁻(0)`. -/
lemma mpc_mul_cos_nonneg (hK : IsPolygonCap Θ K) {x : ℝ} (hx : (aMinus K 0).1 ≤ x) :
    0 ≤ x * cos Θ.ω := by
  have hω0 := mpc_omega_pos Θ
  rcases lt_or_eq_of_le (mpc_omega_le Θ) with hlt | heq
  · have h1 := (mpc_sigma_bottom_lt hK hlt).2.1
    have hc : 0 < cos Θ.ω := cos_pos_of_mem_Ioo ⟨by linarith, hlt⟩
    rw [(mpc_aMinus_coords hK).1] at hx
    nlinarith
  · rw [heq, cos_pi_div_two, mul_zero]

/-- To the left of `C_K⁺(ω)` the lower boundary of `F_ω \ 𝒩_Θ(K)` is the side `l(ω, 0)` of the fan
and lies strictly above the niche (the wedge gaps `z_K(t)` are positive). -/
lemma mpc_left_of_C (hK : IsPolygonCap Θ K) {x : ℝ} (hx : x ≤ (cPlus K Θ.ω).1) :
    mpcTop Θ K x < mpcLow Θ K x ∧ mpcLow Θ K x = mpcL K Θ.ω x := by
  have hω0 := mpc_omega_pos Θ
  have hω2 := mpc_omega_le Θ
  have hsω : 0 < sin Θ.ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
  have hxc := mpc_mul_cos_nonpos hK hx
  have hLω : 0 ≤ mpcL K Θ.ω x := by
    rw [mpc_mpcL_omega hK]
    apply div_nonneg (by linarith) hsω.le
  have hlow : mpcLow Θ K x = mpcL K Θ.ω x := by
    rw [mpcLow, mpc_mpcL_pi_div_two hK, max_eq_left hLω]
  refine ⟨?_, hlow⟩
  rw [hlow, mpcTop, Finset.sup'_lt_iff]
  intro t ht
  apply lt_of_le_of_lt (min_le_right _ _)
  have htb := mpc_angles_bounds ht
  have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  have hst : 0 < sin t := sin_pos_of_pos_of_lt_pi htb.1 (by linarith [pi_pos])
  have hcωt : 0 < cos (Θ.ω - t) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  -- the wedge gap `z_K(t) > 0`
  have hz := (theorem2_5_5 hK.1 ⟨htb.1, htb.2⟩).2
  rw [wedgeGapZ, wedgeZ, (mpc_cPlus_eq hK).1, ← sub_smul, dot_smul_left, dot_vvec_self,
    mul_one, sub_pos, div_lt_iff₀ hcωt] at hz
  have hC := (mpc_cPlus_coords hK).1
  rw [hC] at hx
  rw [mpc_mpcL_omega hK, mpcL, mpcLineY, cos_add_pi_div_two, sin_add_pi_div_two,
    div_lt_div_iff₀ hct hsω]
  rw [cos_sub] at hcωt hz
  nlinarith [mul_le_mul_of_nonneg_right hx (le_of_lt hcωt)]

/-- To the right of `A_K⁻(0)` the lower boundary of `F_ω \ 𝒩_Θ(K)` is the side `l(π/2, 0)` of the
fan and lies strictly above the niche (the wedge gaps `w_K(t)` are positive). -/
lemma mpc_right_of_A (hK : IsPolygonCap Θ K) {x : ℝ} (hx : (aMinus K 0).1 ≤ x) :
    mpcTop Θ K x < mpcLow Θ K x ∧ mpcLow Θ K x = 0 := by
  have hω0 := mpc_omega_pos Θ
  have hω2 := mpc_omega_le Θ
  have hsω : 0 < sin Θ.ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
  have hxc := mpc_mul_cos_nonneg hK hx
  have hLω : mpcL K Θ.ω x ≤ 0 := by
    rw [mpc_mpcL_omega hK]
    apply div_nonpos_of_nonpos_of_nonneg (by linarith) hsω.le
  have hlow : mpcLow Θ K x = 0 := by
    rw [mpcLow, mpc_mpcL_pi_div_two hK, max_eq_right hLω]
  refine ⟨?_, hlow⟩
  rw [hlow, mpcTop, Finset.sup'_lt_iff]
  intro t ht
  apply lt_of_le_of_lt (min_le_left _ _)
  have htb := mpc_angles_bounds ht
  have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  have hst : 0 < sin t := sin_pos_of_pos_of_lt_pi htb.1 (by linarith [pi_pos])
  have hw := (theorem2_5_5 hK.1 ⟨htb.1, htb.2⟩).1
  rw [wedgeGapW, (mpc_aMinus_eq hK).1, wedgeW, dot_uvec_zero, Prod.fst_sub] at hw
  simp only at hw
  rw [sub_pos, div_lt_iff₀ hct] at hw
  have hA := (mpc_aMinus_coords hK).1
  rw [hA] at hx
  rw [mpcL, mpcLineY, div_neg_iff]
  right
  refine ⟨?_, hst⟩
  nlinarith [mul_le_mul_of_nonneg_right hx hct.le]

/-- Where the niche is nonempty, `mpcLow ≤ mpcTop`, we are between `C_K⁺(ω)` and `A_K⁻(0)`. -/
lemma mpc_between (hK : IsPolygonCap Θ K) {x : ℝ} (h : mpcLow Θ K x ≤ mpcTop Θ K x) :
    (cPlus K Θ.ω).1 ≤ x ∧ x ≤ (aMinus K 0).1 :=
  ⟨not_lt.1 fun hx => (mpc_left_of_C hK hx.le).1.not_ge h,
    not_lt.1 fun hx => (mpc_right_of_A hK hx.le).1.not_ge h⟩

/-- `C_K⁺(ω)` lies strictly to the left of `A_K⁻(0)`: the walk along the upper boundary from
`A_K⁻(0)` to `C_K⁺(ω)` moves left by `∑_{t ∈ Θ^◇} σ_K(t) sin t`, which is positive since the walk
climbs from `A_K⁻(0)` on the axis `y = 0` to `v_K⁺(π/2)` on the top side `y = 1`. -/
lemma mpc_C_lt_A (hK : IsPolygonCap Θ K) : (cPlus K Θ.ω).1 < (aMinus K 0).1 := by
  have hnn : ∀ t ∈ mpcDiamond Θ, 0 ≤ sigmaAt K t * sin t := fun t ht =>
    mul_nonneg ENNReal.toReal_nonneg (mpc_sin_pos_of_diamond (mpc_mem_mpcDiamond.1 ht)).le
  rw [← sub_pos, ← mpc_sum_sigma_sin hK]
  refine (Finset.sum_nonneg hnn).lt_of_ne fun h0 => ?_
  -- otherwise all the sides `σ_K(t)`, `t ∈ Θ^◇`, vanish, and `v_K⁺(π/2) = A_K⁻(0)`
  have hσ : ∀ t ∈ mpcDiamond Θ, sigmaAt K t = 0 := fun t ht =>
    (mul_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0.symm t ht)).resolve_right
      (mpc_sin_pos_of_diamond (mpc_mem_mpcDiamond.1 ht)).ne'
  have hv := mpc_walk hK (s := π / 2) (mpc_mem_mpcDiamond.2 (Or.inr (Or.inr rfl)))
  rw [Finset.sum_eq_zero fun t ht => by rw [hσ t (Finset.mem_filter.1 ht).1, zero_smul],
    sub_eq_zero] at hv
  have h1 := dot_vplus_uvec K (π / 2)
  rw [hv, hK.1.2.2.2.1, dot_uvec_pi_div_two, (mpc_aMinus_coords hK).2] at h1
  exact zero_ne_one h1

end Boundary

/-- The polygon niche of a polygon cap is bounded. -/
lemma mpc_isBounded_polyNiche {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) :
    Bornology.IsBounded (polyNiche Θ K) :=
  (proposition3_3_5 hK).1 ▸ nef_nicheH_isBounded Θ (supp K)

end Polyline

end MovingSofaOptimality
