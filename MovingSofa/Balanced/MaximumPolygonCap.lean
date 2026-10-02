module

public import MovingSofa.Balanced.PolygonCap

/-!
# Maximum polygon caps (§3.4)

Definitions 3.4.1–3.4.5, Lemmas 3.4.1–3.4.2, Theorem 3.4.3 (`thm:maximum-polygon-cap`), Theorem 3.4.4
(`thm:polyline`), Lemmas 3.4.5–3.4.8, Theorems 3.4.9 (`thm:balanced-polygon-sofa`) and 3.4.10
(`thm:balanced-polygon-sofa-connected`).

**Statement fix.** In Theorem 3.4.4 the edge lengths are now written `∃ ℓ > (0 : ℝ)`; the original
`∃ ℓ > 0` was elaborated with `ℓ : ℕ`, which makes the statement false
(`mpc_theorem3_4_4_nat_false` at the end of the file).

**Organization of the proofs.**
* Corners (`mpc_corner`): when no defining normal angle of a convex body lies strictly between `a`
  and `b`, the supporting lines `l_K(a)`, `l_K(b)` meet at a point of `K`. This gives the vertices
  `A_K⁻(0)`, `C_K⁺(ω)`, `o_ω`, `O` of a polygon cap and the walk along its upper boundary
  `v_K⁺(s) - A_K⁻(0) = ∑_{t ≤ s} σ_K(t) v_t` (`mpc_walk`).
* The polyline (Theorem 3.4.4): `F_ω \ 𝒩_Θ(K)` is the epigraph of the continuous piecewise linear
  function `mpcG = max (lower boundary of F_ω) (upper boundary of ⋃ Q_K⁻(t))`; its vertices are the
  sorted crossings of the walls `l(s, h_K(s) - 1)`, `s ∈ Θ^◇` (`mpc_polyline_data`). The lengths
  `τ_K(t)` and Lemmas 3.4.5, 3.4.6 and Theorem 3.4.10 are computed in the abscissa.
* Lemma 3.4.7 applies Theorem 3.1.2 to explicit simple Nef representations of `𝓒_Θ(h)` and
  `𝒩_Θ(h)` (`mpcCapData`, `mpcNicheData`); moving `l(t, h(t))` and `l(t, h(t) - 1)` together is
  reduced to two separate moves (`mpc_capH2_two_shift`).
* Theorem 3.4.3 uses the compactness of the support values on the finite set `Θ^◇`
  (`mpc_limit_polycap`) instead of the Blaschke selection theorem.
-/

@[expose] public section

open Real Set

namespace MovingSofa

/-! ### Plane geometry: corners of convex bodies -/

/-- `sin (b - a) (p · u_s) = sin (b - s) (p · u_a) + sin (s - a) (p · u_b)`. -/
lemma mpc_dot_uvec_comb (p : ℝ × ℝ) (a b s : ℝ) :
    sin (b - a) * dot p (uvec s) = sin (b - s) * dot p (uvec a) + sin (s - a) * dot p (uvec b) := by
  simp only [dot, uvec, sin_sub]
  ring

/-- A vector orthogonal to `u_a` is a multiple of `v_a`. -/
lemma mpc_eq_smul_vvec_of_dot_uvec_eq_zero {w : ℝ × ℝ} {a : ℝ} (h : dot w (uvec a) = 0) :
    w = dot w (vvec a) • vvec a := by
  have := eq_dot_uvec_smul_add w a
  rw [h, zero_smul, zero_add] at this
  exact this

/-- Two vectors with the same dot products against `u_a` and `u_b`, `sin (b - a) ≠ 0`, are equal. -/
lemma mpc_eq_of_dot_eq {p q : ℝ × ℝ} {a b : ℝ} (hab : sin (b - a) ≠ 0)
    (ha : dot p (uvec a) = dot q (uvec a)) (hb : dot p (uvec b) = dot q (uvec b)) : p = q := by
  have h1 : dot (p - q) (uvec a) = 0 := by rw [dot_sub_left, ha, sub_self]
  have h2 := mpc_eq_smul_vvec_of_dot_uvec_eq_zero h1
  have h3 : dot (p - q) (uvec b) = 0 := by rw [dot_sub_left, hb, sub_self]
  rw [h2, dot_smul_left, dot_vvec_uvec'] at h3
  have h4 : dot (p - q) (vvec a) = 0 := by
    rcases mul_eq_zero.1 h3 with h | h
    · exact h
    · exact absurd h hab
  rw [h4, zero_smul] at h2
  exact sub_eq_zero.1 h2

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
    mpc_eq_smul_vvec_of_dot_uvec_eq_zero (by rw [dot_sub_left, hpae, hqa, sub_self])
  have hB : pb - q = dot (pb - q) (vvec b) • vvec b :=
    mpc_eq_smul_vvec_of_dot_uvec_eq_zero (by rw [dot_sub_left, hpbe, hqb, sub_self])
  set α := dot (pa - q) (vvec a)
  set β := dot (pb - q) (vvec b)
  have hα : α ≤ 0 := by
    have h1 : dot (pa - q) (uvec b) ≤ 0 := by rw [dot_sub_left, hqb]; linarith
    rw [hA, dot_smul_left, dot_vvec_uvec'] at h1
    by_contra h
    push Not at h
    linarith [mul_pos h hab]
  have hβ : 0 ≤ β := by
    have h1 : dot (pb - q) (uvec a) ≤ 0 := by rw [dot_sub_left, hqa]; linarith
    rw [hB, dot_smul_left, dot_vvec_uvec'] at h1
    have hs : sin (a - b) = - sin (b - a) := by rw [← sin_neg, neg_sub]
    rw [hs] at h1
    by_contra h
    push Not at h
    nlinarith
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
  apply hgap i
  constructor
  · by_contra h
    push Not at h
    nlinarith
  · by_contra h
    push Not at h
    nlinarith

/-- Properties of a corner point `q` of a convex body, the intersection of `l_K(a)` and `l_K(b)`. -/
theorem mpc_corner_props {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {q : ℝ × ℝ} (hq : q ∈ K)
    {a b : ℝ} (hab : 0 < sin (b - a)) (hqa : dot q (uvec a) = supp K a)
    (hqb : dot q (uvec b) = supp K b) :
    vplus K a = q ∧ vminus K b = q ∧
      (∀ s, 0 ≤ sin (s - a) → 0 ≤ sin (b - s) → dot q (uvec s) = supp K s) ∧
      (∀ s, 0 < sin (s - a) → 0 < sin (b - s) → vplus K s = q ∧ vminus K s = q) := by
  have hsab : sin (a - b) = - sin (b - a) := by rw [← sin_neg, neg_sub]
  -- support values between `a` and `b`
  have hmid : ∀ s, 0 ≤ sin (s - a) → 0 ≤ sin (b - s) → dot q (uvec s) = supp K s := by
    intro s hs1 hs2
    apply le_antisymm (dot_le_supp hK.2.1 hq s)
    apply csSup_le (hK.1.image _)
    rintro _ ⟨p, hp, rfl⟩
    have e1 := mpc_dot_uvec_comb p a b s
    have e2 := mpc_dot_uvec_comb q a b s
    have h1 := dot_le_supp hK.2.1 hp a
    have h2 := dot_le_supp hK.2.1 hp b
    have : sin (b - a) * dot p (uvec s) ≤ sin (b - a) * dot q (uvec s) := by
      rw [e1, e2, hqa, hqb]
      nlinarith [mul_le_mul_of_nonneg_left h1 hs2, mul_le_mul_of_nonneg_left h2 hs1]
    exact le_of_mul_le_mul_left this hab
  refine ⟨?_, ?_, hmid, ?_⟩
  · -- `v_K⁺(a) = q`
    have hqe : q ∈ edge K a := ⟨hq, hqa⟩
    have hsup : sSup ((fun p => dot p (vvec a)) '' edge K a) = dot q (vvec a) := by
      apply IsGreatest.csSup_eq
      refine ⟨mem_image_of_mem _ hqe, ?_⟩
      rintro _ ⟨p, ⟨hp, hpl⟩, rfl⟩
      have hpl' : dot p (uvec a) = supp K a := hpl
      have hw := mpc_eq_smul_vvec_of_dot_uvec_eq_zero
        (show dot (p - q) (uvec a) = 0 by rw [dot_sub_left, hpl', hqa, sub_self])
      have h1 : dot (p - q) (uvec b) ≤ 0 := by
        rw [dot_sub_left, hqb]; linarith [dot_le_supp hK.2.1 hp b]
      rw [hw, dot_smul_left, dot_vvec_uvec'] at h1
      have h2 : dot (p - q) (vvec a) ≤ 0 := by
        by_contra h; push Not at h; linarith [mul_pos h hab]
      rw [dot_sub_left] at h2
      linarith
    simp only [vplus, hsup, ← hqa]
    exact (eq_dot_uvec_smul_add q a).symm
  · -- `v_K⁻(b) = q`
    have hqe : q ∈ edge K b := ⟨hq, hqb⟩
    have hinf : sInf ((fun p => dot p (vvec b)) '' edge K b) = dot q (vvec b) := by
      apply IsLeast.csInf_eq
      refine ⟨mem_image_of_mem _ hqe, ?_⟩
      rintro _ ⟨p, ⟨hp, hpl⟩, rfl⟩
      have hpl' : dot p (uvec b) = supp K b := hpl
      have hw := mpc_eq_smul_vvec_of_dot_uvec_eq_zero
        (show dot (p - q) (uvec b) = 0 by rw [dot_sub_left, hpl', hqb, sub_self])
      have h1 : dot (p - q) (uvec a) ≤ 0 := by
        rw [dot_sub_left, hqa]; linarith [dot_le_supp hK.2.1 hp a]
      rw [hw, dot_smul_left, dot_vvec_uvec', hsab] at h1
      have h2 : 0 ≤ dot (p - q) (vvec b) := by
        by_contra h; push Not at h; nlinarith
      rw [dot_sub_left] at h2
      show dot q (vvec b) ≤ dot p (vvec b)
      linarith
    simp only [vminus, hinf, ← hqb]
    exact (eq_dot_uvec_smul_add q b).symm
  · -- strictly between `a` and `b` the edge is the single point `q`
    intro s hs1 hs2
    have hqs := hmid s hs1.le hs2.le
    have hedge : ∀ p ∈ edge K s, p = q := by
      rintro p ⟨hp, hpl⟩
      have hpl' : dot p (uvec s) = supp K s := hpl
      have e1 := mpc_dot_uvec_comb (p - q) a b s
      have h0 : dot (p - q) (uvec s) = 0 := by rw [dot_sub_left, hpl', hqs, sub_self]
      have h1 : dot (p - q) (uvec a) ≤ 0 := by
        rw [dot_sub_left, hqa]; linarith [dot_le_supp hK.2.1 hp a]
      have h2 : dot (p - q) (uvec b) ≤ 0 := by
        rw [dot_sub_left, hqb]; linarith [dot_le_supp hK.2.1 hp b]
      rw [h0, mul_zero] at e1
      have h1' : dot (p - q) (uvec a) = 0 := by
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hs1.le h2]
      have h2' : dot (p - q) (uvec b) = 0 := by
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hs2.le h1]
      have : p - q = 0 := by
        apply mpc_eq_of_dot_eq hab.ne' <;> simp [h1', h2']
      exact sub_eq_zero.1 this
    have hqe : q ∈ edge K s := ⟨hq, hqs⟩
    have himg : (fun p => dot p (vvec s)) '' edge K s = {dot q (vvec s)} := by
      ext x
      simp only [mem_image, mem_singleton_iff]
      constructor
      · rintro ⟨p, hp, rfl⟩; rw [hedge p hp]
      · rintro rfl; exact ⟨q, hqe, rfl⟩
    constructor
    · simp only [vplus, himg, csSup_singleton, ← hqs]
      exact (eq_dot_uvec_smul_add q s).symm
    · simp only [vminus, himg, csInf_singleton, ← hqs]
      exact (eq_dot_uvec_smul_add q s).symm

/-! ### Hausdorff convergence and semicontinuity of the area -/

section Convergence

open Filter Topology MeasureTheory

/-- `|p · u_t| ≤ |p.1| + |p.2|`. -/
lemma mpc_abs_dot_uvec_le (p : ℝ × ℝ) (t : ℝ) : |dot p (uvec t)| ≤ |p.1| + |p.2| := by
  simp only [dot, uvec]
  calc |p.1 * cos t + p.2 * sin t| ≤ |p.1 * cos t| + |p.2 * sin t| := abs_add_le _ _
    _ = |p.1| * |cos t| + |p.2| * |sin t| := by rw [abs_mul, abs_mul]
    _ ≤ |p.1| * 1 + |p.2| * 1 := by
        gcongr
        · exact abs_cos_le_one t
        · exact abs_sin_le_one t
    _ = |p.1| + |p.2| := by ring

/-- The support function of a nonempty compact set is bounded. -/
lemma mpc_supp_bounded {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ M, ∀ t, |supp K t| ≤ M := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨2 * R, fun t => ?_⟩
  have hb : ∀ p ∈ K, |dot p (uvec t)| ≤ 2 * R := by
    intro p hp
    have h := hR hp
    rw [Metric.mem_closedBall, dist_zero_right] at h
    have h1 : |p.1| ≤ R := (norm_fst_le p).trans h
    have h2 : |p.2| ≤ R := (norm_snd_le p).trans h
    linarith [mpc_abs_dot_uvec_le p t]
  obtain ⟨q, hq, hqe⟩ := exists_dot_eq_supp hK hne t
  rw [← hqe]
  exact hb q hq

lemma mpc_bddAbove_abs_supp_sub {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsCompact K₁) (h₁' : K₁.Nonempty)
    (h₂ : IsCompact K₂) (h₂' : K₂.Nonempty) :
    BddAbove (range fun t => |supp K₁ t - supp K₂ t|) := by
  obtain ⟨M₁, hM₁⟩ := mpc_supp_bounded h₁ h₁'
  obtain ⟨M₂, hM₂⟩ := mpc_supp_bounded h₂ h₂'
  refine ⟨M₁ + M₂, ?_⟩
  rintro _ ⟨t, rfl⟩
  calc |supp K₁ t - supp K₂ t| ≤ |supp K₁ t| + |supp K₂ t| := abs_sub _ _
    _ ≤ M₁ + M₂ := add_le_add (hM₁ t) (hM₂ t)

/-- `|h_{K₁}(t) - h_{K₂}(t)| ≤ d_H(K₁, K₂)`. -/
lemma mpc_abs_supp_sub_le {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsCompact K₁) (h₁' : K₁.Nonempty)
    (h₂ : IsCompact K₂) (h₂' : K₂.Nonempty) (t : ℝ) :
    |supp K₁ t - supp K₂ t| ≤ hausdorffDist K₁ K₂ :=
  le_ciSup (mpc_bddAbove_abs_supp_sub h₁ h₁' h₂ h₂') t

/-- Hausdorff convergence of convex bodies gives uniform convergence of the support functions. -/
lemma mpc_supp_uniform {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {Ks : ℕ → Set (ℝ × ℝ)}
    (hKs : ∀ i, IsConvexBody (Ks i)) (hlim : HausdorffTendsto Ks K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ t, |supp (Ks i) t - supp K t| < ε := by
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with i hi t
  exact lt_of_le_of_lt (mpc_abs_supp_sub_le (hKs i).2.1 (hKs i).1 hK.2.1 hK.1 t) hi

lemma mpc_supp_tendsto {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {Ks : ℕ → Set (ℝ × ℝ)}
    (hKs : ∀ i, IsConvexBody (Ks i)) (hlim : HausdorffTendsto Ks K) (t : ℝ) :
    Tendsto (fun i => supp (Ks i) t) atTop (𝓝 (supp K t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := (mpc_supp_uniform hK hKs hlim hε).exists_forall_of_atTop
  exact ⟨N, fun i hi => by rw [Real.dist_eq]; exact hN i hi t⟩

/-- A point lying eventually in the convex bodies `K_i → K` lies in `K`. -/
lemma mpc_mem_of_eventually_mem {K : Set (ℝ × ℝ)} (hK : IsConvexBody K)
    {Ks : ℕ → Set (ℝ × ℝ)} (hKs : ∀ i, IsConvexBody (Ks i)) (hlim : HausdorffTendsto Ks K)
    {p : ℝ × ℝ} (hp : ∀ᶠ i in atTop, p ∈ Ks i) : p ∈ K := by
  rw [mem_iff_forall_dot_le_supp hK]
  intro t
  apply ge_of_tendsto (mpc_supp_tendsto hK hKs hlim t)
  filter_upwards [hp] with i hi
  exact dot_le_supp (hKs i).2.1 hi t

/-! ### Upper semicontinuity of the area -/

/-- The outer parallel set `{p : p · u_s ≤ h(s) + δ for all s ∈ T}`. -/
def mpcOuter (T : Set ℝ) (h : ℝ → ℝ) (δ : ℝ) : Set (ℝ × ℝ) :=
  {p | ∀ s ∈ T, dot p (uvec s) ≤ h s + δ}

lemma mpc_isClosed_outer (T : Set ℝ) (h : ℝ → ℝ) (δ : ℝ) : IsClosed (mpcOuter T h δ) := by
  have : mpcOuter T h δ = ⋂ s ∈ T, {p : ℝ × ℝ | dot p (uvec s) ≤ h s + δ} := by
    ext p; simp [mpcOuter]
  rw [this]
  refine isClosed_biInter fun s _ => isClosed_le ?_ continuous_const
  simp only [dot]; fun_prop

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
  obtain ⟨M, hM⟩ := mpc_supp_bounded hK.2.1 hK.1
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

/-! ### Lower semicontinuity of the area along pointwise eventual membership -/

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
  have hfin : volume (Ns i) ≠ ⊤ := ne_of_lt ((hB.subset (hn₀ i (le_trans (le_max_right _ _) hi))).measure_lt_top)
  have h1 : area (M n) ≤ area (Ns i) := ENNReal.toReal_mono hfin (measure_mono hsub)
  change _ < area (M n) at hn
  linarith

end Convergence

/-! ### Polygon caps: angles, corners and the walk along the upper boundary -/

/-! ### Angles -/

/-- No angle `c` lies strictly between `r` and `s` modulo `2π`, in the sine form used by
`mpc_corner`. -/
lemma mpc_not_gap {r s c : ℝ} (hrs : r < s) (_hsr : s - r < π)
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

lemma mpc_omega_pos (Θ : AngleSet) : 0 < Θ.ω := Θ.hω.1

lemma mpc_omega_le (Θ : AngleSet) : Θ.ω ≤ π / 2 := Θ.hω.2

lemma mpc_angles_bounds {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.angles) : 0 < t ∧ t < Θ.ω :=
  Θ.subset t ht

/-- `Θ^◇` as a finset. -/
noncomputable def mpcDiamond (Θ : AngleSet) : Finset ℝ :=
  Θ.angles ∪ Θ.angles.image (fun t => t + π / 2) ∪ {Θ.ω, π / 2}

lemma mpc_mem_mpcDiamond {Θ : AngleSet} {t : ℝ} : t ∈ mpcDiamond Θ ↔ t ∈ Θ.diamond := by
  simp only [mpcDiamond, AngleSet.diamond, Finset.mem_union, Finset.mem_image,
    Finset.mem_insert, Finset.mem_singleton, mem_union, Finset.mem_coe, mem_image,
    mem_insert_iff, mem_singleton_iff]

lemma mpc_diamond_cases {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.diamond) :
    t ∈ Θ.angles ∨ (∃ s ∈ Θ.angles, t = s + π / 2) ∨ t = Θ.ω ∨ t = π / 2 := by
  rcases ht with (h | ⟨s, hs, rfl⟩) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨s, hs, rfl⟩)
  · rcases h with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

lemma mpc_diamond_bounds {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.diamond) :
    0 < t ∧ t < Θ.ω + π / 2 := by
  have hω := mpc_omega_pos Θ
  have hω' := mpc_omega_le Θ
  have hpi := pi_pos
  rcases mpc_diamond_cases ht with h | ⟨s, hs, rfl⟩ | rfl | rfl
  · have := mpc_angles_bounds h; constructor <;> linarith
  · have := mpc_angles_bounds hs; constructor <;> linarith
  · constructor <;> linarith
  · constructor <;> linarith

lemma mpc_diamond_lt_pi {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.diamond) : t < π := by
  have := mpc_diamond_bounds ht
  have := mpc_omega_le Θ
  linarith

lemma mpc_sin_pos_of_diamond {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.diamond) : 0 < sin t :=
  sin_pos_of_pos_of_lt_pi (mpc_diamond_bounds ht).1 (mpc_diamond_lt_pi ht)

lemma mpc_capAngles_cases {Θ : AngleSet} {c : ℝ} (hc : c ∈ Θ.capAngles) :
    c ∈ Θ.diamond ∨ c = Θ.ω + π ∨ c = 3 * π / 2 := by
  rcases hc with h | h
  · exact Or.inl h
  · rcases h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

lemma mpc_mpcDiamond_nonempty (Θ : AngleSet) : (mpcDiamond Θ).Nonempty :=
  ⟨Θ.ω, mpc_mem_mpcDiamond.2 (Or.inr (Or.inl rfl))⟩

/-- The largest angle of `Θ^◇` is larger than `π/2`. -/
lemma mpc_max_diamond_gt (Θ : AngleSet) :
    π / 2 < (mpcDiamond Θ).max' (mpc_mpcDiamond_nonempty Θ) := by
  obtain ⟨t, ht⟩ := Θ.nonempty
  have hmem : t + π / 2 ∈ mpcDiamond Θ := mpc_mem_mpcDiamond.2 (Or.inl (Or.inr ⟨t, ht, rfl⟩))
  have := (mpcDiamond Θ).le_max' _ hmem
  linarith [(mpc_angles_bounds ht).1]

/-- The smallest angle of `Θ^◇` is smaller than `ω`. -/
lemma mpc_min_diamond_lt (Θ : AngleSet) :
    (mpcDiamond Θ).min' (mpc_mpcDiamond_nonempty Θ) < Θ.ω := by
  obtain ⟨t, ht⟩ := Θ.nonempty
  have hmem : t ∈ mpcDiamond Θ := mpc_mem_mpcDiamond.2 (Or.inl (Or.inl ht))
  have := (mpcDiamond Θ).min'_le _ hmem
  linarith [(mpc_angles_bounds ht).2]

/-! ### Unit vectors at special angles -/

lemma mpc_uvec_zero : uvec 0 = (1, 0) := by simp [uvec]

lemma mpc_uvec_pi_div_two : uvec (π / 2) = (0, 1) := by simp [uvec]

lemma mpc_uvec_pi : uvec π = (-1, 0) := by simp [uvec]

lemma mpc_uvec_three_pi_div_two : uvec (3 * π / 2) = (0, -1) := by
  have : 3 * π / 2 = π / 2 + π := by ring
  rw [this, uvec_add_pi, mpc_uvec_pi_div_two]
  simp

lemma mpc_uvec_neg_pi_div_two : uvec (-(π / 2)) = (0, -1) := by simp [uvec]

lemma mpc_dot_uvec_zero (p : ℝ × ℝ) : dot p (uvec 0) = p.1 := by
  simp [dot, mpc_uvec_zero]

lemma mpc_dot_uvec_pi_div_two (p : ℝ × ℝ) : dot p (uvec (π / 2)) = p.2 := by
  simp [dot, mpc_uvec_pi_div_two]

lemma mpc_dot_uvec_pi (p : ℝ × ℝ) : dot p (uvec π) = -p.1 := by
  simp [dot, mpc_uvec_pi]

lemma mpc_dot_uvec_three_pi_div_two (p : ℝ × ℝ) : dot p (uvec (3 * π / 2)) = -p.2 := by
  simp [dot, mpc_uvec_three_pi_div_two]

lemma mpc_dot_uvec_add_pi (p : ℝ × ℝ) (t : ℝ) : dot p (uvec (t + π)) = -dot p (uvec t) := by
  rw [uvec_add_pi, dot_neg_right]

lemma mpc_supp_neg_pi_div_two (K : Set (ℝ × ℝ)) : supp K (-(π / 2)) = supp K (3 * π / 2) := by
  rw [← supp_add_two_pi]; congr 1; ring

/-! ### Membership in polygon caps -/

/-- A convex body which is an intersection of closed half-planes with normal angles in `A` is the
intersection of its supporting half-planes with normal angles in `A`. -/
lemma mpc_mem_iff_of_halfPlaneInter {K : Set (ℝ × ℝ)} {A : Set ℝ} (hK : IsConvexBody K)
    (hA : IsHalfPlaneInter K A) (p : ℝ × ℝ) :
    p ∈ K ↔ ∀ t ∈ A, dot p (uvec t) ≤ supp K t := by
  refine ⟨fun hp t _ => dot_le_supp hK.2.1 hp t, fun h => ?_⟩
  obtain ⟨ι, t, c, ht, hKeq⟩ := hA
  have hle : ∀ i, supp K (t i) ≤ c i := by
    intro i
    apply csSup_le (hK.1.image _)
    rintro _ ⟨k, hk, rfl⟩
    rw [hKeq] at hk
    exact mem_iInter.1 hk i
  rw [hKeq]
  exact mem_iInter.2 fun i => le_trans (h _ (ht i)) (hle i)

lemma mpc_cap_body {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) : IsConvexBody K := hK.2.1

lemma mpc_cap_subset_fan {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) : K ⊆ fan ω := by
  intro p hp
  have h1 := dot_le_supp hK.2.1.2.1 hp (ω + π)
  have h2 := dot_le_supp hK.2.1.2.1 hp (3 * π / 2)
  rw [hK.2.2.2.2.1, mpc_dot_uvec_add_pi] at h1
  rw [hK.2.2.2.2.2.1, mpc_dot_uvec_three_pi_div_two] at h2
  refine ⟨?_, ?_⟩
  · show 0 ≤ dot p (uvec ω); linarith
  · show 0 ≤ dot p (uvec (π / 2)); rw [mpc_dot_uvec_pi_div_two]; linarith

lemma mpc_cap_le_one {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) {p : ℝ × ℝ} (hp : p ∈ K) :
    dot p (uvec ω) ≤ 1 ∧ p.2 ≤ 1 := by
  have h1 := dot_le_supp hK.2.1.2.1 hp ω
  have h2 := dot_le_supp hK.2.1.2.1 hp (π / 2)
  rw [hK.2.2.1] at h1
  rw [hK.2.2.2.1, mpc_dot_uvec_pi_div_two] at h2
  exact ⟨h1, h2⟩

/-- Membership in a polygon cap. -/
lemma mpc_polycap_mem_iff {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K)
    (p : ℝ × ℝ) :
    p ∈ K ↔ (∀ t ∈ Θ.diamond, dot p (uvec t) ≤ supp K t) ∧ p ∈ fan Θ.ω := by
  rw [mpc_mem_iff_of_halfPlaneInter hK.1.2.1 hK.2]
  constructor
  · intro h
    refine ⟨fun t ht => h t (Or.inl ht), ?_, ?_⟩
    · have := h (Θ.ω + π) (Or.inr (Or.inl rfl))
      rw [hK.1.2.2.2.2.1, mpc_dot_uvec_add_pi] at this
      show 0 ≤ dot p (uvec Θ.ω); linarith
    · have := h (3 * π / 2) (Or.inr (Or.inr rfl))
      rw [hK.1.2.2.2.2.2.1, mpc_dot_uvec_three_pi_div_two] at this
      show 0 ≤ dot p (uvec (π / 2)); rw [mpc_dot_uvec_pi_div_two]; linarith
  · rintro ⟨h, hf1, hf2⟩ c hc
    rcases mpc_capAngles_cases hc with hc | rfl | rfl
    · exact h c hc
    · rw [hK.1.2.2.2.2.1, mpc_dot_uvec_add_pi]
      have : 0 ≤ dot p (uvec Θ.ω) := hf1
      linarith
    · rw [hK.1.2.2.2.2.2.1, mpc_dot_uvec_three_pi_div_two]
      have : 0 ≤ dot p (uvec (π / 2)) := hf2
      rw [mpc_dot_uvec_pi_div_two] at this
      linarith

/-! ### Corners of polygon caps -/

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
    (fun i => mpc_not_gap hrs hsr (hc _ (ht i)))
  obtain ⟨h1, h2, h3, h4⟩ := mpc_corner_props hK.1.2.1 hq hsin hqr hqs
  refine ⟨q, hq, hqr, hqs, h1, h2, fun x hx1 hx2 => h3 x ?_ ?_, fun x hx1 hx2 => h4 x ?_ ?_⟩
  · exact sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  · exact sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  · exact sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  · exact sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

section Corners

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

/-- The corner `A_K⁻(0) = (h_K(0), 0)` of a polygon cap. -/
lemma mpc_aMinus_eq (hK : IsPolygonCap Θ K) :
    aMinus K 0 = (supp K 0, 0) ∧ (supp K 0, (0 : ℝ)) ∈ K ∧
      vminus K ((mpcDiamond Θ).min' (mpc_mpcDiamond_nonempty Θ)) = (supp K 0, 0) := by
  set m := (mpcDiamond Θ).min' (mpc_mpcDiamond_nonempty Θ)
  have hm0 : 0 < m := (mpc_diamond_bounds (mpc_mem_mpcDiamond.1 (Finset.min'_mem _ _))).1
  have hmω := mpc_min_diamond_lt Θ
  have hω := mpc_omega_le Θ
  obtain ⟨q, hq, hq1, hq2, -, hq4, -, hq6⟩ := mpc_polycap_corner hK (r := -(π / 2)) (s := m)
    (by linarith [pi_pos]) (by linarith) (by
      intro c hc
      left
      rcases mpc_capAngles_cases hc with hc | rfl | rfl
      · exact ⟨(mpcDiamond Θ).min'_le _ (mpc_mem_mpcDiamond.2 hc),
          by linarith [mpc_diamond_lt_pi hc, pi_pos]⟩
      · exact ⟨by linarith [pi_pos], by linarith⟩
      · exact ⟨by linarith [pi_pos], by linarith⟩)
  have hqe : q = (supp K 0, 0) := by
    rw [mpc_supp_neg_pi_div_two, hK.1.2.2.2.2.2.1] at hq1
    have h2 : dot q (uvec 0) = supp K 0 := by
      have := (hq6 0 (by linarith [pi_pos]) hm0).2
      rw [← this]; exact dot_vminus_uvec K 0
    rw [mpc_uvec_neg_pi_div_two] at hq1
    simp only [dot] at hq1
    rw [mpc_dot_uvec_zero] at h2
    ext
    · exact h2
    · simp at hq1; simpa using hq1
  subst hqe
  exact ⟨(hq6 0 (by linarith [pi_pos]) hm0).2, hq, hq4⟩


/-- The corner `C_K⁺(ω) = h_K(ω + π/2) v_ω` of a polygon cap. -/
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
    rw [hK.1.2.2.2.2.1, mpc_dot_uvec_add_pi] at hq2
    linarith
  have hqv : dot q (vvec Θ.ω) = supp K (Θ.ω + π / 2) := by
    rw [← uvec_add_pi_div_two]
    exact hq5 _ (by linarith) (by linarith [pi_pos])
  have hqe : q = supp K (Θ.ω + π / 2) • vvec Θ.ω := by
    have := eq_dot_uvec_smul_add q Θ.ω
    rw [hqω, hqv, zero_smul, zero_add] at this
    exact this
  have hpi : supp K π = -q.1 := by
    rw [← hq5 π (by linarith) (by linarith), mpc_dot_uvec_pi]
  rw [hcp]
  exact ⟨hqe, hq, hq3, hq4, hpi⟩

/-- `o_ω · u_ω = 1`. -/
lemma mpc_oPt_dot_uvec {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) : dot (oPt ω) (uvec ω) = 1 := by
  set a := π / 4 - ω / 2 with ha
  have hω' : ω = π / 2 - 2 * a := by rw [ha]; ring
  have hca : 0 < cos a := cos_pos_of_mem_Ioo ⟨by linarith [hω.1, hω.2, pi_pos], by linarith [hω.1, hω.2, pi_pos]⟩
  simp only [oPt, dot, uvec]
  rw [← ha, hω', cos_pi_div_two_sub, sin_pi_div_two_sub, sin_two_mul, cos_two_mul,
    tan_eq_sin_div_cos]
  field_simp
  nlinarith [sin_sq_add_cos_sq a]

/-- `o_ω · v_ω = tan (π/4 - ω/2)`. -/
lemma mpc_oPt_dot_vvec {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) :
    dot (oPt ω) (vvec ω) = tan (π / 4 - ω / 2) := by
  set a := π / 4 - ω / 2 with ha
  have hω' : ω = π / 2 - 2 * a := by rw [ha]; ring
  have hca : 0 < cos a := cos_pos_of_mem_Ioo ⟨by linarith [hω.1, hω.2, pi_pos], by linarith [hω.1, hω.2, pi_pos]⟩
  simp only [oPt, dot, vvec]
  rw [← ha, hω', cos_pi_div_two_sub, sin_pi_div_two_sub, sin_two_mul, cos_two_mul,
    tan_eq_sin_div_cos]
  field_simp
  nlinarith [sin_sq_add_cos_sq a]

lemma mpc_oPt_snd (ω : ℝ) : (oPt ω).2 = 1 := rfl

/-- For `ω < π/2`, the vertex `o_ω` of `P_ω` lies in every polygon cap. -/
lemma mpc_oPt_mem (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) : oPt Θ.ω ∈ K := by
  have hω0 := mpc_omega_pos Θ
  obtain ⟨q, hq, hq1, hq2, -⟩ := mpc_polycap_corner hK (r := Θ.ω) (s := π / 2) hω
    (by linarith [pi_pos]) (by
      intro c hc
      rcases mpc_capAngles_cases hc with hc | rfl | rfl
      · rcases mpc_diamond_cases hc with h | ⟨s, hs, rfl⟩ | rfl | rfl
        · right; exact ⟨by linarith [(mpc_angles_bounds h).1, pi_pos],
            (mpc_angles_bounds h).2.le⟩
        · left; exact ⟨by linarith [(mpc_angles_bounds hs).1],
            by linarith [(mpc_angles_bounds hs).2, pi_pos]⟩
        · right; exact ⟨by linarith [pi_pos], le_rfl⟩
        · left; exact ⟨le_rfl, by linarith [pi_pos]⟩
      · left; exact ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
      · left; exact ⟨by linarith [pi_pos], by linarith [pi_pos]⟩)
  have : q = oPt Θ.ω := by
    apply mpc_eq_of_dot_eq (a := Θ.ω) (b := π / 2)
    · exact (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])).ne'
    · rw [hq1, hK.1.2.2.1, mpc_oPt_dot_uvec Θ.hω]
    · rw [hq2, hK.1.2.2.2.1, mpc_dot_uvec_pi_div_two, mpc_oPt_snd]
  rwa [← this]

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
    apply mpc_eq_of_dot_eq (a := Θ.ω + π) (b := 3 * π / 2)
    · exact (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])).ne'
    · rw [hq1, hK.1.2.2.2.2.1, dot_zero_left]
    · rw [hq2, hK.1.2.2.2.2.2.1, dot_zero_left]
  subst this
  exact ⟨hq, hq3, hq4⟩

/-- `v_K⁺(3π/2) = (h_K(0), 0)`. -/
lemma mpc_vplus_three_pi_div_two (hK : IsPolygonCap Θ K) : vplus K (3 * π / 2) = (supp K 0, 0) := by
  obtain ⟨q, -, hq1, hq2, hq3, -⟩ := mpc_polycap_corner hK (r := 3 * π / 2) (s := 2 * π)
    (by linarith [pi_pos]) (by linarith [pi_pos]) (by
      intro c hc
      right
      rcases mpc_capAngles_cases hc with hc | rfl | rfl
      · exact ⟨by linarith [(mpc_diamond_bounds hc).1], by linarith [mpc_diamond_lt_pi hc, pi_pos]⟩
      · exact ⟨by linarith [mpc_omega_pos Θ, pi_pos], by linarith [mpc_omega_le Θ]⟩
      · exact ⟨by linarith [pi_pos], le_rfl⟩)
  rw [hq3]
  rw [hK.1.2.2.2.2.2.1, mpc_dot_uvec_three_pi_div_two] at hq1
  have h2 : 2 * π = 0 + 2 * π := by ring
  rw [h2, supp_add_two_pi, uvec_add_two_pi, mpc_dot_uvec_zero] at hq2
  ext
  · exact hq2
  · simp only; linarith

lemma mpc_norm2_pair (x : ℝ) : norm2 (x, 0) = |x| := by
  simp [norm2, dot, Real.sqrt_mul_self_eq_abs]

lemma mpc_norm2_smul_vvec (c t : ℝ) : norm2 (c • vvec t) = |c| := by
  simp only [norm2, dot_smul_left, dot_smul_right, dot_vvec_self, mul_one]
  rw [← sq, Real.sqrt_sq_eq_abs]

/-- The bottom side lengths of a polygon cap with `ω < π/2`. -/
lemma mpc_sigma_bottom_lt (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) :
    sigmaAt K (3 * π / 2) = supp K 0 ∧ 0 < supp K 0 ∧
      sigmaAt K (Θ.ω + π) = supp K (Θ.ω + π / 2) ∧ 0 < supp K (Θ.ω + π / 2) := by
  have hω0 := mpc_omega_pos Θ
  have ho := mpc_oPt_mem hK hω
  have hta : 0 < tan (π / 4 - Θ.ω / 2) :=
    tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  have h0 : 0 < supp K 0 := by
    have := dot_le_supp hK.1.2.1.2.1 ho 0
    rw [mpc_dot_uvec_zero] at this
    have e : (oPt Θ.ω).1 = tan (π / 4 - Θ.ω / 2) := rfl
    linarith
  have h1 : 0 < supp K (Θ.ω + π / 2) := by
    have := dot_le_supp hK.1.2.1.2.1 ho (Θ.ω + π / 2)
    rw [uvec_add_pi_div_two, mpc_oPt_dot_vvec Θ.hω] at this
    linarith
  obtain ⟨-, hO1, hO2⟩ := mpc_origin_corner hK hω
  obtain ⟨hC1, -, -, hC4, -⟩ := mpc_cPlus_eq hK
  refine ⟨?_, h0, ?_, h1⟩
  · rw [(proposition2_1_2 hK.1.2.1 _).1, mpc_vplus_three_pi_div_two hK, hO2, sub_zero,
      mpc_norm2_pair, abs_of_pos h0]
  · rw [(proposition2_1_2 hK.1.2.1 _).1, hO1, hC4, hC1, zero_sub, ← neg_smul,
      mpc_norm2_smul_vvec, abs_neg, abs_of_pos h1]

/-- The bottom side length of a polygon cap with `ω = π/2`. -/
lemma mpc_sigma_bottom_eq (hK : IsPolygonCap Θ K) (hω : Θ.ω = π / 2) :
    sigmaAt K (3 * π / 2) = supp K 0 + supp K π := by
  obtain ⟨hC1, hC2, -, hC4, hC5⟩ := mpc_cPlus_eq hK
  have h3 : Θ.ω + π = 3 * π / 2 := by rw [hω]; ring
  rw [h3] at hC4
  rw [(proposition2_1_2 hK.1.2.1 _).1, mpc_vplus_three_pi_div_two hK, hC4, hC1]
  have hv : vvec Θ.ω = (-1, 0) := by rw [hω]; simp [vvec]
  rw [hv]
  have : ((supp K 0, (0 : ℝ)) - supp K (Θ.ω + π / 2) • ((-1 : ℝ), (0 : ℝ))) =
      (supp K 0 + supp K π, 0) := by
    rw [hC5, hC1, hv]
    ext <;> simp
  rw [this, mpc_norm2_pair, abs_of_nonneg]
  -- the width is nonnegative
  obtain ⟨p, hp⟩ := hK.1.2.1.1
  have e1 := dot_le_supp hK.1.2.1.2.1 hp 0
  have e2 := dot_le_supp hK.1.2.1.2.1 hp π
  rw [mpc_dot_uvec_zero] at e1
  rw [mpc_dot_uvec_pi] at e2
  linarith


/-- **Walk along the upper boundary.** For `s ∈ Θ^◇`,
`v_K⁺(s) - A_K⁻(0) = ∑_{t ∈ Θ^◇, t ≤ s} σ_K(t) v_t`. -/
lemma mpc_walk (hK : IsPolygonCap Θ K) {s : ℝ} (hs : s ∈ mpcDiamond Θ) :
    vplus K s - aMinus K 0 =
      ∑ t ∈ (mpcDiamond Θ).filter (· ≤ s), sigmaAt K t • vvec t := by
  set D := mpcDiamond Θ with hD
  suffices H : ∀ n, ∀ s ∈ D, (D.filter (· < s)).card = n →
      vplus K s - aMinus K 0 = ∑ t ∈ D.filter (· ≤ s), sigmaAt K t • vvec t from
    H _ s hs rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hs hcard
  have hvs : vplus K s = vminus K s + sigmaAt K s • vvec s := (proposition2_1_2 hK.1.2.1 s).2
  by_cases hemp : D.filter (· < s) = ∅
  · have hsmin : D.min' (mpc_mpcDiamond_nonempty Θ) = s := by
      apply le_antisymm (D.min'_le s hs)
      by_contra h
      push Not at h
      have : D.min' (mpc_mpcDiamond_nonempty Θ) ∈ D.filter (· < s) :=
        Finset.mem_filter.2 ⟨D.min'_mem _, h⟩
      rw [hemp] at this
      exact absurd this (Finset.notMem_empty _)
    have hfil : D.filter (· ≤ s) = {s} := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨ht, hts⟩
        rcases lt_or_eq_of_le hts with h | h
        · have : t ∈ D.filter (· < s) := Finset.mem_filter.2 ⟨ht, h⟩
          rw [hemp] at this
          exact absurd this (Finset.notMem_empty _)
        · exact h
      · rintro rfl; exact ⟨hs, le_rfl⟩
    have hA := (mpc_aMinus_eq hK)
    rw [hsmin] at hA
    rw [hfil, Finset.sum_singleton, hvs, hA.1, hA.2.2]
    abel
  · have hne : (D.filter (· < s)).Nonempty := Finset.nonempty_iff_ne_empty.2 hemp
    set r := (D.filter (· < s)).max' hne with hr_def
    have hr : r ∈ D.filter (· < s) := Finset.max'_mem _ _
    obtain ⟨hrD, hrs⟩ := Finset.mem_filter.1 hr
    have hlt : (D.filter (· < r)).card < n := by
      rw [← hcard]
      apply Finset.card_lt_card
      refine ⟨fun t ht => ?_, fun h => ?_⟩
      · obtain ⟨htD, htr⟩ := Finset.mem_filter.1 ht
        exact Finset.mem_filter.2 ⟨htD, htr.trans hrs⟩
      · exact lt_irrefl r (Finset.mem_filter.1 (h hr)).2
    have ihr := ih _ hlt r hrD rfl
    have hsd := mpc_diamond_bounds (mpc_mem_mpcDiamond.1 hs)
    have hrd := mpc_diamond_bounds (mpc_mem_mpcDiamond.1 hrD)
    have hspi := mpc_diamond_lt_pi (mpc_mem_mpcDiamond.1 hs)
    have hrpi := mpc_diamond_lt_pi (mpc_mem_mpcDiamond.1 hrD)
    obtain ⟨q, -, -, -, hq3, hq4, -, -⟩ := mpc_polycap_corner hK (r := r) (s := s) hrs
      (by linarith) (by
        intro c hc
        rcases mpc_capAngles_cases hc with hc | rfl | rfl
        · by_cases hcr : c ≤ r
          · right; exact ⟨by linarith [(mpc_diamond_bounds hc).1, pi_pos], hcr⟩
          · left
            refine ⟨?_, by linarith [mpc_diamond_lt_pi hc, pi_pos]⟩
            by_contra hcs
            push Not at hcs
            exact hcr ((D.filter (· < s)).le_max' c
              (Finset.mem_filter.2 ⟨mpc_mem_mpcDiamond.2 hc, hcs⟩))
        · left; exact ⟨by linarith [mpc_omega_pos Θ], by linarith [mpc_omega_le Θ, pi_pos]⟩
        · left; exact ⟨by linarith, by linarith [pi_pos]⟩)
    have hfil : D.filter (· ≤ s) = insert s (D.filter (· ≤ r)) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨ht, hts⟩
        rcases lt_or_eq_of_le hts with h | h
        · right
          exact ⟨ht, (D.filter (· < s)).le_max' t (Finset.mem_filter.2 ⟨ht, h⟩)⟩
        · left; exact h
      · rintro (rfl | ⟨ht, htr⟩)
        · exact ⟨hs, le_rfl⟩
        · exact ⟨ht, htr.trans hrs.le⟩
    have hnot : s ∉ D.filter (· ≤ r) := by
      intro h
      exact absurd (Finset.mem_filter.1 h).2 (not_le.2 hrs)
    rw [hfil, Finset.sum_insert hnot, ← ihr, hvs, hq4, ← hq3]
    abel

/-- `C_K⁺(ω) - A_K⁻(0) = ∑_{t ∈ Θ^◇} σ_K(t) v_t`. -/
lemma mpc_walk_total (hK : IsPolygonCap Θ K) :
    cPlus K Θ.ω - aMinus K 0 = ∑ t ∈ mpcDiamond Θ, sigmaAt K t • vvec t := by
  have hM := Finset.max'_mem (mpcDiamond Θ) (mpc_mpcDiamond_nonempty Θ)
  rw [← (mpc_cPlus_eq hK).2.2.1, mpc_walk hK hM]
  congr 1
  ext t
  simp only [Finset.mem_filter, and_iff_left_iff_imp]
  exact fun ht => (mpcDiamond Θ).le_max' t ht

end Corners

/-! ### The caps `𝓒_Θ(h)` and the height increments (Lemma 3.4.8) -/

section HeightIncrement

open Filter Topology

/-! ### The cap `𝓒_Θ(h)` of a height function -/

lemma mpc_mem_capH (Θ : AngleSet) (h : ℝ → ℝ) (p : ℝ × ℝ) :
    p ∈ capH Θ h ↔ (∀ s ∈ Θ.diamond, dot p (uvec s) ≤ h s) ∧
      h Θ.ω - 1 ≤ dot p (uvec Θ.ω) ∧ h (π / 2) - 1 ≤ dot p (uvec (π / 2)) := by
  simp only [capH, paraH, mem_inter_iff, mem_iInter, mem_insert_iff, mem_singleton_iff,
    halfMinus, halfPlus, mem_ofPred_eq, AngleSet.diamond, mem_union, Finset.mem_coe, mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, (h1 Θ.ω (Or.inl rfl)).2, (h1 (π / 2) (Or.inr rfl)).2⟩
    rintro s ((hs | ⟨u, hu, rfl⟩) | (rfl | rfl))
    · exact h2 s (Or.inl hs)
    · exact h2 _ (Or.inr ⟨u, hu, rfl⟩)
    · exact (h1 _ (Or.inl rfl)).1
    · exact (h1 _ (Or.inr rfl)).1
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, fun s hs => h1 s (Or.inl hs)⟩
    rintro s (rfl | rfl)
    · exact ⟨h1 _ (Or.inr (Or.inl rfl)), h2⟩
    · exact ⟨h1 _ (Or.inr (Or.inr rfl)), h3⟩

open Classical in
/-- `𝓒_Θ(h)` is an intersection of closed half-planes with normal angles in `Θ^◇ ∪ {ω + π, 3π/2}`. -/
lemma mpc_capH_halfPlaneInter (Θ : AngleSet) (h : ℝ → ℝ) :
    IsHalfPlaneInter (capH Θ h) Θ.capAngles := by
  refine ⟨Θ.capAngles, fun i => i.1,
    fun i => if i.1 ∈ Θ.diamond then h i.1 else 1 - h (i.1 - π), fun i => i.2, ?_⟩
  ext p
  rw [mpc_mem_capH, mem_iInter]
  have hω := mpc_omega_pos Θ
  have hω' := mpc_omega_le Θ
  have hnd1 : Θ.ω + π ∉ Θ.diamond := fun h => by linarith [mpc_diamond_lt_pi h, pi_pos]
  have hnd2 : 3 * π / 2 ∉ Θ.diamond := fun h => by linarith [mpc_diamond_lt_pi h, pi_pos]
  constructor
  · rintro ⟨h1, h2, h3⟩ ⟨c, hc⟩
    simp only [halfMinus, mem_ofPred_eq]
    rcases mpc_capAngles_cases hc with hc' | rfl | rfl
    · rw [ite_eq_left hc']; exact h1 c hc'
    · rw [ite_eq_right hnd1, mpc_dot_uvec_add_pi, add_sub_cancel_right]; linarith
    · rw [ite_eq_right hnd2, mpc_dot_uvec_three_pi_div_two]
      rw [mpc_dot_uvec_pi_div_two] at h3
      have : 3 * π / 2 - π = π / 2 := by ring
      rw [this]; linarith
  · intro hall
    have e := fun c (hc : c ∈ Θ.capAngles) => hall ⟨c, hc⟩
    simp only [halfMinus, mem_ofPred_eq] at e
    refine ⟨fun s hs => ?_, ?_, ?_⟩
    · have := e s (Or.inl hs); rwa [ite_eq_left hs] at this
    · have := e (Θ.ω + π) (Or.inr (Or.inl rfl))
      rw [ite_eq_right hnd1, mpc_dot_uvec_add_pi, add_sub_cancel_right] at this
      linarith
    · have := e (3 * π / 2) (Or.inr (Or.inr rfl))
      rw [ite_eq_right hnd2, mpc_dot_uvec_three_pi_div_two] at this
      have h32 : 3 * π / 2 - π = π / 2 := by ring
      rw [h32] at this
      rw [mpc_dot_uvec_pi_div_two]; linarith

lemma mpc_isClosed_halfMinus (t c : ℝ) : IsClosed (halfMinus t c) :=
  isClosed_le (by simp only [dot]; fun_prop) continuous_const

lemma mpc_convex_halfMinus (t c : ℝ) : Convex ℝ (halfMinus t c) := by
  intro x hx y hy a b ha hb hab
  simp only [halfMinus, mem_ofPred_eq] at *
  rw [dot_add_left, dot_smul_left, dot_smul_left]
  have e : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

lemma mpc_isClosed_of_halfPlaneInter {X : Set (ℝ × ℝ)} {A : Set ℝ}
    (hX : IsHalfPlaneInter X A) : IsClosed X := by
  obtain ⟨ι, t, c, -, rfl⟩ := hX
  exact isClosed_iInter fun i => mpc_isClosed_halfMinus _ _

lemma mpc_convex_of_halfPlaneInter {X : Set (ℝ × ℝ)} {A : Set ℝ}
    (hX : IsHalfPlaneInter X A) : Convex ℝ X := by
  obtain ⟨ι, t, c, -, rfl⟩ := hX
  exact convex_iInter fun i => mpc_convex_halfMinus _ _

lemma mpc_halfPlaneInter_mono {X : Set (ℝ × ℝ)} {A B : Set ℝ} (hX : IsHalfPlaneInter X A)
    (hAB : A ⊆ B) : IsHalfPlaneInter X B := by
  obtain ⟨ι, t, c, ht, rfl⟩ := hX
  exact ⟨ι, t, c, fun i => hAB (ht i), rfl⟩

lemma mpc_capAngles_subset (Θ : AngleSet) :
    Θ.capAngles ⊆ jSet Θ.ω ∪ {Θ.ω + π, 3 * π / 2} := by
  intro c hc
  have hω := mpc_omega_pos Θ
  rcases mpc_capAngles_cases hc with hc | rfl | rfl
  · left
    rcases mpc_diamond_cases hc with h | ⟨s, hs, rfl⟩ | rfl | rfl
    · have := mpc_angles_bounds h; left; exact ⟨this.1.le, this.2.le⟩
    · have := mpc_angles_bounds hs; right; constructor <;> linarith
    · left; exact ⟨hω.le, le_rfl⟩
    · right; constructor <;> linarith
  · right; exact Or.inl rfl
  · right; exact Or.inr rfl

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

lemma mpc_isBounded_capH (Θ : AngleSet) (h : ℝ → ℝ) : Bornology.IsBounded (capH Θ h) := by
  obtain ⟨t, ht⟩ := Θ.nonempty
  have htb := mpc_angles_bounds ht
  have hω := mpc_omega_le Θ
  apply mpc_isBounded_of_strip htb.1 (by linarith) (a := h (π / 2) - 1) (b := h (π / 2))
    (c₁ := h t) (c₂ := h (t + π / 2))
  intro p hp
  rw [mpc_mem_capH] at hp
  obtain ⟨h1, -, h3⟩ := hp
  have hπ2 : π / 2 ∈ Θ.diamond := Or.inr (Or.inr rfl)
  have e := h1 _ hπ2
  rw [mpc_dot_uvec_pi_div_two] at e h3
  exact ⟨h3, e, h1 t (Or.inl (Or.inl ht)), h1 _ (Or.inl (Or.inr ⟨t, ht, rfl⟩))⟩

lemma mpc_isCompact_capH (Θ : AngleSet) (h : ℝ → ℝ) : IsCompact (capH Θ h) :=
  Metric.isCompact_of_isClosed_isBounded
    (mpc_isClosed_of_halfPlaneInter (mpc_capH_halfPlaneInter Θ h)) (mpc_isBounded_capH Θ h)

/-! ### Edges of positive length -/

/-- The midpoint of an edge of positive length lies strictly inside every other supporting
half-plane that is not parallel to the edge. -/
lemma mpc_midpoint_strict {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {s : ℝ}
    (hσ : 0 < sigmaAt K s) {r : ℝ} (hr : sin (r - s) ≠ 0) :
    (1 / 2 : ℝ) • (vplus K s + vminus K s) ∈ K ∧
      dot ((1 / 2 : ℝ) • (vplus K s + vminus K s)) (uvec s) = supp K s ∧
      dot ((1 / 2 : ℝ) • (vplus K s + vminus K s)) (uvec r) < supp K r := by
  have hp := vplus_mem_edge hK s
  have hm := vminus_mem_edge hK s
  have hmem : (1 / 2 : ℝ) • (vplus K s + vminus K s) ∈ K := by
    have := hK.2.2 hp.1 hm.1 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    rw [smul_add]
    exact this
  refine ⟨hmem, ?_, ?_⟩
  · rw [dot_smul_left, dot_add_left, dot_vplus_uvec, dot_vminus_uvec]; ring
  · rcases lt_or_eq_of_le (dot_le_supp hK.2.1 hmem r) with h | h
    · exact h
    · exfalso
      have h1 := dot_le_supp hK.2.1 hp.1 r
      have h2 := dot_le_supp hK.2.1 hm.1 r
      rw [dot_smul_left, dot_add_left] at h
      have h3 : dot (vplus K s - vminus K s) (uvec r) = 0 := by
        rw [dot_sub_left]; linarith
      rw [(proposition2_1_2 hK s).2, add_sub_cancel_left, dot_smul_left,
        dot_vvec_uvec'] at h3
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd h4 hσ.ne'
      · exact hr h4

/-- A compact set squeezed between `l(s, c - 1)` and `l(s, c)` and touching both has width one. -/
lemma mpc_width_eq_one {S : Set (ℝ × ℝ)} (hS : IsCompact S) {s c : ℝ}
    (hsub : ∀ p ∈ S, c - 1 ≤ dot p (uvec s) ∧ dot p (uvec s) ≤ c) {P Q : ℝ × ℝ}
    (hP : P ∈ S) (hPs : dot P (uvec s) = c) (hQ : Q ∈ S) (hQs : dot Q (uvec s) = c - 1) :
    width S s = 1 := by
  have h1 : supp S s = c := by
    apply le_antisymm
    · apply csSup_le ⟨_, mem_image_of_mem _ hP⟩
      rintro _ ⟨p, hp, rfl⟩
      exact (hsub p hp).2
    · rw [← hPs]; exact dot_le_supp hS hP s
  have h2 : supp S (s + π) = 1 - c := by
    apply le_antisymm
    · apply csSup_le ⟨_, mem_image_of_mem _ hP⟩
      rintro _ ⟨p, hp, rfl⟩
      dsimp only
      rw [mpc_dot_uvec_add_pi]
      linarith [(hsub p hp).1]
    · have := dot_le_supp hS hQ (s + π)
      rw [mpc_dot_uvec_add_pi, hQs] at this
      linarith
  rw [width, h1, h2]; ring


/-- A set squeezed between `S` and a compact `T` along a direction has the same support value. -/
lemma mpc_supp_eq_of_squeeze {S T : Set (ℝ × ℝ)} (hST : S ⊆ T) (hS : S.Nonempty)
    (hT : IsCompact T) {t c : ℝ} (hSt : supp S t = c) (hT' : ∀ p ∈ T, dot p (uvec t) ≤ c) :
    supp T t = c := by
  apply le_antisymm
  · apply csSup_le (hS.mono hST |>.image _)
    rintro _ ⟨p, hp, rfl⟩
    exact hT' p hp
  · rw [← hSt]; exact supp_mono hST hS hT t

/-- Raising `h_K(t)` for `t ∈ Θ ∪ (Θ + π/2)` gives a polygon cap. -/
lemma mpc_capH_update_inner {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) {t : ℝ}
    (htω : t ≠ Θ.ω) (htπ : t ≠ π / 2) {ε : ℝ} (hε : 0 ≤ ε) :
    IsPolygonCap Θ (capH Θ (Function.update (supp K) t (supp K t + ε))) := by
  set h' := Function.update (supp K) t (supp K t + ε) with hh'
  have hcap := hK.1
  have hω1 : h' Θ.ω = 1 := by rw [hh', Function.update_of_ne htω.symm]; exact hcap.2.2.1
  have hπ1 : h' (π / 2) = 1 := by rw [hh', Function.update_of_ne htπ.symm]; exact hcap.2.2.2.1
  have hle : ∀ r, supp K r ≤ h' r := by
    intro r
    rw [hh', Function.update_apply]
    split_ifs with h
    · rw [h]; linarith
    · exact le_rfl
  have hKsub : K ⊆ capH Θ h' := by
    intro p hp
    rw [mpc_polycap_mem_iff hK] at hp
    obtain ⟨h1, h2, h3⟩ := hp
    rw [mpc_mem_capH, hω1, hπ1]
    refine ⟨fun s hs => (h1 s hs).trans (hle s), ?_, ?_⟩
    · have : 0 ≤ dot p (uvec Θ.ω) := h2; linarith
    · have : 0 ≤ dot p (uvec (π / 2)) := h3; linarith
  have hc := mpc_isCompact_capH Θ h'
  have hne : K.Nonempty := hcap.2.1.1
  have hmem := fun p => (mpc_mem_capH Θ h' p).1
  refine ⟨⟨Θ.hω, ⟨hne.mono hKsub, hc,
    mpc_convex_of_halfPlaneInter (mpc_capH_halfPlaneInter Θ h')⟩, ?_, ?_, ?_, ?_,
    mpc_halfPlaneInter_mono (mpc_capH_halfPlaneInter Θ h') (mpc_capAngles_subset Θ)⟩,
    mpc_capH_halfPlaneInter Θ h'⟩
  · apply mpc_supp_eq_of_squeeze hKsub hne hc hcap.2.2.1
    intro p hp
    have := (hmem p hp).1 Θ.ω (Or.inr (Or.inl rfl))
    rwa [hω1] at this
  · apply mpc_supp_eq_of_squeeze hKsub hne hc hcap.2.2.2.1
    intro p hp
    have := (hmem p hp).1 (π / 2) (Or.inr (Or.inr rfl))
    rwa [hπ1] at this
  · apply mpc_supp_eq_of_squeeze hKsub hne hc hcap.2.2.2.2.1
    intro p hp
    have := (hmem p hp).2.1
    rw [hω1] at this
    rw [mpc_dot_uvec_add_pi]
    linarith
  · apply mpc_supp_eq_of_squeeze hKsub hne hc hcap.2.2.2.2.2.1
    intro p hp
    have := (hmem p hp).2.2
    rw [hπ1, mpc_dot_uvec_pi_div_two] at this
    rw [mpc_dot_uvec_three_pi_div_two]
    linarith


/-- Membership in `𝓒_Θ(h⁺)` for `h⁺ = h_K` raised by `ε` at `t ∈ {ω, π/2}`. -/
lemma mpc_mem_capH_update {Θ : AngleSet} {h : ℝ → ℝ} {t ε : ℝ} {P : ℝ × ℝ}
    (ha : ∀ s ∈ Θ.diamond, s ≠ t → dot P (uvec s) ≤ h s)
    (hb : dot P (uvec t) ≤ h t + ε) (hc : h t + ε - 1 ≤ dot P (uvec t))
    (hd : ∀ s ∈ ({Θ.ω, π / 2} : Set ℝ), s ≠ t → h s - 1 ≤ dot P (uvec s)) :
    P ∈ capH Θ (Function.update h t (h t + ε)) := by
  rw [mpc_mem_capH]
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · by_cases hst : s = t
    · subst hst; rw [Function.update_self]; exact hb
    · rw [Function.update_of_ne hst]; exact ha s hs hst
  · by_cases hst : Θ.ω = t
    · rw [hst, Function.update_self]; exact hc
    · rw [Function.update_of_ne hst]; exact hd _ (Or.inl rfl) hst
  · by_cases hst : π / 2 = t
    · rw [hst, Function.update_self]; exact hc
    · rw [Function.update_of_ne hst]; exact hd _ (Or.inr rfl) hst

lemma mpc_capH_update_bounds {Θ : AngleSet} {h : ℝ → ℝ} {t ε : ℝ} {s : ℝ}
    (hs : s ∈ ({Θ.ω, π / 2} : Set ℝ)) {p : ℝ × ℝ}
    (hp : p ∈ capH Θ (Function.update h t (h t + ε))) :
    Function.update h t (h t + ε) s - 1 ≤ dot p (uvec s) ∧
      dot p (uvec s) ≤ Function.update h t (h t + ε) s := by
  rw [mpc_mem_capH] at hp
  rcases hs with rfl | rfl
  · exact ⟨hp.2.1, hp.1 _ (Or.inr (Or.inl rfl))⟩
  · exact ⟨hp.2.2, hp.1 _ (Or.inr (Or.inr rfl))⟩

lemma mpc_cos_nonneg_of_bottom {Θ : AngleSet} {s t : ℝ} (hs : s ∈ ({Θ.ω, π / 2} : Set ℝ))
    (ht : t ∈ ({Θ.ω, π / 2} : Set ℝ)) : 0 ≤ cos (t - s) := by
  have hω0 := mpc_omega_pos Θ
  have hω2 := mpc_omega_le Θ
  apply cos_nonneg_of_neg_pi_div_two_le_of_le <;>
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> linarith [pi_pos]

/-- **Lemma 3.4.8**, case `t ∈ {ω, π/2}`. -/
lemma mpc_capH_update_bottom {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) {t : ℝ}
    (ht : t ∈ ({Θ.ω, π / 2} : Set ℝ)) (hσ : 0 < sigmaAt K t) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀,
      IsPolygonCapTranslate Θ (capH Θ (Function.update (supp K) t (supp K t + ε))) := by
  have hcap := hK.1
  have hKb := hcap.2.1
  have hω0 := mpc_omega_pos Θ
  have hω2 := mpc_omega_le Θ
  have htd : t ∈ Θ.diamond := by
    rcases ht with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have ht1 : supp K t = 1 := by
    rcases ht with rfl | rfl
    · exact hcap.2.2.1
    · exact hcap.2.2.2.1
  have htπ : supp K (t + π) = 0 := by
    rcases ht with rfl | rfl
    · exact hcap.2.2.2.2.1
    · rw [show π / 2 + π = 3 * π / 2 by ring]; exact hcap.2.2.2.2.2.1
  have htb : 0 < t ∧ t ≤ π / 2 := by
    rcases ht with rfl | rfl
    · exact ⟨hω0, hω2⟩
    · exact ⟨by linarith [pi_pos], le_rfl⟩
  have hfan := mpc_cap_subset_fan hcap
  -- the opposite side has positive length
  have hσπ : 0 < sigmaAt K (t + π) := by
    rcases lt_or_eq_of_le hω2 with hlt | heq
    · obtain ⟨h1, h2, h3, h4⟩ := mpc_sigma_bottom_lt hK hlt
      rcases ht with rfl | rfl
      · rw [h3]; exact h4
      · rw [show π / 2 + π = 3 * π / 2 by ring, h1]; exact h2
    · have ht' : t = π / 2 := by rcases ht with rfl | rfl; exacts [heq, rfl]
      subst ht'
      rw [show π / 2 + π = 3 * π / 2 by ring, mpc_sigma_bottom_eq hK heq]
      have e := (proposition2_1_2 hKb (π / 2)).2
      have hp := (vplus_mem_edge hKb (π / 2)).1
      have hm := (vminus_mem_edge hKb (π / 2)).1
      have e1 := dot_le_supp hKb.2.1 hm 0
      have e2 := dot_le_supp hKb.2.1 hp π
      rw [mpc_dot_uvec_zero] at e1
      rw [mpc_dot_uvec_pi] at e2
      have : (vplus K (π / 2)).1 = (vminus K (π / 2)).1 - sigmaAt K (π / 2) := by
        rw [e]; simp [vvec]; ring
      linarith
  -- the midpoints of the two opposite sides
  set m := (1 / 2 : ℝ) • (vplus K t + vminus K t) with hm_def
  set m' := (1 / 2 : ℝ) • (vplus K (t + π) + vminus K (t + π)) with hm'_def
  have hsin1 : sin (t + π / 2 - t) ≠ 0 := by
    rw [show t + π / 2 - t = π / 2 by ring, sin_pi_div_two]; norm_num
  have hsin2 : sin (t + π / 2 - (t + π)) ≠ 0 := by
    rw [show t + π / 2 - (t + π) = -(π / 2) by ring, sin_neg, sin_pi_div_two]; norm_num
  obtain ⟨hmK, hmt, -⟩ := mpc_midpoint_strict hKb hσ hsin1
  obtain ⟨hm'K, hm't, -⟩ := mpc_midpoint_strict hKb hσπ hsin2
  rw [← hm_def] at hmK hmt
  rw [← hm'_def] at hm'K hm't
  rw [ht1] at hmt
  rw [htπ, mpc_dot_uvec_add_pi] at hm't
  have hm't' : dot m' (uvec t) = 0 := by linarith
  have hslack : ∀ s ∈ Θ.diamond, s ≠ t →
      dot m (uvec s) < supp K s ∧ dot m' (uvec s) < supp K s := by
    intro s hs hst
    have hsb := mpc_diamond_bounds hs
    have hsπ := mpc_diamond_lt_pi hs
    have hsin : sin (s - t) ≠ 0 := by
      intro h0
      rcases lt_trichotomy s t with h | h | h
      · exact absurd h0 (sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)).ne
      · exact hst h
      · exact absurd h0 (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
    refine ⟨(mpc_midpoint_strict hKb hσ hsin).2.2, (mpc_midpoint_strict hKb hσπ ?_).2.2⟩
    rw [show s - (t + π) = (s - t) - π by ring, sin_sub_pi]
    exact neg_ne_zero.2 hsin
  -- the bottom point for the other direction (when `ω < π/2`)
  obtain ⟨c₀, hc₀, hQ⟩ : ∃ c₀ > 0, Θ.ω < π / 2 → ∃ Q ∈ K,
      (∀ s ∈ ({Θ.ω, π / 2} : Set ℝ), s ≠ t → dot Q (uvec s) = 0) ∧ c₀ ≤ dot Q (uvec t) := by
    rcases lt_or_eq_of_le hω2 with hlt | heq
    · obtain ⟨-, h2, -, h4⟩ := mpc_sigma_bottom_lt hK hlt
      have hcos : 0 < cos Θ.ω := cos_pos_of_mem_Ioo ⟨by linarith, hlt⟩
      rcases ht with rfl | rfl
      · refine ⟨supp K 0 * cos Θ.ω, by positivity, fun _ => ⟨_, (mpc_aMinus_eq hK).2.1, ?_, ?_⟩⟩
        · rintro s (rfl | rfl) hst
          · exact absurd rfl hst
          · rw [mpc_dot_uvec_pi_div_two]
        · simp [dot, uvec]
      · obtain ⟨hC1, hC2, -⟩ := mpc_cPlus_eq hK
        refine ⟨supp K (Θ.ω + π / 2) * cos Θ.ω, by positivity, fun _ => ⟨_, hC2, ?_, ?_⟩⟩
        · rintro s (rfl | rfl) hst
          · rw [hC1, dot_smul_left, dot_vvec_uvec', sub_self, sin_zero, mul_zero]
          · exact absurd rfl hst
        · rw [hC1, dot_smul_left, dot_vvec_uvec']
          rw [show π / 2 - Θ.ω = π / 2 - Θ.ω by ring, sin_pi_div_two_sub]
    · exact ⟨1, one_pos, fun h => absurd heq h.ne⟩
  -- smallness of `ε`
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), (∀ s ∈ mpcDiamond Θ, s ≠ t →
      dot m (uvec s) + ε * cos (t - s) ≤ supp K s ∧
        dot m' (uvec s) + ε * cos (t - s) ≤ supp K s) ∧ ε < 1 ∧ ε < c₀ := by
    refine Filter.Eventually.and ?_ (Filter.Eventually.and (gt_mem_nhds one_pos)
      (gt_mem_nhds hc₀))
    rw [Filter.eventually_all_finset]
    intro s hs
    by_cases hst : s = t
    · exact Filter.Eventually.of_forall fun _ h => absurd hst h
    · obtain ⟨h1, h2⟩ := hslack s (mpc_mem_mpcDiamond.1 hs) hst
      have c1 : Tendsto (fun ε : ℝ => dot m (uvec s) + ε * cos (t - s)) (𝓝 0)
          (𝓝 (dot m (uvec s))) := by
        have hc : Continuous (fun ε : ℝ => dot m (uvec s) + ε * cos (t - s)) := by fun_prop
        simpa using hc.tendsto 0
      have c2 : Tendsto (fun ε : ℝ => dot m' (uvec s) + ε * cos (t - s)) (𝓝 0)
          (𝓝 (dot m' (uvec s))) := by
        have hc : Continuous (fun ε : ℝ => dot m' (uvec s) + ε * cos (t - s)) := by fun_prop
        simpa using hc.tendsto 0
      filter_upwards [c1.eventually (gt_mem_nhds h1), c2.eventually (gt_mem_nhds h2)]
        with ε e1 e2 _
      exact ⟨e1.le, e2.le⟩
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ / 2, by positivity, fun ε hε => ?_⟩
  have hεδ : dist ε 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε.1]; linarith [hε.2]
  obtain ⟨hεs, hε1, hεc⟩ := hδP hεδ
  have hε0 := hε.1
  set h' := Function.update (supp K) t (supp K t + ε) with hh'
  have hduu : dot (uvec t) (uvec t) = 1 := dot_uvec_self t
  -- the two points in the direction `t`
  have hT : m + ε • uvec t ∈ capH Θ h' := by
    apply mpc_mem_capH_update
    · intro s hs hst
      rw [dot_add_left, dot_smul_left ε (uvec t) (uvec s), dot_uvec_uvec]
      exact (hεs s (mpc_mem_mpcDiamond.2 hs) hst).1
    · rw [dot_add_left, dot_smul_left ε (uvec t) (uvec t), hduu, hmt, ht1]; linarith
    · rw [dot_add_left, dot_smul_left ε (uvec t) (uvec t), hduu, hmt, ht1]; linarith
    · intro s hs hst
      rw [dot_add_left, dot_smul_left ε (uvec t) (uvec s), dot_uvec_uvec]
      have e1 : 0 ≤ dot m (uvec s) := by
        rcases hs with rfl | rfl
        · exact (hfan hmK).1
        · exact (hfan hmK).2
      have e2 := mpc_cos_nonneg_of_bottom hs ht
      have e3 : supp K s = 1 := by
        rcases hs with rfl | rfl
        · exact hcap.2.2.1
        · exact hcap.2.2.2.1
      rw [e3]; nlinarith
  have hB : m' + ε • uvec t ∈ capH Θ h' := by
    apply mpc_mem_capH_update
    · intro s hs hst
      rw [dot_add_left, dot_smul_left ε (uvec t) (uvec s), dot_uvec_uvec]
      exact (hεs s (mpc_mem_mpcDiamond.2 hs) hst).2
    · rw [dot_add_left, dot_smul_left ε (uvec t) (uvec t), hduu, hm't', ht1]; linarith
    · rw [dot_add_left, dot_smul_left ε (uvec t) (uvec t), hduu, hm't', ht1]; linarith
    · intro s hs hst
      rw [dot_add_left, dot_smul_left ε (uvec t) (uvec s), dot_uvec_uvec]
      have e1 : 0 ≤ dot m' (uvec s) := by
        rcases hs with rfl | rfl
        · exact (hfan hm'K).1
        · exact (hfan hm'K).2
      have e2 := mpc_cos_nonneg_of_bottom hs ht
      have e3 : supp K s = 1 := by
        rcases hs with rfl | rfl
        · exact hcap.2.2.1
        · exact hcap.2.2.2.1
      rw [e3]; nlinarith
  have hc := mpc_isCompact_capH Θ h'
  have hwt : width (capH Θ h') t = 1 := by
    refine mpc_width_eq_one hc (c := h' t) (fun p hp => mpc_capH_update_bounds ht hp) hT ?_ hB ?_
    · rw [hh', Function.update_self, dot_add_left, dot_smul_left ε (uvec t) (uvec t), hduu, hmt, ht1]; ring
    · rw [hh', Function.update_self, dot_add_left, dot_smul_left ε (uvec t) (uvec t), hduu, hm't', ht1]; ring
  have hw : ∀ s ∈ ({Θ.ω, π / 2} : Set ℝ), width (capH Θ h') s = 1 := by
    intro s hs
    by_cases hst : s = t
    · rw [hst]; exact hwt
    · -- the other direction, `ω < π/2`
      have hlt : Θ.ω < π / 2 := by
        rcases lt_or_eq_of_le hω2 with h | h
        · exact h
        · exfalso; apply hst
          rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp_all
      obtain ⟨Q, hQK, hQ1, hQ2⟩ := hQ hlt
      have hs1 : supp K s = 1 := by
        rcases hs with rfl | rfl
        · exact hcap.2.2.1
        · exact hcap.2.2.2.1
      have ho := mpc_oPt_mem hK hlt
      have hos : ∀ r ∈ ({Θ.ω, π / 2} : Set ℝ), dot (oPt Θ.ω) (uvec r) = 1 := by
        rintro r (rfl | rfl)
        · exact mpc_oPt_dot_uvec Θ.hω
        · rw [mpc_dot_uvec_pi_div_two]; rfl
      have hOin : oPt Θ.ω ∈ capH Θ h' := by
        apply mpc_mem_capH_update
        · intro r hr _; exact dot_le_supp hKb.2.1 ho r
        · have := dot_le_supp hKb.2.1 ho t; linarith
        · rw [hos t ht, ht1]; linarith
        · intro r hr _
          rw [hos r hr]
          have := dot_le_supp hKb.2.1 ho r
          rcases hr with rfl | rfl
          · rw [hcap.2.2.1]; norm_num
          · rw [hcap.2.2.2.1]; norm_num
      have hQin : Q ∈ capH Θ h' := by
        apply mpc_mem_capH_update
        · intro r hr _; exact dot_le_supp hKb.2.1 hQK r
        · have := dot_le_supp hKb.2.1 hQK t; linarith
        · rw [ht1]; linarith
        · intro r hr hrt
          rw [hQ1 r hr hrt]
          rcases hr with rfl | rfl
          · rw [hcap.2.2.1]; norm_num
          · rw [hcap.2.2.2.1]; norm_num
      refine mpc_width_eq_one hc (c := h' s) (fun p hp => mpc_capH_update_bounds hs hp) hOin ?_
        hQin ?_
      · rw [hh', Function.update_of_ne hst, hs1, hos s hs]
      · rw [hh', Function.update_of_ne hst, hs1, hQ1 s hs hst]; ring
  apply (proposition3_3_1).2
  refine ⟨⟨⟨_, hT⟩, hc, mpc_convex_of_halfPlaneInter (mpc_capH_halfPlaneInter Θ h')⟩,
    hw _ (Or.inl rfl), hw _ (Or.inr rfl), mpc_capH_halfPlaneInter Θ h'⟩

end HeightIncrement

/-! ### The polyline as the graph of a piecewise linear function (Theorem 3.4.4) -/

section Polyline

open Filter Topology

/-! ### Lines as graphs -/

/-- The height at abscissa `x` of the line `l(s, c)` (for `sin s ≠ 0`). -/
noncomputable def mpcLineY (s c x : ℝ) : ℝ := (c - x * cos s) / sin s

lemma mpc_dot_lt_iff {s c : ℝ} (hs : 0 < sin s) (p : ℝ × ℝ) :
    dot p (uvec s) < c ↔ p.2 < mpcLineY s c p.1 := by
  simp only [dot, uvec, mpcLineY]
  rw [lt_div_iff₀ hs]
  constructor <;> intro h <;> linarith

lemma mpc_dot_le_iff {s c : ℝ} (hs : 0 < sin s) (p : ℝ × ℝ) :
    dot p (uvec s) ≤ c ↔ p.2 ≤ mpcLineY s c p.1 := by
  simp only [dot, uvec, mpcLineY]
  rw [le_div_iff₀ hs]
  constructor <;> intro h <;> linarith

lemma mpc_dot_eq_iff {s c : ℝ} (hs : 0 < sin s) (p : ℝ × ℝ) :
    dot p (uvec s) = c ↔ p.2 = mpcLineY s c p.1 := by
  simp only [dot, uvec, mpcLineY]
  rw [eq_div_iff hs.ne']
  constructor <;> intro h <;> linarith

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

lemma mpc_lt_mpcTop_iff (Θ : AngleSet) (K : Set (ℝ × ℝ)) (x y : ℝ) :
    y < mpcTop Θ K x ↔ ∃ t ∈ Θ.angles, y < mpcL K t x ∧ y < mpcL K (t + π / 2) x := by
  rw [mpcTop, Finset.lt_sup'_iff]
  simp only [lt_min_iff]

section CapGraphs

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

lemma mpc_mpcL_pi_div_two (hK : IsPolygonCap Θ K) (x : ℝ) : mpcL K (π / 2) x = 0 := by
  simp [mpcL, mpcLineY, hK.1.2.2.2.1]

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
    have := mpc_dot_lt_iff hω (c := 0) p
    rw [mpcL, hK.1.2.2.1, sub_self]
    constructor
    · intro h; by_contra h'; push Not at h'; linarith [this.2 h']
    · intro h; by_contra h'; push Not at h'; linarith [this.1 h']
  have e2 : (0 ≤ dot p (uvec (π / 2))) ↔ mpcL K (π / 2) p.1 ≤ p.2 := by
    rw [mpc_mpcL_pi_div_two hK, mpc_dot_uvec_pi_div_two]
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
  constructor
  · rintro ⟨h1, t, ht, hq⟩
    rw [mpc_qMinus_eq ht] at hq
    exact ⟨h1, t, ht, hq⟩
  · rintro ⟨h1, t, ht, hq⟩
    refine ⟨h1, t, ht, ?_⟩
    rw [mpc_qMinus_eq ht]
    exact hq

lemma mpc_fan_diff_eq (hK : IsPolygonCap Θ K) :
    fan Θ.ω \ polyNiche Θ K = {p | mpcG Θ K p.1 ≤ p.2} := by
  rw [mpc_fan_eq hK, mpc_polyNiche_eq hK]
  ext p
  simp only [Set.mem_sdiff, mem_ofPred_eq, not_and, not_lt, mpcG, max_le_iff]
  exact ⟨fun h => ⟨h.1, h.2 h.1⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩

end CapGraphs

/-- The frontier of the epigraph of a continuous function is its graph. -/
lemma mpc_frontier_epigraph {G : ℝ → ℝ} (hG : Continuous G) :
    frontier {p : ℝ × ℝ | G p.1 ≤ p.2} = {p | p.2 = G p.1} := by
  have hcl : IsClosed {p : ℝ × ℝ | G p.1 ≤ p.2} :=
    isClosed_le (hG.comp continuous_fst) continuous_snd
  ext p
  rw [frontier, hcl.closure_eq, Set.mem_sdiff, mem_ofPred_eq, mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    rcases lt_or_eq_of_le h1 with h | h
    · exfalso; apply h2
      have hop : IsOpen {q : ℝ × ℝ | G q.1 < q.2} :=
        isOpen_lt (hG.comp continuous_fst) continuous_snd
      have hsub : {q : ℝ × ℝ | G q.1 < q.2} ⊆ interior {q : ℝ × ℝ | G q.1 ≤ q.2} :=
        interior_maximal (fun q (hq : G q.1 < q.2) => le_of_lt hq) hop
      exact hsub h
    · exact h.symm
  · intro h
    refine ⟨h.ge, fun hint => ?_⟩
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
    have hq : (p.1, p.2 - ε / 2) ∈ Metric.ball p ε := by
      rw [Metric.mem_ball, Prod.dist_eq]
      simp only [dist_self, Real.dist_eq]
      rw [max_lt_iff]
      refine ⟨hε, ?_⟩
      rw [show p.2 - ε / 2 - p.2 = -(ε / 2) by ring, abs_neg, abs_of_pos (half_pos hε)]
      linarith
    have := hball hq
    simp only [mem_ofPred_eq] at this
    linarith


section Boundary

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

lemma mpc_cPlus_coords (hK : IsPolygonCap Θ K) :
    (cPlus K Θ.ω).1 = -(supp K (Θ.ω + π / 2) * sin Θ.ω) ∧
      (cPlus K Θ.ω).2 = supp K (Θ.ω + π / 2) * cos Θ.ω := by
  rw [(mpc_cPlus_eq hK).1]
  simp [vvec]

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
  rw [wedgeGapW, (mpc_aMinus_eq hK).1, wedgeW, mpc_dot_uvec_zero, Prod.fst_sub] at hw
  simp only at hw
  rw [sub_pos, div_lt_iff₀ hct] at hw
  have hA := (mpc_aMinus_coords hK).1
  rw [hA] at hx
  rw [mpcL, mpcLineY, div_neg_iff]
  right
  refine ⟨?_, hst⟩
  nlinarith [mul_le_mul_of_nonneg_right hx hct.le]

/-- `C_K⁺(ω)` lies strictly to the left of `A_K⁻(0)`. -/
lemma mpc_C_lt_A (hK : IsPolygonCap Θ K) : (cPlus K Θ.ω).1 < (aMinus K 0).1 := by
  have hω0 := mpc_omega_pos Θ
  rw [(mpc_cPlus_coords hK).1, (mpc_aMinus_coords hK).1]
  rcases lt_or_eq_of_le (mpc_omega_le Θ) with hlt | heq
  · obtain ⟨-, h0, -, h1⟩ := mpc_sigma_bottom_lt hK hlt
    have hs : 0 < sin Θ.ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
    nlinarith
  · -- `ω = π/2`: a polygon cap is not contained in a vertical line
    rw [heq, sin_pi_div_two, mul_one, show π / 2 + π / 2 = π by ring]
    have hKb := hK.1.2.1
    by_contra hle
    push Not at hle
    have hx : ∀ p ∈ K, p.1 = supp K 0 := by
      intro p hp
      have e1 := dot_le_supp hKb.2.1 hp 0
      have e2 := dot_le_supp hKb.2.1 hp π
      rw [mpc_dot_uvec_zero] at e1
      rw [mpc_dot_uvec_pi] at e2
      linarith
    -- the support values at the angles of `Θ^◇`
    obtain ⟨q, hq, hq2⟩ := exists_dot_eq_supp hKb.2.1 hKb.1 (π / 2)
    rw [hK.1.2.2.2.1, mpc_dot_uvec_pi_div_two] at hq2
    set x₁ := supp K 0
    have hqx : q = (x₁, 1) := by ext; exact hx q hq; exact hq2
    obtain ⟨m, hm⟩ := Finset.exists_min_image Θ.angles sin Θ.nonempty
    set δ := sin m / 2
    have hδ : 0 < δ := by
      have := mpc_angles_bounds hm.1
      exact half_pos (sin_pos_of_pos_of_lt_pi this.1 (by linarith [mpc_omega_le Θ, pi_pos]))
    have hP : (x₁ + δ, (1 : ℝ) / 2) ∈ K := by
      rw [mpc_polycap_mem_iff hK]
      refine ⟨fun s hs => ?_, ?_, ?_⟩
      · have e := dot_le_supp hKb.2.1 hq s
        rw [hqx] at e
        simp only [dot, uvec] at e ⊢
        have hss := mpc_sin_pos_of_diamond hs
        rcases mpc_diamond_cases hs with h | ⟨u, hu, rfl⟩ | rfl | rfl
        · have hsm := hm.2 s h
          have hcs := cos_le_one s
          have : δ * cos s ≤ sin s / 2 := by
            have hcs0 : 0 ≤ cos s := cos_nonneg_of_mem_Icc ⟨by linarith [(mpc_angles_bounds h).1,
              pi_pos], by linarith [(mpc_angles_bounds h).2, mpc_omega_le Θ]⟩
            calc δ * cos s ≤ δ * 1 := mul_le_mul_of_nonneg_left hcs (by positivity)
              _ = sin m / 2 := by ring
              _ ≤ sin s / 2 := by linarith
          nlinarith
        · have hcu : cos (u + π / 2) ≤ 0 := by
            rw [cos_add_pi_div_two]
            have := sin_pos_of_pos_of_lt_pi (mpc_angles_bounds hu).1
              (by linarith [(mpc_angles_bounds hu).2, mpc_omega_le Θ, pi_pos])
            linarith
          nlinarith
        · rw [heq, cos_pi_div_two, sin_pi_div_two] at *
          linarith
        · rw [cos_pi_div_two, sin_pi_div_two] at *
          linarith
      · show 0 ≤ dot (x₁ + δ, (1 : ℝ) / 2) (uvec Θ.ω)
        rw [heq, mpc_dot_uvec_pi_div_two]; norm_num
      · show 0 ≤ dot (x₁ + δ, (1 : ℝ) / 2) (uvec (π / 2))
        rw [mpc_dot_uvec_pi_div_two]; norm_num
    have := hx _ hP
    simp only at this
    linarith

end Boundary

/-- The polygon niche of a polygon cap is bounded. -/
lemma mpc_isBounded_polyNiche {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) : Bornology.IsBounded (polyNiche Θ K) := by
  have hc : IsCompact (Icc (cPlus K Θ.ω).1 (aMinus K 0).1) := isCompact_Icc
  obtain ⟨M₁, hM₁⟩ := hc.exists_bound_of_continuousOn (mpc_continuous_mpcLow Θ K).continuousOn
  obtain ⟨M₂, hM₂⟩ := hc.exists_bound_of_continuousOn (mpc_continuous_mpcTop Θ K).continuousOn
  apply ((Metric.isBounded_Icc (cPlus K Θ.ω).1 (aMinus K 0).1).prod
    (Metric.isBounded_Icc (-M₁) M₂)).subset
  intro p hp
  rw [mpc_polyNiche_eq hK] at hp
  obtain ⟨h1, h2⟩ := hp
  have hx1 : (cPlus K Θ.ω).1 ≤ p.1 := by
    by_contra h; push Not at h
    have := (mpc_left_of_C hK h.le).1; linarith
  have hx2 : p.1 ≤ (aMinus K 0).1 := by
    by_contra h; push Not at h
    have := (mpc_right_of_A hK h.le).1; linarith
  have e1 := hM₁ p.1 ⟨hx1, hx2⟩
  have e2 := hM₂ p.1 ⟨hx1, hx2⟩
  rw [Real.norm_eq_abs, abs_le] at e1 e2
  exact ⟨⟨hx1, hx2⟩, ⟨by linarith, by linarith⟩⟩

end Polyline

/-- A maximum polygon cap with angle set `Θ` (Definition 3.4.1, `def:maximum-polygon-cap`): a polygon
cap containing `o_ω` that maximizes `𝒜_Θ` over the polygon caps with angle set `Θ`. -/
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

/-! ### The mirror reflection (Lemma 3.4.1) -/

section Mirror

open MeasureTheory


lemma mpc_mirror_eq_toLin (ω : ℝ) :
    mirror ω = Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      !![cos (π / 2 + ω), sin (π / 2 + ω); sin (π / 2 + ω), -cos (π / 2 + ω)] := by
  funext p
  rw [Matrix.toLin_finTwoProd_apply]
  simp only [mirror]; ext <;> ring

/-- The mirror reflection preserves the Lebesgue measure. -/
lemma mpc_volume_preimage_mirror (ω : ℝ) (A : Set (ℝ × ℝ)) :
    volume (mirror ω ⁻¹' A) = volume A := by
  have : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hdet : LinearMap.det (Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      !![cos (π / 2 + ω), sin (π / 2 + ω); sin (π / 2 + ω), -cos (π / 2 + ω)]) = -1 := by
    rw [LinearMap.det_toLin, Matrix.det_fin_two_of]
    linear_combination -cos_sq_add_sin_sq (π / 2 + ω)
  rw [mpc_mirror_eq_toLin, Measure.addHaar_preimage_linearMap _ (by rw [hdet]; norm_num), hdet]
  simp

lemma mpc_mirror_mirror (ω : ℝ) (p : ℝ × ℝ) : mirror ω (mirror ω p) = p := by
  simp only [mirror]
  ext
  · simp only; linear_combination p.1 * sin_sq_add_cos_sq (π / 2 + ω)
  · simp only; linear_combination p.2 * sin_sq_add_cos_sq (π / 2 + ω)

lemma mpc_image_mirror (ω : ℝ) (A : Set (ℝ × ℝ)) : mirror ω '' A = mirror ω ⁻¹' A := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [mem_preimage, mpc_mirror_mirror]; exact hq
  · intro hp
    exact ⟨mirror ω p, hp, mpc_mirror_mirror ω p⟩

lemma mpc_area_mirror (ω : ℝ) (A : Set (ℝ × ℝ)) : area (mirror ω '' A) = area A := by
  rw [area, area, mpc_image_mirror, mpc_volume_preimage_mirror]

lemma mpc_dot_mirror (ω : ℝ) (p : ℝ × ℝ) (t : ℝ) :
    dot (mirror ω p) (uvec t) = dot p (uvec (π / 2 + ω - t)) := by
  simp only [mirror, dot, uvec, cos_sub, sin_sub]
  ring

lemma mpc_mem_mirror (ω : ℝ) (A : Set (ℝ × ℝ)) (p : ℝ × ℝ) :
    p ∈ mirror ω '' A ↔ mirror ω p ∈ A := by
  rw [mpc_image_mirror]; rfl

lemma mpc_mirror_oPt {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) : mirror ω (oPt ω) = oPt ω := by
  apply mpc_eq_of_dot_eq (a := ω) (b := ω + π / 2)
  · rw [show ω + π / 2 - ω = π / 2 by ring, sin_pi_div_two]; norm_num
  · rw [mpc_dot_mirror, show π / 2 + ω - ω = π / 2 by ring, mpc_dot_uvec_pi_div_two,
      mpc_oPt_snd, mpc_oPt_dot_uvec hω]
  · rw [mpc_dot_mirror, show π / 2 + ω - (ω + π / 2) = 0 by ring, mpc_dot_uvec_zero,
      uvec_add_pi_div_two, mpc_oPt_dot_vvec hω]
    rfl

lemma mpc_mirror_mirror_angleSet (Θ : AngleSet) : Θ.mirror.mirror = Θ := by
  obtain ⟨ω, angles, hω, hne, hsub⟩ := Θ
  simp only [AngleSet.mirror, AngleSet.mk.injEq, true_and]
  rw [Finset.image_image]
  convert Finset.image_id (s := angles) using 2
  funext t
  simp

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

lemma mpc_uvec_mirrorAngle (ω s : ℝ) : uvec (mpcMirrorAngle ω s) = uvec (π / 2 + ω - s) := by
  rw [mpcMirrorAngle]
  split_ifs
  · exact uvec_add_two_pi _
  · rw [add_zero]

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
  have hcap' : IsCap (mirrorCap K Θ.ω) Θ.ω := proposition2_5_4_isCap hK.1
  have hhpi : IsHalfPlaneInter (mirrorCap K Θ.ω) Θ.mirror.capAngles := by
    obtain ⟨ι, t, c, ht, hKeq⟩ := hK.2
    refine ⟨ι, fun i => mpcMirrorAngle Θ.ω (t i), c, fun i => mpc_mirrorAngle_mem (ht i), ?_⟩
    ext p
    rw [mirrorCap, mpc_mem_mirror, hKeq]
    simp only [mem_iInter, halfMinus, mem_ofPred_eq, mpc_uvec_mirrorAngle, mpc_dot_mirror]
  have hK' : IsPolygonCap Θ.mirror (mirrorCap K Θ.ω) := ⟨hcap', hhpi⟩
  refine ⟨hK', ?_⟩
  -- the polygon niche is mirrored
  have hniche : polyNiche Θ.mirror (mirrorCap K Θ.ω) = mirror Θ.ω '' polyNiche Θ K := by
    ext p
    rw [mpc_mem_mirror]
    simp only [polyNiche, mem_inter_iff, mem_iUnion, exists_prop]
    have hfan : p ∈ fan Θ.mirror.ω ↔ mirror Θ.ω p ∈ fan Θ.ω := by
      simp only [fan, halfPlus, mem_inter_iff, mem_ofPred_eq, mpc_dot_mirror]
      show 0 ≤ dot p (uvec Θ.ω) ∧ 0 ≤ dot p (uvec (π / 2)) ↔ _
      rw [show π / 2 + Θ.ω - Θ.ω = π / 2 by ring, show π / 2 + Θ.ω - π / 2 = Θ.ω by ring]
      exact and_comm
    rw [hfan]
    apply and_congr_right
    intro _
    have hq : ∀ (S : Set (ℝ × ℝ)) (t : ℝ) (q : ℝ × ℝ), q ∈ qMinus S t ↔
        dot q (uvec t) < supp S t - 1 ∧ dot q (uvec (t + π / 2)) < supp S (t + π / 2) - 1 := by
      intro S t q; rw [proposition2_2_2_qMinus]; rfl
    have hback : ∀ r, dot p (uvec r) = dot (mirror Θ.ω p) (uvec (π / 2 + Θ.ω - r)) := by
      intro r
      rw [← mpc_dot_mirror, mpc_mirror_mirror]
    have hsK : ∀ r, supp (mirrorCap K Θ.ω) r = supp K (Θ.ω + π / 2 - r) :=
      proposition2_5_4_supp
    constructor
    · rintro ⟨s, hs, hqs⟩
      refine ⟨Θ.ω - s, mpc_mem_mirror_angles.1 hs, ?_⟩
      rw [hq] at hqs ⊢
      obtain ⟨h1, h2⟩ := hqs
      rw [hsK, hback] at h1
      rw [hsK, hback] at h2
      refine ⟨?_, ?_⟩
      · rw [show Θ.ω - s = π / 2 + Θ.ω - (s + π / 2) by ring]
        convert h2 using 3; ring
      · rw [show Θ.ω - s + π / 2 = π / 2 + Θ.ω - s by ring]
        convert h1 using 3; ring
    · rintro ⟨t, ht, hqt⟩
      refine ⟨Θ.ω - t, mpc_mem_mirror_angles.2 (by rw [show Θ.ω - (Θ.ω - t) = t by ring]; exact ht),
        ?_⟩
      rw [hq] at hqt ⊢
      obtain ⟨h1, h2⟩ := hqt
      rw [hsK, hsK, hback, hback]
      refine ⟨?_, ?_⟩
      · convert h2 using 3 <;> ring
      · convert h1 using 3 <;> ring
  rw [theorem3_2_3 hK', theorem3_2_3 hK, hniche, mpc_area_mirror, mirrorCap, mpc_area_mirror]

end Mirror

/-- **Lemma 3.4.1** (`lem:maximum-polygon-cap-mirror`). The mirror reflection of a maximum polygon cap
is a maximum polygon cap with the angle set `ω - Θ`. -/
theorem lemma3_4_1 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap Θ K) :
    IsMaxPolygonCap Θ.mirror (mirrorCap K Θ.ω) := by
  obtain ⟨hcap, ho, hmax⟩ := hK
  obtain ⟨hK', hA'⟩ := mpc_mirror_polycap hcap
  refine ⟨hK', ⟨oPt Θ.ω, ho, mpc_mirror_oPt Θ.hω⟩, fun K'' hK'' => ?_⟩
  obtain ⟨h1, h2⟩ := mpc_mirror_polycap hK''
  rw [mpc_mirror_mirror_angleSet] at h1 h2
  rw [hA', ← h2]
  exact hmax _ h1

/-! ### The width of polygon caps of positive polygon area (Lemma 3.4.2) -/

section Width

open MeasureTheory


lemma mpc_cap_nonneg {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsCap K ω) {p : ℝ × ℝ} (hp : p ∈ K) :
    0 ≤ p.2 ∧ 0 ≤ dot p (uvec ω) := by
  have h := mpc_cap_subset_fan hK hp
  have h2 : 0 ≤ dot p (uvec (π / 2)) := h.2
  rw [mpc_dot_uvec_pi_div_two] at h2
  exact ⟨h2, h.1⟩

lemma mpc_volume_prod (s t : Set ℝ) : volume (s ×ˢ t) = volume s * volume t := by
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl, Measure.prod_prod]

/-- The width of a cap along `u_0` is at most the width of `P_ω` when `ω < π/2`. -/
lemma mpc_width_le_of_lt {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) (hlt : ω < π / 2) {K : Set (ℝ × ℝ)}
    (hK : IsCap K ω) : width K 0 ≤ 1 / cos ω + tan ω := by
  have hc : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [hω.1], hlt⟩
  have hs : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω.1 (by linarith [pi_pos])
  have hfan := mpc_cap_subset_fan hK
  have hne := hK.2.1.1
  rw [width, zero_add]
  have h0 : supp K 0 ≤ 1 / cos ω := by
    apply csSup_le (hne.image _)
    rintro _ ⟨p, hp, rfl⟩
    have e1 := (mpc_cap_le_one hK hp).1
    have e2 : 0 ≤ p.2 := (mpc_cap_nonneg hK hp).1
    dsimp only
    rw [mpc_dot_uvec_zero, le_div_iff₀ hc]
    simp only [dot, uvec] at e1
    nlinarith
  have hpi : supp K π ≤ tan ω := by
    apply csSup_le (hne.image _)
    rintro _ ⟨p, hp, rfl⟩
    have e1 : 0 ≤ dot p (uvec ω) := (hfan hp).1
    have e2 := (mpc_cap_le_one hK hp).2
    dsimp only
    rw [mpc_dot_uvec_pi, tan_eq_sin_div_cos, le_div_iff₀ hc]
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
    rw [mpc_dot_uvec_zero] at e1
    rw [mpc_dot_uvec_pi] at e2
    linarith
  have hsub : K ⊆ Icc (-supp K π) (supp K 0) ×ˢ Icc 0 1 := by
    intro p hp
    have e1 := dot_le_supp hKb.2.1 hp 0
    have e2 := dot_le_supp hKb.2.1 hp π
    rw [mpc_dot_uvec_zero] at e1
    rw [mpc_dot_uvec_pi] at e2
    exact ⟨⟨by linarith, e1⟩, ⟨(mpc_cap_nonneg hK hp).1, (mpc_cap_le_one hK hp).2⟩⟩
  have hle := measure_mono (μ := volume) hsub
  rw [mpc_volume_prod, Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_mul (by linarith),
    sub_zero, mul_one, sub_neg_eq_add, add_comm (supp K 0)] at hle
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rw [ENNReal.toReal_ofReal (by linarith)] at this
  rw [hd]; simp only [area]; linarith

lemma mpc_wedge_arith {d s m L : ℝ} (hm : 0 < m) (hs : 0 < s) (hd1 : 2 * s < d)
    (hd2 : 32 / m < d) (hL : L = d - s) : d < L / 2 * (L * m / 4) := by
  have hd : 0 < d := by linarith
  have hL2 : d / 2 < L := by rw [hL]; linarith
  have h1 : d * d * m / 32 ≤ L / 2 * (L * m / 4) := by
    have : d / 2 * (d / 2) ≤ L * L := by nlinarith
    have : d * d * m / 32 = (d / 2 * (d / 2)) * m / 8 := by ring
    rw [this]
    have : L / 2 * (L * m / 4) = (L * L) * m / 8 := by ring
    rw [this]
    gcongr
  have h2 : d < d * d * m / 32 := by
    rw [div_lt_iff₀ hm] at hd2
    have : 32 * d < d * (d * m) := by nlinarith
    linarith
  linarith

/-- For `ω = π/2`, a rectangle of area `L² m / 8` lies in the wedge `F_ω ∩ Q_K⁻(t)`. -/
lemma mpc_wedge_rect {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K)
    (hω : Θ.ω = π / 2) {t : ℝ} (htΘ : t ∈ Θ.angles) {m : ℝ}
    (hm1 : m ≤ cos t / sin t) (hm2 : m ≤ sin t / cos t) :
    Ioo (-supp K π + 1 / sin t + (supp K 0 - 1 / cos t - (-supp K π + 1 / sin t)) / 4)
      (supp K 0 - 1 / cos t - (supp K 0 - 1 / cos t - (-supp K π + 1 / sin t)) / 4) ×ˢ
      Ioo 0 ((supp K 0 - 1 / cos t - (-supp K π + 1 / sin t)) * m / 4) ⊆ polyNiche Θ K := by
  have ht := mpc_angles_bounds htΘ
  rw [hω] at ht
  have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩
  have hst : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
  have hKb := hK.1.2.1
  set L := supp K 0 - 1 / cos t - (-supp K π + 1 / sin t) with hL
  have hA : supp K 0 * cos t ≤ supp K t := by
    obtain ⟨p, hp, hpe⟩ := exists_dot_eq_supp hKb.2.1 hKb.1 0
    rw [mpc_dot_uvec_zero] at hpe
    have e := dot_le_supp hKb.2.1 hp t
    have e4 := (mpc_cap_nonneg hK.1 hp).1
    simp only [dot, uvec] at e
    rw [← hpe]; nlinarith
  have hC : supp K π * sin t ≤ supp K (t + π / 2) := by
    obtain ⟨p, hp, hpe⟩ := exists_dot_eq_supp hKb.2.1 hKb.1 π
    rw [mpc_dot_uvec_pi] at hpe
    have e := dot_le_supp hKb.2.1 hp (t + π / 2)
    have e4 := (mpc_cap_nonneg hK.1 hp).1
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
    rw [hω, mpc_dot_uvec_pi_div_two]; exact hy1.le
  · show 0 ≤ dot (x, y) (uvec (π / 2))
    rw [mpc_dot_uvec_pi_div_two]; exact hy1.le
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
    have hsub := mpc_wedge_rect hK hΘ htΘ (min_le_right _ _) (min_le_left _ _)
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

/-! ### Existence of maximum polygon caps (Theorem 3.4.3) -/

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

/-- The polygon cap `K₁ = 𝓒_Θ(1)` of the paper. -/
lemma mpc_K1 (Θ : AngleSet) :
    IsPolygonCap Θ (capH Θ (fun _ => 1)) ∧ oPt Θ.ω ∈ capH Θ (fun _ => 1) ∧
      polyNiche Θ (capH Θ (fun _ => 1)) = ∅ ∧ 0 < area (capH Θ (fun _ => 1)) := by
  have hω0 := mpc_omega_pos Θ
  have hω2 := mpc_omega_le Θ
  set K₁ := capH Θ (fun _ => 1) with hK₁
  have hmem : ∀ p, p ∈ K₁ ↔ (∀ s ∈ Θ.diamond, dot p (uvec s) ≤ 1) ∧ 0 ≤ dot p (uvec Θ.ω) ∧
      0 ≤ dot p (uvec (π / 2)) := by
    intro p; rw [hK₁, mpc_mem_capH]; simp
  -- `o_ω ∈ K₁`
  have ho : oPt Θ.ω ∈ K₁ := by
    rw [hmem]
    refine ⟨fun s hs => ?_, ?_, ?_⟩
    · apply mpc_oPt_dot_le Θ.hω (mpc_diamond_bounds hs).1 (mpc_diamond_lt_pi hs)
      rcases mpc_diamond_cases hs with h | ⟨u, hu, rfl⟩ | rfl | rfl
      · exact Or.inl (mpc_angles_bounds h).2.le
      · right; linarith [(mpc_angles_bounds hu).1]
      · exact Or.inl le_rfl
      · exact Or.inr le_rfl
    · rw [mpc_oPt_dot_uvec Θ.hω]; norm_num
    · rw [mpc_dot_uvec_pi_div_two, mpc_oPt_snd]; norm_num
  have hO : (0 : ℝ × ℝ) ∈ K₁ := by
    rw [hmem]; simp
  have hc : IsCompact K₁ := mpc_isCompact_capH Θ _
  have hconv : Convex ℝ K₁ := mpc_convex_of_halfPlaneInter (mpc_capH_halfPlaneInter Θ _)
  have hbody : IsConvexBody K₁ := ⟨⟨_, hO⟩, hc, hconv⟩
  -- support values
  have hsω : supp K₁ Θ.ω = 1 := by
    apply le_antisymm
    · apply csSup_le ⟨_, mem_image_of_mem _ hO⟩
      rintro _ ⟨p, hp, rfl⟩
      exact ((hmem p).1 hp).1 _ (Or.inr (Or.inl rfl))
    · have := dot_le_supp hc ho Θ.ω
      rwa [mpc_oPt_dot_uvec Θ.hω] at this
  have hsπ : supp K₁ (π / 2) = 1 := by
    apply le_antisymm
    · apply csSup_le ⟨_, mem_image_of_mem _ hO⟩
      rintro _ ⟨p, hp, rfl⟩
      exact ((hmem p).1 hp).1 _ (Or.inr (Or.inr rfl))
    · have := dot_le_supp hc ho (π / 2)
      rwa [mpc_dot_uvec_pi_div_two, mpc_oPt_snd] at this
  have hsωπ : supp K₁ (Θ.ω + π) = 0 := by
    apply le_antisymm
    · apply csSup_le ⟨_, mem_image_of_mem _ hO⟩
      rintro _ ⟨p, hp, rfl⟩
      have := ((hmem p).1 hp).2.1
      dsimp only
      rw [mpc_dot_uvec_add_pi]; linarith
    · have := dot_le_supp hc hO (Θ.ω + π)
      rwa [dot_zero_left] at this
  have hs3 : supp K₁ (3 * π / 2) = 0 := by
    apply le_antisymm
    · apply csSup_le ⟨_, mem_image_of_mem _ hO⟩
      rintro _ ⟨p, hp, rfl⟩
      have := ((hmem p).1 hp).2.2
      dsimp only
      rw [mpc_dot_uvec_three_pi_div_two]
      rw [mpc_dot_uvec_pi_div_two] at this
      linarith
    · have := dot_le_supp hc hO (3 * π / 2)
      rwa [dot_zero_left] at this
  have hcap : IsPolygonCap Θ K₁ :=
    ⟨⟨Θ.hω, hbody, hsω, hsπ, hsωπ, hs3,
      mpc_halfPlaneInter_mono (mpc_capH_halfPlaneInter Θ _) (mpc_capAngles_subset Θ)⟩,
      mpc_capH_halfPlaneInter Θ _⟩
  refine ⟨hcap, ho, ?_, ?_⟩
  · -- the niche is empty since `h_{K₁} ≤ 1` on `Θ^◇`
    rw [eq_empty_iff_forall_notMem]
    intro p hp
    rw [mpc_polyNiche_eq hcap] at hp
    obtain ⟨h1, h2⟩ := hp
    rw [mpc_lt_mpcTop_iff] at h2
    obtain ⟨t, ht, h3, h4⟩ := h2
    have htd : t ∈ Θ.diamond := Or.inl (Or.inl ht)
    have htd2 : t + π / 2 ∈ Θ.diamond := Or.inl (Or.inr ⟨t, ht, rfl⟩)
    have hst := supp K₁ t
    have e1 : supp K₁ t ≤ 1 := csSup_le ⟨_, mem_image_of_mem _ hO⟩ (by
      rintro _ ⟨q, hq, rfl⟩; exact ((hmem q).1 hq).1 t htd)
    have e2 : supp K₁ (t + π / 2) ≤ 1 := csSup_le ⟨_, mem_image_of_mem _ hO⟩ (by
      rintro _ ⟨q, hq, rfl⟩; exact ((hmem q).1 hq).1 _ htd2)
    have hlow : 0 ≤ p.2 := by
      have e : mpcL K₁ (π / 2) p.1 ≤ mpcLow Θ K₁ p.1 := le_max_right _ _
      rw [mpc_mpcL_pi_div_two hcap] at e
      exact e.trans h1
    simp only [mpcL, mpcLineY] at h3 h4
    have htb := mpc_angles_bounds ht
    have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
    have hst' : 0 < sin t := sin_pos_of_pos_of_lt_pi htb.1 (by linarith [pi_pos])
    rw [lt_div_iff₀ hst'] at h3
    rw [sin_add_pi_div_two, cos_add_pi_div_two, lt_div_iff₀ hct] at h4
    -- `p · u_t < 0` and `p · v_t < 0` force `p.2 < 0`
    nlinarith [mul_pos hst' hct, sin_sq_add_cos_sq t]
  · -- a small square near the origin
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
      · rw [mpc_dot_uvec_pi_div_two]; exact hy0
    have hle := ENNReal.toReal_mono hc.measure_lt_top.ne (measure_mono (μ := volume) hsq)
    rw [mpc_volume_prod, Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num),
      ENNReal.toReal_ofReal (by norm_num)] at hle
    simp only [area]
    linarith

/-- Translating a set by `v` translates every half-plane containing it. -/
lemma mpc_halfPlaneInter_translate {K : Set (ℝ × ℝ)} {A : Set ℝ} (hK : IsHalfPlaneInter K A)
    (v : ℝ × ℝ) : IsHalfPlaneInter ((fun p => p + v) '' K) A := by
  obtain ⟨ι, t, c, ht, rfl⟩ := hK
  refine ⟨ι, t, fun i => c i + dot v (uvec (t i)), ht, ?_⟩
  ext p
  simp only [mem_image, mem_iInter, halfMinus, mem_ofPred_eq]
  constructor
  · rintro ⟨q, hq, rfl⟩ i
    rw [dot_add_left]; linarith [hq i]
  · intro hp
    refine ⟨p - v, fun i => ?_, by abel⟩
    rw [dot_sub_left]; linarith [hp i]

/-- Horizontal translates of polygon caps with `ω = π/2` are polygon caps with the same polygon
sofa area. -/
lemma mpc_translate_polycap {Θ : AngleSet} (hω : Θ.ω = π / 2) {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (a : ℝ) :
    IsPolygonCap Θ ((fun p => p + (a, 0)) '' K) ∧
      polyArea Θ ((fun p => p + (a, 0)) '' K) = polyArea Θ K := by
  have hKb := hK.1.2.1
  set K' := (fun p => p + ((a, 0) : ℝ × ℝ)) '' K
  have hc : IsCompact K' := hKb.2.1.image (by fun_prop)
  have hconv : Convex ℝ K' := by
    have := hKb.2.2.translate ((a, 0) : ℝ × ℝ)
    have e : K' = (fun x => ((a, 0) : ℝ × ℝ) + x) '' K := by
      simp only [K']; congr 1; funext x; exact add_comm _ _
    rw [e]; exact this
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
    refine ⟨⟨Θ.hω, ⟨hKb.1.image _, hc, hconv⟩, ?_, ?_, ?_, ?_,
      mpc_halfPlaneInter_translate hK.1.2.2.2.2.2.2 _⟩, mpc_halfPlaneInter_translate hK.2 _⟩
    · rw [hs _ hcos1]; exact hK.1.2.2.1
    · rw [hs _ hcos2]; exact hK.1.2.2.2.1
    · rw [hs _ hcos3]; exact hK.1.2.2.2.2.1
    · rw [hs _ hcos4]; exact hK.1.2.2.2.2.2.1
  refine ⟨hK', ?_⟩
  rw [← (proposition3_3_5 hK').2, ← (theorem3_3_6 hK _).2]
  rfl

open Classical in
/-- The constraint values of `𝓒_Θ(h)` on the angles `Θ^◇ ∪ {ω + π, 3π/2}`. -/
noncomputable def mpcCapC (Θ : AngleSet) (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  if s ∈ Θ.diamond then h s else 1 - h (s - π)

lemma mpc_mem_capH_iff_capAngles (Θ : AngleSet) (h : ℝ → ℝ) (p : ℝ × ℝ) :
    p ∈ capH Θ h ↔ ∀ s ∈ Θ.capAngles, dot p (uvec s) ≤ mpcCapC Θ h s := by
  rw [mpc_mem_capH]
  have hω := mpc_omega_pos Θ
  have hω' := mpc_omega_le Θ
  have hnd1 : Θ.ω + π ∉ Θ.diamond := fun h => by linarith [mpc_diamond_lt_pi h, pi_pos]
  have hnd2 : 3 * π / 2 ∉ Θ.diamond := fun h => by linarith [mpc_diamond_lt_pi h, pi_pos]
  constructor
  · rintro ⟨h1, h2, h3⟩ c hc
    rcases mpc_capAngles_cases hc with hc' | rfl | rfl
    · rw [mpcCapC, ite_eq_left hc']; exact h1 c hc'
    · rw [mpcCapC, ite_eq_right hnd1, mpc_dot_uvec_add_pi, add_sub_cancel_right]; linarith
    · rw [mpcCapC, ite_eq_right hnd2, mpc_dot_uvec_three_pi_div_two,
        show 3 * π / 2 - π = π / 2 by ring]
      rw [mpc_dot_uvec_pi_div_two] at h3; linarith
  · intro hall
    refine ⟨fun s hs => ?_, ?_, ?_⟩
    · have := hall s (Or.inl hs); rwa [mpcCapC, ite_eq_left hs] at this
    · have := hall (Θ.ω + π) (Or.inr (Or.inl rfl))
      rw [mpcCapC, ite_eq_right hnd1, mpc_dot_uvec_add_pi, add_sub_cancel_right] at this
      linarith
    · have := hall (3 * π / 2) (Or.inr (Or.inr rfl))
      rw [mpcCapC, ite_eq_right hnd2, mpc_dot_uvec_three_pi_div_two,
        show 3 * π / 2 - π = π / 2 by ring] at this
      rw [mpc_dot_uvec_pi_div_two]; linarith

/-- A bounded region containing the polygon niches of all polygon caps with support values at most
`R` on `Θ^◇`. -/
lemma mpc_isBounded_niche_region (Θ : AngleSet) (R : ℝ) :
    Bornology.IsBounded (⋃ t ∈ Θ.angles, fan Θ.ω ∩
      {p : ℝ × ℝ | dot p (uvec t) ≤ R ∧ dot p (uvec (t + π / 2)) ≤ R}) := by
  refine (Bornology.isBounded_biUnion_finset Θ.angles).2 fun t ht => ?_
  have htb := mpc_angles_bounds ht
  have hω := mpc_omega_le Θ
  have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  have hst : 0 < sin t := sin_pos_of_pos_of_lt_pi htb.1 (by linarith [pi_pos])
  apply mpc_isBounded_of_strip htb.1 (by linarith) (a := 0) (b := 2 * |R|) (c₁ := R) (c₂ := R)
  rintro p ⟨⟨hf1, hf2⟩, h1, h2⟩
  have hy : 0 ≤ p.2 := by
    have : 0 ≤ dot p (uvec (π / 2)) := hf2
    rwa [mpc_dot_uvec_pi_div_two] at this
  refine ⟨hy, ?_, h1, h2⟩
  -- `p.2 = sin t (p · u_t) + cos t (p · v_t)`
  have e : p.2 = sin t * dot p (uvec t) + cos t * dot p (uvec (t + π / 2)) := by
    rw [uvec_add_pi_div_two]
    simp only [dot, uvec, vvec]
    linear_combination (-p.2) * sin_sq_add_cos_sq t
  rw [e]
  have hs1 := sin_le_one t
  have hc1 := cos_le_one t
  have hR := le_abs_self R
  nlinarith [mul_le_mul_of_nonneg_left h1 hst.le, mul_le_mul_of_nonneg_left h2 hct.le]

section Limit

variable {Θ : AngleSet}

/-- Limits of polygon caps lying in a fixed compact set, with converging support values on `Θ^◇`:
the limit `𝓒_Θ(hinf)` is a polygon cap, and the polygon sofa area is upper semicontinuous. -/
lemma mpc_limit_polycap {K : ℕ → Set (ℝ × ℝ)} (hK : ∀ n, IsPolygonCap Θ (K n))
    {B : Set (ℝ × ℝ)} (hB : IsCompact B) (hKB : ∀ n, K n ⊆ B) {hinf : ℝ → ℝ}
    (hlim : ∀ s ∈ Θ.diamond, Tendsto (fun n => supp (K n) s) atTop (𝓝 (hinf s))) :
    IsPolygonCap Θ (capH Θ hinf) ∧ (∀ s ∈ Θ.diamond, supp (capH Θ hinf) s = hinf s) ∧
      (∀ p, (∀ᶠ n in atTop, p ∈ K n) → p ∈ capH Θ hinf) ∧
      (∀ ε > 0, ∀ᶠ n in atTop, area (K n) ≤ area (capH Θ hinf) + ε) ∧
      (∀ ε > 0, ∀ᶠ n in atTop,
        area (polyNiche Θ (capH Θ hinf)) - ε ≤ area (polyNiche Θ (K n))) := by
  classical
  set L := capH Θ hinf with hL
  have hωd : Θ.ω ∈ Θ.diamond := Or.inr (Or.inl rfl)
  have hπd : π / 2 ∈ Θ.diamond := Or.inr (Or.inr rfl)
  have hω1 : hinf Θ.ω = 1 := by
    have := hlim _ hωd
    simp only [fun n => (hK n).1.2.2.1] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hπ1 : hinf (π / 2) = 1 := by
    have := hlim _ hπd
    simp only [fun n => (hK n).1.2.2.2.1] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hmemL : ∀ p, p ∈ L ↔ (∀ s ∈ Θ.diamond, dot p (uvec s) ≤ hinf s) ∧
      0 ≤ dot p (uvec Θ.ω) ∧ 0 ≤ dot p (uvec (π / 2)) := by
    intro p; rw [hL, mpc_mem_capH, hω1, hπ1, sub_self]
  -- limits of points of the `K n` lie in `L`
  have hclosed : ∀ (ψ : ℕ → ℕ), StrictMono ψ → ∀ (q : ℕ → ℝ × ℝ) (q₀ : ℝ × ℝ),
      (∀ k, q k ∈ K (ψ k)) → Tendsto q atTop (𝓝 q₀) → q₀ ∈ L := by
    intro ψ hψ q q₀ hq hqlim
    have hdot : ∀ v : ℝ × ℝ, Tendsto (fun k => dot (q k) v) atTop (𝓝 (dot q₀ v)) := by
      intro v
      have hc : Continuous fun x : ℝ × ℝ => dot x v := by simp only [dot]; fun_prop
      exact (hc.tendsto q₀).comp hqlim
    rw [hmemL]
    refine ⟨fun s hs => ?_, ?_, ?_⟩
    · exact le_of_tendsto_of_tendsto (hdot _) ((hlim s hs).comp hψ.tendsto_atTop)
        (Eventually.of_forall fun k => dot_le_supp (hK (ψ k)).1.2.1.2.1 (hq k) s)
    · exact ge_of_tendsto (hdot _)
        (Eventually.of_forall fun k => (mpc_cap_subset_fan (hK (ψ k)).1 (hq k)).1)
    · exact ge_of_tendsto (hdot _)
        (Eventually.of_forall fun k => (mpc_cap_subset_fan (hK (ψ k)).1 (hq k)).2)
  -- every limit support value is attained in `L`
  have hattain : ∀ r c, Tendsto (fun n => supp (K n) r) atTop (𝓝 c) → ∃ q ∈ L, dot q (uvec r) = c := by
    intro r c hrc
    have hq : ∀ n, ∃ q ∈ K n, dot q (uvec r) = supp (K n) r := fun n =>
      exists_dot_eq_supp (hK n).1.2.1.2.1 (hK n).1.2.1.1 r
    choose q hqK hqe using hq
    obtain ⟨q₀, -, ψ, hψ, hqψ⟩ := hB.tendsto_subseq fun n => hKB n (hqK n)
    refine ⟨q₀, hclosed ψ hψ (q ∘ ψ) q₀ (fun k => hqK (ψ k)) hqψ, ?_⟩
    have hc : Continuous fun x : ℝ × ℝ => dot x (uvec r) := by simp only [dot]; fun_prop
    have h1 := (hc.tendsto q₀).comp hqψ
    have h2 := hrc.comp hψ.tendsto_atTop
    exact tendsto_nhds_unique (h1.congr fun k => by simp [Function.comp, hqe]) h2
  have hLc : IsCompact L := mpc_isCompact_capH Θ hinf
  obtain ⟨q₀, hq₀, -⟩ := hattain _ _ (hlim _ hωd)
  have hLne : L.Nonempty := ⟨q₀, hq₀⟩
  have hsuppL : ∀ s ∈ Θ.diamond, supp L s = hinf s := by
    intro s hs
    obtain ⟨q, hq, hqe⟩ := hattain _ _ (hlim s hs)
    apply le_antisymm
    · apply csSup_le (hLne.image _)
      rintro _ ⟨p, hp, rfl⟩
      exact ((hmemL p).1 hp).1 s hs
    · rw [← hqe]; exact dot_le_supp hLc hq s
  have hbot : ∀ r, (∀ n, supp (K n) r = 0) → (∀ p ∈ L, dot p (uvec r) ≤ 0) → supp L r = 0 := by
    intro r h0 hle
    obtain ⟨q, hq, hqe⟩ := hattain r 0 (by simp only [h0]; exact tendsto_const_nhds)
    apply le_antisymm
    · exact csSup_le (hLne.image _) (by rintro _ ⟨p, hp, rfl⟩; exact hle p hp)
    · rw [← hqe]; exact dot_le_supp hLc hq r
  have hLcap : IsPolygonCap Θ L := by
    refine ⟨⟨Θ.hω, ⟨hLne, hLc, mpc_convex_of_halfPlaneInter (mpc_capH_halfPlaneInter Θ hinf)⟩,
      by rw [hsuppL _ hωd, hω1], by rw [hsuppL _ hπd, hπ1], ?_, ?_,
      mpc_halfPlaneInter_mono (mpc_capH_halfPlaneInter Θ hinf) (mpc_capAngles_subset Θ)⟩,
      mpc_capH_halfPlaneInter Θ hinf⟩
    · apply hbot _ (fun n => (hK n).1.2.2.2.2.1)
      intro p hp
      rw [mpc_dot_uvec_add_pi]; linarith [((hmemL p).1 hp).2.1]
    · apply hbot _ (fun n => (hK n).1.2.2.2.2.2.1)
      intro p hp
      have := ((hmemL p).1 hp).2.2
      rw [mpc_dot_uvec_three_pi_div_two]
      rw [mpc_dot_uvec_pi_div_two] at this
      linarith
  refine ⟨hLcap, hsuppL, ?_, ?_, ?_⟩
  · -- points eventually in `K n`
    intro p hp
    obtain ⟨N, hN⟩ := hp.exists_forall_of_atTop
    exact hclosed (fun k => k + N) (fun a b h => by simp only; omega) (fun _ => p) p
      (fun k => hN _ (Nat.le_add_left N k)) tendsto_const_nhds
  · -- upper semicontinuity of the area
    intro ε hε
    set c := mpcCapC Θ hinf
    have hLeq : mpcOuter Θ.capAngles c 0 = L := by
      ext p
      simp only [mpcOuter, mem_ofPred_eq, add_zero]
      rw [hL, mpc_mem_capH_iff_capAngles]
    have hb : Bornology.IsBounded (mpcOuter Θ.capAngles c 1) := by
      obtain ⟨t, ht⟩ := Θ.nonempty
      have htb := mpc_angles_bounds ht
      have hω := mpc_omega_le Θ
      have h3 : 3 * π / 2 ∈ Θ.capAngles := Or.inr (Or.inr rfl)
      apply mpc_isBounded_of_strip htb.1 (by linarith) (a := -(c (3 * π / 2) + 1))
        (b := c (π / 2) + 1) (c₁ := c t + 1) (c₂ := c (t + π / 2) + 1)
      intro p hp
      have e1 := hp _ h3
      have e2 := hp _ (Or.inl hπd)
      rw [mpc_dot_uvec_three_pi_div_two] at e1
      rw [mpc_dot_uvec_pi_div_two] at e2
      exact ⟨by linarith, e2, hp t (Or.inl (Or.inl (Or.inl ht))),
        hp _ (Or.inl (Or.inl (Or.inr ⟨t, ht, rfl⟩)))⟩
    obtain ⟨δ, hδ, hδ1, hle⟩ := mpc_area_outer_eventually_le one_pos hb hε
    rw [hLeq] at hle
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
  · -- lower semicontinuity of the niche area
    intro ε hε
    obtain ⟨r, hr⟩ := hB.isBounded.subset_closedBall 0
    have hR : ∀ n s, supp (K n) s ≤ 2 * r := by
      intro n s
      apply csSup_le ((hK n).1.2.1.1.image _)
      rintro _ ⟨p, hp, rfl⟩
      have h := hr (hKB n hp)
      rw [Metric.mem_closedBall, dist_zero_right] at h
      have h1 : |p.1| ≤ r := (norm_fst_le p).trans h
      have h2 : |p.2| ≤ r := (norm_snd_le p).trans h
      have := mpc_abs_dot_uvec_le p s
      dsimp only
      linarith [le_abs_self (dot p (uvec s))]
    apply mpc_area_lsc (B := ⋃ t ∈ Θ.angles, fan Θ.ω ∩
      {p : ℝ × ℝ | dot p (uvec t) ≤ 2 * r ∧ dot p (uvec (t + π / 2)) ≤ 2 * r}) _
      (mpc_isBounded_niche_region Θ (2 * r)) _ hε
    · intro p hp
      obtain ⟨hpf, hpq⟩ := hp
      obtain ⟨t, ht, hq⟩ := mem_iUnion₂.1 hpq
      have htd : t ∈ Θ.diamond := Or.inl (Or.inl ht)
      have htd2 : t + π / 2 ∈ Θ.diamond := Or.inl (Or.inr ⟨t, ht, rfl⟩)
      rw [proposition2_2_2_qMinus] at hq
      have e1 : dot p (uvec t) < supp L t - 1 := hq.1
      have e2 : dot p (uvec (t + π / 2)) < supp L (t + π / 2) - 1 := hq.2
      rw [hsuppL t htd] at e1
      rw [hsuppL _ htd2] at e2
      filter_upwards [(hlim t htd).eventually (lt_mem_nhds (show dot p (uvec t) + 1 < hinf t by
          linarith)),
        (hlim _ htd2).eventually (lt_mem_nhds (show dot p (uvec (t + π / 2)) + 1 <
          hinf (t + π / 2) by linarith))] with n h1 h2
      refine ⟨hpf, mem_iUnion₂.2 ⟨t, ht, ?_⟩⟩
      rw [proposition2_2_2_qMinus]
      exact ⟨show dot p (uvec t) < supp (K n) t - 1 by linarith,
        show dot p (uvec (t + π / 2)) < supp (K n) (t + π / 2) - 1 by linarith⟩
    · refine Eventually.of_forall fun n p hp => ?_
      obtain ⟨hpf, hpq⟩ := hp
      obtain ⟨t, ht, hq⟩ := mem_iUnion₂.1 hpq
      rw [proposition2_2_2_qMinus] at hq
      have e1 : dot p (uvec t) < supp (K n) t - 1 := hq.1
      have e2 : dot p (uvec (t + π / 2)) < supp (K n) (t + π / 2) - 1 := hq.2
      exact mem_iUnion₂.2 ⟨t, ht, hpf, by linarith [hR n t], by linarith [hR n (t + π / 2)]⟩

end Limit

/-- The proof of Theorem 3.4.3. -/
theorem mpc_theorem3_4_3_aux (Θ : AngleSet) : ∃ K, IsMaxPolygonCap Θ K := by
  classical
  obtain ⟨hK₁, ho₁, hN₁, harea₁⟩ := mpc_K1 Θ
  set K₁ := capH Θ (fun _ => 1) with hK₁def
  have hpa₁ : polyArea Θ K₁ = area K₁ := by
    rw [theorem3_2_3 hK₁, hN₁]; simp [area]
  obtain ⟨t₀, ht₀⟩ := Θ.nonempty
  obtain ⟨c, hc, hcK⟩ := lemma3_4_2 Θ.hω (mpc_angles_bounds ht₀)
  have hbound : ∀ K, IsPolygonCap Θ K → polyArea Θ K ≤ c := by
    intro K hK
    by_cases hpos : 0 < polyArea Θ K
    · have hw := hcK Θ rfl ht₀ K hK hpos
      have h1 := mpc_area_le_width hK.1
      have h2 : 0 ≤ area (polyNiche Θ K) := ENNReal.toReal_nonneg
      rw [theorem3_2_3 hK]; linarith
    · push Not at hpos; linarith
  set A : Set ℝ := {x | ∃ K, IsPolygonCap Θ K ∧ polyArea Θ K = x} with hA
  have hAbdd : BddAbove A := ⟨c, by rintro _ ⟨K, hK, rfl⟩; exact hbound K hK⟩
  have hA₁ : polyArea Θ K₁ ∈ A := ⟨K₁, hK₁, rfl⟩
  set M := sSup A with hM
  have hM₁ : polyArea Θ K₁ ≤ M := le_csSup hAbdd hA₁
  have hMpos : 0 < M := by rw [hpa₁] at hM₁; linarith
  -- a maximizing sequence of polygon caps containing `o_ω`
  have hseq : ∀ n : ℕ, ∃ K, IsPolygonCap Θ K ∧ oPt Θ.ω ∈ K ∧
      M - 1 / (n + 1) < polyArea Θ K ∧ 0 < polyArea Θ K := by
    intro n
    have hn : (0 : ℝ) < 1 / (n + 1) := by positivity
    have hlt : max (M - 1 / (n + 1)) (M / 2) < M := max_lt (by linarith) (by linarith)
    obtain ⟨_, ⟨K, hK, rfl⟩, hK2⟩ := exists_lt_of_lt_csSup ⟨_, hA₁⟩ hlt
    have hpos : 0 < polyArea Θ K := by linarith [le_max_right (M - 1 / (n + 1)) (M / 2)]
    have hlow : M - 1 / (n + 1) < polyArea Θ K := lt_of_le_of_lt (le_max_left _ _) hK2
    rcases lt_or_eq_of_le (mpc_omega_le Θ) with hlt' | heq
    · exact ⟨K, hK, mpc_oPt_mem hK hlt', hlow, hpos⟩
    · obtain ⟨p, hp, hpe⟩ := exists_dot_eq_supp hK.1.2.1.2.1 hK.1.2.1.1 (π / 2)
      rw [hK.1.2.2.2.1, mpc_dot_uvec_pi_div_two] at hpe
      obtain ⟨hK', hA'⟩ := mpc_translate_polycap heq hK (-p.1)
      refine ⟨_, hK', ⟨p, hp, ?_⟩, hA' ▸ hlow, hA' ▸ hpos⟩
      simp only [oPt, heq, show π / 4 - π / 2 / 2 = 0 by ring, tan_zero]
      ext
      · simp
      · simp [hpe]
  choose Ks hKs hoKs hlowKs hposKs using hseq
  -- a uniform bounding box
  set R := |(oPt Θ.ω).1| + c with hR
  have hbox : ∀ n, Ks n ⊆ Icc (-R) R ×ˢ Icc 0 1 := by
    intro n p hp
    have hw := hcK Θ rfl ht₀ (Ks n) (hKs n) (hposKs n)
    have hKc := (hKs n).1.2.1.2.1
    have e1 := dot_le_supp hKc hp 0
    have e2 := dot_le_supp hKc (hoKs n) π
    have e3 := dot_le_supp hKc hp π
    have e4 := dot_le_supp hKc (hoKs n) 0
    rw [mpc_dot_uvec_zero] at e1 e4
    rw [mpc_dot_uvec_pi] at e2 e3
    rw [width, zero_add] at hw
    have a1 := neg_abs_le (oPt Θ.ω).1
    have a2 := le_abs_self (oPt Θ.ω).1
    exact ⟨⟨by linarith, by linarith⟩, (mpc_cap_nonneg (hKs n).1 hp).1,
      (mpc_cap_le_one (hKs n).1 hp).2⟩
  -- Bolzano–Weierstrass for the support values on `Θ^◇`
  set v : ℕ → ({s // s ∈ mpcDiamond Θ} → ℝ) := fun n s => supp (Ks n) s.1 with hv
  have hR0 : 0 ≤ R := by positivity
  have hvb : ∀ n, v n ∈ Metric.closedBall (0 : {s // s ∈ mpcDiamond Θ} → ℝ) (R + 1) := by
    intro n
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by linarith)]
    intro s
    obtain ⟨q, hq, hqe⟩ := exists_dot_eq_supp (hKs n).1.2.1.2.1 (hKs n).1.2.1.1 s.1
    rw [Real.norm_eq_abs]
    show |supp (Ks n) s.1| ≤ R + 1
    rw [← hqe]
    have := mpc_abs_dot_uvec_le q s.1
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hbox n hq
    have : |q.1| ≤ R := abs_le.2 ⟨h1, h2⟩
    have : |q.2| ≤ 1 := abs_le.2 ⟨by linarith, h4⟩
    linarith
  obtain ⟨a, -, φ, hφ, hvlim⟩ := (isCompact_closedBall _ _).tendsto_subseq hvb
  set hinf : ℝ → ℝ := fun s => if hs : s ∈ mpcDiamond Θ then a ⟨s, hs⟩ else 0 with hhinf
  have hlim : ∀ s ∈ Θ.diamond, Tendsto (fun n => supp (Ks (φ n)) s) atTop (𝓝 (hinf s)) := by
    intro s hs
    have hs' := mpc_mem_mpcDiamond.2 hs
    have := tendsto_pi_nhds.1 hvlim ⟨s, hs'⟩
    simp only [hhinf, dite_eq_left hs']
    exact this
  obtain ⟨hLcap, -, hmemL, husc, hlsc⟩ := mpc_limit_polycap (fun n => hKs (φ n))
    (isCompact_Icc.prod isCompact_Icc) (fun n => hbox (φ n)) hlim
  refine ⟨capH Θ hinf, hLcap, hmemL _ (Eventually.of_forall fun n => hoKs (φ n)),
    fun K' hK' => ?_⟩
  have hK'M : polyArea Θ K' ≤ M := le_csSup hAbdd ⟨K', hK', rfl⟩
  suffices hML : M ≤ polyArea Θ (capH Θ hinf) by linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show 0 < ε / 3 by positivity)
  have hev : ∀ᶠ n in atTop, M - ε / 3 < polyArea Θ (Ks (φ n)) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have h1 := hlowKs (φ n)
    have h2 : (1 : ℝ) / (φ n + 1) ≤ 1 / (N + 1) := by
      apply div_le_div_of_nonneg_left zero_le_one (by positivity)
      have : (N : ℝ) ≤ φ n := by exact_mod_cast hn.trans (hφ.id_le n)
      linarith
    linarith
  obtain ⟨n, h1, h2, h3⟩ := (hev.and ((husc (ε / 3) (by positivity)).and
    (hlsc (ε / 3) (by positivity)))).exists
  rw [theorem3_2_3 hLcap]
  rw [theorem3_2_3 (hKs (φ n))] at h1
  linarith

end Existence

/-- **Theorem 3.4.3** (`thm:maximum-polygon-cap`). A maximum polygon cap exists for every angle set. -/
theorem theorem3_4_3 (Θ : AngleSet) : ∃ K, IsMaxPolygonCap Θ K := by
  exact mpc_theorem3_4_3_aux Θ

/-- An `x`-monotone polyline through `p_1, …, p_n` (Definition 3.4.2, `def:polyline`). -/
def IsXMonotonePolyline (P : Set (ℝ × ℝ)) : Prop :=
  ∃ (n : ℕ) (p : Fin (n + 1) → ℝ × ℝ), StrictMono (fun i => (p i).1) ∧
    P = ⋃ i : Fin n, segment ℝ (p i.castSucc) (p i.succ)

/-- The open half-line `l⃗_K` from `C_K⁺(ω)` in the direction `v_ω`, without its endpoint. -/
def rayLeft (K : Set (ℝ × ℝ)) (ω : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ s : ℝ, 0 < s ∧ p = cPlus K ω + s • vvec ω}

/-- The open half-line `r⃗_K` from `A_K⁻(0)` in the direction `u_0`, without its endpoint. -/
def rayRight (K : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := {p | ∃ s : ℝ, 0 < s ∧ p = aMinus K 0 + s • uvec 0}

/-- The polyline `𝐩_K` of a polygon cap (Definition 3.4.3, `def:polyline-of-cap`): the boundary of
`F_ω \ 𝒩_Θ(K)` without the two open half-lines. -/
def polyline (Θ : AngleSet) (K : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  frontier (fan Θ.ω \ polyNiche Θ K) \ (rayLeft K Θ.ω ∪ rayRight K)

/-! ### The polyline (Theorem 3.4.4) -/

section Polyline

open Filter Topology

section Rays

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

lemma mpc_G_left (hK : IsPolygonCap Θ K) {x : ℝ} (hx : x ≤ (cPlus K Θ.ω).1) :
    mpcG Θ K x = mpcL K Θ.ω x := by
  obtain ⟨h1, h2⟩ := mpc_left_of_C hK hx
  rw [mpcG, max_eq_left h1.le, h2]

lemma mpc_G_right (hK : IsPolygonCap Θ K) {x : ℝ} (hx : (aMinus K 0).1 ≤ x) :
    mpcG Θ K x = 0 := by
  obtain ⟨h1, h2⟩ := mpc_right_of_A hK hx
  rw [mpcG, max_eq_left h1.le, h2]

lemma mpc_frontier_eq (hK : IsPolygonCap Θ K) :
    frontier (fan Θ.ω \ polyNiche Θ K) = {p | p.2 = mpcG Θ K p.1} := by
  rw [mpc_fan_diff_eq hK]
  exact mpc_frontier_epigraph (mpc_continuous_mpcG Θ K)

lemma mpc_rayLeft_eq (hK : IsPolygonCap Θ K) :
    rayLeft K Θ.ω = {p | p.1 < (cPlus K Θ.ω).1 ∧ p.2 = mpcG Θ K p.1} := by
  have hω0 := mpc_omega_pos Θ
  have hsω : 0 < sin Θ.ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [mpc_omega_le Θ, pi_pos])
  obtain ⟨hC1, hC2⟩ := mpc_cPlus_coords hK
  set c := supp K (Θ.ω + π / 2)
  ext p
  simp only [rayLeft, mem_ofPred_eq]
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hp1 : (cPlus K Θ.ω + s • vvec Θ.ω).1 = -((c + s) * sin Θ.ω) := by
      simp only [Prod.fst_add, Prod.smul_fst, vvec_fst, smul_eq_mul, hC1]; ring
    refine ⟨by rw [hp1, hC1]; nlinarith, ?_⟩
    rw [mpc_G_left hK (by rw [hp1, hC1]; nlinarith), mpc_mpcL_omega hK, hp1]
    simp only [Prod.snd_add, Prod.smul_snd, vvec_snd, smul_eq_mul, hC2]
    field_simp
  · rintro ⟨h1, h2⟩
    rw [mpc_G_left hK h1.le, mpc_mpcL_omega hK] at h2
    refine ⟨-p.1 / sin Θ.ω - c, ?_, ?_⟩
    · rw [hC1] at h1
      rw [sub_pos, lt_div_iff₀ hsω]
      linarith
    · ext
      · simp only [Prod.fst_add, Prod.smul_fst, vvec_fst, smul_eq_mul, hC1]
        field_simp
        ring
      · simp only [Prod.snd_add, Prod.smul_snd, vvec_snd, smul_eq_mul, hC2, h2]
        field_simp
        ring

lemma mpc_rayRight_eq (hK : IsPolygonCap Θ K) :
    rayRight K = {p | (aMinus K 0).1 < p.1 ∧ p.2 = mpcG Θ K p.1} := by
  obtain ⟨hA1, hA2⟩ := mpc_aMinus_coords hK
  ext p
  simp only [rayRight, mem_ofPred_eq]
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hp1 : (aMinus K 0 + s • uvec 0).1 = (aMinus K 0).1 + s := by
      simp [mpc_uvec_zero]
    refine ⟨by rw [hp1]; linarith, ?_⟩
    rw [mpc_G_right hK (by rw [hp1]; linarith)]
    simp [mpc_uvec_zero, hA2]
  · rintro ⟨h1, h2⟩
    rw [mpc_G_right hK h1.le] at h2
    refine ⟨p.1 - (aMinus K 0).1, by linarith, ?_⟩
    ext
    · simp [mpc_uvec_zero]
    · simp [mpc_uvec_zero, hA2, h2]

lemma mpc_polyline_eq (hK : IsPolygonCap Θ K) :
    polyline Θ K = {p | (cPlus K Θ.ω).1 ≤ p.1 ∧ p.1 ≤ (aMinus K 0).1 ∧ p.2 = mpcG Θ K p.1} := by
  rw [polyline, mpc_frontier_eq hK, mpc_rayLeft_eq hK, mpc_rayRight_eq hK]
  ext p
  simp only [Set.mem_sdiff, mem_union, mem_ofPred_eq, not_or, not_and]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by by_contra h; push Not at h; exact absurd h1 (h2 h),
      by by_contra h; push Not at h; exact absurd h1 (h3 h), h1⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h3, fun h => absurd h (not_lt.2 h1), fun h => absurd h (not_lt.2 h2)⟩

end Rays


/-! ### Piecewise linear functions -/

/-- A continuous function without zeros on `(a, b)` has a constant sign on `[a, b]`. -/
lemma mpc_sign_const {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (h0 : ∀ x ∈ Ioo a b, f x ≠ 0) :
    (∀ x ∈ Icc a b, 0 ≤ f x) ∨ (∀ x ∈ Icc a b, f x ≤ 0) := by
  set m := (a + b) / 2
  have hm : m ∈ Ioo a b := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  rcases lt_or_gt_of_ne (h0 m hm) with hneg | hpos
  · right
    intro x hx
    by_contra hfx
    push Not at hfx
    rcases lt_trichotomy x m with hxm | rfl | hxm
    · obtain ⟨c, hc, hfc⟩ := intermediate_value_Ioo' hxm.le hf.continuousOn ⟨hneg, hfx⟩
      exact h0 c ⟨by linarith [hx.1, hc.1], by linarith [hc.2, hm.2]⟩ hfc
    · linarith
    · obtain ⟨c, hc, hfc⟩ := intermediate_value_Ioo hxm.le hf.continuousOn ⟨hneg, hfx⟩
      exact h0 c ⟨by linarith [hc.1, hm.1], by linarith [hc.2, hx.2]⟩ hfc
  · left
    intro x hx
    by_contra hfx
    push Not at hfx
    rcases lt_trichotomy x m with hxm | rfl | hxm
    · obtain ⟨c, hc, hfc⟩ := intermediate_value_Ioo hxm.le hf.continuousOn ⟨hfx, hpos⟩
      exact h0 c ⟨by linarith [hx.1, hc.1], by linarith [hc.2, hm.2]⟩ hfc
    · linarith
    · obtain ⟨c, hc, hfc⟩ := intermediate_value_Ioo' hxm.le hf.continuousOn ⟨hfx, hpos⟩
      exact h0 c ⟨by linarith [hc.1, hm.1], by linarith [hc.2, hx.2]⟩ hfc

/-- The segment between two points of the graph of a line is the graph over the interval. -/
lemma mpc_segment_graph (s c a b : ℝ) (hab : a ≤ b) :
    segment ℝ (a, mpcLineY s c a) (b, mpcLineY s c b) =
      {p | a ≤ p.1 ∧ p.1 ≤ b ∧ p.2 = mpcLineY s c p.1} := by
  rw [segment_eq_image']
  ext p
  simp only [mem_image, mem_Icc, mem_ofPred_eq]
  constructor
  · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
      Prod.snd_sub, smul_eq_mul, mpcLineY]
    refine ⟨by nlinarith, by nlinarith, ?_⟩
    ring
  · rintro ⟨h1, h2, h3⟩
    rcases eq_or_lt_of_le hab with rfl | hlt
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      ext
      · simp; linarith
      · simp [h3, le_antisymm h1 h2]
    · refine ⟨(p.1 - a) / (b - a), ⟨div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).2 (by linarith)⟩, ?_⟩
      have hba : b - a ≠ 0 := by linarith
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
        field_simp
        ring
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul, h3, mpcLineY]
        field_simp
        ring

/-- The intervals between consecutive points of an increasing sequence cover its range. -/
lemma mpc_iUnion_Icc {n : ℕ} {xs : Fin (n + 1) → ℝ} (hxs : StrictMono xs) (hn : 0 < n) :
    ⋃ i : Fin n, Icc (xs i.castSucc) (xs i.succ) = Icc (xs 0) (xs (Fin.last n)) := by
  apply subset_antisymm
  · refine iUnion_subset fun i => Icc_subset_Icc (hxs.monotone (Fin.zero_le _))
      (hxs.monotone (Fin.le_last _))
  · intro y ⟨hy0, hy1⟩
    -- the first index `k` with `y ≤ xs k`
    have hex : ∃ k : ℕ, ∃ hk : k < n + 1, y ≤ xs ⟨k, hk⟩ := ⟨n, Nat.lt_succ_self n, hy1⟩
    classical
    let k := Nat.find hex
    obtain ⟨hk, hyk⟩ := Nat.find_spec hex
    rw [mem_iUnion]
    by_cases hk0 : k = 0
    · refine ⟨⟨0, hn⟩, ?_, ?_⟩
      · have : (Fin.castSucc (⟨0, hn⟩ : Fin n)) = 0 := rfl
        rw [this]; exact hy0
      · have e : xs ⟨k, hk⟩ ≤ xs (Fin.succ ⟨0, hn⟩) := by
          apply hxs.monotone
          show k ≤ 1
          omega
        exact hyk.trans e
    · have hk1 : k - 1 < n := by omega
      refine ⟨⟨k - 1, hk1⟩, ?_, ?_⟩
      · have hlt := Nat.find_min hex (show k - 1 < k by omega)
        push Not at hlt
        exact (hlt (by omega)).le
      · have : (Fin.succ (⟨k - 1, hk1⟩ : Fin n)) = ⟨k, hk⟩ := by
          ext; simp; omega
        rw [this]; exact hyk

/-! ### The breakpoints and vertices of the polyline -/

/-- The abscissa where the lines `l(s, c)` and `l(s', c')` meet. -/
noncomputable def mpcCrossX (s c s' c' : ℝ) : ℝ := (c * sin s' - c' * sin s) / sin (s' - s)

/-- The candidate breakpoints of the polyline: the ends and the crossings of the inner walls. -/
noncomputable def mpcBreaks (Θ : AngleSet) (K : Set (ℝ × ℝ)) : Finset ℝ :=
  (((mpcDiamond Θ ×ˢ mpcDiamond Θ).image
      (fun q => mpcCrossX q.1 (supp K q.1 - 1) q.2 (supp K q.2 - 1))) ∪
    {(cPlus K Θ.ω).1, (aMinus K 0).1}).filter
    (fun x => (cPlus K Θ.ω).1 ≤ x ∧ x ≤ (aMinus K 0).1)

section Vertices

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

lemma mpc_breaks_bounds {x : ℝ} (hx : x ∈ mpcBreaks Θ K) :
    (cPlus K Θ.ω).1 ≤ x ∧ x ≤ (aMinus K 0).1 :=
  (Finset.mem_filter.1 hx).2

lemma mpc_C_mem_breaks (hK : IsPolygonCap Θ K) : (cPlus K Θ.ω).1 ∈ mpcBreaks Θ K :=
  Finset.mem_filter.2 ⟨Finset.mem_union_right _ (by simp), le_rfl, (mpc_C_lt_A hK).le⟩

lemma mpc_A_mem_breaks (hK : IsPolygonCap Θ K) : (aMinus K 0).1 ∈ mpcBreaks Θ K :=
  Finset.mem_filter.2 ⟨Finset.mem_union_right _ (by simp), (mpc_C_lt_A hK).le, le_rfl⟩

lemma mpc_diamond_sin_sub_ne {s s' : ℝ} (hs : s ∈ Θ.diamond) (hs' : s' ∈ Θ.diamond)
    (h : s ≠ s') : sin (s' - s) ≠ 0 := by
  have h1 := mpc_diamond_bounds hs
  have h2 := mpc_diamond_bounds hs'
  have h3 := mpc_diamond_lt_pi hs
  have h4 := mpc_diamond_lt_pi hs'
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  · exact (sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)).ne

/-- A crossing of two inner walls between the ends is a breakpoint. -/
lemma mpc_cross_mem_breaks {s s' : ℝ} (hs : s ∈ Θ.diamond) (hs' : s' ∈ Θ.diamond)
    (h : s ≠ s') {x : ℝ} (hx : (cPlus K Θ.ω).1 ≤ x ∧ x ≤ (aMinus K 0).1)
    (heq : mpcL K s x = mpcL K s' x) : x ∈ mpcBreaks Θ K := by
  have hx' := mpc_lineY_eq_imp (mpc_sin_pos_of_diamond hs).ne'
    (mpc_sin_pos_of_diamond hs').ne' (mpc_diamond_sin_sub_ne hs hs' h) heq
  refine Finset.mem_filter.2 ⟨Finset.mem_union_left _ (Finset.mem_image.2 ⟨(s, s'), ?_, ?_⟩), hx⟩
  · exact Finset.mem_product.2 ⟨mpc_mem_mpcDiamond.2 hs, mpc_mem_mpcDiamond.2 hs'⟩
  · exact hx'.symm

/-- On an interval without breakpoints, the inner walls are ordered. -/
lemma mpc_walls_ordered {a b : ℝ} (hab : a < b) (ha : (cPlus K Θ.ω).1 ≤ a)
    (hb : b ≤ (aMinus K 0).1) (hgap : ∀ y ∈ mpcBreaks Θ K, ¬ (a < y ∧ y < b))
    {s s' : ℝ} (hs : s ∈ Θ.diamond) (hs' : s' ∈ Θ.diamond) :
    (∀ x ∈ Icc a b, mpcL K s x ≤ mpcL K s' x) ∨ (∀ x ∈ Icc a b, mpcL K s' x ≤ mpcL K s x) := by
  by_cases h : s = s'
  · subst h; exact Or.inl fun _ _ => le_rfl
  · rcases mpc_sign_const ((mpc_continuous_mpcL K s').sub (mpc_continuous_mpcL K s)) hab
      (fun x hx h0 => hgap x (mpc_cross_mem_breaks hs hs' h
        ⟨by linarith [hx.1], by linarith [hx.2]⟩ (by linarith [sub_eq_zero.1 h0])) hx) with h1 | h1
    · left; intro x hx; have := h1 x hx; simp only [Pi.sub_apply] at this; linarith
    · right; intro x hx; have := h1 x hx; simp only [Pi.sub_apply] at this; linarith

/-- On an interval without breakpoints, the lower boundary of `F_ω \ 𝒩_Θ(K)` is a single wall. -/
lemma mpc_piece {a b : ℝ} (hab : a < b) (ha : (cPlus K Θ.ω).1 ≤ a)
    (hb : b ≤ (aMinus K 0).1) (hgap : ∀ y ∈ mpcBreaks Θ K, ¬ (a < y ∧ y < b)) :
    ∃ s ∈ Θ.diamond, ∀ x ∈ Icc a b, mpcG Θ K x = mpcL K s x := by
  let P : (ℝ → ℝ) → Prop := fun f => ∃ s ∈ Θ.diamond, ∀ x ∈ Icc a b, f x = mpcL K s x
  have hmax : ∀ f g, P f → P g → P (fun x => max (f x) (g x)) := by
    rintro f g ⟨s, hs, hf⟩ ⟨s', hs', hg⟩
    rcases mpc_walls_ordered hab ha hb hgap hs hs' with h | h
    · exact ⟨s', hs', fun x hx => by dsimp only; rw [hf x hx, hg x hx, max_eq_right (h x hx)]⟩
    · exact ⟨s, hs, fun x hx => by dsimp only; rw [hf x hx, hg x hx, max_eq_left (h x hx)]⟩
  have hmin : ∀ f g, P f → P g → P (fun x => min (f x) (g x)) := by
    rintro f g ⟨s, hs, hf⟩ ⟨s', hs', hg⟩
    rcases mpc_walls_ordered hab ha hb hgap hs hs' with h | h
    · exact ⟨s, hs, fun x hx => by dsimp only; rw [hf x hx, hg x hx, min_eq_left (h x hx)]⟩
    · exact ⟨s', hs', fun x hx => by dsimp only; rw [hf x hx, hg x hx, min_eq_right (h x hx)]⟩
  have hL : ∀ s ∈ Θ.diamond, P (mpcL K s) := fun s hs => ⟨s, hs, fun _ _ => rfl⟩
  have hlow : P (mpcLow Θ K) :=
    hmax _ _ (hL _ (Or.inr (Or.inl rfl))) (hL _ (Or.inr (Or.inr rfl)))
  have htop : P (mpcTop Θ K) := by
    rw [mpc_mpcTop_eq]
    apply Finset.sup'_induction (p := P)
    · intro f hf g hg; exact hmax f g hf hg
    · intro t ht
      exact hmin _ _ (hL _ (Or.inl (Or.inl ht))) (hL _ (Or.inl (Or.inr ⟨t, ht, rfl⟩)))
  exact hmax _ _ hlow htop

/-- The vertices of the polyline: an increasing enumeration of the breakpoints, with the wall
`mpcL K (s i)` followed on the `i`-th piece. -/
lemma mpc_polyline_data (hK : IsPolygonCap Θ K) :
    ∃ (n : ℕ) (xs : Fin (n + 1) → ℝ) (sp : Fin n → ℝ), 0 < n ∧ StrictMono xs ∧
      xs 0 = (cPlus K Θ.ω).1 ∧ xs (Fin.last n) = (aMinus K 0).1 ∧
      (∀ i, sp i ∈ Θ.diamond) ∧
      (∀ i, ∀ x ∈ Icc (xs i.castSucc) (xs i.succ), mpcG Θ K x = mpcL K (sp i) x) := by
  set B := mpcBreaks Θ K
  have hC := mpc_C_mem_breaks hK
  have hA := mpc_A_mem_breaks hK
  have hCA := mpc_C_lt_A hK
  have hcard : 1 < B.card := Finset.one_lt_card.2 ⟨_, hC, _, hA, hCA.ne⟩
  set n := B.card - 1 with hn
  have hcard' : B.card = n + 1 := by omega
  set xs := B.orderEmbOfFin hcard' with hxs
  have hmono : StrictMono xs := xs.strictMono
  have hmem : ∀ i, xs i ∈ B := fun i => Finset.orderEmbOfFin_mem B hcard' i
  have hsurj : ∀ y ∈ B, ∃ i, xs i = y := by
    intro y hy
    have : y ∈ Set.range xs := by
      rw [hxs, Finset.range_orderEmbOfFin]; exact hy
    exact this
  have h0 : xs 0 = (cPlus K Θ.ω).1 := by
    have e := Finset.orderEmbOfFin_zero hcard' (Nat.succ_pos n)
    have : (0 : Fin (n + 1)) = ⟨0, Nat.succ_pos n⟩ := rfl
    rw [this, e]
    exact le_antisymm (B.min'_le _ hC) (B.le_min' _ _ fun y hy => (mpc_breaks_bounds hy).1)
  have hlast : xs (Fin.last n) = (aMinus K 0).1 := by
    have e := Finset.orderEmbOfFin_last hcard' (Nat.succ_pos n)
    have : Fin.last n = ⟨n + 1 - 1, Nat.sub_lt (Nat.succ_pos n) (Nat.succ_pos 0)⟩ := by
      ext; simp
    rw [this, e]
    exact le_antisymm (B.max'_le _ _ fun y hy => (mpc_breaks_bounds hy).2) (B.le_max' _ hA)
  have hpiece : ∀ i : Fin n, ∃ s ∈ Θ.diamond,
      ∀ x ∈ Icc (xs i.castSucc) (xs i.succ), mpcG Θ K x = mpcL K s x := by
    intro i
    apply mpc_piece (hmono (Fin.castSucc_lt_succ (i := i))) (mpc_breaks_bounds (hmem _)).1
      (mpc_breaks_bounds (hmem _)).2
    intro y hy ⟨h1, h2⟩
    obtain ⟨j, rfl⟩ := hsurj y hy
    have e1 := hmono.lt_iff_lt.1 h1
    have e2 := hmono.lt_iff_lt.1 h2
    rw [Fin.lt_def] at e1 e2
    simp at e1 e2
    omega
  choose sp hsp hspG using hpiece
  exact ⟨n, xs, sp, by omega, hmono, h0, hlast, hsp, hspG⟩

end Vertices


/-- The pieces of the polyline are segments. -/
lemma mpc_segment_piece {Θ : AngleSet} {K : Set (ℝ × ℝ)} {a b s : ℝ} (hab : a ≤ b)
    (hG : ∀ x ∈ Icc a b, mpcG Θ K x = mpcL K s x) :
    segment ℝ (a, mpcG Θ K a) (b, mpcG Θ K b) = {q | a ≤ q.1 ∧ q.1 ≤ b ∧ q.2 = mpcG Θ K q.1} := by
  rw [hG a ⟨le_rfl, hab⟩, hG b ⟨hab, le_rfl⟩, mpcL, mpcL, mpc_segment_graph _ _ _ _ hab]
  ext q
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [hG q.1 ⟨h1, h2⟩, mpcL]; exact h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [h3, hG q.1 ⟨h1, h2⟩, mpcL]⟩

end Polyline

/-- **Theorem 3.4.4** (`thm:polyline`). For a polygon cap `K`, the boundary of `F_ω \ 𝒩_Θ(K)` is the
disjoint union, from left to right, of `l⃗_K`, an `x`-monotone polyline `𝐩_K` from `C_K⁺(ω)` to
`A_K⁻(0)` whose segments have normal angles in `Θ^◇`, and `r⃗_K`.

The edge lengths `ℓ` are real numbers: the original statement wrote `∃ ℓ > 0`, which Lean elaborated
with `ℓ : ℕ` (the only constraint on `ℓ` being the scalar action `ℓ • vvec s`); that version is false
(a polygon cap whose polyline is one horizontal segment of length `5/2` admits no subdivision into
segments of natural length). -/
theorem theorem3_4_4 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) :
    frontier (fan Θ.ω \ polyNiche Θ K) = rayLeft K Θ.ω ∪ polyline Θ K ∪ rayRight K ∧
      Disjoint (rayLeft K Θ.ω) (polyline Θ K ∪ rayRight K) ∧ Disjoint (polyline Θ K) (rayRight K) ∧
      ∃ (n : ℕ) (p : Fin (n + 1) → ℝ × ℝ), p 0 = cPlus K Θ.ω ∧ p (Fin.last n) = aMinus K 0 ∧
        StrictMono (fun i => (p i).1) ∧ polyline Θ K = ⋃ i : Fin n, segment ℝ (p i.castSucc) (p i.succ) ∧
        ∀ i : Fin n, ∃ s ∈ Θ.diamond, ∃ ℓ > (0 : ℝ), p i.castSucc - p i.succ = ℓ • vvec s := by
  have hCA := mpc_C_lt_A hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mpc_frontier_eq hK, mpc_rayLeft_eq hK, mpc_polyline_eq hK, mpc_rayRight_eq hK]
    ext p
    simp only [mem_union, mem_ofPred_eq]
    constructor
    · intro h
      by_cases h1 : p.1 < (cPlus K Θ.ω).1
      · exact Or.inl (Or.inl ⟨h1, h⟩)
      · by_cases h2 : (aMinus K 0).1 < p.1
        · exact Or.inr ⟨h2, h⟩
        · push Not at h1 h2
          exact Or.inl (Or.inr ⟨h1, h2, h⟩)
    · rintro ((⟨_, h⟩ | ⟨_, _, h⟩) | ⟨_, h⟩) <;> exact h
  · rw [mpc_rayLeft_eq hK, mpc_polyline_eq hK, mpc_rayRight_eq hK, Set.disjoint_left]
    rintro p ⟨h1, _⟩ (⟨h2, _, _⟩ | ⟨h2, _⟩) <;> linarith
  · rw [mpc_polyline_eq hK, mpc_rayRight_eq hK, Set.disjoint_left]
    rintro p ⟨_, h1, _⟩ ⟨h2, _⟩
    linarith
  · obtain ⟨n, xs, sp, hn, hmono, h0, hlast, hsp, hspG⟩ := mpc_polyline_data hK
    refine ⟨n, fun i => (xs i, mpcG Θ K (xs i)), ?_, ?_, hmono, ?_, ?_⟩
    · show (xs 0, mpcG Θ K (xs 0)) = cPlus K Θ.ω
      have hsω : 0 < sin Θ.ω := mpc_sin_pos_of_diamond (Θ := Θ) (Or.inr (Or.inl rfl))
      rw [h0, mpc_G_left hK le_rfl, mpc_mpcL_omega hK]
      obtain ⟨hC1, hC2⟩ := mpc_cPlus_coords hK
      ext
      · rfl
      · simp only
        rw [hC1, hC2]
        field_simp
    · show (xs (Fin.last n), mpcG Θ K (xs (Fin.last n))) = aMinus K 0
      rw [hlast, mpc_G_right hK le_rfl]
      ext
      · rfl
      · exact (mpc_aMinus_coords hK).2.symm
    · have hseg : ∀ i : Fin n, segment ℝ (xs i.castSucc, mpcG Θ K (xs i.castSucc))
          (xs i.succ, mpcG Θ K (xs i.succ)) =
          {q | xs i.castSucc ≤ q.1 ∧ q.1 ≤ xs i.succ ∧ q.2 = mpcG Θ K q.1} := fun i =>
        mpc_segment_piece (hmono (Fin.castSucc_lt_succ (i := i))).le (hspG i)
      have hcov := mpc_iUnion_Icc hmono hn
      rw [h0, hlast] at hcov
      rw [mpc_polyline_eq hK]
      ext p
      simp only [mem_iUnion, mem_ofPred_eq, hseg]
      constructor
      · rintro ⟨h1, h2, h3⟩
        have : p.1 ∈ ⋃ i : Fin n, Icc (xs i.castSucc) (xs i.succ) := by
          rw [hcov]; exact ⟨h1, h2⟩
        obtain ⟨i, hi⟩ := mem_iUnion.1 this
        exact ⟨i, hi.1, hi.2, h3⟩
      · rintro ⟨i, h1, h2, h3⟩
        have : p.1 ∈ Icc (cPlus K Θ.ω).1 (aMinus K 0).1 := by
          rw [← hcov]; exact mem_iUnion.2 ⟨i, h1, h2⟩
        exact ⟨this.1, this.2, h3⟩
    · intro i
      have hi := hmono (Fin.castSucc_lt_succ (i := i))
      have hs := mpc_sin_pos_of_diamond (hsp i)
      refine ⟨sp i, hsp i, (xs i.succ - xs i.castSucc) / sin (sp i), div_pos (by linarith) hs, ?_⟩
      show (xs i.castSucc, mpcG Θ K (xs i.castSucc)) - (xs i.succ, mpcG Θ K (xs i.succ)) = _
      rw [hspG i _ ⟨le_rfl, hi.le⟩, hspG i _ ⟨hi.le, le_rfl⟩]
      ext
      · simp only [Prod.fst_sub, Prod.smul_fst, vvec_fst, smul_eq_mul]
        field_simp
        ring
      · simp only [Prod.snd_sub, Prod.smul_snd, vvec_snd, smul_eq_mul, mpcL, mpcLineY]
        field_simp
        ring

/-- `τ_K(t)`, the total length of the edges of the polyline `𝐩_K` with normal angle `t`
(Definition 3.4.4, `def:polyline-length`): the sum over the parallel lines `l(t, c)` of the length of
the part of `𝐩_K` on them. Only finitely many terms are nonzero. -/
noncomputable def tau (Θ : AngleSet) (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ :=
  ∑' c : ℝ, lineLength t c (polyline Θ K)

/-! ### The lengths `τ_K(t)` of the polyline -/

section Tau

open Filter Topology MeasureTheory

/-- Telescoping over `Fin`. -/
lemma mpc_sum_telescope {M : Type*} [AddCommGroup M] {n : ℕ} (g : Fin (n + 1) → M) :
    ∑ i : Fin n, (g i.succ - g i.castSucc) = g (Fin.last n) - g 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have := ih (fun i => g i.castSucc)
    simp only [Fin.succ_castSucc] at this ⊢
    rw [this]
    simp only [Fin.castSucc_zero, Fin.succ_last]
    abel

/-- The length of `X ∩ l(s, c)` computed in the abscissa. -/
lemma mpc_lineLength_eq {s : ℝ} (hs : 0 < sin s) (c : ℝ) (X : Set (ℝ × ℝ)) :
    lineLength s c X = (volume {x : ℝ | (x, mpcLineY s c x) ∈ X}).toReal / sin s := by
  set S := {x : ℝ | (x, mpcLineY s c x) ∈ X}
  have hpre : {σ : ℝ | c • uvec s + σ • vvec s ∈ X} =
      (fun σ => -sin s * σ) ⁻¹' ((fun y => c * cos s + y) ⁻¹' S) := by
    ext σ
    simp only [mem_ofPred_eq, mem_preimage, S]
    have e : c • uvec s + σ • vvec s = (c * cos s + -sin s * σ,
        mpcLineY s c (c * cos s + -sin s * σ)) := by
      ext
      · simp [uvec, vvec]; ring
      · simp only [Prod.snd_add, Prod.smul_snd, uvec_snd, vvec_snd, smul_eq_mul, mpcLineY]
        field_simp
        linear_combination c * sin_sq_add_cos_sq s
    rw [e]
  rw [lineLength, hpre, Real.volume_preimage_mul_left (neg_ne_zero.2 hs.ne'),
    measure_preimage_add, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv,
    abs_neg, abs_of_pos hs]
  ring


/-- Intervals between consecutive points of an increasing sequence are almost disjoint. -/
lemma mpc_measure_union_Icc {n : ℕ} {xs : Fin (n + 1) → ℝ} (hxs : StrictMono xs)
    (S : Finset (Fin n)) :
    volume (⋃ i ∈ S, Icc (xs i.castSucc) (xs i.succ)) =
      ∑ i ∈ S, ENNReal.ofReal (xs i.succ - xs i.castSucc) := by
  rw [measure_biUnion_finset₀]
  · simp only [Real.volume_Icc]
  · intro i _ j _ hij
    have key : ∀ i j : Fin n, i < j →
        AEDisjoint volume (Icc (xs i.castSucc) (xs i.succ)) (Icc (xs j.castSucc) (xs j.succ)) := by
      intro i j hlt
      apply measure_mono_null (t := {xs i.succ}) _ (measure_singleton _)
      rintro x ⟨⟨_, h2⟩, ⟨h3, _⟩⟩
      have : xs i.succ ≤ xs j.castSucc := by
        apply hxs.monotone
        rw [Fin.le_def]; simp; exact hlt
      exact le_antisymm h2 (this.trans h3)
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · exact (key j i h).symm
  · intro i _; exact measurableSet_Icc.nullMeasurableSet

section TauComp

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

/-- `τ_K(t)` in terms of the polyline data: the total horizontal extent of the pieces on the wall
with normal angle `t`, divided by `sin t`. -/
lemma mpc_tau_eq (hK : IsPolygonCap Θ K) {n : ℕ} {xs : Fin (n + 1) → ℝ} {sp : Fin n → ℝ}
    (hn : 0 < n) (hmono : StrictMono xs) (h0 : xs 0 = (cPlus K Θ.ω).1)
    (hlast : xs (Fin.last n) = (aMinus K 0).1) (hsp : ∀ i, sp i ∈ Θ.diamond)
    (hspG : ∀ i, ∀ x ∈ Icc (xs i.castSucc) (xs i.succ), mpcG Θ K x = mpcL K (sp i) x)
    {t : ℝ} (ht : t ∈ Θ.diamond) :
    tau Θ K t = (∑ i ∈ Finset.univ.filter (fun i => sp i = t),
      (xs i.succ - xs i.castSucc)) / sin t := by
  have hst := mpc_sin_pos_of_diamond ht
  have hcov := mpc_iUnion_Icc hmono hn
  rw [h0, hlast] at hcov
  have hpoly := mpc_polyline_eq hK
  -- membership in a piece
  have hpiece : ∀ x, (cPlus K Θ.ω).1 ≤ x → x ≤ (aMinus K 0).1 →
      ∃ i : Fin n, x ∈ Icc (xs i.castSucc) (xs i.succ) := by
    intro x h1 h2
    have : x ∈ ⋃ i : Fin n, Icc (xs i.castSucc) (xs i.succ) := by rw [hcov]; exact ⟨h1, h2⟩
    exact mem_iUnion.1 this
  -- the abscissae on `l(t, c)`
  set F : ℝ → Finset ℝ := fun c =>
    Finset.univ.image (fun i => mpcCrossX t c (sp i) (supp K (sp i) - 1)) with hF
  have hsub : ∀ c, {x : ℝ | (x, mpcLineY t c x) ∈ polyline Θ K} ⊆
      (⋃ i ∈ Finset.univ.filter (fun i => sp i = t), Icc (xs i.castSucc) (xs i.succ)) ∪
        (F c : Set ℝ) := by
    intro c x hx
    rw [hpoly] at hx
    obtain ⟨h1, h2, h3⟩ := hx
    obtain ⟨i, hi⟩ := hpiece x h1 h2
    by_cases hit : sp i = t
    · left
      exact mem_iUnion₂.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hit⟩, hi⟩
    · right
      simp only at h3
      rw [hspG i x hi, mpcL] at h3
      have := mpc_lineY_eq_imp hst.ne' (mpc_sin_pos_of_diamond (hsp i)).ne'
        (mpc_diamond_sin_sub_ne ht (hsp i) (Ne.symm hit)) h3
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_univ _, this.symm⟩)
  have hFnull : ∀ c, volume (F c : Set ℝ) = 0 := fun c => (F c).finite_toSet.measure_zero _
  -- the other parallel lines meet the polyline in finitely many points
  have hzero : ∀ c, c ≠ supp K t - 1 → lineLength t c (polyline Θ K) = 0 := by
    intro c hc
    rw [mpc_lineLength_eq hst]
    have : volume {x : ℝ | (x, mpcLineY t c x) ∈ polyline Θ K} = 0 := by
      apply measure_mono_null _ (hFnull c)
      intro x hx
      rcases hsub c hx with h | h
      · exfalso
        obtain ⟨i, hi, hx'⟩ := mem_iUnion₂.1 h
        have hit := (Finset.mem_filter.1 hi).2
        rw [hpoly] at hx
        obtain ⟨-, -, h3⟩ := hx
        simp only at h3
        rw [hspG i x hx', hit, mpcL] at h3
        exact hc (mpc_lineY_inj hst.ne' h3)
      · exact h
    rw [this, ENNReal.toReal_zero, zero_div]
  -- the wall itself
  have hmain : lineLength t (supp K t - 1) (polyline Θ K) =
      (∑ i ∈ Finset.univ.filter (fun i => sp i = t), (xs i.succ - xs i.castSucc)) / sin t := by
    rw [mpc_lineLength_eq hst]
    congr 1
    set U := ⋃ i ∈ Finset.univ.filter (fun i => sp i = t), Icc (xs i.castSucc) (xs i.succ)
    have hUS : U ⊆ {x : ℝ | (x, mpcLineY t (supp K t - 1) x) ∈ polyline Θ K} := by
      intro x hx
      obtain ⟨i, hi, hx'⟩ := mem_iUnion₂.1 hx
      have hit := (Finset.mem_filter.1 hi).2
      rw [mem_ofPred_eq, hpoly]
      have hb0 : xs 0 ≤ xs i.castSucc := hmono.monotone (Fin.zero_le _)
      have hb1 : xs i.succ ≤ xs (Fin.last n) := hmono.monotone (Fin.le_last _)
      rw [h0] at hb0
      rw [hlast] at hb1
      refine ⟨hb0.trans hx'.1, hx'.2.trans hb1, ?_⟩
      simp only
      rw [hspG i x hx', hit, mpcL]
    have hvol : volume {x : ℝ | (x, mpcLineY t (supp K t - 1) x) ∈ polyline Θ K} = volume U := by
      apply le_antisymm
      · calc _ ≤ volume (U ∪ (F (supp K t - 1) : Set ℝ)) := measure_mono (hsub _)
          _ ≤ volume U + volume (F (supp K t - 1) : Set ℝ) := measure_union_le _ _
          _ = volume U := by rw [hFnull, add_zero]
      · exact measure_mono hUS
    rw [hvol, mpc_measure_union_Icc hmono, ENNReal.toReal_sum (fun i _ => ENNReal.ofReal_ne_top)]
    apply Finset.sum_congr rfl
    intro i _
    exact ENNReal.toReal_ofReal (by linarith [hmono (Fin.castSucc_lt_succ (i := i))])
  rw [tau, tsum_eq_single (supp K t - 1) hzero, hmain]

end TauComp

lemma mpc_dot_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ × ℝ) (v : ℝ × ℝ) :
    dot (∑ i ∈ S, f i) v = ∑ i ∈ S, dot (f i) v := by
  simp only [dot, Prod.fst_sum, Prod.snd_sum, Finset.sum_mul, ← Finset.sum_add_distrib]

/-- Partial telescoping over `Fin`. -/
lemma mpc_sum_telescope_from {M : Type*} [AddCommGroup M] {n : ℕ} (g : Fin (n + 1) → M)
    (k : Fin (n + 1)) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.castSucc), (g i.castSucc - g i.succ) =
      g k - g (Fin.last n) := by
  have htel := mpc_sum_telescope (fun j => g (max j k))
  rw [max_eq_left (Fin.le_last k), max_eq_right (Fin.zero_le k)] at htel
  rw [Finset.sum_filter, ← neg_sub (g (Fin.last n)), ← htel, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · rw [max_eq_left (h.trans (Fin.castSucc_lt_succ (i := i)).le), max_eq_left h]
    abel
  · push Not at h
    have h' : i.succ ≤ k := Fin.castSucc_lt_iff_succ_le.1 h
    rw [max_eq_right h', max_eq_right h.le]
    abel

section Balance

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

/-- `∑_{t ∈ Θ^◇} τ_K(t) sin t = A_K⁻(0)_x - C_K⁺(ω)_x`. -/
lemma mpc_sum_tau_sin (hK : IsPolygonCap Θ K) :
    ∑ t ∈ mpcDiamond Θ, tau Θ K t * sin t = (aMinus K 0).1 - (cPlus K Θ.ω).1 := by
  obtain ⟨n, xs, sp, hn, hmono, h0, hlast, hsp, hspG⟩ := mpc_polyline_data hK
  have e : ∀ t ∈ mpcDiamond Θ, tau Θ K t * sin t =
      ∑ i ∈ Finset.univ.filter (fun i => sp i = t), (xs i.succ - xs i.castSucc) := by
    intro t ht
    have ht' := mpc_mem_mpcDiamond.1 ht
    rw [mpc_tau_eq hK hn hmono h0 hlast hsp hspG ht',
      div_mul_cancel₀ _ (mpc_sin_pos_of_diamond ht').ne']
  rw [Finset.sum_congr rfl e, Finset.sum_fiberwise_of_maps_to
    (fun i _ => mpc_mem_mpcDiamond.2 (hsp i)), mpc_sum_telescope, h0, hlast]

/-- `∑_{t ∈ Θ^◇} σ_K(t) sin t = A_K⁻(0)_x - C_K⁺(ω)_x`. -/
lemma mpc_sum_sigma_sin (hK : IsPolygonCap Θ K) :
    ∑ t ∈ mpcDiamond Θ, sigmaAt K t * sin t = (aMinus K 0).1 - (cPlus K Θ.ω).1 := by
  have h := congrArg Prod.fst (mpc_walk_total hK)
  simp only [Prod.fst_sub, Prod.fst_sum, Prod.smul_fst, vvec_fst, smul_eq_mul] at h
  have : ∑ t ∈ mpcDiamond Θ, sigmaAt K t * -sin t = -∑ t ∈ mpcDiamond Θ, sigmaAt K t * sin t := by
    rw [← Finset.sum_neg_distrib]; congr 1; ext t; ring
  rw [this] at h
  linarith

end Balance

end Tau

/-! ### The frontier of the polygon niche on the walls (Lemma 3.4.5) -/

section NicheWalls

open Filter Topology MeasureTheory


/-- Two sets of reals that agree up to finite sets have the same measure. -/
lemma mpc_volume_eq_of_finite_diff {S T F G : Set ℝ} (hF : F.Finite) (hG : G.Finite)
    (h1 : S ⊆ T ∪ F) (h2 : T ⊆ S ∪ G) : volume S = volume T := by
  apply le_antisymm
  · calc volume S ≤ volume (T ∪ F) := measure_mono h1
      _ ≤ volume T + volume F := measure_union_le _ _
      _ = volume T := by rw [hF.measure_zero, add_zero]
  · calc volume T ≤ volume (S ∪ G) := measure_mono h2
      _ ≤ volume S + volume G := measure_union_le _ _
      _ = volume S := by rw [hG.measure_zero, add_zero]

lemma mpc_mem_wallBVec (S : Set (ℝ × ℝ)) (t : ℝ) (P : ℝ × ℝ) :
    P ∈ wallBVec S t ↔ dot P (uvec t) = supp S t - 1 ∧
      dot P (uvec (t + π / 2)) ≤ supp S (t + π / 2) - 1 := by
  rw [uvec_add_pi_div_two]
  constructor
  · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
    have hq : q = (0, q.2) := by ext; exact hq1; rfl
    rw [hq]
    simp only [hallwayMap, rot, dot, uvec, vvec, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    constructor
    · linear_combination (supp S t - 1) * sin_sq_add_cos_sq t
    · have e : (cos t * 0 - sin t * q.2 + (supp S t - 1) * cos t + (supp S (t + π / 2) - 1) *
          -sin t) * -sin t + (sin t * 0 + cos t * q.2 + (supp S t - 1) * sin t +
          (supp S (t + π / 2) - 1) * cos t) * cos t = q.2 + (supp S (t + π / 2) - 1) := by
        linear_combination (q.2 + (supp S (t + π / 2) - 1)) * sin_sq_add_cos_sq t
      rw [e]; linarith
  · rintro ⟨h1, h2⟩
    refine ⟨(0, dot P (vvec t) - (supp S (t + π / 2) - 1)), ⟨rfl, by simp only; linarith⟩, ?_⟩
    have hP := eq_dot_uvec_smul_add P t
    rw [h1] at hP
    conv_rhs => rw [hP]
    ext <;> simp only [hallwayMap, rot, uvec, vvec, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] <;> ring

lemma mpc_mem_wallDVec (S : Set (ℝ × ℝ)) (t : ℝ) (P : ℝ × ℝ) :
    P ∈ wallDVec S t ↔ dot P (uvec (t + π / 2)) = supp S (t + π / 2) - 1 ∧
      dot P (uvec t) ≤ supp S t - 1 := by
  rw [uvec_add_pi_div_two]
  constructor
  · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
    have hq : q = (q.1, 0) := by ext; rfl; exact hq1
    rw [hq]
    simp only [hallwayMap, rot, dot, uvec, vvec, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    constructor
    · linear_combination (supp S (t + π / 2) - 1) * sin_sq_add_cos_sq t
    · have e : (cos t * q.1 - sin t * 0 + (supp S t - 1) * cos t + (supp S (t + π / 2) - 1) *
          -sin t) * cos t + (sin t * q.1 + cos t * 0 + (supp S t - 1) * sin t +
          (supp S (t + π / 2) - 1) * cos t) * sin t = q.1 + (supp S t - 1) := by
        linear_combination (q.1 + (supp S t - 1)) * sin_sq_add_cos_sq t
      rw [e]; linarith
  · rintro ⟨h1, h2⟩
    refine ⟨(dot P (uvec t) - (supp S t - 1), 0), ⟨rfl, by simp only; linarith⟩, ?_⟩
    have hP := eq_dot_uvec_smul_add P t
    rw [h1] at hP
    conv_rhs => rw [hP]
    ext <;> simp only [hallwayMap, rot, uvec, vvec, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] <;> ring

section NicheFrontier

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

/-- `τ_K(t)` is the length of the polyline on the wall `l(t, h_K(t) - 1)`. -/
lemma mpc_tau_eq_lineLength (hK : IsPolygonCap Θ K) {t : ℝ} (ht : t ∈ Θ.diamond) :
    tau Θ K t = lineLength t (supp K t - 1) (polyline Θ K) := by
  obtain ⟨n, xs, sp, hn, hmono, h0, hlast, hsp, hspG⟩ := mpc_polyline_data hK
  have hst := mpc_sin_pos_of_diamond ht
  have hcov := mpc_iUnion_Icc hmono hn
  rw [h0, hlast] at hcov
  have hpoly := mpc_polyline_eq hK
  rw [tau]
  apply tsum_eq_single
  intro c hc
  rw [mpc_lineLength_eq hst]
  have : volume {x : ℝ | (x, mpcLineY t c x) ∈ polyline Θ K} = 0 := by
    apply measure_mono_null _ ((Finset.univ.image
      (fun i => mpcCrossX t c (sp i) (supp K (sp i) - 1)) : Finset ℝ).finite_toSet.measure_zero _)
    intro x hx
    rw [mem_ofPred_eq, hpoly] at hx
    obtain ⟨h1, h2, h3⟩ := hx
    have : x ∈ ⋃ i : Fin n, Icc (xs i.castSucc) (xs i.succ) := by rw [hcov]; exact ⟨h1, h2⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 this
    simp only at h3
    rw [hspG i x hi, mpcL] at h3
    by_cases hit : sp i = t
    · rw [hit] at h3
      exact absurd (mpc_lineY_inj hst.ne' h3) hc
    · have := mpc_lineY_eq_imp hst.ne' (mpc_sin_pos_of_diamond (hsp i)).ne'
        (mpc_diamond_sin_sub_ne ht (hsp i) (Ne.symm hit)) h3
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_univ _, this.symm⟩)
  rw [this, ENNReal.toReal_zero, zero_div]

lemma mpc_closure_polyNiche (hK : IsPolygonCap Θ K) :
    closure (polyNiche Θ K) ⊆ {p | mpcLow Θ K p.1 ≤ p.2 ∧ p.2 ≤ mpcTop Θ K p.1} := by
  rw [mpc_polyNiche_eq hK]
  apply closure_minimal
  · rintro p ⟨h1, h2⟩; exact ⟨h1, h2.le⟩
  · exact (isClosed_le ((mpc_continuous_mpcLow Θ K).comp continuous_fst) continuous_snd).inter
      (isClosed_le continuous_snd ((mpc_continuous_mpcTop Θ K).comp continuous_fst))

lemma mpc_interior_polyNiche (hK : IsPolygonCap Θ K) :
    {p : ℝ × ℝ | mpcLow Θ K p.1 < p.2 ∧ p.2 < mpcTop Θ K p.1} ⊆ interior (polyNiche Θ K) := by
  apply interior_maximal
  · rw [mpc_polyNiche_eq hK]; rintro p ⟨h1, h2⟩; exact ⟨h1.le, h2⟩
  · exact (isOpen_lt ((mpc_continuous_mpcLow Θ K).comp continuous_fst) continuous_snd).inter
      (isOpen_lt continuous_snd ((mpc_continuous_mpcTop Θ K).comp continuous_fst))

lemma mpc_frontier_polyNiche (hK : IsPolygonCap Θ K) {p : ℝ × ℝ}
    (hp : p ∈ frontier (polyNiche Θ K)) :
    mpcLow Θ K p.1 ≤ p.2 ∧ p.2 ≤ mpcTop Θ K p.1 ∧
      (p.2 = mpcLow Θ K p.1 ∨ p.2 = mpcTop Θ K p.1) := by
  obtain ⟨h1, h2⟩ := hp
  obtain ⟨a, b⟩ := mpc_closure_polyNiche hK h1
  refine ⟨a, b, ?_⟩
  by_contra h
  push Not at h
  exact h2 (mpc_interior_polyNiche hK ⟨lt_of_le_of_ne a (Ne.symm h.1), lt_of_le_of_ne b h.2⟩)

lemma mpc_top_mem_frontier (hK : IsPolygonCap Θ K) {x : ℝ}
    (hx : mpcLow Θ K x < mpcTop Θ K x) : (x, mpcTop Θ K x) ∈ frontier (polyNiche Θ K) := by
  refine ⟨?_, fun h => ?_⟩
  · rw [Metric.mem_closure_iff]
    intro ε hε
    set δ := min (ε / 2) ((mpcTop Θ K x - mpcLow Θ K x) / 2)
    have hδ : 0 < δ := lt_min (half_pos hε) (by linarith)
    refine ⟨(x, mpcTop Θ K x - δ), ?_, ?_⟩
    · rw [mpc_polyNiche_eq hK]
      refine ⟨?_, by simp only; linarith⟩
      have := min_le_right (ε / 2) ((mpcTop Θ K x - mpcLow Θ K x) / 2)
      simp only
      linarith
    · rw [Prod.dist_eq]
      simp only [dist_self, Real.dist_eq]
      rw [show mpcTop Θ K x - (mpcTop Θ K x - δ) = δ by ring, abs_of_pos hδ]
      exact max_lt hε (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε))
  · have := interior_subset h
    rw [mpc_polyNiche_eq hK] at this
    exact lt_irrefl _ this.2

lemma mpc_low_mem_frontier (hK : IsPolygonCap Θ K) {p : ℝ × ℝ} (hp : p ∈ polyNiche Θ K)
    (hlow : p.2 = mpcLow Θ K p.1) : p ∈ frontier (polyNiche Θ K) := by
  refine ⟨subset_closure hp, fun hint => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
  have hq : (p.1, p.2 - ε / 2) ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [dist_self, Real.dist_eq]
    rw [show p.2 - ε / 2 - p.2 = -(ε / 2) by ring, abs_neg, abs_of_pos (half_pos hε)]
    exact max_lt hε (half_lt_self hε)
  have := hball hq
  rw [mpc_polyNiche_eq hK] at this
  have := this.1
  simp only at this
  linarith

end NicheFrontier

/-- The crossings of the wall `l(s, h_K(s) - 1)` with the other walls. -/
noncomputable def mpcWallCross (Θ : AngleSet) (K : Set (ℝ × ℝ)) (s : ℝ) : Finset ℝ :=
  (mpcDiamond Θ).image (fun r => mpcCrossX s (supp K s - 1) r (supp K r - 1))

section Walls

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

lemma mpc_mem_wallCross {s r x : ℝ} (hs : s ∈ Θ.diamond) (hr : r ∈ Θ.diamond) (hrs : r ≠ s)
    (h : mpcL K s x = mpcL K r x) : x ∈ (mpcWallCross Θ K s : Set ℝ) := by
  have := mpc_lineY_eq_imp (mpc_sin_pos_of_diamond hs).ne' (mpc_sin_pos_of_diamond hr).ne'
    (mpc_diamond_sin_sub_ne hs hr (Ne.symm hrs)) h
  exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨r, mpc_mem_mpcDiamond.2 hr, this.symm⟩)

lemma mpc_inner_ne {s : ℝ} (hs : s ∈ Θ.angles ∨ ∃ t ∈ Θ.angles, s = t + π / 2) :
    s ∈ Θ.diamond ∧ s ≠ Θ.ω ∧ s ≠ π / 2 := by
  have hω := mpc_omega_le Θ
  rcases hs with h | ⟨t, ht, rfl⟩
  · have := mpc_angles_bounds h
    exact ⟨Or.inl (Or.inl h), by linarith, by linarith⟩
  · have := mpc_angles_bounds ht
    exact ⟨Or.inl (Or.inr ⟨t, ht, rfl⟩), by linarith, by linarith⟩

/-- A point of an inner wall at which the wall equals the lower boundary of the fan is a crossing. -/
lemma mpc_low_cross {s x : ℝ} (hs : s ∈ Θ.angles ∨ ∃ t ∈ Θ.angles, s = t + π / 2)
    (h : mpcL K s x = mpcLow Θ K x) : x ∈ (mpcWallCross Θ K s : Set ℝ) := by
  obtain ⟨hsd, h1, h2⟩ := mpc_inner_ne hs
  rw [mpcLow] at h
  rcases max_choice (mpcL K Θ.ω x) (mpcL K (π / 2) x) with h' | h' <;> rw [h'] at h
  · exact mpc_mem_wallCross hsd (Or.inr (Or.inl rfl)) (Ne.symm h1) h
  · exact mpc_mem_wallCross hsd (Or.inr (Or.inr rfl)) (Ne.symm h2) h

/-- On an inner wall, the frontier of the polygon niche and the polyline agree up to the
crossings. -/
lemma mpc_inner_wall (hK : IsPolygonCap Θ K) {s : ℝ}
    (hs : s ∈ Θ.angles ∨ ∃ t ∈ Θ.angles, s = t + π / 2) :
    {x | (x, mpcL K s x) ∈ frontier (polyNiche Θ K)} ⊆
        {x | (x, mpcL K s x) ∈ polyline Θ K} ∪ (mpcWallCross Θ K s : Set ℝ) ∧
      {x | (x, mpcL K s x) ∈ polyline Θ K} ⊆
        {x | (x, mpcL K s x) ∈ frontier (polyNiche Θ K)} ∪ (mpcWallCross Θ K s : Set ℝ) := by
  rw [mpc_polyline_eq hK]
  constructor
  · intro x hx
    obtain ⟨h1, h2, h3 | h3⟩ := mpc_frontier_polyNiche hK hx
    · exact Or.inr (mpc_low_cross hs h3)
    · left
      simp only [mem_ofPred_eq] at h1 h2 h3 ⊢
      have hG : mpcG Θ K x = mpcL K s x := by rw [mpcG, max_eq_right (h3 ▸ h1), h3]
      refine ⟨?_, ?_, hG.symm⟩
      · by_contra h
        push Not at h
        have := (mpc_left_of_C hK h.le).1
        linarith
      · by_contra h
        push Not at h
        have := (mpc_right_of_A hK h.le).1
        linarith
  · rintro x ⟨h1, h2, h3⟩
    simp only at h3
    by_cases hlt : mpcLow Θ K x < mpcTop Θ K x
    · left
      have hG : mpcG Θ K x = mpcTop Θ K x := max_eq_right hlt.le
      show (x, mpcL K s x) ∈ frontier (polyNiche Θ K)
      rw [h3, hG]
      exact mpc_top_mem_frontier hK hlt
    · right
      push Not at hlt
      have hG : mpcG Θ K x = mpcLow Θ K x := max_eq_left hlt
      exact mpc_low_cross hs (h3.trans hG)

/-- On the wall `b_K(t)`, the frontier of the niche lies on the half-line `b⃗_K(t)` up to
crossings. -/
lemma mpc_wallB_vec (hK : IsPolygonCap Θ K) {t : ℝ} (ht : t ∈ Θ.angles) :
    {x | (x, mpcL K t x) ∈ frontier (polyNiche Θ K)} ⊆
      {x | (x, mpcL K t x) ∈ frontier (polyNiche Θ K) ∩ wallBVec K t} ∪
        (mpcWallCross Θ K t : Set ℝ) := by
  intro x hx
  by_cases hc : x ∈ (mpcWallCross Θ K t : Set ℝ)
  · exact Or.inr hc
  left
  refine ⟨hx, ?_⟩
  have htd : t ∈ Θ.diamond := Or.inl (Or.inl ht)
  have htb := mpc_angles_bounds ht
  have hω := mpc_omega_le Θ
  rw [mpc_mem_wallBVec]
  refine ⟨mpc_dot_lineY _ _ _ (mpc_sin_pos_of_diamond htd).ne', ?_⟩
  have hsd2 : t + π / 2 ∈ Θ.diamond := Or.inl (Or.inr ⟨t, ht, rfl⟩)
  rw [mpc_dot_le_iff (mpc_sin_pos_of_diamond hsd2)]
  simp only
  obtain ⟨-, -, h3 | h3⟩ := mpc_frontier_polyNiche hK hx
  · exact absurd (mpc_low_cross (Or.inl ht) h3) hc
  · simp only at h3
    obtain ⟨r, hr, hrtop⟩ := Finset.exists_mem_eq_sup' Θ.nonempty
      (fun r => min (mpcL K r x) (mpcL K (r + π / 2) x))
    rw [mpcTop, hrtop] at h3
    have hrb := mpc_angles_bounds hr
    rcases min_choice (mpcL K r x) (mpcL K (r + π / 2) x) with h' | h' <;> rw [h'] at h3
    · by_cases hrt : r = t
      · subst hrt
        have := min_le_right (mpcL K r x) (mpcL K (r + π / 2) x)
        rw [h'] at this
        exact h3 ▸ this
      · exact absurd (mpc_mem_wallCross htd (Or.inl (Or.inl hr)) hrt h3) hc
    · exact absurd (mpc_mem_wallCross htd (Or.inl (Or.inr ⟨r, hr, rfl⟩))
        (by intro h; linarith) h3) hc

/-- On the wall `d_K(t)`, the frontier of the niche lies on the half-line `d⃗_K(t)` up to
crossings. -/
lemma mpc_wallD_vec (hK : IsPolygonCap Θ K) {t : ℝ} (ht : t ∈ Θ.angles) :
    {x | (x, mpcL K (t + π / 2) x) ∈ frontier (polyNiche Θ K)} ⊆
      {x | (x, mpcL K (t + π / 2) x) ∈ frontier (polyNiche Θ K) ∩ wallDVec K t} ∪
        (mpcWallCross Θ K (t + π / 2) : Set ℝ) := by
  intro x hx
  by_cases hc : x ∈ (mpcWallCross Θ K (t + π / 2) : Set ℝ)
  · exact Or.inr hc
  left
  refine ⟨hx, ?_⟩
  have htd : t ∈ Θ.diamond := Or.inl (Or.inl ht)
  have hsd2 : t + π / 2 ∈ Θ.diamond := Or.inl (Or.inr ⟨t, ht, rfl⟩)
  have htb := mpc_angles_bounds ht
  have hω := mpc_omega_le Θ
  rw [mpc_mem_wallDVec]
  refine ⟨mpc_dot_lineY _ _ _ (mpc_sin_pos_of_diamond hsd2).ne', ?_⟩
  rw [mpc_dot_le_iff (mpc_sin_pos_of_diamond htd)]
  simp only
  obtain ⟨-, -, h3 | h3⟩ := mpc_frontier_polyNiche hK hx
  · exact absurd (mpc_low_cross (Or.inr ⟨t, ht, rfl⟩) h3) hc
  · simp only at h3
    obtain ⟨r, hr, hrtop⟩ := Finset.exists_mem_eq_sup' Θ.nonempty
      (fun r => min (mpcL K r x) (mpcL K (r + π / 2) x))
    rw [mpcTop, hrtop] at h3
    have hrb := mpc_angles_bounds hr
    rcases min_choice (mpcL K r x) (mpcL K (r + π / 2) x) with h' | h' <;> rw [h'] at h3
    · exact absurd (mpc_mem_wallCross hsd2 (Or.inl (Or.inl hr)) (by intro h; linarith) h3) hc
    · by_cases hrt : r = t
      · subst hrt
        have := min_le_left (mpcL K r x) (mpcL K (r + π / 2) x)
        rw [h'] at this
        exact h3 ▸ this
      · exact absurd (mpc_mem_wallCross hsd2 (Or.inl (Or.inr ⟨r, hr, rfl⟩))
          (by intro h; apply hrt; linarith) h3) hc

end Walls

section Bottom

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

/-- The part of a bottom side of the fan between `C_K⁺(ω)` and `A_K⁻(0)` has horizontal extent
`σ_K(t + π) sin t`. -/
lemma mpc_volume_bottom (hK : IsPolygonCap Θ K) {t : ℝ} (ht : t ∈ ({Θ.ω, π / 2} : Set ℝ)) :
    volume {x | (cPlus K Θ.ω).1 ≤ x ∧ x ≤ (aMinus K 0).1 ∧ mpcL K t x = mpcLow Θ K x} =
      ENNReal.ofReal (sigmaAt K (t + π) * sin t) := by
  have hω0 := mpc_omega_pos Θ
  have hsω : 0 < sin Θ.ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [mpc_omega_le Θ, pi_pos])
  obtain ⟨hC1, -⟩ := mpc_cPlus_coords hK
  obtain ⟨hA1, -⟩ := mpc_aMinus_coords hK
  have hLω := mpc_mpcL_omega hK
  have hLπ := mpc_mpcL_pi_div_two hK
  rcases lt_or_eq_of_le (mpc_omega_le Θ) with hlt | heq
  · obtain ⟨hs1, h0, hs2, h1⟩ := mpc_sigma_bottom_lt hK hlt
    have hcω : 0 < cos Θ.ω := cos_pos_of_mem_Ioo ⟨by linarith, hlt⟩
    have hsign : ∀ x, mpcL K Θ.ω x ≤ 0 ↔ 0 ≤ x := by
      intro x
      rw [hLω, div_nonpos_iff]
      constructor
      · rintro (⟨_, h⟩ | ⟨h, _⟩)
        · linarith
        · by_contra hx; push Not at hx; nlinarith
      · intro h; right; exact ⟨by nlinarith, hsω.le⟩
    rcases ht with rfl | rfl
    · have hset : {x | (cPlus K Θ.ω).1 ≤ x ∧ x ≤ (aMinus K 0).1 ∧
          mpcL K Θ.ω x = mpcLow Θ K x} = Icc (cPlus K Θ.ω).1 0 := by
        ext x
        simp only [mem_ofPred_eq, mem_Icc, mpcLow, hLπ]
        constructor
        · rintro ⟨h1, -, h3⟩
          refine ⟨h1, ?_⟩
          have : 0 ≤ mpcL K Θ.ω x := by rw [h3]; exact le_max_right _ _
          by_contra hx
          push Not at hx
          have := (hsign x).2 hx.le
          have : mpcL K Θ.ω x = 0 := by linarith
          rw [hLω] at this
          have : x * cos Θ.ω = 0 := by
            field_simp at this; linarith
          rcases mul_eq_zero.1 this with h | h <;> linarith
        · rintro ⟨h1, h2⟩
          refine ⟨h1, by linarith, ?_⟩
          rw [max_eq_left]
          by_contra h
          push Not at h
          have := (hsign x).1 h.le
          have : x = 0 := le_antisymm h2 this
          subst this
          rw [hLω] at h
          simp at h
      rw [hset, Real.volume_Icc, hC1, hs2]
      congr 1
      ring
    · have hset : {x | (cPlus K Θ.ω).1 ≤ x ∧ x ≤ (aMinus K 0).1 ∧
          mpcL K (π / 2) x = mpcLow Θ K x} = Icc 0 (aMinus K 0).1 := by
        ext x
        simp only [mem_ofPred_eq, mem_Icc, mpcLow, hLπ]
        constructor
        · rintro ⟨-, h2, h3⟩
          refine ⟨?_, h2⟩
          have : mpcL K Θ.ω x ≤ 0 := by
            have := le_max_left (mpcL K Θ.ω x) 0
            linarith
          exact (hsign x).1 this
        · rintro ⟨h1, h2⟩
          refine ⟨by nlinarith, h2, ?_⟩
          rw [max_eq_right ((hsign x).2 h1)]
      rw [hset, Real.volume_Icc, hA1, show π / 2 + π = 3 * π / 2 by ring, hs1, sin_pi_div_two,
        mul_one, sub_zero]
  · have htπ : t = π / 2 := by rcases ht with rfl | rfl; exacts [heq, rfl]
    subst htπ
    have hset : {x | (cPlus K Θ.ω).1 ≤ x ∧ x ≤ (aMinus K 0).1 ∧
        mpcL K (π / 2) x = mpcLow Θ K x} = Icc (cPlus K Θ.ω).1 (aMinus K 0).1 := by
      ext x
      simp only [mem_ofPred_eq, mem_Icc, mpcLow, hLπ, heq, max_self, and_true]
    rw [hset, Real.volume_Icc, show π / 2 + π = 3 * π / 2 by ring, mpc_sigma_bottom_eq hK heq,
      sin_pi_div_two, mul_one, (mpc_cPlus_eq hK).2.2.2.2, hA1, sub_eq_add_neg]

end Bottom

/-- The proof of Lemma 3.4.5 (2). -/
lemma mpc_lemma3_4_5_two_aux {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) {t : ℝ}
    (ht : t ∈ ({Θ.ω, π / 2} : Set ℝ)) :
    lineLength t 0 (frontier (polyNiche Θ K)) = sigmaAt K (t + π) - tau Θ K t ∧
      lineLength t 0 (polyNiche Θ K) = sigmaAt K (t + π) - tau Θ K t := by
  have htd : t ∈ Θ.diamond := by
    rcases ht with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hst := mpc_sin_pos_of_diamond htd
  have ht1 : supp K t = 1 := by
    rcases ht with rfl | rfl
    · exact hK.1.2.2.1
    · exact hK.1.2.2.2.1
  have hc0 : (0 : ℝ) = supp K t - 1 := by rw [ht1]; ring
  have hLlow : ∀ x, mpcL K t x ≤ mpcLow Θ K x := by
    rcases ht with rfl | rfl
    · exact fun x => le_max_left _ _
    · exact fun x => le_max_right _ _
  have hnotin : ∀ r ∈ Θ.angles, r ≠ t ∧ r + π / 2 ≠ t := by
    intro r hr
    have := mpc_angles_bounds hr
    have hω := mpc_omega_le Θ
    rcases ht with rfl | rfl <;> constructor <;> intro h <;> linarith
  set Y := {x | (x, mpcL K t x) ∈ polyNiche Θ K}
  set SF := {x | (x, mpcL K t x) ∈ frontier (polyNiche Θ K)}
  set X := {x | (x, mpcL K t x) ∈ polyline Θ K}
  set Z := {x | (cPlus K Θ.ω).1 ≤ x ∧ x ≤ (aMinus K 0).1 ∧ mpcL K t x = mpcLow Θ K x}
  have hpoly := mpc_polyline_eq hK
  have hYZ : Y ⊆ Z := by
    intro x hx
    simp only [Y, mem_ofPred_eq] at hx
    rw [mpc_polyNiche_eq hK] at hx
    obtain ⟨h1, h2⟩ := hx
    simp only at h1 h2
    refine ⟨?_, ?_, le_antisymm (hLlow x) h1⟩
    · by_contra h
      push Not at h
      have := (mpc_left_of_C hK h.le).1
      linarith
    · by_contra h
      push Not at h
      have := (mpc_right_of_A hK h.le).1
      linarith
  have hXZ : X ⊆ Z := by
    intro x hx
    simp only [X, mem_ofPred_eq] at hx
    rw [hpoly] at hx
    obtain ⟨h1, h2, h3⟩ := hx
    simp only at h3
    refine ⟨h1, h2, le_antisymm (hLlow x) ?_⟩
    rw [h3]; exact le_max_left _ _
  have hZYX : Z ⊆ Y ∪ X := by
    rintro x ⟨h1, h2, h3⟩
    by_cases hlt : mpcL K t x < mpcTop Θ K x
    · left
      show (x, mpcL K t x) ∈ polyNiche Θ K
      rw [mpc_polyNiche_eq hK]
      exact ⟨h3.symm.le, hlt⟩
    · right
      push Not at hlt
      show (x, mpcL K t x) ∈ polyline Θ K
      rw [hpoly]
      refine ⟨h1, h2, ?_⟩
      simp only
      rw [mpcG, max_eq_left (h3 ▸ hlt), h3]
  have hdisj : Disjoint Y X := by
    rw [Set.disjoint_left]
    intro x hY hX
    simp only [Y, X, mem_ofPred_eq] at hY hX
    rw [mpc_polyNiche_eq hK] at hY
    rw [hpoly] at hX
    have := hY.2
    have h3 := hX.2.2
    simp only at this h3
    rw [h3] at this
    exact absurd (le_max_right _ _) (not_le.2 this)
  have hXc : IsClosed X := by
    have : X = {x | (cPlus K Θ.ω).1 ≤ x ∧ x ≤ (aMinus K 0).1 ∧ mpcL K t x = mpcG Θ K x} := by
      ext x; simp only [X, mem_ofPred_eq, hpoly]
    rw [this]
    exact (isClosed_le continuous_const continuous_id).inter
      ((isClosed_le continuous_id continuous_const).inter
        (isClosed_eq (mpc_continuous_mpcL K t) (mpc_continuous_mpcG Θ K)))
  have hZeq : Z = Y ∪ X := subset_antisymm hZYX (union_subset hYZ hXZ)
  have hvolZ := mpc_volume_bottom hK ht
  have hZfin : volume Z ≠ ⊤ := by rw [hvolZ]; exact ENNReal.ofReal_ne_top
  have hsum : volume Z = volume Y + volume X := by
    rw [hZeq]; exact measure_union hdisj hXc.measurableSet
  have hYfin : volume Y ≠ ⊤ := ne_top_of_le_ne_top hZfin (measure_mono hYZ)
  have hXfin : volume X ≠ ⊤ := ne_top_of_le_ne_top hZfin (measure_mono hXZ)
  have hreal : (volume Y).toReal = sigmaAt K (t + π) * sin t - (volume X).toReal := by
    have := congrArg ENNReal.toReal hsum
    have hnn : 0 ≤ sigmaAt K (t + π) * sin t := mul_nonneg ENNReal.toReal_nonneg hst.le
    rw [ENNReal.toReal_add hYfin hXfin, hvolZ, ENNReal.toReal_ofReal hnn] at this
    linarith
  have htau : tau Θ K t = (volume X).toReal / sin t := by
    rw [mpc_tau_eq_lineLength hK htd, mpc_lineLength_eq hst]
    rfl
  -- the frontier agrees with the niche on the bottom side, up to crossings
  have hSF : SF ⊆ Y ∪ (mpcWallCross Θ K t : Set ℝ) := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := mpc_frontier_polyNiche hK hx
    simp only at h1 h2 h3
    rcases lt_or_eq_of_le h2 with hlt | heq
    · left
      show (x, mpcL K t x) ∈ polyNiche Θ K
      rw [mpc_polyNiche_eq hK]
      exact ⟨h1, hlt⟩
    · right
      obtain ⟨r, hr, hrtop⟩ := Finset.exists_mem_eq_sup' Θ.nonempty
        (fun r => min (mpcL K r x) (mpcL K (r + π / 2) x))
      rw [mpcTop, hrtop] at heq
      obtain ⟨hn1, hn2⟩ := hnotin r hr
      rcases min_choice (mpcL K r x) (mpcL K (r + π / 2) x) with h' | h' <;> rw [h'] at heq
      · exact mpc_mem_wallCross htd (Or.inl (Or.inl hr)) hn1 heq
      · exact mpc_mem_wallCross htd (Or.inl (Or.inr ⟨r, hr, rfl⟩)) hn2 heq
  have hYSF : Y ⊆ SF := by
    intro x hx
    have hx' : (x, mpcL K t x) ∈ polyNiche Θ K := hx
    have h1 := hx'
    rw [mpc_polyNiche_eq hK] at h1
    exact mpc_low_mem_frontier hK hx' (le_antisymm (hLlow x) h1.1)
  have hvolSF : volume SF = volume Y :=
    mpc_volume_eq_of_finite_diff (mpcWallCross Θ K t).finite_toSet finite_empty hSF
      (fun x hx => Or.inl (hYSF hx))
  rw [hc0, mpc_lineLength_eq hst, mpc_lineLength_eq hst]
  change (volume SF).toReal / sin t = _ ∧ (volume Y).toReal / sin t = _
  rw [hvolSF, hreal, htau]
  constructor <;> field_simp

end NicheWalls

/-- **Lemma 3.4.5** (`lem:polyline-length`) (1). For `t ∈ Θ`, the sides of `𝒩_Θ(K)` on `b_K(t)`
(all on the half-line `b⃗_K(t)`) have total length `τ_K(t)`, and those on `d_K(t)` (all on `d⃗_K(t)`)
have total length `τ_K(t + π/2)`. -/
theorem lemma3_4_5_one {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) {t : ℝ}
    (ht : t ∈ Θ.angles) :
    lineLength t (supp K t - 1) (frontier (polyNiche Θ K)) = tau Θ K t ∧
      lineLength t (supp K t - 1) (frontier (polyNiche Θ K) ∩ wallBVec K t) = tau Θ K t ∧
      lineLength (t + π / 2) (supp K (t + π / 2) - 1) (frontier (polyNiche Θ K)) =
        tau Θ K (t + π / 2) ∧
      lineLength (t + π / 2) (supp K (t + π / 2) - 1) (frontier (polyNiche Θ K) ∩ wallDVec K t) =
        tau Θ K (t + π / 2) := by
  have htd : t ∈ Θ.diamond := Or.inl (Or.inl ht)
  have hsd2 : t + π / 2 ∈ Θ.diamond := Or.inl (Or.inr ⟨t, ht, rfl⟩)
  have hfin := fun s => (mpcWallCross Θ K s).finite_toSet
  obtain ⟨hA1, hA2⟩ := mpc_inner_wall hK (Or.inl ht)
  obtain ⟨hB1, hB2⟩ := mpc_inner_wall hK (s := t + π / 2) (Or.inr ⟨t, ht, rfl⟩)
  have e1 : lineLength t (supp K t - 1) (frontier (polyNiche Θ K)) = tau Θ K t := by
    rw [mpc_tau_eq_lineLength hK htd, mpc_lineLength_eq (mpc_sin_pos_of_diamond htd),
      mpc_lineLength_eq (mpc_sin_pos_of_diamond htd)]
    congr 2
    exact mpc_volume_eq_of_finite_diff (hfin t) (hfin t) hA1 hA2
  have e2 : lineLength (t + π / 2) (supp K (t + π / 2) - 1) (frontier (polyNiche Θ K)) =
      tau Θ K (t + π / 2) := by
    rw [mpc_tau_eq_lineLength hK hsd2, mpc_lineLength_eq (mpc_sin_pos_of_diamond hsd2),
      mpc_lineLength_eq (mpc_sin_pos_of_diamond hsd2)]
    congr 2
    exact mpc_volume_eq_of_finite_diff (hfin _) (hfin _) hB1 hB2
  refine ⟨e1, ?_, e2, ?_⟩
  · rw [← e1, mpc_lineLength_eq (mpc_sin_pos_of_diamond htd),
      mpc_lineLength_eq (mpc_sin_pos_of_diamond htd)]
    congr 2
    exact mpc_volume_eq_of_finite_diff (G := (mpcWallCross Θ K t : Set ℝ)) finite_empty (hfin t)
      (fun x hx => Or.inl hx.1) (mpc_wallB_vec hK ht)
  · rw [← e2, mpc_lineLength_eq (mpc_sin_pos_of_diamond hsd2),
      mpc_lineLength_eq (mpc_sin_pos_of_diamond hsd2)]
    congr 2
    exact mpc_volume_eq_of_finite_diff (G := (mpcWallCross Θ K (t + π / 2) : Set ℝ))
      finite_empty (hfin _) (fun x hx => Or.inl hx.1) (mpc_wallD_vec hK ht)

/-- **Lemma 3.4.5** (2). For `t ∈ {ω, π/2}`, the sides of `𝒩_Θ(K)` on `l(t, 0)` have total length
`σ_K(t + π) - τ_K(t)`. -/
theorem lemma3_4_5_two {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) {t : ℝ}
    (ht : t ∈ ({Θ.ω, π / 2} : Set ℝ)) :
    lineLength t 0 (frontier (polyNiche Θ K)) = sigmaAt K (t + π) - tau Θ K t ∧
      lineLength t 0 (polyNiche Θ K) = sigmaAt K (t + π) - tau Θ K t := by
  exact mpc_lemma3_4_5_two_aux hK ht

/-- A polygon cap is balanced if `σ_K(t) = τ_K(t)` for every `t ∈ Θ^◇` (Definition 3.4.5,
`def:polygon-cap-balanced`). -/
def IsBalanced (Θ : AngleSet) (K : Set (ℝ × ℝ)) : Prop := ∀ t ∈ Θ.diamond, sigmaAt K t = tau Θ K t

/-- **Lemma 3.4.6** (`lem:not-balanced-positive`). An unbalanced polygon cap has an angle
`t ∈ Θ^◇` with `σ_K(t) > τ_K(t)`. -/
theorem lemma3_4_6 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K)
    (hnb : ¬ IsBalanced Θ K) : ∃ t ∈ Θ.diamond, tau Θ K t < sigmaAt K t := by
  by_contra hcon
  push Not at hcon
  apply hnb
  have hsum : ∑ t ∈ mpcDiamond Θ, (tau Θ K t - sigmaAt K t) * sin t = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, mpc_sum_tau_sin hK, mpc_sum_sigma_sin hK,
      sub_self]
  have hnn : ∀ t ∈ mpcDiamond Θ, 0 ≤ (tau Θ K t - sigmaAt K t) * sin t := by
    intro t ht
    have ht' := mpc_mem_mpcDiamond.1 ht
    exact mul_nonneg (by linarith [hcon t ht']) (mpc_sin_pos_of_diamond ht').le
  intro t ht
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum t (mpc_mem_mpcDiamond.2 ht)
  rcases mul_eq_zero.1 h1 with h | h
  · linarith
  · exact absurd h (mpc_sin_pos_of_diamond ht).ne'

/-! ### Simple Nef polygons and the balancing step (Lemma 3.4.7) -/

section Balancing

open Filter Topology MeasureTheory


open Classical in
/-- **Theorem 3.1.2** for simple Nef polygons indexed by a finite type. -/
lemma mpc_nef_transfer {ι : Type*} [Fintype ι] [DecidableEq ι] (Φ : (ι → Bool) → Bool)
    (hΦ : ∀ P Q : ι → Bool, (∀ i, P i = true → Q i = true) → Φ P = true → Φ Q = true)
    (d : ι → HalfPlaneData) (hd : Pairwise fun i j => (d i).boundary ≠ (d j).boundary)
    {X : Set (ℝ × ℝ)} (hX : X = {p | Φ (fun i => decide (p ∈ (d i).toSet)) = true})
    (hb : Bornology.IsBounded X) (i₀ : ι) :
    ∃ ε > 0, ∃ C : ℝ, ∀ δ : ℝ, |δ| ≤ ε →
      |area {p | Φ (fun i => decide (p ∈ (Function.update d i₀ ((d i₀).shift δ) i).toSet)) = true} -
        area X - lineLength (d i₀).t (d i₀).h (frontier X) * δ| ≤ C * δ ^ 2 := by
  classical
  set e := Fintype.equivFin ι
  set E : BoolFun (Fintype.card ι) := fun P => Φ (fun i => P (e i))
  set H : Fin (Fintype.card ι) → HalfPlaneData := fun k => d (e.symm k)
  have hsimple : IsSimpleNefPolygon X E H := by
    refine ⟨fun P Q hPQ hP => hΦ _ _ (fun i => hPQ (e i)) hP, ?_, ?_⟩
    · intro k l hkl
      exact hd (fun h => hkl (e.symm.injective h))
    · rw [hX]
      ext p
      simp only [nefPolygon, mem_ofPred_eq, E, H, Equiv.symm_apply_apply]
  obtain ⟨ε, hε, C, hC⟩ := theorem3_1_2 hsimple hb (e i₀)
  refine ⟨ε, hε, C, fun δ hδ => ?_⟩
  have h := hC δ hδ
  have hset : nefPolygon E (Function.update (fun j => (H j).toSet) (e i₀) ((H (e i₀)).shift δ).toSet) =
      {p | Φ (fun i => decide (p ∈ (Function.update d i₀ ((d i₀).shift δ) i).toSet)) = true} := by
    ext p
    simp only [nefPolygon, mem_ofPred_eq, E, H]
    congr! 3 with i
    by_cases hi : i = i₀
    · subst hi
      simp [Function.update_self]
    · rw [Function.update_of_ne (e.injective.ne hi), Function.update_of_ne hi,
        Equiv.symm_apply_apply]
  rw [hset] at h
  simpa [H] using h

/-- Two lines are equal only if they are parallel. -/
lemma mpc_line_eq_imp {t c t' c' : ℝ} (h : line t c = line t' c') :
    sin (t' - t) = 0 ∧ c' = c * cos (t' - t) := by
  have h0 : c • uvec t ∈ line t' c' := by
    rw [← h]; simp [line, dot_smul_left]
  have h1 : c • uvec t + vvec t ∈ line t' c' := by
    rw [← h]; simp [line, dot_add_left, dot_smul_left]
  simp only [line, mem_ofPred_eq, dot_add_left, dot_smul_left, dot_uvec_uvec,
    dot_vvec_uvec'] at h0 h1
  rw [show t - t' = -(t' - t) by ring, cos_neg] at h0 h1
  exact ⟨by linarith, by linarith⟩

/-- The length of the part of the frontier of a convex body on a supporting line is the length of
the edge. -/
lemma mpc_lineLength_edge {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (s : ℝ) :
    lineLength s (supp K s) (frontier K) = sigmaAt K s := by
  have hfr : {σ : ℝ | supp K s • uvec s + σ • vvec s ∈ frontier K} =
      Icc (dot (vminus K s) (vvec s)) (dot (vplus K s) (vvec s)) := by
    ext σ
    simp only [mem_ofPred_eq, mem_Icc]
    set P := supp K s • uvec s + σ • vvec s
    have hPu : dot P (uvec s) = supp K s := by simp [P, dot_add_left, dot_smul_left]
    have hPv : dot P (vvec s) = σ := by simp [P, dot_add_left, dot_smul_left]
    have hmemK : P ∈ frontier K ↔ P ∈ K := by
      constructor
      · intro hP; exact hK.isClosed.frontier_subset hP
      · intro hP
        refine ⟨subset_closure hP, fun hint => ?_⟩
        obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
        have hq : P + (ε / 2) • uvec s ∈ Metric.ball P ε := by
          rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_pos (half_pos hε)]
          have hu : ‖uvec s‖ ≤ 1 := by
            rw [Prod.norm_def]
            simp only [uvec, Real.norm_eq_abs]
            exact max_le (abs_cos_le_one s) (abs_sin_le_one s)
          nlinarith
        have := dot_le_supp hK.2.1 (hball hq) s
        rw [dot_add_left, dot_smul_left, dot_uvec_self, hPu] at this
        linarith
    rw [hmemK]
    have hedge : P ∈ K ↔ P ∈ edge K s := by
      constructor
      · intro hP; exact ⟨hP, hPu⟩
      · intro hP; exact hP.1
    rw [hedge, edge_eq_segment hK]
    have hm := eq_dot_uvec_smul_add (vminus K s) s
    have hp := eq_dot_uvec_smul_add (vplus K s) s
    rw [dot_vminus_uvec] at hm
    rw [dot_vplus_uvec] at hp
    set β₁ := dot (vminus K s) (vvec s)
    set β₂ := dot (vplus K s) (vvec s)
    have hle : β₁ ≤ β₂ := dot_vminus_le_dot_vplus hK s
    constructor
    · rintro ⟨a, b, ha, hb, hab, hP⟩
      have := congrArg (fun q => dot q (vvec s)) hP
      simp only [dot_add_left, dot_smul_left, hPv] at this
      change a * β₁ + b * β₂ = σ at this
      have e1 := mul_nonneg hb (sub_nonneg.2 hle)
      have e2 := mul_nonneg ha (sub_nonneg.2 hle)
      have e3 : a * β₁ + b * β₁ = β₁ := by rw [← add_mul, hab, one_mul]
      have e4 : a * β₂ + b * β₂ = β₂ := by rw [← add_mul, hab, one_mul]
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le hle with heq | hlt
      · have : σ = β₁ := le_antisymm (heq ▸ h2) h1
        refine ⟨1, 0, zero_le_one, le_rfl, by ring, ?_⟩
        rw [one_smul, zero_smul, add_zero, hm]
        show _ = supp K s • uvec s + σ • vvec s
        rw [this]
      · refine ⟨(β₂ - σ) / (β₂ - β₁), (σ - β₁) / (β₂ - β₁), div_nonneg (by linarith) (by linarith),
          div_nonneg (by linarith) (by linarith), by field_simp; ring, ?_⟩
        rw [hm, hp]
        have hne : β₂ - β₁ ≠ 0 := by linarith
        ext <;> simp only [P, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul] <;> field_simp <;> ring
  rw [lineLength, hfr, Real.volume_Icc, ENNReal.toReal_ofReal]
  · rw [(proposition2_1_2 hK s).2, dot_add_left, dot_smul_left, dot_vvec_self]; ring
  · rw [(proposition2_1_2 hK s).2, dot_add_left, dot_smul_left, dot_vvec_self]
    have : 0 ≤ sigmaAt K s := ENNReal.toReal_nonneg
    linarith

/-- Reversing the normal of a line. -/
lemma mpc_lineLength_add_pi (t c : ℝ) (X : Set (ℝ × ℝ)) :
    lineLength (t + π) c X = lineLength t (-c) X := by
  have : {σ : ℝ | c • uvec (t + π) + σ • vvec (t + π) ∈ X} =
      (fun σ => -1 * σ) ⁻¹' {σ : ℝ | (-c) • uvec t + σ • vvec t ∈ X} := by
    ext σ
    simp only [mem_ofPred_eq, mem_preimage, uvec_add_pi, vvec_add_pi]
    rw [show c • -uvec t + σ • -vvec t = (-c) • uvec t + (-1 * σ) • vvec t by
      simp [smul_neg, neg_smul]]
  rw [lineLength, lineLength, this, Real.volume_preimage_mul_left (by norm_num)]
  simp

/-! ### Simple Nef representations of `𝓒_Θ(h)` and `𝒩_Θ(h)` -/

/-- `𝓒_Θ` with separate heights for the upper sides (`hT`) and the bottom sides (`hB`). -/
def mpcCapH2 (Θ : AngleSet) (hT hB : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | (∀ s ∈ Θ.diamond, dot p (uvec s) ≤ hT s) ∧ hB Θ.ω - 1 ≤ dot p (uvec Θ.ω) ∧
    hB (π / 2) - 1 ≤ dot p (uvec (π / 2))}

lemma mpc_capH_eq_capH2 (Θ : AngleSet) (h : ℝ → ℝ) : capH Θ h = mpcCapH2 Θ h h := by
  ext p; rw [mpc_mem_capH]; rfl

/-- The finset `{ω, π/2}` of the bottom normal angles (up to `π`). -/
noncomputable def mpcBot (Θ : AngleSet) : Finset ℝ := {Θ.ω, π / 2}

/-- The finset `Θ ∪ (Θ + π/2)` of the inner normal angles. -/
noncomputable def mpcInner (Θ : AngleSet) : Finset ℝ :=
  Θ.angles ∪ Θ.angles.image (fun t => t + π / 2)

lemma mpc_mem_mpcBot {Θ : AngleSet} {b : ℝ} : b ∈ mpcBot Θ ↔ b = Θ.ω ∨ b = π / 2 := by
  simp [mpcBot]

lemma mpc_mem_mpcInner {Θ : AngleSet} {s : ℝ} :
    s ∈ mpcInner Θ ↔ s ∈ Θ.angles ∨ ∃ t ∈ Θ.angles, s = t + π / 2 := by
  simp only [mpcInner, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨t, ht, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, rfl⟩
  · rintro (h | ⟨t, ht, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, rfl⟩

lemma mpc_bot_diamond {Θ : AngleSet} {b : ℝ} (hb : b ∈ mpcBot Θ) : b ∈ Θ.diamond := by
  rcases mpc_mem_mpcBot.1 hb with rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

lemma mpc_inner_diamond {Θ : AngleSet} {s : ℝ} (hs : s ∈ mpcInner Θ) : s ∈ Θ.diamond :=
  (mpc_inner_ne (mpc_mem_mpcInner.1 hs)).1

lemma mpc_inner_not_bot {Θ : AngleSet} {s : ℝ} (hs : s ∈ mpcInner Θ) : s ∉ mpcBot Θ := by
  obtain ⟨-, h1, h2⟩ := mpc_inner_ne (mpc_mem_mpcInner.1 hs)
  rw [mpc_mem_mpcBot]
  push Not
  exact ⟨h1, h2⟩

/-- The defining half-planes of `𝓒_Θ`. -/
noncomputable def mpcCapData (Θ : AngleSet) (hT hB : ℝ → ℝ) :
    {s // s ∈ mpcDiamond Θ} ⊕ {b // b ∈ mpcBot Θ} → HalfPlaneData
  | Sum.inl s => ⟨s.1, hT s.1, false⟩
  | Sum.inr b => ⟨b.1 + π, 1 - hB b.1, false⟩

/-- The defining half-planes of `𝒩_Θ`. -/
noncomputable def mpcNicheData (Θ : AngleSet) (h : ℝ → ℝ) :
    {s // s ∈ mpcInner Θ} ⊕ {b // b ∈ mpcBot Θ} → HalfPlaneData
  | Sum.inl s => ⟨s.1, h s.1 - 1, true⟩
  | Sum.inr b => ⟨b.1 + π, 1 - h b.1, false⟩

lemma mpc_toSet_bot (b c : ℝ) (p : ℝ × ℝ) :
    p ∈ (⟨b + π, c, false⟩ : HalfPlaneData).toSet ↔ -c ≤ dot p (uvec b) := by
  simp only [HalfPlaneData.toSet, Bool.false_eq_true, ↓reduceIte, halfMinus, mem_ofPred_eq,
    mpc_dot_uvec_add_pi]
  constructor <;> intro h <;> linarith

lemma mpc_mem_capH2_iff (Θ : AngleSet) (hT hB : ℝ → ℝ) (p : ℝ × ℝ) :
    p ∈ mpcCapH2 Θ hT hB ↔ ∀ i, p ∈ (mpcCapData Θ hT hB i).toSet := by
  constructor
  · rintro ⟨h1, h2, h3⟩ (⟨s, hs⟩ | ⟨b, hb⟩)
    · exact h1 s (mpc_mem_mpcDiamond.1 hs)
    · rw [mpcCapData, mpc_toSet_bot]
      rcases mpc_mem_mpcBot.1 hb with rfl | rfl <;> linarith
  · intro h
    refine ⟨fun s hs => h (Sum.inl ⟨s, mpc_mem_mpcDiamond.2 hs⟩), ?_, ?_⟩
    · have := h (Sum.inr ⟨Θ.ω, mpc_mem_mpcBot.2 (Or.inl rfl)⟩)
      rw [mpcCapData, mpc_toSet_bot] at this
      linarith
    · have := h (Sum.inr ⟨π / 2, mpc_mem_mpcBot.2 (Or.inr rfl)⟩)
      rw [mpcCapData, mpc_toSet_bot] at this
      linarith

lemma mpc_mem_nicheH_iff (Θ : AngleSet) (h : ℝ → ℝ) (p : ℝ × ℝ) :
    p ∈ nicheH Θ h ↔ (∀ b : {b // b ∈ mpcBot Θ}, p ∈ (mpcNicheData Θ h (Sum.inr b)).toSet) ∧
      ∃ t, ∃ ht : t ∈ Θ.angles,
        p ∈ (mpcNicheData Θ h (Sum.inl ⟨t, Finset.mem_union_left _ ht⟩)).toSet ∧
        p ∈ (mpcNicheData Θ h (Sum.inl ⟨t + π / 2,
          Finset.mem_union_right _ (Finset.mem_image_of_mem _ ht)⟩)).toSet := by
  simp only [nicheH, fanH, mem_inter_iff, mem_iInter, mem_iUnion, mem_insert_iff,
    mem_singleton_iff, halfPlus, mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨h1, t, ht, h2, h3⟩
    refine ⟨fun ⟨b, hb⟩ => ?_, t, ht, ?_, ?_⟩
    · rw [mpcNicheData, mpc_toSet_bot]
      have := h1 b (mpc_mem_mpcBot.1 hb)
      linarith
    · simp only [mpcNicheData, HalfPlaneData.toSet, ↓reduceIte]; exact h2
    · simp only [mpcNicheData, HalfPlaneData.toSet, ↓reduceIte]; exact h3
  · rintro ⟨h1, t, ht, h2, h3⟩
    refine ⟨fun b hb => ?_, t, ht, ?_, ?_⟩
    · have := h1 ⟨b, mpc_mem_mpcBot.2 hb⟩
      rw [mpcNicheData, mpc_toSet_bot] at this
      linarith
    · simp only [mpcNicheData, HalfPlaneData.toSet, ↓reduceIte] at h2; exact h2
    · simp only [mpcNicheData, HalfPlaneData.toSet, ↓reduceIte] at h3; exact h3

open Classical in
/-- The boolean function of `𝒩_Θ`. -/
noncomputable def mpcNicheBool (Θ : AngleSet)
    (P : {s // s ∈ mpcInner Θ} ⊕ {b // b ∈ mpcBot Θ} → Bool) : Bool :=
  decide ((∀ b, P (Sum.inr b) = true) ∧ ∃ t, ∃ ht : t ∈ Θ.angles,
    P (Sum.inl ⟨t, Finset.mem_union_left _ ht⟩) = true ∧
    P (Sum.inl ⟨t + π / 2, Finset.mem_union_right _ (Finset.mem_image_of_mem _ ht)⟩) = true)

section NefData

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

lemma mpc_capData_pairwise (Θ : AngleSet) (h : ℝ → ℝ) :
    Pairwise fun i j => (mpcCapData Θ h h i).boundary ≠ (mpcCapData Θ h h j).boundary := by
  intro i j hij heq
  simp only [HalfPlaneData.boundary] at heq
  have hl := mpc_line_eq_imp heq
  rcases i with ⟨s, hs⟩ | ⟨b, hb⟩ <;> rcases j with ⟨s', hs'⟩ | ⟨b', hb'⟩ <;>
    simp only [mpcCapData] at hl
  · have hss : s ≠ s' := fun h => hij (by subst h; rfl)
    exact mpc_diamond_sin_sub_ne (mpc_mem_mpcDiamond.1 hs) (mpc_mem_mpcDiamond.1 hs') hss hl.1
  · have hbd := mpc_bot_diamond hb'
    rw [show b' + π - s = (b' - s) + π by ring, sin_add_pi, neg_eq_zero] at hl
    by_cases hsb : s = b'
    · subst hsb
      rw [show s - s + π = π by ring, cos_pi] at hl
      linarith [hl.2]
    · exact mpc_diamond_sin_sub_ne (mpc_mem_mpcDiamond.1 hs) hbd hsb hl.1
  · have hbd := mpc_bot_diamond hb
    rw [show s' - (b + π) = (s' - b) - π by ring, sin_sub_pi, neg_eq_zero] at hl
    by_cases hsb : b = s'
    · subst hsb
      rw [show b - b - π = -π by ring, cos_neg, cos_pi] at hl
      linarith [hl.2]
    · exact mpc_diamond_sin_sub_ne hbd (mpc_mem_mpcDiamond.1 hs') hsb hl.1
  · have hbb : b ≠ b' := fun h => hij (by subst h; rfl)
    rw [show b' + π - (b + π) = b' - b by ring] at hl
    exact mpc_diamond_sin_sub_ne (mpc_bot_diamond hb) (mpc_bot_diamond hb') hbb hl.1

lemma mpc_nicheData_pairwise (Θ : AngleSet) (h : ℝ → ℝ) :
    Pairwise fun i j => (mpcNicheData Θ h i).boundary ≠ (mpcNicheData Θ h j).boundary := by
  intro i j hij heq
  simp only [HalfPlaneData.boundary] at heq
  have hl := mpc_line_eq_imp heq
  rcases i with ⟨s, hs⟩ | ⟨b, hb⟩ <;> rcases j with ⟨s', hs'⟩ | ⟨b', hb'⟩ <;>
    simp only [mpcNicheData] at hl
  · have hss : s ≠ s' := fun h => hij (by subst h; rfl)
    exact mpc_diamond_sin_sub_ne (mpc_inner_diamond hs) (mpc_inner_diamond hs') hss hl.1
  · rw [show b' + π - s = (b' - s) + π by ring, sin_add_pi, neg_eq_zero] at hl
    have hsb : s ≠ b' := fun h => mpc_inner_not_bot hs (h ▸ hb')
    exact mpc_diamond_sin_sub_ne (mpc_inner_diamond hs) (mpc_bot_diamond hb') hsb hl.1
  · rw [show s' - (b + π) = (s' - b) - π by ring, sin_sub_pi, neg_eq_zero] at hl
    have hsb : b ≠ s' := fun h => mpc_inner_not_bot hs' (h ▸ hb)
    exact mpc_diamond_sin_sub_ne (mpc_bot_diamond hb) (mpc_inner_diamond hs') hsb hl.1
  · have hbb : b ≠ b' := fun h => hij (by subst h; rfl)
    rw [show b' + π - (b + π) = b' - b by ring] at hl
    exact mpc_diamond_sin_sub_ne (mpc_bot_diamond hb) (mpc_bot_diamond hb') hbb hl.1

lemma mpc_capData_update_inl (hT hB : ℝ → ℝ) {t : ℝ} (ht : t ∈ mpcDiamond Θ) (δ : ℝ) :
    Function.update (mpcCapData Θ hT hB) (Sum.inl ⟨t, ht⟩)
        ((mpcCapData Θ hT hB (Sum.inl ⟨t, ht⟩)).shift δ) =
      mpcCapData Θ (Function.update hT t (hT t + δ)) hB := by
  funext i
  rcases i with ⟨s, hs⟩ | ⟨b, hb⟩
  · by_cases hst : s = t
    · subst hst
      rw [Function.update_self]
      simp [mpcCapData, HalfPlaneData.shift, Function.update_self]
    · rw [Function.update_of_ne (fun h => hst (by injection h with h; injection h))]
      simp [mpcCapData, Function.update_of_ne hst]
  · rw [Function.update_of_ne (by simp)]
    simp [mpcCapData]

lemma mpc_capData_update_inr (hT hB : ℝ → ℝ) {b : ℝ} (hb : b ∈ mpcBot Θ) (δ : ℝ) :
    Function.update (mpcCapData Θ hT hB) (Sum.inr ⟨b, hb⟩)
        ((mpcCapData Θ hT hB (Sum.inr ⟨b, hb⟩)).shift δ) =
      mpcCapData Θ hT (Function.update hB b (hB b - δ)) := by
  funext i
  rcases i with ⟨s, hs⟩ | ⟨b', hb'⟩
  · rw [Function.update_of_ne (by simp)]
    simp [mpcCapData]
  · by_cases hbb : b' = b
    · subst hbb
      rw [Function.update_self]
      simp only [mpcCapData, HalfPlaneData.shift, Function.update_self]
      congr 1
      ring
    · rw [Function.update_of_ne (fun h => hbb (by injection h with h; injection h))]
      simp [mpcCapData, Function.update_of_ne hbb]

lemma mpc_nicheData_update_inl (h : ℝ → ℝ) {t : ℝ} (ht : t ∈ mpcInner Θ) (δ : ℝ) :
    Function.update (mpcNicheData Θ h) (Sum.inl ⟨t, ht⟩)
        ((mpcNicheData Θ h (Sum.inl ⟨t, ht⟩)).shift δ) =
      mpcNicheData Θ (Function.update h t (h t + δ)) := by
  funext i
  rcases i with ⟨s, hs⟩ | ⟨b, hb⟩
  · by_cases hst : s = t
    · subst hst
      rw [Function.update_self]
      simp only [mpcNicheData, HalfPlaneData.shift, Function.update_self]
      congr 1
      ring
    · rw [Function.update_of_ne (fun h => hst (by injection h with h; injection h))]
      simp [mpcNicheData, Function.update_of_ne hst]
  · rw [Function.update_of_ne (by simp)]
    have hbt : b ≠ t := fun h => mpc_inner_not_bot ht (h ▸ hb)
    simp [mpcNicheData, Function.update_of_ne hbt]

lemma mpc_nicheData_update_inr (h : ℝ → ℝ) {b : ℝ} (hb : b ∈ mpcBot Θ) (δ : ℝ) :
    Function.update (mpcNicheData Θ h) (Sum.inr ⟨b, hb⟩)
        ((mpcNicheData Θ h (Sum.inr ⟨b, hb⟩)).shift δ) =
      mpcNicheData Θ (Function.update h b (h b - δ)) := by
  funext i
  rcases i with ⟨s, hs⟩ | ⟨b', hb'⟩
  · rw [Function.update_of_ne (by simp)]
    have hsb : s ≠ b := fun h => mpc_inner_not_bot hs (h ▸ hb)
    simp [mpcNicheData, Function.update_of_ne hsb]
  · by_cases hbb : b' = b
    · subst hbb
      rw [Function.update_self]
      simp only [mpcNicheData, HalfPlaneData.shift, Function.update_self]
      congr 1
      ring
    · rw [Function.update_of_ne (fun h => hbb (by injection h with h; injection h))]
      simp [mpcNicheData, Function.update_of_ne hbb]

end NefData

section Derivatives

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

lemma mpc_isClosed_capH2 (Θ : AngleSet) (hT hB : ℝ → ℝ) : IsClosed (mpcCapH2 Θ hT hB) := by
  have : mpcCapH2 Θ hT hB = (⋂ s ∈ Θ.diamond, {p : ℝ × ℝ | dot p (uvec s) ≤ hT s}) ∩
      ({p | hB Θ.ω - 1 ≤ dot p (uvec Θ.ω)} ∩ {p | hB (π / 2) - 1 ≤ dot p (uvec (π / 2))}) := by
    ext p; simp [mpcCapH2]
  rw [this]
  have hc : ∀ v : ℝ × ℝ, Continuous fun p : ℝ × ℝ => dot p v := fun v => by
    simp only [dot]; fun_prop
  exact (isClosed_biInter fun s _ => isClosed_le (hc _) continuous_const).inter
    ((isClosed_le continuous_const (hc _)).inter (isClosed_le continuous_const (hc _)))

lemma mpc_isBounded_capH2 (Θ : AngleSet) (hT hB : ℝ → ℝ) :
    Bornology.IsBounded (mpcCapH2 Θ hT hB) := by
  obtain ⟨t, ht⟩ := Θ.nonempty
  have htb := mpc_angles_bounds ht
  have hω := mpc_omega_le Θ
  apply mpc_isBounded_of_strip htb.1 (by linarith) (a := hB (π / 2) - 1) (b := hT (π / 2))
    (c₁ := hT t) (c₂ := hT (t + π / 2))
  rintro p ⟨h1, -, h3⟩
  have e := h1 _ (Or.inr (Or.inr rfl))
  rw [mpc_dot_uvec_pi_div_two] at e h3
  exact ⟨h3, e, h1 t (Or.inl (Or.inl ht)), h1 _ (Or.inl (Or.inr ⟨t, ht, rfl⟩))⟩

/-- Pushing the top side `l(t, h(t))` and the bottom side `l(t, h(t) - 1)` of `𝓒_Θ` by `ε ≤ 1` in the
same direction adds up the two separate area changes. -/
lemma mpc_capH2_two_shift (hh : ℝ → ℝ) {t ε : ℝ} (ht : t ∈ mpcBot Θ) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) :
    area (mpcCapH2 Θ (Function.update hh t (hh t + ε)) (Function.update hh t (hh t + ε))) +
        area (mpcCapH2 Θ hh hh) =
      area (mpcCapH2 Θ (Function.update hh t (hh t + ε)) hh) +
        area (mpcCapH2 Θ hh (Function.update hh t (hh t + ε))) := by
  set hp := Function.update hh t (hh t + ε) with hhp
  have hle : ∀ r, hh r ≤ hp r := by
    intro r; rw [hhp, Function.update_apply]; split_ifs with h
    · rw [h]; linarith
    · exact le_rfl
  have htd := mpc_bot_diamond ht
  set V := mpcCapH2 Θ hp hp
  set X := mpcCapH2 Θ hh hh
  set U := mpcCapH2 Θ hp hh
  set W := mpcCapH2 Θ hh hp
  have hVU : V ⊆ U := by
    rintro p ⟨h1, h2, h3⟩
    exact ⟨h1, by linarith [hle Θ.ω], by linarith [hle (π / 2)]⟩
  have hWX : W ⊆ X := by
    rintro p ⟨h1, h2, h3⟩
    exact ⟨h1, by linarith [hle Θ.ω], by linarith [hle (π / 2)]⟩
  have hdiff : U \ V = X \ W := by
    ext p
    simp only [Set.mem_sdiff, U, V, X, W, mpcCapH2, mem_ofPred_eq, not_and, not_le]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      -- the failing constraint is the raised bottom side at `t`
      have hfail : dot p (uvec t) < hh t + ε - 1 := by
        by_contra hc
        push Not at hc
        have hω' : hp Θ.ω - 1 ≤ dot p (uvec Θ.ω) := by
          rw [hhp, Function.update_apply]; split_ifs with h
          · rw [h]; linarith
          · exact h2
        have hπ' : hp (π / 2) - 1 ≤ dot p (uvec (π / 2)) := by
          rw [hhp, Function.update_apply]; split_ifs with h
          · rw [h]; linarith
          · exact h3
        exact absurd (h4 h1 hω') (not_lt.2 hπ')
      have htop : ∀ s ∈ Θ.diamond, dot p (uvec s) ≤ hh s := by
        intro s hs
        by_cases hst : s = t
        · subst hst; linarith
        · have := h1 s hs
          rwa [hhp, Function.update_of_ne hst] at this
      refine ⟨⟨htop, h2, h3⟩, fun _ hω => ?_⟩
      by_cases htπ : t = π / 2
      · rw [hhp, ← htπ, Function.update_self]; exact hfail
      · have htω : t = Θ.ω := by
          rcases mpc_mem_mpcBot.1 ht with h | h
          · exact h
          · exact absurd h htπ
        rw [hhp, ← htω, Function.update_self] at hω
        linarith
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨⟨fun s hs => (h1 s hs).trans (hle s), h2, h3⟩, fun _ hω => h4 h1 hω⟩
  have hVm := (mpc_isClosed_capH2 Θ hp hp).measurableSet
  have hWm := (mpc_isClosed_capH2 Θ hh hp).measurableSet
  have hfin : ∀ hT hB, MeasureTheory.volume (mpcCapH2 Θ hT hB) ≠ ⊤ := fun hT hB =>
    (mpc_isBounded_capH2 Θ hT hB).measure_lt_top.ne
  have e1 : MeasureTheory.volume V + MeasureTheory.volume (U \ V) = MeasureTheory.volume U := by
    rw [MeasureTheory.measure_add_sdiff hVm.nullMeasurableSet, union_eq_right.2 hVU]
  have e2 : MeasureTheory.volume W + MeasureTheory.volume (X \ W) = MeasureTheory.volume X := by
    rw [MeasureTheory.measure_add_sdiff hWm.nullMeasurableSet, union_eq_right.2 hWX]
  have hd1 : MeasureTheory.volume (U \ V) ≠ ⊤ := ne_top_of_le_ne_top (hfin _ _)
    (MeasureTheory.measure_mono sdiff_subset)
  have r1 := congrArg ENNReal.toReal e1
  have r2 := congrArg ENNReal.toReal e2
  rw [ENNReal.toReal_add (hfin _ _) hd1] at r1
  rw [hdiff] at hd1 r1
  rw [ENNReal.toReal_add (hfin _ _) hd1] at r2
  simp only [area]
  linarith

open Classical in
/-- First-order area change of a polygon cap when one defining half-plane is pushed. -/
lemma mpc_cap_deriv (hK : IsPolygonCap Θ K)
    (i₀ : {s // s ∈ mpcDiamond Θ} ⊕ {b // b ∈ mpcBot Θ}) :
    ∃ ε > 0, ∃ C : ℝ, ∀ δ : ℝ, |δ| ≤ ε →
      |area {p | ∀ i, p ∈ (Function.update (mpcCapData Θ (supp K) (supp K)) i₀
          ((mpcCapData Θ (supp K) (supp K) i₀).shift δ) i).toSet} - area K -
        lineLength (mpcCapData Θ (supp K) (supp K) i₀).t (mpcCapData Θ (supp K) (supp K) i₀).h
          (frontier K) * δ| ≤ C * δ ^ 2 := by
  have hKeq : K = mpcCapH2 Θ (supp K) (supp K) := by
    rw [← mpc_capH_eq_capH2, proposition3_3_4 ⟨K, 0, hK, by simp⟩]
  obtain ⟨ε, hε, C, hC⟩ := mpc_nef_transfer (fun P => decide (∀ i, P i = true))
    (fun P Q hPQ hP => by simp only [decide_eq_true_eq] at hP ⊢; exact fun i => hPQ i (hP i))
    (mpcCapData Θ (supp K) (supp K)) (mpc_capData_pairwise Θ (supp K)) (X := K)
    (by ext p; rw [Set.ext_iff.1 hKeq p, mpc_mem_capH2_iff]; simp) hK.1.2.1.isBounded i₀
  refine ⟨ε, hε, C, fun δ hδ => ?_⟩
  simpa using hC δ hδ

open Classical in
/-- First-order area change of the polygon niche when one defining half-plane is pushed. -/
lemma mpc_niche_deriv (hK : IsPolygonCap Θ K)
    (i₀ : {s // s ∈ mpcInner Θ} ⊕ {b // b ∈ mpcBot Θ}) :
    ∃ ε > 0, ∃ C : ℝ, ∀ δ : ℝ, |δ| ≤ ε →
      |area {p | mpcNicheBool Θ (fun i => decide (p ∈ (Function.update (mpcNicheData Θ (supp K))
          i₀ ((mpcNicheData Θ (supp K) i₀).shift δ) i).toSet)) = true} - area (polyNiche Θ K) -
        lineLength (mpcNicheData Θ (supp K) i₀).t (mpcNicheData Θ (supp K) i₀).h
          (frontier (polyNiche Θ K)) * δ| ≤ C * δ ^ 2 := by
  have hNeq : polyNiche Θ K = nicheH Θ (supp K) := (proposition3_3_5 hK).1.symm
  apply mpc_nef_transfer (mpcNicheBool Θ) _ (mpcNicheData Θ (supp K))
    (mpc_nicheData_pairwise Θ (supp K)) _ (mpc_isBounded_polyNiche hK) i₀
  · intro P Q hPQ hP
    simp only [mpcNicheBool, decide_eq_true_eq] at hP ⊢
    obtain ⟨h1, t, ht, h2, h3⟩ := hP
    exact ⟨fun b => hPQ _ (h1 b), t, ht, hPQ _ h2, hPQ _ h3⟩
  · ext p
    rw [hNeq, mpc_mem_nicheH_iff]
    simp [mpcNicheBool]

end Derivatives

lemma mpc_capH2_eq_bot {Θ : AngleSet} (hT hB hB' : ℝ → ℝ) (h1 : hB Θ.ω = hB' Θ.ω)
    (h2 : hB (π / 2) = hB' (π / 2)) : mpcCapH2 Θ hT hB = mpcCapH2 Θ hT hB' := by
  ext p; simp only [mpcCapH2, mem_ofPred_eq, h1, h2]

lemma mpc_capH2_set (Θ : AngleSet) (hT hB : ℝ → ℝ) :
    {p | ∀ i, p ∈ (mpcCapData Θ hT hB i).toSet} = mpcCapH2 Θ hT hB := by
  ext p; rw [mem_ofPred_eq, mpc_mem_capH2_iff]

open Classical in
lemma mpc_nicheH_set (Θ : AngleSet) (h : ℝ → ℝ) :
    {p | mpcNicheBool Θ (fun i => decide (p ∈ (mpcNicheData Θ h i).toSet)) = true} =
      nicheH Θ h := by
  ext p; rw [mpc_mem_nicheH_iff]; simp [mpcNicheBool]

end Balancing

/-- **Lemma 3.4.7** (`lem:balancing`). Raising `h_K(t)` by a small `ε > 0` changes `𝒜_Θ` by
`(σ_K(t) - τ_K(t)) ε + O(ε²)`, with the constant depending on `K` and `t`. -/
theorem lemma3_4_7 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) {t : ℝ}
    (ht : t ∈ Θ.diamond) :
    ∃ ε₀ > 0, ∃ C : ℝ, ∀ ε ∈ Ioc 0 ε₀,
      |areaH Θ (Function.update (supp K) t (supp K t + ε)) - areaH Θ (supp K) -
          (sigmaAt K t - tau Θ K t) * ε| ≤ C * ε ^ 2 := by
  classical
  have hcap := hK.1
  have hKcap : capH Θ (supp K) = K := proposition3_3_4 ⟨K, 0, hK, by simp⟩
  have hNiche : nicheH Θ (supp K) = polyNiche Θ K := (proposition3_3_5 hK).1
  have hareaH : areaH Θ (supp K) = area K - area (polyNiche Θ K) := by
    rw [areaH, hKcap, hNiche]
  have htD : t ∈ mpcDiamond Θ := mpc_mem_mpcDiamond.2 ht
  have hareaH' : ∀ ε, areaH Θ (Function.update (supp K) t (supp K t + ε)) =
      area (mpcCapH2 Θ (Function.update (supp K) t (supp K t + ε))
        (Function.update (supp K) t (supp K t + ε))) -
      area (nicheH Θ (Function.update (supp K) t (supp K t + ε))) := by
    intro ε; rw [areaH, mpc_capH_eq_capH2]
  by_cases hb : t ∈ mpcBot Θ
  · -- `t ∈ {ω, π/2}`: both the upper and the bottom side of `𝓒_Θ` move
    have ht1 : supp K t = 1 := by
      rcases mpc_mem_mpcBot.1 hb with rfl | rfl
      · exact hcap.2.2.1
      · exact hcap.2.2.2.1
    have htπ : supp K (t + π) = 0 := by
      rcases mpc_mem_mpcBot.1 hb with rfl | rfl
      · exact hcap.2.2.2.2.1
      · rw [show π / 2 + π = 3 * π / 2 by ring]; exact hcap.2.2.2.2.2.1
    obtain ⟨ε1, hε1, C1, hC1⟩ := mpc_cap_deriv hK (Sum.inl ⟨t, htD⟩)
    obtain ⟨ε2, hε2, C2, hC2⟩ := mpc_cap_deriv hK (Sum.inr ⟨t, hb⟩)
    obtain ⟨ε3, hε3, C3, hC3⟩ := mpc_niche_deriv hK (Sum.inr ⟨t, hb⟩)
    refine ⟨min (min ε1 ε2) (min ε3 1), by positivity, C1 + C2 + C3, fun ε hε => ?_⟩
    obtain ⟨hε0, hεle⟩ := hε
    have hε1' : ε ≤ ε1 := hεle.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hε2' : ε ≤ ε2 := hεle.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hε3' : ε ≤ ε3 := hεle.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hε4' : ε ≤ 1 := hεle.trans ((min_le_right _ _).trans (min_le_right _ _))
    have e1 := hC1 ε (by rw [abs_of_pos hε0]; exact hε1')
    have e2 := hC2 (-ε) (by rw [abs_neg, abs_of_pos hε0]; exact hε2')
    have e3 := hC3 (-ε) (by rw [abs_neg, abs_of_pos hε0]; exact hε3')
    rw [mpc_capData_update_inl, mpc_capH2_set] at e1
    rw [mpc_capData_update_inr, mpc_capH2_set, sub_neg_eq_add] at e2
    rw [mpc_nicheData_update_inr, mpc_nicheH_set, sub_neg_eq_add] at e3
    simp only [mpcCapData, mpcNicheData] at e1 e2 e3
    rw [mpc_lineLength_edge hcap.2.1] at e1
    rw [show 1 - supp K t = supp K (t + π) by rw [ht1, htπ]; ring,
      mpc_lineLength_edge hcap.2.1] at e2
    rw [mpc_lineLength_add_pi, show -(1 - supp K t) = 0 by rw [ht1]; ring,
      (lemma3_4_5_two hK (mpc_mem_mpcBot.1 hb)).1, hNiche.symm] at e3
    rw [hNiche] at e3
    have hshift := mpc_capH2_two_shift (Θ := Θ) (supp K) hb hε0.le hε4'
    rw [← mpc_capH_eq_capH2 Θ (supp K), hKcap] at hshift
    rw [hareaH' ε, hareaH]
    have a1 := abs_le.1 e1
    have a2 := abs_le.1 e2
    have a3 := abs_le.1 e3
    rw [neg_sq] at a2 a3
    rw [abs_le]
    constructor <;> nlinarith
  · -- `t ∈ Θ ∪ (Θ + π/2)`: one side moves in `𝓒_Θ` and one in `𝒩_Θ`
    have htI : t ∈ mpcInner Θ := by
      rw [mpc_mem_mpcInner]
      rcases mpc_diamond_cases ht with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (mpc_mem_mpcBot.2 (Or.inl h)) hb
      · exact absurd (mpc_mem_mpcBot.2 (Or.inr h)) hb
    obtain ⟨-, htω, htπ2⟩ := mpc_inner_ne (mpc_mem_mpcInner.1 htI)
    obtain ⟨ε1, hε1, C1, hC1⟩ := mpc_cap_deriv hK (Sum.inl ⟨t, htD⟩)
    obtain ⟨ε3, hε3, C3, hC3⟩ := mpc_niche_deriv hK (Sum.inl ⟨t, htI⟩)
    refine ⟨min ε1 ε3, by positivity, C1 + C3, fun ε hε => ?_⟩
    obtain ⟨hε0, hεle⟩ := hε
    have e1 := hC1 ε (by rw [abs_of_pos hε0]; exact hεle.trans (min_le_left _ _))
    have e3 := hC3 ε (by rw [abs_of_pos hε0]; exact hεle.trans (min_le_right _ _))
    rw [mpc_capData_update_inl, mpc_capH2_set] at e1
    rw [mpc_nicheData_update_inl, mpc_nicheH_set] at e3
    simp only [mpcCapData, mpcNicheData] at e1 e3
    rw [mpc_lineLength_edge hcap.2.1] at e1
    have hτ : lineLength t (supp K t - 1) (frontier (polyNiche Θ K)) = tau Θ K t := by
      rcases mpc_mem_mpcInner.1 htI with h | ⟨r, hr, rfl⟩
      · exact (lemma3_4_5_one hK h).1
      · exact (lemma3_4_5_one hK hr).2.2.1
    rw [hτ] at e3
    rw [mpc_capH2_eq_bot _ _ (Function.update (supp K) t (supp K t + ε))
      (by rw [Function.update_of_ne htω.symm]) (by rw [Function.update_of_ne htπ2.symm])] at e1
    rw [hareaH' ε, hareaH]
    have a1 := abs_le.1 e1
    have a3 := abs_le.1 e3
    rw [abs_le]
    constructor <;> nlinarith

/-- **Lemma 3.4.8** (`lem:height-positive-increment`). If `σ_K(t) > 0`, raising `h_K(t)` by a small
`ε > 0` gives a polygon cap translate `𝓒_Θ(h⁺)`. -/
theorem lemma3_4_8 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) {t : ℝ}
    (ht : t ∈ Θ.diamond) (hσ : 0 < sigmaAt K t) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀,
      IsPolygonCapTranslate Θ (capH Θ (Function.update (supp K) t (supp K t + ε))) := by
  have _ := ht
  by_cases hb : t ∈ ({Θ.ω, π / 2} : Set ℝ)
  · exact mpc_capH_update_bottom hK hb hσ
  · have htω : t ≠ Θ.ω := fun h => hb (Or.inl h)
    have htπ : t ≠ π / 2 := fun h => hb (Or.inr h)
    exact ⟨1, one_pos, fun ε hε => ⟨_, 0, mpc_capH_update_inner hK htω htπ hε.1.le, by simp⟩⟩

/-- **Theorem 3.4.9** (`thm:balanced-polygon-sofa`). Every maximum polygon cap is balanced. -/
theorem theorem3_4_9 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap Θ K) :
    IsBalanced Θ K := by
  by_contra hnb
  obtain ⟨t, ht, hlt⟩ := lemma3_4_6 hK.1 hnb
  have hτ : 0 ≤ tau Θ K t := tsum_nonneg (fun c => ENNReal.toReal_nonneg)
  have hσ : 0 < sigmaAt K t := lt_of_le_of_lt hτ hlt
  obtain ⟨ε₀, hε₀, hcap⟩ := lemma3_4_8 hK.1 ht hσ
  obtain ⟨ε₁, hε₁, C, hC⟩ := lemma3_4_7 hK.1 ht
  set d := sigmaAt K t - tau Θ K t with hd_def
  have hd : 0 < d := sub_pos.2 hlt
  set ε := min (min ε₀ ε₁) (d / (2 * (|C| + 1))) with hε_def
  have hC1 : 0 < |C| + 1 := by positivity
  have hε : 0 < ε := lt_min (lt_min hε₀ hε₁) (by positivity)
  have hεle0 : ε ≤ ε₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hεle1 : ε ≤ ε₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hεd : ε ≤ d / (2 * (|C| + 1)) := min_le_right _ _
  have hCε : C * ε ^ 2 < d * ε := by
    have h1 : ε * (2 * (|C| + 1)) ≤ d := by rwa [le_div_iff₀ (by positivity)] at hεd
    have h2 : C ≤ |C| := le_abs_self C
    nlinarith [mul_pos hε hε]
  have h1 := abs_le.1 (hC ε ⟨hε, hεle1⟩)
  have h2 : areaH Θ (supp K) < areaH Θ (Function.update (supp K) t (supp K t + ε)) := by
    nlinarith [h1.1]
  have htr := hcap ε ⟨hε, hεle0⟩
  have h3 := proposition3_3_7 htr
  obtain ⟨K₀, v, hK₀, hK₀eq⟩ := htr
  have h4 : areaT Θ (capH Θ (Function.update (supp K) t (supp K t + ε))) = polyArea Θ K₀ := by
    rw [hK₀eq]; exact (theorem3_3_6 hK₀ v).2
  have h5 : areaH Θ (supp K) = polyArea Θ K := (proposition3_3_5 hK.1).2
  have h6 := hK.2.2 K₀ hK₀
  linarith

/-- **Theorem 3.4.10** (`thm:balanced-polygon-sofa-connected`). Every maximum polygon cap contains its
polygon niche. -/
theorem theorem3_4_10 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap Θ K) :
    polyNiche Θ K ⊆ K := by
  have hbal := theorem3_4_9 hK
  have hK' := hK.1
  obtain ⟨n, xs, sp, hn, hmono, h0, hlast, hsp, hspG⟩ := mpc_polyline_data hK'
  set P : Fin (n + 1) → ℝ × ℝ := fun i => (xs i, mpcG Θ K (xs i)) with hP
  set ℓ : Fin n → ℝ := fun i => (xs i.succ - xs i.castSucc) / sin (sp i) with hℓ
  have hℓpos : ∀ i, 0 < ℓ i := fun i =>
    div_pos (by linarith [hmono (Fin.castSucc_lt_succ (i := i))])
      (mpc_sin_pos_of_diamond (hsp i))
  have hedge : ∀ i : Fin n, P i.castSucc - P i.succ = ℓ i • vvec (sp i) := by
    intro i
    have hi := hmono (Fin.castSucc_lt_succ (i := i))
    have hs := mpc_sin_pos_of_diamond (hsp i)
    simp only [hP, hℓ]
    rw [hspG i _ ⟨le_rfl, hi.le⟩, hspG i _ ⟨hi.le, le_rfl⟩]
    ext
    · simp only [Prod.fst_sub, Prod.smul_fst, vvec_fst, smul_eq_mul]
      field_simp
      ring
    · simp only [Prod.snd_sub, Prod.smul_snd, vvec_snd, smul_eq_mul, mpcL, mpcLineY]
      field_simp
      ring
  have hPlast : P (Fin.last n) = aMinus K 0 := by
    simp only [hP]
    rw [hlast, mpc_G_right hK' le_rfl]
    ext
    · rfl
    · exact (mpc_aMinus_coords hK').2.symm
  -- `τ_K(t) = ∑_{i : s_i = t} ℓ_i`
  have htau : ∀ t ∈ Θ.diamond, tau Θ K t = ∑ i ∈ Finset.univ.filter (fun i => sp i = t), ℓ i := by
    intro t ht
    rw [mpc_tau_eq hK' hn hmono h0 hlast hsp hspG ht, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← (Finset.mem_filter.1 hi).2]
  -- the vertices lie in the supporting half-planes of `K` with normal angles in `Θ^◇`
  have hvert : ∀ k : Fin (n + 1), ∀ s ∈ Θ.diamond, dot (P k) (uvec s) ≤ supp K s := by
    intro k s hs
    have hsd := mpc_mem_mpcDiamond.2 hs
    have hPk : P k = aMinus K 0 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.castSucc),
        ℓ i • vvec (sp i) := by
      have := mpc_sum_telescope_from P k
      rw [Finset.sum_congr rfl (fun i _ => hedge i), hPlast] at this
      rw [this]; abel
    have hdot : dot (P k) (uvec s) = dot (aMinus K 0) (uvec s) +
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.castSucc), ℓ i * sin (s - sp i) := by
      rw [hPk, dot_add_left, mpc_dot_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [dot_smul_left, dot_vvec_uvec']
    -- drop the negative terms and add the positive ones
    have hbound : ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.castSucc),
        ℓ i * sin (s - sp i) ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => sp i < s), ℓ i * sin (s - sp i) := by
      have hsb := mpc_diamond_bounds hs
      have hsπ := mpc_diamond_lt_pi hs
      rw [← Finset.sum_filter_add_sum_filter_not
        (Finset.univ.filter (fun i : Fin n => k ≤ i.castSucc)) (fun i => sp i < s)]
      have h1 : ∑ i ∈ (Finset.univ.filter (fun i : Fin n => k ≤ i.castSucc)).filter
          (fun i => ¬ sp i < s), ℓ i * sin (s - sp i) ≤ 0 := by
        apply Finset.sum_nonpos
        intro i hi
        have hi' := (Finset.mem_filter.1 hi).2
        push Not at hi'
        have hspb := mpc_diamond_bounds (hsp i)
        exact mul_nonpos_of_nonneg_of_nonpos (hℓpos i).le
          (sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith [mpc_diamond_lt_pi (hsp i)]))
      have h2 : ∑ i ∈ (Finset.univ.filter (fun i : Fin n => k ≤ i.castSucc)).filter
          (fun i => sp i < s), ℓ i * sin (s - sp i) ≤
          ∑ i ∈ Finset.univ.filter (fun i : Fin n => sp i < s), ℓ i * sin (s - sp i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hi).2⟩
        · intro i hi _
          have hi' := (Finset.mem_filter.1 hi).2
          have hspb := mpc_diamond_bounds (hsp i)
          exact mul_nonneg (hℓpos i).le
            (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [mpc_diamond_lt_pi hs]))
      linarith
    -- group by normal angle and use the balance `σ = τ`
    have hgroup : ∑ i ∈ Finset.univ.filter (fun i : Fin n => sp i < s), ℓ i * sin (s - sp i) =
        ∑ t ∈ (mpcDiamond Θ).filter (· < s), sigmaAt K t * sin (s - t) := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := sp) (t := (mpcDiamond Θ).filter (· < s))
        (fun i hi => Finset.mem_filter.2 ⟨mpc_mem_mpcDiamond.2 (hsp i),
          (Finset.mem_filter.1 hi).2⟩)]
      apply Finset.sum_congr rfl
      intro t ht
      obtain ⟨htD, hts⟩ := Finset.mem_filter.1 ht
      have htd := mpc_mem_mpcDiamond.1 htD
      rw [hbal t htd, htau t htd, Finset.sum_mul, Finset.filter_filter]
      apply Finset.sum_congr
      · ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, h⟩; exact h
        · intro h; exact ⟨h ▸ hts, h⟩
      · intro i hi
        rw [(Finset.mem_filter.1 hi).2]
    -- the walk along the upper boundary
    have hwalk : dot (vplus K s - aMinus K 0) (uvec s) =
        ∑ t ∈ (mpcDiamond Θ).filter (· < s), sigmaAt K t * sin (s - t) := by
      rw [mpc_walk hK' hsd, mpc_dot_sum]
      have hsplit : (mpcDiamond Θ).filter (· ≤ s) = insert s ((mpcDiamond Θ).filter (· < s)) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨ht, hts⟩
          rcases lt_or_eq_of_le hts with h | h
          · exact Or.inr ⟨ht, h⟩
          · exact Or.inl h
        · rintro (rfl | ⟨ht, hts⟩)
          · exact ⟨hsd, le_rfl⟩
          · exact ⟨ht, hts.le⟩
      rw [hsplit, Finset.sum_insert (by simp)]
      simp only [dot_smul_left, dot_vvec_uvec', sub_self, sin_zero, mul_zero, zero_add]
    rw [hdot, ← dot_vplus_uvec K s]
    have : dot (vplus K s) (uvec s) = dot (aMinus K 0) (uvec s) +
        dot (vplus K s - aMinus K 0) (uvec s) := by
      rw [dot_sub_left]; ring
    rw [this, hwalk, ← hgroup]
    linarith
  -- the points of the polyline lie in the same half-planes
  have hcov := mpc_iUnion_Icc hmono hn
  rw [h0, hlast] at hcov
  have hline : ∀ x, (cPlus K Θ.ω).1 ≤ x → x ≤ (aMinus K 0).1 →
      ∀ s ∈ Θ.diamond, dot (x, mpcG Θ K x) (uvec s) ≤ supp K s := by
    intro x h1 h2 s hs
    have : x ∈ ⋃ i : Fin n, Icc (xs i.castSucc) (xs i.succ) := by rw [hcov]; exact ⟨h1, h2⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 this
    have hseg := mpc_segment_piece (hmono (Fin.castSucc_lt_succ (i := i))).le (hspG i)
    have hmem : (x, mpcG Θ K x) ∈ segment ℝ (P i.castSucc) (P i.succ) := by
      simp only [hP]
      rw [hseg]
      exact ⟨hi.1, hi.2, rfl⟩
    obtain ⟨a, b, ha, hb, hab, hx⟩ := hmem
    rw [← hx, dot_add_left, dot_smul_left, dot_smul_left]
    have e1 := hvert i.castSucc s hs
    have e2 := hvert i.succ s hs
    have e3 : a * supp K s + b * supp K s = supp K s := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left e1 ha, mul_le_mul_of_nonneg_left e2 hb]
  -- the polygon niche lies below the polyline and above the fan boundary
  intro p hp
  rw [mpc_polyNiche_eq hK'] at hp
  obtain ⟨hp1, hp2⟩ := hp
  have hx1 : (cPlus K Θ.ω).1 ≤ p.1 := by
    by_contra h
    push Not at h
    have := mpc_left_of_C hK' h.le
    linarith [this.1]
  have hx2 : p.1 ≤ (aMinus K 0).1 := by
    by_contra h
    push Not at h
    have := mpc_right_of_A hK' h.le
    linarith [this.1]
  rw [mpc_polycap_mem_iff hK', mpc_fan_eq hK']
  refine ⟨fun s hs => ?_, hp1⟩
  have e := hline p.1 hx1 hx2 s hs
  have hs' := mpc_sin_pos_of_diamond hs
  have hG : p.2 ≤ mpcG Θ K p.1 := le_trans hp2.le (le_max_right _ _)
  simp only [dot, uvec] at e ⊢
  nlinarith

/-! ### Remark: the original statement of Theorem 3.4.4

The statement of Theorem 3.4.4 originally read `∃ ℓ > 0, p i.castSucc - p i.succ = ℓ • vvec s`, which
Lean elaborated with `ℓ : ℕ`. That version is false; we record the counterexample. -/

/-- The angle set `{π/4}` with rotation angle `π/2`. -/
noncomputable def mpcΘ₀ : AngleSet where
  ω := π / 2
  angles := {π / 4}
  hω := ⟨by positivity, le_rfl⟩
  nonempty := ⟨π / 4, Finset.mem_singleton_self _⟩
  subset := by
    intro t ht
    rw [Finset.mem_singleton.1 ht]
    constructor <;> linarith [pi_pos]

/-- **The original statement of Theorem 3.4.4 is false**: Lean elaborated `∃ ℓ > 0` with `ℓ : ℕ`.
For the polygon cap `𝓒_Θ(1)` with `Θ = {π/4}` and `ω = π/2`, the polyline is the horizontal segment
from `(-√2, 0)` to `(√2, 0)`, of irrational length `2√2`, so it is not a union of segments of natural
lengths. -/
theorem mpc_theorem3_4_4_nat_false : ¬ ∀ (Θ : AngleSet) (K : Set (ℝ × ℝ)), IsPolygonCap Θ K →
    frontier (fan Θ.ω \ polyNiche Θ K) = rayLeft K Θ.ω ∪ polyline Θ K ∪ rayRight K ∧
      Disjoint (rayLeft K Θ.ω) (polyline Θ K ∪ rayRight K) ∧ Disjoint (polyline Θ K) (rayRight K) ∧
      ∃ (n : ℕ) (p : Fin (n + 1) → ℝ × ℝ), p 0 = cPlus K Θ.ω ∧ p (Fin.last n) = aMinus K 0 ∧
        StrictMono (fun i => (p i).1) ∧ polyline Θ K = ⋃ i : Fin n, segment ℝ (p i.castSucc) (p i.succ) ∧
        ∀ i : Fin n, ∃ s ∈ Θ.diamond, ∃ ℓ > 0, p i.castSucc - p i.succ = ℓ • vvec s := by
  intro H
  obtain ⟨hK, -, hN, -⟩ := mpc_K1 mpcΘ₀
  set K := capH mpcΘ₀ (fun _ => 1) with hKdef
  have hω : mpcΘ₀.ω = π / 2 := rfl
  obtain ⟨-, -, -, n, p, hp0, hpl, -, hpoly, hedge⟩ := H mpcΘ₀ K hK
  -- the polyline lies on the line `y = 0`
  have hG : ∀ x, mpcG mpcΘ₀ K x = 0 := by
    intro x
    have hlow : mpcLow mpcΘ₀ K x = 0 := by
      rw [mpcLow, hω, mpc_mpcL_pi_div_two hK, max_self]
    have htop : mpcTop mpcΘ₀ K x ≤ 0 := by
      by_contra h
      push Not at h
      have : (x, (0 : ℝ)) ∈ polyNiche mpcΘ₀ K := by
        rw [mpc_polyNiche_eq hK]
        exact ⟨hlow.le, h⟩
      rw [hN] at this
      exact this
    rw [mpcG, hlow, max_eq_left htop]
  have hy : ∀ q ∈ polyline mpcΘ₀ K, q.2 = 0 := by
    intro q hq
    rw [mpc_polyline_eq hK] at hq
    rw [hq.2.2, hG]
  have hmem : ∀ j : Fin n, p j.castSucc ∈ polyline mpcΘ₀ K ∧ p j.succ ∈ polyline mpcΘ₀ K := by
    intro j
    rw [hpoly]
    exact ⟨mem_iUnion.2 ⟨j, left_mem_segment ℝ _ _⟩, mem_iUnion.2 ⟨j, right_mem_segment ℝ _ _⟩⟩
  -- every edge is horizontal of natural length
  have hstep : ∀ j : Fin n, ∃ ℓ : ℕ, (p j.succ).1 - (p j.castSucc).1 = ℓ := by
    intro j
    obtain ⟨s, hs, ℓ, hℓ, he⟩ := hedge j
    have h1 := hy _ (hmem j).1
    have h2 := hy _ (hmem j).2
    have e2 := congrArg Prod.snd he
    have e1 := congrArg Prod.fst he
    simp only [Prod.snd_sub, Prod.fst_sub, h1, h2, sub_zero, Prod.smul_snd, Prod.smul_fst,
      vvec_snd, vvec_fst] at e1 e2
    rw [nsmul_eq_mul] at e1 e2
    have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    have hcos : cos s = 0 := by
      rcases mul_eq_zero.1 e2.symm with h | h
      · linarith
      · exact h
    have hsb := mpc_diamond_bounds hs
    have hsπ := mpc_diamond_lt_pi hs
    have hsin : sin s = 1 := by
      have := sin_sq_add_cos_sq s
      rw [hcos] at this
      have hpos := sin_pos_of_pos_of_lt_pi hsb.1 hsπ
      nlinarith
    refine ⟨ℓ, ?_⟩
    rw [hsin] at e1
    linarith
  choose ℓ hℓ using hstep
  -- the total length `2√2`
  have hsum : (p (Fin.last n)).1 - (p 0).1 = ∑ j, (ℓ j : ℝ) := by
    rw [← mpc_sum_telescope (fun i => (p i).1)]
    exact Finset.sum_congr rfl fun j _ => hℓ j
  have hmemK : ∀ q : ℝ × ℝ, q ∈ K ↔ (∀ s ∈ mpcΘ₀.diamond, dot q (uvec s) ≤ 1) ∧
      0 ≤ dot q (uvec mpcΘ₀.ω) ∧ 0 ≤ dot q (uvec (π / 2)) := by
    intro q; rw [hKdef, mpc_mem_capH]; simp
  have hdiam : ∀ s ∈ mpcΘ₀.diamond, s = π / 4 ∨ s = π / 4 + π / 2 ∨ s = π / 2 := by
    rintro s ((h | ⟨u, hu, rfl⟩) | (h | h))
    · exact Or.inl (Finset.mem_singleton.1 h)
    · exact Or.inr (Or.inl (by rw [Finset.mem_singleton.1 hu]))
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inr h)
  have hs2 : 0 < √2 := by positivity
  have hsq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpt : ∀ x : ℝ, x * x = 2 → (x, (0 : ℝ)) ∈ K := by
    intro x hx
    rw [hmemK]
    refine ⟨fun s hs => ?_, ?_, ?_⟩
    · rcases hdiam s hs with rfl | rfl | rfl
      · simp only [dot, uvec, cos_pi_div_four, sin_pi_div_four]
        nlinarith [sq_nonneg (x - √2), sq_nonneg (x + √2)]
      · simp only [dot, uvec, cos_add_pi_div_two, sin_add_pi_div_two, sin_pi_div_four,
          cos_pi_div_four]
        nlinarith [sq_nonneg (x - √2), sq_nonneg (x + √2)]
      · simp [dot, uvec]
    · rw [hω]; simp [dot, uvec]
    · simp [dot, uvec]
  have hsuppx : ∀ t, t = 0 ∨ t = π → supp K t = √2 := by
    intro t ht
    have hKc := hK.1.2.1.2.1
    apply le_antisymm
    · apply csSup_le (hK.1.2.1.1.image _)
      rintro _ ⟨q, hq, rfl⟩
      rw [hmemK] at hq
      have h1 := hq.1 (π / 4) (Or.inl (Or.inl (Finset.mem_singleton_self _)))
      have h2 := hq.1 (π / 4 + π / 2) (Or.inl (Or.inr ⟨π / 4, Finset.mem_singleton_self _, rfl⟩))
      have h3 := hq.2.2
      simp only [dot, uvec, cos_pi_div_four, sin_pi_div_four, cos_add_pi_div_two,
        sin_add_pi_div_two, cos_pi_div_two, sin_pi_div_two] at h1 h2 h3
      dsimp only
      rcases ht with rfl | rfl
      · simp only [dot, uvec, cos_zero, sin_zero, mul_one, mul_zero, add_zero]
        nlinarith
      · simp only [dot, uvec, cos_pi, sin_pi, mul_neg, mul_one, mul_zero, add_zero]
        nlinarith
    · rcases ht with rfl | rfl
      · have := dot_le_supp hKc (hpt √2 hsq) 0
        simpa [dot, uvec] using this
      · have := dot_le_supp hKc (hpt (-√2) (by nlinarith)) π
        simpa [dot, uvec] using this
  have hA := (mpc_aMinus_coords hK).1
  have hC := (mpc_cPlus_eq hK).2.2.2.2
  rw [hpl, hp0, hA, hsuppx 0 (Or.inl rfl)] at hsum
  have hCx : (cPlus K mpcΘ₀.ω).1 = -√2 := by
    rw [hsuppx π (Or.inr rfl)] at hC; linarith
  rw [hCx] at hsum
  -- `2√2` would be a natural number, whose square would be `8`
  set N := ∑ j, ℓ j
  have hnat : (2 : ℝ) * √2 = (N : ℝ) := by simp only [N]; push_cast; linarith
  have h8 : (N : ℝ) ^ 2 = 8 := by
    rw [← hnat, mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have h8' : N ^ 2 = 8 := by exact_mod_cast h8
  rcases (show N ≤ 2 ∨ 3 ≤ N by omega) with h | h
  · have := Nat.pow_le_pow_left h 2; omega
  · have := Nat.pow_le_pow_left h 2; omega

end MovingSofa
