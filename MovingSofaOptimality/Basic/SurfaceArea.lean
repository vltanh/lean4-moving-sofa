module

public import MovingSofaOptimality.Basic.ConvexBody
public import MovingSofaOptimality.Basic.LebesgueStieltjes
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The surface area measure of a planar convex body

The paper takes the surface area measure `σ_K` from Schneider's book (Definition 2.1.13,
`def:surface-area-measure`) and uses it through two properties: `σ_K({t})` is the length of the edge
`e_K(t)` (Proposition 2.1.2), and `d v_K⁺(t) = v_t σ_K` (Theorem 5.2.2).

We define `σ_K` directly as the Lebesgue–Stieltjes measure on `ℝ` of the monotone right-continuous
function `t ↦ ⟨v_K⁺(t), v_t⟩ + ∫₀ᵗ h_K`. In the plane, `⟨v_K⁺(t), v_t⟩` is the right derivative of
`h_K`, so this is the classical identity `σ_K = h_K'' + h_K` in the sense of distributions. Angles are
real numbers: `σ_K` is `2π`-periodic, and the paper's measure on `S¹` is its restriction to any
interval of length `2π`.

## Proof outline

* Monotonicity of `G = sigmaFun K`: for `s < t`, with `p = v⁺(t)`, `q = v⁺(s)`, the bounds
  `h(r) ≥ ⟨q, u_r⟩` on `[s, m]` and `h(r) ≥ ⟨p, u_r⟩` on `[m, t]` give
  `G(t) - G(s) ≥ ⟨p - q, v_m⟩` for every `m ∈ [s, t]`, and the mean value theorem applied to
  `m ↦ ⟨p - q, u_m⟩` (which is `≤ 0` at `s` and `≥ 0` at `t`) gives an `m` with `⟨p - q, v_m⟩ ≥ 0`.
* `∫_{(a,b]} v_t dσ = (G(b) - G(a)) v_b + ∫_a^b (G(s) - G(a)) u_s ds` by Fubini, and
  `Φ(t) = h(t) u_t - (∫₀ᵗ h) v_t` has right derivative `G(t) u_t`; together with
  `v⁺(t) = G(t) v_t + Φ(t)` this gives `v⁺(b) - v⁺(a) = ∫_{(a,b]} v_t dσ`.
-/

@[expose] public section

open Real Set Filter MeasureTheory Topology

namespace MovingSofaOptimality

/-- The distribution function of the surface area measure: `⟨v_K⁺(t), v_t⟩ + ∫₀ᵗ h_K`. -/
noncomputable def sigmaFun (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ :=
  dot (vplus K t) (vvec t) + ∫ s in (0 : ℝ)..t, supp K s

/-! ### Calculus of the frame `u_t, v_t` -/

private lemma sa_continuous_uvec : Continuous uvec := by unfold uvec; fun_prop

private lemma sa_continuous_vvec : Continuous vvec := by unfold vvec; fun_prop

private lemma sa_continuous_dot : Continuous (fun p : (ℝ × ℝ) × (ℝ × ℝ) => dot p.1 p.2) := by
  unfold dot; fun_prop

private lemma sa_continuous_dot_uvec (q : ℝ × ℝ) : Continuous (fun r => dot q (uvec r)) :=
  sa_continuous_dot.comp (continuous_const.prodMk sa_continuous_uvec)

private lemma sa_hasDerivAt_uvec (t : ℝ) : HasDerivAt uvec (vvec t) t := by
  show HasDerivAt (fun x => (cos x, sin x)) (-sin t, cos t) t
  exact (hasDerivAt_cos t).prodMk (hasDerivAt_sin t)

private lemma sa_hasDerivAt_vvec (t : ℝ) : HasDerivAt vvec (-uvec t) t := by
  have h : -uvec t = (-cos t, -sin t) := by simp [uvec]
  rw [h]
  show HasDerivAt (fun x => (-sin x, cos x)) (-cos t, -sin t) t
  exact (hasDerivAt_sin t).fun_neg.prodMk (hasDerivAt_cos t)

private lemma sa_hasDerivAt_dot_uvec (q : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun r => dot q (uvec r)) (dot q (vvec t)) t := by
  have := ((hasDerivAt_cos t).const_mul q.1).add ((hasDerivAt_sin t).const_mul q.2)
  convert this using 1
  · ext r; simp [dot, uvec]
  · simp [dot, vvec]

private lemma sa_hasDerivAt_dot_vvec (q : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun r => dot q (vvec r)) (-dot q (uvec t)) t := by
  have := ((hasDerivAt_sin t).neg.const_mul q.1).add ((hasDerivAt_cos t).const_mul q.2)
  convert this using 1
  · ext r; simp [dot, vvec]
  · simp [dot, uvec]; ring

/-- `∫_s^t ⟨q, u_r⟩ dr = ⟨q, v_s⟩ - ⟨q, v_t⟩`. -/
private lemma sa_integral_dot_uvec (q : ℝ × ℝ) (s t : ℝ) :
    ∫ r in s..t, dot q (uvec r) = dot q (vvec s) - dot q (vvec t) := by
  have h : ∀ x ∈ uIcc s t, HasDerivAt (fun r => -dot q (vvec r)) (dot q (uvec x)) x := by
    intro x _
    simpa using (sa_hasDerivAt_dot_vvec q x).fun_neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h]
  · ring
  · exact (sa_continuous_dot_uvec q).intervalIntegrable _ _

/-- `∫_s^t u_r dr = v_s - v_t`. -/
private lemma sa_integral_uvec (s t : ℝ) : ∫ r in s..t, uvec r = vvec s - vvec t := by
  have h : ∀ x ∈ uIcc s t, HasDerivAt (fun r => -vvec r) (uvec x) x := by
    intro x _
    simpa using (sa_hasDerivAt_vvec x).fun_neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h (sa_continuous_uvec.intervalIntegrable _ _)]
  abel

private lemma sa_norm_uvec_le (s : ℝ) : ‖uvec s‖ ≤ 1 := by
  rw [Prod.norm_def]
  simp only [uvec, Real.norm_eq_abs]
  exact max_le (abs_cos_le_one s) (abs_sin_le_one s)

private lemma sa_norm_vvec_le (s : ℝ) : ‖vvec s‖ ≤ 1 := by
  rw [Prod.norm_def]
  simp only [vvec, Real.norm_eq_abs, abs_neg]
  exact max_le (abs_sin_le_one s) (abs_cos_le_one s)

private lemma sa_lipschitz_uvec : LipschitzWith 1 uvec := by
  have := Real.lipschitzWith_cos.prodMk Real.lipschitzWith_sin
  show LipschitzWith 1 (fun x => (cos x, sin x))
  simpa using this

private lemma sa_lipschitz_vvec : LipschitzWith 1 vvec := by
  have := Real.lipschitzWith_sin.neg.prodMk Real.lipschitzWith_cos
  show LipschitzWith 1 (fun x => (-sin x, cos x))
  simpa using this

private lemma sa_bv_of_lipschitz {F : Type*} [PseudoEMetricSpace F] {f : ℝ → F} {L : NNReal}
    (hf : LipschitzWith L f) (a b : ℝ) : BoundedVariationOn f (Icc a b) := by
  have := hf.locallyBoundedVariationOn univ a b (mem_univ a) (mem_univ b)
  rwa [univ_inter] at this

/-! ### The support function and the vertex -/

private lemma sa_continuous_supp {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) : Continuous (supp K) :=
  continuous_supp hK.2.1

private lemma sa_vplus_mem {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) : vplus K t ∈ K :=
  (vplus_mem_edge hK t).1

private lemma sa_intervalIntegrable_supp {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (x y : ℝ) :
    IntervalIntegrable (supp K) volume x y :=
  (sa_continuous_supp hK).intervalIntegrable x y

private lemma sa_continuous_primitive {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    Continuous (fun t => ∫ s in (0 : ℝ)..t, supp K s) :=
  intervalIntegral.continuous_primitive (fun a b => sa_intervalIntegrable_supp hK a b) 0

private lemma sa_hasDerivAt_primitive {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, supp K s) (supp K t) t :=
  ((sa_continuous_supp hK).integral_hasStrictDerivAt 0 t).hasDerivAt

private lemma sa_continuousWithinAt_vplus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    ContinuousWithinAt (vplus K) (Ici t) t := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  exact tendsto_vplus_right hK t

/-- `v_K⁺(t) = h_K(t) u_t + ⟨v_K⁺(t), v_t⟩ v_t`. -/
private lemma sa_vplus_eq (K : Set (ℝ × ℝ)) (t : ℝ) :
    vplus K t = supp K t • uvec t + dot (vplus K t) (vvec t) • vvec t := by
  conv_lhs => rw [eq_dot_uvec_smul_add (vplus K t) t]
  rw [dot_vplus_uvec]

private lemma sa_exists_bound {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    ∃ C, ∀ p ∈ K, |p.1| ≤ C ∧ |p.2| ≤ C := by
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  exact ⟨C, fun p hp => ⟨(norm_fst_le p).trans (hC p hp), (norm_snd_le p).trans (hC p hp)⟩⟩

private lemma sa_abs_dot_le {C : ℝ} {p : ℝ × ℝ} (hp : |p.1| ≤ C ∧ |p.2| ≤ C) (v : ℝ × ℝ) :
    |dot p v| ≤ C * (|v.1| + |v.2|) := by
  unfold dot
  calc |p.1 * v.1 + p.2 * v.2| ≤ |p.1 * v.1| + |p.2 * v.2| := abs_add_le _ _
    _ = |p.1| * |v.1| + |p.2| * |v.2| := by rw [abs_mul, abs_mul]
    _ ≤ C * |v.1| + C * |v.2| := by
        gcongr
        · exact hp.1
        · exact hp.2
    _ = C * (|v.1| + |v.2|) := by ring

private lemma sa_abs_supp_le {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {C : ℝ}
    (hC : ∀ p ∈ K, |p.1| ≤ C ∧ |p.2| ≤ C) (t : ℝ) : |supp K t| ≤ 2 * C := by
  obtain ⟨p, hp, hpt⟩ := exists_dot_eq_supp hK.2.1 hK.1 t
  rw [← hpt]
  refine (sa_abs_dot_le (hC p hp) _).trans ?_
  have h1 : |(uvec t).1| ≤ 1 := by simpa using abs_cos_le_one t
  have h2 : |(uvec t).2| ≤ 1 := by simpa using abs_sin_le_one t
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC p hp).1
  nlinarith

/-- The support function of a convex body is Lipschitz. -/
private lemma sa_lipschitz_supp {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {C : ℝ}
    (hC : ∀ p ∈ K, |p.1| ≤ C ∧ |p.2| ≤ C) :
    LipschitzWith (Real.toNNReal (2 * C)) (supp K) := by
  apply LipschitzWith.of_le_add_mul'
  intro x y
  obtain ⟨p, hp, hpx⟩ := exists_dot_eq_supp hK.2.1 hK.1 x
  have hy := dot_le_supp hK.2.1 hp y
  have hd : dot p (uvec x) - dot p (uvec y) = dot p (uvec x - uvec y) := (dot_sub_right _ _ _).symm
  have hb := (le_abs_self _).trans (sa_abs_dot_le (hC p hp) (uvec x - uvec y))
  have h1 : |(uvec x - uvec y).1| ≤ dist x y := by
    simpa [Real.dist_eq] using Real.abs_cos_sub_cos_le x y
  have h2 : |(uvec x - uvec y).2| ≤ dist x y := by
    simpa [Real.dist_eq] using Real.abs_sin_sub_sin_le x y
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC p hp).1
  have : C * (|(uvec x - uvec y).1| + |(uvec x - uvec y).2|) ≤ 2 * C * dist x y := by nlinarith
  linarith

private lemma sa_lipschitz_primitive {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {C : ℝ}
    (hC : ∀ p ∈ K, |p.1| ≤ C ∧ |p.2| ≤ C) :
    LipschitzWith (Real.toNNReal (2 * C)) (fun t => ∫ s in (0 : ℝ)..t, supp K s) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (sa_hasDerivAt_primitive hK t).differentiableAt)
  intro t
  rw [(sa_hasDerivAt_primitive hK t).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
    Real.coe_toNNReal']
  exact (sa_abs_supp_le hK hC t).trans (le_max_left _ _)

/-! ### The distribution function `sigmaFun` -/

private lemma sa_sigmaFun_sub {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (s t : ℝ) :
    sigmaFun K t - sigmaFun K s =
      dot (vplus K t) (vvec t) - dot (vplus K s) (vvec s) + ∫ r in s..t, supp K r := by
  unfold sigmaFun
  rw [← intervalIntegral.integral_interval_sub_left (sa_intervalIntegrable_supp hK 0 t)
    (sa_intervalIntegrable_supp hK 0 s)]
  ring

theorem monotone_sigmaFun {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) : Monotone (sigmaFun K) := by
  intro s t hst
  rcases hst.eq_or_lt with rfl | hst
  · exact le_rfl
  have hp : vplus K t ∈ K := sa_vplus_mem hK t
  have hq : vplus K s ∈ K := sa_vplus_mem hK s
  -- mean value theorem for `m ↦ ⟨p - q, u_m⟩`
  obtain ⟨m, hm, hmeq⟩ := exists_hasDerivAt_eq_slope
    (fun r => dot (vplus K t - vplus K s) (uvec r))
    (fun r => dot (vplus K t - vplus K s) (vvec r)) hst
    (sa_continuous_dot_uvec (vplus K t - vplus K s)).continuousOn
    (fun x _ => sa_hasDerivAt_dot_uvec (vplus K t - vplus K s) x)
  have h1 : 0 ≤ dot (vplus K t - vplus K s) (uvec t) := by
    have := dot_le_supp hK.2.1 hq t
    rw [dot_sub_left, dot_vplus_uvec]
    linarith
  have h2 : dot (vplus K t - vplus K s) (uvec s) ≤ 0 := by
    have := dot_le_supp hK.2.1 hp s
    rw [dot_sub_left, dot_vplus_uvec]
    linarith
  have hd : 0 ≤ dot (vplus K t - vplus K s) (vvec m) := by
    rw [hmeq]
    apply div_nonneg <;> linarith
  -- lower bounds for `∫ h` on `[s, m]` and `[m, t]`
  have hint : ∫ r in s..t, supp K r = (∫ r in s..m, supp K r) + ∫ r in m..t, supp K r := by
    rw [intervalIntegral.integral_add_adjacent_intervals (sa_intervalIntegrable_supp hK s m)
      (sa_intervalIntegrable_supp hK m t)]
  have hb1 : ∫ r in s..m, dot (vplus K s) (uvec r) ≤ ∫ r in s..m, supp K r :=
    intervalIntegral.integral_mono_on hm.1.le
      ((sa_continuous_dot_uvec (vplus K s)).intervalIntegrable _ _)
      (sa_intervalIntegrable_supp hK s m) (fun x _ => dot_le_supp hK.2.1 hq x)
  have hb2 : ∫ r in m..t, dot (vplus K t) (uvec r) ≤ ∫ r in m..t, supp K r :=
    intervalIntegral.integral_mono_on hm.2.le
      ((sa_continuous_dot_uvec (vplus K t)).intervalIntegrable _ _)
      (sa_intervalIntegrable_supp hK m t) (fun x _ => dot_le_supp hK.2.1 hp x)
  rw [sa_integral_dot_uvec] at hb1 hb2
  have := sa_sigmaFun_sub hK s t
  rw [dot_sub_left] at hd
  linarith

theorem continuousWithinAt_sigmaFun {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    ContinuousWithinAt (sigmaFun K) (Ici t) t := by
  have h1 : ContinuousWithinAt (fun s => dot (vplus K s) (vvec s)) (Ici t) t :=
    sa_continuous_dot.continuousAt.comp_continuousWithinAt
      ((sa_continuousWithinAt_vplus hK t).prodMk sa_continuous_vvec.continuousWithinAt)
  exact h1.add (sa_continuous_primitive hK).continuousWithinAt

open Classical in
/-- The Stieltjes function of `σ_K` (the identity function when `K` is not a convex body). -/
noncomputable def sigmaStieltjes (K : Set (ℝ × ℝ)) : StieltjesFunction ℝ :=
  if hK : IsConvexBody K then
    { toFun := sigmaFun K
      mono' := monotone_sigmaFun hK
      right_continuous' := continuousWithinAt_sigmaFun hK }
  else StieltjesFunction.id

/-- The surface area measure `σ_K` of a planar convex body `K` (Definition 2.1.13,
`def:surface-area-measure`), as a `2π`-periodic measure on the angles `t ∈ ℝ`. -/
noncomputable def sigma (K : Set (ℝ × ℝ)) : Measure ℝ := (sigmaStieltjes K).measure

/-- The value `σ_K({t})`, written `σ_K(t)` in the paper. -/
noncomputable def sigmaAt (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ := (sigma K {t}).toReal

instance (K : Set (ℝ × ℝ)) : IsLocallyFiniteMeasure (sigma K) := by
  unfold sigma; infer_instance

theorem sigma_Ioc {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (a b : ℝ) :
    sigma K (Ioc a b) = ENNReal.ofReal (sigmaFun K b - sigmaFun K a) := by
  simp [sigma, sigmaStieltjes, hK]

/-! ### Periodicity -/

private lemma sa_edge_add_two_pi (K : Set (ℝ × ℝ)) (t : ℝ) : edge K (t + 2 * π) = edge K t := by
  simp [edge, suppLine, line, supp_add_two_pi, uvec_add_two_pi]

private lemma sa_vplus_add_two_pi (K : Set (ℝ × ℝ)) (t : ℝ) : vplus K (t + 2 * π) = vplus K t := by
  simp [vplus, supp_add_two_pi, uvec_add_two_pi, vvec_add_two_pi, sa_edge_add_two_pi]

private lemma sa_sigmaFun_add_two_pi {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    sigmaFun K (t + 2 * π) = sigmaFun K t + ∫ s in (0 : ℝ)..2 * π, supp K s := by
  unfold sigmaFun
  rw [sa_vplus_add_two_pi, vvec_add_two_pi]
  have hper : Function.Periodic (supp K) (2 * π) := fun t => supp_add_two_pi K t
  have h := hper.intervalIntegral_add_eq t 0
  rw [zero_add] at h
  rw [← intervalIntegral.integral_add_adjacent_intervals (sa_intervalIntegrable_supp hK 0 t)
    (sa_intervalIntegrable_supp hK t (t + 2 * π)), h]
  ring

theorem sigma_periodic {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (X : Set ℝ) :
    sigma K ((fun t => t + 2 * π) '' X) = sigma K X := by
  have himg : (fun t => t + 2 * π) '' X = (fun t => t - 2 * π) ⁻¹' X := by
    ext x
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro hx; exact ⟨x - 2 * π, hx, by ring⟩
  have hemb : MeasurableEmbedding (fun t : ℝ => t - 2 * π) := measurableEmbedding_subRight _
  have hmap : sigma K = (sigma K).map (fun t => t - 2 * π) := by
    refine Measure.ext_of_Ioc _ _ (fun a b _ => ?_)
    rw [hemb.map_apply]
    have : (fun t : ℝ => t - 2 * π) ⁻¹' Ioc a b = Ioc (a + 2 * π) (b + 2 * π) := by
      ext x
      simp only [mem_preimage, mem_Ioc]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [this, sigma_Ioc hK, sigma_Ioc hK, sa_sigmaFun_add_two_pi hK, sa_sigmaFun_add_two_pi hK]
    ring_nf
  rw [himg, ← hemb.map_apply, ← hmap]

/-! ### Atoms of `σ_K` -/

private lemma sa_sigmaStieltjes_apply {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    sigmaStieltjes K t = sigmaFun K t := by
  simp [sigmaStieltjes, hK]

private lemma sa_leftLim_sigmaFun {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Function.leftLim (sigmaFun K) t =
      dot (vminus K t) (vvec t) + ∫ s in (0 : ℝ)..t, supp K s := by
  apply leftLim_eq_of_tendsto
  have h1 : Tendsto (fun s => dot (vplus K s) (vvec s)) (𝓝[<] t)
      (𝓝 (dot (vminus K t) (vvec t))) :=
    (sa_continuous_dot.tendsto (vminus K t, vvec t)).comp
      ((tendsto_vplus_left hK t).prodMk_nhds
        (sa_continuous_vvec.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
  exact h1.add ((sa_continuous_primitive hK).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

private lemma sa_sigmaAt_eq {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    sigmaAt K t = dot (vplus K t) (vvec t) - dot (vminus K t) (vvec t) := by
  have hcoe : (sigmaStieltjes K : ℝ → ℝ) = sigmaFun K := funext (sa_sigmaStieltjes_apply hK)
  rw [sigmaAt, sigma, StieltjesFunction.measure_singleton, hcoe, sa_leftLim_sigmaFun hK]
  rw [ENNReal.toReal_ofReal]
  · unfold sigmaFun; ring
  · unfold sigmaFun; linarith [dot_vminus_le_dot_vplus hK t]

private lemma sa_vplus_sub_vminus (K : Set (ℝ × ℝ)) (t : ℝ) :
    vplus K t - vminus K t =
      (dot (vplus K t) (vvec t) - dot (vminus K t) (vvec t)) • vvec t := by
  conv_lhs => rw [eq_dot_uvec_smul_add (vplus K t) t, eq_dot_uvec_smul_add (vminus K t) t]
  rw [dot_vplus_uvec, dot_vminus_uvec, sub_smul]
  abel

/-- **Proposition 2.1.2** (`pro:surface-area-measure-side-length`). `σ_K(t)` is the length of the
edge `e_K(t)`, and `v_K⁺(t) = v_K⁻(t) + σ_K(t) v_t`. -/
theorem proposition2_1_2 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    sigmaAt K t = norm2 (vplus K t - vminus K t) ∧
      vplus K t = vminus K t + sigmaAt K t • vvec t := by
  have hc := sa_sigmaAt_eq hK t
  have hnn : 0 ≤ sigmaAt K t := by rw [hc]; linarith [dot_vminus_le_dot_vplus hK t]
  constructor
  · rw [sa_vplus_sub_vminus, ← hc, norm2, dot_smul_left, dot_smul_right, dot_vvec_self, mul_one,
      Real.sqrt_mul_self hnn]
  · rw [hc, ← sa_vplus_sub_vminus]
    abel

/-! ### Bounded variation of the vertex -/

private lemma sa_bv_sPlus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (a b : ℝ) :
    BoundedVariationOn (fun t => dot (vplus K t) (vvec t)) (Icc a b) := by
  obtain ⟨C, hC⟩ := sa_exists_bound hK
  have h1 : BoundedVariationOn (sigmaFun K) (Icc a b) := by
    have := ((monotone_sigmaFun hK).monotoneOn univ).locallyBoundedVariationOn a b
      (mem_univ a) (mem_univ b)
    rwa [univ_inter] at this
  have h2 := sa_bv_of_lipschitz (sa_lipschitz_primitive hK hC) a b
  have := sa_boundedVariationOn_add h1 (sa_boundedVariationOn_const_mul (-1) h2)
  convert this using 1
  ext t; unfold sigmaFun; ring

/-- **Lemma 5.2.1** (`lem:vertex-bounded-variation`). The vertex `v_K⁺` has bounded variation on
every interval. -/
theorem lemma5_2_1 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (a b : ℝ) :
    BoundedVariationOn (vplus K) (Icc a b) := by
  obtain ⟨C, hC⟩ := sa_exists_bound hK
  have e : vplus K = fun t => supp K t • uvec t + dot (vplus K t) (vvec t) • vvec t :=
    funext (sa_vplus_eq K)
  rw [e]
  exact sa_boundedVariationOn_add
    ((sa_bv_of_lipschitz (sa_lipschitz_supp hK hC) a b).smul
      (sa_bv_of_lipschitz sa_lipschitz_uvec a b))
    ((sa_bv_sPlus hK a b).smul (sa_bv_of_lipschitz sa_lipschitz_vvec a b))

/-! ### `d v_K⁺ = v_t σ_K` -/

private lemma sa_sigma_real_Ioc {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a ≤ b) :
    (sigma K).real (Ioc a b) = sigmaFun K b - sigmaFun K a := by
  rw [measureReal_def, sigma_Ioc hK, ENNReal.toReal_ofReal]
  linarith [monotone_sigmaFun hK hab]

/-- The Fubini step: `∫_{(a,b]} v_t dσ = (G(b) - G(a)) v_b + ∫_a^b (G(s) - G(a)) u_s ds`. -/
private lemma sa_integral_vvec_sigma {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ}
    (hab : a ≤ b) :
    ∫ t in Ioc a b, vvec t ∂(sigma K) =
      (sigmaFun K b - sigmaFun K a) • vvec b +
        ∫ s in a..b, (sigmaFun K s - sigmaFun K a) • uvec s := by
  set μ := (sigma K).restrict (Ioc a b) with hμ
  set ν := (volume : Measure ℝ).restrict (Ioc a b) with hν
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  set F : ℝ → ℝ → ℝ × ℝ := fun t s => if t ≤ s then uvec s else 0 with hF
  have h1 : ∀ t ∈ Ioc a b, vvec t = vvec b + ∫ s, F t s ∂ν := by
    intro t ht
    have e1 : (fun s => F t s) = (Ici t).indicator uvec := by
      ext1 s; simp [hF, Set.indicator_apply]
    have e2 : Ioc a b ∩ Ici t = Icc t b := by
      ext x; simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h2, h3⟩; exact ⟨⟨ht.1.trans_le h2, h3⟩, h2⟩
    rw [hν, e1, setIntegral_indicator measurableSet_Ici, e2, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht.2, sa_integral_uvec]
    abel
  have h2 : ∀ s ∈ Ioc a b, ∫ t, F t s ∂μ = (sigmaFun K s - sigmaFun K a) • uvec s := by
    intro s hs
    have e1 : (fun t => F t s) = (Iic s).indicator (fun _ => uvec s) := by
      ext1 t; simp [hF, Set.indicator_apply]
    have e2 : Ioc a b ∩ Iic s = Ioc a s := by
      ext x; simp only [mem_inter_iff, mem_Ioc, mem_Iic]
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3.trans hs.2⟩, h3⟩
    rw [hμ, e1, setIntegral_indicator measurableSet_Iic, e2, setIntegral_const,
      sa_sigma_real_Ioc hK hs.1.le]
  have hFm : Measurable (Function.uncurry F) := by
    apply Measurable.ite (measurableSet_le measurable_fst measurable_snd)
      (sa_continuous_uvec.measurable.comp measurable_snd) measurable_const
  have hFi : Integrable (Function.uncurry F) (μ.prod ν) := by
    refine Integrable.of_bound hFm.aestronglyMeasurable 1 (Eventually.of_forall (fun p => ?_))
    simp only [Function.uncurry, hF]
    split_ifs
    · exact sa_norm_uvec_le _
    · simp
  have hswap := integral_integral_swap hFi
  calc ∫ t in Ioc a b, vvec t ∂(sigma K)
      = ∫ t, (vvec b + ∫ s, F t s ∂ν) ∂μ := setIntegral_congr_fun measurableSet_Ioc h1
    _ = ∫ t, vvec b ∂μ + ∫ t, ∫ s, F t s ∂ν ∂μ :=
        integral_add (integrable_const _) hFi.integral_prod_left
    _ = (sigmaFun K b - sigmaFun K a) • vvec b + ∫ s, ∫ t, F t s ∂μ ∂ν := by
        rw [integral_const, hswap, hμ, measureReal_restrict_apply_univ, sa_sigma_real_Ioc hK hab]
    _ = (sigmaFun K b - sigmaFun K a) • vvec b +
          ∫ s in Ioc a b, (sigmaFun K s - sigmaFun K a) • uvec s := by
        rw [hν, setIntegral_congr_fun measurableSet_Ioc h2]
    _ = _ := by rw [intervalIntegral.integral_of_le hab]

/-- The auxiliary function `Φ(t) = h(t) u_t - (∫₀ᵗ h) v_t`, whose right derivative is `G(t) u_t`. -/
private noncomputable def sa_Phi (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ × ℝ :=
  supp K t • uvec t - (∫ s in (0 : ℝ)..t, supp K s) • vvec t

private lemma sa_hasDerivWithinAt_Phi {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (x : ℝ) :
    HasDerivWithinAt (sa_Phi K) (sigmaFun K x • uvec x) (Ici x) x := by
  have h1 := (hasDerivWithinAt_supp_right hK x).smul (sa_hasDerivAt_uvec x).hasDerivWithinAt
  have h2 := (sa_hasDerivAt_primitive hK x).hasDerivWithinAt.smul
    (s := Ici x) (sa_hasDerivAt_vvec x).hasDerivWithinAt
  have h3 := h1.sub h2
  convert h3 using 1
  · rfl
  · simp only [sigmaFun, add_smul, smul_neg]
    abel

private lemma sa_continuous_Phi {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    Continuous (sa_Phi K) := by
  unfold sa_Phi
  exact ((sa_continuous_supp hK).smul sa_continuous_uvec).sub
    ((sa_continuous_primitive hK).smul sa_continuous_vvec)

/-- The fundamental theorem of calculus for the right derivative of `Φ`. -/
private lemma sa_integral_sigmaFun_uvec {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ}
    (hab : a ≤ b) :
    ∫ s in a..b, sigmaFun K s • uvec s = sa_Phi K b - sa_Phi K a := by
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (sa_continuous_Phi hK).continuousOn
  · intro x _
    exact (sa_hasDerivWithinAt_Phi hK x).mono Ioi_subset_Ici_self
  · exact (monotone_sigmaFun hK).intervalIntegrable.smul_continuousOn
      sa_continuous_uvec.continuousOn

private lemma sa_vplus_eq_Phi {K : Set (ℝ × ℝ)} (t : ℝ) :
    vplus K t = sigmaFun K t • vvec t + sa_Phi K t := by
  rw [sa_Phi, sigmaFun, add_smul]
  conv_lhs => rw [sa_vplus_eq K t]
  abel

/-- The integrated form of Theorem 5.2.2: `v_K⁺(b) - v_K⁺(a) = ∫_{(a,b]} v_t dσ_K(t)`. -/
theorem vplus_sub_vplus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a ≤ b) :
    vplus K b - vplus K a = ∫ t in Ioc a b, vvec t ∂(sigma K) := by
  rw [sa_integral_vvec_sigma hK hab]
  have hi1 : IntervalIntegrable (fun s => sigmaFun K s • uvec s) volume a b :=
    (monotone_sigmaFun hK).intervalIntegrable.smul_continuousOn sa_continuous_uvec.continuousOn
  have hi2 : IntervalIntegrable (fun s => sigmaFun K a • uvec s) volume a b :=
    (sa_continuous_uvec.const_smul (sigmaFun K a)).intervalIntegrable a b
  have e : (fun s => (sigmaFun K s - sigmaFun K a) • uvec s) =
      fun s => sigmaFun K s • uvec s - sigmaFun K a • uvec s := by
    ext1 s; rw [sub_smul]
  rw [e, intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_smul,
    sa_integral_sigmaFun_uvec hK hab, sa_integral_uvec, sa_vplus_eq_Phi b, sa_vplus_eq_Phi a]
  simp only [sub_smul, smul_sub]
  abel

private lemma sa_Ioc_inter_Ioc (a b c d : ℝ) : Ioc c d ∩ Ioc a b = Ioc (max c a) (min d b) := by
  ext x; simp only [mem_inter_iff, mem_Ioc, max_lt_iff, le_min_iff]; tauto

/-- **Theorem 5.2.2** (`thm:boundary-measure`). For `a < b ≤ a + 2π`, `d v_K⁺(t) = v_t σ_K` as
measures on the half-open interval `(a, b]`. (The bound `b ≤ a + 2π` is not needed.) -/
theorem theorem5_2_2 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b) :
    (lsMeasure (vplus K) a b).restrict (Ioc a b) =
      ((sigma K).restrict (Ioc a b)).withDensityᵥ vvec := by
  have hBV := lemma5_2_1 hK a b
  have hrc : ∀ x ∈ Ico a b, ContinuousWithinAt (vplus K) (Ici x) x :=
    fun x _ => sa_continuousWithinAt_vplus hK x
  have : IsFiniteMeasure ((sigma K).restrict (Ioc a b)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hint : Integrable vvec ((sigma K).restrict (Ioc a b)) :=
    Integrable.of_bound sa_continuous_vvec.aestronglyMeasurable 1
      (Eventually.of_forall sa_norm_vvec_le)
  apply sa_vectorMeasure_ext_Ioc
  intro c d _
  rw [VectorMeasure.restrict_apply _ measurableSet_Ioc measurableSet_Ioc,
    withDensityᵥ_apply hint measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    sa_Ioc_inter_Ioc]
  rcases le_or_gt (max c a) (min d b) with h | h
  · rw [sa_lsMeasure_Ioc_of_le hab.le (le_max_right _ _) h (min_le_right _ _) hBV hrc,
      vplus_sub_vplus hK h]
  · rw [Ioc_eq_empty_of_le h.le]
    simp

end MovingSofaOptimality
