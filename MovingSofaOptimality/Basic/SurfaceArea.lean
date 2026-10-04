module

public import MovingSofaOptimality.Basic.ConvexBody
public import MovingSofaOptimality.Basic.LebesgueStieltjes
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The surface area measure of a planar convex body

The paper takes the surface area measure `σ_K` from Schneider's book (Definition 2.1.13,
`def:surface-area-measure`) and uses it through two properties: `σ_K({t})` is the length of the
edge `e_K(t)` (Proposition 2.1.2), and `d v_K⁺(t) = v_t σ_K` (Theorem 5.2.2).

We define `σ_K` directly as the Lebesgue–Stieltjes measure on `ℝ` of the monotone right-continuous
function `t ↦ ⟨v_K⁺(t), v_t⟩ + ∫₀ᵗ h_K`. In the plane, `⟨v_K⁺(t), v_t⟩` is the right derivative
of `h_K`, so this is the classical identity `σ_K = h_K'' + h_K` in the sense of distributions.
Angles are real numbers: `σ_K` is `2π`-periodic, and the paper's measure on `S¹` is its
restriction to any interval of length `2π`.

## Proof outline

* Monotonicity of `G = sigmaFun K`: for `s < t`, with `p = v⁺(t)`, `q = v⁺(s)`, the bounds
  `h(r) ≥ ⟨q, u_r⟩` on `[s, m]` and `h(r) ≥ ⟨p, u_r⟩` on `[m, t]` give
  `G(t) - G(s) ≥ ⟨p - q, v_m⟩` for every `m ∈ [s, t]`, and the mean value theorem applied to
  `m ↦ ⟨p - q, u_m⟩` (which is `≤ 0` at `s` and `≥ 0` at `t`) gives an `m` with `⟨p - q, v_m⟩ ≥ 0`.
* Integrating by parts (`integral_Ioc_stieltjes`),
  `∫_{(a,b]} v_t dσ = G(b) v_b - G(a) v_a + ∫_a^b G(s) u_s ds`, and
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

/-- `∫_s^t ⟨q, u_r⟩ dr = ⟨q, v_s⟩ - ⟨q, v_t⟩`. -/
private lemma sa_integral_dot_uvec (q : ℝ × ℝ) (s t : ℝ) :
    ∫ r in s..t, dot q (uvec r) = dot q (vvec s) - dot q (vvec t) := by
  have h : ∀ x ∈ uIcc s t, HasDerivAt (fun r => -dot q (vvec r)) (dot q (uvec x)) x := by
    intro x _
    simpa using (hasDerivAt_dot_vvec q x).fun_neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h]
  · ring
  · exact (continuous_dot_uvec q).intervalIntegrable _ _

/-! ### The support function and the vertex -/

private lemma sa_intervalIntegrable_supp {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (x y : ℝ) :
    IntervalIntegrable (supp K) volume x y :=
  (IsConvexBody.continuous_supp hK).intervalIntegrable x y

lemma continuous_integral_supp {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    Continuous (fun t => ∫ s in (0 : ℝ)..t, supp K s) :=
  intervalIntegral.continuous_primitive (fun a b => sa_intervalIntegrable_supp hK a b) 0

/-- `(∫₀ᵗ h_K)' = h_K(t)`. -/
lemma hasDerivAt_integral_supp {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, supp K s) (supp K t) t :=
  ((IsConvexBody.continuous_supp hK).integral_hasStrictDerivAt 0 t).hasDerivAt

private lemma sa_continuousWithinAt_vplus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    ContinuousWithinAt (vplus K) (Ici t) t := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  exact tendsto_vplus_right hK t

/-- `v_K⁺(t) = h_K(t) u_t + ⟨v_K⁺(t), v_t⟩ v_t`. -/
lemma vplus_eq_frame (K : Set (ℝ × ℝ)) (t : ℝ) :
    vplus K t = supp K t • uvec t + dot (vplus K t) (vvec t) • vvec t := by
  conv_lhs => rw [eq_dot_uvec_smul_add (vplus K t) t]
  rw [dot_vplus_uvec]

/-- The primitive `t ↦ ∫₀ᵗ h_K` is Lipschitz, as `h_K` is bounded. -/
private lemma sa_lipschitz_primitive {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    ∃ L, LipschitzWith L (fun t => ∫ s in (0 : ℝ)..t, supp K s) := by
  obtain ⟨R, hR⟩ := exists_abs_supp_le hK.2.1 hK.1
  refine ⟨R.toNNReal, lipschitzWith_of_nnnorm_deriv_le
    (fun t => (hasDerivAt_integral_supp hK t).differentiableAt) fun t => ?_⟩
  rw [(hasDerivAt_integral_supp hK t).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
    Real.coe_toNNReal']
  exact (hR t).trans (le_max_left _ _)

/-! ### The distribution function `sigmaFun` -/

private lemma sa_sigmaFun_sub {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (s t : ℝ) :
    sigmaFun K t - sigmaFun K s =
      dot (vplus K t) (vvec t) - dot (vplus K s) (vvec s) + ∫ r in s..t, supp K r := by
  unfold sigmaFun
  rw [← intervalIntegral.integral_interval_sub_left (sa_intervalIntegrable_supp hK 0 t)
    (sa_intervalIntegrable_supp hK 0 s)]
  ring

/-- The distribution function `G = sigmaFun K` is monotone. See the module docstring for the
proof. -/
theorem monotone_sigmaFun {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) : Monotone (sigmaFun K) := by
  intro s t hst
  rcases hst.eq_or_lt with rfl | hst
  · exact le_rfl
  have hp : vplus K t ∈ K := (vplus_mem_edge hK t).1
  have hq : vplus K s ∈ K := (vplus_mem_edge hK s).1
  -- mean value theorem for `m ↦ ⟨p - q, u_m⟩`
  obtain ⟨m, hm, hmeq⟩ := exists_hasDerivAt_eq_slope
    (fun r => dot (vplus K t - vplus K s) (uvec r))
    (fun r => dot (vplus K t - vplus K s) (vvec r)) hst
    (continuous_dot_uvec (vplus K t - vplus K s)).continuousOn
    (fun x _ => hasDerivAt_dot_uvec (vplus K t - vplus K s) x)
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
      ((continuous_dot_uvec (vplus K s)).intervalIntegrable _ _)
      (sa_intervalIntegrable_supp hK s m) (fun x _ => dot_le_supp hK.2.1 hq x)
  have hb2 : ∫ r in m..t, dot (vplus K t) (uvec r) ≤ ∫ r in m..t, supp K r :=
    intervalIntegral.integral_mono_on hm.2.le
      ((continuous_dot_uvec (vplus K t)).intervalIntegrable _ _)
      (sa_intervalIntegrable_supp hK m t) (fun x _ => dot_le_supp hK.2.1 hp x)
  rw [sa_integral_dot_uvec] at hb1 hb2
  have := sa_sigmaFun_sub hK s t
  rw [dot_sub_left] at hd
  linarith

/-- The distribution function `G = sigmaFun K` is right-continuous. -/
theorem continuousWithinAt_sigmaFun {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    ContinuousWithinAt (sigmaFun K) (Ici t) t := by
  have h1 : ContinuousWithinAt (fun s => dot (vplus K s) (vvec s)) (Ici t) t :=
    continuous_dot_pair.continuousAt.comp_continuousWithinAt
      ((sa_continuousWithinAt_vplus hK t).prodMk continuous_vvec.continuousWithinAt)
  exact h1.add (continuous_integral_supp hK).continuousWithinAt

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

/-- `σ_K((a, b]) = G(b) - G(a)`. -/
theorem sigma_Ioc {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (a b : ℝ) :
    sigma K (Ioc a b) = ENNReal.ofReal (sigmaFun K b - sigmaFun K a) := by
  simp [sigma, sigmaStieltjes, hK]

lemma sigma_eq_measure {K : Set (ℝ × ℝ)} : sigma K = (sigmaStieltjes K).measure := rfl

/-- The atom `σ_K({t})` is the jump `F(t) - F(t⁻)` of the distribution function. -/
lemma sigmaAt_eq_jump (K : Set (ℝ × ℝ)) (t : ℝ) :
    sigmaAt K t = sigmaStieltjes K t - Function.leftLim (sigmaStieltjes K) t := by
  rw [sigmaAt, sigma, StieltjesFunction.measure_singleton,
    ENNReal.toReal_ofReal (sub_nonneg.2 ((sigmaStieltjes K).mono.leftLim_le le_rfl))]

/-- `σ_K` has at most countably many atoms. -/
lemma countable_sigma_singleton_ne (K : Set (ℝ × ℝ)) : {t : ℝ | sigma K {t} ≠ 0}.Countable := by
  refine (sigmaStieltjes K).countable_leftLim_ne.mono ?_
  intro t ht h
  apply ht
  rw [sigma, StieltjesFunction.measure_singleton, h, sub_self, ENNReal.ofReal_zero]

/-- If `v_K⁺` is constant on `[x, y]`, so is the distribution function `sigmaFun K`. -/
lemma sigmaFun_eq_of_vplus_const {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {x y : ℝ} (hxy : x ≤ y)
    {p : ℝ × ℝ} (hp : ∀ t ∈ Icc x y, vplus K t = p) : sigmaFun K y = sigmaFun K x := by
  have hint : ∫ s in x..y, supp K s = dot p (vvec x) - dot p (vvec y) := by
    rw [← sa_integral_dot_uvec]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hxy] at ht
    simp only [← hp t ht, dot_vplus_uvec]
  have h := sa_sigmaFun_sub hK x y
  rw [hp y ⟨hxy, le_rfl⟩, hp x ⟨le_rfl, hxy⟩, hint] at h
  linarith

/-- If `v_K⁺` is constant on `[x, y]`, then `σ_K((x, y]) = 0`. -/
lemma sigma_Ioc_eq_zero_of_vplus_const {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {x y : ℝ}
    (hxy : x ≤ y) {p : ℝ × ℝ} (hp : ∀ t ∈ Icc x y, vplus K t = p) : sigma K (Ioc x y) = 0 := by
  rw [sigma_Ioc hK, sigmaFun_eq_of_vplus_const hK hxy hp, sub_self, ENNReal.ofReal_zero]

/-- If `v_K⁺` is constant on `[a, b)`, then `σ_K((a, b)) = 0`. -/
lemma sigma_Ioo_eq_zero_of_vplus_const {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ}
    (hab : a < b) {q : ℝ × ℝ} (hq : ∀ s ∈ Ico a b, vplus K s = q) : sigma K (Ioo a b) = 0 := by
  have hS : sigma K (Ioo a b) =
      ENNReal.ofReal (Function.leftLim (sigmaFun K) b - sigmaFun K a) := by
    simp [sigma, sigmaStieltjes, hK, StieltjesFunction.measure_Ioo]
  have hlim : Function.leftLim (sigmaFun K) b = sigmaFun K a := by
    refine leftLim_eq_of_tendsto (tendsto_const_nhds.congr' ?_)
    filter_upwards [Ioo_mem_nhdsLT hab] with s hs
    exact (sigmaFun_eq_of_vplus_const hK hs.1.le fun t ht => hq t ⟨ht.1, ht.2.trans_lt hs.2⟩).symm
  rw [hS, hlim, sub_self, ENNReal.ofReal_zero]

/-! ### Periodicity -/

lemma edge_add_two_pi (K : Set (ℝ × ℝ)) (t : ℝ) : edge K (t + 2 * π) = edge K t := by
  simp [edge, suppLine, line, supp_add_two_pi, uvec_add_two_pi]

lemma vplus_add_two_pi (K : Set (ℝ × ℝ)) (t : ℝ) : vplus K (t + 2 * π) = vplus K t := by
  simp [vplus, supp_add_two_pi, uvec_add_two_pi, vvec_add_two_pi, edge_add_two_pi]

private lemma sa_sigmaFun_add_two_pi {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    sigmaFun K (t + 2 * π) = sigmaFun K t + ∫ s in (0 : ℝ)..2 * π, supp K s := by
  unfold sigmaFun
  rw [vplus_add_two_pi, vvec_add_two_pi]
  have hper : Function.Periodic (supp K) (2 * π) := fun t => supp_add_two_pi K t
  have h := hper.intervalIntegral_add_eq t 0
  rw [zero_add] at h
  rw [← intervalIntegral.integral_add_adjacent_intervals (sa_intervalIntegrable_supp hK 0 t)
    (sa_intervalIntegrable_supp hK t (t + 2 * π)), h]
  ring

/-- `σ_K` is `2π`-periodic. -/
theorem sigma_periodic {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (X : Set ℝ) :
    sigma K ((fun t => t + 2 * π) '' X) = sigma K X := by
  have hemb : MeasurableEmbedding (fun t : ℝ => t - 2 * π) := measurableEmbedding_subRight _
  -- `σ_K` is invariant under `t ↦ t - 2π`, as both measures agree on the intervals `(a, b]`
  have hmap : sigma K = (sigma K).map (fun t => t - 2 * π) := by
    refine Measure.ext_of_Ioc _ _ (fun a b _ => ?_)
    rw [hemb.map_apply, preimage_sub_const_Ioc, sigma_Ioc hK, sigma_Ioc hK,
      sa_sigmaFun_add_two_pi hK, sa_sigmaFun_add_two_pi hK]
    ring_nf
  simp_rw [image_add_right, ← sub_eq_add_neg]
  rw [← hemb.map_apply, ← hmap]

/-! ### Atoms of `σ_K` -/

lemma sigmaStieltjes_apply {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    sigmaStieltjes K t = sigmaFun K t := by
  simp [sigmaStieltjes, hK]

/-- The left limit `G(t⁻) = ⟨v_K⁻(t), v_t⟩ + ∫₀ᵗ h_K`. -/
lemma leftLim_sigmaFun {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Function.leftLim (sigmaFun K) t =
      dot (vminus K t) (vvec t) + ∫ s in (0 : ℝ)..t, supp K s := by
  apply leftLim_eq_of_tendsto
  have h1 : Tendsto (fun s => dot (vplus K s) (vvec s)) (𝓝[<] t)
      (𝓝 (dot (vminus K t) (vvec t))) :=
    (continuous_dot_pair.tendsto (vminus K t, vvec t)).comp
      ((tendsto_vplus_left hK t).prodMk_nhds
        (continuous_vvec.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
  exact h1.add ((continuous_integral_supp hK).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

/-- `σ_K(t) = ⟨v_K⁺(t) - v_K⁻(t), v_t⟩`, from the jump of the distribution function. -/
private lemma sa_sigmaAt_eq_dot_sub {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    sigmaAt K t = dot (vplus K t) (vvec t) - dot (vminus K t) (vvec t) := by
  have hcoe : (sigmaStieltjes K : ℝ → ℝ) = sigmaFun K := funext (sigmaStieltjes_apply hK)
  rw [sigmaAt, sigma, StieltjesFunction.measure_singleton, hcoe, leftLim_sigmaFun hK]
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
edge `e_K(t)`, and `v_K⁺(t) = v_K⁻(t) + σ_K(t) v_t`.

Departure from the paper: the paper takes `X = {t}` in Schneider's Theorem 2.1.1; this proof
computes the atom of `σ_K` at `t` as the jump at `t` of `t ↦ ⟨v_K⁺(t), v_t⟩ + ∫₀ᵗ h_K`, because
`σ_K` is defined directly as the Lebesgue–Stieltjes measure of that function, not through
Theorem 2.1.1 (reason 3). -/
theorem proposition2_1_2 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    sigmaAt K t = norm2 (vplus K t - vminus K t) ∧
      vplus K t = vminus K t + sigmaAt K t • vvec t := by
  have hc := sa_sigmaAt_eq_dot_sub hK t
  have hnn : 0 ≤ sigmaAt K t := by rw [hc]; linarith [dot_vminus_le_dot_vplus hK t]
  constructor
  · rw [sa_vplus_sub_vminus, ← hc, norm2, dot_smul_left, dot_smul_right, dot_vvec_self, mul_one,
      Real.sqrt_mul_self hnn]
  · rw [hc, ← sa_vplus_sub_vminus]
    abel

/-- `σ_K(t) = ⟨v_K⁺(t) - v_K⁻(t), v_t⟩`: Proposition 2.1.2 in coordinates. -/
lemma sigmaAt_eq_dot_sub {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    sigmaAt K t = dot (vplus K t) (vvec t) - dot (vminus K t) (vvec t) := by
  rw [(proposition2_1_2 hK t).2, dot_add_left, dot_smul_left, dot_vvec_self]; ring

/-! ### Bounded variation of the vertex -/

private lemma sa_bv_sPlus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (a b : ℝ) :
    BoundedVariationOn (fun t => dot (vplus K t) (vvec t)) (Icc a b) := by
  obtain ⟨L, hL⟩ := sa_lipschitz_primitive hK
  have h1 : BoundedVariationOn (sigmaFun K) (Icc a b) := by
    have := ((monotone_sigmaFun hK).monotoneOn univ).locallyBoundedVariationOn a b
      (mem_univ a) (mem_univ b)
    rwa [univ_inter] at this
  have h2 := boundedVariationOn_of_lipschitz hL a b
  have := boundedVariationOn_add h1 (boundedVariationOn_const_mul (-1) h2)
  convert this using 1
  ext t; unfold sigmaFun; ring

/-- **Lemma 5.2.1** (`lem:vertex-bounded-variation`). The vertex `v_K⁺` has bounded variation on
every interval. -/
theorem lemma5_2_1 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (a b : ℝ) :
    BoundedVariationOn (vplus K) (Icc a b) := by
  obtain ⟨L, hL⟩ := exists_lipschitzWith_supp hK.2.1 hK.1
  have e : vplus K = fun t => supp K t • uvec t + dot (vplus K t) (vvec t) • vvec t :=
    funext (vplus_eq_frame K)
  rw [e]
  exact boundedVariationOn_add
    ((boundedVariationOn_of_lipschitz hL a b).smul
      (boundedVariationOn_of_lipschitz lipschitz_uvec a b))
    ((sa_bv_sPlus hK a b).smul (boundedVariationOn_of_lipschitz lipschitz_vvec a b))

/-! ### `d v_K⁺ = v_t σ_K` -/

/-- The auxiliary function `Φ(t) = h(t) u_t - (∫₀ᵗ h) v_t`, whose right derivative is `G(t) u_t`. -/
private noncomputable def sa_Phi (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ × ℝ :=
  supp K t • uvec t - (∫ s in (0 : ℝ)..t, supp K s) • vvec t

private lemma sa_hasDerivWithinAt_Phi {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (x : ℝ) :
    HasDerivWithinAt (sa_Phi K) (sigmaFun K x • uvec x) (Ici x) x := by
  have h1 := (hasDerivWithinAt_supp_right hK x).smul (hasDerivAt_uvec x).hasDerivWithinAt
  have h2 := (hasDerivAt_integral_supp hK x).hasDerivWithinAt.smul
    (s := Ici x) (hasDerivAt_vvec x).hasDerivWithinAt
  have h3 := h1.sub h2
  convert h3 using 1
  · rfl
  · simp only [sigmaFun, add_smul, smul_neg]
    abel

private lemma sa_continuous_Phi {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    Continuous (sa_Phi K) := by
  unfold sa_Phi
  exact ((IsConvexBody.continuous_supp hK).smul continuous_uvec).sub
    ((continuous_integral_supp hK).smul continuous_vvec)

/-- The fundamental theorem of calculus for the right derivative of `Φ`. -/
private lemma sa_integral_sigmaFun_uvec {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ}
    (hab : a ≤ b) :
    ∫ s in a..b, sigmaFun K s • uvec s = sa_Phi K b - sa_Phi K a := by
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (sa_continuous_Phi hK).continuousOn
  · intro x _
    exact (sa_hasDerivWithinAt_Phi hK x).mono Ioi_subset_Ici_self
  · exact (monotone_sigmaFun hK).intervalIntegrable.smul_continuousOn
      continuous_uvec.continuousOn

private lemma sa_vplus_eq_Phi {K : Set (ℝ × ℝ)} (t : ℝ) :
    vplus K t = sigmaFun K t • vvec t + sa_Phi K t := by
  rw [sa_Phi, sigmaFun, add_smul]
  conv_lhs => rw [vplus_eq_frame K t]
  abel

/-- The integrated form of Theorem 5.2.2: `v_K⁺(b) - v_K⁺(a) = ∫_{(a,b]} v_t dσ_K(t)`. -/
theorem vplus_sub_vplus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a ≤ b) :
    vplus K b - vplus K a = ∫ t in Ioc a b, vvec t ∂(sigma K) := by
  -- integration by parts: `∫_{(a,b]} v_t dσ = G(b) v_b - G(a) v_a + ∫_a^b G(s) u_s ds`
  have hcoe : (sigmaStieltjes K : ℝ → ℝ) = sigmaFun K := funext (sigmaStieltjes_apply hK)
  rw [sigma, integral_Ioc_stieltjes _ hab hasDerivAt_vvec continuous_uvec.neg, hcoe]
  simp only [smul_neg, intervalIntegral.integral_neg, sub_neg_eq_add]
  rw [sa_integral_sigmaFun_uvec hK hab, sa_vplus_eq_Phi b, sa_vplus_eq_Phi a]
  abel

/-- **Theorem 5.2.2** (`thm:boundary-measure`). For `a < b ≤ a + 2π`, `d v_K⁺(t) = v_t σ_K` as
measures on the half-open interval `(a, b]`. (The bound `b ≤ a + 2π` is not needed.)

Departure from the paper: the paper checks the identity on the intervals `(a, x]` for polygons,
where `σ_K` is the sum of point masses at the edge lengths, and passes to a general `K` through
polygons with the same edges at `a` and `x` converging to `K` (as in the proof of Schneider's
Theorem 8.3.3), with the weak convergence of Theorem 4.1.3; this proof integrates by parts in the
definition of `σ_K` (`vplus_sub_vplus`), because that approximation by polygons is not in Mathlib
(reason 2), and because `σ_K` is defined as the Lebesgue–Stieltjes measure of
`t ↦ ⟨v_K⁺(t), v_t⟩ + ∫₀ᵗ h_K`, not through Schneider's Theorem 2.1.1, so that the identity is a
computation from the definition (reason 3). -/
theorem theorem5_2_2 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b) :
    (lsMeasure (vplus K) a b).restrict (Ioc a b) =
      ((sigma K).restrict (Ioc a b)).withDensityᵥ vvec := by
  have hBV := lemma5_2_1 hK a b
  have hrc : ∀ x ∈ Ico a b, ContinuousWithinAt (vplus K) (Ici x) x :=
    fun x _ => sa_continuousWithinAt_vplus hK x
  have : IsFiniteMeasure ((sigma K).restrict (Ioc a b)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hint : Integrable vvec ((sigma K).restrict (Ioc a b)) :=
    Integrable.of_bound continuous_vvec.aestronglyMeasurable 1
      (Eventually.of_forall norm_vvec_le)
  apply vectorMeasure_ext_Ioc
  intro c d _
  rw [VectorMeasure.restrict_apply _ measurableSet_Ioc measurableSet_Ioc,
    withDensityᵥ_apply hint measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    Ioc_inter_Ioc]
  rcases le_or_gt (max c a) (min d b) with h | h
  · rw [lsMeasure_Ioc_of_le hab.le (le_max_right _ _) h (min_le_right _ _) hBV hrc,
      vplus_sub_vplus hK h]
  · rw [Ioc_eq_empty_of_le h.le]
    simp

end MovingSofaOptimality
