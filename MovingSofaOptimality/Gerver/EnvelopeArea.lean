module

public import MovingSofaOptimality.Gerver.Envelope
public import MovingSofaOptimality.Convex.CurveArea
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# The area of the niche of a rotation path

This file computes the area of the niche `N` of `MovingSofaOptimality.Gerver.Envelope` (the
analytic part of Theorem 8.4.1 (2) of the paper):
`|N| = 𝒥(𝐱|_{[t₁, t₄]}) - 𝒥(𝐁|_{[t₃, π/2]}) - 𝒥(𝐃|_{[0, t₂]})` (`env_area`).

## The area under a curve

The main tool is a general formula for the area between the `x`-axis and a curve
`z : [a, b] → ℝ²` with `z₂ ≥ 0` and `z₁` monotone or antitone (not necessarily strictly), where `z`
is continuous on `[a, b]` and has a bounded derivative `ψ` off a countable set:
* `envRegion z a b = {q : q₂ ≥ 0, q₁ = z₁(t), q₂ ≤ z₂(t) for some t ∈ [a, b]}` and its variant
  `envRegionStrict z a b` with `q₂ < z₂(t)` are null measurable (`env_nullMeasurableSet_region`);
* both have area `½ [z₁ z₂]_a^b - 𝒥(z)` if `z₁` is monotone (`env_volume_region_of_monotoneOn`) and
  `𝒥(z) - ½ [z₁ z₂]_a^b` if `z₁` is antitone (`env_volume_region_of_antitoneOn`).

*Proof.* Let `T ⊆ (a, b)` be the set of parameters `t` off the countable exceptional set with
`z₂(t) > 0` at which `z₁` takes the value `z₁(t)` only once. The map `(t, λ) ↦ (z₁(t), λ z₂(t))` is
injective on `T × (0, 1)` with Jacobian `z₁'(t) z₂(t)`, so the change of variables formula
(`lintegral_abs_det_fderiv_eq_addHaar_image`) gives the area `∫_T |z₁'| z₂` of its image
(`env_volume_sweep`). Off `T`, either `z₂ = 0` or `z₁` is constant on a nondegenerate interval
through `t`, so `z₁'(t) = 0` (`env_deriv_eq_zero_of_level`); hence `∫_T |z₁'| z₂ = ∫_a^b |z₁'| z₂`.
The image differs from the regions by a null set: the `x`-axis, countably many vertical lines (the
values taken twice by a monotone function form a countable set,
`MonotoneOn.countable_setOfPred_two_preimages`), and the curve itself (`env_volume_image`).
Finally `∫_a^b z₁' z₂ = ½ [z₁ z₂]_a^b - 𝒥(z)` by integration by parts and
`cvx_curveArea_of_primitive` (`env_integral_eq_curveArea`).

## The niche

By `env_niche_eq`, the niche is the union of the regions strictly below `𝐁|_{[t₃, π/2]}`
(`𝐁₁` increasing), `𝐱|_{[t₁, t₄]}` (`𝐱₁` decreasing) and `𝐃|_{[0, t₂]}` (`𝐃₁` increasing), which
overlap only on two vertical lines; the boundary terms cancel since `𝐁(t₃) = 𝐱(t₁)`,
`𝐃(t₂) = 𝐱(t₄)` and `𝐁(π/2)₂ = 𝐃(0)₂ = 0`. Besides `EnvHyp`, `env_area` assumes that `ρ_A` is
bounded below on `[t₃, π/2]` and `ρ_C` on `[0, t₂]` (they are bounded above by `1` there), so that
`𝐁` and `𝐃` have bounded derivatives.
-/

@[expose] public section

open Real Set MeasureTheory

namespace MovingSofaOptimality

/-! ### The sweep map -/

/-- The map `(t, λ) ↦ (z₁(t), λ z₂(t))`, which sweeps the region between the `x`-axis and the
curve `z`. -/
private def env_sweep (z : ℝ → ℝ × ℝ) (p : ℝ × ℝ) : ℝ × ℝ := ((z p.1).1, p.2 * (z p.1).2)

/-- The derivative of `env_sweep z` at `p = (t, λ)`, with matrix `[[ψ₁(t), 0], [λ ψ₂(t), z₂(t)]]`,
where `ψ = z'`. -/
private noncomputable def env_sweepDeriv (z ψ : ℝ → ℝ × ℝ) (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  LinearMap.toContinuousLinearMap
    (Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      !![(ψ p.1).1, 0; p.2 * (ψ p.1).2, (z p.1).2])

/-- The derivative of the sweep map. -/
private lemma env_hasFDerivAt_sweep {z ψ : ℝ → ℝ × ℝ} {p : ℝ × ℝ}
    (hz : HasDerivAt z (ψ p.1) p.1) : HasFDerivAt (env_sweep z) (env_sweepDeriv z ψ p) p := by
  have hz' : HasFDerivAt (fun q : ℝ × ℝ => z q.1)
      (((1 : ℝ →L[ℝ] ℝ).smulRight (ψ p.1)).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) p :=
    hz.hasFDerivAt.comp p hasFDerivAt_fst
  have h1 := hz'.fst
  have h2 := (hasFDerivAt_snd (p := p)).mul hz'.snd
  refine (h1.prodMk h2).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp [env_sweepDeriv]
  constructor <;> ring

/-- The Jacobian of the sweep map is `z₁'(t) z₂(t)`. -/
private lemma env_det_sweepDeriv (z ψ : ℝ → ℝ × ℝ) (p : ℝ × ℝ) :
    (env_sweepDeriv z ψ p).det = (ψ p.1).1 * (z p.1).2 := by
  unfold env_sweepDeriv
  rw [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin, Matrix.det_fin_two_of]
  ring

/-- The sweep map is injective where `z₁` is injective and `z₂ > 0`. -/
private lemma env_sweep_injOn {z : ℝ → ℝ × ℝ} {S : Set ℝ} (hinj : InjOn (fun t => (z t).1) S)
    (hpos : ∀ t ∈ S, 0 < (z t).2) : InjOn (env_sweep z) (S ×ˢ univ) := by
  rintro ⟨t, l⟩ ⟨ht, -⟩ ⟨t', l'⟩ ⟨ht', -⟩ heq
  simp only [env_sweep, Prod.mk.injEq] at heq
  have htt : t = t' := hinj ht ht' heq.1
  subst htt
  rw [mul_right_cancel₀ (hpos t ht).ne' heq.2]

/-- The area swept by `env_sweep z` over `T × (0, 1)` is `∫_T |z₁'| z₂`. -/
private lemma env_volume_sweep {z ψ : ℝ → ℝ × ℝ} {T : Set ℝ} (hT : MeasurableSet T)
    (hd : ∀ t ∈ T, HasDerivAt z (ψ t) t) (hinj : InjOn (fun t => (z t).1) T)
    (hpos : ∀ t ∈ T, 0 < (z t).2)
    (hF : AEMeasurable (fun t => ENNReal.ofReal (|(ψ t).1| * (z t).2)) (volume.restrict T)) :
    volume (env_sweep z '' (T ×ˢ Ioo 0 1)) =
      ∫⁻ t in T, ENNReal.ofReal (|(ψ t).1| * (z t).2) := by
  have hmeas : MeasurableSet (T ×ˢ Ioo (0 : ℝ) 1) := hT.prod measurableSet_Ioo
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image volume hmeas
    (fun p hp => (env_hasFDerivAt_sweep (hd p.1 hp.1)).hasFDerivWithinAt)
    ((env_sweep_injOn hinj hpos).mono (prod_mono subset_rfl (subset_univ _)))]
  have e1 : ∫⁻ p in T ×ˢ Ioo (0 : ℝ) 1, ENNReal.ofReal |(env_sweepDeriv z ψ p).det| =
      ∫⁻ p in T ×ˢ Ioo (0 : ℝ) 1, ENNReal.ofReal (|(ψ p.1).1| * (z p.1).2) * 1 := by
    refine setLIntegral_congr_fun hmeas fun p hp => ?_
    rw [env_det_sweepDeriv, abs_mul, abs_of_pos (hpos _ hp.1), mul_one]
  rw [e1, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (g := fun _ => (1 : ENNReal)) hF aemeasurable_const]
  simp only [lintegral_one, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
    ENNReal.ofReal_one, mul_one]

/-- A bounded function that is the derivative of a curve off a countable set is integrable. -/
lemma env_integrableOn_of_deriv {z ψ : ℝ → ℝ × ℝ} {a b : ℝ} {S : Set ℝ} (hS : S.Countable)
    {M : ℝ} (hd : ∀ t ∈ Ioo a b \ S, HasDerivAt z (ψ t) t) (hM : ∀ t ∈ Icc a b, ‖ψ t‖ ≤ M) :
    IntegrableOn ψ (Icc a b) := by
  have hS' : (S ∪ {a, b}).Countable := hS.union (Set.toFinite _).countable
  have hae : ∀ᵐ t ∂(volume.restrict (Icc a b)), deriv z t = ψ t := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hS'.ae_notMem volume] with t ht htI
    simp only [mem_union, mem_insert_iff, mem_singleton_iff, not_or] at ht
    exact (hd t ⟨⟨lt_of_le_of_ne htI.1 (Ne.symm ht.2.1), lt_of_le_of_ne htI.2 ht.2.2⟩,
      ht.1⟩).deriv
  exact Integrable.of_bound ((measurable_deriv z).aestronglyMeasurable.congr hae) M
    (ae_restrict_of_forall_mem measurableSet_Icc hM)

/-- Integration by parts against the curve area functional: for a primitive `z` of a bounded
integrable `ψ` (off a countable set), `∫_a^b ψ₁ z₂ = ½ [z₁ z₂]_a^b - 𝒥(z)`. -/
lemma env_integral_eq_curveArea {z ψ : ℝ → ℝ × ℝ} {a b : ℝ} {S : Set ℝ} {M : NNReal}
    (hab : a ≤ b) (hS : S.Countable) (hz : ContinuousOn z (Icc a b))
    (hd : ∀ t ∈ Ioo a b \ S, HasDerivAt z (ψ t) t)
    (hψ : IntegrableOn ψ (Icc a b)) (hψM : ∀ t ∈ Icc a b, ‖ψ t‖ ≤ M) :
    ∫ t in a..b, (ψ t).1 * (z t).2 =
      ((z b).1 * (z b).2 - (z a).1 * (z a).2) / 2 - curveArea z a b := by
  have hprim : ∀ t ∈ Icc a b, z t = z a + ∫ s in a..t, ψ s := by
    intro t ht
    rw [integral_eq_of_hasDerivAt_off_countable_of_le z ψ ht.1 hS
      (hz.mono (Icc_subset_Icc le_rfl ht.2))
      (fun s hs => hd s ⟨⟨hs.1.1, hs.1.2.trans_le ht.2⟩, hs.2⟩)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).2
        (hψ.mono_set (Icc_subset_Icc le_rfl ht.2)))]
    abel
  rw [cvx_curveArea_of_primitive hab hψ hψM hprim]
  -- `𝒥(z) = ½ ∫ z × ψ = ½ (∫ z₁ ψ₂ - ∫ ψ₁ z₂)`, and `∫ (ψ₁ z₂ + z₁ ψ₂) = [z₁ z₂]_a^b`.
  have i1 : IntervalIntegrable (fun t => (ψ t).1 * (z t).2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
      (IntegrableOn.mul_continuousOn (Integrable.fst hψ) hz.snd isCompact_Icc)
  have i2 : IntervalIntegrable (fun t => (z t).1 * (ψ t).2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
      (IntegrableOn.continuousOn_mul hz.fst (Integrable.snd hψ) isCompact_Icc)
  have hprod : ∫ t in a..b, ((ψ t).1 * (z t).2 + (z t).1 * (ψ t).2) =
      (z b).1 * (z b).2 - (z a).1 * (z a).2 :=
    integral_eq_of_hasDerivAt_off_countable_of_le (fun t => (z t).1 * (z t).2) _ hab hS
      (hz.fst.mul hz.snd)
      (fun t ht => (hasDerivAt_fst (hd t ht)).mul (hasDerivAt_snd (hd t ht))) (i1.add i2)
  have hcross : ∫ t in a..b, cross (z t) (ψ t) =
      (∫ t in a..b, (z t).1 * (ψ t).2) - ∫ t in a..b, (ψ t).1 * (z t).2 := by
    rw [← intervalIntegral.integral_sub i2 i1]
    congr 1; ext t; simp only [cross]; ring
  rw [intervalIntegral.integral_add i1 i2] at hprod
  rw [hcross]
  linarith

/-! ### The region under a curve with monotone abscissa -/

/-- The region `{q : q₂ ≥ 0, q₁ = z₁(t) and q₂ ≤ z₂(t) for some t ∈ [a, b]}` between the `x`-axis
and the curve `z|_{[a, b]}`. -/
def envRegion (z : ℝ → ℝ × ℝ) (a b : ℝ) : Set (ℝ × ℝ) :=
  {q | 0 ≤ q.2 ∧ ∃ t ∈ Icc a b, (z t).1 = q.1 ∧ q.2 ≤ (z t).2}

/-- The region `{q : q₂ ≥ 0, q₁ = z₁(t) and q₂ < z₂(t) for some t ∈ [a, b]}` strictly below the
curve `z|_{[a, b]}`. -/
def envRegionStrict (z : ℝ → ℝ × ℝ) (a b : ℝ) : Set (ℝ × ℝ) :=
  {q | 0 ≤ q.2 ∧ ∃ t ∈ Icc a b, (z t).1 = q.1 ∧ q.2 < (z t).2}

/-- The region strictly below a curve lies in the region below it. -/
lemma env_regionStrict_subset (z : ℝ → ℝ × ℝ) (a b : ℝ) :
    envRegionStrict z a b ⊆ envRegion z a b :=
  fun _ ⟨h0, t, ht, h1, h2⟩ => ⟨h0, t, ht, h1, h2.le⟩

/-- The `x`-axis is a null set. -/
lemma env_volume_horizontal : volume {q : ℝ × ℝ | q.2 = 0} = 0 := by
  have : {q : ℝ × ℝ | q.2 = 0} = univ ×ˢ {0} := by ext q; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

/-- Countably many vertical lines form a null set. -/
lemma env_volume_vertical {C : Set ℝ} (hC : C.Countable) : volume {q : ℝ × ℝ | q.1 ∈ C} = 0 := by
  have : {q : ℝ × ℝ | q.1 ∈ C} = C ×ˢ univ := by ext q; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, hC.measure_zero, zero_mul]

/-- The image of a curve that is differentiable off a countable set is a null set. -/
lemma env_volume_image {z ψ : ℝ → ℝ × ℝ} {a b : ℝ} {S : Set ℝ} (hS : S.Countable)
    (hd : ∀ t ∈ Ioo a b \ S, HasDerivAt z (ψ t) t) : volume (z '' Icc a b) = 0 := by
  have hsub : z '' Icc a b ⊆ (fun p : ℝ × ℝ => z p.1) '' ((Ioo a b \ S) ×ˢ {0}) ∪
      {q | q.1 ∈ Prod.fst '' (z '' (S ∪ {a, b}))} := by
    rintro _ ⟨t, ht, rfl⟩
    by_cases h : t ∈ S ∪ {a, b}
    · exact Or.inr ⟨z t, ⟨t, h, rfl⟩, rfl⟩
    · simp only [mem_union, mem_insert_iff, mem_singleton_iff, not_or] at h
      exact Or.inl ⟨(t, 0), ⟨⟨⟨lt_of_le_of_ne ht.1 (Ne.symm h.2.1),
        lt_of_le_of_ne ht.2 h.2.2⟩, h.1⟩, rfl⟩, rfl⟩
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · apply addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    · intro p hp
      exact ((hd p.1 hp.1).hasFDerivAt.comp p
        hasFDerivAt_fst).differentiableAt.differentiableWithinAt
    · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]
  · exact env_volume_vertical (((hS.union (Set.toFinite _).countable).image z).image Prod.fst)

/-- A monotone or antitone function is constant between two points where it takes equal values. -/
lemma env_eq_of_mono {f : ℝ → ℝ} {a b : ℝ} (hf : MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b))
    {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : f u = f v) {s : ℝ}
    (hs : s ∈ Icc u v) : f s = f u := by
  have hs' : s ∈ Icc a b := ⟨hu.1.trans hs.1, hs.2.trans hv.2⟩
  rcases hf with hf | hf
  · exact le_antisymm ((hf hs' hv hs.2).trans huv.ge) (hf hu hs' hs.1)
  · exact le_antisymm (hf hu hs' hs.1) (huv.le.trans (hf hs' hv hs.2))

/-- At a point of a level set with two points, the derivative of a monotone or antitone function
vanishes. -/
lemma env_deriv_eq_zero_of_level {f : ℝ → ℝ} {f' a b t u v : ℝ}
    (hf : MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b)) (ht : t ∈ Icc a b)
    (hd : HasDerivAt f f' t) (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u < v)
    (hfu : f u = f t) (hfv : f v = f t) : f' = 0 := by
  have hp : min t u ∈ Icc a b := ⟨le_min ht.1 hu.1, (min_le_left _ _).trans ht.2⟩
  have hq : max t v ∈ Icc a b := ⟨ht.1.trans (le_max_left _ _), max_le ht.2 hv.2⟩
  have hpq : min t u < max t v := (min_le_right t u).trans_lt (huv.trans_le (le_max_right t v))
  have hfp : f (min t u) = f t := by
    rcases min_cases t u with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
    · rw [h, hfu]
  have hfq : f (max t v) = f t := by
    rcases max_cases t v with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
    · rw [h, hfv]
  have hconst : ∀ s ∈ Icc (min t u) (max t v), f s = f t := fun s hs => by
    rw [env_eq_of_mono hf hp hq (hfp.trans hfq.symm) hs, hfp]
  have htpq : t ∈ Icc (min t u) (max t v) := ⟨min_le_left _ _, le_max_left _ _⟩
  have h2 : HasDerivWithinAt f 0 (Icc (min t u) (max t v)) t :=
    (hasDerivWithinAt_const t (Icc (min t u) (max t v)) (f t)).congr (fun s hs => hconst s hs) rfl
  exact (uniqueDiffOn_Icc hpq t htpq).eq_deriv _ hd.hasDerivWithinAt h2

/-- Every point of `(a, b)` is an accumulation point of `[a, b]`. -/
lemma env_accPt_Icc {a b t : ℝ} (ht : t ∈ Ioo a b) : AccPt t (Filter.principal (Icc a b)) := by
  have := (PerfectSpace.univ_preperfect t (mem_univ t)).nhds_inter (Icc_mem_nhds ht.1 ht.2)
  rwa [inter_univ] at this

/-- **Area under a curve.** Let `z` be continuous on `[a, b]`, with derivative `ψ` (integrable on
`[a, b]`) off a countable set, with `z₂ ≥ 0`, and with `z₁` monotone or antitone on `[a, b]`. Then
the regions on and strictly below the curve are null measurable, with area `∫_{(a,b)} |z₁'| z₂`. -/
theorem env_volume_region {z ψ : ℝ → ℝ × ℝ} {a b : ℝ} {S : Set ℝ} (hS : S.Countable)
    (hz : ContinuousOn z (Icc a b)) (hd : ∀ t ∈ Ioo a b \ S, HasDerivAt z (ψ t) t)
    (hψ : IntegrableOn ψ (Icc a b)) (hnn : ∀ t ∈ Icc a b, 0 ≤ (z t).2)
    (hmono : MonotoneOn (fun t => (z t).1) (Icc a b) ∨ AntitoneOn (fun t => (z t).1) (Icc a b)) :
    volume (envRegion z a b) = ENNReal.ofReal (∫ t in Ioo a b, |(ψ t).1| * (z t).2) ∧
      volume (envRegionStrict z a b) = ENNReal.ofReal (∫ t in Ioo a b, |(ψ t).1| * (z t).2) ∧
      NullMeasurableSet (envRegion z a b) ∧ NullMeasurableSet (envRegionStrict z a b) := by
  set f : ℝ → ℝ := fun t => (z t).1
  -- Step 1: the parameter set `T` of the sweep: the points of `(a, b)` off `S` with `z₂ > 0` at
  -- which `f = z₁` takes a value it takes only once (the values taken twice form a countable
  -- set `V`).
  set V : Set ℝ := {c | ∃ u v, u ∈ Icc a b ∧ v ∈ Icc a b ∧ u < v ∧ f u = c ∧ f v = c}
  have hV : V.Countable :=
    hmono.elim (·.countable_setOfPred_two_preimages) (·.countable_setOfPred_two_preimages)
  set Tbad : Set ℝ := Icc a b ∩ f ⁻¹' V with hTbad_def
  set T : Set ℝ := (Ioo a b ∩ (fun t => (z t).2) ⁻¹' Ioi 0) \ (S ∪ Tbad)
  have hTbad : MeasurableSet Tbad := by
    have e : Tbad = ⋃ c ∈ V, Icc a b ∩ f ⁻¹' {c} := by
      ext t
      simp only [hTbad_def, mem_inter_iff, mem_preimage, mem_iUnion, mem_singleton_iff,
        exists_prop]
      exact ⟨fun h => ⟨f t, h.2, h.1, rfl⟩, fun ⟨c, hc, ht, htc⟩ => ⟨ht, htc ▸ hc⟩⟩
    rw [e]
    exact MeasurableSet.biUnion hV fun c _ =>
      (hz.fst.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton).measurableSet
  have hT : MeasurableSet T :=
    ((hz.snd.mono Ioo_subset_Icc_self).isOpen_inter_preimage isOpen_Ioo
      isOpen_Ioi).measurableSet.diff (hS.measurableSet.union hTbad)
  have hTsub : T ⊆ Ioo a b := fun t ht => ht.1.1
  have hinj : InjOn f T := by
    intro t ht t' ht' heq
    by_contra hne
    have htI := Ioo_subset_Icc_self ht.1.1
    have htI' := Ioo_subset_Icc_self ht'.1.1
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ht.2 (Or.inr ⟨htI, t, t', htI, htI', hlt, rfl, heq.symm⟩)
    · exact ht.2 (Or.inr ⟨htI, t', t, htI', htI, hlt, heq.symm, rfl⟩)
  have hint : IntegrableOn (fun t => |(ψ t).1| * (z t).2) (Ioo a b) := by
    have h1 : Integrable (fun t => |(ψ t).1|) (volume.restrict (Icc a b)) := by
      simpa only [Real.norm_eq_abs] using (Integrable.fst hψ).norm
    exact (IntegrableOn.mul_continuousOn h1 hz.snd isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hF : AEMeasurable (fun t => ENNReal.ofReal (|(ψ t).1| * (z t).2)) (volume.restrict T) :=
    (hint.aestronglyMeasurable.aemeasurable.ennreal_ofReal).mono_measure
      (Measure.restrict_mono hTsub le_rfl)
  have hdT : ∀ t ∈ T, HasDerivAt z (ψ t) t := fun t ht => hd t ⟨ht.1.1, fun h => ht.2 (Or.inl h)⟩
  have hposT : ∀ t ∈ T, 0 < (z t).2 := fun t ht => ht.1.2
  -- Step 2: the swept region `E` is measurable with area `∫_T |z₁'| z₂ = ∫_{(a,b)} |z₁'| z₂`,
  -- since `z₁' = 0` at the points of `(a, b) \ T` off `S` where `z₂ > 0`.
  set E := env_sweep z '' (T ×ˢ Ioo 0 1) with hE_def
  have hE_meas : MeasurableSet E := measurable_image_of_fderivWithin (hT.prod measurableSet_Ioo)
    (fun p hp => (env_hasFDerivAt_sweep (hdT p.1 hp.1)).hasFDerivWithinAt)
    ((env_sweep_injOn hinj hposT).mono (prod_mono subset_rfl (subset_univ _)))
  have hE_vol : volume E = ENNReal.ofReal (∫ t in Ioo a b, |(ψ t).1| * (z t).2) := by
    rw [hE_def, env_volume_sweep hT hdT hinj hposT hF,
      ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Ioo
        fun t ht => mul_nonneg (abs_nonneg _) (hnn t (Ioo_subset_Icc_self ht))),
      ← lintegral_inter_add_sdiff _ (Ioo a b) hT, inter_eq_right.2 hTsub]
    have h0 : ∫⁻ t in Ioo a b \ T, ENNReal.ofReal (|(ψ t).1| * (z t).2) = 0 := by
      rw [setLIntegral_congr_fun_ae (measurableSet_Ioo.diff hT) (g := fun _ => 0) ?_,
        lintegral_zero]
      filter_upwards [hS.ae_notMem volume] with t htS ht
      have ht1 : t ∈ Ioo a b := ht.1
      by_cases hpos : 0 < (z t).2
      · have htb : t ∈ Tbad := by
          by_contra hcon
          exact ht.2 ⟨⟨ht1, hpos⟩, fun h => h.elim htS hcon⟩
        obtain ⟨u, v, hu, hv, huv, hfu, hfv⟩ := htb.2
        have h0 := env_deriv_eq_zero_of_level hmono htb.1
          (hasDerivAt_fst (hd t ⟨ht1, htS⟩)) hu hv huv hfu hfv
        simp [h0]
      · have : (z t).2 = 0 := le_antisymm (not_lt.1 hpos) (hnn t (Ioo_subset_Icc_self ht1))
        simp [this]
    rw [h0, add_zero]
  -- Step 3: `E ⊆ envRegionStrict ⊆ envRegion ⊆ E ∪ N`, where the null set `N` consists of the
  -- `x`-axis, countably many vertical lines and the curve itself.
  have hE_sub : E ⊆ envRegionStrict z a b := by
    rintro _ ⟨⟨t, l⟩, ⟨ht, hl⟩, rfl⟩
    have hz2 := hposT t ht
    refine ⟨mul_nonneg hl.1.le hz2.le, t, Ioo_subset_Icc_self ht.1.1, rfl, ?_⟩
    show l * (z t).2 < (z t).2
    nlinarith [hl.2]
  have hsc := env_regionStrict_subset z a b
  set C : Set ℝ := f '' (S ∪ {a, b}) ∪ V
  have hC : C.Countable := ((hS.union (Set.toFinite _).countable).image f).union hV
  set N : Set (ℝ × ℝ) := {q | q.2 = 0} ∪ {q | q.1 ∈ C} ∪ z '' Icc a b
  have hN : volume N = 0 := measure_union_null
    (measure_union_null env_volume_horizontal (env_volume_vertical hC)) (env_volume_image hS hd)
  have hcl_sub : envRegion z a b ⊆ E ∪ N := by
    rintro q ⟨hq0, t, ht, hq1, hq2⟩
    by_cases hq0' : q.2 = 0
    · exact Or.inr (Or.inl (Or.inl hq0'))
    by_cases htC : t ∈ S ∪ {a, b} ∪ Tbad
    · refine Or.inr (Or.inl (Or.inr ?_))
      show q.1 ∈ C
      rw [← hq1]
      rcases htC with h | h
      · exact Or.inl ⟨t, h, rfl⟩
      · exact Or.inr h.2
    by_cases hq2' : q.2 = (z t).2
    · refine Or.inr (Or.inr ⟨t, ht, ?_⟩)
      exact Prod.ext hq1 hq2'.symm
    have htS : t ∉ S := fun h => htC (Or.inl (Or.inl h))
    have hta : t ≠ a := fun h => htC (Or.inl (Or.inr (Or.inl h)))
    have htb : t ≠ b := fun h => htC (Or.inl (Or.inr (Or.inr h)))
    have htB : t ∉ Tbad := fun h => htC (Or.inr h)
    have ht' : t ∈ Ioo a b := ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩
    have hq2pos : 0 < q.2 := lt_of_le_of_ne hq0 (Ne.symm hq0')
    have hlt : q.2 < (z t).2 := lt_of_le_of_ne hq2 hq2'
    have hz2 : 0 < (z t).2 := hq2pos.trans hlt
    have htT : t ∈ T := ⟨⟨ht', hz2⟩, fun h => h.elim htS htB⟩
    refine Or.inl ⟨(t, q.2 / (z t).2), ⟨htT, div_pos hq2pos hz2, (div_lt_one hz2).2 hlt⟩, ?_⟩
    refine Prod.ext hq1 ?_
    show q.2 / (z t).2 * (z t).2 = q.2
    field_simp
  -- Step 4: hence both regions have the area of `E` and are null measurable.
  have hvol_cl : volume (envRegion z a b) = volume E := by
    apply le_antisymm
    · calc volume (envRegion z a b) ≤ volume (E ∪ N) := measure_mono hcl_sub
        _ ≤ volume E + volume N := measure_union_le _ _
        _ = volume E := by rw [hN, add_zero]
    · exact measure_mono (hE_sub.trans hsc)
  have hvol_st : volume (envRegionStrict z a b) = volume E :=
    le_antisymm ((measure_mono hsc).trans hvol_cl.le) (measure_mono hE_sub)
  have hnm : ∀ R : Set (ℝ × ℝ), E ⊆ R → R ⊆ E ∪ N → NullMeasurableSet R volume := by
    intro R h1 h2
    rw [← union_sdiff_cancel h1]
    exact hE_meas.nullMeasurableSet.union (NullMeasurableSet.of_null
      (measure_mono_null (fun q hq => (h2 hq.1).resolve_left hq.2) hN))
  exact ⟨hvol_cl.trans hE_vol, hvol_st.trans hE_vol, hnm _ (hE_sub.trans hsc) hcl_sub,
    hnm _ hE_sub (hsc.trans hcl_sub)⟩

/-- For `z₁` monotone, `∫_{(a,b)} |z₁'| z₂ = ½ [z₁ z₂]_a^b - 𝒥(z)`. -/
lemma env_integral_abs_of_monotoneOn {z ψ : ℝ → ℝ × ℝ} {a b : ℝ} {S : Set ℝ} {M : NNReal}
    (hab : a ≤ b) (hS : S.Countable) (hz : ContinuousOn z (Icc a b))
    (hd : ∀ t ∈ Ioo a b \ S, HasDerivAt z (ψ t) t) (hψ : IntegrableOn ψ (Icc a b))
    (hψM : ∀ t ∈ Icc a b, ‖ψ t‖ ≤ M) (hmono : MonotoneOn (fun t => (z t).1) (Icc a b)) :
    ∫ t in Ioo a b, |(ψ t).1| * (z t).2 =
      ((z b).1 * (z b).2 - (z a).1 * (z a).2) / 2 - curveArea z a b := by
  rw [← env_integral_eq_curveArea hab hS hz hd hψ hψM, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_ae measurableSet_Ioo ?_
  filter_upwards [hS.ae_notMem volume] with t htS ht
  rw [abs_of_nonneg ((hasDerivAt_fst (hd t ⟨ht, htS⟩)).hasDerivWithinAt.nonneg_of_monotoneOn
    (env_accPt_Icc ht) hmono)]

/-- For `z₁` antitone, `∫_{(a,b)} |z₁'| z₂ = 𝒥(z) - ½ [z₁ z₂]_a^b`. -/
lemma env_integral_abs_of_antitoneOn {z ψ : ℝ → ℝ × ℝ} {a b : ℝ} {S : Set ℝ} {M : NNReal}
    (hab : a ≤ b) (hS : S.Countable) (hz : ContinuousOn z (Icc a b))
    (hd : ∀ t ∈ Ioo a b \ S, HasDerivAt z (ψ t) t) (hψ : IntegrableOn ψ (Icc a b))
    (hψM : ∀ t ∈ Icc a b, ‖ψ t‖ ≤ M) (hanti : AntitoneOn (fun t => (z t).1) (Icc a b)) :
    ∫ t in Ioo a b, |(ψ t).1| * (z t).2 =
      curveArea z a b - ((z b).1 * (z b).2 - (z a).1 * (z a).2) / 2 := by
  have h := env_integral_eq_curveArea hab hS hz hd hψ hψM
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo] at h
  have e : ∫ t in Ioo a b, |(ψ t).1| * (z t).2 = ∫ t in Ioo a b, -((ψ t).1 * (z t).2) := by
    refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [hS.ae_notMem volume] with t htS ht
    rw [abs_of_nonpos ((hasDerivAt_fst (hd t ⟨ht, htS⟩)).hasDerivWithinAt.nonpos_of_antitoneOn
      (env_accPt_Icc ht) hanti), neg_mul]
  rw [e, integral_neg, h]
  ring

/-- **Area under a curve with nondecreasing abscissa.** Let `z` be continuous on `[a, b]`, with a
bounded derivative `ψ` off a countable set, `z₂ ≥ 0` and `z₁` monotone on `[a, b]`. Then the regions
on and strictly below `z|_{[a, b]}` both have area `½ [z₁ z₂]_a^b - 𝒥(z)`. -/
theorem env_volume_region_of_monotoneOn {z ψ : ℝ → ℝ × ℝ} {a b M : ℝ} {S : Set ℝ} (hab : a ≤ b)
    (hS : S.Countable) (hz : ContinuousOn z (Icc a b))
    (hd : ∀ t ∈ Ioo a b \ S, HasDerivAt z (ψ t) t) (hψM : ∀ t ∈ Icc a b, ‖ψ t‖ ≤ M)
    (hnn : ∀ t ∈ Icc a b, 0 ≤ (z t).2) (hmono : MonotoneOn (fun t => (z t).1) (Icc a b)) :
    volume (envRegion z a b) =
        ENNReal.ofReal (((z b).1 * (z b).2 - (z a).1 * (z a).2) / 2 - curveArea z a b) ∧
      volume (envRegionStrict z a b) =
        ENNReal.ofReal (((z b).1 * (z b).2 - (z a).1 * (z a).2) / 2 - curveArea z a b) ∧
      0 ≤ ((z b).1 * (z b).2 - (z a).1 * (z a).2) / 2 - curveArea z a b := by
  have hψ := env_integrableOn_of_deriv hS hd hψM
  have hψM' : ∀ t ∈ Icc a b, ‖ψ t‖ ≤ M.toNNReal := fun t ht =>
    (hψM t ht).trans (Real.le_coe_toNNReal M)
  have hI := env_integral_abs_of_monotoneOn hab hS hz hd hψ hψM' hmono
  obtain ⟨h1, h2, -, -⟩ := env_volume_region hS hz hd hψ hnn (Or.inl hmono)
  refine ⟨hI ▸ h1, hI ▸ h2, hI ▸ setIntegral_nonneg measurableSet_Ioo fun t ht =>
    mul_nonneg (abs_nonneg _) (hnn t (Ioo_subset_Icc_self ht))⟩

/-- **Area under a curve with nonincreasing abscissa.** Let `z` be continuous on `[a, b]`, with a
bounded derivative `ψ` off a countable set, `z₂ ≥ 0` and `z₁` antitone on `[a, b]`. Then the regions
on and strictly below `z|_{[a, b]}` both have area `𝒥(z) - ½ [z₁ z₂]_a^b`. -/
theorem env_volume_region_of_antitoneOn {z ψ : ℝ → ℝ × ℝ} {a b M : ℝ} {S : Set ℝ} (hab : a ≤ b)
    (hS : S.Countable) (hz : ContinuousOn z (Icc a b))
    (hd : ∀ t ∈ Ioo a b \ S, HasDerivAt z (ψ t) t) (hψM : ∀ t ∈ Icc a b, ‖ψ t‖ ≤ M)
    (hnn : ∀ t ∈ Icc a b, 0 ≤ (z t).2) (hanti : AntitoneOn (fun t => (z t).1) (Icc a b)) :
    volume (envRegion z a b) =
        ENNReal.ofReal (curveArea z a b - ((z b).1 * (z b).2 - (z a).1 * (z a).2) / 2) ∧
      volume (envRegionStrict z a b) =
        ENNReal.ofReal (curveArea z a b - ((z b).1 * (z b).2 - (z a).1 * (z a).2) / 2) ∧
      0 ≤ curveArea z a b - ((z b).1 * (z b).2 - (z a).1 * (z a).2) / 2 := by
  have hψ := env_integrableOn_of_deriv hS hd hψM
  have hψM' : ∀ t ∈ Icc a b, ‖ψ t‖ ≤ M.toNNReal := fun t ht =>
    (hψM t ht).trans (Real.le_coe_toNNReal M)
  have hI := env_integral_abs_of_antitoneOn hab hS hz hd hψ hψM' hanti
  obtain ⟨h1, h2, -, -⟩ := env_volume_region hS hz hd hψ hnn (Or.inr hanti)
  refine ⟨hI ▸ h1, hI ▸ h2, hI ▸ setIntegral_nonneg measurableSet_Ioo fun t ht =>
    mul_nonneg (abs_nonneg _) (hnn t (Ioo_subset_Icc_self ht))⟩

/-- The regions on and strictly below a curve with monotone or antitone abscissa are null
measurable. -/
theorem env_nullMeasurableSet_region {z ψ : ℝ → ℝ × ℝ} {a b M : ℝ} {S : Set ℝ}
    (hS : S.Countable) (hz : ContinuousOn z (Icc a b))
    (hd : ∀ t ∈ Ioo a b \ S, HasDerivAt z (ψ t) t) (hψM : ∀ t ∈ Icc a b, ‖ψ t‖ ≤ M)
    (hnn : ∀ t ∈ Icc a b, 0 ≤ (z t).2)
    (hmono : MonotoneOn (fun t => (z t).1) (Icc a b) ∨ AntitoneOn (fun t => (z t).1) (Icc a b)) :
    NullMeasurableSet (envRegion z a b) ∧ NullMeasurableSet (envRegionStrict z a b) :=
  (env_volume_region hS hz hd (env_integrableOn_of_deriv hS hd hψM) hnn hmono).2.2

/-- The abscissas of the region below a curve with monotone abscissa lie in `[z₁(a), z₁(b)]`. -/
lemma env_region_fst_mem_of_monotoneOn {z : ℝ → ℝ × ℝ} {a b : ℝ}
    (hmono : MonotoneOn (fun t => (z t).1) (Icc a b)) {q : ℝ × ℝ} (hq : q ∈ envRegion z a b) :
    q.1 ∈ Icc (z a).1 (z b).1 := by
  obtain ⟨-, t, ht, hq1, -⟩ := hq
  rw [← hq1]
  exact ⟨hmono ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1, hmono ht ⟨ht.1.trans ht.2, le_rfl⟩ ht.2⟩

/-- The abscissas of the region below a curve with antitone abscissa lie in `[z₁(b), z₁(a)]`. -/
lemma env_region_fst_mem_of_antitoneOn {z : ℝ → ℝ × ℝ} {a b : ℝ}
    (hanti : AntitoneOn (fun t => (z t).1) (Icc a b)) {q : ℝ × ℝ} (hq : q ∈ envRegion z a b) :
    q.1 ∈ Icc (z b).1 (z a).1 := by
  obtain ⟨-, t, ht, hq1, -⟩ := hq
  rw [← hq1]
  exact ⟨hanti ht ⟨ht.1.trans ht.2, le_rfl⟩ ht.2, hanti ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1⟩

/-- Areas of two sets on either side of a vertical line `{q₁ = c}` add up. -/
lemma env_volume_union_of_sep {R₁ R₂ : Set (ℝ × ℝ)} (c : ℝ) (hR₂ : NullMeasurableSet R₂ volume)
    (hsep : ((∀ q ∈ R₁, q.1 ≤ c) ∧ ∀ q ∈ R₂, c ≤ q.1) ∨ ((∀ q ∈ R₁, c ≤ q.1) ∧ ∀ q ∈ R₂, q.1 ≤ c)) :
    volume (R₁ ∪ R₂) = volume R₁ + volume R₂ := by
  refine measure_union₀ hR₂ (measure_mono_null ?_ (env_volume_vertical (countable_singleton c)))
  rintro q ⟨hq₁, hq₂⟩
  rcases hsep with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact le_antisymm (h₁ q hq₁) (h₂ q hq₂)
  · exact le_antisymm (h₂ q hq₂) (h₁ q hq₁)

/-! ### The area of the niche -/

/-- The region below a union of curves is the union of the regions. -/
lemma env_underStrict_union (Γ₁ Γ₂ : Set (ℝ × ℝ)) :
    envUnderStrict (Γ₁ ∪ Γ₂) = envUnderStrict Γ₁ ∪ envUnderStrict Γ₂ := by
  ext q
  constructor
  · rintro ⟨h0, γ, hγ | hγ, h1, h2⟩
    exacts [Or.inl ⟨h0, γ, hγ, h1, h2⟩, Or.inr ⟨h0, γ, hγ, h1, h2⟩]
  · rintro (⟨h0, γ, hγ, h1, h2⟩ | ⟨h0, γ, hγ, h1, h2⟩)
    exacts [⟨h0, γ, Or.inl hγ, h1, h2⟩, ⟨h0, γ, Or.inr hγ, h1, h2⟩]

/-- The region strictly below the image of a curve. -/
lemma env_underStrict_image (z : ℝ → ℝ × ℝ) (a b : ℝ) :
    envUnderStrict (z '' Icc a b) = envRegionStrict z a b := by
  ext q
  constructor
  · rintro ⟨h0, _, ⟨t, ht, rfl⟩, h1, h2⟩
    exact ⟨h0, t, ht, h1, h2⟩
  · rintro ⟨h0, t, ht, h1, h2⟩
    exact ⟨h0, z t, ⟨t, ht, rfl⟩, h1, h2⟩

section area

variable {t₁ t₂ t₃ t₄ sA sC : ℝ} {x : ℝ → ℝ × ℝ} {α β ρA ρC : ℝ → ℝ}

/-- The niche is the union of the regions strictly below `𝐁|_{[t₃, π/2]}`, `𝐱|_{[t₁, t₄]}` and
`𝐃|_{[0, t₂]}`. -/
lemma env_niche_eq_union (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) :
    envNiche x = envRegionStrict (envB x α) t₃ (π / 2) ∪ envRegionStrict x t₁ t₄ ∪
      envRegionStrict (envD x β) 0 t₂ := by
  rw [env_niche_eq h, envCurve, env_underStrict_union, env_underStrict_union,
    env_underStrict_image, env_underStrict_image, env_underStrict_image]

/-- **The area of the niche** (Theorem 8.4.1 (2)):
`|N| = 𝒥(𝐱|_{[t₁, t₄]}) - 𝒥(𝐁|_{[t₃, π/2]}) - 𝒥(𝐃|_{[0, t₂]})`. The extra hypotheses bound `ρ_A` and
`ρ_C` from below on the intervals where `𝐁` and `𝐃` are used (they are bounded above by `1` there
by `EnvHyp`). -/
theorem env_area (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC)
    (hρA : BddBelow (ρA '' Icc t₃ (π / 2))) (hρC : BddBelow (ρC '' Icc 0 t₂)) :
    area (envNiche x) =
      curveArea x t₁ t₄ - curveArea (envB x α) t₃ (π / 2) - curveArea (envD x β) 0 t₂ := by
  obtain ⟨ht₁, ht₁₂, ht₂₃, ht₃₄, ht₄⟩ := h.ht
  have hS := (env_bp_finite t₁ t₂ t₃ t₄).countable
  -- the curve `𝐁` on `[t₃, π/2]`
  obtain ⟨mA, hmA⟩ := hρA
  have hB_cont : ContinuousOn (envB x α) (Icc t₃ (π / 2)) :=
    (env_B_cont h).mono (Icc_subset_Icc (by linarith) le_rfl)
  have hB_d : ∀ t ∈ Ioo t₃ (π / 2) \ {t₁, t₂, t₃, t₄},
      HasDerivAt (envB x α) ((ρA t - 1) • vvec t) t :=
    fun t ht => h.B_deriv t ⟨by linarith [ht.1.1], ht.1.2⟩ ht.2
  have hB_M : ∀ t ∈ Icc t₃ (π / 2), ‖(ρA t - 1) • vvec t‖ ≤ 1 - mA := fun t ht => by
    have h1 : mA ≤ ρA t := hmA ⟨t, ht, rfl⟩
    have h2 : ρA t < 1 := h.ρA_lt t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_neg (by linarith)]
    nlinarith [norm_vvec_le t, norm_nonneg (vvec t)]
  have hB_nn : ∀ t ∈ Icc t₃ (π / 2), 0 ≤ (envB x α t).2 := fun t ht =>
    h.B_end ▸ (env_B₂_strictAnti h).antitoneOn ht ⟨by linarith [ht.1], le_rfl⟩ ht.2
  have hB_mono := (env_B₁_strictMono h).monotoneOn
  obtain ⟨-, hB2, hB3⟩ :=
    env_volume_region_of_monotoneOn (by linarith) hS hB_cont hB_d hB_M hB_nn hB_mono
  -- the curve `𝐱` on `[t₁, t₄]`
  have hsubx : Icc t₁ t₄ ⊆ Icc 0 (π / 2) := Icc_subset_Icc ht₁.le ht₄.le
  have hx_cont : ContinuousOn x (Icc t₁ t₄) := h.x_cont.mono hsubx
  have hx_d : ∀ t ∈ Ioo t₁ t₄ \ {t₁, t₂, t₃, t₄},
      HasDerivAt x (α t • uvec t + β t • vvec t) t :=
    fun t ht => h.x_deriv t ⟨by linarith [ht.1.1], by linarith [ht.1.2]⟩
  have hψx : ContinuousOn (fun t => α t • uvec t + β t • vvec t) (Icc t₁ t₄) :=
    ((h.α_cont.mono hsubx).smul continuous_uvec.continuousOn).add
      ((h.β_cont.mono hsubx).smul continuous_vvec.continuousOn)
  obtain ⟨Mx, hx_M⟩ := isCompact_Icc.exists_bound_of_continuousOn hψx
  have hx_nn : ∀ t ∈ Icc t₁ t₄, 0 ≤ (x t).2 := fun t ht => (h.x_pos t ht).le
  have hx_anti := (env_x₁_strictAnti h).antitoneOn
  obtain ⟨-, hx2, hx3⟩ :=
    env_volume_region_of_antitoneOn (by linarith) hS hx_cont hx_d hx_M hx_nn hx_anti
  -- the curve `𝐃` on `[0, t₂]`
  obtain ⟨mC, hmC⟩ := hρC
  have hD_cont : ContinuousOn (envD x β) (Icc 0 t₂) :=
    (env_D_cont h).mono (Icc_subset_Icc le_rfl (by linarith))
  have hD_d : ∀ t ∈ Ioo 0 t₂ \ {t₁, t₂, t₃, t₄},
      HasDerivAt (envD x β) ((1 - ρC t) • uvec t) t :=
    fun t ht => h.D_deriv t ⟨ht.1.1, by linarith [ht.1.2]⟩ ht.2
  have hD_M : ∀ t ∈ Icc 0 t₂, ‖(1 - ρC t) • uvec t‖ ≤ 1 - mC := fun t ht => by
    have h1 : mC ≤ ρC t := hmC ⟨t, ht, rfl⟩
    have h2 : ρC t < 1 := h.ρC_lt t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
    nlinarith [norm_uvec_le t, norm_nonneg (uvec t)]
  have hD_nn : ∀ t ∈ Icc 0 t₂, 0 ≤ (envD x β t).2 := fun t ht =>
    h.D_end ▸ (env_D₂_strictMono h).monotoneOn ⟨le_rfl, by linarith [ht.2]⟩ ht ht.1
  have hD_mono := (env_D₁_strictMono h).monotoneOn
  obtain ⟨-, hD2, hD3⟩ :=
    env_volume_region_of_monotoneOn (by linarith) hS hD_cont hD_d hD_M hD_nn hD_mono
  -- null measurability, and the separation of the three regions by two vertical lines
  have hx4 := (env_nullMeasurableSet_region hS hx_cont hx_d hx_M hx_nn (Or.inr hx_anti)).2
  have hD4 := (env_nullMeasurableSet_region hS hD_cont hD_d hD_M hD_nn (Or.inl hD_mono)).2
  have hB_fst : ∀ q ∈ envRegionStrict (envB x α) t₃ (π / 2), (x t₁).1 ≤ q.1 := fun q hq => by
    have := (env_region_fst_mem_of_monotoneOn hB_mono (env_regionStrict_subset _ _ _ hq)).1
    rwa [h.B_t₃] at this
  have hx_fst : ∀ q ∈ envRegionStrict x t₁ t₄, q.1 ∈ Icc (x t₄).1 (x t₁).1 := fun q hq =>
    env_region_fst_mem_of_antitoneOn hx_anti (env_regionStrict_subset _ _ _ hq)
  have hD_fst : ∀ q ∈ envRegionStrict (envD x β) 0 t₂, q.1 ≤ (x t₄).1 := fun q hq => by
    have := (env_region_fst_mem_of_monotoneOn hD_mono (env_regionStrict_subset _ _ _ hq)).2
    rwa [h.D_t₂] at this
  have hx14 : (x t₄).1 ≤ (x t₁).1 :=
    hx_anti ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
  have hvol : volume (envNiche x) = volume (envRegionStrict (envB x α) t₃ (π / 2)) +
      volume (envRegionStrict x t₁ t₄) + volume (envRegionStrict (envD x β) 0 t₂) := by
    rw [env_niche_eq_union h,
      env_volume_union_of_sep (x t₄).1 hD4 (Or.inr ⟨fun q hq => ?_, hD_fst⟩),
      env_volume_union_of_sep (x t₁).1 hx4 (Or.inr ⟨hB_fst, fun q hq => (hx_fst q hq).2⟩)]
    rcases hq with hq | hq
    · exact hx14.trans (hB_fst q hq)
    · exact (hx_fst q hq).1
  rw [area, hvol, hB2, hx2, hD2, ← ENNReal.ofReal_add hB3 hx3,
    ← ENNReal.ofReal_add (add_nonneg hB3 hx3) hD3,
    ENNReal.toReal_ofReal (add_nonneg (add_nonneg hB3 hx3) hD3), h.B_end, h.B_t₃, h.D_t₂,
    h.D_end]
  ring

end area

end MovingSofaOptimality
