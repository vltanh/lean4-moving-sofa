module

public import MovingSofaQuantitative.InactiveWallGap
public import MovingSofaQuantitative.PerturbationEnergy

/-!
# Perturbing a wall inequality that vanishes at both endpoints

Uncompiled proof source. Ordinary uniform closeness is insufficient near the
zero endpoints. The exact value and first-derivative matches give the weighted
bound |w(t)| <= C (t-a)(b-t)^2, which is compared to the reference gap with the
same weight. No positive minimum of the unweighted gap is assumed.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

def harmonicBridge (a b ya yb : ℝ) (t : ℝ) : ℝ :=
  (ya*sin(b-t)+yb*sin(t-a))/sin(b-a)

def harmonicBridgeFirst (a b ya yb : ℝ) (t : ℝ) : ℝ :=
  (-ya*cos(b-t)+yb*cos(t-a))/sin(b-a)

theorem harmonicBridge_derivative (a b ya yb t : ℝ) :
    HasDerivAt (harmonicBridge a b ya yb) (harmonicBridgeFirst a b ya yb t) t := by
  convert (((((hasDerivAt_id t).const_sub b).sin).const_mul ya).add
    ((((hasDerivAt_id t).sub_const a).sin).const_mul yb)).div_const (sin (b-a)) using 1 <;>
    simp only [harmonicBridge, harmonicBridgeFirst] <;> ring

theorem harmonicBridge_second (a b ya yb t : ℝ) :
    HasDerivAt (harmonicBridgeFirst a b ya yb) (-harmonicBridge a b ya yb t) t := by
  convert (((((hasDerivAt_id t).const_sub b).cos).const_mul (-ya)).add
    ((((hasDerivAt_id t).sub_const a).cos).const_mul yb)).div_const (sin (b-a)) using 1 <;>
    simp only [harmonicBridge, harmonicBridgeFirst] <;> ring

theorem harmonicBridge_endpoints {a b ya yb : ℝ} (hs : sin(b-a) ≠ 0) :
    harmonicBridge a b ya yb a = ya ∧ harmonicBridge a b ya yb b = yb := by
  constructor <;> simp [harmonicBridge, hs]

/-- A first-derivative bound which vanishes linearly at the matched right jet. -/
theorem derivative_bound_from_right_zero {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    {f df : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hb : f b = 0) (hbound : ∀ t ∈ Ioo a b, |df t| ≤ M)
    {t : ℝ} (ht : t ∈ Icc a b) : |f t| ≤ M*(b-t) := by
  have hup := right_derivative_increment_le ht.2
    (hf.mono (Icc_subset_Icc_left ht.1))
    (fun u hu => hd u ⟨ht.1.trans_lt hu.1, hu.2⟩)
    (fun u hu => (abs_le.mp (hbound u ⟨ht.1.trans_lt hu.1, hu.2⟩)).2)
  have hlo := right_derivative_increment_ge ht.2
    (hf.mono (Icc_subset_Icc_left ht.1))
    (fun u hu => hd u ⟨ht.1.trans_lt hu.1, hu.2⟩)
    (B := -M) (fun u hu => (abs_le.mp (hbound u ⟨ht.1.trans_lt hu.1, hu.2⟩)).1)
  rw [hb] at hup hlo
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem integral_linear_tail (b M t : ℝ) :
    (∫ u in t..b, M*(b-u)) = M*(b-t)^2/2 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u : ℝ => M*(b*u-u^2/2)) (f' := fun u => M*(b-u))
    (fun u _ => by
      convert (((hasDerivAt_id u).const_mul b).sub
        (((hasDerivAt_id u).pow 2).div_const 2)).const_mul M using 1 <;> ring)
    ((show Continuous (fun u : ℝ => M*(b-u)) by fun_prop).intervalIntegrable _ _)
  rw [h]
  ring

/-- The endpoint value and derivative matches produce a quadratic remainder
without requiring a continuous second derivative at the internal knots. -/
theorem quadratic_endpoint_bound {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    {f df ddf : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) (hdf : ContinuousOn df (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hdd : ∀ t ∈ Ioo a b, HasDerivWithinAt df (ddf t) (Ioi t) t)
    (hfb : f b = 0) (hdb : df b = 0)
    (hbound : ∀ t ∈ Ioo a b, |ddf t| ≤ M)
    {t : ℝ} (ht : t ∈ Icc a b) : |f t| ≤ M*(b-t)^2/2 := by
  have hfirst : ∀ u ∈ Icc a b, |df u| ≤ M*(b-u) :=
    fun u hu => derivative_bound_from_right_zero hab hM hdf hdd hdb hbound hu
  have hi := (hdf.mono (Icc_subset_Icc_left ht.1)).intervalIntegrable_of_Icc ht.2
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.2
    (hf.mono (Icc_subset_Icc_left ht.1))
    (fun u hu => hd u ⟨ht.1.trans_lt hu.1, hu.2⟩) hi
  have hup := intervalIntegral.integral_mono_on ht.2 hi
    ((show Continuous (fun u : ℝ => M*(b-u)) by fun_prop).intervalIntegrable t b)
    (fun u hu => (abs_le.mp (hfirst u ⟨ht.1.trans hu.1, hu.2⟩)).2)
  have hlo := intervalIntegral.integral_mono_on ht.2
    ((show Continuous (fun u : ℝ => -(M*(b-u))) by fun_prop).intervalIntegrable t b) hi
    (fun u hu => (abs_le.mp (hfirst u ⟨ht.1.trans hu.1, hu.2⟩)).1)
  rw [he, hfb, integral_linear_tail] at hup
  rw [intervalIntegral.integral_neg, integral_linear_tail, he, hfb] at hlo
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The normalized weight has the same linear and quadratic zeros as the
reference inactive-wall gap. -/
theorem weighted_endpoint_bound {a b M : ℝ} (hab : a < b) (hM : 0 ≤ M)
    {f df ddf : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) (hdf : ContinuousOn df (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hdd : ∀ t ∈ Ioo a b, HasDerivWithinAt df (ddf t) (Ioi t) t)
    (hfa : f a = 0) (hfb : f b = 0) (hdb : df b = 0)
    (hbound : ∀ t ∈ Ioo a b, |ddf t| ≤ M)
    {t : ℝ} (ht : t ∈ Icc a b) :
    |f t| ≤ (4*M/(b-a))*(t-a)*(b-t)^2 := by
  have hfirst : ∀ u ∈ Icc a b, |df u| ≤ M*(b-a) := by
    intro u hu
    exact (derivative_bound_from_right_zero hab.le hM hdf hdd hdb hbound hu).trans
      (mul_le_mul_of_nonneg_left (by linarith [hu.1]) hM)
  have hup := right_derivative_increment_le ht.1
    (hf.mono (Icc_subset_Icc_right ht.2))
    (fun u hu => hd u ⟨hu.1, hu.2.trans_le ht.2⟩)
    (fun u hu => (abs_le.mp (hfirst u ⟨hu.1.le, hu.2.le.trans ht.2⟩)).2)
  have hlo := right_derivative_increment_ge ht.1
    (hf.mono (Icc_subset_Icc_right ht.2))
    (fun u hu => hd u ⟨hu.1, hu.2.trans_le ht.2⟩)
    (B := -(M*(b-a))) (fun u hu => (abs_le.mp (hfirst u ⟨hu.1.le, hu.2.le.trans ht.2⟩)).1)
  rw [hfa] at hup hlo
  have hlin : |f t| ≤ M*(b-a)*(t-a) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hquad := quadratic_endpoint_bound hab.le hM hf hdf hd hdd hfb hdb hbound ht
  have hL : 0 < b-a := sub_pos.mpr hab
  apply (le_div_iff₀ hL).mp
  rw [show (4*M/(b-a))*(t-a)*(b-t)^2 = (4*M*(t-a)*(b-t)^2)/(b-a) by ring]
  apply (le_div_iff₀ hL).mpr
  rcases le_total t ((a+b)/2) with hleft | hright
  · have hs : (b-a)^2 ≤ 4*(b-t)^2 := by nlinarith [ht.1, ht.2]
    have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg hM (sub_nonneg.mpr ht.1))
    have hb := mul_le_mul_of_nonneg_right hlin hL.le
    nlinarith only [hm, hb]
  · have hs : b-a ≤ 2*(t-a) := by linarith
    have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg hM (sq_nonneg (b-t)))
    have hb := mul_le_mul_of_nonneg_right hquad hL.le
    nlinarith only [hm, hb]

/-- A C1 profile with the exact harmonic right jet admits a weighted error
bound against its harmonic bridge. The bound is finite, not sampled. -/
theorem HalfCapProfile.bridge_error_bound {φ c : ℝ} (F : HalfCapProfile φ)
    (hφ : 0 < φ) (hφc : φ < c) (hcv : c < π/2)
    (hjet : F.first c = harmonicBridgeFirst φ c (F.value φ) (F.value c) c) :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Icc φ c,
      |F.value t-harmonicBridge φ c (F.value φ) (F.value c) t| ≤
        B*(t-φ)*(c-t)^2 := by
  let H := harmonicBridge φ c (F.value φ) (F.value c)
  let dH := harmonicBridgeFirst φ c (F.value φ) (F.value c)
  let w := fun t => F.value t-H t
  let dw := fun t => F.first t-dH t
  let ddw := fun t => F.secondR t+H t
  have hH : Continuous H := continuous_iff_continuousAt.mpr fun t =>
    (harmonicBridge_derivative φ c (F.value φ) (F.value c) t).continuousAt
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((F.continuous_value.norm.add hH.norm).continuousOn)
  let M := F.curvatureBound+|R|+1
  have hM : 0 < M := by dsimp [M]; have h := F.bound_nonneg; positivity
  have hbound : ∀ t ∈ Ioo φ c, |ddw t| ≤ M := by
    intro t ht
    have hc := F.central_right t ⟨ht.1.le, ht.2.le.trans hcv.le⟩
    have hr := hR t ⟨ht.1.le, ht.2.le⟩
    have he : ddw t = (F.secondR t+F.value t)+(H t-F.value t) := by dsimp [ddw]; ring
    rw [he]
    have hh := (abs_add_le _ _).trans (add_le_add hc (abs_sub _ _))
    dsimp [M]
    simp only [Real.norm_eq_abs] at hr
    linarith [le_abs_self R]
  have hs : sin(c-φ) ≠ 0 :=
    (sin_pos_of_pos_of_lt_pi (sub_pos.mpr hφc) (by linarith [pi_pos])).ne'
  have he := harmonicBridge_endpoints (ya := F.value φ) (yb := F.value c) hs
  refine ⟨4*M/(c-φ), by positivity, ?_⟩
  intro t ht
  apply weighted_endpoint_bound hφc hM.le
    ((F.continuous_value.sub hH).continuousOn)
    ((F.first_continuous.sub (continuous_iff_continuousAt.mpr fun u =>
      (harmonicBridge_second φ c (F.value φ) (F.value c) u).continuousAt)).continuousOn)
    (fun u _ => ((F.derivative u).sub (harmonicBridge_derivative φ c (F.value φ) (F.value c) u)).hasDerivWithinAt)
    (fun u _ => by
      convert (F.second_right u).mono (show Ioi u ⊆ Ici u from Ioi_subset_Ici_self) |>.sub
        (harmonicBridge_second φ c (F.value φ) (F.value c) u).hasDerivWithinAt using 1 <;> ring)
    (by dsimp [w, H]; rw [he.1]; ring)
    (by dsimp [w, H]; rw [he.2]; ring)
    (by dsimp [dw, dH]; rw [hjet]; ring) hbound ht

end MovingSofaQuantitative
