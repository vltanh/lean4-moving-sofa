module

public import MovingSofaQuantitative.EndpointAveraging
public import MovingSofaQuantitative.KernelGram

/-!
# The two auxiliary endpoint penalties

Uncompiled proof source. The penalties come from weighted Cauchy--Schwarz on
subarcs of the auxiliary residuals. The wall slacks have opposite signs in the
two formulas; these signs are retained rather than lost inside a norm estimate.
This analytic lemma does not itself assert that a feasible triple has the
required reference-density bounds. The actual-triple adapter is separate.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaStability

namespace MovingSofaQuantitative

/-- The integrated reciprocal-square kernel bounds a weighted residual
without discarding the full subarc energy. -/
theorem weighted_endpoint_penalty {a b D E : ℝ} (hab : a ≤ b) (hD : 0 < D)
    {k r : ℝ → ℝ} (hk : ContinuousOn k (Icc a b))
    (hr : IntervalIntegrable r volume a b)
    (hr2 : IntervalIntegrable (fun t => r t ^ 2) volume a b)
    (hkernel : (∫ t in a..b, k t ^ 2) = D)
    (henergy : arcSquare a b r ≤ E) :
    (∫ t in a..b, k t * r t) ^ 2 / D ≤ E := by
  have h := (integral_square_control hab hk hr hr2).bound
  rw [hkernel] at h
  apply (div_le_iff₀ hD).2
  have he := mul_le_mul_of_nonneg_left henergy hD.le
  nlinarith only [h, he]

/-- The B penalty, including a possibly nonzero wall slack at c. -/
theorem right_auxiliary_penalty {p c : ℝ} (hp : 0 < p) (hpc : p < c)
    (hc : c < π / 2) {f B dB : ℝ → ℝ} {s E : ℝ}
    (hB : Continuous B)
    (hdB : ∀ t ∈ Ioo p c, HasDerivWithinAt B (dB t) (Ioi t) t)
    (htop : B (π / 2) = 0) (hleft : B p = -f p)
    (hright : B c = -f c - s)
    (hr : IntervalIntegrable (tangentResidual (π / 2) B dB) volume p c)
    (hr2 : IntervalIntegrable (fun t => tangentResidual (π / 2) B dB t ^ 2) volume p c)
    (henergy : arcSquare p c (tangentResidual (π / 2) B dB) ≤ E)
    (hD : 0 < tan c - tan p) :
    (f p / cos p - f c / cos c - s / cos c) ^ 2 / (tan c - tan p) ≤ E := by
  have hcos : ∀ t ∈ Icc p c, cos t ≠ 0 := fun t ht =>
    (cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2.trans_lt hc⟩).ne'
  have hs : ∀ t ∈ Icc p c, sin (π / 2 - t) ≠ 0 := by
    intro t ht
    simpa only [sin_pi_div_two_sub] using hcos t ht
  have hk : ContinuousOn (fun t => 1 / cos t) (Icc p c) :=
    continuousOn_const.div continuous_cos.continuousOn hcos
  have hi := residual_div_sin_integrable hpc.le hr hs
  have hFTC := tangent_quotient_integral hpc.le hB.continuousOn hdB hs hi
  simp only [tangentQuotient, htop, zero_mul, sub_zero,
    sin_pi_div_two_sub, hleft, hright] at hFTC
  have hweighted : (∫ t in p..c, (1 / cos t) * tangentResidual (π / 2) B dB t) =
      -(f p / cos p - f c / cos c - s / cos c) := by
    have hi' : (∫ t in p..c, tangentResidual (π / 2) B dB t / sin (π / 2 - t)) =
        ∫ t in p..c, (1 / cos t) * tangentResidual (π / 2) B dB t := by
      apply intervalIntegral.integral_congr
      intro t _
      rw [sin_pi_div_two_sub]
      ring
    rw [hi'] at hFTC
    rw [hFTC]
    ring
  have hn : (∫ t in p..c, (1 / cos t) ^ 2) = tan c - tan p :=
    secant_sq_integral hpc.le hcos
  have h := weighted_endpoint_penalty hpc.le hD hk hr hr2 hn henergy
  simpa only [hweighted, neg_sq] using h

/-- The D penalty. A positive wall slack at d enters with the PLUS sign. -/
theorem left_auxiliary_penalty {p d : ℝ} (hp : 0 < p)
    (hpd : p < π / 2) (hd : π / 2 < d) (hdT : d < π - p)
    {f D dD : ℝ → ℝ} {s E : ℝ}
    (hDcont : Continuous D)
    (hdD : ∀ t ∈ Ioo (π / 2) d, HasDerivWithinAt D (dD t) (Ioi t) t)
    (htop : D (π / 2) = 0) (hend : D (π - p) = -f (π - p))
    (hvalue : D d = -f d - s)
    (hr : IntervalIntegrable (tangentResidual (π - p) D dD) volume (π / 2) d)
    (hr2 : IntervalIntegrable (fun t => tangentResidual (π - p) D dD t ^ 2)
      volume (π / 2) d)
    (henergy : arcSquare (π / 2) d (tangentResidual (π - p) D dD) ≤ E)
    (hweight : 0 < cotangent (π - p - d) - tan p) :
    (f d / sin (π - p - d) - (cotangent (π - p - d) - tan p) * f (π - p) +
      s / sin (π - p - d)) ^ 2 / (cotangent (π - p - d) - tan p) ≤ E := by
  have hs : ∀ t ∈ Icc (π / 2) d, sin (π - p - t) ≠ 0 := by
    intro t ht
    exact (sin_pos_of_pos_of_lt_pi (by linarith [ht.2]) (by linarith [ht.1, pi_pos])).ne'
  have hk : ContinuousOn (fun t => 1 / sin (π - p - t)) (Icc (π / 2) d) :=
    continuousOn_const.div (by fun_prop) hs
  have hi := residual_div_sin_integrable hd.le hr hs
  have hFTC := tangent_quotient_integral hd.le hDcont.continuousOn hdD hs hi
  have he : cotangent (π - p - π / 2) = tan p := by
    simp only [cotangent, show π - p - π / 2 = π / 2 - p by ring,
      cos_pi_div_two_sub, sin_pi_div_two_sub, tan_eq_sin_div_cos]
  have hn : (∫ t in (π / 2)..d, (1 / sin (π - p - t)) ^ 2) =
      cotangent (π - p - d) - tan p := by
    rw [shifted_cosecant_sq_integral hd.le hs, he]
  have hweighted : (∫ t in (π / 2)..d,
      (1 / sin (π - p - t)) * tangentResidual (π - p) D dD t) =
      f d / sin (π - p - d) - (cotangent (π - p - d) - tan p) * f (π - p) +
        s / sin (π - p - d) := by
    have hi' : (∫ t in (π / 2)..d, tangentResidual (π - p) D dD t / sin (π - p - t)) =
        ∫ t in (π / 2)..d, (1 / sin (π - p - t)) * tangentResidual (π - p) D dD t := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    rw [hi'] at hFTC
    rw [hFTC]
    simp only [tangentQuotient, htop, hend, hvalue, zero_sub, neg_mul, sub_neg_eq_add]
    have he' : cos (π - p - π / 2) / sin (π - p - π / 2) = tan p := he
    unfold cotangent
    rw [← he']
    ring
  have h := weighted_endpoint_penalty hd.le hweight hk hr hr2 hn henergy
  simpa only [hweighted] using h

/-- Pure deficit bookkeeping after the two actual integral estimates have been
proved. Both auxiliary energies and the dual slack remain nonnegative. -/
theorem auxiliary_penalty_budget {Ec EB ED L Δ JB JD sB sD DB DD c z : ℝ}
    (hidentity : Δ = L + Ec + EB + ED) (hL : 0 ≤ L)
    (hB : (JB - sB / cos c) ^ 2 / DB ≤ 2 * EB)
    (hD : (JD + sD / sin z) ^ 2 / DD ≤ 2 * ED) :
    2 * Ec + (JB - sB / cos c) ^ 2 / DB + (JD + sD / sin z) ^ 2 / DD ≤ 2 * Δ := by
  linarith

end MovingSofaQuantitative
