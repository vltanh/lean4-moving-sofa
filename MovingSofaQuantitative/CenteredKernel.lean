module

public import MovingSofaStability.CapEstimate

/-!
# Centered Green profiles and the square-integral argument

Proof source, not yet compiled in this session.

This module proves the six scalar profile identities and the measure-theoretic
Cauchy--Schwarz implication. The application to the actual four-arc residual
operator additionally requires its kernel-square and covariance integral
identities. Those hypotheses are explicit below; this file must NOT be cited
as a completed centered-cap theorem before that application is proved.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter
open MovingSofaStability

namespace MovingSofaQuantitative

/-- The proposed covariance of the evaluation kernel at t with that at zero. -/
def greenCovariance (φ t : ℝ) : ℝ :=
  let A := 1 / cos φ
  if t ≤ φ then 2 * A ^ 2 * cos t - sin t
  else if t ≤ π / 2 - φ then A + A ^ 2 * cos t - sin t
  else if t ≤ π / 2 then (A ^ 2 + A * sin φ) * cos t
  else if t ≤ π / 2 + φ then A * (A - sin φ) * cos t
  else if t ≤ π - φ then A + A ^ 2 * cos t - sin t
  else -sin t

/-- The squared centered evaluation profile. -/
def centeredGreenSquare (φ t : ℝ) : ℝ :=
  let A := 1 / cos φ
  let B := A * sin φ - A ^ 2 / 2
  if t ≤ φ then (A ^ 2 / 2) * cos t ^ 2
  else if t ≤ π / 2 - φ then A * cos t - (A ^ 2 / 2) * cos t ^ 2
  else if t ≤ π / 2 then sin t * cos t + B * cos t ^ 2
  else if t ≤ π / 2 + φ then -sin t * cos t + B * cos t ^ 2
  else if t ≤ π - φ then -A * cos t - (A ^ 2 / 2) * cos t ^ 2
  else (A ^ 2 / 2) * cos t ^ 2

private theorem cos_sq_mul_tan (t : ℝ) : cos t ^ 2 * tan t = sin t * cos t := by
  by_cases hc : cos t = 0
  · simp [hc]
  · rw [tan_eq_sin_div_cos]
    field_simp [hc]
    ring

/-- The polarization identity for the six explicit scalar profiles. This is
algebra, not a substitute for verifying the actual kernel covariance. -/
theorem centeredGreenSquare_identity (φ t : ℝ) :
    centeredGreenSquare φ t = greenNormSquared φ t - cos t * greenCovariance φ t +
      ((1 / cos φ) ^ 2 / 2) * cos t ^ 2 := by
  have ht := cos_sq_mul_tan t
  have hφ : tan φ = (1 / cos φ) * sin φ := by rw [tan_eq_sin_div_cos]; ring
  by_cases h1 : t ≤ φ
  · simp only [centeredGreenSquare, greenNormSquared, greenCovariance, if_pos h1]
    nlinarith only [ht]
  by_cases h2 : t ≤ π / 2 - φ
  · simp only [centeredGreenSquare, greenNormSquared, greenCovariance, if_neg h1, if_pos h2]
    ring
  by_cases h3 : t ≤ π / 2
  · simp only [centeredGreenSquare, greenNormSquared, greenCovariance, if_neg h1,
      if_neg h2, if_pos h3, hφ]
    ring
  by_cases h4 : t ≤ π / 2 + φ
  · simp only [centeredGreenSquare, greenNormSquared, greenCovariance, if_neg h1,
      if_neg h2, if_neg h3, if_pos h4]
    ring
  by_cases h5 : t ≤ π - φ
  · simp only [centeredGreenSquare, greenNormSquared, greenCovariance, if_neg h1,
      if_neg h2, if_neg h3, if_neg h4, if_pos h5]
    ring
  · simp only [centeredGreenSquare, greenNormSquared, greenCovariance, if_neg h1,
      if_neg h2, if_neg h3, if_neg h4, if_neg h5]
    ring

/-- The coefficient on the short arcs is nonpositive. -/
theorem centered_short_coefficient_nonpos {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    (1 / cos φ) * sin φ - (1 / cos φ) ^ 2 / 2 ≤ 0 := by
  obtain ⟨_, _, _, hsec⟩ := cap_angle_parameters hφ
  have ht : tan φ = (1 / cos φ) * sin φ := by rw [tan_eq_sin_div_cos]; ring
  have hsq := sq_nonneg (tan φ - 1)
  rw [hsec, ← ht]
  nlinarith

/-- The centered scalar profile has maximum at most sec(phi)^2/2.
The estimate includes all six branches and both horizontal endpoints. -/
theorem centeredGreenSquare_le {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) (t : ℝ) :
    centeredGreenSquare φ t ≤ (1 / cos φ) ^ 2 / 2 := by
  let A := 1 / cos φ
  have hsec := (cap_angle_parameters hφ).2.2.2
  have hA2 : 1 ≤ A ^ 2 := by dsimp [A]; nlinarith [sq_nonneg (tan φ)]
  have hcos : cos t ^ 2 ≤ 1 := by nlinarith [sin_sq_add_cos_sq t, sq_nonneg (sin t)]
  have hp : sin t * cos t ≤ (1 / 2 : ℝ) := by
    nlinarith [sin_sq_add_cos_sq t, sq_nonneg (sin t - cos t)]
  have hm : -(1 / 2 : ℝ) ≤ sin t * cos t := by
    nlinarith [sin_sq_add_cos_sq t, sq_nonneg (sin t + cos t)]
  have hB := centered_short_coefficient_nonpos hφ
  have hBc := mul_nonpos_of_nonpos_of_nonneg hB (sq_nonneg (cos t))
  have hAc := mul_nonneg (sq_nonneg A) (sub_nonneg.mpr hcos)
  change centeredGreenSquare φ t ≤ A ^ 2 / 2
  unfold centeredGreenSquare
  change (if t ≤ φ then (A ^ 2 / 2) * cos t ^ 2
    else if t ≤ π / 2 - φ then A * cos t - (A ^ 2 / 2) * cos t ^ 2
    else if t ≤ π / 2 then sin t * cos t + (A * sin φ - A ^ 2 / 2) * cos t ^ 2
    else if t ≤ π / 2 + φ then -sin t * cos t + (A * sin φ - A ^ 2 / 2) * cos t ^ 2
    else if t ≤ π - φ then -A * cos t - (A ^ 2 / 2) * cos t ^ 2
    else (A ^ 2 / 2) * cos t ^ 2) ≤ A ^ 2 / 2
  change (A * sin φ - A ^ 2 / 2) * cos t ^ 2 ≤ 0 at hBc
  split_ifs
  · nlinarith only [hAc]
  · nlinarith [sq_nonneg (A * cos t - 1)]
  · nlinarith only [hp, hBc, hA2]
  · nlinarith only [hm, hBc, hA2]
  · nlinarith [sq_nonneg (A * cos t + 1)]
  · nlinarith only [hAc]

section Integral

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) {k k₀ r : X → ℝ}

/-- Integrability and exact expansion of a centered square. -/
theorem centered_square_integral (a : ℝ)
    (hk : Integrable (fun x => k x ^ 2) μ)
    (h₀ : Integrable (fun x => k₀ x ^ 2) μ)
    (hk₀ : Integrable (fun x => k x * k₀ x) μ) :
    Integrable (fun x => (k x - a * k₀ x) ^ 2) μ ∧
      (∫ x, (k x - a * k₀ x) ^ 2 ∂μ) =
        (∫ x, k x ^ 2 ∂μ) - 2 * a * (∫ x, k x * k₀ x ∂μ) +
          a ^ 2 * (∫ x, k₀ x ^ 2 ∂μ) := by
  have hpoly : Integrable (fun x => k x ^ 2 - (2 * a) * (k x * k₀ x) + a ^ 2 * k₀ x ^ 2) μ :=
    (hk.sub (hk₀.const_mul _)).add (h₀.const_mul _)
  have he : ∀ x, k x ^ 2 - (2 * a) * (k x * k₀ x) + a ^ 2 * k₀ x ^ 2 =
      (k x - a * k₀ x) ^ 2 := fun x => by ring
  refine ⟨hpoly.congr (Eventually.of_forall he), ?_⟩
  calc
    _ = ∫ x, k x ^ 2 - (2 * a) * (k x * k₀ x) + a ^ 2 * k₀ x ^ 2 ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x => (he x).symm)
    _ = _ := by
      rw [integral_add (hk.sub (hk₀.const_mul _)) (h₀.const_mul _),
        integral_sub hk (hk₀.const_mul _), integral_const_mul, integral_const_mul]

/-- Cauchy--Schwarz after centering, assuming the three ACTUAL Gram integrals
have been identified. This is the interface the four-arc kernel construction
must instantiate; no cap or Q-deficit conclusion is hidden in the hypotheses. -/
theorem centered_kernel_integral_bound {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (hk : Integrable (fun x => k x ^ 2) μ)
    (h₀ : Integrable (fun x => k₀ x ^ 2) μ)
    (hk₀ : Integrable (fun x => k x * k₀ x) μ)
    (hr : Integrable (fun x => r x ^ 2) μ)
    (hkr : Integrable (fun x => k x * r x) μ)
    (h₀r : Integrable (fun x => k₀ x * r x) μ)
    (hknorm : (∫ x, k x ^ 2 ∂μ) = greenNormSquared φ t)
    (h₀norm : (∫ x, k₀ x ^ 2 ∂μ) = 2 * (1 / cos φ) ^ 2)
    (hcov : (∫ x, k x * k₀ x ∂μ) = greenCovariance φ t) :
    |(∫ x, k x * r x ∂μ) - (cos t / 2) * (∫ x, k₀ x * r x ∂μ)| ≤
      (1 / cos φ) * sqrt ((∫ x, r x ^ 2 ∂μ) / 2) := by
  let a := cos t / 2
  obtain ⟨hcenter, hexpand⟩ := centered_square_integral μ a hk h₀ hk₀
  have hcenterR : Integrable (fun x => (k x - a * k₀ x) * r x) μ :=
    (hkr.sub (h₀r.const_mul a)).congr (Eventually.of_forall fun x => by ring)
  have heval : (∫ x, (k x - a * k₀ x) * r x ∂μ) =
      (∫ x, k x * r x ∂μ) - a * (∫ x, k₀ x * r x ∂μ) := by
    calc
      _ = ∫ x, k x * r x - a * (k₀ x * r x) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun x => by ring)
      _ = _ := by rw [integral_sub hkr (h₀r.const_mul a), integral_const_mul]
  have hnorm : (∫ x, (k x - a * k₀ x) ^ 2 ∂μ) = centeredGreenSquare φ t := by
    rw [hexpand, hknorm, h₀norm, hcov, centeredGreenSquare_identity]
    dsimp [a]
    ring
  have hsq := integral_mul_sq_le μ hcenter hr hcenterR
  rw [heval, hnorm] at hsq
  have henergy : 0 ≤ ∫ x, r x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hupper := mul_le_mul_of_nonneg_right (centeredGreenSquare_le hφ t) henergy
  apply abs_le_mul_sqrt_of_sq_le (one_div_nonneg.mpr (cap_angle_parameters hφ).1.le)
  change ((∫ x, k x * r x ∂μ) - a * (∫ x, k₀ x * r x ∂μ)) ^ 2 ≤ _
  nlinarith only [hsq, hupper]

end Integral

/-- The centered scalar coefficient has the desired rational source-box bound. -/
theorem sec_phi_rational_bound {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) :
    1 / cos φ ≤ 1250 / 1249 ∧ (1250 / 1249 : ℝ) < 1001 / 1000 := by
  have h := (cap_constant_lt_2002 hφ).1
  have he : 2 / cos φ = 2 * (1 / cos φ) := by ring
  rw [he] at h
  constructor
  · linarith
  · norm_num

end MovingSofaQuantitative
