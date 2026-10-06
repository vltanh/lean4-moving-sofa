module

public import MovingSofaQuantitative.CenteredKernel

/-!
# A scalar projection argument for centered coercivity

Uncompiled proof source. The theorem below is purely algebraic. It converts
an evaluation estimate valid after every multiple of one comparison profile
is subtracted into the corresponding centered estimate. Degenerate Gram
matrices are handled explicitly; no positive determinant is assumed.
-/

@[expose] public section
noncomputable section

open Real

namespace MovingSofaQuantitative

/-- Two-dimensional Cauchy--Schwarz from the whole comparison family.
Here `q` is the squared residual norm, `s` the squared comparison norm,
`y` the residual/comparison pairing, `c` the comparison evaluation, and `n`
the original squared evaluation norm. -/
theorem recentered_evaluation_sq {n s q x y c : ℝ}
    (hn : 0 ≤ n) (hs : 0 < s) (hq : 0 ≤ q)
    (hdet : c ^ 2 ≤ n * s) (hy : y ^ 2 ≤ s * q)
    (hfamily : ∀ a : ℝ, (x - a * c) ^ 2 ≤ n * (q - 2 * a * y + a ^ 2 * s))
    (b : ℝ) :
    (x - b * y) ^ 2 ≤ (n - 2 * b * c + b ^ 2 * s) * q := by
  let d := n * s - c ^ 2
  let N := n - 2 * b * c + b ^ 2 * s
  have hd : 0 ≤ d := sub_nonneg.mpr hdet
  have hN : 0 ≤ N := by
    have he : s * N = (c - b * s) ^ 2 + d := by dsimp [N, d]; ring
    nlinarith only [sq_nonneg (c - b * s), hd, he, hs]
  have hzero := hfamily 0
  simp only [zero_mul, sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add,
    add_zero] at hzero
  by_cases hnzero : n = 0
  · have hc : c = 0 := by nlinarith only [hdet, hnzero, sq_nonneg c]
    have hx : x = 0 := by nlinarith only [hzero, hnzero, sq_nonneg x]
    have hh := mul_le_mul_of_nonneg_left hy (sq_nonneg b)
    simpa only [hnzero, hc, hx, mul_zero, zero_sub, zero_add, neg_sq, mul_pow,
      mul_assoc] using hh
  have hnpos : 0 < n := lt_of_le_of_ne hn (Ne.symm hnzero)
  have hpoly : ∀ a : ℝ,
      0 ≤ d * (a * a) + (2 * (x * c - n * y)) * a + (n * q - x ^ 2) := by
    intro a
    have ha := hfamily a
    dsimp [d]
    nlinarith only [ha]
  have hdisc := discrim_le_zero hpoly
  rw [discrim] at hdisc
  have hgram : (x * c - n * y) ^ 2 ≤ d * (n * q - x ^ 2) := by
    nlinarith only [hdisc]
  rcases hd.eq_or_lt with hd0 | hdpos
  · have hd0' : d = 0 := hd0.symm
    have hcross : n * y - c * x = 0 := by
      rw [hd0', zero_mul] at hgram
      nlinarith only [hgram, sq_nonneg (n * y - c * x)]
    have hprod : 0 ≤ n * N * (n * q - x ^ 2) :=
      mul_nonneg (mul_nonneg hn hN) (sub_nonneg.mpr hzero)
    have he : n ^ 2 * (N * q - (x - b * y) ^ 2) =
        n * N * (n * q - x ^ 2) + b ^ 2 * d * x ^ 2 +
          (n * y - c * x) * (2 * b * n * x - b ^ 2 * (n * y + c * x)) := by
      dsimp [N, d]
      ring
    rw [hd0', hcross] at he
    have hn2 : 0 < n ^ 2 := sq_pos_of_pos hnpos
    change (x - b * y) ^ 2 ≤ N * q
    nlinarith only [he, hprod, hn2]
  · have hdual : s * x ^ 2 - 2 * c * x * y + n * y ^ 2 ≤ d * q := by
      have he : d * (n * q - x ^ 2) - (x * c - n * y) ^ 2 =
          n * (d * q - (s * x ^ 2 - 2 * c * x * y + n * y ^ 2)) := by
        dsimp [d]
        ring
      nlinarith only [hgram, he, hnpos]
    have hmul := mul_le_mul_of_nonneg_left hdual hN
    have he : N * (s * x ^ 2 - 2 * c * x * y + n * y ^ 2) -
        d * (x - b * y) ^ 2 = ((c - b * s) * x - (n - b * c) * y) ^ 2 := by
      dsimp [N, d]
      ring
    change (x - b * y) ^ 2 ≤ N * q
    nlinarith only [hmul, he, sq_nonneg ((c - b * s) * x - (n - b * c) * y), hdpos]

/-- Specialization to the centered Green profiles. The inputs are the actual
comparison-family inequality and norm/pairing identities; no integral bound
for the centered evaluation is assumed. -/
theorem centered_evaluation_of_comparison {φ t E x y : ℝ}
    (hφ : φ ∈ Set.Ioo 0 (π / 4)) (hE : 0 ≤ E)
    (hn : 0 ≤ MovingSofaStability.greenNormSquared φ t)
    (hdet : greenCovariance φ t ^ 2 ≤
      MovingSofaStability.greenNormSquared φ t * (2 * (1 / cos φ) ^ 2))
    (hy : y ^ 2 ≤ (2 * (1 / cos φ) ^ 2) * (2 * E))
    (hfam : ∀ a : ℝ, (x - a * greenCovariance φ t) ^ 2 ≤
      MovingSofaStability.greenNormSquared φ t *
        (2 * E - 2 * a * y + a ^ 2 * (2 * (1 / cos φ) ^ 2))) :
    |x - (y / 2) * cos t| ≤ (1 / cos φ) * sqrt E := by
  have hc := (MovingSofaStability.cap_angle_parameters hφ).1
  have hs : 0 < 2 * (1 / cos φ) ^ 2 := by positivity
  have hsq := recentered_evaluation_sq hn hs (mul_nonneg (by norm_num) hE)
    hdet hy hfam (cos t / 2)
  have he : MovingSofaStability.greenNormSquared φ t -
      2 * (cos t / 2) * greenCovariance φ t +
      (cos t / 2) ^ 2 * (2 * (1 / cos φ) ^ 2) = centeredGreenSquare φ t := by
    rw [centeredGreenSquare_identity]
    ring
  rw [he] at hsq
  have hupper := mul_le_mul_of_nonneg_right (centeredGreenSquare_le hφ t)
    (mul_nonneg (by norm_num) hE)
  apply MovingSofaStability.abs_le_mul_sqrt_of_sq_le (by positivity)
  nlinarith only [hsq, hupper]

end MovingSofaQuantitative
