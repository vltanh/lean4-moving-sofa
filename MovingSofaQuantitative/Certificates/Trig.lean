module

public import MovingSofaQuantitative.Certificates.Interval
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Exact rational Taylor enclosures for real trigonometry

Uncompiled proof source. The rational generator computes powers of i*q as
pairs of rationals. The error comes from Mathlib's complex exponential series
bound, not from a decimal oracle. A Lipschitz estimate enlarges a point enclosure
to the complete input interval. No floating-point test decides acceptance.
-/

@[expose] public section

open scoped BigOperators

namespace MovingSofaQuantitative.Certificates

def imaginaryPower (q : ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | n + 1 => (-q * (imaginaryPower q n).2, q * (imaginaryPower q n).1)

def complexOfPair (z : ℚ × ℚ) : ℂ := ⟨(z.1 : ℝ), (z.2 : ℝ)⟩

theorem imaginaryPower_correct (q : ℚ) (n : ℕ) :
    complexOfPair (imaginaryPower q n) = ((q : ℂ) * Complex.I) ^ n := by
  induction n with
  | zero => simp [imaginaryPower, complexOfPair]
  | succ n ih =>
      rw [pow_succ, ← ih]
      apply Complex.ext <;>
        simp [imaginaryPower, complexOfPair, Complex.mul_re, Complex.mul_im] <;> ring

def trigPolynomial (q : ℚ) (n : ℕ) : ℚ × ℚ :=
  (∑ k ∈ Finset.range n, (imaginaryPower q k).1 / (k.factorial : ℚ),
   ∑ k ∈ Finset.range n, (imaginaryPower q k).2 / (k.factorial : ℚ))

theorem trigPolynomial_correct (q : ℚ) (n : ℕ) :
    complexOfPair (trigPolynomial q n) =
      ∑ k ∈ Finset.range n, ((q : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) := by
  simp_rw [← imaginaryPower_correct]
  apply Complex.ext <;>
    simp [trigPolynomial, complexOfPair, Complex.div_re, Complex.div_im]

def trigRemainder (q : ℚ) (n : ℕ) : ℚ :=
  2 * |q| ^ n / (n.factorial : ℚ)

/-- Both Taylor errors are enclosed by the same exact rational remainder. -/
theorem trigPolynomial_error {q : ℚ} {n : ℕ}
    (hsmall : |q| / (n + 1 : ℚ) ≤ 1 / 2) :
    |Real.cos (q : ℝ) - ((trigPolynomial q n).1 : ℝ)| ≤ (trigRemainder q n : ℝ) ∧
    |Real.sin (q : ℝ) - ((trigPolynomial q n).2 : ℝ)| ≤ (trigRemainder q n : ℝ) := by
  have hnorm : ‖(q : ℂ) * Complex.I‖ = |(q : ℝ)| := by
    rw [norm_mul, Complex.norm_I, mul_one]
    simp
  have hratio : ‖(q : ℂ) * Complex.I‖ / (n + 1 : ℝ) ≤ 1 / 2 := by
    rw [hnorm]
    exact_mod_cast hsmall
  have h := Complex.exp_bound' (x := (q : ℂ) * Complex.I) (n := n) hratio
  rw [← trigPolynomial_correct, hnorm] at h
  have hreal := (Complex.abs_re_le_norm (Complex.exp ((q : ℂ) * Complex.I) -
    complexOfPair (trigPolynomial q n))).trans h
  have himag := (Complex.abs_im_le_norm (Complex.exp ((q : ℂ) * Complex.I) -
    complexOfPair (trigPolynomial q n))).trans h
  have hr : |(q : ℝ)| ^ n / (n.factorial : ℝ) * 2 = (trigRemainder q n : ℝ) := by
    simp only [trigRemainder, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_abs,
      Rat.cast_ofNat, Rat.cast_natCast]
    ring
  constructor
  · simpa [Complex.exp_ofReal_mul_I, complexOfPair, hr] using hreal
  · simpa [Complex.exp_ofReal_mul_I, complexOfPair, hr] using himag

namespace Interval

def midpoint (I : Interval) : ℚ := (I.lo + I.hi) / 2

def radius (I : Interval) : ℚ := (I.hi - I.lo) / 2

theorem abs_sub_midpoint_le {I : Interval} {x : ℝ} (hx : I.Contains x) :
    |x - (I.midpoint : ℝ)| ≤ (I.radius : ℝ) := by
  apply abs_le.mpr
  dsimp [midpoint, radius]
  push_cast
  constructor <;> linarith [hx.1, hx.2]

/-- Sixty-four terms suffice for every angle in the parameter boxes. Failure
of the rational precondition produces `none`, never a guessed enclosure. -/
def sin (I : Interval) : Option Interval :=
  let q := I.midpoint
  if I.lo ≤ I.hi ∧ |q| / 65 ≤ 1 / 2 then
    let c := (trigPolynomial q 64).2
    let e := trigRemainder q 64 + I.radius
    some ⟨c - e, c + e⟩
  else none

def cos (I : Interval) : Option Interval :=
  let q := I.midpoint
  if I.lo ≤ I.hi ∧ |q| / 65 ≤ 1 / 2 then
    let c := (trigPolynomial q 64).1
    let e := trigRemainder q 64 + I.radius
    some ⟨c - e, c + e⟩
  else none

theorem contains_sin {I J : Interval} {x : ℝ} (hx : I.Contains x)
    (hJ : I.sin = some J) : J.Contains (Real.sin x) := by
  unfold sin at hJ
  split_ifs at hJ with hguard
  · cases Option.some.inj hJ
    have hpoint := (trigPolynomial_error (n := 64) hguard.2).2
    have hchange := (Real.abs_sin_sub_sin_le x (I.midpoint : ℝ)).trans (abs_sub_midpoint_le hx)
    have htotal := (abs_sub_le (Real.sin x) (Real.sin (I.midpoint : ℝ))
      ((trigPolynomial I.midpoint 64).2 : ℝ)).trans (add_le_add hchange hpoint)
    have hbounds := abs_le.mp htotal
    change (((trigPolynomial I.midpoint 64).2 - (trigRemainder I.midpoint 64 + I.radius) : ℚ) : ℝ)
        ≤ Real.sin x ∧ Real.sin x ≤
      (((trigPolynomial I.midpoint 64).2 + (trigRemainder I.midpoint 64 + I.radius) : ℚ) : ℝ)
    push_cast
    constructor <;> linarith [hbounds.1, hbounds.2]
  · cases hJ

theorem contains_cos {I J : Interval} {x : ℝ} (hx : I.Contains x)
    (hJ : I.cos = some J) : J.Contains (Real.cos x) := by
  unfold cos at hJ
  split_ifs at hJ with hguard
  · cases Option.some.inj hJ
    have hpoint := (trigPolynomial_error (n := 64) hguard.2).1
    have hchange := (Real.abs_cos_sub_cos_le x (I.midpoint : ℝ)).trans (abs_sub_midpoint_le hx)
    have htotal := (abs_sub_le (Real.cos x) (Real.cos (I.midpoint : ℝ))
      ((trigPolynomial I.midpoint 64).1 : ℝ)).trans (add_le_add hchange hpoint)
    have hbounds := abs_le.mp htotal
    change (((trigPolynomial I.midpoint 64).1 - (trigRemainder I.midpoint 64 + I.radius) : ℚ) : ℝ)
        ≤ Real.cos x ∧ Real.cos x ≤
      (((trigPolynomial I.midpoint 64).1 + (trigRemainder I.midpoint 64 + I.radius) : ℚ) : ℝ)
    push_cast
    constructor <;> linarith [hbounds.1, hbounds.2]
  · cases hJ

/-- A fixed rational enclosure whose correctness comes from Mathlib's proof. -/
def piInterval : Interval :=
  ⟨314159265358979323846 / 100000000000000000000,
   314159265358979323847 / 100000000000000000000⟩

theorem contains_pi : piInterval.Contains Real.pi := by
  constructor
  · exact le_of_lt (by simpa [piInterval] using Real.pi_gt_d20)
  · exact le_of_lt (by simpa [piInterval] using Real.pi_lt_d20)

end Interval
end MovingSofaQuantitative.Certificates
