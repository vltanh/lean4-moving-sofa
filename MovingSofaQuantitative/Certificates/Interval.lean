module

public import Mathlib

/-!
# Rational interval arithmetic with real semantics

Uncompiled proof source. Bounds are exact rationals. An interval containing
zero cannot be inverted. A malformed interval denotes the empty set and cannot
make an arbitrary real value pass: every soundness theorem requires membership.
This layer contains no numerical oracle, axiom, or native evaluator shortcut.
-/

@[expose] public section

namespace MovingSofaQuantitative.Certificates

structure Interval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

namespace Interval

/-- Real meaning of a rational enclosure. -/
def Contains (I : Interval) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def point (q : ℚ) : Interval := ⟨q, q⟩
def neg (I : Interval) : Interval := ⟨-I.hi, -I.lo⟩
def add (I J : Interval) : Interval := ⟨I.lo + J.lo, I.hi + J.hi⟩
def sub (I J : Interval) : Interval := I.add J.neg

def mul (I J : Interval) : Interval :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
    max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩

def reciprocal (I : Interval) : Option Interval :=
  if 0 < I.lo ∨ I.hi < 0 then some ⟨1 / I.hi, 1 / I.lo⟩ else none

def divide (I J : Interval) : Option Interval := do
  let R ← J.reciprocal
  return I.mul R

def powNat (I : Interval) : ℕ → Interval
  | 0 => point 1
  | n + 1 => (I.powNat n).mul I

@[simp] theorem contains_point (q : ℚ) : (point q).Contains (q : ℝ) := ⟨le_rfl, le_rfl⟩

theorem contains_neg {I : Interval} {x : ℝ} (hx : I.Contains x) : I.neg.Contains (-x) := by
  change ((-I.hi : ℚ) : ℝ) ≤ -x ∧ -x ≤ ((-I.lo : ℚ) : ℝ)
  push_cast
  exact ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

theorem contains_add {I J : Interval} {x y : ℝ} (hx : I.Contains x) (hy : J.Contains y) :
    (I.add J).Contains (x + y) := by
  change ((I.lo + J.lo : ℚ) : ℝ) ≤ x + y ∧ x + y ≤ ((I.hi + J.hi : ℚ) : ℝ)
  push_cast
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem contains_sub {I J : Interval} {x y : ℝ} (hx : I.Contains x) (hy : J.Contains y) :
    (I.sub J).Contains (x - y) := by
  simpa only [sub_eq_add_neg] using contains_add hx (contains_neg hy)

private theorem product_upper {a b c d x y U : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hac : a * c ≤ U) (had : a * d ≤ U) (hbc : b * c ≤ U) (hbd : b * d ≤ U) :
    x * y ≤ U := by
  rcases le_total 0 y with hpos | hneg
  · have hb := mul_le_mul_of_nonneg_right hx.2 hpos
    rcases le_total 0 b with hbpos | hbneg
    · exact hb.trans ((mul_le_mul_of_nonneg_left hy.2 hbpos).trans hbd)
    · exact hb.trans ((mul_le_mul_of_nonpos_left hy.1 hbneg).trans hbc)
  · have ha := mul_le_mul_of_nonpos_right hx.1 hneg
    rcases le_total 0 a with hapos | haneg
    · exact ha.trans ((mul_le_mul_of_nonneg_left hy.2 hapos).trans had)
    · exact ha.trans ((mul_le_mul_of_nonpos_left hy.1 haneg).trans hac)

private theorem product_lower {a b c d x y L : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hac : L ≤ a * c) (had : L ≤ a * d) (hbc : L ≤ b * c) (hbd : L ≤ b * d) :
    L ≤ x * y := by
  rcases le_total 0 y with hpos | hneg
  · have ha := mul_le_mul_of_nonneg_right hx.1 hpos
    rcases le_total 0 a with hapos | haneg
    · exact (hac.trans (mul_le_mul_of_nonneg_left hy.1 hapos)).trans ha
    · exact (had.trans (mul_le_mul_of_nonpos_left hy.2 haneg)).trans ha
  · have hb := mul_le_mul_of_nonpos_right hx.2 hneg
    rcases le_total 0 b with hbpos | hbneg
    · exact (hbc.trans (mul_le_mul_of_nonneg_left hy.1 hbpos)).trans hb
    · exact (hbd.trans (mul_le_mul_of_nonpos_left hy.2 hbneg)).trans hb

theorem contains_mul {I J : Interval} {x y : ℝ} (hx : I.Contains x) (hy : J.Contains y) :
    (I.mul J).Contains (x * y) := by
  constructor
  · apply product_lower hx hy
    · exact_mod_cast (min_le_left (min (I.lo * J.lo) (I.lo * J.hi))
        (min (I.hi * J.lo) (I.hi * J.hi))).trans (min_le_left _ _)
    · exact_mod_cast (min_le_left (min (I.lo * J.lo) (I.lo * J.hi))
        (min (I.hi * J.lo) (I.hi * J.hi))).trans (min_le_right _ _)
    · exact_mod_cast (min_le_right (min (I.lo * J.lo) (I.lo * J.hi))
        (min (I.hi * J.lo) (I.hi * J.hi))).trans (min_le_left _ _)
    · exact_mod_cast (min_le_right (min (I.lo * J.lo) (I.lo * J.hi))
        (min (I.hi * J.lo) (I.hi * J.hi))).trans (min_le_right _ _)
  · apply product_upper hx hy
    · exact_mod_cast (le_max_left (I.lo * J.lo) (I.lo * J.hi)).trans
        (le_max_left (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi)))
    · exact_mod_cast (le_max_right (I.lo * J.lo) (I.lo * J.hi)).trans
        (le_max_left (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi)))
    · exact_mod_cast (le_max_left (I.hi * J.lo) (I.hi * J.hi)).trans
        (le_max_right (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi)))
    · exact_mod_cast (le_max_right (I.hi * J.lo) (I.hi * J.hi)).trans
        (le_max_right (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi)))

/-- A denominator enclosure must lie strictly in one half-line. -/
theorem contains_reciprocal {I R : Interval} {x : ℝ}
    (hx : I.Contains x) (hR : I.reciprocal = some R) : R.Contains (1 / x) := by
  unfold reciprocal at hR
  split_ifs at hR with hsign
  · cases Option.some.inj hR
    change ((1 / I.hi : ℚ) : ℝ) ≤ 1 / x ∧ 1 / x ≤ ((1 / I.lo : ℚ) : ℝ)
    push_cast
    rcases hsign with hpos | hneg
    · have hl : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hpos
      have hxp : 0 < x := hl.trans_le hx.1
      exact ⟨one_div_le_one_div_of_le hxp hx.2, one_div_le_one_div_of_le hl hx.1⟩
    · have hh : (I.hi : ℝ) < 0 := by exact_mod_cast hneg
      have hxn : x < 0 := hx.2.trans_lt hh
      have h1 := one_div_le_one_div_of_le (neg_pos.mpr hh) (neg_le_neg hx.2)
      have h2 := one_div_le_one_div_of_le (neg_pos.mpr hxn) (neg_le_neg hx.1)
      simp only [one_div_neg] at h1 h2
      constructor <;> linarith
  · cases hR

theorem reciprocal_nonzero {I R : Interval} {x : ℝ}
    (hx : I.Contains x) (hR : I.reciprocal = some R) : x ≠ 0 := by
  unfold reciprocal at hR
  split_ifs at hR with hsign
  · rcases hsign with hpos | hneg
    · have hp : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hpos
      exact ne_of_gt (hp.trans_le hx.1)
    · have hn : (I.hi : ℝ) < 0 := by exact_mod_cast hneg
      exact ne_of_lt (hx.2.trans_lt hn)
  · cases hR

theorem contains_divide {I J R : Interval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) (hR : I.divide J = some R) :
    R.Contains (x / y) := by
  unfold divide at hR
  cases he : J.reciprocal with
  | none => simp [he] at hR
  | some J' =>
      simp only [he, Option.bind_some, Option.some.injEq] at hR
      subst R
      simpa only [div_eq_mul_inv, one_div] using contains_mul hx (contains_reciprocal hy he)

theorem contains_powNat {I : Interval} {x : ℝ} (hx : I.Contains x) (n : ℕ) :
    (I.powNat n).Contains (x ^ n) := by
  induction n with
  | zero => simpa [powNat] using contains_point 1
  | succ n ih => simpa only [powNat, pow_succ] using contains_mul ih hx

/-- A successful rational upper-endpoint test proves a real inequality. -/
theorem le_of_upper {I : Interval} {x : ℝ} {q : ℚ} (hx : I.Contains x) (h : I.hi ≤ q) :
    x ≤ (q : ℝ) := hx.2.trans (by exact_mod_cast h)

theorem lt_of_upper {I : Interval} {x : ℝ} {q : ℚ} (hx : I.Contains x) (h : I.hi < q) :
    x < (q : ℝ) := hx.2.trans_lt (by exact_mod_cast h)

end Interval
end MovingSofaQuantitative.Certificates
