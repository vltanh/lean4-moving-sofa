module

public import MovingSofaQuantitative.Certificates.Trig
public import MovingSofaQuantitative.Certificates.Cover

/-!
# Trigonometric expressions for continuum certificates

Uncompiled proof source. The evaluator encloses every real point of its input
box. Min/max and absolute values have semantics; they are not replaced by a
branch chosen at a sample point. A reciprocal whose interval straddles zero
still fails. This file is infrastructure, not the instantiated .93 certificate.
-/

@[expose] public section

namespace MovingSofaQuantitative.Certificates

namespace Interval

def hull (I J : Interval) : Interval := ⟨min I.lo J.lo, max I.hi J.hi⟩
def minimum (I J : Interval) : Interval := ⟨min I.lo J.lo, min I.hi J.hi⟩
def maximum (I J : Interval) : Interval := ⟨max I.lo J.lo, max I.hi J.hi⟩
def absolute (I : Interval) : Interval :=
  ⟨max 0 (max I.lo (-I.hi)), max (-I.lo) I.hi⟩

theorem contains_hull_left {I J : Interval} {x : ℝ} (hx : I.Contains x) :
    (I.hull J).Contains x := by
  constructor
  · exact (by exact_mod_cast min_le_left I.lo J.lo).trans hx.1
  · exact hx.2.trans (by exact_mod_cast le_max_left I.hi J.hi)

theorem contains_hull_right {I J : Interval} {x : ℝ} (hx : J.Contains x) :
    (I.hull J).Contains x := by
  constructor
  · exact (by exact_mod_cast min_le_right I.lo J.lo).trans hx.1
  · exact hx.2.trans (by exact_mod_cast le_max_right I.hi J.hi)

theorem contains_minimum {I J : Interval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.minimum J).Contains (min x y) := by
  change ((min I.lo J.lo : ℚ) : ℝ) ≤ min x y ∧ min x y ≤ ((min I.hi J.hi : ℚ) : ℝ)
  push_cast
  exact ⟨min_le_min hx.1 hy.1, min_le_min hx.2 hy.2⟩

theorem contains_maximum {I J : Interval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.maximum J).Contains (max x y) := by
  change ((max I.lo J.lo : ℚ) : ℝ) ≤ max x y ∧ max x y ≤ ((max I.hi J.hi : ℚ) : ℝ)
  push_cast
  exact ⟨max_le_max hx.1 hy.1, max_le_max hx.2 hy.2⟩

theorem contains_absolute {I : Interval} {x : ℝ} (hx : I.Contains x) :
    I.absolute.Contains |x| := by
  change ((max 0 (max I.lo (-I.hi)) : ℚ) : ℝ) ≤ |x| ∧
    |x| ≤ ((max (-I.lo) I.hi : ℚ) : ℝ)
  push_cast
  constructor
  · exact max_le (abs_nonneg x) (max_le (hx.1.trans (le_abs_self x))
      ((neg_le_neg hx.2).trans (neg_le_abs x)))
  · rw [abs_le]
    constructor
    · have h := le_max_left (-(I.lo : ℝ)) (I.hi : ℝ)
      linarith [hx.1]
    · exact hx.2.trans (le_max_right _ _)

end Interval

inductive TrigExpr (n : ℕ) where
  | rational : ℚ → TrigExpr n
  | variable : Fin n → TrigExpr n
  | pi : TrigExpr n
  | neg : TrigExpr n → TrigExpr n
  | add : TrigExpr n → TrigExpr n → TrigExpr n
  | mul : TrigExpr n → TrigExpr n → TrigExpr n
  | inv : TrigExpr n → TrigExpr n
  | pow : TrigExpr n → ℕ → TrigExpr n
  | sin : TrigExpr n → TrigExpr n
  | cos : TrigExpr n → TrigExpr n
  | abs : TrigExpr n → TrigExpr n
  | min : TrigExpr n → TrigExpr n → TrigExpr n
  | max : TrigExpr n → TrigExpr n → TrigExpr n
  deriving Repr, DecidableEq

namespace TrigExpr

variable {n : ℕ}

noncomputable def realValue (x : Fin n → ℝ) : TrigExpr n → ℝ
  | rational q => q
  | variable i => x i
  | pi => Real.pi
  | neg f => -(f.realValue x)
  | add f g => f.realValue x + g.realValue x
  | mul f g => f.realValue x * g.realValue x
  | inv f => 1 / f.realValue x
  | pow f k => f.realValue x ^ k
  | sin f => Real.sin (f.realValue x)
  | cos f => Real.cos (f.realValue x)
  | abs f => |f.realValue x|
  | min f g => _root_.min (f.realValue x) (g.realValue x)
  | max f g => _root_.max (f.realValue x) (g.realValue x)

def intervalValue (box : Box n) : TrigExpr n → Option Interval
  | rational q => some (Interval.point q)
  | variable i => some (box i)
  | pi => some Interval.piInterval
  | neg f => do return (← f.intervalValue box).neg
  | add f g => do return (← f.intervalValue box).add (← g.intervalValue box)
  | mul f g => do return (← f.intervalValue box).mul (← g.intervalValue box)
  | inv f => do (← f.intervalValue box).reciprocal
  | pow f k => do return (← f.intervalValue box).powNat k
  | sin f => do (← f.intervalValue box).sin
  | cos f => do (← f.intervalValue box).cos
  | abs f => do return (← f.intervalValue box).absolute
  | min f g => do return (← f.intervalValue box).minimum (← g.intervalValue box)
  | max f g => do return (← f.intervalValue box).maximum (← g.intervalValue box)

/-- Soundness is proved constructor by constructor, including all branches of
min/max. Inverses and trigonometric evaluations must succeed first. -/
theorem intervalValue_sound (e : TrigExpr n) {box : Box n} {x : Fin n → ℝ}
    (hx : InBox box x) {I : Interval} (he : e.intervalValue box = some I) :
    I.Contains (e.realValue x) := by
  induction e generalizing I with
  | rational q =>
      simp only [intervalValue, Option.some.injEq] at he
      subst I
      exact Interval.contains_point q
  | variable i =>
      simp only [intervalValue, Option.some.injEq] at he
      subst I
      exact hx i
  | pi =>
      simp only [intervalValue, Option.some.injEq] at he
      subst I
      exact Interval.contains_pi
  | neg f ih =>
      cases hf : f.intervalValue box with
      | none => simp [intervalValue, hf] at he
      | some J =>
          simp only [intervalValue, hf, Option.bind_some, Option.some.injEq] at he
          subst I
          exact Interval.contains_neg (ih hf)
  | inv f ih =>
      cases hf : f.intervalValue box with
      | none => simp [intervalValue, hf] at he
      | some J =>
          simp only [intervalValue, hf, Option.bind_some] at he
          exact Interval.contains_reciprocal (ih hf) he
  | pow f k ih =>
      cases hf : f.intervalValue box with
      | none => simp [intervalValue, hf] at he
      | some J =>
          simp only [intervalValue, hf, Option.bind_some, Option.some.injEq] at he
          subst I
          exact Interval.contains_powNat (ih hf) k
  | sin f ih =>
      cases hf : f.intervalValue box with
      | none => simp [intervalValue, hf] at he
      | some J =>
          simp only [intervalValue, hf, Option.bind_some] at he
          exact Interval.contains_sin (ih hf) he
  | cos f ih =>
      cases hf : f.intervalValue box with
      | none => simp [intervalValue, hf] at he
      | some J =>
          simp only [intervalValue, hf, Option.bind_some] at he
          exact Interval.contains_cos (ih hf) he
  | abs f ih =>
      cases hf : f.intervalValue box with
      | none => simp [intervalValue, hf] at he
      | some J =>
          simp only [intervalValue, hf, Option.bind_some, Option.some.injEq] at he
          subst I
          exact Interval.contains_absolute (ih hf)
  | add f g ihf ihg | mul f g ihf ihg | min f g ihf ihg | max f g ihf ihg =>
      cases hf : f.intervalValue box with
      | none => simp [intervalValue, hf] at he
      | some J =>
          cases hg : g.intervalValue box with
          | none => simp [intervalValue, hf, hg] at he
          | some K =>
              simp only [intervalValue, hf, hg, Option.bind_some, Option.some.injEq] at he
              subst I
              first
              | exact Interval.contains_add (ihf hf) (ihg hg)
              | exact Interval.contains_mul (ihf hf) (ihg hg)
              | exact Interval.contains_minimum (ihf hf) (ihg hg)
              | exact Interval.contains_maximum (ihf hf) (ihg hg)

def checkUpper (box : Box n) (e : TrigExpr n) (q : ℚ) : Bool :=
  match e.intervalValue box with
  | none => false
  | some I => decide (I.hi < q)

theorem checkUpper_sound {box : Box n} {e : TrigExpr n} {q : ℚ}
    (h : checkUpper box e q = true) {x : Fin n → ℝ} (hx : InBox box x) :
    e.realValue x < (q : ℝ) := by
  cases he : e.intervalValue box with
  | none => simp [checkUpper, he] at h
  | some I =>
      have hq : I.hi < q := by simpa only [checkUpper, he, decide_eq_true_eq] using h
      exact Interval.lt_of_upper (intervalValue_sound e hx he) hq

/-- The existing exact cover checker works with the richer expression language. -/
theorem covered_upper (tree : CoverTree n) (box : Box n) (e : TrigExpr n) (q : ℚ)
    (hcheck : tree.check (fun b => checkUpper b e q) box = true) :
    ∀ x, InBox box x → e.realValue x < (q : ℝ) :=
  tree.check_sound _ _ (fun _ h _ hx => checkUpper_sound h hx) hcheck

end TrigExpr
end MovingSofaQuantitative.Certificates
