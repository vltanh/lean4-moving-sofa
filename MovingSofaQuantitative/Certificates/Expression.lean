module

public import MovingSofaQuantitative.Certificates.Interval

/-!
# A small interval expression language

Uncompiled proof source. The evaluator returns `none` when an inverse cannot
be justified. Its soundness theorem connects every successful result to the
REAL expression. This permits untrusted generators to emit only data.
-/

@[expose] public section

namespace MovingSofaQuantitative.Certificates

inductive Expr (n : ℕ) where
  | rational : ℚ → Expr n
  | variable : Fin n → Expr n
  | neg : Expr n → Expr n
  | add : Expr n → Expr n → Expr n
  | mul : Expr n → Expr n → Expr n
  | inv : Expr n → Expr n
  | pow : Expr n → ℕ → Expr n
  deriving Repr, DecidableEq

namespace Expr

variable {n : ℕ}

def realValue (x : Fin n → ℝ) : Expr n → ℝ
  | rational q => q
  | variable i => x i
  | neg f => -(f.realValue x)
  | add f g => f.realValue x + g.realValue x
  | mul f g => f.realValue x * g.realValue x
  | inv f => 1 / f.realValue x
  | pow f k => f.realValue x ^ k

def intervalValue (box : Fin n → Interval) : Expr n → Option Interval
  | rational q => some (Interval.point q)
  | variable i => some (box i)
  | neg f => do return (← f.intervalValue box).neg
  | add f g => do return (← f.intervalValue box).add (← g.intervalValue box)
  | mul f g => do return (← f.intervalValue box).mul (← g.intervalValue box)
  | inv f => do (← f.intervalValue box).reciprocal
  | pow f k => do return (← f.intervalValue box).powNat k

/-- A successful enclosure is valid for every point in the whole input box. -/
theorem intervalValue_sound (e : Expr n) {box : Fin n → Interval} {x : Fin n → ℝ}
    (hx : ∀ i, (box i).Contains (x i)) {I : Interval}
    (he : e.intervalValue box = some I) : I.Contains (e.realValue x) := by
  induction e generalizing I with
  | rational q =>
      simp only [intervalValue, Option.some.injEq] at he
      subst I
      exact Interval.contains_point q
  | variable i =>
      simp only [intervalValue, Option.some.injEq] at he
      subst I
      exact hx i
  | neg f ih =>
      cases hf : f.intervalValue box with
      | none => simp [intervalValue, hf] at he
      | some J =>
          simp only [intervalValue, hf, Option.bind_some, Option.some.injEq] at he
          subst I
          exact Interval.contains_neg (ih hf)
  | add f g ihf ihg =>
      cases hf : f.intervalValue box with
      | none => simp [intervalValue, hf] at he
      | some J =>
          cases hg : g.intervalValue box with
          | none => simp [intervalValue, hf, hg] at he
          | some K =>
              simp only [intervalValue, hf, hg, Option.bind_some, Option.some.injEq] at he
              subst I
              exact Interval.contains_add (ihf hf) (ihg hg)
  | mul f g ihf ihg =>
      cases hf : f.intervalValue box with
      | none => simp [intervalValue, hf] at he
      | some J =>
          cases hg : g.intervalValue box with
          | none => simp [intervalValue, hf, hg] at he
          | some K =>
              simp only [intervalValue, hf, hg, Option.bind_some, Option.some.injEq] at he
              subst I
              exact Interval.contains_mul (ihf hf) (ihg hg)
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

/-- Only a strict rational endpoint comparison accepts a strict inequality. -/
def checkUpper (box : Fin n → Interval) (e : Expr n) (q : ℚ) : Bool :=
  match e.intervalValue box with
  | none => false
  | some I => decide (I.hi < q)

theorem checkUpper_sound {box : Fin n → Interval} {e : Expr n} {q : ℚ}
    (h : checkUpper box e q = true) {x : Fin n → ℝ}
    (hx : ∀ i, (box i).Contains (x i)) : e.realValue x < (q : ℝ) := by
  cases he : e.intervalValue box with
  | none => simp [checkUpper, he] at h
  | some I =>
      have hq : I.hi < q := by simpa only [checkUpper, he, decide_eq_true_eq] using h
      exact Interval.lt_of_upper (intervalValue_sound e hx he) hq

/-- Structural substitution preserves real evaluation; generators can share
small expression templates without introducing trusted evaluation code. -/
def substitute {m : ℕ} (s : Fin n → Expr m) : Expr n → Expr m
  | rational q => rational q
  | variable i => s i
  | neg f => neg (f.substitute s)
  | add f g => add (f.substitute s) (g.substitute s)
  | mul f g => mul (f.substitute s) (g.substitute s)
  | inv f => inv (f.substitute s)
  | pow f k => pow (f.substitute s) k

theorem realValue_substitute {m : ℕ} (s : Fin n → Expr m) (x : Fin m → ℝ) (e : Expr n) :
    (e.substitute s).realValue x = e.realValue (fun i => (s i).realValue x) := by
  induction e <;> simp_all [substitute, realValue]

end Expr
end MovingSofaQuantitative.Certificates
