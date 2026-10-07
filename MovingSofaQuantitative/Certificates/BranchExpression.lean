module

public import MovingSofaQuantitative.Certificates.TrigExpression

/-!
# Sound interval evaluation of conditional scalar formulas

Uncompiled proof source. A branch is selected only when its comparison holds
on the entire box. When an interval comparison is undecided, both branches
must evaluate and their hull is retained. This covers changing overlap and
arc boundaries without assuming that a sampled branch holds everywhere.
-/

@[expose] public section

namespace MovingSofaQuantitative.Certificates

inductive BranchExpr (n : ℕ) where
  | atom : TrigExpr n → BranchExpr n
  | neg : BranchExpr n → BranchExpr n
  | add : BranchExpr n → BranchExpr n → BranchExpr n
  | mul : BranchExpr n → BranchExpr n → BranchExpr n
  | inv : BranchExpr n → BranchExpr n
  | pow : BranchExpr n → ℕ → BranchExpr n
  | abs : BranchExpr n → BranchExpr n
  | iteLE : TrigExpr n → TrigExpr n → BranchExpr n → BranchExpr n → BranchExpr n
  deriving Repr, DecidableEq

namespace BranchExpr

variable {n : ℕ}

noncomputable def realValue (x : Fin n → ℝ) : BranchExpr n → ℝ
  | atom e => e.realValue x
  | neg e => -(e.realValue x)
  | add e f => e.realValue x + f.realValue x
  | mul e f => e.realValue x * f.realValue x
  | inv e => 1 / e.realValue x
  | pow e k => e.realValue x ^ k
  | abs e => |e.realValue x|
  | iteLE a b e f => if a.realValue x ≤ b.realValue x then e.realValue x else f.realValue x

def intervalValue (box : Box n) : BranchExpr n → Option Interval
  | atom e => e.intervalValue box
  | neg e => do return (← e.intervalValue box).neg
  | add e f => do return (← e.intervalValue box).add (← f.intervalValue box)
  | mul e f => do return (← e.intervalValue box).mul (← f.intervalValue box)
  | inv e => do (← e.intervalValue box).reciprocal
  | pow e k => do return (← e.intervalValue box).powNat k
  | abs e => do return (← e.intervalValue box).absolute
  | iteLE a b e f => do
      let A ← a.intervalValue box
      let B ← b.intervalValue box
      if A.hi ≤ B.lo then e.intervalValue box
      else if B.hi < A.lo then f.intervalValue box
      else return (← e.intervalValue box).hull (← f.intervalValue box)

/-- A definite interval ordering implies the ordering of all enclosed values. -/
private theorem le_of_intervals {A B : Interval} {a b : ℝ}
    (ha : A.Contains a) (hb : B.Contains b) (h : A.hi ≤ B.lo) : a ≤ b :=
  ha.2.trans ((by exact_mod_cast h).trans hb.1)

private theorem not_le_of_intervals {A B : Interval} {a b : ℝ}
    (ha : A.Contains a) (hb : B.Contains b) (h : B.hi < A.lo) : ¬a ≤ b := by
  have hlt : b < a := hb.2.trans_lt ((by exact_mod_cast h).trans_le ha.1)
  exact not_le.mpr hlt

theorem intervalValue_sound (e : BranchExpr n) {box : Box n} {x : Fin n → ℝ}
    (hx : InBox box x) {I : Interval} (he : e.intervalValue box = some I) :
    I.Contains (e.realValue x) := by
  induction e generalizing I with
  | atom e => exact TrigExpr.intervalValue_sound e hx he
  | neg e ih =>
      cases h : e.intervalValue box with
      | none => simp [intervalValue, h] at he
      | some J =>
          simp only [intervalValue, h, Option.bind_some, Option.some.injEq] at he
          subst I
          exact Interval.contains_neg (ih h)
  | inv e ih =>
      cases h : e.intervalValue box with
      | none => simp [intervalValue, h] at he
      | some J =>
          simp only [intervalValue, h, Option.bind_some] at he
          exact Interval.contains_reciprocal (ih h) he
  | pow e k ih =>
      cases h : e.intervalValue box with
      | none => simp [intervalValue, h] at he
      | some J =>
          simp only [intervalValue, h, Option.bind_some, Option.some.injEq] at he
          subst I
          exact Interval.contains_powNat (ih h) k
  | abs e ih =>
      cases h : e.intervalValue box with
      | none => simp [intervalValue, h] at he
      | some J =>
          simp only [intervalValue, h, Option.bind_some, Option.some.injEq] at he
          subst I
          exact Interval.contains_absolute (ih h)
  | add e f ihe ihf | mul e f ihe ihf =>
      cases ha : e.intervalValue box with
      | none => simp [intervalValue, ha] at he
      | some A =>
          cases hb : f.intervalValue box with
          | none => simp [intervalValue, ha, hb] at he
          | some B =>
              simp only [intervalValue, ha, hb, Option.bind_some, Option.some.injEq] at he
              subst I
              first
              | exact Interval.contains_add (ihe ha) (ihf hb)
              | exact Interval.contains_mul (ihe ha) (ihf hb)
  | iteLE a b e f ihe ihf =>
      cases ha : a.intervalValue box with
      | none => simp [intervalValue, ha] at he
      | some A =>
          cases hb : b.intervalValue box with
          | none => simp [intervalValue, ha, hb] at he
          | some B =>
              have hva := TrigExpr.intervalValue_sound a hx ha
              have hvb := TrigExpr.intervalValue_sound b hx hb
              simp only [intervalValue, ha, hb, Option.bind_some] at he
              split_ifs at he with hyes hno
              · simpa only [realValue, if_pos (le_of_intervals hva hvb hyes)] using ihe he
              · simpa only [realValue, if_neg (not_le_of_intervals hva hvb hno)] using ihf he
              · cases hE : e.intervalValue box with
                | none => simp [hE] at he
                | some J =>
                    cases hF : f.intervalValue box with
                    | none => simp [hE, hF] at he
                    | some K =>
                        simp only [hE, hF, Option.bind_some, Option.some.injEq] at he
                        subst I
                        dsimp only [realValue]
                        split_ifs
                        · exact Interval.contains_hull_left (ihe hE)
                        · exact Interval.contains_hull_right (ihf hF)

def checkUpper (box : Box n) (e : BranchExpr n) (q : ℚ) : Bool :=
  match e.intervalValue box with
  | none => false
  | some I => decide (I.hi < q)

theorem checkUpper_sound {box : Box n} {e : BranchExpr n} {q : ℚ}
    (hc : checkUpper box e q = true) {x : Fin n → ℝ} (hx : InBox box x) :
    e.realValue x < (q : ℝ) := by
  cases he : e.intervalValue box with
  | none => simp [checkUpper, he] at hc
  | some I =>
      have hq : I.hi < q := by simpa only [checkUpper, he, decide_eq_true_eq] using hc
      exact Interval.lt_of_upper (intervalValue_sound e hx he) hq

end BranchExpr
end MovingSofaQuantitative.Certificates
