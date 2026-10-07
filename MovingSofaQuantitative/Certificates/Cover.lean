module

public import MovingSofaQuantitative.Certificates.Expression

/-!
# Binary box certificates and a sound bounded search

Uncompiled proof source. Checking isolated sample points is insufficient.
Every split below covers its parent, including the splitting hyperplane, and
induction propagates a leaf theorem to every real point of the root box.
Failure, exhausted fuel, and an invalid cut all return false.
-/

@[expose] public section

namespace MovingSofaQuantitative.Certificates

abbrev Box (n : ℕ) := Fin n → Interval

def InBox {n : ℕ} (box : Box n) (x : Fin n → ℝ) : Prop :=
  ∀ i, (box i).Contains (x i)

def splitLeft {n : ℕ} (box : Box n) (axis : Fin n) (cut : ℚ) : Box n :=
  Function.update box axis ⟨(box axis).lo, cut⟩

def splitRight {n : ℕ} (box : Box n) (axis : Fin n) (cut : ℚ) : Box n :=
  Function.update box axis ⟨cut, (box axis).hi⟩

/-- The two closed children cover the parent; no boundary point is lost. -/
theorem split_covers {n : ℕ} {box : Box n} {x : Fin n → ℝ}
    (hx : InBox box x) (axis : Fin n) (cut : ℚ) :
    InBox (splitLeft box axis cut) x ∨ InBox (splitRight box axis cut) x := by
  rcases le_total (x axis) (cut : ℝ) with hl | hr
  · left
    intro i
    by_cases hi : i = axis
    · subst i
      simpa only [splitLeft, Function.update_same, Interval.Contains] using ⟨(hx axis).1, hl⟩
    · simpa only [splitLeft, Function.update_noteq hi] using hx i
  · right
    intro i
    by_cases hi : i = axis
    · subst i
      simpa only [splitRight, Function.update_same, Interval.Contains] using ⟨hr, (hx axis).2⟩
    · simpa only [splitRight, Function.update_noteq hi] using hx i

inductive CoverTree (n : ℕ) where
  | leaf : CoverTree n
  | split : Fin n → ℚ → CoverTree n → CoverTree n → CoverTree n
  deriving Repr

namespace CoverTree

variable {n : ℕ}

def check (leafCheck : Box n → Bool) : CoverTree n → Box n → Bool
  | leaf, box => leafCheck box
  | split axis cut left right, box =>
      decide ((box axis).lo ≤ cut ∧ cut ≤ (box axis).hi) &&
      left.check leafCheck (splitLeft box axis cut) &&
      right.check leafCheck (splitRight box axis cut)

/-- Soundness quantifies over the entire box, not just its vertices or center. -/
theorem check_sound (leafCheck : Box n → Bool) (P : (Fin n → ℝ) → Prop)
    (hleaf : ∀ box, leafCheck box = true → ∀ x, InBox box x → P x)
    (tree : CoverTree n) {box : Box n} (hcheck : tree.check leafCheck box = true) :
    ∀ x, InBox box x → P x := by
  induction tree generalizing box with
  | leaf => exact hleaf box hcheck
  | split axis cut left right ihl ihr =>
      have hparts := Bool.and_eq_true.mp hcheck
      have hparts' := Bool.and_eq_true.mp hparts.1
      intro x hx
      rcases split_covers hx axis cut with hl | hr
      · exact ihl hparts'.2 x hl
      · exact ihr hparts.2 x hr

/-- Each accepted expression leaf has a corresponding real inequality. -/
theorem expression_certificate (tree : CoverTree n) (box : Box n) (e : Expr n) (q : ℚ)
    (hcheck : tree.check (fun b => Expr.checkUpper b e q) box = true) :
    ∀ x, InBox box x → e.realValue x < (q : ℝ) :=
  tree.check_sound _ _ (fun _ h _ hx => Expr.checkUpper_sound h hx) hcheck

end CoverTree

/-- A deterministic search can be used instead of a large generated tree.
The caller chooses only the axis. The splitting point is always the rational
midpoint, so no heuristic choice is trusted to establish the covering claim. -/
def boundedCheck {n : ℕ} (leafCheck : Box n → Bool) (chooseAxis : Box n → Fin n) :
    ℕ → Box n → Bool
  | 0, _ => false
  | fuel + 1, box =>
      if leafCheck box then true
      else
        let i := chooseAxis box
        let c := ((box i).lo + (box i).hi) / 2
        boundedCheck leafCheck chooseAxis fuel (splitLeft box i c) &&
        boundedCheck leafCheck chooseAxis fuel (splitRight box i c)

/-- Bounded search is a proof-producing decision procedure after reduction;
exhausting the bound never silently accepts. -/
theorem boundedCheck_sound {n : ℕ} (leafCheck : Box n → Bool)
    (chooseAxis : Box n → Fin n) (P : (Fin n → ℝ) → Prop)
    (hleaf : ∀ box, leafCheck box = true → ∀ x, InBox box x → P x)
    (fuel : ℕ) {box : Box n}
    (hcheck : boundedCheck leafCheck chooseAxis fuel box = true) :
    ∀ x, InBox box x → P x := by
  induction fuel generalizing box with
  | zero => simp [boundedCheck] at hcheck
  | succ fuel ih =>
      by_cases hleafPass : leafCheck box = true
      · exact hleaf box hleafPass
      · have hfalse : leafCheck box = false := Bool.eq_false_of_not_eq_true hleafPass
        simp only [boundedCheck, hfalse, Bool.false_eq_true, ↓reduceIte] at hcheck
        have hparts := Bool.and_eq_true.mp hcheck
        intro x hx
        let i := chooseAxis box
        let c := ((box i).lo + (box i).hi) / 2
        rcases split_covers hx i c with hl | hr
        · exact ih hparts.1 x hl
        · exact ih hparts.2 x hr

/-- Conjunction of certificates establishes every requested inequality on the
same parameter domain; a missing requested inequality cannot be hidden by an
empty generated leaf list. -/
def checkExpressions {n : ℕ} (box : Box n) (claims : List (Expr n × ℚ)) : Bool :=
  claims.all (fun p => Expr.checkUpper box p.1 p.2)

theorem checkExpressions_sound {n : ℕ} {box : Box n} {claims : List (Expr n × ℚ)}
    (h : checkExpressions box claims = true) {x : Fin n → ℝ} (hx : InBox box x)
    {e : Expr n} {q : ℚ} (he : (e, q) ∈ claims) : e.realValue x < (q : ℝ) := by
  have hc : Expr.checkUpper box e q = true := (List.all_eq_true.mp h) (e, q) he
  exact Expr.checkUpper_sound hc hx

end MovingSofaQuantitative.Certificates
