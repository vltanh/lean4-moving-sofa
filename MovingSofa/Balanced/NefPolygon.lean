module

public import MovingSofa.Monotone.CapContainsNiche

/-!
# Simple Nef polygons (§3.1)

Definitions 3.1.1–3.1.4, Proposition 3.1.1 (`pro:monotone-boolean-function`) and Theorem 3.1.2
(`thm:simple-nef-polygon`). Definition 3.1.5 (the `O`-notation with subscripts) is rendered by
explicit constants: a statement `f = O_{X,i}(g)` becomes `∃ C, |f| ≤ C g` with `C` chosen after `X`
and `i`.
-/

@[expose] public section

open Real Set

namespace MovingSofa

/-- An `n`-ary boolean function (Definition 3.1.1, `def:boolean-function`). -/
abbrev BoolFun (n : ℕ) : Type := (Fin n → Bool) → Bool

/-- A monotone boolean function (Definition 3.1.2, `def:monotone-boolean-function`). -/
def BoolFun.IsMonotone {n : ℕ} (E : BoolFun n) : Prop :=
  ∀ P Q : Fin n → Bool, (∀ i, P i = true → Q i = true) → E P = true → E Q = true

/-- Boolean expressions built from variables with conjunctions and disjunctions only. -/
inductive PosBoolExpr (n : ℕ) where
  | var (i : Fin n)
  | and (a b : PosBoolExpr n)
  | or (a b : PosBoolExpr n)

/-- The boolean function of a positive boolean expression. -/
def PosBoolExpr.eval {n : ℕ} : PosBoolExpr n → BoolFun n
  | .var i => fun P => P i
  | .and a b => fun P => a.eval P && b.eval P
  | .or a b => fun P => a.eval P || b.eval P

/-- **Proposition 3.1.1** (`pro:monotone-boolean-function`). A boolean function obtained from the
variables by conjunctions and disjunctions is monotone. -/
theorem proposition3_1_1 {n : ℕ} (e : PosBoolExpr n) : e.eval.IsMonotone := by
  sorry

open Classical in
/-- The Nef polygon `𝓔(H_1, …, H_n) = {p : 𝓔(p ∈ H_1, …, p ∈ H_n)}` (Definition 3.1.3,
`def:nef-polygon`). -/
noncomputable def nefPolygon {n : ℕ} (E : BoolFun n) (H : Fin n → Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {p | E (fun i => decide (p ∈ H i)) = true}

/-- A defining half-plane of a simple Nef polygon: the closed half-plane `H₋(t, h)` or the open
half-plane `H₋°(t, h)`. -/
structure HalfPlaneData where
  t : ℝ
  h : ℝ
  isOpen : Bool

/-- The half-plane described by a `HalfPlaneData`. -/
def HalfPlaneData.toSet (d : HalfPlaneData) : Set (ℝ × ℝ) :=
  if d.isOpen then halfMinusOpen d.t d.h else halfMinus d.t d.h

/-- The boundary line `l(t, h)` of a defining half-plane. -/
def HalfPlaneData.boundary (d : HalfPlaneData) : Set (ℝ × ℝ) := line d.t d.h

/-- The half-plane pushed by `δ` in the direction of its normal: `H₋(t, h + δ)` or `H₋°(t, h + δ)`. -/
def HalfPlaneData.shift (d : HalfPlaneData) (δ : ℝ) : HalfPlaneData := { d with h := d.h + δ }

/-- `X` is a simple Nef polygon with defining half-planes `H_1, …, H_n` (Definition 3.1.4,
`def:simple-nef-polygon`): `X = 𝓔(H_1, …, H_n)` for a monotone boolean function `𝓔`, and the
half-planes have pairwise different boundary lines. -/
def IsSimpleNefPolygon {n : ℕ} (X : Set (ℝ × ℝ)) (E : BoolFun n) (H : Fin n → HalfPlaneData) :
    Prop :=
  E.IsMonotone ∧ Pairwise (fun i j => (H i).boundary ≠ (H j).boundary) ∧
    X = nefPolygon E (fun i => (H i).toSet)

/-- **Theorem 3.1.2** (`thm:simple-nef-polygon`). Pushing the `i`-th defining half-plane of a bounded
simple Nef polygon `X` by `δ` changes its area by `𝓗¹(∂X ∩ l_i) δ + O_{X,i}(δ²)`. The paper's
statement leaves the boundedness of `X` (finiteness of its area) implicit. -/
theorem theorem3_1_2 {n : ℕ} {X : Set (ℝ × ℝ)} {E : BoolFun n} {H : Fin n → HalfPlaneData}
    (hX : IsSimpleNefPolygon X E H) (hb : Bornology.IsBounded X) (i : Fin n) :
    ∃ ε > 0, ∃ C : ℝ, ∀ δ : ℝ, |δ| ≤ ε →
      |area (nefPolygon E (Function.update (fun j => (H j).toSet) i ((H i).shift δ).toSet)) -
          area X - lineLength (H i).t (H i).h (frontier X) * δ| ≤ C * δ ^ 2 := by
  sorry

end MovingSofa
