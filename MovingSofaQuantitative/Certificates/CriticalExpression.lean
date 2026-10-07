module

public import MovingSofaQuantitative.ClosedCriticalModel

/-!
# Concrete rank-two scalar expressions and certificate leaves

Uncompiled proof source. The expression model is instantiated from the actual
kernel Gram expressions. A passing leaf proves both slack sensitivities and
either a diagonal fallback or the normalized pair inequality. Zero-cosine
boxes therefore never need an invalid division. No certificate acceptance is
asserted by the soundness lemmas in this file.
-/

@[expose] public section

open Real

namespace MovingSofaQuantitative.Certificates
namespace CriticalExpression

open KernelExpression

variable {n : ℕ}

structure Coordinates (n : ℕ) where
  d₁ : BranchExpr n
  d₂ : BranchExpr n
  g₁₁ : BranchExpr n
  g₁₂ : BranchExpr n
  g₂₂ : BranchExpr n
  k₀ : BranchExpr n
  k₁ : BranchExpr n
  k₂ : BranchExpr n

namespace Coordinates

def s₁₁ (m : Coordinates n) : BranchExpr n := .add m.d₁ m.g₁₁
def s₂₂ (m : Coordinates n) : BranchExpr n := .add m.d₂ m.g₂₂
def det (m : Coordinates n) : BranchExpr n := bsub (.mul m.s₁₁ m.s₂₂) (.pow m.g₁₂ 2)
def a₁ (m : Coordinates n) : BranchExpr n :=
  bdiv (bsub (.mul m.s₂₂ m.k₁) (.mul m.g₁₂ m.k₂)) m.det
def a₂ (m : Coordinates n) : BranchExpr n :=
  bdiv (bsub (.mul m.s₁₁ m.k₂) (.mul m.g₁₂ m.k₁)) m.det
def value (m : Coordinates n) : BranchExpr n :=
  bsub (bsub m.k₀ (.mul m.a₁ m.k₁)) (.mul m.a₂ m.k₂)

noncomputable def realValue (x : Fin n → ℝ) (m : Coordinates n) : GramCoordinates :=
  ⟨m.d₁.realValue x, m.d₂.realValue x, m.g₁₁.realValue x,
    m.g₁₂.realValue x, m.g₂₂.realValue x, m.k₀.realValue x,
    m.k₁.realValue x, m.k₂.realValue x⟩

theorem a₁_real (m : Coordinates n) (x : Fin n → ℝ) :
    m.a₁.realValue x = (m.realValue x).a₁ := rfl

theorem a₂_real (m : Coordinates n) (x : Fin n → ℝ) :
    m.a₂.realValue x = (m.realValue x).a₂ := rfl

theorem value_real (m : Coordinates n) (x : Fin n → ℝ) :
    m.value.realValue x = (m.realValue x).value := rfl

end Coordinates

def weightB (φ θ : TrigExpr n) : TrigExpr n :=
  sub (KernelExpression.tan (sub halfPi θ)) (KernelExpression.tan φ)

def weightD (φ θ : TrigExpr n) : TrigExpr n :=
  sub (cot (sub (sub .pi φ) (.add halfPi θ))) (KernelExpression.tan φ)

def bPieces (φ θ : TrigExpr n) : List (TrigExpr n × TrigExpr n) :=
  [(φ, sec φ), (sub halfPi θ, .neg (sec (sub halfPi θ)))]

def dPieces (φ θ : TrigExpr n) : List (TrigExpr n × TrigExpr n) :=
  [(.add halfPi θ, csc (sub (sub .pi φ) (.add halfPi θ))),
   (sub .pi φ, .neg (weightD φ θ))]

def centeredPieces (t : TrigExpr n) : List (TrigExpr n × TrigExpr n) :=
  [(t, rat 1), (rat 0, .neg (div (.cos t) (rat 2)))]

def pairPieces (t u : TrigExpr n) : List (TrigExpr n × TrigExpr n) :=
  [(t, .cos u), (u, .neg (.cos t))]

def model (φ θ : TrigExpr n) (ks : List (TrigExpr n × TrigExpr n)) : Coordinates n :=
  let B := bPieces φ θ
  let D := dPieces φ θ
  ⟨lift (weightB φ θ), lift (weightD φ θ),
    combinationGram φ B B, combinationGram φ B D, combinationGram φ D D,
    combinationGram φ ks ks, combinationGram φ ks B, combinationGram φ ks D⟩

/-- Expression construction preserves the actual finite Gram model exactly. -/
theorem model_real (x : Fin n → ℝ) (φ θ : TrigExpr n)
    (ks : List (TrigExpr n × TrigExpr n)) :
    (model φ θ ks).realValue x = criticalCoordinates (φ.realValue x) (θ.realValue x)
      (ks.map fun k => (k.1.realValue x, k.2.realValue x)) := by
  unfold model Coordinates.realValue criticalCoordinates
  simp only [combinationGram_real, bPieces, dPieces, List.map_cons, List.map_nil,
    scalarB, scalarD, scalarWeightB, scalarWeightD, weightB, weightD,
    lift, BranchExpr.realValue, TrigExpr.realValue, sec, csc, cot,
    KernelExpression.tan, halfPi, sub, div, rat, Real.tan_eq_sin_div_cos]

/-- Sensitivity to the two physical wall gaps, rather than the rescaled gaps. -/
def sensitivity (φ θ : TrigExpr n) (m : Coordinates n) : BranchExpr n :=
  .add (.abs (bdiv m.a₁ (lift (.cos (sub halfPi θ)))))
    (.abs (bdiv m.a₂ (lift (.sin (sub (sub .pi φ) (.add halfPi θ))))))

def denominator (t u : TrigExpr n) : TrigExpr n := .add (.abs (.cos t)) (.abs (.cos u))

def pointT : Coordinates 4 := model (.variable 0) (.variable 1) (centeredPieces (.variable 2))
def pointU : Coordinates 4 := model (.variable 0) (.variable 1) (centeredPieces (.variable 3))
def pairModel : Coordinates 4 := model (.variable 0) (.variable 1)
  (pairPieces (.variable 2) (.variable 3))

def sensT : BranchExpr 4 := sensitivity (.variable 0) (.variable 1) pointT
def sensU : BranchExpr 4 := sensitivity (.variable 0) (.variable 1) pointU

def twice (e : BranchExpr n) : BranchExpr n := .mul (lift (rat 2)) e

def normalizedPair : BranchExpr 4 :=
  bdiv (twice pairModel.value) (lift (.pow (denominator (.variable 2) (.variable 3)) 2))

def positiveDenominator (box : Box 4) : Bool :=
  match (denominator (.variable 2) (.variable 3)).intervalValue box with
  | none => false
  | some I => decide (0 < I.lo)

def diagonalCheck (box : Box 4) : Bool :=
  BranchExpr.checkUpper box (twice pointT.value) ((93 / 100 : ℚ) ^ 2) &&
  BranchExpr.checkUpper box (twice pointU.value) ((93 / 100 : ℚ) ^ 2)

def pairCheck (box : Box 4) : Bool :=
  positiveDenominator box && BranchExpr.checkUpper box normalizedPair ((93 / 100 : ℚ) ^ 2)

/-- Numerical acceptance is strict. All zero cases are covered by the diagonal
branch; an inconclusive denominator is never inverted as an interval. -/
def leafCheck (box : Box 4) : Bool :=
  BranchExpr.checkUpper box sensT (1 / 2) &&
  BranchExpr.checkUpper box sensU (1 / 2) &&
  (diagonalCheck box || pairCheck box)

noncomputable def LeafProperty (x : Fin 4 → ℝ) : Prop :=
  sensT.realValue x < 1 / 2 ∧ sensU.realValue x < 1 / 2 ∧
    ((2 * pointT.value.realValue x < (93 / 100 : ℝ) ^ 2 ∧
      2 * pointU.value.realValue x < (93 / 100 : ℝ) ^ 2) ∨
      2 * pairModel.value.realValue x <
        ((93 / 100 : ℝ) * (|cos (x 2)| + |cos (x 3)|)) ^ 2)

/-- This is an entire-box theorem; values at its center play no role. -/
theorem leafCheck_sound (box : Box 4) (hc : leafCheck box = true)
    (x : Fin 4 → ℝ) (hx : InBox box x) : LeafProperty x := by
  have h := Bool.and_eq_true.mp hc
  have hs := Bool.and_eq_true.mp h.1
  refine ⟨BranchExpr.checkUpper_sound hs.1 hx, BranchExpr.checkUpper_sound hs.2 hx, ?_⟩
  rcases Bool.or_eq_true.mp h.2 with hd | hp
  · left
    have hds := Bool.and_eq_true.mp hd
    have ht := BranchExpr.checkUpper_sound hds.1 hx
    have hu := BranchExpr.checkUpper_sound hds.2 hx
    simpa only [twice, lift, rat, BranchExpr.realValue, TrigExpr.realValue,
      Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat] using And.intro ht hu
  · right
    have hps := Bool.and_eq_true.mp hp
    have hpositive : 0 < |cos (x 2)| + |cos (x 3)| := by
      unfold positiveDenominator at hps
      cases he : (denominator (.variable 2) (.variable 3)).intervalValue box with
      | none => simp only [he, Bool.false_eq_true, false_and] at hps
      | some I =>
          have hlo : (0 : ℚ) < I.lo := by simpa only [he, decide_eq_true_eq] using hps.1
          have hv := TrigExpr.intervalValue_sound
            (denominator (.variable 2) (.variable 3)) hx he
          have hreal : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hlo
          exact hreal.trans_le hv.1
    have hbound := BranchExpr.checkUpper_sound hps.2 hx
    change (2 * pairModel.value.realValue x) / (|cos (x 2)| + |cos (x 3)|) ^ 2 <
      ((93 / 100 : ℚ) ^ 2 : ℝ) at hbound
    have hmul := (div_lt_iff₀ (sq_pos_of_pos hpositive)).mp hbound
    norm_cast at hmul
    nlinarith only [hmul]

/-- Fixed parameter box inherited from the already proved reference enclosures.
The angular upper endpoint encloses pi rather than a decimal approximation below it. -/
def rootBox : Box 4 :=
  ![⟨39177264 / 1000000000, 39177465 / 1000000000⟩,
    ⟨681301409 / 1000000000, 681301610 / 1000000000⟩,
    ⟨0, Interval.piInterval.hi⟩,
    ⟨0, Interval.piInterval.hi⟩]

/-- Parameter widths are weighted because their reciprocal kernels are more
sensitive than the two evaluation angles. Axis choice affects cost, not soundness. -/
def chooseAxis (box : Box 4) : Fin 4 :=
  let w : Fin 4 → ℚ := fun i =>
    (if i = 0 ∨ i = 1 then 4096 else 1) * ((box i).hi - (box i).lo)
  if w 0 ≥ w 1 ∧ w 0 ≥ w 2 ∧ w 0 ≥ w 3 then 0
  else if w 1 ≥ w 2 ∧ w 1 ≥ w 3 then 1
  else if w 2 ≥ w 3 then 2
  else 3

/-- A closed finite check, deliberately separate from any assertion that it
has passed. Certificate generation/replay can choose a shallower accepted tree. -/
def closedCheck (depth : ℕ) : Bool := boundedCheck leafCheck chooseAxis depth rootBox

theorem closedCheck_sound (depth : ℕ) (h : closedCheck depth = true) :
    ∀ x, InBox rootBox x → LeafProperty x :=
  boundedCheck_sound leafCheck chooseAxis LeafProperty leafCheck_sound depth h

end CriticalExpression
end MovingSofaQuantitative.Certificates
