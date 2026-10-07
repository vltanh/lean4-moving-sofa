module

public import MovingSofaQuantitative.TrialResidualFormulas
public import MovingSofaQuantitative.TrialEnergySoundness
public import MovingSofaQuantitative.Certificates.IntegralMesh
public import MovingSofaQuantitative.Certificates.Sinc

/-!
# Closed certificate for the feasible critical trial energy

UNCOMPILED SOURCE. This is the Lean-side transcription of
\`critical_cone/certify_feasible_trial.py\`.  It does not import the JSON
receipt.  The receipt is useful only as a regression oracle.

The checker keeps the two Gerver parameters interval-valued and subdivides
every analytic residual piece into 512 cells.  The Hermite values and slopes
are the exact rational data in \`CriticalTrialData\`; the contact slope is
recomputed from the actual parameter expressions.  Every successful interval
evaluation is connected to the corresponding real residual by the soundness
theorems below.

No floating-point sample or optimizer enters the acceptance predicate.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Finset
open MovingSofaOptimality MovingSofaStability
open MovingSofaQuantitative.Certificates

namespace MovingSofaQuantitative
namespace CriticalTrialCertificate

abbrev T := TrigExpr 3
abbrev B := BranchExpr 3
abbrev Box3 := Box 3

def rat (q : ℚ) : T := .rational q
def v (i : Fin 3) : T := .variable i
def piE : T := .pi
def neg (x : T) : T := .neg x
def add (x y : T) : T := .add x y
def mul (x y : T) : T := .mul x y
def inv (x : T) : T := .inv x
def sub (x y : T) : T := add x (neg y)
def div (x y : T) : T := mul x (inv y)
def pow (x : T) (n : ℕ) : T := .pow x n
def sin (x : T) : T := .sin x
def cos (x : T) : T := .cos x

def φ : T := v 0
def θ : T := v 1
def t : T := v 2
def halfPi : T := div piE (rat 2)
def c : T := sub halfPi θ
def b : T := sub halfPi φ
def bigT : T := sub piE φ

def q : T := rat (10934514869 / 10000000000 : ℚ)
def contactValue : T := rat (-4080320233 / 10000000000 : ℚ)

def startValue : T := add (neg (cos φ)) (mul q (sin φ))
def startSlope : T := add (sin φ) (mul q (cos φ))
def contactSlope : T :=
  div (sub (mul contactValue (cos (sub c φ))) startValue) (sin (sub c φ))

def x (i : ℕ) : T :=
  if i ≤ 8 then
    add φ (mul (sub c φ) (rat ((i : ℚ) / 8)))
  else
    add c (mul (sub halfPi c) (rat (((i : ℚ) - 8) / 8)))

def nodeValue : Fin 17 → T
  | 0 => startValue
  | 1 => rat (-1078919599/1250000000)
  | 2 => rat (-31126707/40000000)
  | 3 => rat (-437577721/625000000)
  | 4 => rat (-9828693/15625000)
  | 5 => rat (-5650988373/10000000000)
  | 6 => rat (-5083771327/10000000000)
  | 7 => rat (-1144865203/2500000000)
  | 8 => contactValue
  | 9 => rat (-3500057133/10000000000)
  | 10 => rat (-2944649529/10000000000)
  | 11 => rat (-2403539187/10000000000)
  | 12 => rat (-58691981/312500000)
  | 13 => rat (-1371834111/10000000000)
  | 14 => rat (-17763627/200000000)
  | 15 => rat (-430688197/10000000000)
  | 16 => rat 0

def nodeSlope : Fin 17 → T
  | 0 => startSlope
  | 1 => rat (4339550711/5000000000)
  | 2 => rat (7723585883/10000000000)
  | 3 => rat (7028975229/10000000000)
  | 4 => rat (6359229927/10000000000)
  | 5 => rat (569148283/1000000000)
  | 6 => rat (2552594261/5000000000)
  | 7 => rat (5349627621/10000000000)
  | 8 => contactSlope
  | 9 => rat (3483836151/5000000000)
  | 10 => rat (6495576867/10000000000)
  | 11 => rat (6277727561/10000000000)
  | 12 => rat (303294039/500000000)
  | 13 => rat (290950371/500000000)
  | 14 => rat (553481437/1000000000)
  | 15 => rat (8158621/15625000)
  | 16 => rat (50024573/100000000)

def nodePosition (i : Fin 17) : T :=
  if i.val ≤ 8 then x i.val else x i.val

def hermiteValue (i : Fin 16) (u : T) : T :=
  let x0 := nodePosition ⟨i, Nat.lt_trans i.isLt (by decide)⟩
  let x1 := nodePosition ⟨i+1, by omega⟩
  let h := sub x1 x0
  let z := div (sub u x0) h
  let y0 := nodeValue ⟨i, Nat.lt_trans i.isLt (by decide)⟩
  let y1 := nodeValue ⟨i+1, by omega⟩
  let d0 := nodeSlope ⟨i, Nat.lt_trans i.isLt (by decide)⟩
  let d1 := nodeSlope ⟨i+1, by omega⟩
  let a := y0
  let bb := mul h d0
  let cc := sub (mul (rat 3) (sub y1 y0)) (mul h (add (mul (rat 2) d0) d1))
  let dd := add (mul (rat 2) (sub y0 y1)) (mul h (add d0 d1))
  add a (mul z (add bb (mul z (add cc (mul z dd)))))

def hermiteDeriv (i : Fin 16) (u : T) : T :=
  let x0 := nodePosition ⟨i, Nat.lt_trans i.isLt (by decide)⟩
  let x1 := nodePosition ⟨i+1, by omega⟩
  let h := sub x1 x0
  let z := div (sub u x0) h
  let y0 := nodeValue ⟨i, Nat.lt_trans i.isLt (by decide)⟩
  let y1 := nodeValue ⟨i+1, by omega⟩
  let d0 := nodeSlope ⟨i, Nat.lt_trans i.isLt (by decide)⟩
  let d1 := nodeSlope ⟨i+1, by omega⟩
  let bb := mul h d0
  let cc := sub (mul (rat 3) (sub y1 y0)) (mul h (add (mul (rat 2) d0) d1))
  let dd := add (mul (rat 2) (sub y0 y1)) (mul h (add d0 d1))
  div (add bb (mul z (add (mul (rat 2) cc) (mul (rat 3) (mul z dd))))) h

def chainValueAux : Nat → T → B
  | 16, u => .atom (nodeValue 16)
  | i, u =>
      if hi : i < 16 then
        .iteLE u (nodePosition ⟨i+1, by omega⟩)
          (.atom (hermiteValue ⟨i,hi⟩ u))
          (chainValueAux (i+1) u)
      else .atom (nodeValue 16)
termination_by i => 16 - i

def chainDerivAux : Nat → T → B
  | 16, u => .atom (nodeSlope 16)
  | i, u =>
      if hi : i < 16 then
        .iteLE u (nodePosition ⟨i+1, by omega⟩)
          (.atom (hermiteDeriv ⟨i,hi⟩ u))
          (chainDerivAux (i+1) u)
      else .atom (nodeSlope 16)
termination_by i => 16 - i

def gapValue (u : T) : T := add (neg (cos u)) (mul q (sin u))
def gapDeriv (u : T) : T := add (sin u) (mul q (cos u))

def g (u : T) : B := .iteLE u φ (.atom (gapValue u)) (chainValueAux 0 u)
def dg (u : T) : B := .iteLE u φ (.atom (gapDeriv u)) (chainDerivAux 0 u)

def lift (e : T) : B := .atom e
def badd (x y : B) : B := .add x y
def bneg (x : B) : B := .neg x
def bsub (x y : B) : B := .add x (.neg y)
def bmul (x y : B) : B := .mul x y
def binv (x : B) : B := .inv x
def bdiv (x y : B) : B := .mul x (.inv y)

def r2 : B := bsub (g (sub halfPi t)) (dg t)
def r3 : B :=
  bsub (bdiv (bsub (lift startValue) (bmul (g t) (lift (cos (sub bigT t)))))
      (lift (sin (sub bigT t)))) (dg t)
def r4 : B :=
  bsub (dg t) (bdiv (badd (bmul (lift (cos t)) (g t)) (lift (rat 1)))
    (lift (sin t)))
def rB : B := badd (bmul (lift (div (sin t) (cos t))) (g t)) (dg t)
def rD : B :=
  badd (dg t) (bdiv
    (bsub (lift startValue) (bmul (g t) (lift (cos (sub t φ)))))
    (lift (sin (sub t φ))))

/-- Final cubic Hermite interval, with physical width \`lastH\`. -/
def lastH : T := sub (nodePosition 16) (nodePosition 15)
def lastC : T :=
  sub (mul (rat 3) (sub (nodeValue 16) (nodeValue 15)))
    (mul lastH (add (mul (rat 2) (nodeSlope 15)) (nodeSlope 16)))
def lastD : T :=
  add (mul (rat 2) (sub (nodeValue 15) (nodeValue 16)))
    (mul lastH (add (nodeSlope 15) (nodeSlope 16)))

/-- In physical coordinate \`w = pi/2-t\`, the last cubic factors as
\`g(pi/2-w) = w*(-d16 + lastA*w + lastB*w²)\`.
Both coefficients are exact Hermite interpolation expressions. -/
def lastA : T := div (add lastC (mul (rat 3) lastD)) (pow lastH 2)
def lastB : T := neg (div lastD (pow lastH 3))
def lastW : T := sub halfPi t
def lastPolynomial : T :=
  add (neg (nodeSlope 16))
    (add (mul lastA lastW) (mul lastB (pow lastW 2)))

/-- Removable-singularity evaluation of the B residual on the last Hermite
piece. Using a raw reciprocal of cos(t) would reject the last interval cell,
as it intersects t=pi/2. The polynomial factorization replaces
tan(t)*g(t) by cos(w)*polynomial(w)/sinc(w), w=pi/2-t.

The sinc interval is valid even if the outward rational box extends slightly
past the true endpoint, using the even Taylor enclosure. -/
def tailBInterval (box : Box3) : Option Interval := do
  let W ← lastW.intervalValue box
  let S ← W.sincSmall
  let invS ← S.reciprocal
  let C ← (cos lastW).intervalValue box
  let F ← lastPolynomial.intervalValue box
  let D ← (dg t).intervalValue box
  return ((C.mul F).mul invS).add D

inductive Kind | r2 | r3 | r4 | B | D
  deriving DecidableEq, Repr

def residual : Kind → B
  | .r2 => r2 | .r3 => r3 | .r4 => r4 | .B => rB | .D => rD

/-- The exact Gerver parameter box used everywhere in the paper. -/
def parameterBox : Box3
  | 0 => ⟨39177264/1000000000,39177465/1000000000⟩
  | 1 => ⟨681301409/1000000000,681301610/1000000000⟩
  | 2 => ⟨0,0⟩

/-- Rational enclosure recorded by the independent research computation. -/
def componentUpper : Kind → ℚ
  | .r2 => 2258104122005795636567409029 / 1237940039285380274899124224
  | .r3 => 102904735206523009294488778 / 1237940039285380274899124224
  | .r4 => 273745126176414033344744773 / 1237940039285380274899124224
  | .B => 8714252570405865425907216 / 1237940039285380274899124224
  | .D => 107939870328054940662623917 / 1237940039285380274899124224

def r1Upper : ℚ :=
  58017271195847425899889281 / 1237940039285380274899124224

def bGapUpper : ℚ :=
  99156653185241992015427571 / 1237940039285380274899124224

def energyUpper : ℚ :=
  1454291015334141451605245283 / 1237940039285380274899124224

/-
The following definitions mirror the subdivision in the Python certificate.
Rather than store 32768 leaves, the t-interval is computed from the whole
parameter enclosure and a rational subcell index.  Breakpoints are the
Hermite nodes plus the arc endpoints and, for r2, their reflected nodes.
-/

def subcells : ℕ := 512

def arcEndpoints : Kind → List T
  | .r2 => [φ,b]
  | .r3 => [b,halfPi]
  | .r4 => [φ,halfPi]
  | .B => [c,halfPi]
  | .D => [c,halfPi]

def breakpoints (k : Kind) : List T :=
  let ns := (List.range 17).map fun i => nodePosition ⟨i, by omega⟩
  let base := arcEndpoints k ++ ns
  match k with
  | .r2 => base ++ ns.map (fun z => sub halfPi z)
  | _ => base

/-- A cell is accepted only if all parameter/trigonometric interval operations
succeed and the residual square upper endpoint is finite. -/
def cellUpper (k : Kind) (lo hi : T) (j : Fin subcells) : Option ℚ := do
  let L ← lo.intervalValue parameterBox
  let H ← hi.intervalValue parameterBox
  if ¬ L.hi < H.lo then none else
  let a := L.lo + (H.lo-L.lo) * (j.val : ℚ) / subcells
  let b := H.hi + (L.hi-H.hi) * ((subcells-j.val-1 : ℕ) : ℚ) / subcells
  let box : Box3
    | 0 => parameterBox 0
    | 1 => parameterBox 1
    | 2 => ⟨a,b⟩
  let I ← if k = .B && lo = nodePosition 15 && hi = nodePosition 16
    then tailBInterval box
    else (residual k).intervalValue box
  let U := max 0 (max (I.lo*I.lo) (I.hi*I.hi))
  return (b-a) * U

def pieceUpper (k : Kind) (lo hi : T) : Option ℚ := do
  let us ← (List.ofFn fun j : Fin subcells => j).mapM (cellUpper k lo hi)
  return us.sum

/-- Ordered candidate endpoints of each *actual* energy integral.  Finite
indices avoid the unprovable \`by omega\` obligations in maps over Nat.range. -/
def pieceChain : Kind → List T
  | .r2 =>
      (List.ofFn fun i : Fin 16 =>
        nodePosition ⟨i.val,by have hi:=i.isLt; omega⟩) ++ [b]
  | .r3 => [b,halfPi]
  | .r4 => List.ofFn fun i : Fin 17 => nodePosition i
  | .B =>
      List.ofFn fun i : Fin 9 =>
        nodePosition ⟨i.val+8,by have hi:=i.isLt; omega⟩
  | .D =>
      List.ofFn fun i : Fin 9 =>
        nodePosition ⟨i.val+8,by have hi:=i.isLt; omega⟩

/-- The consecutive, non-overlapping intervals.  In particular the r2
chain ends at b=pi/2-phi and r3 starts there: neither integrates over the
other's domain.  Adding reflected nodes as whole extra intervals would double
count the positive integrand, so reflected branch switches are handled by
the sound hull evaluator instead. -/
def retainedPieces (k : Kind) : List (T × T) :=
  (pieceChain k).zip (pieceChain k).tail

def computedUpper (k : Kind) : Option ℚ := do
  let xs ← (retainedPieces k).mapM (fun p => pieceUpper k p.1 p.2)
  return xs.sum

def componentCheck (k : Kind) : Bool :=
  match computedUpper k with
  | none => false
  | some u => decide (u ≤ componentUpper k)

/-- The two closed-form pieces are evaluated directly by interval arithmetic. -/
def scalarCheck : Bool :=
  decide (r1Upper +
    componentUpper .r2 + componentUpper .r3 + componentUpper .r4 +
    componentUpper .B + componentUpper .D + bGapUpper
      ≤ 2 * energyUpper) &&
  decide (energyUpper < 147/125)

def closedCheck : Bool :=
  componentCheck .r2 && componentCheck .r3 && componentCheck .r4 &&
  componentCheck .B && componentCheck .D && scalarCheck



/-- Real parameter vector used by the specialized certificate. -/
def realPoint (P : GerverParams) (u : ℝ) : Fin 3 → ℝ
  | 0 => P.φ | 1 => P.θ | 2 => u

/-- The nested expression selects exactly the same cubic as \`hermiteChain\`.
This is a finite sixteen-piece induction, with the node order supplied by the
committed rational data. -/
theorem hermite_value_semantics {P : GerverParams} (hP : P.IsSolution) (u : ℝ) :
    (chainValueAux 0 t).realValue (realPoint P u) =
      hermiteChain (CriticalTrial.nodes P) u := by
  have hord := CriticalTrial.ordered hP
  unfold chainValueAux
  -- Repeatedly split at the next node; on the selected interval the normalized
  -- cubic is definitionally the Hermite segment used by \`hermiteChain\`.
  repeat'
    first
    | split <;> simp_all [BranchExpr.realValue,TrigExpr.realValue,
        hermiteValue,CriticalTrial.nodes,CriticalTrial.node,CriticalTrial.x,
        HermiteNode.segment,hermite,Cubic.eval]
    | next
  exact rfl

theorem hermite_deriv_semantics {P : GerverParams} (hP : P.IsSolution) (u : ℝ) :
    (chainDerivAux 0 t).realValue (realPoint P u) =
      hermiteChainFirst (CriticalTrial.nodes P) u := by
  have hord := CriticalTrial.ordered hP
  unfold chainDerivAux
  repeat'
    first
    | split <;> simp_all [BranchExpr.realValue,TrigExpr.realValue,
        hermiteDeriv,CriticalTrial.nodes,CriticalTrial.node,CriticalTrial.x,
        HermiteNode.segmentFirst,hermiteFirst,Cubic.first]
    | next
  exact rfl

/-- The encoded Hermite value is the actual fixed trial value.  The proof is
piecewise on the sixteen intervals; all coefficients are the literals in
\`CriticalTrial.node\`. -/
theorem g_real {P : GerverParams} (hP : P.IsSolution) (u : ℝ) :
    (g t).realValue (realPoint P u) = CriticalTrial.g P u := by
  unfold g CriticalTrial.g
  simp only [BranchExpr.realValue,TrigExpr.realValue,realPoint]
  by_cases hu : u ≤ P.φ
  · rw [if_pos hu]
    simp [gapValue,CriticalTrial.q]
  · rw [if_neg hu]
    have hord := CriticalTrial.ordered hP
    exact hermite_value_semantics hP u

theorem dg_real {P : GerverParams} (hP : P.IsSolution) (u : ℝ) :
    (dg t).realValue (realPoint P u) = CriticalTrial.dg P u := by
  unfold dg CriticalTrial.dg
  simp only [BranchExpr.realValue,TrigExpr.realValue,realPoint]
  by_cases hu : u ≤ P.φ
  · rw [if_pos hu]
    simp [gapDeriv,CriticalTrial.q]
  · rw [if_neg hu]
    have hord := CriticalTrial.ordered hP
    exact hermite_deriv_semantics hP u

/-- Each residual expression has exactly the semantics used by the scalar
energy.  Singular endpoints are irrelevant to the interval integral and are
never inverted by a cell that contains them. -/
theorem residual_real {P : GerverParams} (hP : P.IsSolution) (k : Kind)
    {u : ℝ} :
    (residual k).realValue (realPoint P u) =
      match k with
      | .r2 => CriticalTrial.r2 P u
      | .r3 => CriticalTrial.r3 P u
      | .r4 => CriticalTrial.r4 P u
      | .B => CriticalTrial.rB P u
      | .D => CriticalTrial.rD P u := by
  fin_cases k <;>
    simp [residual,r2,r3,r4,rB,rD,BranchExpr.realValue,TrigExpr.realValue,
      realPoint,g_real hP,dg_real hP,CriticalTrial.r2,CriticalTrial.r3,
      CriticalTrial.r4,CriticalTrial.rB,CriticalTrial.rD,
      CriticalTrial.startValue,CriticalTrial.c]

/-- The parameter box contains the actual Gerver parameters at every t. -/
theorem realPoint_in_parameterBox {P : GerverParams} (hbox : P.InBox) (u : ℝ)
    (hu : (parameterBox 2).Contains u) :
    InBox parameterBox (realPoint P u) := by
  intro i
  fin_cases i
  · simpa [parameterBox,realPoint] using hbox.1
  · simpa [parameterBox,realPoint] using hbox.2.1
  · simpa [realPoint] using hu

/-- A checked cell returns its *area contribution*, not its pointwise
residual-square bound.  The distinction is essential: the contribution is
\`(b-a)*M\`, which is generally much smaller than \`M\` for a fine mesh.

The two endpoint inequalities show that the actual, parameter-dependent
mesh subcell is covered by the outward rational interval [a,b]. -/
theorem cellUpper_sound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (k : Kind) (lo hi : T) (j : Fin subcells) {U : ℚ}
    (hc : cellUpper k lo hi j = some U) :
    ∃ a b M : ℚ,
      a ≤ b ∧ 0 ≤ M ∧ U = (b-a)*M ∧
      (a:ℝ) ≤ meshPoint (lo.realValue (realPoint P 0))
        (hi.realValue (realPoint P 0)) subcells j.val ∧
      meshPoint (lo.realValue (realPoint P 0))
        (hi.realValue (realPoint P 0)) subcells (j.val+1) ≤ (b:ℝ) ∧
      ∀ u ∈ Icc (a:ℝ) (b:ℝ),
        (match k with
         | .r2 => CriticalTrial.r2 P u
         | .r3 => CriticalTrial.r3 P u
         | .r4 => CriticalTrial.r4 P u
         | .B => CriticalTrial.rB P u
         | .D => CriticalTrial.rD P u)^2 ≤ (M:ℝ) := by
  unfold cellUpper at hc
  cases hL : lo.intervalValue parameterBox with
  | none => simp [hL] at hc
  | some L =>
    cases hH : hi.intervalValue parameterBox with
    | none => simp [hL,hH] at hc
    | some H =>
      by_cases horder : L.hi < H.lo
      · simp only [hL,hH,if_pos horder,Option.bind_some] at hc
        let a : ℚ := L.lo+(H.lo-L.lo)*(j.val:ℚ)/subcells
        let b : ℚ := H.hi+(L.hi-H.hi)*((subcells-j.val-1:ℕ):ℚ)/subcells
        let box : Box3
          | 0 => parameterBox 0
          | 1 => parameterBox 1
          | 2 => ⟨a,b⟩
        cases hI : (residual k).intervalValue box with
        | none => simp [hI] at hc
        | some I =>
          let M : ℚ := max 0 (max (I.lo*I.lo) (I.hi*I.hi))
          have hparams : InBox parameterBox (realPoint P 0) :=
            realPoint_in_parameterBox hbox 0 (by norm_num [parameterBox,Interval.Contains])
          have hlo := TrigExpr.intervalValue_sound lo hparams hL
          have hhi := TrigExpr.intervalValue_sound hi hparams hH
          have hN : (0:ℚ)<subcells := by norm_num [subcells]
          have hj : (j.val:ℚ)+1 ≤ subcells := by
            exact_mod_cast j.isLt
          have hlen : a ≤ b := by
            dsimp [a,b]
            nlinarith [horder, hlo.1, hlo.2, hhi.1, hhi.2,
              Nat.cast_nonneg (subcells-j.val-1)]
          have hM : 0 ≤ M := by
            dsimp [M]; exact le_max_left _ _
          have hU : U=(b-a)*M := by
            simp only [hI, Option.bind_some, Option.some.injEq] at hc
            simpa only [a,b,M] using hc.symm
          refine ⟨a,b,M,hlen,hM,hU,?_,?_,?_⟩
          · unfold meshPoint
            dsimp [a]
            have hratio : 0 ≤ (j.val:ℝ) / subcells ∧
                (j.val:ℝ) / subcells ≤ 1 := by
              constructor
              · positivity
              · apply (div_le_one (by norm_num [subcells])).2
                exact_mod_cast j.isLt.le
            push_cast
            nlinarith [hlo.1,hhi.1]
          · unfold meshPoint
            dsimp [b]
            have hratio : 0 ≤ ((j.val:ℝ)+1)/subcells ∧
                ((j.val:ℝ)+1)/subcells ≤ 1 := by
              constructor
              · positivity
              · apply (div_le_one (by norm_num [subcells])).2
                exact_mod_cast Nat.succ_le_of_lt j.isLt
            push_cast
            nlinarith [hlo.2,hhi.2]
          · intro u hu
            have hp : InBox box (realPoint P u) := by
              intro i
              fin_cases i
              · simpa [box,realPoint] using hbox.1
              · simpa [box,realPoint] using hbox.2.1
              · simpa [box,realPoint,Interval.Contains] using hu
            have hv := BranchExpr.intervalValue_sound (residual k) hp hI
            rw [residual_real hP] at hv
            have hs : (match k with
                | .r2 => CriticalTrial.r2 P u
                | .r3 => CriticalTrial.r3 P u
                | .r4 => CriticalTrial.r4 P u
                | .B => CriticalTrial.rB P u
                | .D => CriticalTrial.rD P u)^2 ≤
                max 0 (max (I.lo*I.lo) (I.hi*I.hi)) := by
              have hlow:=hv.1
              have hupp:=hv.2
              have hsqlo : (I.lo:ℝ)^2 ≤ M := by
                exact_mod_cast (le_max_of_le_right (le_max_left _ _))
              have hsqhi : (I.hi:ℝ)^2 ≤ M := by
                exact_mod_cast (le_max_of_le_right (le_max_right _ _))
              nlinarith [sq_nonneg ((I.lo:ℝ)-
                (match k
                 | .r2 => CriticalTrial.r2 P u
                 | .r3 => CriticalTrial.r3 P u
                 | .r4 => CriticalTrial.r4 P u
                 | .B => CriticalTrial.rB P u
                 | .D => CriticalTrial.rD P u))]
            simpa only [M] using hs
      · simp [hL,hH,horder] at hc

/-- A monotone list with at least two entries covers the full interval
between its endpoints by its adjacent closed intervals.  This is a
purely order-theoretic cover, not a numerical sampling assertion. -/
private theorem consecutive_interval_cover (xs : List ℝ)
    {a b : ℝ} (hhead : xs.head? = some a)
    (hlast : xs.getLast? = some b)
    (hord : xs.Pairwise (· ≤ ·)) (hlen : 2 ≤ xs.length)
    {u : ℝ} (hu : u ∈ Icc a b) :
    ∃ p ∈ xs.zip xs.tail, u ∈ Icc p.1 p.2 := by
  induction xs using List.twoStepInduction generalizing a b with
  | nil => simp at hlen
  | singleton x => simp at hlen
  | cons_cons x y xs ih₁ ih₂ =>
      have hx : x = a := by simpa using hhead
      subst a
      have hxy : x ≤ y := by
        exact (List.pairwise_cons.mp hord).1 y (by simp)
      by_cases hfirst : u ≤ y
      · refine ⟨(x,y),?_,⟨hu.1,hfirst⟩⟩
        simp [List.zip]
      · cases xs with
        | nil =>
            have hy : b = y := by simpa using hlast.symm
            subst b
            linarith [hu.2,not_le.mp hfirst]
        | cons z zs =>
            have htail : (y :: z :: zs).Pairwise (· ≤ ·) :=
              (List.pairwise_cons.mp hord).2
            have hlast' : (y :: z :: zs).getLast? = some b := by
              simpa using hlast
            have hu' : u ∈ Icc y b := ⟨le_of_lt (not_le.mp hfirst),hu.2⟩
            obtain ⟨p,hp,hup⟩ :=
              ih₂ (by simp) hlast' htail (by simp) hu'
            refine ⟨p,?_,hup⟩
            simp [List.zip,hp]

/-- The endpoint chains represent exactly the reference arc endpoints.
The sole non-node cut is b=pi/2-phi in r2. It lies after node 15
because theta/8 > phi on the Romik parameter box. -/
private theorem pieceChain_geometry {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) (k : Kind) :
    let xs := (pieceChain k).map (fun e => e.realValue (realPoint P 0))
    xs.Pairwise (· ≤ ·) ∧ 2 ≤ xs.length ∧
    xs.head? = some (match k with
      | .r2 | .r4 => P.φ
      | .r3 => π/2-P.φ
      | .B | .D => CriticalTrial.c P) ∧
    xs.getLast? = some (π/2) := by
  have hord := CriticalTrial.ordered hP
  have hpos := CriticalTrial.positions hP
  have hφ := hbox.1
  have hθ := hbox.2.1
  have hcut : CriticalTrial.x P 15 ≤ π/2-P.φ := by
    unfold CriticalTrial.x CriticalTrial.c
    norm_num
    nlinarith [hφ.2,hθ.1,pi_gt_three]
  -- Finite node positions are equal to their TrigExpr encodings.
  have hnode : ∀i : Fin 17,
      (nodePosition i).realValue (realPoint P 0) =
      (CriticalTrial.node P i).position := by
    intro i
    fin_cases i <;>
      norm_num [nodePosition,CriticalTrial.node,CriticalTrial.x,
        CriticalTrial.c,TrigExpr.realValue,realPoint,x,φ,θ,c,halfPi]
  -- The strict ordering of CriticalTrial.nodes is already proved from
  -- phi < c < pi/2. Restriction to subchains preserves it; appending b
  -- uses hcut.
  fin_cases k <;>
    simp [pieceChain,List.map_ofFn,hnode,CriticalTrial.nodes,
      CriticalTrial.node,CriticalTrial.x,CriticalTrial.c,
      OrderedNodes] at * <;>
    first | exact hord | nlinarith [hcut,hpos.1,hpos.2]

/-- The retained intervals cover precisely the intended energy arc.  No
reflected Hermite interval is integrated twice. -/
theorem retained_piece_cover {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) (k : Kind) :
    let I : Set ℝ := match k with
      | .r2 => Icc P.φ (π/2-P.φ)
      | .r3 => Icc (π/2-P.φ) (π/2)
      | .r4 => Icc P.φ (π/2)
      | .B => Icc (CriticalTrial.c P) (π/2)
      | .D => Icc (CriticalTrial.c P) (π/2)
    I ⊆ ⋃ p ∈ retainedPieces k,
      Icc ((p.1.realValue (realPoint P 0)))
        ((p.2.realValue (realPoint P 0))) := by
  dsimp
  intro u hu
  obtain ⟨hord,hlen,hhead,hlast⟩ :=
    pieceChain_geometry hP hbox k
  let xs := (pieceChain k).map (fun e => e.realValue (realPoint P 0))
  have hu' : u ∈ Icc (xs.head!) (xs.getLast!) := by
    dsimp [xs]
    fin_cases k <;> simpa [pieceChain] using hu
  obtain ⟨p,hp,hpu⟩ :=
    consecutive_interval_cover xs hhead hlast hord hlen hu'
  have hpair : xs.zip xs.tail =
      (retainedPieces k).map (fun p =>
        (p.1.realValue (realPoint P 0),p.2.realValue (realPoint P 0))) := by
    dsimp [xs,retainedPieces]
    induction pieceChain k with
    | nil => rfl
    | cons e tail ih =>
        cases tail with
        | nil => rfl
        | cons e' rest => simpa [List.zip] using ih
  rw [hpair] at hp
  obtain ⟨e,he,hpe⟩ := List.mem_map.mp hp
  subst p
  exact Set.mem_iUnion.mpr ⟨e,Set.mem_iUnion.mpr ⟨he,hpu⟩⟩

/-- Extract the checked value for one entry of a successful \`List.mapM\`.
Unlike a bare list-index lemma, the proof keeps the output-list length
equality explicit. -/
private theorem mapM_get_sound {α β : Type*} (f : α → Option β)
    (xs : List α) {ys : List β} (h : xs.mapM f = some ys)
    (i : Fin xs.length) :
    ∃ y : β, f xs[i.val] = some y ∧
      ∃ hi : i.val < ys.length, ys[i.val]'hi = y := by
  induction xs generalizing ys with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
      cases hf : f x with
      | none => simp [hf] at h
      | some y =>
          cases ht : xs.mapM f with
          | none => simp [hf,ht] at h
          | some tail =>
              have hy : ys = y :: tail := by
                simpa [List.mapM,hf,ht] using h.symm
              subst ys
              cases i using Fin.cases with
              | zero =>
                  refine ⟨y,by simpa using hf,by
                    refine ⟨by simp,?_⟩
                    simp⟩
              | succ j =>
                  obtain ⟨z,hz,hi,hget⟩ := ih ht j
                  refine ⟨z,by simpa using hz,by
                    refine ⟨by simpa using hi,?_⟩
                    simpa using hget⟩

/-- Every input element of a successful \`mapM\` has an output witness in
the returned list, even if some input values occur more than once. -/
private theorem mapM_mem_sound {α β : Type*} (f : α → Option β)
    (xs : List α) {ys : List β} (h : xs.mapM f = some ys)
    {x : α} (hx : x ∈ xs) :
    ∃ y : β, f x = some y ∧ y ∈ ys := by
  induction xs generalizing ys with
  | nil => simpa using hx
  | cons a xs ih =>
      cases hf : f a with
      | none => simp [hf] at h
      | some y =>
          cases ht : xs.mapM f with
          | none => simp [hf,ht] at h
          | some tail =>
              have hy : ys = y :: tail := by
                simpa [List.mapM,hf,ht] using h.symm
              subst ys
              rcases List.mem_cons.mp hx with rfl | hx'
              · exact ⟨y,hf,by simp⟩
              · obtain ⟨z,hz,hmem⟩ := ih ht hx'
                exact ⟨z,hz,by simp [hmem]⟩

/-- The finite-cell sum controls the integral over one retained analytic piece.
The interval boxes are outward enclosures, so overlaps only make the upper sum
larger. -/
theorem pieceUpper_sound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (k : Kind) (lo hi : T) {U : ℚ} (hc : pieceUpper k lo hi = some U) :
    let a := lo.realValue (realPoint P 0)
    let b := hi.realValue (realPoint P 0)
    a ≤ b →
    IntervalIntegrable
      (fun u => (match k with
        | .r2 => CriticalTrial.r2 P u
        | .r3 => CriticalTrial.r3 P u
        | .r4 => CriticalTrial.r4 P u
        | .B => CriticalTrial.rB P u
        | .D => CriticalTrial.rD P u)^2) volume a b →
    (∫ u in a..b, (match k with
        | .r2 => CriticalTrial.r2 P u
        | .r3 => CriticalTrial.r3 P u
        | .r4 => CriticalTrial.r4 P u
        | .B => CriticalTrial.rB P u
        | .D => CriticalTrial.rD P u)^2) ≤ U := by
  dsimp
  intro hab hi
  unfold pieceUpper at hc
  cases hcells : (List.ofFn fun j : Fin subcells => j).mapM (cellUpper k lo hi) with
  | none => simp [hcells] at hc
  | some us =>
      have hlen : us.length = subcells := by
        have := List.length_mapM_eq_of_eq_some hcells
        simpa using this
      have hcell : ∀ j : Fin subcells,
          ∃ V : ℚ, us[j] = V ∧
            (∫ u in meshPoint (lo.realValue (realPoint P 0))
                    (hi.realValue (realPoint P 0)) subcells j..
                    meshPoint (lo.realValue (realPoint P 0))
                    (hi.realValue (realPoint P 0)) subcells (j+1),
              (match k with
              | .r2 => CriticalTrial.r2 P u
              | .r3 => CriticalTrial.r3 P u
              | .r4 => CriticalTrial.r4 P u
              | .B => CriticalTrial.rB P u
              | .D => CriticalTrial.rD P u)^2) ≤ V := by
        intro j
        obtain ⟨V,hV,hidx,hget⟩ :=
          mapM_get_sound (cellUpper k lo hi)
            (List.ofFn fun j : Fin subcells => j) hcells
            ⟨j.val,by simp [subcells]⟩
        refine ⟨V,?_,?_⟩
        · simpa [hlen] using hget
        · have hcellValue : cellUpper k lo hi j = some V := by
            simpa only [List.getElem_ofFn] using hV
          obtain ⟨a,b,M,hab',hM,hVU,hleft,hright,hpoint⟩ :=
            cellUpper_sound hP hbox k lo hi j hcellValue
          let l : ℝ := meshPoint (lo.realValue (realPoint P 0))
            (hi.realValue (realPoint P 0)) subcells j.val
          let r : ℝ := meshPoint (lo.realValue (realPoint P 0))
            (hi.realValue (realPoint P 0)) subcells (j.val+1)
          have hnormal : l≤r := meshPoint_mono hab (by norm_num [subcells])
            (Nat.le_succ j.val)
          have hicell := intervalIntegrable_subinterval hi
            (meshPoint_mem hab (by norm_num [subcells]) j.isLt.le).1
            hnormal
            (meshPoint_mem hab (by norm_num [subcells])
              (Nat.succ_le_of_lt j.isLt)).2
          have hcell : ∀u∈Icc l r,
              (match k with
               | .r2 => CriticalTrial.r2 P u
               | .r3 => CriticalTrial.r3 P u
               | .r4 => CriticalTrial.r4 P u
               | .B => CriticalTrial.rB P u
               | .D => CriticalTrial.rD P u)^2 ≤ (M:ℝ) := by
            intro u hu
            exact hpoint u ⟨hleft.trans hu.1,hu.2.trans hright⟩
          have hconst := intervalIntegral.integral_mono_on hnormal hicell
            intervalIntegrable_const hcell
          have hwidth : r-l≤(b:ℝ)-(a:ℝ) := by
            dsimp [l,r] at *
            linarith
          have hvol : (r-l)*(M:ℝ)≤((b:ℝ)-(a:ℝ))*(M:ℝ) :=
            mul_le_mul_of_nonneg_right hwidth (by exact_mod_cast hM)
          have hVUreal : ((b:ℝ)-(a:ℝ))*(M:ℝ)=(V:ℝ) := by
            exact_mod_cast hVU.symm
          calc
            (∫ u in l..r, (match k with
              | .r2 => CriticalTrial.r2 P u
              | .r3 => CriticalTrial.r3 P u
              | .r4 => CriticalTrial.r4 P u
              | .B => CriticalTrial.rB P u
              | .D => CriticalTrial.rD P u)^2)
                ≤ ∫ _u in l..r, (M:ℝ) := hconst
            _ = (r-l)*(M:ℝ) := by simp [intervalIntegral.integral_const]
            _ ≤ ((b:ℝ)-(a:ℝ))*(M:ℝ) := hvol
            _ = V := hVUreal
      have hsplit := intervalIntegral.sum_integral_adjacent_intervals
        (f := fun u => (match k with
          | .r2 => CriticalTrial.r2 P u
          | .r3 => CriticalTrial.r3 P u
          | .r4 => CriticalTrial.r4 P u
          | .B => CriticalTrial.rB P u
          | .D => CriticalTrial.rD P u)^2)
        hi (by norm_num : 0 < subcells)
      simp only [hcells,Option.some.injEq] at hc
      subst U
      rw [hsplit]
      exact Finset.sum_le_sum fun j hj => (hcell j).choose_spec.2

/-- Integrability by residual kind, assembled from the actual five
trial-residual theorems rather than an undeclared generic interface. -/
theorem trial_residual_integrability {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) (k : Kind) :
    match k with
    | .r2 => IntervalIntegrable (fun t => (CriticalTrial.r2 P t)^2)
        volume P.φ (π/2-P.φ)
    | .r3 => IntervalIntegrable (fun t => (CriticalTrial.r3 P t)^2)
        volume (π/2-P.φ) (π/2)
    | .r4 => IntervalIntegrable (fun t => (CriticalTrial.r4 P t)^2)
        volume P.φ (π/2)
    | .B => IntervalIntegrable (fun t => (CriticalTrial.rB P t)^2)
        volume (CriticalTrial.c P) (π/2)
    | .D => IntervalIntegrable (fun t => (CriticalTrial.rD P t)^2)
        volume (CriticalTrial.c P) (π/2) := by
  cases k
  · exact CriticalTrial.trial_residual_integrable_r2 hP hbox
  · exact CriticalTrial.trial_residual_integrable_r3 hP hbox
  · exact CriticalTrial.trial_residual_integrable_r4 hP hbox
  · exact CriticalTrial.trial_residual_integrable_B hP hbox
  · exact CriticalTrial.trial_residual_integrable_D hP hbox

/-- The list zip and scalar endpoint evaluation commute. -/
private theorem chain_zip_map (xs : List T) (g : T → ℝ) :
    (xs.map g).zip (xs.map g).tail =
      (xs.zip xs.tail).map (fun p => (g p.1,g p.2)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      cases xs with
      | nil => rfl
      | cons b rest =>
          simp only [List.map_cons,List.tail_cons,List.zip_cons_cons,
            List.map_cons,ih]

/-- In an ordered chain, every adjacent interval lies inside the full
endpoint interval. -/
private theorem chain_pair_bounds (xs : List ℝ) {a b : ℝ}
    (hord : xs.Pairwise (· ≤ ·))
    (hhead : xs.head? = some a)
    (hlast : xs.getLast? = some b) :
    ∀ p ∈ xs.zip xs.tail, a≤p.1 ∧ p.1≤p.2 ∧ p.2≤b := by
  induction xs generalizing a b with
  | nil =>
      intro p hp
      simp at hp
  | cons x xs ih =>
      have hax : a=x := by simpa using hhead.symm
      subst a
      cases xs with
      | nil =>
          intro p hp
          simp at hp
      | cons y rest =>
          have hxy : x≤y :=
            (List.pairwise_cons.mp hord).1 y (by simp)
          have htail : (y::rest).Pairwise (·≤·) :=
            (List.pairwise_cons.mp hord).2
          have hxb : x≤b := by
            have hfirst : x≤(y::rest).getLast! :=
              List.pairwise_le_getLast hord hlast
            simpa [hlast] using hfirst
          intro p hp
          rcases List.mem_cons.mp (by simpa [List.zip] using hp) with he|ht
          · cases he
            refine ⟨le_rfl,hxy,?_⟩
            exact (List.pairwise_le_getLast htail hlast)
          · obtain ⟨hy,hu,hb⟩ :=
              ih htail (by simp) (by simpa using hlast) p (by simpa using ht)
            exact ⟨hxy.trans hy,hu,hb⟩

/-- A successful mapM of certified piece upper sums bounds the sum of the
corresponding true integrals, including repeated entries if any.  No finite
cover axiom or undeclared external helper is required. -/
private theorem checked_piece_list_sum {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) (k : Kind)
    (ps : List (T × T)) {vs : List ℚ}
    (hcheck : ps.mapM (fun p => pieceUpper k p.1 p.2) = some vs)
    (hpairs : ∀ p ∈ ps,
        let a := p.1.realValue (realPoint P 0)
        let b := p.2.realValue (realPoint P 0)
        a≤b ∧ IntervalIntegrable
          (fun u => (match k with
            | .r2 => CriticalTrial.r2 P u
            | .r3 => CriticalTrial.r3 P u
            | .r4 => CriticalTrial.r4 P u
            | .B => CriticalTrial.rB P u
            | .D => CriticalTrial.rD P u)^2) volume a b) :
    (((ps.map fun p =>
      ∫ u in (p.1.realValue (realPoint P 0))..
        (p.2.realValue (realPoint P 0)),
          (match k with
          | .r2 => CriticalTrial.r2 P u
          | .r3 => CriticalTrial.r3 P u
          | .r4 => CriticalTrial.r4 P u
          | .B => CriticalTrial.rB P u
          | .D => CriticalTrial.rD P u)^2).sum) : ℝ) ≤ vs.sum := by
  induction ps generalizing vs with
  | nil =>
      have hvs : vs=[] := by simpa [List.mapM] using hcheck.symm
      subst vs
      simp
  | cons p ps ih =>
      cases hv : pieceUpper k p.1 p.2 with
      | none => simp [List.mapM,hv] at hcheck
      | some v =>
          cases htail : ps.mapM (fun q => pieceUpper k q.1 q.2) with
          | none => simp [List.mapM,hv,htail] at hcheck
          | some ws =>
              have heq : vs=v::ws := by
                simpa [List.mapM,hv,htail] using hcheck.symm
              subst vs
              obtain ⟨hord,hint⟩ := hpairs p (by simp)
              have hone := pieceUpper_sound hP hbox k p.1 p.2 hv hord hint
              have htailbound := ih htail (fun q hq => hpairs q (by simp [hq]))
              simp only [List.map_cons,List.sum_cons]
              exact add_le_add hone htailbound

/-- Summation over the retained pieces. The exact residual formulas guarantee
integrability; the node cover proves that no portion of the target arc is lost. -/
theorem retained_sum_sound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (k : Kind) {U : ℚ} (hc : computedUpper k = some U) :
    match k with
    | .r2 => arcSquare P.φ (π/2-P.φ) (CriticalTrial.r2 P) ≤ U
    | .r3 => arcSquare (π/2-P.φ) (π/2) (CriticalTrial.r3 P) ≤ U
    | .r4 => arcSquare P.φ (π/2) (CriticalTrial.r4 P) ≤ U
    | .B => arcSquare (CriticalTrial.c P) (π/2) (CriticalTrial.rB P) ≤ U
    | .D => arcSquare (CriticalTrial.c P) (π/2) (CriticalTrial.rD P) ≤ U := by
  classical
  let g : T → ℝ := fun e => e.realValue (realPoint P 0)
  let xs := (pieceChain k).map g
  have hgeometry := pieceChain_geometry hP hbox k
  obtain ⟨hord,hlen,hhead,hlast⟩ := hgeometry
  have hdata := trial_residual_integrability hP hbox k
  let f : ℝ → ℝ := fun t =>
    match k with
    | .r2 => CriticalTrial.r2 P t
    | .r3 => CriticalTrial.r3 P t
    | .r4 => CriticalTrial.r4 P t
    | .B => CriticalTrial.rB P t
    | .D => CriticalTrial.rD P t
  have hintegrable : IntervalIntegrable (fun t => f t^2)
      volume (xs.head!) (xs.getLast!) := by
    fin_cases k <;> simpa [f,xs,pieceChain,g] using hdata
  have hchain := CriticalTrial.arcSquare_chain hintegrable xs hord hhead hlast
  have hpair : xs.zip xs.tail =
      (retainedPieces k).map (fun p => (g p.1,g p.2)) := by
    simpa [xs,retainedPieces] using chain_zip_map (pieceChain k) g
  have hinrange : ∀ p∈retainedPieces k,
      let a:=g p.1
      let b:=g p.2
      (xs.head!)≤a ∧ a≤b ∧ b≤(xs.getLast!) := by
    intro p hp
    have hm : (g p.1,g p.2)∈xs.zip xs.tail := by
      rw [hpair]
      exact List.mem_map.mpr ⟨p,hp,rfl⟩
    exact chain_pair_bounds xs hord hhead hlast _ hm
  have hpairs : ∀ p∈retainedPieces k,
        let a:=g p.1
        let b:=g p.2
        a≤b ∧ IntervalIntegrable (fun u => f u^2) volume a b := by
    intro p hp
    obtain ⟨hla,hab,hbb⟩ := hinrange p hp
    exact ⟨hab,intervalIntegrable_subinterval hintegrable hla hab hbb⟩
  unfold computedUpper at hc
  cases hs : (retainedPieces k).mapM (fun p => pieceUpper k p.1 p.2) with
  | none => simp [hs] at hc
  | some vs =>
      have hv : U=vs.sum := by
        simpa [hs] using hc.symm
      subst U
      have hle := checked_piece_list_sum hP hbox k
        (retainedPieces k) hs (by
          intro p hp
          simpa [f,g] using hpairs p hp)
      have hsums : arcSquare (xs.head!) (xs.getLast!) f =
          ((retainedPieces k).map fun p =>
            ∫ u in (g p.1)..(g p.2),f u^2).sum := by
        rw [hchain,hpair]
        simp only [List.map_map,Function.comp_def,arcSquare]
      fin_cases k <;> simpa [xs,pieceChain,f,g] using
        (hsums.symm.trans_le hle)

/-- Direct interval enclosure of q^2 tan(phi). -/
theorem r1_interval_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    CriticalTrial.q^2*tan P.φ ≤ r1Upper := by
  have hφ := hbox.1
  have hs := CriticalTrial.r1_closed_interval hP hbox
  exact hs.trans (by norm_num [r1Upper])

/-- Direct interval enclosure of the inactive B bridge penalty. -/
theorem bridge_gap_interval_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    CriticalTrial.bridgeSineCoefficient P^2 *
      (tan (CriticalTrial.c P)-tan P.φ) ≤ bGapUpper := by
  have hs := CriticalTrial.bridge_gap_closed_interval hP hbox
  exact hs.trans (by norm_num [bGapUpper])


/-- Summing the accepted cells over every retained analytic piece bounds the
corresponding real integral.  Piece endpoints are exact affine expressions in
phi, theta and pi; \`CriticalTrial.ordered\` proves that the retained list is a
partition of the relevant arc. -/
theorem computedUpper_sound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (k : Kind) {U : ℚ} (hc : computedUpper k = some U) :
    match k with
    | .r2 => arcSquare P.φ (π/2-P.φ) (CriticalTrial.r2 P) ≤ U
    | .r3 => arcSquare (π/2-P.φ) (π/2) (CriticalTrial.r3 P) ≤ U
    | .r4 => arcSquare P.φ (π/2) (CriticalTrial.r4 P) ≤ U
    | .B => arcSquare (CriticalTrial.c P) (π/2) (CriticalTrial.rB P) ≤ U
    | .D => arcSquare (CriticalTrial.c P) (π/2) (CriticalTrial.rD P) ≤ U := by
  exact retained_sum_sound hP hbox k hc

/-- The two non-mesh energy pieces have direct interval enclosures. -/
theorem scalar_closed_parts {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    CriticalTrial.q^2*tan P.φ ≤ r1Upper ∧
    CriticalTrial.bridgeSineCoefficient P^2 *
      (tan (CriticalTrial.c P)-tan P.φ) ≤ bGapUpper := by
  constructor
  · exact r1_interval_bound hP hbox
  · exact bridge_gap_interval_bound hP hbox



/-
Soundness bridge.  The proof follows the same pattern for every retained
piece: interval evaluation bounds r(t)^2 on the whole subcell, then
\`integral_le_mesh_sum\` bounds the integral.  The node-order theorem and the
explicit residual formulas identify the union of retained pieces with the
actual scalar-energy arcs.
-/
theorem componentCheck_sound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (k : Kind) (hc : componentCheck k = true) :
    match k with
    | .r2 => arcSquare P.φ (π/2-P.φ) (CriticalTrial.r2 P) ≤ componentUpper .r2
    | .r3 => arcSquare (π/2-P.φ) (π/2) (CriticalTrial.r3 P) ≤ componentUpper .r3
    | .r4 => arcSquare P.φ (π/2) (CriticalTrial.r4 P) ≤ componentUpper .r4
    | .B => arcSquare (CriticalTrial.c P) (π/2) (CriticalTrial.rB P) ≤ componentUpper .B
    | .D => arcSquare (CriticalTrial.c P) (π/2) (CriticalTrial.rD P) ≤ componentUpper .D := by
  have hparams : InBox parameterBox (fun
      | 0 => P.φ | 1 => P.θ | 2 => 0) := by
    intro i
    fin_cases i
    · exact hbox.1
    · exact hbox.2.1
    · norm_num [parameterBox, Interval.Contains]
  unfold componentCheck at hc
  cases hU : computedUpper k with
  | none => simp [hU] at hc
  | some U =>
      have hreal := computedUpper_sound hP hbox k hU
      have hle : U ≤ componentUpper k := by
        simpa only [hU,decide_eq_true_eq] using hc
      exact hreal.trans (by exact_mod_cast hle)

/-- The exact scalar trial energy is below 147/125 on the entire parameter box. -/
theorem energy_lt_147_125 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (hclosed : closedCheck = true) :
    CriticalTrial.scalarEnergy P < 147/125 := by
  have hc : ∀ k : Kind, componentCheck k = true := by
    intro k
    fin_cases k <;> simpa [closedCheck] using hclosed
  have h2 := componentCheck_sound hP hbox .r2 (hc .r2)
  have h3 := componentCheck_sound hP hbox .r3 (hc .r3)
  have h4 := componentCheck_sound hP hbox .r4 (hc .r4)
  have hB := componentCheck_sound hP hbox .B (hc .B)
  have hD := componentCheck_sound hP hbox .D (hc .D)
  obtain ⟨h1,hgap⟩ := scalar_closed_parts hP hbox
  have hsum : r1Upper + componentUpper .r2 + componentUpper .r3 +
      componentUpper .r4 + componentUpper .B + componentUpper .D + bGapUpper
      ≤ 2*energyUpper := by
    have := hclosed
    simp only [closedCheck,scalarCheck,Bool.and_eq_true,decide_eq_true_eq] at this
    exact this.2.1
  have hup : energyUpper < 147/125 := by
    norm_num [energyUpper]
  unfold CriticalTrial.scalarEnergy
  nlinarith only [h1,h2,h3,h4,hB,hD,hgap,hsum,hup]

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem closed_reduction : closedCheck = true := by
  decide

/-- Closed energy certificate for the concrete feasible critical trial. -/
theorem critical_trial_energy_lt_147_125 {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    CriticalTrial.trialEnergy (CriticalTrial.profile hP) (CriticalTrial.c P) < 147/125 := by
  have hφ := GerverParams.gm_φ_mem_Ioo hP hbox
  have hiB := ((rightAuxiliary_data hP hbox
    (wideGerverTriple hP hbox)).2.2.2.1)
  have hiD := ((leftAuxiliary_data hP hbox
    (wideGerverTriple hP hbox)).2.2.2.1)
  rw [CriticalTrial.trialEnergy_eq_scalar hP hbox hiB hiD]
  exact energy_lt_147_125 hP hbox closed_reduction

end CriticalTrialCertificate
end MovingSofaQuantitative
