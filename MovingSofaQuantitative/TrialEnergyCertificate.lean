module

public import MovingSofaQuantitative.TrialResidualFormulas
public import MovingSofaQuantitative.Certificates.IntegralMesh

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
  let I ← (residual k).intervalValue box
  let U := max 0 (max (I.lo*I.lo) (I.hi*I.hi))
  return (b-a) * U

def pieceUpper (k : Kind) (lo hi : T) : Option ℚ := do
  let us ← (List.ofFn fun j : Fin subcells => j).mapM (cellUpper k lo hi)
  return us.sum

/-- Sort-free retained piece list.  The exact order is proved below from the
node formulas; duplicated/non-overlapping candidates contribute zero only after
their order has been certified. -/
def retainedPieces (k : Kind) : List (T × T) :=
  match k with
  | .r2 =>
      (List.range 16).map (fun i => (nodePosition ⟨i,by omega⟩,
        nodePosition ⟨i+1,by omega⟩)) ++
      (List.range 16).map (fun i => (sub halfPi (nodePosition ⟨i+1,by omega⟩),
        sub halfPi (nodePosition ⟨i,by omega⟩)))
  | .r3 => (List.range 16).map (fun i => (nodePosition ⟨i,by omega⟩,
      nodePosition ⟨i+1,by omega⟩))
  | .r4 => (List.range 16).map (fun i => (nodePosition ⟨i,by omega⟩,
      nodePosition ⟨i+1,by omega⟩))
  | .B => (List.range 8).map (fun i => (nodePosition ⟨i+8,by omega⟩,
      nodePosition ⟨i+9,by omega⟩))
  | .D => (List.range 8).map (fun i => (nodePosition ⟨i+8,by omega⟩,
      nodePosition ⟨i+9,by omega⟩))

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
    exact CriticalTrial.hermite_expr_value_eq hP hord u

theorem dg_real {P : GerverParams} (hP : P.IsSolution) (u : ℝ) :
    (dg t).realValue (realPoint P u) = CriticalTrial.dg P u := by
  unfold dg CriticalTrial.dg
  simp only [BranchExpr.realValue,TrigExpr.realValue,realPoint]
  by_cases hu : u ≤ P.φ
  · rw [if_pos hu]
    simp [gapDeriv,CriticalTrial.q]
  · rw [if_neg hu]
    have hord := CriticalTrial.ordered hP
    exact CriticalTrial.hermite_expr_deriv_eq hP hord u

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

/-- One certified t-cell bounds the real squared residual on that entire
cell.  This is the local soundness statement needed by the integral sum. -/
theorem cellUpper_sound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (k : Kind) (lo hi : T) (j : Fin subcells) {U : ℚ}
    (hc : cellUpper k lo hi j = some U) :
    ∃ a b : ℝ, a ≤ b ∧
      (∀ u ∈ Icc a b,
        (match k with
        | .r2 => CriticalTrial.r2 P u
        | .r3 => CriticalTrial.r3 P u
        | .r4 => CriticalTrial.r4 P u
        | .B => CriticalTrial.rB P u
        | .D => CriticalTrial.rD P u)^2 ≤ U) := by
  unfold cellUpper at hc
  cases hL : lo.intervalValue parameterBox with
  | none => simp [hL] at hc
  | some L =>
    cases hH : hi.intervalValue parameterBox with
    | none => simp [hL,hH] at hc
    | some H =>
      split at hc <;> try contradiction
      let a : ℝ := L.lo + (H.lo-L.lo)*(j.val:ℚ)/subcells
      let b : ℝ := H.hi + (L.hi-H.hi)*((subcells-j.val-1:ℕ):ℚ)/subcells
      let box : Box3
        | 0 => parameterBox 0
        | 1 => parameterBox 1
        | 2 => ⟨a,b⟩
      cases hI : (residual k).intervalValue box with
      | none => simp [hL,hH,hI] at hc
      | some I =>
        refine ⟨a,b,?_,?_⟩
        · exact_mod_cast show
            L.lo + (H.lo-L.lo)*(j.val:ℚ)/subcells ≤
            H.hi + (L.hi-H.hi)*((subcells-j.val-1:ℕ):ℚ)/subcells by
              nlinarith
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
            have hlo := hv.1
            have hhi := hv.2
            rcases le_total 0 (match k with
              | .r2 => CriticalTrial.r2 P u
              | .r3 => CriticalTrial.r3 P u
              | .r4 => CriticalTrial.r4 P u
              | .B => CriticalTrial.rB P u
              | .D => CriticalTrial.rD P u) with hp | hn
            · exact_mod_cast (sq_le_sq₀ hp (hhi.trans (by exact_mod_cast
                le_max_right (I.lo*I.lo) (I.hi*I.hi)))).2
            · have hh := neg_le_neg hlo
              nlinarith [sq_nonneg (match k with
                | .r2 => CriticalTrial.r2 P u
                | .r3 => CriticalTrial.r3 P u
                | .r4 => CriticalTrial.r4 P u
                | .B => CriticalTrial.rB P u
                | .D => CriticalTrial.rD P u)]
          simp only [Option.some.injEq] at hc
          subst U
          nlinarith

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
  have hord := CriticalTrial.ordered hP
  have hpartition := CriticalTrial.retained_piece_partition hP k
  unfold computedUpper at hc
  exact CriticalTrial.integral_le_retained_cell_sum hP hbox k hord hpartition
    (fun lo hi j V hV => cellUpper_sound hP hbox k lo hi j hV) hc

/-- The two non-mesh energy pieces have direct interval enclosures. -/
theorem scalar_closed_parts {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    CriticalTrial.q^2*tan P.φ ≤ r1Upper ∧
    CriticalTrial.bridgeSineCoefficient P^2 *
      (tan (CriticalTrial.c P)-tan P.φ) ≤ bGapUpper := by
  constructor
  · exact CriticalTrial.r1_interval_bound hP hbox
  · exact CriticalTrial.bridge_gap_interval_bound hP hbox


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
