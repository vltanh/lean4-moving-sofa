module

public import MovingSofaQuantitative.StableGram
public import MovingSofaQuantitative.Certificates.BranchExpression

/-!
# Symbolic expressions for the actual continuum kernel Gram entries

Uncompiled proof source. The real interpretation of the generated expression
is proved equal to `stableEvaluationGram`. Arc selection and changing piece
overlaps are represented by checked branches, not by a sampled choice. The
last/last entry is the nonsingular formula from StableGram.
-/

@[expose] public section

open Real Set

namespace MovingSofaQuantitative.Certificates

namespace KernelExpression

variable {n : ℕ}

abbrev T := TrigExpr n
abbrev B := BranchExpr n

def rat (q : ℚ) : T := .rational q
def sub (a b : T) : T := .add a (.neg b)
def div (a b : T) : T := .mul a (.inv b)
def sec (a : T) : T := .inv (.cos a)
def csc (a : T) : T := .inv (.sin a)
def tan (a : T) : T := div (.sin a) (.cos a)
def cot (a : T) : T := div (.cos a) (.sin a)
def halfPi : T := div .pi (rat 2)
def bsub (a b : B) : B := .add a (.neg b)
def bdiv (a b : B) : B := .mul a (.inv b)
def lift (a : T) : B := .atom a

def sum : List B → B
  | [] => lift (rat 0)
  | e :: es => .add e (sum es)

theorem sum_real (x : Fin n → ℝ) (es : List B) :
    (sum es).realValue x = (es.map (BranchExpr.realValue x)).sum := by
  induction es with
  | nil => simp [sum, lift, rat, BranchExpr.realValue, TrigExpr.realValue]
  | cons e es ih => simp [sum, BranchExpr.realValue, ih]

structure Piece (n : ℕ) where
  component : Fin 4
  lo : TrigExpr n
  hi : TrigExpr n
  a : TrigExpr n
  b : TrigExpr n

noncomputable def Piece.realValue (x : Fin n → ℝ) (p : Piece n) : KernelPiece :=
  ⟨p.component, p.lo.realValue x, p.hi.realValue x, p.a.realValue x, p.b.realValue x⟩

/-- A primitive expression on an overlap; the overlap order is checked outside. -/
def crossPrimitive (φ : T) (p q : Piece n) (a b : T) : T :=
  if p.component = 0 then .mul (.mul p.a q.a) (sub (tan b) (tan a))
  else if p.component = 1 then .mul (.mul p.a q.a) (sub b a)
  else if p.component = 2 then
    .mul (.mul p.a q.a) (sub (cot (sub (sub .pi φ) b)) (cot (sub (sub .pi φ) a)))
  else
    .add (.add
      (.mul (.mul p.a q.a) (sub (cot a) (cot b)))
      (.mul (.add (.mul p.a q.b) (.mul p.b q.a)) (sub (csc a) (csc b))))
      (.mul (.mul p.b q.b) (sub (sub (cot a) (cot b)) (sub b a)))

def cross (φ : T) (p q : Piece n) : B :=
  if p.component = q.component then
    .iteLE (.max p.lo q.lo) (.min p.hi q.hi)
      (lift (crossPrimitive φ p q (.max p.lo q.lo) (.min p.hi q.hi)))
      (lift (rat 0))
  else lift (rat 0)

theorem crossPrimitive_real (x : Fin n → ℝ) (φ : T) (p q : Piece n) (a b : T) :
    (crossPrimitive φ p q a b).realValue x =
      KernelPiece.crossPrimitive (φ.realValue x) (p.realValue x) (q.realValue x)
        (a.realValue x) (b.realValue x) := by
  unfold crossPrimitive KernelPiece.crossPrimitive Piece.realValue
  split_ifs <;>
    simp [sub, div, tan, cot, csc, TrigExpr.realValue, MovingSofaStability.cotangent,
      Real.tan_eq_sin_div_cos, one_div] <;> ring

theorem cross_real (x : Fin n → ℝ) (φ : T) (p q : Piece n) :
    (cross φ p q).realValue x = (p.realValue x).cross (φ.realValue x) (q.realValue x) := by
  unfold cross KernelPiece.cross
  simp only [Piece.realValue]
  split_ifs
  · simp only [BranchExpr.realValue, TrigExpr.realValue, lift, rat, crossPrimitive_real]
  · rfl

/-- Piece patterns; index 4 is the zero terminal endpoint. -/
def pieces (φ t : T) (kind : Fin 5) : List (Piece n) :=
  let A := sec φ
  let v := halfPi
  let b := sub v φ
  let T := sub .pi φ
  match kind with
  | 0 =>
      [⟨0, t, φ, .cos t, rat 0⟩,
       ⟨1, φ, b, .mul (.cos t) A, rat 0⟩,
       ⟨2, b, v, .mul (.cos t) A, rat 0⟩,
       ⟨3, v, .add v φ, .mul (.mul (.cos t) A) (sub A (.sin φ)), rat 0⟩,
       ⟨3, .add v φ, T, .mul (.cos t) (.pow A 2), .mul (.cos t) A⟩]
  | 1 =>
      [⟨1, t, b, rat 1, rat 0⟩,
       ⟨2, b, v, rat 1, rat 0⟩,
       ⟨3, v, .add v t, sub A (.sin t), rat 0⟩,
       ⟨3, .add v t, T, A, rat 1⟩]
  | 2 =>
      [⟨2, t, v, .sin (sub T t), rat 0⟩,
       ⟨3, v, T, .mul (div (.cos t) (.cos φ)) (.sin φ), rat 0⟩]
  | 3 => [⟨3, v, t, .neg (.sin t), rat 0⟩]
  | 4 => []

/-- Arc decisions agree with the actual evaluation kernel, including pi. -/
def choose (φ t : T) (body : List (Piece n) → B) : B :=
  .iteLE t φ (body (pieces φ t 0))
    (.iteLE t (sub halfPi φ) (body (pieces φ t 1))
      (.iteLE t halfPi (body (pieces φ t 2))
        (.iteLE .pi t (body []) (body (pieces φ t 3)))))

theorem choose_real (x : Fin n → ℝ) (φ t : T) (body : List (Piece n) → B)
    (f : List KernelPiece → ℝ)
    (hbody : ∀ ps, (body ps).realValue x = f (ps.map (Piece.realValue x))) :
    (choose φ t body).realValue x = f (evaluationPieces (φ.realValue x) (t.realValue x)) := by
  unfold choose evaluationPieces
  simp only [BranchExpr.realValue, sub, halfPi, div, rat, TrigExpr.realValue]
  split_ifs <;>
    simp only [hbody, pieces, List.map_cons, List.map_nil, Piece.realValue,
      sec, halfPi, sub, div, rat, TrigExpr.realValue]
  all_goals first | rfl | (exfalso; linarith)

def pieceGram (φ : T) (ps qs : List (Piece n)) : B :=
  sum (ps.map fun p => sum (qs.map fun q => cross φ p q))

theorem pieceGram_real (x : Fin n → ℝ) (φ : T) (ps qs : List (Piece n)) :
    (pieceGram φ ps qs).realValue x =
      ((ps.map (Piece.realValue x)).map fun p =>
        ((qs.map (Piece.realValue x)).map fun q => p.cross (φ.realValue x) q).sum).sum := by
  simp only [pieceGram, sum_real, List.map_map, cross_real]

/-- The generic non-last/last primitive expression. -/
def ordinaryGram (φ t u : T) : B :=
  choose φ t (fun ps => choose φ u (fun qs => pieceGram φ ps qs))

theorem ordinaryGram_real (x : Fin n → ℝ) (φ t u : T) :
    (ordinaryGram φ t u).realValue x =
      evaluationPieceGram (φ.realValue x) (t.realValue x) (u.realValue x) := by
  unfold ordinaryGram evaluationPieceGram
  apply choose_real
  intro ps
  apply choose_real
  intro qs
  exact pieceGram_real x φ ps qs

/-- The stable last/last formula avoids evaluating reciprocal sine at pi. -/
def gram (φ t u : T) : B :=
  let ordinary := ordinaryGram φ t u
  let last := lift (.mul (.neg (.sin (.max t u))) (.cos (.min t u)))
  .iteLE halfPi t (.iteLE halfPi u last ordinary) ordinary

theorem gram_real (x : Fin n → ℝ) (φ t u : T) :
    (gram φ t u).realValue x =
      stableEvaluationGram (φ.realValue x) (t.realValue x) (u.realValue x) := by
  unfold gram stableEvaluationGram
  simp only [BranchExpr.realValue, halfPi, div, rat, TrigExpr.realValue,
    lift, ordinaryGram_real]
  split_ifs <;> simp_all

/-- Coefficient-weighted finite Gram entry. -/
def combinationGram (φ : T) (ps qs : List (T × T)) : B :=
  sum (ps.map fun p => sum (qs.map fun q =>
    .mul (lift (.mul p.2 q.2)) (gram φ p.1 q.1)))

noncomputable def realCombinationGram (φ : ℝ) (ps qs : List (ℝ × ℝ)) : ℝ :=
  (ps.map fun p => (qs.map fun q => p.2 * q.2 * stableEvaluationGram φ p.1 q.1).sum).sum

theorem combinationGram_real (x : Fin n → ℝ) (φ : T) (ps qs : List (T × T)) :
    (combinationGram φ ps qs).realValue x = realCombinationGram (φ.realValue x)
      (ps.map fun p => (p.1.realValue x, p.2.realValue x))
      (qs.map fun q => (q.1.realValue x, q.2.realValue x)) := by
  simp only [combinationGram, realCombinationGram, sum_real, List.map_map,
    BranchExpr.realValue, lift, TrigExpr.realValue, gram_real]

end KernelExpression
end MovingSofaQuantitative.Certificates
