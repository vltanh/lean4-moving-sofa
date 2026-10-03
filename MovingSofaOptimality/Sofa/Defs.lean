module

public import MovingSofaOptimality.Basic.SurfaceArea
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Hallways, moving sofas and their rotation angle

Definitions 1.1.1 (`def:hallway`), 1.1.2 (`def:moving-sofa`), 2.2.1–2.2.3 (hallway parts and the
supporting hallway), 2.3.1–2.3.11 (strips, rotation angle, standard position, the parallelogram
`P_ω`, the monotonization `𝓘(S)`, monotone sofas, the set `𝓒(S)`, `J_ω`).

**Rigid motions.** The paper moves a sofa by a continuous curve `Φ_t ∈ SE(2)`, `t ∈ [0, 1]`, with
`Φ_0` a translation. We write `Φ_t(p) = R_{θ(t)} p + c(t)` with a continuous angle `θ` and a
continuous translation `c`; by path lifting in `SO(2)`, every continuous curve in `SE(2)` has this
form. The *rotation angle* of the movement is the clockwise angle `ω = θ(0) - θ(1)`; we normalise
`θ(0) = 0`.
-/

@[expose] public section

open Real Set

namespace MovingSofaOptimality

/-! ### The hallway (Definition 1.1.1) -/

/-- The horizontal side `H_L = (-∞, 1] × [0, 1]` of the hallway. -/
def horizSide : Set (ℝ × ℝ) := {p | p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}

/-- The vertical side `V_L = [0, 1] × (-∞, 1]` of the hallway. -/
def vertSide : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 ≤ 1}

/-- The hallway `L = H_L ∪ V_L` (Definition 1.1.1, `def:hallway`). -/
def hallway : Set (ℝ × ℝ) := horizSide ∪ vertSide

/-! ### Moving sofas (Definition 1.1.2) and their rotation angle (Definition 2.3.3) -/

/-- A movement of `S` inside the hallway with clockwise rotation angle `ω`: a continuous rigid
motion `Φ_s(p) = R_{θ(s)} p + c(s)`, `s ∈ [0, 1]`, with `Φ_0` a translation taking `S` into `H_L`,
every `Φ_s` taking `S` into `L`, and `Φ_1` taking `S` into `V_L`. -/
structure IsMovement (S : Set (ℝ × ℝ)) (ω : ℝ) (θ : ℝ → ℝ) (c : ℝ → ℝ × ℝ) : Prop where
  continuousOn_angle : ContinuousOn θ (Icc 0 1)
  continuousOn_shift : ContinuousOn c (Icc 0 1)
  angle_zero : θ 0 = 0
  angle_one : θ 1 = -ω
  start : ∀ p ∈ S, rot (θ 0) p + c 0 ∈ horizSide
  inside : ∀ s ∈ Icc (0 : ℝ) 1, ∀ p ∈ S, rot (θ s) p + c s ∈ hallway
  finish : ∀ p ∈ S, rot (θ 1) p + c 1 ∈ vertSide

/-- `S` is a moving sofa admitting a movement with rotation angle `ω`
(Definitions 1.1.2 and 2.3.3, `def:moving-sofa`, `def:rotation-angle`). -/
def IsMovingSofaWithAngle (S : Set (ℝ × ℝ)) (ω : ℝ) : Prop :=
  IsClosed S ∧ IsConnected S ∧ ∃ θ c, IsMovement S ω θ c

/-- A moving sofa (Definition 1.1.2, `def:moving-sofa`): a nonempty, connected and closed set that
can be moved inside `L` by a continuous rigid motion from `H_L` to `V_L`. -/
def IsMovingSofa (S : Set (ℝ × ℝ)) : Prop := ∃ ω, IsMovingSofaWithAngle S ω

/-! ### Strips, standard position and the parallelogram (§2.3) -/

/-- The horizontal strip `H = ℝ × [0, 1]` (Definition 2.3.2, `def:strips`). -/
def hStrip : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ 1}

/-- The vertical strip `V = [0, 1] × ℝ` (Definition 2.3.2). -/
def vStrip : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1}

/-- The rotated vertical strip `V_ω = R_ω(V)` (Definition 2.3.2). -/
def vStripRot (ω : ℝ) : Set (ℝ × ℝ) := rot ω '' vStrip

/-- A moving sofa with rotation angle `ω ∈ (0, π/2]` is in standard position if
`h_S(ω) = h_S(π/2) = 1` (Definition 2.3.4, `def:standard-position`). -/
def IsStandardPosition (S : Set (ℝ × ℝ)) (ω : ℝ) : Prop := supp S ω = 1 ∧ supp S (π / 2) = 1

/-- The parallelogram `P_ω = H ∩ V_ω` (Definition 2.3.5, `def:parallelogram`). -/
def para (ω : ℝ) : Set (ℝ × ℝ) := hStrip ∩ vStripRot ω

/-- The upper right vertex `o_ω = (tan(π/4 - ω/2), 1)` of `P_ω` (Definition 2.3.5). -/
noncomputable def oPt (ω : ℝ) : ℝ × ℝ := (tan (π / 4 - ω / 2), 1)

/-! ### Parts of the hallway and the supporting hallway (§2.2) -/

/-- The inner corner `x_L = (0, 0)` (Definition 2.2.1, `def:hallway-parts`). -/
def xL : ℝ × ℝ := (0, 0)
/-- The outer corner `y_L = (1, 1)`. -/
def yL : ℝ × ℝ := (1, 1)
/-- The outer wall `a_L : x = 1`. -/
def aL : Set (ℝ × ℝ) := {p | p.1 = 1}
/-- The outer wall `c_L : y = 1`. -/
def cL : Set (ℝ × ℝ) := {p | p.2 = 1}
/-- The inner wall `b⃗_L = {0} × (-∞, 0]`. -/
def bVecL : Set (ℝ × ℝ) := {p | p.1 = 0 ∧ p.2 ≤ 0}
/-- The inner wall `d⃗_L = (-∞, 0] × {0}`. -/
def dVecL : Set (ℝ × ℝ) := {p | p.2 = 0 ∧ p.1 ≤ 0}
/-- The line `b_L : x = 0`. -/
def bL : Set (ℝ × ℝ) := {p | p.1 = 0}
/-- The line `d_L : y = 0`. -/
def dL : Set (ℝ × ℝ) := {p | p.2 = 0}
/-- The closed quarter-plane `Q_L⁺ = (-∞, 1]²`. -/
def qPlusL : Set (ℝ × ℝ) := {p | p.1 ≤ 1 ∧ p.2 ≤ 1}
/-- The open quarter-plane `Q_L⁻ = (-∞, 0)²`. -/
def qMinusL : Set (ℝ × ℝ) := {p | p.1 < 0 ∧ p.2 < 0}

/-- The rigid motion `f_{S,t}(p) = R_t(p) + (h_S(t) - 1) u_t + (h_S(t + π/2) - 1) v_t`
(Definition 2.2.2, `def:tangent-hallway`). -/
noncomputable def hallwayMap (S : Set (ℝ × ℝ)) (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  rot t p + (supp S t - 1) • uvec t + (supp S (t + π / 2) - 1) • vvec t

/-- The supporting hallway `L_S(t) = f_{S,t}(L)` (Definition 2.2.2). -/
def suppHallway (S : Set (ℝ × ℝ)) (t : ℝ) : Set (ℝ × ℝ) := hallwayMap S t '' hallway

/-- The inner corner `x_S(t) = f_{S,t}(x_L)` (Definition 2.2.3, `def:rotating-hallway-parts`). -/
noncomputable def innerCorner (S : Set (ℝ × ℝ)) (t : ℝ) : ℝ × ℝ := hallwayMap S t xL
/-- The outer corner `y_S(t) = f_{S,t}(y_L)`. -/
noncomputable def outerCorner (S : Set (ℝ × ℝ)) (t : ℝ) : ℝ × ℝ := hallwayMap S t yL
/-- The outer wall `a_S(t) = f_{S,t}(a_L)`. -/
def wallA (S : Set (ℝ × ℝ)) (t : ℝ) : Set (ℝ × ℝ) := hallwayMap S t '' aL
/-- The inner wall line `b_S(t) = f_{S,t}(b_L)`. -/
def wallB (S : Set (ℝ × ℝ)) (t : ℝ) : Set (ℝ × ℝ) := hallwayMap S t '' bL
/-- The outer wall `c_S(t) = f_{S,t}(c_L)`. -/
def wallC (S : Set (ℝ × ℝ)) (t : ℝ) : Set (ℝ × ℝ) := hallwayMap S t '' cL
/-- The inner wall line `d_S(t) = f_{S,t}(d_L)`. -/
def wallD (S : Set (ℝ × ℝ)) (t : ℝ) : Set (ℝ × ℝ) := hallwayMap S t '' dL
/-- The inner half-line wall `b⃗_S(t) = f_{S,t}(b⃗_L)`. -/
def wallBVec (S : Set (ℝ × ℝ)) (t : ℝ) : Set (ℝ × ℝ) := hallwayMap S t '' bVecL
/-- The inner half-line wall `d⃗_S(t) = f_{S,t}(d⃗_L)`. -/
def wallDVec (S : Set (ℝ × ℝ)) (t : ℝ) : Set (ℝ × ℝ) := hallwayMap S t '' dVecL
/-- The closed quarter-plane `Q_S⁺(t) = f_{S,t}(Q_L⁺)`. -/
def qPlus (S : Set (ℝ × ℝ)) (t : ℝ) : Set (ℝ × ℝ) := hallwayMap S t '' qPlusL
/-- The open quarter-plane `Q_S⁻(t) = f_{S,t}(Q_L⁻)`. -/
def qMinus (S : Set (ℝ × ℝ)) (t : ℝ) : Set (ℝ × ℝ) := hallwayMap S t '' qMinusL

/-! ### Monotone sofas (§2.3) -/

/-- The intersection `𝓘(S) = P_ω ∩ ⋂_{t ∈ [0, ω]} L_S(t)` (Definition 2.3.6, `def:monotonization`). -/
def monotonization (S : Set (ℝ × ℝ)) (ω : ℝ) : Set (ℝ × ℝ) :=
  para ω ∩ ⋂ t ∈ Icc 0 ω, suppHallway S t

/-- A monotone sofa with rotation angle `ω ∈ (0, π/2]`: the intersection `𝓘(S')` of some moving sofa
`S'` with rotation angle `ω` in standard position (Definition 2.3.7, `def:monotone-sofa`). -/
def IsMonotoneSofa (S : Set (ℝ × ℝ)) (ω : ℝ) : Prop :=
  ω ∈ Ioc 0 (π / 2) ∧ ∃ S', IsMovingSofaWithAngle S' ω ∧ IsStandardPosition S' ω ∧
    S = monotonization S' ω

/-- `X` is closed in the direction of `v` (Definition 2.3.8, `def:closed-in-direction`). -/
def ClosedInDirection (X : Set (ℝ × ℝ)) (v : ℝ × ℝ) : Prop :=
  ∀ x ∈ X, ∀ c : ℝ, 0 ≤ c → x + c • v ∈ X

/-- The left side of a line `l(t, h)` that is not parallel to the `x`-axis: the closed half-plane
bounded by it containing `-N u_0` for large `N` (Definition 2.3.9, `def:line-half-plane-directions`;
the paper says "`y`-axis", but `±N u_0` lie on the same side of a horizontal line). -/
def leftSide (t h : ℝ) : Set (ℝ × ℝ) := if 0 < cos t then halfMinus t h else halfPlus t h

/-- The right side of a line `l(t, h)` not parallel to the `x`-axis (Definition 2.3.9). -/
def rightSide (t h : ℝ) : Set (ℝ × ℝ) := if 0 < cos t then halfPlus t h else halfMinus t h

/-- The convex set `𝓒(S) = P_ω ∩ ⋂_{t ∈ [0, ω]} Q_S⁺(t)` (Definition 2.3.10, `def:cap-sofa`). -/
def capOf (S : Set (ℝ × ℝ)) (ω : ℝ) : Set (ℝ × ℝ) := para ω ∩ ⋂ t ∈ Icc 0 ω, qPlus S t

/-- The set `J_ω = [0, ω] ∪ [π/2, ω + π/2]` (Definition 2.3.11, `def:set-j`). -/
def jSet (ω : ℝ) : Set ℝ := Icc 0 ω ∪ Icc (π / 2) (ω + π / 2)

end MovingSofaOptimality
