# Definitions

[Back to the README](../README.md)

Read these before trusting the results: Lean's kernel checks the proofs, not that the statements mean
what you intend. The statements of record, in [`Challenge.lean`](../Challenge.lean), use only Mathlib and the
definitions below, which [`Challenge.lean`](../Challenge.lean) copies verbatim from [`ChallengeDefs.lean`](../ChallengeDefs.lean); the
bridge library and [`Solution.lean`](../Solution.lean) use the same constants, and [`Solution.lean`](../Solution.lean) proves that the definitions of the
optimality library, which the uniqueness library uses too, agree with them. There are two sets of definitions, each in its
own namespace: those of Baek's paper, `Baek`, and those of Google DeepMind's formal-conjectures,
`FormalConjectures.MovingSofa`. The bridge theorems ([Results](results.md#the-bridge)) show that they describe
the same objects.

## Baek's definitions

### The plane and the hallway

The plane is `ℝ × ℝ`, and the area of a set is its Lebesgue measure `volume`. `rot t` is the
counterclockwise rotation by `t`. The hallway `L = H_L ∪ V_L` is the union of its horizontal side
`H_L = (-∞, 1] × [0, 1]` and its vertical side `V_L = [0, 1] × (-∞, 1]`:

```lean
noncomputable def rot (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (cos t * p.1 - sin t * p.2, sin t * p.1 + cos t * p.2)

def horizSide : Set (ℝ × ℝ) := {p | p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}
def vertSide : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 ≤ 1}
def hallway : Set (ℝ × ℝ) := horizSide ∪ vertSide
```

### Moving sofas

A moving sofa is a closed, connected (hence nonempty) set that a continuous rigid motion carries from
the horizontal side to the vertical side without leaving the hallway:

```lean
def IsMovingSofa (S : Set (ℝ × ℝ)) : Prop :=
  IsClosed S ∧ IsConnected S ∧
    ∃ (θ : ℝ → ℝ) (c : ℝ → ℝ × ℝ), ContinuousOn θ (Icc 0 1) ∧ ContinuousOn c (Icc 0 1) ∧
      θ 0 = 0 ∧ (∀ p ∈ S, rot (θ 0) p + c 0 ∈ horizSide) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ p ∈ S, rot (θ s) p + c s ∈ hallway) ∧
      (∀ p ∈ S, rot (θ 1) p + c 1 ∈ vertSide)
```

At time `s` the motion is `Φ_s(p) = R_{θ(s)} p + c(s)`. The angle starts at `0`, so `Φ_0` is a
translation: the set may start anywhere, and only its translate by `c(0)` must lie in `H_L`. This is
Baek's Definition 1.1.2, where the motion is a continuous curve in the group of orientation-preserving
isometries starting at a translation; any such curve has this form, by lifting its rotation part to
a continuous angle.

### Gerver's sofa

Gerver's sofa is defined by Romik's description of it (*Differential equations and exact solutions in
the moving sofa problem*, 2018). Seen from the sofa, the hallway turns by `t ∈ [0, π/2]` around it,
and its inner corner follows the *rotation path* `𝐱(t)`. The sofa is the *shape* of the path: the set
of points that lie in the horizontal side and in every moved hallway, and in the vertical side at the
end (Romik's Equation (8)):

```lean
def shapeOfPath (x : ℝ → ℝ × ℝ) : Set (ℝ × ℝ) :=
  horizSide ∩ (⋂ t ∈ Icc 0 (π / 2), (fun p => x t + rot t p) '' hallway) ∩
    (fun p => x (π / 2) + rot (π / 2) p) '' vertSide
```

Gerver's rotation path is glued from five explicit families `𝐱_1, …, 𝐱_5` on the phases `[0, φ)`,
`[φ, θ)`, `[θ, π/2 - θ]`, `(π/2 - θ, π/2 - φ]` and `(π/2 - φ, π/2]`. A structure [`GerverParams`](../MovingSofaOptimality/Gerver/Defs.lean#L31) holds
their 22 parameters: the two angles `φ`, `θ`, ten coefficients and five translations. Each phase is a
rotated polynomial or trigonometric curve, for example

```lean
noncomputable def x₂ (t : ℝ) : ℝ × ℝ :=
  rot t (-t ^ 2 / 4 + P.b₁ * t + P.b₂, t / 2 - P.b₁ - 1) + P.κ₂
```

[`GerverParams.IsSolution`](../MovingSofaOptimality/Gerver/Defs.lean#L93) states Romik's equations (27)–(44): left–right symmetry, the start of the
path at the origin, continuous differentiability at the four phase boundaries, and two contact
conditions `𝐱_1(φ) = 𝐁(π/2 - θ)` and `𝐱_5(π/2 - φ) = 𝐃(θ)`, where `𝐁(t) = 𝐱(t) + ⟨𝐱'(t), u_t⟩ v_t`
and `𝐃(t) = 𝐱(t) - ⟨𝐱'(t), v_t⟩ u_t` are the points where the inner walls of the hallway touch the
sofa. [`GerverParams.InBox`](../MovingSofaOptimality/Gerver/Defs.lean#L109) restricts the angles to `φ ∈ [0.039, 0.04]` and `θ ∈ [0.68, 0.69]`, around
Romik's numerical solution `φ = 0.039177…`, `θ = 0.681301…`. Then

```lean
def gerverSofa (P : GerverParams) : Set (ℝ × ℝ) := shapeOfPath P.path
```

The theorems [`Baek.gerver_params_exists`](../Challenge.lean#L332) and [`Baek.gerver_params_unique`](../Challenge.lean#L336) prove that the box holds exactly one solution, so
Gerver's sofa is well defined, and [`Baek.gerver_sofa_area`](../Challenge.lean#L342) that its area lies between `2.2192` and `2.2199`, around
Gerver's `2.21953…`. The definitions of `x₁`, …, `x₅`, [`IsSolution`](../MovingSofaOptimality/Gerver/Defs.lean#L93) and [`InBox`](../MovingSofaOptimality/Gerver/Defs.lean#L109) are in
[`ChallengeDefs.lean`](../ChallengeDefs.lean); [Chapter 10](proof/10-gerver.md) of the text explains them.

## Formal-conjectures' definitions

[formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/MovingSofa.lean)
(file `FormalConjectures/Wikipedia/MovingSofa.lean`, Git blob
`59b6ed7eb42e11b208b09539c245da4d3f11ed00`, Apache-2.0, Copyright 2026 The Formal Conjectures Authors)
states the problem with definitions of its own. The Challenge restates them inside the namespace
`FormalConjectures` (formal-conjectures itself uses `MovingSofa`), with formal-conjectures' code for
every definition and statement. It rewords the docstrings, declares the `ℝ²` notation and the two
instances on it that formal-conjectures takes from its utility library, and gives the topology
instance on `E(2)`, which formal-conjectures leaves anonymous, an explicit name, since Lean's
generated name depends on the library that declares it.

### The plane, the hallway and moving sofas

The plane is `ℝ² = EuclideanSpace ℝ (Fin 2)`, the hallway is the same set, and `E(2)` is the group of
affine isometries of `ℝ²`, with the topology of continuous affine maps. A moving sofa comes with its
motion `m`, a continuous path in `E(2)` that starts at the identity:

```lean
structure IsMovingSofa (s : Set ℝ²) (m : I → E(2)) : Prop where
  isConnected : IsConnected s
  isClosed : IsClosed s
  continuous : Continuous m
  zero : m 0 = .refl ℝ ℝ²
  initial : s ⊆ horizontalHallway
  subset_hallway : ∀ t, m t '' s ⊆ hallway
  final : m 1 '' s ⊆ verticalHallway
```

Since the motion starts at the identity, the sofa itself lies in the horizontal side. The *sofa
constant* is the supremum of the areas of moving sofas:

```lean
def sofaConstant : ℝ≥0∞ := ⨆ (s : Set ℝ²) (_ : ∃ m, IsMovingSofa s m), volume s
```

### Gerver's sofa

formal-conjectures takes Gerver's sofa from Gerver's own description: four constants `A`, `B`, `φ`,
`θ`, the solution of a system of four equations (Romik's Equations (1)–(4)) on the domain
`0 ≤ φ ≤ θ ≤ π/4`, `A, B ≥ 0`:

```lean
def ABφθSpec (A B φ θ : ℝ) : Prop :=
  0 ≤ φ ∧ φ ≤ θ ∧ θ ≤ π / 4 ∧ 0 ≤ A ∧ 0 ≤ B ∧
  A * (θ.cos - φ.cos) - 2 * B * φ.sin
    + (θ - φ - 1) * θ.cos - θ.sin + φ.cos + φ.sin = 0 ∧
  A * (3 * θ.sin + φ.sin) - 2 * B * φ.cos
    + 3 * (θ - φ - 1) * θ.sin + 3 * θ.cos - φ.sin + φ.cos = 0 ∧
  A * φ.cos - (φ.sin + 1 / 2 - φ.cos / 2 + B * φ.sin) = 0 ∧
  (A + π / 2 - φ - θ) - (B - (θ - φ) * (1 + A) / 2 - (θ - φ)^2 / 4) = 0
```

The theorem `ABφθSpec.existsUnique` says that the system has exactly one solution, and the constants
`A`, `B`, `φ`, `θ` are defined as that solution. A piecewise radius `r` and its integrals `x`, `y`
define the rotation path `p`, and Gerver's sofa is the sofa of the path, in the convention that
translates each hallway by `p α` and then rotates it by `α`:

```lean
def sofaOfRotateTranslatePath (p : ℝ → ℝ²) : Set ℝ² :=
  rotateTranslate 0 (p 0) '' horizontalHallway ∩
  rotateTranslate ↑(π / 2) (p (π / 2)) '' verticalHallway ∩
  ⋂ α ∈ Set.Icc 0 (π / 2), rotateTranslate α (p α) '' hallway

def gerversSofa : Set ℝ² := sofaOfRotateTranslatePath GerversSofa.p
```

The definitions of `r`, `x`, `y` and `p` are in [`ChallengeDefs.lean`](../ChallengeDefs.lean); [Chapter 13](proof/13-bridge.md) of
the text explains them, and [Appendix A](proof/appendix-a.md) proves that the constants are unique.

## The two sets of definitions side by side

| | Baek's paper | formal-conjectures |
| --- | --- | --- |
| The plane | `ℝ × ℝ` | `EuclideanSpace ℝ (Fin 2)` |
| A motion | a continuous angle and translation, starting at a translation | a continuous path in `E(2)`, starting at the identity |
| The optimal area | the area of Gerver's sofa, by Theorem 1.1.1 | the supremum `sofaConstant` |
| Gerver's sofa | Romik's 22 parameters; each hallway rotated, then translated | Gerver's four constants; each hallway translated, then rotated |
