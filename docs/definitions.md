# Definitions

[Back to the README](../README.md)

Read these before trusting the results: Lean's kernel checks the proofs, not that the statements mean
what you intend. The statements of record of the two Palomar entries ([Results](results.md)) use only Mathlib and
the definitions below. There are three sets of definitions, each in its own namespace: those of Baek's paper,
`Baek`, those of Google DeepMind's formal-conjectures, `FormalConjectures.MovingSofa`, and those of the
certificate, `Certificate`, which only the certificate entry uses. The bridge theorems
([Results](results.md#the-bridge)) show that the first two describe the same objects.

The Challenges may import only Mathlib, so they copy their definitions verbatim from marked blocks of two modules
of the project ([`scripts/sync_challenge_defs.py`](../scripts/sync_challenge_defs.py)):

| Block | Module | Definitions | [`Challenge.lean`](../Challenge.lean) (the certificate entry) | [`baek/Challenge.lean`](../baek/Challenge.lean) (Baek's entry) |
| --- | --- | --- | --- | --- |
| `BAEK CORE DEFINITIONS` | [`ChallengeDefs.lean`](../ChallengeDefs.lean) | Baek's, up to Gerver's sofa | yes | yes |
| `BAEK STABILITY DEFINITIONS` | [`ChallengeDefs.lean`](../ChallengeDefs.lean) | the terms of the stability theorems | yes | no |
| `SHARED DEFINITIONS 1` and `2` | [`ChallengeDefs.lean`](../ChallengeDefs.lean) | formal-conjectures' | yes | yes |
| `CERTIFICATE DEFINITIONS` | [`CertificateDefs.lean`](../CertificateDefs.lean) | the certificate's | yes | no |

The bridge library and the Solutions use the constants of these modules, since Comparator compares constants by
name. [`SolutionCoercive.lean`](../SolutionCoercive.lean) and [`baek/Solution.lean`](../baek/Solution.lean) prove that the definitions of the optimality library, which
the uniqueness library uses too, agree with those of `Baek`; [`SolutionCoercive.lean`](../SolutionCoercive.lean) also proves that the
libraries' forms of the stability terms agree with the Challenge's, and [`CertificateProof.lean`](../CertificateProof.lean) that the
certificate's definitions agree with the libraries'.

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

The theorems [`Baek.gerver_params_exists`](../Challenge.lean#L664) and [`Baek.gerver_params_unique`](../Challenge.lean#L668) prove that the box holds exactly one solution, so
Gerver's sofa is well defined, and [`Baek.gerver_sofa_area`](../Challenge.lean#L674) that its area lies between `2.2192` and `2.2199`, around
Gerver's `2.21953…`. The definitions of `x₁`, …, `x₅`, [`IsSolution`](../MovingSofaOptimality/Gerver/Defs.lean#L93) and [`InBox`](../MovingSofaOptimality/Gerver/Defs.lean#L109) are in
[`ChallengeDefs.lean`](../ChallengeDefs.lean); [Chapter 10](proof/10-gerver.md) of the text explains them.

### Stability

The stability theorems ([Results](results.md#stability)), which only the certificate entry states, use five more
definitions, in [`Challenge.lean`](../Challenge.lean) and not in [`baek/Challenge.lean`](../baek/Challenge.lean). A moving sofa *with
angle* `ω` is one whose motion ends with the rotation by `-ω`, that is, turns it clockwise by `ω`. The
*deficit* of a set is the area of Gerver's sofa minus its area. `normalizedSofa P S` translates `S` so
that its highest point has height 1 and its leftmost point the abscissa of the leftmost point of
Gerver's sofa. `EuclideanClose r S T` says that every point of each set lies within Euclidean distance
`r` of a point of the other; for nonempty compact sets, this is a Euclidean Hausdorff distance at most
`r`:

```lean
def IsMovingSofaWithAngle (S : Set (ℝ × ℝ)) (ω : ℝ) : Prop :=
  IsClosed S ∧ IsConnected S ∧
    ∃ (θ : ℝ → ℝ) (c : ℝ → ℝ × ℝ), ContinuousOn θ (Icc 0 1) ∧ ContinuousOn c (Icc 0 1) ∧
      θ 0 = 0 ∧ θ 1 = -ω ∧ (∀ p ∈ S, rot (θ 0) p + c 0 ∈ horizSide) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ p ∈ S, rot (θ s) p + c s ∈ hallway) ∧
      (∀ p ∈ S, rot (θ 1) p + c 1 ∈ vertSide)

noncomputable def sofaDeficit (P : GerverParams) (S : Set (ℝ × ℝ)) : ℝ :=
  (volume (gerverSofa P)).toReal - (volume S).toReal

noncomputable def normalizedSofa (P : GerverParams) (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  (fun p => p + (sInf (Prod.fst '' gerverSofa P) - sInf (Prod.fst '' S), 1 - sSup (Prod.snd '' S)))
    '' S

noncomputable def euclideanDist (p q : ℝ × ℝ) : ℝ := √((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

def EuclideanClose (r : ℝ) (S T : Set (ℝ × ℝ)) : Prop :=
  (∀ p ∈ S, ∃ q ∈ T, euclideanDist p q ≤ r) ∧ (∀ q ∈ T, ∃ p ∈ S, euclideanDist q p ≤ r)
```

The library states the same theorems with its own forms of these definitions: the normalization
with support functions, and the distance through its Euclidean norm; [`SolutionCoercive.lean`](../SolutionCoercive.lean) proves that
the two forms agree.

## Formal-conjectures' definitions

[formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/MovingSofa.lean)
(file `FormalConjectures/Wikipedia/MovingSofa.lean`, Git blob
`59b6ed7eb42e11b208b09539c245da4d3f11ed00`, Apache-2.0, Copyright 2026 The Formal Conjectures Authors)
states the problem with definitions of its own. Both Challenges restate them inside the namespace
`FormalConjectures` (formal-conjectures itself uses `MovingSofa`), with formal-conjectures' code for
every definition and statement. They reword the docstrings, declare the `ℝ²` notation and the two
instances on it that formal-conjectures takes from its utility library, and give the topology
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

## The certificate's definitions

The certificate ([Results](results.md#the-certificate)), which only the certificate entry states, is an estimate for
Baek's upper bound `𝒬`, a functional of a cap and two convex bodies. [`CertificateDefs.lean`](../CertificateDefs.lean) restates what it needs in the
namespace `Certificate`, each definition with the body of the matching definition of [`MovingSofaOptimality`](../MovingSofaOptimality) or
[`MovingSofaStability`](../MovingSofaStability), written with Mathlib and Baek's definitions above, except as said below:

- convex bodies ([`Certificate.IsConvexBody`](../Challenge.lean#L444)), support functions `h_K` ([`Certificate.supp`](../Challenge.lean#L447)), the vertices `v_K^±(t)`
  of their edges ([`Certificate.vplus`](../Challenge.lean#L457), [`Certificate.vminus`](../Challenge.lean#L462)), and the surface area measure `σ_K` ([`Certificate.sigma`](../Challenge.lean#L478)),
  the Lebesgue–Stieltjes measure of `G_K(t) = ⟨v_K⁺(t), v_t⟩ + ∫₀ᵗ h_K`;
- caps with rotation angle `ω` ([`Certificate.IsCap`](../Challenge.lean#L496)), the cap `𝒞(S)` of a set ([`Certificate.capOf`](../Challenge.lean#L526)), and the inner
  corner `𝐱_S(t)` of its supporting hallway ([`Certificate.innerCorner`](../Challenge.lean#L530));
- the curve areas `𝒥(𝐱) = ½ ∫ 𝐱 × d𝐱` ([`Certificate.curveArea`](../Challenge.lean#L580)), `𝒥([p, q]) = (p × q)/2` ([`Certificate.segArea`](../Challenge.lean#L584)) and
  `½ ∫_{(a,b)} h_K dσ_K` ([`Certificate.convexCurveArea`](../Challenge.lean#L536));
- Baek's upper bound `𝒬` ([`Certificate.upperQ`](../Challenge.lean#L603), his Definition 8.2.2) and the enlarged domain `T̄` of triples
  ([`Certificate.InWideL`](../Challenge.lean#L612)): Baek's triples `(K, B, D)`, with `K` any cap with rotation angle `π/2` in place of a cap of
  his class `𝒦ⁱ`, so that `K` need not satisfy his injectivity condition;
- Gerver's cap `K_G` ([`Certificate.gerverCap`](../Challenge.lean#L624)), the cap of Gerver's sofa with rotation angle `π/2`, and its horizontal
  translate with the leftmost abscissa of a cap `K` ([`Certificate.shiftedReferenceCap`](../Challenge.lean#L632)).

```lean
def upperQ (φ : ℝ) (K B D : Set (ℝ × ℝ)) : ℝ :=
  (volume K).toReal + convexCurveArea D (3 * π / 2) (3 * π / 2 + (π / 2 - φ)) +
    segArea (yD φ D) (xLeft φ K) - curveArea (innerCorner K) φ (π / 2 - φ) +
    segArea (xRight φ K) (xB φ B) + convexCurveArea B (π + φ) (3 * π / 2)

def InWideL (φ : ℝ) (K B D : Set (ℝ × ℝ)) : Prop :=
  IsCap K (π / 2) ∧ IsConvexBody B ∧ IsConvexBody D ∧ B ⊆ K ∧ D ⊆ K ∧
    (∀ t ∈ Icc φ (π / 2), supp K t + supp B (π + t) ≤ 1) ∧
    supp K φ + supp B (π + φ) = 1 ∧ supp K (π / 2) + supp B (π + π / 2) = 1 ∧
    (∀ t ∈ Icc 0 (π / 2 - φ), supp K (π / 2 + t) + supp D (3 * π / 2 + t) ≤ 1) ∧
    supp K (π / 2 + 0) + supp D (3 * π / 2 + 0) = 1 ∧
    supp K (π / 2 + (π / 2 - φ)) + supp D (3 * π / 2 + (π / 2 - φ)) = 1
```

Three definitions are written differently and are equal to the library's by definition: [`Certificate.gerverCap`](../Challenge.lean#L624) is
the library's [`GerverParams.cap`](../MovingSofaOptimality/Gerver/Properties.lean#L67), [`Certificate.innerCorner`](../Challenge.lean#L530) writes `(0, 0)` for the library's `xL`, and
[`Certificate.upperQ`](../Challenge.lean#L603) writes `(volume K).toReal` for the library's `area K`. One body differs. The library's
surface area measure contains the library's proofs that `G_K` is monotone and right-continuous, which a Challenge
cannot carry, so [`Certificate.sigma`](../Challenge.lean#L478) tests the two properties instead, and is Lebesgue measure when they fail, as
the library's is on sets that are not convex bodies. The two agree on convex bodies, where the properties hold,
but can differ on other sets: on `∅`, `G_K` is zero, and [`Certificate.sigma`](../Challenge.lean#L478) is the zero measure.
[`CertificateProof.lean`](../CertificateProof.lean) proves that each definition is the library's: by definition, except [`Certificate.sigma`](../Challenge.lean#L478) and
[`Certificate.convexCurveArea`](../Challenge.lean#L536), which agree with the library's on convex bodies, and [`Certificate.upperQ`](../Challenge.lean#L603), which
agrees with it when `B` and `D` are convex bodies, as they are in `T̄`.
