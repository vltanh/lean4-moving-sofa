# Results

[Back to the README](../README.md)

[`Challenge.lean`](../Challenge.lean) states twelve theorems with the definitions of [Definitions](definitions.md), and
[`Solution.lean`](../Solution.lean) proves them; [Comparator](verification.md#comparator) checks that the proofs prove
exactly these statements, with Lean's standard axioms only.

## Baek's theorems

Gerver's sofa is well defined, has the area Gerver found, has maximum area (Baek's Theorem 1.1.1), and
is, up to rigid motions, the only moving sofa of maximum area:

```lean
theorem gerver_params_exists : ∃ P : GerverParams, P.IsSolution ∧ P.InBox

theorem gerver_params_unique (P Q : GerverParams) (hP : P.IsSolution) (hPb : P.InBox)
    (hQ : Q.IsSolution) (hQb : Q.InBox) : P = Q

theorem gerver_sofa_area (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    ENNReal.ofReal 2.2192 ≤ volume (gerverSofa P) ∧ volume (gerverSofa P) ≤ ENNReal.ofReal 2.2199

theorem gerver_sofa_optimal (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    IsMovingSofa (gerverSofa P) ∧ ∀ S, IsMovingSofa S → volume S ≤ volume (gerverSofa P)

theorem gerver_sofa_unique (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) (S : Set (ℝ × ℝ))
    (hS : IsMovingSofa S) (harea : volume S = volume (gerverSofa P)) :
    ∃ (θ : ℝ) (v : ℝ × ℝ), (fun p => rot θ p + v) '' S = gerverSofa P
```

- [`Baek.gerver_params_exists`](../Challenge.lean#L328), [`Baek.gerver_params_unique`](../Challenge.lean#L332): Romik's system has exactly one solution with
  `φ ∈ [0.039, 0.04]` and `θ ∈ [0.68, 0.69]`. Romik solves the system numerically and asserts the
  uniqueness without proof; the paper uses it to define Gerver's sofa.
- [`Baek.gerver_sofa_area`](../Challenge.lean#L338): the area lies in `[2.2192, 2.2199]`, which identifies the shape defined from
  Romik's parameters with the sofa of area `2.21953…` that Gerver found.
- [`Baek.gerver_sofa_optimal`](../Challenge.lean#L344): Baek's Theorem 1.1.1, the main theorem of the paper.
- [`Baek.gerver_sofa_unique`](../Challenge.lean#L351): every moving sofa with the area of Gerver's sofa is mapped onto it, as a
  set, by a rotation about the origin followed by a translation. With [`Baek.gerver_sofa_optimal`](../Challenge.lean#L344), the moving
  sofas of maximum area are exactly the moving sofas that a rigid motion maps onto Gerver's sofa.
  Baek's paper does not prove this; the argument was written by ChatGPT Pro 6 for this repository and
  has not been peer reviewed.

## The bridge

The definitions of formal-conjectures describe the same objects as Baek's. Write
`(fun p : ℝ² => (p 0, p 1))` for the coordinates of a point of `ℝ² = EuclideanSpace ℝ (Fin 2)`:

```lean
theorem isMovingSofa_iff (s : Set ℝ²) :
    (∃ m, FormalConjectures.MovingSofa.IsMovingSofa s m) ↔
      s ⊆ FormalConjectures.MovingSofa.horizontalHallway ∧
        Baek.IsMovingSofa ((fun p : ℝ² => (p 0, p 1)) '' s)

theorem sofaConstant_eq :
    FormalConjectures.MovingSofa.sofaConstant =
      ⨆ (S : Set (ℝ × ℝ)) (_ : Baek.IsMovingSofa S), volume S

theorem gerversSofa_eq (P : Baek.GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    (fun p : ℝ² => (p 0, p 1)) '' FormalConjectures.MovingSofa.gerversSofa = Baek.gerverSofa P
```

- [`Bridge.isMovingSofa_iff`](../Challenge.lean#L363): a set is a moving sofa of formal-conjectures if and only if it lies in the
  horizontal side of the hallway and its coordinates form a moving sofa of Baek's. The motions of
  formal-conjectures start at the identity, Baek's at a translation; a slide inside the horizontal
  side makes up the difference.
- [`Bridge.sofaConstant_eq`](../Challenge.lean#L371): the sofa constant is the supremum of the areas of Baek's moving sofas.
- [`Bridge.gerversSofa_eq`](../Challenge.lean#L379): in coordinates, formal-conjectures' Gerver's sofa, defined from Gerver's four
  constants, is Baek's, defined from Romik's parameters.

The bridge uses no result about optimal sofas. [Chapter 13](proof/13-bridge.md) of the text proves it.

## Formal-conjectures' theorems

```lean
theorem GerversSofa.ABφθSpec.existsUnique : ∃! ABφθ : ℝ × ℝ × ℝ × ℝ,
    ABφθSpec ABφθ.1 ABφθ.2.1 ABφθ.2.2.1 ABφθ.2.2.2

theorem isMovingSofa_gerversSofa : ∃ m, IsMovingSofa gerversSofa m

theorem sofaConstant_eq_volume_gerversSofa : sofaConstant = volume gerversSofa

theorem volume_eq_sofaConstant_iff_congruent_gerversSofa (s : Set ℝ²)
    (hs : ∃ m, IsMovingSofa s m) :
    volume s = sofaConstant ↔ ∃ g : E(2), s = g '' gerversSofa
```

- [`FormalConjectures.MovingSofa.GerversSofa.ABφθSpec.existsUnique`](../Challenge.lean#L272): Gerver's four constants exist and are unique, so formal-conjectures'
  definitions make sense. The uniqueness is proved by elementary inequalities, without numerical
  certificates ([Appendix A](proof/appendix-a.md)).
- [`FormalConjectures.MovingSofa.isMovingSofa_gerversSofa`](../Challenge.lean#L388) and [`FormalConjectures.MovingSofa.sofaConstant_eq_volume_gerversSofa`](../Challenge.lean#L392): Gerver's sofa is a moving sofa whose area is the sofa
  constant. formal-conjectures marks these solved.
- [`FormalConjectures.MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa`](../Challenge.lean#L396): a moving sofa has area the sofa constant if and only if an isometry maps
  Gerver's sofa onto it. formal-conjectures marks this open.

[`Solution.lean`](../Solution.lean) derives these three theorems from Baek's theorems and the bridge in a few lines
each, and the uniqueness of the constants from the library's analytic proof.

## The libraries

The twelve theorems rest on the three libraries:

- [`MovingSofaOptimality/`](../MovingSofaOptimality), Baek's paper: every numbered result of the paper, under its number (for
  example [`MovingSofaOptimality.theorem2_3_2`](../MovingSofaOptimality/Monotone/MonotoneSofa.lean#L395) for Theorem 2.3.2), with the main theorem [`MovingSofaOptimality.theorem1_1_1`](../MovingSofaOptimality/Main.lean#L301), the results it
  cites (Schneider's area formula [`MovingSofaOptimality.area_eq_half_integral_supp`](../MovingSofaOptimality/External/AreaFormula.lean#L558), Romik's system [`MovingSofaOptimality.GerverParams.romik_exists`](../MovingSofaOptimality/External/Romik.lean#L354) and
  [`MovingSofaOptimality.GerverParams.romik_unique`](../MovingSofaOptimality/External/Romik.lean#L360)), and the structure of Gerver's sofa (Theorem 8.4.1). [`scripts/Audit.lean`](../scripts/Audit.lean) lists them all.
- [`MovingSofaUniqueness/`](../MovingSofaUniqueness), the uniqueness: [`MovingSofaUniqueness.image_eq_gerver_of_volume_eq`](../MovingSofaUniqueness/Main.lean#L212), and one module per proposition of the
  informal proof ([Chapters 11 and 12](proof/11-selection.md)).
- [`MovingSofaBridge/`](../MovingSofaBridge), the bridge: [`MovingSofaBridge.isMovingSofa_iff`](../MovingSofaBridge/Motion.lean#L562), [`MovingSofaBridge.sofaConstant_eq`](../MovingSofaBridge/Motion.lean#L600), [`MovingSofaBridge.gerversSofa_eq`](../MovingSofaBridge/GerverSofa.lean#L507) and
  [`MovingSofaBridge.GerverConstants.spec_unique`](../MovingSofaBridge/GerverConstants.lean#L1143).
