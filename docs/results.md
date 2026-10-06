# Results

[Back to the README](../README.md)

[`Challenge.lean`](../Challenge.lean) states fifteen theorems with the definitions of [Definitions](definitions.md), and
[`Solution.lean`](../Solution.lean) proves them; [Comparator](verification.md#comparator) checks that the proofs prove
exactly these statements, with Lean's standard axioms only. [`SolutionCoercive.lean`](../SolutionCoercive.lean) proves them again
through the coercive route ([the coercive route](coercive.md)), and [`scripts/AuditCoerciveRoute.lean`](../scripts/AuditCoerciveRoute.lean) checks that its
theorems have the same statements.

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

- [`Baek.gerver_params_exists`](../Challenge.lean#L372), [`Baek.gerver_params_unique`](../Challenge.lean#L376): Romik's system has exactly one solution with
  `φ ∈ [0.039, 0.04]` and `θ ∈ [0.68, 0.69]`. Romik solves the system numerically and asserts the
  uniqueness without proof; the paper uses it to define Gerver's sofa.
- [`Baek.gerver_sofa_area`](../Challenge.lean#L382): the area lies in `[2.2192, 2.2199]`, which identifies the shape defined from
  Romik's parameters with the sofa of area `2.21953…` that Gerver found.
- [`Baek.gerver_sofa_optimal`](../Challenge.lean#L388): Baek's Theorem 1.1.1, the main theorem of the paper.
- [`Baek.gerver_sofa_unique`](../Challenge.lean#L395): every moving sofa with the area of Gerver's sofa is mapped onto it, as a
  set, by a rotation about the origin followed by a translation. With [`Baek.gerver_sofa_optimal`](../Challenge.lean#L388), the moving
  sofas of maximum area are exactly the moving sofas that a rigid motion maps onto Gerver's sofa.
  Baek's paper does not prove this; the argument was written by ChatGPT Pro 6 for this repository and
  has not been peer reviewed.

## Stability

A moving sofa whose area is nearly maximal is close to Gerver's sofa. Write `ε = sofaDeficit P S` for the
area of Gerver's sofa minus the area of `S`:

```lean
theorem gerver_sofa_stable (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    ∃ C C' ε₀ : ℝ, 0 < C ∧ 0 < C' ∧ 0 < ε₀ ∧
      ∀ S, IsMovingSofa S → sofaDeficit P S < ε₀ →
        EuclideanClose (C * √(sofaDeficit P S)) (normalizedSofa P S) (gerverSofa P) ∧
        (volume (normalizedSofa P S ∆ gerverSofa P)).toReal ≤ C' * √(sofaDeficit P S)

theorem gerver_sofa_angle_stable (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ S ω, IsMovingSofaWithAngle S ω → ω ∈ Icc (arccos (5 / 11)) (π / 2) →
        sofaDeficit P S < ε₀ → π / 2 - ω ≤ C * sofaDeficit P S

theorem gerver_sofa_stability_exponent (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox)
    (a C ε₀ : ℝ) (ha : 1 / 2 < a) (hε₀ : 0 < ε₀) :
    ∃ S, IsMovingSofa S ∧ 0 < sofaDeficit P S ∧ sofaDeficit P S < ε₀ ∧
      ∀ (θ : ℝ) (v : ℝ × ℝ),
        ¬ EuclideanClose (C * sofaDeficit P S ^ a) S ((fun p => rot θ p + v) '' gerverSofa P)
```

- [`Baek.gerver_sofa_stable`](../Challenge.lean#L405): once translated so that its highest point has height 1 and its leftmost
  point the abscissa of Gerver's ([`normalizedSofa`](../MovingSofaStability/Basic.lean#L195)), a moving sofa of deficit `ε < ε₀` lies within
  Euclidean Hausdorff distance `C√ε` of Gerver's sofa, and the symmetric difference of the two has area
  at most `C'√ε`. The sofa is any closed connected set with a motion: no smoothness, convexity or
  monotonicity is assumed. At zero deficit the theorem strengthens [`Baek.gerver_sofa_unique`](../Challenge.lean#L395): a moving sofa with the
  area of Gerver's sofa has `ε = 0 < ε₀`, so its normalized copy lies within distance 0 of Gerver's sofa and
  Gerver's sofa within distance 0 of it, which makes the two sets equal; the normalized copy is a translate, so a
  translation alone maps the sofa onto Gerver's sofa (the libraries also prove this directly:
  [`MovingSofaUniqueness.translate_eq_gerver_of_volume_eq`](../MovingSofaUniqueness/Main.lean#L336)).
- [`Baek.gerver_sofa_angle_stable`](../Challenge.lean#L415): such a sofa, if its motion turns it clockwise by an angle
  `ω ≥ arcsec 2.2 = arccos (5/11)`, turns by at least `π/2 - Cε`. Baek's Theorem 1.5.1 gives every
  moving sofa of area at least 2.2 such an angle.
- [`Baek.gerver_sofa_stability_exponent`](../Challenge.lean#L425): no exponent `a > 1/2` can replace the square root, whatever the
  constant, the threshold and the rotation and translation of Gerver's sofa.

The constants exist but are not computed. Baek's paper does not prove these theorems; the argument was
written by ChatGPT Pro 6 for this repository and has not been peer reviewed. [Stability](stability.md) gives
the proof and the library's further results. The proofs of the first two take the optimality and the
uniqueness from the coercive route ([the coercive route](coercive.md)), not from Baek's Theorem 1.1.1 or the first
proof of uniqueness.

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

- [`Bridge.isMovingSofa_iff`](../Challenge.lean#L439): a set is a moving sofa of formal-conjectures if and only if it lies in the
  horizontal side of the hallway and its coordinates form a moving sofa of Baek's. The motions of
  formal-conjectures start at the identity, Baek's at a translation; a slide inside the horizontal
  side makes up the difference.
- [`Bridge.sofaConstant_eq`](../Challenge.lean#L447): the sofa constant is the supremum of the areas of Baek's moving sofas.
- [`Bridge.gerversSofa_eq`](../Challenge.lean#L455): in coordinates, formal-conjectures' Gerver's sofa, defined from Gerver's four
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

- [`FormalConjectures.MovingSofa.GerversSofa.ABφθSpec.existsUnique`](../Challenge.lean#L316): Gerver's four constants exist and are unique, so formal-conjectures'
  definitions make sense. The uniqueness is proved by elementary inequalities, without numerical
  certificates ([Appendix A](proof/appendix-a.md)).
- [`FormalConjectures.MovingSofa.isMovingSofa_gerversSofa`](../Challenge.lean#L464) and [`FormalConjectures.MovingSofa.sofaConstant_eq_volume_gerversSofa`](../Challenge.lean#L468): Gerver's sofa is a moving sofa whose area is the sofa
  constant. formal-conjectures marks these solved.
- [`FormalConjectures.MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa`](../Challenge.lean#L472): a moving sofa has area the sofa constant if and only if an isometry maps
  Gerver's sofa onto it. formal-conjectures marks this open.

[`Solution.lean`](../Solution.lean) derives these three theorems from Baek's theorems and the bridge in a few lines
each, and the uniqueness of the constants from the library's analytic proof.

## The libraries

The fifteen theorems rest on five libraries:

- [`MovingSofaOptimality/`](../MovingSofaOptimality), Baek's paper: its numbered results, each under its number (for
  example [`MovingSofaOptimality.theorem2_3_2`](../MovingSofaOptimality/Monotone/MonotoneSofa.lean#L430) for Theorem 2.3.2), with the main theorem [`MovingSofaOptimality.theorem1_1_1`](../MovingSofaOptimality/Main.lean#L302), the results it
  cites (Schneider's area formula [`MovingSofaOptimality.area_eq_half_integral_supp`](../MovingSofaOptimality/External/AreaFormula.lean#L558), Romik's system [`MovingSofaOptimality.GerverParams.romik_exists`](../MovingSofaOptimality/External/Romik.lean#L354) and
  [`MovingSofaOptimality.GerverParams.romik_unique`](../MovingSofaOptimality/External/Romik.lean#L360)), and the structure of Gerver's sofa (Theorem 8.4.1). [`scripts/Audit.lean`](../scripts/Audit.lean) lists them all, and the
  [report](../REPORT.md#9-not-formalized) lists the few results left out.
- [`MovingSofaUniqueness/`](../MovingSofaUniqueness), the uniqueness: [`MovingSofaUniqueness.image_eq_gerver_of_volume_eq`](../MovingSofaUniqueness/Main.lean#L301), and one module per proposition of the
  informal proof ([Chapters 11 and 12](proof/11-selection.md)). [`MovingSofaUniqueness.MaximizerRoute`](../MovingSofaUniqueness/MaximizerRoute.lean) proves Baek's theorem a second time, from the
  maximizing caps of [`MovingSofaUniqueness.Maximizing`](../MovingSofaUniqueness/Maximizing.lean) and without Baek's Theorem 1.1.1, [`MovingSofaUniqueness.MaximizerRoute.gerver_sofa_optimal`](../MovingSofaUniqueness/MaximizerRoute.lean#L92), and the
  uniqueness from it, [`MovingSofaUniqueness.MaximizerRoute.image_eq_gerver_of_volume_eq`](../MovingSofaUniqueness/MaximizerRoute.lean#L99) (a remark at
  the end of Section 8 of the [manuscript](paper/README.md)); [`scripts/AuditMaximizerRoute.lean`](../scripts/AuditMaximizerRoute.lean) checks that this proof does not use Baek's theorem.
- [`MovingSofaBridge/`](../MovingSofaBridge), the bridge: [`MovingSofaBridge.isMovingSofa_iff`](../MovingSofaBridge/Motion.lean#L562), [`MovingSofaBridge.sofaConstant_eq`](../MovingSofaBridge/Motion.lean#L600), [`MovingSofaBridge.gerversSofa_eq`](../MovingSofaBridge/GerverSofa.lean#L507) and
  [`MovingSofaBridge.GerverConstants.spec_unique`](../MovingSofaBridge/GerverConstants.lean#L1143).
- [`MovingSofaStability/`](../MovingSofaStability), the stability: [`MovingSofaStability.unrestricted_stability`](../MovingSofaStability/Global.lean#L512),
  [`MovingSofaStability.terminal_angle_stability`](../MovingSofaStability/Global.lean#L530) and [`MovingSofaStability.no_hausdorff_exponent_gt_half`](../MovingSofaStability/Sharpness.lean#L345) ([Stability](stability.md)).
- [`MovingSofaExtremal/`](../MovingSofaExtremal), the coercive route: the certificate [`MovingSofaStability.coercive_certificate`](../MovingSofaStability/CapEstimate.lean#L1120) gives optimality,
  [`MovingSofaExtremal.gerver_sofa_optimal`](../MovingSofaExtremal/Main.lean#L107), and uniqueness, [`MovingSofaExtremal.image_eq_gerver_of_volume_eq`](../MovingSofaExtremal/Main.lean#L121) and
  [`MovingSofaExtremal.translate_eq_gerver_of_volume_eq`](../MovingSofaExtremal/Main.lean#L129), without Baek's Theorem 1.1.1 or the first proof of uniqueness; the stability
  library takes its uniqueness from it, and [`MovingSofaExtremal.gerver_sofa_optimal_unique_stable`](../MovingSofaExtremal/Unified.lean#L38) states the three results
  ([the coercive route](coercive.md)).
