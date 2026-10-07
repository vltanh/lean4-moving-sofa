# Results

[Back to the README](../README.md)

The repository has two Palomar entries. Each has a Challenge, which states theorems with the definitions of
[Definitions](definitions.md) and imports only Mathlib, and a Solution that proves them; [Comparator](verification.md#comparator)
checks that the proofs prove exactly these statements, with Lean's standard axioms only.

- **The certificate entry**, at the root, not registered yet ([`comparator.json`](../comparator.json)). [`Challenge.lean`](../Challenge.lean) states
  seventeen theorems: Baek's five, the bridge's three, formal-conjectures' four, the three stability theorems, the
  coercive certificate and the theorem that Gerver's triple meets the certificate's hypothesis.
  [`Solution.lean`](../Solution.lean) proves them through the certificate. It restates fourteen, each proved by the matching theorem
  of [`MovingSofaExtremal/Statements.lean`](../MovingSofaExtremal/Statements.lean), which proves fifteen in the namespace `CoerciveSolution` through
  [the coercive route](coercive.md); `ABφθSpec.existsUnique` is proved in [`MovingSofaBridge/Defs.lean`](../MovingSofaBridge/Defs.lean), for both entries, and the
  two theorems about the certificate in [`MovingSofaExtremal/Certificate.lean`](../MovingSofaExtremal/Certificate.lean). [`scripts/AuditCoerciveRoute.lean`](../scripts/AuditCoerciveRoute.lean) checks that these proofs use neither
  Baek's Theorem 1.1.1, nor the results of his balance argument, nor the first proof of uniqueness, and that the
  twelve theorems that [`MovingSofaExtremal/Statements.lean`](../MovingSofaExtremal/Statements.lean) shares with [`baek/Solution.lean`](../baek/Solution.lean) have the same statements.
- **Baek's entry**, in [`baek/`](../baek), registered as PALOMAR-2026-10-02-000008 ([`baek/comparator.json`](../baek/comparator.json)).
  [`baek/Challenge.lean`](../baek/Challenge.lean) states twelve of these theorems: Baek's five, the bridge's three and formal-conjectures'
  four. [`baek/Solution.lean`](../baek/Solution.lean) proves them through Baek's Theorem 1.1.1 and the first proof of uniqueness.

## Baek's theorems

Both entries state that Gerver's sofa is well defined, has the area Gerver found, has maximum area (Baek's Theorem
1.1.1), and is, up to rigid motions, the only moving sofa of maximum area:

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

- [`Baek.gerver_params_exists`](../Challenge.lean#L664), [`Baek.gerver_params_unique`](../Challenge.lean#L668): Romik's system has exactly one solution with
  `φ ∈ [0.039, 0.04]` and `θ ∈ [0.68, 0.69]`. Romik solves the system numerically and asserts the
  uniqueness without proof; the paper uses it to define Gerver's sofa.
- [`Baek.gerver_sofa_area`](../Challenge.lean#L674): the area lies in `[2.2192, 2.2199]`, which identifies the shape defined from
  Romik's parameters with the sofa of area `2.21953…` that Gerver found.
- [`Baek.gerver_sofa_optimal`](../Challenge.lean#L680): Baek's Theorem 1.1.1, the main theorem of the paper.
- [`Baek.gerver_sofa_unique`](../Challenge.lean#L687): every moving sofa with the area of Gerver's sofa is mapped onto it, as a
  set, by a rotation about the origin followed by a translation. With [`Baek.gerver_sofa_optimal`](../Challenge.lean#L680), the moving
  sofas of maximum area are exactly the moving sofas that a rigid motion maps onto Gerver's sofa.
  Baek's paper does not prove this; the argument was written by ChatGPT Pro 6 for this repository and
  has not been peer reviewed. The certificate entry proves it through the certificate, Baek's entry by that
  argument.

## Stability

The certificate entry states that a moving sofa whose area is nearly maximal is close to Gerver's sofa; Baek's
entry does not state this. Write `ε = sofaDeficit P S` for the area of Gerver's sofa minus the area of `S`:

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

- [`Baek.gerver_sofa_stable`](../Challenge.lean#L697): once translated so that its highest point has height 1 and its leftmost
  point the abscissa of Gerver's ([`normalizedSofa`](../MovingSofaStability/Basic.lean#L195)), a moving sofa of deficit `ε < ε₀` lies within
  Euclidean Hausdorff distance `C√ε` of Gerver's sofa, and the symmetric difference of the two has area
  at most `C'√ε`. The sofa is any closed connected set with a motion: no smoothness, convexity or
  monotonicity is assumed. At zero deficit the theorem strengthens [`Baek.gerver_sofa_unique`](../Challenge.lean#L687): a moving sofa with the
  area of Gerver's sofa has `ε = 0 < ε₀`, so its normalized copy lies within distance 0 of Gerver's sofa and
  Gerver's sofa within distance 0 of it, which makes the two sets equal; the normalized copy is a translate, so a
  translation alone maps the sofa onto Gerver's sofa (the libraries also prove this directly:
  [`MovingSofaUniqueness.translate_eq_gerver_of_volume_eq`](../MovingSofaUniqueness/Main.lean#L336)).
- [`Baek.gerver_sofa_angle_stable`](../Challenge.lean#L707): such a sofa, if its motion turns it clockwise by an angle
  `ω ≥ arcsec 2.2 = arccos (5/11)`, turns by at least `π/2 - Cε`. Baek's Theorem 1.5.1 gives every
  moving sofa of area at least 2.2 such an angle.
- [`Baek.gerver_sofa_stability_exponent`](../Challenge.lean#L717): no exponent `a > 1/2` can replace the square root, whatever the
  constant, the threshold and the rotation and translation of Gerver's sofa.

The constants exist but are not computed. Baek's paper does not prove these theorems; the argument was
written by ChatGPT Pro 6 for this repository and has not been peer reviewed. [Stability](stability.md) gives
the proof and the library's further results. The proofs of the first two take the optimality and the
uniqueness from the coercive route ([the coercive route](coercive.md)), not from Baek's Theorem 1.1.1 or the first
proof of uniqueness.

## The certificate

The certificate entry also states the estimate from which its Solution derives optimality, uniqueness and stability.
Let `G` be Gerver's sofa and `φ` Gerver's angle, the parameter `φ` of Romik's solution:

```lean
theorem Certificate.coercive_certificate (P : Baek.GerverParams) (hP : P.IsSolution)
    (hPb : P.InBox) (K B D : Set (ℝ × ℝ)) (h : Certificate.InWideL P.φ K B D) :
    Certificate.upperQ P.φ K B D ≤ (volume (Baek.gerverSofa P)).toReal ∧
      Baek.EuclideanClose
        ((2 / cos P.φ) * √((volume (Baek.gerverSofa P)).toReal - Certificate.upperQ P.φ K B D))
        K (Certificate.shiftedReferenceCap (Certificate.gerverCap P) K)

theorem Certificate.gerver_triple (P : Baek.GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    ∃ B D : Set (ℝ × ℝ), Certificate.InWideL P.φ (Certificate.gerverCap P) B D ∧
      Certificate.upperQ P.φ (Certificate.gerverCap P) B D =
        (volume (Baek.gerverSofa P)).toReal
```

- [`Certificate.coercive_certificate`](../Challenge.lean#L644), Theorem 11.1 of the [manuscript](paper/README.md): for every triple `(K, B, D)`
  of the enlarged domain ([`Certificate.InWideL`](../Challenge.lean#L612)), Baek's upper bound `𝒬(K, B, D)` ([`Certificate.upperQ`](../Challenge.lean#L603), his
  Definition 8.2.2) is at most `|G|`, and the cap `K` lies within Euclidean Hausdorff distance
  `2 sec φ √(|G| - 𝒬(K, B, D))` of Gerver's cap translated horizontally so that its leftmost point has the
  abscissa of the leftmost point of `K` ([`Certificate.shiftedReferenceCap`](../Challenge.lean#L632)). On the enlarged domain the cap has
  rotation angle `π/2` but need not satisfy Baek's injectivity condition.
- [`Certificate.gerver_triple`](../Challenge.lean#L655): Gerver's cap, with the two tails of Gerver's triple, lies in the enlarged domain
  and attains `𝒬 = |G|`. So the certificate's hypothesis can be met, and its bound `𝒬 ≤ |G|` is attained.
- The first half bounds the value of `𝒬`, which gives optimality; at zero gap the second half makes a maximizing
  cap a translate of Gerver's cap, which gives uniqueness; at small gap it gives the local estimate of the
  stability proof ([the coercive route](coercive.md)).

The definitions of `𝒬`, of the enlarged domain and of Gerver's cap are restated from the libraries
([Definitions](definitions.md#the-certificates-definitions)). [`MovingSofaExtremal/Certificate.lean`](../MovingSofaExtremal/Certificate.lean) proves that they agree with the libraries' and
derives the two statements from the library's [`MovingSofaStability.coercive_certificate`](../MovingSofaStability/CapEstimate.lean#L1120) and
[`MovingSofaStability.wideGerver_value`](../MovingSofaStability/Deficit.lean#L350). Baek's paper does not contain the
certificate: it combines two estimates of the stability argument that ChatGPT Pro 6 wrote for this repository,
which has not been peer reviewed.

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

- [`Bridge.isMovingSofa_iff`](../Challenge.lean#L731): a set is a moving sofa of formal-conjectures if and only if it lies in the
  horizontal side of the hallway and its coordinates form a moving sofa of Baek's. The motions of
  formal-conjectures start at the identity, Baek's at a translation; a slide inside the horizontal
  side makes up the difference.
- [`Bridge.sofaConstant_eq`](../Challenge.lean#L739): the sofa constant is the supremum of the areas of Baek's moving sofas.
- [`Bridge.gerversSofa_eq`](../Challenge.lean#L747): in coordinates, formal-conjectures' Gerver's sofa, defined from Gerver's four
  constants, is Baek's, defined from Romik's parameters.

The bridge uses no result about optimal sofas. [Chapter 13](../baek/proof/13-bridge.md) of the text proves it.

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

- [`FormalConjectures.MovingSofa.GerversSofa.ABφθSpec.existsUnique`](../Challenge.lean#L373): Gerver's four constants exist and are unique, so formal-conjectures'
  definitions make sense. The uniqueness is proved by elementary inequalities, without numerical
  certificates ([Appendix A](../baek/proof/appendix-a.md)).
- [`FormalConjectures.MovingSofa.isMovingSofa_gerversSofa`](../Challenge.lean#L756) and [`FormalConjectures.MovingSofa.sofaConstant_eq_volume_gerversSofa`](../Challenge.lean#L760): Gerver's sofa is a moving sofa whose area is the sofa
  constant. formal-conjectures marks these solved.
- [`FormalConjectures.MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa`](../Challenge.lean#L764): a moving sofa has area the sofa constant if and only if an isometry maps
  Gerver's sofa onto it. formal-conjectures marks this open.

For the certificate entry, [`MovingSofaExtremal/Statements.lean`](../MovingSofaExtremal/Statements.lean) derives the last three from the theorems of the coercive route
and the bridge in a few lines each; for Baek's entry, [`baek/Solution.lean`](../baek/Solution.lean) does the same with Baek's theorems.
[`MovingSofaBridge/Defs.lean`](../MovingSofaBridge/Defs.lean) proves the uniqueness of the constants, for both entries, from the library's analytic proof.

## The libraries

The theorems of the two entries rest on five libraries. The certificate entry uses all five, but neither Baek's
Theorem 1.1.1, nor the results of his balance argument, nor the first proof of uniqueness; Baek's entry uses the
first three:

- [`MovingSofaOptimality/`](../MovingSofaOptimality), Baek's paper: its numbered results, each under its number (for
  example [`MovingSofaOptimality.theorem2_3_2`](../MovingSofaOptimality/Monotone/MonotoneSofa.lean#L430) for Theorem 2.3.2), with the main theorem [`MovingSofaOptimality.theorem1_1_1`](../MovingSofaOptimality/Main.lean#L302), the results it
  cites (Schneider's area formula [`MovingSofaOptimality.area_eq_half_integral_supp`](../MovingSofaOptimality/External/AreaFormula.lean#L558), Romik's system [`MovingSofaOptimality.GerverParams.romik_exists`](../MovingSofaOptimality/External/Romik.lean#L354) and
  [`MovingSofaOptimality.GerverParams.romik_unique`](../MovingSofaOptimality/External/Romik.lean#L360)), and the structure of Gerver's sofa (Theorem 8.4.1). [`scripts/Audit.lean`](../scripts/Audit.lean) lists them all, and the
  [report](../baek/REPORT.md#9-not-formalized) lists the few results left out.
- [`MovingSofaUniqueness/`](../MovingSofaUniqueness), the uniqueness: [`MovingSofaUniqueness.image_eq_gerver_of_volume_eq`](../MovingSofaUniqueness/Main.lean#L301), and one module per proposition of the
  informal proof ([Chapters 11 and 12](../baek/proof/11-selection.md)). [`MovingSofaUniqueness.MaximizerRoute`](../MovingSofaUniqueness/MaximizerRoute.lean) proves Baek's theorem a second time, from the
  maximizing caps of [`MovingSofaUniqueness.Maximizing`](../MovingSofaUniqueness/Maximizing.lean) and without Baek's Theorem 1.1.1, [`MovingSofaUniqueness.MaximizerRoute.gerver_sofa_optimal`](../MovingSofaUniqueness/MaximizerRoute.lean#L92), and the
  uniqueness from it, [`MovingSofaUniqueness.MaximizerRoute.image_eq_gerver_of_volume_eq`](../MovingSofaUniqueness/MaximizerRoute.lean#L99) (a remark at
  the end of Section 8 of the [manuscript](paper/README.md)); [`scripts/AuditMaximizerRoute.lean`](../scripts/AuditMaximizerRoute.lean) checks that this proof does not use Baek's theorem.
- [`MovingSofaBridge/`](../MovingSofaBridge), the bridge: [`MovingSofaBridge.isMovingSofa_iff`](../MovingSofaBridge/Motion.lean#L562), [`MovingSofaBridge.sofaConstant_eq`](../MovingSofaBridge/Motion.lean#L600), [`MovingSofaBridge.gerversSofa_eq`](../MovingSofaBridge/GerverSofa.lean#L507) and
  [`MovingSofaBridge.GerverConstants.spec_unique`](../MovingSofaBridge/GerverConstants.lean#L1143). It also holds the definitions that both Challenges copy,
  [`MovingSofaBridge/Defs.lean`](../MovingSofaBridge/Defs.lean) ([Definitions](definitions.md)).
- [`MovingSofaStability/`](../MovingSofaStability), the stability: [`MovingSofaStability.unrestricted_stability`](../MovingSofaStability/Global.lean#L512),
  [`MovingSofaStability.terminal_angle_stability`](../MovingSofaStability/Global.lean#L530) and [`MovingSofaStability.no_hausdorff_exponent_gt_half`](../MovingSofaStability/Sharpness.lean#L345) ([Stability](stability.md)).
- [`MovingSofaExtremal/`](../MovingSofaExtremal), the coercive route: the certificate [`MovingSofaStability.coercive_certificate`](../MovingSofaStability/CapEstimate.lean#L1120) gives optimality,
  [`MovingSofaExtremal.gerver_sofa_optimal`](../MovingSofaExtremal/Main.lean#L107), and uniqueness, [`MovingSofaExtremal.image_eq_gerver_of_volume_eq`](../MovingSofaExtremal/Main.lean#L121) and
  [`MovingSofaExtremal.translate_eq_gerver_of_volume_eq`](../MovingSofaExtremal/Main.lean#L129), without Baek's Theorem 1.1.1 or the first proof of uniqueness; the stability
  library takes its uniqueness from it, and [`MovingSofaExtremal.gerver_sofa_optimal_unique_stable`](../MovingSofaExtremal/Unified.lean#L38) states the three results
  ([the coercive route](coercive.md)). Three more modules hold the proofs of the certificate entry:
  [`MovingSofaExtremal/CertificateDefs.lean`](../MovingSofaExtremal/CertificateDefs.lean) holds the definitions that [`Challenge.lean`](../Challenge.lean) copies,
  [`MovingSofaExtremal/Certificate.lean`](../MovingSofaExtremal/Certificate.lean) proves the Challenge's two statements about the certificate from
  [`MovingSofaStability.coercive_certificate`](../MovingSofaStability/CapEstimate.lean#L1120) and [`MovingSofaStability.wideGerver_value`](../MovingSofaStability/Deficit.lean#L350), with lemmas that identify these definitions
  with the libraries', and [`MovingSofaExtremal/Statements.lean`](../MovingSofaExtremal/Statements.lean) proves the other fifteen.
