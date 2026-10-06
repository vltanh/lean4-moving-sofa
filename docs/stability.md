# Stability

[Back to the README](../README.md)

A moving sofa whose area is close to the maximum is close to Gerver's sofa. The library
[`MovingSofaStability/`](../MovingSofaStability) proves this with the rate √ε, where ε is the missing area, and proves that the
rate of the Hausdorff distance cannot be improved. The argument and the Lean code were written by ChatGPT Pro 6
(pull request #8) and compiled here; no person has reviewed the argument, and Lean's kernel checks
every proof ([verification](verification.md)). Baek's paper does not contain these results. The proof takes the
optimality and the uniqueness of Gerver's sofa from the coercive route, which derives them from the
same estimate as the local step below ([the coercive route](coercive.md)), so that it uses neither Baek's
Theorem 1.1.1 nor the first proof of uniqueness.

Throughout, `P` is the solution of Romik's system in the box (`P.IsSolution`, `P.InBox`), `G` is
Gerver's sofa `gerverSofa P`, and the definitions of moving sofas, caps and areas are Baek's
([definitions](definitions.md)).

[`Challenge.lean`](../Challenge.lean) restates the three main theorems in Mathlib's vocabulary, as
[`Baek.gerver_sofa_stable`](../Challenge.lean#L401), [`Baek.gerver_sofa_angle_stable`](../Challenge.lean#L411) and [`Baek.gerver_sofa_stability_exponent`](../Challenge.lean#L421)
([Results](results.md#stability)); below are the library's forms, from which [`Solution.lean`](../Solution.lean)
proves them.

## The theorems

### Stability

The *deficit* of a set `S` is `area G - area S`. A moving sofa may sit anywhere along the horizontal
side of the hallway, so the theorem first translates it: `normalizedSofa P S` is the translate of `S`
whose top is at height 1 and whose leftmost point has the abscissa of Gerver's. Distances are
Euclidean, between the sets themselves, not their convex hulls: `EuclideanClose r S T` says that
every point of each set lies within Euclidean distance `r` of a point of the other.

```lean
def sofaDeficit (P : GerverParams) (S : Set Point) : ℝ :=
  area (gerverSofa P) - area S

def UnrestrictedStability (P : GerverParams) : Prop :=
  ∃ C Carea ε₀ : ℝ, 0 < C ∧ 0 < Carea ∧ 0 < ε₀ ∧
    ∀ S : Set Point, IsMovingSofa S → sofaDeficit P S < ε₀ →
      EuclideanClose (C * sqrt (sofaDeficit P S)) (normalizedSofa P S) (gerverSofa P) ∧
      symmetricDifferenceArea (normalizedSofa P S) (gerverSofa P) ≤
        Carea * sqrt (sofaDeficit P S)

def TerminalAngleStability (P : GerverParams) : Prop :=
  ∃ Cangle ε₀ : ℝ, 0 < Cangle ∧ 0 < ε₀ ∧
    ∀ (S : Set Point) (ω : ℝ), IsMovingSofaWithAngle S ω →
      ω ∈ Icc (arccos (5 / 11)) (π / 2) → sofaDeficit P S < ε₀ →
      0 ≤ π / 2 - ω ∧ π / 2 - ω ≤ Cangle * sofaDeficit P S

theorem unrestricted_stability {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    UnrestrictedStability P

theorem terminal_angle_stability {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    TerminalAngleStability P
```

- [`MovingSofaStability.unrestricted_stability`](../MovingSofaStability/GlobalStability.lean#L113): after the translation, a moving sofa of deficit `ε < ε₀`
  is within Euclidean Hausdorff distance `C√ε` of Gerver's sofa, and its symmetric difference with
  Gerver's sofa has area at most `C_area√ε`. The sofa is an arbitrary closed connected set with a
  motion: no smoothness, convexity, monotonicity or injectivity is assumed.
- [`MovingSofaStability.terminal_angle_stability`](../MovingSofaStability/GlobalStability.lean#L136): if a moving sofa of deficit `ε < ε₀` moves with a
  rotation angle `ω ≥ arcsec 2.2 = arccos (5/11)`, then `ω ≥ π/2 - C_angle ε`. Baek's Theorem 1.5.1
  gives every moving sofa of area at least 2.2 such an angle.
- The constants are existential. The threshold `ε₀` comes from a compactness argument and is not
  computed; the constants are not claimed to be optimal.

### The exponent one half is optimal

Removing a small open disk of radius `r` from the interior of Gerver's sofa leaves a moving sofa that
has lost area `πr²`, lies at Euclidean Hausdorff distance `r` from Gerver's sofa, and at distance at
least `r` from every rigid copy of it:

```lean
theorem punctured_gerver_family {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ p : Point, ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      IsMovingSofa (puncture (gerverSofa P) p r) ∧
      sofaDeficit P (puncture (gerverSofa P) p r) = π * r ^ 2 ∧
      EuclideanClose r (puncture (gerverSofa P) p r) (gerverSofa P) ∧
      (∀ g : Rigid, ∀ d : ℝ,
        EuclideanClose d (puncture (gerverSofa P) p r) (g '' gerverSofa P) → r ≤ d) ∧
      rigidHausdorffDistance (puncture (gerverSofa P) p r) (gerverSofa P) = r

theorem no_hausdorff_exponent_gt_half {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {a : ℝ} (ha : 1 / 2 < a)
    (C : ℝ) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ S : Set Point, IsMovingSofa S ∧ 0 < sofaDeficit P S ∧ sofaDeficit P S < ε₀ ∧
      ∀ g : Rigid, ¬EuclideanClose (C * (sofaDeficit P S) ^ a) S (g '' gerverSofa P)
```

- [`MovingSofaStability.punctured_gerver_family`](../MovingSofaStability/PuncturedSofa.lean#L61): `puncture G p r` is `G` minus the open Euclidean disk of center `p` and
  radius `r`; it keeps the circle, so it is closed, and it is connected. The lower bound holds for
  every rotation and translation `g`, and [`MovingSofaStability.rigidHausdorffDistance`](../MovingSofaStability/PunctureMetric.lean#L116) is the infimum over all of them.
- [`MovingSofaStability.no_hausdorff_exponent_gt_half`](../MovingSofaStability/SharpExponent.lean#L69) and [`MovingSofaStability.rigid_distance_not_higher_order`](../MovingSofaStability/SharpExponent.lean#L86): no bound
  `C εᵃ` with `a > 1/2` holds, whatever the constant, the threshold and the alignment. The exponent
  of the stability theorem is therefore optimal for the Hausdorff distance. Nothing is claimed about
  the optimal exponent of the symmetric-difference area.

### The cap estimate

For caps, the rate has an explicit constant. A cap `K` of Baek's class `Kᵢ` (a right-angle cap with
the injectivity condition and area at least 2.2) lies within Euclidean Hausdorff distance
`(2 / cos φ) √(|G| - sofaArea (π/2) K)` of Gerver's cap, translated horizontally so that their
leftmost points have the same abscissa; with Romik's `φ ∈ [0.039, 0.04]`, `2 / cos φ ≤ 2500/1249 < 1001/500`:

```lean
theorem sharp_ki_cap_distance_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hK : IsKi K) :
    EuclideanClose ((2 / cos P.φ) * sqrt (area (gerverSofa P) - sofaArea (π / 2) K))
      K (shiftedReferenceCap P.cap K)

theorem ki_cap_distance_bound_2002 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hK : IsKi K) :
    EuclideanClose ((1001 / 500) * sqrt (area (gerverSofa P) - sofaArea (π / 2) K))
      K (shiftedReferenceCap P.cap K)
```

[`MovingSofaStability.sharp_wide_cap_distance_bound`](../MovingSofaStability/SharpCapDistance.lean#L61) and [`MovingSofaStability.wide_cap_distance_bound_2002`](../MovingSofaStability/SharpCapDistance.lean#L85) prove the same bound, in terms of
the deficit of Baek's upper bound `𝒬`, for every triple of the enlarged domain of nonsmooth caps that
the proof of stability uses. Note 01 of the archive argues that `2 sec φ` is the best constant in the
space of residuals; that is not proved in Lean, and no claim is made that it is the best constant
over feasible caps or after optimizing the translation. The proof of the stability theorem takes the
cap estimate, with the coefficient `2 sec φ`, from the coercive certificate
[`MovingSofaStability.coercive_certificate`](../MovingSofaStability/CoerciveCertificate.lean#L33) ([the coercive route](coercive.md)); the constants of the theorem are existential, so
the coefficient does not appear in its statement. [`MovingSofaStability.wide_cap_distance_bound`](../MovingSofaStability/CapDistance.lean#L121) proves the
coefficient 80 by mass estimates, which the proof of the stability theorem no longer uses.

## The proof

The informal proof is in the archived notes of the pull request ([`docs/archive/stability/`](archive/stability)):
notes 08, 05, 06 and 07 for the stability theorem, 01 for the cap estimate and 09 for the punctured
sofas. Each step below names the main modules that carry it.

1. **The deficit certificate** (`QuadraticDeficit`, `MamikonEnergy`, `WideDomain`,
   `WideGerverCertificate`, `WideResidualEnergy`). Baek's upper bound `𝒬`, a quadratic function of a
   cap and two auxiliary bodies, is extended to an enlarged domain on which the cap may have corners
   (curvature atoms). On that domain the deficit `|G| - 𝒬(ξ)` is a nonnegative dual slack plus six
   squared differences of Mamikon displacements, the energies. Only Gerver's cap is differentiated;
   the competing cap need not be smooth.
2. **From the energies to the cap** (`Residuals`, `ODEReconstruction`, `ResidualPropagation`,
   `FourArcCoercivity`, `CapCoercivity`, `CapDistance`; for the coefficient `2 sec φ`,
   `TrigKernelIntegrals`, `SharpReconstruction`, `SharpEvaluation`, `SharpCapDistance`). The support
   function of the cap is reconstructed from the residuals on the four arcs of Gerver's cap. The
   energies bound its distance to Gerver's support function, with coefficient 80 by mass estimates
   or `2 sec φ` by the exact kernel integrals, which the proof uses, and bounds on support functions
   become Euclidean distances between the caps.
3. **A local upper bound** (`ExposedFaceStability`, `LocalArmMargins`, `NicheFeet`,
   `CanonicalTriple`, `CoreIntegral`, `CutSeparation`, `CoreAreaBound`, `LocalUpperBound`). For every
   right-angle cap whose upper support function is close to Gerver's, the canonical triple is
   feasible, the niche lies in the cap, and the sofa area satisfies `A(K) ≤ 𝒬(ξ_K) ≤ |G|`, without
   Baek's injectivity condition. The exposed points, arm margins and cut separations of Gerver's cap
   persist under small perturbations, and the area of the core is computed through right
   derivatives. The bound `𝒬(ξ_K) ≤ |G|` and the distance from the cap to Gerver's come from the coercive
   certificate ([`MovingSofaStability.coercive_certificate`](../MovingSofaStability/CoerciveCertificate.lean#L33)).
4. **A missing final angle costs area** (`FloorCoverage`, `PartialHallways`, `OmittedWedgeArea`,
   `TerminalFloor`, `TerminalComparison`). If the sofa turns only through `ω < π/2`, the tilted final
   strip removes a floor region of area at least `c(π/2 - ω)`, while the omitted hallway positions
   add less, so `area S ≤ A(K) - c(π/2 - ω)`.
5. **Back to the sofa itself** (`SofaCoordinates`, `SofaCap`, `GerverRoof`, `RoofMargins`,
   `GerverMargins`, `InteriorBalls`, `MissingAreaRecovery`, `LocalSofaRecovery`,
   `ConvexParallelArea`, `SymmetricDifference`). The cap `K` of the sofa is the part of the upper
   half-plane below the sofa's upper supporting lines, and it has the sofa's upper support function.
   Gerver's sofa has uniform interior balls and a roof with uniform margins, so the distance between
   the caps and the missing area bound the Euclidean distance between `S` and `G` in both
   directions, and a parallel-body estimate bounds the symmetric difference.
6. **Entry and assembly** (`CompactSetLimits`, `SofaBounds`, `SofaLimitMotion`, `QualitativeEntry`,
   `GlobalStability`). Normalized sofas of nearly maximal area lie in a fixed rectangle, and their
   Hausdorff limits are moving sofas of maximal area, by the optimality theorem of the coercive route
   ([`MovingSofaExtremal.area_le_gerver`](../MovingSofaExtremal/Main.lean#L101)), hence Gerver's sofa by its uniqueness theorem
   ([`MovingSofaExtremal.translate_eq_gerver_of_volume_eq`](../MovingSofaExtremal/Main.lean#L129)), which does not use this step ([the coercive route](coercive.md)). So every sofa
   of small deficit enters the neighborhood where steps 2 to 5 apply; compactness gives this entry, not
   the rate.

The sharpness (`PunctureTopology`, `EuclideanDisks`, `PunctureMetric`, `RigidInterior`,
`PuncturedSofa`, `SharpExponent`) moves the punctured sofa along the motion of Gerver's sofa, and
uses a compactness argument on rigid motions: the rigid copies of `G` close to `G` keep a fixed
interior point of `G`, so no alignment brings the punctured sofa closer than `r`.

## The Lean code and the pull request

The Lean code is that of pull request #8, compiled. Its statements are unchanged, with three kinds of
exceptions:

- Twenty lemmas were false as written, because their hypotheses were declared as section variables
  and never mentioned in the statements, so that Lean left them out. An `include` now adds them,
  which is what the draft's proofs and callers assumed: [`mamikon_combo_energy`](../MovingSofaStability/MamikonEnergy.lean#L76),
  [`mamikon_midpoint_energy`](../MovingSofaStability/MamikonEnergy.lean#L114), the four slope bounds of `EnvelopeSlope`, the three envelope lemmas of
  `EnvelopeSlack`, the five lemmas of `SharpReconstruction` and the six of `SharpEvaluation`.
- Six helper lemmas lost a hypothesis that their proofs do not use.
- Two variable names that Lean does not accept were renamed.

The proofs are the draft's. Where one did not compile, only its Lean changed: names of Mathlib
lemmas, tactics, type annotations, and a few private helpers for routine steps. A separate review
compared every repaired proof with the draft's and found no change of argument.
