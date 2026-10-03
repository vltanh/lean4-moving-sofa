# Dependency ledger and implementation plan

## Status categories

- **Retained input:** a specified geometric result from Baek/Gerver/Romik, not reproved from scratch in this manuscript.
- **Written argument:** a proof supplied in the manuscript, subject to mathematical review.
- **Source counterpart:** an existing uncompiled Lean script identified for comparison, not evidence of successful elaboration.
- **Not established here:** an extension or certification that this PR does not claim.

The manuscript makes no claim that all results called 'written arguments' are independently verified. No Lean, Lake, CI, Comparator, or independent checker was run.

## 1. The graph that avoids circularity

```text
concrete Gerver feasibility and lower bound ─────────────────────┐
                                                              │
Baek's pre-optimality fixed-angle feasible-attainment theorem   │
             │                                                │
             ├── finite polygon geometry + positive width bound│
             │                │                               │
             │       persistent sampled selection             │
             │                │                               │
             │       ┌────────┴─────────┐                     │
             │   pinned limits    curvature limits            │
             │       │                 │                      │
             │   same-sofa angle   maximum-deficit bootstrap   │
             │   extension             │                      │
             │                    injectivity                 │
             │                         │                      │
             └──── feasible maxima ────┴── Q area/sign toolkit ┘
                                       │
                              GLOBAL OPTIMALITY
                                       │
                            all cap objectives <= |G|
                                       │
                      own cap of each maximizing sofa is maximal
                                       │
                      same-set reductions + zero Q deficit
                                       │
                             cap rigidity / translation
                                       │
                         regular-closed target + closed subset
                                       │
                           EXACT STARTING-SET UNIQUENESS
```

The original final theorem `MovingSofa.theorem1_1_1` is NOT an input to the node labeled GLOBAL OPTIMALITY. It may only be recovered there as a conclusion. In the current uniqueness source, `Draft.cap_area_le_gerver` calls that final theorem. Its mathematical analogue therefore moves AFTER the new upper-bound proof; simply importing that helper earlier would be circular.

## 2. Retained geometric inputs

| Input | Precise content used | Source / boundary |
| --- | --- | --- |
| G1 | Boundedness, suitable angle for a sofa of area >=11/5, normalization, monotonization preserving containment | Baek Theorem 1.5.1 and Chapter 2; no global optimality |
| G2 | An unrestricted fixed-angle cap maximum has at least one representative with niche contained in cap, hence a connected feasible sofa of the same value | Baek Theorems 3.5.2, 3.5.4-3.5.6; balanced-maximizer existence remains inside this dependency |
| G3a | Positive finite cap objective bounds horizontal width uniformly in finer meshes retaining a fixed coarse angle | Baek Lemma 3.4.2 |
| G3b | Finite objective continuity, completed inner-boundary geometry, the derivative sigma-tau, and feasible outward moves of positive facets | Baek Sections 3.1-3.4, especially Lemmas 3.4.5, 3.4.7-3.4.8 |
| G3c | Three-neighbor inner-ray geometry and gap-to-completed-inner-edge bounds | Local calculations in Baek Sections 4.1 and 6.3; their maximality-independent parts are restated in the manuscript |
| G4 | Convex triple domain, A<=Q, six-square/affine representation, and the sign of the directional derivative at Gerver | Baek Chapters 7-8; not his completed sofa-area upper bound |
| G5 | Concrete Gerver feasibility, area lower bound, phase range, and contact/envelope facts | Gerver/Romik and Baek Section 8.4; numerical enclosures remain inputs requiring proof |

This ledger is not a claim that the above sources are free of typographical errors. In particular the manuscript uses N(K) contained in K in the feasible-cap criterion, not the reversed inclusion appearing in a sentence of the arXiv HTML proof of Theorem 2.5.9. Statements are taken in their mathematically consistent direction.

## 3. Written arguments and source counterparts

| Written argument | Manuscript location | Existing source counterpart at 36dec2e |
| --- | --- | --- |
| One-step arm bootstrap | 01, Theorem 1.1 | `InjectivityFromCurvature.lean` / earlier note 11; the scalar argument can be extracted from the geometric module |
| Error-tolerant bootstrap | 01, Theorem 1.2 | New extension in this paper PR; no matching Lean theorem is claimed |
| Failure of unrestricted interval length | 01, Example 1.3 | New exact analytic counterexample in this paper PR; not a sofa |
| Fixed persistent selection | 02, Theorem 2.1 and Section 2.2 | `FixedPenaltySelection`, `DyadicSelector`, `SelectedCaps` |
| Single-sample floating variation | 02, Section 2.3 | `FloatingVariation`, `SampledPenalty`, `SupportSamples` |
| Pinned normalization and signed defects | 02, Sections 2.4-2.5 | `PinnedGeometry`, `PinnedVariation`, `PinnedLimit` |
| Endpoint-safe curvature inequalities | 02, Section 2.6 | `SelectedCurvature`, `CurvatureLimit`, `MirroredCurvature` |
| Exact affine-minus-squares deficit | 03, Proposition 3.1 | `Convex/QuadraticEquality`, `SquareGap`, `Optimality/Equality`; the Hilbert-space presentation is the paper's simplification |
| Four-equation cap rigidity | 03, Proposition 3.2 | `MamikonCapKernel`, `SupportKernelEquations`, `Draft/CapKernel` |
| Explicit cap coercivity | 03, Proposition 3.3 | Earlier paper note 17; no checked quantitative Lean theorem is asserted |
| Same-sofa angle extension | 04, Section 4.1 | `Draft/AngleExtension`, `AngleCertificates` |
| Regular-closedness and exact recovery | 04, Lemmas 4.1-4.2 | `RegularClosedEnvelope`, `GerverRegularClosed`, `SetRecovery` |
| Optimality before own-cap maximality | main, Theorem 5.1 and Corollary 5.2 | New dependency order; not already proved by importing the old Main theorem |
| Actual starting-set equality | main, Theorem 6.1 | `Draft/ShapeUniqueness`, with the preceding reordered upper-bound input |

The whole-column existence of a source counterpart does not establish that the counterpart is correct or has the same complete dependency graph. Each comparison must be made declaration by declaration during later review.

## 4. What a genuinely balance-free proof still needs

A replacement for G2 must prove BOTH attainment of the relaxed maximum and feasibility of an attaining cap:

    For each fixed angle, there is a cap C maximizing A,
    N(C) is contained in C, and C minus N(C) is the required connected sofa.

Ordinary compactness can address attainment. It does not by itself address niche containment or connectedness. The fixed-penalty theorem selects a prescribed maximizer but also does not prove those properties.

A possible research direction is a quantitative version of the polygon feasibility argument: show that a persistent excursion of the inner envelope outside the cap forces a nonvanishing allowable first-variation defect. This is a proposed lemma, not proved or assumed anywhere in the manuscript. In particular endpoint-weighted defects do not automatically control unweighted curve lengths near normals 0 and pi.

Retaining Baek's G2 is currently the honest conservative route. That route is already noncircular and can incorporate the scalar and deficit simplifications.

## 5. Proposed Lean migration, not executed work

A future source refactor should follow this order, without changing the final theorem statement:

1. Extract a Mathlib-only arm lemma using continuous nonnegative functions and the two integral inequalities. Keep the robust-error version separate until formalized.
2. Extract a generic affine-minus-squares identity in a convex domain; do not make it depend on any sofa optimum.
3. Bundle specified-maximizer stationarity with only the finite polygon and convergence inputs. Avoid imports through `MovingSofa.Main` that conceal the old optimum.
4. Give feasible attainment an explicit theorem/interface and record that its present implementation still uses Baek's Chapter 3.
5. Prove the sofa upper bound from that interface, the stationarity results, and the Q toolkit.
6. Only then derive the universal cap bound, own-cap maximality, and the original-set equality theorem.
7. Reuse the existing ordinary coordinate/motion/reference bridge for the exact formal-conjectures corollary; do not introduce an exporter, alternative reference shape, or statement-changing premise.

This PR creates no new Lean declarations and does not claim any of those migration tasks has been executed.

## 6. Numerical and verification boundaries

The paper supplies exact rational/trigonometric calculations for its new slack constants. It does not silently replace the inherited Gerver parameter enclosures, contact geometry, or Q derivative inequalities by numerical approximations. There is no decision-kernel or native evaluation step in the manuscript.

An eventual Palomar-style submission still needs the literal theorem/definition comparison, a transitive proof-method audit, only the permitted axioms in the elaborated closure, and independent checking. No configuration file alone establishes compliance. No claim of accepted publication, accepted formal-conjectures submission, or Palomar certification is made.

The status of PR #1 and any contemporaneous changes on main are separate from this paper-only PR. This ledger refers to the pinned research source, not an assumed current build result.
