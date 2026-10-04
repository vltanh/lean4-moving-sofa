# Audit of the paper and the formalization

Paper: Jineon Baek, *Optimality of Gerver's Sofa*, arXiv:2411.19826v1 (the only version, 29 November
2024). The audit was made against the arXiv LaTeX source of that version. Result, definition and
equation numbers are the paper's (chapter.section.number). A TeX location such as `05/07:67` means
line 67 of `05._Monotone_Sofas_and_Caps/07._Supporting_Hallway.tex` in the `out/` directory of the
arXiv source; the chapter directories `01, 05, 10, 15, 17, 20, 22, 25` hold the paper's Chapters 1–8.

Status of the formalization:

- Every numbered result the paper proves is proved in Lean, with the deviations listed in Sections 3,
  6 and 7, and so is the main theorem (Theorem 1.1.1): Gerver's sofa is a moving sofa, and every moving
  sofa has area at most that of Gerver's sofa.
- The results the paper takes from the literature and uses in its proofs are proved too:
  - Schneider's area formula for planar convex bodies, in [`MovingSofaOptimality/External/`](MovingSofaOptimality/External);
  - the existence and uniqueness of the solution of Romik's system that defines Gerver's sofa;
  - the remaining cited facts (weak convergence of surface area measures, Blaschke selection,
    continuity of area, Lebesgue–Stieltjes calculus), in the files that use them or in Mathlib
    (Section 2).
- Theorem 8.4.1 (the structure of Gerver's sofa), which the paper states without proof, is proved
  from Romik's equations by interval arithmetic ([`MovingSofaOptimality/Gerver/`](MovingSofaOptimality/Gerver)).
- `lake build` succeeds. The only `sorry`s are the statements of [`Challenge.lean`](Challenge.lean), which are
  `sorry` by design and proved in [`Solution.lean`](Solution.lean). There is no `axiom`, `admit`, `native_decide` or
  `implemented_by`.
- [`scripts/Audit.lean`](scripts/Audit.lean) checks that every declaration of the library, every paper result and the
  Challenge theorems depend only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound). It also lists the
  results from prior work that each paper result uses (Section 8).
- [`Challenge.lean`](Challenge.lean) restates Theorem 1.1.1, together with the existence and uniqueness of Gerver's
  parameters and the area of Gerver's sofa (between 2.2192 and 2.2199), using Mathlib's vocabulary
  only. [`Solution.lean`](Solution.lean) proves these statements from the
  library, and `lake comparator` accepts the solution. The Challenge also states the uniqueness of
  the optimal sofa, which is not a result of the paper; the README describes it.
- Statements of the paper that are false as printed are formalized in their intended form; Section 6
  lists every such correction. No result had to be weakened.
- Every proof follows the paper's argument, except at the steps that Section 7 lists, each forced by
  an error or gap of the paper, by mathematics that Mathlib lacks, or by the formalization's
  representation of the surface area measure. A route check in CI compares the results that each
  proof uses with those that the paper's proof cites (Section 8).

## 1. Summary

- **Errors.**
  - Two statements are false as written:
    - Definition 3.2.5 uses the parallelogram P_ω where the fan F_ω is meant, which makes
      Proposition 3.3.5 and Lemma 3.4.2 false (E6);
    - the direction (1) ⇒ (2) of Proposition 5.1.4 is false (E11).
  - In addition, several statements contain slips that make them false or meaningless as printed,
    although their intended form is clear: E1, E3, E7, E9, E13, E14, E20, E22, E24, E25.
  - Every result of the paper survives with the intended statements.
- **Gaps.**
  - Two proofs are missing or invalid:
    - Theorem 8.4.1, the structure of Gerver's sofa, is stated without proof (E23);
    - the proof of Theorem 6.1.2 (Gerver's sofa satisfies the injectivity condition) rests on a
      misreading of Gerver's Theorem 2 (E12).

    Both statements are true; they are proved here from Romik's equations.
  - The proofs of Lemma 8.1.7 (2), (4) and of the decomposition in Theorem 8.2.4 use 𝒩(K) ⊆ K, which
    the cap space 𝒦^i does not provide. The statements hold nevertheless (E20).
  - The other gaps are minor, and the claims hold (E2, E4, E5, E8, E10, E15, E17, E18, E19, E21).
- **Missing hypotheses.** None. No statement of the paper needs a hypothesis it does not have.
- **Redundant hypotheses.** Several statements carry hypotheses that their proofs never use, for
  instance K being a cap in the mirror identities of Proposition 2.5.4 and t ∈ [0, π/2] in
  Propositions 6.2.1 and 6.2.2. The Lean statements omit them (Section 5).
- **Use of cited results.**
  - Every cited result is used correctly except Gerver's Theorem 2 in the proof of Theorem 6.1.2 (E12).
  - The paper relies on the uniqueness of the solution of Romik's system, which Romik asserts without
    proof. It is proved here in the box φ ∈ [0.039, 0.04], θ ∈ [0.68, 0.69].

## 2. Results from prior work and how the paper uses them

### Proved in `MovingSofaOptimality/External/`

| Result | Where the paper uses it | Source | Lean |
| --- | --- | --- | --- |
| \|K\| = ½ ∫ h_K dσ_K for a planar convex body K | Theorem 7.1.3, and through it Chapter 8 (Lemma 8.3.5, Theorems 8.2.4, 8.3.8, 8.5.7) | Schneider, *Convex Bodies*, Remark 5.1.2 and Eq. (5.19) | [`area_eq_half_integral_supp`](MovingSofaOptimality/External/AreaFormula.lean#L558) ([`MovingSofaOptimality/External/AreaFormula.lean`](MovingSofaOptimality/External/AreaFormula.lean)) |
| Romik's system (27)–(44) has a solution with 0 < φ < θ < π/4 (his Table 1: φ = 0.0391773…, θ = 0.6813015…) | Definition 8.1.2 (Gerver's sofa G) | Romik 2018, Section 4 | [`GerverParams.romik_exists`](MovingSofaOptimality/External/Romik.lean#L354) ([`MovingSofaOptimality/External/Romik.lean`](MovingSofaOptimality/External/Romik.lean)), [`definition8_1_2_exists`](MovingSofaOptimality/Main.lean#L32) |
| This solution is unique | Definition 8.1.2 ("the" solution) | Romik 2018, asserted without proof | [`GerverParams.romik_unique`](MovingSofaOptimality/External/Romik.lean#L360), [`definition8_1_2_unique`](MovingSofaOptimality/Main.lean#L37) |

- [`MovingSofaOptimality/External/AreaFormula.lean`](MovingSofaOptimality/External/AreaFormula.lean) proves the area formula by a change of variables from an
  interior point along the arc-length parametrization of ∂K. The parametrization is built in
  [`MovingSofaOptimality/External/AreaFormula/Param.lean`](MovingSofaOptimality/External/AreaFormula/Param.lean) from the generalized inverse of the distribution
  function of σ_K.
- [`MovingSofaOptimality/External/Romik.lean`](MovingSofaOptimality/External/Romik.lean) eliminates the parameters that enter linearly, reducing Romik's
  system to two equations H(φ, θ) = 0. [`MovingSofaOptimality/External/Romik/Num.lean`](MovingSofaOptimality/External/Romik/Num.lean) encloses H and its
  derivatives on the box by interval arithmetic; it is generated by [`scripts/romik/mk_num.py`](scripts/romik/mk_num.py), and every
  step is a `norm_num` inequality. [`MovingSofaOptimality/External/Romik/Fix.lean`](MovingSofaOptimality/External/Romik/Fix.lean) shows that z ↦ z − M·H(z) is a
  ½-contraction of the box. This gives a unique
  zero, within 10⁻¹⁰ of (0.0391773648, 0.6813015094), and the enclosures of all parameters
  ([`GerverParams.romik_bounds`](MovingSofaOptimality/External/Romik.lean#L522)) that the numerical verifications use.

### Cited results proved where they are used

| Cited result | Where the paper uses it | In the formalization |
| --- | --- | --- |
| Schneider Theorem 4.2.3: σ_K(X) is the length of ⋃_{t∈X} e_K(t) (the paper's Theorem 2.1.1) | Proposition 2.1.2 and the side lengths throughout | σ_K is defined directly, as the Lebesgue–Stieltjes measure of t ↦ ⟨v_K⁺(t), v_t⟩ + ∫₀ᵗ h_K ([`sigma`](MovingSofaOptimality/Basic/SurfaceArea.lean#L169), [`MovingSofaOptimality/Basic/SurfaceArea.lean`](MovingSofaOptimality/Basic/SurfaceArea.lean)). Proposition 2.1.2 (σ_K({t}) is the length of e_K(t)) and Theorem 5.2.2 (dv_K⁺ = v_t dσ_K) are proved from this definition. [`MovingSofaOptimality/External/AreaFormula/Param.lean`](MovingSofaOptimality/External/AreaFormula/Param.lean) shows that the normal angle along the arc-length parametrization of ∂K pushes Lebesgue measure forward to σ_K, which is Theorem 2.1.1 in arc-length form. |
| Schneider Lemma 1.8.14: d_H(K, L) = sup_t \|h_K(t) − h_L(t)\| | Chapter 3 (limits of caps) | Hausdorff distance is defined in this support-function form ([`hausdorffDist`](MovingSofaOptimality/Basic/ConvexBody.lean#L83)). The comparison with Mathlib's Hausdorff distance needed for Blaschke's theorem is proved in [`mpc_blaschke`](MovingSofaOptimality/Balanced/MaxPolygonCapExists.lean#L846). |
| Blaschke selection theorem | Theorems 3.4.3, 3.5.2 | Mathlib (compactness of nonempty compact sets in the Hausdorff metric), via [`mpc_blaschke`](MovingSofaOptimality/Balanced/MaxPolygonCapExists.lean#L846) |
| Schneider Theorem 1.8.20: area is continuous in d_H | Theorems 3.4.3, 3.5.5 | proved ([`mpc_tendsto_area`](MovingSofaOptimality/Balanced/MaxPolygonCapExists.lean#L889), from the one-sided forms [`mpc_area_usc`](MovingSofaOptimality/Balanced/CapGeometry.lean#L282) and [`mpc_area_lsc`](MovingSofaOptimality/Balanced/CapGeometry.lean#L296)) |
| Schneider Theorem 4.2.1: σ is weakly continuous in K (the paper's Theorem 4.1.3) | Theorem 4.1.4, Lemma 6.4.2, Theorem 6.4.3 | [`theorem4_1_3`](MovingSofaOptimality/Angle/HorizontalSide.lean#L844), proved by integration by parts against the distribution function of σ and dominated convergence; the three results use it as the paper does, through the Portmanteau theorem |
| Schneider Eq. (4.14): σ of a reflected body | Proposition 2.5.4 | proved directly ([`proposition2_5_4_sigma`](MovingSofaOptimality/Monotone/CapContainsNiche.lean#L583)) |
| Schneider Theorem 1.7.5(a) and Remark 1.7.7: h_{K+L} = h_K + h_L | Theorem 7.1.2 | proved ([`cvx_supp_convexBodyComb`](MovingSofaOptimality/Convex/ConvexDomain.lean#L206)) |
| Revuz–Yor Theorem 4.3 (Lebesgue–Stieltjes measures) and Proposition 4.5 (integration by parts) | Chapter 5: the measures df, and Lemma 5.1.2, through which the later integrations by parts go | Mathlib's measures of functions of bounded variation (`BoundedVariationOn.vectorMeasure`) and their integration by parts (`BoundedVariationOn.setIntegral_Ioc_leftLim_smul_vectorMeasure_eq_sub`), used in the proof of Lemma 5.1.2; the integrations by parts of Lemma 5.1.3 and Theorems 7.4.1, 8.5.2 and 8.5.4 go through Lemma 5.1.2, for cross products coordinate by coordinate |
| Jordan curve theorem; Green's theorem (Apostol, Theorem 10.43) | Theorems 7.2.1, 7.2.3, Proposition 7.2.7, and through them Lemmas 7.3.5, 8.2.2, 8.2.3 and Theorem 8.4.1(2) | not used: each area these results are used for is computed directly (Section 7) |
| Brunn–Minkowski inequality | Theorem 8.1.1 (1) | not used: the area condition of 𝒦^i is shown to be preserved by a slicing argument ([`opt_comb_area`](MovingSofaOptimality/Optimality/Domain.lean#L396); Section 7) |
| Gerver 1992, Theorem 2 | Theorem 6.1.2 | not used: Theorem 6.1.2 is proved from Romik's equations (E12) |

### Standard facts used without citation

| Fact | Where | In the formalization |
| --- | --- | --- |
| Intermediate value theorem | Chapters 1, 7, 8 | `intermediate_value_Icc` |
| Fundamental theorem of calculus | throughout | `intervalIntegral.integral_eq_sub_of_hasDerivAt` and variants with countably many exceptions |
| Cavalieri's principle, Fubini–Tonelli | Theorems 1.5.1, 3.1.2, 8.1.1, Chapter 8 | `MeasureTheory.Measure.prod_apply`, `MeasureTheory.lintegral_prod`, `volume_regionBetween_eq_integral` |
| Change of variables in the plane | Theorem 7.1.3, the niche of Gerver's sofa | `lintegral_abs_det_fderiv_eq_addHaar_image` |
| Radon–Nikodym theorem | Corollary 6.4.4 | `MeasureTheory.Measure.withDensity_rnDeriv_eq` |
| Lebesgue differentiation theorem | Proposition 5.1.4, and Theorem 6.5.1 through it | Mathlib (`Mathlib/MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean`) |
| Dominated convergence | Theorem 4.1.3 | `intervalIntegral.tendsto_integral_filter_of_dominated_convergence` |
| Portmanteau theorem | Theorem 4.1.4, Lemma 6.4.2, Theorem 6.4.3 | derived from Theorem 4.1.3 for the measures σ_K on the circle: for lower and upper semicontinuous functions, open and closed sets ([`ang_portmanteau_lsc`](MovingSofaOptimality/Angle/HorizontalSide.lean#L969), [`ang_portmanteau_usc`](MovingSofaOptimality/Angle/HorizontalSide.lean#L999), [`ang_portmanteau_open`](MovingSofaOptimality/Angle/HorizontalSide.lean#L1034), [`ang_portmanteau_closed`](MovingSofaOptimality/Angle/HorizontalSide.lean#L1048)) |
| Banach fixed point theorem | (Romik's system) | `ContractingWith.exists_fixedPoint'` |

### Does the paper use each cited result correctly?

| Cited result | Where | Verdict |
| --- | --- | --- |
| Schneider Theorem 4.2.3, Lemma 1.8.14, Theorem 1.8.20, Theorem 4.2.1, Eq. (4.14), Theorem 1.7.5(a), Remark 5.1.2, Eq. (5.19) | Chapters 2–8 | correct |
| Revuz–Yor Theorem 4.3, Proposition 4.5 | Chapter 5 | correct (Proposition 5.1.4 is the paper's own; see E11) |
| Brunn–Minkowski inequality | Theorem 8.1.1 | correct (the multiplicative form, which follows from the additive one) |
| Gerver 1992, Theorem 2 | Theorem 6.1.2 | misapplied (E12) |
| Romik 2018, Equations (9)–(12), (25)–(44), Theorem 2 and Table 1 | Definitions 8.1.2, 8.4.1–8.4.3, Theorem 8.4.2 | correct; the uniqueness of the solution is used but not proved by Romik, and is proved here |

The following citations give context only and are not used in proofs: Moser 1966; Hammersley; Kallus
and Romik 2018 (the upper bound 2.37); Gibbs; Batsch; Leng; Deng; Stone 1949; Marckert 2014; Bieri
(terminology); Mnatsakanian (Mamikon's theorem, which the paper reproves as Theorem 7.4.1).

## 3. Errors and gaps in the paper

**E1. Definition 2.3.9** (`def:line-half-plane-directions`, `05/10:105`). "Assuming l is not parallel
to the y-axis, call the left side … the closed half-plane … containing the point −Nu₀". The condition
should be "not parallel to the x-axis": for a horizontal line the points ±Nu₀ lie on the same side,
while for a vertical line the definition works (and the proof of Theorem 2.3.6 applies it to the
vertical line l_{π/2}). Typo; the Lean definitions [`leftSide`](MovingSofaOptimality/Sofa/Defs.lean#L154) and [`rightSide`](MovingSofaOptimality/Sofa/Defs.lean#L157) follow the intended
reading.

**E2. Theorem 2.4.2 and Definition 2.4.5** (`05/12:82`, `05/12:63`). The theorem's formula takes the
union over t ∈ [0, ω], the definition of the niche over t ∈ (0, ω). The two agree because
F_ω ∩ Q⁻_K(0) = F_ω ∩ Q⁻_K(ω) = ∅ (Q⁻_K(0) lies below y = 0, Q⁻_K(ω) below l(ω, 0)); the paper does not
say so. Trivial gap; the theorem holds.

**E3. Proposition 2.5.4** (`pro:mirror-reflection`, `05/15:99–101`). The first bullet claims
?_{K^m}(t) = M_ω(?_K(ω − t)) for ? = L, 𝐱, 𝐲, a, b, c, d, W, Z, but the reflection M_ω exchanges a ↔ c,
b ↔ d and W ↔ Z; only L, 𝐱, 𝐲 map to themselves. The second bullet should have K, not K^m, on the right:
A^±_{K^m}(t) = M_ω(C^∓_K(ω − t)). The third bullet is consistent with the exchanges. Slips in the
statement; the Lean statements ([`proposition2_5_4_hallway`](MovingSofaOptimality/Monotone/CapContainsNiche.lean#L496), [`proposition2_5_4_vertices`](MovingSofaOptimality/Monotone/CapContainsNiche.lean#L524)) are the
corrected ones.

**E4. Lemma 2.5.6 and Theorem 2.5.8 (4 ⇒ 3)** (`lem:niche-in-cap`, `05/15:151–168`; `05/15:212`). The
proofs use, without proof, two facts about every cap K:

- (a) C⁺_K(ω) lies on l(ω, 0) and A⁻_K(0) on l(π/2, 0);
- (b) the origin lies in K when ω < π/2 (cases 2 and 4 of Lemma 2.5.6 use O as a vertex of the
  wedge).

Both hold. For (b): A⁻_K(0) = (a, 0) with a ≥ 0 and C⁺_K(ω) = λv_ω with λ ≥ 0, so every half-plane
H₋(s, k) defining K with s in J_ω has k ≥ 0. For ω = π/2, O need not lie in K (K = [5, 6] × [0, 1] is a
cap), but the paper's proof of that case does not use O. Minor gap; both results hold. The Lean proof
of Lemma 2.5.6 follows the paper's cases and proves (a) (`IsCap.cPlus_eq_corner`, and
`IsCap.aMinus_eq_corner` from it by Proposition 2.5.4) and (b) (`IsCap.zero_mem`).

**E5. Theorem 3.1.2 and Lemma 3.4.7** (`thm:simple-nef-polygon`, `lem:balancing`, `10/15:215–223`).
Lemma 3.4.7 applies Theorem 3.1.2 twice, the second time to the polygon already modified by the first
application, while Theorem 3.1.2 gives constants ε(X, i) and O_{X,i}(δ²) that depend on the polygon X.
The paper's one-line justification (the two changed strips are disjoint) is the right one: for ε < 1
the change of area splits into two changes of the fixed polygon C_Θ(h). Minor gap; the lemma holds.

**E6. Definition 3.2.5** (`def:angled-niche`, `10/11:64`): 𝒩_Θ(K) = P_ω ∩ ⋃_{t∈Θ} Q⁻_K(t). The rest of
the paper uses F_ω instead of P_ω: Definition 3.3.3 (𝒩_Θ(h) = F_h ∩ …), the overview, and the proofs
of Lemma 3.4.2, Theorem 3.4.4, Lemma 3.4.5, Theorems 3.5.4 and 4.1.2.

- With P_ω, Proposition 3.3.5 (𝒩_Θ(h_K) = 𝒩_Θ(K)) is false. Take ω = π/2, Θ = {π/4} and the cap
  K = {0 ≤ y ≤ 1, x + y ≤ 101, y − x ≤ 1}. Then 𝐱_K(π/4) = (50.000, 49.586), and
  \|P_ω ∩ Q⁻_K(π/4)\| = 98.17 while \|F_ω ∩ Q⁻_K(π/4)\| = 2458.75.
- With P_ω, Lemma 3.4.2 (caps with 𝒜_Θ(K) > 0 have bounded width) is also false. For
  K = C_{π/4}([0, d] × [0, 1]), every horizontal slice of K exceeds that of the P_ω-niche by
  sec t + csc t, so 𝒜_Θ(K) = 2√2 for every d.

Error. With F_ω every result of Chapter 3 holds; the Lean definition [`polyNiche`](MovingSofaOptimality/Balanced/PolygonCap.lean#L53) uses the fan F_ω.

**E7. Proposition 3.3.1 (2)** (`pro:cap-trans-space`, `10/12:20`). "K′ is a convex polygon with normal
angles in the set Θ^◇". Since Θ^◇ ⊂ (0, π], no bounded polygon with nonempty interior has all its
normal angles there. The bottom normals ω + π and 3π/2 are missing; the proof of Proposition 3.3.2
uses Θ^◇ ∪ {ω + π, 3π/2}. Slip in the statement; the Lean statement ([`proposition3_3_1`](MovingSofaOptimality/Balanced/PolygonCap.lean#L423), through
[`AngleSet.capAngles`](MovingSofaOptimality/Balanced/PolygonCap.lean#L38)) includes the bottom normals.

**E8. Theorems 3.4.3, 3.5.2 and 3.5.4** (`10/15:49`, `10/20:47`, `10/20:69`).

- In Theorem 3.4.3, the domain ℬ_Θ is compact by the Blaschke selection theorem only if a Hausdorff
  limit of its members is again a polygon cap with angle set Θ, which the proof does not show. It
  holds for the limit of a maximizing sequence, whose area is at least 𝒜_Θ(K₁) > 0, so that it has
  an interior point. Also, ℬ_Θ should require 𝒜_Θ(K) > 0, as Lemma 3.4.2 does; K₁ is still in it.
- "Checking K ∈ 𝒦^c_ω is easy" in Theorem 3.5.2: a Hausdorff limit of caps is a cap. The value
  conditions follow from uniform convergence of the support functions, but the closedness condition
  K = ⋂_{t∈J_ω∪{ω+π,3π/2}} H_K(t) is not proved. It holds: the normal cones of the approximating caps
  are arcs with endpoints in a closed set whose gaps have length at most π/2.
- In the proof of Theorem 3.5.4, "either 𝒩_{Θ_j}(K) is empty or 𝒩_{Θ_j}(K_i) → 𝒩_{Θ_j}(K)" need not
  hold, since a wedge can be empty for K but not for K_i. Lemma 3.5.3 only needs that each point of
  𝒩_{Θ_j}(K) lies in 𝒩_{Θ_j}(K_i) for large i, which holds because the quadrants Q⁻ are open.

Minor gaps; the theorems hold.

**E9. Lemma 4.2.4** (`lem:calculation-inequalities`, `15/10:102`). The lemma assumes
ω ∈ [tan⁻¹(2.2), π/2), but its proof also treats ω < tan⁻¹(2.2), and Theorem 4.2.5 applies it on all of
[sec⁻¹(2.2), π/2), where sec⁻¹(2.2) = 1.09893 < tan⁻¹(2.2) = 1.14417. The hypothesis should read
ω ∈ [sec⁻¹(2.2), π/2).

- The recomputed endpoint values are 0.957571, 0.871398, 0.934932, and exactly 1 at π/2.
- The strict inequality on (tan⁻¹ 2.2, π/2) needs one more line: a convex function with values < 1 at
  the left end and = 1 at the right end is < 1 in between.

Slip in the statement and a trivial gap. [`lemma4_2_4`](MovingSofaOptimality/Angle/RightAngle.lean#L523) is stated on [sec⁻¹(2.2), π/2).

**E10. Theorem 1.5.2, proof** (`thm:angle`, in `15/10:178`). "the set P_ω \ Δ_ω has width ≤ 1 for every
direction u_t with t ∈ [ω, π/2]" is asserted without proof. It is true: P_ω \ Δ_ω is a pentagon whose
width in direction u_t is max(sin t, cos(t − ω)) ≤ 1. Trivial gap.

**E11. Proposition 5.1.4** (`pro:lebesgue-stieltjes-abs-cont`, `17/17:91–111`). The proposition
claims that a right-continuous f of bounded variation is absolutely continuous if and only if
df = r dt for a measurable and *bounded* r. The direction (1) ⇒ (2) is false.

- Counterexample: f(t) = 2√t on [0, 1] is absolutely continuous, with df = t^{−1/2} dt. The density is
  unique almost everywhere, and it is unbounded.
- The proof never shows that the derivative is bounded.
- The correct statement takes r integrable. The paper uses the proposition once, in the proof of
  Theorem 6.5.1, in the direction (2) ⇒ (1) together with the a.e.-derivative clause, for a bounded r.
  That use is correct.

Error; Theorem 6.5.1 survives. [`proposition5_1_4`](MovingSofaOptimality/Basic/LebesgueStieltjes.lean#L541) is the correct version (r integrable), and
[`proposition5_1_4_deriv`](MovingSofaOptimality/Basic/LebesgueStieltjes.lean#L580) is the derivative clause with bounded r. [`proposition5_1_4_as_stated_false`](MovingSofaOptimality/Basic/LebesgueStieltjes.lean#L607)
refutes the statement as printed, with the counterexample above.

**E12. Theorem 6.1.2** (`thm:injectivity-gerver`, `20/02:39–48`). The proof reads: "Theorem 2 of
[Gerver 1992] explicitly constructs a sequence of maximum polygon sofas converging to Gerver's sofa G.
So G is a balanced maximum sofa, and Theorem 6.1.1 proves the claim."

- This cannot be right. If the cap of G were a limit of maximum polygon caps, Theorem 3.5.5 would make
  it a maximizer of 𝒜_{π/2}. With Theorems 1.5.1 and 1.5.2 that would already be the main theorem,
  which Gerver only conjectured.
- The paper's own introduction (`01/01/00:46`) describes Gerver's Theorem 2 as showing that G
  satisfies the local optimality (balancedness) condition, not that it is a limit of maximizers.
- Remark 6.1.1 notes that the statement can be checked from Romik's equations.

Gap: the proof is invalid as written; the statement is true. [`theorem6_1_2`](MovingSofaOptimality/Gerver/Properties.lean#L168) is proved from Romik's
formulas ([`gv_injectivity`](MovingSofaOptimality/Gerver/Structure.lean#L140)): σ_K is absolutely continuous on [0, π/2) and on (π/2, π], with densities
⟨𝐀′(t), v_t⟩ and ⟨−𝐂′(t − π/2), u_{t−π/2}⟩; the inner corner is the path 𝐱, which is C¹; and
𝐱′·u_t < 0 < 𝐱′·v_t on (0, π/2).

**E13. Proposition 6.2.2** (`pro:cap-tangent-arm-mirror`, `20/05:30`). "f^±_{K^m}(t) = g^∓_K(t)" should
read f^±_{K^m}(t) = g^∓_K(π/2 − t), and likewise for g, because the reflection also reverses the angle.
Lemma 6.5.2 uses this corrected form. Slip in the statement; [`proposition6_2_2`](MovingSofaOptimality/Injectivity/ArmLengths.lean#L158) is the corrected one.

**E14. Definition 6.2.2 and Theorem 6.2.3** (`def:left-right-derivative`, `thm:inner-corner-deriv`,
`20/05:43`, `20/05:56`). The definition calls ∂⁺ the left derivative, while Theorem 6.2.3 uses it as the
right derivative; and the second display of Theorem 6.2.3 writes ∂⁺𝐱_K where ∂⁻𝐱_K is meant. Typos; the
Lean statements use one-sided derivatives within [t, ∞) and (−∞, t].

**E15. Lemma 6.3.1** (`lem:leg-bounded`, `20/10:29`). The proof cites Theorem 3.5.4 (balanced maximum
caps) to obtain condition (1) of Theorem 2.5.8, 𝒩(K) ⊆ K, for a maximum *polygon* cap K. The applicable
result is Theorem 3.4.10 (𝒩_Θ(K) ⊆ K), which only gives what is needed for the wedge at π/4: the inner
corner 𝐱_K(π/4) has height at most 1. The diameter bound 2 + 2√2 < 5 is correct (H ∩ Q⁺_K(π/4) is a
trapezoid whose diameter is its base). Minor gap with a wrong reference; the lemma holds.

**E16. Definition 6.4.1** (`def:cap-nondegenerate`, `20/15:134`): "f_K, g_K : [0, π/2] → ℝ²" should map
to ℝ. Typo.

**E17. Theorem 6.5.1, Lemmas 6.5.2–6.5.5 and Theorem 6.5.6** (`20/20`).

- (a) Lemma 6.5.2 needs f_K(0) ≥ 1, which is never stated. It holds: A_K(0) lies on y = 0 by fact (a)
  of E4, so f_K(0) = 1.
- (b) Theorem 6.5.6 claims f_K(t) > 1 on (0, π/2] and g_K(t) > 1 on [0, π/2), "by Lemma 6.5.2 and
  Lemma 6.5.5". But Lemma 6.5.2 compares f_K with f_n only on [0, π/2), and g_K only on (0, π/2]. The
  endpoint values f_K(π/2) and g_K(0) follow from the continuity of f_K and g_K (Proposition 6.4.6).
- (c) Lemma 6.5.5 states its conclusion on (0, 1], and the proof of Lemma 6.5.3 opens with
  x ∈ [0, 1], although the lemma is stated on [0, π/2]; the proofs, and Theorem 6.5.6, need
  [0, π/2] and (0, π/2].

Minor gaps and slips. The constants of Lemma 6.5.3 were recomputed: the minimizers
c = 7/6 − π/4 and c = 5/3 − π/2 lie in [0, 2/3], with minimum values 0.12782 and 0.005644. The Lean
statements of Lemmas 6.5.3 and 6.5.5 use the ranges [0, π/2] and (0, π/2].

**E18. Lemma 8.1.5, proof** (`25/03:155`). "Because \|K\| ≥ 2.2, the edge e_K(3π/2) has length ≥ 2.2" is
not justified. The reason is that for a cap with ω = π/2 the horizontal width does not increase with
height (right-boundary normals lie in [0, π/2], left ones in [π/2, π]), so \|K\| ≤ \|e_K(3π/2)\|. Minor
gap.

**E19. Lemma 8.3.5, proof** (`lem:upper-boundary-tracing`, `25/10:129`). The proof applies Theorem 7.3.2
to the curve 𝐮_K^{0,π}, outside its range a < b < a + π. The identity it needs follows anyway: split
(0, π) at φ^R, φ^L, π/2 into atoms and intervals of length < π, apply Theorem 7.3.2 on each interval,
and note that the atoms at φ^R, φ^L vanish by the injectivity condition while the atom at π/2
contributes 𝒥(A_K(π/2), C_K(0)). Minor gap.

**E20. Lemma 8.1.7 (2), (4) and Theorem 8.2.4** (`lem:right-left-body`, `thm:upper-bound-q`,
`25/03:200–213`, `25/05:123`).

- The proof of Lemma 8.1.7 (2) argues that a boundary point p of K is outside the niche "by (2) of
  Theorem 2.5.8", which presupposes 𝒩(K) ⊆ K. The proof of Theorem 8.2.4 splits \|𝒩(K)\| into three
  disjoint pieces, which also uses that the niche avoids H̆^R_K ∩ H̆^L_K.
- The cap space 𝒦^i does not give 𝒩(K) ⊆ K. Let K₅ be the union of [1, 4] × [0, 1] and the quarter
  discs of radius 1 centred at (1, 0) and (4, 0). It lies in 𝒦^i: σ = dt on the arcs, f = 1 + 3 sin t
  and g = 1 + 3 cos t, and \|K₅\| = 3 + π/2. Its inner corner is 𝐱_K(π/4) = (2.5, 1.5) ∉ K₅.
- Both statements hold nevertheless.
  - For Lemma 8.1.7 (2), let p be the topmost point of K on b^R_K and d(t) = h_K(t) − p·u_t, so
    d(φ^R) = 1, and let θ ∈ [φ^R, φ^R + π] be a normal angle of K at p. If θ > φ^R + π/2, then
    p·u_{φ^R} ≤ C_K(φ^R)·u_{φ^R}, so g_K(φ^R) ≤ 1, contradicting the injectivity condition (3).
    Otherwise the sublinearity of h_K bounds d on [φ^R, θ] by interpolation between d(φ^R) = 1 and
    d(θ) = 0, and on [θ, π/2] by interpolation using h_K(π/2) = 1 and p_y ≥ 0. So d ≤ 1 on
    [φ^R, π/2], that is, p ∈ B_K.
  - For Theorem 8.2.4, adding the defining inequalities of H̆^R_K and H̆^L_K shows that their
    intersection lies above height Y* = (h_K(φ) + h_K(π − φ) − 2)/(2 sin φ). The niche lies below the
    inner corners, whose height is at most W₀/2, where W₀ = h_K(0) + h_K(π) ≥ \|K\| ≥ 2.2. Since
    W₀(cos φ − sin φ) > 2, we get W₀/2 < Y*.

  In Lemma 8.1.7 (4) the equality is claimed "at t = 0, φ^R"; it should be φ^L.

Gap in the proofs, and a slip in (4). The Lean statements are the paper's (with φ^L in (4)), proved by
these arguments.

**E21. Theorem 8.1.1 (2) and Theorem 8.1.8.** Covered by E20; no separate issue.

**E22. Lemma 8.3.6 (3)** (`lem:linvals`, `25/10:151`). The statement evaluates the tangent-line
parametrization 𝐥_K^{π/2+φ^L} at φ^L, where it equals 𝐲_K(φ^L), so its left side 𝒥(𝐲_K(φ^L), 𝐲_K(φ^L))
is 0. The statement would then claim that 𝒥(Z^L_K, 𝐱^L_K) is linear in K, which is false (it contains
the term −c² cot φ^L/2 with c = h_K(π/2 + φ^L) − 1). The term the paper uses later (`25/10:197`) evaluates
at π/2. Slip in the statement (false as printed); [`lemma8_3_6`](MovingSofaOptimality/Optimality/Concavity.lean#L889) evaluates at π/2.

**E23. Theorem 8.4.1** (`thm:gerver-monotone`, `25/12:43–74`). The theorem is stated without proof.
Remark 8.4.1 notes that its properties are "easy to verify numerically and implicitly assumed" in the
literature, but that "a rigorous symbolic verification … would still be worthy". It asserts that:

- G is a monotone sofa with cap K;
- the curves 𝐀, 𝐂 and 𝐱 are the vertices and the inner corner of K;
- the niche is the region enclosed by 𝐁, 𝐱|[t₁,t₄], 𝐃 and the x-axis;
- 𝐁 and 𝐃 lie on the walls, with 𝐁′ a negative multiple of v_t and 𝐃′ a positive multiple of u_t.

Gap (an unproved theorem; true). The formalization proves it from Romik's equations:

- [`MovingSofaOptimality/Gerver/Frame.lean`](MovingSofaOptimality/Gerver/Frame.lean) writes each phase in a rotating frame, x = R_t w + κ, with x′ = αu_t + βv_t.
- [`MovingSofaOptimality/Gerver/StructureCap.lean`](MovingSofaOptimality/Gerver/StructureCap.lean) constructs the cap K_G = {y ≥ 0} ∩ ⋂_{σ∈[0,π]} H₋(σ, H(σ)) from the path.
  It shows that G = K_G \ 𝒩(K_G) is a monotone sofa (Theorems 2.5.8–2.5.9) and identifies the
  vertices.
- The niche (part (2)) is the delicate part, since the margins are about 10⁻³ near t = π/4 and two
  points are tangencies. [`MovingSofaOptimality/Gerver/Envelope.lean`](MovingSofaOptimality/Gerver/Envelope.lean) shows that the niche of a rotation path is exactly the
  region strictly under the curve 𝐃 ∪ 𝐱 ∪ 𝐁. The key observation is that a point p avoids the quadrant
  Q⁻(s) as soon as (p − 𝐱(s))·u_σ ≥ 0 for some σ ∈ [s, s + π/2]. Monotonicity in the remaining variable
  then reduces the two-parameter family of inequalities to one-variable ones, which
  [`MovingSofaOptimality/Gerver/NicheBounds.lean`](MovingSofaOptimality/Gerver/NicheBounds.lean) verifies.
- [`MovingSofaOptimality/Gerver/EnvelopeArea.lean`](MovingSofaOptimality/Gerver/EnvelopeArea.lean) and [`MovingSofaOptimality/Gerver/Niche.lean`](MovingSofaOptimality/Gerver/Niche.lean) compute the niche's area as
  𝒥(𝐱|[t₁,t₄]) − 𝒥(𝐁) − 𝒥(𝐃).

**E24. Theorem 8.4.3 (2)** (`thm:gerver-left-right`, `25/12:151`): "𝐱^R_K = X_{B_K} = 𝐃(t₃)" should be
𝐁(t₃); 𝐃 is defined on [t₀, t₂] only. Slip in the statement; [`theorem8_4_3_two`](MovingSofaOptimality/Gerver/Properties.lean#L1680) uses 𝐁(t₃).

**E25. Proposition 8.4.4 (4)** (`pro:measure-translation`, `25/12:202`): "⟨𝐃′(t), u_t⟩ dt = σ̆_D as
measures on t ∈ (t₀, t₂]". Since 𝐃(t) = v_{D_K}(3π/2 + t), σ̆_D lives on (π/2 + t₀, π/2 + t₂], with density
⟨𝐃′(τ − π/2), u_{τ−π/2}⟩, the same shifted form as item (3). Theorems 8.4.5 and 8.5.6 use this form. As
printed, the left side is σ_{D_K} on (π, π + θ], which is 0. Slip in the statement;
[`proposition8_4_4`](MovingSofaOptimality/Gerver/Properties.lean#L1203) is the shifted form.

**E26. Typos.**

- Theorem 2.1.3 (`05/05:156`, `05/05:175–177`): v_K⁺(t), v_K⁻(u) for v_K⁺(s), v_K⁻(s); v^±_K(u) for
  v^±_K(t₀); g_K(t₀) for H_K(t₀).
- Proposition 2.2.2 (`05/07:67`): the second half-plane of Q⁻_S(t) lacks its "− 1"; the Lean statement
  has it.
- Theorem 2.3.6, proof (`05/10:163`): l_θ \ X for l_θ ∩ X.
- Theorem 2.4.1, proof (`05/12:40`): the directions v₀, u_ω should be −v₀, −u_ω.
- Lemma 2.5.6, proof (`05/15:159`): in case 1, x_K(t) ∈ K forces x_K(t) = O and T_K(t) = ∅; this is not
  a contradiction, but the conclusion holds.
- Theorem 2.5.9, proof (`05/15:225`): "𝒩(K) contains K" for "K contains 𝒩(K)"; and
  K \ 𝒩(K) = 𝓘(S) is Theorem 2.4.2 (S is a moving sofa with cap K), not Theorem 2.4.3, which
  assumes S monotone.
- Theorem 3.1.2, proof (`10/10:97`): H₋(t, x) for H₋(t_i, x).
- Lemma 3.4.7, proof (`10/15:221`): the sign of the change of \|𝒩_Θ\| is reversed; with the printed sign
  the lemma does not follow.
- Theorem 3.4.3, proof (`10/15:47`): h_K(t) for h_K(t + π/2). Theorem 3.4.4, proof (`10/15:87`): Q_K(t)
  for the half-line l⃗_K, and a bold r_K.
- Theorem 3.4.10, proof (`10/15:281`): A⁻_K(0) − p for p − A⁻_K(0).
- §3.3–3.4: h := h_K for h_{K′} (Proposition 3.3.4); 𝒜_Θ(h′) for 𝒜_Θ(h) (Definition 3.3.4);
  𝒦′_Θ and 𝒦^c_Θ for 𝒦^t_Θ (Theorems 3.3.6, 3.4.9); K_Θ for 𝒦^c_Θ (Remark 3.4.1); "width less than
  zero" for "less than one" (Lemma 3.4.8, footnote); Theorem 3.5.2's statement is garbled at
  "a balanced maximum cap 𝒦^c_ω".
- Theorem 3.5.2, proof (`10/20:47`): the diameter bound √(1 + c) should be √(1 + c²). Theorem 3.5.5,
  proof: the index n should be i.
- Theorem 4.1.4 (`15/05:65`): a stray reference inside the statement. Lemma 4.1.1, proof (`15/05:18`):
  l_K(t) for b_K(t).
- Lemma 4.2.2, proof (`15/10:46`, `15/10:50`): o_ω − v_ω for o_ω − u_ω; R_ω for R_{ω,1.1}.
- Theorem 4.2.5, proof (`15/10:158`, `15/10:150`): H°₋(h_K(t) − 1, t) for H°₋(t, h_K(t) − 1), and an
  empty reference "()".
- Lemma 5.2.1, proof (`17/20:11`): the interval [3π/4, 2π] is not one on which the coordinates of v_K⁺
  are monotone; it should be split. Theorem 5.2.2, proof (`17/20:33`): u_t σ for v_t σ.
- Lemma 6.3.2 (1) (`20/10:73–75`): d_K(t + δ) for d_K(t − δ), and "t and t + δ adjacent" for "t − δ
  and t".
- Theorem 6.3.3, proof (`20/10:124`, `20/10:150`): 𝓗¹ missing inside a max; ν_K for τ_K.
- Lemma 6.4.2, proof (`20/15:44`): σ({t}) = 0 for σ({t + π/2}) = 0. Theorem 6.4.3 (`20/15:90–91`):
  g⁺_{K_n} − g⁺_{K_n} for g⁺_{K_n} − g⁺_K. Corollary 6.4.4 (`20/15:107`): "condition (4)" does not
  exist; condition (1) is meant.
- Lemma 6.5.2 (`20/20:58–60`): m₀(f_K(π/2 − u)) for m₀(f_n(π/2 − u)).
- Proposition 7.2.4, proof (`22/10:125`): s for d. Proposition 7.2.6: the proof is truncated (the claim,
  additivity of the integral, is immediate). Proposition 7.2.7 (`22/10:169`): "clockwise" for
  "counterclockwise". Theorem 7.2.1 (`22/10:14`): ∂U = ∂V = X for Γ.
- Lemma 7.3.1, proof (`22/20:52`): v_K⁺(a) − v_K⁻(b) = αv_a + βv_b for v_K⁻(b) − v_K⁺(a) = αv_a + βv_b,
  which is the vector τv_{t′}.
- Theorem 7.4.1, proof (`22/30:48`): αu_t for αv_t (the result is unaffected).
- Lemma 8.1.6, proof (`25/03:179`): the spanning directions u_t, −v_t for −u_t, v_t.
- Definition 8.3.3 (`25/10:60`): ℛ_B uses π/2 + φ^R; it should be π + φ^R (with π/2 + φ^R both the curve
  and its endpoints change). Lemma 8.3.4, proof (`25/10:100`): "Definition of 𝒮_K" for 𝒫_K.
- Lemma 8.3.6, proof of (1) (`25/10:163–164`): ∫₀^ω for ∫_{φ^R}^{φ^L}. Lemma 8.3.7, proof
  (`25/10:216`, `25/10:228`): 𝒥₄₂ = h_K(π)/2, not h_K(π/2)/2, and 𝒥₁₂ lacks a factor ½ (both terms are
  ≡_K 0).
- Theorem 8.5.7, proof (`25/15:170–231`): "nonnegative" for "nonpositive" (twice); J₁ for J₁₀; it cites
  Lemma 8.1.7 (1), (3) for an arbitrary (K*, B*, D*) ∈ 𝓛, where Definition 8.1.3 (2)–(5) is meant.
- Table of symbols (`A1:26–27`, `A1:51`, `A1:79`): H and V are swapped; 𝒦^i is described without the
  condition \|K\| ≥ 2.2; 𝐳 should map to ℝ².

## 4. Missing hypotheses

None. Every statement of the paper is true without additional hypotheses, once the slips of
Section 3 are corrected. In particular, the hypothesis 𝒩(K) ⊆ K that the proofs of Lemma 8.1.7 and
Theorem 8.2.4 use is not needed by their statements (E20).

## 5. Redundant hypotheses

The following hypotheses of the paper's statements are not used by their proofs. The Lean statements
omit them, so they are more general than the paper's.

| Result | Hypothesis that is not needed | Lean |
| --- | --- | --- |
| Proposition 2.5.4 (all identities except that K^m is a cap) | K is a cap | [`proposition2_5_4_supp`](MovingSofaOptimality/Monotone/CapContainsNiche.lean#L489), `_hallway`, `_vertices`, `_gaps`, `_sets` hold for every set K |
| Theorem 5.2.2 | b ≤ a + 2π | [`theorem5_2_2`](MovingSofaOptimality/Basic/SurfaceArea.lean#L403) assumes only a < b |
| Proposition 6.2.1 | K is a cap; t ∈ [0, π/2] | [`proposition6_2_1`](MovingSofaOptimality/Injectivity/ArmLengths.lean#L123) holds for every K and t |
| Proposition 6.2.2 | K is a cap; t ∈ [0, π/2] | [`proposition6_2_2`](MovingSofaOptimality/Injectivity/ArmLengths.lean#L158) |
| Theorem 6.2.3 | t ∈ [0, π/2) (right derivatives); t ∈ (0, π/2] (left derivatives) | [`theorem6_2_3_right`](MovingSofaOptimality/Injectivity/ArmLengths.lean#L201), [`theorem6_2_3_left`](MovingSofaOptimality/Injectivity/ArmLengths.lean#L225) |
| Lemma 6.2.4 | K is a cap; t ∈ [0, π/2] | [`lemma6_2_4`](MovingSofaOptimality/Injectivity/ArmLengths.lean#L251) holds for every convex body K and every t |
| Lemma 6.4.2 | the polygon caps K_n have rotation angle π/2 | [`lemma6_4_2`](MovingSofaOptimality/Injectivity/LimitIneq.lean#L329) |
| Lemma 6.5.4 | f ≥ 0 and g ≥ 0 (the codomain ℝ≥0) | [`lemma6_5_4`](MovingSofaOptimality/Injectivity/BoundingArms.lean#L388) holds for all continuous f ≤ g |
| Theorem 7.1.2 (2) | a < b < a + π, for the vertices v_K^±(a), v_K(a, b) | [`theorem7_1_2_vertices`](MovingSofaOptimality/Convex/ConvexDomain.lean#L262) |
| Proposition 7.2.4 | q ∈ l(t, h) (it follows from p ∈ l(t, h) and q − p = d v_t) | [`proposition7_2_4_line`](MovingSofaOptimality/Convex/CurveArea.lean#L686) |
| Theorem 7.3.2, last claim | a < b < a + π, for the quadraticity of 𝒥(𝐮_K^{a,b}) | [`theorem7_3_2_quadratic`](MovingSofaOptimality/Convex/ConvexCurve.lean#L1116) |
| Theorem 8.3.2 | a > t − π | [`theorem8_3_2`](MovingSofaOptimality/Optimality/Concavity.lean#L256) assumes a ≤ b ≤ t |

## 6. How the formalization reads the paper

**Representation choices.**

- The plane is `ℝ × ℝ` and the area of a set is its Lebesgue measure, `area X = (volume X).toReal`.
  Unit vectors, dot and cross products, rotations, lines and half-planes are defined in
  [`MovingSofaOptimality/Basic/Plane.lean`](MovingSofaOptimality/Basic/Plane.lean) exactly as in the paper.
- **Moving sofas** (Definition 1.1.2). The paper's continuous curve Φ_t in SE(2) with Φ₀ a translation
  is written as a continuous angle θ(t) with θ(0) = 0 and a continuous translation c(t); every
  continuous curve in SE(2) has this form, by lifting its rotation part. The rotation angle ω is
  −θ(1).
- **The one-dimensional Hausdorff measure** 𝓗¹ is used by the paper only for subsets of lines (edges,
  sides of polygons). It is formalized as the Lebesgue measure along the line, `lineLength t c X`.
- **The surface area measure** σ_K is the Lebesgue–Stieltjes measure on ℝ of
  t ↦ ⟨v_K⁺(t), v_t⟩ + ∫₀ᵗ h_K, which is 2π-periodic. Measures on S¹ are read as periodic measures on ℝ
  or as measures on [0, 2π). See Section 2 for its relation to Schneider's definition. The paper
  derives the atoms of σ_K and dv_K⁺ = v_t σ_K from Schneider's description; here they follow from the
  definition, and Section 7 lists the proofs where this matters.
- **The Lebesgue–Stieltjes measure** df of a function of bounded variation on [a, b] is Mathlib's
  vector measure of the function extended by constants outside [a, b] ([`lsMeasure`](MovingSofaOptimality/Basic/LebesgueStieltjes.lean#L57)). Its mass at the
  left endpoint is 0, as in Definition 5.1.3.
- **The Hausdorff distance** of convex bodies is defined as sup_t \|h_K(t) − h_L(t)\| (Section 2).
- **The polyline of a cap** (Definitions 3.4.3 and 3.4.4). The paper defines 𝐩_K as the set
  ∂(F_ω \ 𝒩_Θ(K)) \ l⃗_K \ r⃗_K, which Theorem 3.4.4 shows to be a polyline, and τ_K(t) as the total
  length of its edges with normal angle t. Edges are not formalized: τ_K(t) is the sum, over the
  lines l(t, c), of the length of 𝐩_K on l(t, c) (`tau`, in [`Polyline.lean`](MovingSofaOptimality/Balanced/Polyline.lean)).
- **The curve area functional** 𝒥 of a curve of bounded variation is the vector integral
  ½ ∫ 𝐱 × d𝐱 against [`lsMeasure`](MovingSofaOptimality/Basic/LebesgueStieltjes.lean#L57) ([`curveArea`](MovingSofaOptimality/Convex/CurveArea.lean#L530)). The functional of the convex arc 𝐮_K^{a,b} is
  ½ ∫_{(a,b)} h_K dσ_K ([`convexCurveArea`](MovingSofaOptimality/Convex/ConvexCurve.lean#L33)). Theorem 7.3.2 shows that it is the curve area functional
  of an injective parametrization of the arc.
- **Gerver's sofa** follows Romik:
  - [`GerverParams`](MovingSofaOptimality/Gerver/Defs.lean#L30) holds the 22 parameters, and `x₁, …, x₅` are his solutions (SOL1)–(SOL5).
  - [`IsSolution`](MovingSofaOptimality/Gerver/Defs.lean#L92) is his system (27)–(44) together with 0 < φ < θ < π/4, and [`InBox`](MovingSofaOptimality/Gerver/Defs.lean#L108) is
    φ ∈ [0.039, 0.04], θ ∈ [0.68, 0.69].
  - [`gerverSofa`](MovingSofaOptimality/Gerver/Defs.lean#L119) is the shape of the rotation path, Romik's Equation (8).
  - Every result about Gerver's sofa is stated for every solution in the box; the box contains exactly
    one solution.
- **Chapter 8** is stated for a parameter φ ∈ [0.039, 0.04] standing for φ^R, with φ^L = π/2 − φ, rather
  than for Gerver's angle itself. This is how Lemma 8.1.7 (1), (3) get their hypothesis on φ; the
  paper's statements hold for Gerver's φ, which lies in that interval.
- **Jordan curves and Green's theorem** (Theorems 7.2.1, 7.2.3, Proposition 7.2.7) are not formalized
  (Section 9). Lemma 7.3.5 (1), that the boundary Γ of the region between a convex arc and its two
  tangent segments is a counterclockwise Jordan curve, is stated as what the paper uses it for, the
  area of that region ([`lemma7_3_5`](MovingSofaOptimality/Convex/ConvexCurve.lean#L1633)); the region enclosed by Γ is taken to be
  T° \ ⋂_{t∈[a,b]} H_K(t), with T the triangle of the tangent segments, so that (3) holds by
  definition. The areas that the paper computes with Green's theorem are computed directly; Section 7
  lists these proofs.
- **Theorem 8.4.1 (2)** is stated as what the paper uses from it:
  - the curves 𝐁, 𝐱|[t₁,t₄] and 𝐃 lie on the boundary of the niche;
  - they have the stated endpoints;
  - the niche has area 𝒥(𝐱|[t₁,t₄]) − 𝒥(𝐁) − 𝒥(𝐃).

  The proof shows more: the niche is exactly the region strictly under these curves.
- **Proofs.** Where a proof departs from the paper's argument, Section 7 says how and why.

**Corrections of the paper's statements.** Each is the minimal change that makes the statement true,
and each is explained in the module docstring of its file.

| Result | Correction | Lean | See |
| --- | --- | --- | --- |
| Definition 2.3.9 | "not parallel to the x-axis" | [`leftSide`](MovingSofaOptimality/Sofa/Defs.lean#L154), [`rightSide`](MovingSofaOptimality/Sofa/Defs.lean#L157) | E1 |
| Proposition 2.2.2 | Q⁻_S(t) = H°₋(t, h_S(t) − 1) ∩ H°₋(t + π/2, h_S(t + π/2) − 1) | [`proposition2_2_2_qMinus`](MovingSofaOptimality/Monotone/SupportingHallway.lean#L177) | E26 |
| Proposition 2.5.4 | a ↔ c, b ↔ d, W ↔ Z exchanged; K, not K^m, on the right | [`proposition2_5_4_hallway`](MovingSofaOptimality/Monotone/CapContainsNiche.lean#L496), [`proposition2_5_4_vertices`](MovingSofaOptimality/Monotone/CapContainsNiche.lean#L524) | E3 |
| Definition 3.2.5 | F_ω instead of P_ω | [`polyNiche`](MovingSofaOptimality/Balanced/PolygonCap.lean#L53) | E6 |
| Proposition 3.3.1 (2) | normal angles in Θ^◇ ∪ {ω + π, 3π/2} | [`proposition3_3_1`](MovingSofaOptimality/Balanced/PolygonCap.lean#L423) | E7 |
| Lemma 4.2.4 | ω ∈ [sec⁻¹(2.2), π/2) | [`lemma4_2_4`](MovingSofaOptimality/Angle/RightAngle.lean#L517) | E9 |
| Proposition 5.1.4 | r integrable instead of bounded | [`proposition5_1_4`](MovingSofaOptimality/Basic/LebesgueStieltjes.lean#L541) | E11 |
| Proposition 6.2.2 | g^∓_K(π/2 − t), f^∓_K(π/2 − t) | [`proposition6_2_2`](MovingSofaOptimality/Injectivity/ArmLengths.lean#L158) | E13 |
| Lemma 6.5.5 | range (0, π/2] | [`lemma6_5_5`](MovingSofaOptimality/Injectivity/BoundingArms.lean#L408) | E17 |
| Lemma 8.1.7 (4) | equality at t = 0, φ^L | [`lemma8_1_7_four`](MovingSofaOptimality/Optimality/Domain.lean#L1310) | E20 |
| Definition 8.3.3 | ℛ_B = 𝓜_B(π + φ^R, 3π/2; 𝐥_B^{3π/2}) | [`mamikonR`](MovingSofaOptimality/Optimality/Concavity.lean#L278) | E26 |
| Lemma 8.3.6 (3) | the tangent-line parametrization evaluated at π/2 | [`lemma8_3_6`](MovingSofaOptimality/Optimality/Concavity.lean#L889) | E22 |
| Theorem 8.4.3 (2) | 𝐁(t₃) instead of 𝐃(t₃) | [`theorem8_4_3_two`](MovingSofaOptimality/Gerver/Properties.lean#L1680) | E24 |
| Proposition 8.4.4 (4) | σ̆_D on (π/2 + t₀, π/2 + t₂] with density ⟨𝐃′(t − π/2), u_{t−π/2}⟩ | [`proposition8_4_4`](MovingSofaOptimality/Gerver/Properties.lean#L1203) | E25 |

Four further readings concern conjuncts that are vague in the paper or follow from the rest:

- Lemma 7.1.4 is stated as the formula for the one-sided derivative Df(K; K'). The paper's closing
  remark, that Df(K; −) is well defined and linear, is not stated separately: the proof shows that
  the derivative exists, and the linearity follows from the formula
  ([`lemma7_1_4`](MovingSofaOptimality/Convex/ConvexDomain.lean#L83));
- the measurability claim of Mamikon's Theorem 7.4.1 is read on [a, b], where 𝐳 is constrained
  ([`theorem7_4_1`](MovingSofaOptimality/Convex/Mamikon.lean#L569));
- Theorem 8.4.1 (2) is read as described above;
- in Theorem 8.4.3 (2), the tails 𝐝_{D_K} and 𝐛_{B_K} are the curves 𝐃 and 𝐁 "as oriented curves":
  this is stated as the equality of the sets together with 𝒥(𝐝_{D_K}) = 𝒥(𝐃) and
  𝒥(𝐛_{B_K}) = 𝒥(𝐁), which is what Theorem 8.4.6 uses from it; orientations of curves are not
  formalized, and 𝒥 of a convex arc is ½∫ h dσ ([`theorem8_4_3_two`](MovingSofaOptimality/Gerver/Properties.lean#L1680)).

## 7. Departures from the paper's proofs

Every proof follows the paper's argument: the same intermediate claims and constructions, and the
results that the paper's proof cites, which the route check verifies (Section 8). The exceptions are
the steps below. Each is necessary for one of three reasons: (1) the paper's step is wrong, or has a
gap that cannot be repaired along its lines; (2) the step needs mathematics that Lean lacks and that
this project cannot reasonably build; (3) the step has no meaning in a representation that the
formalization uses (Section 6). Gaps that can be repaired along the paper's lines are repaired there
and are not listed (for example E4, E5, and E8 for Theorems 3.4.3, 3.5.2 and 3.5.4). The docstring of each
Lean declaration describes its departure ("Departure from the paper"), and so do
[`formalization.yaml`](formalization.yaml) and [`docs/route_differences.tsv`](docs/route_differences.tsv).

| Result | The paper's argument | The formalization's | Why it is necessary | E-item |
| --- | --- | --- | --- | --- |
| Proposition 2.1.2 | σ_K({t}) is the length of e_K(t) by Schneider's Theorem 2.1.1 with X = {t} | the atom of σ_K at t is the jump at t of ⟨v_K⁺(t), v_t⟩ + ∫₀ᵗ h_K | (3) σ_K is defined as the Lebesgue–Stieltjes measure of that function, not through Theorem 2.1.1 | – |
| Theorem 5.2.2 | dv_K⁺ = v_t σ_K for polygons, then a limit along polygons with the same edges at the ends of the interval (as in Schneider's proof of his Theorem 8.3.3), by Theorem 4.1.3 and the Portmanteau theorem | integration by parts in the definition of σ_K | (2) that approximation by polygons is not in Mathlib; (3) σ_K is defined from v_K⁺ and h_K, so that the identity follows from the definition, while the paper's limit serves to relate Schneider's σ_K to v_K⁺ | – |
| Theorem 6.1.2 | Theorem 6.1.1, for Gerver's sofa taken as a balanced maximum sofa by Gerver's Theorem 2 | the three conditions of the injectivity condition, checked from Romik's equations; Gerver's sofa is the monotone sofa of its cap by Theorems 2.5.9 and 2.4.3 | (1) Gerver's Theorem 2 does not make Gerver's sofa a balanced maximum sofa | E12 |
| Lemma 6.3.1 | 𝒩(K) ⊆ K by Theorem 3.5.4, then the height of 𝐱_K(π/4) by (1) ⇒ (3) of Theorem 2.5.8 | 𝒩_Θ(K) ⊆ K by Theorem 3.4.10, and the height of 𝐱_K(π/4) bounded by the part of Q⁻_K(π/4) in F_{π/2}, which lies in 𝒩_Θ(K) ⊆ K | (1) Theorem 3.5.4 is about balanced maximum caps, and K is a maximum polygon cap | E15 |
| Theorem 6.5.6 | Lemmas 6.5.2 and 6.5.5 | also f_K(π/2) > 1 and g_K(0) > 1, by the continuity of f_K and g_K (Proposition 6.4.6) | (1) Lemma 6.5.2 gives its bounds only on [0, π/2) and (0, π/2] | E17 |
| Theorem 7.3.2 | \|K′\| for the cut body K′ by Green's theorem (Theorem 7.2.3, Proposition 7.2.4) and by Theorem 7.1.3; σ_K((a, b)) = 0 for an arc that is a point, by Schneider's Theorem 2.1.1 | the curve area functional of a parametrization of the arc by arc length, by a change of variables; for an arc that is a point p, v_K⁺ = p on [a, b), hence σ_K((a, b)) = 0 | (2) Mathlib has neither the Jordan curve theorem nor Green's theorem; (3) σ_K is not defined through Theorem 2.1.1 | – |
| Lemma 7.3.5 | (1): Γ is a counterclockwise Jordan curve, by Proposition 7.2.7; (3): the region enclosed by Γ is disjoint from ⋂_{t∈[a,b]} H_K(t), as it is simply connected | (1) is replaced by the area \|T\| − \|K′\| of the region, with \|K′\| by Theorem 7.1.3, which is what the paper uses (1) for; the region is T° \ ⋂_{t∈[a,b]} H_K(t), so that (3) holds by definition | (2) as for Theorem 7.3.2 | – |
| Theorem 8.1.1 (1) | \|(1 − c)K₁ + cK₂\| ≥ 2.2 by the Brunn–Minkowski inequality | horizontal slices and Fubini give \|(1 − c)K₁ + cK₂\| ≥ (1 − c)\|K₁\| + c\|K₂\| | (2) Mathlib has no Brunn–Minkowski inequality | – |
| Lemma 8.1.7 (2), (4) | the point p of δK on b_K^R is outside 𝒩(K) by Theorem 2.5.8 (2), hence in B_K by Lemma 8.1.6 | the topmost point of K on b_K^R (on d_K^L) lies in B_K (in D_K): a normal angle of K there beyond φ^R + π/2 (below φ^L) would contradict g_K(φ^R) > 1 (f_K(φ^L) > 1, Theorem 6.2.3); otherwise the sublinearity of h_K bounds h_K(t) − ⟨p, u_t⟩ by 1 on [φ^R, π/2] | (1) Theorem 2.5.8 (2) needs 𝒩(K) ⊆ K, which 𝒦^i does not provide | E20 |
| Lemma 8.2.2 | the region R bounded by 𝐛_B and two segments; \|R\| by Green's theorem (Theorem 7.2.3) and Proposition 7.2.6 | R is the part of the triangle X_B W_K^R W_B outside B, with area by Lemma 7.3.5 and Theorem 7.1.3 | (2) as for Theorem 7.3.2 | – |
| Lemma 8.2.3 | the region G bounded by 𝐱_K\|[φ^R, φ^L] and three segments; \|G\| − \|R\| by Green's theorem | regions between graphs, with areas by Fubini | (2) as for Theorem 7.3.2 | – |
| Theorem 8.2.4 | splits \|𝒩(K)\| into three parts, disjoint by Lemma 8.1.4 and 𝒩(K) ⊆ K | 𝒩(K) ∩ H̆^R ∩ H̆^L = ∅, by comparing heights | (1) 𝒩(K) ⊆ K fails on 𝒦^i | E20 |
| Lemma 8.3.5 | \|K\| = 𝒥(𝐮_K^{0,π}) by Theorem 7.3.2, then split by Lemma 7.3.4, with 𝒥(A_K(π/2), C_K(0)) = σ_K({π/2})/2 by Propositions 2.1.2 and 7.2.4 | ½∫_{[0,π]} h_K dσ_K split at the atom π/2, which gives σ_K({π/2})/2 directly, then Lemma 7.3.4 at φ^R and φ^L | (1) 𝐮_K^{0,π} is outside the range a < b < a + π of Theorem 7.3.2 and Lemma 7.3.4; (3) 𝒥(𝐮_K^{a,b}) is ½∫_{(a,b)} h_K dσ_K by definition (Section 6) | E19 |
| Theorem 8.4.1 | none: the theorem is stated without proof | proved from Romik's equations by interval arithmetic; the niche is the region under the curves of (2) | (1) there is no argument to follow | E23 |
| Theorem 8.4.3 (2), the equalities of 𝒥 | none: they follow from the equality of the curves as oriented curves | both sides computed, from the densities of σ (the computation of Proposition 8.4.4, through Theorem 5.2.2) and from the pieces of 𝐃 and 𝐁 | (3) 𝒥 of a convex arc is ½∫ h dσ, and orientations of curves are not formalized | – |
| Theorem 8.5.1 | the symmetry of Schneider's mixed area V(K₁, K₂) = ½∫ h_{K₁} dσ_{K₂} (Schneider (5.19)) | the symmetry of ½∫ h_{K₁} dσ_{K₂} on 𝒦^i, by integration by parts | (2) Mathlib has neither mixed volumes nor Schneider's formula (5.19) | – |

## 8. What each result depends on

[`scripts/Audit.lean`](scripts/Audit.lean) lists, for every numbered result, the axioms it uses and the results from prior
work its proof reaches. Every result uses exactly [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound). The
results whose proofs use results from prior work are these; no other result uses any.

| Result | Lean | Results from prior work used |
| --- | --- | --- |
| Theorem 1.1.1 | [`theorem1_1_1`](MovingSofaOptimality/Main.lean#L302) | [`area_eq_half_integral_supp`](MovingSofaOptimality/External/AreaFormula.lean#L558), [`GerverParams.romik_exists`](MovingSofaOptimality/External/Romik.lean#L354) |
| Theorem 7.1.3 | [`theorem7_1_3`](MovingSofaOptimality/Convex/ConvexDomain.lean#L380), [`theorem7_1_3_quadratic`](MovingSofaOptimality/Convex/ConvexDomain.lean#L411) | [`area_eq_half_integral_supp`](MovingSofaOptimality/External/AreaFormula.lean#L558) |
| Lemma 7.3.5 | [`lemma7_3_5`](MovingSofaOptimality/Convex/ConvexCurve.lean#L1633) | [`area_eq_half_integral_supp`](MovingSofaOptimality/External/AreaFormula.lean#L558) |
| Theorem 8.1.1 (2) | [`theorem8_1_1_balanced`](MovingSofaOptimality/Main.lean#L43) | [`GerverParams.romik_exists`](MovingSofaOptimality/External/Romik.lean#L354) |
| Definition 8.1.2 (existence, uniqueness) | [`definition8_1_2_exists`](MovingSofaOptimality/Main.lean#L32), [`definition8_1_2_unique`](MovingSofaOptimality/Main.lean#L37) | [`GerverParams.romik_exists`](MovingSofaOptimality/External/Romik.lean#L354), [`GerverParams.romik_unique`](MovingSofaOptimality/External/Romik.lean#L360) |
| Proposition 8.2.1, Lemma 8.2.2, Theorem 8.2.4 | [`proposition8_2_1`](MovingSofaOptimality/Optimality/UpperBound.lean#L368), [`lemma8_2_2`](MovingSofaOptimality/Optimality/UpperBound.lean#L529), [`theorem8_2_4`](MovingSofaOptimality/Optimality/UpperBound.lean#L1089) | [`area_eq_half_integral_supp`](MovingSofaOptimality/External/AreaFormula.lean#L558) |
| Lemmas 8.3.5, 8.3.7, Theorem 8.3.8 | [`lemma8_3_5`](MovingSofaOptimality/Optimality/Concavity.lean#L854), [`lemma8_3_7`](MovingSofaOptimality/Optimality/Concavity.lean#L1113), [`theorem8_3_8`](MovingSofaOptimality/Optimality/Concavity.lean#L1131) | [`area_eq_half_integral_supp`](MovingSofaOptimality/External/AreaFormula.lean#L558) |
| Theorems 8.5.1, 8.5.6, 8.5.7, Corollary 8.5.8 | [`theorem8_5_1`](MovingSofaOptimality/Optimality/Variation.lean#L445), [`theorem8_5_6`](MovingSofaOptimality/Optimality/Variation.lean#L680), [`theorem8_5_7`](MovingSofaOptimality/Main.lean#L136), [`corollary8_5_8`](MovingSofaOptimality/Main.lean#L259) | [`area_eq_half_integral_supp`](MovingSofaOptimality/External/AreaFormula.lean#L558) |

The results about Gerver's sofa (Theorems 6.1.2, 8.1.1 (3), 8.4.1–8.4.6) are stated for any solution
of Romik's system in the box. Their proofs use no result from prior work; the existence of a solution
enters only through Definition 8.1.2.

The audit also records, for every numbered result, the numbered results that its Lean proof uses.
[`scripts/route_check.py`](scripts/route_check.py), run in CI, compares them with the results that
the paper's proof cites, extracted from the TeX source into
[`docs/paper_routes.tsv`](docs/paper_routes.tsv). Every difference is recorded, with its reason, in
[`docs/route_differences.tsv`](docs/route_differences.tsv): a departure of Section 7, a result that
the paper uses without citing it, or a citation that the paper makes in passing.

## 9. Not formalized

- **Theorems 7.2.1 and 7.2.3, Proposition 7.2.7, and Definitions 7.2.1–7.2.3, 7.2.7 and 7.2.9:** the
  Jordan curve theorem, the area enclosed by a Jordan curve, and the orientation and concatenation of
  Jordan arcs. The formalization replaces every use by a direct area computation (Section 6).
- **Theorem 2.1.1** (Schneider's Theorem 4.2.3, cited) is not stated in its 𝓗¹ form. The surface area
  measure is defined directly, and the properties the paper uses are proved (Section 2).
- **Theorem 1.3.1** quotes Gerver's Theorem 1 for orientation; the paper reproves its content in
  Chapter 3 (Theorems 3.5.4–3.5.6), and those are formalized.
- **Remarks** (15 in the paper), figures, the overview's informal descriptions and Remark 8.4.1's
  numerical comments are not formalized. The overview's results that restate later ones
  (Propositions 1.2.1, 1.2.2, Theorems 1.5.1, 1.5.2, 1.7.1) are formalized through the later
  statements or directly.
