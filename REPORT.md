# Audit of the paper and the formalization

Paper: Jineon Baek, *Optimality of Gerver's Sofa*, arXiv:2411.19826v1 (the only version, 29 November
2024). The audit was made against the arXiv LaTeX source of that version. Result, definition and
equation numbers are the paper's (chapter.section.number). A TeX location such as `05/07:67` means
line 67 of `05._Monotone_Sofas_and_Caps/07._Supporting_Hallway.tex` in the `out/` directory of the
arXiv source; the chapter directories `01, 05, 10, 15, 17, 20, 22, 25` hold the paper's Chapters 1–8.

Status of the formalization:

- Every numbered result the paper proves is proved in Lean, with the deviations listed in Sections 3
  and 6, and so is the main theorem (Theorem 1.1.1): Gerver's sofa is a moving sofa, and every moving
  sofa has area at most that of Gerver's sofa.
- The results the paper takes from the literature and uses in its proofs are proved too:
  - Schneider's area formula for planar convex bodies, in [`MovingSofa/External/`](MovingSofa/External);
  - the existence and uniqueness of the solution of Romik's system that defines Gerver's sofa;
  - the remaining cited facts (weak convergence of surface area measures, Blaschke selection,
    continuity of area, Lebesgue–Stieltjes calculus), in the files that use them or in Mathlib
    (Section 2).
- Theorem 8.4.1 (the structure of Gerver's sofa), which the paper states without proof, is proved
  from Romik's equations by interval arithmetic ([`MovingSofa/Gerver/`](MovingSofa/Gerver)).
- `lake build` succeeds. The only `sorry`s are the four statements of [`Challenge.lean`](Challenge.lean), which are
  `sorry` by design and proved in [`Solution.lean`](Solution.lean). There is no `axiom`, `admit`, `native_decide` or
  `implemented_by`.
- [`scripts/Audit.lean`](scripts/Audit.lean) checks that every declaration of the library, every paper result and the
  Challenge theorems depend only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound). It also lists the
  results from prior work that each paper result uses (Section 7).
- [`Challenge.lean`](Challenge.lean) restates Theorem 1.1.1, together with the existence and uniqueness of Gerver's
  parameters and the area of Gerver's sofa (between 2.2192 and 2.2199), using Mathlib's vocabulary
  only. [`Solution.lean`](Solution.lean) proves these statements from the
  library, and `lake comparator` accepts the solution.
- Statements of the paper that are false as printed are formalized in their intended form; Section 6
  lists every such correction. No result had to be weakened.

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

### Proved in `MovingSofa/External/`

| Result | Where the paper uses it | Source | Lean |
| --- | --- | --- | --- |
| \|K\| = ½ ∫ h_K dσ_K for a planar convex body K | Theorem 7.1.3, and through it Chapter 8 (Lemma 8.3.5, Theorems 8.2.4, 8.3.8, 8.5.7) | Schneider, *Convex Bodies*, Remark 5.1.2 and Eq. (5.19) | [`area_eq_half_integral_supp`](MovingSofa/External/AreaFormula.lean#L592) ([`MovingSofa/External/AreaFormula.lean`](MovingSofa/External/AreaFormula.lean)) |
| Romik's system (27)–(44) has a solution with 0 < φ < θ < π/4 (his Table 1: φ = 0.0391773…, θ = 0.6813015…) | Definition 8.1.2 (Gerver's sofa G) | Romik 2018, Section 4 | [`GerverParams.romik_exists`](MovingSofa/External/Romik.lean#L387) ([`MovingSofa/External/Romik.lean`](MovingSofa/External/Romik.lean)), [`definition8_1_2_exists`](MovingSofa/Main.lean#L24) |
| This solution is unique | Definition 8.1.2 ("the" solution) | Romik 2018, asserted without proof | [`GerverParams.romik_unique`](MovingSofa/External/Romik.lean#L393), [`definition8_1_2_unique`](MovingSofa/Main.lean#L28) |

- [`MovingSofa/External/AreaFormula.lean`](MovingSofa/External/AreaFormula.lean) proves the area formula by a change of variables from an
  interior point along the arc-length parametrization of ∂K. The parametrization is built in
  [`MovingSofa/External/AreaFormula/Param.lean`](MovingSofa/External/AreaFormula/Param.lean) from the generalized inverse of the distribution
  function of σ_K.
- [`MovingSofa/External/Romik.lean`](MovingSofa/External/Romik.lean) eliminates the parameters that enter linearly, reducing Romik's
  system to two equations H(φ, θ) = 0. [`MovingSofa/External/Romik/Num.lean`](MovingSofa/External/Romik/Num.lean) encloses H and its
  derivatives on the box by interval arithmetic; it is generated by [`scripts/romik/mk_num.py`](scripts/romik/mk_num.py), and every
  step is a `norm_num` inequality. [`MovingSofa/External/Romik/Fix.lean`](MovingSofa/External/Romik/Fix.lean) shows that z ↦ z − M·H(z) is a
  ½-contraction of the box. This gives a unique
  zero, within 10⁻¹⁰ of (0.0391773648, 0.6813015094), and the enclosures of all parameters
  ([`GerverParams.romik_bounds`](MovingSofa/External/Romik.lean#L577)) that the numerical verifications use.

### Cited results proved where they are used

| Cited result | Where the paper uses it | In the formalization |
| --- | --- | --- |
| Schneider Theorem 4.2.3: σ_K(X) is the length of ⋃_{t∈X} e_K(t) (the paper's Theorem 2.1.1) | Proposition 2.1.2 and the side lengths throughout | σ_K is defined directly, as the Lebesgue–Stieltjes measure of t ↦ ⟨v_K⁺(t), v_t⟩ + ∫₀ᵗ h_K ([`sigma`](MovingSofa/Basic/SurfaceArea.lean#L281), [`MovingSofa/Basic/SurfaceArea.lean`](MovingSofa/Basic/SurfaceArea.lean)). Proposition 2.1.2 (σ_K({t}) is the length of e_K(t)) and Theorem 5.2.2 (dv_K⁺ = v_t dσ_K) are proved from this definition. [`MovingSofa/External/AreaFormula/Param.lean`](MovingSofa/External/AreaFormula/Param.lean) shows that the normal angle along the arc-length parametrization of ∂K pushes Lebesgue measure forward to σ_K, which is Theorem 2.1.1 in arc-length form. |
| Schneider Lemma 1.8.14: d_H(K, L) = sup_t \|h_K(t) − h_L(t)\| | Chapter 3 (limits of caps) | Hausdorff distance is defined in this support-function form ([`hausdorffDist`](MovingSofa/Basic/ConvexBody.lean#L74)). The comparison with Mathlib's Hausdorff distance needed for Blaschke's theorem is proved in [`mpc_blaschke`](MovingSofa/Balanced/BalancedMaximumSofa.lean#L223). |
| Blaschke selection theorem | Theorem 3.5.2 | Mathlib (compactness of nonempty compact sets in the Hausdorff metric), via [`mpc_blaschke`](MovingSofa/Balanced/BalancedMaximumSofa.lean#L223) |
| Schneider Theorem 1.8.20: area is continuous in d_H | Theorems 3.4.3, 3.5.2 | proved in the one-sided forms the proofs need ([`MovingSofa/Balanced/MaximumPolygonCap.lean`](MovingSofa/Balanced/MaximumPolygonCap.lean), [`MovingSofa/Balanced/BalancedMaximumSofa.lean`](MovingSofa/Balanced/BalancedMaximumSofa.lean)) |
| Schneider Theorem 4.2.1: σ is weakly continuous in K (the paper's Theorem 4.1.3) | Theorems 4.1.4, 6.4.3 | [`theorem4_1_3`](MovingSofa/Angle/HorizontalSide.lean#L1121), proved by integration by parts against the distribution function of σ and dominated convergence |
| Schneider Eq. (4.14): σ of a reflected body | Proposition 2.5.4 | proved directly ([`proposition2_5_4_sigma`](MovingSofa/Monotone/CapContainsNiche.lean#L718)) |
| Schneider Theorem 1.7.5(a) and Remark 1.7.7: h_{K+L} = h_K + h_L | Theorem 7.1.2 | proved ([`cvx_supp_convexBodyComb`](MovingSofa/Convex/ConvexDomain.lean#L207)) |
| Revuz–Yor Theorem 4.3 (Lebesgue–Stieltjes measures) and Proposition 4.5 (integration by parts) | Chapter 5, Lemma 8.5.4 | Mathlib's measures of functions of bounded variation (`BoundedVariationOn.vectorMeasure`) and their integration by parts (`setIntegral_Icc_leftLim_vectorMeasure_eq_sub`) |
| Jordan curve theorem; Green's theorem (Apostol, Theorem 10.43) | Theorems 7.2.1, 7.2.3, Proposition 7.2.7, and through them Lemmas 7.3.5, 8.2.2, 8.2.3 and Theorem 8.4.1(2) | not used: each area these results are used for is computed directly (Section 6) |
| Brunn–Minkowski inequality | Theorem 8.1.1 (1) | not used: the area condition of 𝒦^i is shown to be preserved by a slicing argument ([`opt_comb_area`](MovingSofa/Optimality/Domain.lean#L476)) |
| Gerver 1992, Theorem 2 | Theorem 6.1.2 | not used: Theorem 6.1.2 is proved from Romik's equations (E12) |

### Standard facts used without citation

| Fact | Where | In the formalization |
| --- | --- | --- |
| Intermediate value theorem | Chapters 1, 7, 8 | `intermediate_value_Icc` |
| Fundamental theorem of calculus | throughout | `intervalIntegral.integral_eq_sub_of_hasDerivAt` and variants with countably many exceptions |
| Cavalieri's principle, Fubini–Tonelli | Theorems 1.5.1, 3.1.2, 8.1.1, Chapter 8 | `MeasureTheory.Measure.prod_apply`, `MeasureTheory.lintegral_prod`, `volume_regionBetween_eq_integral` |
| Change of variables in the plane | Theorem 7.1.3, the niche of Gerver's sofa | `lintegral_abs_det_fderiv_eq_addHaar_image` |
| Radon–Nikodym theorem | Corollary 6.4.4 | `MeasureTheory.Measure.withDensity_rnDeriv_eq` |
| Lebesgue differentiation theorem | Proposition 5.1.4, Theorem 6.5.1 | Mathlib (`Mathlib/MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean`) |
| Dominated convergence | Theorem 4.1.3 | `intervalIntegral.tendsto_integral_filter_of_dominated_convergence` |
| Portmanteau theorem | Lemma 6.4.2, Theorem 6.4.3 | not used: the limits are taken through support-function difference quotients |
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
vertical line l_{π/2}). Typo; the Lean definitions [`leftSide`](MovingSofa/Sofa/Defs.lean#L153) and [`rightSide`](MovingSofa/Sofa/Defs.lean#L156) follow the intended
reading.

**E2. Theorem 2.4.2 and Definition 2.4.5** (`05/12:82`, `05/12:63`). The theorem's formula takes the
union over t ∈ [0, ω], the definition of the niche over t ∈ (0, ω). The two agree because
F_ω ∩ Q⁻_K(0) = F_ω ∩ Q⁻_K(ω) = ∅ (Q⁻_K(0) lies below y = 0, Q⁻_K(ω) below l(ω, 0)); the paper does not
say so. Trivial gap; the theorem holds.

**E3. Proposition 2.5.4** (`pro:mirror-reflection`, `05/15:99–101`). The first bullet claims
?_{K^m}(t) = M_ω(?_K(ω − t)) for ? = L, 𝐱, 𝐲, a, b, c, d, W, Z, but the reflection M_ω exchanges a ↔ c,
b ↔ d and W ↔ Z; only L, 𝐱, 𝐲 map to themselves. The second bullet should have K, not K^m, on the right:
A^±_{K^m}(t) = M_ω(C^∓_K(ω − t)). The third bullet is consistent with the exchanges. Slips in the
statement; the Lean statements ([`proposition2_5_4_hallway`](MovingSofa/Monotone/CapContainsNiche.lean#L624), [`proposition2_5_4_vertices`](MovingSofa/Monotone/CapContainsNiche.lean#L650)) are the
corrected ones.

**E4. Lemma 2.5.6 and Theorem 2.5.8 (4 ⇒ 3)** (`lem:niche-in-cap`, `05/15:151–168`; `05/15:212`). The
proofs use, without proof, two facts about every cap K:

- (a) C⁺_K(ω) lies on l(ω, 0) and A⁻_K(0) on l(π/2, 0);
- (b) the origin lies in K when ω < π/2 (cases 2 and 4 of Lemma 2.5.6 use O as a vertex of the
  wedge).

Both hold. For (b): A⁻_K(0) = (a, 0) with a ≥ 0 and C⁺_K(ω) = λv_ω with λ ≥ 0, so every half-plane
H₋(s, k) defining K with s in J_ω has k ≥ 0. For ω = π/2, O need not lie in K (K = [5, 6] × [0, 1] is a
cap), but the paper's proof of that case does not use O. Minor gap; both results hold. The Lean proof
of Lemma 2.5.6 checks directly that every point of the wedge satisfies the half-plane conditions of
the cap.

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

Error. With F_ω every result of Chapter 3 holds; the Lean definition [`polyNiche`](MovingSofa/Balanced/PolygonCap.lean#L53) uses the fan F_ω.

**E7. Proposition 3.3.1 (2)** (`pro:cap-trans-space`, `10/12:20`). "K′ is a convex polygon with normal
angles in the set Θ^◇". Since Θ^◇ ⊂ (0, π], no bounded polygon with nonempty interior has all its
normal angles there. The bottom normals ω + π and 3π/2 are missing; the proof of Proposition 3.3.2
uses Θ^◇ ∪ {ω + π, 3π/2}. Slip in the statement; the Lean statement ([`proposition3_3_1`](MovingSofa/Balanced/PolygonCap.lean#L458), through
[`AngleSet.capAngles`](MovingSofa/Balanced/PolygonCap.lean#L38)) includes the bottom normals.

**E8. Theorems 3.5.2, 3.5.4 and 3.5.5** (`10/20:47`, `10/20:69`, `10/20:80–90`).

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

Slip in the statement and a trivial gap. [`lemma4_2_4`](MovingSofa/Angle/RightAngle.lean#L517) is stated on [sec⁻¹(2.2), π/2).

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

Error; Theorem 6.5.1 survives. [`proposition5_1_4`](MovingSofa/Basic/LebesgueStieltjes.lean#L391) is the correct version (r integrable), and
[`proposition5_1_4_deriv`](MovingSofa/Basic/LebesgueStieltjes.lean#L431) is the derivative clause with bounded r. [`proposition5_1_4_as_stated_false`](MovingSofa/Basic/LebesgueStieltjes.lean#L458)
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

Gap: the proof is invalid as written; the statement is true. [`theorem6_1_2`](MovingSofa/Gerver/Properties.lean#L140) is proved from Romik's
formulas ([`gv_injectivity`](MovingSofa/Gerver/Structure.lean#L143)): σ_K is absolutely continuous on [0, π/2) and on (π/2, π], with densities
⟨𝐀′(t), v_t⟩ and ⟨−𝐂′(t − π/2), u_{t−π/2}⟩; the inner corner is the path 𝐱, which is C¹; and
𝐱′·u_t < 0 < 𝐱′·v_t on (0, π/2).

**E13. Proposition 6.2.2** (`pro:cap-tangent-arm-mirror`, `20/05:30`). "f^±_{K^m}(t) = g^∓_K(t)" should
read f^±_{K^m}(t) = g^∓_K(π/2 − t), and likewise for g, because the reflection also reverses the angle.
Lemma 6.5.2 uses this corrected form. Slip in the statement; [`proposition6_2_2`](MovingSofa/Injectivity/ArmLengths.lean#L150) is the corrected one.

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
- (c) Lemmas 6.5.3 and 6.5.5 state their conclusions on [0, 1] and (0, 1]; their proofs, and
  Theorem 6.5.6, need [0, π/2] and (0, π/2].

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
at π/2. Slip in the statement (false as printed); [`lemma8_3_6`](MovingSofa/Optimality/Concavity.lean#L1047) evaluates at π/2.

**E23. Theorem 8.4.1** (`thm:gerver-monotone`, `25/12:43–74`). The theorem is stated without proof.
Remark 8.4.1 notes that its properties are "easy to verify numerically and implicitly assumed" in the
literature, but that "a rigorous symbolic verification … would still be worthy". It asserts that:

- G is a monotone sofa with cap K;
- the curves 𝐀, 𝐂 and 𝐱 are the vertices and the inner corner of K;
- the niche is the region enclosed by 𝐁, 𝐱|[t₁,t₄], 𝐃 and the x-axis;
- 𝐁 and 𝐃 lie on the walls, with 𝐁′ a negative multiple of v_t and 𝐃′ a positive multiple of u_t.

Gap (an unproved theorem; true). The formalization proves it from Romik's equations:

- [`MovingSofa/Gerver/Frame.lean`](MovingSofa/Gerver/Frame.lean) writes each phase in a rotating frame, x = R_t w + κ, with x′ = αu_t + βv_t.
- [`MovingSofa/Gerver/StructureCap.lean`](MovingSofa/Gerver/StructureCap.lean) constructs the cap K_G = {y ≥ 0} ∩ ⋂_{σ∈[0,π]} H₋(σ, H(σ)) from the path.
  It shows that G = K_G \ 𝒩(K_G) is a monotone sofa (Theorems 2.5.8–2.5.9) and identifies the
  vertices.
- The niche (part (2)) is the delicate part, since the margins are about 10⁻³ near t = π/4 and two
  points are tangencies. [`MovingSofa/Gerver/Envelope.lean`](MovingSofa/Gerver/Envelope.lean) shows that the niche of a rotation path is exactly the
  region strictly under the curve 𝐃 ∪ 𝐱 ∪ 𝐁. The key observation is that a point p avoids the quadrant
  Q⁻(s) as soon as (p − 𝐱(s))·u_σ ≥ 0 for some σ ∈ [s, s + π/2]. Monotonicity in the remaining variable
  then reduces the two-parameter family of inequalities to one-variable ones, which
  [`MovingSofa/Gerver/NicheBounds.lean`](MovingSofa/Gerver/NicheBounds.lean) verifies.
- [`MovingSofa/Gerver/EnvelopeArea.lean`](MovingSofa/Gerver/EnvelopeArea.lean) and [`MovingSofa/Gerver/Niche.lean`](MovingSofa/Gerver/Niche.lean) compute the niche's area as
  𝒥(𝐱|[t₁,t₄]) − 𝒥(𝐁) − 𝒥(𝐃).

**E24. Theorem 8.4.3 (2)** (`thm:gerver-left-right`, `25/12:151`): "𝐱^R_K = X_{B_K} = 𝐃(t₃)" should be
𝐁(t₃); 𝐃 is defined on [t₀, t₂] only. Slip in the statement; [`theorem8_4_3_two`](MovingSofa/Gerver/Properties.lean#L1505) uses 𝐁(t₃).

**E25. Proposition 8.4.4 (4)** (`pro:measure-translation`, `25/12:202`): "⟨𝐃′(t), u_t⟩ dt = σ̆_D as
measures on t ∈ (t₀, t₂]". Since 𝐃(t) = v_{D_K}(3π/2 + t), σ̆_D lives on (π/2 + t₀, π/2 + t₂], with density
⟨𝐃′(τ − π/2), u_{τ−π/2}⟩, the same shifted form as item (3). Theorems 8.4.5 and 8.5.6 use this form. As
printed, the left side is σ_{D_K} on (π, π + θ], which is 0. Slip in the statement;
[`proposition8_4_4`](MovingSofa/Gerver/Properties.lean#L1689) is the shifted form.

**E26. Typos.**

- Theorem 2.1.3 (`05/05:156`, `05/05:175–177`): v_K⁺(t), v_K⁻(u) for v_K⁺(s), v_K⁻(s); v^±_K(u) for
  v^±_K(t₀); g_K(t₀) for H_K(t₀).
- Proposition 2.2.2 (`05/07:67`): the second half-plane of Q⁻_S(t) lacks its "− 1"; the Lean statement
  has it.
- Theorem 2.3.6, proof (`05/10:163`): l_θ \ X for l_θ ∩ X.
- Theorem 2.4.1, proof (`05/12:40`): the directions v₀, u_ω should be −v₀, −u_ω.
- Lemma 2.5.6, proof (`05/15:159`): in case 1, x_K(t) ∈ K forces x_K(t) = O and T_K(t) = ∅; this is not
  a contradiction, but the conclusion holds.
- Theorem 2.5.9, proof (`05/15:225`): "𝒩(K) contains K" for "K contains 𝒩(K)".
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
| Proposition 2.5.4 (all identities except that K^m is a cap) | K is a cap | [`proposition2_5_4_supp`](MovingSofa/Monotone/CapContainsNiche.lean#L620), `_hallway`, `_vertices`, `_gaps`, `_sets` hold for every set K |
| Theorem 5.2.2 | b ≤ a + 2π | [`theorem5_2_2`](MovingSofa/Basic/SurfaceArea.lean#L525) assumes only a < b |
| Proposition 6.2.1 | K is a cap; t ∈ [0, π/2] | [`proposition6_2_1`](MovingSofa/Injectivity/ArmLengths.lean#L118) holds for every K and t |
| Proposition 6.2.2 | K is a cap; t ∈ [0, π/2] | [`proposition6_2_2`](MovingSofa/Injectivity/ArmLengths.lean#L150) |
| Theorem 6.2.3 | t ∈ [0, π/2) (right derivatives); t ∈ (0, π/2] (left derivatives) | [`theorem6_2_3_right`](MovingSofa/Injectivity/ArmLengths.lean#L201), [`theorem6_2_3_left`](MovingSofa/Injectivity/ArmLengths.lean#L226) |
| Lemma 6.2.4 | t ∈ [0, π/2] | [`lemma6_2_4`](MovingSofa/Injectivity/ArmLengths.lean#L251) |
| Lemma 6.4.2 | the polygon caps K_n have rotation angle π/2 | [`lemma6_4_2`](MovingSofa/Injectivity/LimitIneq.lean#L312) |
| Lemma 6.5.4 | f ≥ 0 (only g ≥ 0 is needed) | [`lemma6_5_4`](MovingSofa/Injectivity/BoundingArms.lean#L344) |
| Theorem 7.1.2 (2) | a < b < a + π, for the vertices v_K^±(a), v_K(a, b) | [`theorem7_1_2_vertices`](MovingSofa/Convex/ConvexDomain.lean#L258) |
| Proposition 7.2.4 | q ∈ l(t, h) (it follows from p ∈ l(t, h) and q − p = d v_t) | [`proposition7_2_4_line`](MovingSofa/Convex/CurveArea.lean#L483) |
| Theorem 7.3.2, last claim | a < b < a + π, for the quadraticity of 𝒥(𝐮_K^{a,b}) | [`theorem7_3_2_quadratic`](MovingSofa/Convex/ConvexCurve.lean#L1251) |
| Theorem 8.3.2 | a > t − π | [`theorem8_3_2`](MovingSofa/Optimality/Concavity.lean#L309) assumes a ≤ b ≤ t |
| Theorem 8.5.2 | b < a + π | [`theorem8_5_2`](MovingSofa/Optimality/Variation.lean#L710) assumes a < b |

## 6. How the formalization reads the paper

**Representation choices.**

- The plane is `ℝ × ℝ` and the area of a set is its Lebesgue measure, `area X = (volume X).toReal`.
  Unit vectors, dot and cross products, rotations, lines and half-planes are defined in
  [`MovingSofa/Basic/Plane.lean`](MovingSofa/Basic/Plane.lean) exactly as in the paper.
- **Moving sofas** (Definition 1.1.2). The paper's continuous curve Φ_t in SE(2) with Φ₀ a translation
  is written as a continuous angle θ(t) with θ(0) = 0 and a continuous translation c(t); every
  continuous curve in SE(2) has this form, by lifting its rotation part. The rotation angle ω is
  −θ(1).
- **The one-dimensional Hausdorff measure** 𝓗¹ is used by the paper only for subsets of lines (edges,
  sides of polygons). It is formalized as the Lebesgue measure along the line, `lineLength t c X`.
- **The surface area measure** σ_K is the Lebesgue–Stieltjes measure on ℝ of
  t ↦ ⟨v_K⁺(t), v_t⟩ + ∫₀ᵗ h_K, which is 2π-periodic. Measures on S¹ are read as periodic measures on ℝ
  or as measures on [0, 2π). See Section 2 for its relation to Schneider's definition.
- **The Lebesgue–Stieltjes measure** df of a function of bounded variation on [a, b] is Mathlib's
  vector measure of the function extended by constants outside [a, b] ([`lsMeasure`](MovingSofa/Basic/LebesgueStieltjes.lean#L54)). Its mass at the
  left endpoint is 0, as in Definition 5.1.3.
- **The Hausdorff distance** of convex bodies is defined as sup_t \|h_K(t) − h_L(t)\| (Section 2).
- **The curve area functional** 𝒥 of a curve of bounded variation is the vector integral
  ½ ∫ 𝐱 × d𝐱 against [`lsMeasure`](MovingSofa/Basic/LebesgueStieltjes.lean#L54) ([`curveArea`](MovingSofa/Convex/CurveArea.lean#L350)). The functional of the convex arc 𝐮_K^{a,b} is
  ½ ∫_{(a,b)} h_K dσ_K ([`convexCurveArea`](MovingSofa/Convex/ConvexCurve.lean#L32)). Theorem 7.3.2 shows that it is the curve area functional
  of an injective parametrization of the arc.
- **Gerver's sofa** follows Romik:
  - `GerverParams` holds the 22 parameters, and `x₁, …, x₅` are his solutions (SOL1)–(SOL5).
  - [`IsSolution`](MovingSofa/Gerver/Defs.lean#L89) is his system (27)–(44) together with 0 < φ < θ < π/4, and [`InBox`](MovingSofa/Gerver/Defs.lean#L105) is
    φ ∈ [0.039, 0.04], θ ∈ [0.68, 0.69].
  - `gerverSofa` is the shape of the rotation path, Romik's Equation (8).
  - Every result about Gerver's sofa is stated for every solution in the box; the box contains exactly
    one solution.
- **Chapter 8** is stated for a parameter φ ∈ [0.039, 0.04] standing for φ^R, with φ^L = π/2 − φ, rather
  than for Gerver's angle itself. This is how Lemma 8.1.7 (1), (3) get their hypothesis on φ; the
  paper's statements hold for Gerver's φ, which lies in that interval.
- **Jordan curves and Green's theorem** (Theorems 7.2.1, 7.2.3, Proposition 7.2.7) are not formalized.
  Each area the paper computes with them is computed directly, by Fubini or by a change of variables:
  - Lemma 7.3.5 (1) is replaced by the area of the region between the convex arc and its tangent
    triangle ([`lemma7_3_5`](MovingSofa/Convex/ConvexCurve.lean#L1830));
  - in Lemmas 8.2.2 and 8.2.3, the regions bounded by curves are written as regions between graphs,
    whose areas Fubini gives;
  - the niche of Gerver's sofa is shown to be a region under a curve whose first coordinate is
    monotone ([`env_niche_eq`](MovingSofa/Gerver/Envelope.lean#L842), [`env_volume_region_of_monotoneOn`](MovingSofa/Gerver/EnvelopeArea.lean#L420)).
- **Theorem 8.4.1 (2)** is stated as what the paper uses from it:
  - the curves 𝐁, 𝐱|[t₁,t₄] and 𝐃 lie on the boundary of the niche;
  - they have the stated endpoints;
  - the niche has area 𝒥(𝐱|[t₁,t₄]) − 𝒥(𝐁) − 𝒥(𝐃).

  The proof shows more: the niche is exactly the region strictly under these curves.
- **Theorem 8.1.1 (1)** (𝒦^i is convex) is proved without the Brunn–Minkowski inequality. Every cap
  with ω = π/2 spans the heights 0 ≤ y ≤ 1, so each horizontal slice of (1 − c)K₁ + cK₂ contains the
  combination of the slices of K₁ and K₂, and Fubini gives
  \|(1 − c)K₁ + cK₂\| ≥ (1 − c)\|K₁\| + c\|K₂\| ≥ 2.2 ([`opt_comb_area`](MovingSofa/Optimality/Domain.lean#L476)).
- **Proofs that follow a different route** from the paper, with the same statements:
  - Lemma 2.5.6 and Theorem 2.5.8 (direct half-plane checks);
  - Theorem 3.4.3 (compactness of finitely many support values instead of Blaschke selection);
  - Theorems 3.5.4–3.5.5 (pointwise convergence of niches);
  - the mirror halves of Theorems 4.1.2, 4.1.4 and 4.2.5 (proved directly);
  - Lemma 6.4.2 and Theorem 6.4.3 (difference quotients of support functions instead of the
    Portmanteau theorem);
  - Theorem 6.1.2 and Theorem 8.4.1 (from Romik's equations).

**Corrections of the paper's statements.** Each is the minimal change that makes the statement true,
and each is explained in the module docstring of its file.

| Result | Correction | Lean | See |
| --- | --- | --- | --- |
| Definition 2.3.9 | "not parallel to the x-axis" | [`leftSide`](MovingSofa/Sofa/Defs.lean#L153), [`rightSide`](MovingSofa/Sofa/Defs.lean#L156) | E1 |
| Proposition 2.2.2 | Q⁻_S(t) = H°₋(t, h_S(t) − 1) ∩ H°₋(t + π/2, h_S(t + π/2) − 1) | [`proposition2_2_2_qMinus`](MovingSofa/Monotone/SupportingHallway.lean#L185) | E26 |
| Proposition 2.5.4 | a ↔ c, b ↔ d, W ↔ Z exchanged; K, not K^m, on the right | [`proposition2_5_4_hallway`](MovingSofa/Monotone/CapContainsNiche.lean#L624), [`proposition2_5_4_vertices`](MovingSofa/Monotone/CapContainsNiche.lean#L650) | E3 |
| Definition 3.2.5 | F_ω instead of P_ω | [`polyNiche`](MovingSofa/Balanced/PolygonCap.lean#L53) | E6 |
| Proposition 3.3.1 (2) | normal angles in Θ^◇ ∪ {ω + π, 3π/2} | [`proposition3_3_1`](MovingSofa/Balanced/PolygonCap.lean#L458) | E7 |
| Lemma 4.2.4 | ω ∈ [sec⁻¹(2.2), π/2) | [`lemma4_2_4`](MovingSofa/Angle/RightAngle.lean#L517) | E9 |
| Proposition 5.1.4 | r integrable instead of bounded | [`proposition5_1_4`](MovingSofa/Basic/LebesgueStieltjes.lean#L391) | E11 |
| Proposition 6.2.2 | g^∓_K(π/2 − t), f^∓_K(π/2 − t) | [`proposition6_2_2`](MovingSofa/Injectivity/ArmLengths.lean#L150) | E13 |
| Lemmas 6.5.3, 6.5.5 | ranges [0, π/2], (0, π/2] | [`lemma6_5_3`](MovingSofa/Injectivity/BoundingArms.lean#L277), [`lemma6_5_5`](MovingSofa/Injectivity/BoundingArms.lean#L364) | E17 |
| Lemma 8.1.7 (4) | equality at t = 0, φ^L | [`lemma8_1_7_four`](MovingSofa/Optimality/Domain.lean#L1367) | E20 |
| Definition 8.3.3 | ℛ_B = 𝓜_B(π + φ^R, 3π/2; 𝐥_B^{3π/2}) | [`mamikonR`](MovingSofa/Optimality/Concavity.lean#L330) | E26 |
| Lemma 8.3.6 (3) | the tangent-line parametrization evaluated at π/2 | [`lemma8_3_6`](MovingSofa/Optimality/Concavity.lean#L1047) | E22 |
| Theorem 8.4.3 (2) | 𝐁(t₃) instead of 𝐃(t₃) | [`theorem8_4_3_two`](MovingSofa/Gerver/Properties.lean#L1505) | E24 |
| Proposition 8.4.4 (4) | σ̆_D on (π/2 + t₀, π/2 + t₂] with density ⟨𝐃′(t − π/2), u_{t−π/2}⟩ | [`proposition8_4_4`](MovingSofa/Gerver/Properties.lean#L1689) | E25 |

Two further readings concern conjuncts that are vague in the paper:

- the measurability claim of Mamikon's Theorem 7.4.1 is read on [a, b], where 𝐳 is constrained
  ([`theorem7_4_1`](MovingSofa/Convex/Mamikon.lean#L552));
- Theorem 8.4.1 (2) is read as described above.

## 7. What each result depends on

[`scripts/Audit.lean`](scripts/Audit.lean) lists, for every numbered result, the axioms it uses and the results from prior
work its proof reaches. Every result uses exactly [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound). The
results whose proofs use results from prior work are these; no other result uses any.

| Result | Lean | Results from prior work used |
| --- | --- | --- |
| Theorem 1.1.1 | [`theorem1_1_1`](MovingSofa/Main.lean#L318) | [`area_eq_half_integral_supp`](MovingSofa/External/AreaFormula.lean#L592), [`GerverParams.romik_exists`](MovingSofa/External/Romik.lean#L387) |
| Theorem 7.1.3 | [`theorem7_1_3`](MovingSofa/Convex/ConvexDomain.lean#L296), [`theorem7_1_3_quadratic`](MovingSofa/Convex/ConvexDomain.lean#L332) | [`area_eq_half_integral_supp`](MovingSofa/External/AreaFormula.lean#L592) |
| Lemma 7.3.5 | [`lemma7_3_5`](MovingSofa/Convex/ConvexCurve.lean#L1830) | [`area_eq_half_integral_supp`](MovingSofa/External/AreaFormula.lean#L592) |
| Theorem 8.1.1 (2) | [`theorem8_1_1_balanced`](MovingSofa/Main.lean#L34) | [`GerverParams.romik_exists`](MovingSofa/External/Romik.lean#L387) |
| Definition 8.1.2 (existence, uniqueness) | [`definition8_1_2_exists`](MovingSofa/Main.lean#L24), [`definition8_1_2_unique`](MovingSofa/Main.lean#L28) | [`GerverParams.romik_exists`](MovingSofa/External/Romik.lean#L387), [`GerverParams.romik_unique`](MovingSofa/External/Romik.lean#L393) |
| Proposition 8.2.1, Lemma 8.2.2, Theorem 8.2.4 | [`proposition8_2_1`](MovingSofa/Optimality/UpperBound.lean#L467), [`lemma8_2_2`](MovingSofa/Optimality/UpperBound.lean#L503), [`theorem8_2_4`](MovingSofa/Optimality/UpperBound.lean#L1187) | [`area_eq_half_integral_supp`](MovingSofa/External/AreaFormula.lean#L592) |
| Lemmas 8.3.5, 8.3.7, Theorem 8.3.8 | [`lemma8_3_5`](MovingSofa/Optimality/Concavity.lean#L1013), [`lemma8_3_7`](MovingSofa/Optimality/Concavity.lean#L1272), [`theorem8_3_8`](MovingSofa/Optimality/Concavity.lean#L1290) | [`area_eq_half_integral_supp`](MovingSofa/External/AreaFormula.lean#L592) |
| Theorems 8.5.1, 8.5.6, 8.5.7, Corollary 8.5.8 | [`theorem8_5_1`](MovingSofa/Optimality/Variation.lean#L677), [`theorem8_5_6`](MovingSofa/Optimality/Variation.lean#L977), [`theorem8_5_7`](MovingSofa/Main.lean#L138), [`corollary8_5_8`](MovingSofa/Main.lean#L253) | [`area_eq_half_integral_supp`](MovingSofa/External/AreaFormula.lean#L592) |

The results about Gerver's sofa (Theorems 6.1.2, 8.1.1 (3), 8.4.1–8.4.6) are stated for any solution
of Romik's system in the box. Their proofs use no result from prior work; the existence of a solution
enters only through Definition 8.1.2.

## 8. Not formalized

- **Theorems 7.2.1 and 7.2.3, Proposition 7.2.7, and Definitions 7.2.1–7.2.3 and 7.2.7:** the Jordan
  curve theorem, the area enclosed by a Jordan curve, and the orientation of Jordan arcs. The
  formalization replaces every use by a direct area computation (Section 6).
- **Theorem 2.1.1** (Schneider's Theorem 4.2.3, cited) is not stated in its 𝓗¹ form. The surface area
  measure is defined directly, and the properties the paper uses are proved (Section 2).
- **Theorem 1.3.1** quotes Gerver's Theorem 1 for orientation; the paper reproves its content in
  Chapter 3 (Theorems 3.5.4–3.5.6), and those are formalized.
- **Remarks** (15 in the paper), figures, the overview's informal descriptions and Remark 8.4.1's
  numerical comments are not formalized. The overview's results that restate later ones
  (Propositions 1.2.1, 1.2.2, Theorems 1.5.1, 1.5.2, 1.7.1) are formalized through the later
  statements or directly.
