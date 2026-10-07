# Formalizations of Baek's proof

[Back to the README](../README.md)

Three Lean 4 formalizations prove Jineon Baek's theorem ([arXiv:2411.19826](https://arxiv.org/abs/2411.19826))
that Gerver's sofa has the largest area of any moving sofa: [deancureton/MovingSofa](https://github.com/deancureton/MovingSofa), directed by
Dean Cureton; [RuifengCao/sofa-formal](https://github.com/RuifengCao/sofa-formal), directed by Ruifeng Cao; and this repository. AI agents wrote
each project's own Lean code. This page calls the first two Cureton's and Cao's formalizations and
compares the three at the commits below.

On 5 October 2026 we read the sources and documents of the three projects at these commits, built
the three formalizations, and listed the axioms and the declarations of the three with the
same Lean script. We did not review their proofs line by line. Where a statement rests only on a
project's own documents, the text says so. Dates are in UTC.

| | Cureton | Cao | This repository |
| --- | --- | --- | --- |
| Commit | [`4d55691`](https://github.com/deancureton/MovingSofa/tree/4d5569131940815f47a9ccf3e90a4c5043c56127) (22 September 2026); its Lean files are those of `a075386`, which formal-conjectures links | [`ca8585c`](https://github.com/RuifengCao/sofa-formal/tree/ca8585c28c3c39528d5f5da87976af8fbfe48c18) (24 September 2026); its definitions and proofs are those of `838baca`, which formal-conjectures links, and it changes comments and adds an audit script | [`16653ae`](https://github.com/vltanh/lean4-moving-sofa/tree/16653ae81e0e4f52a362bafae2ad3440100ad065) (4 October 2026), version 4 of Palomar entry PALOMAR-2026-10-02-000008 |
| Lean and Mathlib | v4.35.0-rc1 | v4.33.1, the versions of formal-conjectures | v4.35.0-rc3 |
| Code outside Mathlib and its dependencies | the packages jordan_pick and LeanCert; copies of Dawid Trela's GerverSofaLean, of Jonathan Ho's Brunn–Minkowski inequality (lean-pool) and of ten Tau Ceti files | none | none |
| Theorems that Comparator checks | 3 | 4 | 12 |

## Summary

All three prove the statement `sofaConstant = volume gerversSofa` of Google DeepMind's
formal-conjectures with Lean's standard axioms only. All three found that some of Baek's proofs need
repairs, and none of the repairs affects his theorem. They differ in how much of the paper's
machinery they keep and in what they prove besides.

Cureton's formalization keeps the most. It defines the surface area measure through the length of
the boundary, as Schneider's book does, and proves the theorem about it that the paper quotes, in a
corrected form; it uses the Brunn–Minkowski inequality and the Jordan curve theorem from other Lean
libraries. It is also the largest: 66,000 lines of
its own code, and a copy of Trela's library of 181,000 lines, most of it a kernel-checked certificate
for Gerver's constants. Its Comparator configuration replays the proofs in a second, independent
kernel.

Cao's formalization is the smallest, with 28,000 lines, and replaces the most. It defines the
surface area measure as h″ + h, computes areas directly where the paper uses Jordan curves and
Green's theorem, replaces the weak convergence of surface area measures by the convergence of their
distribution functions, and proves the concavity of 𝒬 on a larger set, so that it needs neither the
convexity of the class 𝒦ⁱ (Theorem 8.1.1) nor the Brunn–Minkowski inequality. It works with caps
where the paper works with balanced maximum sofas, and uses Hammersley's sofa, and a bound on the
area of Gerver's cap, where the paper uses the area of Gerver's sofa. It alone compiles
formal-conjectures' statements against formal-conjectures' own Mathlib and keeps the whole of
formal-conjectures' file in its Challenge. It also proves Hammersley's bounds on the sofa constant,
and its repository includes the outputs of its axiom audits.

This repository defines the surface area measure as Cao's formalization does and also avoids the
Jordan curve theorem, Green's theorem and the Brunn–Minkowski inequality, but keeps closer to the
paper elsewhere: it proves and uses the weak convergence of surface area measures, the Portmanteau
step, Theorem 3.5.6 and Theorem 8.1.1, and its continuous integration compares the results that each
Lean proof uses with those that Baek's proof cites. It also proves that Gerver's sofa is the only
optimal sofa up to rigid motions, which formal-conjectures lists as open, and encloses the area of Gerver's sofa in
[2.2192, 2.2199]. It is the only one of the three registered in Palomar.

## 1. What each proves

Each formalization copies the definitions and statements of formal-conjectures' file
[`MovingSofa.lean`](https://github.com/google-deepmind/formal-conjectures/blob/b022febed81da0c91de2546a26000cf695c7ba38/FormalConjectures/Wikipedia/MovingSofa.lean) into a Challenge file that imports only Mathlib, and proves them in a
Solution file. Comparator checks that the two files state the same theorems with the same definitions
and that the proofs use no axiom besides [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).

| Theorem that Comparator checks | Cureton | Cao | This repository |
| --- | --- | --- | --- |
| [`ABφθSpec.existsUnique`](https://github.com/google-deepmind/formal-conjectures/blob/b022febed81da0c91de2546a26000cf695c7ba38/FormalConjectures/Wikipedia/MovingSofa.lean#L163): Gerver's four constants exist and are unique | yes | yes | yes |
| [`isMovingSofa_gerversSofa`](https://github.com/google-deepmind/formal-conjectures/blob/b022febed81da0c91de2546a26000cf695c7ba38/FormalConjectures/Wikipedia/MovingSofa.lean#L208): Gerver's sofa is a moving sofa | yes | yes | yes |
| [`sofaConstant_eq_volume_gerversSofa`](https://github.com/google-deepmind/formal-conjectures/blob/b022febed81da0c91de2546a26000cf695c7ba38/FormalConjectures/Wikipedia/MovingSofa.lean#L235) | yes | yes | yes |
| [`sofaConstant_eq`](https://github.com/google-deepmind/formal-conjectures/blob/b022febed81da0c91de2546a26000cf695c7ba38/FormalConjectures/Wikipedia/MovingSofa.lean#L228), the same with formal-conjectures' `answer` marker | no | yes, without the marker | no |
| [`volume_eq_sofaConstant_iff_congruent_gerversSofa`](https://github.com/google-deepmind/formal-conjectures/blob/b022febed81da0c91de2546a26000cf695c7ba38/FormalConjectures/Wikipedia/MovingSofa.lean#L246): every sofa of maximum area is congruent to Gerver's sofa, open in formal-conjectures | no | no | yes |
| Statements in Baek's own definitions | none | none | five: Romik's parameters exist and are unique in a box; the area of Gerver's sofa lies in [2.2192, 2.2199]; Baek's Theorem 1.1.1; uniqueness |
| Statements that the two sets of definitions agree | none | none | three |

Apart from the changes listed below, every definition and statement that the three copies keep has
the text of formal-conjectures' file. Cureton's copy and ours leave out [`sofaConstant_eq`](https://github.com/google-deepmind/formal-conjectures/blob/b022febed81da0c91de2546a26000cf695c7ba38/FormalConjectures/Wikipedia/MovingSofa.lean#L228), `unitSquare` and formal-conjectures' tests, and
Cureton's also leaves out the open uniqueness statement; Cao's copy keeps the whole file. The other
changes leave every statement as it is: all three copy the `ℝ²` notation and two instances from
formal-conjectures' utility library; Cureton's copy and ours give the anonymous topology instance a
name, since Comparator compares names; our copy moves everything into the namespace
`FormalConjectures.MovingSofa`; Cao's copy drops the `answer` marker, which the kernel ignores; and
Cureton's writes `Module.Basis.orientation` for `Basis.orientation`, the same constant. Only Cao's
formalization compiles its copy against formal-conjectures' own Mathlib. In the newer Mathlib that the
other two use, the topology that formal-conjectures puts on rigid motions is induced from a different
instance on continuous affine maps, which gives the same topology.

We built Cao's formalization at `ca8585c` and Cureton's at `4d55691`, and listed the axioms of every
theorem that their Comparator configurations name with Lean's `collectAxioms`: each depends on
[`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound) only. This repository's continuous integration and
Palomar's verification check the same of its twelve theorems.

Besides the theorems that Comparator checks, Cureton's formalization states Baek's theorem in
Baek's convention, where a motion may start with a translation
([`paperGerverSofa_maximum`](https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Sofa/Maximum.lean#L22-L61)), proves that every
moving sofa in one convention has a translate of the same area in the other
([`canonical_paper_motion_bridge`](https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Motion/CanonicalBridge.lean#L36)), and proves three descriptions of
Gerver's sofa equal (Section 2). Cao's proves Hammersley's bounds π/2 + 2/π ≤ `sofaConstant` ≤ 2√2
([lower](https://github.com/RuifengCao/sofa-formal/blob/ca8585c28c3c39528d5f5da87976af8fbfe48c18/Sofa/HammersleyArea.lean#L221-L226),
[upper](https://github.com/RuifengCao/sofa-formal/blob/ca8585c28c3c39528d5f5da87976af8fbfe48c18/Sofa/Hammersley.lean#L363-L371)).

## 2. Definitions

### Moving sofas

In formal-conjectures, a moving sofa is a nonempty closed connected subset of the horizontal arm of
the hallway together with a continuous path of isometries of the plane (reflections included) that
starts at the identity, keeps the set in the hallway and ends with it in the vertical arm; the sofa
constant is the supremum of the areas of moving sofas, in ℝ≥0∞. Baek's Definition 1.1.2 moves any
translate of such a set, by rotations and translations. Both conventions give the same supremum.

- Cureton's formalization has its own notion of motion in Baek's convention
  ([`IsPaperMotion`](https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Motion/Basic.lean#L11-L20)) and relates the two as above. It also
  proves that a continuous path of isometries that starts at the identity preserves orientation.
- Cao's has no second notion of moving sofa: a sofa with rotation angle ω is a set some translate of
  which is a moving sofa in formal-conjectures' sense
  ([`IsSofaWithAngle`](https://github.com/RuifengCao/sofa-formal/blob/ca8585c28c3c39528d5f5da87976af8fbfe48c18/Sofa/StdPos.lean#L167-L172)).
- This repository states Baek's definitions on ℝ × ℝ in their own namespace
  ([Definitions](../docs/definitions.md)), and Comparator checks the bridge theorems [`Bridge.isMovingSofa_iff`](../Challenge.lean#L732)
  and [`Bridge.sofaConstant_eq`](../Challenge.lean#L740).

Cureton's and Cao's formalizations work in formal-conjectures' plane, `EuclideanSpace ℝ (Fin 2)`; this
repository works in ℝ × ℝ and converts at the bridge.

### Convex bodies and the surface area measure

Cureton's formalization uses Mathlib's convex bodies and defines the surface area measure σ_K through
the length of the boundary: the image of the length measure on the boundary points with a unique
normal under the normal map, with separate cases for points and segments
([definition](https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Analysis/SurfaceMeasure/Basic.lean#L35-L44)). It proves
Schneider's theorem that the paper quotes as its Theorem 2.1.1, for bodies with interior points and
for arcs of normal angles shorter than π
([theorem](https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Analysis/SurfaceMeasure/Properties.lean#L89-L103)); as the paper states it, the theorem fails
for segments.

Cao's formalization and this repository define σ_K the same way: as the Lebesgue–Stieltjes measure of
t ↦ ⟨v_K⁺(t), v_t⟩ + ∫₀ᵗ h_K, that is σ_K = h_K″ + h_K
([`sigmaK`](https://github.com/RuifengCao/sofa-formal/blob/ca8585c28c3c39528d5f5da87976af8fbfe48c18/Sofa/SurfaceArea.lean#L250-L262) in Cao's, [`sigma`](../MovingSofaOptimality/Basic/SurfaceArea.lean#L169) here). Neither states Theorem 2.1.1;
both prove that the atoms of σ_K are the edge lengths. Cao's states convexity and compactness as
hypotheses, and this repository uses a predicate [`IsConvexBody`](../MovingSofaOptimality/Basic/ConvexBody.lean#L52).

### Gerver's sofa

formal-conjectures defines Gerver's sofa from Gerver's four constants A, B, φ, θ, the unique solution
of four equations with 0 ≤ φ ≤ θ ≤ π/4 and A, B ≥ 0, as the sofa carried by Gerver's rotation path.
Baek's paper defines it from Romik's solution of his Equations (25)–(44) (Definitions 8.1.2 and
8.4.2), which this repository encodes by 22 parameters.

- Cureton's formalization has three descriptions and proves them equal
  ([`gerver_canonical_paper_literal`](https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Gerver/Area.lean#L23-L145)):
  formal-conjectures' set, the set along Romik's explicit path (from Trela's library), and Baek's cap
  minus its niche.
- Cao's uses formal-conjectures' set only. It obtains Baek's curves 𝐀 and 𝐂 as vertex curves of the
  cap, and the tails 𝐁 and 𝐃 as envelopes of the inner walls.
- This repository uses Romik's solution, as the paper does, and proves formal-conjectures' set equal
  to the result ([`Bridge.gerversSofa_eq`](../Challenge.lean#L748)).

## 3. How closely each follows the paper

### The numbered results

Baek's paper has 301 numbered environments: 68 theorems, 44 lemmas, 38 propositions, 2 corollaries,
134 definitions and 15 remarks.

- In this repository, Lean docstrings name 146 of the 152 theorems, lemmas, propositions and
  corollaries. The other six are Proposition 1.2.1 (stated as Proposition 2.3.1), Theorem 1.3.1
  (Gerver's theorem, quoted for orientation), Theorem 2.1.1 (Schneider's theorem in its Hausdorff
  measure form), and Theorems 7.2.1 and 7.2.3 and Proposition 7.2.7 (the Jordan curve theorem, Green's
  theorem and the orientation of Jordan curves), whose uses are replaced
  ([report, Section 9](REPORT.md#9-not-formalized)).
- In Cao's formalization, docstrings and section headers cite 112 of them, and the content of 18 more,
  in whole or in part, is in lemmas that do not cite them (for instance Lemma 3.4.1 and Proposition
  3.5.1, on mirror images). Its README says that the Jordan curve arguments are replaced by direct
  area computations (Theorem 7.2.1) and lists Theorem 7.2.3, Proposition 7.2.7 and Lemmas 7.3.1 and
  7.3.5 (Green's theorem and its uses) as not formalized, and its sources say that 13 more are replaced
  or not needed (for instance the polyline of Theorem 3.4.4, the calculus of Section 5.1 and Lemma
  6.3.1). The remaining four do not appear: Theorem 1.3.1, which the paper quotes; Proposition 3.1.1, which serves the representation of Section 3.3 by Nef
  polygons that Cao's formalization replaces; and Lemmas 7.1.6 and 8.1.3, which no proof of the paper
  cites.
- Cureton's notes say that 20 of the 286 numbered environments other than remarks have no Lean
  counterpart (11 of them theorems, lemmas or propositions, by our count), and give a reason for each; the main theorem uses none of them
  ([NOTES.md](https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/NOTES.md?plain=1#L126-L152)). Its Lean files do not cite the paper's
  numbers, so this count is taken from its notes. Unlike the other two, it takes the Jordan curve
  theorem (Theorem 7.2.1) from jordan_pick and proves the area formula of Theorem 7.2.3.

### The proofs

The table compares the steps where at least one formalization takes another route than the paper.

| Step of the paper | Cureton | Cao | This repository |
| --- | --- | --- | --- |
| σ_K and Theorem 2.1.1 (quoted from Schneider) | the length of the boundary; Theorem 2.1.1 for bodies with interior points and short arcs | σ_K = h″ + h; Theorem 2.1.1 not stated | σ_K = h″ + h; Theorem 2.1.1 not stated |
| Theorem 5.2.2, dv_K⁺ = v_t dσ_K | polygons and a limit, as in the paper | an estimate by Riemann sums | integration by parts in the definition of σ_K |
| Weak convergence of σ_K (Theorem 4.1.3, quoted) and the Portmanteau step (Lemma 6.4.2) | proved and used; Lemma 6.4.2 through restrictions to sets with null frontier | Theorem 4.1.3 not stated: Chapter 4 uses inclusions of segments, Chapter 6 the convergence of distribution functions; no Portmanteau step | proved and used as in the paper |
| Polygon caps: the derivative of the area (Theorem 3.1.2, Lemmas 3.4.5–3.4.7) | Nef polygons, as in the paper | regions between graphs; no polyline | Nef polygons, as in the paper |
| Balanced maximum sofas (Theorem 3.5.6) | as in the paper | no separate statement; the final step works with caps | as in the paper |
| An area above 2.2 (Theorems 1.5.1 and 8.1.1) | Gerver's sofa, \|G\| ≥ 11/5 | Hammersley's sofa, π/2 + 2/π; for Gerver's cap, \|C(G)\| ≥ 2.2 | Gerver's sofa, \|G\| ≥ 2.2 (from its enclosure in [2.2192, 2.2199]) |
| The area formula \|K\| = ½∫ h_K dσ_K (Theorem 7.1.3, quoted) | polygons and a limit | a decomposition into sectors around an interior point | a change of variables along the boundary |
| Convexity of 𝒦ⁱ by Brunn–Minkowski (Theorem 8.1.1) | Ho's inequality | not needed: 𝒬 is concave on a larger set | slices and Fubini's theorem |
| Symmetry of mixed areas (quoted from Schneider in the proof of Theorem 8.5.1) | polygons and a limit | integration by parts | integration by parts |
| Jordan curves and Green's theorem (Chapters 7 and 8) | the Jordan curve theorem from jordan_pick; the area formula of Theorem 7.2.3 proved with a winding-number kernel | areas computed directly | areas computed directly |
| The maximum of 𝒬 (Theorem 7.1.5, Corollary 8.5.8) | Theorem 7.1.5, as in the paper | concavity at λ = ½; Theorem 7.1.5 proved but not used | Theorem 7.1.5, as in the paper |
| Theorem 6.1.2, Gerver's sofa satisfies the injectivity condition | checked from Romik's formulas | checked from the support function | checked from Romik's equations |
| Theorem 8.4.1, the structure of Gerver's sofa (no proof in the paper) | proved | proved in the form the proof uses | proved |

Sources: Cureton's notes ([errors and their repairs](https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/NOTES.md?plain=1#L59-L73),
[other routes](https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/NOTES.md?plain=1#L113-L124)); Cao's
[README](https://github.com/RuifengCao/sofa-formal/blob/ca8585c28c3c39528d5f5da87976af8fbfe48c18/README.md?plain=1#L49-L54), its
[blueprint](https://github.com/RuifengCao/sofa-formal/blob/ca8585c28c3c39528d5f5da87976af8fbfe48c18/blueprint/ch3-8.md) (a development log) and the headers of its files; this repository's
[report, Section 7](REPORT.md#7-departures-from-the-papers-proofs), and the route check of its
continuous integration, which records 222 differences between the results that the Lean proofs use
and those that Baek's proofs cite, each with its reason ([route_differences.tsv](route_differences.tsv)).
We read the Lean declarations behind each entry. For Cao's formalization, the dependency graph of the
compiled main theorem confirms that it does not use Theorem 7.1.5.

The formalizations also add hypotheses where the paper's statements need them, for instance the
boundedness of the Nef polygons in Theorem 3.1.2, which Cureton's formalization and this repository
both add. Cao's Theorems 8.1.8 and 8.2.4 assume that the niche of the cap lies in the cap
([`IsInjectiveCap.inL`](https://github.com/RuifengCao/sofa-formal/blob/ca8585c28c3c39528d5f5da87976af8fbfe48c18/Sofa/NicheCore.lean#L835-L839)); it applies them to balanced maximum
caps and to Gerver's cap, which satisfy it, so its main theorem is unaffected. The paper uses this
fact without stating it, and Cureton's formalization and this repository prove the two theorems
without it (E21 in the [report](REPORT.md#3-errors-and-gaps-in-the-paper)).

## 4. Gerver's sofa

| | Cureton | Cao | This repository |
| --- | --- | --- | --- |
| Gerver's four constants | from Trela's library: interval arithmetic excludes all but a small cell, where a Krawczyk-type contraction gives the unique solution | interval arithmetic narrows the solutions to a small box, where a Krawczyk-type contraction gives the unique solution | uniqueness by monotonicity inequalities on the whole domain; existence from Romik's solution |
| Romik's solution | Romik's explicit formulas, from Trela's library | not used | unique in φ ∈ [0.039, 0.04], θ ∈ [0.68, 0.69], by a contraction on that box |
| How the numbers are checked | `decide +kernel`: 26,794 calls in Trela's library and 2 in its own code | `decide +kernel`, 120 calls | interval arithmetic whose steps are lemmas closed by `norm_num` |
| Gerver's sofa moves around the corner | Trela's proof, in formal-conjectures' form, and its own, in Baek's | its own; connectedness by interval bisections | from Theorem 8.4.1 and Theorem 2.3.2 |
| Area of Gerver's sofa | at least 11/5, and finite (an interval certificate) | no bound stated for \|G\| itself (its theorems give π/2 + 2/π ≤ \|G\| ≤ 2√2); its cap has area at least 2.2 | between 2.2192 and 2.2199 |
| Theorems 6.1.2, 8.4.1, 8.4.2 | proved | proved; 8.4.1 (2) in the form the proof uses | proved |

Every row describes the formalization's own proof, except where it names Trela's library. Cureton's
notes add that formal-conjectures' equations for the constants were compared with Gerver's and
Romik's papers only numerically
([NOTES.md](https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/NOTES.md?plain=1#L25-L28)). In this repository, the bridge proves
that formal-conjectures' set equals the set defined from Romik's solution, and the area bounds agree
with Gerver's value 2.21953….

## 5. Errors found in the paper

Each project records the places where Baek's proofs need repair: this repository in its
[report](REPORT.md) (Sections 2 to 7), Cureton's in its notes, Cao's in its blueprint and in
comments. We merged the three lists, matching items by content and classifying each against the
paper's LaTeX source. They describe 99 distinct issues: 12 errors or gaps (a step fails, or a claim is
used without proof, and a new argument or hypothesis is needed), 57 misprints with an evident fix, 15
conventions or routine details that the paper leaves to the reader, and 15 that are not errors (for
instance a hypothesis that a proof does not use).

| Recorded by | Issues | Errors and gaps | Misprints | Conventions and details | Not errors |
| --- | --- | --- | --- | --- | --- |
| this repository's report | 93 | 12 | 57 | 12 | 12 |
| Cureton's notes | 48 | 11 | 34 | 2 | 1 |
| Cao's blueprint and comments | 20 | 5 | 8 | 5 | 2 |
| all three | 12 | 5 | 7 | 0 | 0 |

The three lists are not alike. The report lists every slip it found, typographical ones included.
Cureton's notes publish 44 of the 76 places that were recorded (11 errors and gaps and 33 misprints)
and leave out 16 typos without mathematical content, 13 conventions and 3 non-errors. Cao's remarks
are spread over a development log. The table counts distinct issues and classifies each one itself: three items
of Cureton's notes describe two issues each, one issue comes from its list of results not formalized
(the Mamikon region of Definition 7.4.1), and two items are classified differently from the notes
(the truncated proof of Proposition 7.2.6 counts as a routine detail, the unchecked limit in the proof
of Theorem 3.5.2 as a gap). So Cureton's row has 48 issues: 11 errors and gaps, 34 misprints, 2
conventions and 1 non-error.

The twelve issues that all three record include the parallelogram P_ω printed for the fan F_ω in
Definition 3.2.5, the unproved convergence of polygon niches in the proof of Theorem 3.5.4, the proof
of Theorem 6.1.2, the missing proof of Theorem 8.4.1, and the use of 𝒩(K) ⊆ K in Lemma 8.1.7 and
Theorem 8.2.4, which the class 𝒦ⁱ does not provide. Each of the 44 errors, gaps and misprints in
Cureton's notes is in the report; twelve of them were added in commit `16653ae`, with credit. Six
issues are recorded only by Cao's project (five) or Cureton's (one, from its list of results not
formalized): three conventions or routine details and three that are not errors. None of them needs
a new argument.

The projects describe some issues differently. The proof of Theorem 6.1.2 says that Gerver's Theorem 2
constructs maximum polygon sofas converging to Gerver's sofa. The report reads this as a misreading of
Gerver's theorem, which is a local statement; Cureton's notes call the step circular, since a balanced
maximum sofa has maximum area; Cao's blueprint says that the claim needs checking against Gerver's
paper, and its README counts the theorem among the results that Baek imports. All three check the
injectivity condition for Gerver's sofa directly. The report also calls Definition 3.2.5 and
Proposition 5.1.4 errors, since they are false as printed, where Cureton's notes call them misprints,
and the two propose opposite repairs for the conflict between the domain ℬ_Θ of Theorem 3.4.3 and the
hypothesis of Lemma 3.4.2.

## 6. Checking

What a reader has to trust is the same for the three: Lean's kernel, the Mathlib definitions that the
statements use, and the Challenge file. Lean checks the code outside Mathlib that Cureton's
formalization uses as it checks the project's own, and the axiom checks show that the theorems rest on
no further axiom; that code adds to the time a build takes, not to what has to be trusted.

| | Cureton | Cao | This repository |
| --- | --- | --- | --- |
| Comparator's configuration replays the proofs in the independent kernel nanoda | yes | no; its UPSTREAM.md and its prize submission report a separate run with nanoda | yes, and so does Palomar's verification |
| Axiom audit in the repository | none | `#print axioms` for 1,473 results, and `collectAxioms` for every constant, with their outputs | `collectAxioms` for every constant, run by continuous integration |
| Continuous integration | none | none | build, axiom audit, route check, documentation checks, Palomar's preflight |
| `set_option` | none in its own code; 18,577 in Trela's library, 977 of which remove the limit on heartbeats | 6 heartbeat limits, 3 that turn off asynchronous elaboration | none |
| Uses Lean's module system | no (its ten copied Tau Ceti files do) | no | yes |

## 7. Size

Lines of code exclude comments and blank lines; the statement files with `sorry` and the audit scripts
are left out. The numbers of theorems and definitions are those of the compiled declarations that a
user can name, counted by the same script for the three.

| | Cureton | Cao | This repository |
| --- | --- | --- | --- |
| Lean files | 376 | 86 | 65 |
| Lines of code | 66,203 | 27,654 | 37,901: 31,992 for Baek's paper, 3,713 for the uniqueness, 1,925 for the bridge, 271 for the definitions and the Solution |
| Copied code | 1,048 files, 182,788 lines (181,129 in Trela's library) | none | none |
| Theorems and definitions | 2,490 and 530 | 2,328 and 454 | 2,680 and 580 |
| Of these, used by the proof of `sofaConstant = volume gerversSofa` | 2,406 and 470 | 2,086 and 391 | 2,372 and 498 |
| Theorems and definitions that this proof uses from libraries other than Mathlib and its dependencies | 13,920 from Trela's library, 255 from LeanCert, 139 from jordan_pick, 33 from lean-pool, 14 from Tau Ceti | none | none |
| Mathlib declarations (theorems, definitions, instances and types) that this proof uses | 39,595 | 31,574 | 30,126 |
| Largest file, in lines as Palomar counts them | 2,193; 11,372 in Trela's library | 1,235; 1,540 with the audit file `Sofa/Check.lean` | 3,051, generated |
| Build on our machine (20 cores, Mathlib from its cache) | 1 h 21 min, 15.4 hours of user CPU time | 6 min 35 s, 0.3 hours | 2 min 51 s, 0.2 hours |

## 8. Status on 5 October 2026

- formal-conjectures links Cureton's formalization from [`sofaConstant_eq`](https://github.com/google-deepmind/formal-conjectures/blob/b022febed81da0c91de2546a26000cf695c7ba38/FormalConjectures/Wikipedia/MovingSofa.lean#L228) and
  [`sofaConstant_eq_volume_gerversSofa`](https://github.com/google-deepmind/formal-conjectures/blob/b022febed81da0c91de2546a26000cf695c7ba38/FormalConjectures/Wikipedia/MovingSofa.lean#L235) (pull request
  [#6440](https://github.com/google-deepmind/formal-conjectures/pull/6440), merged on 21 September), Cao's from the four
  theorems it proves ([#6526](https://github.com/google-deepmind/formal-conjectures/pull/6526), merged on 24 September),
  and Trela's GerverSofaLean from [`isMovingSofa_gerversSofa`](https://github.com/google-deepmind/formal-conjectures/blob/b022febed81da0c91de2546a26000cf695c7ba38/FormalConjectures/Wikipedia/MovingSofa.lean#L208). Pull request
  [#6808](https://github.com/google-deepmind/formal-conjectures/pull/6808), opened on 3 October, would link this repository and mark the
  uniqueness statement solved; it is open.
- Only this repository is registered in Palomar. Cureton's repository has a branch that ran Palomar's
  preflight five times on 20 September; none completed. Two runs stopped at Palomar's checks of the
  package setup (the package name of lean-pool and Tau Ceti's Mathlib pin), which the copies of
  lean-pool and Tau Ceti were made to pass; one at checking out a commit not yet pushed; one in
  Comparator's stage, when the build was denied permission to write outside the project, which its
  notes say building the copies inside the package avoids; and the last, on the commit that
  formal-conjectures links, ran out of its 5.5 hours in Comparator's stage. Since 28 September,
  Palomar has required every Lean file of a submission to use Lean's module system and to have at
  most 10,000 lines; Cao's files and Cureton's own do not use the module system, and Trela's library
  in Cureton's has a file of 11,372 lines.
- A pull request to the Justin Sun Prize
  ([TheJustinSunPrize/awards#4441](https://github.com/TheJustinSunPrize/awards/pull/4441)) asks to record Cao's
  formalization; it notes that Cureton's is earlier. It is open.

## 9. How they were made

| | Cureton | Cao | This repository |
| --- | --- | --- | --- |
| Directed by | Dean Cureton | Ruifeng Cao | The-Anh Vu-Le |
| AI systems | OpenAI Codex agents (GPT-5.6), then Claude Code agents | Claude Opus 5, then Claude Opus 5.5 | Claude Opus 5.5 in Claude Code; ChatGPT Pro 6 for the uniqueness argument and drafts |
| Time | about four days, until 20 September 2026 | 42 rounds, 16 to 23 September 2026 | eight rounds over three days, until 4 October 2026; the first, Baek's paper, took a session of 3 hours 50 minutes with 19 sub-agents |
| Review | AI agents, each starting from a fresh context, reviewed each proof and checked the statement against the paper; no human expert has reviewed the mathematics | a check by the assistant that wrote it | AI agents, each starting from a fresh context, checked the statements and the report against the paper's source; no person has reviewed the proofs |

The first two columns come from the projects' own documents: Cureton's
[README](https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/README.md?plain=1#L11) and
[metadata](https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/formalization.yaml#L135-L183), and Cao's
[prize submission](https://github.com/TheJustinSunPrize/awards/pull/4441) and the comments of its files. The rounds of this
repository are in [CREDITS.md](../docs/CREDITS.md).

## 10. Other Lean projects on the moving sofa

A search of GitHub on 5 October 2026 found six other Lean projects on the moving sofa problem. None of
them proves the optimality of Gerver's sofa.

| Repository | What it proves |
| --- | --- |
| [dawidmtrela-dotcom/GerverSofaLean](https://github.com/dawidmtrela-dotcom/GerverSofaLean) | Gerver's four constants exist and are unique, by a kernel-checked certificate, and Gerver's sofa is a moving sofa; formal-conjectures links it, and Cureton's formalization copies it |
| [abobreshov/moving-sofa-lean](https://github.com/abobreshov/moving-sofa-lean) | the problem stated, and the unit square, the half disc and Hammersley's sofa moved around the corner; the source of an entry of Lean Pool |
| [Li-Hongmin/jsp-000018-sofa](https://github.com/Li-Hongmin/jsp-000018-sofa) | definitions and the main statements, with `sorry` |
| [Khurramcoder/Moving_sofa](https://github.com/Khurramcoder/Moving_sofa) | definitions and Gerver's construction; the optimality is a named proposition, not proved, and the facts about Hammersley's sofa are `sorry` |
| [ElVec1o/moving-sofa-local-max](https://github.com/ElVec1o/moving-sofa-local-max) | lemmas for the ambidextrous problem; the project began as an argument for the local maximality of Gerver's sofa |
| [devinokeefe/ambidextrous-sofa-bounds](https://github.com/devinokeefe/ambidextrous-sofa-bounds) | upper bounds for the ambidextrous problem: 2√2 − 1, and 353/200 by a certificate whose checker is proved correct in Lean |
