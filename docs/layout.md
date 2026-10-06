# Layout

[Back to the README](../README.md)

The project has five libraries, one per result and one for the coercive route, and the files of the Palomar
registry at its root.

| Path | Contents |
| --- | --- |
| [`MovingSofaOptimality/`](../MovingSofaOptimality) | Baek's paper: its numbered results (the report's Section 9 lists the few left out), the results it cites, and the structure of Gerver's sofa |
| [`MovingSofaUniqueness/`](../MovingSofaUniqueness) | the uniqueness of Gerver's sofa, with Baek's definitions |
| [`MovingSofaBridge/`](../MovingSofaBridge) | the bridge between formal-conjectures' definitions and Baek's |
| [`MovingSofaStability/`](../MovingSofaStability) | the stability of Gerver's sofa, with Baek's definitions, and the punctured sofas that show its exponent is optimal |
| [`MovingSofaExtremal/`](../MovingSofaExtremal) | the coercive route: optimality and uniqueness from one certificate of the stability proof |
| [`ChallengeDefs.lean`](../ChallengeDefs.lean) | the definitions of the statements of record, which the Challenge copies |
| [`Challenge.lean`](../Challenge.lean), [`Solution.lean`](../Solution.lean) | the statements of record and their proofs |
| [`SolutionCoercive.lean`](../SolutionCoercive.lean) | the statements of record proved again through the coercive route |
| [`SolutionCoerciveComparator.lean`](../SolutionCoerciveComparator.lean) | the theorems of [`SolutionCoercive.lean`](../SolutionCoercive.lean) under the Challenge's names, for Comparator; no module imports it |
| [`comparator.json`](../comparator.json), [`comparator-coercive.json`](../comparator-coercive.json), [`formalization.yaml`](../formalization.yaml) | Comparator's configurations for the two solutions, and the Palomar metadata |
| [`REPORT.md`](../REPORT.md) | the audit of Baek's paper against its LaTeX source and the formalization |
| [`CREDITS.md`](../CREDITS.md) | how the formalization was made: who, by which procedure, and the time and effort of each round |
| [`docs/proof/`](proof/README.md) | the illustrated text of the proofs, with its figures |
| [`docs/paper/`](paper/README.md) | the arXiv manuscript of the uniqueness of Gerver's sofa, with its figures and Makefile |
| [`docs/archive/`](archive) | earlier documents: the first map of the uniqueness proof, and ChatGPT Pro 6's notes on the uniqueness, the stability and the coercive route |
| [`scripts/`](../scripts) | the axiom audits, the generators of two Lean files, the figures, and the documentation tools |

### `MovingSofaOptimality/`: Baek's paper

Facts that several files use live in `Basic/` under plain names ([`dot_uvec_pi_div_two`](../MovingSofaOptimality/Basic/Plane.lean#L238),
[`tendsto_supp`](../MovingSofaOptimality/Basic/ConvexBody.lean#L257), …). A helper lemma used by one part of the proof carries a prefix that names that
part: `ms_` for monotone sofas, `cn_` for the cap containing its niche, `nef_` for Nef polygons and
polygon caps, `mpc_` for maximum polygon caps, `ang_` for the rotation angle, `inj_` for the
injectivity condition, `cvx_` for convex curves, `opt_` for the upper bound, `gs_`, `gb_`, `gn_`,
`ga_`, `gv_` and `gm_` for Gerver's sofa, `env_` for envelopes, `af_` for the area formula and
`rom_` for Romik's system.

| Module | Paper content |
| --- | --- |
| [`MovingSofaOptimality/Basic/Plane.lean`](../MovingSofaOptimality/Basic/Plane.lean) | the plane: unit vectors, dot and cross products, rotations, lines, half-planes, area, and the facts about them that the other files share (values at the axes, continuity, derivatives, invariance of area) |
| [`MovingSofaOptimality/Basic/ConvexBody.lean`](../MovingSofaOptimality/Basic/ConvexBody.lean) | §2.1: convex bodies, support functions, edges and vertices, Hausdorff distance, Theorem 2.1.3 |
| [`MovingSofaOptimality/Basic/Interval.lean`](../MovingSofaOptimality/Basic/Interval.lean) | interval arithmetic and Taylor bounds for cos and sin, used by the two generated files of numerics |
| [`MovingSofaOptimality/Basic/LebesgueStieltjes.lean`](../MovingSofaOptimality/Basic/LebesgueStieltjes.lean) | §5.1: Lebesgue–Stieltjes measures and integrals |
| [`MovingSofaOptimality/Basic/SurfaceArea.lean`](../MovingSofaOptimality/Basic/SurfaceArea.lean) | the surface area measure σ_K, Proposition 2.1.2, §5.2 |
| [`MovingSofaOptimality/Sofa/Defs.lean`](../MovingSofaOptimality/Sofa/Defs.lean) | Chapter 1 and §2.2–2.3: hallways, moving sofas, supporting hallways, monotone sofas |
| [`MovingSofaOptimality/Intro/RotationAngleBound.lean`](../MovingSofaOptimality/Intro/RotationAngleBound.lean) | Theorem 1.5.1 |
| [`MovingSofaOptimality/Monotone/`](../MovingSofaOptimality/Monotone) | §2.2–2.5: supporting hallways, monotonization, caps and niches |
| [`MovingSofaOptimality/Balanced/`](../MovingSofaOptimality/Balanced) | Chapter 3: nef polygons (`NefPolygon`), polygon caps (`PolygonCap`), maximum polygon caps (§3.4, in four modules: `CapGeometry`, the geometry of polygon caps and their niches; `MaxPolygonCapExists`, Definition 3.4.1, Lemmas 3.4.1–3.4.2 and Theorem 3.4.3; `Polyline`, Definitions 3.4.2–3.4.4, Theorem 3.4.4 and Lemma 3.4.5; `MaximumPolygonCap`, Lemmas 3.4.6–3.4.8 and Theorems 3.4.9–3.4.10), balanced maximum sofas (`BalancedMaximumSofa`) |
| [`MovingSofaOptimality/Angle/`](../MovingSofaOptimality/Angle) | Chapter 4: the rotation angle of a balanced maximum sofa (Theorem 1.5.2) |
| [`MovingSofaOptimality/Injectivity/`](../MovingSofaOptimality/Injectivity) | Chapter 6 (except Theorem 6.1.2): the injectivity condition |
| [`MovingSofaOptimality/Convex/`](../MovingSofaOptimality/Convex) | Chapter 7: convex domains, curve area functionals, convex curves, Mamikon's theorem |
| [`MovingSofaOptimality/Optimality/`](../MovingSofaOptimality/Optimality) | Chapter 8, §8.1–8.3 and §8.5: the upper bound 𝒬 and its variation |
| [`MovingSofaOptimality/Gerver/Defs.lean`](../MovingSofaOptimality/Gerver/Defs.lean), [`MovingSofaOptimality/Gerver/Bounds.lean`](../MovingSofaOptimality/Gerver/Bounds.lean) | Gerver's sofa from Romik's parameters, and enclosures of the parameters |
| [`MovingSofaOptimality/Gerver/Frame.lean`](../MovingSofaOptimality/Gerver/Frame.lean), [`MovingSofaOptimality/Gerver/StructureCap.lean`](../MovingSofaOptimality/Gerver/StructureCap.lean), [`MovingSofaOptimality/Gerver/Structure.lean`](../MovingSofaOptimality/Gerver/Structure.lean) | Theorem 8.4.1 (except (2)), Theorem 8.4.2, Theorem 6.1.2 |
| [`MovingSofaOptimality/Gerver/Envelope.lean`](../MovingSofaOptimality/Gerver/Envelope.lean), [`MovingSofaOptimality/Gerver/EnvelopeArea.lean`](../MovingSofaOptimality/Gerver/EnvelopeArea.lean), [`MovingSofaOptimality/Gerver/NicheBounds.lean`](../MovingSofaOptimality/Gerver/NicheBounds.lean), [`MovingSofaOptimality/Gerver/Niche.lean`](../MovingSofaOptimality/Gerver/Niche.lean) | Theorem 8.4.1 (2): the niche of Gerver's sofa and its area |
| [`MovingSofaOptimality/Gerver/AreaBounds.lean`](../MovingSofaOptimality/Gerver/AreaBounds.lean) | the bound \|G\| ≥ 2.2 |
| [`MovingSofaOptimality/Gerver/Properties.lean`](../MovingSofaOptimality/Gerver/Properties.lean) | §8.4: Theorems 8.4.1–8.4.6, Proposition 8.4.4 |
| [`MovingSofaOptimality/Main.lean`](../MovingSofaOptimality/Main.lean) | Definition 8.1.2, Theorem 8.1.1 (2)–(3), Theorem 8.5.7, Corollary 8.5.8, Theorem 1.1.1 |
| [`MovingSofaOptimality/External/AreaFormula.lean`](../MovingSofaOptimality/External/AreaFormula.lean), [`MovingSofaOptimality/External/AreaFormula/`](../MovingSofaOptimality/External/AreaFormula) | Schneider's area formula (Remark 5.1.2 of *Convex Bodies*) |
| [`MovingSofaOptimality/External/Romik.lean`](../MovingSofaOptimality/External/Romik.lean), [`MovingSofaOptimality/External/Romik/`](../MovingSofaOptimality/External/Romik) | Romik's system: existence, uniqueness and enclosures of its solution |

### `MovingSofaUniqueness/`: the uniqueness of Gerver's sofa

One module per proposition of the informal proof ([Chapters 11 and 12](proof/11-selection.md) of the text):

| Module | Content |
| --- | --- |
| [`MovingSofaUniqueness/Rigid.lean`](../MovingSofaUniqueness/Rigid.lean) | rigid maps, the recovery of a closed set from a regular closed superset of the same area, moving sofas in a strip of height one, and horizontal translates of caps, niches and sofas |
| [`MovingSofaUniqueness/Mamikon.lean`](../MovingSofaUniqueness/Mamikon.lean) | square integrals and Mamikon displacements, the canonical triple of a cap of `𝒦^i` and Baek's maximum of `𝒬` (shared with the stability library) |
| [`MovingSofaUniqueness/Selection.lean`](../MovingSofaUniqueness/Selection.lean) | Proposition 1: polygon caps converging to a given maximizing cap |
| [`MovingSofaUniqueness/Variation.lean`](../MovingSofaUniqueness/Variation.lean) | Proposition 2 and the bounds (19): variations of the selected polygons and their limits |
| [`MovingSofaUniqueness/Curvature.lean`](../MovingSofaUniqueness/Curvature.lean) | Proposition 3: curvature bounds and the injectivity condition for every maximizing right-angle cap |
| [`MovingSofaUniqueness/AngleExtension.lean`](../MovingSofaUniqueness/AngleExtension.lean) | Proposition 4: the right-angle motion of the same sofa |
| [`MovingSofaUniqueness/Rigidity.lean`](../MovingSofaUniqueness/Rigidity.lean) | Proposition 5: equality in Mamikon's terms, and Gerver's cap up to a horizontal translation |
| [`MovingSofaUniqueness/RegularClosed.lean`](../MovingSofaUniqueness/RegularClosed.lean) | Proposition 6: Gerver's sofa is the closure of its interior |
| [`MovingSofaUniqueness/Main.lean`](../MovingSofaUniqueness/Main.lean) | the theorem |

Two more modules give a second proof of Baek's optimality theorem, which does not use Baek's Theorem 1.1.1, and
prove the theorem again from it (a remark at the end of Section 8 of the [manuscript](paper/README.md)); they do not import `Main`:

| Module | Content |
| --- | --- |
| [`MovingSofaUniqueness/Maximizing.lean`](../MovingSofaUniqueness/Maximizing.lean) | maximizing caps (existence, the injectivity condition at the right angle, the right-angle motion), and the assembly that turns the value and the shape of the maximizing right-angle caps into optimality and uniqueness; the coercive route uses it too |
| [`MovingSofaUniqueness/MaximizerRoute.lean`](../MovingSofaUniqueness/MaximizerRoute.lean) | the value of the maximizing right-angle caps from Baek's bound, their shape from the equality analysis of `Rigidity`, and the second proof of optimality and the theorem from them (namespace [`MovingSofaUniqueness.MaximizerRoute`](../MovingSofaUniqueness/MaximizerRoute.lean)) |

### `MovingSofaBridge/`: the bridge to formal-conjectures

[Chapter 13](proof/13-bridge.md) and [Appendix A](proof/appendix-a.md) of the text:

| Module | Content |
| --- | --- |
| [`MovingSofaBridge/GerverConstants.lean`](../MovingSofaBridge/GerverConstants.lean) | Gerver's four constants are unique, by elementary inequalities |
| [`MovingSofaBridge/RomikParams.lean`](../MovingSofaBridge/RomikParams.lean) | Gerver's four constants and Romik's parameters; the constants exist |
| [`MovingSofaBridge/Motion.lean`](../MovingSofaBridge/Motion.lean) | the two notions of moving sofa agree, and so do the two optimal areas |
| [`MovingSofaBridge/GerverSofa.lean`](../MovingSofaBridge/GerverSofa.lean) | the two Gerver's sofas are the same set |

### `MovingSofaStability/`: the stability

[Stability](stability.md) describes the theorems and the proof. The modules, by step of the proof:

| Module | Content |
| --- | --- |
| [`MovingSofaStability/Basic.lean`](../MovingSofaStability/Basic.lean) | Euclidean distance between sets, the deficit, the normalization and the statements |
| [`MovingSofaStability/WideDomain.lean`](../MovingSofaStability/WideDomain.lean) | Baek's bound `𝒬` on the enlarged domain of caps with corners, and its concavity there |
| [`MovingSofaStability/Deficit.lean`](../MovingSofaStability/Deficit.lean) | the first variation at Gerver's triple, which makes it the maximum, and the deficit as a slack plus squared Mamikon differences |
| [`MovingSofaStability/CapEstimate.lean`](../MovingSofaStability/CapEstimate.lean) | from the energies to the support function of the cap and the Euclidean distance between caps, with coefficient 2 sec φ; the coercive certificate |
| [`MovingSofaStability/Margins.lean`](../MovingSofaStability/Margins.lean) | the shape of a cap, interior balls, and the roof and margins of Gerver's sofa |
| [`MovingSofaStability/LocalGeometry.lean`](../MovingSofaStability/LocalGeometry.lean) | exposed faces, arm margins, the niche and the canonical triple of a cap near Gerver's |
| [`MovingSofaStability/LocalBound.lean`](../MovingSofaStability/LocalBound.lean) | Baek's area bound for the caps near Gerver's, without the injectivity condition, and their distance to Gerver's cap |
| [`MovingSofaStability/Terminal.lean`](../MovingSofaStability/Terminal.lean) | a missing final angle costs area |
| [`MovingSofaStability/Recovery.lean`](../MovingSofaStability/Recovery.lean) | from the cap back to the sofa: the sofa's cap, the Euclidean distance and the symmetric difference |
| [`MovingSofaStability/Global.lean`](../MovingSofaStability/Global.lean) | entry into the neighborhood by compactness, and the main theorems |
| [`MovingSofaStability/Sharpness.lean`](../MovingSofaStability/Sharpness.lean) | the punctured sofas: the exponent one half is optimal |
| [`MovingSofaStability/All.lean`](../MovingSofaStability/All.lean) | imports all the others |

### `MovingSofaExtremal/`: the coercive route

[The coercive route](coercive.md) describes the theorems and the proof. The library imports the stability library up to
`CapEstimate`, and the stability library's `Recovery` and `Global` import its `Main`:

| Module | Content |
| --- | --- |
| [`MovingSofaExtremal/Main.lean`](../MovingSofaExtremal/Main.lean) | the value and the shape of the maximizing right-angle caps from the coercive certificate, and optimality and uniqueness from them, through the assembly of [`MovingSofaUniqueness/Maximizing.lean`](../MovingSofaUniqueness/Maximizing.lean) |
| [`MovingSofaExtremal/Unified.lean`](../MovingSofaExtremal/Unified.lean) | optimality, uniqueness and stability in one theorem |
| [`MovingSofaExtremal/All.lean`](../MovingSofaExtremal/All.lean) | imports all the others |

### `scripts/`

| Path | Content |
| --- | --- |
| [`scripts/Audit.lean`](../scripts/Audit.lean) | the axiom and dependency audit, which also records the route of every result of the paper |
| [`scripts/AuditMaximizerRoute.lean`](../scripts/AuditMaximizerRoute.lean) | checks that the second proof of optimality uses neither Baek's Theorem 1.1.1, nor the results from which Baek derives the right-angle motion and the injectivity condition of Baek's cap from its balance, nor [`MovingSofaUniqueness.Main`](../MovingSofaUniqueness/Main.lean) |
| [`scripts/AuditCoerciveRoute.lean`](../scripts/AuditCoerciveRoute.lean) | checks that the coercive route and the stability library use neither Baek's Theorem 1.1.1, nor the results of his balance argument, nor the first proof of uniqueness, that optimality and uniqueness do not use stability, and that [`SolutionCoercive.lean`](../SolutionCoercive.lean) proves exactly the statements of [`Solution.lean`](../Solution.lean) |
| [`scripts/route_check.py`](../scripts/route_check.py), [`docs/paper_routes.tsv`](paper_routes.tsv), [`docs/route_differences.tsv`](route_differences.tsv) | the route check: the results that each of Baek's proofs cites (extracted from the paper's LaTeX source), and the reviewed differences from the Lean proofs, each with its reason |
| [`scripts/romik/`](../scripts/romik), [`scripts/area/`](../scripts/area) | the generators of the two Lean files of interval arithmetic |
| [`scripts/figures/`](../scripts/figures) | the figures of the text: the geometry of Gerver's sofa (`gerver.py`), the drawing helpers (`sofa_figures.py`), one module per chapter, and `make_all.py` |
| [`scripts/sync_challenge_defs.py`](../scripts/sync_challenge_defs.py) | copies the shared definitions into the Challenge, or checks the copy |
| [`scripts/linkify_docs.py`](../scripts/linkify_docs.py), [`scripts/check_md_tables.py`](../scripts/check_md_tables.py) | link the documents to the code; check their tables |
