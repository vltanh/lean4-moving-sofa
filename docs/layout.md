# Layout

[Back to the README](../README.md)

The project has three libraries, one per result, and the files of the Palomar registry at its root.

| Path | Contents |
| --- | --- |
| [`MovingSofaOptimality/`](../MovingSofaOptimality) | Baek's paper: every numbered result, the results it cites, and the structure of Gerver's sofa |
| [`MovingSofaUniqueness/`](../MovingSofaUniqueness) | the uniqueness of Gerver's sofa, with Baek's definitions |
| [`MovingSofaBridge/`](../MovingSofaBridge) | the bridge between formal-conjectures' definitions and Baek's |
| [`ChallengeDefs.lean`](../ChallengeDefs.lean) | the definitions of the statements of record, which the Challenge copies |
| [`Challenge.lean`](../Challenge.lean), [`Solution.lean`](../Solution.lean) | the statements of record and their proofs |
| [`comparator.json`](../comparator.json), [`formalization.yaml`](../formalization.yaml) | Comparator's configuration and the Palomar metadata |
| [`REPORT.md`](../REPORT.md) | the audit of Baek's paper against its LaTeX source and the formalization |
| [`docs/proof/`](proof/README.md) | the illustrated text of the proofs, with its figures |
| [`docs/archive/`](archive) | earlier documents: the first map of the uniqueness proof and ChatGPT Pro's notes |
| [`scripts/`](../scripts) | the axiom audit, the generators of two Lean files, the figures, and the documentation tools |

### `MovingSofaOptimality/`: Baek's paper

| Module | Paper content |
| --- | --- |
| [`MovingSofaOptimality/Basic/Plane.lean`](../MovingSofaOptimality/Basic/Plane.lean) | the plane: unit vectors, dot and cross products, rotations, lines, half-planes, area |
| [`MovingSofaOptimality/Basic/ConvexBody.lean`](../MovingSofaOptimality/Basic/ConvexBody.lean) | §2.1: convex bodies, support functions, edges and vertices, Hausdorff distance, Theorem 2.1.3 |
| [`MovingSofaOptimality/Basic/LebesgueStieltjes.lean`](../MovingSofaOptimality/Basic/LebesgueStieltjes.lean) | §5.1: Lebesgue–Stieltjes measures and integrals |
| [`MovingSofaOptimality/Basic/SurfaceArea.lean`](../MovingSofaOptimality/Basic/SurfaceArea.lean) | the surface area measure σ_K, Proposition 2.1.2, §5.2 |
| [`MovingSofaOptimality/Sofa/Defs.lean`](../MovingSofaOptimality/Sofa/Defs.lean) | Chapter 1 and §2.2–2.3: hallways, moving sofas, supporting hallways, monotone sofas |
| [`MovingSofaOptimality/Intro/RotationAngleBound.lean`](../MovingSofaOptimality/Intro/RotationAngleBound.lean) | Theorem 1.5.1 |
| [`MovingSofaOptimality/Monotone/`](../MovingSofaOptimality/Monotone) | §2.2–2.5: supporting hallways, monotonization, caps and niches |
| [`MovingSofaOptimality/Balanced/`](../MovingSofaOptimality/Balanced) | Chapter 3: nef polygons, polygon caps, maximum polygon caps, balanced maximum sofas |
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
| [`MovingSofaUniqueness/Rigid.lean`](../MovingSofaUniqueness/Rigid.lean) | rigid maps, and the recovery of a closed set from a regular closed superset of the same area |
| [`MovingSofaUniqueness/Selection.lean`](../MovingSofaUniqueness/Selection.lean) | Proposition 1: polygon caps converging to a given maximizing cap |
| [`MovingSofaUniqueness/Variation.lean`](../MovingSofaUniqueness/Variation.lean) | Proposition 2 and the bounds (19): variations of the selected polygons and their limits |
| [`MovingSofaUniqueness/Curvature.lean`](../MovingSofaUniqueness/Curvature.lean) | Proposition 3: curvature bounds and the injectivity condition for every maximizing right-angle cap |
| [`MovingSofaUniqueness/AngleExtension.lean`](../MovingSofaUniqueness/AngleExtension.lean) | Proposition 4: the right-angle motion of the same sofa |
| [`MovingSofaUniqueness/Rigidity.lean`](../MovingSofaUniqueness/Rigidity.lean) | Proposition 5: equality in Mamikon's terms, and Gerver's cap up to a horizontal translation |
| [`MovingSofaUniqueness/RegularClosed.lean`](../MovingSofaUniqueness/RegularClosed.lean) | Proposition 6: Gerver's sofa is the closure of its interior |
| [`MovingSofaUniqueness/Main.lean`](../MovingSofaUniqueness/Main.lean) | the theorem |

### `MovingSofaBridge/`: the bridge to formal-conjectures

[Chapter 13](proof/13-bridge.md) and [Appendix A](proof/appendix-a.md) of the text:

| Module | Content |
| --- | --- |
| [`MovingSofaBridge/GerverConstants.lean`](../MovingSofaBridge/GerverConstants.lean) | Gerver's four constants are unique, by elementary inequalities |
| [`MovingSofaBridge/RomikParams.lean`](../MovingSofaBridge/RomikParams.lean) | Gerver's four constants and Romik's parameters; the constants exist |
| [`MovingSofaBridge/Motion.lean`](../MovingSofaBridge/Motion.lean) | the two notions of moving sofa agree, and so do the two optimal areas |
| [`MovingSofaBridge/GerverSofa.lean`](../MovingSofaBridge/GerverSofa.lean) | the two Gerver's sofas are the same set |

### `scripts/`

| Path | Content |
| --- | --- |
| [`scripts/Audit.lean`](../scripts/Audit.lean) | the axiom and dependency audit |
| [`scripts/romik/`](../scripts/romik), [`scripts/area/`](../scripts/area) | the generators of the two Lean files of interval arithmetic |
| [`scripts/figures/`](../scripts/figures) | the figures of the text: the geometry of Gerver's sofa (`gerver.py`), the drawing helpers (`sofa_figures.py`), one module per chapter, and `make_all.py` |
| [`scripts/sync_challenge_defs.py`](../scripts/sync_challenge_defs.py) | copies the shared definitions into the Challenge, or checks the copy |
| [`scripts/linkify_docs.py`](../scripts/linkify_docs.py), [`scripts/check_md_tables.py`](../scripts/check_md_tables.py) | link the documents to the code; check their tables |
