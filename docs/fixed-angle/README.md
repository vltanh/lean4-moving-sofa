# Fixed net rotation angle: all-angle proof draft

This directory now contains an assembled **paper-and-interval-certificate proof covering every `0 <= omega <= pi/2`** in the usual unit-width right-angled hallway. It treats a prescribed **net rotation**, with backtracking permitted, not a change to the hallway corner angle.

**Status:** complete angle coverage in a computer-assisted research proof draft. The analytic arguments and ordinary-Python checker have not been independently refereed or verified in Lean. The final continuation is not presented as a purely symbolic hand proof.

## Main result

The optimizer is attained and unique up to congruence at every angle in the stated closed interval. For `0 < omega < pi/2`, the two upper endpoint support conditions fix a unique translation, and the normalized optimizer is unique as a set.

For `0 <= omega <= 1`, the exact optimum is

`m(omega) = 1 + omega^2/2`.

Above one radian, that formula is strictly too large and Baek's old relaxed-cap sofa is strictly suboptimal. The actual optimizer is specified exactly by a **unique admissible three-contact system**, elementary piecewise-linear shooting equations, and the boundary-integral area formula in the main paper. The reflected contact intervals may cross or overlap; the proof does not extrapolate one fixed ordering through those changes.

At `omega=pi/2`, the companion Gerver theorem supplies optimality and uniqueness up to congruence. The endpoint support directions coincide there, so horizontal translation is not fixed by the open-angle normalization.

## Read first

| File | Purpose |
| --- | --- |
| [all-angle-optimality-uniqueness.tex](all-angle-optimality-uniqueness.tex) | Main theorem, exact optimizer definition, area formula, complete angle coverage, parameter uniqueness and stability. |
| [PEM.md](PEM.md) | Current proof-exploration memo and dependency ledger. |
| [REVIEW.md](REVIEW.md) | Analytic and implementation audit, negative results, corrections and verification limits. |
| [validated-contact-cover.tex](validated-contact-cover.tex) | Mathematical justification of the interval root and whole-interval geometry checks. |
| [checks/README.md](checks/README.md) | Rebuild/replay instructions and the boundary between numerical proposals and verified inequalities. |
| [checks/CERTIFICATE_REPORT.json](checks/CERTIFICATE_REPORT.json) | Actual replay results, record hashes and frozen verifier hashes. |

## No angle gap remains in the assembled argument

| Range | Coverage proof |
| --- | --- |
| `[0,1]` | Analytic optimality and uniqueness in [optimality-uniqueness.tex](optimality-uniqueness.tex). |
| `(1,1.01]` | Explicit analytic contact construction and rational admissibility bounds in [explicit-first-regime.tex](explicit-first-regime.tex). |
| `[1.01,1.5706]` | 750 parameter-uniform interval root and geometry certificates, including reflected-contact crossings. |
| `[1.5706,pi/2)` | 16 endpoint-parameter boxes plus 15 joining boxes, and the analytic coverage argument in [endpoint-bridge.tex](endpoint-bridge.tex). |
| `{pi/2}` | Separate companion Gerver endpoint theorem. |

The 781 contact records were generated and replayed. Their intervals, not merely their midpoints, are covered. Exact `Fraction` comparisons verify the compact parameter coverage, and the endpoint joins are checked by actual root-box containment. A final mixed-type derivative-dispatch correction was followed by another replay of all records.

## What makes the computation a global sofa proof

The analytic work applies to **every global maximizing cap**, not just the proposed symmetric family. Cap attainment, penalized selection, fixed-angle curvature, the arm certificate, pinned endpoint bounds and global cut geometry give the hypotheses of the lifted upper bound. [vertical-core-lifting.tex](vertical-core-lifting.tex) removes an unnecessary interior-threshold assumption by using vertical core slices.

The lifted functional is strictly concave on a convex obstacle domain. [order-independent-contact-certificate.tex](order-independent-contact-certificate.tex) proves that an admissible contact root is a feasible sofa whose area equals the global lifted bound, and that its niche has exactly the asserted exposed arcs. Equality identifies every maximizing cap; regular closedness recovers arbitrary original sofas from their equal-area envelopes.

The interval computation supplies only root existence and the finite support tests in [finite-admissibility-tests.tex](finite-admissibility-tests.tex). It is not a numerical optimization over a restricted class. [order-independent-shooting.tex](order-independent-shooting.tex) proves the linear shooting problem nonsingular independently of the reflected contact ordering.

## Negative and intermediate results remain available

[negative-results.tex](negative-results.tex) gives an exact feasible convex counterexample to applying `A_1` to every feasible cap. [beyond-one-radian.tex](beyond-one-radian.tex) proves the relaxed quadratic value ceases to be sharp precisely above one radian. [redundant-angle-improvement.tex](redundant-angle-improvement.tex) proves the old relaxed-cap sofa itself is strictly suboptimal there by a feasible perturbation with unchanged niche.

The earlier elementary, small-angle, transition-model, fifth-order asymptotic and local contact-branch notes are retained as component proofs and research history. Their statements about what a particular note does not prove describe that note's scope. This README, the PEM and the all-angle assembly state the current overall result.

## Reproduce the finite verification

From `checks/`:

```sh
python check_verifier_primitives.py
python build_contact_cover.py --part all --output-dir certificates
python verify_contact_cover.py certificates/*.json --report replay.json
```

Only the Python standard library is required. Floating-point Newton iterations propose boxes; outward-rounded interval checks decide acceptance. The verifier recomputes the records without trusting stored success flags. The complete reference records are supplied in the verification attachment and can also be regenerated from the committed source. The source and data digests are recorded in the report.

## Attribution and validation boundary

Baek's *A Conditional Upper Bound for the Moving Sofa Problem*, arXiv:2406.10725v1, already contains `A_1`, the original relaxed cap and its relaxed value. The support/contact approach follows Romik and Baek. Imported companion inputs are the fixed-angle cap/monotonization identities, penalized selection and first variations at commit `1ade045936f32cf76572ee668ed8aa1627772bde`; the Gerver theorem is used separately at the right-angle endpoint.

Independent mathematical review, implementation review and any later formalization remain distinct from the completed interval coverage. This does not solve a different hallway-angle problem or the ambidextrous problem.

No CI, workflow dispatch, Lean compilation, axiom audit or TeX compilation was run. Every research commit uses `[skip ci]`. All changes are confined to this research directory; the original uniqueness manuscript, Lean sources and workflow files are unchanged.
