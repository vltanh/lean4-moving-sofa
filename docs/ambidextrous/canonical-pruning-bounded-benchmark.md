# Bounded measured A/B run of canonical-support certificate search

**Status: measured search-performance improvement, not a verified new area certificate.** This continuation answered the request to run the O'Keefe four-hallway search with and without our CP canonical-support domain reduction. The original C source was inspected through the connected GitHub repository but could not be cloned into the local runtime (network DNS unavailable). To compare like with like, we wrote an **independent Python floating-point reproduction** of the exact same 3–4–5 four-hallway union-over-offset-box geometry, polygon splitting, maximal-component tests, and widest-coordinate bisection. Every mode uses the same evaluator; only its search domain and cheap necessary-support rejections differ.

The delivered reproducibility bundle is \`canonical_pruning_benchmark.zip\`, containing \`benchmark.py\`, \`benchmark_runs.json\`, \`README.md\` and SHA256SUMS. Script SHA-256: \`ff4f95534679fbaac7040591c3bfbe0b1fab905631f6cee8d9ee49fb8c0123d0\`. Python depends on Shapely already installed. Each actual script run was externally capped at five seconds; the internal budgets were 2.4–4.1 seconds. No dependency installation, Lean/Lake compilation, CI, manuscript build, or long search was run.

## 1. A necessary correctness check before measuring

The first draft misread affine coordinate triples \`(constant, x_coefficient, y_coefficient)\` and returned area zero on O'Keefe's known rational four-angle configuration. That draft's numbers were rejected. After correcting the order, **the same evaluator** reproduced that published connected finite-hallway witness:
\[
|E|=29\,092\,957\,301/16\,800\,000\,000
=1.731723648869047\ldots
\]
to within \(2.3\times10^{-16}\) in floating arithmetic, with seven nonempty polygons. This verifies a known input and does **not** certify every computed box or the released \(353/200\) certificate.

## 2. Completed A/B searches, using identical floating-point geometry

Three modes:
- **original:** the external paper's original free eight-offset rational root box;
- **trimmed:** the smaller canonical-support root box proved exhaustive for the *global connected-component supremum* by CP1;
- **support:** the trimmed box plus cheap necessary support subadditivity, normal-pair and antipodal-width rejection tests from CP.9–CP.11.

| Threshold | Version | Search nodes | Search time (seconds) | Finished? |
|---|---|---:|---:|---|
| \(2.6\) | original | 15,905 | 2.3103 | yes |
| \(2.6\) | trimmed | 255 | 0.04635 | yes |
| \(2.6\) | support | 255, of which 13 pruned | 0.04730 | yes |
| \(2.5\) | original | 21,009 | 3.1417 | yes |
| \(2.5\) | trimmed | 407 | 0.07471 | yes |
| \(2.5\) | support | 395, of which 14 pruned | 0.09009 | yes |

Thus the **post-import search loop** was roughly \(50\times\) faster at 2.6, and \(42\times\) faster at 2.5, using the trimmed root alone. At threshold 2.6, complete-process shell timings **including Python/Shapely imports** were 2.98 seconds original, 0.72 seconds trimmed, 0.69 seconds support: only about \(4.1\)–\(4.3\times\) end-to-end because of fixed import overhead. Additional support constraints save geometric evaluations but are not consistently faster than the already small trimmed root.

At target \(1.765\), all three modes were **still incomplete after their separate 2.4-second caps**: original processed 7,446 nodes; trimmed processed 9,078; support processed 8,896 (including 242 necessary-support rejections). At target 1.9, none finished in that cap either. Comparing unfinished node counts **does not** establish a relative completion time, so the measured \(42\)–\(50\times\) easy-threshold ratio must not be extrapolated to the 436-million-leaf production certificate.

## 3. Exact status and next honest experiment

These are **floating-point discovery trees**, not exact-rational-verified certificates. A production checker would need (i) a trusted proof that the entire connected search can first be replaced by canonical-support offsets, (ii) exact rational proofs of every pruned leaf's necessary-condition contradiction, (iii) the original exact polygon/component verification on every other leaf, and (iv) complete tree coverage. A complete float tree at threshold \(2.5\) or \(2.6\) is itself a **weak** global bound, not a new improvement over \(\mu_{\rm ambi}\le1.765\).

The external repository's actual \(353/200\) full certificate was **not** rerun. We have now **measured** that CP1 reduces easy full search trees by about two orders of magnitude in nodes, substantially less than the root-box's four-orders-of-magnitude volume shrinkage. The difficult residual near the optimum dominates future uncertainty.

**Decision:** retaining CP1 is justified as a meaningful certificate-search optimization. Claim neither an exact checker improvement nor an improved sofa-area constant until those additional steps are performed. This note and the delivered bundle preserve the benchmark, rather than quoting the \(10{,}802\times\) root-volume factor as runtime.