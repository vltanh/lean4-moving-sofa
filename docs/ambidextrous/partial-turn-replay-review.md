# Replay review: missing-angle loss versus quadrature refinement

**Status.** These are reproducible diagnostics supporting review of the uploaded PC package, not a certificate of a near-reference partial-turn family or of either optimality theorem. The mathematical results are the hand proofs in `circular-corner-completion-bound.md` and `exact-in-place-completion-obstruction.md`.

## 1. Original replay

The original script was executed unchanged under a ten-second subprocess limit, finishing in 2.35 seconds internally. All 126 rational Part A tests passed. Its four floating-point rows matched the uploaded record exactly in this runtime, apart from runtime/version metadata.

The original first row has completion loss -6.498075844074691e-7. This cannot be an exact geometric loss: completing a motion adds constraints. The two separately spaced angle grids are not nested, so finite maxima can have either comparison sign.

The original author record and all four original files remain unchanged in the supplied-archive reproduction bundle. Their hashes are listed in `partial-turn-package-audit.md`. The replay wrapper checks both the archive and original source hashes before execution; it does not silently accept a different input.

## 2. Correct comparison of the sampled motions

For a completion diagnostic, the full lower-turn grid must consist of exactly the old visited grid plus samples from the missing interval. Merely taking the union of two full equispaced grids is not enough: that also refines already visited orientations and confounds ordinary quadrature improvement with loss caused by new orientations.

One such union-grid trial was made and preserved. It produced apparent losses above the circular-corner allowance at epsilon=0.02 and 0.05. The excess was not a counterexample: that trial was adding constraints inside the visited interval as well. It is not used as a measurement of missing-angle loss.

The retained comparison uses

`full_lower_grid = visited_lower_grid union linspace(alpha, pi/2, 1001)[:-1]`.

Thus every new lower orientation is genuinely missing from the original motion. The opposite upper motion uses the same grid in both area calculations. This guarantees monotonicity of the sampled lower niche. Additional pointwise assertions check that the numerical completion loss equals Xi-Z and that C-area(E_full) equals R-Z, preserving the distinction between signed fibers and their positive parts.

A fresh run through the committed wrapper completed in 2.90 seconds internally under a ten-second limit. Results:

| Missing angle epsilon | Original grid difference | Missing-angle-only difference | Circular allowance lambda(epsilon) |
|---:|---:|---:|---:|
| 0.02 | -6.498075844e-7 | 2.761820990e-7 | 3.333466672e-7 |
| 0.05 | 2.996480778e-6 | 4.316214264e-6 | 5.209635746e-6 |
| 0.10 | 3.197432061e-5 | 3.454259364e-5 | 4.170837554e-5 |
| 0.20 | 2.730906048e-4 | 2.768649895e-4 | 3.346720855e-4 |

Every displayed retained difference is nonnegative and below the new allowance. These are floating-point values, not rigorous upper or lower area bounds. The finite visited grid still misses orientations; finite spatial integration still has unknown error. Hull vertex retention to a tolerance and sampled fiber positivity are not continuum feasibility proofs.

The sampled negative-fiber correction Z was zero in these four runs. This does not justify setting Z=0 for arbitrary partial-turn hulls. In general the true AS switching remainder is R, while the difference C-area(E_full) is R-Z.

## 3. Exact checks of the new hand-proof algebra

`computer-assisted/check_circular_completion.py` ran under a five-second limit in about 0.155 seconds. Its source SHA-256 is `641674c36732787f6e8346356cb31b86e509d6ed1e5454cb444f9ecd981898f0`, and its executed bytes match committed Git blob `a9069ce6e3fedfa4301ef1434e6012b37ac1f1b0`.

It verifies the triangle polynomial identity coefficient by coefficient, plus 7,290 rational triangle point/frame cases, 147 tangent-wall tests, 462 bisector-cone cases, and 934 signed-fiber cases. The latter include 621 negative full signed fibers, making the positive-part distinction explicit. Three negative controls reject a missing triangle angle, identify signed-versus-actual area differences, and check the low-area large-deficit counterexample to unqualified PC6.

The exact tests do not verify continuum motion, area integration or optimality. The all-angle triangle proof and exact circular area calculation are the mathematical arguments.

A separate fixed triangle discovery screen covered 27 prescribed parameter pairs in about 0.010 seconds; its candidate with k=1/10 and R=1 was subsequently proved analytically in IC. No feasibility assertion is based solely on that screen.

## 4. Reproduction

The committed wrapper is `computer-assisted/replay_partial_turn_package.py`. Its executed bytes match Git blob `bbf5a43340388f5bec248bf94e39ce32845426d8`, SHA-256 `a4d40f46bde322e393ddcc85e9f80f25947712c4c00e4706042c58029a3d57e0`.

Run separately, with the original supplied archive as explicit input:

```sh
python docs/ambidextrous/computer-assisted/replay_partial_turn_package.py \
  --package partial-turn-completion-package.zip --output replay-original --mode original
python docs/ambidextrous/computer-assisted/replay_partial_turn_package.py \
  --package partial-turn-completion-package.zip --output replay-missing --mode missing-only
timeout 5s python docs/ambidextrous/computer-assisted/check_circular_completion.py
```

Each wrapper invocation enforces a ten-second cap on the numerical subprocess. Numpy and scipy are required only by the original diagnostic. No dependencies were installed in this continuation. The exact checker needs only the standard library.

The wrapper preserves its generated source and raw output and records both source hashes. The retained modified numerical source has SHA-256 `9a65765c7829a16e37f9df6f49290e659e0afc5d12208a46bb07cb94ddbf3c52`. Numerical sources, the unsuccessful union-grid diagnostic, and their raw records are in the reproduction bundle; original author output is separate.

## 5. Mathematical conclusion

The package's useful bridge survives review, and its geometric allowance can be reduced from the enclosing triangle to the circular corner. The corrected diagnostic is consistent with that bound. The supplied near-reference family and its asymptotic conclusions are still numerical rather than proved. IC gives a rigorous small-deficit obstruction to in-place completion, but its area is not competitive.

The exact missing step remains a sharp bound with the required completion margin on actual partial-turn hulls, or a valid component-preserving alternative. An unqualified connected full-turn optimum alone does not supply either. No full-turn or unrestricted optimality closure is claimed; the current proofs remain self-reviewed rather than independently refereed.

No CI, Lean/Lake compilation, dependency installation, manuscript build, long search or repeated optimizer campaign was used.
