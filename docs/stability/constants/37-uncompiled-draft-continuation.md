# Uncompiled-draft continuation

Starting checkpoint: `4dd50d4933e1afb82ab1491ab05af8c90f0428e2`.

The user's instruction is now to complete the uncompiled draft. No Lean, Lake,
CI, remote build, or compiler installation is to be attempted. Pure Python
source checks and mathematical experiments remain separate from proof checking.
The optional `MovingSofaQuantitative` library remains outside default targets.

A result is source-complete only when its actual statement has a proof term
whose dependencies are also implemented. Defining its proposition, adding a
hypothesis that asserts the desired result, or bounding an unrelated scalar
profile does not count. Uncompiled source may have elaboration or proof errors;
none of it is described as kernel-checked.

## A smaller centered-cap proof

Instead of rebuilding every pair of Green kernels, use the already integrated
pinned evaluation inequality on `f - a*C`, where `C` is the explicit covariance
profile against the zero-endpoint kernel. Its residual pairing with any actual
four-arc function `f` is exactly `f(0)`, by the existing reconstruction at zero.
In particular its energy is `sec(phi)^2`. A scalar discriminant argument then
transports the pinned evaluation estimate to the centered one. This requires
proving the comparison profile's actual residuals and regularity, not assuming
the covariance integral as an input to the final theorem.

## Preservation

Keep the faithful Baek proof, both established uniqueness routes, semantic bridge,
Challenge statements, canonical solutions, and the integrated paper's verified
claims unchanged. Uncompiled quantitative material must carry an explicit draft
status. The final `10^-600` target remains the simultaneous arbitrary-sofa result
recorded in `Targets.ExplicitCutoff`; it is not replaced by a local conditional
statement.
