# Punctured sofas and cap-constant refinement

This continuation starts from PR #8 at
`fa4a20e2dde9f80c3a2034bd44e403d0bb06af4e`.
The requested order is: finish the two additions here, leave manuscript
integration to the separate session, then implement the coercive-route plan
in PR #9. Do not fold the PR #9 refactor into this branch.

## Targets

1. A punctured Gerver family of actual closed connected moving sofas. Prove
   the area loss and a Hausdorff lower bound after allowing arbitrary rigid
   alignment, not merely for the identity alignment. Use it to rule out every
   unrestricted Hausdorff exponent greater than one half.
2. Sharpen the coefficient in the actual cap-distance chain. The existing
   Lean source uses 80; note 01 derives `2 / cos(phi)`, less than 2.002 in the
   source box. A bound on a displayed kernel formula is not enough: connect
   its norm to the residual integrals and the cap support.

## Initial inspection

The puncture argument in note 09 needs a genuine rigid-orbit interior lemma:
Hausdorff-close arbitrary sets can have holes, whereas sufficiently close
rigid copies of a fixed compact set retain any fixed interior point.

For the sharp middle-arc reconstruction, Fubini can be avoided. With
`F(w)=f(pi/2+w)`, `A=sec(phi)`, and `B(w)=(A-sin(w))/cos(w)`,

    (B F)' = -F - B r4(pi/2+w).

Integrating this identity joins the middle and last residuals with their
correct common kernel. It avoids the earlier triangle-inequality loss and
also avoids an unnecessarily large double-integral formalization.

## Validation boundary

No Lean, Lake, CI, remote build, or TeX compilation is permitted. New Lean
files are uncompiled proof source, not verified theorems. Non-Lean formula,
manifest, and source checks may be run, and their limited meaning must be
recorded. Research commits include `[skip ci]`. Existing proofs, the bridge,
Challenge statements, and manuscript verification claims are preserved.
