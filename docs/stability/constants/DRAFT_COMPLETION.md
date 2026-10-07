# Completion pass for the uncompiled quantitative draft

Starting checkpoint: `41c9d3c9ffbee892e8e0afefc097405011b3b6d3`.

The user explicitly requests completing the uncompiled draft, with no Lean or
CI execution. Do not install a compiler, dispatch a workflow, or interpret the
absence of compilation as evidence that the mathematics or proof terms work.
Python-only arithmetic, syntax, inventory, and manuscript source checks are
permitted; their scope must be reported separately.

## Publication boundary

The new source and the appendix draft may be developed together, but the paper
must distinguish them from the integrated kernel-checked baseline. An exact
proposition contract, a conditional transfer theorem, or an interval checker
without the required instantiated certificate is not an unconditional proof.
No `sorry`, new axiom, or false claim of completed verification may be used to
close that gap. Keep the 10^-600 proposition in the draft and in the target
inventory; do not weaken it to an already-local assertion.

## Source present at the starting checkpoint

The centered cap route now has an actual comparison profile, right derivative,
residual identities, pairing and polarization arguments, and final declarations
`centered_energy`, `centered_cap`, and `centered_ki`. The quantitative manifest
still records these as planned and must be brought up to date. Their state is
proof source, not checked.

The branch also has the concrete four-arc L2 evaluation kernels and generic
rank-two Gram algebra. The remaining steps must connect those objects to the
full-Q feasibility constraints and the continuous operator certificate, rather
than assume the desired estimate in a theorem hypothesis.

## Workstreams

1. Complete source-to-target bookkeeping and inspect the existing analytic proof
   obligations for quantitative sharpness, full-Q bounds, and effective entry.
2. Complete the numerical/analytic transfer lemmas and explicit scale arithmetic,
   keeping all missing geometric inputs visible until they are actually proved.
3. Reorganize the TeX into main statements/proof sketches, technical Appendix F,
   and quantitative Appendix G, with a conspicuous draft verification boundary.
4. Run only non-Lean source and arithmetic checks; update the PR with the exact
   implementation state, not a blanket claim based on file counts.

This ledger will be updated with the actual results of the pass.
