# Completion pass for the uncompiled quantitative draft

This ledger records the user's requested endpoint: **finish the uncompiled
source draft without running Lean or CI**.

## Completion criterion

For this pass, "finished" means:

- every quantitative headline proposition in `Targets.lean` has a named
  theorem body in the quantitative library;
- the source includes the intended analytic and finite-certificate dependencies
  rather than hiding them as assumptions in the final target;
- the working paper has the planned main-text / Appendix F / Appendix G
  organization and accurately labels the new material as uncompiled;
- the `10^-600` theorem remains an arbitrary-original-sofa theorem with no
  existential local radius;
- manifests and ledgers match the actual source state.

It explicitly does **not** mean successful Lean elaboration, kernel checking,
or TeX compilation.

## Result

The source-completion criterion is met.

All fifteen entries of `docs/paper/quantitative_manifest.json` are now
`source`, with corresponding declarations listed in
`docs/paper/quantitative_theorem_manifest.tsv`.

The two last mathematical source assemblies were:

1. `MovingSofaQuantitative.effective_entry`:
   [
   epsilonle10^{-144}
   Longrightarrow
   d_H(S_c,G)le3{,}000{,}000,epsilon^{1/12}.
   ]

2. `MovingSofaQuantitative.explicit_cutoff`:
   [
   epsilonle10^{-600}
   Longrightarrow
   d_H(S_c,G)le2.3sqrtepsilon,quad
   |S_c	riangle G|le50sqrtepsilon,quad
   pi/2-omegale3.1epsilon
   ]
   for every admissible reduced motion.

The effectivity chain includes source for:

- integral-penalized right-angle regularization;
- exact coarse-angle separation;
- partial-angle penalized comparison and right-angle extension;
- the `500 epsilon^(1/6)` angle estimate;
- partial-to-full cap completion with `72 alpha` / `144 alpha` budgets;
- explicit actual-set recovery;
- fixed local support, terminal, normal, and sector scales;
- final activation at `10^-600`.

## Paper state

`docs/paper/quantitative-draft.tex` now has:

- short main stability statement/proof architecture;
- short unified-certificate narrative;
- technical Appendix F by reuse of the integrated detailed proof;
- quantitative Appendix G with centered cap coercivity, explicit
  `2.3/50/3.1`, sharpness, full-Q `0.922--0.93`, effective entry, and
  `10^-600`.

All status boxes now say that the quantitative extension is source-complete
but uncompiled.

## Verification boundary

No Lean, Lake, CI, axiom audit, Comparator, or TeX build was run.

The closed Boolean reductions in `FullQCertificate.lean`,
`TrialEnergyCertificate.lean`, and `CoarseAngleCertificate.lean` were written
but deliberately not executed.

Therefore the next phase is compile-time verification and repair.  In
particular, this source-completion pass does not establish that every identifier,
tactic invocation, or theorem signature elaborates in the pinned environment.

No `sorry`, new axiom, or weakening of the requested quantitative theorem
surface was intentionally introduced to obtain this endpoint.
