> **Additional mathematical audit repairs (October 7, 2026).** The effective
> right-angle source contained a false unanchored \(L^2\)-to-supremum
> inequality: a nonzero constant function has Lipschitz constant zero but
> positive supremum. The source now uses the actual common top support
> \(h_K(\pi/2)=h_C(\pi/2)=1\), so the support difference vanishes at
> \(\pi/2\); its one-sided integration interval is restricted to
> radius at most \(\pi/2\). The penalized comparison cap's radius is now
> measured relative to the **input cap's horizontal midpoint**, not the
> origin (absolute radius cannot be translation invariant). A relative
> midpoint estimate and common-centre Lipschitz adapter were drafted from
> the support penalty. Nearest-point lemmas now require a nonempty compact
> set and use the minimizing property when equating an attained distance
> to the infimum. Static regression patterns were added.
>
> These are corrections of genuine mathematical/source errors, **not**
> proof of the still-blocked quantitative targets. No Lean, Lake, CI,
> TeX, or finite Boolean certificate was run.

> **Source-audit correction (October 7, 2026).** The earlier claim that the quantitative extension is "source-complete" is **withdrawn**. All 15 headline theorem declarations have bodies, but this is not equivalent to a self-contained draft. The source-only audit found unresolved Gerver sector/normal geometry, penalized-cap and terminal/effective-entry bridges, coarse-angle search soundness, and a feasible-trial energy-cover proof. The trial-energy cell integral and arc double-counting defects were corrected in follow-up commits, but the numerical Boolean reductions remain unexecuted. See `scripts/audit_quantitative_source_static.py` and `docs/paper/quantitative_manifest.json` for current blockers. No Lean, Lake, CI, or TeX build was run.

---

## Historical draft-completion report (superseded)

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
