# Third research round: publication-level theorem targets

Starting checkpoint: `0a4000998d260c99c20a02eb13dead9b1810127c` (36 commits in PR #7).

The goal is a proved structural result, not simply larger floating-point candidates. Work is not restricted to the cap/uniqueness machinery. No CI, workflow dispatch, workflow rerun, or Lean build is used.

## Audit of the target

- The two aligned-endpoint motion classes have not been proved exhaustive. Statements about their suprema must not be labeled unrestricted sofa optimality.
- Excluding the forward class at 150 degrees is a pointwise statement, not by itself a theorem on the entire interval above 150 degrees.
- Opposite dominance at two parameter values does not establish a unique transition, nor even a crossing without an appropriate continuity argument.
- Existing numerical work already reports the competing branches: Xingyi He, *A Gas-Driven Algorithm for Variants of the Moving Sofa Problem*, arXiv:2608.11206v1, Sections 2.2, 2.5 and 3. Its full-rotation assumptions and local-optimization status are explicit. The approximate corridor-angle crossing 43.327 degrees corresponds to bend 136.673 degrees here. No novelty is claimed for that numerical phenomenon.
- The previously suggested endpoint asymptotics for the unrestricted optimum are targets, not results. Current midpoint upper bounds apply only to the aligned-endpoint classes.

## Research priorities

1. Seek exact or asymptotically sharp upper/lower bounds for an entire motion class, with explicit constructions and proofs valid on an interval of angles.
2. Seek stronger finite-pose bounds with a transparent universal quantifier over all translations; numerical local maximization of a finite intersection is not such a bound.
3. Investigate continuity/comparison principles without assuming compactness, regularity, or a full-rotation reduction that has not been established.
4. Commit both successful derivations and obstructed routes. Keep analytic proofs, exploratory numerical tests, and certified arithmetic separate.

## Sources checked

- He: https://arxiv.org/html/2608.11206v1
- Existing bounds and certificate assumptions in `CLASS_BOUNDS.md`, `CLASS_EXCLUSIONS.md`, and `INTERVAL_CERTIFICATES.md`.

## Initial limitations

A direct repository clone was unavailable in this runtime (DNS failure). GitHub read/write actions remain available; local experiments will use retrieved source or self-contained new code. This is not a CI failure and no CI was attempted.
