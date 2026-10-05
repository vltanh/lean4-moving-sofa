# Lean formalization of quantitative stability

This continuation starts at `4770c508a05295b26215435b5fc85b0a5121fb45`.
The mathematical target is note 08's unrestricted theorem, not just the earlier
conditional injective-cap theorem. The written arguments in notes 01--09 are
not themselves Lean proofs.

## Validation policy

No Lean invocation, Lake invocation, CI dispatch, CI rerun, or remote build is
permitted in this continuation. Source inspection and non-Lean text checks are
allowed. Every commit carries `[skip ci]`. A file with a proof term is still
**uncompiled proof source**, not a kernel-verified result.

The new development will live in `MovingSofaStability/`. Existing optimality,
uniqueness, bridge, audit, and manuscript verification claims are not extended
merely by adding that directory. It must remain clear which results are proved
from existing declarations and which geometric/analytic prerequisites remain
unimplemented. There will be no new axioms, `sorry`, or disguised assumption of
the final theorem.

## Dependency ledger

- [ ] Precise target using the repository's sofa, area, and Euclidean geometry.
- [ ] Exact quantitative deficit of the existing three-body functional.
- [ ] Integral/evaluation inequalities and cap coercivity.
- [ ] Nonsmooth algebraic extension (note 05).
- [ ] Local canonical-body and geometric area bounds (note 06).
- [ ] Terminal-angle loss, including the missing-set bookkeeping (note 07).
- [ ] Quantitative recovery of the actual nonconvex sets (notes 03 and 08).
- [ ] Qualitative entry into a fixed neighborhood (note 02).
- [ ] Unconditional assembly of the unrestricted stability theorem.
- [ ] Exponent sharpness with the rigid-alignment quantifier (note 09).

Updates will distinguish completed proof source, source-level checks, and
remaining dependencies. None of the boxes denotes a compilation result.

## Source-inspection findings

The repository models points by `Real × Real` but separately defines `norm2`
for the Euclidean norm. The default product metric is not Euclidean. The
stability statement must not silently substitute its Hausdorff metric for the
Euclidean Hausdorff distance of the paper, especially in the explicit cap
constant.

A local `git clone` was attempted only to obtain source files and failed
because the runtime cannot resolve github.com. Repository reads and commits
are instead performed through the connected GitHub API. This is unrelated to
Lean verification; no Lean process has been started.
