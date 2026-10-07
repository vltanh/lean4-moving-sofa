# Explicit local radii and the final cutoff: continuation ledger

Base: `0ae744d727e77876cf148d19d0d0012d56e1bd8b` (PR #10).
The requested target is one numerical epsilon_* activating the actual-sofa
bounds 2.3, 50, and 3.1. Formalization is frozen. This continuation changes
analytic notes and Python checks only; no Lean, Lake, CI, or manuscript build.

## Acceptance conditions

A proposed small number is not a proof. The final cutoff must imply each local
hypothesis with an explicit chain of inequalities: canonical-body feasibility,
core/cut geometry and niche containment; terminal floor persistence and omitted
wedges; Euclidean normal witnesses; and the sector recovery scale. The global
entry modulus of note 27 is an analytic input whose normalization and geometric
claims must also be checked, not treated as verified merely because a previous
status message called the rest bookkeeping.

The final 2.3 bound is under horizontal-midpoint/top normalization. Left support
pinning gives a different statement. Cap distance, actual-sofa distance, and
Q deficit must not be interchanged without their established bridges.

## Working strategy

Quantify exposed faces by finite support differences and the reference's
one-sided derivative/curvature bounds. Keep fixed-face endpoints separate from
smooth supports. Obtain numerical local tolerances before substituting the
coarse epsilon^(1/12) entry modulus. Check scalar implications with exact rational
arithmetic and use interval tests only for the reference quantities they actually
cover. Any counterexample to an inherited local claim is committed before using
or repairing that claim.

## Environment

The active runtime cannot resolve raw.githubusercontent.com. Repository reads
and writes use the connected GitHub API. No build/test workflow is invoked.
The prior experiment archives are mounted, but their contents do not by
themselves validate the current analytic constants or certificates.
