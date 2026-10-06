# Execution of the paper/formalization roadmap

The user has authorized implementation of roadmap 34, including formalization of
the final 10^-600 proposition. The earlier formalization freeze is therefore
superseded for source work. No workflow dispatch, rerun, or CI change is authorized
or performed; all commits continue to use `[skip ci]`.

## Baseline integration

Merge `3635e01821a9c45bb3f5dd8ceedb29b5d098fad9` incorporates the integrated paper
at `859ba93f8bb73ccc4378118a7b47415827710c2f`. It preserves that baseline's
optimality, uniqueness, stability, coercive route, bridge, Challenge, and paper
files. All constants notes/scripts remain in `docs/stability/constants/`.
The eleven earlier uncompiled constants prototypes are archived byte-for-byte in
`docs/archive/constants/lean-source/`, because their imports refer to modules
removed by the integrated refactor. They are not verified theorem dependencies.

## Publication gates

The main paper keeps the checked baseline theorem statements until their proposed
stronger replacements are actually proved and checked. Appendix G must not be
populated with unproved headline statements merely because the corresponding
analytic notes or scalar receipts exist. The 10^-600 cutoff remains mandatory
in the final intended theorem inventory, not optional and not silently dropped.

New quantitative work is isolated from the existing default library globs until
it passes its own build/axiom/statement checks. Module names in roadmap 34 were
provisional; a separate quantitative namespace can avoid accidental collisions
and prevent uncompiled work from changing the baseline verification surface.

## A strict-lower-bound issue to preserve

The operational assertion `for every eta>0 there is a feasible example below eta
with ratio >461/500` alone implies only an asymptotic coefficient >=461/500.
It does NOT justify a strict asymptotic lower bound: the ratios could approach
461/500 from above. The planned lower-family proof must supply a uniform larger
rational ratio, or a fixed trial ratio with a proved strict margin, before the
paper states `461/500 < C_Q^*`. This is an explicit acceptance condition, not a
reason to weaken the feasible-family goal without notice.

## Current execution environment

No Lean or Lake executable is installed in this session's container. Direct
GitHub/network installation is unavailable there. An attempt to retrieve an
existing upstream Lean build artifact (without running any workflow) was refused
because it exceeds the connector's artifact-size limit. No compiler or axiom
check has therefore run in this session. The connected GitHub tools do support
source inspection and commits; Python supports independent local source/tests.
A connected machine with the pinned Lean/Mathlib toolchain is needed before any
new result may be marked kernel-checked. This limitation must remain visible
in status reports and must not be replaced by a fabricated build receipt.

## Status meanings

- planned: a specified mathematical target, not a proof;
- source: proof source written, not yet elaborated;
- checked: successful elaboration plus the project-standard axiom audit,
  exact statement check, and source-bound receipt;
- paper-ready: checked and manually matched to its TeX assertion.

A syntax scan or passing Python diagnostic never promotes a theorem to checked.
