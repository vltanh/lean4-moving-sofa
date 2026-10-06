# Coercive extremal route

This directory plans the refactor that turns the quantitative cap-deficit
machinery into an independently audited proof of optimality and uniqueness,
while preserving Baek's faithful formalization, the current main uniqueness
proof, and the formal-conjectures bridge.

Read in this order:

1. [ROADMAP.md](ROADMAP.md) — mathematical and implementation phases;
2. [DEPENDENCIES.md](DEPENDENCIES.md) — allowed/forbidden proof dependencies and audit design;
3. [FORMAL_CONJECTURES.md](FORMAL_CONJECTURES.md) — bridge, Challenge, and dual-solution strategy.

## Branch/PR policy

This work is intentionally stacked on \`research/quantitative-stability\`.
The coercive classification needs the lower stability modules
(\`BaekDeficit\`, residual energy, cap coercivity, support distance, cap
distance), but should not depend on the global stability/qualitative-entry
layer.

The desired eventual source graph has three coexisting theorem routes:

- **Baek:** faithful optimality in \`MovingSofaOptimality\`;
- **main uniqueness:** the current equality/CapKernel proof;
- **coercive extremal:** independent optimality and uniqueness from maximality
  plus zero-deficit coercivity.

The same \`MovingSofaBridge\` then transports either internal extremal proof to
the unchanged formal-conjectures statement.

## Current status

Planning only. No Lean files are changed by the initial roadmap commits. No
Lean, Lake, CI, remote build, or TeX compilation has been run. The next code
milestone is the dependency refactor around neutral Mamikon gap lemmas and
maximizer geometry.
