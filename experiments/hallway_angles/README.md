# Arbitrary hallway angles: research experiment

Status: exploratory work, not a theorem of optimality and not part of the Lean build.

## Scope

Change the actual bend of a unit-width, sharp-corner hallway. Write `beta` for the change in travel direction, with `0 < beta < pi`; `beta = pi/2` is the classical hallway. The angle between the two rays pointing away from the corner is `pi - beta`. This is **not** Baek's fixed sofa rotation parameter `omega` in the original right-angle hallway.

Work starts from `main` at `16653ae81e0e4f52a362bafae2ad3440100ad065`. All changes are confined to this experiment. Existing paper and Lean claims are untouched. No CI, Lean build, workflow dispatch, or workflow rerun is requested. Commits carry `[skip ci]`.

## Research protocol

1. Specify the hallway by unit-normal inequalities and verify the right-angle case.
2. Derive what survives from the support-function/Mamikon argument without presuming a sharp concave relaxation exists.
3. Implement reproducible local numerical search for motion paths, considering both natural endpoint rotation directions.
4. Separate sampled-intersection area from continuously feasible area. A finite set of collision checks alone is not a lower-bound certificate.
5. Record negative results as well as successful constructions, with seeds, parameters, and limitations.

A nonconvex numerical solver does not establish global optimality. Uniqueness of a continuous optimizer would not by itself establish convergence of a discretization. Affinely shearing Gerver's sofa and hallway does not transport a rigid rotation into a rigid rotation.

## Starting references

- Jineon Baek, *Optimality of Gerver's Sofa*, arXiv:2411.19826, especially the cap, niche, and concave upper-bound constructions: <https://arxiv.org/html/2411.19826v1>.
- This repository's uniqueness manuscript, `paper/uniqueness-arxiv`, `docs/paper/sections/08-equality.tex`: the Mamikon square-gap identity and support-function tangent equations.
- Yoav Kallus and Dan Romik, *Improved upper bounds in the moving sofa problem*, arXiv:1706.06630: <https://arxiv.org/abs/1706.06630>.
- Xingyi He, *A Gas-Driven Algorithm for Variants of the Moving Sofa Problem*, arXiv:2608.11206: <https://arxiv.org/html/2608.11206v1>. This is relevant numerical prior work on actual corridor-angle variation and competing motion patterns, not a proof of the global optimum. Its corridor-angle convention is supplementary to our bend-angle convention.

## Log

- Initial checkpoint: scope and validation requirements recorded before implementation. In particular, no arbitrary-angle analogue of Baek's sharp functional `Q` is assumed.
