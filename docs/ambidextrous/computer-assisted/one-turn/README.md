# One-turn reduction: numerical diagnostics

Companion scripts for `../../one-turn-reduction.md`. **These are floating-point diagnostics, not proof certificates.** They sample caps and use finite angle grids. Computed niches are unions of finitely many hallway quadrants, so they are inner approximations, and computed sofa areas slightly over-estimate the truth.

Requirements: Python 3, numpy, scipy. Run each from this directory.

| Script | What it checks | Runtime (2 cores) |
|---|---|---|
| `cand.py` | Builds Romik's candidate from the exact support (14.2) and checks 2Psi(U*) = abs(E(U*,U*)) ≈ M, clipping 0, niche height 1/2 + R - sqrt 2 | about 1 s |
| `optimize_psi.py` | Maximizes Psi(U) = abs(T_U) - W/2 over polygon caps from candidate, wide and narrow starts | about 8 min |
| `optimize_pairs.py` | Maximizes abs(T_U cap rho(T_U' + shift)) over asymmetric pairs; reports the clipping term | about 6 min |
| `repair.py` | Random polygon caps: does the curvature repair R decrease the one-turn functional A? Also confirms the candidate is a fixed point of R | about 3 min |
| `repair_search.py` | Adversarial version of the same question, with a width cap `--wmax` | about 10 min per 5 trials |
| `af_chain.py` | Checks A = F on repaired caps (SR1; `--converge` shows first-order convergence) and F - W/2 <= M/2 (AF3) on samples | about 4 min |

## Results recorded for the note

- `cand.py`: abs(E(U*,U*)) = 2Psi(U*) = 1.645005 at 3000 hallway angles, against M = 1.644955.
- `optimize_psi.py`: 16 runs, at 12 and 14 normals per quarter, all reach one configuration, with W in [2.327, 2.336], face 1.18–1.22, end edges 0.44–0.51, and niche height 0.387–0.390. At 14 normals no run exceeds the discretized candidate, 0.821628.
- `optimize_pairs.py`: no asymmetric gain beyond discretization, with clipping at most 5e-6 at the optima.
- `repair.py` and `repair_search.py`: no decrease for W <= 2.8, minimum +0.000005; a decrease of 0.050 near W = 4.5. GR1 proves a decrease at W = 2.52 that these searches cannot resolve.
- `af_chain.py`: A - F was 6.4e-4, 3.2e-4 and 1.6e-4 on successive refinements; F - W/2 - M/2 was at most -0.032 on 40 samples.
