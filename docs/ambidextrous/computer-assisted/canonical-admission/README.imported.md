# Canonical-wing admission package

This package belongs with `docs/ambidextrous/two-wing-canonical-admission.md`, which is laid out to drop into PR #3 at `cb91e77`.

| Path | Status |
|---|---|
| `docs/ambidextrous/two-wing-canonical-admission.md` | Written note with self-reviewed proofs: GH1, CW1–CW4, Theorem CA, CA2, JX1–JX2. Not independently audited. |
| `docs/ambidextrous/computer-assisted/check_two_wing_general_height.py` | Exact SymPy checker for the finite algebra of GH1. |
| `docs/ambidextrous/computer-assisted/two-wing-general-height-checks.json` | Executed record of that checker: 8 identities, 3 rejected mutations, source sha256 `77eae99b…`. |
| `diagnostics/` | Floating-point diagnostics behind Section 7 of the note and the GH.5 table. **Not certificates.** |

Requirements: Python 3, numpy, scipy, shapely ≥ 2, matplotlib, and sympy for the checker. Run each diagnostic from inside `diagnostics/`. Runtimes are for 2 cores.

## Exact checker

```sh
cd docs/ambidextrous/computer-assisted
python3 check_two_wing_general_height.py
```

This takes about 12 s. It rebuilds the SQ.6 pre-minimisation expression, which is the same source expression as `check_two_wing_height.py`, but with independent bottom deficits B₀ and C₀. It then checks the following exactly:

- the general mixed term GH.2/GH.3;
- the regressions to WS.10, SQ.9 and NH.8;
- the Hessians against WS.6 and WS.9;
- the absorption identity GH.4 and the WS.11 factorisation.

It also rejects three mutations.

## Diagnostics (`diagnostics/`)

`wings.py` implements the canonical wings, the core curve Γ and the functional Ŵ. `precise.py` computes fiberwise areas of T(K) and saturates the hull by iterating K ← conv T(K). `cand.py` builds Romik's hull from the support formulas of Note 14.

| Command | What it shows | Time | Recorded result |
|---|---|---|---|
| `python3 precise.py` | Candidate: Ŵ ≈ M and \|T\| ≈ Ŵ | 5 s | \|T\| − Ŵ = +2·10⁻⁵ (discretisation) |
| `python3 loops_compressed.py 0.9` (and `0.95`) | Compressed hull at three resolutions; \|T\| − Ŵ against the area of negatively wound faces of Γ | 85 s each | 0.90: 5.19, 5.50, 5.60 ×10⁻⁴ against 5.48, 5.47, 5.47 ×10⁻⁴. 0.95: 3.7, 5.2, 6.1 ×10⁻⁵ against 6.4, 5.5, 5.5 ×10⁻⁵ |
| `python3 -c "import loops; loops.study(0.08, [(3000,2000,4000,1441,3001),(3000,4000,8000,2881,6001),(3000,8000,12000,4001,8001)])"` | Hull shaved at ±π/2 ± β, ε = 0.08 | 2 min | 3.94, 3.38, 3.21 ×10⁻⁴ against 3.90, 3.27, 3.09 ×10⁻⁴ |
| `python3 shave_pi4.py 0.02 0.05 0.1` | Facets at ±π/4, ±3π/4 | 1 min | \|T\| − Ŵ = +4.6·10⁻⁶, +3.3·10⁻⁶, −2.5·10⁻⁵; loops ≤ 6·10⁻⁷ |
| `python3 ca_hyp.py` | Hypotheses of Theorem CA on six hulls | 100 s | (M) holds for x-scale 1.05 and 1.10, and \|T\| − Ŵ is within discretisation there. It fails for x-scale 0.95 and for the junction shaving. |
| `python3 curv.py` | Largest h + h'' on the open quarters for compressed hulls | 1 s | 0.84, 0.87, 0.91, 0.95 for scale 1, 0.95, 0.9, 0.85 |
| `python3 gh1_region.py` | Free minimum of the finite remainder against the GH.5 threshold along rays | 30 s | The table in Section 2 of the note; no negative sample inside GH.5 |
| `python3 junction_test.py 0.005 0.01 0.02 0.04 0.08` | Junction shaving sweep at one resolution | 40 s | \|T\| − Ŵ = −2·10⁻⁶, +3·10⁻⁶, +1.8·10⁻⁵, +8.1·10⁻⁵, +4.0·10⁻⁴; the first three are within discretisation. M − Ŵ = 0.0017, 0.0043, 0.012, 0.034, 0.109 |

## Caveats

The niche is a finite union of quadrants, so it is an inner approximation, and computed areas of T are biased upward by about 2·10⁻⁵ at the default resolution.

The wings R and D are intersections of finitely many half-planes, so they are outer approximations.

The quantity p(β) printed by `precise.py` is a one-sided finite difference of a polygonal support. Treat it as indicative only.

Disconnected envelopes, such as horizontal stretching by 1.15 or more, violate a hypothesis of every comparison here. They must be excluded before reading any \|T\| − Ŵ value.
