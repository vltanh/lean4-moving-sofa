# One-turn arm reduction: floating-point companion checks

Companion to [one-turn-arm-reduction.md](../../one-turn-arm-reduction.md), labels AR. The proofs there are pen-and-paper. This directory only replays formulas and examples in floating point; nothing here is a certificate.

## Files

- `check_one_turn_arm_reduction.py` — the checker. Requires numpy, scipy and shapely.
- `one-turn-arm-reduction-checks.json` — the executed record. Its `script_sha256` field is the SHA-256 of the exact checker that produced it.

Recorded run: Python 3.13.16, numpy 2.5.3, scipy 1.18.1, shapely 2.1.2, about 80 s.

Run with

```
python3 -I check_one_turn_arm_reduction.py one-turn-arm-reduction-checks.json
```

## What each part checks

**A — candidate**
- The constants Y, beta, M, a_*, the switching momentum z, and relation (A.18).
- The closed forms AR.6–AR.7: W_*=2a_*, T_*=a_*, arms 1/(2 sin beta), max rho=cot(beta)/4<1.
- A-F=0 and Psi=M/2 for the cap integrated from the AF Euler–Lagrange law (AR.5) with q(0)=1/(2 sin beta)-1.

**B — arm propagation (sample test)**
- Random admissible trajectories of the curvature class (WR.5), and of WR.5 together with AR.9.
- Trajectories leaving p<=1, q>=-1 are discarded, since Lemma AR0 rules them out for caps.
- Records the worst value of sup q minus the bounds AR.8 and AR.10.

**C0 — fold-free control:** a curvature-class cap with rho<=0.61, which should give A-F=0 up to evaluation error.

**C — negative examples (AR8)**
- Shoots the two curvature-class caps with an active envelope fold.
- Checks class membership and, separately, the AR.9 violations.
- Computes A-F at two resolutions and the swallowtail loop area of the B envelope.

**D — discrete exposure, AR7 (a), (b) and the mirror of (a)**
- Uses circumscribed grid polygons of ODE-built caps.
- The niche is the finite union of open quadrants; exposed wall lengths are computed with shapely.

**E — saturated-balance diagnostic, Section 9:** first passage time of q to -1/2 under the saturated laws, as a function of q(0).

## Method notes

- Caps are generated from the contact-velocity system with f(0)=1 (translation), g(0)=1 (height) and p(0)=1/2. f(L)=1 is imposed through H(L)=integral_0^L (p sin t+q cos t) dt=0.
- The cap area is computed from AR1. The niche area is the integral of the positive part of the interior roof sup_t min(R_t,L_t). That roof is evaluated by a discrete argmax over angles followed by golden-section refinement with the dense ODE interpolant.

## Known limitations

- Sample tests can miss violations.
- The negative examples are evidence only for the curvature class WR.5. They also violate AR.9, so they say nothing about the class cut out by WR.5 and AR.9 together.
- Part E assumes an unproved exact exposure law and activity pattern.
