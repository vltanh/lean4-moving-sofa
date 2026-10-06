# Arbitrary-angle sofas: a stronger global interval and an analytic crossing model

**Sixth-round mathematical proof drafts, not independently reviewed or Lean-checked.** The current global theorem covers **every bend from 173 degrees up to, but not including, 180 degrees**. A separate result derives an explicit three-phase forward contact model and certifies its unique scalar crossing with the reverse formula near 136.672184698 degrees. **That model crossing is not yet an established global phase transition.**

Start with [INTERIOR_CORE_GLOBAL_CUTOFF.md](INTERIOR_CORE_GLOBAL_CUTOFF.md) for the stronger global theorem and [FORWARD_CONTACT_MODEL.md](FORWARD_CONTACT_MODEL.md) for the crossing equations. Earlier proofs, failed approaches, and numerical data remain available.

## Scope and angle convention

The actual bend beta is the change in travel direction, 0<beta<pi. The classical hallway has beta=pi/2. Write e=pi-beta for the angle between the corridor rays pointing away from the junction. Both arms have unit width and the corner is sharp. This is not a rotation parameter inside a fixed right-angle hallway.

The research branch starts from `main` at `16653ae81e0e4f52a362bafae2ad3440100ad065`. All changes remain under `experiments/hallway_angles/`; the original paper, Lean libraries, and workflows are untouched. No CI, workflow dispatch/rerun, or Lean build was attempted. New commits carry `[skip ci]`.

## 1. Exact unrestricted optimality on a larger explicit interval

For every

    0<e<=1/8 radians, beta=pi-e,

one has

    M(beta)=V(e),

and the unique maximizing compact connected sofa up to congruence is the explicit convex S_e. Competitors need not be convex, symmetric, smooth, aligned, of full actual width, or moved monotonically.

The sufficient starting bend is pi-1/8, with the exact-integer enclosure

    172.838027560 degrees < cutoff < 172.838027561 degrees.

Thus 173-, 174-, 175-, and 176-degree hallways are now included, in addition to the previously covered 177..180-degree range. The fifth-round cutoff pi-1/19 is superseded by this stronger result. The new cutoff is sufficient, not the true onset of reverse optimality or beta_c. No unrestricted optimum at 150 or 170 degrees is asserted here.

The analytic shape and area formula are unchanged:

    d0=cos e, q=sin e, m=2-d0,
    eta=sqrt((2-d0)/(2+d0)),
    K=sqrt(e^2+3(e/sin e)^2)/2,
    R=eta sin K/(cos K+eta sin K),
    V(e)=e/m+(1+2d0)/(4q)+3d0^2 R/(2q m^2).

These outward enclosures evaluate the formula with exact integers. Their interpretation as unrestricted optima depends on the analytic proof draft.

| Bend | Optimum lower endpoint | Optimum upper endpoint |
| --- | ---: | ---: |
| 173 degrees | 11.114966030 | 11.114966031 |
| 175 degrees | 15.553004835 | 15.553004836 |
| 177 degrees | 25.912848797 | 25.912848798 |
| 179 degrees | 77.725311765 | 77.725311766 |

### What improves the cutoff

The previous proof used the candidate's flat-contact rectangle. The new proof uses many wider rectangles contained in its curved interior. Canonical-path error bounds shrink each rectangle into a containing majorant region from which the actual sofa misses only a controlled area. A directional-width inequality then rules out every nonzero entry/exit strip-normal mismatch.

The new exact checker verifies candidate rectangles over the WHOLE e interval and covers EVERY mismatch direction. The compact reproduction record uses 64 parameter cells, 255 common rectangles, and 1024 direction cells; 65 rectangles suffice in the final cover. A separate 128-cell run also passed. These are continuous interval covers, not collision samples.

The proof avoids the earlier full Hausdorff/inball stability dependency. It still depends on the analytic cap-area identity, canonical crossing/excursion majorant, width correction, strict quadratic maximization, geometric realization of S_e, and alignment lemma. A scalar certificate does not independently establish those geometric statements.

## 2. Explicit analytic equations for a candidate branch crossing

The three-phase forward contact model has an early circle-pair phase, a central hyperbolic solution of a constant-coefficient variational equation, and a reflected late phase. Its constants reduce to one contact parameter T.

Writing s=sin(beta/2), c=cos(beta/2), d=cos beta, define

    mu=sqrt(3/[4sin(beta)^2]-1),
    eta_F=sqrt((-1-2d)/(1-2d)).

The matching condition is the explicit transcendental equation

    F(beta,T)=eta_F[3s sin T-c cos T-1]
      +tanh(mu T)[s sin T-3c cos T-eta_F^2]=0.

The closed signed-area expression W(beta,T), derived without numerical quadrature, is given in [FORWARD_CONTACT_MODEL.md](FORWARD_CONTACT_MODEL.md). The scalar system

    F(beta,T)=0,    W(beta,T)=V(pi-beta)

has exactly one solution on 135<=beta<=140 degrees and 13/20<=T<=3/4. The exact-integer certificate proves

    136.672184698 degrees < beta_model < 136.672184699 degrees.

It also encloses the common signed area between 1.867419188 and 1.867419194. These are results about specified analytic expressions. The floating-point representative is approximately 1.867419190797876.

**Missing steps before beta_model can be called the global phase transition:** the complete contact-boundary geometry and continuous feasibility, a matching upper bound for every forward-class competitor, and an unrestricted comparison ruling out other motion/contact types near that angle. No such conclusions follow merely from a unique scalar root.

The central functional is strictly concave for arbitrary fixed-endpoint H^1 variations on the relevant interval; see [FORWARD_CENTRAL_CONCAVITY.md](FORWARD_CENTRAL_CONCAVITY.md). This is stronger than fitting a numerical curve, but it does not optimize over all contact patterns or phase-switch locations.

## Reading order

For the global theorem:

1. [INTERIOR_CORE_GLOBAL_CUTOFF.md](INTERIOR_CORE_GLOBAL_CUTOFF.md).
2. [CURVED_CONTACT_CORES.md](CURVED_CONTACT_CORES.md) and [CONTACT_RECTANGLE_LEMMA.md](CONTACT_RECTANGLE_LEMMA.md).
3. The foundational [REVERSE_CAP_AREA.md](REVERSE_CAP_AREA.md), [REVERSE_GENERAL_MAJORANT.md](REVERSE_GENERAL_MAJORANT.md), [REVERSE_QUADRATIC_THEOREM.md](REVERSE_QUADRATIC_THEOREM.md), [REVERSE_GEOMETRIC_THEOREM.md](REVERSE_GEOMETRIC_THEOREM.md), and [ALIGNMENT_REDUCTION.md](ALIGNMENT_REDUCTION.md), Sections 1-4.

For the contact model, read [FORWARD_CONTACT_MODEL.md](FORWARD_CONTACT_MODEL.md), [FORWARD_CENTRAL_CONCAVITY.md](FORWARD_CENTRAL_CONCAVITY.md), `forward_contact_equations.py`, and `contact_crossing_certificate.py`.

## Reproduce locally

The exact scalar certificate commands require only the Python standard library:

```sh
python interior_core_certificate.py --parameter-cells 128 --points 128 \
  --direction-cells 1024 --output interior-core-proof.json
python contact_crossing_certificate.py --cells 256 --output contact-model-proof.json
```

For the optional numerical regression tests, install `requirements-round6.txt` in an isolated environment. Then run:

```sh
python -m unittest -v test_interior_core test_contact_model
python round6_check.py --output results/round6-checks.json
python forward_contact_diagnostics.py --output /tmp/forward-contact-diagnostics.json
```

**All 29 new local tests passed, none skipped.** The combined reproduction uses the independently successful 64-cell core cover to reduce runtime; it still covers the whole parameter interval. It also verifies source hashes for pinned baseline modules and records code hashes, exact margins, certified values, and hashes of the full certificate records. The result is [results/round6-checks.json](results/round6-checks.json). This is not a rerun of the entire older repository suite.

The crossing checker uses interval automatic differentiation, interval-Newton root tubes, rigorously bounded hyperbolic series, and exact double-angle reduction for trigonometric evaluation. No numerical optimizer or floating-point trigonometric library enters the scalar proof. Numerical quadrature, finite differences, and polygon checks are separate regression evidence.

## Failures retained

[ROUND6_NEGATIVE_RESULTS.md](ROUND6_NEGATIVE_RESULTS.md) records overly wide direct trigonometric enclosures, inconclusive off-root derivative boxes, coarse core/direction failures, and the initial combined-run timeout. No inconclusive interval is replaced by a favorable point sample.

Sampled nonconvex boundary polygons can have small positive outside area even when the signed-area expression and numerical intersection appear to agree. The diagnostics report that discrepancy rather than treating it as zero or calling the polygon an inner certificate. The scalar contact-model crossing is deliberately not relabeled as beta_c.

## Earlier results and their scope

The fifth-round [EXPLICIT_GLOBAL_CUTOFF.md](EXPLICIT_GLOBAL_CUTOFF.md) and [EXPLICIT_MOTION_RIGIDITY.md](EXPLICIT_MOTION_RIGIDITY.md) retain the previous proof and explicit near-optimal mismatch penalty. The fourth-round [EXACT_NEAR_REVERSAL.md](EXACT_NEAR_REVERSAL.md), [REVERSE_SET_STABILITY.md](REVERSE_SET_STABILITY.md), and [UNIVERSAL_LIMIT_SHAPE.md](UNIVERSAL_LIMIT_SHAPE.md) retain separate stability and limit-shape drafts. They are not needed for the new interior-core global argument.

Other earlier results remain: exact reverse-class optimality from beta approximately 114.4698 degrees; the sharp asymptotic expansion; value-function attainment and continuity; and comparison roots bounding all aligned-class crossings between about 133.6443 and 142.0984 degrees. Those roots are not beta_c. The new model root is not a substitute for their class-level quantifiers.

The original searches, failed optimizer terminations, false coarse-grid right-angle improvement, and interval-rectangle lower constructions remain in `results/`. The 29 sixth-round tests do not independently re-audit all previous analytic claims.

## Publication and prior work

The current work provides a stronger draft global interval and an explicit analytic target for the middle-angle transition. Both require independent mathematical and priority review. The competing numerical branches and their approximate crossing were already reported by Xingyi He, *A Gas-Driven Algorithm for Variants of the Moving Sofa Problem*, arXiv:2608.11206v1; that phenomenon is not a new claim here.

Other starting references are Jineon Baek, *Optimality of Gerver's Sofa*, arXiv:2411.19826, and Yoav Kallus and Dan Romik, *Improved upper bounds in the moving sofa problem*, arXiv:1706.06630. The original uniqueness manuscript motivated the project, but the new reverse functional and alignment arguments do not use its uniqueness theorem.
