# Uniqueness of the optimal moving sofa: research record

## Target and current status

The target is equality of SHAPES: every closed connected moving sofa S with
area equal to Gerver's sofa G should satisfy U(S)=G for some Euclidean isometry U.
Equality modulo null sets or uniqueness of Romik's parameter solution is not enough.

The research notes now contain a **candidate full pen-and-paper proof**:
[start with note 08](uniqueness/08-candidate-uniqueness-proof.md).
It is not independently reviewed or formalized. In particular, the substantial
extensions of the polygon variational argument in notes 05 and 06 remain the
highest-priority targets for adversarial checking. Full shape uniqueness is NOT
claimed as a kernel-checked result of this repository.

The work after commit `865eb1f` is paper-first. Positive results, failed
approaches, and repairs are committed separately. These research commits use
`[skip ci]`; CI is not used as a runner. No further Lean declarations, axioms,
challenge changes, or workflow changes were made in this paper-research phase.

## Paper notes

| Note | Contribution and status |
| --- | --- |
| [01: Mamikon equality](uniqueness/01-mamikon-equality.md) | Square-gap identity and complete first-order equality kernels, including nonsmooth support functions. |
| [02: Cap rigidity](uniqueness/02-cap-rigidity.md) | Paper proof that equality in the four cap terms forces a horizontal translation. |
| [03: Obstructions](uniqueness/03-global-reduction-obstructions.md) | Counterexamples to invalid compactness and equal-area set arguments; conditional set-recovery lemma. |
| [04: Penalized selection](uniqueness/04-penalized-selection.md) | Abstract selection theorem for a specified maximizer and a mesh-scale penalty estimate. |
| [05: Right-angle extension](uniqueness/05-right-angle-selection.md) | Proposed extension of the surface-measure and injectivity argument to every maximizing right-angle cap. |
| [06: Shape-preserving angle reduction](uniqueness/06-shape-preserving-angle.md) | Proposed endpoint-balance argument that retains the specified sofa when obtaining a right-angle motion. |
| [07: Regular closedness](uniqueness/07-regular-closedness.md) | Paper proof of G=closure(interior G) from the existing envelope facts, without a new numerical bound. |
| [08: Candidate full proof](uniqueness/08-candidate-uniqueness-proof.md) | Assembly of the arguments, retaining an actual containment of the original sofa through every step. |
| [09: Adversarial review](uniqueness/09-adversarial-review.md) | A further perturbation counterexample, repairs, logical checks, and remaining uncertainty. |

These are mathematical research notes, not automatically validated theorem
statements. No alternative noncongruent maximizing sofa has been constructed.

## Main mathematical progress

Let f=h_K-h_{C(G)} be the support-function difference. Equality in a tangent
Mamikon term with target normal T gives

```text
sin(T-t) f'(t) + cos(T-t) f(t) = f(T)
f(t) = f(T) cos(T-t) + C sin(T-t).
```

Equality in the outer-corner term gives f'(t)=f(t+pi/2). Matching the four cap
intervals in the order 4,3,2,1, using f(pi/2)=0, forces

```text
f(t)=a cos t  for every t in [0,pi].
```

The lower support function is determined by the bottom segment, so this
identifies the entire cap as C(G)+(a,0). The difficulty beyond this short
rigidity argument is ensuring that the cap belongs to the PARTICULAR original
maximizing sofa. The proposed solution is penalized polygon approximation,
not the false claim that every continuum maximum is a limit of exact discrete
maxima. Notes 05-06 retain and control its first-variation errors.

The resulting candidate chain is:

```text
original optimal sofa
  subset its own monotonization
  -> a rotated copy of that same monotonization with right-angle motion
  subset its right-angle monotonization
  = a congruent copy of G.
```

Regular-closedness of G then turns containment plus equal area into exact set
equality. Notes 03 and 09 explain why weaker shortcuts fail.

## Existing Lean equality cases

The earlier commit `865eb1f4e936a976d1405cb59f7a83ffc00fe32b` contains the Lean
equality-case foundation. Import `MovingSofa.Optimality.Equality` to use it.
That development does not itself prove geometric uniqueness.

For a quadratic functional f with midpoint m,
`ConvexDomain.quadratic_deficit_identity` proves

```text
f(x)-f(y) = -Df(x;y) + 4*(f(m)-(f(x)+f(y))/2).
```

For a concave functional maximized at x, both terms on the right are
nonnegative. Equality of endpoint values is equivalent to zero first variation
and zero midpoint gap.

For `upperQL`, `mamikonSegmentEquality_iff` extracts the three separate
convexity equalities for `mamikonS`, `mamikonR`, and `mamikonL`.
`upperQL_eq_gerver_iff` characterizes triples with Gerver's objective value by
zero first variation and those midpoint equalities. The corresponding segment
results hold at every parameter in [0,1].

`ki_upperQL_eq_gerver_of_sofaArea_eq` and
`ki_maximizer_equality_conditions` connect these equalities to an `IsKi` cap
attaining Gerver's sofa area. They do not assume that equality for the auxiliary
objective follows merely from stationarity.

## Verification boundary

The earlier Lean modules and their seven regression examples were checked at
`865eb1f`; that historical check does NOT verify the new paper arguments.
The tests include -x^2 (stationarity alone is insufficient), a constant
functional with distinct maximizers, the deficit identity, the equality
characterization, and the Gerver-cap application. The existing axiom audit
imports those modules. The original optimality proofs and axiom allowlist are
unchanged.

The next mathematical review should focus on the uniform approximation and
endpoint perturbation claims in notes 05-06 before translating the candidate
proof into Lean. The smaller cap-rigidity and regular-closedness arguments can
be checked independently of those extensions.
