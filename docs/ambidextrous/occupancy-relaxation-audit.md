# A necessary correction to the optimality-only occupancy plan

This note audits the proposed computer-assisted route before spending effort on a large search. It does not change the proved forbidden-triple bound CF2. It proves that the unbranched LP in the new plan has a structural lower bound that prevents it from giving the requested sharp upper bound on many of the planned search boxes.

Labels OR are local. The baseline is `924ee7fef66b4cb1b9d5d9ba356a41d6adb250c7`. No numerical computation, existing optimum, or one-turn functional theorem is needed below.

## 1. The fractional barrier

Let a finite partition of a region Omega have cells of areas a_i >= 0. Consider exactly the relaxation

$$
0\le z_i\le1,\qquad z_i+z_j+z_k\le2
$$

for any collection of triples of distinct cells. Its objective is to maximize sum_i a_i z_i. The constraints are necessary for the indicator of cells met by a feasible body, as in CF1--CF2.

**Proposition OR1.** The optimum of this LP is at least

$$
\boxed{\frac23\sum_i a_i=\frac23|\Omega|.}
$$

**Proof.** The constant assignment z_i=2/3 is feasible for every possible triple. Evaluate its objective. QED.

This holds if all possible geometric triples are included, at every angular and spatial resolution. Thus finer cells and additional hallway angles cannot by themselves overcome this bound. For equal cells, it also follows directly from CF2: putting L=sum_e lambda_e and c_i=sum_{e containing i}lambda_e gives sum_i c_i=3L, and

$$
2L+\sum_i(1-c_i)_+\ge 2N/3.
$$

Indeed (1-c)_+ >= 1-(2/3)c when 0<=c<=1, while for c>=1 the needed combined pointwise inequality is (2/3)c+(1-c)_+ >=2/3. Summing the latter proves the assertion for every nonnegative dual proposal, whether or not its degrees exceed one.

On the planned rectangle [0,4] times [0,1], the barrier is 8/3. Even after reducing the bounding rectangle to [0,W] times [0,1], it is 2W/3, so this LP cannot prove an upper bound below M when W>=3M/2. This is a statement about the relaxation, not a feasible sofa of area 2W/3.

## 2. Repeated witnesses provide pair constraints, but not a complete cure

CF1 permits q=r. If two distinct cells P,Q satisfy both strict separations

$$
\inf_{p\in P,q\in Q}(q-p)\cdot u>1,\qquad
\inf_{p\in P,q\in Q}(q-p)\cdot v>1,
$$

then they cannot both be met, giving z_P+z_Q<=1. These constraints were omitted by the distinct-triple-only relaxation, even though they follow from its continuous geometric source.

Adding arbitrary pair constraints as well as triples still leaves z_i=1/2 feasible. Consequently the resulting unconditioned LP has optimum at least |Omega|/2. On an area-four search rectangle this remains two, above the target. Additional mandatory occupied cells, certified empty regions, clique inequalities, or integral branching can change this conclusion; OR1 does not concern those strengthened models.

## 3. What an adequate replacement must do

At least one of the following is necessary for the proposed global computation:

1. Branch on actual occupation decisions, or on support-witness/placement boxes that imply occupied and empty cells, then certify an upper bound at every leaf.
2. Use stronger valid occupancy inequalities such as those for incompatible cliques or exact small hypergraph subproblems, retaining a verified derivation.
3. Work directly with interval bounds for the ordinary area of finite-position hallway intersections, as in the older width certificate.

For occupation branching, a split on cell i covers all actual bodies because their meet indicators are exactly zero or one. The children impose z_i=0 and z_i=1. After z_i=1, an incident forbidden triple becomes a pair constraint; after two occupied members its remaining member is forbidden. These are exact logical consequences, not fractional rounding.

A complete proof tree must retain both children unless a child is independently infeasible or has a verified upper bound. A large explored-node count with unresolved leaves is not a global certificate. Nor is a branch a candidate-neighborhood certificate unless a separate geometric theorem maps its conditions to the precise neighborhood used by the local proof.

## 4. Additional distinction at the local boundary

The global-versus-local strategy also needs a noncircular local theorem on an explicitly specified neighborhood in a topology covered by the computation. A bound on finitely many sampled support values is not automatically a C1 neighborhood; uniform Hausdorff closeness does not imply derivative or curvature closeness. The saturated axis-cut examples already demonstrate why exposed faces need separate care.

The existing restricted geometric theorems cannot simply be declared to be the required local theorem. Each has admission hypotheses that must be verified for every body in the chosen residual set.

## 5. Decision

Do not run the unmodified triple-only LP over the entire width/endpoint domain expecting it to localize all competitive bodies. Retain CF2 for boxes where it is effective, and implement or prove a strengthened, independently checked finite-position bound for the remaining boxes. This audit removes an impossible computational expectation; it does not prove the optimal value or refute the candidate.
