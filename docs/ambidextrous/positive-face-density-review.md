# Review: the full-turn value reduces to saturated positive opposite faces

**Unrestricted optimality is not proved.** This continuation gives a hand-proof approximation theorem, not a new sharp area upper bound. Its payoff is to remove point faces as a separate *value* obligation. Its caution is equally important: the positive opposite-end-face class carries the entire full-turn supremum, so it is not a class that can be discarded by a uniform numerical margin.

Baseline: `c68813d3b5148b21fdd44553c1ced55060bf4844`. New sources are [RR](rounded-strip-regularization.md) and [PD](full-turn-positive-face-density.md). The proofs use the earlier canonical motion reduction and SI safe-strip transport. Only the final localization to unit end strips uses the existing AW-W width theorem and FD1 face classification. The weighted theorem WV2 is not a premise of this approximation argument.

## 1. The exact new statements

RR1 proves that, for 0<lambda<1 and r=(1-lambda)/2,

$$R_\lambda=\lambda S+rB$$

preserves every canonical hallway already feasible for S. The proof is the pointwise depth estimate

$$\lambda(h_S(n)-s\cdot n)+r(1-z\cdot n)\le\lambda+2r=1.$$

Its width function is exactly lambda w_S+1-lambda, so the safe-strip set has not been enlarged. The body stays connected and its area tends to |S| as lambda tends to one.

RR2 cuts epsilon<r from each of two opposite supports. The original center set lambda S remains inside the slab. The shaved body is a union of convex disk caps attached to that connected center set, so it remains connected. Support disks supply two actual positive-length face chords. This avoids the false assertion that arbitrary strip clipping preserves connectedness.

PD chooses a record width slightly above one near a boundary of the safe-strip component. A semiconvex width estimate proves that sufficiently shallow shaving retains a strictly increasing width interval up to that direction. After shrinking by the reciprocal of the attained slab width, the whole path of intermediate strip directions has width at most one. SI2 therefore supplies actual full turns in the new incoming orientation.

The positive left derivative of width orders the two faces strictly: the top face is to the left of the bottom face. The two homotheties tend to the identity, and RR's area sandwich gives convergence to the original area. The approximants can be chosen with area strictly below the original area without assuming that the original body is optimal.

Thus, for full-turn bodies,

$$\boxed{\sup |S|=\sup_{\text{positive opposite-end faces}}|S|,}$$

where the width-greater-than-two qualification is imposed only on the competitive part of the supremum. A full-turn counterexample above M would produce a counterexample in that positive-face class.

## 2. Saturation does not weaken this reduction

**Corollary PS1.** The same supremum is obtained by restricting further to fully canonically saturated bodies with positive opposite-end faces.

**Proof.** Let S_j be a competitive approximant from PD, in its new unit-span full-turn coordinates, and set K_j=conv(S_j). Let E_j be the full canonical two-turn envelope inside K_j.

Every abscissa in the hull projection occurs in S_j because S_j is connected. The vertical sections of K_j are intervals, while the lower forbidden sweep has downward sections and the upper sweep has upward sections. Hence every vertical section of E_j is a nonempty closed interval. The set E_j is compact. It is connected: a separation into two disjoint compact sets would assign each connected fiber to one of them, giving two disjoint compact projections partitioning an interval. This is impossible.

The inequalities defining E_j give both full canonical motions, and

$$S_j\subseteq E_j\subseteq K_j=\operatorname{conv}(S_j),$$

so its hull is exactly K_j. Its face geometry is unchanged, and saturating again gives the same E_j. Also |E_j|>=|S_j|. Thus every area approximated by the S_j is bounded above by areas in the saturated positive-face class. The reverse supremum inequality is immediate because those bodies are full-turn bodies. QED.

If the original S is an attained full-turn maximizer of value V, then |E_j|<=V and |S_j|->V, so |E_j|->V as well. If S is merely the reference body of area M, the argument gives liminf |E_j|>=M; it does **not** assert |E_j|<=M or convergence to M before optimality is established.

## 3. The sharpness obstruction is now proved for positive faces too

Apply the from-below part of PD2 to the reference. It produces genuine connected full-turn bodies with two nondegenerate faces in opposite end strips and

$$|S_j|<M,\qquad |S_j|\longrightarrow M.$$

Consequently no epsilon>0 can make the entire positive opposite-face class satisfy |S|<=M-epsilon. After PS1, requiring full canonical saturation does not restore such a gap.

This rules out a proposed strategy before an expensive certificate search: excluding literal point faces does not leave a uniformly suboptimal positive-face remainder. A computer or hand proof on that class must itself be sharp or keep an analytically treated limiting neighborhood. It is not enough to improve a coarse global constant.

The conclusion does not assert an example above M. Nor does it undo FAS or RS: the approximants deliberately have separated, asymmetric faces and may change their incoming orientation. FD3's prohibition concerned aligned positive-face approximants, which are not being used.

## 4. Main independent-review points

- The rounding budget is paid by a shrink. It is not the failed Minkowski average of the actual nonconvex body, and finite-step area monotonicity is not asserted.
- The shave depth is strictly less than the rounding radius. All disk centers survive; this is the connectedness argument.
- The final face segments are actual points of the body, not merely formal facets of a larger hull.
- The actual shaved hull is only a subset of the clipped convex hull. Its final width agrees at the two cutting supports; this is sufficient for the bridge and for the derivative comparison. Equality of the whole hulls is not assumed.
- The width perturbation argument uses semiconvexity and a fixed positive derivative interval. Uniform convergence of arbitrary continuous functions would not give that conclusion.
- Choosing a record excursion gives a strict width gap on the entire earlier path, not just at sampled strip normals.
- A further shrinking factor makes that entire path safe. Full turns in the new orientation follow from SI2; reorientation is not declared free without proof.
- The area limit has both bounds: a retained homothetic copy of S below, and a vanishing neighborhood above. Hausdorff convergence alone would not give the lower area bound.
- The optional from-below choice is made after selecting the record normal and before the sufficiently small shaving. The order of choices is essential.

These are self-reviewed arguments, not an independent verification of the complete motion/width dependency chain.

## 5. Bounded checks actually executed

The standard-library script [check_positive_face_density.py](computer-assisted/check_positive_face_density.py) ran under an external five-second limit. Its internal runtime was about 0.007 seconds. It passed 93 named checks, including 80 depth-budget cases and 101 rational clipped-width samples, plus four deliberately omitted/incorrect-premise controls.

The [record](computer-assisted/positive-face-density-checks.json) reports Python version, hashes and scope. Executed bytes match Git blob `761900d38540215411807cbd7a40c23cd6927b2f` and SHA-256 `adbf1fab0e4aee1a6d40d61eef40c060dc28721acbdf943ec176e63d392428ec`.

The rectangle calculations test the convex strip lemma at rational directions, not the full continuum density theorem. The script does not certify an arbitrary body's feasibility, connectedness, strip component or limiting area. Those are proved in RR/PD/PS.

Two earlier exploratory invocations were each capped at five seconds: sampled rectangle-niche values and finite-angle tests on prescribed parallelograms. Neither produced a sharp bound or a verified continuum counterexample, and neither is a premise of the new result. No large search or refinement campaign was run.

## 6. What remains

The weighted value and previously admitted ordinary-area classes remain as stated in the branch. PD/PS do not add an upper bound for the positive opposite-end-face class. Instead they show that bounding this single saturated positive-face class sharply would settle **all full-turn bodies**, including point-face limits.

Uncovered partial-turn bodies remain separate. RR preserves known motions; it does not create the missing bridge across a width bump between outgoing strip directions. SI3 continues to apply only when its full safe-strip interval hypothesis is verified.

The honest remaining targets are therefore:

1. A sharp ordinary-area upper bound on saturated full-turn bodies with positive opposite-end faces, or an equivalent valid reduction.
2. An upper comparison or full-turn reduction for the remaining partial-turn configurations.

A result for one attained unrestricted maximizer still suffices for the value. Counting the number of named face alternatives is not a measure of proximity to that proof. In particular, the new density theorem shows that the full-turn remainder retains the entire supremum.

All substantive findings use `[skip ci]`. No CI, Lean/Lake compilation, dependency installation, manuscript build or long computation was used. PR #3 remains open and draft; unrestricted optimality and independent verification remain unfinished.
