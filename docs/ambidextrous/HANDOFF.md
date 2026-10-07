# Ambidextrous sofa research — start a new session here

**Unrestricted optimality is not proved.** The weighted one-turn value is established in the written WV chain. The new FAS1 theorem proves the ordinary-area bound for every full-turn body with identical positive-length horizontal hull faces, with no minimum face length. Point faces, opposite-end faces, and unhandled partial turns remain. Unrestricted uniqueness is deferred.

Repository: `vltanh/lean4-moving-sofa`.
Branch: `research/ambidextrous-pen-and-paper`.
Draft PR: #3; current base: `main`.
Latest substantive review before this handoff: `e786b22345666776bdcb92397fc68b186ed2b36b`.
Always query the live tip and read intervening commits. Do not reset the PR to the historical paper base.

## 1. User instructions and proof status

Prefer pen-and-paper proofs. Use brief computer calculations to reject bad ideas or check arithmetic, not long searches. New script invocations remain capped at 30 seconds, preferably external five/ten-second limits. **No CI, Lean/Lake compilation, dependency installation or manuscript build.** Commit substantial findings, including negative ones, frequently with `[skip ci]`. Keep work under `docs/ambidextrous/` and preserve concurrent edits.

All arguments are written and self-reviewed. The full historical proof chain has not been independently verified or kernel-checked. Read [short-face-extension-review.md](short-face-extension-review.md) for the latest audit and [weighted-value-proof-review.md](weighted-value-proof-review.md) for the main weighted theorem's dependencies.

The reference value is

$$M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.$$

For optimality, an upper bound for one attained global ambidextrous maximizer suffices. Do not add unrestricted equality classification as a prerequisite or assume that an ambidextrous maximizer is a weighted-cap maximizer.

## 2. Latest completed ordinary-area case

Read [full-turn-aligned-short-faces.md](full-turn-aligned-short-faces.md) first. **FAS1** proves

$$\boxed{\text{both full conventional turns and identical faces of length }T>0
\Longrightarrow |S|\le M.}$$

There is no curvature, smoothness, symmetry, endpoint-height or lower face-length premise beyond those stated. The proof removes the old T>=1 restriction in this full-turn class.

Its short argument is:

1. [SW1](scaled-width-margin.md) scales a body of width W>2 uniformly to width two and uses AW-W's height-at-most-one version. It gives `|S|<41 W^2/100`, hence
   
   `W<=1001/500 => |S|<41082041/25000000<M`.
2. For W>1001/500 and aligned 0<T<1, retained endpoints of both faces force flank inequalities at every angle in `(0,2 arctan T)`.
3. They imply T>2-sqrt(3), so testing pi/6 bounds each flank by sqrt(3)/2.
4. Failure of a SCG clipping inequality forces one flank below `cos(2 arctan T)`. Thus W<=T+cos(2 arctan T)+sqrt(3)/2.
5. An explicit polynomial sum-of-nonnegative-terms identity bounds this by `1201/600<1001/500`, a contradiction.
6. SCG then confines both positive niches to the common face, gives zero clipping and adds the two universal weighted bounds.

No numerical maximization or new computer-assisted theorem is in this chain. The rational margin and polynomial identity have hand proofs.

## 3. A finite hand criterion can also force full turns

[SCG1](short-chord-optimality.md) starts with four actual points `(a,0),(a,1),(b,0),(b,1)` and actual horizontal extreme points `(l,y_L),(r,y_R)`. Write T=b-a, R=r-a, B=b-l and m_i=min(y_i,1-y_i). For 0<T<1 its sufficient conditions are R,B>1 and

$$2TR+m_R(1-T^2)>1+T^2,\qquad
2TB+m_L(1-T^2)>1+T^2.$$

They force both full turns and zero clipping. The rectangle between the four points only needs to lie in the hull; its four corners must be in the actual body.

[CSF1](central-short-face-optimality.md) makes those tests automatic if both face intervals span `[l+1,r-1]` and the width exceeds an explicit threshold. Examples: W>1+sqrt(2) with no extra extreme-height information, W>7/3 for extremes in [1/4,3/4], W>sqrt(5) for mid-height extremes. Initial floor tests force a common left endpoint, support widths force full turns, and final tests force right alignment. It never treats a face-interior point as retained before this is proved.

The CSF note verifies an actual feasible short-face example: an ellipse of semiaxes 7/10 and 1/2 added to a horizontal segment of length 9/10. Its actual two-turn hull has width 23/10 and common face length 9/10. Support inequalities, niche-height bounds and surviving extreme points are checked analytically.

An earlier parameter-only example W=12/5,T=2/5 was not a verified realization; FAS's flank bounds show it is infeasible. Both notes now use the actual ellipse example instead. The correction is recorded in the review.

## 4. The remaining full-turn alternatives are now explicit

[FD1--FD2](full-turn-face-dichotomy.md) classify the endpoint interval tests. For W>2 and both full turns, two nondegenerate faces must either coincide and span `[l+1,r-1]`, or lie in opposite unit end intervals `[l,l+1]` and `[r-1,r]`.

FAS handles the first case entirely. Thus a full-turn counterexample above M must have

- at least one point face; or
- two positive faces in opposite end intervals.

The second alternative has both face lengths at most one. No positive-face shifted-overlap case remains. Neither of the two remaining alternatives is excluded by the current arguments.

Partial-turn bodies still need actual angular coverage or a direct area bound. CSF and earlier angle tests cover only their stated subcases.

**Do not try the naive point-face limit.** FD3 proves that aligned positive-face, full-turn, unit-span hulls of widths tending to W>2 cannot converge to an aligned point-face hull: their common face lengths are at least W_j-2, and the positive limiting segment remains in both faces. Adding a tiny horizontal segment at fixed height is therefore not a valid approximation. Shrinking first loses the required unit span unless a separate feasible restoration is proved.

## 5. Weighted theorem and earlier infrastructure

The signed one-turn objective is

$$\Psi(U)=|U|-|N(U)|-W(U)/2,$$

where N(U) is the whole positive-height niche. [WV2](one-turn-weighted-value.md) proves sup Psi=M/2 in the current written chain. PA2 gives attainment; WP/WR give selection and regularity; AR/PT/TS/EB give same-sign control, a positive top face, half-height niche and exact limiting exposure balance. TF/HF give niche confinement, T=W/2 and the stationary convex-core identity.

CG improves the sufficient arm threshold. SE uses an actual feasible one-turn body and Gerver's established area bound to force one good curvature quarter. VE proves a source-flux lower bound from globally visible pieces. WV's energy contradiction forces the other quarter good; AR4/SR1/AF3 then give the sharp weighted value. VE's limiting argument and the historical chain still deserve independent review. The assumed saturated ODE is not a premise.

The one-turn Gerver theorem and the six pinned rational enclosures in SE are explicit external inputs. No Lean source was compiled. The latest short-face proofs do not use TE or the large matching/width certificates.

AW-W excludes width<=2 analytically; SW1 now strengthens the competitive lower restriction to W>1001/500. AL1 still gives W<=2999/1020. AM2 and TE1 retain their scoped computer-assisted exclusions, not a complete sharp covering. Common-hull reduction and attainment remain earlier written dependencies.

## 6. Exact remaining area comparison

For general full-turn cap pairs with nonempty surviving fibers,

$$|E|=\Psi(U)+\Psi(V)+G,\qquad G\ge0.$$

With Delta(U)=M/2-Psi(U)>=0, the remaining target is G<=Delta(U)+Delta(V), or an alternative legitimate ordinary-area bound. The new FAS proof makes G=0 in its class only. It does not make a symmetric weighted-maximizer body dominate every competitor.

Retain the earlier negative controls AF4, GR1, AX1/SAT1, SAC2, SC3, TR1 and AO1. Repair, saturation and candidate proximity did not justify those universal enclosures. Canonical-wing bookkeeping still has both negative winding and uncovered surviving material. Small extreme-height difference does not imply mid-height or C1 proximity. Point-face examples can approach M, so a uniform strict gap on that whole class is not available.

Original uploaded packages and author diagnostics remain preserved with provenance in their reviews. The unconditioned occupancy LP's fractional barriers still rule out simply refining the old model. No long search is authorized by the present task.

## 7. Short executed checks

Run

```sh
timeout 5s python docs/ambidextrous/computer-assisted/check_short_face_extension.py
```

The record `computer-assisted/short-face-checks.json` reports 19 named checks. The full FAS polynomial identity is verified coefficient by coefficient; 1,805 rational strip tests, 985 flank tests, 27 central-threshold regressions and 6,084 interval pairs supply finite negative/positive controls. Internal time was about 0.030 seconds under a five-second cap.

The executed bytes match fetched Git blob `65ab585aa3c29f5596f00bd2569c7103c1030529`. These checks do not verify WV2 or replace the continuum proofs. The review also records the hull-only retention counterexample and the rejected parameter-only illustration.

## 8. Restart rule

Read FAS, FD and the latest review before choosing the next target. The active unresolved classes are point faces, opposite-end positive faces, and remaining partial-turn bodies. Prove a genuine improvement or ordinary-area bound for one specified class; do not re-maximize Psi or assume the new face tests cover all maximizers.

Refresh blob SHAs before edits, preserve concurrent work, commit both positive and negative findings, and keep scripts short. No CI, Lean/Lake compilation, dependency installation or manuscript build was used. PR #3 remains open and draft because unrestricted optimality remains unproved.
