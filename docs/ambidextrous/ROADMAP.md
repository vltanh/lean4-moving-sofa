# Active roadmap after trying four directions

**General full-turn and partial-turn optimality remain unproved.** The latest user request was to commit the different directions and try all of them. The first pass is documented in [four-direction-first-pass-review.md](four-direction-first-pass-review.md); the original plan is [four-direction-research-plan.md](four-direction-research-plan.md). This roadmap replaces the previous default of extending the most recent conditional family.

## 1. Goal and rules

The goal is ordinary area at most the explicit reference value

$$M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.$$

A new result should eliminate a possible maximizing configuration, give a correctly oriented universal area comparison on its domain, or reduce the target to a complete smaller class. A special-case margin is not global admission, and rewriting the target as a clipping inequality does not establish it.

Prefer hand proofs. Keep each computation under an external five/ten-second cap where practical, never over 30 seconds without new authorization. Commit substantive positive and negative findings frequently with `[skip ci]` under docs/ambidextrous. **No CI, Lean/Lake compilation, dependency installation or manuscript build.** Preserve concurrent work. All written arguments and historical dependencies remain self-reviewed rather than independently verified. Unrestricted uniqueness stays deferred.

## 2. Results and decisions

| Direction | First attempt produced | Decision and next gate |
|---|---|---|
| D1: actual maximizer structure | Exact second-order rejection of feasible balanced saddles; finite critical-face candidates for bounded rational quadratic charts. | Continue on actual unresolved geometric charts. Do not re-derive the already known first-order balance or drop its normal cone. The continuum curvature/injectivity theorem is still missing. |
| D2: coupled dual | An overlap-safe dual, and an exact counterexample to sharpness with one constant weight per quadrant. | Stop that unsplit-weight version. Continue spatial allocation valid across parameter boxes. No globally sharp allocation yet. |
| D3: finite-angle exclusion | One complete eight-offset box has upper area 709/480<M. Two independent rational methods and a hand integration agree. A larger box was not excluded. | Combine exact boxes with D1 critical faces. Record every residual region; no claim of complete global covering or improved global constant. |
| D4: area versus angle | Exact allowance Lambda(p,q;e) using actual strip widths; zero allowance when arccos(p)+arccos(q)>=e. | Insert into genuine partial-endpoint branches. Positive allowances still require a deficit. No automatic minimum-width/slack relation or connected deletion. |

The notes are [D1](direction-1-critical-face-reduction.md), [D2](direction-2-overlap-safe-duality.md), [D3](direction-3-robust-finite-angle-box.md), and [D4](direction-4-width-aware-completion.md).

## 3. Concrete next experiment

Use one precisely stated finite-angle placement region, with rational normals and a proved bounding box. The robust forbidden-union method first gives an upper bound for every placement in that region. If inconclusive, subdivide into actual line-arrangement charts and apply the exact critical-face candidate reduction. Keep all candidates at chart boundaries and all actual connectedness/hull-retention constraints if optimizing the connected class.

This combines Directions 1 and 3 with the spatial accounting retained from Direction 2. It avoids two unproved substitutions: treating arbitrary caps as weighted maximizers and pretending that a hull-area gain survives niche deletion. It also avoids the fractional occupancy barrier by evaluating the finite geometric envelope rather than only pair/triple occupancy constraints.

**What would count as a decisive next result:** a complete exclusion of a genuinely unresolved compact configuration region, an explicit surviving critical configuration with a valid analytic improving direction, or a sharp residual theorem covering all remaining branches. A growing list of individually successful boxes is not complete coverage. The number of finite charts can be large; the abstract finite-candidate theorem is not a runtime guarantee.

For a branch with partial endpoint angles, use Direction 4's actual incoming/outgoing widths. It reduces the worst-case CC cost and can sometimes supply a zero-loss bridge. Do not choose a more favorable incoming frame unless the actual body has a proved motion to it.

## 4. The global equality that is still not paid

For compatible full-turn cap pairs with nonempty surviving fibers,

$$|E|=\Psi(U)+\Psi(V)+G,\qquad
\Delta(U)+\Delta(V)-G=M-|E|.$$

Thus G<=Delta(U)+Delta(V) is the desired full-turn theorem itself. The weighted value in the existing written WV chain does not pay G. AS's adaptive aggregate upper bound is a stronger sufficient target and is also unproved globally.

In the valid minimum-width frame, the identity instead reads

$$G_s=T_s+C_s-sW.$$

The universal shortcut G_s<=0 is **false**. MS proves G_s/s -> 2T-W on a regular scaling family, with an explicit positive stadium example. NR gives positive G_s arbitrarily near M from below. These are in `minimum-width-positive-slack-counterexample.md` and `near-reference-positive-minwidth-slack.md`. Retain cap deficits; do not reopen the false sign-only strategy.

MF's same-body face overlap, FO's conditional overhang budget, and SM/SB's reference-scale margin and exact bridge remain useful scoped results. They do not place arbitrary competitors in their domains. The current four attempts do not independently audit the entire WV/SR/AF continuum chain.

## 5. Partial-turn bookkeeping

CC gives the unit-strip allowance lambda(e)=tan(e/2)-e/2 and the exact relation between visited and signed full fibers. Direction 4 replaces each lambda by a no-larger Lambda using actual endpoint widths. For p,q<=1 and a=arccos p, b=arccos q:

$$\Lambda=0\quad\text{if }a+b\ge e,$$

and otherwise

$$\Lambda=\frac12\left[\frac{2pq-\cos(e)(p^2+q^2)}{\sin(e)}-p\sqrt{1-p^2}-q\sqrt{1-q^2}-e+a+b\right].$$

The signed full length may be negative on some fibers. Its integral is not the area of a connected full-turn body; the empty-fiber correction and possibly disconnected components cannot be ignored. If both allowances vanish the same body completes; otherwise a genuine area margin or another feasible construction remains necessary.

## 6. Reproduction and stop rules

The committed `computer-assisted/check_four_directions.py` passed all prescribed tests in about 0.01055 seconds internally and 0.605 seconds including subprocess startup, under a five-second cap. D1--D3 use exact rational arithmetic. D4's numerical integration is diagnostic, with its theorem proved in the note. Source and result identities are in `computer-assisted/four-direction-checks.json`.

No untrusted optimizer output or unsupported external ambidextrous bound is a premise. Negative results from earlier repair, averaging, midline, face-matching, span and occupancy tests remain active controls. Stop a proposed mechanism when one of them refutes it; do not spend another pass improving constants on an already adequate obstruction.

The research has not reached a general proof. Keep PR #3 draft and preserve that distinction in every status report.
