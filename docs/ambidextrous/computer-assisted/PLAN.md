# Computer-assisted route: explicit proof boundaries

Starting snapshot: `24ae299437e3a88dfd972accc5fd557f8ce9be89` (PR #3).
The user now explicitly authorizes numerical/computer-assisted work. The prior prohibitions on CI and Lean/Lake compilation remain in force. This pass runs local Python only, and does not run CI, Lean, Lake, or a manuscript build.

## Target and acceptance criteria

First attack the width gate: every normalized ambidextrous body of horizontal width at most two should have area strictly below Romik's candidate. A successful result must include a finite covering certificate and an independently executable verifier using exact rational arithmetic, or an analytic argument extracted from and checked against the search. A floating-point maximization result is only discovery data, never a global upper bound.

The selected directions will have rational sine and cosine, using

`cos(t)=(1-u^2)/(1+u^2), sin(t)=2u/(1+u^2)`

with rational u. Directions must be justified as actually visited by any body above the comparison threshold. In particular, sampling an angle beyond a possibly partial endpoint without a terminal-angle argument is forbidden.

The planned finite model keeps the two turns independent and imposes their hallway inequalities directly. It does not assume symmetry, curvature bounds, a contact ansatz, or equality between actual area and the adaptive functional. Bounds may use the total relaxed area, but any resulting finite-position witness must not be called a continuously feasible sofa without separate verification.

## Search versus verification

A numerical search may propose parameters, split choices, and polynomial contact cells. An accepted certificate must establish full parameter coverage, verify all pruning inequalities with outward/exact arithmetic, and reject malformed, incomplete, or understated claims. Unfinished frontiers and unsuccessful models must be recorded, not reported as a proof.

A rational strict bound such as 41/25 is useful because it is below the exact candidate value; that comparison must also receive an analytic or rational interval proof. The true optimum cannot generally be identified exactly by merely taking a finite mesh: a final local theorem or a genuine sharp analytic certificate is still needed.

## Prior work informing the design

Kallus and Romik, *Improved upper bounds in the moving sofa problem*, arXiv:1706.06630, Sections 2–3, formulate finite hallway-intersection relaxations and an exact-rational branch-and-bound scheme: https://arxiv.org/html/1706.06630v2 . The present two-turn computation is a new implementation to be checked, not an invocation of their one-turn numerical bound.

The existing branch's common-pose and canonical-angle reductions are potential coverage inputs, but the finite geometry and arithmetic will be written and tested separately. No independent audit of every historical note is claimed.

## Bounded checkpoints

1. Audit the finite geometric model and replay elementary examples.
2. Search both symmetric and unrestricted placements; record values as non-certified.
3. Implement rational area evaluation and covering verification, with negative controls.
4. Attempt a complete width-two certificate. If the attempted covering is unfinished, retain its frontier and state the exact remaining obligation.
5. Only after this gate is genuinely proved, combine it with the analytic route and attack curvature/enclosure. Do not close the PR on the strength of a numerical optimizer status.
