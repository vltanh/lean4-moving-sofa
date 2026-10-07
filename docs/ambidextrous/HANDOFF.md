# Ambidextrous sofa research — current handoff

**Neither general full-turn nor partial-turn optimality is proved.** The user's latest instruction was to commit four alternative research directions and try all of them. That first pass is complete: one structural finite reduction, a failed constant-weight dual, a verified finite-angle box exclusion, and a general width-aware partial-completion allowance. None is a global sharp covering or a proof of continuum maximizing-hull regularity.

Repository: `vltanh/lean4-moving-sofa`.
Branch: `research/ambidextrous-pen-and-paper`.
Draft PR: #3, base `main`.
Latest substantive review: `b6e766e1e49c85863c424b854e73e2fcf87b2d63`.
Always query the live head and preserve intervening work.

## 1. Read first

Read [four-direction-first-pass-review.md](four-direction-first-pass-review.md), [four-direction-research-plan.md](four-direction-research-plan.md), and [ROADMAP.md](ROADMAP.md). The four attempt notes are linked in the review. The older proof files remain intact; the review is not independent verification of their entire chain.

The user objects to accumulating increasingly narrow family lemmas while the global problem remains unchanged. A new result should eliminate a possible maximizing configuration, establish a correctly signed universal comparison on its stated domain, or reduce the problem to a complete smaller class. Do not count another reference-family calculation as global progress merely because its constants improve.

Prefer hand proofs. Short computations may reject a proposed implication or test an attack direction: preferably an external five/ten-second cap, at most 30 seconds per invocation. No long search or repeated refinement without a new instruction. **No CI, Lean/Lake compilation, dependency installation or manuscript build.** Commit substantive positive and negative findings with `[skip ci]` under this directory. Keep PR #3 open and draft while the global theorem is open. Unrestricted uniqueness is deferred.

## 2. Four directions: current outcomes

### D1 — maximizing-body structure through actual finite charts

[direction-1-critical-face-reduction.md](direction-1-critical-face-reduction.md) reuses Notes 21, 53 and 54 instead of re-deriving their existing balance equations. Active geometric constraints and hidden boundary are real obstructions; no multiplier is dropped.

A feasible critical direction with zero first variation and positive Hessian work excludes a local maximum. A quadratic polynomial on a compact polytope has a maximizing representative at a vertex or at a unique stationary point on a face with negative definite restricted Hessian. Singular stationary ridges can be followed to lower-dimensional faces. For rational finite geometry this produces finitely many rational candidates.

The exact connected two-hallway test has a balanced saddle of area 25/98 and maximum 125/392 on its parameter box. It is finite-angle data, not a complete moving sofa. **Not proved:** a uniform family of such improving directions at an arbitrary noncandidate continuum maximizer, or the full curvature/injectivity theorem.

### D2 — coupled duality with overlap counted once

[direction-2-overlap-safe-duality.md](direction-2-overlap-safe-duality.md) uses nonnegative forbidden-area weights with total pointwise charge at most one. The exact four-hallway test shows that unweighted swept areas give a false upper bound, and even optimal constant weights leave a strict gap 809/16800. At the reference every finite collection of lower niche triangles has a common positive-area region, forcing its scalar weights to sum to at most one. More angles do not cure this unsplit-weight obstruction.

**Reject:** one global scalar weight per quadrant as the sharp union accounting. **Retain:** spatial allocations, especially robust allocations valid for all parameters in a box. This does not reject all dual or injectivity approaches. The universally sharp spatial certificate is missing.

### D3 — complete finite-angle branch exclusion

[direction-3-robust-finite-angle-box.md](direction-3-robust-finite-angle-box.md) encloses every body in an eight-offset box by a fixed outer rectangle minus robust forbidden quadrants. The offsets vary independently by 1/20 around the displayed supports. The exact remaining area is 709/480<8/5<M, by a short hand integration and two independent rational algorithms.

This excludes a whole parameter region, not samples. Increasing the radius to 1/10 gives upper bound 117/70 and is not excluded by that test. **Not proved:** a full parameter covering, a new global upper bound, or a sharp residual neighborhood theorem. Disconnected finite envelopes can safely be counted for an upper bound; they cannot be promoted to actual feasible sofas.

### D4 — joint area/angle bound retains actual endpoint widths

[direction-4-width-aware-completion.md](direction-4-width-aware-completion.md) computes the exact first-wall deletion allowance for strips of widths p,q<=1 separated by a missing angle e<pi/2. With a=arccos p, b=arccos q, the allowance is zero when a+b>=e. Otherwise

$$\Lambda(p,q;e)=\frac12\left[\frac{2pq-\cos(e)(p^2+q^2)}{\sin(e)}-p\sqrt{1-p^2}-q\sqrt{1-q^2}-e+a+b\right].$$

The proof is polar-coordinate geometry over the entire angle interval. It reduces to CC's tan(e/2)-e/2 at p=q=1 and is never larger. With the actual incoming and outgoing strip widths it replaces the two worst-case CC allowances in the signed-fiber area bound. Two zero allowances complete the same body without deletion. Positive allowances still need payment by a proved area deficit; arbitrary frame changes and connectedness after deletion are not assumed.

## 3. The unchanged global mathematical boundary

For actual compatible full-turn caps, with nonempty envelope fibers,

$$|E|=\Psi(U)+\Psi(V)+G,\qquad\Psi(U)=|U|-|N(U)|-W/2,$$

where N is the entire positive niche. The written weighted theorem claims sup Psi=M/2, with its long independently unverified PA/WP/WR/AR/PT/TS/EB/TF/HF/CG/SE/VE chain. Defining Delta=M/2-Psi gives

$$\Delta(U)+\Delta(V)-G=M-|E|.$$

Thus the global clipping inequality is exactly the missing full-turn optimality theorem, not an independently known lemma. AS's aggregate bound is stronger and also unproved globally. SR/AF's function-space calibration does not itself enclose arbitrary sofa area.

PD/PS reduce the full-turn supremum to saturated positive opposite-end faces; the class need not attain its supremum and has reference-area limits. There is no uniform strict gap for that whole class. FAS, RS, CW and conditional tail-transfer results retain their stated frame, curvature and geometric hypotheses.

## 4. Minimum-width ideas and negative controls remain relevant

The supplied minimum-width package is reviewed in `minimum-width-package-review.md`; its original archive hash is `21bc2d3b71b1deac325b94faca87d1eaac3d0849a012a0d689049f026f6eeff8`. MF changes the frame without dilation, makes face intervals overlap and gives

$$|E|=\Psi(U)+\Psi(V)+G_s,\qquad G_s=T_s+C_s-sW.$$

**The universal sign G_s<=0 is false.** `minimum-width-positive-slack-counterexample.md` proves the scaling law G_s/s -> 2T-W and a genuine stadium family with G_s>3s/4 for 0<s<=1/256. `near-reference-positive-minwidth-slack.md` gives positive G_s at actual global minimum-width frames with areas strictly below and arbitrarily near M. Do not spend another pass proving the false sign shortcut. The deficits must be kept.

`minimum-width-face-overhang-budget.md` gives a conditional regular-cap decomposition and aligned-short-face subunit-span theorem. SM/SB prove the reference-scale margin and a safe bridge only for their specified actual-hull class, not all nearby hulls. Original package files and author outputs remain preserved separately from reviews and replay outputs.

The partial-turn package archive hash is `03dffee9b89a6cecb359b8b5c49d6284952f466bc34f7a3a21ceaa28636b1a81`. CC's signed completion identity retains Z=integral(-ell_full)_+ and the possibility of disconnected full envelopes. A componentwise bound by M does not bound the total by M. D4 sharpens the allowance, not this outstanding global area comparison.

Retain all prior failure controls: scalar occupancy fractional barriers, hidden outer edges, nonzero normal-cone terms, body/cap averaging, curvature-repair and face-filling failures, common-background and half-height obstructions, lost span after hull reflection, and affine normalization failure. None is erased by a successful finite numerical test.

## 5. Reproduction and restart

Run the committed `computer-assisted/check_four_directions.py` under an external five-second cap. D1--D3 are exact rational calculations; D4's nine floating-point quadratures are diagnostic checks of a separate hand proof. The retained run took about 0.01055 seconds internally, 0.605 seconds including subprocess startup, with return code zero. Source Git blob: `65a619e742b44eeea3ebb0ed0bb544ec845f0566`. The committed record is `computer-assisted/four-direction-checks.json`.

The most concrete next attempt combines D1 critical faces and D3 whole-box certificates, using D2 spatially allocated union accounting. Specify a complete bounded geometric region, certify its exclusions and state the residual exactly. D4 can be inserted when a branch has partial endpoint widths. No complete global covering or continuum critical-cone reduction has yet been carried out.

All new and historical written arguments remain self-reviewed. Do not state that the four attempts closed the frontiers or that a finite outer envelope is an actual moving sofa.
