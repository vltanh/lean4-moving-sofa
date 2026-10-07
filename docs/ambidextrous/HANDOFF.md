# Ambidextrous sofa research — start a new session here

**Primary goal: unrestricted optimal value. It is not proved.** The signed weighted one-turn subproblem is now proved in the written chain WV2, and LF1 proves the ordinary-area bound for bodies with two horizontal hull faces longer than one. The remaining short-face class is not covered. Unrestricted uniqueness is deferred.

Repository: `vltanh/lean4-moving-sofa`.
Branch: `research/ambidextrous-pen-and-paper`.
Draft PR: #3; live base at this update: `main`.
Latest substantive review before this handoff: `9e27db0b73021820a21991b0ac45f654a38c7682`.
Always query the live branch and read intervening changes before continuing. Do not reset the base to the old paper branch.

## 1. Instructions and verification status

Prefer pen-and-paper proofs. Only short computer checks are authorized: new invocations are capped at 30 seconds, preferably external five/ten-second limits. No large search, multistart campaign or repeated refinement without a new instruction. A timeout is unfinished work, not evidence.

Commit substantive positive and negative findings frequently with `[skip ci]`. **No CI, Lean/Lake compilation, dependency installation or manuscript build.** Keep edits under `docs/ambidextrous/`, refresh blob SHAs, and preserve concurrent work. Keep PR #3 draft while unrestricted optimality remains unproved.

All mathematical statements below are written and self-reviewed, not independently refereed or kernel-verified. In particular the historical dependencies have not all been re-audited. Read [weighted-value-proof-review.md](weighted-value-proof-review.md) before treating the latest chain as infrastructure.

The known reference area is

$$M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.$$

For the value, an upper bound on one attained global ambidextrous maximizer suffices. Do not add unrestricted equality classification as a prerequisite.

## 2. The weighted one-turn value is now proved in writing

Read [one-turn-weighted-value.md](one-turn-weighted-value.md), then the critical new lemma [one-turn-visible-exposure-bound.md](one-turn-visible-exposure-bound.md).

The objective is

$$\Psi(U)=|U|-|N(U)|-W(U)/2,$$

where U is a normalized full-right-angle cap and N(U) is the entire positive-height niche, not clipped to U. WV2 proves

$$\boxed{\sup_U\Psi(U)=M/2.}$$

Its proof is not a universal adaptive-functional enclosure. It establishes unit curvature for an attained weighted maximizer and only then invokes the signed-roof/calibration chain on that admitted cap.

### New proof mechanism

For f(t)=h(t), g(t)=h(t+pi/2), use p=f'-g+1, q=g'+f-1, u=f''+f, v=g''+g.

[CG1](one-turn-curvature-guard.md) strengthens the sufficient endpoint-arm bound from two to sqrt(17)/2. The initial same-sign energy `(p-1/2)^2+(q+1)^2` is nonincreasing. CG2 also localizes possible excess to short endpoint windows, but these are intermediate statements now superseded at actual weighted maximizers by WV1's full unit-curvature conclusion.

[SE2](one-turn-single-excess-quarter.md) supplies at least one good quarter. HF's core gives `2 Psi>=sqrt(T^2+1)`. The actual feasible one-turn body U minus N has area Psi+T, at most Gerver's area. The six pinned reference enclosures give `G<=22199/10000`, hence `T<48/35`. Since the endpoint arms sum to 3T, one is below `72/35<sqrt(17)/2`, so CG1 makes its quarter good.

This is a legitimate use of Gerver's global area bound on a feasible one-turn body, not a transfer of unpenalized cap maximality. The rational enclosure source is pinned in SE. No Gerver source was compiled in this work.

Reflect so v<=1 globally. If u had excess, it would occur with p<0,q>1 in the initial positive-q component. After q crosses one, u<=1 throughout its entire future. On the subsequent p<0<q<1 interval, VE proves that both the second-wall tangency and the corner are globally visible. Their second-wall source fluxes are 1-v and -p. EB identifies total exposure with v, so `2v>=1-p`. Combining with v<=1 and WR gives p>=-1 and `v=(1-p)/2`.

Now `(1-p)^2+(1+q)^2` is nondecreasing. At q=1 with p<0 it exceeds five; at the later q=0 with p>=-1 it is at most five. This contradiction proves u<=1 too. AR4/SR1/AF3 then give WV2.

### Why this does not repeat the rejected saturation argument

The old claim that actual exposure=curvature forces exposure to attain an arbitrary local upper bound was false; see [exposure-saturation-gap.md](exposure-saturation-gap.md). VE instead proves a lower bound from globally visible pieces using one globally good quarter and the other quarter's good future.

The finite graph proof retains two source directions. It passes oriented tangent flux, not ordinary perimeter, and explicitly treats unique maximizing angles and zero-length plateau images. This is the main new continuum step requiring independent review. SP1's assumed saturated ODE is not used in the closure chain.

## 3. The earlier weighted infrastructure used by WV

PA2 gives attainment. ST1 gives roof>=1/2. WP1--WP2 select any prescribed weighted maximizer with summable finite facet errors. WR1 gives bounded open-quarter curvature and exact half-height end edges. AR7/AR5' give same-sign inequalities and control of later positive-q components.

PT3 proves a positive top face. TS1 then bounds full niche height by one half and gives niche containment; TS2 bounds both endpoint arms by 9/4. EB1 and EB.10 give exact limiting exposure=curvature and a vanishing sum of absolute finite defects.

TF proves positive wall-tangency heights and

$$N(U)\subset(a,b)\times[0,1/2],$$

where [a,b] is its top face. The symmetric surviving body S_U is genuinely ambidextrous and has `|S_U|=2 Psi(U)`, with zero clipping in this specific construction.

HF gives `T=W/2>1` and

$$U=V+([0,T]\times[0,1/2]),\quad W(V)=T,\quad H(V)=1/2,$$

with V convex, zero end heights and point top. Its stationary identity is `2 Psi(U)=Per(V)-T`. It is not a perimeter objective on arbitrary cores. These are weighted-maximizer statements, not properties of arbitrary ambidextrous maximizing hulls.

## 4. Actual ordinary-area theorem now available

[FL1](aligned-face-optimality.md) proves |S|<=M when the top and bottom faces of the common unit-span hull coincide in an interval of length at least one. Curvature, symmetry, contact order and full turns are not assumptions: the contained unit square forces full turns, and retained face endpoints confine the connected niche projections so the clipping term is zero. WV2 then bounds both caps.

[LF1](long-faces-force-alignment.md) shows that if both face lengths are strictly greater than one, alignment follows. Initial floor traces force the left endpoints to agree. Their common unit square forces full turns. Final floor traces force the right endpoints to agree. Consequently

$$\boxed{\text{both horizontal face lengths}>1\quad\Longrightarrow\quad |S|\le M.}$$

Thus a possible counterexample of area greater than M must have at least one horizontal face of length at most one. This is the primary remaining geometric class. No theorem says every maximizer has two long faces. The point-face examples approaching M preclude a uniform strict margin on the whole short-face class.

The general full-turn two-cap identity still has

$$|E|=\Psi(U)+\Psi(V)+G,\qquad G\ge0.$$

WV2 alone gives |E|<=M+G. A valid upper comparison for the remaining class must control G, prove a suitable improving operation, or avoid that decomposition. Partial-angle bodies still need actual angle coverage. The symmetric weighted-maximizer construction has not been proved to dominate all competitors.

## 5. Wing admission and its new negative control

[MW1](weighted-maximizer-canonical-wings.md) proves full height, constrained widths and outward-support agreement for the truncated canonical wings of S_U. It does not claim they survive omitted angles; that overstatement in the first draft was corrected in the next commit. All-angle wings do survive and have diameter one.

But [AO1](all-angle-wing-reference-obstruction.md) proves that inserting those smaller all-angle wings into the old fixed-cut core functional undercounts even the reference by at least

$$2(1-\cos\beta)^2/(\sin\beta\cos\beta)>0.$$

A new ordinary-area comparison cannot be inferred from their full height, diameter, survival, or SQ1 data membership alone. The successful WV proof does not use that false substitution.

The earlier canonical-wing identity remains `|S|-widehat W=N+U-B`, retaining negative winding, uncovered surviving material, and nonnegative deductions. No general paid correction budget is established.

## 6. Existing global restrictions and failed shortcuts

AW-W analytically excludes width<=2 for competitive bodies. AL1 bounds width by 2999/1020<3. AM2 has a complete all-width certificate for its stated steep extreme-height region. TE1 proves both competitive turns exceed 2 arctan(29/50)>pi/3. These are not an unrestricted sharp covering.

Do not repeat the unconditioned occupancy LP: its triple-only relaxation has a 2/3 fractional barrier, and pairs retain a 1/2 barrier. The user's preference is now short checks and hand proofs, not large renewed searches.

Mandatory negative controls remain AF4, GR1, AX1/SAT1, SAC2, SC3 and TR1: auxiliary enclosure and least-repair monotonicity fail even in some saturated near-candidate families. Small endpoint-height difference does not locate both endpoints near one half. PR #8/#9's one-turn maximality or qualitative entry cannot be imported into arbitrary two-turn bodies.

Original uploaded files and their diagnostics are preserved at the provenance checkpoints in the three package reviews. Do not overwrite imported author records with fresh results or call their floating-point observations exact certificates.

## 7. Short checks and current records

Run

```sh
timeout 5s python docs/ambidextrous/computer-assisted/check_core_arm_reduction.py
```

The latest record `computer-assisted/core-arm-checks.json` has 19 named checks, 48 initial-energy cases, six triangle cases, 36 corner-flux cases, 16 tangent-flux cases, 36 final-energy cases and three negative controls. Internal time was about 0.0021 seconds. Executed source matches Git blob `9f7b4170304b8409d8819f9941e47c54c9e20a67`.

These are exact arithmetic regressions, not verification of VE's continuum limit or the historical chain. The review records two short unsuccessful geometric diagnostics; no solver output is used to assert optimality. No new long computation was run.

## 8. Restart priorities

Read this handoff, [ROADMAP.md](ROADMAP.md), and the current review. The weighted value no longer needs to be re-maximized unless review finds a specific gap. The next actual upper-bound target is the short-face class left by LF1, preserving the clipping and motion hypotheses.

A result for one attained global ambidextrous maximizer suffices for the value. Do not assume it is a weighted cap maximizer. Do not turn a conditional family theorem into unrestricted closure. Keep equality and uniqueness deferred, scripts short, and commits frequent.

Refresh SHAs before every update. No CI, Lean/Lake compilation, dependency installation or manuscript build was used. PR #3 remains open and draft.
