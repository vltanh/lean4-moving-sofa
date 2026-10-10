# Review of the uploaded one-turn arm-reduction package

**Unrestricted optimality is not proved.** This note records the scope of the user's `one-turn-arm-reduction-package.zip`, the deductions checked in this session, and the distinction between written reductions, exact algebra checks, and floating-point diagnostics. The package does not establish its remaining endpoint bound.

Review baseline: `c29e55536c1338f8ba01a2089a5aca4349679a98`. Archive SHA-256: `a485d55950df0f6a9adf2a752e18ab973fbb883036fb4ae938cd3b0bfaf02302`. The uploaded note uses AR labels. The original four mathematical/diagnostic files are preserved byte-for-byte at `0b187ac80852234b65fe9046fc4eaf6cd4d25264`; the root packaging README remains in the supplied archive and review bundle. Two transcription mistakes in the first script commit were corrected before this provenance checkpoint.

| Original file | Verified Git blob |
|---|---|
| `one-turn-arm-reduction.md` | `c0a279d397694c419bab55b94a52eda11f559793` |
| `computer-assisted/one-turn-arms/README.md` | `630b09b9134ecf0a0d8af0da8d442b8598dd56f1` |
| `computer-assisted/one-turn-arms/check_one_turn_arm_reduction.py` | `8821609a8843ac8f63b8ef229bbf29bd97944110` |
| `computer-assisted/one-turn-arms/one-turn-arm-reduction-checks.json` | `c8fed348193b83bd3b587613e7ff6b720e79fc6a` |

## 1. The useful endpoint reduction

Let P be the attained maximum of the **signed** full-right-angle cap objective

$$
\Psi(U)=|U|-|N(U)|-W(U)/2.
$$

For the upper support h, write L=pi/2, f(t)=h(t), g(t)=h(t+L), p=f'-g+1 and q=g'+f-1. Let the horizontal projection be [x_L,x_R] and the top face [x_tl,x_tr] at height one. Then

$$
q(0)=x_R-x_{tl}-1,\qquad p(L)=1-(x_{tr}-x_L).
$$

The package derives the sharper same-sign consequence of weighted polygon inequalities:

$$
\rho_f=0,\quad\rho_g\le1/2\text{ on }\{p>0,q>0\},
$$

and the reflected statement on {p<0,q<0}. Combining this with WR1 gives

$$
q(t)\le\max(q(0),1/8),\qquad
p(t)\ge\min(p(L),-1/8).
$$

Consequently the endpoint hypotheses

$$
x_R-x_{tl}\le2,\qquad x_{tr}-x_L\le2
\tag{EA2}
$$

imply |p|,|q|<=1, hence rho_f,rho_g<=1. The signed-roof identity SR1 and existing AF3 calibration then give Psi<=M/2. The reference cap attains M/2.

**Value-only quantifier.** It suffices to prove EA2 for **one** attained global Psi-maximizer. Requiring it for every maximizer belongs to the package's stronger uniqueness equivalence. EA2 has not been established for even one maximizer by this review.

This is still a one-turn auxiliary problem. The two-turn area identity retains positive clipping, so P=M/2 alone would not prove unrestricted ambidextrous optimality.

## 2. Mathematical checks of the imported reduction

The endpoint formulas follow from the four support traces. The cap-area support integral cancels the two end-edge products against their atoms, retaining every half-height side contribution.

The AR7 neighboring-quadrant tests have the stated signs. The next companion-wall threshold satisfies v_plus-v0=tan(delta)(q_plus-T), with T=tan(delta/2). The first wall is completely hidden when p_plus>T and q_plus>T. Under the second stated condition the companion's exposed interval has length at most (2T-ell)_+. WP2 gives ell<=T+b; this is an inequality, not exact balance.

The passage to open same-sign sets has an elementary justification. Add a fixed quadratic to the uniformly semiconvex supports. A convex function's one-sided derivatives at x are bracketed by difference quotients at x-r,x,x+r. Uniform function convergence and uniform continuity of the limiting derivative on a slightly larger compact interval squeeze these brackets uniformly, first choosing r and then the sequence index. This proves the locally uniform derivative convergence needed to transfer strict sign margins. Summable WP errors and weak curvature-measure convergence then give AR7.

For propagation, on a positive-q component p'<=-1/2. If its selected endpoint has p>=0, every earlier p on that component is positive. AR7 improves this to p'=-1-q<=-1 and q'<=p-1/2. An initial component starts at p=1/2 and cannot increase q. A later component starts with p<=1 and q=0, allowing increase at most integral_0^(1/2)(1/2-u)du=1/8. If p<0 at the selected point, go back to its last zero and use q'<=-1/2. Reflection gives the other bound.

AR2 and AR4 depend on the branch's signed-roof and functional-calibration proofs. This review checks their hypotheses and identifications; it is not independent verification of the full historical chain.

## 3. New finite shortening result: TS1--TS2

[one-turn-top-shortening.md](one-turn-top-shortening.md) turns the proposal's horizontal variation into a finite comparison. If the top face has length T>0, removing a horizontal segment of length 0<epsilon<T gives another admissible normalized cap U_minus. Let H_N(U) be the supremum height of its full niche. Then

$$
\boxed{\Psi(U_{\rm minus})-\Psi(U)
\ge\varepsilon\bigl(H_N(U)-1/2-\varepsilon/2\bigr).}
$$

The proof uses N(V)+[0,epsilon]e_x contained in N(V+[0,epsilon]e_x), followed by one-dimensional interval growth and Fubini. It requires no niche-area derivative, stable contacts, or curvature bound.

**TS1:** a global weighted maximizer with T>0 has H_N<=1/2. Together with ST1's half-height rectangle, this proves its niche lies inside its cap. A rational-direction support test then gives **TS2**:

$$
x_R-x_{tl}\le9/4,\qquad x_{tr}-x_L\le9/4.
$$

The threshold is **9/4, not two**. This leaves possible arms in (2,9/4], as well as the separate T=0 case. It does not establish EA2.

Reflecting such a cap and intersecting its two surviving bodies gives an actual connected full-turn ambidextrous body through the common midline, with

$$
|S_U|=2\Psi(U)+2\int\min(n,1-a)\,dx\ge2\Psi(U).
$$

Thus a positive-top weighted maximizing cap with Psi>M/2 would furnish a genuinely larger ambidextrous body. No such cap is constructed; the nonnegative clipping term is retained.

## 4. New analytic passage-time theorem: SP1

[one-turn-saturated-passage.md](one-turn-saturated-passage.md) solves the package's proposed piecewise ODE, without asserting that it governs maximizing caps. Starting at (p,q)=(1/2,q0), q0>=0, the first time tau(q0) at which q=-1/2 is strictly increasing. Its unique value tau=pi/2 occurs at the reference q0=1/(2sin(beta))-1.

For the standard quadrant, set x=-p, y=q. The system is x'=m(y), y'=-m(x), with m(u)=(1+u)/2 up to one and m(u)=1 thereafter. A separable conserved quantity gives explicit passage formulas on v in [0,1], [1,7/4], and [7/4,infinity). The low-q0 reverse-region case is handled separately. Differentiating these formulas proves monotonicity with no numerical grid premise.

This resolves the proposal's ODE-monotonicity question. It leaves the more important geometric hypotheses of its proposed saturated system unproved: the relevant niche-area derivative, exact exposure balance and activity in folded configurations. An explicit orbit is not a theorem that every maximizer follows it.

## 5. Executed checks, with their limits

The original script SHA-256 is `03ba9e809a5ecf4dc06fc3223ebb4bae793c3b7964ba3cc4d584231369e105b7`, matching the uploaded JSON. Its source was read first, and all parts A, B, C0, C, D, E were freshly executed unchanged. The original author's JSON was not overwritten. The new [review record](computer-assisted/one-turn-arms/review-results.json) reports local Python 3.13.5, NumPy 2.3.5 and SciPy 1.17.0, distinct from the uploaded environment.

The full replay reproduces the candidate and sampled propagation results and the two positive fine-grid A-F discrepancies. SP1's closed passage formula differs from the fifty sampled ODE times by at most about 1.09e-8. These comparisons have no certified continuum error bounds.

A separate [review checker](computer-assisted/one-turn-arms/review_checks.py) passed **23 exact symbolic identities**, **213 rational local-offset exposure cases**, and **200 interval-growth cases**, with two rejected sign/threshold controls. Its executed bytes match fetched Git blob `671fd75fc929f04e85eeb84937b57e7d09830a61`. These tests check algebra and finite instances; the analytic arguments supply the continuum statements.

Reproduce the exact checks using the committed review script. To include the replay comparison, first execute the unchanged original script with an output path, then pass that path with `--imported-run`. The full fresh output and checks are included in the review bundle, with hashes in the committed summary.

**Diagnostic qualifications.** AR8's examples are floating-point evidence, not exact constructed counterexamples. Part B does not enforce the entire cap boundary-value problem. Part D's random trajectories are not shot to enforce f(L)=g(0)=1, and the code directly uses the sampled offsets rather than first validating a circumscribed cap with those actual supports. Its samples therefore are not a verified family of cap realizations. Moreover floating-point intersections of nearly coincident lines and polygon boundaries can miss exposed lengths. The review's rational local-offset cases also explicitly do not claim global cap realizability.

Part E assumes the saturated law. SP1 proves the mathematical statement for that law, not the law's missing connection to geometry. No numerical optimizer output is promoted to a global bound.

## 6. Remaining optimality obligations

The imported endpoint reduction is useful; the endpoint condition itself is unproved. For value only, a successful next step could establish EA2 for one weighted maximizer, or justify the saturated exposure system with its required initial/sign and first-passage conditions. The T=0 case and the remaining long-arm interval under TS2 are explicit outstanding cases.

Even a sharp weighted one-turn theorem still needs a valid two-turn ordinary-area comparison controlling clipping and the exceptional face configurations. The direct anchored-certificate route remains separate; this review does not claim that the unpublished anchor follow-on bundle has been merged.

No CI, Lean/Lake compilation, dependency installation, or manuscript build was used. All changes are under docs/ambidextrous. The new proofs are written and self-reviewed, not independently refereed or kernel-verified. The primary goal remains the optimal value; unrestricted closure is not claimed.
