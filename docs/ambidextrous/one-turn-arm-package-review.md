# Review of the uploaded one-turn arm-reduction package

**Unrestricted optimality is not proved.** This note records the scope of the user's `one-turn-arm-reduction-package.zip`, the deductions checked in this session, and the distinction between a written reduction and a numerical check. The package is not evidence that its missing endpoint inequality has already been established.

Review baseline: `c29e55536c1338f8ba01a2089a5aca4349679a98`. Archive SHA-256: `a485d55950df0f6a9adf2a752e18ab973fbb883036fb4ae938cd3b0bfaf02302`. The package identifies its statements by AR labels. The prior session described other contributions as coming from Claude; this file records the actual uploaded bytes rather than independently attributing a generating model.

## 1. The useful reduction

Let P be the attained maximum of the **signed** full-right-angle cap objective

$$
\Psi(U)=|U|-|N(U)|-W(U)/2.
$$

For the upper support h, write L=pi/2, f(t)=h(t), g(t)=h(t+L), p=f'-g+1 and q=g'+f-1. Let the horizontal projection be [x_L,x_R] and the top face [x_tl,x_tr] at height one. Then

$$
q(0)=x_R-x_{tl}-1,\qquad p(L)=1-(x_{tr}-x_L).
$$

The package proves a sharper same-sign consequence of the weighted polygon inequalities:

$$
\rho_f=0,\quad\rho_g\le1/2\text{ on }\{p>0,q>0\},
$$

and its reflected version on {p<0,q<0}. Combining this with WR1 gives

$$
q(t)\le\max(q(0),1/8),\qquad
p(t)\ge\min(p(L),-1/8).
$$

Consequently the endpoint hypotheses

$$
x_R-x_{tl}\le2,\qquad x_{tr}-x_L\le2
\tag{EA2}
$$

imply |p|,|q|<=1, hence rho_f,rho_g<=1. The signed-roof identity SR1 and the existing AF3 calibration then give Psi<=M/2. The reference cap attains M/2.

**Value-only quantifier.** It is sufficient to prove EA2 for **one** attained global Psi-maximizer. Requiring it for every maximizer is needed by the package's stronger uniqueness equivalence, not by the current value-only milestone. The audit does not establish EA2 for even one maximizer.

This still concerns a one-turn auxiliary problem. The two-turn formula retains its positive clipping correction, so proving P=M/2 is not by itself unrestricted ambidextrous optimality.

## 2. What was checked mathematically

The endpoint formulas follow directly from the four support traces. The cap-area support integral cancels the two end-edge products against their atoms, so no half-height side contribution is omitted.

The AR7 neighboring-quadrant tests have the stated signs. In particular the next companion-wall threshold satisfies v_plus-v0=tan(delta)(q_plus-T), with T=tan(delta/2). The first wall is completely hidden when p_plus>T and q_plus>T. The companion's remaining exposed interval has length at most (2T-ell)_+ under the second stated condition. WP2 then gives ell<=T+b; this is an inequality, not exact balance.

The passage to open same-sign sets does not need the cited textbook theorem as a black box. Add a fixed quadratic to the uniformly semiconvex support functions. For a convex function, its one-sided derivatives at x are bracketed by difference quotients at x-r,x,x+r. Uniform function convergence and the uniform continuity of the limiting derivative on a slightly larger compact interval squeeze these brackets uniformly, first choosing r and then the sequence index. This proves the locally uniform convergence needed to transfer the strict sign margins. Summable WP errors and weak convergence of curvature measures give AR7.

For the propagation estimate, on a positive-q component one has p'<=-1/2. If its endpoint has p>=0, all earlier p on that component are positive. AR7 improves this to p'=-1-q<=-1 and q'<=p-1/2. An initial component starts with p=1/2 and cannot increase q; a later component starts with p<=1 and q=0, giving an increase of at most integral_0^(1/2)(1/2-u)du=1/8. If p<0 at the selected point, go back to its last zero and use q'<=-1/2. Reflection gives the other bound.

AR2 and AR4 additionally depend on the branch's signed-roof and functional-calibration proofs. This review checked their hypotheses and formula identifications, not an independent audit of the entire historical chain.

## 3. Numerical status and limits

The original script SHA-256 is `03ba9e809a5ecf4dc06fc3223ebb4bae793c3b7964ba3cc4d584231369e105b7`, matching the hash recorded in the uploaded JSON. Its local source was read before execution. A fresh run of the unchanged script has completed during this review; a separate replay record will preserve the local versions, output, and exact-check scope.

All imported computations use floating-point ODE integration, quadrature, root finding, or polygon intersections. Their results are not rigorous continuum certificates. In particular AR8's examples are numerical evidence, not exact constructed counterexamples. Part B checks only one direction of arm propagation on sampled trajectories; it does not impose the complete cap boundary-value problem or prove its converse by sampling.

Part D computes intersections of floating-point lines with a polygon-union boundary. Near-coincident lines may be missed by such a test, so a tiny reported exposure excess is not a proof of a wall-length inequality. The review instead checks the defining line identities exactly.

Part E assumes a saturated exposure law whose applicability to actual maximizers is unproved. Monotonicity of sampled passage times cannot substitute for the missing exposure law or a proof of monotonicity on an interval.

## 4. Direct continuation

Section 9's horizontal shortening is a useful **finite admissible comparison** when the top face has positive length. It can be used without differentiating the niche area: the Minkowski inclusion of the old and shortened full niches yields a quantitative shortening gain. A separate note supplies this argument and its precise hypotheses.

It does not resolve the zero-length top-face case or EA2. The earlier two-turn and winding corrections remain in force. The primary objective remains the optimal value, not uniqueness or another unlinked calibration.

No CI, Lean/Lake compilation, dependency installation, or manuscript build was used. Only files under docs/ambidextrous are being changed. The proofs remain self-reviewed and are committed for scrutiny.
