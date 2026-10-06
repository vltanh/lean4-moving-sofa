# Continuation: distinguish a numerical coefficient from an effective threshold

This continuation starts from the six existing constants commits at
`4acfa639976ce41eab7ae77f2485591b9e3f6bb9`, based on the merged paper checkpoint
`a8f7719fd43fa91b223d9f6c0eb53594e5a95716`. Those commits already contain the
split-deficit budget, full-disk recovery, rational reference geometry, and
arithmetic for a candidate coefficient 84. They are inherited work, not new
results of this continuation.

PR #8 has been merged. This branch remains separate from the open coercive-route
PR #9 and will not rewrite the paper, faithful Baek proof, main uniqueness proof,
bridge, Challenge, or canonical solution. No Lean, Lake, CI, remote build, or
TeX compilation is permitted. New theorem source remains uncompiled.

## Goals

1. Audit the complete analytic implication to an explicit Hausdorff coefficient
   for all sufficiently near-optimal sofas, not just scalar arithmetic.
2. Improve the reference interior-ball ratio using Euclidean rather than
   coordinatewise estimates, and preserve the split deficit throughout recovery.
3. Keep terminal-angle error linear in the remaining deficit. It should affect
   the entry threshold, not inflate the leading square-root coefficient.
4. State the two directed estimates and special full-angle case separately.
5. Identify what would be needed for an effective pair (C, epsilon0), and do not
   confuse an explicit C with a computed positive epsilon0.
6. Record counterexamples, lower bounds, failed proof shortcuts, numerical checks,
   and the exact distinction between analytic arguments and Lean proof source.

## First additional refinement

The inherited reference proof uses roof Lipschitz constant 26 and interior-ball
ratio 1/28. In the low central region the coordinatewise estimate loses radius:
for a displacement v of norm at most w,

    26*abs(v.x) - v.y <= sqrt(26^2+1)*w < (261/10)*w.

Thus centering the ball at p+(0,(261/10)*w), with w=(10/271)*rho, fits the ball
inside the roof epigraph and inside Bbar(p,rho). This improves the ratio to
10/271. The wing and upper-central constructions have larger ratios, so they
are not the bottleneck. With k<=1001/500 and pi>3,

    sqrt(2*k^2+2/pi) < 59/20,
    (271/10)*(59/20) = 15989/200 < 80.

The forward coefficient remains below 26*(k+1)<80 after reducing the entry
threshold. These calculations suggest 80 instead of 84, but the geometric
adapters must be supplied before that is an assembled Lean theorem.

## Scope of 'global'

The intended numerical coefficient is uniform over ALL moving sofas sufficiently
near the optimum. It is not yet a numerical estimate valid for every possible
area deficit, and it does not specify the size of the near-optimal regime.
The existing compactness/uniqueness argument gives a positive entry threshold
only existentially. Neither unverified floating-point optimization nor shrinking
that existential threshold computes it.
