# A reproducible two-sided intrinsic full-Q estimate

This note closes the coefficient question to a useful numerical interval, not
an exact optimum. The mathematical reductions are analytic and require review;
the operator and trial-energy inequalities have been recomputed by exact
outward interval arithmetic. No Lean, Lake, CI, or manuscript build was run.

## 1. The coefficient being bounded

Let xi=(K,B,D) range over the enlarged continuously feasible right-angle triple
domain, let M=|G|, and Delta=M-Q(xi). Define

    d_tr(K,K_G)=inf_s d_H(K,K_G+(s,0)).

All distances are Euclidean cap distances. Put

    C_Q^*=lim_{eta down to 0} sup_{0<Delta<=eta} d_tr(K,K_G)/sqrt(Delta).

The supremum includes all feasible triples, not just the zero-first-variation
face. The monotone limit exists as an extended real number; the upper bound
below makes it finite. The same definition restricted to L=0 is the face
coefficient. Neither is the constant for fixed midpoint normalization, nor the
constant for arbitrary original sofas measured by their area deficits.

The result is

    461/500 < C_Q^* <= 93/100,                                 (1)

and the same two bounds hold for the face coefficient. The interval has width
0.008. No attained optimizer, unique critical mode, or optimal closed form is
claimed.

## 2. Executed all-pairs upper certificate

For continuous f with f(pi/2)=0 the exact translation quotient is

    inf_s ||f-s*cos||_infinity
      =sup_{t,u} |cos(u)f(t)-cos(t)f(u)|/(|cos(t)|+|cos(u)|),    (2)

excluding the zero denominator. One-dimensional closed-interval intersection
proves the formula; angles with zero cosine impose only the already satisfied
condition f(pi/2)=0. The angle-zero constraint bounds possible translations,
so the minimum is attained.

The two forced auxiliary penalties of note 18 give a positive rank-two update
of the four-residual Hilbert-space energy. Its inverse computes the norm of
every functional in (2) exactly. The committed all-pairs program integrates
cross kernels analytically and encloses the resulting 2-by-2 inverse over the
ENTIRE Gerver parameter box and the ENTIRE angle-pair domain.

A complete run with target 93/100 exhausted all 21 unordered pairs of the six
analytic angle regions:

    290591 visited boxes,
    145306 accepted leaf rectangles,
    zero failures and zero remaining frontier.

The largest accepted squared upper endpoint is the exact rational

    535347164580060136196379395 / 618970019642690137449562112
      < (93/100)^2.

Every box covers the full phi/theta enclosure. Dyadic angle subdivision does
not turn a sampled angle test into a certificate: the interval evaluation
covers the complete angle rectangle, and the replay verifies the covering
binary forest, including its endpoints, disjoint interiors, and all root areas.
An initial 250000-visit run left 21 boxes and was correctly inconclusive.
The larger run was subsequently regenerated and its invariant receipt matched.

On L=0 this proves

    d_tr(K,K_G) <= .93*sqrt(Delta).                            (3)

The certificate bounds a relaxation of the feasible critical face, so its
acceptance does not assert that every extremizing residual is feasible.

## 3. Nonzero first variation: a finite-deficit theorem

The endpoint-slack estimates in note 19 remain valid. In the completed-square
rank-two formula, the midpoint evaluation's affine slack response has sensitivity
at most 1/2. The response for the quotient functional (2) is a weighted difference
of two such responses; dividing by |cos(t)|+|cos(u)| preserves that same bound.
Thus the new all-pairs estimate and the old sensitivity certificate combine as

    d_tr(K,K_G) <= .93*sqrt(Delta)+(1/2)*max(ell_B,ell_D).

The active measure density lower bound, L2 derivative bound, and endpoint
averaging give max(ell_B,ell_D)<=16*Delta^(2/3) for Delta<=1/512. Consequently

    d_tr(K,K_G) <= .93*sqrt(Delta)+8*Delta^(2/3),
                  0<Delta<=1/512.                            (4)

At Delta=0 the original coercivity gives zero cap distance, without dividing
by Delta. In particular

    Delta<=10^(-18)  ==>  d_tr(K,K_G)<=.94*sqrt(Delta),          (5)

since .93+8/1000=.938<.94. More generally each C>.93 is valid on the explicit
Q-deficit range

    0<=Delta<=min(1/512,((C-.93)/8)^6).

Taking Delta down to zero in (4) proves the upper bound in (1). The old .98/.99
results concerned prescribed midpoint translation; the sharper .93/.94 here
permit the best horizontal translation. They are different normalizations.

## 4. Rebuilt continuously feasible lower family

The previous note 23 named a trial program and rational coefficients that were
not actually committed. This continuation reconstructs and publishes a new
trial in `critical_cone/feasible-trial-data.json`, rather than pretending those
missing bytes were available.

It uses the same analytically checked support construction: a harmonic first
normal gap, seventeen Hermite nodes on [phi,pi/2], exact matching at phi and
c=pi/2-theta, and reflection. The new q is exactly

    10934514869/10000000000.

All thirty-one free coefficients are rational and committed. The auxiliary
supports coincide with the cap on containment contact arcs, are harmonic on
zero-curvature gaps, and cancel the paired wall perturbations on active arcs.
The derivative at c is fixed by harmonic interpolation, not rounded. The
convexity, containment, and inactive-wall argument of corrected note 23 then
gives actual feasible triples for every sufficiently small positive amplitude.
Their first-variation slack is exactly zero and

    Delta_tau=tau^2*E_trial.

The exact interval program `certify_feasible_trial.py` integrates all SIX
residual energies across the whole reference box. Its 32768-cell run gives

    1.1729403846 < E_trial < 1.1747669267 < 147/125.

The extreme support changes are both -tau, so every horizontal translation
has cap error at least tau. The final rational check is

    (461/500)^2*(147/125)=31240587/31250000<1.

Therefore the feasible family has ratio greater than 461/500 and tends to
Gerver as tau decreases. This proves both lower bounds claimed in (1).
The numerical amplitude at which all geometric constraints hold is not needed
for this asymptotic statement; its existence is established by the support-
measure and endpoint-gap argument, not inferred from the energy computation.

## 5. Replay instructions and scope

In `docs/stability/constants/critical_cone`, run:

    python replay_translation_quotient.py --expect translation-quotient-replay.json
    python certify_feasible_trial.py
    python check_critical_certificate.py

The first command RECOMPUTES the interval bounds before comparing the invariant
receipt. Its optional --input mode only checks an existing generated receipt's
cover and metadata and must not be advertised as numerical recomputation.
The second reproduces the full trial-energy enclosure. The third rechecks the
.98 midpoint/sensitivity certificate and its arithmetic/negative controls.

The canonical sorted all-pairs leaf digest is
`5dc8a0c99f0800e5c08b47f19837f5da410a7b67e59530206f7326181feee71f`.
The small committed receipts identify all source hashes. Full generated leaves
can be regenerated rather than adding a roughly 50 MB JSON file to Git.

The computer verifies the displayed analytic formulas with exact arithmetic;
it does not verify the functional-analytic reductions, reference contact
geometry, or Lean proofs. No float decides interval acceptance. The geometric
family proof and the endpoint-slack argument should be reviewed independently.

## 6. Effective consequence, and the boundary not to cross

For feasible Q triples, (5) is already an unconditional effective theorem on
its stated domain. For example, d_tr>=r implies

    Delta>=min(10^(-18),(r/.94)^2).

For a Ki cap the canonical inequality Q>=A transfers the small-deficit estimate
to M-A. For an arbitrary original sofa, assigning a suitable triple with the
required area comparison is a separate problem. The number 10^(-18) is NOT a
numerical entry threshold for the unrestricted actual-sofa theorem. The entry
work must not replace that missing implication by renaming Delta as epsilon.
