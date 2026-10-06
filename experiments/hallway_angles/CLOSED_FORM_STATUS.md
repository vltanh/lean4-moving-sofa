# Closed-form search: outcome and exact scope

This round addresses the request for an explicit closed form or a nonexistence proof. It adds a genuine restricted impossibility theorem, but does **not** supply either a closed form for the global beta_c or a theorem that no elementary expression for it exists. An implicit root definition and additional digits are not being presented as a solution to that request.

## New rigorous deduction

For the explicit forward contact equation in the hyperbolic regime, cos(beta) and cos(alpha) cannot both be algebraic, where alpha is the first switching angle. In particular beta and alpha cannot both be rational multiples of pi or both straightedge-and-compass constructible directions.

More strongly, when exp(i beta) is algebraic, the central half-angle T, exp(iT), exp(2mu T), sin T, cos T, tan T, and tanh(mu T) are all transcendental. The proof is in `CONTACT_TRANSCENDENCE.md` and uses classical Gelfond-Schneider and Lindemann-Weierstrass with their hypotheses checked explicitly. It is a mathematical deduction, not an inference from numerical recognition.

This does **not** imply that beta alone lacks a closed form. The contact equation also has a solution at beta=3pi/4, demonstrating that elementary beta values are compatible with the proved restrictions on the switching data. The result at the model crossing says at least one direction has transcendental coordinates; it does not identify which one. Nor does transcendence itself preclude elementary expressions involving exp/log.

## Algebraic simplification attempted

The exponential substitution z=exp(iT), w=exp(2mu T) converts the contact equation into P(z)w+Q(z)=0, with explicit coprime quadratics P,Q. Exact symbolic elimination verified the nonzero resultant and ruled out a cancellation of their common factors. The power z^(-2i mu) is not an algebraic function of z, by its infinite monodromy. These observations explain the obstruction to this direct polynomial reduction. They are not proofs excluding every conceivable transformation or Lambert-W representation.

## Bounded numerical recognition attempted

The model root was recomputed at 180 decimal digits and cross-checked at 260 digits. A total of 67 PSLQ calls examined polynomial relations of degree 1..8 for eight natural target quantities and three small bases built from pi, square roots, and logarithms. The maximum coefficient was 10^6 and the maximum iteration count was 3000 per call. No candidate relation was returned.

That is recorded as a failed bounded search, not as proof that no polynomial or elementary expression exists. A finite bound on degree, height, expression grammar, precision, or algorithm iterations cannot establish general nonexistence. Even a numerically returned relation would still require exact verification.

## Validation

All 11 new local tests passed with no skips. They check the exponential normal form, the exact resultant, the common-root contradiction, the nonzero exponential coefficient, and the monodromy factor. Separate numerical tests compare independent precisions and ensure the recognition routine can find known elementary examples.

The initial test run contained one failure from comparing expanded and factored symbolic expressions syntactically. The test was corrected to compare their exactly expanded difference with zero; no mathematical formula changed. The failure is retained in the result log.

The committed code and test blobs match the locally tested files. The tested optional dependencies are mpmath 1.3.0 and SymPy 1.14.0 with Python 3.13.5. Passing these tests does not formalize the transcendence proof or recheck the earlier geometric theorem drafts. No CI, workflow dispatch/rerun, or Lean build was attempted. Every commit carries `[skip ci]`.

From this directory, using an isolated environment:

    python -m pip install -r requirements-closed-form.txt
    python -m unittest -v test_closed_form_obstructions
    python closed_form_search.py --output /tmp/contact-closed-form-search.json

`results/closed-form-checks.json` records all search limits, common null outcomes, symbolic identities, source hashes, and the canonical full-search-record hash. `CLOSED_FORM_RESEARCH.md` gives the expression classes and source references; `CONTACT_TRANSCENDENCE.md` contains the proof.

## Remaining exact target

The desired beta-only claim is either a verified finite expression in a stated elementary/special-function class, or a proof of nonmembership in that class. Neither has been established in this round. Independently, identifying beta_model with an unrestricted global phase transition still requires the missing geometric/optimality arguments. No prior optimum ranges or phase-transition classifications are expanded here.
