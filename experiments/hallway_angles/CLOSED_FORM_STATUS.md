# Closed-form status: conditional non-elementarity, not just irrationality

**Current strongest arithmetic result:** assuming Schanuel's conjecture, the analytic contact-model crossing beta_model has no expression in the full algebraic/exp/log field L. This is a conditional mathematical proof draft requiring independent review. It is not a proof of Schanuel, unconditional non-elementarity, or identification of beta_model with the unrestricted geometric transition beta_c.

The new argument does not compute additional digits, enlarge a denominator bound, or call an implicit root definition an elementary formula.

## 1. The exact expression class now excluded conditionally

L is the smallest algebraically closed subfield of C containing the algebraic numbers and closed under exp and all complex logarithms. It contains every finite expression built from algebraic constants, arithmetic, arbitrary algebraic roots, exponentials, logarithms, circular/hyperbolic functions and their ordinary inverses. In particular pi, e, and familiar exp/log constants belong to it. No special inverse of the sofa equation is added.

`SCHANUEL_NON_ELEMENTARITY.md` proves

    Schanuel => beta_model not in L.

Since L is algebraically closed, this is equivalently transcendence over L. It excludes a polynomial equation for beta_model with elementary coefficients, not only a polynomial with rational coefficients. It is substantially stronger than beta_model/pi being irrational or exp(i beta_model) being transcendental over Q.

The theorem is stated for EVERY real simultaneous solution of the compact contact and area-equality equations on 2pi/3<beta<pi, 0<T<beta/2. The isolated model crossing in the earlier computation is one such solution; its decimal value and uniqueness certificate are not used by the non-elementarity proof.

## 2. What closes the previous gap

The existing branch already contained `ELEMENTARY_TOWER_LEMMAS.md` and the conditional algebraic-direction exclusion in `SCHANUEL_ALGEBRAIC_DIRECTION.md`. The new proof completes the elementary-bend argument, including directions whose coordinates are transcendental.

First anchor pi in the base of a finite reduced exp/log tower. If beta were elementary, the area equation would make exp(iT) algebraic over that tower with T adjoined. The contact equation then does the same for exp(2mu*T). Schanuel forces T and both exponentials into the original finite tower.

A minimal tower containing all the coupled data can end in only two ways:

- At a logarithmic last step, the real/imaginary multiplier comparison forces T to descend. Since pi is already in the base and the coefficient of beta in the area equation is nonzero, beta then descends too.
- At an exponential last step, mu can be reconstructed from two already-descended arguments. It determines exp(i beta) algebraically, so the contact coefficients descend. The coprime rational contact graph cannot support a nonconstant monomial substitution, forcing the remaining contact exponentials to descend; the area equation then forces the reverse exponential down as well.

Both cases contradict minimality. `COUPLED_CONTACT_CAPTURE.md` and `SCHANUEL_NON_ELEMENTARITY.md` give the complete reasoning rather than treating non-elementarity as a consequence of numerical evidence.

A proposed expression with at most m exp/log operations over Qbar and pi is already excluded by Schanuel in ranks up to m+5. This bounds the conjectural hypothesis required for any specified finite expression; it does not prove those Schanuel cases.

## 3. The switching data are conditionally non-elementary too

`SCHANUEL_AUXILIARY_NON_ELEMENTARITY.md` extends the same conditional conclusion to

    T, alpha=beta/2-T, 2mu*T, K=k(pi-beta),

and to their exponential coordinates. The bend coordinates sin beta, cos beta, tan beta, exp(i beta), the normalized angle beta/pi, and the frequencies mu,k are also outside L.

These additional proofs use a relative Schanuel rank bound over a finite reduced tower and the exact nonsquare identity k^2=mu^2+5/4. No arithmetic classification of the common signed area is claimed. Not every derived constant is non-elementary: the matching amplitude 1/3 is elementary.

## 4. What remains unconditional

The earlier exact-arithmetic rational-angle exclusions, paired-direction transcendence results, and cyclotomic frequency-degree consequences remain recorded in their original files. They were not rerun or strengthened in this round. The strongest recorded finite denominator bound is of order 10^74; it remains a finite exclusion, not an irrationality theorem.

The monomial-graph lemma and algebraic identities used in the new proof are unconditional. The saturation/capture steps are not: they require Schanuel. Thus the full no-elementary-expression statement is still conditional, and no unconditional beta-only irrationality theorem is added here.

A bounded exclusion of rational multiples of pi does not by itself exclude every constructible or algebraic direction. Those broader classes are excluded by the new CONDITIONAL non-elementarity theorem, not by the Farey argument alone.

## 5. Validation and retained failures

All 15 new local exact-algebra tests passed with no skips. They verify fourteen symbolic identities, the nonzero resultant/pole factors, the frequency reconstruction, a nonsquare rational-function obstruction, and exact examples showing why the monomial lemma's hypotheses matter. The combined runner checks the two source Git blob hashes before executing the tests.

The first run had one syntactic-expression-equality failure. It was fixed by comparing the exact cancelled difference, with no change to the mathematics. This is recorded together with the other negative controls in `ELEMENTARY_DESCENT_LIMITS.md` and `results/elementary-descent-checks.json`.

These tests do NOT formally verify the tower proof, the auxiliary rank arguments, Schanuel, or any geometric optimality theorem. There was no CI, workflow run, or Lean build. No old full test suite or 512-bit root certificate was rerun.

From this directory, using the optional dependencies in `requirements-closed-form.txt`:

    python elementary_descent_algebra.py
    python -m unittest -v test_elementary_descent
    python run_elementary_descent_checks.py --output results/elementary-descent-checks.json

## 6. Reading order and remaining task

1. `SCHANUEL_NON_ELEMENTARITY.md`: the main conditional theorem and complete minimal-tower descent.
2. `COUPLED_CONTACT_CAPTURE.md`: rationalization, nondegeneracy, anchored towers, and the switching-data capture.
3. `SCHANUEL_AUXILIARY_NON_ELEMENTARITY.md`: the further switching/phase exclusions.
4. `ELEMENTARY_DESCENT_LIMITS.md`: necessary hypotheses, counterexamples, and the exact boundary of what is established.

The requested unconditional no-elementary-expression theorem remains unproved. The conditional conclusion now addresses that actual expression class, rather than substituting irrationality for non-elementarity. A verified elementary expression for this model root would contradict Schanuel, according to the proof draft. Independently, identifying the model root with a global geometric phase transition still needs the missing forward-optimality and unrestricted-comparison arguments.

## Primary source

Timothy Y. Chow, *What is a closed-form number?*, American Mathematical Monthly 106 (1999), 440–448, Sections 2–3: https://arxiv.org/html/math/9805045 . That source explains the number fields and reduced-tower approach; the explicit coupled-system descent above is given as a proof in this repository, not claimed to be a quoted theorem from Chow.
