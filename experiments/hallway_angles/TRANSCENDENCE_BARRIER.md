# Where the unconditional irrationality proof currently stops

This note records the number-theory barrier rather than presenting an open conjecture as a solved lemma. It concerns the analytic contact-model crossing, not the unrestricted global phase transition.

Assume hypothetically that beta/pi is rational in the certified crossing range. Then:

1. The hallway trigonometric data are algebraic.
2. `RATIONAL_BEND_FREQUENCY.md` proves the reverse frequency kappa is algebraic irrational.
3. Gelfond-Schneider therefore makes u=(-1)^kappa transcendental.
4. The forward contact equation gives an algebraic relation between

       z=exp(iT),  w=exp(2mu T),

   with algebraic coefficients, namely P(z)w+Q(z)=0.
5. Classical Gelfond-Schneider/Lindemann-Weierstrass also force z,w and the switching data to be transcendental.

The missing contradiction would have to control **algebraic dependence among these already-transcendental quantities**.

## Why ordinary Four Exponentials is not enough in the direct setup

For

    x1=i*pi, x2=i*T,
    y1=1, y2=-2i*mu,

the four exponentials are

    -1, exp(2mu*pi), z, w.

Gelfond-Schneider already makes exp(2mu*pi) transcendental, while the contact theorem makes z and w transcendental. The Four Exponentials Conjecture only says that at least one of these four values is transcendental. Its conclusion is therefore already satisfied and yields no contradiction.

This does not prove that no ingenious use of Four Exponentials could help after a different reformulation. It shows that the direct 2x2 application suggested by the contact relation is too weak.

## Relation to known open algebraic-power problems

If one additionally assumed T/pi were algebraic, then z and w become two algebraic powers of the algebraic base -1 with algebraic, Q-linearly independent exponents. Their algebraic dependence would be exactly the kind of phenomenon addressed by the classical Gel'fond/Schneider algebraic-independence problems for algebraic powers.

General statements asserting algebraic independence for arbitrary Q-linearly independent algebraic exponents remain conjectural. Known results prove substantial special cases and large-transcendence-degree estimates, but not the general two-exponent statement needed here.

Thus even the extra hypothesis that T/pi is algebraic does not reduce the problem to elementary Baker-style linear forms in logarithms.

## Current unconditional and conditional endpoints

Unconditionally:

- beta_model/pi cannot have reduced denominator below the exact bound in `DEEP_RATIONAL_EXCLUSION.md`.
- beta and the switching direction cannot both have algebraic trigonometric coordinates.
- a hypothetical rational beta forces transcendental switching data and an algebraic-irrational reverse frequency.

Conditionally on Schanuel:

- beta_model/pi is irrational.

No claim is made that Schanuel is logically necessary. The point is that the most direct remaining route asks for algebraic-independence information of a type that classical one-variable transcendence theorems do not presently provide.

## Literature landmarks

The relevant landscape includes:

- Gel'fond's 1949 algebraic-independence results for algebraic powers and later extensions by Chudnovsky, Philippon, Diaz, Nesterenko, Brownawell, Waldschmidt, and others.
- The Six Exponentials Theorem, which is unconditional but only forces at least one transcendental value in a larger grid.
- The Four Exponentials Conjecture and stronger variants, which remain open.
- Schanuel's conjecture, which gives the needed transcendence-degree control in the conditional argument.

A publication should cite primary or standard survey sources for these results; web searches in the research session are not substitutes for the final bibliography.
