# Rational bends force an irrational algebraic reverse frequency

This is an unconditional arithmetic lemma for the analytic contact-model crossing. It does not identify that model crossing with the unrestricted global phase transition.

Let beta lie strictly between 135 and 140 degrees and suppose beta/pi=q is rational. Define the reverse oscillation frequency

    kappa = (1-q)/2 * sqrt(1+3/sin(beta)^2),

so that the reverse phase angle is K=kappa*pi.

## Lemma

Under these assumptions, kappa is an irrational algebraic number.

### Proof

Because exp(i beta) is a root of unity, sin(beta)^2 is algebraic, hence kappa is algebraic.

Suppose kappa were rational. Since q is rational and 1-q is nonzero, this would force

    1+3/sin(beta)^2

to be rational, and hence sin(beta)^2 to be rational. Therefore

    cos(2 beta)=1-2 sin(beta)^2

would be rational.

Now 2 beta/pi is rational. Niven's theorem for rational trigonometric values says that a rational cosine at a rational multiple of pi must belong to

    { -1, -1/2, 0, 1/2, 1 }.

But for 135 degrees < beta < 140 degrees,

    270 degrees < 2 beta < 280 degrees,

so

    0 < cos(2 beta) < cos(280 degrees) < 1/2.

None of the five possible rational values lies in that open interval. Contradiction.

Thus kappa is algebraic irrational.

## Consequences

Under a hypothetical rational bend at the model crossing,

    u=exp(iK)=(-1)^kappa

is transcendental by Gelfond-Schneider.

This removes the rational-kappa branch from the conditional argument in `SCHANUEL_RATIONAL_ANGLE.md`. It does not by itself contradict the crossing equations: the reverse area can contain the transcendental algebraic power u, and the forward side contains the separate transcendental contact quantities.

The direct Four Exponentials setup also remains noncontradictory: with x_1=i*pi, x_2=i*T and y_1=1, y_2=-2i*mu, three of the four exponentials are already known or expected to be transcendental. The conjecture's conclusion that at least one is transcendental therefore supplies no new contradiction in that direct arrangement.

This identifies the remaining obstacle as algebraic independence among several transcendental quantities, rather than individual transcendence.
