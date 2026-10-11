# Hypothetical rational bends have enormous algebraic-frequency degree

This is an unconditional consequence of the ultradeep rational-angle exclusion and elementary cyclotomic theory. It concerns the analytic contact-model crossing, not the unrestricted global phase transition.

Assume hypothetically

    beta/pi = p/q

in lowest terms. By `ULTRADEEP_RATIONAL_EXCLUSION.md`,

    q >= Q0
      =120960480401807934322756058341844601463578189551623733657668053196745441803.

Define

    mu^2 = 3/(4 sin(beta)^2)-1,

and

    kappa^2 = (1-p/q)^2/4 * (1+3/sin(beta)^2).

These are the forward hyperbolic and reverse oscillatory algebraic frequencies.

## 1. Their squares generate the real cyclotomic field

Because p/q is reduced,

    exp(2 i beta)=exp(2 pi i p/q)

is a primitive q-th root of unity. Hence

    [Q(cos 2 beta):Q] = phi(q)/2.

Also

    sin(beta)^2=(1-cos 2 beta)/2,

so

    Q(sin(beta)^2)=Q(cos 2 beta).

The defining formulas are invertible rational transformations:

    sin(beta)^2 = 3/[4(mu^2+1)],

and

    sin(beta)^2
      =3/[4 kappa^2/(1-p/q)^2-1].

Therefore

    Q(mu^2)=Q(kappa^2)=Q(cos 2 beta),

and consequently

    deg_Q(mu), deg_Q(kappa) >= phi(q)/2.              (1)

The elementary totient inequality

    phi(n) >= sqrt(n/2)

gives

    deg_Q(mu), deg_Q(kappa) >= sqrt(q/8).

Using q>=Q0 and exact integer square-root arithmetic,

    deg_Q(mu), deg_Q(kappa)
      >= 3888452140662913159824188222522713815.       (2)

Thus each frequency would have algebraic degree at least about 3.888 x 10^36.

## 2. The three numbers 1, mu, kappa are Q-linearly independent

The relation between the frequencies is

    kappa^2=(1-p/q)^2 mu^2 + (5/4)(1-p/q)^2.          (3)

Suppose

    a+b mu+c kappa=0

with rational a,b,c, not all zero.

If b=0 or c=0, (2) immediately contradicts rationality of the remaining frequency. Otherwise write kappa=A+B mu with rational A,B and B nonzero. Substitution in (3) gives a polynomial equation of degree at most two for mu:

    [B^2-(1-p/q)^2] mu^2
      +2AB mu
      +A^2-(5/4)(1-p/q)^2=0.

It cannot vanish identically: the linear coefficient would force A=0 or B=0, while the constant term rules out A=0 and B=0 was already excluded. Hence mu would have degree at most two, contradicting (2).

Therefore

    1, mu, kappa

are Q-linearly independent.

## 3. Relation to algebraic-power conjectures

With the algebraic base -1, the two constants

    exp(mu (p/q) pi)=(-1)^(-i mu p/q),

    exp(i kappa pi)=(-1)^kappa

are algebraic powers with algebraic exponents. The exponent set

    1, -i mu p/q, kappa

is Q-linearly independent.

A standard equivalent formulation of the classical Gel'fond/Schneider algebraic-power conjecture predicts that, for an algebraic base alpha not 0 or 1, alpha^beta_1,...,alpha^beta_m are algebraically independent whenever 1,beta_1,...,beta_m are Q-linearly independent algebraic numbers. This remains conjectural in general.

The very large algebraic degrees in (2) therefore do not make the needed algebraic-independence statement a known low-degree case. Existing structured-power theorems guarantee independence among some powers alpha^(gamma^j), but do not identify the specific pair of exponents above.

This does not prove that the sofa irrationality problem is equivalent to the Gel'fond conjecture. It pinpoints another direct route that reaches a standard open algebraic-independence frontier.
