# A 74-digit denominator exclusion for rational bend angles

This is the strongest current unconditional beta-only arithmetic result for the analytic contact-model crossing. It does not identify that model crossing with the unrestricted global phase transition, and it is not an irrationality proof.

The standalone 512-bit checker `ultradeep_rational_exclusion.py` proves

    L < beta_model/pi < U,

where

    L =
    91134299355359730620075344463050084054257690016349718007751311644708802731
    /
    120025694476154505239302526413929185366049268162850319859865885681419706546,

and

    U =
    709773526022809658397345482386942267278154400754731831515505447771213258
    /
    934785925653429083453531927915416097528921388773413797802167515325735257.

The exact signed-area gap is positive at L and negative at U. The two fractions are Farey neighbours:

    numerator(U)*denominator(L)-numerator(L)*denominator(U)=1.

Therefore every reduced rational p/q in the open interval has

    q >= denominator(L)+denominator(U)
      = 120960480401807934322756058341844601463578189551623733657668053196745441803.

Consequently

    beta_model/pi=p/q in lowest terms
      ==> q >=
      120960480401807934322756058341844601463578189551623733657668053196745441803.

This is about 1.21 x 10^74.

## Exact endpoint signs

At L the checker obtains the positive interval

    [513691,526491] / 2^512.

At U it obtains the negative interval

    [-939971207,-939960594] / 2^512.

Thus the signs are not inferred from rounded decimal values.

## Method

The checker uses:

- a 512-bit fixed dyadic denominator;
- exact rational Machin-series bounds for pi;
- Taylor sine/cosine after exact quarter-angle reduction;
- Taylor sinh/cosh on the relevant unit interval;
- interval Newton for the contact parameter T;
- exact evaluation of the signed-area difference;
- the Farey-neighbour denominator theorem.

No binary floating point, numerical optimizer, external trig library, or polygon computation is part of the proof.

The code was prototyped with an independent exact-dyadic implementation in the research runtime. The repository runtime could not be cloned because DNS resolution of github.com failed; no CI or Lean build was attempted.

## Why this still cannot prove irrationality

A finite rational bracket can exclude only a finite denominator range. If beta_model/pi were rational with denominator larger than the displayed bound, the result would remain logically compatible with that possibility.

Arbitrary-precision continuation can make the bound enormous but cannot turn this method into an irrationality theorem in finitely many steps. A structural transcendence argument is still required.
