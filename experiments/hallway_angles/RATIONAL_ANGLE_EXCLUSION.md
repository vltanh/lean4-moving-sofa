# Rational-angle exclusions for the contact-model crossing

This note concerns the uniquely certified crossing of the analytic forward contact model with the explicit reverse value. It does **not** identify that model crossing with the unrestricted global phase transition. No Lean or CI verification is claimed.

Let beta_model denote the unique model root certified in `FORWARD_CONTACT_MODEL.md` and `contact_crossing_certificate.py`. The exact degree bracket there is

    136.672184698 < beta_model < 136.672184699.

Equivalently,

    68336092349/90000000000
      < beta_model/pi
      < 136672184699/180000000000.                    (1)

## Theorem: no rational angle of denominator at most 723688

If beta_model/pi=p/q in lowest terms, then

    q > 723688.

Thus the model crossing is not any of the usual rational multiples of pi, nor any rational angle with denominator at most 723688.

### Farey proof

The two fractions

    L=257315/338889,
    U=292174/384799

are Farey neighbours:

    292174*338889 - 257315*384799 = 1.

The certified interval (1) is contained in (L,U). Hence every reduced rational strictly inside it has denominator at least

    338889+384799 = 723688.

The unique fraction attaining that minimum denominator between L and U is their mediant

    M=(257315+292174)/(338889+384799)
     =549489/723688.

It remains to exclude M itself.

The crossing certificate gives, at

    beta_0=136.672184698 degrees,

an upper bound on the signed-area gap

    g(beta_0) <= 405343882600452697 / 2^96,

and over the whole certified root tube it gives

    g'(beta) <=
      -109505625206996195173306350356 / 2^96.

The Machin-series certificate gives

    pi >= 248902613312231085230521944622 / 2^96.

Since M-beta_0/pi is positive, integration of the derivative bound yields

    g(pi M)
      <= g(beta_0)
         + sup(g') * pi_lower * (M-beta_0/pi)
      <= -25615043635931743867557904276141502602544309995149128041590869
          / 6388120125954163446495180153893873006254145728443686543299706880000000000
      < 0.

So beta_model/pi is not M. By the Farey-neighbour denominator theorem, every remaining rational in the root interval has denominator strictly greater than 723688.

All arithmetic in the final displayed inequality is exact rational arithmetic. The geometric and interval-analytic meaning of the stored crossing certificate remains a dependency.

## What this does not prove

This is **not** a proof that beta_model/pi is irrational: rational numbers with larger denominators are not excluded.

It is nevertheless stronger than saying the decimal does not look familiar. It exactly eliminates every rational multiple of pi with denominator through 723688, including all standard elementary angles by an enormous margin.

The next unconditional step would require either a substantially narrower certified root interval plus repeated exact rational exclusions, or a new transcendence argument using the area equation. Merely computing more decimal digits does not prove irrationality.
