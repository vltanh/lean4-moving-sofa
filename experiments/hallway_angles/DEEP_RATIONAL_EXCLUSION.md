# A much deeper unconditional rational-angle exclusion

This strengthens `RATIONAL_ANGLE_EXCLUSION.md` for the analytic contact-model crossing. It still does **not** prove irrationality and does not identify the model crossing with the unrestricted global phase transition.

Using the 192-bit exact interval checker in `deep_rational_exclusion.py`, the unique contact-model crossing satisfies

    504644407557908571 / 664626775090067219
      < beta_model/pi
      < 1920149641230808118 / 2528875470784124371.      (1)

The signed-area gap is rigorously positive at the left fraction and negative at the right fraction. These evaluations use exact integer/rational interval arithmetic, an exact Machin enclosure for pi, Taylor remainders, and interval Newton for the contact parameter; no floating-point trigonometry or optimizer is part of the proof.

The two fractions in (1) are Farey neighbours:

    1920149641230808118*664626775090067219
      -504644407557908571*2528875470784124371 = 1.

Therefore every reduced rational p/q strictly between them has denominator at least

    664626775090067219 + 2528875470784124371
      = 3193502245874191590.

Hence:

    beta_model/pi=p/q in lowest terms
      ==> q >= 3,193,502,245,874,191,590.

This improves the previous denominator exclusion by more than twelve orders of magnitude.

## Meaning

This is still a **finite denominator theorem**, not an irrationality proof. A rational multiple of pi with an astronomically larger denominator remains logically possible.

What it does establish unconditionally is that beta_model is not merely an unfamiliar small rational angle. Any rational explanation would require a denominator exceeding three quintillion.

The proof remains conditional on the mathematical interpretation of the previously certified contact-model crossing. It is independent of the missing proof that beta_model is the unrestricted global beta_c.

## Why the process stops

With fixed 192-bit arithmetic one can continue Stern-Brocot refinement only until interval evaluation of the signed-area gap becomes inconclusive. Increasing arithmetic precision can push the denominator bound farther, but no finite precision can prove irrationality by this method alone.

That is why the transcendence route and the rational-approximation route have fundamentally different endpoints: the latter can exclude arbitrarily large finite ranges, while a genuine irrationality proof needs structural number theory.
