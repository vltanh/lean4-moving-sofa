# Contact-certificate reproduction

The contact continuation is **computer-assisted**. These programs verify roots and geometric inequalities over continuous parameter intervals; they do not merely sample angles. They are ordinary Python programs, not Lean/kernel certificates.

## Rebuild and replay

From this directory:

```sh
python check_verifier_primitives.py
python build_contact_cover.py --part all --output-dir certificates
python verify_contact_cover.py certificates/*.json --report replay.json
```

Only the Python standard library is required. The reference execution used CPython 3.13.5 on an IEEE-754 binary64 Linux platform. The interval layer checks the float format and subnormal behavior. It uses outward rounding for basic operations and interval Taylor polynomials for sine and cosine; verification does not trust platform `sin` or `cos` calls.

The builder can be split into `--part 1`, `2`, `3`, `4`, `5`, and `endpoint`. Each part writes a distinct file in the output directory. Run the final verifier over all six certificate files together. Keep the replay report **outside** that directory so the shell glob does not mistake it for an input certificate.

Saved JSON records can be replayed directly without running Newton or the builder. The reference records are identified by SHA-256 digests in [CERTIFICATE_REPORT.json](CERTIFICATE_REPORT.json), and were also supplied as a conversation attachment. The repository contains the complete standard-library procedure to regenerate the records; it does not depend on that attachment remaining available.

## What each stage establishes

`build_contact_cover.py` uses floating-point Newton steps only to propose root boxes and preconditioners. A proposed inverse is not trusted as an exact inverse. Every accepted record passes the outward-rounded contraction, root-inclusion, ordering, and support tests. An incomplete checkpoint, failed proposal, or stalled discovery is not a proof of an uncovered interval.

`verify_contact_cover.py` ignores stored success flags and numerical bounds, recomputes every mathematical acceptance test from the box coordinates, and checks exact parameter coverage using `Fraction`. It also checks that each endpoint joining box is contained in both neighboring root boxes. `--partial` deliberately checks only the supplied records and makes no claim of full angle coverage.

The compact records cover the exact rational interval `[101/100, 7853/5000]`, or `[1.01, 1.5706]`. The endpoint records cover `h = omega-c` in `[0,1/32]`; the paper proves that their continuous branch covers every angle from `1.5706` up to, but not including, `pi/2`. The analytic first-regime note covers `(1,1.01]`. The right-angle theorem is a separate companion input, not a numerical identification at the endpoint.

## Reference replay

The reference run accepted and replayed 750 compact-angle parameter boxes, 16 endpoint parameter boxes, and 15 endpoint joining boxes: **781 records total**. The largest outward contraction bound was below `0.439`; every support-second-derivative upper bound was below `-0.093`. All records also passed the strict endpoint support tests. The precise maxima, source hashes and record hashes are in the report.

Different platforms may produce different proposed boxes. Byte-for-byte identity with the reference JSON is not required: successful replay of every record and the exact full-coverage test are the mathematical acceptance criteria. Conversely, a matching printed approximate root or small residual alone proves nothing.

## Source roles

- `contact_core.py`: exact elementary propagation for every contact-indicator combination, with no ODE solver.
- `interval_contact.py`: outward intervals, certified trigonometric enclosures, first derivatives and reflected event-order enumeration.
- `jet_contact.py`: interval Hessians, parameter-uniform root inclusion/contraction, and whole-interval geometry checks.
- `endpoint_contact.py`: regularized endpoint equations with `h = omega-c` as parameter.
- `build_contact_cover.py`: untrusted proposal generation followed by verification.
- `verify_contact_cover.py`: saved-record replay, endpoint gluing and exact coverage checks.
- `check_verifier_primitives.py`: exact-rational regression cases and initial-value/derivative checks of all eight flow pieces; these tests supplement, but do not replace, the replay or the analytic derivation.

The older `arm_certificate.py` and `transition_certificate.py` check separate exact rational calculations from earlier notes. They are not substitutes for the new contact-cover verification.

## Review and execution boundary

The checker assumes the documented floating-point arithmetic model. Its source and the analytic reductions have not been independently verified by a proof assistant or referee. The interval arithmetic and derivative code were audited, including a corrected mixed interval/second-derivative division dispatch; all contact records were replayed again after that correction. No CI, Lean compilation, or TeX compilation was run. These scripts are not connected to a workflow.
