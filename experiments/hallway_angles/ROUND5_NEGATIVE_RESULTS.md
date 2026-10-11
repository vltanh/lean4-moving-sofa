# Fifth-round failures, qualifications, and audit scope

## 1. The sufficient cutoff is not an optimal transition

`prove_propagation(Fraction(53,1000))` rejects the proposed epsilon cutoff 53/1000. The final contradiction margin is exactly -2032897/127200000. The same estimates prove the cutoff 1/19, whose margin is 166189/7125000>0.

This is a failure of this set of sufficient constants, not a feasible counterexample, a claim that the explicit sofa ceases to be optimal, or a bracket on beta_c. No broader cutoff is inferred from a favorable sampled value.

## 2. One coarse parameter cell is insufficient

The exact-integer scalar checker with one cell covering [0,1/10] rejects both sides of its first eV enclosure as inconclusive. With 256 cells it verifies all ten strict bounds on the whole interval. Rejection is a regression test; no fallback accepts midpoint values as interval proofs.

## 3. The missing-area width inequality needs its triangular-cap regime

Dropping the condition d<min{aW^2/(2b),bH^2/(2a)} from the contact-rectangle lemma gives a false statement.

Take Q=[0,1]^2, E=[0,1/10]x[0,1], and direction (a,b)=(100,1). The missing area is 9/10 and E has directional width 11. The purported unconditional lower bound would be 101-2sqrt(90)>82, a contradiction. The actual hypothesis fails since 9/10>1/200.

The explicit global proof verifies this regime separately before invoking the square-root cap estimate. The example is retained in `test_explicit_cutoff.py`.

## 4. A smaller proof dependency is not an independent verification

The new contact-core argument avoids the full Hausdorff/inball theorem. It still uses canonicalization, the crossing and excursion area majorant, the exact continuous quadratic optimization, and the explicit feasible candidate. Interval proofs of ten scalar inequalities do not independently validate those geometric arguments. The explicit global theorem remains a mathematical proof draft, not a Lean theorem or a refereed publication.

## 5. Scope does not expand automatically

The proved cutoff pi-1/19 is not the onset of unrestricted reverse optimality. The comparison roots near 133.64 and 142.10 degrees remain class-level comparison bounds, not exact phase-transition angles. No global optimum at 150 or 170 degrees is asserted by the fifth-round cutoff. No forward-class solution is added.

## 6. Local source and tool limitations

A direct Git clone failed at DNS resolution. The local copies of `parameter_certificate.py`, `width_certificate.py`, and `reverse_exact.py` were transcribed from connector reads and matched against their fetched Git blob hashes before use. No CI, workflow run, or Lean build was attempted. Floating-point geometry tests are supplementary and are not in the exact scalar certificate's trust boundary.
