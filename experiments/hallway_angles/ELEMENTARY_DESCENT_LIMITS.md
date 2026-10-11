# Elementary-descent audit: failed shortcuts and exact scope

This round does not enlarge a Farey denominator bound. It proves a structural implication under Schanuel for the specified contact/crossing equations. The following limitations and negative controls are retained alongside the positive theorem.

## 1. The conjectural step has not disappeared

Both saturation of a reduced finite exp/log tower and the two-argument capture lemma use Schanuel's transcendence-degree assertion. The last-step descent is not an unconditional replacement for it. The new conclusion is

    Schanuel => beta_model is outside the full algebraic/exp/log field L,

not an unconditional claim that no closed form exists. The auxiliary switching/phase conclusions have the same assumption. No theorem proving Schanuel, Four Exponentials, or unconditional irrationality is supplied.

## 2. The area equation is essential

The contact equation alone does not make exp(iT) algebraic over an elementary field with T adjoined. The area relation, whose rational term C_b is nonconstant, supplies that extra dependency. Omitting it breaks capture.

This is not merely a technical concern: the existing contact branch has solutions at the elementary hallway angle beta=3pi/4. A theorem excluding all elementary beta values from the contact equation alone would therefore be false. The new theorem concerns simultaneous contact AND equal-area solutions, not every stationary forward candidate.

## 3. A genuine nonzero pole is necessary for monomial exclusion

The algebra lemma requires deg(P)>0, P(0) nonzero, and gcd(P,Q)=1. Each condition matters. Write c=sqrt(2), z=exp(x), w=exp(c*x).

- With P=1 and Q=-2z, the equation is w=2z and has the elementary nonzero solution x=log(2)/(c-1). The denominator polynomial has no pole.
- With P=z and Q=-2, the equation is w=2/z and has the elementary nonzero solution x=log(2)/(c+1). Its only pole is at zero.
- With P=z-1 and Q=-2z(z-1), cancellation gives the first example again. There is a nonzero pole before cancellation, but P and Q are not coprime.

These exact controls are in `test_elementary_descent.py`. Nonlinearity, a transcendental exponential, or the mere presence of a denominator does not by itself establish non-elementarity.

## 4. A rational multiplier would not force logarithmic descent

At a logarithmic final step the coefficient comparison gives s=c*r with r,s rational. In the actual application c=-2i*mu is nonzero and purely imaginary, so r=s=0. For a rational multiplier, such as c=3, the nonzero pair r=1/2,s=3/2 satisfies the relation. That essential distinction is also a regression test.

## 5. Why pi is anchored

Putting pi into the base field eliminates a potentially moving logarithmic coefficient in the area equation. After t descends, the coefficient A=(d+6)/(4(d+2)) is nonzero and forces b to descend. Without this anchor, one has to control an additional relation between the top-level b and pi coefficients; the earlier algebraic-direction proof addressed a restricted version with a rank case split. The new proof avoids that extra restriction, rather than assuming the case split extends to all elementary directions.

## 6. The remaining claim is about a model, not the global transition

The theorem applies to all real solutions of the displayed compact system on its stated hyperbolic domain. The previous isolated model crossing is one such solution. The geometric statements needed to identify it with the unrestricted beta_c are not established by this arithmetic theorem.

Likewise the proof does not expand the unrestricted-optimality angle range, reverify any earlier sofa proof, or assert that every auxiliary quantity is non-elementary. For example the model amplitude 1/3 is elementary. The common signed area's arithmetic nature is not settled here.

## 7. Symbolic regression failure and correction

The first run had one failing test because it compared the two expression trees

    (d+6)/(4*(d+2)) and (d+6)/(4*d+8)

using syntactic equality. The test was corrected to check that their exact cancelled difference is zero. No area formula, coefficient, or theorem statement was changed. The corrected run passed all 15 tests, and the source-hashed combined runner passed them again.

## 8. Trust boundary

The exact SymPy checks establish fourteen algebraic identities and verify controls for the necessary hypotheses. They do not machine-check Schanuel, reduced-tower saturation, capture, the minimal-tower argument, or the auxiliary rank arguments. Those remain ordinary conditional mathematical proofs requiring independent review. Numerical approximations to beta, PSLQ, and Farey intervals are absent from the new proof and tests.

The only attempted raw-source download failed with DNS resolution; repository reads and writes used the working GitHub connector. The two new tested source files were compared with their committed Git blob hashes before the final validation record was written. No CI, workflow run, or Lean build was attempted, and commits carry `[skip ci]`.
