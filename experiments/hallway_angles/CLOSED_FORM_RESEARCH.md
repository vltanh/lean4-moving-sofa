# Closed-form research: targets and inference boundaries

Starting checkpoint: `267ba93548d58c23f10e6b8793b952099acdc5b2`.

The request is an explicit closed-form expression for the transition angle, or a proof that none exists. An implicit root definition and extra decimal digits do not meet that request. The current contact-model crossing is not yet identified with an unrestricted global transition.

## Expression classes

The principal target is a finite expression starting from algebraic numbers and using arithmetic, radicals/algebraic operations, exp, log, and their usual trigonometric, hyperbolic, and inverse-function equivalents (with specified branches). Defining a new inverse function of this very equation is not counted as progress toward an explicit form. Standard additional functions such as Lambert W would be reported separately, not silently included.

For rigorous partial exclusion results, a smaller class is useful: angles whose unit-circle directions exp(i theta) are algebraic. This includes rational multiples of pi and straightedge-and-compass constructible directions. Excluding a pair of such directions does NOT exclude a closed form for beta alone or finite exp/log expressions.

## Work plan

1. Analyze algebraic cancellation in the contact equation after an exponential substitution; test direct polynomial and Lambert-W-style reductions without asserting their completeness.
2. Apply Gelfond-Schneider and Lindemann-Weierstrass only when their algebraicity and nondegeneracy hypotheses are verified.
3. Run reproducible high-precision expression-recognition experiments with declared degree/height limits. A failed search is not a nonexistence theorem, and numerical success would require exact verification.
4. Commit narrower proven obstructions and unsuccessful routes alongside any positive closed-form simplification. Keep the geometric beta_model=beta_c question separate.

## References checked

- Timothy Y. Chow, *What is a closed-form number?*, arXiv:math/9805045; https://arxiv.org/html/math/9805045 . This distinguishes finite expressions for constants from elementary antiderivatives and from unrestricted implicit definitions.
- Michail Karatarakis and Freek Wiedijk, *A formalization of the Gelfond-Schneider theorem*, arXiv:2603.24823v1, Theorem 3.1 and the arbitrary logarithm branch in Section 3.1; https://arxiv.org/html/2603.24823v1 . Only the stated classical theorem is used here, not any assertion that this sofa project is formalized.
- Jean-Paul Bezivin and Philippe Robba, *A new p-adic method for proving irrationality and transcendence results*, Annals of Mathematics 129 (1989), 151-160; https://annals.math.princeton.edu/1989/129-1/p05 . Its stated Lindemann-Weierstrass theorem gives linear independence of exponentials of distinct algebraic numbers over the algebraic numbers.

No CI, workflow dispatch/rerun, or Lean build will be used. Analytic proofs, exact symbolic checks, and numerical recognition have different roles. No blanket nonexistence theorem is inferred from the apparent difficulty of the equation.
