# 04. Selecting a specified maximizer without assuming it is balanced

Date: 2026-10-02. Status: proved abstract lemmas; application to the full sofa problem still requires the geometric checks listed below.

## A compact selection lemma

Let X be compact, F:X->R continuous, and x_* a global maximizer with value M. Let F_n be continuous functions with

    sup_X |F_n-F| <= e_n,     e_n -> 0.

Let X_n be nonempty compact subsets of X, and suppose there exist r_n in X_n with r_n -> x_* and F_n(r_n) >= M-eta_n, where eta_n >= 0. Let P:X->R be continuous, nonnegative, and vanish precisely at x_*. Choose lambda_n>0 with

    lambda_n -> 0,     (e_n+eta_n)/lambda_n -> 0.

Choose x_n to maximize F_n-lambda_n P on X_n. Then x_n -> x_*.

Proof. Comparing x_n to r_n gives

    M+e_n-lambda_n P(x_n)
      >= F_n(x_n)-lambda_n P(x_n)
      >= M-eta_n-lambda_n P(r_n).

Consequently

    P(x_n) <= (e_n+eta_n)/lambda_n + P(r_n) -> 0.

Every convergent subsequence therefore has limit x_*, by continuity and the zero set of P. Compactness implies convergence of the whole sequence.

The lemma deliberately does NOT claim that x_n maximizes the unpenalized F_n. That is the false inference recorded in note 03.

## A support-function penalty

For standard right-angle caps in a fixed compact box, fix a target cap K_* and define

    P(K) = integral_0^pi [h_K(t)-h_{K_*}(t)]^2 dt.

It is continuous in the Hausdorff metric. If P(K)=0, continuity of the support functions gives their equality on [0,pi], and the bottom-segment argument of note 02 gives K=K_*. Hence it is a valid selector, including the horizontal position rather than silently quotienting it out.

If all bodies are contained in a radius-R ball, the differences of their support functions are uniformly bounded. The penalty has a particularly useful local derivative, as follows.

## A mesh-scale derivative lemma

Suppose a perturbation K_epsilon of K satisfies

    h_{K_epsilon}(t)-h_K(t)=epsilon beta(t)

on [0,pi], with beta supported in an interval of length at most 2 delta and |beta|<=2. Then

    P(K_epsilon)-P(K)
      = 2 epsilon integral (h_K-h_{K_*}) beta
        + epsilon^2 integral beta^2.

If |h_K-h_{K_*}|<=H, then

    |d/d epsilon P(K_epsilon)|_{epsilon=0+} <= 8 H delta.

In particular, maximizing F_n-lambda_n P imposes a first-order error only of order lambda_n delta in such a variation. After division by the angle mesh delta, the error is O(lambda_n), which tends to zero.

This is why a penalty depending on an integral of support functions is preferable here to a generic Hausdorff-distance penalty. An unscaled O(lambda_n) error PER FACET could sum to O(lambda_n/delta), which need not vanish.

## Candidate right-angle application: checks, not assumptions

The proposed X is the compact family of standard right-angle caps in a sufficiently large fixed box. F is the cap sofa-area functional A, F_n is the finite-angle upper approximation A_n on a nested uniform mesh, X_n consists of polygon caps for that mesh, and r_n is the circumscribed polygon approximation to K_*.

To make this a proof of injectivity for every maximizing right-angle cap, the following must be checked:

1. A_n converges uniformly to A on X, including continuity of the full niche area and the endpoint angles.
2. The chosen r_n lies in X_n, converges to K_*, and has A_n(r_n)>=A(K_*). The box can be chosen with a strict margin around K_* so its artificial boundary is eventually irrelevant to local variations.
3. Pushing an existing nonhorizontal polygon facet outward changes its actual support function only on the two adjacent angle cells, with the bound in the derivative lemma. Redundant facets and the cells adjacent to 0 and pi need explicit treatment.
4. The polygon area variation yields one-sided approximate balance

       sigma_i <= tau_i + C lambda_n delta.

5. Baek's geometric estimate for tau_i is valid for these polygon caps WITHOUT assuming exact maximum or niche containment. Combining it with (4) must give the same limiting surface-area-measure inequality as in Chapter 6.
6. The arm-length argument can then be run for the chosen limiting cap and its reflection, using those measure inequalities rather than the definition `IsBalancedMaxCap`.

Even completion of this right-angle application would leave the shape-preserving rotation-angle reduction for arbitrary moving sofas. This note does not claim that the full shape-uniqueness theorem follows merely from the abstract selection lemma.
