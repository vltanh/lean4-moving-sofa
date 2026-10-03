# 09. Adversarial review log

Date: 2026-10-02. This is the author's mathematical self-review, not independent review or machine verification. The candidate global proof is in note 08; this log preserves failed arguments and explains where their replacements are used.

## A further negative result: bounded diameter does not control height perturbations

A tempting claim in the pinned-strip argument is that changing each defining half-plane height by at most epsilon changes a uniformly bounded polygon by O(epsilon), with a constant independent of its geometry. This is false.

For 0<delta<1, take

    K_delta={(x,y): 0<=x<=1, 0<=y<=delta x}.

Replace the bottom inequality y>=0 by y>=epsilon, where 0<epsilon<delta. All polygons remain in the unit square, and only one unit-normal height changes, by epsilon. But the distance from (0,0) in K_delta to the new polygon is

    epsilon sqrt(1+delta^(-2)),

because its nearest point is (epsilon/delta,epsilon). The ratio to epsilon diverges as delta->0.

**Repair used in note 06:** the fixed-angle cap family contains a COMMON positive-radius interior ball, and the two homothetic inclusions give the required uniform estimate. That ball is proved using the triangle with vertices O,(c_omega,0),(c_omega,1). As omega->pi/2, c_omega->0 and this particular argument degenerates. Note 05 does not use it: its right-angle density argument varies only floating facets and uses the exact local sine-hat formula. It does not vary the pinned top strip.

This counterexample invalidates the geometry-free perturbation estimate, not the repaired estimate and not sofa uniqueness.

## Detailed logical checks

### 1. The support ODE has the correct sign and endpoint treatment

For a tangent target T, the equation is

    sin(T-t) f'(t)+cos(T-t) f(t)=f(T).

Both f(T)cos(T-t) and C sin(T-t) satisfy it. The quotient derivative in note 01 is zero only on compact subintervals away from sin(T-t)=0; continuity, not division by zero, supplies endpoints. The four cap pieces must be matched in the order 4,3,2,1. A translation changes h by a cos t, exactly the remaining mode after the top normalization.

### 2. Do not manufacture exact maximizers

The selected K_n maximize A_n-lambda_n P, not A_n. Uniform approximation and comparison with the recovery caps force convergence to the specified K_*. Approximate balance is then derived directly from the penalized objective. The counterexample F_n(x)=x/n in note 03 remains relevant: deleting the penalty would reintroduce that gap.

### 3. Actual and assigned supports differ at a pinned variation

For a floating facet, containment of the old polygon in the new one keeps every other sampled support exactly fixed. For a pinned strip, the bottom half-plane moves as well and this reasoning fails. Note 06 instead uses actual-support <= assigned-height and the direction of niche monotonicity. Subtracting the smaller actual niche makes the actual objective LARGER, the direction needed to contradict penalized maximality. Treating all assigned heights as actual would be an unjustified step.

### 4. Niche containment is not smuggled into the approximations

Penalized polygon caps are not known to contain their niches. The finite Nef variation, the common boundary-endpoint identity, and the geometric ray-length estimates used in notes 05-06 are statements about general polygon caps and their fan niches. The diameter estimate is supplied by the compact family, not by the original maximal-polygon niche-containment theorem. Niche containment is used later only for caps of actual monotone sofas, where it is already available.

### 5. The error accumulation has the required scale

There are O(1/delta_n) floating facets. Their total defect is O(lambda_n), not O(lambda_n/delta_n), because the integral penalty has support variation on a set of length O(delta_n). The right-angle trigonometric error contributes O(delta_n). At the two fixed pinned directions, the O(lambda_n) errors are not summed over the mesh. The weighted boundary-vector identity controls their opposite signs without dividing by a sine tending to zero.

### 6. Weak limits and endpoints

Surface measures converge weakly under Hausdorff convergence. Sampled support points converge only at directions with a unique limiting support point; these directions have full angular measure. Uniform boundedness permits dominated convergence of the step densities. The first-cell bound is needed to exclude an atom at normal 0, and its reflection excludes an atom at pi. A top atom at pi/2 is permitted. The inequality for a pinned atom in note 06 uses limsup sigma_n({t})<=sigma({t}), not the reverse.

### 7. The Gerver envelope proves set recovery without a hidden Jordan assumption

The niche graph lies below the cap's height-one top rectangle. Its B and D portions have height strictly below one. On the x portion, a height-one point forces -alpha/beta=cot t; the first side is nondecreasing and the second strictly decreasing, so there is at most one such point. This rules out a positive-length top remnant. The density-of-interior argument still works at a possible single contact. It does not assume a strict new numerical bound on niche height.

## Remaining uncertainty

The new extension arguments are substantial mathematical claims. This self-review does not replace an independent review, and the existing Lean equality lemmas do not verify them. In particular, notes 05-06 should be checked line by line against the finite-angle geometry before treating note 08 as an established theorem. The current record contains a candidate proof, not a verified declaration of full uniqueness and not a constructed alternative optimal shape.
