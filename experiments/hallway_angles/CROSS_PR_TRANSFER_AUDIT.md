# Cross-PR transfer audit for the arbitrary-hallway project

This note audits neighboring PRs in the same repository for results that can strengthen the arbitrary-bend hallway work. It does not import their conclusions automatically: each result is a research proof draft with its own scope and verification boundary, and the right-angle/fixed-net-angle geometry differs from changing the actual hallway bend.

## Highest-value source: PR #4, fixed-net-angle optimality and uniqueness

Branch: `research/fixed-rotation-angle-paper-20261005`.

The problem in PR #4 keeps the hallway right-angled and prescribes a net sofa rotation omega. This is NOT the arbitrary-hallway problem here. Nevertheless several proof mechanisms are directly relevant.

### 1. Order-independent contact shooting

`order-independent-shooting.tex` rewrites the arm equations as a positive affine integral fixed point and proves uniqueness by a one-ended Poincare contraction. It survives crossings and overlaps of reflected contact intervals.

**Transfer target:** the forward arbitrary-bend contact model currently assumes a three-phase ordering. Re-express its wall/contact equations in indicator form and seek either:
- a contraction on the full pair of arm variables with a bend-dependent weighted norm, or
- contractions on the two side phases plus a coercive central solve.

If successful, this removes dependence on one prescribed event ordering and gives nonsingularity before nonlinear switch-angle shooting.

### 2. A global contact certificate, not a candidate-only check

`order-independent-contact-certificate.tex` is especially important. It proves that exact contact equations plus a small list of support/norm inequalities imply:
- the proposed arcs are the entire niche boundary;
- the candidate is feasible;
- the lifted first variation has the correct sign against every competitor;
- strict concavity gives the unique maximizing cap.

The proof uses sine-kernel inequalities and monotone corner tangent angle, not a sampled boundary.

**Transfer target:** this is the missing bridge for the analytic forward branch near 136.67 degrees. The arbitrary-bend version should replace the perpendicular wall frame by the two bend-dependent normals, then reproduce:
- one sign-change lemma for the wall curvature;
- joining-point inequalities against all later inner walls;
- early-parameter exclusion by slope comparison;
- radial/graph reconstruction of the niche.

A successful analogue would upgrade the current forward contact model from a stationary ansatz to a certified global forward-class optimizer.

### 3. Vertical-core lifting removes unknown-maximizer threshold assumptions

`vertical-core-lifting.tex` replaces radial contractions by vertical slices and proves the upper lift using only:
- strict arms;
- fan containment;
- positivity at two chosen cuts;
- cut separation.

It does NOT require every interior threshold of an unknown maximizer to be positive.

**Transfer target:** the reverse arbitrary-bend theorem currently stops near beta=114.47 degrees because the general-majorant proof controls arbitrary canonical-corner excursions only on a restricted angle interval. A bend-adapted vertical-core lift is the most promising route to prove the reverse-class formula for ALL obtuse bends beta in (pi/2,pi).

This is the single clearest opportunity to remove a current theorem cutoff.

### 4. All-maximizer curvature and pinned-edge estimates

`fixed-angle-curvature.tex`, `pinned-endpoint-bounds.tex`, and `global-cut-geometry.tex` show how to derive, for EVERY prescribed maximizer rather than the candidate:
- endpoint-safe curvature domination;
- strict arm inequalities;
- quantitative endpoint corner lengths;
- fan containment;
- two cut half-planes whose overlap misses the niche.

**Transfer target:** derive the corresponding local wall estimate with arbitrary hallway wall angle beta. The polygon calculation is local and appears to depend mainly on neighboring rotated supports; the coefficients will change from the right-angle arm functions. If the resulting density bound is available, PR #2's arm bootstrap and PR #4's vertical lift provide a route from maximality to the universal upper functional.

This would replace several assumptions currently imposed directly on arbitrary-bend canonical paths.

## PR #2: stationarity, deficit, and rigidity

Branch: `paper/stationarity-deficit-rigidity`.

### 5. Persistent-penalty selection of a specified maximizer

`02-selection-and-stationarity.md` gives an abstract selection theorem using fixed positive weights on dense support observations. It selects any prescribed global maximizer and yields floating-facet defects whose TOTAL error tends to zero, without choosing a tuned vanishing penalty.

**Transfer target:** use the same mechanism for arbitrary-bend cap classes. This is preferable to proving regularity only for a specially selected symmetric maximizer. It is particularly relevant if forward/reverse class optimality and uniqueness are to classify EVERY maximizer.

### 6. One-step arm bootstrap with errors

`01-arm-bootstrap.md` proves strict arm lower bounds from integral inequalities on any interval length L<5/3 and includes an additive-error version.

**Transfer target:** the reverse orientation interval e=pi-beta always lies below pi/2<5/3 for obtuse hallways. Once a maximality-derived curvature inequality is obtained, this theorem should transfer nearly verbatim and can give strict reverse arms on the FULL obtuse range. That is exactly the regularity needed by a vertical-core lift.

For the forward orientation interval beta>pi/2 the full interval may exceed 5/3, so this lemma alone does not solve the forward class; it may still apply on individual contact subintervals.

### 7. Affine-minus-squares deficit identity

`03-deficit-and-rigidity.md` decomposes the area deficit into:
- geometric slack;
- first-variation slack;
- explicit squared displacement residuals.

It then propagates the residuals to a Hausdorff cap bound.

**Transfer target:** formulate the arbitrary-bend lifted functional in the same affine-minus-squares form. Once a forward/reverse candidate satisfies the first-variation certificate, the same identity should yield:
- uniqueness from zero residual;
- quantitative stability from small residual;
- a numerically certifiable route to candidate recovery.

This is more robust than using strict concavity only qualitatively.

## PR #6 and PR #8/#9: quantitative coercivity and maximizer-first assembly

### 8. Sharp cap support/distance coercivity

PR #6 derives an explicit right-angle cap stability bound; PR #8 sharpens the relevant coefficient to approximately 2.002 by combining residual arcs optimally.

**Transfer target:** after deriving the arbitrary-bend displacement kernel, solve the corresponding first-order residual propagation exactly and optimize its evaluation norm. This can materially improve the unrestricted alignment step and perhaps lower the current global beta>=pi-1/8 cutoff.

The constants themselves do NOT transfer; the method does.

### 9. Maximizer-first optimality from zero deficit

PR #9 and the older PR #5 assemble the logic

    actual maximizer -> maximality geometry -> upper functional
    -> zero deficit -> shape equality -> global optimality/uniqueness.

**Transfer target:** use exactly this architecture for the arbitrary hallway. In particular, avoid assuming the known optimal value when proving class rigidity. Gerver/the reverse candidate enters first as a competitor to obtain a lower bound; the universal functional gives the matching upper bound.

This is the clean architecture for an eventual forward/reverse phase theorem.

## PR #3: ambidextrous lessons

The ambidextrous branch has many useful negative results.

### 10. Do not rely on convexification/repair to preserve ordinary area comparisons

Several exact counterexamples show that a sharp analytic functional can fail to majorize actual area even arbitrarily near a candidate, and that curvature repair/convexification can introduce clipping terms of the wrong sign.

**Transfer warning:** in the arbitrary-bend forward problem, a new lifted functional must be tied to an ACTUAL niche decomposition or to a rigorously area-dominating surrogate. Candidate stationarity plus functional calibration is not sufficient.

### 11. Quantitative finite-angle repair

`38-quantitative-angle-completion.md` proves that finite sampled hallway inclusions can be converted to genuine continuous motions by scaling by 1/(1+R Delta), with exact area loss.

**Transfer target:** this is directly usable in arbitrary-bend computer-assisted candidate existence/feasibility. It gives a simple, general way to turn a finite interval cover into a true motion with controlled loss. For an exact optimum theorem the loss must eventually vanish or be absorbed, but it is valuable for rigorous lower constructions and selection approximants.

## Concrete priority order after this audit

1. **Reverse class on all obtuse bends.** Adapt PR #2 maximality curvature/arm bootstrap plus PR #4 vertical-core lifting. Target theorem:
   
       M_-(beta)=V(pi-beta) for every pi/2<beta<pi,
   
   with uniqueness.

2. **Forward-class global certificate near the model crossing.** Adapt PR #4 order-independent contact certificate to the bend-dependent wall frame. Target theorem:
   
       M_+(beta)=W(beta,T(beta))
   
   on an interval containing the candidate crossing.

3. **Class exhaustiveness/alignment.** Combine all-maximizer geometry and quantitative coercivity to prove
   
       M(beta)=max{M_+(beta),M_-(beta)}
   
   near the crossing, rather than only near reversal.

4. **Exact phase transition.** Once 1-3 hold, the already certified unique analytic crossing becomes the genuine beta_c.

## Verification boundary

Every source PR audited here is itself research work with stated limitations. PR #4 uses an executed ordinary-Python interval verifier but is not Lean-checked; PRs #2/#6 are manuscript/experiment arguments; PRs #8/#9 contain substantial uncompiled Lean source; PR #3 remains incomplete. This transfer audit therefore identifies reusable METHODS and candidate lemmas, not automatically inherited theorems for the arbitrary-bend problem.
