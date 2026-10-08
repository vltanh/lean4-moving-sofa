# A direct spatial partition: valid area enclosure before auxiliary optimization

**Scope.** This records an alternative attack direction with its ordinary-area linkage proved first. It is independent of background existence, curvature domination, face alignment and weighted maximality. The sharp maximum of the resulting one-cap expression is NOT proved. No numerical sample is promoted to that missing bound. Labels SPB are local.

Baseline: `9307910d73167a19f92c1785433aa27febacd375`. The only imported motion step is canonical tightening from Note 8. The fiber identities below are elementary and self-contained. This is not a claimed closure of either the full-turn or the partial-turn problem.

## 1. The actual two-cap fibers

Let S be a compact connected body in the common incoming strip 0<=y<=1, with projection I=[l,r], W=r-l. Use its actual hull to form downward caps U,V from the upper hull roof and reflected lower hull roof. Write their upper roofs as A_U,A_V.

Let n_U,n_V be the positive niche roofs over the angular intervals actually supplied by the two canonical motions. For a full-turn body these are the full niches; for a partial-turn body they are only the visited sweeps. The upper and lower intervals remain independent.

The canonical envelope containing S has fibers

$$E_x=[\max(n_U,1-A_V),\ \min(A_U,1-n_V)].$$

They are nonempty because S is connected and projects onto the entire I. Hence its area is the integral of

$$\ell(x)=\min(A_U,1-n_V)-\max(n_U,1-A_V)\ge0.\tag{SPB.1}$$

Empty fibers outside this actual-body setting would require positive parts and a separate correction; the following unqualified integral identity is not asserted for such data.

## 2. Split the projection, rather than replace its geometry

Put

$$J=[l+W/4,r-W/4],\qquad |J|=|I\setminus J|=W/2.$$

On the middle half J, simply discard the two outer hull restrictions. On the two exterior quarters, discard the niche restrictions. These are upper relaxations of each nonempty fiber:

$$\ell\le1-n_U-n_V\quad\text{on }J,$$

$$\ell\le A_U+A_V-1\quad\text{on }I\setminus J.$$

Define the spatially weighted one-cap quantity

$$\mathcal P_J(U)=\int_{I\setminus J}A_U(x)\,dx-\int_J n_U(x)\,dx,\tag{SPB.2}$$

with the actual angular interval included in the definition of n_U.

**Theorem SPB1 (direct ordinary-area enclosure).**

$$\boxed{|S|\le|E|\le\mathcal P_J(U)+\mathcal P_J(V).}\tag{SPB.3}$$

**Proof.** Integrate the two fiber inequalities. The constants cancel because |J|=|I minus J|. QED.

No curvature, symmetry, contact order, common top-face interval or background cap is needed. The two caps are not required to maximize any objective. This proves the geometric comparison before asking whether its right side can be sharply optimized.

## 3. The entire relaxation error has an exact positive formula

Put d_U=1-A_U, d_V=1-A_V. Subtract SPB.1 from each relaxed fiber bound. Directly using max(x,y)-x=(y-x)_+ gives

$$
\begin{aligned}
\mathcal P_J(U)+\mathcal P_J(V)-|E|
={}&\int_J[(d_V-n_U)_++(d_U-n_V)_+]dx\\
&+\int_{I\setminus J}[(n_U-d_V)_++(n_V-d_U)_+]dx.
\end{aligned}\tag{SPB.4}
$$

All terms are nonnegative. Thus there is no unaccounted signed winding or positive clipping term in SPB.3. There can still be genuine relaxation slack; SPB.4 identifies it exactly instead of assuming it vanishes.

For the reference caps, J is exactly their top-face interval, the cap roof is one there, and the positive niches lie inside J. Outside J the niches vanish. Every term in SPB.4 is therefore zero, and the explicit reference calculation gives

$$\mathcal P_J(U_*)=M/2.$$

Thus the proposed upper relaxation is exact on the reference. Exactness on one example does not prove its universal maximum.

## 4. Relationship to the earlier signed objective

For the full niche and the same projection,

$$\boxed{\mathcal P_J(U)=\Psi(U)+\int_J(1-A_U)dx+\int_{I\setminus J}n_Udx.}\tag{SPB.5}$$

The two added terms are nonnegative. Accordingly the written theorem Psi<=M/2 does NOT prove P_J<=M/2. This is a strictly stronger possible one-cap bound, not a relabeling of WV2. The usual signed-roof calibration cannot be applied with the extra terms silently deleted.

For example a regular stadium cap whose top face is longer than J generally has positive niche area outside J, so P_J can be strictly larger than Psi even without rough curvature. A future proof must pay both of the explicitly added terms.

## 5. The exact unproved acceptance target

For the full-turn problem, a sufficient theorem would be

$$\mathcal P_{J(U)}(U)\le M/2$$

for every full-niche cap that can occur in an actual competitive pair, where J(U) is its middle projection half. Proving this on all normalized caps in the relevant width range would be stronger and also sufficient. The two independent cap inequalities would then close full-turn optimality immediately through SPB.3, without a separate background-admission theorem.

This proposed scalar bound has not been proved or certified. In particular the input cap need not have the regularity of a weighted maximizer, and its spatial window depends on its width. A coupled bound on the sum that uses compatibility of U,V could work even if the stronger independent-cap bound fails.

For partial turns, SPB.3 still holds with the visited niches, but replacing them by the larger full niches lowers the proposed upper expression and is not allowed. The outgoing-strip constraints also couple the original upper and lower hull data. No partial-turn closure follows from a conjecture concerning only full niches.

## 6. Short discovery tests and their limitations

Two fixed, nonadaptive runs evaluated 41 prescribed caps/cuts and 108 prescribed circular-flank caps. Their runtimes were about 0.144 and 0.275 seconds under five-second caps. No large-margin violation was found. The finite reference discretization already overestimates P_J(U_*) by about 0.000240, so the small positive sample excesses are not rigorous counterexamples or evidence of a true excess. No certified quadrature error is available.

One additional fixed-budget run tested polygonal caps with 308 untrusted objective evaluations, six differential-evolution iterations and no polishing. It ended at its preset iteration limit in about 0.097 seconds and proposed a sampled value about 0.791. That result is far below the reference and supplies neither a sharp bound nor global optimizer convergence. The source and outputs are preserved in the session bundle.

The first prescribed-cap script had two failed helper-name lookups before the retained successful run; neither failure produced mathematical data. All tests were short and explicitly noncertifying. Their absence of a convincing violation is only a reason to retain this as a possible direction, not to mark an optimality gate complete.

The actual positive result is SPB.3--SPB.4. No CI, Lean/Lake compilation, dependency installation, manuscript build, long search or new global certificate was used. The unrestricted optimal value remains unproved.
