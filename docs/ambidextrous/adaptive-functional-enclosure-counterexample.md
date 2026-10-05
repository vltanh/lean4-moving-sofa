# Adaptive-functional supplement: an exact failure of ordinary-area enclosure

Theorem AF3 in the [global calibration supplement](adaptive-functional-global-calibration.md) proves the sharp functional bound without curvature or contact hypotheses. It does not assert that this functional majorizes the ordinary area of every feasible sofa. The following calculation gives a concrete reason that assertion would be false.

## E.1 The existing feasible family

Use the first-upper-quarter perturbations and their reflected copies from [Note 28](28-high-area-curvature-counterexamples.md) and [Note 41](41-resolving-the-high-curvature-family.md). Their support change is confined to a fixed compact interval J inside the candidate's middle phase, away from both switching angles and all axis normals. These are convex hulls of actual compact connected feasible bodies. Their curvature can exceed one.

Let h_c be the convex-minorant repair from Notes 40–41. Write f_c=f+u on the changed first quarter, with u>=0, g unchanged, and the change reflected on the lower half. The increment is in H^1_0(J). The signs p<0<q persist on J before and after repair; all contact switches and endpoint values remain unchanged.

The geometric hybrid-roof description, feasibility, and common-hull retention are proved in Note 41. They are not inferred just from preservation of one wall envelope. Since the repaired curvature equals one wherever u>0, integration by parts gives

\[
\int_J\rho_f u=\int_Ju+\int_Ju'^2-\int_Ju^2.
\tag{E.1}
\]

The smooth original examples from Note 28 suffice here; a singular-measure extension is not needed.

## E.2 The exact difference

Lemma 80 in [Note 40](40-curvature-repair-by-convexification.md) gives the actual surviving-area gain

\[
|S_c|-|S|=2\int_J(1-q-u)u+\int_Ju'^2.
\tag{E.2}
\]

Here q is the original velocity. This formula includes the changed middle-corner area and both reflected halves.

Compute the adaptive functional independently. On J both contact-square terms are active. Holding g fixed, its half-functional first variation in f is (2rho_f-1-q)u, and its homogeneous quadratic change is one half of the integral of u^2-2u'^2. Adding the reflected half and using (E.1) gives

\[
\begin{aligned}
\widetilde{\mathcal Q}(h_c)-\widetilde{\mathcal Q}(h)
&=2\int_J(2\rho_f-1-q)u+\int_Ju^2-2\int_Ju'^2\\
&=2\int_J(1-q)u+2\int_Ju'^2-3\int_Ju^2.
\end{aligned}
\tag{E.3}
\]

The repaired body satisfies |S_c|=tilde Q(h_c) by the earlier exact niche formula. Subtracting (E.2) from (E.3) proves:

**Proposition AF4 (positive ordinary-area defect).**

\[
\boxed{|S|-\widetilde{\mathcal Q}(h)=\int_J(u'^2-u^2).}
\tag{E.4}
\]

For a nonzero repair this is strictly positive. Indeed, if J has length ell<pi, the Dirichlet inequality gives

\[
\int_J(u'^2-u^2)\geq\left(\frac{\pi^2}{\ell^2}-1\right)\int_Ju^2>0.
\]

The windows in this construction are shorter than pi/2. No switch-endpoint contribution is missing: the switches are outside J, and the contact signs stay strict on the modified interval.

## E.3 The counterexamples approach the candidate's area

For the oscillatory supports h_n from Note 28, the repair u_n is nonzero for all sufficiently large n because the original curvature exceeds one on an interval. Notes 28 and 41 establish their complete feasibility and |S_n| tending to M from below. Equation (E.4) now gives

\[
\boxed{\widetilde{\mathcal Q}(h_n)<|S_n|<M.}
\tag{E.5}
\]

Their horizontal width is exactly the candidate's width, because every axis support value is unchanged. Thus they satisfy AF3's width condition. The theorem is not contradicted: it bounds their functional values, which are smaller than their actual areas.

The inequality |S_n|<M comes from the feasible improving repair, not from the functional calibration alone. The calculation proves that no fixed area threshold below M, even together with proximity to the candidate, justifies unqualified enclosure by the adaptive functional.

## E.4 The remaining geometric task

AF3 completes the analytic maximum and equality case on all normalized real H^1 profiles of width at least one. It does not complete the sofa problem. An enclosure |S|<=tilde Q(h_conv S) for actual global maximizers would be one sufficient next statement, but AF4 shows it must use maximality or a proved improvement, not feasibility alone.

A surrogate profile could also be used without being convex or feasible, since AF3 imposes neither property. However its ordinary-area comparison still needs proof, and uniqueness additionally needs a containment or equality-recovery argument. Merely choosing a profile with value M is not such a construction.

The existing curvature/contact route remains sufficient for the geometric comparison; the WG width gate supplies its full-turn consequence. The support conditions are no longer premises of the analytic theorem AF3, but have not been removed from that existing geometric argument.

Both the positive calibration and this failed enclosure are retained explicitly. No unrestricted completion claim is made. No CI, Lean/Lake compilation, numerical experiment, computer algebra, or manuscript build was used. These are written, self-reviewed arguments with the stated prior dependencies.
