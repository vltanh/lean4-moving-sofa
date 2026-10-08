# 38. Quantitative completion of a finite-angle witness

This is an unrestricted approximation result. It does not require smoothness, a curvature cap, a contact pattern, symmetry, or a maximizing assumption. It turns the compactness-only convergence in Note 32 into an explicit bound by converting sampled angular feasibility into genuine complete motions after a small uniform scaling.

The scaling is an area-loss estimate, not a proof that a partial endpoint angle can be extended to pi/2. "Completion" here means filling in the angles **between the same sampled endpoints**.

## 38.1 Sampled canonical witnesses

Let S be a compact connected body contained in a Euclidean ball of radius R centered at the chosen origin, and put K=conv(S). Suppose its incoming and terminal strip widths are at most one for each of the two witnesses. Let their endpoint magnitudes be alpha,gamma in [0,pi/2].

For each witness suppose the canonical hallway inclusion is known at a finite set of angles containing both endpoints, with consecutive angular gaps at most Delta. Every intermediate angle is then at distance at most Delta/2 from a sampled angle of the same witness.

At an angle t use its ordered orthonormal frame (u_t,v_t), allowing the appropriate fixed handedness for the upper turn. Define the two canonical coordinates of p in S by

\[
X_t(p)=p\cdot u_t-h_K(u_t)+1,
\qquad Z_t(p)=p\cdot v_t-h_K(v_t)+1.
\tag{38.1}
\]

They always satisfy X_t,Z_t<=1. A canonical hallway inclusion is precisely X_t>=0 or Z_t>=0. For the upper physical hallway its second coordinate is y=1-Z, rather than y=Z; this is just the fixed-handedness representation, not a reflection performed during a motion.

## 38.2 The quantitative disjunction

Support continuity and the radius bound give, for either rotating unit normal,

\[
|[p\cdot u_t-h_K(u_t)]-[p\cdot u_s-h_K(u_s)]|
\leq2R\|u_t-u_s\|\leq2R|t-s|.
\tag{38.2}
\]

At a nearest sampled angle s, at least one coordinate is nonnegative. Keeping that same coordinate at t therefore proves

\[
X_t(p)\geq-\varepsilon\quad\text{or}\quad Z_t(p)\geq-\varepsilon,
\qquad\varepsilon=R\Delta.
\tag{38.3}
\]

No continuity of the choice of the two sides of the disjunction is required: for each point and each t, a nearest sample and one valid side suffice. The outer coordinate inequalities were already exact at every t because they use the actual hull support.

## 38.3 Repairing all intermediate placements

**Theorem 76 (quantitative finite-angle repair).** With the hypotheses above, the scaled body

\[
S^{\rm full}=\lambda S,\qquad\lambda=\frac1{1+R\Delta},
\tag{38.4}
\]

is a genuinely feasible compact connected ambidextrous body. Its two complete motions can use the same endpoint angles as the sampled witnesses. In particular,

\[
|S^{\rm full}|=\frac{|S|}{(1+R\Delta)^2}.
\tag{38.5}
\]

**Proof.** First extend the *canonical placement formula* continuously over the two angular intervals, even though S need not yet fit those intermediate placements. In the ordered coordinates, replace both X and Z by

\[
X'=\lambda X+\lambda\varepsilon,
\qquad Z'=\lambda Z+\lambda\varepsilon.
\]

Their upper bounds are one, since lambda(1+epsilon)=1. The approximate disjunction (38.3) becomes X'>=0 or Z'>=0. Thus the repaired placement is a genuine hallway inclusion at every intermediate angle.

This coordinate operation is realizable by proper motions of lambda S. For the lower physical hallway, if the original canonical map is g_-(t)p=R_-(t)p+a_-(t), use

\[
\widehat g_-(t)q=R_-(t)q+\lambda a_-(t)
+\lambda\varepsilon(1,1).
\]

For the upper physical hallway use

\[
\widehat g_+(t)q=R_+(t)q+\lambda a_+(t)
+(\lambda\varepsilon,0).
\]

Indeed y=1-Z in the upper ordered frame, so y'=1-Z'=lambda y. The two formulas have continuous translations, unchanged proper rotational parts, and the required initial orientation. Different initial translations are permitted in the posed problem.

The endpoint arm inclusions also hold. An exact coordinate in [0,1] becomes one in [lambda epsilon,1] in a lower ordered arm; the upper physical y-coordinate instead lies in [0,lambda]. The other required coordinate bound remains valid. Compactness and connectedness are preserved by scaling, and planar area scales by lambda squared. QED.

The body is not claimed to retain vertical span exactly one after repair; it is a valid competitor for the unrestricted problem, which is all that the upper-value comparison needs.

## 38.4 Explicit convergence of finite-angle upper values

Use the box from Note 25,

\[
B=[-D,D]\times[0,1],\quad D=1+\sqrt2,
\quad R_B=\sqrt{D^2+1}=\sqrt{4+2\sqrt2}.
\]

Let V be the unrestricted attained maximum and let v_n be the finite-angle maximum defined in Note 32, with N=2^n equally spaced samples on each of the two endpoint intervals. Its angular gaps are at most L/N, where L=pi/2. Put

\[
e_n=R_B L\,2^{-n}.
\]

**Corollary 77 (certified finite-angle error).**

\[
\boxed{V\leq v_n\leq(1+e_n)^2V.}
\tag{38.6}
\]

Consequently

\[
0\leq v_n-V\leq |B|(2e_n+e_n^2),
\qquad |B|=2(1+\sqrt2).
\tag{38.7}
\]

**Proof.** Every normalized genuine competitive body is in the finite class, so v_n>=V. Apply Theorem 76 to a finite-class maximizing body, using its actual endpoint angles and the bound R_B. The resulting genuine body's area is at least v_n/(1+e_n)^2 and is at most V. The final estimate uses V<=|B|, supplied by the common bounding-box reduction. QED.

Thus the convergence is quantitatively O(2^{-n}), not just subsequential. This is a mathematical estimate for the exact variational values v_n; no finite-angle optimization or numerical bound has been computed here.

## 38.5 What it does not establish

The theorem does not make an arbitrary floating-height perturbation admissible **without** area loss. Repairing a perturbation with violation proportional to its amplitude generally loses area to first order, so it cannot be inserted into a stationarity proof while dropping that cost.

It also does not prove V=M, force full quarter-turn endpoints, or provide a complexity bound for evaluating v_n. Its use is to control the relaxation error and make the arbitrary-maximizer selection quantitative, which is done next.
