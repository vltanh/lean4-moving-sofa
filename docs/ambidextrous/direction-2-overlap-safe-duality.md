# Direction 2: coupled forbidden-area duals must allocate overlap spatially

**First-attempt outcome.** A dual written directly on the union of both forbidden sweeps has the correct area direction. But one scalar weight per forbidden quadrant is too weak: the exact finite test below proves a positive loss, and the reference's shared lower-niche overlap makes the obstruction persist under angular refinement. Spatial allocation of the forbidden area repairs the bookkeeping and gives a certificate usable on whole parameter boxes. A globally sharp allocation has not been constructed.

This is a concrete attempt at a coupled dual, not another optimization of the separate cap functional. It uses finite polygons and elementary indicator inequalities; no weighted-maximizer premise or curvature theorem is needed. Baseline: `80fb626e5672d9bb66a52c88d4b1b027b6c62e11`. Labels D2 are local.

## 1. The correct dual direction

Let B be a bounded measurable outer enclosure, and let F_i=B intersect Q_i be finitely many forbidden quadrants from either turn. Every candidate in the selected hallways satisfies

$$|S|\le |B|-|\bigcup_i F_i|.$$

For nonnegative measurable functions w_i on B, the pointwise constraint

$$\sum_i w_i(z)1_{F_i}(z)\le1\quad\text{a.e. on }B$$

gives the rigorous dual upper bound

$$\boxed{|S|\le |B|-\sum_i\int_{F_i}w_i(z)\,dz.}$$

The constraint is joint across both turns. Giving unit weight to two overlapping sweeps violates it; summing the areas of all forbidden pieces can give an alleged upper bound smaller than the true feasible envelope.

For constant weights lambda_i, subdivision into the finite line-arrangement cells makes the capacity inequalities a finite linear system: for each nonzero-area cell, the weights of all quadrants containing it sum to at most one. With rational unit normals and offsets, all cell areas and coefficients are rational. Numerical dual output would still require exact checking of every capacity and sign.

## 2. Exact four-hallway test of the constant-weight proposal

Take B=[0,3/2] times [0,1]. Select the lower-turn normals

$$u_1=(3/5,4/5),\quad v_1=(-4/5,3/5),\qquad
u_2=(4/5,3/5),\quad v_2=(-3/5,4/5).$$

Here the symbol nu_2 denotes the second first normal, not an additional direction. Each displayed pair is orthonormal. Use the actual supports of B as the outer hallway offsets. The lower forbidden regions are

$$Q_1=\{(3/5)x+(4/5)y<7/10,\ (-4/5)x+(3/5)y<-2/5\},$$

$$Q_2=\{(4/5)x+(3/5)y<4/5,\ (-3/5)x+(4/5)y<-1/5\}.$$

Add their vertical reflections Q_3,Q_4 under y -> 1-y, corresponding to two upper-turn positions. Their positive lower triangles each have area 8/75 and maximum height 8/25. Upper and lower triangles do not intersect in positive area; the middle strip through y=1/2 survives. All four box vertices survive, so the compact connected finite envelope has actual convex hull B. No full continuous motion is claimed for it.

The intersection of the two lower triangles has vertices, in boundary order,

$$(1/2,0),\ (5/7,2/7),\ (3/4,5/16),\ (11/14,2/7),\ (1,0).$$

Its shoelace area is 37/448; the upper pair has the same overlap. Consequently

$$|E|=3/2-4(8/75)+2(37/448)=\boxed{20807/16800}.$$

The unweighted swept-area subtraction would report 161/150, strictly *below* this exact envelope area: it is not a valid upper bound.

For nonnegative constant weights, the lower overlap imposes lambda_1+lambda_2<=1, and the upper overlap imposes lambda_3+lambda_4<=1. These are also sufficient capacities, as opposite turns have no overlapping triangles. Equal individual areas make the exact best constant-weight dual value

$$3/2-(8/75)\max\sum_i\lambda_i=\boxed{193/150}.$$

It exceeds the true envelope area by exactly

$$\boxed{193/150-20807/16800=809/16800>0.}$$

Thus even the optimal constant weights cannot be sharp on this simple connected, actual-hull finite configuration. This is not evidence against Romik optimality; it is a falsification of the proposed unsplit dual's exactness.

## 3. Why angular refinement alone cannot fix scalar weights at the reference

The explicit reference's regular upper cap has width 2m>2. Its baseline intervals for every interior lower-turn quadrant contain the common interval (1-m,m-1), by the intercept inequalities of CW. In particular any finite collection of these lower quadrants contains a common small positive-area neighborhood above the central baseline point. That neighborhood lies in the reference convex hull.

Therefore any nonnegative constant weights for these finite reference lower quadrants obey

$$\sum_i\lambda_i\le1.$$

Their weighted forbidden-area contribution can be no larger than the largest individual triangle area. Adding further overlapping angles does not turn this weighted average into the union area. The same holds for the upper turn. This is a structural obstruction to this **particular constant-weight proposal**, not to general two-turn duality or to spatially varying weights.

## 4. A spatial dual with no double counting

One exact allocation is the priority partition

$$P_i=F_i\setminus\bigcup_{j<i}F_j.$$

The P_i are disjoint, their union is the complete forbidden set, and weights w_i=1 on P_i, zero elsewhere, saturate the dual pointwise. This is simply exact union accounting, not a new sharp global theorem. It demonstrates what the scalar dual was missing: a point covered twice must be assigned once, while exclusive pieces of every sweep must still be counted.

More usefully, suppose offsets vary in a parameter box and robust inner sets F_i^- satisfy F_i^- subset F_i(z) for every parameter z in that box. Allocating the fixed union of the F_i^- gives a valid dual for **every** parameter in the box. Direction 3 uses exactly this construction with rational offset bounds, producing an ordinary-area exclusion over eight independent offset variables.

## 5. Decision and remaining gate

**Reject:** another search for one global nonnegative scalar weight per sampled quadrant. Shared overlap prevents it from aggregating the forbidden union even at the reference.

**Retain:** spatially allocated, jointly two-turn certificates, especially allocations valid on parameter boxes. They can be checked by exact arrangement geometry and do not require injectivity of an unverified limiting boundary curve.

**Missing:** an allocation tight enough on every competitive parameter branch, including any limiting reference branch. An identity that computes a finite union exactly is not a proof that its maximum over all placements is M. Direction 1's critical-face reduction and Direction 3's robust boxes offer concrete ways to address that remaining maximization, but a complete covering is not supplied here.

The finite areas were checked by two independent rational implementations: polygon clipping/inclusion-exclusion and vertical line-order integration. These checks do not certify all intermediate hallway angles; finite-angle outer bounds do not require that stronger feasibility assertion. No CI, Lean/Lake compilation, dependency installation, manuscript build or long search was used.
