# Motion-preserving rounding and connected strip shaving

**Scope.** This is an elementary regularization of actual bodies, not an averaging of convex caps or an unproved area-enlarging operation. It supplies the connected, positive-face approximants used in the companion full-turn density theorem. The operation may decrease area, but its area loss tends to zero. It does not prove the sharp optimum. Labels RR are local.

Baseline: `c68813d3b5148b21fdd44553c1ced55060bf4844`. The only motion input is canonical support tightening from Note 8. The proofs below are self-contained once that formulation is adopted. No computation is a premise, and no novelty claim is made for the general rounding idea.

## 1. Rounded homothety preserves every already feasible hallway

Let S be a nonempty compact connected body, let B be the closed Euclidean unit disk, and choose 0<lambda<1. Put

$$r=(1-\lambda)/2,\qquad R_\lambda=\lambda S+rB.$$

For every unit vector n,

$$h_{R_\lambda}(n)=\lambda h_S(n)+r,\qquad
w_{R_\lambda}(n)=\lambda w_S(n)+1-\lambda.\tag{RR.1}$$

**Lemma RR1.** If S fits its canonical unit hallway for an ordered orthonormal frame (u,v), then R_lambda fits its own canonical unit hallway for that same frame. Thus every canonical angular interval of either handedness feasible for S remains feasible for R_lambda.

**Proof.** Every p in R_lambda has a representation p=lambda s+r z, with s in S and |z|<=1. Since s fits, at least one of

$$h_S(u)-s\cdot u\le1,\qquad h_S(v)-s\cdot v\le1$$

holds. For that normal n,

$$h_{R_\lambda}(n)-p\cdot n
=\lambda(h_S(n)-s\cdot n)+r(1-z\cdot n)
\le\lambda+2r=1.$$

The outer supporting inequalities hold by definition of h. This proves the inner-wall disjunction as well. Support continuity gives the continuous canonical motion, and (RR.1) preserves any required endpoint strip of width at most one. QED.

Compactness and connectedness follow because R_lambda is the continuous image of S times B under addition and scaling. Uniform shrinking alone also preserves all feasible frames: replace the final depth estimate by k times the old depth, for 0<k<=1. No reflection of the body is used in either argument.

An important exact feature is

$$\{n:w_{R_\lambda}(n)\le1\}=\{n:w_S(n)\le1\}.\tag{RR.2}$$

Rounding has not manufactured a bridge across an interval of unsafe straight-strip directions.

## 2. Shaving both supports does not disconnect the rounded body

Fix a unit vector n. For 0<epsilon<r define the closed slab

$$Q_\epsilon=\{x:-h_{R_\lambda}(-n)+\epsilon
\le x\cdot n\le h_{R_\lambda}(n)-\epsilon\},$$

and put

$$B_{\lambda,\epsilon}=R_\lambda\cap Q_\epsilon.$$

Assume its prescribed slab width

$$d=w_{R_\lambda}(n)-2\epsilon$$

is positive. This is automatic in the later application, where d>1.

**Lemma RR2.** B_(lambda,epsilon) is compact and connected, contains lambda S, and has width exactly d in direction n. Both exposed hull faces normal to n and -n have positive length; in fact each contains a segment of length

$$\boxed{2\sqrt{2r\epsilon-\epsilon^2}>0.}\tag{RR.3}$$

It inherits every motion of R_lambda, since it is a subset.

**Proof.** Every center lambda s lies between the two original supports with distance at least r from each boundary plane. Since epsilon<r, all centers lie in Q_epsilon. Furthermore

$$B_{\lambda,\epsilon}
=\bigcup_{s\in S}\bigl((\lambda s+rB)\cap Q_\epsilon\bigr).$$

Each set in this union is convex and contains its center. The connected set lambda S intersects all of them, so their union is connected. This does not require S itself to be path connected or to have interior.

Take s_+ attaining h_S(n). The plane x dot n=h_(R_lambda)(n)-epsilon cuts the radius-r disk centered at lambda s_+ at normal distance r-epsilon from its center. Its chord has the length (RR.3), lies on the upper slab boundary, and satisfies the other slab inequality since d>0. The analogous disk at a minimizing support point supplies a chord on the lower boundary. Thus both supports of the slab are attained by actual points of B_(lambda,epsilon), with positive-length exposed segments. QED.

The preservation of lambda S is the reason clipping is harmless for connectedness here. Clipping an arbitrary connected body by a convex strip would not justify the same conclusion.

## 3. Convex width control for the clipped body

Let K_lambda=conv(R_lambda) and K_(lambda,epsilon)=K_lambda intersect Q_epsilon. Then

$$\operatorname{conv}(B_{\lambda,\epsilon})\subseteq K_{\lambda,\epsilon},$$

with equality of their two support values at n and -n by RR2. We will use this inclusion, not assume equality of the entire hulls.

Fix any s_0 in S and set p_0=lambda s_0. Its distance from either original support plane of K_lambda is at least r. The homothetic copy

$$p_0+(1-\epsilon/r)(K_\lambda-p_0)$$

lies in K_(lambda,epsilon). Therefore for every direction theta,

$$\boxed{(1-\epsilon/r)w_{K_\lambda}(\theta)
\le w_{K_{\lambda,\epsilon}}(\theta)
\le w_{K_\lambda}(\theta).}\tag{RR.4}$$

In particular the clipped convex width converges uniformly to the original convex width as epsilon decreases to zero with lambda fixed. This explicit enclosure will justify the preservation of a strictly increasing width interval.

## 4. Area convergence without a boundary regularity assumption

As lambda increases to one, R_lambda converges to S in Hausdorff distance. It contains lambda S, so

$$|R_\lambda|\ge\lambda^2|S|.$$

On the other hand R_lambda is eventually contained in every fixed closed neighborhood of S. The areas of those neighborhoods decrease to |S|, since S is compact and bounded. Hence

$$\boxed{|R_\lambda|\longrightarrow|S|.}\tag{RR.5}$$

For the shaved body, the even simpler bounds

$$\lambda^2|S|\le |B_{\lambda,\epsilon}|\le |R_\lambda|\tag{RR.6}$$

hold for every epsilon<r. Thus along lambda_j -> 1, any such shavings have areas tending to |S|. A further homothety k_j -> 1 preserves that limiting area, and an orthogonal change of incoming coordinates preserves area exactly.

This is not an area-monotonicity theorem at finite lambda. The numerical value of the optimum is not used anywhere in these estimates.

## 5. Boundary and next step

The shavings produce two positive support faces in a freely chosen normal direction, but that direction need not yet be a valid incoming orientation. Merely producing these faces does not license a full-turn theorem in the new coordinates. The companion density note proves the required interval of safe strips after a further shrinking factor tending to one.

The operation is different from the invalid maps S -> (S+JS)/2 and cap averaging. RR1 pays for its rounding by an explicit uniform shrink. No convex-hull feasibility, area-improvement claim, or unhandled clipping correction is inserted.

No CI, Lean/Lake compilation, dependency installation, manuscript build or numerical search was used. The results are written and self-reviewed, not independently verified.
