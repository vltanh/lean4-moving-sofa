# 64. A positive canonical corner is quantitatively inside the horizontal projection

This removes one of the residual cases listed in Theorem 117. A lower canonical corner at a horizontal projection endpoint cannot be in the incoming strip at all: it is strictly below it. Consequently it cannot obstruct the existing circular replacement by pinching a fiber there.

The geometric estimate below has no maximality, regularity, curvature, full-turn, or candidate-neighborhood hypothesis. Its use for a singular-curvature improvement retains the outer-clearance and floating-normal hypotheses of Notes 56 and 58.

## 64.1 Two support inequalities

Let K be a nonempty compact convex set contained in

\[
[x_-,x_+]\times[0,1],
\]

where x_- and x_+ are its actual horizontal extrema. Fix 0<t<pi/2 and put

\[
\mu_t=(\cos t,\sin t),\quad\nu_t=(-\sin t,\cos t),
\qquad c=(h_K(\mu_t)-1)\mu_t+(h_K(\nu_t)-1)\nu_t.
\]

Thus c is the canonical lower inner corner. The rectangle containing K gives

\[
c\cdot\mu_t+1=h_K(\mu_t)\leq x_+\cos t+\sin t,
\]

\[
c\cdot\nu_t+1=h_K(\nu_t)\leq-x_-\sin t+\cos t.
\]

Rearranging, with no sign changes because sine and cosine are positive,

\[
\boxed{
 x_+-c_x\geq\frac{1-(1-c_y)\sin t}{\cos t},\qquad
 c_x-x_-\geq\frac{1-(1-c_y)\cos t}{\sin t}.
}
\tag{64.1}
\]

These inequalities hold even when c lies outside K or below the strip. There is no assertion that the corner belongs to the body.

**Theorem 118 (positive-corner interior margin).** If c_y>=0, then

\[
 c_x-x_-\geq\tan(t/2)>0,
\qquad x_+-c_x\geq\tan\bigl((\pi/2-t)/2\bigr)>0.
\tag{64.2}
\]

In particular, for delta<=t<=pi/2-delta with delta>0, the abscissa of every such corner is at distance at least tan(delta/2) from each horizontal projection endpoint.

**Proof.** In (64.1), c_y>=0 permits replacing 1-c_y by 1 to obtain lower bounds. Use (1-cos t)/sin t=tan(t/2), and the same identity at pi/2-t. QED.

The full formulas (64.1) are stronger than (64.2): increasing the corner height increases the lower bounds on its distances from both sides. No feasibility assumption was needed beyond the incoming-strip containment of K.

## 64.2 Endpoint and exterior corners lie strictly below the strip

Taking the contrapositive quantitatively in (64.1) gives

\[
 c_x\leq x_-\ \Longrightarrow\ c_y\leq1-\sec t<0,
\]

\[
 c_x\geq x_+\ \Longrightarrow\ c_y\leq1-\csc t<0.
\tag{64.3}
\]

For t in a fixed compact interior angular interval, these are uniform negative bounds. For instance on [delta,pi/2-delta] each is at most 1-sec(delta).

Reflection across y=1/2 gives the corresponding statements for an upper canonical corner: if its height is at most one, its abscissa is strictly interior with the same bounds; at or outside a projection endpoint its height is strictly greater than one.

These statements are for interior angles. At the axis angles the strict margin vanishes, and the division used in (64.1) is not available. Pinned or axis cases are not disposed of by this argument.

## 64.3 Consequence for an actual support replacement

Consider the circular replacement of Note 56 or 58 on a shrinking floating normal interval about t_0. It changes only one quarter support function, leaves the incoming vertical supports and all terminal-strip supports unchanged, raises the support by u>=0, and has ||u||_infinity tending to zero.

Suppose its old source corner has abscissa at either endpoint of the horizontal projection of K. By (64.3) its height is strictly negative. Continuity of the support-determined corner path gives an angular neighborhood in which every old corner stays a fixed distance below zero. Uniform smallness of u then gives the same property for every changed corner.

Every lower forbidden quadrant at an interior conventional angle lies at or below its corner height: a point in it has the form c-a mu_t-b nu_t with a,b>0, so its vertical coordinate is c_y-a sin t-b cos t<c_y. Consequently none of these changed quadrants meets the strip containing K or the enlarged hull K_c. There is **no lost old body area**, not merely a small quadratic loss.

The untouched upper sweep is unchanged, and K_c contains K. Therefore the new canonical envelope contains the entire old saturated body. Its horizontal projection is the same because the horizontal supports are unchanged. All its vertical fibers over that projection are intervals containing an old body point. Compactness and the interval-fiber connectedness argument of Theorem 26 make the new envelope a connected feasible competitor for the original endpoint angles.

For a second-quarter or upper-turn change the argument is identical after exchanging the two frame vectors or reflecting the strip.

**Corollary 119 (the projection-endpoint residual is not protective).** Under the strictly clear outer-edge or outer-point hypotheses of Theorem 105 or 107, a source corner at a horizontal projection endpoint does not prevent a singular-curvature improvement. The positive added region in those theorems survives, while the old-area loss is zero. Hence the corresponding atom or singular-density point cannot occur at a global maximizer.

**Proof.** The previous paragraph supplies feasibility, containment, and connectedness without any positive-fiber-gap assumption. The clear outer region is retained by the same triangle or unique-exposed-point argument as in Notes 56 and 58. That region has strictly positive area outside the old hull. QED.

The same argument covers source corners outside the projection. Outer clearance is still required to retain a positive part of the added hull; it is not inferred from the position of the inner corner.

## 64.4 Exact effect on the residual list

The projection-endpoint alternative in Theorem 117 can be deleted wherever the cited singular repair has its stated outer-clearance and floating-normal hypotheses. A positive-height source corner is automatically a fixed distance inside the projection on compact angular windows, and an endpoint source corner removes no incoming-strip points.

This leaves two kinds of residual geometry from that list: genuine outer/inner-corner coincidences, and actual pinches not yet covered by a suitable ceiling or contact-graph argument. This note does not prove those remaining sets null, bound the remaining absolutely continuous density by one, or complete the endpoint rotation.

The calculations are pen-and-paper. No CI, Lean/Lake compilation, numerical experiment, or computer algebra was used. All later optimality uses of the earlier branch theorems remain subject to their stated hypotheses and independent review.
