# 65. An active interior-angle corner cannot sit at a projection endpoint

This removes one of the residual singular-contact cases listed in Theorem 117. The argument is a direct support estimate in the incoming strip. It needs neither maximality, smoothness, curvature domination, nor full-quarter endpoint angles.

It concerns the **source corner** associated with a varied support normal, not every outer point that might coincide with some other corner. The latter obstruction is not removed here.

## 65.1 A quantitative horizontal margin

Let K be a compact convex body in 0<=y<=1, with horizontal projection [x_-,x_+]. At an interior angle 0<t<pi/2 put

\[
\mu_t=(\cos t,\sin t),\qquad
\nu_t=(-\sin t,\cos t),
\]

and let its lower canonical inner corner be

\[
c=(h_K(\mu_t)-1)\mu_t+(h_K(\nu_t)-1)\nu_t.
\]

In particular h_K(mu_t)=c dot mu_t+1 and h_K(nu_t)=c dot nu_t+1. Bounding the support over the containing rectangle gives

\[
c_x\cos t+c_y\sin t+1
\leq x_+\cos t+\sin t,
\]

\[
-c_x\sin t+c_y\cos t+1
\leq-x_-\sin t+\cos t.
\]

**Lemma 121 (corner projection margins).**

\[
\boxed{
\begin{aligned}
x_+-c_x&\geq\frac{1-(1-c_y)\sin t}{\cos t},\\
c_x-x_-&\geq\frac{1-(1-c_y)\cos t}{\sin t}.
\end{aligned}}
\tag{65.1}
\]

In particular, if c_y>=0 then

\[
c_x-x_-\geq\tan(t/2)>0,
\qquad
x_+-c_x\geq\tan((\pi/2-t)/2)>0.
\tag{65.2}
\]

**Proof.** Rearrange the two preceding support bounds, divide by the positive sine or cosine, and use the half-angle identities (1-cos t)/sin t=tan(t/2) and (1-sin t)/cos t=tan((pi/2-t)/2). QED.

For t in a compact interior angular interval [epsilon,pi/2-epsilon], every corner with c_y>=0 is therefore at horizontal distance at least tan(epsilon/2) from both projection endpoints. This is uniform over K; no bound on derivatives of its support is used.

The upper-turn statement is obtained by reflection across y=1/2. An upper corner with c_y<=1 has exactly the same horizontal margins, with its positive angle magnitude as parameter.

## 65.2 Endpoint or exterior source corners are strictly inactive in the strip

If a lower corner has c_x>=x_+, the first inequality in (65.1) gives

\[
c_y\leq1-\frac1{\sin t}<0.
\tag{65.3}
\]

If c_x<=x_-, the second gives

\[
c_y\leq1-\frac1{\cos t}<0.
\tag{65.4}
\]

All points in its downward forbidden quadrant have y<c_y, because at least one of the strictly positive downward frame coefficients contributes to the vertical displacement. Thus that quadrant has no point in the incoming strip. Continuity of the canonical corner path and the strict inequalities make the same assertion hold on a sufficiently small angular neighborhood. Small uniform support changes supported there also keep the changed corners below the strip.

The reflected upper corner lies strictly above y=1 in the analogous situation, and its upward forbidden quadrant likewise misses the strip.

**Corollary 122 (projection endpoints cannot obstruct a clear singular repair).** Consider the floating-normal circular replacements of Theorem 105 or 107. Suppose their required outer-edge or outer-point clearance holds. If the source corner is at or beyond a horizontal projection endpoint, then the changed quadrants miss the entire strip for all sufficiently small replacement scales. Hence the old body is retained, and the positive added region in those theorems gives a genuine area improvement without a fiber-gap assumption.

**Proof.** Equations (65.3)-(65.4) give a strict vertical margin. The original and replaced corners converge uniformly on their shrinking windows to that corner, so all the changed quadrants remain outside the strip. The window avoids the axis and pinned endpoint normals; consequently the strip and horizontal projection are unchanged. The hull enlarges and every old fiber is retained. As in Note 61, the full new envelope has interval fibers containing the old connected body, is connected, and follows the same complete angular intervals. The clear added region survives by the previous replacement proofs. QED.

This is not an assertion that an arbitrary newly enlarged hull is itself feasible. The competitor is its canonical envelope, whose nonempty fibers and endpoint conditions are checked as above.

## 65.3 Correction to the residual list in Theorem 117

The projection-endpoint source-corner case was left open unnecessarily in Note 63. Under its floating interior-angle assumptions, the estimate above makes such a source corner strictly inactive. The below-strip or above-strip case of the existing repair theorem applies; the case cannot protect singular curvature at a strictly clear outer contact of a maximizer.

Thus the still-unexcluded singular-continuous support in that theorem's active floating regime reduces, up to the null sets already specified there, to:

1. outer points that are themselves canonical inner corners;
2. actual collapsed source-corner fibers without an oblique touching affine ceiling.

The second case has its source abscissa strictly inside the projection by (65.2). At an interior source abscissa, strict source inactivity is handled by Note 61 and a positive fiber gap is handled by the roof-continuity argument in Note 63.

The remaining two sets are not proved null. Hidden edge atoms and the sharp bound on the absolutely continuous density are not settled by this note. It removes a specific residual case by an explicit estimate rather than relabeling all corner contacts as harmless.

No CI, Lean/Lake compilation, numerical experiment, or computer algebra was used.
