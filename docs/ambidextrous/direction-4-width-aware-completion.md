# Direction 4: a width-aware completion allowance for arbitrary terminal strips

**Result of the first attempt.** The existing CC bound is the worst case when both endpoint strips have width one. Keeping their actual widths gives an exact smaller geometric allowance, including a zero-loss regime. This is a general two-strip theorem, not a reference-family calculation. It does not prove that every partial-turn competitor falls in the zero-loss regime or has enough area deficit to pay a positive allowance. No full-turn optimality is asserted.

Baseline: `80fb626e5672d9bb66a52c88d4b1b027b6c62e11`. Inputs: canonical support tightening and the signed-fiber accounting in CC. New labels D4. All new derivations below are hand proofs; numerical tests are supplementary.

## 1. Two endpoint strips with their actual widths

Fix unit normals n_0,n_e separated counterclockwise by e in (0,pi/2). Suppose an actual hull lies in two strips of widths p,q in (0,1], respectively. Translate the intersection of their lower supporting lines to A=0, so

$$0\le z\cdot n_0\le p,\qquad0\le z\cdot n_e\le q.$$

Let D be the intersection of the upper supporting lines, D dot n_0=p and D dot n_e=q. For every intermediate normal n_t, t in [0,e], positive sine interpolation implies h_K(n_t)<=D dot n_t. The relaxed possible missing-first-wall region is

$$\Omega=\{z:z\cdot n_0,z\cdot n_e\ge0,\ (D-z)\cdot n_t>1\text{ for some }0\le t\le e\}.$$

No upper strip bound on z is imposed in this region: discarding it only enlarges the missing material. Reflection and rotation preserve its area.

Put a=arccos(p), b=arccos(q), so a,b in [0,pi/2).

**Theorem D4.1.** The exact area of this relaxed region is zero if a+b>=e. If a+b<e, it is

$$\boxed{\Lambda(p,q;e)=\frac12\left[\frac{2pq-\cos(e)(p^2+q^2)}{\sin(e)}-p\sqrt{1-p^2}-q\sqrt{1-q^2}-e+a+b\right].}$$

In all cases

$$0\le\Lambda(p,q;e)\le\Lambda(1,1;e)=\tan(e/2)-e/2.$$

These equalities describe the relaxed first-wall region, not a claim that all its points can simultaneously belong to one feasible sofa.

## 2. Proof by polar coordinates around the upper corner

Write x=D-z. Membership in the lower cone is equivalent to x dot n_0<=p and x dot n_e<=q. If the maximum of x dot n_t over [0,e] exceeds one, it cannot be attained at either endpoint, because both endpoint values are at most one. The maximizing normal is therefore the direction of x, lying strictly inside the arc, and |x|>1. This also excludes directions on the opposite side of the circle: any interior critical maximum of a scalar product with unit normals has the direction of x, while the opposite direction is a minimum.

For x=r n_t the two inequalities become

$$1<r\le\min\{p/\cos t,\ q/\cos(e-t)\}.$$

Both cosines are positive because e<pi/2. Thus

$$|\Omega|=\frac12\int_0^e\left[\min\{p^2\sec^2t,q^2\sec^2(e-t)\}-1\right]_+dt.$$

The integrand is positive exactly on (a,e-b); hence the region is empty up to boundary when a+b>=e. In the positive case, p/cos t increases and q/cos(e-t) decreases. Their unique crossing t_* lies in (a,e-b), with

$$\tan t_*=(q-p\cos e)/(p\sin e),$$

and the two sides of the integral use the first and second expression, respectively. Integration gives

$$2|\Omega|=p^2(\tan t_*-\tan a)+q^2(\tan(e-t_*)-\tan b)-(e-a-b).$$

Use p tan a=sqrt(1-p^2), q tan b=sqrt(1-q^2), and

$$p^2\tan t_*+q^2\tan(e-t_*)=[2pq-\cos e(p^2+q^2)]/\sin e$$

to obtain the formula. Increasing either endpoint width increases the radial upper bound, proving monotonicity and the unit-width upper bound. At p=q=1 the formula is exactly CC's circular allowance. QED.

## 3. Zero-loss completion criterion

The same proof gives the pointwise assertion, not just an area-zero estimate:

$$\boxed{\arccos p+\arccos q\ge e\ \Longrightarrow\ w_K(n_t)\le1\quad(0\le t\le e).}$$

Indeed the sine-interpolation envelope is the width of the containing parallelogram in these intermediate directions. A violation would put its lower corner z=0 in Omega, which the polar inequalities exclude. Equivalently, the two prescribed widths admit no vector satisfying both endpoint inequalities and an intermediate projection exceeding one.

Consequently this condition supplies all missing hallway frames when one of the two normals in each missing frame runs over this arc: a unit strip in that normal makes the associated inner-wall alternative hold for the whole body. Together with the original visited frames, canonical continuity gives full motion without deletion. This recovers the finite strip-bridge criterion geometrically; it is not a new assertion that every partial turn completes.

For equal widths p=q=h, the criterion is h<=cos(e/2). In the positive case the closed formula simplifies to

$$\Lambda(h,h;e)=h^2\tan(e/2)-h\sqrt{1-h^2}-e/2+\arccos h.$$

For one unit endpoint, the zero-loss criterion is p<=cos e. Thus even one endpoint's actual strip slack can remove the entire worst-case circular allowance. Whether that slack exists must be checked on the actual body.

## 4. Insertion into the actual signed-fiber comparison

For a conventional partial-turn body let p be its incoming strip width and let q_-,q_+ be the two outgoing strip widths, all at most one. Missing angles are e_-,e_+ in [0,pi/2). The existing CC proof counts the difference between visited and full thresholds above the actual hull floor (and its reflected counterpart). Those counted points remain in the two lower endpoint half-planes, while their offending first-wall thresholds are bounded by D dot n_t-1. Thus they lie in the translated/rotated Omega just computed.

The same signed accounting therefore gives

$$\boxed{|S|\le\int_I\ell_{\rm full}(x)dx+\Lambda(q_-,p;e_-)+\Lambda(q_+,p;e_+).}$$

Set Lambda=0 at e=0. Reflection supplies the upper-turn estimate. This retains signed empty fibers exactly as CC does; integral ell_full is not silently replaced by the area of a connected completed body.

This theorem is valid without curvature bounds, reference collars, symmetry, or a minimum-width hypothesis. If both allowances vanish, the same body completes, so connectedness is unchanged. If either is positive, it still needs payment by an actual area deficit; its smaller value alone does not finish optimality. It is not valid to choose a narrow frame that the original motions cannot reach and insert its width here.

## 5. First-attempt outcome and next gate

**Positive:** a closed-form allowance retains actual endpoint widths and interpolates between zero-loss completion and the exact unit-strip circular cost. It is directly usable in a geometry/angle parameter box together with Direction 3's finite constraints.

**Still missing:** a joint area/angle certificate that bounds the full signed term by M minus the positive allowance on every remaining partial-turn branch. No relation between missing angle and minimum-width slack has been presumed.

No CI, Lean/Lake compilation, dependency installation, manuscript build, or long search is used. The theorem and the earlier motion/fiber dependencies are self-reviewed, not independently verified.
