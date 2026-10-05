# 29. A geometric full-turn criterion and stability near the candidate

Full-angle completion follows immediately from one concrete hull property: containment of an axis-parallel unit square in the incoming coordinates. This note proves that criterion, verifies it for the candidate and the new curvature counterexamples, and gives a quantitative endpoint-angle estimate for nearby hulls.

It does not establish the square-containment property for every global maximizer.

## 29.1 A square forbids a partial endpoint

**Proposition 61 (unit-square gate).** Let S be a competitive ambidextrous body, put in the normalized canonical representation of Theorem 30, and let K=conv(S). If K contains a translate of [0,1] times [0,1], then both reduced endpoint magnitudes are pi/2.

**Proof.** For any alpha in (0,pi/2), the width of that square in direction (cos(alpha),sin(alpha)) is cos(alpha)+sin(alpha)>1. Width is monotone under inclusion. But a lower terminal arm requires the whole hull to have width at most one in precisely that direction, a contradiction. Thus alpha=pi/2. The upper endpoint has the same absolute-coordinate width formula, so gamma=pi/2 as well. QED.

The square need only lie in the convex hull. It need not lie in the nonconvex sofa itself. This matters for a body with upper and lower niches removed.

A sufficient way to obtain the square is for the top and bottom exposed-face intervals to overlap in a horizontal interval of length at least one. Convexity then fills the corresponding vertical rectangle.

## 29.2 The candidate passes this gate with a margin

For K_* the common face length is

\[
\ell_*=r_*-\ell_*=4A/3=1/(3\sin\beta)>1.
\tag{29.1}
\]

In this display the first ell_* on the left denotes the face length; to avoid endpoint ambiguity below, write this length as lambda_*=4A/3. The strict inequality follows from A>3/4. Hence K_* contains a rectangle of height one and length lambda_*>1.

All of the high-frequency curvature counterexamples in Note 28 have the **same** exposed-face intervals and therefore contain that same rectangle. Their partial-angle reductions cannot avoid full turns. Consequently their failure of the curvature cap is not explained by an alternative short-turn witness.

For clarity, the unambiguous width statement used below is

\[
w_{K_*}(\cos\alpha,\sin\alpha)
\geq\lambda_*\cos\alpha+\sin\alpha,
\qquad0\leq\alpha\leq\pi/2.
\tag{29.2}
\]

## 29.3 Endpoint angles of nearby hulls are necessarily close to full

Suppose a normalized competitive hull K is at Hausdorff distance at most epsilon from a fixed translate of K_*. Translation has no effect on widths. Uniform support convergence gives

\[
|w_K(n)-w_{K_*}(n)|\leq2\varepsilon
\]

for every unit n. Let alpha be a terminal magnitude and set d=pi/2-alpha. Competition above sqrt(2) gives 0<=d<pi/4. The endpoint strip and (29.2) imply

\[
\lambda_*\sin d+\cos d-1\leq2\varepsilon.
\tag{29.3}
\]

Since

\[
\lambda_*\sin d+\cos d-1
=\sin d\,[\lambda_*-\tan(d/2)]
\geq[\lambda_*-(\sqrt2-1)]\sin d,
\]

and sin(d)>=2d/pi on [0,pi/2], we obtain

\[
\boxed{\pi/2-\alpha\leq
\frac{\pi\varepsilon}{\lambda_*-(\sqrt2-1)}.}
\tag{29.4}
\]

The same inequality holds for gamma. This bounds the missing endpoint intervals by the geometric hull error, not by an assumed differentiability of the motion.

## 29.4 The exact remaining use of this result

A proof that every global maximizer has an overlapping top/bottom face interval of length at least one would remove the endpoint-angle hypothesis in the present route. Such a theorem has not been proved here. The candidate's rectangle and the bound for nearby hulls do not by themselves transfer that property to an unknown maximizing hull.

Likewise, convergence of area to M does not imply Hausdorff convergence to K_* without an independent stability or uniqueness theorem on the relevant class. Equation (29.4) begins with a stated Hausdorff hypothesis and does not infer it from near-optimality.
