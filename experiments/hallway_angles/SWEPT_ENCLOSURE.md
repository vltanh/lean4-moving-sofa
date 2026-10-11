# A tighter continuous-motion enclosure

This supplements the first-order construction in THEORY.md. It is an exact-real argument implemented with ordinary floating-point polygon geometry in `swept.py`, **not an interval-certified numerical certificate**.

## Setup

Fix one of the piecewise-linear corner paths and a uniform angular grid containing every path knot. Let `S_N` be the unshrunk sampled intersection with the entry strip. Let `B` be the bounding rectangle derived in `Motion.bounding_rectangle()`, so `S_N` is contained in `B`. Let `R` bound the distance from any point of `S_N` to any path corner, including intermediate corners. The maximum distance over exterior polygon vertices and path knots gives such a bound, since the norm is convex in either argument.

Write `delta` for the angular width of a grid cell and `D` for a bound on the corresponding corner displacement. On each cell, the corner is affine in the angle. The formulas below use absolute angular width and also apply to reverse rotation.

## Outer walls: second-order interpolation

For either unit wall normal, put

$$f(\theta)=n(\theta)\cdot(q-c(\theta)).$$

For `q in S_N`, differentiation on a cell gives

$$f''=-n\cdot(q-c)-2Jn\cdot c',\qquad |f''|\le R+2D/\delta.$$

The error between a twice-differentiable function and its endpoint linear interpolant is at most the supremum of its second derivative times `delta^2/8`. Hence imposing

$$f(\theta_i)\le1-\varepsilon_{\rm out},\qquad
\varepsilon_{\rm out}=\frac{\delta^2}{8}(R+2D/\delta)$$

at every sampled pose ensures that both outer inequalities hold at all intervening poses. The implementation adds a small heuristic floating-point guard to this margin.

## Inner corner: enclose the swept forbidden wedge

Let `W` be the fixed forbidden open wedge of the hallway. Suppose a point `q in S_N` lies in the forbidden wedge at some intermediate parameter `s in [0,1]` of a cell. There is a vector `w in W` with

$$q=c_s+R_{\theta_s}w,\qquad |w|\le R.$$

Define the endpoint images of the same vector by

$$q_a=c_a+R_{\theta_a}w,\qquad q_b=c_b+R_{\theta_b}w.$$

These points lie in the two endpoint forbidden wedges. They need not lie in the original bounding box. However,

$$|q_a-q|,\ |q_b-q|\le D+2R\sin(\delta/2).$$

Therefore **enlarge `B` before clipping the endpoint wedges**, by more than that amount in every coordinate. The implementation uses padding `D+2*R*sin(delta/2)+1`. Both endpoint images then lie in the clipped endpoint wedges.

The corner interpolation is exact. Applying the same second-order interpolation estimate to the vector-valued rotation map gives

$$\left|q-\bigl((1-s)q_a+s q_b\bigr)\right|\le\varepsilon_{\rm sweep},
\qquad\varepsilon_{\rm sweep}=R\delta^2/8.$$

Let `C_i` be the convex hull of the two endpoint wedges, each clipped to the enlarged box. Every intermediate forbidden point of `S_N` is contained in

$$C_i+\varepsilon_{\rm sweep}\overline B_2,$$

where `B_2` is the unit Euclidean disk.

The code does not approximate this disk by an inscribed polygon. Instead, it shifts each supporting halfplane of the convex polygon `C_i` outward by `epsilon_sweep`. Their intersection is a mitered outer offset, which contains the Minkowski sum above. Subtract these offsets from the tightened outer cap for every grid cell.

## Why the construction is not circular

The radius was computed from the raw sampled intersection, whereas the outer-cap tightening is initially applied to a larger convex cap. The final result is nevertheless a subset of `S_N`: each sampled forbidden wedge within `B` is already contained in a neighboring swept hull, and every sampled outer inequality has been tightened. Thus the radius bound applies to every retained point.

A genuinely forbidden point has both inner-wall inequalities strict. Its endpoint images lie in the interiors of the clipped wedges, because of the extra box padding. This gives interior membership in the removed outer offset. Taking the regular closed polygonal difference does not restore such a point merely as a boundary point.

It follows, in exact arithmetic, that the returned construction `S_inner` satisfies

$$S_{\rm inner}\subseteq\bigcap_{0\le u\le1}\bigl(c(u)+R_{\theta(u)}H_\beta\bigr)\cap\{0\le y\le1\}.$$

Keep one positive-area connected polygon component. As explained in THEORY.md, the endpoint strip conditions allow incoming and outgoing translations, completing the motion.

## Observed improvement and limitations

For the frozen 9-knot right-angle path, at 1025 sampled poses:

| Method | Inner-construction area | Raw sampled area |
| --- | ---: | ---: |
| First-order uniform margin | 2.187465851663766 | 2.213028228128224 |
| Swept hull with interpolation margins | 2.2097998645873833 | 2.213028228128224 |

Both inner constructions pass the denser whole-polygon containment check in floating arithmetic. The improved method retains considerably more area, at additional Boolean-geometry cost.

The margins are quadratic in the angular step on a fixed piecewise-linear segment. This is **not a theorem of quadratic area convergence**: convexifying the endpoint wedges can create additional excess area. No convergence rate for the final objective is asserted.

NumPy and GEOS still use floating-point arithmetic. The guard, regression tests, and dense audits are checks rather than a rounding-error proof. Publishing rigorous decimal lower bounds would require exact or interval geometry, validated trigonometry, and area bounds. Neither enclosure method produces a global upper bound over all motions, and neither makes the path-area optimization convex.
