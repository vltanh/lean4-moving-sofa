# Elementary upper bounds for the two aligned-endpoint motion classes

These bounds use a single intermediate hallway and horizontal cross-sections, not the uniqueness proof. They bound the two `Motion` classes, **not all arbitrary-angle moving sofas without an additional motion reduction**. In particular, no result here excludes partially rotated or more complicated motions outside those classes. No novelty claim is made for these elementary estimates.

Let the bend be beta in (0,pi), write s=sin(beta/2)>0 and c=cos(beta/2)>0, and normalize the entry strip to 0 <= y <= 1. The sofa is contained in this strip throughout the body-fixed description.

## Forward class: area <= 2 csc(beta/2)

At the midpoint hallway angle beta/2, translate the inner corner horizontally to (0,z). The two unit outer-wall normals are (-s,c) and (s,c). Membership in the hallway is equivalent to

    0 <= s |x| + c(y-z) <= 1.

For a fixed y, put d=c(y-z). If d>1 the section is empty. If 0<=d<=1 its length is 2(1-d)/s. If d<0 it is the union of two intervals with total length 2/s. Thus the length is at most 2/s at every height. Integration over the entry strip gives the assertion, without a connectedness assumption.

## Reverse class: area <= sec(beta/2)

At the midpoint angle (beta-pi)/2 the two normals are (c,s) and (c,-s). With corner (x0,z), hallway membership is

    0 <= c(x-x0) + s |y-z| <= 1.

Every horizontal section is an interval of length exactly 1/c. Its intersection with 0<=y<=1 therefore has total area 1/c, irrespective of the corner translation. Any sofa in this class has at most that area.

## What this does and does not imply

The larger of these bounds is an upper bound for the UNION of the two tested classes. The maximum of numerically optimized sampled-intersection areas is not an upper bound, even for that union. A trajectory need not be monotone for the argument if its orientation is continuous and passes through the stated midpoint while its entry pose has the stated alignment. But showing that every globally maximizing sofa admits one of these aligned-endpoint descriptions is a separate theorem, not supplied here.

The estimates are deliberately crude. They are useful sanity checks and expose a real upper/lower gap rather than mistaking a local optimizer's output for an optimum.

## Second-round checkpoint

The boundary-gradient implementation agrees with central differences on all free coordinates of perturbed nine-pose examples at bends 30,60,90,120,150 degrees in both directions (test tolerance 2e-6). Coincident endpoint walls at the symmetric 90-degree reverse seed produce genuine nondifferentiability; this is explicitly tested rather than asserting differentiability there.

A cubic-basis right-angle search with 33 controls and 513 poses gives sampled area 2.220683662188335. The *same exported piecewise-linear path*, without further optimization, has swept-enclosure inner area 2.216806093076189 at 1025 poses, 2.2188489119104755 at 4097 poses, and 2.2193575926742546 at 16385 poses. These are floating-point constructions. The apparent above-Gerver sampled values are artifacts, not improvements to the known optimum.

The bounded-size rectangular-cut implementation agrees with the original cap-clipped implementation to symmetric-difference area below 7e-16 on six checked examples. Its set-theoretic equivalence is C minus (W intersect B) = C minus W for C subset B. This makes much denser checks practical without weakening the continuous-motion enclosure argument.
