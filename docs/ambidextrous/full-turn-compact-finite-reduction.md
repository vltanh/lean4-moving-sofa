# Compact global finite relaxations and a certified finite-to-full conversion

**Scope.** This gives an end-to-end finite-dimensional formulation of the *unpenalized full-turn value*, with a proved compact parameter box, attainment, and an explicit error bound when finitely many orientations are replaced by both continuous quarter turns. It uses the actual-body gap-compression theorem GC rather than assuming that every finite envelope is connected. It does not compute the global finite optima or prove their limit equals Romik's M. The quantitative conversion is not a floating-point convergence observation. Labels FR are local.

Inputs: canonical support-depth tightening and GC1--GC4 in `horizontal-gap-compression.md`. The finite midpoint upper bound MH is independent of the long weighted-cap chain. No weighted-maximizer, smooth-contact, or curvature hypothesis is used.

## 1. A rational-angle width bound for every connected candidate

Fix the lower hallway with orthonormal normals u=(3/5,4/5), v=(-4/5,3/5). Let S be compact, contained in a horizontal strip of actual height H<=1, with projection extremes l,r. Its actual support depths satisfy

$$h_S(u)-p\cdot u\ge(3/5)(r-p_x)-(4/5)H,$$
$$h_S(v)-p\cdot v\ge(4/5)(p_x-l)-(3/5)H.$$

If p survives this hallway, at least one depth is at most one. Consequently

$$p_x\ge r-(5+4H)/3\ge r-3\quad\text{or}\quad
p_x\le l+(5+3H)/4\le l+2. \tag{FR.1}$$

If S is connected, its projection is [l,r], so FR.1 implies r-l<=5. If it is disconnected, its projection D has Lebesgue measure at most five. GC's map T(x)=integral_l^x 1_D collapses exactly the empty projection gaps; vertical filling then gives a connected set with at least the original area, the same vertical extrema, and all the same prescribed hallway and endpoint-strip constraints. For a finite or full canonical envelope its fibers are intervals or empty, so the area is preserved exactly. The resulting horizontal width is |D|<=5.

After translation every such connected representative lies in

$$\boxed{[0,5]\times[0,1],\qquad \operatorname{diam}(S)\le\sqrt{26}<6.} \tag{FR.2}$$

No competitive-area threshold or earlier computer-certified width bound is used here.

## 2. Full-turn attainment in this compact class

Let A_F be the supremum of areas of compact connected bodies with both complete conventional quarter turns and incoming height at most one. FR.1 bounds the horizontal width of every such body by five; translate its bottom and left extrema to zero.

A maximizing sequence in the fixed compact rectangle has a Hausdorff-convergent subsequence. The limit is nonempty, compact and connected. The last assertion follows because a separation of the limit into two positively separated compact pieces would separate every sufficiently close approximant. Support functions converge uniformly, so each closed support-depth disjunction at each fixed angle passes to the limit. The unit incoming strip and full endpoint strips also pass to the limit. Continuous support-tightened corner translations give the two actual continuous motions of the limiting body.

Area is upper semicontinuous on compact subsets of a fixed bounded rectangle: an approximant eventually lies in any fixed neighborhood of the limit, and the areas of those neighborhoods decrease to the limit's area. The limiting area is therefore at least the limsup of the maximizing sequence. It cannot exceed A_F by feasibility.

**Theorem FR1.** A_F is attained by a compact connected full-turn body in [0,5] times [0,1]. In particular the actual-maximizer premise of FV1 can be supplied independently of the weighted-cap attainment theorem.

## 3. Fully specified compact finite offset problems

For even n>=2 let

$$\Theta_n=\{2\arctan(j/n):j=0,\ldots,n\}\cup\{\pi/4\}.$$

Take both conventional sampled hallway families indexed by Theta_n and pi+Theta_n, including their endpoint frames. This contains the rational-angle hallway of Section 1 (j=n/2) and the two midpoint hallways of MH. Under dyadic refinement the angle sets are nested.

Use a real offset h(theta) at every frame-normal direction theta. At the four axes impose

$$h(0)=W\in[0,5],\quad h(\pi)=0,\quad
h(\pi/2)=H\in[0,1],\quad h(3\pi/2)=0.$$

Every other offset ranges independently in [-6,6]. Define E_n(h) by intersection of the finite hallway sets with these offsets. The axis frames enclose E_n(h) in [0,W] times [0,H]. Its fibers are intervals or empty; it is compact, possibly empty or disconnected. No convex-support consistency condition is imposed on the proposed offset list.

Let

$$A_n=\max_h |E_n(h)|$$

over this compact box. The maximum exists: for convergent offsets, membership can change only on the finite union of limiting wall lines, a planar null set, so dominated convergence gives continuity of area.

This box captures the entire finite relaxation, not merely a selected region. Any compact set satisfying those sampled hallways can first be tightened to its actual support offsets, compressed by GC, vertically filled, and translated into the rectangle FR.2 without losing area. Its actual support values then lie in [-sqrt(26),sqrt(26)] and have the prescribed axis values. Tightening again and taking the finite envelope cannot decrease area. Conversely every E_n(h) in the box is sampled-feasible and GC turns it into a connected sampled-feasible body of exactly the same area. Therefore A_n is the unrestricted sampled value, including the total areas of disconnected finite envelopes.

The objective is a continuous piecewise quadratic polynomial in the offsets. Intersections of two fixed nonparallel wall lines depend affinely on the offsets; the event that such an intersection crosses a third line is a linear condition. Parallel-line order changes are also linear conditions. The finitely many resulting polyhedral arrangement cells have fixed boundary combinatorics, and shoelace area is quadratic there. Degenerate cells are retained by continuity. The coefficients lie in Q(sqrt(2)): all j/n normals are rational and the added midpoint normals have coordinates 1/sqrt(2).

The existing D1 critical-face reduction can therefore solve each cell by finitely many exact linear-algebra candidates, including boundary faces and singular ridges. **No enumeration of all these cells is claimed to have been run.** Finite describability is not a statement that the full enumeration is short.

## 4. A uniform conversion of any sampled set into a full-turn sofa

For a compact set S in FR.2 and p in S, define its support depth

$$D_S(p,z)=h_S(z)-p\cdot z=\sup_{q\in S}(q-p)\cdot z.$$

For unit normals z,z',

$$|D_S(p,z)-D_S(p,z')|\le\operatorname{diam}(S)|z-z'|<6|z-z'|. \tag{FR.3}$$

Parameterize the upper-right unit normals by

$$N(r)=\left(\frac{1-r^2}{1+r^2},\frac{2r}{1+r^2}\right),\qquad0\le r\le1.$$

Direct algebra gives

$$|N(r)-N(q)|=\frac{2|r-q|}{\sqrt{(1+r^2)(1+q^2)}}\le2|r-q|. \tag{FR.4}$$

Every r has a nearest j/n at distance at most 1/(2n). Thus both normals of its orthonormal hallway frame are within 1/n of the corresponding sampled normals. Whichever sampled inner wall protects p has depth at most one; its corresponding intervening wall has depth at most 1+6/n by FR.3. This argument is pointwise and does not assume the protecting wall stays the same as r varies.

Uniformly shrink S by

$$\boxed{\lambda_n=(1+6/n)^{-1}.}$$

Every support depth is multiplied by lambda_n. The shrunk set therefore satisfies both hallway families at **every** angle, not just the mesh. Its height remains at most one, it is still connected, and its continuous actual support gives continuous full motions with valid endpoint strips.

**Theorem FR2 (certified value bracket).**

$$\boxed{\frac{A_n}{(1+6/n)^2}\le A_F\le A_n\le2\sqrt2-1.} \tag{FR.5}$$

The upper bound A_F<=A_n follows by dropping constraints; the last bound is MH because the mesh contains both midpoint hallways. For the lower bound take a maximizing finite envelope, apply GC to connect it without area loss, and apply the uniform shrink just proved. Thus

$$0\le A_n-A_F\le(2\sqrt2-1)\left[1-(1+6/n)^{-2}\right],$$

and A_n tends to A_F. Along dyadic n, the upper sequence is nonincreasing. Choosing the connected shrunk finite maximizers and taking a Hausdorff subsequence produces an actual full-turn maximizer, with areas converging to A_F.

This provides a legitimate finite-to-continuum maximizing sequence for the unpenalized problem. It does not assume that a sampled maximizer's unshrunk polygon is continuously feasible. It also does not supply curvature or contact-order control of the limit.

A certified computed upper bound B_n>=A_n would give A_F<=B_n. A certified area a of one feasible sampled configuration would give A_F>=a/(1+6/n)^2. An untrusted optimizer's sampled value is not B_n; it supplies no global upper bound.

## 5. Why a fixed finite mesh alone cannot prove equality with M

For every finite set of hallway orientations containing the endpoint frames, the reference Sigma lies in the corresponding finite envelope using its actual support offsets. The boundary of that envelope lies in finitely many wall lines. Choose a point p on one strictly curved, retained outer arc of Sigma, away from the strip axes and every one of those lines. Such a point exists because an open strictly convex outer arc cannot be contained in finitely many lines.

Then p is an interior point of the finite envelope: no finite constraint is active there. A small closed disk centered at p is contained in that envelope, and has a positive-area portion outside the reference convex hull, since p is on its supporting boundary. The connected set Sigma union that disk is sampled-feasible and has area strictly greater than M.

**Lemma FR3.** Every finite orientation-only relaxation of this kind has optimum strictly greater than M. In particular A_n>M for every finite n, independently of whether A_F=M is ultimately true.

Consequently merely refining the mesh and asking for an exact finite upper bound <=M cannot succeed. A proof of the exact value needs a uniform analytic estimate followed by a limit, a sharp residual-neighborhood theorem, or additional valid constraints beyond finitely many placements. FR.5 supplies a rigorous convergence modulus but does not identify its limit as M.

## 6. Remaining proof obligation

The globally sharp full-turn value is still unknown in this work. The remaining structural issue is to control the limiting maximizing geometry or prove a sharp global inequality. Finite maximizers may occur at wall ties or have hidden hull edges; free-offset stationarity alone still does not replace exposed boundary length by the full convex-hull curvature measure.

This note removes conditional attainment, unbounded parameter escape, disconnectedness, and uncertified angular interpolation from the *finite-to-continuum reduction*. It does not claim that those removals prove the final area constant. No CI, Lean/Lake compilation, dependency installation, manuscript build or long optimization was used.