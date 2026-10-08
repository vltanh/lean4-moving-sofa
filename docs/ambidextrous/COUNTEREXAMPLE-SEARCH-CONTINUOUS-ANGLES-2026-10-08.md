# Adversarial search for a sofa larger than Romik: continuous-angle polygon test and independent partial turns

**Scope.** This is a deliberate attempt to **falsify** Romik
optimality rather than assuming the reference candidate is
optimal. The target is one explicitly connected ambidextrous
sofa with true left- and right-hand motions and area exceeding
\[
M=1+4Y^2+\arctan Y
=1.6449552184254408\ldots,\qquad
4Y^3+3Y-1=0,\quad Y>0.
\]
**Outcome:** **NO verified counterexample**. This is a
negative experimental result on explored classes, not proof
of local or global optimality. Real counterexamples may
lie outside all searched parameterizations.

New reproducible source:
- [all_angle_polygon_pair.py](computer-assisted/all_angle_polygon_pair.py):
  algebraic finite-candidate evaluation of the *full continuous
  turning-angle envelope* of any pair of convex polygonal one-turn
  caps, with numerical quartic roots and numerical horizontal
  integration.
- [test_all_angle_polygon_pair.py](computer-assisted/test_all_angle_polygon_pair.py):
  independent 30,001-angle and hull-facet crosschecks.
- [explore_partial_turn_paths.py](computer-assisted/explore_partial_turn_paths.py):
  optimization of two independent continuous moving hallway
  corner paths, including terminal angles **strictly below
  90 degrees** and explicit outgoing straight strips.
- The previous
  [explore_romik_counterexamples.py](computer-assisted/explore_romik_counterexamples.py)
  is an older *finite-angle* diagnostic and must not be
  mistaken for a counterexample certificate.

No Lean/Lake formalization or numerical *global* area upper
bound was attempted. All exploration was on the PR #3
pen-and-paper research branch.

## 1. An actual mathematical strengthening of counterexample verification

Let P be a **convex polygonal one-turn cap** of
vertical span at most one. At a conventional
turn angle \(0<t<\pi/2\), let the two actual
upper supporting vertices be
\(F=(X,Y)\) for normal \(u_t=(\cos t,\sin t)\)
and \(G=(P,Q)\) for normal
\(v_t=(-\sin t,\cos t)\).
On any *support sector* where those two
vertices stay fixed, its two forbidden
inner-wall height functions at abscissa x are
\[
\boxed{\begin{aligned}
W_1(t,x)&=\frac{(X-x)\cos t+Y\sin t-1}{\sin t},\\
W_2(t,x)&=\frac{(x-P)\sin t+Q\cos t-1}{\cos t}.
\end{aligned}}
\tag{CA-1}
\]
The actual full positive forbidden-niche height is
\[
n_P(x)=\max\bigl(0,\sup_{0<t<\pi/2}
                 \min(W_1(t,x),W_2(t,x))\bigr).
\tag{CA-2}
\]

**Lemma CA-ANGLE.** For **each fixed x**, the
supremum CA-2 occurs among finitely many
algebraic candidates:
1. endpoints of support sectors where a
   maximizing polygon vertex changes;
2. interior stationary points of W₁
   satisfying \(\cos t=X-x\);
3. interior stationary points of W₂
   satisfying \(\sin t=x-P\);
4. intersections of the two walls, characterized by
   \[
   \boxed{
   x=X\cos^2t+P\sin^2t+
   (Y-Q)\sin t\cos t-\cos t+\sin t.
   }
   \tag{CA-3}
   \]
   At a crossing, the corner's x-coordinate
   equals the slice abscissa.

**Proof.** On each fixed-support sector,
the two wall heights are analytic.
A local maximum of their minimum
is either a stationary point of the
active wall or a point at which the
active wall changes; in the latter
case the two wall values coincide.
The compact sector endpoints are
the remaining candidates. Since
there are finitely many polygon vertices
and finitely many roots of the resulting
algebraic equations (or harmless
identically-zero special cases),
the candidate set is finite after
coincident branches are merged. QED.

To implement CA-3 without overlooking
a nonmonotone corner-x map, split each
fixed-support sector at critical points
of its derivative. In terms of
\(z=\tan(t/2)\), put
\(d_x=P-X,\ d_y=Y-Q\).
The derivative vanishes exactly where
\[
\boxed{
(d_y-1)z^4+(2-4d_x)z^3
-6d_yz^2+(2+4d_x)z+(d_y+1)=0.
}
\tag{CA-4}
\]
For each resulting monotone sub-sector,
a crossing of CA-3 can be found by
bisection. **This uses a genuine continuum
of angles**: the angular positions of
the maxima are computed from the polygon
itself and the selected x, not sampled
on a uniform mesh.

The implementation uses floating-point
quartic roots and bisection, so CA-ANGLE
is a mathematical candidate-reduction
lemma, **not** a computer-certified proof
of completeness or rigorous area bounds.
Horizontal area is still integrated
by trapezoidal quadrature.
Neither an upper nor a lower rigorous
area enclosure is inferred merely from
this algorithm.

## 2. Independent numerical validation of CA-ANGLE

The validation applied nine convex
polygonal caps, including a sampled
Romik cap and eight randomized affine/
curvature-modified caps. At **31 separate
x-coordinates each**, it compared CA-ANGLE's
niche value with an independent maximization
over **30,001 distinct conventional angles**.
In all nine tests, the algebraic candidate
method's output was **never below** the
independently sampled maximum (up to
\(8\cdot10^{-16}\) floating error in the
reference case). The worst discrepancy
between the polygon's upper roof and an
independent formula using its exact outward
supporting facets was below \(2\cdot10^{-11}\).

The executed test printed
“PASS: 9 polygon caps, 31 x values each,
30,001 sampled angles per point.”

The test is a valuable **negative control**.
It cannot rule out a missed nearly multiple
quartic root, an untested shape or a
defect in numerical spatial integration;
it is not a proof of the optimum.

## 3. Test 1: keep one exact reference half, strongly vary the other

The upper parent was represented by a
convex polygon sampled from the exact
Romik support formula. The other parent
was allowed twelve independent parameters:
horizontal width scaling, high-y shear,
five local upper-roof variations, and
five horizontal distortions. Convex hulls
were rebuilt from the resulting vertices
on every objective evaluation.

A seeded **differential-evolution search made
6,552 objective evaluations**. Its best
*coarse* finite-angle area was about
1.645267, versus the same mesh's
polygon reference benchmark of about
1.645267—an apparent sub-micro-unit gain,
not a credible counterexample.

The continuous-angle test of that selected
candidate, using the same two polygonal
parents for refinement, gave:

| horizontal samples | identical polygonal Romik parents | optimized unequal pair |
|---|---:|---:|
| 1,201 | 1.644923687 | 1.644908607 |
| 4,001 | 1.644927964 | 1.644909464 |
| 12,001 | 1.644928278 | 1.644909731 |

The refined asymmetric candidate is
**smaller than both** its corresponding
polygon reference and the exact analytic
Romik target M. Its occupied portion
has a single numerically resolved connected
x-component. No counterexample was found.

Because the polygon approximates but does
not equal Romik's smooth curved cap, the
polygon benchmark is intentionally
distinguished from the analytic M.

## 4. Test 2: two independently variable polygon parents

The same cap-vertex parameterization was
applied **independently to both parents**,
for 24 real parameters. Multiple Powell
searches from both the reference and
randomized starting profiles were run;
all used fresh convex hulls to permit
new support facets and nonlinear curvature
changes.

The best coarse-grid candidate was again
a tiny perturbation of the reference.
After maximizing the full continuum-angle
niches and refining the horizontal mesh,
its area was approximately
**1.644908**, versus approximately
**1.644928** for the reference polygon
of the same resolution. Substantially
deformed candidates were smaller.
The early coarse-grid pseudo-improvements
vanished after CA-ANGLE validation.

This is not exhaustive: neither the 24-parameter
family nor Powell optimization spans arbitrary
convex caps.

## 5. Test 3: abandon Gerver caps; optimize two turning *motions*

An even broader search parameterized the
**locations of the hallway inner corners
as functions of turning angle** for the
two handed turns. In moving hallway coordinates,
an inner corner c(t) supplies exact outer-wall
offsets
\[
f(t)=1+c(t)\cdot u_t,\qquad
g(t)=1+c(t)\cdot v_t.
\tag{CA-5}
\]
Thus the placed L-shaped hallway is determined
by a continuous corner path; the path
need **not** arise as a canonical support
path of a prior convex cap.

Each handed route turns over
\[
0\le t\le\alpha_j,\qquad
\alpha_j\le\pi/2.
\]
At the **terminal angle**, the
required outgoing straight-strip
condition is imposed explicitly:
\[
f(\alpha_j)-1\le p\cdot u_{\alpha_j}
\le f(\alpha_j)\quad(p\in S).
\tag{CA-6}
\]
Both routes share the same initial incoming
unit strip. Their intersection is a sofa
only if **connected** and feasible along
the **entire continuous path**; sampled
angles alone do not certify this.

One differential-evolution run over
16 independent corner-trajectory/terminal-angle
parameters made **7,808 objective evaluations**,
without fixing symmetry or full turns.
Its largest coarse candidate area was
about 1.636960.
After refinement to 3,201 spatial/angle samples
it was about **1.635940**, versus
about **1.644998** for the same sampled Romik
motion. The best run's terminal-turn
shortfalls were around .00224 and .01233
radians, *near* full quarter turns.

Two separate Powell optimizations over
26 trajectory variables reinforced this
qualitative picture:

* Starting from a substantially perturbed,
  partly turning path, the objective grew
  from ≈1.357 to ≈1.641, while the optimized
  terminal angles moved very close to 90°.
* Starting from Romik's actual full-turn
  path, the best improvement at 801/1,001
  angular sampling was only ≈0.000002.
  On 4,001-point refinement its area
  was ≈1.64499008, **below** the matching
  sampled Romik reference ≈1.64499303.

All numbers in this section are **sampling
diagnostics**, not true feasible lower
bounds. In particular, the finite-angle
motions could collide between samples;
this is why they are not promoted as
new moving sofas.

## 6. A meaningful stop criterion

A real challenge to Romik requires all three:

1. an explicit connected sofa set S
   (a polygon or controlled algebraic
   boundary suffices);
2. actual continuous left- and right-turning
   motions, including their outgoing
   straight strips, with **no uncovered angles**;
3. a mathematically certified ordinary area
   lower bound exceeding
   \(M=1.6449552184254408\ldots\),
   e.g. **area ≥329/200=1.645**.

This iteration supplies neither such an S
nor any numerical candidate whose high-resolution
values point convincingly above M.
It improves the *adversarial testing*
of two alternate geometric models: arbitrary
polygonal one-turn caps checked against the
angle continuum, and independent partially
turning motion paths.

**Conclusion:** Romik **may** be nonoptimal;
this investigation did **not** disprove it.
No amount of these finite tests proves
that an unexamined shape cannot beat it.
The important outcome is a reusable
falsification-checking method that
makes the earlier false positive mechanism
explicit rather than repeating small,
uncalibrated grid improvements.

For actual global optimality, the
decisive unresolved questions remain
how to bound the interaction of **arbitrary**
one-turn caps and how to admit or
exclude all competitive partial-turn
motions. There is no reason to invent
another small Romik perturbation merely
to produce another near-M inequality.

No Lean, CI or independent peer review
was performed in this iteration.
