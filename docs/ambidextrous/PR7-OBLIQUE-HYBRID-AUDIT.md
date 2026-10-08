# Can PR #7's near-180-degree sofa beat Romik when combined with Gerver?

**Cross-PR research, October 8, 2026.** The linked
[PR #7](https://github.com/vltanh/lean4-moving-sofa/pull/7)
studies an *actual hallway bend* \(\beta\in(0,\pi)\),
and its reverse-turn convex shape \(S_\varepsilon\)
for \(\varepsilon=\pi-\beta\). The ambidextrous
problem of this PR has *two separate feasible turns
through 90-degree hallways*. The two geometries
are not interchangeable. The objective of this
audit was to try PR #7 as an actual **source of
counterexamples**, not to assume Romik's sharp
optimality.

**Summary.** The unmodified PR #7 near-reversal
extremizer cannot outperform Romik after *any*
uniform scaling and rotation compatible with
both handed turns, even partially/nonmonotonically: Theorem OB1 below
proves a strict bound **288/191 < 1.508 < M**.
Nonuniformly compressed reverse-turn shapes
and independently grafted reverse arcs were
then evaluated anew against the actual pair
of 90-degree full turning constraints and
gave no credible area > M. The PR #7
**forward three-phase contact model** is much
closer after optimizing width, but its apparent
tiny gains disappeared with finer angular
sampling, just as earlier false positives did.
These are *numerical diagnostics*, not global
optimization results and not interval-certified
feasible-area lower bounds.

## 1. Geometry audit: these are not the same 180 degrees

PR #7 defines beta as the **change in travel
direction**, with \(e=\pi-\beta\). At beta=90°
it recovers the ordinary single right-angle
hallway; at beta near 180° its two wall
normals are nearly antiparallel, not perpendicular.
Its near-180° reverse-turn motion rotates the
sofa by only \(e\), rather than by a 90° quarter
turn in each handed direction.

The determinant of PR #7's two outer normal
directions has magnitude \(\sin e\), and
its **translation-only feasible parallelogram**
has area \(\csc e\), which diverges as \(e\to0\).
By contrast, each pair of 90° wall normals
is orthogonal, determinant one. The huge area
of a near-180° sofa comes from a nearly singular
pair of support directions, **not** from free
rectangular material that can be inserted into
two perpendicular quarter turns.

The two historical proof chains also have different
statuses. PR #7's claimed unrestricted optimum
for \(e\le1/8\) is a self-reviewed mathematical draft
with dependent geometric premises and exact scalar
certificates, not a Lean/independently verified
theorem. Its 136.672° forward/reverse **contact-model
crossing is not an unrestricted phase-transition
theorem**. The present argument below needs only
the *explicit feasible reverse shape and its area
formula*, not its conjectured unrestricted
optimality or the crossing.

## 2. Exact hand obstruction to every *similarity* of the reverse optimizer

**Theorem OB1.** Let \(0<e\le1/8\), and let
\(S_e\) be the explicit unit-height convex
reverse-turn sofa constructed in PR #7's
[REVERSE_GEOMETRIC_THEOREM.md]
(https://github.com/vltanh/lean4-moving-sofa/blob/research/arbitrary-hallway-angles-20261005/experiments/hallway_angles/REVERSE_GEOMETRIC_THEOREM.md).
If **any Euclidean similarity image**
\(B=\lambda R S_e+t\), with \(\lambda>0\)
and \(R\) orthogonal, is a compact connected
ambidextrous sofa with **arbitrary continuous
possibly partial or nonmonotone motions**
through both handed 90° hallway bends,
then

\[
\boxed{
|B|<\frac{288}{191}
<\frac{41}{25}<M.
}
\tag{OB.1}
\]

In particular one cannot construct a Romik
counterexample merely by shrinking, rotating
or translating PR #7's entire near-reversal
maximizer. No unproved sharp area inequality
is used to reach the numerical \(288/191\)
bound.

**Proof.** PR #7 gives the explicit area of its
*constructed shape* as
\[
V(e)=\frac e{2-\cos e}
+\frac{1+2\cos e}{4\sin e}
+\frac{3\cos^2 e}{2\sin e\,(2-\cos e)^2}
 \frac{\eta\sin K}{\cos K+\eta\sin K},
\]
where
\[
\eta=\sqrt{\frac{2-\cos e}{2+\cos e}},\qquad
K=\tfrac12\sqrt{e^2+3(e/\sin e)^2}.
\]
The geometric realization proves \(0<K<\pi/2\),
so its last term is nonnegative and the first
term is positive. Since \(0<e\le1/8\),
\[
\sin e\le e\le1/8,\qquad
\cos e\ge1-e^2/2\ge127/128.
\]
Therefore, strictly,
\[
\boxed{
V(e)>\frac{1+2(127/128)}{4(1/8)}
=\frac{191}{32}.}
\tag{OB.2}
\]

The original S_e lies in a horizontal strip
of height 1. Let \(W_e\) be its horizontal
projection width and \(D_e\) its Euclidean
diameter. Fubini gives
\[
D_e\ge W_e\ge|S_e|=V(e).
\tag{OB.3}
\]

Independently, the
[partial-turn three-point width theorem PTW1]
(partial-turn-three-point-width.md)
applies to **any compact connected ambidextrous
sofa with arbitrary continuous motions**.
Write H≤1 for the actual incoming vertical
span of the proposed similarity image B.
If \(|B|\le\sqrt2\,H\), then
\[
|B|\le\sqrt2<288/191
\]
and the claim is immediate. Otherwise
\(|B|>\sqrt2 H\), and PTW1 forces
its common-incoming horizontal width
\(W_B\le2\sqrt2\). The same body lies in
a rectangle of height H≤1, so its
Euclidean diameter is at most
\[
\boxed{\sqrt{(2\sqrt2)^2+H^2}\le3.}
\tag{OB.4}
\]
This step **does not require completing
both original turning motions**.
This diameter conclusion is *rotation-invariant*;
no assumption is made about how S_e was
originally oriented before attempting to
use it in the two-handed 90° problem.

If B is a similarity image, its diameter
is \(\lambda D_e\), and hence
\[
\lambda\le3/D_e\le3/V(e).
\]
Area scales by \(\lambda^2\); thus
\[
|B|=\lambda^2 V(e)
\le\frac9{V(e)}
<\frac9{191/32}
=\frac{288}{191}.
\]
Finally \(288\cdot25=7200<
7831=41\cdot191\), while the
known explicit candidate bound
\(M>41/25\) is elementary. This proves
OB.1, without any numerical
optimization or geometric assumptions
on the similarity orientation. QED.

**Boundary.** The theorem applies to an
*entire PR #7 reverse shape under similarities*
and now covers **every genuinely ambidextrous
motion type**, including partial/nonmonotone
turns, through the area-dependent PTW width gate.
Horizontal-only compression, nonlinear
boundary grafting, and intersection with
other one-turn surviving sets remain
**outside** its scope.

### A more general similarity exclusion principle

The diameter proof actually gives a useful statement
independent of the PR #7 formulas:

**Lemma OB2.** Let A be any compact planar set of
ordinary area \(a>0\) lying in some straight strip
of width at most one. If any Euclidean similarity
image \(B=\lambda R A+t\) is a *connected*
ambidextrous sofa with arbitrary full/partial
continuous turning motions through both right-angle
bends, then

\[
\boxed{|B|\le\max\{\sqrt2,\;9/a\}.}
\tag{OB.5}
\]

Indeed, if its area does not exceed
\(\sqrt2 H\), with H≤1 its actual
incoming vertical span, the first term
applies. Otherwise PTW1 gives diameter(B)≤3.
The original A has diameter at least
its strip-longitudinal projection width,
which by Fubini is ≥a.
Thus \(\lambda\le3/a\), and
\(|B|=\lambda^2 a\le9/a\).
This proof allows **every rotation** of A.

In particular a unit-strip shape with
area \(a>9/M\) can never be turned into
a Romik counterexample by a similarity:
both bounds in OB.5 are then **strictly
below M**. The explicit reverse-turn
shapes of PR #7 satisfy \(a>191/32>9/M\)
in the stated range, which recovers OB1.
This is a general geometric obstruction
to using very elongated, high-area
single-bend sofas as direct two-handed
quarter-turn competitors.

## 3. Reverse PR #7 curved bodies compressed horizontally and retested

To test a non-similarity construction, sample
the actual convex boundary from PR #7's
[reverse_exact.py]
(https://github.com/vltanh/lean4-moving-sofa/blob/research/arbitrary-hallway-angles-20261005/experiments/hallway_angles/reverse_exact.py).
Normalize the vertical strip to [0,1], compress
*only the horizontal coordinate* to a chosen
width W, and take the downward one-turn convex
cap formed by the upper hull roof plus the
entire bottom segment. This operation
**does not preserve the original 180° motions**;
they are discarded.

Instead recompute the support values and
full forbidden niche for every 90° angle
in the **lower** turn, and pair the
one-turn survivor with an independent
vertically reflected upper-turn survivor.
The numerical area of the true angular
continuum envelope is approximated by
an increasingly fine angular mesh and
horizontal quadrature. The resulting
body is an *actual full-two-turn sofa*
whenever the continuous-angle niche
stays below its half-height midline;
the samples show that condition in these
cases, but no interval proof over all
angles is asserted.

At the **fixed Romik horizontal width**
\(W\approx2.334099633\), diagnostic
areas were:

| PR #7 source bend | Source sofa's area | Re-evaluated double-90° intersection |
|---|---:|---:|
| 120° | ≈1.400 | ≈1.4795 |
| 130° | ≈1.640 | ≈1.4495 |
| 136.67° | ≈1.867 | ≈1.4327 |
| 145° | ≈2.280 | ≈1.4152 |
| 155° | ≈3.151 | ≈1.3991 |
| 165° | ≈5.206 | ≈1.3884 |
| 173° | ≈11.115 | ≈1.3836 |
| 177° | ≈25.912 | ≈1.3826 |

The entire reverse candidate initially grows to
huge area, but its shape incurs increasing
collision losses when tested in **both
perpendicular turning geometries**.
In fact at 136.67°, one 45-degree
position of each handed turn *alone*
reduces the area of the self-pair to
about 1.550; the full pair reduces
it further to about 1.433. These are
approximations, not exact certificates.

We additionally flipped one reverse cap
horizontally and paired it with the *actual
Romik one-turn cap*, scanning relative
horizontal translations in [-.45,.45].
The best sampled mixed overlaps were
about 1.570 (120° source), 1.548
(136.67° source), and 1.536 (150°
source), all well below M.

## 4. Grafting reverse *contact arcs* independently

A more creative hybrid does not preserve
the whole reverse shape. Split both PR #7's
compressed cap roof and Romik's cap roof
into left flank, horizontal top face, and
right flank. Reparametrize the PR #7 left
and right flank separately so their
horizontal endpoints match a chosen Romik
face position. Mix the two flank curves
independently with parameters
\(\lambda_L,\lambda_R\), then allow
each parent cap its own face displacement
\(\delta\); take its convex hull.

This produces two truly independent,
potentially asymmetric mixed caps with
**six real parameters**, and their
two-handed full 90° intersection can
be tested against the exact candidate M.
The family includes the reference at
zero parameters, and admits genuine
reverse-only left/right profile grafts
with opposite displacements. Its
90° motions are always recomputed
from its final supports, rather than
inherited from either source hallway.

Two seeded differential-evolution
searches, **832 coarse evaluations each**,
used source bends 136.67° and 173°.
After selecting the best coarse
candidates, refining to **6501 angular
and spatial samples** gave:

| Source reverse bend | Mixed graft candidate | Matching sampled Romik reference |
|---|---:|---:|
| 136.67° | 1.64488085 | 1.64493396 |
| 173° | 1.64488088 | 1.64493396 |

The apparently competitive coarse
grafts lost area on refinement.
The results are not certified lower
bounds or exhaustive optimizers
over the six-dimensional class.

## 5. The *forward* PR #7 contact equations give a closer model

The best positive cross-PR transfer found in
this experiment was **not the 180° reverse
body**, but the distinct
[FORWARD_CONTACT_MODEL.md]
(https://github.com/vltanh/lean4-moving-sofa/blob/research/arbitrary-hallway-angles-20261005/experiments/hallway_angles/FORWARD_CONTACT_MODEL.md)
near the forward/reverse 136.67° candidate crossing.

That source is expressly a **stationary three-phase
signed boundary model**; PR #7 does **not**
claim its entire boundary is geometrically
feasible or globally optimal. For the present
90° experiment we sample its proposed boundary,
take its planar *convex hull*, normalize to unit
vertical height and a horizontal width W,
then recompute the complete **90° turning niches**
from this new cap. Thus no unproved forward
feasibility assertion is imported.

At W=the reference width, the resulting
self-pair has sampled area between roughly
1.6422 and 1.6426 over β∈[135°,140°].
Allowing W to vary gives far closer shapes.
A bounded search over β∈[130°,145°]
and W∈[2.18,2.58] selected
β≈131.5623°, W≈2.40371.

Its apparent area **above** M at
701–7001 angular samples was an artifact.
With a more densely sampled source polygon
and **25,001** angular/spatial samples:

| Candidate | Sampled area | Difference from exact M |
|---|---:|---:|
| Optimized forward-contact transfer | 1.644943283 | −0.000011935 |
| Romik control evaluated with same grid | 1.644960804 | +0.000005586 |

A still larger shape family dropped the
contact equation \(F(\beta,T)=0\) itself:
we varied the central half-interval T
independently of β, built the (possibly
non-matching) signed boundary, convexified
it, normalized width W and recomputed
the **full two 90° turn constraints**.
One differential-evolution run over
(β,T,W) found approximate optimum
(130.4145°, 0.720646, 2.40815).

That candidate again appeared slightly
above M on coarse meshes but gave
**1.64494563** at 16,001 samples,
strictly below the exact M. Even this
off-stationary family did not yield a
credible larger sofa.

An **independently varying two-parent**
forward-contact search over
(β₁,T₁,β₂,T₂,W,relative shift)
likewise showed no improvement after
16,001-sample refinement (area ≈1.6448701).
Some candidates had signed nonempty-fiber
failures outside their occupied region;
connectedness and true continuum
feasibility were not automatically
certified.

## 6. Exact comparison with PR #7's own mode

PR #7 explains the phase difference
analytically. Its forward central contact
equation has characteristic factor
\[
4\sin^2\beta\,\lambda^2+
4\sin^2\beta-3.
\]
At β=90° the corresponding mode is
**oscillatory**, \(\lambda^2=-1/4\);
at β>120° it becomes **hyperbolic**,
\(\lambda^2>0\).
Hence a hyperbolic shape optimized for
a substantially obtuse hallway is not
stationary for the right-angle
one-turn contact problem simply by
changing the corridor label.

This is a concrete reason the close
forward-model transfer still requires
independent retuning and why its
136.67° contact crossing is not a
new Romik-competitor optimum.

## 7. What PR #7 can usefully transfer

**Potentially useful mathematical methods:**

1. Its *canonical support reconstruction* of a
   continuous motion and exact cap-area identities
   can be generalized to analyze nonsmooth
   mixed 90° contact configurations.
2. Its *strict concavity / quadratic deficit*
   for a specified contact class is a model
   for proving that an area gain from
   mismatched one-turn halves cannot
   exceed their individual variational losses.
   In PR #3 language the needed inequality is
   \[
   \boxed{G(U,V)\le
   [M/2-\Psi(U)]+[M/2-\Psi(V)].}
   \]
   The right side is known to be nonnegative
   in the branch's written weighted cap theorem,
   but the left-side **clipping credit** is
   not globally dominated. PR #7 does not
   solve this two-cap issue.
3. Its *corner/strip alignment* lemmas and
   missing-area rectangle capture may inspire
   a proof that a maximizer satisfies a
   more rigid contact geometry. Such a
   transfer would require the true
   *two-handed* 90° support inequalities;
   an oblique single-bend cap lemma alone
   has the wrong pair of normals.

**Explicitly false shortcuts:**
- Claim the near-180° optimizer itself
  can fit two 90° turns by rotation/scaling
  (OB1 disproves it).
- Apply PR #7's optimality bound for
  \(\beta\ge173^\circ\) to a hallway of
  angle 90°. The angles and their
  feasible sets differ.
- Treat a pruned/sampled hybrid as a
  rigorously feasible larger sofa merely
  because its finite grid area exceeds M.
- Identify PR #7's forward/reverse contact
  crossing at ≈136.67° with a global
  transition theorem or a new ambidextrous
  candidate. PR #7 disclaims both.

**Conclusion:** PR #7 contributes a
real analytic framework and a surprisingly
close **forward-model** trial shape, but
the near-180° maximizers' enormous
advantage does *not* survive two
orthogonal right-angle turns. The
numerical hybrids do not beat Romik
after refinement. Romik optimality
is still **unproved**, and the search
does not rule out other counterexamples.

Numerical results are exploratory;
the pure hand proof OB1 rests on the
explicit PR #7 shape-area formula and
the previously written PR #3 width theorem.
Neither research dependency has been
independently refereed or Lean-checked.
