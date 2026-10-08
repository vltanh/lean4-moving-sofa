# Trying to falsify Romik ambidextrous optimality (October 8, 2026)

**Question:** Could an asymmetric or even disconnected-looking
alternative beat Romik's feasible area
\[
M=1+4Y^2+\arctan Y,\quad
4Y^3+3Y-1=0,\quad
M\approx1.6449552184254408?
\]
**Answer:** The conjecture remains open. This research run
actively tried to produce an area *larger* than M using
independently varying one-turn parents, actual Gerver
one-turn shapes, localized irregular hull boundary
modifications, and larger opposite shears of Romik's
curved core. **No feasible, certified counterexample was
found.** These are **exploratory computational
diagnostics, not proofs of optimality or local maximality**.

No Lean formalization was performed. The exact
Romik support formulas come from the repo's
[reference note](romik-horizontal-misalignment-sharp-bound.md).
The Gerver continuous path comes from the existing
[scripts/figures/gerver.py](../../scripts/figures/gerver.py).
A compact reproducible exploration driver is at
[computer-assisted/explore_romik_counterexamples.py]
(computer-assisted/explore_romik_counterexamples.py).

## 1. A particularly simple exact target to falsify Romik

**Lemma CE-THRESHOLD.**
Every connected sofa with both actual handed motions
and certified ordinary area **at least**
\[
\boxed{\frac{329}{200}=1.645}
\tag{CE.1}
\]
would be a rigorous counterexample to Romik optimality.

**Proof.** Put \(x=7451/25000=0.29804\).
The defining cubic is strictly increasing
on the positive reals and
\(4x^3+3x-1>0\), so \(Y<x\).
Since \(z\mapsto1+4z^2+\arctan z\)
is increasing on \(z>0\), and the
alternating arctangent series gives
\(\arctan x<x-x^3/3+x^5/5\),
\[
\begin{aligned}
M&<1+4x^2+x-x^3/3+x^5/5\\
&=\frac{240966349588674380186753}
{146484375000000000000000}\\
&<\frac{329}{200}.
\end{aligned}
\]
The final strict positive difference is exactly
\[
\frac{329}{200}-
\frac{240966349588674380186753}
{146484375000000000000000}
=
\frac{447286325619813247}
{146484375000000000000000}>0.
\]
All of these comparisons use rational arithmetic
except the rigorous alternating-series inequality,
which holds for \(0<x<1\).
QED.

This gives a clean acceptance criterion for
any future rational polygon/curve construction:
an *actual* connected two-turn motion together with
a rigorous area lower bound ≥1.645 suffices.
A floating grid result slightly above 1.645
does not suffice.

## 2. How candidate areas were evaluated (NOT rigorous certification)

Take two compact convex downward one-turn caps P,Q
represented by planar hull vertices in the
incoming unit strip. At each proper lower
turn angle \(t\in(0,\pi/2)\), use the true
outer supports
\[
f_P(t)=h_P(\cos t,\sin t),\quad
g_P(t)=h_P(-\sin t,\cos t)
\]
and the genuine forbidden-corner wall roof
\[
H_P(t,x)=\min\left(
\frac{f_P(t)-1-x\cos t}{\sin t},\
\frac{g_P(t)-1+x\sin t}{\cos t}
\right).
\]
Let \(A_P(x)\) be the upper convex-hull roof and
\(n_P(x)=\max(0,\sup_t H_P(t,x))\)
the *full continuum-angle* niche roof;
define A_Q,n_Q analogously.
Then the true full-turn two-cap envelope E has
vertical length, for x in the common horizontal
projection,
\[
\ell(x)=\left[
\min(A_P(x),1-n_Q(x))-
\max(n_P(x),1-A_Q(x))
\right]_+.
\tag{CE.2}
\]
It is feasible for both turn families when
its occupied set is connected and the
parent-canonical hallway paths are continuous.
If \(\ell(x)\) has a nontrivial gap,
the union of two disconnected components is **not**
one sofa and its combined area must not be
credited to one feasible body.

For exploration, the angle supremum was replaced
by a finite angular grid and \(\int\ell(x)dx\)
by trapezoid quadrature. The finite angular
sampling *omits true collision constraints*
and can falsely **increase** the reported area.
Spatial quadrature can err in either direction.
No result below is a validated **lower bound**
on feasible area, and none is an upper bound
on all possible sofas. The analytic reference
M is used as a calibration standard.

## 3. Original Gerver copies are a poor starting counterexample

Using the Gerver rotation path already written in
the repository and numerically intersecting the
unmodified one-turn sofa with its vertically
reflected copy (common natural incoming frame):

| Shape used | Sampled planar area | Connected components |
|---|---:|---|
| One Gerver sofa | ≈2.2195 | one |
| Two reflected Gerver sofas, unshifted | ≈1.475 | **two**, ≈0.737 each |
| Romik's actual ambidextrous sofa | \(M\approx1.6449552\) | one |

The Gerver intersection is **disconnected**;
calling its combined area a moving sofa
would already be a serious logical error.
Moreover even its combined sampled area is
far below Romik's.

Moving one of the two Gerver copies horizontally
through sample offsets ±0.75 did not improve
the *combined* sampled overlap beyond ≈1.475.
This is **not** an exhaustive continuous-offset
maximum certificate.

Mixing an unchanged Gerver one-turn sofa with
Romik's modified one-turn survivor, adjusting
their relative horizontal placement, produced
combined sampled overlaps around 1.33 or below
in a finite offset scan. The natural mixed
intersection also has empty vertical fibers
at some abscissae; its combined area is not
automatically a connected sofa.

**Interpretation:** Simply intersecting unmodified
Gerver sofas, or pairing one Gerver with one Romik
half, is not a promising counterexample at the
sampled placements. The special Romik modification
substantially changes how much central material
survives **both** turns.

## 4. Two-parent asymmetric cap search near and away from Romik

One starting representation was the exact
Romik one-turn support curve sampled densely
and converted to a convex polygon.
The independent parent hulls were perturbed in:

* horizontal extent and opposite horizontal shifts;
* y-dependent horizontal shears;
* odd/even/asymmetric changes to the upper roof;
* localized Gaussian raises/shaves or narrow
  polygonal facets.

Each candidate's supports were recomputed
from its **actual polygonal convex hull**.
The full lower/upper finite-angle niches were
then computed from CE.2. Disconnected candidates
were not accepted as feasible counterexamples.

**Exploratory diagnostics only:**

1. Three independent differential-evolution runs
   over twelve real cap-shape variables
   (3,360 area evaluations each) produced
   larger-area candidates only when compared with
   other *perturbed* candidates, not against the
   accurate Romik reference. Their refined
   representative areas were approximately
   1.643095, 1.642758 and 1.641639.
2. Three Powell local runs, begun near Romik
   with independently variable upper/lower caps,
   likewise produced no refined area greater
   than the exact M. One candidate looked
   above M at a coarse spatial/angular mesh but
   dropped below M after refinement.
3. A scan of **972** localized perturbation
   combinations (vertical changes, horizontal
   changes, facet-like raises/shaves; nine
   centers, three widths, four signs/magnitudes,
   three parent-pair choices) revealed a
   valuable **false positive**. For example
   raising the self-paired roof by
   \(0.015\,y(1-y)e^{-(x-0.6)^2/(2\cdot0.22^2)}\)
   appeared to gain roughly \(5\cdot10^{-6}\)
   relative to a polygonal Romik baseline on
   a 1201×901 integration mesh. On a
   4501×2501 mesh the difference changed sign
   to about \(-1.8\cdot10^{-6}\).
   Thus **the apparent counterexample vanished**.
   Other apparent gains had empty vertical
   fibers and failed connectedness.
4. A deliberately **nonlocal** rectangular-core
   test swept **841** pairs of actual Romik-core
   horizontal shear parameters
   \((d_1,d_2)\in[-0.14,0.14]^2\),
   sampled on the 29×29 lattice.
   The best sampled area was at \(d_1=d_2=0\).
   At a shear as small as 0.01 in one parent,
   the relative sampled loss after refinement
   was already around \(1.7\cdot10^{-4}\).
   All these shears are much larger than
   the tiny neighborhood guaranteed by the
   branch's prior analytic two-shear result.
   This is still a **finite exploratory scan**,
   not a global optimization certificate over
   the shear square.

The implementation of the reference polygonization,
finite-angle niches, Gerver-components check and
nonlocal shear diagnostic is retained in the
reproducible driver linked above.
The more general twelve-variable optimization and
Gaussian-mode scans were run locally;
their numerical results are recorded here as
**search diagnostics**, not as theorem premises.

## 5. What this does and does not tell us

**No larger candidate was verified.** That does
*not* demonstrate that Romik is locally maximal,
globally optimal, or necessarily symmetric.
Many possible counterexample mechanisms lie
outside these tested shape families:

1. a **strongly different asymmetric pair**
   of one-turn caps with large interaction/clipping;
2. discontinuous changes of curvature support,
   different widths, or thin new facets beyond
   any fixed smooth perturbation model;
3. two valid **partial-turn** paths that have
   not been canonically completed to full turns;
4. shapes whose true contact history cannot
   be inferred from a simple preset cap
   interpolation without an independent
   feasibility verification.

A credible falsification should provide:
- an explicit connected shape (polygon or
  controlled algebraic arcs);
- complete continuous left and right rigid motions
  through unit corridors, without relying only
  on sampled-angle containment;
- a **rigorous ordinary-area lower bound**
  exceeding M (or the simpler exact target
  329/200 in CE.1).

If this cannot be supplied, report a proposed
numerical candidate **only as exploratory**.
Conversely a family that withstands fine mesh
refinement but remains below M is not a
proof of optimality.

## 6. Decision

The tests fail to overturn Romik's candidate
within the probes attempted here. They also
identify an exact danger: a grid error on the
order of \(10^{-5}\) is easily large enough
to produce a **false alleged improvement**.
Future computational counterexample searches
need a geometry-aware error bound before
advertising results near 1.645.

The most plausible genuinely new falsification
target is not another tiny Gaussian modification
of Romik, but a substantially different,
connected asymmetric *pair of one-turn survivors*
or a partial-turn construction outside the
known full-turn cap reductions.

No conclusion about unrestricted maximality
is inferred, and no Lean formalization or CI
work was performed.
