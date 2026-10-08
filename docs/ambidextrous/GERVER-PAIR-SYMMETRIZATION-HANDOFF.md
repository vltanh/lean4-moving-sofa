# Can arbitrary interacting Gerver-like halves be replaced by identical halves?

**Research status, October 8, 2026.** Unrestricted Romik
optimality is **not proved**. The goal of this iteration
was specifically to test a structural reduction of an
arbitrary *two-half* one-turn intersection into an
identical-parent (symmetrically paired) intersection,
without appealing to unrelated coarse numerical bounds.
No Lean formalization, CI, or global area optimizer was
performed.

## A definitive negative control near the sharp candidate

[PII1/PII2](pair-versus-identical-romik-obstruction.md)
shows an exact **anti-Jensen** identity on two
midline-saturated one-turn caps whose complete positive
niches are confined to their own top-face intervals:

\[
\boxed{
|E(U,V)|-\frac{|E(U,U)|+|E(V,V)|}{2}
=G(U,V)\ge0.
}
\tag{GP.1}
\]

The correction G is the exact ordinary-area
clipping recovered by pairing two different
one-turn survivors. It may be *strictly*
positive, so merely selecting the larger
of the two identical-parent constructions
does not preserve area.

More decisively, let U_{+δ},U_{−δ} be
**oppositely sheared copies of the actual
Romik curved one-turn cap**, with
0<|δ|≤1/2000. Their two self-pair sofas
have exactly equal area by horizontal
reflection, yet the mixed sofa has
strictly larger area:

\[
\boxed{
|E(U_{+δ},U_{−δ})|
>|E(U_{+δ},U_{+δ})|
=|E(U_{−δ},U_{−δ})|.
}
\tag{GP.2}
\]

All three are **actual connected sofas
with both complete 90-degree turns**
and their areas approach M as δ→0.
The mixed shape remains strictly below
M by the already written sheared-core
sharp theorem SCR. The proof of the
*strict relative gain* needs only the
elementary niche-positive endpoint test
and the exact clipping formula.
This is not a counterexample to Romik
optimality or to the possible existence
of a **globally** symmetric maximizer.

**Stop rule:** Never again try to
prove the global symmetrization statement
\( |E(U,V)|\le\max(|E(U,U)|,|E(V,V)|)\).
It is false arbitrarily close to Romik.

## A positive, genuinely structural replacement

[MSY1](two-cap-minkowski-symmetrization-sharp-hand.md)
establishes a different statement:
**average the two convex parent caps,
not their nonconvex survivors**.
For any *actual compact connected full-turn sofa*
with two caps U,V of common projection,
width W>2, open-quarter curvatures
\(0\le\rho\le1-\eta\), and second-derivative
pair discrepancy

\[
\|\Delta f''\|_\infty,\|\Delta g''\|_\infty
\le\lambda\le 7\eta/100,
\]

one has

\[
\boxed{
|S|\le|E(U,V)|
\le2\Psi((U+V)/2)\le M.
}
\tag{GP.3}
\]

This needs **no closeness of either
parent to Romik**, no symmetry of
either parent, no top-face alignment
and no half-height midline assumption
on the *actual sofa*.

The proof is not a restatement of an
unproved symmetrization principle.
It compares two **proved quantities**:

* the exact clipping gain from
  unequal top-face endpoints obeys
  \[
  G(U,V)\le
  (|a_U-a_V|^3+|b_U-b_V|^3)/(3\eta);
  \]
* the fixed-width strong Jensen
  gain of the signed one-turn
  functional obeys
  \[
  2\Psi((U+V)/2)-\Psi(U)-\Psi(V)
  \ge 7(|a_U-a_V|^3+
         |b_U-b_V|^3)/(300\lambda).
  \]

Thus the explicit \(\lambda/\eta\)
threshold pays **all** the mixed
ordinary clipping without asserting
it vanishes.

When both parents also contain the
full bottom half-height rectangle
and their niches stay below that
line, the average cap's **own
identical-parent two-turn intersection**
is a genuine connected sofa of
area \(2\Psi((U+V)/2)\). Therefore
MSY proves a constructive,
area-nondecreasing **pair-to-identical
Minkowski averaging operation on the
stated shape class**.

The one-turn strong concavity/signed-roof/
sharp-value inputs AF/SD/SR/WV are
older written, self-reviewed arguments.
The new transfer is hand algebra
conditional on those inputs; no
external review or Lean check is
claimed.

## Beyond infinitesimal or near-reference cases

[RSA1](romik-stadium-global-pair-averaging.md)
proves the same conclusion on the
**entire real parameter square** for
two parent caps drawn independently
from the Minkowski arc joining
Romik's actual curved cap to a
different **radius-1/2 circular
stadium cap**, with the same
width and lower half-height rectangle:

\[
\boxed{
|E(U_s,U_t)|
\le |E(U_{(s+t)/2},U_{(s+t)/2})|
-\frac1{6000}(s-t)^2
\le M.
}
\]

No pairwise small-C² hypothesis is
needed here: s,t may be 0 and 1.
The proof exploits the exact
*shared circular end arcs*: the
outer roof deficit and inner notch
near mismatched top-face tips are
both bounded by
\(q(d)=\frac12-\sqrt{\frac14-d^2}\).
The resulting true mixed clipping
has a cubic upper bound, which is
strictly smaller than a fixed-width
Jensen gap derived from one interior
support difference at angle π/4.
There is **no finite-angle niche
sampling** in the proof.

## The precise remaining unrestricted sharp-value gate

The proven positive reduction MSY
has assumptions a hypothetical
maximizer need not satisfy:
- a **uniform** open-quarter curvature
  gap \(1-\rho\ge\eta>0\);
- sufficiently small *difference*
  of the two parents' second
  derivatives, relative to this gap;
- truly complete conventional turns
  for the final full-sharp area
  comparison; partial-turn extension
  remains separate.

No argument shows these properties
can be imposed without reducing the
area of an unknown maximum.
An unrestricted global proof would
need either:

1. a **pairwise coercivity inequality
   paying the clipping G for all cap
   pairs**, without smallness of
   second-derivative difference or
   strict curvature gap; or
2. a separate area-preserving
   geometric transformation of a
   hypothetical maximizer into a
   class where MSY's averaging
   hypotheses are established.

Neither is proved here. In fact
the EAC counterexample shows the
averaged-Ψ inequality is false on
a wider unconstrained filled-core
domain, even with U=V; the
niche-confinement hypothesis is
not cosmetic.

## Research decision

This line of investigation produced
both a **rigorous near-reference
obstruction to naive symmetrization**
and a **genuine area-nondecreasing
Minkowski averaging theorem** under
quantitative, shape-independent
regularity conditions.
The next step should not be another
finite-dimensional shear or polygon
subclass. It should try to extend
the Jensen-versus-clipping estimate
to **all curvature-dominated pairs**,
or find a direct structural reason
that an *actual global maximizer*
has pair discrepancy small enough
for the proved estimate to apply.

Everything is committed to the
existing PR #3 research branch,
with no change to Lean sources.
