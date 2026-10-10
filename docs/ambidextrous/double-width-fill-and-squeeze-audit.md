# Widen the corridor, fill vertically, and squeeze: exact hand audit

**Scope.** This note tests the proposed construction:
widen the two-handed hallway from width one to two,
treat the two turns separately, fill a central rectangle,
and compress the result back to a unit hallway.
There is a **valid one-way filling theorem**, but the
proposed reverse operation fails even for a single
connected rectangle having positive area and two
complete conventional turning motions. The example
can be made to produce a **spurious area greater than
Romik's candidate** after vertical compression or
after removing the vertical filler.

This is a hand calculation, not a claim that the
ambidextrous sharp optimum is settled. It does not
invalidate a *different* special-purpose squeeze
operation with additional proved geometric
hypotheses. No Lean, solver, or numerical optimization
is used.

## 1. The exact feasible-rectangle criterion

For hallway width \(w>0\), let
\[
K_{L,H}=[0,L]\times[0,H],
\qquad L\ge0,\quad 0<H\le w.
\]
Use the canonical conventional lower-turn frame
\[
u_t=(\cos t,\sin t),\qquad
v_t=(-\sin t,\cos t),\qquad
0\le t\le\pi/2.
\]
At each \(p=(x,y)\in K_{L,H}\), the two *actual*
support depths are
\[
D_u(p)=(L-x)\cos t+(H-y)\sin t,\qquad
D_v(p)=x\sin t+(H-y)\cos t.
\tag{SQ.1}
\]

**Lemma SQ1 (necessary and sufficient condition).**
The rectangle \(K_{L,H}\) follows the complete
canonical lower-turn hallway family of width \(w\)
if and only if
\[
\boxed{L+2H\le2\sqrt2\,w.}
\tag{SQ.2}
\]
By reflection symmetry in its horizontal midline,
the **same criterion** is necessary and sufficient
for both complete conventional handed turns.

**Proof.** At \(t=\pi/4\), take the retained
bottom midpoint \(p=(L/2,0)\).
Both support depths in SQ.1 equal
\((L/2+H)/\sqrt2\).
Their minimum must not exceed w, proving
the necessary inequality SQ.2.

Conversely assume SQ.2, and fix
\(0<t<\pi/2\), \(c=\cos t>0\),
\(s=\sin t>0\), \(p=(x,y)\in K\).
If both depths in SQ.1 were \(>w\),
then, since \(H-y\le H\),
\[
 (L-x)c+Hs>w,\qquad xs+Hc>w.
\]
Eliminating x gives
\[
L>
\frac{w-Hs}{c}+\frac{w-Hc}{s}
=\frac{w(s+c)-H}{sc}.
\tag{SQ.3}
\]
Let \(z=s+c\in(1,\sqrt2]\).
Since \(sc=(z^2-1)/2\), the expression
on the right is \(F(z)=2(wz-H)/(z^2-1)\).
It is *nonincreasing* on this interval:
\[
F'(z)=
-\frac{2[w(z-1)^2+2(w-H)z]}{(z^2-1)^2}\le0,
\tag{SQ.4}
\]
using \(H\le w\).
Therefore
\[
L>F(z)\ge F(\sqrt2)=2\sqrt2 w-2H,
\]
contrary to SQ.2. No point violates both
inner hallway alternatives, and the outer
walls use the actual support, so the whole
rectangle fits the canonical width-w
hallway at every interior angle.
At the two endpoint angles one safe depth
is at most H≤w. Continuity of the
support-tightened placements gives the
complete continuous quarter-turn motion.
Reflecting \(y\mapsto H-y\) exchanges the
handed turns and fixes the rectangle as a
set, proving the last statement. QED.

This is a full **continuum-angle** criterion,
not a 45-degree-only sufficient condition.

## 2. Widening and filling does work in one direction

For any compact body S, a point p∈S, and a unit
normal n, write its actual supporting depth
\[
D_S(p,n)=h_S(n)-p\cdot n.
\]
For compact sets A,B,
\[
D_{A+B}(p+q,n)=D_A(p,n)+D_B(q,n).
\tag{SQ.5}
\]

Let \(I=[0,1]e_y\) be the *vertical unit segment*.
Then
\(0\le D_I(q,n)\le |n_y|\le1\).
If S fits one of the two width-one inner
wall alternatives at every visited turn angle,
then the Minkowski thickening
\[
\boxed{S^{\rm wide}=S+I}
\tag{SQ.6}
\]
fits the corresponding *width-two*
inner-wall alternative at that angle.
The same argument works for the opposite
handed turn, and the outgoing full-strip
condition follows from
\[
w_{S+I}(n)=w_S(n)+|n_y|\le2
\]
whenever the old outgoing strip has width
at most one. Incoming vertical span also
grows by exactly one to at most two.
Canonical support offsets vary continuously,
giving genuinely traversable widened
motions, not just unrelated sampled
placements.

**Lemma SQ2 (one-way vertical extrusion).**
Every compact unit-width ambidextrous
sofa can be vertically Minkowski-expanded
by I to give a valid two-width
ambidextrous sofa.
If the original vertical fibers are
intervals over a horizontal projection
of length W, then ordinary area obeys
\[
\boxed{|S+I|=|S|+W.}
\tag{SQ.7}
\]
This is Fubini: every nonempty vertical
fiber gains exactly one unit of height.
If some original vertical fibers have
holes, the area identity need not hold;
the *feasibility* direction remains valid.

This is a precise implementation of
"widen the hallway and fill the middle."
It does **not** provide a reverse map
from arbitrary width-two sofas to
width-one sofas.

## 3. An exact positive-area counterexample to the squeeze

Take the **rational** rectangle
\[
\boxed{
K_2=[0,37/20]\times[0,19/10].
}
\tag{SQ.8}
\]
It has width \(37/20=1.85\),
height \(19/10=1.9\), and area \(703/200=3.515\).
It admits **both complete conventional
turns in a width-two hallway**, by SQ1:
\[
L+2H=\frac{37}{20}+\frac{19}{5}
=\frac{113}{20}
<4\sqrt2=2\sqrt2\,w.
\]
The strict comparison is exact, since
\(113^2=12769<12800=2(80)^2\).

There are two natural readings of
"squeeze back to a unit hallway."

**(A) Compress the vertical coordinate by one-half.**
The candidate becomes
\[
K_{\rm half}=[0,37/20]\times[0,19/20],
\quad |K_{\rm half}|=\frac{703}{400}=1.7575.
\]
Its incoming height is below one, but
at the canonical 45-degree hallway,
the bottom midpoint \(p=(37/40,0)\)
has **both** true supporting depths
\[
\boxed{
D_u(p)=D_v(p)=
\frac{37/40+19/20}{\sqrt2}
=\frac{15}{8\sqrt2}>1.
}
\tag{SQ.9}
\]
It cannot fit *any* width-one right-angle
hallway at that orientation. In particular
it cannot complete either conventional
quarter turn. Its large compressed
area is **not** a sofa counterexample.

**(B) Remove the one-unit vertical filler
using exact Minkowski erosion.**
The rectangle is literally
\[
K_2=K_{\rm core}+[0,1]e_y,\qquad
K_{\rm core}=[0,37/20]\times[0,9/10].
\tag{SQ.10}
\]
(The Minkowski erosion of K2 by I
recovers exactly Kcore.)
The putative width-one core has
ordinary area
\[
\boxed{|K_{\rm core}|=\frac{333}{200}=1.665>M.}
\tag{SQ.11}
\]
For the strict M comparison, with
\(4Y^3+3Y-1=0\), \(Y>0\),
the exact candidate formula
\(M=1+4Y^2+\arctan Y\)
satisfies \(M<83/50=1.66<333/200\):
the increasing cubic has its root
below 3/10 and \(\arctan Y<Y\).

Nevertheless at the same bottom midpoint
the two true 45-degree support depths are
\[
\boxed{
D_u(p)=D_v(p)=
\frac{37/40+9/10}{\sqrt2}
=\frac{73}{40\sqrt2}>1.
}
\tag{SQ.12}
\]
Thus Kcore, although a genuine
positive-area rectangular core in an
exact filled-center Minkowski decomposition,
**cannot** traverse a unit-width hallway.

This is a particularly strong
counterexample: *even decomposability
into an original core plus exactly
one unit of vertical filling* does
not make the inverse squeeze
motion-preserving.

## 4. Why independently optimal Gerver halves are not enough

The two one-turn pieces of an ambidextrous
shape interact through their common
horizontal width and the portions of
one turn's niche lying outside the
other half's hull. The exact identity
[OT1](one-turn-reduction.md) for nonempty
two-turn canonical-envelope fibers reads
\[
\boxed{|E|=\mathcal A(U)+\mathcal A(V)-W+G
=\Psi(U)+\Psi(V)+G,}
\tag{SQ.13}
\]
where \(\mathcal A(U)=|U|-|N(U)|\),
\(\Psi(U)=\mathcal A(U)-W/2\)
and \(G\ge0\) is an *explicit
ordinary-area clipping correction*.
In the aligned, unclipped class \(G=0\);
outside it, omitting G would be
mathematically incorrect.

The Gerver sofa maximizes an
**unpenalized** one-turn area problem,
but independently maximizing those
areas does not maximize SQ.13.
Even when G=0, each half pays
a width cost \(W/2\); the relevant
one-turn objective is \(\Psi\), not
\(\mathcal A\).
Under the endpoint-arm variation
with an inactive niche wall, extending
a vertical end edge of height e by
horizontal amount \(\varepsilon\)
changes \(\Psi\) to first order by
\((e-1/2)\varepsilon\), so stationary
ambidextrous reference halves require
end-edge height 1/2 rather than
the zero end-edge stationarity of
the unpenalized Gerver variational
problem; this is already observed
in OT2b.

The main unresolved geometric
task is not separate optimization of
two Gerver sofas: it is proving an
**ordinary-area comparison that pays G**
for arbitrary interacting halves,
or a genuine area-preserving
symmetrization that removes G.

## 5. Boundary of the conclusion

Reversing a rigid motion reverses
the **entire shape** and exchanges
entry and exit. It does not reflect
only the top half into the bottom half.
A problem invariant under reflection
need not have every optimizer invariant
without a proved feasible
area-nondecreasing symmetrization.
The branch's
[RS2](reflection-symmetric-optimality.md)
already proves the exact Romik bound
for its stated left-right symmetric
subclass, with its known historical
dependencies; it does **not** prove
that every competitor can be replaced
by such a symmetric body.

The positive SQ2 construction and
negative SQ.8–SQ.12 make precise why
a double-width filling approach
cannot be inverted *without additional
geometric hypotheses*. A special
inverse filling theorem, if found,
might still be useful, but any
proposed version must exclude this
explicit rectangle and must preserve
the full **continuum** turning motions,
not merely the incoming strip.

These are hand proofs and exact rational
comparisons, not numerical optimization,
Lean formalization, or independent
referee certification. Global Romik
optimality remains open.
