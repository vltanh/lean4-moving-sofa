# Bootstrap the finite-to-full mesh error from the three-point width theorem

**Purpose.** The proof of
[FR2](full-turn-compact-finite-reduction.md) used a conservative
diameter bound \(D<6\) for every connected finite-angle candidate,
and therefore uniform shrink \(1/(1+6/n)\).
The new sharp width theorem
[TSW1](three-point-switching-fiber-width.md)
gives a **self-improving compactness estimate**, with an
asymptotic angular-interpolation constant \(3\), rather
than \(6\). This is a rigorous numerical-bound refinement
for a different future certification program; it does
**not** identify Romik's optimal area.

Let \(n\ge8\) be even and let \(A_n\) be the *global*
finite-hallway area optimum defined in FR Section 3
(both sampled conventional turns and the endpoint frames).
Set

\[
\boxed{
d_n=
\frac{8/n+\sqrt{9-8/n^2}}{1-8/n^2}.
}
\tag{FB.1}
\]

**Theorem FB1 (improved certified finite-to-full bracket).**
For all even \(n\ge8\),

\[
\boxed{
\frac{A_n}{(1+d_n/n)^2}
\le A_F\le A_n,\qquad d_n=3+\frac8n+O(n^{-2}).
}
\tag{FB.2}
\]

Thus the angular interpolation factor in FR2 improves
from \(1+6/n\) to \(1+d_n/n\) without curvature or
contact hypotheses. At \(n=32\), for instance, the
squared factor drops from \(1.41015625\) to
approximately \(1.215112\).

## Proof

Take a maximizing finite envelope from FR Section 3;
apply GC's horizontal gap compression and vertical
filling, which preserve its sampled hallway constraints
and, for these canonical envelopes, its **exact area**
\(A_n\). Denote the resulting compact connected finite
candidate by \(S\). Its incoming vertical span is
\(H\le1\), its horizontal width \(W\le5\), and
its Euclidean diameter \(D=\operatorname{diam}S\le
\sqrt{W^2+H^2}\le\sqrt{26}<6\).

The proof of FR2 actually uses only the *pointwise*
bound

\[
|h_S(v)-p\cdot v-h_S(u)+p\cdot u|
\le D|v-u|
\]

for unit normals and any \(p\in S\).
Therefore, using the **actual** \(D\) instead of the
conservative \(6\), all missing angles are feasible
after the exact uniform shrink

\[
\lambda=(1+D/n)^{-1}.
\tag{FB.3}
\]

GC already supplied connectedness, so the shrunken
set is a legitimate **complete conventional two-turn**
sofa of area \(\lambda^2 A_n\). It has horizontal
width \(\lambda W\). By global theorem TSW1,

\[
\lambda W\le2\sqrt2
\quad\Longrightarrow\quad
W\le2\sqrt2(1+D/n).
\tag{FB.4}
\]

Combine this bound with \(H\le1\):

\[
D^2\le W^2+H^2
\le8(1+D/n)^2+1.
\]

Rearrange:

\[
(1-8/n^2)D^2-\frac{16}{n}D-9\le0.
\tag{FB.5}
\]

For \(n\ge8\), the quadratic has positive
leading coefficient, so every nonnegative
\(D\) satisfying FB.5 is at most its positive
root

\[
\frac{16/n+\sqrt{(16/n)^2+36(1-8/n^2)}}
{2(1-8/n^2)}
=\frac{8/n+\sqrt{9-8/n^2}}{1-8/n^2}
=d_n.
\]

FR's finite-angle interpolation can consequently
be replayed using \(d_n\) in place of \(D\),
shrinking by \(\lambda_n=(1+d_n/n)^{-1}\)
and producing a full-turn sofa of area at least
\(A_n/(1+d_n/n)^2\). This gives the first
inequality in FB.2; the other is simply the
relaxation \(A_F\le A_n\).
The asymptotic expression follows by an ordinary
Taylor expansion of the displayed explicit
algebraic root. QED.

**No circularity.** The first shrink FB.3 uses the
candidate's *known finite diameter* \(D\), not a
presumed full-turn width theorem. **Only after
the shrink is proven full-turn feasible** do we
invoke TSW1. The bootstrap is then an algebraic
consequence of that actual feasible shrunken body.

## Consequences and correct scope

The root \(d_n\) is an upper bound on the
diameter of **every connected finite-envelope
maximizer** after FR's compression, not only
on a chosen local numerical optimum. The
argument works equally for any finite-angle
candidate satisfying FR's assumptions.

This does **not** turn a finite mesh into a
sharp proof of \(A_F=M\). Indeed FR3 proves
that every finite orientation-only relaxation
has \(A_n>M\), even if the true full-turn
optimum ultimately equals \(M\). The improved
error only makes numerical-to-continuum brackets
more efficient. It cannot replace a sharp
limiting inequality or a new structural theorem
for ordinary area.

No Lean, CI or long numerical search was run;
the proof is analytic and uses only FR, GC
and the new TSW width theorem.
