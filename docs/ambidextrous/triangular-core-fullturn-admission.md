# Both independently filled triangular cores yield genuine connected full-turn sofas

**Theorem TCA1 (complete the geometric admission of TCG1).**
Every pair of filled triangular cores in
[TCG.1](triangular-core-expanded-gerver-sharp-hand-bound.md),
with
\[
11/10\le T\le6/5,\qquad
2/5\le a,b\le4/5,
\]
has **both full positive turning niches strictly below
the half-height line \(y=1/2\)**.
Consequently the actual two-turn intersection
\[
E_{a,b,T}=(U_a\setminus N(U_a))
\cap\rho(U_b\setminus N(U_b))
\]
is compact, has an interval vertical section
containing \((x,1/2)\) at **every**
\(x\in[0,2T]\), is connected, and admits
both full conventional \(90^\circ\) turning motions
from the same incoming orientation. In particular
the exact area upper bound TCG.2 applies to
**actual valid ambidextrous sofas**, not merely a
possibly disconnected artificial envelope.

This supplements the separate area inequality
TCG1. Its proof is a finite-by-hand trigonometric
case estimate valid for the *entire continuous
turn-angle range*, not a mesh certificate.

## 1. Inner-corner height dominates every forbidden niche point

For an angle \(t\in(0,\pi/2)\), put
\(c=\cos t,s=\sin t\).
The two outer support values of the filled
triangular cap \(U_a=V_a+[0,T]\times[0,1/2]\)
are exactly
\[
\boxed{
f_{T,a}=Tc+\tfrac12s+\max(Tc,ac+\tfrac12s),
\quad
g_a=\tfrac12c+\max(0,\tfrac12c-as).
}
\tag{TCA.1}
\]

The inner forbidden quadrant is the intersection
of the two open halfplanes whose corresponding
upper roofs are
\[
R_t(x)=\frac{f_{T,a}-1-xc}{s},
\qquad
L_t(x)=\frac{g_a-1+xs}{c}.
\]
The roofs cross at the actual inner corner
\[
y_C(t;T,a)
=(f_{T,a}-1)s+(g_a-1)c.
\tag{TCA.2}
\]
Because one roof decreases in x and the other
increases, **every forbidden point with
positive height is below this inner-corner
height**. Thus an upper bound
\(y_C<1/2\) for all t is sufficient.

For fixed t with c,s≥0, TCA.1 shows
\(y_C\) is **nondecreasing in T**
and **convex in the apex parameter a**:
the two support values are maxima of
affine functions of a, multiplied by
nonnegative s,c. Hence, throughout TCG.1,
\[
y_C(t;T,a)\le\max\{
y_C(t;6/5,2/5),\,y_C(t;6/5,4/5)\}.
\tag{TCA.3}
\]

Horizontal reflection \(x\mapsto2T-x\)
exchanges a with T-a and, at the same time,
exchanges the two one-turn walls under
\(t\mapsto\pi/2-t\). At T=6/5 it sends
a=2/5 to a=4/5 and preserves the corner
height. Therefore it suffices to bound
\(y_C(t;6/5,2/5)\) for all t.

## 2. Three exact support regimes, none exceeds half-height

Take \(T=6/5,a=2/5\).
From TCA.1, the choice of the first
support maximum switches at
\(\tan t=2(T-a)=8/5\);
the choice of the second maximum
switches at \(\tan t=1/(2a)=5/4\).
Since \(5/4<8/5\), there are only
three regimes. In each put
\(z=s+c\), and note the elementary
universal inequality
\[
\boxed{
s+c=\sqrt{1+2sc}\ge1+\tfrac45sc
\quad(0\le sc\le\tfrac12).
}
\tag{TCA.4}
\]
Indeed both sides are positive, and
squaring reduces it to
\(\tfrac25sc\ge\tfrac{16}{25}(sc)^2\),
true for \(sc\le1/2<5/8\).
Strictness holds for 0<sc≤1/2.

**Regime I: \(\tan t\le5/4\).**
Then \(f=(12/5)c+s/2,\ g=c-(2/5)s\).
Hence
\[
\begin{aligned}
y_C&=1+2sc-\tfrac12s^2-s-c\\
&\le\tfrac65sc-\tfrac12s^2
<\tfrac12.
\end{aligned}
\]
For the final inequality observe
\[
\tfrac12+\tfrac12s^2-\tfrac65sc
=\left(s-\tfrac35c\right)^2
+\tfrac7{50}c^2>0.
\tag{TCA.5}
\]

**Regime II: \(5/4\le\tan t\le8/5\).**
Then \(f=(12/5)c+s/2,\ g=c/2\), giving
\[
y_C=\tfrac12+\tfrac{12}{5}sc-(s+c)
<\tfrac12.
\tag{TCA.6}
\]
Here \(s+c\ge2\sqrt{sc}\), while
\((12/5)sc<2\sqrt{sc}\) for
\(0<sc\le1/2\), since
\(\sqrt{sc}\le1/\sqrt2<5/6\).

**Regime III: \(\tan t\ge8/5\).**
Then \(f=(8/5)c+s,\ g=c/2\), so
\[
\begin{aligned}
y_C&=1+\tfrac85sc-\tfrac12c^2-s-c\\
&\le\tfrac45sc-\tfrac12c^2
\le\tfrac25<\tfrac12.
\end{aligned}
\tag{TCA.7}
\]

The endpoint corner heights at t=0,π/2
are nonpositive or zero by direct
substitution; continuity and the
strict interior bounds show
\[
\boxed{\max_{t\in[0,\pi/2]}y_C(t;T,a)<1/2}
\]
uniformly for the closed T,a parameter
range of TCG.1, by compactness.
This proves every full positive niche
is confined strictly below the midline.

## 3. A genuine full-turn intersection

Each U_a contains the entire rectangle
\([0,2T]\times[0,1/2]\) and has height
at most one. Its full lower niche
is a downward-closed union of open
forbidden quadrants in the incoming
half-plane; at every x the surviving
one-turn vertical fiber is therefore
a nonempty **closed interval**
\([n_a(x),A_a(x)]\) containing y=1/2.
Likewise for U_b.

After vertical reflection, the
other survivor has interval fibers
\([1-A_b(x),1-n_b(x)]\) containing
the same midline. The intersection
therefore has the nonempty closed
interval fibers
\[
\boxed{
E_x=[\max(n_a(x),1-A_b(x)),
\min(A_a(x),1-n_b(x))]
\ni\tfrac12
}
\tag{TCA.8}
\]
over every x∈[0,2T].
In particular its horizontal
projection is the entire interval,
and because all vertical fibers are
intervals sharing a connected
midline, E is connected.

All points in E satisfy both complete
canonical hallway families using
the respective full-angle
support-tightened placements of
U_a and the reflected U_b.
At t=0 and π/2 the same outer
supports give the usual straight
incoming/outgoing unit strips.
Their support functions depend
continuously on t; hence the
angle families are actual
continuous rigid-body motions,
not isolated placements.
Thus E is a valid two-handed sofa.

Finally, by [TCG1](triangular-core-expanded-gerver-sharp-hand-bound.md),
its genuine ordinary area obeys
\[
|E|<41/25<M.
\]

## 4. Boundary of applicability

The triangular core model gives
many distinct curved-core shape
parameters \(a,b\), and supplies
an exact short proof for a family of
genuinely feasible asymmetric bodies.
It still excludes the **smooth
Romik core** and general long
curvature distributions, which
require the *whole* moving niche
rather than two 45-degree triangles.
This is not a replacement for the
unrestricted area comparison.

The theorem relies only on exact
analytic geometry, not on WV2,
formalization, numerical upper
bounds or independent peer review.
