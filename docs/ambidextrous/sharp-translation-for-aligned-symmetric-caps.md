# A sharp Romik-area theorem for horizontally shifted *arbitrary* symmetric caps with matched top faces

**Theorem STC1 (no triangular niche hypothesis is needed for the sharp value).**
Let \(0<b<m\), let \(I=[-m,m]\),
\(J=[-b,b]\), and let U,V be any two
**independently chosen** compact
horizontally symmetric, convex,
downward-closed one-turn caps in
\(I\times[0,1]\) such that:

1. each contains the complete rectangle
   \(I\times[0,1/2]\);
2. each has its whole top horizontal
   face **exactly** \(J\times\{1\}\);
3. each full positive-height turning niche
   lies inside \(J\times[0,h_X]\), with its
   own ceiling \(h_U,h_V<1/2\).
   No triangular shrinkage, symmetry
   of niche sections, curvature bound
   or common active contact pattern is assumed.

Let \(T_X=X\setminus N(X)\) and
\(\rho(x,y)=(x,1-y)\).
Then for **every** horizontal displacement \(d\),

\[
\boxed{
|T_U\cap(\rho T_V+(d,0))|
\le |T_U\cap\rho T_V|
=\Psi(U)+\Psi(V)\le M.
}
\tag{STC.1}
\]

The first two statements are pure
geometric/ordinary-area hand equalities
and inequalities. The final comparison
uses the written universal weighted
one-turn sharp theorem WV2, whose
independent mathematical review remains
outstanding. It does **not** assert
that every unrestricted competitive
two-turn sofa can be represented by
this special symmetric-cap pairing.

**Quantitative variant STC2.** Suppose
additionally each niche at height y
is supported in
\([-(b-\sigma y),b-\sigma y]\)
for a shared \(\sigma>0\), with
these intervals nonempty wherever
the niche is nonempty. Put
\(K=2(m-b)>0\). Then

\[
\boxed{
|T_U\cap(\rho T_V+(d,0))|
\le M-
\frac{\sigma\,\min(|d|,m-b)^2}
{K(K+\sigma)}.
}
\tag{STC.2}
\]

For Romik's reference, \(b=m/2\),
\(\sigma=1\), so STC2 specializes
to the explicit deficit in RH1.

## 1. A purely one-dimensional comparison

For \(a\ge c\ge0\), let \(D_{a,c}(t)\)
be the overlap lost between centered
intervals of radii a,c after relative
horizontal displacement t≥0.
It is absolutely continuous with derivative
\[
D'_{a,c}(t)=
\mathbf1_{\{a-c<t<a+c\}}
\quad\text{for almost every }t>0.
\tag{STC.3}
\]

For either cap X, the horizontal section
above \(y=1/2\) is the centered interval
of halfwidth \(R_X(y)\), where convexity
implies R_X concave and
\[
R_X(1/2)=m,\qquad R_X(1)=b.
\]
Writing \(K=2(m-b)\), the chord
inequality gives
\[
\boxed{
R_X(z)\ge m-K(z-1/2),\qquad
R_X(1-y)\ge b+Ky.
}
\tag{STC.4}
\]

Below \(y=1/2\), the survivor's
section is \(I\setminus N_X(y)\).
The niche is empty for y≥h_X<1/2
and is contained in I_b for y<h_X.
The exact Fubini decomposition of the
area of the translated cross intersection
has two ordinary outer interval overlaps,
one for each upper/lower half, **minus**
one niche overlap for each cap.

At zero shift the niche is entirely
inside the other's upper interval:
\(R_X(1-y)\ge b\).
At nonzero shift the possible
*recovery* of material by no longer
overlapping a niche can be at most
the loss of overlap of the entire
centered interval I_b with that upper
interval. (This is a set-containment
estimate; a niche slice need not be
connected.) Consequently

\[
\begin{aligned}
\Phi(0)-\Phi(d)\ge&
\int_{1/2}^{1}
[D_{m,R_U(z)}(t)+D_{m,R_V(z)}(t)]\,dz\\
&-\int_0^{h_U}D_{R_V(1-y),b}(t)\,dy
-\int_0^{h_V}D_{R_U(1-y),b}(t)\,dy,
\end{aligned}
\tag{STC.5}
\]
where \(t=|d|\) and \(\Phi(d)\) is
the true translated intersection area.

## 2. A sharp cancellation at small offsets

For \(0<t<m-b=K/2\), STC.4
implies that each **outer**
derivative contributes measure at least
\(t/K\): the entire height interval
\((1/2,\,1/2+t/K)\) satisfies
\(m-R_X(z)<t<m+R_X(z)\).

Each **niche** derivative contributes
measure at most \(t/K\):
an active niche level y must satisfy
\[
R_X(1-y)-b\ge Ky<t.
\]
There are two outer contributions
and two niche contributions, so the
derivative of the right side of
STC.5 is **nonnegative** for almost
every \(0<t<m-b\). This is the exact
point where concavity of both caps
balances all potential gain from
relative niche displacement; it
does not use a triangle condition.

For \(m-b<t<m+b\), both outer
overlap-loss derivatives contribute
exactly 1/2, for a total of 1,
while both niche contributions
have total measure at most
\(h_U+h_V<1\). Thus the derivative
is strictly positive.
For \(t\ge m+b\), no niche term
is active (both radii sum to at
most m+b), so the derivative
is nonnegative.

The right side of STC.5 starts at
zero and is absolutely continuous.
It is therefore nonnegative for all
t≥0, proving the first inequality
of STC.1 for both signs of d.

## 3. At zero shift the old weighted bound applies *exactly*

The half-height rectangle implies
the cap roofs A_U,A_V are at least 1/2;
the strict niche ceilings imply
n_U,n_V<1/2. The two survivors
and their reflected pairing have
nonempty vertical interval sections
containing height 1/2.

On J both roofs are exactly 1;
the unshifted interval length is
\(1-n_U-n_V\).
Outside J both niches are zero;
the length is \(A_U+A_V-1\).
Thus
\[
|T_U\cap\rho T_V|
=|U|+|V|-|N(U)|-|N(V)|-2m
=\Psi(U)+\Psi(V).
\]
WV2 states \(\Psi(X)\le M/2\)
for every normalized cap X in its
full right-angle domain; U,V meet
that definition. Hence
\(\Psi(U)+\Psi(V)\le M\).
This finishes STC1.

## 4. Quantitative strengthening if the notch tapers

Suppose \(N_X(y)\subseteq
I_{b-\sigma y}\) instead of merely I_b.
By STC.4 the unshifted interval
gap in the niche derivative is at least
\[
R_X(1-y)-(b-\sigma y)\ge(K+\sigma)y.
\]
Therefore each inner derivative
contributes at most \(t/(K+\sigma)\),
while each outer derivative still
contributes at least \(t/K\).
For \(0<t<m-b\) the derivative
of the lower bound STC.5 is at least
\[
2t\left(\frac1K-\frac1{K+\sigma}\right)
=\frac{2\sigma t}{K(K+\sigma)}.
\]
Integrating yields
\(\sigma t^2/[K(K+\sigma)]\)
through \(t=m-b\). The same
nondecreasing argument at larger t
preserves this deficit. This proves
STC.2.

## 5. Why this does not settle arbitrary sofas

No result here transforms an arbitrary
convex hull into **two independently
horizontally symmetric caps with
coincident original top-face intervals**
while preserving ordinary area and
both turning motions. Such a
symmetrization is precisely the kind
of delicate global operation for which
the research branch already records
negative examples.

The theorem gives a sharp,
global-in-horizontal-offset
area comparison for an
**infinite-dimensional asymmetric
family**, with independent cap
profiles and no curvature restrictions.
It is not an unrestricted optimality
proof, does not control general
partial turns, and does not make
the missing symmetrization
lemma an innocuous assumption.

No computer search, Lean formalization
or CI is part of the mathematical
argument. The result is a
self-reviewed pen-and-paper theorem.
