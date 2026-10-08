# A sharp obstruction to the Minkowski-average proof for filled cores

**Theorem EAC1 (counterexample to a tempting global Jensen bridge).**
There is a single explicitly described convex triangular core V
with width \(T=7/6\) and height \(1/2\), whose filled cap
\[
U=V+[0,T]\times[0,1/2]
\]
has a **complete positive niche strictly below height \(1/2\)**,
so that the symmetric two-turn intersection
\(E=(U\setminus N(U))\cap\rho(U\setminus N(U))\)
is an actual compact connected two-complete-turn sofa, yet
\[
\boxed{|E|>2\Psi(U),\quad
\Psi(U)=|U|-|N(U)|-T.}\tag{EAC.1}
\]
In particular the appealing averaging inequality
\[
|E(U,V)|\ \stackrel{?}{\le}\ 
2\Psi\bigl((U+V)/2\bigr)
\tag{EAC.2}
\]
is **false for the filled-core domain even when \(U=V\)**.
A Minkowski-average proof cannot simply replace both parents by
their average and apply the previously proved signed one-turn
value theorem. The ordinary-area clipping correction must be
included and paid.

This is an exact elementary hand counterexample: no sampled
angle evaluation, optimizer or formalization is a proof premise.
It does **not** construct a sofa larger than Romik's candidate.

## 1. An actual core and its filled cap

Put
\[
T=\frac76,\quad a=\frac{16}{15},\qquad
V=\operatorname{conv}
\left\{(0,0),(T,0),(a,\tfrac12)\right\}.
\tag{EAC.3}
\]
Its filled cap \(U=V+[0,T]\times[0,1/2]\) lies in
\([0,2T]\times[0,1]\), contains the whole bottom half-height
rectangle, and has the horizontal top-face interval
\(J=[a,a+T]\).
Its upper roof on \(0\le x\le a\) is
\[
\boxed{A(x)=\frac12+\frac{x}{2a}<1\quad(0\le x<a).}
\tag{EAC.4}
\]

For \(0<t<\pi/2\), write \(c=\cos t,s=\sin t\).
The two upper support values of U in the conventional
frame are
\[
f(t)=Tc+\frac12s+\max(Tc,ac+\frac12s),
\qquad
g(t)=\frac12c+\max(0,\frac12c-as).
\tag{EAC.5}
\]
These are actual support functions of the Minkowski sum.

## 2. A complete hand proof that the niche is below the midline

At any turn angle, the maximum height of its inner
forbidden quadrant is the corner ordinate
\[
Y_C(t)=(f(t)-1)s+(g(t)-1)c.
\tag{EAC.6}
\]
Both wall roofs have respectively negative and positive
slopes in x, so every positive niche point lies at
height at most \(\max_tY_C(t)\).
There are exactly three angle regions because
\[
2(T-a)=\frac15<
\frac1{2a}=\frac{15}{32}.
\]

We use the elementary identity and inequality
\[
s+c-1=\frac{2sc}{1+s+c}
\ge 2(\sqrt2-1)sc
>\frac{33}{40}sc \quad(0<t<\pi/2).
\tag{EAC.7}
\]
The strict last comparison follows by squaring
\(113/80<\sqrt2\):
\(113^2=12769<12800=2\cdot80^2\).

**Region I:** \(\tan t\le1/5\).
Then \(f=2Tc+s/2\), \(g=c-as\), and
\[
Y_C=(2T-a)sc+1-\tfrac12s^2-(s+c)
\le\frac{53}{120}sc-\frac12s^2
\le\frac{53}{240}<\frac12.
\tag{EAC.8}
\]

**Region II:** \(1/5\le\tan t\le15/32\).
Then \(f=(T+a)c+s\), \(g=c-as\), and
\[
Y_C=Tsc+1-(s+c)
\le\frac{41}{120}sc
\le\frac{41}{240}<\frac12.
\tag{EAC.9}
\]

**Region III:** \(\tan t\ge15/32\).
Then \(f=(T+a)c+s\), \(g=c/2\), and
\[
Y_C=1-\frac12c^2+(T+a)sc-(s+c)
\le\frac{169}{120}sc-\frac12c^2
<\frac12.
\tag{EAC.10}
\]
Indeed the last strict inequality is equivalent to
\((169/60)sc<1+c^2\), and
\[
(1+c^2)^2-8s^2c^2=(1-3c^2)^2\ge0.
\]
Thus \(1+c^2\ge2\sqrt2\,sc\), while
\(169/60<2\sqrt2\) because
\(169^2=28561<28800=8\cdot60^2\).
The endpoint angles also have Y_C=0.

These three cases prove rigorously that
\[
\boxed{\sup_{x\in\mathbb R} n_U(x)<1/2.}
\tag{EAC.11}
\]
The full niche lies below the horizontal midline.
As the cap's lower half-rectangle is entirely present,
the lower one-turn survivor contains that midline at
every x. The two-turn intersection with its vertical
reflection has nonempty interval vertical fibers
containing the same midline. It is compact, connected,
and follows both *actual continuous complete* canonical
turns by support continuity. Thus the example is a
valid two-handed sofa, not a disconnected envelope.

## 3. Positive clipping outside the flat top-face interval

At the exact turning angle \(t=\pi/4\), the inner
quadrant is an isosceles open triangular niche with
base endpoints
\[
L_0=\sqrt2-\frac12,\qquad
R_0=T+a+1-\sqrt2
=\frac{97}{30}-\sqrt2.
\tag{EAC.12}
\]
Its vertical roof on the interval
\(L_0<x<a\) is at least \(x-L_0\).
Indeed \((L_0+R_0)/2=(T+a+1/2)/2>a\),
since \(a<T+1/2\), so the increasing
left wall is the smaller of the two
walls throughout \((L_0,a)\).

This entire x-interval lies **strictly
to the left of the cap's top-face interval**:
\(L_0<a\), because
\[
d:=a-L_0=\frac{47}{30}-\sqrt2>0,
\]
the strict comparison following from
\(47^2=2209>1800=2\cdot30^2\).
There the cap roof falls strictly below one:
\[
1-A(x)=\frac{a-x}{2a}>0.
\tag{EAC.13}
\]

The exact ordinary-area two-cap identity OT1,
applied to two identical caps U, reads
\[
|E|=2\Psi(U)+G,\qquad
G=2\int_0^{2T}\min(n_U(x),1-A(x))\,dx.
\]
Both terms in the minimum are positive
on \((L_0,a)\), so \(G>0\).
Indeed the entire interval supports the
quantitative hand bound
\[
\begin{aligned}
G
&\ge 2\int_{L_0}^a
\min\left(x-L_0,\frac{a-x}{2a}\right)dx\\
&=\boxed{\frac{d^2}{2a+1}
=\frac{15}{47}\left(\frac{47}{30}-\sqrt2\right)^2>0.}
\tag{EAC.14}
\end{aligned}
\]
The integral is evaluated by splitting
at \(x-L_0=d/(2a+1)\).
This proves EAC.1 with a strictly
positive, completely explicit margin.

## 4. Exactly what this falsifies

Even *identical* filled caps can have positive
ordinary-area clipping when their full turning
niches extend outside their top-face intervals.
Therefore the statement
\[
|E(U,V)|\le2\Psi((U+V)/2)
\]
is **false** on the natural core-plus-rectangle
domain; it already fails at U=V from EAC.1.
This cannot be repaired by strict niche
height <1/2, convexity, full-turn feasibility,
identical cores, or adding more continuum
turning angles: the example has all of them.

The universal weighted value theorem
\(\Psi(U)\le M/2\), even if fully accepted,
does **not** imply \(|E|\le M\) without
paying G. This case remains far below
Romik's area; it does not refute the
possible *direct* sharp inequality on
the whole filled-core domain.

A valid core-pair proof must either
(a) establish confinement of each niche
to the flat top-face interval and control
the mismatch there, or (b) bound the
true **effective niche loss** by the
sharp quantity in
[the exact RCE area formula]
(rectangular-core-exact-two-turn-area.md).
No unproved global Jensen or
symmetrization assumption is inserted.

No Lean, global numerical area bound,
large optimizer, or independent
refereeing is used here.
