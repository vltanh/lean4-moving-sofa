# Why PR #7's one-crossing area proof needs a two-front replacement at Romik

**Research conclusion.** The near-180-degree single-bend
PR #7 proof maximizes a quadratic *after* giving
an ordinary-area enclosure by a **single monotonically
crossing inner-corner graph**. This cannot be applied
to either one-turn half of Romik as written:
its true inner corner starts at height zero,
rises to a unique positive maximum at the
45-degree frame, then returns to zero.

This note proves the obstruction explicitly,
then gives a rigorous **two-front horizontal-slice
area formula** for any pair of one-turn caps whose
corner-height superlevel sets are intervals.
This is an exact geometric transfer, not another
numerical upper bound. It does not establish
the global inequality \(|S|\le M\):
the min/max **clipping** of each inner forbidden
interval against the other cap is the remaining
ordinary-area optimization.

**Source dependency:** PR #7's
[REVERSE_GENERAL_MAJORANT.md]
(https://github.com/vltanh/lean4-moving-sofa/blob/research/arbitrary-hallway-angles-20261005/experiments/hallway_angles/REVERSE_GENERAL_MAJORANT.md)
and
[REVERSE_QUADRATIC_THEOREM.md]
(https://github.com/vltanh/lean4-moving-sofa/blob/research/arbitrary-hallway-angles-20261005/experiments/hallway_angles/REVERSE_QUADRATIC_THEOREM.md).
Both source arguments are research proof drafts, not independently
refereed or Lean-checked. The geometric lemmas below have
elementary standalone proofs.

## 1. Exact corners for an ordinary one-turn cap

Let U be any compact convex height-one downward
cap in \(0\le y\le1\), with upper support
\[
f(t)=h_U(\cos t,\sin t),\quad
g(t)=h_U(-\sin t,\cos t),\qquad
0\le t\le L=\pi/2.
\]
The canonical inner-corner trajectory is
\[
C(t)=(f(t)-1)(\cos t,\sin t)
+(g(t)-1)(-\sin t,\cos t).
\]
Write \(x_C(t),h_C(t)\) for its coordinates,
so \(h_C=(f-1)\sin t+(g-1)\cos t\).

At every \(0<t<L\), the positive-height
forbidden quadrant is exactly the set
\[
\boxed{
0\le y<h_C(t),\quad
x_C(t)-(h_C(t)-y)\cot t
<x<
x_C(t)+(h_C(t)-y)\tan t.
}
\tag{DC.1}
\]
Indeed the two perpendicular inner-wall
inequalities for a point p are
\((p-C)\cdot(\cos t,\sin t)<0\)
and
\((p-C)\cdot(-\sin t,\cos t)<0\).
Solving them for x proves DC.1.
Its horizontal interval has length
\((h_C-y)/(\sin t\cos t)>0\).

## 2. The Romik corner crosses every intermediate height twice

**Lemma DC1 (strict double crossing at Romik).**
For the exact downward reference one-turn
cap U_* from
[RH.2](romik-horizontal-misalignment-sharp-bound.md),
its canonical corner ordinate \(h_*(t)\)
is **strictly increasing** on \(0<t<L/2\),
strictly decreasing on \(L/2<t<L\),
and satisfies
\[
\boxed{
h_*(0)=h_*(L)=0,\qquad
h_*(L/2)=R_0+\frac12-\sqrt2>0.
}
\tag{DC.2}
\]
Here \(\beta=\arctan Y\),
\(4Y^3+3Y-1=0\) and
\(R_0=\cos\beta/
\sin(3\beta/2+\pi/8)\).
For every \(0<y<h_*(L/2)\),
**exactly two distinct actual hallway
angles** satisfy \(h_*(t)=y\).

**Proof.** The strictly increasing cubic
has \(Y<1/3\), since its value at \(1/3\)
is \(4/27>0\). Thus
\(\beta<\arctan(1/3)<\pi/8\) and
\(m=1/(3\sin\beta)>1\).

On the first phase \(0\le t\le\beta\),
the displayed RH support formulas give
\[
h_*(t)=\frac{3m}2\sin t\cos t
+\frac12-\sin t-\frac12\cos t.
\]
Its derivative is
\[
h_*'(t)=\frac{3m}2\cos(2t)
-\cos t+\frac12\sin t.
\]
Because
\(\cos(2t)\ge\cos(2\arctan(1/3))=4/5\),
\(m>1\), \(\cos t\le1\), and
\(\sin t\ge0\), the derivative exceeds
\(6/5-1>0\).

On the middle phase
\(\beta\le t\le L-\beta\),
\[
h_*(t)=R_0\sin(3t/2+\pi/8)
+\frac12-\sin t-\cos t.
\]
Its second derivative is
\[
h_*''(t)=-\frac94 R_0
\sin(3t/2+\pi/8)+\sin t+\cos t.
\]
The argument of the first sine runs
symmetrically between
\(u_0=3\beta/2+\pi/8\) and
\(\pi-u_0\), with
\(0<u_0<\pi/2\). Therefore
\[
R_0\sin(3t/2+\pi/8)
\ge R_0\sin u_0=\cos\beta.
\]
Since \(\beta<\arctan(1/3)\),
\(\cos\beta>3/\sqrt{10}> (4/9)\sqrt2\),
and so
\[
h_*''(t)\le-\frac94\cos\beta+\sqrt2<0.
\]
The reference support phases exchange f
and g under \(t\mapsto L-t\);
hence \(h_*(L-t)=h_*(t)\).
Strict concavity forces the middle
maximum to occur uniquely at \(L/2=\pi/4\).
The reflected last phase is strictly
decreasing.

The endpoint values are zero by the RH
formulas. At the middle point,
\(3(L/2)/2+\pi/8=\pi/2\), giving
\(h_*(L/2)=R_0+1/2-\sqrt2\).
Moreover \(3\beta/2+\pi/8 <
L-\beta\), because
\(\beta<\pi/8<3\pi/20\).
Thus \(\sin u_0<\cos\beta\),
so \(R_0>1\) and
\(h_*(L/2)>3/2-\sqrt2>0\).
Strict increase/decrease and the
intermediate value theorem prove
exactly two crossings for each y
between zero and the maximum. QED.

**Why PR #7's crossing cannot transfer verbatim.**
The reverse-bend canonical corner
in PR #7 crosses each actual strip
height only once, and its
ordinary-area majorant integrates
a **single** left forbidden boundary
\(x=g(y)\).
Romik's genuine one-turn corner
crosses every intermediate height
twice, so any such single-crossing
identity would omit one entire
wall branch. This obstruction occurs
already at the candidate itself;
it cannot be removed by imposing
near-reference regularity.

## 3. Transfer: connected corner superlevels give interval niches

**Lemma DC2 (continuous union of forbidden intervals).**
For any downward cap U, fix y≥0
and put
\[
T_y=\{t\in(0,L):h_C(t)>y\}.
\]
If \(T_y\) is a **nonempty interval**,
then the complete forbidden niche
section at height y is one open interval
\[
\boxed{N(U)_y=(\ell_U(y),r_U(y)),}
\tag{DC.3}
\]
with endpoints determined by the
**entire turning-angle continuum**:
\[
\boxed{\begin{aligned}
\ell_U(y)&=\inf_{t\in T_y}
[x_C(t)-(h_C(t)-y)\cot t],\\
r_U(y)&=\sup_{t\in T_y}
[x_C(t)+(h_C(t)-y)\tan t].
\end{aligned}}
\tag{DC.4}
\]

**Proof.** For each t∈T_y, DC.1 gives
one nonempty open interval I_t(y).
The two endpoints depend continuously
on t in T_y. Given t_0∈T_y,
the interval I_{t_0} has positive
length; for all t sufficiently close
to t_0, I_t intersects I_{t_0}.
If the union of the I_t had two
disjoint connected components,
the preimages of those components
under this locally-overlapping
family would partition the connected
interval T_y into two disjoint
nonempty relatively open subsets.
This is impossible. The union is
therefore a connected open subset of
the line, hence an open interval.
Its endpoints are precisely the infimum
and supremum in DC.4. QED.

**Corollary DC3 (Romik horizontal niche
is one interval at every positive level).**
By DC1, for each \(0<y<h_*(L/2)\)
the set T_y is precisely the
interval between its two crossing
angles. Thus DC2 applies.

The reference cap and its niche are
horizontally reflection symmetric.
The interval is therefore centered:
\[
N(U_*)_y=(-r_*(y),r_*(y)).
\]
Its **true ordinary niche area**
is exactly
\[
\boxed{
|N(U_*)|=2\int_0^{h_*(L/2)}r_*(y)\,dy.
}
\tag{DC.5}
\]
This is the two-front counterpart
of PR #7's integral under one
crossing graph.

## 4. Exact two-front *ordinary-area* formula for two opposite turns

Let U,V be two downward convex caps
in a shared incoming unit strip,
with full positive niches below y=1/2.
Let \(C=U\cap\rho V\) be their
**outer convex intersection**, where
\(\rho(x,y)=(x,1-y)\).
For each y, \(C_y\) is a compact
interval \([L_C(y),R_C(y)]\), possibly
empty. Suppose both one-turn
corner heights have connected
superlevel angle sets T_y
for every \(0<y<1/2\).
By DC2, their positive niche
slices are intervals
\((\ell_U(y),r_U(y))\) and
\((\ell_V(y),r_V(y))\).

The lower and upper forbidden regions
are disjoint in height, so by Fubini
the genuine paired surviving set
\(E=(U\setminus N(U))\cap\rho(V\setminus N(V))\)
has **exact ordinary area**
\[
\boxed{\begin{aligned}
|E|={}&|C|\\
&-\int_0^{1/2}
 \big[\min(R_C(y),r_U(y))
       -\max(L_C(y),\ell_U(y))\big]_+\,dy\\
&-\int_0^{1/2}
 \big[\min(R_C(1-y),r_V(y))
       -\max(L_C(1-y),\ell_V(y))\big]_+\,dy.
\end{aligned}}
\tag{DC.6}
\]
An empty outer slice is interpreted as
zero intersection length.

This formula has **the correct clipping sign**
even when the two caps have different
faces, different contact patterns,
different widths or asymmetric left/right
flanks. It is a direct 1D horizontal
intersection calculation; it does
**not** replace the effective niche
loss by an untruncated signed Green area.

If S is an actual connected sofa
contained in E, then \(|S|\le|E|\).
E need not be connected for arbitrary
input caps, and disconnected total
area is not claimed to be the area
of one physically connected sofa.
For actual full-turn hull caps,
S⊂E follows from canonical support
tightening and their outer caps.

**Important:** for arbitrary competing
caps, h_C need not be unimodal;
T_y may have multiple components.
In that case DC.6 can be extended
by retaining a union of intervals,
but the simple four-boundary
formula is not licensed by DC2.
PR #7's fixed-endpoint quadratic
coercivity alone does not impose
this one-peak contact topology
on arbitrary two-turn competitors.

## 5. The unsolved sharp inequality is now concrete

Within the two-front domain DC.6,
Romik's optimality would follow by
proving for *all actual competitive
pairs* that the true effective
loss integrals dominate
\(|C|-M\). At the candidate equality
is attained. This is **not a proved
inequality**, and it is not an
automatic consequence of PR #7's
one-corner reverse quadratic theorem.

Two independent new difficulties
remain after the transfer:

1. **Geometric admission:** show
   every putative global area maximizer
   can be handled by the one-peak
   two-front domain, or include all
   extra contact components with
   correctly signed area terms.
2. **Sharp two-cap calibration:** prove
   that the sum of the two *clipped*
   removal integrals in DC.6 is at least
   \(|C|-M\), paying for the genuine
   mixed-parent area credit. The
   signed one-turn objective by
   itself does not do this.

PR #7 already solves a different
quadratic after a successful
single-crossing area reduction;
the sharp auxiliary functional
AF3 in PR #3 also already
maximizes to M. Merely importing
more strict-concavity algebra
does **not** supply the missing
ordinary-area bridge.

**Status:** DC1–DC6 are pen-and-paper
identities and monotonicity statements,
self-reviewed only. They do not
prove global Romik optimality,
a universal new area bound, or
a reduction of all possible motions
to complete turns. No Lean, CI,
numerical optimizer, or sampled
area certificate is used.
