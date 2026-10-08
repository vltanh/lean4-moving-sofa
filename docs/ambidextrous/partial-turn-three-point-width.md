# The \(2\sqrt2\) width gate also holds for competitive **partial** turns

**Main theorem PTW1.** Every compact connected ambidextrous sofa \(S\)
starting in a common incoming unit-width strip \(0\le y\le H\le1\),
with arbitrary continuous (possibly nonmonotone or more-than-quarter)
motions around both handednesses, satisfies

\[
\boxed{|S|>\sqrt2 H\quad\Longrightarrow\quad
\operatorname{width}_x S\le 2\sqrt2.}
\tag{PTW.1}
\]

In particular, since \(M> \sqrt2\), any sofa competitive with
Romik's area \(M=1.644955\ldots\) obeys the bound.
The area threshold is used **only** to force the correct handed
angular reach. This is not a \(1.65\) argument and neither proves
Romik optimality nor assumes candidate curvature, symmetry,
horizontal-face alignment, or completion of the original motions.

The proof strengthens [TSW](three-point-switching-fiber-width.md)
by discovering that the **outgoing unit strip**, not an artificially
completed quarter turn, supplies the second endpoint of the
safe-wall switching argument.

## 1. Endpoint version of the switching-square lemma

Let \(S\subseteq\{0\le y\le H\}\) be compact and nonempty.
Fix a conventional lower-turn family of hallway orientations
\(0\le t\le\alpha\le\pi/2\), with actual (not proposed)
support-depth disjunction

\[
h_S(u_t)-p\cdot u_t\le1
\quad\text{or}\quad
h_S(v_t)-p\cdot v_t\le1,\qquad
u_t=(\cos t,\sin t),\
v_t=(-\sin t,\cos t).
\tag{PTW.2}
\]

Assume **the terminal full-body unit-strip condition**

\[
\boxed{w_S(u_\alpha)\le1.}
\tag{PTW.3}
\]

For a point \(p=(x,y)\in S\) with \(R=r-x>1\),
the first depth at \(t=0\) is \(r-x=R>1\).
At the endpoint \(t=\alpha\) the first depth is
\(\le w_S(u_\alpha)\le1\).

Let \(A\) and \(B\) be the closed sets of turn angles
at which the first and second support depths are
respectively at most one. Hallway feasibility is
\(A\cup B=[0,\alpha]\). The first set \(A\)
is nonempty and excludes zero. Put
\(\tau=\min A>0\).
For every \(0\le t<\tau\), \(t\notin A\)
and hence \(t\in B\). By closedness,
\(\tau\in B\); and by definition \(\tau\in A\).
Thus at **one actual visited** frame
\(\tau\in(0,\alpha]\), both support depths
are at most one. No second-wall unsafety
at the terminal frame was required.

Reflecting a conventional upper-handed motion
in a horizontal line gives the same lemma.
The reflected outgoing strip is again a
full-body unit strip of the corresponding
first normal.

## 2. The full three-point fiber argument is unchanged

Let \([l,r]\) be the horizontal projection of
compact connected \(S\), and suppose \(W=r-l>2\).
For any \(x\in(l+1,r-1)\), connectedness
supplies actual points \((x,y_-),(x,y_+)\in S\)
at the minimum and maximum height of that fiber.
Choose actual horizontal extreme points
\(P=(l,y_L), Q=(r,y_R)\).

Apply the first-entry lemma to \(p_-=(x,y_-)\)
for the lower turn and to the horizontally
reflected \(p_+=(x,y_+)\) for the upper turn.
The resulting angles \(\theta,\varphi\)
need not agree and need not reach \(\pi/2\).
The same four retained-point support tests as
in TSW.5–TSW.6 yield exactly

\[
2(y_+-y_-)\le
G_{L,R}(\theta)+G_{L,R}(\varphi),
\tag{PTW.4}
\]

where \(L=x-l>1\), \(R=r-x>1\) and

\[
G_{L,R}(t)=
\frac{\sin t+\cos t-R\cos^2t-L\sin^2t}
{\sin t\cos t}.
\tag{PTW.5}
\]

Since \(\theta,\varphi\in(0,\pi/2)\),
the same pointwise conclusion TSW.9 follows
**without full-turn completion**.
At the horizontal midpoint \(x=(l+r)/2\),
\(L=R=D=W/2>1\), so

\[
0\le y_+-y_-
\le\max_{0<t<\pi/2}
\frac{\sin t+\cos t-D}{\sin t\cos t}.
\]

If \(D>\sqrt2\), every numerator is negative,
a contradiction. Hence \(W\le2\sqrt2\).
The explicit midpoint-fiber ceiling TSW.13
also remains valid for any partial motions
satisfying the two endpoint hypotheses PTW.3.

**Important:** We used the *actual* terminal strip,
not merely a terminal hallway placement. A body
fitting a single L-shaped corridor position
need not satisfy PTW.3. The latter is part of
a completed passage around the corner.

## 3. Admission of arbitrary original motions at high area

It remains to justify the two conventional
partial intervals and their terminal strips.
This is exactly the proper-angle reach
argument in
[GH Section 3](midpoint-bound-general-motions.md).
For completeness, the relevant steps are:

1. The original motion's lifted frame angle
   begins at zero, and the endpoint sits in
   an **outgoing unit strip** with its prescribed
   rotated normal \(u_\omega\).
2. Intersection of incoming and outgoing unit
   strips of vertical span \(H\) yields
   \(|S|\le H/|\cos\omega|\) when the determinant
   is nonzero. If \(|S|>\sqrt2 H\), the endpoint
   cannot have \(|\cos\omega|\ge1/\sqrt2\).
3. GH Section 2 shows a **wrong-way**
   \(45^\circ\) hallway has area at most
   \(\sqrt2 H\). Thus a continuous lifted
   motion from zero whose endpoint has
   \(|\cos\omega|<1/\sqrt2\) must reach
   proper \(+\pi/4\) (after the appropriate
   vertical reflection for the upper hand).
4. If the path ever reaches the proper
   \(\pi/2\), restrict to the first
   \([0,\pi/2]\) interval of actually visited
   frames. At \(\alpha=\pi/2\) the first
   normal is vertical, so its full-body
   span is \(\le H\le1\). Otherwise its
   endpoint angle is a proper partial
   \(\alpha\in(\pi/4,\pi/2)\), and the
   **actual outgoing strip** supplies
   \(w_S(u_\alpha)\le1\).

Both hands therefore satisfy the exact
hypotheses of Section 1. Section 2
proves PTW.1. Arbitrarily nonmonotone
motions are allowed because continuity
forces every intermediate angle to be
visited; no monotonicity assumption
or chosen hallway translations enter
the switch argument.

## 4. A genuinely new width normalization, not a sharp value

The branch previously had a width bound
\(W\le 1+2\sqrt2<4\) from
[DU](diagonal-width-upper-bound.md),
and the general full-turn compact box
\([0,5]\times[0,1]\) from FR1.
PTW1 improves the **competitive**
full/partial search domain to

\[
\boxed{[0,2\sqrt2]\times[0,H]}
\quad\text{up to translation, when }|S|>\sqrt2 H.
\tag{PTW.6}
\]

In particular the Euclidean diameter of
such a candidate is at most
\(\sqrt{(2\sqrt2)^2+H^2}\le3\).
This can reduce rigorous angular-mesh
continuity error constants in future
**direct ordinary-area** certificates.

The bound is not an area inequality and
does not eliminate the long-standing
asymmetric opposite-face class.
It gives no area-free replacement for
arbitrary partial-turn completion.

**Verification boundary.** The argument is
a direct hand proof invoking GH's existing
proper-angle reduction, and remains
subject to independent mathematical review.
No Lean/Lake build, CI, heuristic optimizer,
or long certificate was run.
