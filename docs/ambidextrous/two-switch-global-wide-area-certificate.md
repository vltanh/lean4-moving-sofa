# A direct two-switch area certificate for all full turns of width at least 2.822

**New result TS-CERT1.** Every compact connected planar sofa with
both **complete conventional** right-angle turns through a
unit-width hallway from one common incoming horizontal strip
obeys

\[
\boxed{W\ge\frac{1411}{500}=2.822\quad\Longrightarrow\quad
|S|\le \frac{4198376550651309}{2560000000000000}
=1.6399908\ldots<\frac{41}{25}<M.}
\tag{TS-CERT.1}
\]

The global width theorem [TSW](three-point-switching-fiber-width.md)
already gives \(W\le2\sqrt2\), so the result excludes the
**entire outer width interval**
\([2.822,2\sqrt2]\), about \(0.006427\) units wide, from
any sharp-area counterexample. This improves the earlier
explicit \(10^{-7}\) excluded interval by **more than 60,000-fold**.

The argument uses no \(P_J\) optimization, curvature regularity,
maximizer hypothesis, Romik neighborhood, symmetry of a
competitor, or artificial assumption that its horizontal extrema
have equal heights. It *does* require both complete conventional
turns; unrestricted partial-turn sharp optimality is still open.

## 1. Two real switching angles, three retained witnesses

Normalize the horizontal extrema of S to \(x=0,W\) and its
incoming vertical span to \(H\le1\). By connectedness,
choose an actual point \(C=(W/2,y_0)\in S\) and
actual horizontal extreme points
\(P=(0,y_0+a)\), \(Q=(W,y_0+b)\in S\).

Set \(D=W/2\). At the first safe-wall switch
\(\theta\in(0,\pi/2)\) of C in the lower turn
and the corresponding switch \(\varphi\) in the
vertically reflected upper turn, **both**
inner support depths at C are at most one.
Testing their *actual support functions* against P,Q yields

\[
\begin{array}{ll}
b\le F_R(\theta,W),&
a\le F_L(\theta,W),\\
-b\le F_R(\varphi,W),&
-a\le F_L(\varphi,W),
\end{array}
\tag{TS-CERT.2}
\]

where

\[
F_R(t,W)=\frac{1-D\cos t}{\sin t},\qquad
F_L(t,W)=\frac{1-D\sin t}{\cos t}.
\tag{TS-CERT.3}
\]

The *same switches* also give **true outer support bounds**
at C:

\[
h_S(u_\theta)-C\cdot u_\theta\le1,\quad
h_S(v_\theta)-C\cdot v_\theta\le1,
\tag{TS-CERT.4}
\]

and both reflected counterparts at \(\varphi\).
These outer inequalities, rather than the anchor-only
inner bounds, are what makes the area exclusion possible.

Adding TS-CERT.2 shows separately that
\(F_R(\theta)+F_R(\varphi)\ge0\) and
\(F_L(\theta)+F_L(\varphi)\ge0\);
parameter boxes on which either necessary condition is
strictly impossible can be rejected.

By [TSW.13](three-point-switching-fiber-width.md),
for \(D\ge3/(2\sqrt2)\) the maximum of
\(G_D=F_R+F_L\) is \(2\sqrt2-W=:\varepsilon\).
Since \(0\le G_D(\theta)+G_D(\varphi)\),
each G value is at least \(-\varepsilon\).
Hence

\[
\sin\theta+\cos\theta
\ge D-\varepsilon\sin\theta\cos\theta
\ge W-\sqrt2 .
\tag{TS-CERT.5}
\]

For \(W\ge2.822\), \(W-\sqrt2>7/5\).
At half-tangents \(r=\tan(t/2)=1/4\)
and \(r=3/5\), \(\sin t+\cos t=23/17<7/5\);
the trigonometric sum is strictly larger between
these two angles and smaller outside them.
Thus for **both** actual switches

\[
\boxed{\frac14<\tan(\theta/2),\tan(\varphi/2)<\frac35.}
\tag{TS-CERT.6}
\]

The numerical root comparisons are elementary exact rational
squares; no decimal approximation to \(\sqrt2\) is a premise.

## 2. Eliminate the unknown anchor heights on each parameter box

Put \(q=x/W\in[0,1]\).
Let a rational rectangular box have
\(W\in[w_-,w_+]\),
\(r_\theta\in[t_-,t_+]\),
\(r_\varphi\in[p_-,p_+]\), with
\(r=\tan(t/2)\).
The half-angle identities make all normal coordinates rational:

\[
c(r)=\frac{1-r^2}{1+r^2},\qquad
s(r)=\frac{2r}{1+r^2}.
\]

For \(W>2\) and \(r\in(0,1)\),
\(F_R(r,W)=(1-(W/2)c(r))/s(r)\)
is **increasing in r**, decreasing in W.
Likewise \(F_L(r,W)=(1-(W/2)s(r))/c(r)\)
is **decreasing in r**, decreasing in W.
Consequently TS-CERT.2 gives the **exact interval bounds**

\[
\boxed{
\begin{aligned}
a_-&=-F_L(p_-,w_-)\le a\le F_L(t_-,w_-)=a_+,\\
b_-&=-F_R(p_+,w_-)\le b\le F_R(t_+,w_-)=b_+.
\end{aligned}}
\tag{TS-CERT.7}
\]

These enclosures need not use the same parameter value
at both ends: they are independent safe relaxations.
If their intervals are empty, reject the box.
Also reject if either exact rational upper bound
\(F_R(t_+,w_-)+F_R(p_+,w_-)<0\) or
\(F_L(t_-,w_-)+F_L(p_-,w_-)<0\).

## 3. True ordinary-area bounds from eighteen fixed frames

Take the eighteen rational directions
\((c,s)=(a/h,b/h),(b/h,a/h)\) for
the nine Pythagorean triples

\[
(3,4,5),(5,12,13),(8,15,17),(20,21,29),
(28,45,53),(33,56,65),(48,55,73),
(65,72,97),(60,91,109).
\tag{TS-CERT.8}
\]

They are truly visited during **both full quarter turns**.
Each has \(c,s>0\) and
\(\max(c/s,s/c)\le12/5\).

For any actual point \((Wq,y_0+z)\in S\)
consider the support depths at one lower frame.
The three retained witnesses \(P,Q,C\) imply

\[
\begin{split}
z&\ge \min\left(
\frac{\max(W(1-q)c+b s,\;-Wq c+a s,\;W(1/2-q)c)-1}{s},
\\[-2pt]&\hspace{29mm}
\frac{\max(Wq s+a c,\;-W(1-q)s+b c,\;W(q-1/2)s)-1}{c}
\right)=:B_t(q;a,b,W).
\end{split}
\tag{TS-CERT.9}
\]

This follows from the necessary **inner-wall disjunction**:
the actual support exceeds the support of each
retained anchor, so every feasible point must be above
the minimum of the two anchor-supported wall heights.
The vertically reflected upper-turn frames analogously give
\(z\le-B_t(q;-a,-b,W)\).

On a rational parameter box, each term in TS-CERT.9 is
an affine function of q. To bound it from below,
choose \(a_-,b_-\) and minimize each W-dependent affine
term separately over \([w_-,w_+]\), respecting its
coefficient's sign. Let \(\underline B_t(q)\) be the
resulting explicit piecewise-affine lower bound.
For the reflected side use \(-a_+,-b_+\).
Then every feasible point satisfies

\[
z\ge\max_t\underline B_t(q),\qquad
z\le-\max_t\underline B_t(q;-a_+,-b_+).
\tag{TS-CERT.10}
\]

The checker enumerates all three anchor terms on both
walls, splits at q=1/2 for the sign of
the midpoint term, and never substitutes a sampled
**upper** bound for an actual support lower bound.

## 4. The two unknown switch frames supply outer ceilings

At the true lower switch \(\theta\),
TS-CERT.4 implies every sofa point satisfies

\[
z\le
K_\theta(q,W):=
\min\left(
\frac{1+W(1/2-q)\cos\theta}{\sin\theta},
\frac{1+W(q-1/2)\sin\theta}{\cos\theta}
\right).
\tag{TS-CERT.11}
\]

At the true upper switch,
\(z\ge-K_\varphi(q,W)\).
On the box, upper-bound each of the two affine
branches using the monotonic endpoint bounds for
\(1/s,1/c,c/s,s/c\), choosing w_+ for
positive W coefficients and w_- for negative ones.
Their minimum \(K^+_{[t_-,t_+]}(q)\)
is a valid *upper* bound for every actual
\(K_\theta(q,W)\). Likewise for the phi box.

Thus at every q the true vertical-fiber spread is at most

\[
d(q)=
\min\left(1,\left[
\min\left(K^+_\theta(q),
-\max_t\underline B_t(q;-a_+,-b_+)\right)
-\max\left(-K^+_\varphi(q),\max_t\underline B_t(q)\right)
\right]_+\right),
\tag{TS-CERT.12}
\]

with \([x]_+=\max(0,x)\).
The incoming strip height H≤1 gives the
additional cap of one. Its unknown vertical
location does not affect this valid **area upper**.
No assumption of interval-filled fibers is used.

Fubini gives \(|S|\le W\int_0^1d(q)\,dq\).
All constituent functions of d(q) are min/max
of finitely many affine rational functions;
their absolute q-slopes are ≤\(w_+(12/5)<7\)
for either the upper or lower roof. Thus d
is **14-Lipschitz** on [0,1].

## 5. Exact 512-cell rational quadrature and complete box covering

For \(N=512\), \(q_i=(2i+1)/(2N)\),
the elementary Lipschitz midpoint bound is

\[
\boxed{|S|\le w_+
\left(\frac1N\sum_{i=0}^{N-1}d(q_i)
+\frac{14}{4N}\right).}
\tag{TS-CERT.13}
\]

The 14/(4N) term rigorously covers **every
real q**, not just the finite midpoint samples.

The [replay checker](computer-assisted/check_two_switch_wide_area.py)
starts from the single rational root box

\[
[w_-,w_+]=[1411/500,283/100],\qquad
[t_-,t_+]=[p_-,p_+]=[1/4,3/5].
\]

It recursively bisects whichever of
\((w_+-w_-)/(1/20),\,t_+-t_-,\,p_+-p_-\)
is largest, with deterministic first-maximum
tie-breaking. Every child exactly partitions
its parent's parameter box.

For each leaf it either proves the necessary
switch-height intervals are incompatible, or
proves TS-CERT.13 is **strictly below 41/25**
using rational operations exclusively.
To evaluate the q-cell affine envelopes cheaply,
it rounds every affine **lower** coefficient
downward to integers at scale 10^10, and every
affine **upper** coefficient upward. Subsequent
multiplication by rational q_i is itself
rounded outward. The final area bound is
compared using exact Fraction arithmetic.
Explicit magnitude guards keep every
numpy int64 operation safely away from overflow.

**Executed exact replay (October 8, 2026):**

- 5,393 total visited parameter boxes;
- 1,410 boxes rejected by exact necessary-condition contradictions;
- 1,287 accepted exact area leaves;
- maximum depth 19; **no unresolved leaves**;
- largest accepted upper area
  \[
  \boxed{\frac{4198376550651309}{2560000000000000}
  =1.6399908\ldots}
  \]
  and strict rational margin to 41/25
  \[
  \boxed{\frac{23449348691}{2560000000000000}>0.}
  \]

The arithmetic checker is not itself a Lean proof of
Sections 1–4: the geometric reductions are explicit
pen-and-paper arguments, still awaiting independent review.
The checker is deterministic and **does not trust an
optimizer or a locally discovered maximizer**.
No Lean formalization, CI, dependency installation
or manuscript build was performed.

## 6. Sharp-value scope and next useful direction

The argument excludes a **global 0.006427-unit width band**
of complete two-turn sofas, a substantial improvement
over the 1e-7 switching-near-equality certificate.
It is nevertheless only a **boundary-domain** theorem.

The long unsolved interval \(2<W<2.822\)
includes Romik's horizontal span.
The new approach's two-dimensional switch-angle
box search is much smaller than the original
eight-dimensional full-hallway offset search,
but it cannot be sharpened to \(M\) merely
by adding boxes if its underlying three-anchor
relaxation remains too loose. Any proposed
extension must first measure the gap at
widths around the Romik reference and
incorporate **additional interacting occupied points**
or stronger actual support information.

Do not promote TS-CERT1 to unrestricted sharp
optimality or assume partial turns can be
completed without area loss.
