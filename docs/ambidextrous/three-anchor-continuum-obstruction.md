# A continuum, connected area-1.67 obstruction to three-anchor switching relaxations

**Result AR3-NEG.** Even retaining **every continuously
rotating hallway orientation** does not make the
three-horizontal-anchor support relaxation sharp.
There is an explicit compact, connected, unit-height
set \(E\) of area

\[
\boxed{|E|=\frac{167}{100}=1.67>M}
\tag{AR3.1}
\]

with horizontal width \(W=12/5\), containing the
left, midpoint and right anchors

\[
P=(0,1/2),\quad C=(6/5,1/2),\quad
Q=(12/5,1/2),
\]

such that *every point of E*, at *every angle*
of **both** conventional quarter-turn families,
satisfies the inner-wall disjunction **when the
support functions are replaced by the support of
only these three anchors**. It also satisfies
both outer-wall constraints at the proposed
\(45^\circ\) switches anchored at C.

Nevertheless **E is not a real full-turn sofa**:
an explicit triple of its actual points violates
the actual, full-support hallway condition at
a single rational angle. Thus this is a
counterexample to an **auxiliary relaxation
strategy**, not a construction exceeding Romik's
feasible sofa area.

The example directly shows why indefinitely refining
the all-angle **three-anchor** method used in the
wide-area certificates is not enough to prove
sharpness near Romik's horizontal width.
One must retain additional **interacting occupied
points** and their induced changes to real support.

## 1. Two rational polygonal wings and a zero-area bridge

Let \(W=12/5\). For \(0\le x\le1\) define

\[
h(x)=
\begin{cases}
x+1/5,&0\le x\le3/10,\\
1/2,&3/10\le x\le17/20,\\
(10/3)(1-x),&17/20\le x\le1.
\end{cases}
\tag{AR3.2}
\]

Put

\[
\begin{split}
L&=\{(x,y):0\le x\le1,\ |y-1/2|\le h(x)\},\\
R&=\{(W-x,y):(x,y)\in L\},\\
B&=[1,W-1]\times\{1/2\},\qquad
E=L\cup B\cup R .
\end{split}\tag{AR3.3}
\]

The definitions match at all three breakpoints.
L and R meet the bridge B at (1,1/2) and
(W-1,1/2), so E is compact and connected.
It lies in the unit-height incoming strip,
contains P,C,Q, and has width W.

The exact area calculation is elementary:

\[
\int_0^1h(x)\,dx=
\underbrace{\frac{21}{200}}_{[0,3/10]}
+\underbrace{\frac{11}{40}}_{[3/10,17/20]}
+\underbrace{\frac{3}{80}}_{[17/20,1]}
=\frac{167}{400}.
\]

Each wing has vertical fiber length 2h, the
bridge has area zero, and the wings do not
overlap. Hence \(|E|=4(167/400)=167/100\).

For the exact candidate area
\(M=1+4Y^2+\arctan Y\),
\(4Y^3+3Y-1=0\), monotonicity of the
cubic gives \(Y<3/10\).
Because \(\arctan Y<Y\) for positive Y,

\[
M<1+4(3/10)^2+3/10
=\frac{83}{50}=1.66<1.67 .
\tag{AR3.4}
\]

No rounded decimal is needed.

## 2. Each wing lies inside its anchor's unit disk

For all \(x\in[0,1]\),

\[
\boxed{x^2+h(x)^2\le1.}\tag{AR3.5}
\]

For the first two intervals this follows from
\(x\le3/10,h\le1/2\) and
\(x\le17/20,h=1/2\).
On the third interval,
\(x^2+(10(1-x)/3)^2\) is a
convex quadratic, hence no greater
than the larger endpoint value;
the values at \(17/20\) and 1 are
\(389/400<1\) and 1.
Thus every left-wing point has Euclidean
distance at most one from P, and by
reflection every right-wing point is
at Euclidean distance at most one from Q.

Let \(h_A\) be the support of **only**
the three anchors \(A=\{P,C,Q\}\).
For any \(t\in[0,\pi/2]\), put
\(u_t=(\cos t,\sin t)\) and
\(v_t=(-\sin t,\cos t)\).
Because the anchors share ordinate 1/2,

\[
h_A(u_t)=W\cos t+\tfrac12\sin t,
\qquad
h_A(v_t)=\tfrac12\cos t.
\tag{AR3.6}
\]

For any left-wing point p,
\(h_A(v_t)-p\cdot v_t
=(P-p)\cdot v_t\le|P-p|\le1\).
For any right-wing point,
\(h_A(u_t)-p\cdot u_t
=(Q-p)\cdot u_t\le|Q-p|\le1\).
The vertical reflection across y=1/2
preserves all anchor positions and the
two wing disk inequalities, so the
**upper-hand anchored** disjunction
also holds for every angle.

For bridge points \(p=(x,1/2)\) with
\(1\le x\le7/5\), the two anchored
depths are \((W-x)\cos t\) and
\(x\sin t\). Therefore

\[
\min((W-x)\cos t,x\sin t)
\le\sqrt{x(W-x)\sin t\cos t}
\le\sqrt{\frac{(W/2)^2}{2}}
=\frac{3\sqrt2}{5}<1.
\]

Thus the bridge also obeys **both**
anchored full-angle inner-wall systems.

## 3. The two proposed switch outer walls also contain E

At \(t=\pi/4\), take the four proposed
outer support bounds at the midpoint
anchor C as \(h(u)-C\cdot u\le1\),
\(h(v)-C\cdot v\le1\), and their
vertically reflected counterparts.
Their intersection in physical coordinates is

\[
\boxed{|x-6/5|+|y-1/2|\le\sqrt2 .}
\tag{AR3.7}
\]

This contains E. Indeed on its left wing
\(h(x)\le x+1/5\), so
\((6/5-x)+h(x)\le7/5<\sqrt2\).
The right wing is the horizontal reflection;
and the horizontal bridge has
\(|x-6/5|\le1/5<\sqrt2\).
The associated three-anchor **switch**
depths at C are \(6/(5\sqrt2)<1\),
so the assumed switch itself also has
consistent anchor data.

**All these are legitimate necessary
constraints when using only the three
retained anchors**. They do **not**
assert the actual support of E equals
\(h_A\).

## 4. A concrete actual forbidden triple

At the proper rational angle
\(u=(3/5,4/5)\), \(v=(-4/5,3/5)\),
take the three actual points of E

\[
p=(31/20,1/20),\quad
q=(21/10,1),\quad r=(0,7/10).
\]

The right-wing profile contains p and q,
and the left-wing profile contains r.
Direct rational evaluation gives

\[
\boxed{
(q-p)\cdot u=\frac{109}{100}>1,
\qquad
(r-p)\cdot v=\frac{163}{100}>1.
}
\tag{AR3.8}
\]

By the exact full-support forbidden-triple
equivalence [CF1](configuration-area-certificate.md),
**no** placement of that ordinary unit
L-hallway contains E at this angle.
Thus E is not a real full-turn sofa,
despite satisfying all the weakened
three-anchor tests and the proposed
45-degree switch outer walls.

## 5. Strategic conclusion

The earlier
[two-switch wide certificate](two-switch-global-wide-area-certificate.md)
is mathematically sound as a **necessary-condition
area bound** on its wide domain, where it
does exclude possible sharp competitors.
But the present exact connected example
shows that carrying the **same three-anchor
relaxation** to the reference width cannot
be expected to prove \(|S|\le M\):
the relaxed domain is already too large
even after keeping every turning angle.

The next genuinely different direct approach
must keep **interacting support witnesses from
occupied spatial regions**, such as the
forbidden triples of CF1, or find a
global geometric operation eliminating
those incompatible configurations without
artificially asserting disconnectedness
or curvature.

This is a self-contained pen-and-paper
negative result. It uses no numerical search,
Lean, CI, or candidate-shape approximation.
