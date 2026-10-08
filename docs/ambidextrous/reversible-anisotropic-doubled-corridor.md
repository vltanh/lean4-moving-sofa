# The exact reversible doubled-corridor geometry is anisotropic

**Theorem RAD1 (an exact one-to-one filling correspondence).**
Let \(A\subset\mathbb R^2\) be compact, let \(t_0\ge0\),
let \(I_{t_0}=\{(0,z):0\le z\le t_0\}\), and put
\(B=A+I_{t_0}\).
At any *proper conventional* lower turning orientation
\(\theta\in[0,\pi/2]\), set
\[
u_\theta=(\cos\theta,\sin\theta),\qquad
v_\theta=(-\sin\theta,\cos\theta).
\]
Then **A fits some canonical width-one L-hallway at
orientation \(\theta\)** if and only if **B fits the
corresponding supporting L-hallway whose two perpendicular
arm-normal widths are respectively**
\[
\boxed{1+t_0\sin\theta,\qquad1+t_0\cos\theta.}
\tag{RAD.1}
\]
The same iff statement holds for the reflected upper-handed
orientation with normals
\((\cos\theta,-\sin\theta)\) and
\((-\sin\theta,-\cos\theta)\).
This is a *pointwise exact equivalence*, not a heuristic
sufficient condition. It holds simultaneously over the
full continuous turning intervals and for arbitrary
compact nonsmooth sets A; no curvature, convexity,
reflection symmetry or maximizing hypothesis is needed.

**Crucial qualification:** The variable-width hallways in
RAD.1 do **not** describe a single physical rigid corridor
whose walls simply rotate in the body frame.
They constitute an angle-dependent *support-constraint
system*. This exactly captures the additional information
lost when each arm is instead given **uniform width two**.
No new physical moving-sofa equivalence with one rigid
width-two hallway is claimed.

## 1. Proof of the lower-handed iff

For a unit normal n and p∈A, write
\(D_A(p,n)=h_A(n)-p\cdot n\).
For any two compact sets the support function is additive:
\(h_{A+I_{t_0}}=h_A+h_{I_{t_0}}\).
For a lower-handed frame both normals have nonnegative
vertical component, so for any \(p\in A\) and \(z\in[0,t_0]\),

\[
\begin{aligned}
D_B(p+(0,z),u_\theta)
&=D_A(p,u_\theta)+(t_0-z)\sin\theta,\\
D_B(p+(0,z),v_\theta)
&=D_A(p,v_\theta)+(t_0-z)\cos\theta.
\end{aligned}
\tag{RAD.2}
\]

The canonical placement of an L-hallway with arm-normal
widths \(w_u,w_v\) is feasible for every point of B
exactly when
\[
\forall q\in B:\quad
D_B(q,u_\theta)\le w_u\quad\text{or}\quad
D_B(q,v_\theta)\le w_v.
\tag{RAD.3}
\]
Its outer bounds use \(h_B(u_\theta),h_B(v_\theta)\)
and are automatic.

Take the widths from RAD.1.
If every p in A has \(D_A(p,u_\theta)\le1\)
or \(D_A(p,v_\theta)\le1\), the same protecting
arm is safe for **every** vertical fill point
\(p+(0,z)\), by RAD.2.
Conversely, suppose RAD.3 holds for all fill points.
In particular it holds at \(z=0\) for every p∈A.
Subtracting the corresponding **full**
\(t_0\sin\theta\) or \(t_0\cos\theta\)
from the appropriate depth inequality yields
\(D_A(p,u_\theta)\le1\) or
\(D_A(p,v_\theta)\le1\), proving the other direction.

## 2. The reflected upper handedness

For upper normals
\(\tilde u=(\cos\theta,-\sin\theta)\),
\(\tilde v=(-\sin\theta,-\cos\theta)\),
the vertical coordinate of either normal is negative.
Thus \(h_{I_{t_0}}(\tilde u)
=h_{I_{t_0}}(\tilde v)=0\), and
\[
D_B(p+(0,z),\tilde u)
=D_A(p,\tilde u)+z\sin\theta,\qquad
D_B(p+(0,z),\tilde v)
=D_A(p,\tilde v)+z\cos\theta.
\tag{RAD.4}
\]
This time the **topmost** fill point \(z=t_0\)
is the worst simultaneous case.
Evaluating RAD.3 at that top point and subtracting
the corresponding full coefficients again proves
the reverse implication. The forward implication
is immediate for all \(z\). QED.

The incoming/terminal full-body strip conditions
transform exactly as
\(w_B(n)=w_A(n)+t_0|n_y|\);
thus the same additive bookkeeping applies at
the endpoint normal directions. The support-tightened
offsets vary continuously with orientation for compact
A, giving continuous *families of placements*,
although the angle-dependent corridor widths make
this an analytical rather than a rigid-physical
widened hallway.

## 3. Why ordinary width two is strictly weaker

For \(t_0=1\), the reversible arm widths at
\(\theta=\pi/4\) are both
\[
\boxed{1+1/\sqrt2\approx1.7071,}
\]
whereas an ordinary double-width corridor permits
both depths to be as large as 2. The gap at the
symmetric turning orientation is exactly
\(1-1/\sqrt2>0\) per arm.

An exact non-reversibility witness is the rectangle
\[
B=[0,37/20]\times[0,19/10]
=A+I_1,\qquad
A=[0,37/20]\times[0,9/10].
\]
By [SQ1](double-width-fill-and-squeeze-audit.md),
B genuinely completes both conventional turns in
a rigid width-two hallway. At the lower
\(45^\circ\) frame the original core A has a
point where **both** unit-hallway depths equal
\[
73/(40\sqrt2)>1;
\]
hence B violates the stricter reversible
RAD.1 disjunction at that angle, even though it
satisfies a uniform width-two hallway
disjunction. Thus **membership in the doubled
Gerver feasibility domain does not encode the
unit-width inverse**.

## 4. Central filling identity for two actual one-turn survivors

Suppose A and C are genuine width-one one-turn
survivors in common body coordinates, each with
interval-or-empty vertical fibers, and their
original fiber intervals overlap throughout
their common horizontal projection J of
length W. Then the exact geometric identity
from [DGL.6](double-width-gerver-intersection-lift.md) is
\[
\boxed{
(A+I_1)\cap(C+I_1)=(A\cap C)+I_1,\qquad
\left|(A+I_1)\cap(C+I_1)\right|
=|A\cap C|+W.
}
\tag{RAD.5}
\]
The enlarged pair individually satisfies the
reversible variable-arm constraints RAD.1
for its respective handed turn.
The full-sharp ordinary-area statement
\(|A\cap C|\le M\) is therefore **exactly equivalent**
to
\[
\boxed{|(A+I_1)\cap(C+I_1)|\le M+W}
\tag{RAD.6}
\]
on this admissible full-overlap class.

This is the **mathematically correct form**
of the proposed “two expanded Gerver halves plus a
filled center” inequality. It is not proved here.
One cannot substitute the ordinary width-two Gerver
theorem for RAD.6: that theorem optimizes a
**larger, non-reversible, fixed-rigid-hallway class**
without the angle-dependent deductions RAD.1.

## 5. A concrete potential proof direction

The precise widened class has a central area \(W\)
already paid for and a mixed-direction clearance rule
\(1+\sin\theta\) versus \(1+\cos\theta\).
A geometric sharp proof would have to exploit these
specific *unequal arm widths* and pairwise overlap
constraints. Merely growing the corridor to width 2,
maximizing ordinary one-turn areas independently,
or subtracting a free rectangle is not equivalent.

The class remains nonconvex because each frame
requires a disjunction of two inner-wall inequalities.
No area-preserving symmetrization or globally
sharp overlap bound is inferred from support
additivity alone. This is a new exact reversible
encoding and a falsifiable target, not a solution
of the unrestricted Romik conjecture.
No Lean formalization or numerical upper-bound
search was used.
