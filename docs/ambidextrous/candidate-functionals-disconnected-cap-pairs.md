# The two one-turn survivor sets can have a disconnected intersection

**Purpose.** The user-supplied candidate-functionals note, Remark CF8, proposes that an arbitrary intersection of the surviving bodies of two normalized one-turn caps is itself a two-full-turn sofa. That statement is false **without a connectedness/nonempty-fiber hypothesis**. An exact \(2\times1\) rectangle demonstrates the gap. It is an elementary negative control on the proposed cap-pair shifts/splits, not a counterexample to Romik's area. Labels CI are local.

## 1. A single normalized cap with connected one-turn survivor

Let \(U=[-1,1]\times[0,1]\), a downward convex cap with a full bottom interval, height one and width two. At a lower turn angle \(0\le t\le\pi/2\), write \(c=\cos t,s=\sin t\). Its two upper supports are
\[
f(t)=h_U(c,s)=c+s,\qquad
g(t)=h_U(-s,c)=s+c.
\]
The inner-wall forbidden quadrant has upper envelope
\[
\min\left(
\frac{f(t)-1-xc}{s},
\frac{g(t)-1+xs}{c}
\right),
\]
when \(0<t<\pi/2\). The roof reaches its maximum over all x at the inner-wall corner
\[
C_y(t)=(f-1)s+(g-1)c=(c+s)(c+s-1).
\]
Because \(1\le c+s\le\sqrt2\), this height never exceeds
\[
\boxed{H_N=2-\sqrt2<1.}
\]
The top segment \([-1,1]\times\{1\}\) is consequently untouched by every forbidden lower-turn quadrant, and the complete one-turn survivor \(A_U=U\setminus N(U)\) has connected nonempty vertical interval sections, all meeting that top segment. Its lower full-turn motion exists by the canonical support-tightening construction.

Vertically reflect this one-turn body, producing \(A_U^\rho=\rho(A_U)\) with \(\rho(x,y)=(x,1-y)\). It is connected and has a complete upper-turn motion. The two one-turn bodies share the same incoming vertical strip and horizontal projection.

## 2. Their full intersection is disconnected

At the single angle \(t=\pi/4\), and at x=0, both inner-wall roof values equal
\[
\boxed{n_U(0)\ge2-\sqrt2>\frac12,}
\]
because \(\sqrt2<3/2\). The downward one-turn survivor requires \(y\ge n_U(0)\), while the reflected upper-turn survivor requires \(y\le1-n_U(0)\). They have **no common point with x=0**.

Nevertheless the points \(p_+=(1,1/2)\) and \(p_-=(-1,1/2)\) survive *both* complete turns. For \(p_+\), at every lower-turn angle its first inner-wall depth is
\[
h_U(c,s)-p_+\cdot(c,s)=(c+s)-(c+s/2)=s/2\le1;
\]
for \(p_-\), its second inner-wall depth is
\[
h_U(-s,c)-p_-\cdot(-s,c)=(s+c)-(s+c/2)=c/2\le1.
\]
The reflected upper-turn constraints are the same because the rectangle and these mid-height points are invariant under y-reflection.

Thus
\[
E=A_U\cap\rho(A_U)
\]
contains points of both positive and negative x, but **contains no point at x=0**. Any connected subset of the plane meeting both sides has a connected x-projection containing zero. Therefore
\[
\boxed{E\text{ is nonempty but disconnected.}}
\tag{CI.1}
\]

## 3. Corrected interpretation of the package

Each point of \(E\) satisfies the two families of canonical hallway constraints, so **each connected component** is a feasible full-turn subset after appropriate endpoint placement. But the union \(E\) is not necessarily a single sofa: it can consist of two disjoint components.

Consequently the assertion in CF8 that intersections or shifted/split cap pairs always *produce admissible connected sofas* needs a connectedness hypothesis (or an explicit component selection). A bound on a sum of component areas is not automatically a bound on the largest connected sofa, and an upper relaxation computed on disconnected unions cannot be promoted to an attained feasible sofa.

The elementary SPB upper enclosure for an **already actual connected** full-turn body remains valid, because its actual hull fibers are nonempty and the canonical envelope containing that body is connected. The exact counterexample here does not challenge the bound \(P_J(U)\le M/2\); it challenges only CF8's unconditional feasibility statement.

All geometry above is pen and paper. No numerical check, CI, Lean/Lake compilation, dependency installation or manuscript build is used.