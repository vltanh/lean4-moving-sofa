# Exact short-width exclusion for every horizontal-middle cap

**October 10, 2026. Written proof, independently audited within this research session.** This is a globally quantified, nonsharp exclusion within the [active spatial one-cap problem](gate1-spatial-dual-height-width-compactness.md). It uses three actual hallway angles and ordinary areas. Maximality, endpoint stationarity, curvature bounds, reflection symmetry and niche connectivity are not hypotheses.

**Theorem SW1.** Let U be a compact downward convex cap of height one with
\[
I=[-a,a],\quad 0<a\le1,\quad J=[-a/2,a/2],\quad A_U|_J=1.
\]
For its entire continuous-angle positive niche n,
\[
\boxed{\mathcal P(U)=\int_{I\setminus J}A_U-\int_J n
\le\frac{41}{50}<\frac M2.}
\tag{SW.1}
\]
In particular a horizontal canonical global maximizer cannot have width
at most two. This theorem does not bound the remaining wide or tilted caps.

## 1. Exact 45-degree relaxation and quantitative restrictions

Write
\[
k=\sqrt2-1,\quad
u=\sqrt2h_U(\pi/4)-1,\quad v=\sqrt2h_U(3\pi/4)-1,
\quad m=(u+v)/2,\quad d=(u-v)/2.
\]
The top endpoints and the containing box imply \(a/2\le u,v\le a\).
The cap lies below
\[
A_0(x)=\min(1,1+u-x,1+v+x),\qquad
O_0:=\int_{I\setminus J}A_0
=a-\frac{(a-u)^2+(a-v)^2}{2}.
\]
Put \(D=\int_{I\setminus J}(A_0-A_U)\ge0\).
The actual angle \(\pi/4\) supplies the tent
\[
n_{45}(x)=[\min(u-k-x,v-k+x)]_+.
\]
Its apex d lies in J. For \(a>k\), exact triangle integration gives
\[
N_{45}:=\int_Jn_{45}
=(m-k)_+^2-\frac{(u-k-a/2)_+^2+(v-k-a/2)_+^2}{2}.
\]
Consequently \(\mathcal P\le F-D\), where
\[
F=a-\frac{(a-u)^2+(a-v)^2}{2}-(m-k)_+^2
+\frac{(u-k-a/2)_+^2+(v-k-a/2)_+^2}{2}.
\tag{SW.2}
\]
This F is concave in \((u,v)\) on \([a/2,a]^2\). Where \(m>k\),
its piecewise Hessian is
\[
\begin{pmatrix}
-3/2+\mathbf1_{u-k-a/2>0}&-1/2\\
-1/2&-3/2+\mathbf1_{v-k-a/2>0}
\end{pmatrix},
\]
negative semidefinite in all four cases. Where \(m\le k\), both
clipping terms vanish and the Hessian is \(-\mathrm{Id}\). First
derivatives agree across all boundaries. The symmetric interior critical
point \(u=v=(a+k)/2\) therefore proves
\[
F\le B(a):=a-(a-k)^2/2\le B(1)=2k.
\tag{SW.3}
\]

Suppose for contradiction that \(\mathcal P>41/50\). The trivial
bound \(\mathcal P\le a\) gives \(a>41/50>k\). We claim
\[
a>9/10,\quad m>16/25,\quad
u-a/2<8/25,\quad v-a/2<8/25,
\quad D<2k-41/50<3/350.
\tag{SW.4}
\]
Here are the full checks.

- B increases on \((k,1]\), and \(k<1/2\) gives
  \(B(9/10)<9/10-(2/5)^2/2=41/50\).
- Concavity and exchange symmetry give \(F(a,u,v)\le F(a,m,m)\).
  If \(m\le16/25\) and \(a>9/10\), the clipping terms vanish.
  For \(m\le1/2\),
  \(a-(a-m)^2=m+1/4-(a-m-1/2)^2\le3/4\).
  For \(1/2<m\le16/25\), the symmetric expression increases with
  \(a\le1\), then with \(m\le16/25\). Its upper value is
  \((2050k-337)/625<41/50\).
- On the constrained half-square \(v-a/2\ge t_0:=8/25\), the
  concave maximum is at
  \(v=a/2+t_0\), \(u=a/2+(2k-t_0)/3\).
  Both clipping terms vanish there, the u derivative is zero, and
  the v derivative is \((2k-4t_0)/3<0\). These are the sufficient
  concave optimality conditions on the whole constrained square.
  The resulting value is
  \[
  B(a)-\frac23(t_0-k/2)^2
  \le\frac{9550k-881}{3750}<\frac{41}{50}.
  \]
  The last comparison follows from \(\sqrt2<577/408\), whose
  squared difference is \(577^2-2\cdot408^2=1\).
  Exchanging u and v proves the other restriction.
- Finally \(\sqrt2<99/70\) gives \(2k-41/50<3/350\).

Since \(8/25<k\), the entire positive 45-degree tent is now inside J.

## 2. Exterior area pays for two support deficits

Set
\[
\theta=\pi/8,\quad c=\cos\theta,\quad s=\sin\theta,\quad
\beta=c-s,\quad K=1/k=1+\sqrt2,
\quad C_0=\frac1{2k(1-k)}=Kc^2=\frac{4+3\sqrt2}{4}.
\]
The support of \(A_0\) at normal \((-s,c)\) is \(c+sv\), at
\((-v,1)\). Define the actual deficits
\[
\delta_L=c+sv-h_U(5\pi/8)\ge0,\qquad
\delta_R=c+su-h_U(3\pi/8)\ge0.
\]
Since \((-a/2,1)\in U\),
\[
\delta_L\le s(v-a/2).
\tag{SW.5}
\]
Cutting \(A_0\) by its actual support line lowered by \(\delta_L\)
removes a triangle at \((-v,1)\). Its horizontal side lengths are
\(\delta_L/s\) toward the top and \(\delta_L/(c-s)\) toward the
45-degree outer facet. If the latter is at most \(a-v\), SW.5 puts
the entire triangle in the charged left wing. Its exact area is
\[
\frac{\delta_L^2}{2s(c-s)}=K\delta_L^2.
\]
This containment must hold. Otherwise set
\(\delta_0=(c-s)(a-v)<\delta_L\). SW.5 still puts the corresponding
smaller triangle entirely in the wing, forcing
\[
D\ge K\delta_0^2=\frac{(a-v)^2}{\sqrt2}
>\frac{(13/100)^2}{\sqrt2}>\frac3{350},
\]
because \(a-v>9/20-8/25=13/100\). This contradicts SW.4.
The reflected triangle lies in the other wing, so no material is counted
twice and
\[
\boxed{D\ge K(\delta_L^2+\delta_R^2).}
\tag{SW.6}
\]

## 3. Two disjoint genuine additional niche tails

Put \(\eta=2/25\) and
\[
E_L=(\eta-\delta_L/c)_+,\qquad E_R=(\eta-\delta_R/c)_+.
\]
The second wall at \(\pi/8\) has height
\(S_\theta(x)=(h_U(5\pi/8)-1)/c+kx\).
At the left zero \(x_0=k-v\) of the 45-degree tent, it equals
\[
S_\theta(x_0)=1-1/c+k^2-\delta_L/c.
\]
Suppose \(E_L>0\). The exact inequality
\[
1-1/c+k^2>\eta
\tag{SW.7}
\]
shows that this wall dominates \(S'(x)=E_L+k(x-x_0)\).
The companion first wall is also sufficient, as follows.

An attaining point for \(h_U(\pi/4)\) has \(x+y=1+u\) and
\(y\le1\), hence \(x\ge u\). Therefore
\[
h_U(\pi/8)\ge s+cu.
\tag{SW.8}
\]
At \(x_R=x_0+E_L/(1-k)\), the first-wall lower bound from SW.8
is at least \(S'\) exactly when
\[
2m\ge1/c+(1+\sqrt2)E_L.
\]
This follows from \(m>16/25\), \(E_L\le\eta\), and
\[
1/c+(1+\sqrt2)\eta<32/25.
\tag{SW.9}
\]
The difference of the two lines increases as x decreases. Hence the
whole tail interval ending at \(x_R\) really is under both attached
walls, and the full niche dominates \(S'_+\) there.

Furthermore
\[
x_R-d=k-m+\frac{E_L}{1-k}
<k-\frac{16}{25}+\frac\eta{1-k}<0.
\]
The last comparison follows from
\(k+\eta/(1-k)=(26k+3)/25<16/25\).
Thus the extra niche area above \(n_{45}\), on the left side of
its apex, contains a triangle of peak height \(E_L\), left slope k,
and right downward slope \(1-k\). Its area is \(C_0E_L^2\).

The peak is inside J because \(x_0+a/2>k-8/25>0\).
Only the outer tip can be clipped by J. The omitted horizontal length
is at most
\[
L_0=8/25-k+\eta/k=(12-23k)/25>0,
\]
so the omitted area is at most \(kL_0^2/2\).
If \(E_L=0\), the lower bound
\(C_0E_L^2-kL_0^2/2\) is already true by nonnegativity; no wall
comparison is asserted in that case.

Horizontal reflection supplies the corresponding right tail at
\(3\pi/8\). It lies strictly to the right of d, so the two added
regions are disjoint. Consequently
\[
\boxed{\int_Jn\ge N_{45}
+C_0(E_L^2+E_R^2)-kL_0^2.}
\tag{SW.10}
\]
This remains valid for arbitrary additional overlaps and disconnected
horizontal sections of the full niche.

For exact checks of SW.7 and SW.9 use \(c^2=(2+\sqrt2)/4\)
and square positive sides. SW.7 is equivalent to
\(\sqrt2<1777/1249\), which follows from \(\sqrt2<99/70\).
SW.9 is equivalent to \(\sqrt2>231/167\), implied by
\(\sqrt2>24/17\).

## 4. Combine the two ordinary-area payments

Since \(Kc^2=C_0\), every \(\delta\ge0\) satisfies
\[
K\delta^2+C_0(\eta-\delta/c)_+^2
=C_0\bigl[(\delta/c)^2+(\eta-\delta/c)_+^2\bigr]
\ge C_0\eta^2/2.
\]
Apply this separately to the two wings and their disjoint niche tails.
SW.3, SW.6 and SW.10 give
\[
\mathcal P\le F-C_0\eta^2+kL_0^2
\le2k-C_0\eta^2+kL_0^2
=\frac{5140k-1617}{625}
<\frac{3587}{4375}<\frac{41}{50}.
\]
The simplification uses \(k^2=1-2k\); the penultimate comparison uses
\(k<29/70\). The last rational gap is \(1/8750\).
This contradicts the supposition \(\mathcal P>41/50\) and proves SW1.

Finally the defining cubic is negative at \(297/1000\), so
\(Y>297/1000\). The inequality \(\arctan Y\ge Y-Y^3/3\)
and monotonicity on the relevant positive interval give
\[
\frac M2>
\frac{1+4(297/1000)^2+297/1000-(297/1000)^3/3}{2}
>\frac{41}{50}.
\]
Thus the exclusion is strictly below the exact reference value, without
using a rounded numerical approximation to M.

The proof was checked independently for the support constraints, all
window clipping, disjointness, concave optimization, and exact constants.
It is a written mathematical proof, not a Lean verification or a
finite-angle numerical certificate for the full sharp inequality.
