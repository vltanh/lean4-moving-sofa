# Gate 2: a three-angle width cut without endpoint niche boxes

Written mathematical proof, October 10, 2026. This note transfers the
three full-triangle comparison [FT](gate1-tilted-full-triangle-width-cut.md)
to the actual partial score at every remaining terminal angle. It replaces
FT's two-sided endpoint niche box estimate by the partial endpoint
identities and a joint bound on the two positive-floor losses. The three
geometric niche payments remain the actual tents at
\(\pi/8,\pi/4,3\pi/8\).

The inputs are the [partial endpoint and source theorem
PS](gate2-partial-endpoint-source-and-green.md), the [all-width terminal
angle exclusion AT](gate2-all-width-terminal-angle-exclusion.md), and the
three-angle transfers in [TP, Section 1](gate2-terminal-facet-and-prefix-reduction.md).
No upper bound on either endpoint value of the partial barrier is used.
There is no reflection of the outgoing constraint in the variational
problem.

## 1. Statement and the finite-angle comparison

Suppose an above-reference joint partial-cap maximum exists, and choose
the largest-angle canonical representative used in PS and TP. Write
\(C=W/4\). AT and TP supply

\[
\alpha>\arctan(8/3)>3\pi/8,\qquad
\frac{1001}{2000}<C<\frac45,\qquad 0\le h<\frac{17}{50},
\tag{WC.1}
\]

where \(h\) is the absolute height difference between the middle
endpoints. The conclusion is

\[
\boxed{C<\frac{37}{50}.}
\tag{WC.2}
\]

More precisely, the following comparison excludes the complementary
width range. Put

\[
I=[-a,a],\qquad J=[-a/2,a/2],\qquad a=2C.
\]

For this finite-angle comparison only, label the high middle endpoint
as the right one and write

\[
A(-a/2)=1-h,\qquad A(a/2)=1,\qquad
\frac{37}{25}\le a\le\frac85,\quad 0\le h\le\frac{17}{50}.
\tag{WC.3}
\]

If this requires reflecting the cap, reflect its actual barrier \(N\)
at the same time. The maximum of the three displayed tents is unchanged
by this reflection: it exchanges the tents at \(\pi/8\) and
\(3\pi/8\), and preserves the one at \(\pi/4\). Thus the reflected
\(N\) still dominates those three actual tents, whether or not it is
itself a partial objective with a first outgoing wall.

Let

\[
q_\pm=N(\pm a/2),\qquad e_R=A(a),\qquad e_L=A(-a).
\]

PS's endpoint identities, with the same relabeling, are

\[
e_R=\frac12+\frac h4+\frac{3q_+-q_-}{4},\qquad
e_L=\frac12-\frac{3h}{4}+\frac{3q_--q_+}{4}.
\tag{WC.4}
\]

We prove that every cap and nonnegative barrier satisfying these
geometric hypotheses, WC.4, and domination of the three tents obeys

\[
\boxed{\int_{I\setminus J}A-\int_JN
<\frac{25811237}{31500000}<\frac{41}{50}<\frac M2.}
\tag{WC.5}
\]

This statement supplies WC.2 for all three signs of the original middle
tilt. It requires neither unit source curvature nor any estimate on the
terminal facet mass.

## 2. Replace FT's endpoint bounds

Use FT's constants and lifted support notation:

\[
r=\sqrt2,\quad k=r-1,\quad
c_8=\cos(\pi/8),\quad s_8=\sin(\pi/8),
\]
\[
\gamma=1-r/2,\qquad t=2c_8-r,\qquad
\mathsf A=1-k,\quad \mathsf b=2-k,\quad \mathsf d=3r-1.
\tag{WC.6}
\]

Raise the low charged wing by \(h\), put the middle roof at height one,
and keep the high charged wing. This is FT's genuine lifted cap
\(\widehat U\). Put

\[
u=rh_{\widehat U}(\pi/4)-1,\qquad
v=rh_{\widehat U}(3\pi/4)-1,\qquad
M_0=(u+v)/2,
\]
\[
w_R=a-u,\qquad w_L=a-v+h.
\tag{WC.7}
\]

Here the arguments of \(h_{\widehat U}\) denote the angles of its
outward normals. In the original cap the two 45-degree support
parameters are \(u\) and \(v-h\), so its actual 45-degree tent is

\[
\bigl[\min\{u-k-x,\ v-h-k+x\}\bigr]_+.
\]

Concavity and the height bound give \(e_R\le1\) and
\(e_L\le1-3h/2\). Solving WC.4 for the opposite endpoint and using
\(q_\pm\ge0\) gives

\[
e_R\ge\frac13+\frac h2+\frac23q_+\ge\frac13+\frac h2,
\qquad
e_L\ge\frac13-\frac{2h}{3}+\frac23q_-\ge\frac13-\frac{2h}{3}.
\tag{WC.8}
\]

The actual endpoint support inequalities are
\(e_R\le1-w_R\), \(e_L\le1-w_L\). Also, adding WC.4 gives

\[
e_R+e_L=1-\frac h2+\frac{q_-+q_+}{2}\ge1-\frac h2.
\]

Consequently the support deficits satisfy

\[
\boxed{
\begin{aligned}
0&\le w_R\le \frac23-\frac h2,\\
0&\le w_L\le \frac23+\frac{2h}{3},\\
w_R+w_L&\le1+\frac h2.
\end{aligned}}
\tag{WC.9}
\]

Nonnegativity also follows directly from the lifted support bounds and
the affine extension of the original middle roof. These inequalities
replace FT.8–FT.9. In particular their sum retains the bound
\(M_0-h/2\ge a-1/2-h/4\) used in FT.11 and FT.15. No endpoint
niche box has entered the argument.

## 3. Bound the two floor losses together

FT.10's disjoint exterior triangles, FT.11–FT.12's fitting of the
two full additional niche triangles, and FT.13's exact positive-floor
correction use actual supports and the three genuine tents. They
therefore hold with \(N\) in place of the full-turn niche. In
particular, their floor correction is at most

\[
\gamma\bigl[(w_R-t)_+^2+(w_L-t)_+^2\bigr].
\tag{WC.10}
\]

We now maximize this expression on the entire enlarged polygon WC.9.
Set

\[
R_h=\frac23-\frac h2,\qquad
L_h=\frac23+\frac{2h}{3},\qquad S_h=1+\frac h2.
\]

The cost is nondecreasing in each coordinate. Since
\(R_h+L_h-S_h=(1-h)/3>0\), every feasible point can be increased
coordinatewise to the segment \(w_R+w_L=S_h\). The restriction of
the cost to this segment is convex, so its maximum is at one of

\[
(R_h,S_h-R_h)=\left(\frac23-\frac h2,\frac13+h\right),
\qquad
(S_h-L_h,L_h)=\left(\frac13-\frac h6,\frac23+\frac{2h}{3}\right).
\tag{WC.11}
\]

The second pair has the same sum and is at least as spread as the
first: its smaller entry \(1/3-h/6\) is no larger than either
entry of the first, and its larger entry is no smaller than either.
For the convex function \(\phi(w)=(w-t)_+^2\), this implies that
the second pair has at least as large a total cost. Explicitly, each
entry of the first pair is a convex combination of the two entries
of the second, with complementary coefficients; convexity and addition
give the comparison.

The elementary bounds \(1/3<t<2/3\) hold, and hence the smaller
entry of the second pair has zero cost. We obtain the exact uniform
replacement for FT.14:

\[
\boxed{
\gamma\bigl[(w_R-t)_+^2+(w_L-t)_+^2\bigr]
\le \gamma\left(D+\frac{2h}{3}\right)^2,
\qquad D:=\frac23-t>0.}
\tag{WC.12}
\]

This is a joint estimate; bounding the two deficits separately would
discard the sum constraint in WC.9.

## 4. The same support concavity completes the comparison

Retain the genuine exterior and niche payments in FT.15–FT.17, changing
only the floor correction to WC.12. The undepleted peak sum uses
\(e_R+e_L\ge1-h/2\), which was proved above. Thus FT's function
\(G_h(a,u,v)\), with all 45-degree floor and window clipping retained,
satisfies

\[
\int_{I\setminus J}A-\int_JN
\le G_h(a,u,v)+\gamma\left(D+\frac{2h}{3}\right)^2.
\tag{WC.13}
\]

FT.18–FT.24 prove joint concavity of \(G_h\) in the geometric support
variables and verify its unclipped support critical point at
\(a_0=37/25\). Those calculations use no endpoint niche estimate.
Consequently, for every \(a\ge a_0\) in WC.3,

\[
G_h(a,u,v)\le K_0(h),
\]
\[
K_0(h)=B(a_0)-\frac{kh}{2}-\frac{h^2}{8}
-\frac29\left(\sigma_0-\frac{\mathsf A h}{4}\right)^2,
\tag{WC.14}
\]

where

\[
B(a)=a-\frac{(a-k)^2}{2},\qquad
\sigma_0=\frac{\mathsf d a_0}{2}-(4c_8-2),\qquad
\frac{703}{1000}<\sigma_0<\frac{71}{100}.
\tag{WC.15}
\]

This retains all of FT's genuine tents; the larger partial barrier
only strengthens the required niche lower bound.

## 5. An exact decreasing scalar bound

Let

\[
F(h)=K_0(h)+\gamma\left(D+\frac{2h}{3}\right)^2.
\]

Differentiation gives the affine expression

\[
\begin{aligned}
F'(h)={}&-\frac k2+\frac{\mathsf A\sigma_0}{9}
+\frac{4\gamma D}{3}\\
&+h\left(-\frac14-\frac{\mathsf A^2}{36}
+\frac{8\gamma}{9}\right).
\end{aligned}
\tag{WC.16}
\]

Use

\[
k>\frac25,\quad \mathsf A<\frac35,\quad
\gamma<\frac3{10},\quad \sigma_0<\frac{71}{100},
\]
\[
D=\frac23-2c_8+r
<\frac23-\frac{1846}{1000}+\frac{99}{70}
<\frac{47}{200}.
\tag{WC.17}
\]

The radical bounds here are the same
\(c_8>923/1000\), \(r<99/70\) already checked in FT.20.
The constant and linear coefficients in WC.16 respectively obey

\[
-\frac k2+\frac{\mathsf A\sigma_0}{9}
+\frac{4\gamma D}{3}
<-\frac15+\frac{71}{1500}+\frac{47}{500}
=-\frac{22}{375},
\]
\[
-\frac14-\frac{\mathsf A^2}{36}+\frac{8\gamma}{9}
<\frac1{60}.
\]

It follows, on the whole tilt interval in WC.3, that

\[
F'(h)<-\frac{22}{375}+\frac{17}{3000}
=-\frac{53}{1000}<0.
\tag{WC.18}
\]

Thus the complete upper bound is maximal at \(h=0\). Moreover,

\[
\gamma D^2<\frac3{10}\left(\frac{47}{200}\right)^2
=\frac{6627}{400000}<\frac{17}{1000}.
\]

Since \(B(a_0)=(62/25)k-72/625\), the same rational endpoint
certificate as FT.26 applies:

\[
\begin{aligned}
\int_{I\setminus J}A-\int_JN
&<\frac{62}{25}\frac{29}{70}-\frac{72}{625}
-\frac29\left(\frac{703}{1000}\right)^2
+\frac{17}{1000}\\
&=\frac{25811237}{31500000}
<\frac{41}{50}.
\end{aligned}
\tag{WC.19}
\]

The final strict rational gap is \(18763/31500000\). This proves
WC.5 and excludes WC.3. Combining with WC.1 gives WC.2 for every
remaining sign of the middle roof and every remaining terminal angle.
In particular, the width conclusion requires no small-terminal-deficit
hypothesis. The sharp partial-cap comparison remains a separate
obligation on the smaller width interval.
