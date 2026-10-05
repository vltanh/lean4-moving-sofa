# 45. The exact diagonal equality shape fails an additional hallway position

The sharp three-position relaxation in Note 44 does not solve the moving problem. This note excludes its equality shape by one explicit support test. Combined with the attained maximum from Note 25, it gives a strict unrestricted inequality below 2sqrt(2)-1. The following note makes the strict gap quantitative without relying on attainment.

## 45.1 Centered coordinates for the equality body

Let T=sqrt(2), a=1/T, and d=1-a. Center the diagonal coordinates of (44.9) at (1,1), and denote them by (U,V). The equality body is

\[
F_0=\{(U,V):|U|\leq1,\ |V|\leq1,
\ |U+V|\leq a,\ UV\leq0\}.
\tag{45.1}
\]

Its convex hull is

\[
K_0=[-1,1]^2\cap\{|U+V|\leq a\}.
\tag{45.2}
\]

Indeed all six vertices of this hexagon belong to F_0, so their convex hull is retained. The physical horizontal coordinate is (U-V)/T, and the centered vertical coordinate is (U+V)/T. Thus the incoming strip is centered and has width one.

Put epsilon=arctan(1/7). The physical lower-turn angle

\[
t_+=\pi/4+\varepsilon=\arctan(4/3)
\]

has cosine 3/5 and sine 4/5. In the (U,V) basis its two inward testing normals are

\[
n=(7,1)/(5T),\qquad m=(-1,7)/(5T).
\tag{45.3}
\]

## 45.2 A retained point falls strictly inside the canonical forbidden quadrant

The vertex (1,-d) of K_0 maximizes n dot z, while (-d,1) maximizes m dot z. To check the first assertion, maximize 7U+V under U<=1 and U+V<=a: the objective is 6U+(U+V)<=6+a=7-d, with equality at that vertex. The second objective -U+7V is maximized at V=1 and U=-1 (not at the upper-strip endpoint). The following proof uses the retained point (-d,1) only as a **lower bound** on that support; it does not need to identify the maximizer of m.

Take P=(0,-a), which belongs to F_0. The two retained points A=(1,-d) and B=(-d,1) satisfy

\[
n\cdot(A-P)=\frac{6+T}{5T}>1,
\qquad
m\cdot(B-P)=\frac{8+3T}{5T}>1.
\tag{45.4}
\]

The first inequality is 6>4T, proved by squaring positive quantities. The second is 8>2T. Therefore

\[
h_{K_0}(n)-1>P\cdot n,
\qquad h_{K_0}(m)-1>P\cdot m.
\tag{45.5}
\]

These are the two strict inner inequalities for the canonical forbidden quadrant. Thus F_0 fails the supporting hallway at t_+.

For clarity, no asserted equality h_{K_0}(m)=m dot B is used: a single retained point B already supplies the sufficient lower bound. The proof is a three-point obstruction and is insensitive to a larger support in that direction.

## 45.3 Why a different translation or an early exit cannot avoid the test

For any fixed ordered pair of perpendicular unit normals n,m, a unit hallway containing a compact body must have outer bounds at least h_K(n),h_K(m). Its two inner thresholds are consequently at least h_K(n)-1,h_K(m)-1. If a point satisfies (45.5), it is forbidden for every such placement, not just for one chosen translation. This is also the contrapositive of Proposition 19.

A body of area 2T-1 cannot finish a reduced lower turn before t_+, because the two-strip bound would then give

\[
|S|\leq\sec(t_+)=5/3<2T-1.
\]

For the last strict comparison, T>4/3 suffices. The correct-sign reduction is available because the area exceeds T. Therefore any hypothetical equality sofa must actually traverse the tested angle.

If the diagonal axes were exchanged in the equality calculation, the unordered pair of testing normals corresponds instead to the lower-turn angle t_-=arctan(3/4). This is also visited, since 0<t_-<t_+. Alternatively F_0 itself is unchanged under exchange of U,V.

**Corollary 87 (strict unrestricted bound).** If V_* denotes the attained supremal area from Theorem 55, then

\[
M\leq V_*<2\sqrt2-1.
\tag{45.6}
\]

**Proof.** Theorem 85 gives the non-strict upper bound. Equality would identify the body as F_0 by Proposition 86 and regular-closed recovery. Equations (45.4)–(45.5) make the required additional pose impossible. Since the supremum is attained, it cannot equal the excluded value. Candidate feasibility gives the lower bound M. QED.

This is not optimality of the candidate. It closes the equality question for the diagonal relaxation and identifies an explicit missing-angle obstruction. No numerical search or compilation is involved.
