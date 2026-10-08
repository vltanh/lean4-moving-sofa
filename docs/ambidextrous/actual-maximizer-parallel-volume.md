# Parallel-volume tests for actual maximizing bodies

**Scope.** These necessary conditions apply directly to an attained maximizing ambidextrous body, including a body with partial turns. They do not assume it is a weighted-cap maximizer, has a regular hull, or admits a tail background. They do not prove the optimal value. Labels PV are local. Baseline: `9307910d73167a19f92c1785433aa27febacd375`.

The only motion input is canonical support tightening from Note 8. The rounding estimate generalizes RR1 from a radius-one-half disk to any convex body of diameter at most one. No computation is a premise.

## 1. A family of feasible perturbations of the actual set

Let S be nonempty, compact and connected, with two canonical turning witnesses and their actual endpoint strips. Let C be any nonempty compact convex set with diameter at most one, and let t>=0. Define

$$S_{t,C}=\frac{S+tC}{1+t}.$$

For a unit normal n and p=(s+tc)/(1+t),

$$h_{S_{t,C}}(n)-p\cdot n
=\frac{h_S(n)-s\cdot n+t(h_C(n)-c\cdot n)}{1+t}.$$

At every already feasible hallway, at least one of its two inner-wall depths for s is at most one. The corresponding depth of c in C is at most its directional width, hence at most one. The same wall therefore protects p. Outer supporting bounds are automatic. Every endpoint strip width of S at most one stays at most one under this convex combination of widths.

**Lemma PV1.** S_(t,C) is compact, connected and feasible for the same two angular intervals, with the same initial and terminal strip directions. This includes partial as well as full turns.

Connectedness follows from the continuous image of S times C under addition. Continuous support functions give continuous canonical motions. No feasibility of conv(S), reflection averaging, or clipping of S is assumed.

## 2. A finite inequality at an attained maximum

Let S attain the unrestricted ambidextrous maximum and put A=|S|. By PV1,

$$\boxed{|S+tC|\le(1+t)^2A\quad(t\ge0,\ \operatorname{diam}C\le1).}\tag{PV.1}$$

The same conclusion holds for an attained maximum restricted to the class of bodies with both full turns, because PV1 preserves that class too. It does not assert attainment of the positive-opposite-face subclass.

For C equal to the disk of radius one half, put t=2r. With D the unit disk,

$$\boxed{|S+rD|\le(1+2r)^2A\quad(r\ge0).}\tag{PV.2}$$

In particular its outer Minkowski content is finite:

$$\limsup_{r\downarrow0}\frac{|S+rD|-|S|}{r}\le4A.\tag{PV.3}$$

If a proposed actual body violates PV.1 for a single C,t, the displayed perturbation is a genuine better ambidextrous body. This is a finite comparison, not an optimizer or stationarity assertion about an auxiliary support profile.

## 3. Finite perimeter without a boundary smoothness premise

Define the distributional perimeter by

$$P(S)=\sup\left\{\int_S\operatorname{div}X:
X\in C_c^1(\mathbb R^2;\mathbb R^2),\ |X|\le1\right\}.$$

For such an X and sufficiently small positive r, the map T_r(x)=x+rX(x) is an orientation-preserving C1 diffeomorphism: its derivative is uniformly close to the identity, and the map is the identity outside a compact set. Also T_r(S) subset S+rD. The change of variables formula, valid for measurable S, gives in the plane

$$|T_r(S)|=A+r\int_S\operatorname{div}X+r^2\int_S\det(DX).$$

Combine this with PV.2, divide by r, and let r decrease to zero. This yields integral_S div X<=4A. Taking the supremum proves:

**Theorem PV2.** Every attained maximizing body in either class above is a set of finite perimeter and satisfies

$$\boxed{P(S)\le4|S|.}\tag{PV.4}$$

This proof does not identify the reduced boundary with every topological boundary point. In particular PV.4 alone does not control curvature of conv(S), produce smooth support functions, or validate a niche-exposure formula. It is regularity of the actual measurable body, at the level explicitly defined above.

## 4. A stronger directional family when a classical boundary exists

For a piecewise C2 body with finitely many boundary arcs and corners, the first variation of outer Minkowski addition by a convex C is

$$\left.\frac{d}{dt}|S+tC|\right|_{0+}
=P_C(S):=\int_{\partial S}h_C(n)\,ds.$$

One may establish this by adding normal strips along the smooth arcs and estimating the finitely many corner regions by O(t^2). Translation of C does not change the integral, since the integral of the boundary normal is zero. The formula is not being asserted without qualifications for arbitrary rough representatives of finite-perimeter sets.

PV.1 implies the necessary inequalities

$$\boxed{P_C(S)\le2|S|\quad(\operatorname{diam}C\le1)}\tag{PV.5}$$

whenever the displayed classical variation formula applies. Disk rounding is just one member of this family. Conversely a strict violation gives an improving perturbation for small t. There is no claim that satisfying all these inequalities is sufficient for maximality.

## 5. Boundary of this direction

PV acts on actual bodies and preserves all existing partial-turn endpoint constraints. It neither creates missing hallway angles nor constructs a curvature-controlled background. The companion reference test shows that even this entire convex-template family can have strict first-order slack at the reference, so it cannot be presumed to identify the optimum or eliminate nearby cut families automatically.

The finite comparisons and finite-perimeter implication are hand proofs. No CI, Lean/Lake compilation, long script, dependency installation or manuscript build was used. The unrestricted value remains unproved; all new statements are self-reviewed rather than independently verified.
