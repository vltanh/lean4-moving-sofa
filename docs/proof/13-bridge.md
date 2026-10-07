# 13. The bridge to formal-conjectures

[Contents](README.md) · [← 12. Uniqueness II: every maximum is Gerver's sofa](12-uniqueness.md) · [Appendix A. Gerver's four constants →](appendix-a.md)

Google DeepMind's formal-conjectures states the moving sofa problem in Lean with definitions of its
own (§13.1). Its plane is the Euclidean plane `EuclideanSpace ℝ (Fin 2)` rather than
$\mathbb{R} \times \mathbb{R}$. A moving sofa comes with its motion, a continuous path from the
identity in the group $\mathrm{E}(2)$ of affine isometries. The optimal area is a supremum, the
*sofa constant*. Gerver's sofa is built from Gerver's four constants $A, B, \varphi, \theta$
through a rotation path given by integrals, and each hallway is translated and then rotated. This
chapter proves that, read in coordinates, these definitions describe the same objects as Baek's:
the same moving sofas (Theorem 13.9), the same optimal area (Theorem 13.10) and the same Gerver's
sofa (Theorem 13.19). These are the three theorems of the namespace `Bridge` of the Challenge. With
Baek's theorem and the uniqueness theorem they give formal-conjectures' four statements (Theorem
13.20), among them the uniqueness of the optimal sofa, which formal-conjectures lists as open. The
bridge itself uses no result about optimal sofas.

The motions are matched by topology (§13.2 and §13.3). Along a continuous path in $\mathrm{E}(2)$
from the identity, the determinant of the linear part cannot jump from $1$ to $-1$, so every element
of the path is a rotation followed by a translation. The angle of the rotation lifts to a continuous
real function through the covering of the circle by the real line. Baek's motions start at a
translation, which a straight slide inside the horizontal side absorbs. Gerver's sofa takes more
work (§13.4 and §13.5). formal-conjectures defines Gerver's constants as the unique solution of four
equations, so the bridge proves that this system has exactly one solution: one because Romik's
system has one, and at most one by the elementary inequalities of [Appendix A](appendix-a.md).
Romik's 22 parameters are explicit functions of the four constants. The radius $r(\alpha)$ of
formal-conjectures is the speed of Romik's contact point $\mathbf{C}$, its integrals are the
coordinates of the contact points $\mathbf{A}$ and $\mathbf{C}$, and its rotation path $p$ is
Romik's path $\mathbf{x}$ seen in the rotating frame of the hallway. §13.6 derives
formal-conjectures' theorems, and §13.7 explains how the Challenge and the Solution are arranged so
that Comparator can check them.

## 13.1 The two sets of definitions

The statements of record are in the Challenges of the two Palomar entries,
[`Challenge.lean`](../../Challenge.lean) and [`baek/Challenge.lean`](../../baek/Challenge.lean). Both restate
formal-conjectures' definitions verbatim from its file `FormalConjectures/Wikipedia/MovingSofa.lean`
(Git blob `59b6ed7eb42e11b208b09539c245da4d3f11ed00`), inside the namespace
`FormalConjectures.MovingSofa` instead of `MovingSofa`. The only other change is an explicit name
for the topology instance on $\mathrm{E}(2)$, which formal-conjectures leaves anonymous: the name
that Lean generates for an anonymous instance depends on the library that declares it. The
[Definitions](../definitions.md) page shows the Lean code; this section states the definitions in
the notation of this text.

Write $\mathbb{E}^2$ for `EuclideanSpace ℝ (Fin 2)`, with points $q = (q_0, q_1)$, and
$\mathrm{E}(2)$ for the group of its affine isometries, written `E(2)` there. The *coordinate map*
is

```math
\chi : \mathbb{E}^2 \to \mathbb{R}^2, \qquad \chi(q) = (q_0, q_1).
```

formal-conjectures' horizontal side, vertical side and hallway are
$\chi^{-1}(H_L) = \lbrace q : q_0 \le 1,\ 0 \le q_1 \le 1 \rbrace$, $\chi^{-1}(V_L)$ and
$\chi^{-1}(L)$: the points whose coordinates lie in Baek's $H_L$, $V_L$ and $L$. Table 13.1 lists
the two sets of definitions side by side. In this chapter $\vartheta$ is the angle of a motion,
written $\theta$ on the front page, and $\theta$ is one of Gerver's angles.

| | Baek's paper (`Baek`) | formal-conjectures (`FormalConjectures.MovingSofa`) |
| --- | --- | --- |
| The plane | $\mathbb{R}^2 = \mathbb{R} \times \mathbb{R}$ | $\mathbb{E}^2$, `EuclideanSpace ℝ (Fin 2)` |
| The hallway | $L = H_L \cup V_L$ | $\chi^{-1}(L) = \chi^{-1}(H_L) \cup \chi^{-1}(V_L)$ |
| A motion | $\Phi_s(q) = R_{\vartheta(s)} q + c(s)$ with $\vartheta$, $c$ continuous on $[0, 1]$ and $\vartheta(0) = 0$ | a continuous $m : [0, 1] \to \mathrm{E}(2)$ with $m(0) = \mathrm{id}$ |
| A moving sofa $S$ | closed, connected, $\Phi_0(S) \subseteq H_L$, every $\Phi_s(S) \subseteq L$, $\Phi_1(S) \subseteq V_L$ | closed, connected, $S \subseteq \chi^{-1}(H_L)$, every $m(t)(S) \subseteq \chi^{-1}(L)$, $m(1)(S) \subseteq \chi^{-1}(V_L)$ |
| The optimal area | $\alpha_{\max} = \sup \lvert S \rvert$, which is $\lvert G \rvert$ by Theorem 1.2 | the sofa constant $\alpha_{\mathrm{fc}} = \sup \lvert S \rvert$ |
| Gerver's constants | Romik's 22 parameters, a solution of Romik's equations (27)–(44) in the box $\varphi \in [0.039, 0.04]$, $\theta \in [0.68, 0.69]$ | Gerver's four constants $A, B, \varphi, \theta$, the unique solution of Romik's equations (1)–(4) with $0 \le \varphi \le \theta \le \pi/4$, $A, B \ge 0$ |
| The rotation path | $\mathbf{x}$, glued from five explicit phases | $p$, given by integrals of a piecewise radius $r$ |
| The hallway at the angle $t$ | rotated by $t$, then translated by $\mathbf{x}(t)$: $\mathbf{x}(t) + R_t L$ | translated by $p(t)$, then rotated by $t$: $R_t (L + p(t))$ |
| Gerver's sofa | $G = \operatorname{shape}(\mathbf{x})$ | $G_{\mathrm{fc}}$, the sofa of the path $p$ |

*Table 13.1.* The definitions of Baek's paper, as in the [front page](README.md#11-the-problem) and
[Chapter 10](10-gerver.md), and those of formal-conjectures (Definitions 13.1 to 13.4).

### Definition 13.1 (moving sofas of formal-conjectures)

Give $\mathrm{E}(2)$ the topology induced by its inclusion in the continuous affine maps of
$\mathbb{E}^2$: a map into $\mathrm{E}(2)$ is continuous when its value at the origin and its linear
part are continuous. A set $S \subseteq \mathbb{E}^2$ is a *moving sofa of formal-conjectures*, with
*motion* $m : [0, 1] \to \mathrm{E}(2)$, if

1. $S$ is connected (hence nonempty) and closed;
2. $m$ is continuous and $m(0)$ is the identity;
3. $S \subseteq \chi^{-1}(H_L)$, $m(t)(S) \subseteq \chi^{-1}(L)$ for every $t \in [0, 1]$, and
   $m(1)(S) \subseteq \chi^{-1}(V_L)$.

*Lean: [`FormalConjectures.MovingSofa.IsMovingSofa`](../../Challenge.lean#L337),
[`FormalConjectures.MovingSofa.horizontalHallway`](../../Challenge.lean#L320),
[`FormalConjectures.MovingSofa.verticalHallway`](../../Challenge.lean#L323),
[`FormalConjectures.MovingSofa.hallway`](../../Challenge.lean#L326),
[`FormalConjectures.MovingSofa.instTopologicalSpaceAffineIsometryEquivRealEuclideanSpaceFinOfNatNat`](../../Challenge.lean#L331).*

Baek's moving sofas ([§1.1](README.md#11-the-problem), [Chapter 2](02-preliminaries.md);
[`Baek.IsMovingSofa`](../../Challenge.lean#L171), in the library
[`MovingSofaOptimality.IsMovingSofa`](../../MovingSofaOptimality/Sofa/Defs.lean#L59)) differ in two
ways. Their motion is given by a rotation angle $\vartheta$ and a translation $c$, continuous on
$[0, 1]$ with $\vartheta(0) = 0$, while formal-conjectures' motion is any continuous path in
$\mathrm{E}(2)$, a group that also contains reflections. And Baek's motion starts at a translation
$\Phi_0$, so only $\Phi_0(S)$ must lie in $H_L$, while formal-conjectures' motion starts at the
identity, so the sofa itself lies in the horizontal side. In both definitions the motion moves the
sofa and the hallway stays fixed.

### Definition 13.2 (the sofa constant)

The *sofa constant* of formal-conjectures is

```math
\alpha_{\mathrm{fc}} = \sup \bigl\lbrace \lvert S \rvert : S \subseteq \mathbb{E}^2 \text{ is a moving sofa of formal-conjectures} \bigr\rbrace \in [0, \infty],
```

where $\lvert S \rvert$ is the Lebesgue outer measure of $\mathbb{E}^2$ (`volume`).

*Lean: [`FormalConjectures.MovingSofa.sofaConstant`](../../Challenge.lean#L419).*

Baek's optimal area $\alpha_{\max}$ is the supremum of $\lvert S \rvert$ over Baek's moving sofas
$S \subseteq \mathbb{R}^2$; Theorem 13.10 also takes it in $[0, \infty]$.

### Definition 13.3 (Gerver's system and Gerver's four constants)

For real numbers $A$, $B$, $\varphi$, $\theta$ let

```math
\begin{aligned}
E_1 &= A(\cos\theta - \cos\varphi) - 2B\sin\varphi + (\theta - \varphi - 1)\cos\theta - \sin\theta + \cos\varphi + \sin\varphi, \\
E_2 &= A(3\sin\theta + \sin\varphi) - 2B\cos\varphi + 3(\theta - \varphi - 1)\sin\theta + 3\cos\theta - \sin\varphi + \cos\varphi, \\
E_3 &= A\cos\varphi - \bigl(\sin\varphi + \tfrac12 - \tfrac12\cos\varphi + B\sin\varphi\bigr), \\
E_4 &= \bigl(A + \tfrac\pi2 - \varphi - \theta\bigr) - \bigl(B - \tfrac12(\theta - \varphi)(1 + A) - \tfrac14(\theta - \varphi)^2\bigr).
\end{aligned}
```

A quadruple $(A, B, \varphi, \theta)$ *solves Gerver's system* if
$0 \le \varphi \le \theta \le \pi/4$, $A \ge 0$, $B \ge 0$ and $E_1 = E_2 = E_3 = E_4 = 0$. These
are Romik's Equations (1)–(4). formal-conjectures states that the system has exactly one solution
(Theorem 13.13) and defines *Gerver's four constants* $A$, $B$, $\varphi$, $\theta$ as that
solution, the witness of the statement taken with `Exists.choose`. Numerically (Newton's method in
30-digit arithmetic),

```math
A = 0.0944265608\ldots, \qquad B = 1.3992037273\ldots, \qquad \varphi = 0.0391773647\ldots, \qquad \theta = 0.6813015093\ldots .
```

*Lean: [`FormalConjectures.MovingSofa.GerversSofa.ABφθSpec`](../../Challenge.lean#L362),
[`FormalConjectures.MovingSofa.GerversSofa.A`](../../Challenge.lean#L378),
[`FormalConjectures.MovingSofa.GerversSofa.B`](../../Challenge.lean#L379),
[`FormalConjectures.MovingSofa.GerversSofa.φ`](../../Challenge.lean#L380),
[`FormalConjectures.MovingSofa.GerversSofa.θ`](../../Challenge.lean#L381),
[`MovingSofaBridge.GerverConstants.Spec`](../../MovingSofaBridge/GerverConstants.lean#L117).*

The angles $\varphi$ and $\theta$ are those of Romik's description used by Baek
([Chapter 10](10-gerver.md)). §13.4 derives each equation from Romik's system: $E_3$ and $E_4$ from
the smoothness of the rotation path at $\varphi$ and at $\theta$, and $E_1$, $E_2$ from its first
contact condition.

### Definition 13.4 (formal-conjectures' Gerver's sofa)

With Gerver's four constants, let the *radius* be

```math
r(\alpha) = \begin{cases} \tfrac12, & \alpha \le \varphi, \\ \tfrac12 (1 + A + \alpha - \varphi), & \varphi < \alpha \le \theta, \\ A + \alpha - \varphi, & \theta < \alpha \le \tfrac\pi2 - \theta, \\ B - \tfrac12 (1 + A) \bigl(\tfrac\pi2 - \alpha - \varphi\bigr) - \tfrac14 \bigl(\tfrac\pi2 - \alpha - \varphi\bigr)^2, & \tfrac\pi2 - \theta < \alpha \le \tfrac\pi2 - \varphi, \\ 0, & \alpha > \tfrac\pi2 - \varphi, \end{cases}
```

let

```math
X(\alpha) = 1 - \int_\alpha^{\pi/2 - \varphi} r(t) \cos t \, dt, \qquad Y(\alpha) = \int_\alpha^{\pi/2 - \varphi} r(t) \sin t \, dt,
```

and let the *rotation path* $p = (p_1, p_2) : \mathbb{R} \to \mathbb{E}^2$ be given in coordinates
by

```math
p_1(\alpha) = \begin{cases} \cos\alpha - 1, & \alpha \le \varphi, \\ X(\tfrac\pi2 - \alpha) \cos\alpha + Y(\tfrac\pi2 - \alpha) \sin\alpha - 1, & \alpha > \varphi, \end{cases}
```

```math
p_2(\alpha) = \begin{cases} Y(\alpha) \cos\alpha - \bigl(4X(0) - 2 - X(\alpha)\bigr) \sin\alpha - 1, & \alpha \le \tfrac\pi2 - \varphi, \\ -\bigl(4X(0) - 3\bigr) \sin\alpha - 1, & \alpha > \tfrac\pi2 - \varphi. \end{cases}
```

For an angle $\alpha$ and a point $q \in \mathbb{E}^2$, let $T_{\alpha, q} \in \mathrm{E}(2)$
translate by $q$ and then rotate by $\alpha$ about the origin, for the standard orientation of
$\mathbb{E}^2$: $T_{\alpha, q}(z) = \mathrm{rot}(\alpha)(z + q)$. formal-conjectures' *Gerver's
sofa* is the sofa of the path $p$,

```math
G_{\mathrm{fc}} = T_{0, p(0)}\bigl(\chi^{-1}(H_L)\bigr) \cap T_{\pi/2, p(\pi/2)}\bigl(\chi^{-1}(V_L)\bigr) \cap \bigcap_{\alpha \in [0, \pi/2]} T_{\alpha, p(\alpha)}\bigl(\chi^{-1}(L)\bigr).
```

*Lean: [`FormalConjectures.MovingSofa.GerversSofa.r`](../../Challenge.lean#L383),
[`FormalConjectures.MovingSofa.GerversSofa.x`](../../Challenge.lean#L398),
[`FormalConjectures.MovingSofa.GerversSofa.y`](../../Challenge.lean#L395),
[`FormalConjectures.MovingSofa.GerversSofa.p`](../../Challenge.lean#L401),
[`FormalConjectures.MovingSofa.rotateTranslate`](../../Challenge.lean#L347),
[`FormalConjectures.MovingSofa.sofaOfRotateTranslatePath`](../../Challenge.lean#L354),
[`FormalConjectures.MovingSofa.gerversSofa`](../../Challenge.lean#L412).*

The functions $X$ and $Y$ are formal-conjectures' `x` and `y`; capital letters keep them apart from
the coordinates. Baek's Gerver's sofa is the shape of Romik's rotation path $\mathbf{x}$
([§1.2](README.md#12-the-main-theorems), [Chapter 10](10-gerver.md)):

```math
G = \operatorname{shape}(\mathbf{x}) = H_L \cap \bigcap_{t \in [0, \pi/2]} \bigl(\mathbf{x}(t) + R_t L\bigr) \cap \bigl(\mathbf{x}(\pi/2) + R_{\pi/2} V_L\bigr).
```

Both sets are intersections of hallways that touch the sofa, one for each angle. They differ in how
the hallway at the angle $t$ is placed (Figure 13.1). Baek and Romik rotate $L$ by $t$ about the
origin $O$ and then translate it, so that its inner corner lands on $\mathbf{x}(t)$.
formal-conjectures translates $L$ by $p(t)$ and then rotates the result by $t$ about $O$, which
moves the inner corner from $p(t)$ to $R_t\, p(t)$. The two hallways agree when
$R_t\, p(t) = \mathbf{x}(t)$, which Proposition 13.17 proves.

![Two panels with Gerver's sofa and the hallway at the angle t = 0.7 that touches it. Left: the hallway L is rotated by t about the origin O (dashed), then translated by Romik's inner corner x(t). Right: L is translated by formal-conjectures' point p(t) (dashed), then rotated by t about O, which carries p(t) to x(t). Both give the same hallway](figures/13-bridge/conventions.svg)

*Figure 13.1.* The two conventions, for Gerver's sofa at the angle $t = 0.7$. Left: $L$ rotated by
$t$ about $O$ (dashed), then translated by $\mathbf{x}(t)$ (orange). Right: $L$ translated by $p(t)$
(dashed), then rotated by $t$ about $O$ (green arc), which carries $p(t)$ to
$\mathbf{x}(t) = R_t\, p(t)$. Both give the same hallway, which touches the sofa.

## 13.2 Coordinates and rigid motions

### Lemma 13.5 (coordinates)

The coordinate map $\chi$ is a linear homeomorphism, whose inverse sends $(x, y)$ to the point with
coordinates $x$ and $y$; so it maps closed sets to closed sets and connected sets to connected sets.
It preserves area: $\lvert \chi(S) \rvert = \lvert S \rvert$ for every set $S \subseteq \mathbb{E}^2$,
measurable or not. And $\chi(q)$ lies in $H_L$, $V_L$ or $L$ if and only if $q$ lies in
formal-conjectures' horizontal side, vertical side or hallway, respectively.

*Lean: [`MovingSofaBridge.coordinates`](../../MovingSofaBridge/Motion.lean#L43),
[`MovingSofaBridge.point`](../../MovingSofaBridge/Motion.lean#L46),
[`MovingSofaBridge.volume_coordinates_image`](../../MovingSofaBridge/Motion.lean#L91),
[`MovingSofaBridge.coordinates_image_closed`](../../MovingSofaBridge/Motion.lean#L102),
[`MovingSofaBridge.coordinates_mem_hallway`](../../MovingSofaBridge/Motion.lean#L136).*

*Proof.* Mathlib identifies `EuclideanSpace ℝ (Fin 2)` with the functions
$\lbrace 0, 1 \rbrace \to \mathbb{R}$, and these functions with pairs, by maps that preserve volume;
$\chi$ is their composite. It is a measurable embedding, so it preserves the outer measure of every
set, measurable or not. The other statements hold by definition. $\square$

### Lemma 13.6 (rotations and translations in E(2))

For an angle $a$ and a vector $c \in \mathbb{R}^2$ there is an element $\rho(a, c)$ of
$\mathrm{E}(2)$ that rotates by $a$ and then translates by $c$:
$\chi(\rho(a, c)(q)) = R_a\, \chi(q) + c$ for every $q \in \mathbb{E}^2$. The map
$(a, c) \mapsto \rho(a, c)$ is continuous for the topology of Definition 13.1. Every element of
$\mathrm{E}(2)$ preserves the area of every set.

*Lean: [`MovingSofaBridge.realization`](../../MovingSofaBridge/Motion.lean#L220),
[`MovingSofaBridge.realization_coordinates`](../../MovingSofaBridge/Motion.lean#L224),
[`MovingSofaBridge.realization_continuous`](../../MovingSofaBridge/Motion.lean#L258),
[`MovingSofaBridge.volume_image_affineIsometry`](../../MovingSofaBridge/Motion.lean#L167).*

*Proof.* The map $q \mapsto \chi^{-1}(R_a\, \chi(q))$ is linear, and it preserves the norm since
$\cos^2 a + \sin^2 a = 1$. Followed by the translation by $\chi^{-1}(c)$, it is the affine isometry
$\rho(a, c)$. As a continuous affine map, $\rho(a, c)$ has the value $\chi^{-1}(c)$ at the origin
and the linear part $\cos a \cdot \mathrm{id} + \sin a \cdot J$, where $J(q_0, q_1) = (-q_1, q_0)$
is the quarter turn. Both are continuous in $(a, c)$, so $\rho$ is continuous, by Mathlib's
homeomorphism between continuous affine maps and pairs (value at the origin, linear part). Finally,
an affine isometry $e$ is its linear part followed by the translation by $e(0)$. Both preserve
Lebesgue measure, and $e$ is a homeomorphism, hence a measurable embedding, so it preserves the
outer measure of every set. $\square$

### Lemma 13.7 (the determinant along a path)

For $e \in \mathrm{E}(2)$ let $a = \chi(\ell_e(1, 0))$ and $b = \chi(\ell_e(0, 1))$ be the columns
of its linear part $\ell_e$, and $\det e = a_0 b_1 - a_1 b_0$.

1. $\lvert a \rvert = \lvert b \rvert = 1$, $\langle a, b \rangle = 0$ and $(\det e)^2 = 1$.
2. The columns and the determinant are continuous in $e$, and along a continuous path
   $m : [0, 1] \to \mathrm{E}(2)$ with $m(0) = \mathrm{id}$, $\det m(t) = 1$ for every $t$.
3. If $\det e = 1$ and $a = (\cos\vartheta, \sin\vartheta)$, then
   $\chi(\ell_e(q)) = R_\vartheta\, \chi(q)$ for every $q$.

*Lean: [`MovingSofaBridge.determinant`](../../MovingSofaBridge/Motion.lean#L289),
[`MovingSofaBridge.determinant_sq`](../../MovingSofaBridge/Motion.lean#L332),
[`MovingSofaBridge.determinant_eq_one_on_path`](../../MovingSofaBridge/Motion.lean#L350),
[`MovingSofaBridge.linear_eq_euclideanRotate`](../../MovingSofaBridge/Motion.lean#L384).*

*Proof.* (1) $\ell_e$ preserves norms, so $\lvert a \rvert = \lvert b \rvert = 1$ and
$\lvert a + b \rvert^2 = \lvert (1, 1) \rvert^2 = 2$, which gives $\langle a, b \rangle = 0$. By
Lagrange's identity,
$(\det e)^2 = \lvert a \rvert^2 \lvert b \rvert^2 - \langle a, b \rangle^2 = 1$.

(2) The linear part is $\ell_e(q) = e(q) - e(0)$, and $e \mapsto e(q)$ is continuous for every $q$,
so the columns and the determinant are continuous in $e$. Along the path, $\det m(0) = 1$. If
$\det m(t) \le 0$ for some $t$, the intermediate value theorem gives a $u$ with $\det m(u) = 0$,
against (1). So $\det m(t) > 0$, and $\det m(t) = 1$ by (1).

(3) By (1) and $\det e = 1$,
$(b_0 + a_1)^2 + (b_1 - a_0)^2 = \lvert a \rvert^2 + \lvert b \rvert^2 - 2 \det e = 0$. So
$b = (-a_1, a_0)$, and $\ell_e(q) = q_0 a + q_1 b$ is the rotation by $\vartheta$. $\square$

### Proposition 13.8 (the lifted angle)

Let $m : [0, 1] \to \mathrm{E}(2)$ be continuous with $m(0) = \mathrm{id}$. There are continuous
functions $\vartheta : [0, 1] \to \mathbb{R}$ and $c : [0, 1] \to \mathbb{R}^2$ with
$\vartheta(0) = 0$, $c(0) = 0$ and

```math
\chi\bigl(m(t)(q)\bigr) = R_{\vartheta(t)}\, \chi(q) + c(t) \qquad \text{for all } t \in [0, 1],\ q \in \mathbb{E}^2.
```

*Lean: [`MovingSofaBridge.exists_angle_lift`](../../MovingSofaBridge/Motion.lean#L424),
[`MovingSofaBridge.firstDirection`](../../MovingSofaBridge/Motion.lean#L403).*

*Proof.* The idea is to lift the first column of $m(t)$, a path in the unit circle, to a path of
angles. The first column $a(t)$ of the linear part of $m(t)$ is a unit vector (Lemma 13.7), so
$\gamma(t) = a_0(t) + i\, a_1(t)$ is a path in the unit circle of $\mathbb{C}$, continuous by
Lemma 13.7 (2), with $\gamma(0) = 1$. The map $\vartheta \mapsto e^{i\vartheta}$ from $\mathbb{R}$
to $S^1$ is a covering map, so $\gamma$ lifts (Mathlib's path lifting for covering maps): there is
a continuous $\vartheta$ with $\vartheta(0) = 0$ and $e^{i\vartheta(t)} = \gamma(t)$ for every
$t$. Then $a(t) = (\cos\vartheta(t), \sin\vartheta(t))$ and $\det m(t) = 1$, so by Lemma 13.7 (3)
the linear part of $m(t)$ is $R_{\vartheta(t)}$ in coordinates. Put $c(t) = \chi(m(t)(0))$, which is
continuous with $c(0) = 0$. $\square$

The angle $\vartheta(t)$ is the total angle through which the motion has turned by the time $t$,
counted with its sign and its full turns, as Figure 13.2 shows; the argument of $\gamma(t)$ in
$(-\pi, \pi]$ would jump. Baek's rotation angle of the motion is $\omega = -\vartheta(1)$.

![Left: a continuous path of rigid motions m(t), t from 0 to 1, applied to a pennant in the hallway: it slides along the horizontal side, turns the corner and leaves along the vertical side, spinning clockwise by five quarter turns; the pennant is drawn at nine times, darker as t grows. Right: the lifted angle ϑ(t), a continuous function decreasing from 0 to −5π/2, and the principal argument of the first column of m(t), dashed, which agrees with it until it reaches −π and then jumps to π](figures/13-bridge/angle-lift.svg)

*Figure 13.2.* A continuous path $m(t)$ in $\mathrm{E}(2)$ from the identity, applied to a pennant,
which stays in the hallway while it spins clockwise by five quarter turns (left, darker as $t$
grows). Its lifted angle $\vartheta(t)$ decreases continuously from $0$ to $-5\pi/2$ (orange,
right); the principal argument of the first column (dashed) agrees with it down to $-\pi$ and then
jumps to $\pi$.

## 13.3 Moving sofas and the sofa constant

### Theorem 13.9 (the two notions of moving sofa agree)

A set $S \subseteq \mathbb{E}^2$ is a moving sofa of formal-conjectures, for some motion, if and
only if $S \subseteq \chi^{-1}(H_L)$ and $\chi(S)$ is a moving sofa.

*Lean: [`Bridge.isMovingSofa_iff`](../../Challenge.lean#L731),
[`MovingSofaBridge.isMovingSofa_iff`](../../MovingSofaBridge/Motion.lean#L562),
[`MovingSofaBridge.isMovingSofa_coordinates`](../../MovingSofaBridge/Motion.lean#L460),
[`MovingSofaBridge.isMovingSofa_of_coordinates`](../../MovingSofaBridge/Motion.lean#L490).*

*Proof.* *From formal-conjectures to Baek.* Let $m$ be a motion of $S$. By definition
$S \subseteq \chi^{-1}(H_L)$, and $\chi(S)$ is closed and connected by Lemma 13.5. Proposition 13.8
writes $m(t)$ in coordinates as $q \mapsto R_{\vartheta(t)} q + c(t)$ with $\vartheta(0) = 0$ and
$c(0) = 0$. Extend $\vartheta$ and $c$ to $\mathbb{R}$ by their values at the nearer end of
$[0, 1]$. Then $\Phi_s(q) = R_{\vartheta(s)} q + c(s)$ is a motion of $\chi(S)$ in Baek's sense.
Indeed $\Phi_0$ is the identity and $\chi(S) \subseteq H_L$. Each $\Phi_s(\chi(S)) = \chi(m(s)(S))$
lies in $\chi(\chi^{-1}(L)) = L$, and in the same way $\Phi_1(\chi(S)) \subseteq V_L$. The rotation
angle of $\Phi$ is $\omega = -\vartheta(1)$.

*From Baek to formal-conjectures.* Let $\Phi_s(q) = R_{\vartheta(s)} q + c(s)$ be a motion of
$\chi(S)$, with $\vartheta(0) = 0$. A motion of formal-conjectures must start at the identity, while
$\Phi_0$ is the translation by $c(0)$. So first slide $S$ to its translate by $c(0)$, then follow
$\Phi$ at double speed (Figure 13.3). With $\lambda(t) = \min(2t, 1)$ and
$\tau(t) = \max(0, 2t - 1)$, let

```math
m(t) = \rho\bigl(\vartheta(\tau(t)),\ \lambda(t)\, c(\tau(t))\bigr), \qquad t \in [0, 1].
```

It is continuous by Lemma 13.6, and $m(0) = \rho(0, 0)$ is the identity. For $t \le 1/2$,
$\tau(t) = 0$ and $m(t)$ is the translation by $\lambda c(0)$ with
$\lambda = \lambda(t) \in [0, 1]$. For $q \in S$, both $\chi(q)$ and
$\chi(q) + c(0) = \Phi_0(\chi(q))$ lie in $H_L$, and $H_L$ is convex, so

```math
\chi(q) + \lambda c(0) = (1 - \lambda)\, \chi(q) + \lambda\, \bigl(\chi(q) + c(0)\bigr) \in H_L \subseteq L.
```

For $t \ge 1/2$, $\lambda(t) = 1$ and $m(t)$ is $\Phi_{2t - 1}$ in coordinates, which maps $\chi(S)$
into $L$, and at $t = 1$ into $V_L$. $\square$

![The hallway with a sofa S, a half-disk of radius 1, in its horizontal side (dashed outline); the translate S + c(0), where a motion of Baek's paper starts, against the inner corner O (solid); the arrow c(0) between them; and the sofa halfway through that motion, turned by π/4 about O (faint)](figures/13-bridge/slide.svg)

*Figure 13.3.* The motion of formal-conjectures built from one of Baek's, for the half-disk $S$ of
radius 1 (dashed). Its motion in Baek's sense starts at the translate $S + c(0)$ against the inner
corner (solid) and turns it about $O$; the faint copy is $\Phi_{1/2}(S)$, halfway. In the first half
of the time, $S$ slides by $\lambda c(0)$, $0 \le \lambda \le 1$, inside the convex set $H_L$; in
the second half it follows Baek's motion.

### Theorem 13.10 (the two optimal areas agree)

The sofa constant is the supremum of the areas of Baek's moving sofas:

```math
\alpha_{\mathrm{fc}} = \sup \bigl\lbrace \lvert S \rvert : S \subseteq \mathbb{R}^2 \text{ is a moving sofa} \bigr\rbrace = \alpha_{\max}.
```

*Lean: [`Bridge.sofaConstant_eq`](../../Challenge.lean#L739),
[`MovingSofaBridge.sofaConstant_eq`](../../MovingSofaBridge/Motion.lean#L600),
[`MovingSofaBridge.exists_isMovingSofa_volume_eq`](../../MovingSofaBridge/Motion.lean#L574).*

*Proof.* Theorem 13.9 carries sofas in both directions, and $\chi$ preserves area (Lemma 13.5). If
$S$ is a moving sofa of formal-conjectures, then $\chi(S)$ is a moving sofa by Theorem 13.9, and
$\lvert S \rvert = \lvert \chi(S) \rvert \le \alpha_{\max}$. Conversely, let
$S \subseteq \mathbb{R}^2$ be a moving sofa with motion $\Phi_s(q) = R_{\vartheta(s)} q + c(s)$. Its
translate $S + c(0) = \Phi_0(S)$ lies in $H_L$, and it is a moving sofa with the motion
$q \mapsto R_{\vartheta(s)} q + c(s) - R_{\vartheta(s)} c(0)$. By Theorem 13.9,
$\chi^{-1}(S + c(0))$ is a moving sofa of formal-conjectures, of area
$\lvert S + c(0) \rvert = \lvert S \rvert$. So $\lvert S \rvert \le \alpha_{\mathrm{fc}}$. $\square$

## 13.4 Gerver's constants and Romik's parameters

formal-conjectures defines Gerver's sofa from four constants, Baek from Romik's 22 parameters
([Chapter 10](10-gerver.md)). This section shows that each set of parameters determines the other,
and that Gerver's system has exactly one solution.

Write $u_t = (\cos t, \sin t)$ and $v_t = (-\sin t, \cos t)$ for the frame of the hallway at the
angle $t$. On each of its five phases, Romik's rotation path has the form
$\mathbf{x}(t) = R_t\, w(t) + \kappa_i$, where $w = (w_1, w_2)$ is an explicit polynomial or
trigonometric curve and $\kappa_i$ a constant vector
([Definition 10.3](10-gerver.md#definition-103-romiks-parameters-and-the-five-phases)). By
[Lemma 10.5](10-gerver.md#lemma-105-the-phases-in-the-rotating-frame)
([`MovingSofaOptimality.GerverParams.rom_hasDerivAt_rot`](../../MovingSofaOptimality/External/Romik.lean#L47)),
the velocity has the components $\langle \mathbf{x}'(t), u_t \rangle = w_1' - w_2$ and
$\langle \mathbf{x}'(t), v_t \rangle = w_2' + w_1$ in this frame; Table 10.1 lists them phase by
phase. So every condition of Romik's system on $\mathbf{x}'$ at a phase boundary is a pair of
equations between the parameters.

### Definition 13.11 (Romik's parameters from Gerver's constants, and back)

For $D = (A, B, \varphi, \theta)$, let $\mathrm{toRomik}(D)$ be Romik's parameters with the angles
$\varphi$, $\theta$ and

```math
\begin{aligned}
a_1 &= \tfrac12 \bigl((A + \tfrac12) \sin\varphi + (B + 1) \cos\varphi\bigr), & a_2 &= -\tfrac14, \\
b_1 &= \tfrac12 (\varphi - 1 - A), & b_2 &= B - \tfrac12 - b_1 \varphi + \tfrac14 \varphi^2, \\
c_1 &= \tfrac\pi2 + A - \varphi - 1, & c_2 &= A - \varphi - 1, \\
d_1 &= \tfrac\pi4 - b_1, & d_2 &= b_2 + \tfrac\pi4 \bigl(2 b_1 - \tfrac\pi4\bigr), \\
e_1 &= a_1, & e_2 &= \tfrac14,
\end{aligned}
```

and the translations

```math
\begin{aligned}
\kappa_1 &= \bigl(1 - a_1, \tfrac14\bigr), & \kappa_2 &= \kappa_1 + R_\varphi \bigl(-\tfrac B2, \tfrac14\bigr), & \kappa_3 &= \kappa_2 + R_\theta \bigl(\tfrac12, \tfrac12 (1 - A - (\theta - \varphi))\bigr), \\
\kappa_4 &= \bigl(2\kappa_{3,1} - \kappa_{2,1},\ \kappa_{2,2}\bigr), & \kappa_5 &= \bigl(2\kappa_{3,1} - 1 + a_1,\ \tfrac14\bigr).
\end{aligned}
```

Conversely, for Romik's parameters $P$, let
$\mathrm{ofRomik}(P) = \bigl(\varphi - 1 - 2b_1,\ \tfrac12 - \tfrac14 \varphi^2 + b_1 \varphi + b_2,\ \varphi,\ \theta\bigr)$.

*Lean: [`MovingSofaBridge.GerverConstants`](../../MovingSofaBridge/GerverConstants.lean),
[`MovingSofaBridge.GerverConstants.toRomik`](../../MovingSofaBridge/RomikParams.lean#L54),
[`MovingSofaBridge.GerverConstants.ofRomik`](../../MovingSofaBridge/RomikParams.lean#L150).*

On the second phase $w(t) = (-\tfrac14 t^2 + b_1 t + b_2,\ \tfrac12 t - b_1 - 1)$, so the formulas
for $b_1$ and $b_2$ say that

```math
\mathbf{x}'(\varphi) = -A\, u_\varphi + B\, v_\varphi :
```

Gerver's $A$ and $B$ are the components of the velocity of the inner corner at the angle $\varphi$,
in the frame of the hallway. The path rebuilt by $\mathrm{toRomik}$ is symmetric. Let
$\sigma(q) = (2\kappa_{3,1} - q_1, q_2)$ be the reflection in the vertical line through $\kappa_3$.
Then the fifth, fourth and third phases satisfy
$\mathbf{x}_5(\tfrac\pi2 - t) = \sigma(\mathbf{x}_1(t))$,
$\mathbf{x}_4(\tfrac\pi2 - t) = \sigma(\mathbf{x}_2(t))$ and
$\mathbf{x}_3(\tfrac\pi2 - t) = \sigma(\mathbf{x}_3(t))$, identities between explicit functions
([`MovingSofaBridge.GerverConstants.x5_reflection`](../../MovingSofaBridge/RomikParams.lean#L105),
[`MovingSofaBridge.GerverConstants.x4_reflection`](../../MovingSofaBridge/RomikParams.lean#L111),
[`MovingSofaBridge.GerverConstants.x3_reflection`](../../MovingSofaBridge/RomikParams.lean#L117)).

### Lemma 13.12 (from Romik's parameters to Gerver's constants)

Let $P$ be a solution of Romik's system with $\varphi \in [0.039, 0.04]$ and
$\theta \in [0.68, 0.69]$. Then $\mathrm{ofRomik}(P)$ solves Gerver's system, and
$\mathrm{toRomik}(\mathrm{ofRomik}(P)) = P$.

*Lean:
[`MovingSofaBridge.GerverConstants.ofRomik_valid`](../../MovingSofaBridge/RomikParams.lean#L312),
[`MovingSofaBridge.GerverConstants.ofRomik_toRomik`](../../MovingSofaBridge/RomikParams.lean#L210),
[`MovingSofaBridge.GerverConstants.ofRomik_frame`](../../MovingSofaBridge/RomikParams.lean#L157),
[`MovingSofaBridge.GerverConstants.contact_error`](../../MovingSofaBridge/RomikParams.lean#L132).*

*Proof.* Each of Gerver's equations is one of Romik's conditions written in the four constants. Let
$(A, B, \varphi, \theta) = \mathrm{ofRomik}(P)$. Then $b_1$ and $b_2$ are given by Definition 13.11,
so on the second phase the velocity at $\varphi$ has the components $-A$ and $B$. Table 10.1 gives
the components on the other phases.

1. *Smoothness at $\varphi$.* Matching the components of the first phase at $\varphi$ with $-A$ and
   $B$ gives

   ```math
   2 a_1 \sin\varphi = A + \tfrac12 (1 - \cos\varphi), \qquad 2 a_1 \cos\varphi = B + 1 + \tfrac12 \sin\varphi .
   ```

   Eliminating $a_1$, with $\sin^2\varphi + \cos^2\varphi = 1$, gives $E_3 = 0$; solving for $a_1$
   gives the formula of Definition 13.11.
2. *Smoothness at $\theta$.* Matching the first components of the second and third phases at
   $\theta$, $2b_1 + 1 - \theta = \tfrac\pi2 - 1 - c_1 - \theta$, gives
   $c_1 = \tfrac\pi2 + A - \varphi - 1$, and $c_2 = c_1 - \tfrac\pi2 = A - \varphi - 1$ by Romik's
   symmetry equations. Matching the second components,
   $\tfrac12 - \tfrac14\theta^2 + b_1\theta + b_2 = 1 + c_1 - \theta$, is then $E_4 = 0$.
3. *The parameters.* The coefficients $a_1, b_1, b_2, c_1, c_2$ of $P$ are those of
   $\mathrm{toRomik}(A, B, \varphi, \theta)$ by steps 1 and 2. Romik's symmetry equations (27)–(31)
   give $d_1, d_2, e_1, e_2$, and Romik's start equations give $a_2$ and $\kappa_1$. The continuity of
   $\mathbf{x}$ at $\varphi$ and $\theta$ determines $\kappa_2$ and $\kappa_3$. With the symmetry of
   the rebuilt path, the continuity at $\pi/2 - \theta$ and $\pi/2 - \varphi$ determines $\kappa_4$
   and $\kappa_5$. So $\mathrm{toRomik}(A, B, \varphi, \theta) = P$.
4. *The contact condition.* For the parameters of $\mathrm{toRomik}$, a direct computation gives

   ```math
   \mathbf{x}_2(\varphi) - \mathbf{B}_4\bigl(\tfrac\pi2 - \theta\bigr) = \bigl(-\tfrac12 E_2,\ -\tfrac12 E_1\bigr),
   ```

   where $\mathbf{B}_4$ is the contact point $\mathbf{B} = \mathbf{x} + \langle \mathbf{x}', u \rangle v$
   of the fourth phase. By step 3 these parameters are $P$, which satisfies Romik's first contact
   condition $\mathbf{x}_1(\varphi) = \mathbf{B}_4(\pi/2 - \theta)$ and the continuity
   $\mathbf{x}_1(\varphi) = \mathbf{x}_2(\varphi)$. So $E_1 = E_2 = 0$.
5. *The domain.* Romik's system has $0 < \varphi < \theta < \pi/4$. Every solution in the box has
   $b_1 \in [-0.5276245983, -0.5276245978]$ and $b_2 \in [0.9202583844, 0.920258386]$
   ([Proposition B.7](appendix-b.md#proposition-b7-enclosures-of-the-parameters)). So
   $A = \varphi - 1 - 2b_1 > -1 + 1.0552 > 0$ and
   $B = \tfrac12 - \tfrac14\varphi^2 + b_1\varphi + b_2 \ge \tfrac12 - \tfrac1{400} - 0.53 \cdot 0.04 + 0.92 > 0$.
   $\square$

### Theorem 13.13 (Gerver's system has exactly one solution)

Gerver's system has exactly one solution $D$. For every solution $P$ of Romik's system with
$\varphi \in [0.039, 0.04]$ and $\theta \in [0.68, 0.69]$, $D = \mathrm{ofRomik}(P)$ and
$\mathrm{toRomik}(D) = P$.

*Lean: [`FormalConjectures.MovingSofa.GerversSofa.ABφθSpec.existsUnique`](../../Challenge.lean#L373),
[`MovingSofaBridge.GerverConstants.spec_existsUnique`](../../MovingSofaBridge/RomikParams.lean#L345),
[`MovingSofaBridge.GerverConstants.eq_ofRomik`](../../MovingSofaBridge/RomikParams.lean#L355),
[`MovingSofaBridge.GerverConstants.romik_solution`](../../MovingSofaBridge/RomikParams.lean#L362).*

*Proof.* Romik's system has a solution in the box
([Theorem 1.1](README.md#theorem-11-gervers-sofa-is-well-defined), proved by interval arithmetic in
[Appendix B](appendix-b.md)). For every such solution $P$, $\mathrm{ofRomik}(P)$ solves Gerver's
system by Lemma 13.12. By Theorem A.1 ([Appendix A](appendix-a.md)), Gerver's system has at most
one solution. So it has exactly one, $D$, and $D = \mathrm{ofRomik}(P)$ for every such $P$; then
$\mathrm{toRomik}(D) = \mathrm{toRomik}(\mathrm{ofRomik}(P)) = P$ by Lemma 13.12. $\square$

The existence rests on the rigorous numerics for Romik's system. The uniqueness holds on the whole
domain $0 \le \varphi \le \theta \le \pi/4$, $A, B \ge 0$, and uses only elementary inequalities.

## 13.5 The two Gerver's sofas

Throughout this section $D = (A, B, \varphi, \theta)$ solves Gerver's system, and $\mathbf{x}$ is
the rotation path of $\mathrm{toRomik}(D)$, which solves Romik's system by Theorem 13.13. The path
$p$ and the functions $r$, $X$, $Y$ are those of Definition 13.4, computed from $D$, and $p$ is read
in coordinates. Romik's contact points
([Definition 10.2](10-gerver.md#definition-102-contact-paths-romik-equations-912)) are

```math
\mathbf{A}(t) = \mathbf{x}(t) + \langle \mathbf{x}'(t), u_t \rangle\, v_t + u_t, \qquad \mathbf{C}(t) = \mathbf{x}(t) - \langle \mathbf{x}'(t), v_t \rangle\, u_t + v_t ,
```

the points where the outer walls $a(t)$ and $c(t)$ of the hallway $\mathbf{x}(t) + R_t L$ touch
Gerver's sofa.

### Lemma 13.14 (the two conventions)

Let $p, \mathbf{y} : \mathbb{R} \to \mathbb{R}^2$ with $p(0) = 0$ and $R_t\, p(t) = \mathbf{y}(t)$
for $t \in [0, \pi/2]$. Then

```math
R_0\bigl(H_L + p(0)\bigr) \cap R_{\pi/2}\bigl(V_L + p(\tfrac\pi2)\bigr) \cap \bigcap_{t \in [0, \pi/2]} R_t\bigl(L + p(t)\bigr) = \operatorname{shape}(\mathbf{y}).
```

*Lean:
[`MovingSofaBridge.GerverConstants.shape_eq_of_rotated_path`](../../MovingSofaBridge/GerverSofa.lean#L78),
[`MovingSofaBridge.GerverConstants.shapeFromPrePath`](../../MovingSofaBridge/GerverSofa.lean#L69).*

*Proof.* For $t \in [0, \pi/2]$ and every $q$,
$R_t(q + p(t)) = R_t q + R_t\, p(t) = \mathbf{y}(t) + R_t q$. So
$R_t(L + p(t)) = \mathbf{y}(t) + R_t L$ and
$R_{\pi/2}(V_L + p(\pi/2)) = \mathbf{y}(\pi/2) + R_{\pi/2} V_L$, and $R_0(H_L + p(0)) = H_L$.
$\square$

### Lemma 13.15 (the radius is the speed of the contact point C)

The contact point $\mathbf{C}$ is continuous, and at every $t$ it has the right derivative
$-r^+(t)\, u_t$, where $r^+$ equals $r$ except at the four breakpoints $\varphi$, $\theta$,
$\pi/2 - \theta$, $\pi/2 - \varphi$, where it takes the value of the next piece. Consequently, for
all real $a$ and $b$,

```math
\int_a^b r(t) \cos t \, dt = \mathbf{C}_1(a) - \mathbf{C}_1(b), \qquad \int_a^b r(t) \sin t \, dt = \mathbf{C}_2(a) - \mathbf{C}_2(b).
```

*Lean:
[`MovingSofaBridge.GerverConstants.rightRadius_eq_phase`](../../MovingSofaBridge/GerverSofa.lean#L125),
[`MovingSofaBridge.GerverConstants.radius_ae_rightRadius`](../../MovingSofaBridge/GerverSofa.lean#L136),
[`MovingSofaBridge.GerverConstants.contactC_right_deriv`](../../MovingSofaBridge/GerverSofa.lean#L168),
[`MovingSofaBridge.GerverConstants.contactC_integrals`](../../MovingSofaBridge/GerverSofa.lean#L177).*

*Proof.* On each phase, [Lemma 10.5](10-gerver.md#lemma-105-the-phases-in-the-rotating-frame) gives
$\mathbf{C}(t) = R_t(-w_2'(t), w_2(t) + 1) + \kappa$ and $\mathbf{C}'(t) = -\rho_C(t)\, u_t$, with
$\rho_C = w_2'' + w_2 + 1$. Table 13.2 rewrites the $\rho_C$ of Table 10.1 with the parameters of
Definition 13.11: on each phase it is the corresponding piece of $r$. The path of a solution of
Romik's system agrees with the phase formula, together with its derivative, on each closed phase
interval. So $\mathbf{C}$ is continuous and has, at every $t$, the right derivative of the phase
that starts at $t$, which is $-r^+(t)\, u_t$. Since $r$ and $r^+$ differ at four points only, they
have the same integrals, and the fundamental theorem of calculus for right derivatives gives the
two formulas. $\square$

| Phase | Interval | $\rho_C(t)$ (Table 10.1) | $\rho_C(t)$ with Definition 13.11 |
| --- | --- | --- | --- |
| 1 | $t < \varphi$ | $\tfrac12$ | $\tfrac12$ |
| 2 | $\varphi \le t < \theta$ | $\tfrac12 t - b_1$ | $\tfrac12(1 + A + t - \varphi)$ |
| 3 | $\theta \le t < \tfrac\pi2 - \theta$ | $1 + c_1 + t - \tfrac\pi2$ | $A + t - \varphi$ |
| 4 | $\tfrac\pi2 - \theta \le t < \tfrac\pi2 - \varphi$ | $\tfrac12 - \tfrac14 s^2 + b_1 s + b_2$, $s = \tfrac\pi2 - t$ | $B - \tfrac12(1 + A)(s - \varphi) - \tfrac14(s - \varphi)^2$ |
| 5 | $t \ge \tfrac\pi2 - \varphi$ | $0$ | $0$ |

*Table 13.2.* The speed $\rho_C$ of the contact point $\mathbf{C}$ on each phase, as in Table 10.1
and in terms of Gerver's constants. The last column is a piece of $r$, and $r^+(t)$ takes that piece
for $t$ in the interval of the second column.

Since $\mathbf{C}'(t) = -r(t)\, u_t$, the direction of $\mathbf{C}$ turns at unit rate while it
moves at speed $r(t)$. So $r(t)$ is the radius of curvature of the curve that $\mathbf{C}$ traces,
the upper left boundary of Gerver's sofa (Figure 13.4). The radius jumps at $\varphi$, from $1/2$
to $(1 + A)/2 = 0.5472\ldots$; at $\theta$, from $0.8683\ldots$ to $0.7366\ldots$; and at
$\pi/2 - \varphi$, from $B = 1.3992\ldots$ to $0$. It is continuous at $\pi/2 - \theta$, with the
value $0.9447\ldots$, exactly because $E_4 = 0$.

![Above: the graph of formal-conjectures' radius r(α) for α from 0 to π/2: the constant 1/2 up to φ, then two increasing linear pieces, a quadratic piece up to π/2 − φ, and 0 after it; r jumps at φ, θ and π/2 − φ and is continuous at π/2 − θ. Below: Gerver's sofa with Romik's contact point C(α) on its upper left boundary (orange), from C(0) on the top edge down to the corner C(π/2 − φ), with dots at the breakpoints θ and π/2 − θ, and its mirror image A on the upper right boundary (green)](figures/13-bridge/radius.svg)

*Figure 13.4.* Above: formal-conjectures' radius $r(\alpha)$, with its four breakpoints. Below:
Gerver's sofa and the curve $\mathbf{C}(\alpha) = (2\kappa_{3,1} - X(\alpha), Y(\alpha))$ that $r$
integrates to (orange), from $\mathbf{C}(0) = (1 - 2a_1, 1)$ on the top edge to the corner
$\mathbf{C}(\pi/2 - \varphi) = (2\kappa_{3,1} - 1, 0)$; $\mathbf{C}(\varphi)$ lies within $0.025$ of
$\mathbf{C}(0)$. Its mirror image $\mathbf{A}$ (green) bounds the sofa on the right.

### Lemma 13.16 (the integrals are the coordinates of the contact points)

Let $\kappa_3$ be the translation of $\mathrm{toRomik}(D)$ and
$\sigma(q) = (2\kappa_{3,1} - q_1, q_2)$.

1. $\mathbf{C}(t) = (2\kappa_{3,1} - 1, 0)$ for $t \ge \pi/2 - \varphi$, $\mathbf{A}(t) = (1, 0)$
   for $t \le \varphi$, and $\mathbf{C}(0) = (1 - 2a_1, 1)$.
2. $\mathbf{A}(t) = \sigma(\mathbf{C}(\pi/2 - t))$ for every $t$.
3. $\mathbf{C}(t) = \bigl(2\kappa_{3,1} - X(t),\ Y(t)\bigr)$ and
   $\mathbf{A}(t) = \bigl(X(\tfrac\pi2 - t),\ Y(\tfrac\pi2 - t)\bigr)$ for every $t$.
4. $2\kappa_{3,1} = 4X(0) - 2$.

*Lean:
[`MovingSofaBridge.GerverConstants.contactC_last`](../../MovingSofaBridge/GerverSofa.lean#L210),
[`MovingSofaBridge.GerverConstants.contactA_first`](../../MovingSofaBridge/GerverSofa.lean#L219),
[`MovingSofaBridge.GerverConstants.contactC_zero`](../../MovingSofaBridge/GerverSofa.lean#L230),
[`MovingSofaBridge.GerverConstants.contactA_reflection`](../../MovingSofaBridge/GerverSofa.lean#L272),
[`MovingSofaBridge.GerverConstants.contactC_integral_coordinates`](../../MovingSofaBridge/GerverSofa.lean#L280),
[`MovingSofaBridge.GerverConstants.contactA_integral_coordinates`](../../MovingSofaBridge/GerverSofa.lean#L287),
[`MovingSofaBridge.GerverConstants.horizontal_normalization`](../../MovingSofaBridge/GerverSofa.lean#L301).*

*Proof.* (1) By Lemma 10.5, $\mathbf{C} = R_t(-w_2', w_2 + 1) + \kappa$ and
$\mathbf{A} = R_t(w_1 + 1, w_1') + \kappa$ on each phase. On the fifth phase,
$(-w_2', w_2 + 1) = (-a_1 \cos t - \tfrac14 \sin t,\ a_1 \sin t - \tfrac14 \cos t) = R_{-t}(-a_1, -\tfrac14)$,
so $\mathbf{C}(t) = (-a_1, -\tfrac14) + \kappa_5 = (2\kappa_{3,1} - 1, 0)$. In the same way, on the
first phase $\mathbf{A}(t) = (a_1, -\tfrac14) + \kappa_1 = (1, 0)$ and
$\mathbf{C}(0) = (-a_1, \tfrac34) + \kappa_1 = (1 - 2a_1, 1)$.

(2) On each phase $i$, $\mathbf{A}_i(t) = \sigma(\mathbf{C}_{6-i}(\tfrac\pi2 - t))$ is an identity
between explicit functions, and $t$ lies in the closed interval of phase $i$ exactly when
$\pi/2 - t$ lies in that of phase $6 - i$.

(3) Lemma 13.15 with $b = \pi/2 - \varphi$, and (1), give
$\mathbf{C}(t) = \mathbf{C}(\tfrac\pi2 - \varphi) + \bigl(\int_t^{\pi/2 - \varphi} r \cos,\ \int_t^{\pi/2 - \varphi} r \sin\bigr) = (2\kappa_{3,1} - X(t),\ Y(t))$.
Then (2) gives
$\mathbf{A}(t) = \sigma(2\kappa_{3,1} - X(\tfrac\pi2 - t), Y(\tfrac\pi2 - t)) = (X(\tfrac\pi2 - t), Y(\tfrac\pi2 - t))$.

(4) By (1) and (3) at $t = 0$, $X(0) = 2\kappa_{3,1} - 1 + 2a_1$. For the parameters of
$\mathrm{toRomik}(D)$, a direct computation gives
$\kappa_{3,1} - (1 - \tfrac43 a_1) = \tfrac16 E_2 = 0$
([`MovingSofaBridge.GerverConstants.k3_fst`](../../MovingSofaBridge/RomikParams.lean#L84)). So
$4X(0) - 2 = 8\kappa_{3,1} - 6 + 8a_1 = 2\kappa_{3,1}$. $\square$

Numerically $a_1 = 1.2103224220\ldots$, $\kappa_{3,1} = -0.6137632294\ldots$ and
$X(0) = 0.1931183852\ldots$. So the sofa reaches from $2\kappa_{3,1} - 1 = -2.2275264588\ldots$ to
$1$, and its top edge runs from $\mathbf{C}(0) = (-1.4206448441\ldots, 1)$ to
$\mathbf{A}(\pi/2) = (X(0), 1)$.

### Proposition 13.17 (rotating the path)

For every $t$,

```math
p(t) = \bigl(\langle \mathbf{x}(t), u_t \rangle,\ \langle \mathbf{x}(t), v_t \rangle\bigr),
```

so $R_t\, p(t) = \mathbf{x}(t)$, and $p(0) = 0$.

*Lean:
[`MovingSofaBridge.GerverConstants.prePath_eq_projections`](../../MovingSofaBridge/GerverSofa.lean#L322),
[`MovingSofaBridge.GerverConstants.rotated_prePath`](../../MovingSofaBridge/GerverSofa.lean#L346),
[`MovingSofaBridge.GerverConstants.prePath_zero_of_valid`](../../MovingSofaBridge/GerverSofa.lean#L351).*

*Proof.* Each coordinate of $\mathbf{x}(t)$ in the frame $(u_t, v_t)$ is read off a contact point.
Since $u_t$ and $v_t$ are orthonormal, the definitions of $\mathbf{A}$ and $\mathbf{C}$ give

```math
\langle \mathbf{A}(t), u_t \rangle = \langle \mathbf{x}(t), u_t \rangle + 1, \qquad \langle \mathbf{C}(t), v_t \rangle = \langle \mathbf{x}(t), v_t \rangle + 1 .
```

For $t \le \varphi$, $\mathbf{A}(t) = (1, 0)$ by Lemma 13.16 (1), so
$\langle \mathbf{x}(t), u_t \rangle = \cos t - 1 = p_1(t)$. For $t > \varphi$, Lemma 13.16 (3) gives
$\langle \mathbf{x}(t), u_t \rangle = X(\tfrac\pi2 - t) \cos t + Y(\tfrac\pi2 - t) \sin t - 1 = p_1(t)$.
For $t \le \pi/2 - \varphi$, Lemma 13.16 (3) and (4) give
$\langle \mathbf{C}(t), v_t \rangle = -(4X(0) - 2 - X(t)) \sin t + Y(t) \cos t = p_2(t) + 1$. For
$t > \pi/2 - \varphi$, $\mathbf{C}(t) = (2\kappa_{3,1} - 1, 0)$ gives
$\langle \mathbf{C}(t), v_t \rangle = -(4X(0) - 3) \sin t = p_2(t) + 1$. Finally, every point $q$ is
$R_t (\langle q, u_t \rangle, \langle q, v_t \rangle)$, so $R_t\, p(t) = \mathbf{x}(t)$, and
$p(0) = \mathbf{x}(0) = 0$ by Romik's system. $\square$

So formal-conjectures' path is Romik's inner corner seen in the frame $(u_t, v_t)$ of the hallway
(Figure 13.1). Its coordinates plus 1 are the distances from $O$ of the outer walls $a(t)$ and
$c(t)$, which formal-conjectures computes from the boundary of the sofa. The path $p$ runs from
$p(0) = 0$ almost straight up to $p(\pi/2) = (0, 2 - 4X(0)) = (0, 1.2275264588\ldots)$, which
$R_{\pi/2}$ carries to $\mathbf{x}(\pi/2) = (-1.2275264588\ldots, 0)$.

### Lemma 13.18 (formal-conjectures' rotations in coordinates)

For every real $t$ and $q \in \mathbb{E}^2$, the rotation by $t$ for the standard orientation of
$\mathbb{E}^2$ satisfies $\chi(\mathrm{rot}(t)\, q) = R_t\, \chi(q)$. Consequently
$\chi(T_{t, p}(q)) = R_t\bigl(\chi(q) + \chi(p)\bigr)$.

*Lean:
[`MovingSofaBridge.rightAngleRotation_coordinates`](../../MovingSofaBridge/GerverSofa.lean#L424),
[`MovingSofaBridge.rotation_coordinates`](../../MovingSofaBridge/GerverSofa.lean#L432),
[`MovingSofaBridge.rotateTranslate_coordinates`](../../MovingSofaBridge/GerverSofa.lean#L440).*

*Proof.* Mathlib defines $\mathrm{rot}(t)\, q = \cos t \cdot q + \sin t \cdot J q$, where $J$ is the
right-angle rotation of the orientation. The standard basis $e_0, e_1$ is orthonormal and
positively oriented, so the area form $\Omega$ of the orientation has $\Omega(e_0, e_1) = 1$. The
vector $J e_0$ is orthogonal to $e_0$, and $\langle J e_0, e_1 \rangle = \Omega(e_0, e_1) = 1$. So
$J e_0 = e_1$ and $J e_1 = J^2 e_0 = -e_0$. Hence $\chi(J q) = (-q_1, q_0)$ and
$\chi(\mathrm{rot}(t)\, q) = (q_0 \cos t - q_1 \sin t,\ q_0 \sin t + q_1 \cos t) = R_t\, \chi(q)$.
Finally $T_{t, p}(q) = \mathrm{rot}(t)(q + p)$. $\square$

### Theorem 13.19 (the two Gerver's sofas agree)

For every solution $P$ of Romik's system with $\varphi \in [0.039, 0.04]$ and
$\theta \in [0.68, 0.69]$, the coordinates of formal-conjectures' Gerver's sofa form Baek's:

```math
\chi(G_{\mathrm{fc}}) = G .
```

*Lean: [`Bridge.gerversSofa_eq`](../../Challenge.lean#L747),
[`MovingSofaBridge.gerversSofa_eq`](../../MovingSofaBridge/GerverSofa.lean#L507),
[`MovingSofaBridge.coordinates_gerversSofa`](../../MovingSofaBridge/GerverSofa.lean#L496),
[`MovingSofaBridge.GerverConstants.shape_eq_gerverSofa_of_isSolution`](../../MovingSofaBridge/GerverSofa.lean#L362).*

*Proof.* Let $D = (A, B, \varphi, \theta)$ be formal-conjectures' constants; they solve Gerver's
system by their choice in Definition 13.3 and Theorem 13.13. By Lemma 13.18, a point $q$ lies in
$T_{t, p(t)}(\chi^{-1}(L))$ if and only if $\chi(q)$ lies in $R_t(L + \chi(p(t)))$, and likewise for
$H_L$ and $V_L$. So $\chi(G_{\mathrm{fc}})$ is the left side of Lemma 13.14 for the path
$\chi \circ p$. By Proposition 13.17, $\chi(p(0)) = 0$ and $R_t\, \chi(p(t)) = \mathbf{x}(t)$, so
Lemma 13.14 gives $\chi(G_{\mathrm{fc}}) = \operatorname{shape}(\mathbf{x})$, the Gerver's sofa of
$\mathrm{toRomik}(D)$. By Theorem 13.13, $\mathrm{toRomik}(D) = P$. $\square$

## 13.6 Formal-conjectures' theorems

### Theorem 13.20 (formal-conjectures' theorems)

1. Gerver's system has exactly one solution.
2. Gerver's sofa $G_{\mathrm{fc}}$ is a moving sofa of formal-conjectures.
3. $\alpha_{\mathrm{fc}} = \lvert G_{\mathrm{fc}} \rvert$.
4. A moving sofa $S \subseteq \mathbb{E}^2$ of formal-conjectures has
   $\lvert S \rvert = \alpha_{\mathrm{fc}}$ if and only if $S = g(G_{\mathrm{fc}})$ for some
   $g \in \mathrm{E}(2)$.

*Lean: [`FormalConjectures.MovingSofa.GerversSofa.ABφθSpec.existsUnique`](../../Challenge.lean#L373),
[`FormalConjectures.MovingSofa.isMovingSofa_gerversSofa`](../../Challenge.lean#L756),
[`FormalConjectures.MovingSofa.sofaConstant_eq_volume_gerversSofa`](../../Challenge.lean#L760),
[`FormalConjectures.MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa`](../../Challenge.lean#L764).*

formal-conjectures marks (2) and (3) solved and (4) open. The Challenge leaves out its test lemmas
and its theorem `MovingSofa.sofaConstant_eq`, which states (3) inside formal-conjectures' `answer`
marker, a notation that Mathlib does not have.

*Proof.* The bridge carries Baek's theorems over. (1) is Theorem 13.13. For the others, fix a
solution $P$ of Romik's system in the box
([Theorem 1.1](README.md#theorem-11-gervers-sofa-is-well-defined),
[`Baek.gerver_params_exists`](../../Challenge.lean#L664)), and let $G$ be its Gerver's sofa. By
Theorem 13.19, $\chi(G_{\mathrm{fc}}) = G$, so $\lvert G_{\mathrm{fc}} \rvert = \lvert G \rvert$ by
Lemma 13.5. By [Theorem 1.2](README.md#theorem-12-optimality-baek-theorem-111), $G$ is a moving sofa
and every moving sofa has area at most $\lvert G \rvert$.

(2) $G = \operatorname{shape}(\mathbf{x}) \subseteq H_L$, so
$G_{\mathrm{fc}} = \chi^{-1}(G) \subseteq \chi^{-1}(H_L)$, and $\chi(G_{\mathrm{fc}}) = G$ is a
moving sofa. Theorem 13.9 gives a motion.

(3) By Theorem 13.10 and Theorem 1.2,
$\alpha_{\mathrm{fc}} = \alpha_{\max} = \lvert G \rvert = \lvert G_{\mathrm{fc}} \rvert$.

(4) If $\lvert S \rvert = \alpha_{\mathrm{fc}}$, then $\chi(S)$ is a moving sofa by Theorem 13.9,
of area $\lvert S \rvert = \lvert G \rvert$ by (3). By [Theorem 1.3](README.md#theorem-13-uniqueness)
(the uniqueness theorem) there are an angle $a$ and a vector $v$ with $R_a\, \chi(S) + v = G$. The
element $g_0 = \rho(a, v)$ of Lemma 13.6 has
$\chi(g_0(S)) = R_a\, \chi(S) + v = G = \chi(G_{\mathrm{fc}})$. As $\chi$ is injective,
$g_0(S) = G_{\mathrm{fc}}$, so $S = g_0^{-1}(G_{\mathrm{fc}})$. Conversely, if
$S = g(G_{\mathrm{fc}})$, then $\lvert S \rvert = \lvert G_{\mathrm{fc}} \rvert = \alpha_{\mathrm{fc}}$,
since $g$ preserves area (Lemma 13.6). $\square$

In (4) the isometry found is a rotation followed by a translation. formal-conjectures allows every
element of $\mathrm{E}(2)$, reflections included, which adds no new sets, since Gerver's sofa is
symmetric under the reflection in a vertical line. Figure 13.5 shows, for each of these proofs, the
theorems of the Challenge of Baek's entry that it uses.

![A diagram of the twelve theorems of the Challenge in three rows: Baek's five above, formal-conjectures' four in the middle, the bridge's three below. Arrows lead from a theorem to the theorems of formal-conjectures whose proofs in baek/Solution.lean use it: gerver_params_exists and gerver_sofa_optimal to the three theorems about Gerver's sofa, gerver_sofa_unique to the congruence theorem, isMovingSofa_iff to the first and the third of them, sofaConstant_eq to the second and the third, and gerversSofa_eq to all three; a dashed arrow leads from ABφθSpec.existsUnique, which defines Gerver's constants, to gerversSofa_eq. gerver_params_unique and gerver_sofa_area have no arrows](figures/13-bridge/dependencies.svg)

*Figure 13.5.* The twelve theorems of Baek's entry and the proofs of formal-conjectures' theorems
in its Solution, [`baek/Solution.lean`](../../baek/Solution.lean): an arrow leads from a theorem to each theorem whose proof
uses it. Baek's theorems (blue) come from the libraries
[`MovingSofaOptimality`](../../MovingSofaOptimality) and
[`MovingSofaUniqueness`](../../MovingSofaUniqueness), the bridge's (green) from
[`MovingSofaBridge`](../../MovingSofaBridge). The dashed arrow marks a definition:
`ABφθSpec.existsUnique` defines Gerver's constants, and so formal-conjectures' Gerver's sofa, of
which [`gerversSofa_eq`](../../MovingSofaBridge/GerverSofa.lean#L507) and the other three theorems
of the middle row speak. The uniqueness of Romik's parameters and the area bounds of Gerver's sofa
are not used.

In [`MovingSofaExtremal/Statements.lean`](../../MovingSofaExtremal/Statements.lean), as in [`baek/Solution.lean`](../../baek/Solution.lean), two private lemmas,
$\alpha_{\mathrm{fc}} = \lvert G \rvert$ and $\lvert G_{\mathrm{fc}} \rvert = \lvert G \rvert$,
carry (3), and the element $\rho$ of Lemma 13.6 turns the rotation and the translation of Theorem
1.3 into an element of $\mathrm{E}(2)$
([`MovingSofaBridge.realization_image_eq`](../../MovingSofaBridge/Motion.lean#L270)).

## 13.7 The Challenge, the Solution and Comparator

The repository has two Palomar entries, each with a Challenge that states its theorems with `sorry`
and a Solution that proves them. The certificate entry, at the root, states seventeen theorems in
[`Challenge.lean`](../../Challenge.lean): the twelve below, three on the stability of Gerver's sofa and
two about a certificate for Baek's upper bound; [`Solution.lean`](../../Solution.lean) proves them
through the certificate ([Results](../results.md)). Baek's entry, in [`baek/`](../../baek), states the
twelve in [`baek/Challenge.lean`](../../baek/Challenge.lean): Baek's five
([`Baek.gerver_params_exists`](../../Challenge.lean#L664),
[`Baek.gerver_params_unique`](../../Challenge.lean#L668),
[`Baek.gerver_sofa_area`](../../Challenge.lean#L674),
[`Baek.gerver_sofa_optimal`](../../Challenge.lean#L680),
[`Baek.gerver_sofa_unique`](../../Challenge.lean#L687)), the bridge's three, and formal-conjectures'
four. [`baek/Solution.lean`](../../baek/Solution.lean) proves them: it restates eleven, and the twelfth,
`ABφθSpec.existsUnique`, is proved in [`MovingSofaBridge/Defs.lean`](../../MovingSofaBridge/Defs.lean), which it
imports. Lake's Comparator, configured by [`comparator.json`](../../comparator.json) for the certificate
entry and by [`baek/comparator.json`](../../baek/comparator.json) for Baek's, checks in a sandbox that a
Solution proves exactly the statements of its Challenge, with no axioms beyond
[`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext),
[`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound)
and
[`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice).
The two entries are arranged in the same way.

Comparator compares the statements through the names of the constants they use: every constant that
a statement mentions must be the same, by name and by definition, in the environment of the
Challenge and in that of the Solution. The Challenge may import only Mathlib, so it carries its own
copies of the definitions, while the Solution imports the libraries. The shared definitions
therefore live once, in [`MovingSofaBridge/Defs.lean`](../../MovingSofaBridge/Defs.lean), in marked blocks: Baek's
core definitions, the definitions of the stability statements, and formal-conjectures' definitions
in two blocks.
[`scripts/sync_challenge_defs.py`](../../scripts/sync_challenge_defs.py) copies the four blocks verbatim
into [`Challenge.lean`](../../Challenge.lean), followed by the certificate's block of
[`MovingSofaExtremal/CertificateDefs.lean`](../../MovingSofaExtremal/CertificateDefs.lean), and all but the stability block into
[`baek/Challenge.lean`](../../baek/Challenge.lean); with `--check` it only compares them, as the CI does.
The bridge modules [`MovingSofaBridge.Motion`](../../MovingSofaBridge/Motion.lean) and
[`MovingSofaBridge.GerverSofa`](../../MovingSofaBridge/GerverSofa.lean) import
[`MovingSofaBridge.Defs`](../../MovingSofaBridge/Defs.lean) and state their theorems about its constants, such as
[`FormalConjectures.MovingSofa.gerversSofa`](../../Challenge.lean#L412) and
[`FormalConjectures.MovingSofa.sofaConstant`](../../Challenge.lean#L419). So the bridge speaks about
the very constants of the Challenges, not about copies of them. Baek's definitions in the Challenges
are copies of the library's: [`MovingSofaExtremal/Statements.lean`](../../MovingSofaExtremal/Statements.lean) proves that they agree for the certificate entry,
and [`baek/Solution.lean`](../../baek/Solution.lean) for Baek's ([`Baek.isMovingSofa_iff_lib`](../../baek/Solution.lean#L35), and
[`Baek.gerverSofa_eq_lib`](../../baek/Solution.lean#L58), which holds by definition).

Between formal-conjectures' two blocks the Challenges state
[`FormalConjectures.MovingSofa.GerversSofa.ABφθSpec.existsUnique`](../../Challenge.lean#L373),
because the second of them defines $A$, $B$, $\varphi$ and $\theta$ as the components of the solution
that this theorem provides. So [`MovingSofaBridge/Defs.lean`](../../MovingSofaBridge/Defs.lean) must prove the
theorem at that point, with a module that it imports,
[`MovingSofaBridge.RomikParams`](../../MovingSofaBridge/RomikParams.lean). That module cannot
mention [`FormalConjectures.MovingSofa.GerversSofa.ABφθSpec`](../../Challenge.lean#L362), which
[`MovingSofaBridge.Defs`](../../MovingSofaBridge/Defs.lean) defines only after importing it. So
[`MovingSofaBridge.GerverConstants.Spec`](../../MovingSofaBridge/GerverConstants.lean#L117) is a
word-for-word copy of it, and [`MovingSofaBridge.Defs`](../../MovingSofaBridge/Defs.lean) proves the theorem by
[`MovingSofaBridge.GerverConstants.spec_existsUnique`](../../MovingSofaBridge/RomikParams.lean#L345):
the two definitions are equal by unfolding. The restated definitions compile with this
repository's Lean v4.35.0-rc3; formal-conjectures pins v4.33.1.
