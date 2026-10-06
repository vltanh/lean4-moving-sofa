# 4. Balanced maximum sofas

[Contents](README.md) · [← 3. Monotone sofas, caps and niches](03-monotone.md) · [5. The rotation angle →](05-rotation-angle.md)

This chapter proves that for every rotation angle $\omega \in (0, \pi/2]$ a *balanced maximum sofa*
exists (Theorem 4.40; Baek, Theorem 3.5.6): a monotone sofa that has the largest area among the
moving sofas with rotation angle $\omega$, and whose cap is a limit of balanced polygon caps. It
follows Chapter 3 of Baek's paper, which makes rigorous a balancing argument of Gerver [3].
[Chapter 5](05-rotation-angle.md) uses the balance to show that a balanced maximum sofa of area at
least $2.2$ can turn through a full right angle, and Chapters [6](06-surface-area.md) and
[7](07-injectivity.md) use it to show that the sofa satisfies the injectivity condition.

The construction keeps only finitely many supporting hallways. For a finite set $\Theta$ of angles
in $(0, \omega)$ the sofa becomes a polygon, the difference of a *polygon cap* $K$ and a *polygon
niche* $\mathcal{N}_\Theta(K)$ (§4.3). A polygon cap that maximizes
$\mathcal{A}_\Theta(K) = \lvert K \rvert - \lvert \mathcal{N}_\Theta(K) \rvert$ is *balanced*
(Theorem 4.31): for every normal angle $t$, the side of the cap with outer normal $u_t$ is as long as
the lower boundary of the sofa on the parallel line at distance one. Otherwise pushing one hallway
would increase the area. Gerver ran this argument on the polygon sofa itself, where pushing a
hallway can disconnect the sofa (§4.1). Baek runs it on the cap and lets the niche stick out of the
cap. The hallway is pushed only in the direction that enlarges the cap, and the pushed cap is a
translate of a polygon cap, on which $\mathcal{A}_\Theta$ takes the same value (§4.4). Balance then
shows that the niche does not stick out after all: its boundary is made of the sides of the upper
boundary of the cap, in another order (Theorem 4.32). As $\Theta$ becomes dense in $(0, \omega)$,
the maximum polygon caps converge to a cap that contains its niche and maximizes the sofa area
functional $\mathcal{A}_\omega$ (Theorems 4.37 and 4.38).

The notation is that of Chapters [2](02-preliminaries.md) and [3](03-monotone.md):

- the lines $l(t, h) = \lbrace p : \langle p, u_t \rangle = h \rbrace$ and the closed and open
  half-planes $H_\pm(t, h)$, $H^\circ_\pm(t, h)$ that they bound
  ([Definition 2.2](02-preliminaries.md#definition-22-lines-and-half-planes-baek-definitions-214-and-215));
- the strips $H$ and $V_\omega$, the parallelogram $P_\omega = H \cap V_\omega$ with corners
  $O = (0, 0)$ and $o_\omega = (\tan(\pi/4 - \omega/2), 1)$
  ([Definition 2.13](02-preliminaries.md#definition-213-strips-and-the-parallelogram-baek-definitions-232-and-235)),
  and the fan $F_\omega = H_+(\omega, 0) \cap H_+(\pi/2, 0)$
  ([Definition 3.11](03-monotone.md#definition-311-fan-and-niche-baek-definitions-244-and-245));
- the space $\mathcal{K}^\mathrm{c}_\omega$ of caps
  ([Definition 3.9](03-monotone.md#definition-39-cap-baek-definitions-241-and-242)), the cap
  $\mathcal{C}(S)$ of a sofa $S$
  ([Theorem 3.10](03-monotone.md#theorem-310-the-cap-of-a-moving-sofa-baek-theorem-241)) and, for a
  cap $K$, its supporting hallways $L_K(t) = Q^+_K(t) \setminus Q^-_K(t)$ with the quarter-planes
  $Q^+_K(t) = H_-(t, h_K(t)) \cap H_-(t + \pi/2, h_K(t + \pi/2))$ and
  $Q^-_K(t) = H^\circ_-(t, h_K(t) - 1) \cap H^\circ_-(t + \pi/2, h_K(t + \pi/2) - 1)$, the outer walls
  $a_K(t) = l(t, h_K(t))$ and $c_K(t)$, the inner walls $b_K(t) = l(t, h_K(t) - 1)$ and $d_K(t)$, and
  the inner corner $\mathbf{x}_K(t)$
  ([Proposition 2.19](02-preliminaries.md#proposition-219-the-parts-of-the-supporting-hallway-baek-proposition-222));
- the vertices $A^\pm_K(t)$, $C^\pm_K(t)$ and the upper boundary $\delta K$
  ([Definition 3.15](03-monotone.md#definition-315-vertices-and-upper-boundary-baek-definitions-251-and-252)),
  and the wedges $T_K(t) = F_\omega \cap Q^-_K(t)$ with their ends $W_K(t)$, $Z_K(t)$ and gaps
  $w_K(t), z_K(t) > 0$
  ([Definition 3.18](03-monotone.md#definition-318-wedges-their-ends-and-gaps-baek-definitions-253255),
  [Theorem 3.22](03-monotone.md#theorem-322-the-wedge-gaps-are-positive-baek-theorem-255));
- the niche $\mathcal{N}(K) = F_\omega \cap \bigcup_{t \in (0, \omega)} Q^-_K(t)$, the sofa area
  functional $\mathcal{A}_\omega(K) = \lvert K \rvert - \lvert \mathcal{N}(K) \rvert$
  ([Definition 3.28](03-monotone.md#definition-328-sofa-area-functional-baek-definition-258)), and
  the mirror image $K^\mathrm{m} = M_\omega(K)$
  ([Definition 3.20](03-monotone.md#definition-320-mirror-reflection-baek-definition-256));
- the edge $e_K(t)$ of a convex body $K$ with outer normal $u_t$
  ([Definition 2.8](02-preliminaries.md#definition-28-edges-and-vertices-baek-definitions-219-2110-and-2114)),
  and its length $\sigma_K(t) = \sigma_K(\lbrace t \rbrace)$, an atom of the surface area measure
  $\sigma_K$ of [Chapter 6](06-surface-area.md)
  ([Proposition 6.10](06-surface-area.md#proposition-610-atoms-baek-proposition-212)).

## 4.1 Gerver's balancing argument and its gap

Gerver's Theorem 1 [3], quoted in Baek's paper as Theorem 1.3.1, states the following. There are an
angle $\gamma \in [\pi/3, \pi/2]$ and a region $S$ that moves around the corner of $L$ rotating
through $\gamma$, such that no region of larger area moves around the corner, and such that for
arbitrarily large $n$ the region $S$ is approximated arbitrarily closely by a polygon $P_n$ with a
*balanced* boundary: for any two parallel lines at distance one, the sides of $P_n$ on the two
lines have the same total length. Each $P_n$ is the intersection of the half-strip $H_L$, a
translate of $V_L$ rotated by $\gamma$, and translates of the hallway $L$ rotated by $k\gamma/n$ for
$0 < k < n$. The theorem is not formalized as stated. Baek reproves its content as Theorems 4.31 and
4.40 and
[Theorem 5.1](05-rotation-angle.md#theorem-51-a-first-bound-on-the-rotation-angle-baek-theorem-151),
and these are formalized.

Fix $\omega \in (0, \pi/2]$ and a finite set $\Theta \subset (0, \omega)$. The *polygon sofa*

```math
S_\Theta = H \cap V_\omega \cap \bigcap_{t \in \Theta} L_t
```

is the part of $P_\omega$ that lies in the hallways $L_t = \mathbf{x}(t) + R_t L$, each turned by
$t$ and translated so that its inner corner is $\mathbf{x}(t)$ (Figure 4.1). The discrete problem
asks for the inner corners that maximize $\lvert S_\Theta \rvert$. Gerver's idea is that a maximizer
is balanced.

![A horizontal strip H between two thick grey lines, and two hallways turned by pi/6 (green walls) and pi/3 (purple walls), each drawn as its two outer walls meeting at an outer corner above the strip and its two inner walls meeting at an inner corner inside the strip. The blue polygon sofa is the part of the strip inside both hallways: a long hexagon-like region with a notch in its lower side below the two inner corners x(pi/3) and x(pi/6)](figures/04-balanced/polygon-sofa.svg)

*Figure 4.1.* The polygon sofa $S_\Theta$ (blue) for $\Theta = \lbrace \pi/6, \pi/3 \rbrace$ and
$\omega = \pi/2$, where $V_\omega = H$: the part of the strip $H$ in the hallways $L_{\pi/6}$
(green) and $L_{\pi/3}$ (purple). Its notch is cut out by the inner corners $\mathbf{x}(\pi/6)$ and
$\mathbf{x}(\pi/3)$. This is the maximum polygon sofa for this angle set, computed numerically; its
area is $2.5154$.

**The balancing argument.** Suppose that a maximizer $S_\Theta$ is not balanced: two parallel lines
$l^+$ and $l^-$ at distance one carry sides of $S_\Theta$ of total lengths $s^+ > s^-$. The two lines
are the walls of one strip $X$ of width one: $H$, $V_\omega$, or one arm of a hallway $L_t$.
Translate $X$ by $\varepsilon$ towards $l^+$; if $X$ is $H$ or $V_\omega$, translate the whole
configuration back afterwards. The sofa gains a strip of area $\varepsilon s^+ + O(\varepsilon^2)$
along $l^+$ and loses one of area $\varepsilon s^- + O(\varepsilon^2)$ along $l^-$ (Figure 4.2). So
its area grows by $\varepsilon(s^+ - s^-) + O(\varepsilon^2) > 0$ for small $\varepsilon$, which
contradicts the maximality.

![The polygon sofa of Gerver's example with c = 0.1, in blue, between the lines y = 0 and y = 1. Its right side, thick green, lies on the outer wall of the hallway turned by pi/6; a thick orange side, the right side of the notch in its lower boundary, lies on the inner wall of the same hallway. An arrow eps u points outwards from the green side. Dashed lines show both walls pushed by epsilon; a thin green strip along the right side is gained and a thin orange strip along the orange side is lost](figures/04-balanced/balancing-move.svg)

*Figure 4.2.* The balancing move. The side $s^+$ of the polygon sofa on the outer wall of
$L_{\pi/6}$ (thick green, length $1.1547$) is longer than its side $s^-$ on the inner wall (thick
orange, length $0.7614$). Pushing the hallway by $\varepsilon u$ with $u = u_{\pi/6}$ moves both walls
to the dashed lines: the sofa gains the green strip and loses the orange one, and its area grows by
$\varepsilon (s^+ - s^-) + O(\varepsilon^2)$. Here $\varepsilon = 0.1$, from $c = 0.1$ to $c = 0$ in
the example below.

**The gap.** A moving sofa is connected, so the maximum should be taken over connected polygon
sofas. The balancing move can disconnect $S_\Theta$, so a maximizer over connected polygon sofas
need not be balanced. Baek's example (overview, §1.4) takes $\omega = \pi/2$,
$\Theta = \lbrace \pi/6, \pi/3 \rbrace$, $u = u_{\pi/6}$, $\mathbf{x}(\pi/3) = (-0.9, 0.98)$ and
$\mathbf{x}(\pi/6) = (0, 1) - c\,u$. For every $c \in [0, 0.1]$ the side of $S_\Theta$ with outer
normal $u$ is longer than its sides with outer normal $-u$, so the argument pushes $L_{\pi/6}$ along
$u$ and decreases $c$. At $c = 0$ the inner corner $\mathbf{x}(\pi/6)$ reaches the top line $y = 1$.
For $c < 0$ the quadrant below it cuts the strip, and $S_\Theta$ falls into two pieces
(Figure 4.3). Another pair of sides could be balanced instead, keeping $S_\Theta$ connected, but
Gerver's proof makes no such choice.

![Three rows, for c = 0.1, 0 and -0.2, each showing the strip between y = 0 and y = 1 with the blue polygon sofa of Gerver's example, its side on the outer wall of the pi/6 hallway in thick green, its side on the inner wall in thick orange, the inner corner of that hallway as an orange dot with short dashed walls, and the quadrant below the inner corner shaded light orange. In the first row the corner is below the top line, in the second it touches it, and in the third it lies above the top line and the shaded quadrant cuts the sofa into two pieces](figures/04-balanced/disconnect.svg)

*Figure 4.3.* Gerver's example for $c = 0.1$, $0$ and $-0.2$. The green side, on the outer wall of
$L_{\pi/6}$, is longer than the orange sides, on its inner wall, so balancing pushes $L_{\pi/6}$
along $u$. The inner corner (orange dot) rises to the line $y = 1$; once it is above, the quadrant
below it (light orange) cuts $S_\Theta$ in two.

Baek's remedy is to allow the disconnected configurations and to prove connectedness afterwards.
Write $S_\Theta = K \setminus \mathcal{N}_\Theta(K)$ with a polygon cap $K$ and its polygon niche,
and maximize $\mathcal{A}_\Theta(K) = \lvert K \rvert - \lvert \mathcal{N}_\Theta(K) \rvert$ over all
polygon caps, also those whose niche is not contained in the cap, like $c = -0.2$ in Figure 4.3. A
maximizer is balanced (Theorem 4.31), and balance forces $\mathcal{N}_\Theta(K) \subseteq K$
(Theorem 4.32), so that $S_\Theta$ is connected after all.

## 4.2 Simple Nef polygons

When one of the half-planes that cut out a region is pushed, the area of the region changes at a
rate equal to the length of its boundary on the moving line. This section proves this for the
regions that occur, the simple Nef polygons.

### Definition 4.1 (Nef polygons; Baek, Definitions 3.1.1–3.1.4)

An $n$-ary *boolean function* is a map $\mathcal{E} : \lbrace \mathsf{true}, \mathsf{false} \rbrace^n
\to \lbrace \mathsf{true}, \mathsf{false} \rbrace$; it is *monotone* if $\mathcal{E}(P_1, \dots, P_n)$
implies $\mathcal{E}(Q_1, \dots, Q_n)$ whenever $P_i$ implies $Q_i$ for every $i$. For half-planes
$H_1, \dots, H_n$ (closed or open), the *Nef polygon*

```math
\mathcal{E}(H_1, \dots, H_n) = \lbrace p \in \mathbb{R}^2 : \mathcal{E}(p \in H_1, \dots, p \in H_n) \rbrace
```

is a *simple Nef polygon* with *defining half-planes* $H_1, \dots, H_n$ if $\mathcal{E}$ is monotone
and the boundary lines of the $H_i$ are pairwise different.

*Lean: [`BoolFun`](../../MovingSofaOptimality/Balanced/NefPolygon.lean#L21), [`BoolFun.IsMonotone`](../../MovingSofaOptimality/Balanced/NefPolygon.lean#L24), [`nefPolygon`](../../MovingSofaOptimality/Balanced/NefPolygon.lean#L56), [`HalfPlaneData`](../../MovingSofaOptimality/Balanced/NefPolygon.lean#L61), [`IsSimpleNefPolygon`](../../MovingSofaOptimality/Balanced/NefPolygon.lean#L80).*

A line is a Nef polygon, the intersection of the two closed half-planes it bounds, but not a simple
one: the two half-planes have the same boundary. In a simple Nef polygon $X$, monotonicity says that
if $p \in X$ and $q$ lies in every defining half-plane that contains $p$, then $q \in X$.

### Proposition 4.2 (monotone boolean functions; Baek, Proposition 3.1.1)

A boolean function obtained from the variables $P_1, \dots, P_n$ by conjunctions and disjunctions is
monotone.

*Proof.* Each variable is monotone, and conjunctions and disjunctions of monotone functions are
monotone. The Lean proof is an induction on the expression. $\square$

*Lean: [`proposition3_1_1`](../../MovingSofaOptimality/Balanced/NefPolygon.lean#L41), [`PosBoolExpr`](../../MovingSofaOptimality/Balanced/NefPolygon.lean#L28).*

### Theorem 4.3 (pushing a half-plane; Baek, Theorem 3.1.2)

Let $X = \mathcal{E}(H_1, \dots, H_n)$ be a bounded simple Nef polygon whose defining half-planes are
$H_i = H_-(t_i, h_i)$ or $H^\circ_-(t_i, h_i)$, with boundaries $l_i = l(t_i, h_i)$, and fix $i$. Let
$X'_\delta$ be $X$ with $H_i$ replaced by $H_-(t_i, h_i + \delta)$, or by $H^\circ_-(t_i, h_i + \delta)$
if $H_i$ is open. There are $\varepsilon > 0$ and $C$ such that for $\lvert \delta \rvert \le \varepsilon$

```math
\Bigl\lvert\, \lvert X'_\delta \rvert - \lvert X \rvert - \mathcal{H}^1(\partial X \cap l_i)\, \delta \,\Bigr\rvert \le C \delta^2 .
```

*Lean: [`theorem3_1_2`](../../MovingSofaOptimality/Balanced/NefPolygon.lean#L697).*

The paper leaves out that $X$ is bounded; without it the areas can be infinite, as for a
half-plane, and the statement fails (REPORT.md, Section 4). Every application, to the polygon caps
and niches, is to bounded sets. Here $\mathcal{H}^1$ is the length along a line
([`lineLength`](../../MovingSofaOptimality/Basic/Plane.lean#L78)).

*Proof sketch.* The area gained or lost lies in a thin strip along $l_i$, and its slices parallel to
$l_i$ have a length that varies Lipschitz-continuously. Take $\delta \ge 0$; the case $\delta \le 0$
is symmetric. Let $Y$ be the set of points $p$ at which $\mathcal{E}$ is true when its $i$-th argument
is set to true, and false when it is set to false: at these points, and only there, membership in
$X$ is decided by $H_i$. Since $\mathcal{E}$ is monotone, $X \subseteq X'_\delta$, and the added
points are the points of $Y$ in the strip between $l_i$ and $l(t_i, h_i + \delta)$. By Cavalieri's
principle in the frame $(u_{t_i}, v_{t_i})$,

```math
\lvert X'_\delta \rvert - \lvert X \rvert = \int_{h_i}^{h_i + \delta} g(s)\, ds , \qquad g(s) = \mathcal{H}^1\bigl(Y \cap l(t_i, s)\bigr) .
```

The other boundary lines differ from $l_i$. Those parallel to $l_i$ stay away from $l(t_i, s)$ for
$s$ near $h_i$, and the others cross $l(t_i, s)$ at points that move linearly with $s$. So
$g$ is Lipschitz near $h_i$. Finally $g(h_i) = \mathcal{H}^1(\partial X \cap l_i)$, because a point
of $l_i$ on no other boundary line is a boundary point of $X$ exactly when it lies in $Y$. Hence
$\lvert X'_\delta \rvert - \lvert X \rvert = g(h_i)\, \delta + O(\delta^2)$. The paper argues instead
with the regions cut out by the other boundary lines: in each region $X$ is empty, everything, or
the half-plane $H_i$, since monotonicity excludes its complement. The full proof is in
[`MovingSofaOptimality/Balanced/NefPolygon.lean`](../../MovingSofaOptimality/Balanced/NefPolygon.lean). $\square$

## 4.3 Polygon caps and polygon niches

### Definition 4.4 (angle sets; Baek, Definitions 3.2.1–3.2.2)

An *angle set* $\Theta$ with *rotation angle* $\omega \in (0, \pi/2]$ is a nonempty finite subset
of $(0, \omega)$, together with $\omega$. Its *angle domain* is

```math
\Theta^\diamond = \Theta \cup (\Theta + \pi/2) \cup \lbrace \omega, \pi/2 \rbrace \subset (0, \pi) .
```

*Lean: [`AngleSet`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L26), [`AngleSet.diamond`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L34).*

### Definition 4.5 (polygon caps; Baek, Definitions 3.2.3–3.2.4)

The *polygon caps* with angle set $\Theta$ are the caps $K \in \mathcal{K}^\mathrm{c}_\omega$ that
are intersections of closed half-planes with normal angles in
$\Theta^\diamond \cup \lbrace \omega + \pi, 3\pi/2 \rbrace$; they form the space
$\mathcal{K}^\mathrm{c}_\Theta$. For a cap $K$ with rotation angle $\omega$,

```math
\mathcal{C}_\Theta(K) = P_\omega \cap \bigcap_{t \in \Theta} Q^+_K(t) .
```

*Lean: [`IsPolygonCap`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L43), [`AngleSet.capAngles`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L38), [`polyCap`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L48).*

A polygon cap $K$ is the intersection of its supporting half-planes $H_K(s)$,
$s \in \Theta^\diamond \cup \lbrace \omega + \pi, 3\pi/2 \rbrace$: each defining half-plane with
normal angle $s$ contains $H_K(s)$, and $K$ lies in every $H_K(s)$. The proofs below use this
repeatedly.

### Proposition 4.6 (the approximating polygon cap; Baek, Proposition 3.2.1)

For every cap $K$ with rotation angle $\omega$, $\mathcal{C}_\Theta(K)$ is a polygon cap with angle
set $\Theta$ that contains $K$, and $\mathcal{C}_\Theta(K) = K$ if $K \in \mathcal{K}^\mathrm{c}_\Theta$.
So $\mathcal{C}_\Theta : \mathcal{K}^\mathrm{c}_\omega \to \mathcal{K}^\mathrm{c}_\Theta$ is onto.

*Proof.* $K$ lies in $P_\omega$ and in its supporting half-planes, so $K \subseteq \mathcal{C}_\Theta(K)
\subseteq P_\omega$. Since $P_\omega = H_-(\pi/2, 1) \cap H_-(3\pi/2, 0) \cap H_-(\omega, 1) \cap
H_-(\omega + \pi, 0)$, the set $\mathcal{C}_\Theta(K)$ is an intersection of closed half-planes with
normal angles in $\Theta^\diamond \cup \lbrace \omega + \pi, 3\pi/2 \rbrace$. It is bounded, also
for $\omega = \pi/2$, where $H_K(t)$ and $H_K(t + \pi/2)$, $t \in \Theta$, cut the strip $P_\omega$ on
the right and on the left. It lies between $K$ and $P_\omega$, which both have the support values
$1, 1, 0, 0$ at $\omega, \pi/2, \omega + \pi, 3\pi/2$, so it has them too, and it is a cap. If $K$ is a
polygon cap, it is the intersection of its supporting half-planes at these normal angles, and those
at $\omega$, $\pi/2$, $\omega + \pi$, $3\pi/2$ are the half-planes of $P_\omega$. So
$K = \mathcal{C}_\Theta(K)$. $\square$

*Lean: [`proposition3_2_1`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L314), [`proposition3_2_1_fix`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L329).*

### Definition 4.7 (polygon niche and polygon area functional; Baek, Definitions 3.2.5–3.2.6)

For a cap $K$ with rotation angle $\omega$, the *polygon niche* and the *polygon sofa area
functional* are

```math
\mathcal{N}_\Theta(K) = F_\omega \cap \bigcup_{t \in \Theta} Q^-_K(t) , \qquad \mathcal{A}_\Theta(K) = \lvert \mathcal{C}_\Theta(K) \rvert - \lvert \mathcal{N}_\Theta(K) \rvert .
```

*Lean: [`polyNiche`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L53), [`polyArea`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L58).*

Baek's Definition 3.2.5 writes the parallelogram $P_\omega$ where the fan $F_\omega$ is meant; the
rest of the paper uses $F_\omega$ (REPORT.md, E6). With $P_\omega$, Proposition 4.16 and Lemma 4.22
below are false. Figure 4.5 shows the caps that break Lemma 4.22.

![A polygon cap in blue with rotation angle 1.2 inside a dashed parallelogram, and the fan, the region above two dark half-lines from the origin O, one along the x-axis to the right and one up and to the left. Two inner corners x_K(0.4) and x_K(0.8), marked as orange dots above O, each with two dashed walls going down to the edge of the fan; the polygon niche, in orange, is the part of the fan below these walls, a small region around O inside the blue cap](figures/04-balanced/cap-niche.svg)

*Figure 4.4.* A polygon cap $K$ (blue) with $\omega = 1.2$ and $\Theta = \lbrace 0.4, 0.8 \rbrace$,
inside $P_\omega$ (dashed). Its polygon niche (orange) is the part of the fan $F_\omega$, above the
two dark half-lines from $O$, that lies below the walls $b_K(t)$ and $d_K(t)$ of the inner corners
$\mathbf{x}_K(0.4)$ and $\mathbf{x}_K(0.8)$. The cap is the maximum polygon cap for this angle set,
computed numerically.

![A long blue trapezoid K between the lines y = 0 and y = 1, from x = -1 to x = 9 at the bottom, and a large orange triangle standing on the x-axis with its apex x_K(pi/4) high above the strip. The part of the triangle inside the strip below the dashed line y = 1 is darker orange; the part above the dashed line is light orange with a dashed outline](figures/04-balanced/fan.svg)

*Figure 4.5.* Why the fan. The polygon cap $K = \lbrace 0 \le y \le 1,\ y - 1 \le x \le 9 - y \rbrace$
for $\omega = \pi/2$ and $\Theta = \lbrace \pi/4 \rbrace$ (blue) has area $9$. Its polygon niche, the
triangle below $\mathbf{x}_K(\pi/4) = (4, 5 - \sqrt2)$, has area $(5 - \sqrt2)^2 = 12.86$, so
$\mathcal{A}_\Theta(K) < 0$. The parallelogram $P_\omega$ is the strip below the dashed line, and it
keeps only the darker part of the triangle, of area $9 - 2\sqrt2$. With $P_\omega$ in place of
$F_\omega$, every cap $\lbrace 0 \le y \le 1,\ y - 1 \le x \le d + 1 - y \rbrace$ with $d \ge 2\sqrt2$
would have $\mathcal{A}_\Theta = (d + 1) - (d + 1 - 2\sqrt2) = 2\sqrt2 > 0$, and Lemma 4.22 would
fail; with $F_\omega$, $\mathcal{A}_\Theta = d + 1 - (d/2 + 1 - \sqrt2)^2$.

### Proposition 4.8 (polygon niches; Baek, Proposition 3.2.2)

For every cap $K$ with rotation angle $\omega$,
$\mathcal{N}_\Theta(K) = \mathcal{N}_\Theta(\mathcal{C}_\Theta(K)) \subseteq \mathcal{N}(K)$.

*Proof.* The polygon niche $\mathcal{N}_\Theta(K)$ depends only on $\omega$ and on the support values
of $K$ on $\Theta \cup (\Theta + \pi/2)$. The cap $\mathcal{C}_\Theta(K)$ has the same support values
there: the supporting lines of $K$ at these angles bound $\mathcal{C}_\Theta(K)$ and touch
$K \subseteq \mathcal{C}_\Theta(K)$. The inclusion holds because $\Theta \subseteq (0, \omega)$.
$\square$

*Lean: [`proposition3_2_2`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L338).*

### Theorem 4.9 (polygon upper bound; Baek, Theorem 3.2.3)

For a polygon cap $K \in \mathcal{K}^\mathrm{c}_\Theta$,
$\mathcal{A}_\Theta(K) = \lvert K \rvert - \lvert \mathcal{N}_\Theta(K) \rvert$. For every cap $K$ with
rotation angle $\omega$, $\mathcal{A}_\omega(K) \le \mathcal{A}_\Theta(K)$.

*Proof.* The first claim is $\mathcal{C}_\Theta(K) = K$ (Proposition 4.6). For the second,
$\lvert K \rvert \le \lvert \mathcal{C}_\Theta(K) \rvert$ by Proposition 4.6 and
$\lvert \mathcal{N}_\Theta(K) \rvert \le \lvert \mathcal{N}(K) \rvert$ by Proposition 4.8. $\square$

*Lean: [`theorem3_2_3`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L360), [`theorem3_2_3_le`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L366).*

So the maximum of $\mathcal{A}_\Theta$ over polygon caps bounds the area of every monotone sofa with
rotation angle $\omega$. Kallus and Romik's bound $2.37$ [5] essentially computes such a maximum for
a set of five angles (Baek's Remark 3.2.2).

## 4.4 Support values

A polygon cap is determined by its support values on $\Theta^\diamond$. Letting these values vary
freely gives a space in which a single side can be moved. The result need not be a cap, but it is
always a region cut out by half-planes.

### Definition 4.10 (cap translates and support values; Baek, Definitions 3.3.1–3.3.2)

$\mathcal{K}^\mathrm{t}_\Theta$ is the set of translates of the polygon caps with angle set
$\Theta$, and $\mathcal{H}_\Theta$ the space of functions $h : \Theta^\diamond \to \mathbb{R}$.

*Lean: [`IsPolygonCapTranslate`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L379).*

The formalization represents $h \in \mathcal{H}_\Theta$ by a function on $\mathbb{R}$ of which only
the values on $\Theta^\diamond$ are used.

### Proposition 4.11 (cap translates; Baek, Proposition 3.3.1)

A convex body $K'$ is in $\mathcal{K}^\mathrm{t}_\Theta$ if and only if (1) its widths
$h_{K'}(\omega) + h_{K'}(\omega + \pi)$ and $h_{K'}(\pi/2) + h_{K'}(3\pi/2)$ are both one, and (2) it is
an intersection of closed half-planes with normal angles in
$\Theta^\diamond \cup \lbrace \omega + \pi, 3\pi/2 \rbrace$.

*Proof.* Translates of polygon caps satisfy (1) and (2). Conversely, translate $K'$ by the vector $v$
with $\langle v, u_\omega \rangle = h_{K'}(\omega) - 1$ and $\langle v, u_{\pi/2} \rangle = h_{K'}(\pi/2) - 1$
(one condition if $\omega = \pi/2$). The translate $K' - v$ has support values $1$ at $\omega$ and
$\pi/2$, hence $0$ at $\omega + \pi$ and $3\pi/2$ by (1), and it is a polygon cap by (2). $\square$

*Lean: [`proposition3_3_1`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L423).*

Baek's statement asks in (2) for normal angles in $\Theta^\diamond$. No convex body is such an
intersection: since $\Theta^\diamond \subset (0, \pi)$, it would contain with each point every point
below it. The bottom normal angles $\omega + \pi$ and $3\pi/2$, which the paper's proof of
Proposition 4.12 uses, are meant (REPORT.md, E7).

### Proposition 4.12 (support values determine the cap; Baek, Proposition 3.3.2)

The map $\mathcal{K}^\mathrm{t}_\Theta \to \mathcal{H}_\Theta$, $K' \mapsto h_{K'}|_{\Theta^\diamond}$,
is injective.

*Proof.* By Proposition 4.11 (2), $K'$ is the intersection of its supporting half-planes with normal
angles in $\Theta^\diamond \cup \lbrace \omega + \pi, 3\pi/2 \rbrace$. By (1), its support values at
$\omega + \pi$ and $3\pi/2$ are $1 - h_{K'}(\omega)$ and $1 - h_{K'}(\pi/2)$. So

```math
K' = \bigcap_{t \in \Theta^\diamond} H_-(t, h_{K'}(t)) \cap \bigcap_{t \in \lbrace \omega, \pi/2 \rbrace} H_+(t, h_{K'}(t) - 1)
```

is determined by the values of $h_{K'}$ on $\Theta^\diamond$. $\square$

*Lean: [`proposition3_3_2`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L467).*

### Definition 4.13 (cap, niche and area of support values; Baek, Definition 3.3.3)

For $h \in \mathcal{H}_\Theta$, the parallelogram, cap, fan, niche and polygon sofa area functional
of $h$ are

```math
P_h = \bigcap_{t \in \lbrace \omega, \pi/2 \rbrace} H_-(t, h(t)) \cap H_+(t, h(t) - 1) , \qquad \mathcal{C}_\Theta(h) = P_h \cap \bigcap_{t \in \Theta \cup (\Theta + \pi/2)} H_-(t, h(t)) ,
```

```math
F_h = \bigcap_{t \in \lbrace \omega, \pi/2 \rbrace} H_+(t, h(t) - 1) , \qquad \mathcal{N}_\Theta(h) = F_h \cap \bigcup_{t \in \Theta} \Bigl( H^\circ_-(t, h(t) - 1) \cap H^\circ_-(t + \pi/2, h(t + \pi/2) - 1) \Bigr) ,
```

and $\mathcal{A}_\Theta(h) = \lvert \mathcal{C}_\Theta(h) \rvert - \lvert \mathcal{N}_\Theta(h) \rvert$.

*Lean: [`paraH`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L487), [`capH`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L491), [`fanH`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L496), [`nicheH`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L500), [`areaH`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L505).*

### Proposition 4.14 (Nef representations; Baek, Proposition 3.3.3)

For $h \in \mathcal{H}_\Theta$: (1) $\mathcal{C}_\Theta(h)$ is a simple Nef polygon with the defining
half-planes $H_-(t, h(t))$, $t \in \Theta^\diamond$, and $H_+(t, h(t) - 1)$, $t \in \lbrace \omega,
\pi/2 \rbrace$; (2) $\mathcal{N}_\Theta(h)$ is a simple Nef polygon with the defining half-planes
$H^\circ_-(t, h(t) - 1)$, $t \in \Theta \cup (\Theta + \pi/2)$, and $H_+(t, h(t) - 1)$,
$t \in \lbrace \omega, \pi/2 \rbrace$.

*Proof.* Both sets are built from these half-planes by intersections and unions, so the boolean
function is monotone (Proposition 4.2). The boundary lines differ. Lines with different normal
angles in $(0, \pi)$ differ, and $H_+(t, h(t) - 1) = H_-(t + \pi, 1 - h(t))$ is bounded by the line
$l(t, h(t) - 1)$, at distance one from $l(t, h(t))$. $\square$

*Lean: [`proposition3_3_3`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L742), [`capHalfPlanes`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L509), [`nicheHalfPlanes`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L515).*

### Proposition 4.15 (compatibility of caps; Baek, Proposition 3.3.4)

For $K' \in \mathcal{K}^\mathrm{t}_\Theta$, $\mathcal{C}_\Theta(h_{K'}) = K'$.

*Proof.* By Definition 4.13, $\mathcal{C}_\Theta(h_{K'})$ is the right-hand side of the formula for
$K'$ in the proof of Proposition 4.12. $\square$

*Lean: [`proposition3_3_4`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L808).*

### Proposition 4.16 (compatibility of niches; Baek, Proposition 3.3.5)

For $K \in \mathcal{K}^\mathrm{c}_\Theta$, $\mathcal{N}_\Theta(h_K) = \mathcal{N}_\Theta(K)$ and
$\mathcal{A}_\Theta(h_K) = \mathcal{A}_\Theta(K)$.

*Proof.* Since $h_K(\omega) = h_K(\pi/2) = 1$, the fan $F_{h_K}$ is $F_\omega$. The term with index
$t$ of the union in $\mathcal{N}_\Theta(h_K)$ is the quarter-plane $Q^-_K(t)$
([Proposition 2.19](02-preliminaries.md#proposition-219-the-parts-of-the-supporting-hallway-baek-proposition-222)).
So the niches agree. The areas agree because $\mathcal{C}_\Theta(h_K) = K$ (Proposition 4.15) and
$\mathcal{A}_\Theta(K) = \lvert K \rvert - \lvert \mathcal{N}_\Theta(K) \rvert$ (Theorem 4.9). $\square$

*Lean: [`proposition3_3_5`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L833).*

### Definition 4.17 (niches of cap translates; Baek, Definition 3.3.4)

For $K' \in \mathcal{K}^\mathrm{t}_\Theta$, $\mathcal{N}_\Theta(K') = \mathcal{N}_\Theta(h_{K'})$ and
$\mathcal{A}_\Theta(K') = \mathcal{A}_\Theta(h_{K'})$.

*Lean: [`nicheT`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L850), [`areaT`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L853).*

### Theorem 4.18 (translation invariance; Baek, Theorem 3.3.6)

For $K \in \mathcal{K}^\mathrm{c}_\Theta$ and $v \in \mathbb{R}^2$,
$\mathcal{N}_\Theta(K + v) = \mathcal{N}_\Theta(K) + v$ and
$\mathcal{A}_\Theta(K + v) = \mathcal{A}_\Theta(K)$. So Definition 4.17 extends Definition 4.7.

*Proof.* $h_{K+v}(t) = h_K(t) + \langle v, u_t \rangle$, so every defining half-plane of
$\mathcal{N}_\Theta(h_{K+v})$ is that of $\mathcal{N}_\Theta(h_K)$ translated by $v$, and the first
claim follows from Proposition 4.16. By Proposition 4.15 and the translation invariance of area,
$\mathcal{A}_\Theta(K + v) = \lvert K + v \rvert - \lvert \mathcal{N}_\Theta(K) + v \rvert =
\mathcal{A}_\Theta(K)$. $\square$

*Lean: [`theorem3_3_6`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L868).*

### Proposition 4.19 (reduction to a cap translate; Baek, Proposition 3.3.7)

Let $h^+ \in \mathcal{H}_\Theta$ be such that $K^+ = \mathcal{C}_\Theta(h^+)$ is in
$\mathcal{K}^\mathrm{t}_\Theta$. Then $\mathcal{A}_\Theta(h^+) \le \mathcal{A}_\Theta(K^+)$.

*Proof.* The lines of $h^+$ need not all touch $K^+$, so $h^+$ need not be the support function of
$K^+$. But $h_{K^+} \le h^+$ on $\Theta^\diamond$, because $K^+$ lies in the half-planes
$H_-(t, h^+(t))$. At $t \in \lbrace \omega, \pi/2 \rbrace$ equality holds: $K^+$ lies in the strip of
$P_{h^+}$ of width one in the direction $u_t$, and has width one in that direction
(Proposition 4.11), so it touches both lines of the strip. Hence $F_{h_{K^+}} = F_{h^+}$. The
quarter-planes of $h_{K^+}$ lie in those of $h^+$, so
$\mathcal{N}_\Theta(h_{K^+}) \subseteq \mathcal{N}_\Theta(h^+)$, while
$\mathcal{C}_\Theta(h_{K^+}) = K^+ = \mathcal{C}_\Theta(h^+)$ by Proposition 4.15. Subtracting the
areas gives the claim. $\square$

*Lean: [`proposition3_3_7`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L926).*

## 4.5 Maximum polygon caps

### Definition 4.20 (maximum polygon cap; Baek, Definition 3.4.1)

A *maximum polygon cap* with angle set $\Theta$ is a polygon cap $K_\Theta \in \mathcal{K}^\mathrm{c}_\Theta$
with $o_\omega \in K_\Theta$ that maximizes $\mathcal{A}_\Theta$ over $\mathcal{K}^\mathrm{c}_\Theta$.

*Lean: [`IsMaxPolygonCap`](../../MovingSofaOptimality/Balanced/MaxPolygonCapExists.lean#L44).*

For $\omega < \pi/2$ every cap contains $o_\omega$. For $\omega = \pi/2$ the caps can slide
horizontally, and the condition $o_\omega = (0, 1) \in K_\Theta$ keeps them from sliding away.

### Lemma 4.21 (mirror image; Baek, Lemma 3.4.1)

The mirror image $M_\omega(K_\Theta)$ of a maximum polygon cap with angle set $\Theta$ is a maximum
polygon cap with angle set $\omega - \Theta$.

*Proof.* By [Proposition 3.21](03-monotone.md#proposition-321-mirror-symmetry-baek-proposition-254),
$h_{K^\mathrm{m}}(t) = h_K(\omega + \pi/2 - t)$ and $T_{K^\mathrm{m}}(t) = M_\omega(T_K(\omega - t))$.
The map $t \mapsto \omega + \pi/2 - t$ takes $\Theta^\diamond$ onto $(\omega - \Theta)^\diamond$. So
$M_\omega$ maps the polygon caps with angle set $\Theta$ onto those with angle set $\omega - \Theta$,
and their polygon niches, the unions of the wedges, onto each other. It preserves areas and fixes
$o_\omega$. $\square$

*Lean: [`lemma3_4_1`](../../MovingSofaOptimality/Balanced/MaxPolygonCapExists.lean#L176), [`AngleSet.mirror`](../../MovingSofaOptimality/Balanced/MaxPolygonCapExists.lean#L48), [`mirrorCap`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L79).*

### Lemma 4.22 (bounded width; Baek, Lemma 3.4.2)

Let $\omega \in (0, \pi/2]$ and $t \in (0, \omega)$. There is $c_{\omega, t} > 0$ such that every
polygon cap $K$ with an angle set $\Theta \ni t$ of rotation angle $\omega$ and with
$\mathcal{A}_\Theta(K) > 0$ has width $h_K(0) + h_K(\pi) \le c_{\omega, t}$.

*Proof.* A long cap has a large wedge $T_K(t)$, whose area grows quadratically with the width,
while the area of the cap grows linearly. If $\omega < \pi/2$, then $K \subseteq P_\omega$, whose
width is $\sec \omega + \tan \omega$. Let $\omega = \pi/2$ and $d = h_K(0) + h_K(\pi)$. The cap lies
between the lines $y = 0$ and $y = 1$, so $\lvert K \rvert \le d$. The ends $A^-_K(0) = (h_K(0), 0)$
and $C^+_K(\pi/2) = (-h_K(\pi), 0)$ of the upper boundary lie in $K$
([Definition 3.15](03-monotone.md#definition-315-vertices-and-upper-boundary-baek-definitions-251-and-252)),
so $h_K(t) \ge h_K(0) \cos t$ and $h_K(t + \pi/2) \ge h_K(\pi) \sin t$. Hence the wall $b_K(t)$ meets
the $x$-axis at $W_K(t) = ((h_K(t) - 1)/\cos t, 0)$, with first coordinate at least
$h_K(0) - \sec t$, and the wall $d_K(t)$ meets it at $Z_K(t)$, with first coordinate at most
$-h_K(\pi) + \csc t$. Suppose that $L = d - \sec t - \csc t > 0$. Then the wedge $T_K(t)$ is the
triangle above the segment from $Z_K(t)$ to $W_K(t)$, of length at least $L$, with a right angle at
$\mathbf{x}_K(t)$ and the angles $t$ and $\pi/2 - t$ at its ends; its area is at least
$L^2 \sin(2t)/4$. As $T_K(t) \subseteq \mathcal{N}_\Theta(K)$, Theorem 4.9 gives

```math
\mathcal{A}_\Theta(K) \le d - \tfrac14 (d - \sec t - \csc t)^2 \sin 2t ,
```

which is negative for all large $d$. The Lean proof uses a rectangle inside the wedge instead of the
triangle. $\square$

*Lean: [`lemma3_4_2`](../../MovingSofaOptimality/Balanced/MaxPolygonCapExists.lean#L343).*

### Theorem 4.23 (existence of maximum polygon caps; Baek, Theorem 3.4.3)

For every angle set $\Theta$ a maximum polygon cap exists.

*Proof sketch.* As in the paper: $\mathcal{A}_\Theta$ is continuous in the Hausdorff distance, the
caps worth considering lie in one bounded box, and a maximizing sequence has a limit by the Blaschke
selection theorem.

1. *Continuity.* Area is continuous in the Hausdorff distance (Schneider, Theorem 1.8.20). The
   polygon niche $\mathcal{N}_\Theta(K)$ is the union of the wedges $T_K(t)$, $t \in \Theta$, as in
   Proposition 3.19, so
   $\lvert \lvert \mathcal{N}_\Theta(K') \rvert - \lvert \mathcal{N}_\Theta(K) \rvert \rvert$ is at
   most the sum over $t \in \Theta$ of the areas of the symmetric differences of $T_{K'}(t)$ and
   $T_K(t)$. In the coordinates $(\langle p, u_t \rangle, \langle p, v_t \rangle)$ each of them lies
   in two strips, of widths $2 \lvert h_{K'}(t) - h_K(t) \rvert$ and
   $2 \lvert h_{K'}(t + \pi/2) - h_K(t + \pi/2) \rvert$, cut off by a bounded square, so its area
   tends to $0$ as $K' \to K$.
2. *A bounded domain.* Let $K^{\mathbf 1} = \mathcal{C}_\Theta(\mathbf 1)$, where $\mathbf 1$ is the
   constant function $1$. It is a polygon cap that contains $o_\omega$ and the points $u_s$,
   $s \in \Theta^\diamond$. Its support values on $\Theta^\diamond$ are therefore all $1$, and its
   inner corners are all at $O$. Its niche is empty, because the open quarter-planes below $O$ miss
   $F_\omega$, so $\mathcal{A}_\Theta(K^{\mathbf 1}) = \lvert K^{\mathbf 1} \rvert > 0$. Let
   $\mathcal{B}_\Theta$ be the set of polygon caps $K \ni o_\omega$ with $\mathcal{A}_\Theta(K) > 0$.
   It contains $K^{\mathbf 1}$, and its members lie between $y = 0$ and $y = 1$ and have bounded
   width by Lemma 4.22, so they lie in one bounded box.
3. *The maximum on $\mathcal{B}_\Theta$.* Take a sequence $K_n$ in $\mathcal{B}_\Theta$ along which
   $\mathcal{A}_\Theta$ tends to its supremum on $\mathcal{B}_\Theta$. By the Blaschke selection
   theorem (Theorem 2.12), a subsequence converges to a convex body $L$. Its area is at least
   $\mathcal{A}_\Theta(K^{\mathbf 1}) > 0$, so it has an interior point $q$. A point $p$ that
   satisfies the constraints of $L$ with normal angles in
   $\Theta^\diamond \cup \lbrace \omega + \pi, 3\pi/2 \rbrace$ is a limit of points of the segment
   $(p, q]$, which lie in the late $K_n$, so $L$ is a polygon cap with angle set $\Theta$. It
   contains $o_\omega$, and $\mathcal{A}_\Theta(L)$ is the supremum, by continuity.
4. *Every polygon cap.* A polygon cap $K'$ with $\mathcal{A}_\Theta(K') \le 0$ is no better than
   $L$. If $\mathcal{A}_\Theta(K') > 0$, then $K' \in \mathcal{B}_\Theta$ when $\omega < \pi/2$, since
   $K'$ then contains $o_\omega$, and for $\omega = \pi/2$ a horizontal translate of $K'$ lies in
   $\mathcal{B}_\Theta$ and has the same value (Theorem 4.18). $\square$

*Lean: [`theorem3_4_3`](../../MovingSofaOptimality/Balanced/MaxPolygonCapExists.lean#L1164), [`mpc_tendsto_area_polyNiche`](../../MovingSofaOptimality/Balanced/MaxPolygonCapExists.lean#L1050), [`mpc_blaschke`](../../MovingSofaOptimality/Balanced/MaxPolygonCapExists.lean#L846).*

The paper requires only $\mathcal{A}_\Theta(K) \ge 0$ in $\mathcal{B}_\Theta$, while Lemma 4.22 needs
$\mathcal{A}_\Theta(K) > 0$, and it does not show that the limit is a polygon cap (REPORT.md, E8).

## 4.6 Balanced polygon caps

### Definition 4.24 (monotone polyline; Baek, Definition 3.4.2)

For points $p_1, \dots, p_n$ with strictly increasing $x$-coordinates, the union of the segments from
$p_i$ to $p_{i+1}$, $1 \le i < n$, is an *$x$-monotone polyline*.

*Lean: [`IsXMonotonePolyline`](../../MovingSofaOptimality/Balanced/Polyline.lean#L42).*

### Theorem 4.25 (the polyline; Baek, Theorem 3.4.4)

For a polygon cap $K \in \mathcal{K}^\mathrm{c}_\Theta$, the boundary of $F_\omega \setminus
\mathcal{N}_\Theta(K)$ is the disjoint union, from left to right, of

1. the open half-line $\vec l_K$ from $C^+_K(\omega)$ in the direction $v_\omega$, without
   $C^+_K(\omega)$;
2. an $x$-monotone polyline $\mathbf{p}_K$ from $C^+_K(\omega)$ to $A^-_K(0)$ whose segments have
   normal angles in $\Theta^\diamond$;
3. the open half-line $\vec r_K$ from $A^-_K(0)$ in the direction $u_0$, without $A^-_K(0)$.

*Lean: [`theorem3_4_4`](../../MovingSofaOptimality/Balanced/Polyline.lean#L436), [`polyline`](../../MovingSofaOptimality/Balanced/Polyline.lean#L55), [`rayLeft`](../../MovingSofaOptimality/Balanced/Polyline.lean#L47), [`rayRight`](../../MovingSofaOptimality/Balanced/Polyline.lean#L51).*

*Proof sketch.* Each quarter-plane $Q^-_K(t)$ is open, and closed in the direction $-v_0$: with a
point it contains every point below it
([Definition 3.11](03-monotone.md#definition-311-fan-and-niche-baek-definitions-244-and-245)). So
$F_\omega \setminus \mathcal{N}_\Theta(K)$ is the part of $F_\omega$ on or above the graph of

```math
G(x) = \max\Bigl(\text{bottom of } F_\omega \text{ at } x,\ \text{top of } \bigcup_{t \in \Theta} Q^-_K(t) \text{ at } x\Bigr) .
```

This is a continuous piecewise linear function. Its pieces lie on the lines $l(\pi/2, 0)$,
$l(\omega, 0)$, $b_K(t)$ and $d_K(t)$, $t \in \Theta$, whose normal angles $\pi/2$, $\omega$, $t$ and
$t + \pi/2$ lie in $\Theta^\diamond$. The half-line $\vec r_K$ avoids every $Q^-_K(t)$, because its
points lie to the right of $A^-_K(0)$, which lies to the right of $W_K(t)$ by the gap
$w_K(t) > 0$ ([Theorem 3.22](03-monotone.md#theorem-322-the-wedge-gaps-are-positive-baek-theorem-255)).
Likewise $\vec l_K$ avoids them, by $z_K(t) > 0$. So the graph of $G$ follows the bottom of
$F_\omega$ to the left of $C^+_K(\omega)$ and to the right of $A^-_K(0)$. Between these two points it
is the polyline $\mathbf{p}_K$, whose vertices are the sorted crossings of the walls. $\square$

### Definition 4.26 (balanced polygon cap; Baek, Definitions 3.4.3–3.4.5)

The polyline $\mathbf{p}_K$ of Theorem 4.25 is the *polyline* of $K \in \mathcal{K}^\mathrm{c}_\Theta$.
For $t \in \Theta^\diamond$, $\tau_K(t)$ is the total length of the segments of $\mathbf{p}_K$ with normal
angle $t$. The polygon cap $K$ is *balanced* if $\sigma_K(t) = \tau_K(t)$ for every
$t \in \Theta^\diamond$.

*Lean: [`polyline`](../../MovingSofaOptimality/Balanced/Polyline.lean#L55), [`MovingSofaOptimality.tau`](../../MovingSofaOptimality/Balanced/Polyline.lean#L478), [`IsBalanced`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L48), [`sigmaAt`](../../MovingSofaOptimality/Basic/SurfaceArea.lean#L172).*

The upper boundary $\delta K$ runs from $A^-_K(0)$ to $C^+_K(\omega)$ through sides of lengths
$\sigma_K(t)$, $t \in \Theta^\diamond$, and the polyline runs back below the sofa through segments
of total lengths $\tau_K(t)$ (Figure 4.6). The side of the cap with normal $u_t$ lies on the outer
wall of a hallway, or on the top of $H$ or $V_\omega$. The segments of the polyline with the same
normal angle lie on the parallel inner wall, or on the bottom of $F_\omega$ for
$t \in \lbrace \omega, \pi/2 \rbrace$. So balance is Gerver's condition of §4.1.

![A polygon sofa in light grey with rotation angle 1.2, between its endpoints C on the left and A on the right, marked as black dots, with two dashed grey half-lines continuing from them along the bottom of the fan. The six sides of the upper boundary are drawn thick, each in its own colour and labelled sigma 1 to sigma 6; the six segments of the polyline below the sofa, which goes down along the lower left side, up and down around the niche and along the x-axis to A, are drawn thick in the same colours and labelled tau 1 to tau 6. Each tau segment has the colour and the length of the sigma side with the same index](figures/04-balanced/balanced.svg)

*Figure 4.6.* Balanced side lengths, for the maximum polygon cap of Figure 4.4. The sides
$\sigma_1, \dots, \sigma_6$ of the upper boundary have the normal angles $0.4$, $0.8$, $\omega$,
$\pi/2$, $0.4 + \pi/2$, $0.8 + \pi/2$; the polyline from $C^+_K(\omega)$ to $A^-_K(0)$ (thick, below
the sofa) has segments $\tau_1, \dots, \tau_6$ with the same normal angles, coloured alike. Here
each side has the length of the segment of its colour, so the polyline is a rearrangement of the
upper boundary.

### Lemma 4.27 (sides of the polygon niche; Baek, Lemma 3.4.5)

Let $K \in \mathcal{K}^\mathrm{c}_\Theta$.

1. For $t \in \Theta$, the boundary of $\mathcal{N}_\Theta(K)$ has length $\tau_K(t)$ on $b_K(t)$, all
   of it on the half-line $\vec b_K(t)$, and length $\tau_K(t + \pi/2)$ on $d_K(t)$, all of it on
   $\vec d_K(t)$.
2. For $t \in \lbrace \omega, \pi/2 \rbrace$,
   $\mathcal{H}^1(\partial \mathcal{N}_\Theta(K) \cap l(t, 0)) = \mathcal{H}^1(\mathcal{N}_\Theta(K) \cap l(t, 0)) = \sigma_K(t + \pi) - \tau_K(t)$.

*Lean: [`lemma3_4_5_one`](../../MovingSofaOptimality/Balanced/Polyline.lean#L999), [`lemma3_4_5_two`](../../MovingSofaOptimality/Balanced/Polyline.lean#L1040).*

*Proof sketch.* By Theorem 4.25, the boundary of $\mathcal{N}_\Theta(K)$ consists of the pieces of
the polyline inside the open fan, which lie on the walls, the part of $\partial F_\omega$ covered by
the niche, and finitely many points. (1) For $t \in \Theta$, the only line among the walls and the
bottom of $F_\omega$ with normal angle $t$ is $b_K(t)$, and the only one with normal angle
$t + \pi/2$ is $d_K(t)$. The pieces on these lines lie on the half-lines that bound $Q^-_K(t)$.
(2) The bottom side $e_K(t + \pi)$ of $K$, of length $\sigma_K(t + \pi)$, lies on $l(t, 0)$. The
polyline covers the part of it outside the niche, of length $\tau_K(t)$, and the niche covers the
rest. $\square$

### Lemma 4.28 (an unbalanced cap has a long side; Baek, Lemma 3.4.6)

If $K \in \mathcal{K}^\mathrm{c}_\Theta$ is not balanced, then $\sigma_K(t) > \tau_K(t)$ for some
$t \in \Theta^\diamond$.

*Proof.* Walk from $A^-_K(0)$ to $C^+_K(\omega)$ along the polyline, and along the upper boundary of
$K$; each segment or side with normal angle $t$ is traversed in the direction $v_t$. So

```math
C^+_K(\omega) - A^-_K(0) = \sum_{t \in \Theta^\diamond} \tau_K(t)\, v_t = \sum_{t \in \Theta^\diamond} \sigma_K(t)\, v_t .
```

Take the inner product with $u_0$. As $\langle v_t, u_0 \rangle = -\sin t < 0$ on $(0, \pi)$, this
gives $\sum_{t} (\tau_K(t) - \sigma_K(t)) \sin t = 0$. If $\sigma_K \le \tau_K$ everywhere, every term
is nonnegative, so every term vanishes and $K$ is balanced. $\square$

*Lean: [`lemma3_4_6`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L52), [`mpc_walk`](../../MovingSofaOptimality/Balanced/CapGeometry.lean#L658).*

### Lemma 4.29 (the balancing step; Baek, Lemma 3.4.7)

Let $K \in \mathcal{K}^\mathrm{c}_\Theta$, $h = h_K$, and $t \in \Theta^\diamond$, and let $h^+$ agree
with $h$ except $h^+(t) = h(t) + \varepsilon$. There are $\varepsilon_0 > 0$ and $C$ such that for
$0 < \varepsilon \le \varepsilon_0$

```math
\Bigl\lvert\, \mathcal{A}_\Theta(h^+) - \mathcal{A}_\Theta(h) - \bigl(\sigma_K(t) - \tau_K(t)\bigr)\, \varepsilon \,\Bigr\rvert \le C \varepsilon^2 .
```

*Proof.* Theorem 4.3 applies to the bounded simple Nef polygons $\mathcal{C}_\Theta(h) = K$ and
$\mathcal{N}_\Theta(h) = \mathcal{N}_\Theta(K)$ (Propositions 4.14 to 4.16). Figure 4.2 shows the
analogous move on the polygon sofa.

Suppose first that $t \notin \lbrace \omega, \pi/2 \rbrace$. Then $h^+$ moves one defining half-plane
of each. Theorem 4.3 for $K$ and its half-plane $H_-(t, h(t))$, whose line meets $\partial K$ in the
side $e_K(t)$, gives
$\lvert \mathcal{C}_\Theta(h^+) \rvert = \lvert K \rvert + \sigma_K(t)\, \varepsilon + O(\varepsilon^2)$.
Theorem 4.3 for $\mathcal{N}_\Theta(h)$ and its half-plane $H^\circ_-(t, h(t) - 1)$, with
Lemma 4.27 (1), gives
$\lvert \mathcal{N}_\Theta(h^+) \rvert = \lvert \mathcal{N}_\Theta(h) \rvert + \tau_K(t)\, \varepsilon + O(\varepsilon^2)$.
Subtract.

Now let $t \in \lbrace \omega, \pi/2 \rbrace$. Then the whole strip of $P_h$ in the direction $u_t$
moves by $\varepsilon$: both $H_-(t, h(t))$ and the bottom half-plane $H_+(t, h(t) - 1)$ move. For
$\varepsilon < 1$ the two moves change disjoint strips, along $l(t, h(t))$ and along $l(t, 0)$, and in
each strip the other move changes nothing. So the change of $\lvert \mathcal{C}_\Theta \rvert$ is the
sum of the changes caused by each move made alone on $K$, and Theorem 4.3 applies to each:
$\lvert \mathcal{C}_\Theta(h^+) \rvert = \lvert K \rvert + (\sigma_K(t) - \sigma_K(t + \pi))\,\varepsilon +
O(\varepsilon^2)$. In the niche only the fan half-plane $H_+(t, h(t) - 1)$ moves, and the niche loses
the strip along $l(t, 0)$. So by Lemma 4.27 (2)
$\lvert \mathcal{N}_\Theta(h^+) \rvert = \lvert \mathcal{N}_\Theta(h) \rvert - (\sigma_K(t + \pi) -
\tau_K(t))\,\varepsilon + O(\varepsilon^2)$. Subtract again. $\square$

*Lean: [`lemma3_4_7`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L570).*

The paper's proof prints the change of $\lvert \mathcal{N}_\Theta \rvert$ in the second case with the
opposite sign (REPORT.md, E27). It also applies Theorem 4.3 twice in a row, the second time to a
polygon that the first application has changed. The disjointness of the two strips justifies this,
as above (REPORT.md, E5).

### Lemma 4.30 (the pushed cap is a translate; Baek, Lemma 3.4.8)

Let $K \in \mathcal{K}^\mathrm{c}_\Theta$ and $t \in \Theta^\diamond$ with $\sigma_K(t) > 0$, and let $h^+$
be as in Lemma 4.29. For all small $\varepsilon > 0$, $K^+ = \mathcal{C}_\Theta(h^+)$ is in
$\mathcal{K}^\mathrm{t}_\Theta$.

*Proof.* Write $h = h_K$. Suppose first that $t \notin \lbrace \omega, \pi/2 \rbrace$. Then
$K \subseteq K^+ \subseteq P_\omega$, so $K^+$ has the support values $1, 1, 0, 0$ of $K$ and
$P_\omega$ at $\omega$, $\pi/2$, $\omega + \pi$, $3\pi/2$, and it is a polygon cap.

Now let $t \in \lbrace \omega, \pi/2 \rbrace$. By Proposition 4.11 it suffices to show that $K^+$ has
width one in the directions $u_\omega$ and $u_{\pi/2}$. In the direction $u_t$, $K^+$ lies in a
strip of width one. It reaches the top line $l(t, h(t) + \varepsilon)$, because $\sigma_K(t) > 0$:
the points just beyond the relative interior of the side $e_K(t)$ satisfy all the other defining
inequalities of $K$. It reaches the bottom line $l(t, h(t) - 1 + \varepsilon)$, which still cuts $K$
for $\varepsilon < 1$, since every point $p \in K$ with $\langle p, u_t \rangle \ge h(t) - 1 + \varepsilon$
lies in $K^+$. If $\omega < \pi/2$, let $t'$ be the other angle of $\lbrace \omega, \pi/2 \rbrace$.
The cap $K$ contains $o_\omega$, on the top line of the direction $u_{t'}$, and $o_\omega - u_{t'}$,
on its bottom line (as in the proof of
[Theorem 3.10](03-monotone.md#theorem-310-the-cap-of-a-moving-sofa-baek-theorem-241)). Both points
have $\langle p, u_t \rangle > 0 = h(t) - 1$, so they lie in $K^+$ for small $\varepsilon$, and $K^+$
has width one in the direction $u_{t'}$ too. $\square$

*Lean: [`lemma3_4_8`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L955).*

For $t \in \lbrace \omega, \pi/2 \rbrace$ and $\sigma_K(t) = 0$, the line $l(t, h(t) + \varepsilon)$
would miss $K^+$, and the width of $K^+$ along $u_t$ would drop below one. This is why Lemma 4.28
looks for a side that is too long, and why the balancing move pushes only outwards.

### Theorem 4.31 (maximum polygon caps are balanced; Baek, Theorem 3.4.9)

Every maximum polygon cap is balanced.

*Proof.* Suppose that a maximum polygon cap $K$ is not balanced. By Lemma 4.28 there is
$t \in \Theta^\diamond$ with $\sigma_K(t) > \tau_K(t) \ge 0$. Let $h^+$ raise $h_K(t)$ by a small
$\varepsilon > 0$, as in Lemma 4.29. By Lemma 4.30, $K^+ = \mathcal{C}_\Theta(h^+)$ is a translate
$K_0 + v$ of a polygon cap $K_0$, and

```math
\mathcal{A}_\Theta(K) = \mathcal{A}_\Theta(h_K) < \mathcal{A}_\Theta(h^+) \le \mathcal{A}_\Theta(K^+) = \mathcal{A}_\Theta(K_0)
```

by Proposition 4.16, Lemma 4.29 (for $\varepsilon < (\sigma_K(t) - \tau_K(t))/C$), Proposition 4.19
and Theorem 4.18. This contradicts the maximality of $K$. $\square$

*Lean: [`theorem3_4_9`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L970).*

The comparison cap $K_0$ is a polygon cap whose niche may stick out. No connectedness is needed,
and this closes the gap of §4.1.

### Theorem 4.32 (the polygon niche lies in the cap; Baek, Theorem 3.4.10)

Every maximum polygon cap $K$ with angle set $\Theta$ contains its polygon niche $\mathcal{N}_\Theta(K)$.

*Proof.* By balance, the polyline consists of the sides of the upper boundary of $K$, rearranged.
From $A^-_K(0)$, the upper boundary takes its sides in increasing order of normal angle, the order
that goes farthest in each direction $u_s$. So a rearrangement that stays in the fan $F_\omega$ stays
in $K$.

In detail, let $p$ be a vertex of $\mathbf{p}_K$ and $A = A^-_K(0)$. Walking along $\mathbf{p}_K$
from $A$ to $p$ gives $p = A + \sum_i \ell_i v_{s_i}$, summed over the segments to the right of $p$;
the lengths $\ell_i$ of the segments with normal angle $t$ add up to at most $\tau_K(t)$. Let
$s \in \Theta \cup \lbrace \omega \rbrace$. Since $\langle v_{s_i}, u_s \rangle = \sin(s - s_i)$ and all angles lie in
$(0, \pi)$, the terms with $s_i < s$ are positive and the others are not. So

```math
\langle p, u_s \rangle \le \langle A, u_s \rangle + \sum_{t < s} \tau_K(t) \sin(s - t) = \langle A, u_s \rangle + \sum_{t < s} \sigma_K(t) \sin(s - t) = \langle v^+_K(s), u_s \rangle = h_K(s) ,
```

where the sums run over $t \in \Theta^\diamond$. The first equality is the balance of $K$
(Theorem 4.31). The second walks along the upper boundary from $A$ to the vertex $v^+_K(s)$, through
the sides $e_K(t)$, $t \le s$, each in the direction $v_t$. So $p$, and by convexity
$\mathbf{p}_K$, lies in $H_K(s)$ for $s \in \Theta \cup \lbrace \omega \rbrace$. The mirror image
$K^m$ is a maximum polygon cap with angle set $\omega - \Theta$ (Lemma 4.21), and $M_\omega$ maps
$F_\omega$ and $\mathcal{N}_\Theta(K)$ to $F_\omega$ and $\mathcal{N}_{\omega - \Theta}(K^m)$ and
exchanges the two half-lines of Theorem 4.25, so $M_\omega(\mathbf{p}_K) = \mathbf{p}_{K^m}$. The
same argument for $K^m$, with $h_{K^m}(t) = h_K(\omega + \pi/2 - t)$ (Proposition 3.21), gives
$\mathbf{p}_K \subseteq H_K(s)$ for $s \in (\Theta + \pi/2) \cup \lbrace \pi/2 \rbrace$ as well. So
$\mathbf{p}_K$ lies in every supporting half-plane of $K$ with normal angle in $\Theta^\diamond$, and
in $F_\omega$, whose two half-planes are the other supporting half-planes of $K$; so
$\mathbf{p}_K \subseteq K$. By Theorem 4.25 the niche lies in $F_\omega$ below the polyline, between
$C^+_K(\omega)$ and $A^-_K(0)$. So each point of the niche lies on a vertical segment from a point of
a bottom side of $K$ up to a point of $\mathbf{p}_K$, and this segment lies in $K$. $\square$

*Lean: [`theorem3_4_10`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L1240), [`theorem3_4_4`](../../MovingSofaOptimality/Balanced/Polyline.lean#L436), [`lemma3_4_1`](../../MovingSofaOptimality/Balanced/MaxPolygonCapExists.lean#L176), [`mpc_walk`](../../MovingSofaOptimality/Balanced/CapGeometry.lean#L658).*

## 4.7 Balanced maximum sofas

### Definition 4.33 (balanced maximum cap; Baek, Definitions 3.5.1–3.5.2)

The *uniform angle set* with $n \ge 2$ intervals is
$\Theta_{\omega, n} = \lbrace i\omega/n : 1 \le i < n \rbrace$. A *balanced maximum cap* with rotation
angle $\omega \in (0, \pi/2]$ is a cap $K_\omega \in \mathcal{K}^\mathrm{c}_\omega$ for which there
are powers of two $1 < n_1 < n_2 < \cdots$ and maximum polygon caps $K_i$ with angle sets
$\Theta_{\omega, n_i}$ such that $K_i \to K_\omega$ in the Hausdorff distance
$d_\mathrm{H}(K, K') = \sup_t \lvert h_K(t) - h_{K'}(t) \rvert$
([Definition 2.11](02-preliminaries.md#definition-211-hausdorff-distance-baek-definition-2112)).

*Lean: [`uniformAngleSet`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L33), [`dyadicAngleSet`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L51), [`IsBalancedMaxCap`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L137), [`hausdorffDist`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L86),
[`HausdorffTendsto`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L89).*

![Three rows, for n = 4, 8 and 16, each showing a blue polygon sofa between faint lines y = 0 and y = 1 with a dashed outline of Gerver's sofa centred on the same vertical line. For n = 4 the polygon sofa is visibly wider, with straight slanted ends and a jagged notch; for n = 8 it is closer; for n = 16 its ends and its notch nearly follow the dashed outline](figures/04-balanced/limit.svg)

*Figure 4.7.* The maximum polygon sofas for $\omega = \pi/2$ and the uniform angle sets with
$n = 4$, $8$ and $16$ intervals (blue), computed numerically, with the outline of Gerver's sofa
(dashed). Their values $\mathcal{A}_\Theta(K_\Theta) = 2.4148$, $2.3027$, $2.2584$ decrease towards
$\lvert G \rvert = 2.2195$; each of them is balanced to within $10^{-12}$ (Theorem 4.31).

As $n$ doubles, the angle set grows. For each cap the polygon cap then shrinks and the polygon niche
grows, so the maximum values decrease (Figure 4.7). By Theorem 4.9 each value bounds the area of
every monotone sofa with rotation angle $\pi/2$. The values converge to the maximum of
$\mathcal{A}_{\pi/2}$ (proof of Theorem 4.38), which [Chapter 9](09-optimality.md) identifies with
$\lvert G \rvert$.

### Proposition 4.34 (mirror image; Baek, Proposition 3.5.1)

The mirror image of a balanced maximum cap is a balanced maximum cap.

*Proof.* The mirror image of a cap is a cap
([Proposition 3.21](03-monotone.md#proposition-321-mirror-symmetry-baek-proposition-254)). Apply
Lemma 4.21 to the maximum polygon caps $K_i$: the uniform angle sets satisfy
$\omega - \Theta_{\omega, n} = \Theta_{\omega, n}$, and $M_\omega$ preserves the Hausdorff distance,
since $h_{K^\mathrm{m}}(t) = h_K(\omega + \pi/2 - t)$. $\square$

*Lean: [`proposition3_5_1`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L175).*

### Theorem 4.35 (existence of balanced maximum caps; Baek, Theorem 3.5.2)

For every $\omega \in (0, \pi/2]$ there is a balanced maximum cap with rotation angle $\omega$.

*Proof sketch.* For each $m$ let $\Theta_m = \Theta_{\omega, 2^{m+1}}$, and let $K_m$ be a maximum
polygon cap with angle set $\Theta_m$ (Theorem 4.23). The angle $\omega/2$ lies in every $\Theta_m$,
and $\mathcal{A}_{\Theta_m}(K_m) \ge \mathcal{A}_{\Theta_m}(K^{\mathbf 1}) > 0$ with $K^{\mathbf 1}$ as
in the proof of Theorem 4.23. So by Lemma 4.22 the widths of the $K_m$ are at most
$c_{\omega, \omega/2}$. The $K_m$ contain $o_\omega$ and lie between the lines $y = 0$ and $y = 1$, so
they lie in one compact box. By the Blaschke selection theorem
([Theorem 2.12](02-preliminaries.md#theorem-212-blaschke-selection-theorem)) a subsequence converges
to a convex body $K$. The support values $1, 1, 0, 0$ at $\omega$, $\pi/2$, $\omega + \pi$, $3\pi/2$
pass to the limit.

It remains to see that $K$ is an intersection of half-planes with normal angles in
$J_\omega \cup \lbrace \omega + \pi, 3\pi/2 \rbrace$, $J_\omega = [0, \omega] \cup [\pi/2, \omega + \pi/2]$.
The gaps $(a, b)$ between these angles are shorter than $\pi$, and a polygon cap $K_m$ has no normal
angle in them. So the supporting lines $l_{K_m}(a)$ and $l_{K_m}(b)$ meet at a corner $q$ of $K_m$,
and $h_{K_m}(r) = \langle q, u_r \rangle$ for $a \le r \le b$. With
$\sin(b - a)\, u_r = \sin(b - r)\, u_a + \sin(r - a)\, u_b$ this gives

```math
\sin(b - a)\, h(r) = \sin(b - r)\, h(a) + \sin(r - a)\, h(b) \qquad (a \le r \le b)
```

for $h = h_{K_m}$. The identity passes to the limit $h = h_K$. Since its coefficients are
nonnegative, it shows that $H_K(a) \cap H_K(b) \subseteq H_K(r)$ for $a < r < b$. So the half-planes
$H_K(r)$ with $r$ in a gap can be dropped from $K = \bigcap_r H_K(r)$
([Lemma 2.7](02-preliminaries.md#lemma-27-the-support-function)). The paper calls this check easy
(REPORT.md, E8). $\square$

*Lean: [`theorem3_5_2`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L326), [`mpc_blaschke`](../../MovingSofaOptimality/Balanced/MaxPolygonCapExists.lean#L846), [`mpc_gap_limit`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L197).*

### Lemma 4.36 (limits of nested sets; Baek, Lemma 3.5.3)

Let $X, Y, X_i, Y_i$ be bounded nonempty subsets of $\mathbb{R}^2$ with $X_i \to X$ and $Y_i \to Y$ in
the Hausdorff distance of sets, and $Y$ compact. If $X_i \subseteq Y_i$ for all $i$, then
$X \subseteq Y$.

*Proof.* Let $p \in X$. Then $d(p, X_i) \to 0$, so there are $p_i \in X_i \subseteq Y_i$ with $p_i \to p$,
and $d(p_i, Y) \le d_\mathrm{H}(Y_i, Y) \to 0$. So $d(p, Y) = 0$, and $p \in Y$ as $Y$ is closed.
$\square$

*Lean: [`lemma3_5_3`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L373).*

The proof of Theorem 4.37 applies Lemma 4.36 to single points, which lie in the polygon niches of all
late $K_i$ (REPORT.md, E8).

### Theorem 4.37 (the niche lies in the cap; Baek, Theorem 3.5.4)

Every balanced maximum cap $K_\omega$ contains its niche: $\mathcal{N}(K_\omega) \subseteq K_\omega$.

*Proof.* Let $K = K_\omega$, with maximum polygon caps $K_i \to K$ for the angle sets
$\Theta_i = \Theta_{\omega, n_i}$, and let $p \in \mathcal{N}(K)$. Then $p \in F_\omega \cap Q^-_K(t)$
for some $t \in (0, \omega)$:

```math
\langle p, u_t \rangle < h_K(t) - 1 , \qquad \langle p, u_{t + \pi/2} \rangle < h_K(t + \pi/2) - 1 .
```

The support function is continuous, so both strict inequalities hold, with a margin $\delta > 0$, at
some dyadic angle $s = j\omega/2^k$ near $t$. For large $i$ the angle $s$ lies in $\Theta_i$, since
these sets increase, and $\lvert h_{K_i} - h_K \rvert < \delta$. So
$p \in \mathcal{N}_{\Theta_i}(K_i) \subseteq K_i$ by Theorem 4.32. The convex bodies $K_i$
converge to $K$ also in the Hausdorff distance of sets, which for convex bodies is at most the
distance of their support functions (Schneider, Lemma 1.8.14). So Lemma 4.36, applied to
$\lbrace p \rbrace \subseteq K_i$, gives $p \in K$. $\square$

*Lean: [`theorem3_5_4`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L486), [`mpc_niche_eventually`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L444), `mpc_tendsto_metric_hausdorffDist`.*

The paper argues that the polygon niches $\mathcal{N}_{\Theta_j}(K_i)$ converge to $\mathcal{N}_{\Theta_j}(K)$
unless the latter is empty. This can fail when a wedge is empty for $K$ but not for the $K_i$; the
eventual membership above is what Lemma 4.36 needs (REPORT.md, E8).

### Theorem 4.38 (maximality; Baek, Theorem 3.5.5)

A balanced maximum cap $K_\omega$ maximizes the sofa area functional $\mathcal{A}_\omega$ over all
caps with rotation angle $\omega$.

*Proof.* Let $K'$ be a cap with rotation angle $\omega$. By Theorem 4.9 and the maximality of $K_i$,

```math
\mathcal{A}_\omega(K') \le \mathcal{A}_{\Theta_i}(K') \le \mathcal{A}_{\Theta_i}(K_i) = \lvert K_i \rvert - \lvert \mathcal{N}_{\Theta_i}(K_i) \rvert .
```

The right-hand side tends to $\mathcal{A}_\omega(K_\omega)$, which proves the theorem. First,
$\lvert K_i \rvert \to \lvert K_\omega \rvert$, since area is continuous in the Hausdorff distance.
With $K' = K_\omega$, the inequality gives
$\limsup \lvert \mathcal{N}_{\Theta_i}(K_i) \rvert \le \lvert \mathcal{N}(K_\omega) \rvert$. Conversely,
fix $m$. For $i \ge m$ the angle set $\Theta_i$ contains $\Theta_m$, so
$\mathcal{N}_{\Theta_m}(K_i) \subseteq \mathcal{N}_{\Theta_i}(K_i)$, and
$\lvert \mathcal{N}_{\Theta_m}(K_i) \rvert \to \lvert \mathcal{N}_{\Theta_m}(K_\omega) \rvert$ by the
estimate of the wedges in the proof of Theorem 4.23. So
$\liminf_i \lvert \mathcal{N}_{\Theta_i}(K_i) \rvert \ge \lvert \mathcal{N}_{\Theta_m}(K_\omega) \rvert$
for every $m$, and these niches increase to $\mathcal{N}(K_\omega)$ (proof of Theorem 4.37). Hence
$\mathcal{A}_{\Theta_i}(K_i) \to \mathcal{A}_\omega(K_\omega)$. $\square$

*Lean: [`theorem3_5_5`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L534), [`mpc_tendsto_area`](../../MovingSofaOptimality/Balanced/MaxPolygonCapExists.lean#L889), [`mpc_tendsto_area_polyNiche`](../../MovingSofaOptimality/Balanced/MaxPolygonCapExists.lean#L1050).*

### Definition 4.39 (balanced maximum sofa; Baek, Definition 3.5.3)

A *balanced maximum sofa* with rotation angle $\omega$ is a monotone sofa $S_\omega$ whose cap
$\mathcal{C}(S_\omega)$ is a balanced maximum cap.

*Lean: [`IsBalancedMaxSofa`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L606).*

### Theorem 4.40 (balanced maximum sofas; Baek, Theorem 3.5.6)

For every $\omega \in (0, \pi/2]$ there is a balanced maximum cap $K_\omega$ such that
$S_\omega = K_\omega \setminus \mathcal{N}(K_\omega)$ is a balanced maximum sofa with cap $K_\omega$, and
$\lvert S \rvert \le \lvert S_\omega \rvert$ for every moving sofa $S$ with rotation angle $\omega$.

*Proof.* Theorem 4.35 gives a balanced maximum cap $K_\omega$. It contains its niche
(Theorem 4.37), so it is the cap of the monotone sofa $S_\omega = K_\omega \setminus \mathcal{N}(K_\omega)$
([Theorems 3.26](03-monotone.md#theorem-326-the-caps-of-monotone-sofas-baek-theorem-259) and
[3.13](03-monotone.md#theorem-313-a-monotone-sofa-is-its-cap-minus-its-niche-baek-theorem-243)), and
$\lvert S_\omega \rvert = \mathcal{A}_\omega(K_\omega)$
([Theorem 3.29](03-monotone.md#theorem-329-the-area-of-a-monotone-sofa-baek-theorem-2510)). Let $S$
be a moving sofa with rotation angle $\omega$. A translate of $S$ is in standard position
([Proposition 3.1](03-monotone.md#proposition-31-standard-position-baek-propositions-121-and-231))
and lies in its monotonization, a monotone sofa
([Theorem 3.3](03-monotone.md#theorem-33-monotonization-baek-theorem-232)). The cap $K'$ of the
monotonization has $\mathcal{A}_\omega(K')$ equal to its area (Theorem 3.29). So
$\lvert S \rvert \le \mathcal{A}_\omega(K') \le \mathcal{A}_\omega(K_\omega) = \lvert S_\omega \rvert$ by
Theorem 4.38. $\square$

*Lean: [`theorem3_5_6`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L611).*
