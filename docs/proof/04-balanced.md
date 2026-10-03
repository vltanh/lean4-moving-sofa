# 4. Balanced maximum sofas

[Contents](README.md) · [← 3. Monotone sofas, caps and niches](03-monotone.md) · [5. The rotation angle →](05-rotation-angle.md)

This chapter proves that for every rotation angle $\omega \in (0, \pi/2]$ some monotone sofa of
largest area among the moving sofas of rotation angle $\omega$ is a limit of balanced polygons: a
*balanced maximum sofa* exists (Theorem 4.40; Baek, Theorem 3.5.6). It follows Chapter 3 of Baek's
paper, which makes rigorous a balancing argument of Gerver [3]. [Chapter 5](05-rotation-angle.md)
uses the balance to show that a balanced maximum sofa of area at least $2.2$ can turn through a full
right angle, and Chapters [6](06-surface-area.md) and [7](07-injectivity.md) to show that it
satisfies the injectivity condition.

The construction keeps only finitely many supporting hallways. For a finite set $\Theta$ of angles
in $(0, \omega)$ the sofa becomes a polygon, the difference of a *polygon cap* $K$ and a *polygon
niche* $\mathcal{N}_\Theta(K)$ (§4.3). A polygon cap that maximizes
$\mathcal{A}_\Theta(K) = \lvert K \rvert - \lvert \mathcal{N}_\Theta(K) \rvert$ is *balanced*: for
every normal angle $t$, the side of the cap with outer normal $u_t$ is as long as the sides of the
niche on the parallel line at distance one, since otherwise pushing one hallway would increase the
area (Theorem 4.31). Gerver ran this argument on the polygon sofa itself, where pushing a hallway can
disconnect the sofa (§4.1). Baek runs it on the cap: the niche may stick out of the cap, the hallway
is only pushed in the direction that enlarges the cap, and the pushed cap is then a translate of a
polygon cap, which a translation-invariant functional cannot tell apart (§4.4). Balance then shows
afterwards that the niche does not stick out: the boundary of the niche is made of the same sides as
the upper boundary of the cap, in another order (Theorem 4.32). As $\Theta$ fills $[0, \omega]$, the
maximum polygon caps converge to a cap that contains its niche and maximizes the sofa area
functional $\mathcal{A}_\omega$ (Theorems 4.37 and 4.38).

We use the notation of Chapters [2](02-preliminaries.md) and [3](03-monotone.md): the strips $H$ and
$V_\omega$, the
parallelogram $P_\omega = H \cap V_\omega$ with corners $O = (0, 0)$ and
$o_\omega = (\tan(\pi/4 - \omega/2), 1)$, the fan $F_\omega = H_+(\omega, 0) \cap H_+(\pi/2, 0)$,
caps $K \in \mathcal{K}^\mathrm{c}_\omega$, the quarter-planes
$Q^+_K(t) = H_-(t, h_K(t)) \cap H_-(t + \pi/2, h_K(t + \pi/2))$ and
$Q^-_K(t) = H^\circ_-(t, h_K(t) - 1) \cap H^\circ_-(t + \pi/2, h_K(t + \pi/2) - 1)$ of the
supporting hallway $L_K(t) = Q^+_K(t) \setminus Q^-_K(t)$, its walls $a_K(t) = l(t, h_K(t))$,
$b_K(t) = l(t, h_K(t) - 1)$, $c_K(t)$, $d_K(t)$ and inner corner $\mathbf{x}_K(t)$, the vertices
$A^\pm_K(t)$, $C^\pm_K(t)$, the wedges $T_K(t) = F_\omega \cap Q^-_K(t)$ with their ends $W_K(t)$,
$Z_K(t)$ and gaps $w_K(t), z_K(t) > 0$, the niche
$\mathcal{N}(K) = F_\omega \cap \bigcup_{t \in (0, \omega)} Q^-_K(t)$, the mirror image
$K^\mathrm{m} = M_\omega(K)$, and $\mathcal{A}_\omega(K) = \lvert K \rvert - \lvert \mathcal{N}(K) \rvert$.
Here $H_\pm(t, h)$ and $H^\circ_\pm(t, h)$ are the closed and open half-planes
$\lbrace p : \pm(p \cdot u_t - h) \ge 0 \rbrace$, $\lbrace p : \pm(p \cdot u_t - h) > 0 \rbrace$
bounded by the line $l(t, h) = \lbrace p : p \cdot u_t = h \rbrace$, and
$\sigma_K(t) = \sigma_K(\lbrace t \rbrace)$ is the length of the edge $e_K(t)$ of a convex body $K$ with
outer normal $u_t$ (Baek's Proposition 2.1.2; the surface area measure $\sigma_K$ is constructed in
[Chapter 6](06-surface-area.md)).

## 4.1 Gerver's balancing argument and its gap

Gerver's Theorem 1 [3], quoted in Baek's paper as Theorem 1.3.1, states the following. There are an
angle $\gamma \in [\pi/3, \pi/2]$ and a region $S$ that moves around the corner of $L$ rotating
through $\gamma$, such that no region of larger area moves around the corner, and such that for
arbitrarily large $n$ the region $S$ is approximated arbitrarily closely by a polygon $P_n$ with a
*balanced* boundary: for any two parallel lines at distance one, the sides of $P_n$ on the two
lines have the same total length. Each $P_n$ is the intersection of the half-strip $H_L$, a
translate of $V_L$ rotated by $\gamma$, and translates of the hallway $L$ rotated by $k\gamma/n$ for
$0 < k < n$. The theorem is not formalized as stated; Baek reproves its content, as Theorems 4.31
and 4.40 and
[Theorem 5.1](05-rotation-angle.md#theorem-51-a-first-bound-on-the-rotation-angle-baek-theorem-151),
and those are formalized.

Fix $\omega \in (0, \pi/2]$ and a finite set $\Theta \subset (0, \omega)$. The *polygon sofa*

```math
S_\Theta = H \cap V_\omega \cap \bigcap_{t \in \Theta} L_t
```

is the part of $P_\omega$ that lies in the hallways $L_t = \mathbf{x}(t) + R_t L$, each turned by
$t$ and translated so that its inner corner is $\mathbf{x}(t)$ (Figure 4.1). The discrete problem
asks for the inner corners that maximize $\lvert S_\Theta \rvert$, and Gerver's idea is that a
maximizer is balanced.

![A horizontal strip H between two thick grey lines, and two hallways turned by pi/6 (green walls) and pi/3 (purple walls), each drawn as its two outer walls meeting at an outer corner above the strip and its two inner walls meeting at an inner corner inside the strip. The blue polygon sofa is the part of the strip inside both hallways: a long hexagon-like region with a notch in its lower side below the two inner corners x(pi/3) and x(pi/6)](figures/04-balanced/polygon-sofa.svg)

*Figure 4.1.* The polygon sofa $S_\Theta$ (blue) for $\Theta = \lbrace \pi/6, \pi/3 \rbrace$ and
$\omega = \pi/2$, where $V_\omega = H$: the part of the strip $H$ in the hallways $L_{\pi/6}$
(green) and $L_{\pi/3}$ (purple). Its notch is cut out by the inner corners $\mathbf{x}(\pi/6)$ and
$\mathbf{x}(\pi/3)$. This is the maximum polygon sofa for this angle set, computed numerically; its
area is $2.5154$.

**The balancing argument.** Suppose that a maximizer $S_\Theta$ is not balanced: two parallel lines
$l^+$ and $l^-$ at distance one carry sides of $S_\Theta$ of total lengths $s^+ > s^-$. Both lines
bound one strip $X$: $H$, $V_\omega$, or one arm of a hallway $L_t$, whose outer and inner walls are
parallel at distance one. Translate $X$ by $\varepsilon$ towards $l^+$. The sofa gains a strip of
area $\varepsilon s^+ + O(\varepsilon^2)$ along $l^+$ and loses one of area
$\varepsilon s^- + O(\varepsilon^2)$ along $l^-$, so its area grows by
$\varepsilon(s^+ - s^-) + O(\varepsilon^2)$ (Figure 4.2); if $X$ is $H$ or $V_\omega$, translate
everything back afterwards. This contradicts the maximality.

![The polygon sofa of Gerver's example with c = 0.1, in blue, between the lines y = 0 and y = 1. Its right side, thick green, lies on the outer wall of the hallway turned by pi/6; a thick orange side, the right side of the notch in its lower boundary, lies on the inner wall of the same hallway. An arrow eps u points outwards from the green side. Dashed lines show both walls pushed by epsilon; a thin green strip along the right side is gained and a thin orange strip along the orange side is lost](figures/04-balanced/balancing-move.svg)

*Figure 4.2.* The balancing move. The side $s^+$ of the polygon sofa on the outer wall of
$L_{\pi/6}$ (thick green, length $1.1547$) is longer than its side $s^-$ on the inner wall (thick
orange, length $0.7614$). Pushing the hallway by $\varepsilon u$ with $u = u_{\pi/6}$ moves both walls
to the dashed lines: the sofa gains the green strip and loses the orange one, and its area grows by
$\varepsilon (s^+ - s^-) + O(\varepsilon^2)$. Here $\varepsilon = 0.1$, from $c = 0.1$ to $c = 0$ in
the example below.

**The gap.** A moving sofa is connected, and the maximum should be taken among connected polygon
sofas; but the balancing move can disconnect $S_\Theta$, so the maximizer over connected polygon sofas
need not be balanced. Baek's example (overview, §1.4) takes $\omega = \pi/2$,
$\Theta = \lbrace \pi/6, \pi/3 \rbrace$, $u = u_{\pi/6}$, $\mathbf{x}(\pi/3) = (-0.9, 0.98)$ and
$\mathbf{x}(\pi/6) = (0, 1) - c\,u$. For every $c \in [0, 0.1]$ the side of $S_\Theta$ with normal
$u$ is longer than its sides with normal $-u$, so the argument pushes $L_{\pi/6}$ along $u$ and
decreases $c$. At $c = 0$ the inner corner $\mathbf{x}(\pi/6)$ reaches the top line $y = 1$, and for
$c < 0$ the quadrant below it cuts the strip, and $S_\Theta$ falls into two pieces (Figure 4.3).
Another pair of sides could be balanced instead, keeping $S_\Theta$ connected, but Gerver's proof
makes no such choice.

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

The area of a region cut out by half-planes changes, when one half-plane is pushed, at the rate of
the length of the boundary on its line. This section proves this for the regions that occur.

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

*Lean: [`BoolFun`](../../MovingSofaOptimality/Balanced/NefPolygon.lean#L21), [`BoolFun.IsMonotone`](../../MovingSofaOptimality/Balanced/NefPolygon.lean#L24), [`nefPolygon`](../../MovingSofaOptimality/Balanced/NefPolygon.lean#L56), [`HalfPlaneData`](../../MovingSofaOptimality/Balanced/NefPolygon.lean#L61), [`IsSimpleNefPolygon`](../../MovingSofaOptimality/Balanced/NefPolygon.lean#L79).*

A line is a Nef polygon, the intersection of the two closed half-planes it bounds, but not a simple
one: the two half-planes have the same boundary. In a simple Nef polygon a point lying in more of the
defining half-planes is more likely to lie in the polygon.

### Proposition 4.2 (monotone boolean functions; Baek, Proposition 3.1.1)

A boolean function obtained from the variables $P_1, \dots, P_n$ by conjunctions and disjunctions is
monotone.

*Proof.* Each variable is monotone, and conjunctions and disjunctions of monotone functions are
monotone; the Lean proof is an induction on the expression. $\square$

*Lean: [`proposition3_1_1`](../../MovingSofaOptimality/Balanced/NefPolygon.lean#L41), [`PosBoolExpr`](../../MovingSofaOptimality/Balanced/NefPolygon.lean#L28).*

### Theorem 4.3 (pushing a half-plane; Baek, Theorem 3.1.2)

Let $X = \mathcal{E}(H_1, \dots, H_n)$ be a bounded simple Nef polygon whose defining half-planes are
$H_i = H_-(t_i, h_i)$ or $H^\circ_-(t_i, h_i)$, with boundaries $l_i = l(t_i, h_i)$, and fix $i$. Let
$X'_\delta$ be $X$ with $H_i$ replaced by $H_-(t_i, h_i + \delta)$, or by $H^\circ_-(t_i, h_i + \delta)$
if $H_i$ is open. There are $\varepsilon > 0$ and $C$ such that for $\lvert \delta \rvert \le \varepsilon$

```math
\Bigl\lvert\, \lvert X'_\delta \rvert - \lvert X \rvert - \mathcal{H}^1(\partial X \cap l_i)\, \delta \,\Bigr\rvert \le C \delta^2 .
```

*Lean: [`theorem3_1_2`](../../MovingSofaOptimality/Balanced/NefPolygon.lean#L841).*

The paper leaves the boundedness of $X$ implicit; $\mathcal{H}^1$ is the length along a line
([`lineLength`](../../MovingSofaOptimality/Basic/Plane.lean#L64)).

*Proof sketch.* Take $\delta \ge 0$; the case $\delta \le 0$ is symmetric. Since $\mathcal{E}$ is
monotone, $X \subseteq X'_\delta$, and the added points are those of the strip between $l_i$ and
$l(t_i, h_i + \delta)$ that lie in the set $Y$ of points $p$ for which $\mathcal{E}$ is true when the
$i$-th argument is true and false when it is false: there, and only there, membership in $X$ is
decided by $H_i$. By Cavalieri's principle in the frame $(u_{t_i}, v_{t_i})$,

```math
\lvert X'_\delta \rvert - \lvert X \rvert = \int_{h_i}^{h_i + \delta} g(s)\, ds , \qquad g(s) = \mathcal{H}^1\bigl(Y \cap l(t_i, s)\bigr) .
```

The other boundary lines are different from $l_i$: those parallel to it stay away from
$l(t_i, s)$ for $s$ near $h_i$, and the others cross $l(t_i, s)$ at points that move linearly with
$s$. So $Y \cap l(t_i, s)$ changes only near finitely many crossings, and $g$ is Lipschitz near
$h_i$. Finally $g(h_i) = \mathcal{H}^1(\partial X \cap l_i)$, because a point of $l_i$ on no other
boundary line is a boundary point of $X$ exactly when it lies in $Y$. So
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

### Proposition 4.6 (the approximating polygon cap; Baek, Proposition 3.2.1)

For every cap $K$ with rotation angle $\omega$, $\mathcal{C}_\Theta(K)$ is a polygon cap with angle
set $\Theta$ that contains $K$, and $\mathcal{C}_\Theta(K) = K$ if $K \in \mathcal{K}^\mathrm{c}_\Theta$.
So $\mathcal{C}_\Theta : \mathcal{K}^\mathrm{c}_\omega \to \mathcal{K}^\mathrm{c}_\Theta$ is onto.

*Proof.* $K$ lies in $P_\omega$ and in its supporting half-planes, so $K \subseteq \mathcal{C}_\Theta(K)
\subseteq P_\omega$. Since $P_\omega = H_-(\pi/2, 1) \cap H_-(3\pi/2, 0) \cap H_-(\omega, 1) \cap
H_-(\omega + \pi, 0)$, the set $\mathcal{C}_\Theta(K)$ is an intersection of half-planes with normal
angles in $\Theta^\diamond \cup \lbrace \omega + \pi, 3\pi/2 \rbrace$; lying between $K$ and $P_\omega$, it
has the support values $1, 1, 0, 0$ of both at $\omega, \pi/2, \omega + \pi, 3\pi/2$, so it is a cap.
If $K$ is a polygon cap, it is the intersection of its supporting half-planes at these normal angles,
and those at $\omega, \pi/2, \omega + \pi, 3\pi/2$ are the half-planes of $P_\omega$; this
intersection is $\mathcal{C}_\Theta(K)$. $\square$

*Lean: [`proposition3_2_1`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L350), [`proposition3_2_1_fix`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L364).*

### Definition 4.7 (polygon niche and polygon area functional; Baek, Definitions 3.2.5–3.2.6)

For a cap $K$ with rotation angle $\omega$, the *polygon niche* and the *polygon sofa area
functional* are

```math
\mathcal{N}_\Theta(K) = F_\omega \cap \bigcup_{t \in \Theta} Q^-_K(t) , \qquad \mathcal{A}_\Theta(K) = \lvert \mathcal{C}_\Theta(K) \rvert - \lvert \mathcal{N}_\Theta(K) \rvert .
```

*Lean: [`polyNiche`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L53), [`polyArea`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L58).*

Baek's Definition 3.2.5 writes the parallelogram $P_\omega$ where the fan $F_\omega$ is meant; the
rest of the paper uses $F_\omega$ (REPORT.md, E6). With $P_\omega$, Proposition 4.16 and Lemma 4.22
below are false: Figure 4.5 shows the caps that break Lemma 4.22.

![A polygon cap in blue with rotation angle 1.2 inside a dashed parallelogram, and the fan, the region above two dark half-lines from the origin O, one along the x-axis to the right and one up and to the left. Two inner corners x_K(0.4) and x_K(0.8), marked as orange dots above O, each with two dashed walls going down to the edge of the fan; the polygon niche, in orange, is the part of the fan below these walls, a small region around O inside the blue cap](figures/04-balanced/cap-niche.svg)

*Figure 4.4.* A polygon cap $K$ (blue) with $\omega = 1.2$ and $\Theta = \lbrace 0.4, 0.8 \rbrace$,
inside $P_\omega$ (dashed). Its polygon niche (orange) is the part of the fan $F_\omega$, above the
two dark half-lines from $O$, that lies below the walls $b_K(t)$ and $d_K(t)$ of the inner corners
$\mathbf{x}_K(0.4)$ and $\mathbf{x}_K(0.8)$. The cap is the maximum polygon cap for this angle set,
computed numerically.

![A long blue trapezoid K between the lines y = 0 and y = 1, from x = -1 to x = 9 at the bottom, and a large orange triangle standing on the x-axis with its apex x_K(pi/4) high above the strip. The part of the triangle inside the strip below the dashed line y = 1 is darker orange; the part above the dashed line is light orange with a dashed outline](figures/04-balanced/fan.svg)

*Figure 4.5.* Why the fan. The polygon cap $K = \lbrace 0 \le y \le 1,\ y - 1 \le x \le 9 - y \rbrace$
for $\omega = \pi/2$ and $\Theta = \lbrace \pi/4 \rbrace$ (blue) has area $9$, and its polygon niche,
the triangle below $\mathbf{x}_K(\pi/4) = (4, 5 - \sqrt2)$, has area $(5 - \sqrt2)^2 = 12.86$, so
$\mathcal{A}_\Theta(K) < 0$. The parallelogram $P_\omega$ is the strip below the dashed line, and it
keeps only the darker part of the triangle, of area $9 - 2\sqrt2$. With $P_\omega$ in place of
$F_\omega$, every cap $\lbrace 0 \le y \le 1,\ y - 1 \le x \le d + 1 - y \rbrace$ with $d \ge 2\sqrt2$
would have $\mathcal{A}_\Theta = (d + 1) - (d + 1 - 2\sqrt2) = 2\sqrt2 > 0$, and Lemma 4.22 would
fail; with $F_\omega$, $\mathcal{A}_\Theta = d + 1 - (d/2 + 1 - \sqrt2)^2$.

### Proposition 4.8 (polygon niches; Baek, Proposition 3.2.2)

For every cap $K$ with rotation angle $\omega$,
$\mathcal{N}_\Theta(K) = \mathcal{N}_\Theta(\mathcal{C}_\Theta(K)) \subseteq \mathcal{N}(K)$.

*Proof.* $\mathcal{N}_\Theta(K)$ depends only on $\omega$ and on the support values of $K$ on
$\Theta \cup (\Theta + \pi/2)$, which $K$ and $\mathcal{C}_\Theta(K)$ share: the supporting lines of
$K$ at these angles bound $\mathcal{C}_\Theta(K)$ and touch $K \subseteq \mathcal{C}_\Theta(K)$. The
inclusion holds because $\Theta \subseteq (0, \omega)$. $\square$

*Lean: [`proposition3_2_2`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L373).*

### Theorem 4.9 (polygon upper bound; Baek, Theorem 3.2.3)

For a polygon cap $K \in \mathcal{K}^\mathrm{c}_\Theta$,
$\mathcal{A}_\Theta(K) = \lvert K \rvert - \lvert \mathcal{N}_\Theta(K) \rvert$. For every cap $K$ with
rotation angle $\omega$, $\mathcal{A}_\omega(K) \le \mathcal{A}_\Theta(K)$.

*Proof.* The first claim is $\mathcal{C}_\Theta(K) = K$ (Proposition 4.6). For the second,
$\lvert K \rvert \le \lvert \mathcal{C}_\Theta(K) \rvert$ by Proposition 4.6 and
$\lvert \mathcal{N}_\Theta(K) \rvert \le \lvert \mathcal{N}(K) \rvert$ by Proposition 4.8. $\square$

*Lean: [`theorem3_2_3`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L395), [`theorem3_2_3_le`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L399).*

So the maximum of $\mathcal{A}_\Theta$ over polygon caps bounds the area of every monotone sofa of
rotation angle $\omega$. Kallus and Romik's bound $2.37$ [5] essentially computes such a maximum for
a set of five angles (Baek's Remark 3.2.2).

## 4.4 Support values

A polygon cap is determined by its support values on $\Theta^\diamond$. Letting these values vary
freely gives a space in which a single side can be moved: the result need not be a cap, but it is
always a region cut out by half-planes.

### Definition 4.10 (cap translates and support values; Baek, Definitions 3.3.1–3.3.2)

$\mathcal{K}^\mathrm{t}_\Theta$ is the set of translates of the polygon caps with angle set
$\Theta$, and $\mathcal{H}_\Theta$ the space of functions $h : \Theta^\diamond \to \mathbb{R}$.

*Lean: [`IsPolygonCapTranslate`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L412).*

The formalization represents $h \in \mathcal{H}_\Theta$ by a function on $\mathbb{R}$ of which only
the values on $\Theta^\diamond$ are used.

### Proposition 4.11 (cap translates; Baek, Proposition 3.3.1)

A convex body $K'$ is in $\mathcal{K}^\mathrm{t}_\Theta$ if and only if (1) its widths
$h_{K'}(\omega) + h_{K'}(\omega + \pi)$ and $h_{K'}(\pi/2) + h_{K'}(3\pi/2)$ are both one, and (2) it is
an intersection of closed half-planes with normal angles in
$\Theta^\diamond \cup \lbrace \omega + \pi, 3\pi/2 \rbrace$.

*Proof.* Translates of polygon caps satisfy (1) and (2). Conversely, translate $K'$ by the vector $v$
with $v \cdot u_\omega = h_{K'}(\omega) - 1$ and $v \cdot u_{\pi/2} = h_{K'}(\pi/2) - 1$ (one condition
if $\omega = \pi/2$). The translate $K' - v$ has support values $1$ at $\omega$ and $\pi/2$, hence $0$
at $\omega + \pi$ and $3\pi/2$ by (1), and is a polygon cap by (2). $\square$

*Lean: [`proposition3_3_1`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L458).*

Baek's statement asks in (2) for normal angles in $\Theta^\diamond$; since
$\Theta^\diamond \subset (0, \pi)$, no bounded convex body has that property, and the bottom normal
angles $\omega + \pi$ and $3\pi/2$, which the paper's proof of Proposition 4.12 uses, are meant
(REPORT.md, E7).

### Proposition 4.12 (support values determine the cap; Baek, Proposition 3.3.2)

The map $\mathcal{K}^\mathrm{t}_\Theta \to \mathcal{H}_\Theta$, $K' \mapsto h_{K'}|_{\Theta^\diamond}$,
is injective.

*Proof.* By Proposition 4.11, $K'$ is the intersection of its supporting half-planes with normal
angles in $\Theta^\diamond \cup \lbrace \omega + \pi, 3\pi/2 \rbrace$, and its support values at
$\omega + \pi$ and $3\pi/2$ are $1 - h_{K'}(\omega)$ and $1 - h_{K'}(\pi/2)$. $\square$

*Lean: [`proposition3_3_2`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L500).*

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

*Lean: [`paraH`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L520), [`capH`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L524), [`fanH`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L529), [`nicheH`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L533), [`areaH`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L538).*

### Proposition 4.14 (Nef representations; Baek, Proposition 3.3.3)

For $h \in \mathcal{H}_\Theta$: (1) $\mathcal{C}_\Theta(h)$ is a simple Nef polygon with the defining
half-planes $H_-(t, h(t))$, $t \in \Theta^\diamond$, and $H_+(t, h(t) - 1)$, $t \in \lbrace \omega,
\pi/2 \rbrace$; (2) $\mathcal{N}_\Theta(h)$ is a simple Nef polygon with the defining half-planes
$H^\circ_-(t, h(t) - 1)$, $t \in \Theta \cup (\Theta + \pi/2)$, and $H_+(t, h(t) - 1)$,
$t \in \lbrace \omega, \pi/2 \rbrace$.

*Proof.* Both sets are built from these half-planes by intersections and unions, so the boolean
function is monotone (Proposition 4.2). The boundaries differ: lines with different normal angles in
$(0, \pi)$ differ, and $H_+(t, h(t) - 1) = H_-(t + \pi, 1 - h(t))$ is bounded by the line
$l(t, h(t) - 1)$, at distance one from $l(t, h(t))$. $\square$

*Lean: [`proposition3_3_3`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L747), [`capHalfPlanes`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L542), [`nicheHalfPlanes`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L548).*

### Proposition 4.15 (compatibility of caps; Baek, Proposition 3.3.4)

For $K' \in \mathcal{K}^\mathrm{t}_\Theta$, $\mathcal{C}_\Theta(h_{K'}) = K'$.

*Proof.* By Proposition 4.11, $K'$ is the intersection of its supporting half-planes with normal
angles in $\Theta^\diamond \cup \lbrace \omega + \pi, 3\pi/2 \rbrace$, and since its widths at $\omega$
and $\pi/2$ are one, those at $\omega + \pi$ and $3\pi/2$ are the half-planes
$H_+(t, h_{K'}(t) - 1)$, $t \in \lbrace \omega, \pi/2 \rbrace$, of $P_{h_{K'}}$. $\square$

*Lean: [`proposition3_3_4`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L811).*

### Proposition 4.16 (compatibility of niches; Baek, Proposition 3.3.5)

For $K \in \mathcal{K}^\mathrm{c}_\Theta$, $\mathcal{N}_\Theta(h_K) = \mathcal{N}_\Theta(K)$ and
$\mathcal{A}_\Theta(h_K) = \mathcal{A}_\Theta(K)$.

*Proof.* Since $h_K(\omega) = h_K(\pi/2) = 1$, the fan $F_{h_K}$ is $F_\omega$, and each union term of
$\mathcal{N}_\Theta(h_K)$ is the quadrant $Q^-_K(t)$ of the supporting hallway (Baek's
Proposition 2.2.2, in [Chapter 2](02-preliminaries.md)). The areas agree by Proposition 4.15 and
Theorem 4.9. $\square$

*Lean: [`proposition3_3_5`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L836).*

### Definition 4.17 (niches of cap translates; Baek, Definition 3.3.4)

For $K' \in \mathcal{K}^\mathrm{t}_\Theta$, $\mathcal{N}_\Theta(K') = \mathcal{N}_\Theta(h_{K'})$ and
$\mathcal{A}_\Theta(K') = \mathcal{A}_\Theta(h_{K'})$.

*Lean: [`nicheT`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L853), [`areaT`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L856).*

### Theorem 4.18 (translation invariance; Baek, Theorem 3.3.6)

For $K \in \mathcal{K}^\mathrm{c}_\Theta$ and $v \in \mathbb{R}^2$,
$\mathcal{N}_\Theta(K + v) = \mathcal{N}_\Theta(K) + v$ and
$\mathcal{A}_\Theta(K + v) = \mathcal{A}_\Theta(K)$. So Definition 4.17 extends Definition 4.7.

*Proof.* $h_{K+v}(t) = h_K(t) + v \cdot u_t$, so every defining half-plane of
$\mathcal{N}_\Theta(h_{K+v})$ is that of $\mathcal{N}_\Theta(h_K)$ translated by $v$. By
Propositions 4.15 and 4.16 and the translation invariance of area,
$\mathcal{A}_\Theta(K + v) = \lvert K + v \rvert - \lvert \mathcal{N}_\Theta(K) + v \rvert =
\mathcal{A}_\Theta(K)$. $\square$

*Lean: [`theorem3_3_6`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L872).*

### Proposition 4.19 (reduction to a cap translate; Baek, Proposition 3.3.7)

Let $h^+ \in \mathcal{H}_\Theta$ be such that $K^+ = \mathcal{C}_\Theta(h^+)$ is in
$\mathcal{K}^\mathrm{t}_\Theta$. Then $\mathcal{A}_\Theta(h^+) \le \mathcal{A}_\Theta(K^+)$.

*Proof.* The values $h^+$ need not be the support values of $K^+$, since the lines need not all touch
$K^+$; but $h_{K^+} \le h^+$ on $\Theta^\diamond$, because $K^+$ lies in the half-planes. At
$t \in \lbrace \omega, \pi/2 \rbrace$ equality holds: $K^+ \subseteq P_{h^+}$ has width one in the
direction $u_t$, as does the strip of $P_{h^+}$, so it touches both of its lines. Hence
$F_{h_{K^+}} = F_{h^+}$ and $\mathcal{N}_\Theta(h_{K^+}) \subseteq \mathcal{N}_\Theta(h^+)$, while
$\mathcal{C}_\Theta(h_{K^+}) = K^+ = \mathcal{C}_\Theta(h^+)$ by Proposition 4.15. Subtracting the
areas gives the claim. $\square$

*Lean: [`proposition3_3_7`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L933).*

## 4.5 Maximum polygon caps

### Definition 4.20 (maximum polygon cap; Baek, Definition 3.4.1)

A *maximum polygon cap* with angle set $\Theta$ is a polygon cap $K_\Theta \in \mathcal{K}^\mathrm{c}_\Theta$
with $o_\omega \in K_\Theta$ that maximizes $\mathcal{A}_\Theta$ over $\mathcal{K}^\mathrm{c}_\Theta$.

*Lean: [`IsMaxPolygonCap`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L1864).*

For $\omega < \pi/2$ every cap contains $o_\omega$; for $\omega = \pi/2$ the caps can slide
horizontally, and the condition $o_\omega = (0, 1) \in K_\Theta$ keeps them from sliding away.

### Lemma 4.21 (mirror image; Baek, Lemma 3.4.1)

The mirror image $M_\omega(K_\Theta)$ of a maximum polygon cap with angle set $\Theta$ is a maximum
polygon cap with angle set $\omega - \Theta$.

*Proof.* $h_{K^\mathrm{m}}(t) = h_K(\omega + \pi/2 - t)$ (Baek's Proposition 2.5.4, in
[Chapter 3](03-monotone.md)), so $M_\omega$ maps the polygon caps with angle set $\Theta$ onto those
with angle set $\omega - \Theta$ and their polygon niches onto each other; it preserves areas and
fixes $o_\omega$. $\square$

*Lean: [`lemma3_4_1`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L2053), [`AngleSet.mirror`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L1868), [`mirrorCap`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L79).*

### Lemma 4.22 (bounded width; Baek, Lemma 3.4.2)

Let $\omega \in (0, \pi/2]$ and $t \in (0, \omega)$. There is $c_{\omega, t} > 0$ such that every
polygon cap $K$ with an angle set $\Theta \ni t$ of rotation angle $\omega$ and with
$\mathcal{A}_\Theta(K) > 0$ has width $h_K(0) + h_K(\pi) \le c_{\omega, t}$.

*Proof.* If $\omega < \pi/2$, then $K \subseteq P_\omega$, whose width is
$\sec \omega + \tan \omega$. Let $\omega = \pi/2$ and $d = h_K(0) + h_K(\pi)$. The cap lies between
the lines $y = 0$ and $y = 1$, so $\lvert K \rvert \le d$. No normal angle of $K$ lies strictly
between $\pi$ and $2\pi$ except $3\pi/2$, so the corners $(h_K(0), 0)$ and $(-h_K(\pi), 0)$ lie in
$K$, and $h_K(t) \ge h_K(0) \cos t$, $h_K(t + \pi/2) \ge h_K(\pi) \sin t$.
Hence the wall $b_K(t)$ meets the $x$-axis at $W_K(t) = ((h_K(t) - 1)/\cos t, 0)$, at least
$h_K(0) - \sec t$, and the wall $d_K(t)$ meets it at $Z_K(t)$, at most $-h_K(\pi) + \csc t$. If
$L = d - \sec t - \csc t > 0$, the wedge $T_K(t)$ is the triangle above the segment from $Z_K(t)$ to
$W_K(t)$, of length at least $L$, with angles $t$ and $\pi/2 - t$ at its ends, so its area is at
least $L^2 \sin(2t)/4$. As $T_K(t) \subseteq \mathcal{N}_\Theta(K)$,

```math
\mathcal{A}_\Theta(K) \le d - \tfrac14 (d - \sec t - \csc t)^2 \sin 2t ,
```

which is negative for all large $d$. The Lean proof uses a rectangle inside the wedge instead of the
triangle. $\square$

*Lean: [`lemma3_4_2`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L2221).*

### Theorem 4.23 (existence of maximum polygon caps; Baek, Theorem 3.4.3)

For every angle set $\Theta$ a maximum polygon cap exists.

*Proof sketch.* The polygon cap $K_1 = \mathcal{C}_\Theta(1)$ with all support values $1$ contains
$o_\omega$, and its niche is empty: its inner corners are all at $O$, and below $O$ the quadrants miss
$F_\omega$. So $\mathcal{A}_\Theta(K_1) = \lvert K_1 \rvert > 0$, and it suffices to maximize over the
set $\mathcal{B}_\Theta$ of polygon caps $K \ni o_\omega$ with
$\mathcal{A}_\Theta(K) \ge \mathcal{A}_\Theta(K_1)$. By Lemma 4.22 they all lie in one bounded box.
Take a maximizing sequence in $\mathcal{B}_\Theta$. Its support values on the finite set
$\Theta^\diamond$ are bounded, so a subsequence converges to some
$h_\infty$, and $L = \mathcal{C}_\Theta(h_\infty)$ is a polygon cap containing $o_\omega$ with these
support values. The area of the caps is upper semicontinuous along the sequence, and that of the
niches lower semicontinuous: a point of $\mathcal{N}_\Theta(L)$ satisfies strict inequalities in the
support values, so it lies in the niches of all late terms. Hence
$\mathcal{A}_\Theta(L) \ge \limsup \mathcal{A}_\Theta(K_n)$, the supremum over $\mathcal{B}_\Theta$.
A polygon cap outside $\mathcal{B}_\Theta$ has $\mathcal{A}_\Theta < \mathcal{A}_\Theta(K_1)$, or, for
$\omega = \pi/2$, a horizontal translate in $\mathcal{B}_\Theta$ with the same value (Theorem 4.18).
The paper instead uses the continuity of $\mathcal{A}_\Theta$ in the Hausdorff distance and the
Blaschke selection theorem. $\square$

*Lean: [`theorem3_4_3`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L2806), [`mpc_limit_polycap`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L2515).*

## 4.6 Balanced polygon caps

### Definition 4.24 (monotone polyline; Baek, Definition 3.4.2)

For points $p_1, \dots, p_n$ with strictly increasing $x$-coordinates, the union of the segments from
$p_i$ to $p_{i+1}$, $1 \le i < n$, is an *$x$-monotone polyline*.

*Lean: [`IsXMonotonePolyline`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L2810).*

### Theorem 4.25 (the polyline; Baek, Theorem 3.4.4)

For a polygon cap $K \in \mathcal{K}^\mathrm{c}_\Theta$, the boundary of $F_\omega \setminus
\mathcal{N}_\Theta(K)$ is the disjoint union, from left to right, of

1. the open half-line $\vec l_K$ from $C^+_K(\omega)$ in the direction $v_\omega$, without
   $C^+_K(\omega)$;
2. an $x$-monotone polyline $\mathbf{p}_K$ from $C^+_K(\omega)$ to $A^-_K(0)$ whose segments have
   normal angles in $\Theta^\diamond$;
3. the open half-line $\vec r_K$ from $A^-_K(0)$ in the direction $u_0$, without $A^-_K(0)$.

*Lean: [`theorem3_4_4`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L3163), [`polyline`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L2823), [`rayLeft`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L2815), [`rayRight`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L2819).*

*Proof sketch.* Each quadrant $Q^-_K(t)$ is open and closed in the direction $-v_0$: with a point it
contains every point below it. So $F_\omega \setminus \mathcal{N}_\Theta(K)$ is the part of $F_\omega$
on or above the graph of $G(x) = \max(\text{bottom of } F_\omega \text{ at } x,\ \text{top of }
\bigcup_{t \in \Theta} Q^-_K(t) \text{ at } x)$, a continuous piecewise linear function whose pieces
lie on the lines $l(\pi/2, 0)$, $l(\omega, 0)$, $b_K(t)$ and $d_K(t)$, $t \in \Theta$, with normal
angles $\pi/2$, $\omega$, $t$ and $t + \pi/2$ in $\Theta^\diamond$. The half-line $\vec r_K$ avoids every
$Q^-_K(t)$, since $A^-_K(0)$ lies right of $b_K(t)$ by $w_K(t) > 0$ (Baek's Theorem 2.5.5, in
[Chapter 3](03-monotone.md)); likewise $z_K(t) > 0$ for $\vec l_K$. So the graph of $G$ is the bottom of
$F_\omega$ outside the segment between $C^+_K(\omega)$ and $A^-_K(0)$. The vertices of $\mathbf{p}_K$ are
the sorted crossings of the walls. $\square$

### Definition 4.26 (balanced polygon cap; Baek, Definitions 3.4.3–3.4.5)

The polyline $\mathbf{p}_K$ of Theorem 4.25 is the *polyline* of $K \in \mathcal{K}^\mathrm{c}_\Theta$.
For $t \in \Theta^\diamond$, $\tau_K(t)$ is the total length of the segments of $\mathbf{p}_K$ with normal
angle $t$. The polygon cap $K$ is *balanced* if $\sigma_K(t) = \tau_K(t)$ for every
$t \in \Theta^\diamond$.

*Lean: [`polyline`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L2823), [`MovingSofaOptimality.tau`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L3240), [`IsBalanced`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L4027), [`sigmaAt`](../../MovingSofaOptimality/Basic/SurfaceArea.lean#L284).*

The upper boundary $\delta K$ of the cap runs from $A^-_K(0)$ to $C^+_K(\omega)$ through sides of
lengths $\sigma_K(t)$, $t \in \Theta^\diamond$, and the polyline runs back below the sofa through
segments of total lengths $\tau_K(t)$ (Figure 4.6). A side of the cap with normal $u_t$ lies on the
outer wall of a hallway, and the segments with the same normal angle lie on the inner wall of the
same arm, or on the bottom of $F_\omega$ for $t \in \lbrace \omega, \pi/2 \rbrace$: balance is
Gerver's condition.

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

*Lean: [`lemma3_4_5_one`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L3981), [`lemma3_4_5_two`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L4019).*

*Proof sketch.* The boundary of $\mathcal{N}_\Theta(K)$ consists of the pieces of the polyline inside
the open fan, which lie on the walls, the part of $\partial F_\omega$ covered by the niche, and
finitely many points. (1) For $t \in \Theta$ the only line among the walls and the bottom of
$F_\omega$ with normal angle $t$ is $b_K(t)$, and the only one with normal angle $t + \pi/2$ is
$d_K(t)$; the pieces lie on the half-lines that bound $Q^-_K(t)$. (2) The bottom side
$e_K(t + \pi)$ of $K$, of length $\sigma_K(t + \pi)$, lies on $l(t, 0)$; the polyline covers the part
of it outside the niche, of length $\tau_K(t)$, and the niche the rest. $\square$

### Lemma 4.28 (an unbalanced cap has a long side; Baek, Lemma 3.4.6)

If $K \in \mathcal{K}^\mathrm{c}_\Theta$ is not balanced, then $\sigma_K(t) > \tau_K(t)$ for some
$t \in \Theta^\diamond$.

*Proof.* Walking from $A^-_K(0)$ to $C^+_K(\omega)$ along the polyline, and along the upper boundary of
$K$,

```math
C^+_K(\omega) - A^-_K(0) = \sum_{t \in \Theta^\diamond} \tau_K(t)\, v_t = \sum_{t \in \Theta^\diamond} \sigma_K(t)\, v_t .
```

Taking the inner product with $u_0$, and using $v_t \cdot u_0 = -\sin t < 0$ on $(0, \pi)$,
$\sum_{t} (\tau_K(t) - \sigma_K(t)) \sin t = 0$. If $\sigma_K \le \tau_K$ everywhere, every term is
nonnegative, so every term vanishes and $K$ is balanced. $\square$

*Lean: [`lemma3_4_6`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L4031), [`mpc_walk`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L866).*

### Lemma 4.29 (the balancing step; Baek, Lemma 3.4.7)

Let $K \in \mathcal{K}^\mathrm{c}_\Theta$, $h = h_K$, and $t \in \Theta^\diamond$, and let $h^+$ agree
with $h$ except $h^+(t) = h(t) + \varepsilon$. There are $\varepsilon_0 > 0$ and $C$ such that for
$0 < \varepsilon \le \varepsilon_0$

```math
\Bigl\lvert\, \mathcal{A}_\Theta(h^+) - \mathcal{A}_\Theta(h) - \bigl(\sigma_K(t) - \tau_K(t)\bigr)\, \varepsilon \,\Bigr\rvert \le C \varepsilon^2 .
```

*Proof.* Suppose first that $t \notin \lbrace \omega, \pi/2 \rbrace$. Theorem 4.3, applied to the simple
Nef polygon $\mathcal{C}_\Theta(h) = K$ and its half-plane $H_-(t, h(t))$, whose line meets
$\partial K$ in the side $e_K(t)$, gives
$\lvert \mathcal{C}_\Theta(h^+) \rvert = \lvert K \rvert + \sigma_K(t)\, \varepsilon + O(\varepsilon^2)$.
Applied to $\mathcal{N}_\Theta(h)$ and its half-plane $H^\circ_-(t, h(t) - 1)$, it gives with
Lemma 4.27 (1)
$\lvert \mathcal{N}_\Theta(h^+) \rvert = \lvert \mathcal{N}_\Theta(h) \rvert + \tau_K(t)\, \varepsilon + O(\varepsilon^2)$.
Subtract (Figure 4.2 shows the two strips).

Now let $t \in \lbrace \omega, \pi/2 \rbrace$. Then both $H_-(t, h(t))$ and the bottom half-plane
$H_+(t, h(t) - 1)$ move by $\varepsilon$: the whole strip of $P_h$ in the direction $u_t$ moves. For
$\varepsilon < 1$ the two moves change disjoint strips, so two applications of Theorem 4.3 give
$\lvert \mathcal{C}_\Theta(h^+) \rvert = \lvert K \rvert + (\sigma_K(t) - \sigma_K(t + \pi))\,\varepsilon +
O(\varepsilon^2)$; the fan loses the strip along $l(t, 0)$, so by Lemma 4.27 (2)
$\lvert \mathcal{N}_\Theta(h^+) \rvert = \lvert \mathcal{N}_\Theta(h) \rvert - (\sigma_K(t + \pi) -
\tau_K(t))\,\varepsilon + O(\varepsilon^2)$. Subtract again. $\square$

*Lean: [`lemma3_4_7`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L4579).*

The paper's proof prints the change of $\lvert \mathcal{N}_\Theta \rvert$ in the second case with the
opposite sign (REPORT.md, E26), and applies Theorem 4.3 twice in a row, to a polygon that the first
application has changed; that is justified because the two strips are disjoint (REPORT.md, E5).

### Lemma 4.30 (the pushed cap is a translate; Baek, Lemma 3.4.8)

Let $K \in \mathcal{K}^\mathrm{c}_\Theta$ and $t \in \Theta^\diamond$ with $\sigma_K(t) > 0$, and let $h^+$
be as in Lemma 4.29. For all small $\varepsilon > 0$, $K^+ = \mathcal{C}_\Theta(h^+)$ is in
$\mathcal{K}^\mathrm{t}_\Theta$.

*Proof.* If $t \notin \lbrace \omega, \pi/2 \rbrace$, then $K \subseteq K^+ \subseteq P_\omega$, so $K^+$
has the support values of $K$ at $\omega$, $\pi/2$, $\omega + \pi$, $3\pi/2$, and is a polygon cap. If
$t \in \lbrace \omega, \pi/2 \rbrace$, it suffices by Proposition 4.11 to see that $K^+$ has width one
in the directions $u_\omega$ and $u_{\pi/2}$. Since $\sigma_K(t) > 0$, part of the side $e_K(t)$ moves
out with the line, so $h_{K^+}(t) = h_K(t) + \varepsilon$, and the raised bottom line still cuts $K$,
so $h_{K^+}(t + \pi) = h_K(t + \pi) - \varepsilon$: the width along $u_t$ stays one. If
$\omega < \pi/2$, let $t'$ be the other angle of $\lbrace \omega, \pi/2 \rbrace$. The side $e_K(t')$ is
not moved, and the bottom side $e_K(t' + \pi)$, of length at least $o_\omega \cdot u_0 > 0$ since
$o_\omega \in K$, loses only a short piece at $O$; so $K^+$ still touches both lines of the direction
$u_{t'}$. $\square$

*Lean: [`lemma3_4_8`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L4671).*

Without $\sigma_K(t) > 0$ the line $l(t, h(t) + \varepsilon)$ would not touch $K^+$, and the width of
$K^+$ along $u_t$ would drop below one. This is why Lemma 4.28 looks for a side that is too long, and
why the balancing move is made only outwards.

### Theorem 4.31 (maximum polygon caps are balanced; Baek, Theorem 3.4.9)

Every maximum polygon cap is balanced.

*Proof.* Let $K$ be a maximum polygon cap that is not balanced. By Lemma 4.28 there is
$t \in \Theta^\diamond$ with $\sigma_K(t) > \tau_K(t) \ge 0$. For small $\varepsilon > 0$, Lemma 4.30
writes $K^+ = \mathcal{C}_\Theta(h^+) = K_0 + v$ with a polygon cap $K_0$, and

```math
\mathcal{A}_\Theta(K) = \mathcal{A}_\Theta(h_K) < \mathcal{A}_\Theta(h^+) \le \mathcal{A}_\Theta(K^+) = \mathcal{A}_\Theta(K_0)
```

by Proposition 4.16, Lemma 4.29 (for $\varepsilon < (\sigma_K(t) - \tau_K(t))/C$), Proposition 4.19
and Theorem 4.18. This contradicts the maximality of $K$. $\square$

*Lean: [`theorem3_4_9`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L4683).*

The comparison cap $K_0$ is a polygon cap, which may have a niche that sticks out; no connectedness is
needed, and this closes the gap of §4.1.

### Theorem 4.32 (the polygon niche lies in the cap; Baek, Theorem 3.4.10)

Every maximum polygon cap $K$ with angle set $\Theta$ contains its polygon niche $\mathcal{N}_\Theta(K)$.

*Proof.* We show that every vertex $p$ of the polyline lies in $K$. Walking along $\mathbf{p}_K$ from
$A = A^-_K(0)$ to $p$ gives $p = A + \sum_i \ell_i v_{s_i}$ over the segments right of $p$, where the
lengths $\ell_i$ of the segments with normal angle $t$ add up to at most $\tau_K(t)$. Let
$s \in \Theta^\diamond$. Since $v_{s_i} \cdot u_s = \sin(s - s_i)$, and all angles lie in $(0, \pi)$,
the terms with $s_i < s$ are positive and the others are not, so

```math
p \cdot u_s \le A \cdot u_s + \sum_{t < s} \tau_K(t) \sin(s - t) = A \cdot u_s + \sum_{t < s} \sigma_K(t) \sin(s - t) = v^+_K(s) \cdot u_s = h_K(s) ,
```

where the sums run over $t \in \Theta^\diamond$, the first equality is the balance of $K$
(Theorem 4.31), and the second walks along the upper boundary of $K$ from $A$ to the vertex
$v^+_K(s)$. So $p$ lies in every supporting half-plane of $K$ with normal angle in $\Theta^\diamond$, and
it lies in $F_\omega$; hence $p \in K$. By convexity $\mathbf{p}_K \subseteq K$, and the niche, which by
Theorem 4.25 lies in $F_\omega$ below the polyline, is contained in $K$: each vertical segment from the
bottom of $F_\omega$, a point of a bottom side of $K$, up to the polyline lies in $K$. $\square$

*Lean: [`theorem3_4_10`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L4717), [`mpc_walk`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L866).*

The paper proves $p \cdot u_s \le h_K(s)$ for $s \in \Theta \cup \lbrace \omega \rbrace$ and obtains the
other angles from the mirror image; the estimate above holds for all $s \in \Theta^\diamond$ at once,
as in the Lean proof.

## 4.7 Balanced maximum sofas

### Definition 4.33 (balanced maximum cap; Baek, Definitions 3.5.1–3.5.2)

The *uniform angle set* with $n \ge 2$ intervals is
$\Theta_{\omega, n} = \lbrace i\omega/n : 1 \le i < n \rbrace$. A *balanced maximum cap* with rotation
angle $\omega \in (0, \pi/2]$ is a cap $K_\omega \in \mathcal{K}^\mathrm{c}_\omega$ for which there
are powers of two $1 < n_1 < n_2 < \cdots$ and maximum polygon caps $K_i$ with angle sets
$\Theta_{\omega, n_i}$ such that $K_i \to K_\omega$ in the Hausdorff distance
$d_\mathrm{H}(K, K') = \sup_t \lvert h_K(t) - h_{K'}(t) \rvert$ ([Chapter 2](02-preliminaries.md)).

*Lean: [`uniformAngleSet`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L32), [`dyadicAngleSet`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L50), [`IsBalancedMaxCap`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L133), [`hausdorffDist`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L74),
[`HausdorffTendsto`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L77).*

![Three rows, for n = 4, 8 and 16, each showing a blue polygon sofa between faint lines y = 0 and y = 1 with a dashed outline of Gerver's sofa centred on the same vertical line. For n = 4 the polygon sofa is visibly wider, with straight slanted ends and a jagged notch; for n = 8 it is closer; for n = 16 its ends and its notch nearly follow the dashed outline](figures/04-balanced/limit.svg)

*Figure 4.7.* The maximum polygon sofas for $\omega = \pi/2$ and the uniform angle sets with
$n = 4$, $8$ and $16$ intervals (blue), computed numerically, with the outline of Gerver's sofa
(dashed). Their values $\mathcal{A}_\Theta(K_\Theta) = 2.4148$, $2.3027$, $2.2584$ decrease towards
$\lvert G \rvert = 2.2195$; each of them is balanced to within $10^{-12}$ (Theorem 4.31).

As $n$ doubles, the angle set grows, so for each cap the polygon cap shrinks and the polygon niche
grows, and the maximum values decrease (Figure 4.7). By Theorem 4.9 each value bounds the area of
every monotone sofa of rotation angle $\pi/2$. The paper's proof of Theorem 3.5.5 shows that they
converge to the maximum of $\mathcal{A}_{\pi/2}$, which [Chapter 9](09-optimality.md) identifies with
$\lvert G \rvert$.

### Proposition 4.34 (mirror image; Baek, Proposition 3.5.1)

The mirror image of a balanced maximum cap is a balanced maximum cap.

*Proof.* Apply Lemma 4.21 to the maximum polygon caps $K_i$: the uniform angle sets satisfy
$\omega - \Theta_{\omega, n} = \Theta_{\omega, n}$, and $M_\omega$ preserves the Hausdorff distance. $\square$

*Lean: [`proposition3_5_1`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L182).*

### Theorem 4.35 (existence of balanced maximum caps; Baek, Theorem 3.5.2)

For every $\omega \in (0, \pi/2]$ there is a balanced maximum cap with rotation angle $\omega$.

*Proof sketch.* For each $m$ let $K_m$ be a maximum polygon cap with angle set $\Theta_{\omega, 2^{m+1}}$
(Theorem 4.23). The angle $\omega/2$ lies in every one of these angle sets, and
$\mathcal{A}_\Theta(K_m) \ge \mathcal{A}_\Theta(K_1) > 0$ with $K_1$ as in the proof of
Theorem 4.23, so by Lemma 4.22 the widths of the $K_m$ are at most $c_{\omega, \omega/2}$; as they
contain $o_\omega$ and lie between the lines $y = 0$ and $y = 1$, they lie in one compact box. By the
Blaschke selection theorem ([Chapter 2](02-preliminaries.md)) a subsequence converges to a convex
body $K$. The support values at $\omega$, $\pi/2$, $\omega + \pi$, $3\pi/2$ pass to the limit. It
remains to see that $K$ is an
intersection of half-planes with normal angles in $J_\omega \cup \lbrace \omega + \pi, 3\pi/2 \rbrace$,
$J_\omega = [0, \omega] \cup [\pi/2, \omega + \pi/2]$. The complementary gaps $(a, b)$ are shorter
than $\pi$, and a polygon cap has no normal angle in them, so its support function satisfies

```math
\sin(b - a)\, h(r) = \sin(b - r)\, h(a) + \sin(r - a)\, h(b) \qquad (a \le r \le b) ,
```

the identity of a corner. It passes to the limit, and says that $K$ has no normal angle in the gap.
The paper calls this check easy (REPORT.md, E8). $\square$

*Lean: [`theorem3_5_2`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L452), [`mpc_blaschke`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L223), [`mpc_gap_limit`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L306).*

### Lemma 4.36 (limits of nested sets; Baek, Lemma 3.5.3)

Let $X, Y, X_i, Y_i$ be bounded nonempty subsets of $\mathbb{R}^2$ with $X_i \to X$ and $Y_i \to Y$ in
the Hausdorff distance, and $Y$ compact. If $X_i \subseteq Y_i$ for all $i$, then $X \subseteq Y$.

*Proof.* Let $p \in X$. Then $d(p, X_i) \to 0$, so there are $p_i \in X_i \subseteq Y_i$ with $p_i \to p$,
and $d(p_i, Y) \le d_\mathrm{H}(Y_i, Y) \to 0$. So $d(p, Y) = 0$, and $p \in Y$ as $Y$ is closed.
$\square$

*Lean: [`lemma3_5_3`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L494).*

The formal proofs of the next two theorems do not use Lemma 4.36; they use the eventual membership
of the points of the niche in the polygon niches, as follows.

### Theorem 4.37 (the niche lies in the cap; Baek, Theorem 3.5.4)

Every balanced maximum cap $K_\omega$ contains its niche: $\mathcal{N}(K_\omega) \subseteq K_\omega$.

*Proof.* Let $K = K_\omega$, with maximum polygon caps $K_i \to K$ for the angle sets
$\Theta_i = \Theta_{\omega, n_i}$, and let $p \in \mathcal{N}(K)$. Then $p \in F_\omega \cap Q^-_K(t)$
for some $t \in (0, \omega)$:

```math
p \cdot u_t < h_K(t) - 1 , \qquad p \cdot u_{t + \pi/2} < h_K(t + \pi/2) - 1 .
```

The support function is continuous, so both strict inequalities hold, with a margin $\delta > 0$, at
some dyadic angle $s = j\omega/2^k$ near $t$. For large $i$ the angle $s$ lies in $\Theta_i$, since
these sets increase, and $\lvert h_{K_i} - h_K \rvert < \delta$; so
$p \in \mathcal{N}_{\Theta_i}(K_i) \subseteq K_i$ by Theorem 4.32. Since $K_i \to K$, $p \in K$. $\square$

*Lean: [`theorem3_5_4`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L572), [`mpc_niche_eventually`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L523).*

The paper argues that the polygon niches $\mathcal{N}_{\Theta_j}(K_i)$ converge to $\mathcal{N}_{\Theta_j}(K)$
unless the latter is empty, which can fail when a wedge is empty for $K$ but not for the $K_i$; the
eventual membership above is what the argument needs (REPORT.md, E8).

### Theorem 4.38 (maximality; Baek, Theorem 3.5.5)

A balanced maximum cap $K_\omega$ maximizes the sofa area functional $\mathcal{A}_\omega$ over all
caps with rotation angle $\omega$.

*Proof.* Let $K'$ be a cap with rotation angle $\omega$. By Theorem 4.9 and the maximality of $K_i$,

```math
\mathcal{A}_\omega(K') \le \mathcal{A}_{\Theta_i}(K') \le \mathcal{A}_{\Theta_i}(K_i) = \lvert K_i \rvert - \lvert \mathcal{N}_{\Theta_i}(K_i) \rvert .
```

Area is upper semicontinuous in the Hausdorff distance, so
$\limsup \lvert K_i \rvert \le \lvert K_\omega \rvert$. By the proof of Theorem 4.37, each point of
$\mathcal{N}(K_\omega)$ lies in $\mathcal{N}_{\Theta_i}(K_i)$ for all large $i$, and these sets lie in one
bounded set, so $\liminf \lvert \mathcal{N}_{\Theta_i}(K_i) \rvert \ge \lvert \mathcal{N}(K_\omega) \rvert$ by
Fatou's lemma. Hence $\mathcal{A}_\omega(K') \le \mathcal{A}_\omega(K_\omega)$. The paper shows moreover
that $\mathcal{A}_{\Theta_i}(K_i) \to \mathcal{A}_\omega(K_\omega)$. $\square$

*Lean: [`theorem3_5_5`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L582), [`mpc_area_usc`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L390), [`mpc_area_lsc`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L402).*

### Definition 4.39 (balanced maximum sofa; Baek, Definition 3.5.3)

A *balanced maximum sofa* with rotation angle $\omega$ is a monotone sofa $S_\omega$ whose cap
$\mathcal{C}(S_\omega)$ is a balanced maximum cap.

*Lean: [`IsBalancedMaxSofa`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L646).*

### Theorem 4.40 (balanced maximum sofas; Baek, Theorem 3.5.6)

For every $\omega \in (0, \pi/2]$ there is a balanced maximum cap $K_\omega$ such that
$S_\omega = K_\omega \setminus \mathcal{N}(K_\omega)$ is a balanced maximum sofa with cap $K_\omega$, and
$\lvert S \rvert \le \lvert S_\omega \rvert$ for every moving sofa $S$ with rotation angle $\omega$.

*Proof.* Theorem 4.35 gives a balanced maximum cap $K_\omega$. It contains its niche (Theorem 4.37), so
it is the cap of the monotone sofa $K_\omega \setminus \mathcal{N}(K_\omega)$ (Baek's Theorems 2.5.9 and
2.4.3, in [Chapter 3](03-monotone.md)). Let $S$ be a moving sofa with rotation angle $\omega$.
Translated into standard position, $S$ lies in its monotonization, a monotone sofa (Baek's
Theorem 2.3.2), whose cap $K'$ has $\mathcal{A}_\omega(K')$ equal to the area of the monotonization
(Baek's Theorem 2.5.10). So
$\lvert S \rvert \le \mathcal{A}_\omega(K') \le \mathcal{A}_\omega(K_\omega) = \lvert S_\omega \rvert$ by
Theorem 4.38. $\square$

*Lean: [`theorem3_5_6`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L651).*
